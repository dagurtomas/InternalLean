#!/usr/bin/env python3
"""Run the AR0 theorem-replay abbreviation timeout probes.

The script only runs Lean files supplied by the caller.  It does not create Lake packages or edit a
downstream checkout; use a disposable downstream copy/worktree with a real InternalLean package.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path


DEFAULT_MINIMIZED = Path("/tmp/InternalLeanReplayTimeoutMinimized.lean")
DEFAULT_CONTROL = Path("/tmp/InternalLeanReplayTimeoutExpandedRhsControl.lean")


@dataclass
class ProbeResult:
    case: str
    path: str
    status: str
    returncode: int | None
    elapsed_seconds: float
    stdout_bytes: int
    stderr_bytes: int
    stdout_log: str
    stderr_log: str


def build_command(path: Path, profile: bool) -> list[str]:
    cmd = ["lake", "env", "lean"]
    if profile:
        cmd.extend(
            [
                "-DinternalLean.profileLFCheckPhases=true",
                "-DinternalLean.conversion.profile=true",
                "-DinternalLean.conversion.traceFallbacks=true",
            ]
        )
    cmd.append(str(path))
    return cmd


def tail_lines(text: str, count: int) -> str:
    if count <= 0:
        return ""
    return "\n".join(text.splitlines()[-count:])


def run_probe(
    case: str,
    path: Path,
    timeout_seconds: float,
    workdir: Path,
    log_dir: Path,
    profile: bool,
    tail_count: int,
) -> ProbeResult:
    cmd = build_command(path, profile)
    start = time.monotonic()
    status = "completed"
    returncode: int | None = None
    stdout = ""
    stderr = ""
    try:
        proc = subprocess.run(
            cmd,
            cwd=workdir,
            text=True,
            capture_output=True,
            timeout=timeout_seconds,
            check=False,
        )
        returncode = proc.returncode
        stdout = proc.stdout
        stderr = proc.stderr
    except subprocess.TimeoutExpired as ex:
        status = "timeout"
        stdout = ex.stdout or ""
        stderr = ex.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
    elapsed = time.monotonic() - start
    stdout_path = log_dir / f"{case}.stdout.log"
    stderr_path = log_dir / f"{case}.stderr.log"
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    print(
        f"{case}: status={status} returncode={returncode} "
        f"elapsed={elapsed:.2f}s stdout={len(stdout)}B stderr={len(stderr)}B"
    )
    combined_tail = tail_lines(stdout + stderr, tail_count)
    if combined_tail:
        print(f"--- {case} tail ({tail_count} lines) ---")
        print(combined_tail)
    return ProbeResult(
        case=case,
        path=str(path),
        status=status,
        returncode=returncode,
        elapsed_seconds=elapsed,
        stdout_bytes=len(stdout),
        stderr_bytes=len(stderr),
        stdout_log=str(stdout_path),
        stderr_log=str(stderr_path),
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workdir", type=Path, default=Path.cwd())
    parser.add_argument("--minimized", type=Path, default=DEFAULT_MINIMIZED)
    parser.add_argument("--control", type=Path, default=DEFAULT_CONTROL)
    parser.add_argument("--minimized-timeout", type=float, default=60.0)
    parser.add_argument("--control-timeout", type=float, default=120.0)
    parser.add_argument("--log-dir", type=Path, default=Path(".pi/ar0"))
    parser.add_argument("--json", type=Path, default=None)
    parser.add_argument("--tail-lines", type=int, default=40)
    parser.add_argument("--profile", action=argparse.BooleanOptionalAction, default=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    workdir = args.workdir.resolve()
    if not workdir.exists():
        print(f"workdir does not exist: {workdir}", file=sys.stderr)
        return 2
    for path in [args.minimized, args.control]:
        if not path.exists():
            print(f"probe file does not exist: {path}", file=sys.stderr)
            return 2
    args.log_dir.mkdir(parents=True, exist_ok=True)
    results = [
        run_probe(
            "control_expanded_rhs",
            args.control,
            args.control_timeout,
            workdir,
            args.log_dir,
            args.profile,
            args.tail_lines,
        ),
        run_probe(
            "minimized_folded_rhs",
            args.minimized,
            args.minimized_timeout,
            workdir,
            args.log_dir,
            args.profile,
            args.tail_lines,
        ),
    ]
    payload = {
        "workdir": str(workdir),
        "profile": args.profile,
        "results": [asdict(r) for r in results],
    }
    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2) + "\n")
    else:
        print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
