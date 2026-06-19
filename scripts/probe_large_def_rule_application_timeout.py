#!/usr/bin/env python3
"""Run LR0 large-definition primitive-rule application probes.

The script runs Lean files supplied by the caller. It does not create Lake packages or edit a
worktree; use a disposable downstream checkout with a real InternalLean package copy.
"""

from __future__ import annotations

import argparse
import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path


DEFAULT_CASES: tuple[tuple[str, Path, float], ...] = (
    (
        "simple_idtoeqv_child_control",
        Path("/tmp/SimpleTheoremInIdtoeqvAtChild.lean"),
        80.0,
    ),
    (
        "theorem_ref_minimized_control",
        Path("/tmp/InternalLeanTheoremRefTimeoutMinimized.lean"),
        100.0,
    ),
    (
        "theorem_ref_univ_only_control",
        Path("/tmp/UseSigmaFstTyInUnivOnlyChild.lean"),
        100.0,
    ),
    (
        "hott_sigmaFst_control",
        Path("/tmp/HoTTUseSigmaFstTyProbe2.lean"),
        100.0,
    ),
    (
        "pointed_carrier_control",
        Path("/tmp/PointedCarrierTyProofProbe2.lean"),
        180.0,
    ),
    (
        "apply_idtoeqv_rule",
        Path("/tmp/ApplyIdtoeqvAtRuleProbe.lean"),
        120.0,
    ),
    (
        "apply_idtoeqv_rule_delta",
        Path("/tmp/ApplyIdtoeqvAtRuleProbeDelta.lean"),
        120.0,
    ),
    (
        "univ_only_univ_univ_exact",
        Path("/tmp/UnivOnlyUnivUnivExactProbe.lean"),
        120.0,
    ),
    (
        "hott_univ_univ_exact",
        Path("/tmp/UnivUnivExactProbe.lean"),
        120.0,
    ),
    (
        "hott_univalence_pi_ty",
        Path("/tmp/UnivalencePiTyProbeHoTTOnly.lean"),
        120.0,
    ),
)

PROFILE_OPTIONS: tuple[str, ...] = (
    "-DinternalLean.profileInternalDef=true",
    "-DinternalLean.conversion.profile=true",
    "-DinternalLean.conversion.traceFallbacks=true",
)


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
        cmd.extend(PROFILE_OPTIONS)
    cmd.append(str(path))
    return cmd


def tail_lines(text: str, count: int) -> str:
    if count <= 0:
        return ""
    return "\n".join(text.splitlines()[-count:])


def terminate_process_group(proc: subprocess.Popen[str]) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        proc.wait(timeout=5.0)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            return
        proc.wait()


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
    stdout_path = log_dir / f"{case}.stdout.log"
    stderr_path = log_dir / f"{case}.stderr.log"
    start = time.monotonic()
    status = "completed"
    returncode: int | None = None
    with stdout_path.open("w") as stdout_file, stderr_path.open("w") as stderr_file:
        proc = subprocess.Popen(
            cmd,
            cwd=workdir,
            text=True,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=True,
        )
        try:
            returncode = proc.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            status = "timeout"
            terminate_process_group(proc)
    elapsed = time.monotonic() - start
    stdout = stdout_path.read_text(errors="replace")
    stderr = stderr_path.read_text(errors="replace")
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


def parse_cases(selected: set[str], timeout_override: float | None) -> list[tuple[str, Path, float]]:
    cases: list[tuple[str, Path, float]] = []
    known = {case for case, _, _ in DEFAULT_CASES}
    unknown = selected - known
    if unknown:
        raise SystemExit(f"unknown case(s): {', '.join(sorted(unknown))}")
    for case, path, timeout_seconds in DEFAULT_CASES:
        if selected and case not in selected:
            continue
        cases.append((case, path, timeout_override or timeout_seconds))
    return cases


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workdir", type=Path, default=Path.cwd())
    parser.add_argument("--log-dir", type=Path, default=Path(".pi/lr0"))
    parser.add_argument("--json", type=Path, default=None)
    parser.add_argument("--timeout", type=float, default=None)
    parser.add_argument("--tail-lines", type=int, default=40)
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--profile", action=argparse.BooleanOptionalAction, default=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    workdir = args.workdir.resolve()
    if not workdir.exists():
        print(f"workdir does not exist: {workdir}", file=sys.stderr)
        return 2
    cases = parse_cases(set(args.case), args.timeout)
    for _, path, _ in cases:
        if not path.exists():
            print(f"probe file does not exist: {path}", file=sys.stderr)
            return 2
    args.log_dir.mkdir(parents=True, exist_ok=True)
    results = [
        run_probe(case, path, timeout, workdir, args.log_dir, args.profile, args.tail_lines)
        for case, path, timeout in cases
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
