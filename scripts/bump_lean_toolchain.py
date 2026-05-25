#!/usr/bin/env python3
"""Manually bump the Lean toolchain and run the standard InternalLean checks."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

DEFAULT_CHECKS = [
    ["lake", "update"],
    ["lake", "build", "InternalLean", "InternalLeanTest"],
    ["lake", "env", "lean", "InternalLean.lean"],
    ["lake", "env", "lean", "InternalLeanTest.lean"],
    ["scripts/check_text_style.py"],
    ["scripts/check_lean_line_lengths.py", "--max", "100"],
]


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def normalize_toolchain(target: str) -> str:
    target = target.strip()
    if target.startswith("leanprover/lean4:"):
        return target
    if not target:
        raise ValueError("empty Lean version")
    return f"leanprover/lean4:{target}"


def run(cmd: list[str], *, cwd: Path, dry_run: bool) -> None:
    print("+ " + " ".join(cmd), flush=True)
    if dry_run:
        return
    subprocess.run(cmd, cwd=cwd, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--to",
        required=True,
        help="Lean version tag, e.g. v4.30.0-rc2, or full leanprover/lean4:v... string",
    )
    parser.add_argument(
        "--no-checks",
        action="store_true",
        help="only update lean-toolchain; do not run lake update/build/style checks",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="print the intended changes and commands without modifying files",
    )
    args = parser.parse_args()

    root = repo_root()
    toolchain_path = root / "lean-toolchain"
    new_toolchain = normalize_toolchain(args.to)
    old_toolchain = toolchain_path.read_text().strip()

    print(f"Current toolchain: {old_toolchain}")
    print(f"Target toolchain:  {new_toolchain}")

    if old_toolchain == new_toolchain:
        print("lean-toolchain is already up to date")
    elif args.dry_run:
        print(f"Would write {new_toolchain!r} to lean-toolchain")
    else:
        toolchain_path.write_text(new_toolchain + "\n")
        print("Updated lean-toolchain")

    if args.no_checks:
        print("Skipping checks because --no-checks was passed")
        return 0

    try:
        for cmd in DEFAULT_CHECKS:
            run(cmd, cwd=root, dry_run=args.dry_run)
    except subprocess.CalledProcessError as err:
        message = f"Command failed with exit code {err.returncode}: {' '.join(err.cmd)}"
        print(message, file=sys.stderr)
        return err.returncode

    if args.dry_run:
        print("Dry run complete")
    else:
        print("Lean toolchain bump checks passed")
        print("Review the diff, then commit lean-toolchain and any lake-manifest.json changes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
