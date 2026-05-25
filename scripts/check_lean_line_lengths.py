#!/usr/bin/env python3
"""Check that Lean source files have no lines longer than the configured limit."""

from __future__ import annotations

import argparse
from pathlib import Path

DEFAULT_EXCLUDED_DIRS = {".git", ".lake", ".pi"}


def lean_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*.lean"):
        if any(part in DEFAULT_EXCLUDED_DIRS for part in path.parts):
            continue
        files.append(path)
    return sorted(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max", type=int, default=100, help="maximum allowed line length")
    parser.add_argument(
        "--root", type=Path, default=Path.cwd(), help="repository root to scan"
    )
    args = parser.parse_args()

    bad: list[tuple[Path, int, int]] = []
    root = args.root.resolve()
    for path in lean_files(root):
        rel = path.relative_to(root)
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            length = len(line)
            if length > args.max:
                bad.append((rel, line_number, length))

    if bad:
        for path, line_number, length in bad:
            print(f"{path}:{line_number}: line length {length} > {args.max}")
        print(f"Found {len(bad)} overlong Lean line(s).")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
