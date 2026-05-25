#!/usr/bin/env python3
"""Check simple text-file style rules used by CI."""

from __future__ import annotations

import argparse
from pathlib import Path

DEFAULT_EXCLUDED_DIRS = {".git", ".lake", ".pi"}
DEFAULT_SUFFIXES = {".lean", ".md", ".toml", ".yml", ".yaml", ".py"}
DEFAULT_NAMES = {"README.md", "LICENSE", ".gitignore", "lean-toolchain"}


def text_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        if any(part in DEFAULT_EXCLUDED_DIRS for part in path.parts):
            continue
        if path.suffix in DEFAULT_SUFFIXES or path.name in DEFAULT_NAMES:
            files.append(path)
    return sorted(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path.cwd(), help="repository root to scan"
    )
    args = parser.parse_args()

    root = args.root.resolve()
    bad: list[str] = []
    for path in text_files(root):
        rel = path.relative_to(root)
        content = path.read_bytes()
        if content and not content.endswith(b"\n"):
            bad.append(f"{rel}: missing final newline")
        if path.suffix == ".lean":
            continue
        for line_number, line in enumerate(path.read_text().splitlines(), 1):
            if line.rstrip() != line:
                bad.append(f"{rel}:{line_number}: trailing whitespace")

    if bad:
        print("\n".join(bad))
        print(f"Found {len(bad)} text style issue(s).")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
