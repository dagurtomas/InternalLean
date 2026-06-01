#!/usr/bin/env python3
"""Wall-clock smoke benchmark for compiled incremental LF checker caches.

The benchmark builds a synthetic base theory once, then times three downstream files that import the
compiled base module:

* import-only;
* one admitted internal theorem;
* one checked internal theorem.

It is intended for local performance checks, not CI-grade absolute timing assertions.
"""

from __future__ import annotations

import argparse
import os
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass
class TimedRun:
    label: str
    times: list[float]

    @property
    def median(self) -> float:
        return statistics.median(self.times)


def base_source(size: int) -> str:
    lines = [
        "import InternalLean.Command",
        "open InternalLean",
        f"declare_type_theory BenchIncrementalCache{size} where",
        "  syntax_sort Obj",
        "  judgment J (x : Obj)",
        "  lf_opaque base : Obj",
        "  rule intro (x : Obj) : J x",
        "  lf_def d000 : Obj := base",
    ]
    for i in range(1, size + 1):
        lines.append(f"  lf_def d{i:03d} : Obj := d{i - 1:03d}")
    lines.append("  judgment_theorem imported : J base := intro base")
    return "\n".join(lines) + "\n"


def downstream_source(size: int, variant: str) -> str:
    header = [
        f"import InternalLeanCacheBench.Base{size}",
        f"namespace BenchIncrementalCache{size}",
    ]
    if variant == "import-only":
        body: list[str] = []
    elif variant == "admitted":
        body = ["internal theorem cache_admitted : J base := sorry"]
    elif variant == "checked":
        body = ["internal theorem cache_checked : J base := imported"]
    else:
        raise ValueError(variant)
    footer = [f"end BenchIncrementalCache{size}"]
    return "\n".join(header + body + footer) + "\n"


def run(cmd: list[str], repo: Path, env: dict[str, str] | None = None) -> float:
    start = time.perf_counter()
    proc = subprocess.run(
        cmd,
        cwd=repo,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - start
    if proc.returncode != 0:
        print(proc.stdout, file=sys.stderr)
        raise SystemExit(f"command failed: {' '.join(cmd)}")
    return elapsed


def lake_env_prefix(repo: Path) -> list[str]:
    return ["lake", "env", "lean"]


def compile_base(repo: Path, bench_root: Path, size: int) -> None:
    module_dir = bench_root / "InternalLeanCacheBench"
    module_dir.mkdir(parents=True, exist_ok=True)
    source = module_dir / f"Base{size}.lean"
    source.write_text(base_source(size))
    run(
        lake_env_prefix(repo)
        + [str(source), "-o", str(source.with_suffix(".olean")), "-i", str(source.with_suffix(".ilean"))],
        repo,
    )


def time_variant(repo: Path, bench_root: Path, size: int, variant: str, runs: int) -> TimedRun:
    module_dir = bench_root / "InternalLeanCacheBench"
    path = module_dir / f"Downstream{size}_{variant.replace('-', '_')}.lean"
    path.write_text(downstream_source(size, variant))
    env = os.environ.copy()
    old_path = env.get("LEAN_PATH", "")
    env["LEAN_PATH"] = str(bench_root) + ((":" + old_path) if old_path else "")
    times = [run(lake_env_prefix(repo) + [str(path)], repo, env=env) for _ in range(runs)]
    return TimedRun(variant, times)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="repository root")
    parser.add_argument("--size", type=int, default=200, help="number of prior LF definitions")
    parser.add_argument("--runs", type=int, default=3, help="runs per downstream variant")
    args = parser.parse_args()

    repo = args.repo.resolve()
    bench_root = repo / ".lake" / "build" / "internallean-cache-bench"
    compile_base(repo, bench_root, args.size)
    for variant in ["import-only", "admitted", "checked"]:
        result = time_variant(repo, bench_root, args.size, variant, args.runs)
        print(f"{variant:11s} median={result.median:8.3f}s times={result.times}")


if __name__ == "__main__":
    main()
