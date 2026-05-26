#!/usr/bin/env python3
"""Wall-clock smoke benchmarks for InternalLean direct-LF checker scaling.

The normal Lean test suite checks deterministic correctness. This script is intended for local or
scheduled runs before merging checker-hardening work. It generates temporary Lean files, runs
`lake env lean`, and fails on broad scaling regressions rather than machine-specific absolute
microbenchmarks.
"""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path


@dataclass
class BenchResult:
    fixture: str
    size: int
    times: list[float]

    @property
    def median(self) -> float:
        return statistics.median(self.times)

    def to_json(self) -> dict[str, object]:
        data = asdict(self)
        data["median"] = self.median
        return data


def def_chain_source(size: int) -> str:
    lines = [
        "import InternalLean.Command",
        "open InternalLean",
        f"declare_type_theory BenchDefChain{size} where",
        "  syntax_sort Obj",
        "  lf_opaque base : Obj",
        "  lf_def d000 : Obj := base",
    ]
    for i in range(1, size + 1):
        lines.append(f"  lf_def d{i:03d} : Obj := d{i - 1:03d}")
    lines.append(f"#check_type_theory BenchDefChain{size}")
    return "\n".join(lines) + "\n"


def theorem_chain_source(size: int) -> str:
    lines = [
        "import InternalLean.Command",
        "open InternalLean",
        f"declare_type_theory BenchTheoremChain{size} where",
        "  syntax_sort Obj",
        "  judgment J (x : Obj)",
        "  lf_opaque base : Obj",
        "  rule intro (x : Obj) : J x",
        "  judgment_theorem t000 : J base := intro base",
    ]
    for i in range(1, size + 1):
        lines.append(f"  judgment_theorem t{i:03d} : J base := t{i - 1:03d}")
    lines.append(f"#check_type_theory BenchTheoremChain{size}")
    return "\n".join(lines) + "\n"


def indexed_grid_source(size: int) -> str:
    lines = [
        "import InternalLean.Command",
        "open InternalLean",
        f"declare_type_theory BenchIndexedGrid{size} where",
        "  syntax_sort Ctx",
        "  syntax_sort Ty (Γ : Ctx)",
        "  judgment J (Γ : Ctx) (A : Ty Γ)",
        "  lf_opaque mkTy (Γ : Ctx) : Ty Γ",
    ]
    for i in range(size):
        lines.append(f"  lf_opaque c{i:03d} : Ctx")
    for i in range(size):
        lines.append(f"  rule r{i:03d} : J c{i:03d} (mkTy c{i:03d})")
    lines.append(f"#check_type_theory BenchIndexedGrid{size}")
    return "\n".join(lines) + "\n"


FIXTURES = {
    "def-chain": def_chain_source,
    "theorem-chain": theorem_chain_source,
    "indexed-grid": indexed_grid_source,
}


def run_lean(repo: Path, source: str, fixture: str, size: int, run_id: int) -> float:
    bench_dir = repo / ".lake" / "build" / "internallean-bench"
    bench_dir.mkdir(parents=True, exist_ok=True)
    path = bench_dir / f"{fixture}-{size}-{run_id}.lean"
    path.write_text(source)
    start = time.perf_counter()
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=repo,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    elapsed = time.perf_counter() - start
    if proc.returncode != 0:
        print(proc.stdout, file=sys.stderr)
        raise SystemExit(f"benchmark fixture {fixture}@{size} failed")
    return elapsed


def benchmark_fixture(repo: Path, fixture: str, size: int, runs: int, warmup: bool) -> BenchResult:
    source = FIXTURES[fixture](size)
    if warmup:
        run_lean(repo, source, fixture, size, -1)
    times = [run_lean(repo, source, fixture, size, i) for i in range(runs)]
    return BenchResult(fixture=fixture, size=size, times=times)


def check_scaling(results: list[BenchResult], max_ratio: float, allowance: float) -> list[str]:
    failures: list[str] = []
    by_fixture: dict[str, list[BenchResult]] = {}
    for result in results:
        by_fixture.setdefault(result.fixture, []).append(result)
    for fixture, rs in by_fixture.items():
        rs.sort(key=lambda r: r.size)
        for prev, cur in zip(rs, rs[1:]):
            adjusted_prev = max(prev.median, allowance)
            ratio = cur.median / adjusted_prev
            if ratio > max_ratio:
                failures.append(
                    f"{fixture}: size {prev.size}->{cur.size} ratio {ratio:.2f} "
                    f"exceeds {max_ratio:.2f} (medians {prev.median:.3f}s->{cur.median:.3f}s)"
                )
    return failures


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--quick", action="store_true", help="run quick local benchmark sizes")
    parser.add_argument("--full", action="store_true", help="run larger pre-release sizes")
    parser.add_argument("--json", type=Path, help="write JSON results to this path")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="repository root")
    args = parser.parse_args()

    if args.full:
        sizes = [50, 100, 200, 400]
        runs = 3
        max_ratio = 3.0
    else:
        sizes = [25, 50, 100]
        runs = 1 if args.quick else 3
        max_ratio = 3.5

    repo = args.repo.resolve()
    results: list[BenchResult] = []
    for fixture in FIXTURES:
        for size in sizes:
            result = benchmark_fixture(repo, fixture, size, runs=runs, warmup=(runs > 1))
            results.append(result)
            print(f"{fixture:14s} n={size:4d} median={result.median:8.3f}s times={result.times}")

    data = [r.to_json() for r in results]
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(data, indent=2) + "\n")

    failures = check_scaling(results, max_ratio=max_ratio, allowance=0.25)
    if failures:
        print("\nPotential checker scaling regression:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
