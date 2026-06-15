#!/usr/bin/env python3
"""Wall-clock smoke benchmark for compiled incremental LF checker caches.

The benchmark builds a synthetic base theory once, then times downstream files that import the
compiled base module.  It is intended for local performance checks, not CI-grade absolute timing
assertions.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

DEFAULT_VARIANTS = [
    "import-only",
    "admitted",
    "checked",
    "checked-obj",
    "checked-obj-10-top",
    "checked-obj-10-batch",
]


@dataclass
class TimedRun:
    size: int
    label: str
    times: list[float]

    @property
    def median(self) -> float:
        return statistics.median(self.times)

    def to_json(self) -> dict[str, object]:
        return {
            "size": self.size,
            "variant": self.label,
            "median": round(self.median, 6),
            "times": [round(t, 6) for t in self.times],
        }


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


def downstream_body(variant: str) -> list[str]:
    if variant == "import-only":
        return []
    if variant == "admitted":
        return ["internal theorem cache_admitted : J base := sorry"]
    if variant == "checked":
        return ["internal theorem cache_checked : J base := imported"]
    if variant == "checked-obj":
        return ["internal def cache_obj : Obj := base"]
    if variant == "checked-obj-10-top":
        return [f"internal def cache_obj_{i:02d} : Obj := base" for i in range(10)]
    if variant == "checked-obj-10-batch":
        return ["internal_defs where"] + [
            f"  def cache_obj_{i:02d} : Obj := base" for i in range(10)
        ]
    raise ValueError(variant)


def downstream_source(size: int, variant: str, profile: bool) -> str:
    header = [f"import InternalLeanCacheBench.Base{size}"]
    if profile:
        header.extend([
            "set_option internalLean.profileInternalDef true",
            "set_option internalLean.profileLFCheckPhases true",
        ])
    header.append(f"namespace BenchIncrementalCache{size}")
    footer = [f"end BenchIncrementalCache{size}"]
    return "\n".join(header + downstream_body(variant) + footer) + "\n"


def run(
    cmd: list[str],
    repo: Path,
    env: dict[str, str] | None = None,
    show_output: bool = False,
) -> float:
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
    if show_output and proc.stdout:
        print(proc.stdout, end="" if proc.stdout.endswith("\n") else "\n")
    if proc.returncode != 0:
        print(proc.stdout, file=sys.stderr)
        raise SystemExit(f"command failed: {' '.join(cmd)}")
    return elapsed


def lake_env_prefix(_repo: Path) -> list[str]:
    return ["lake", "env", "lean"]


def compile_base(repo: Path, bench_root: Path, size: int) -> None:
    module_dir = bench_root / "InternalLeanCacheBench"
    module_dir.mkdir(parents=True, exist_ok=True)
    source = module_dir / f"Base{size}.lean"
    source.write_text(base_source(size))
    run(
        lake_env_prefix(repo) + [
            str(source),
            "-o",
            str(source.with_suffix(".olean")),
            "-i",
            str(source.with_suffix(".ilean")),
        ],
        repo,
    )


def time_variant(
    repo: Path,
    bench_root: Path,
    size: int,
    variant: str,
    runs: int,
    profile: bool,
    show_output: bool,
) -> TimedRun:
    module_dir = bench_root / "InternalLeanCacheBench"
    path = module_dir / f"Downstream{size}_{variant.replace('-', '_')}.lean"
    path.write_text(downstream_source(size, variant, profile))
    env = os.environ.copy()
    old_path = env.get("LEAN_PATH", "")
    env["LEAN_PATH"] = str(bench_root) + ((":" + old_path) if old_path else "")
    times = [
        run(lake_env_prefix(repo) + [str(path)], repo, env=env, show_output=show_output)
        for _ in range(runs)
    ]
    return TimedRun(size, variant, times)


def parse_csv_ints(value: str) -> list[int]:
    out = []
    for part in value.split(","):
        part = part.strip()
        if part:
            out.append(int(part))
    if not out:
        raise argparse.ArgumentTypeError("expected at least one size")
    return out


def parse_variants(value: str) -> list[str]:
    variants = DEFAULT_VARIANTS if value == "all" else [v.strip() for v in value.split(",")]
    variants = [v for v in variants if v]
    unknown = [v for v in variants if v not in DEFAULT_VARIANTS]
    if unknown:
        raise argparse.ArgumentTypeError(f"unknown variant(s): {', '.join(unknown)}")
    return variants


def format_times(times: list[float]) -> str:
    return "[" + ", ".join(f"{t:.3f}" for t in times) + "]"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="repository root")
    parser.add_argument("--size", type=int, default=200, help="single size to benchmark")
    parser.add_argument("--sizes", type=parse_csv_ints, help="comma-separated sizes to benchmark")
    parser.add_argument("--runs", type=int, default=3, help="runs per downstream variant")
    parser.add_argument("--variants", type=parse_variants, default=DEFAULT_VARIANTS)
    parser.add_argument("--json", type=Path, help="write machine-readable benchmark results")
    parser.add_argument("--profile", action="store_true", help="enable bounded Lean profile output")
    parser.add_argument("--show-output", action="store_true", help="print successful Lean output")
    args = parser.parse_args()

    repo = args.repo.resolve()
    bench_root = repo / ".lake" / "build" / "internallean-cache-bench"
    sizes = args.sizes if args.sizes is not None else [args.size]
    variants = args.variants
    results: list[TimedRun] = []
    for size in sizes:
        compile_base(repo, bench_root, size)
        for variant in variants:
            result = time_variant(
                repo,
                bench_root,
                size,
                variant,
                args.runs,
                args.profile,
                args.show_output,
            )
            results.append(result)
            print(
                f"size={size:<5d} {variant:22s} median={result.median:8.3f}s "
                f"times={format_times(result.times)}"
            )
    if args.json is not None:
        payload = {
            "schema": "internallean-incremental-cache-benchmark-v2",
            "runs": args.runs,
            "profile": args.profile,
            "variants": variants,
            "results": [result.to_json() for result in results],
        }
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
