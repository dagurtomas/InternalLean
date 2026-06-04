#!/usr/bin/env python3
"""Benchmark generated model-interface elaboration for synthetic large LF signatures."""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / ".lake" / "build" / "internallean-bench"


def chunked(xs: list[str], n: int) -> list[list[str]]:
    return [xs[i : i + n] for i in range(0, len(xs), n)]


def synthetic_source(field_count: int, theory_name: str, model_name: str) -> str:
    if field_count < 1:
        raise ValueError("field_count must be positive")
    const_count = max(0, field_count - 2)
    decls = [
        f"declare_type_theory {theory_name} where",
        "  syntax_sort Obj",
        "  judgment J (x : Obj)",
    ]
    for i in range(const_count):
        decls.append(f"  lf_opaque c{i:04d} : Obj")
    for i in range(const_count):
        decls.append(f"  rule j{i:04d} : J c{i:04d}")
    checks = [f"#check {theory_name}.{model_name}"]
    if const_count:
        checks.append(f"#check {theory_name}.{model_name}.c{const_count - 1:04d}")
        checks.append(f"#check {theory_name}.{model_name}.j{const_count - 1:04d}")
    return "\n".join(
        [
            "import InternalLean.Command",
            "",
            "open InternalLean",
            "set_option maxHeartbeats 0",
            "",
            *decls,
            "",
            f"generate_model_interface {theory_name} as {model_name}",
            "",
            *checks,
            "",
        ]
    )


def run_lean(path: Path, out_dir: Path, stem: str) -> dict[str, Any]:
    olean = out_dir / f"{stem}.olean"
    ilean = out_dir / f"{stem}.ilean"
    stdout = out_dir / f"{stem}.stdout"
    stderr = out_dir / f"{stem}.stderr"
    for p in [olean, ilean, stdout, stderr]:
        try:
            p.unlink()
        except FileNotFoundError:
            pass
    cmd = ["lake", "env", "lean", str(path), "-o", str(olean), "-i", str(ilean)]
    start = time.perf_counter()
    with stdout.open("wb") as out, stderr.open("wb") as err:
        proc = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=err)
    elapsed = time.perf_counter() - start
    result: dict[str, Any] = {
        "seconds": elapsed,
        "returncode": proc.returncode,
        "olean_bytes": olean.stat().st_size if olean.exists() else 0,
        "ilean_bytes": ilean.stat().st_size if ilean.exists() else 0,
        "stdout": str(stdout),
        "stderr": str(stderr),
    }
    if proc.returncode != 0:
        result["stderr_tail"] = stderr.read_text(errors="replace")[-4000:]
    return result


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    seconds = [float(r["seconds"]) for r in rows]
    return {
        "runs": len(rows),
        "mean_seconds": statistics.mean(seconds),
        "median_seconds": statistics.median(seconds),
        "min_seconds": min(seconds),
        "max_seconds": max(seconds),
        "mean_olean_bytes": statistics.mean(int(r["olean_bytes"]) for r in rows),
        "mean_ilean_bytes": statistics.mean(int(r["ilean_bytes"]) for r in rows),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", default="80,200,500", help="comma-separated field counts")
    parser.add_argument("--runs", type=int, default=3, help="measured runs per size")
    parser.add_argument("--no-warmup", action="store_true", help="skip one warmup run per size")
    parser.add_argument("--json", type=Path, help="write JSON results to this path")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT, help="output directory")
    args = parser.parse_args()

    sizes = [int(s.strip()) for s in args.sizes.split(",") if s.strip()]
    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    all_results: dict[str, Any] = {"sizes": {}, "runs": args.runs}

    for size in sizes:
        theory_name = f"LargeModelBenchmark{size}"
        model_name = "LargeModel"
        lean_path = out_dir / f"large_model_{size}.lean"
        lean_path.write_text(synthetic_source(size, theory_name, model_name))
        if not args.no_warmup:
            print(f"warmup size={size}", flush=True)
            warmup = run_lean(lean_path, out_dir, f"large_model_{size}_warmup")
            if warmup["returncode"] != 0:
                print(warmup.get("stderr_tail", ""))
                return int(warmup["returncode"])
        rows: list[dict[str, Any]] = []
        for i in range(args.runs):
            print(f"run size={size} iter={i + 1}", flush=True)
            row = run_lean(lean_path, out_dir, f"large_model_{size}_{i + 1}")
            if row["returncode"] != 0:
                print(row.get("stderr_tail", ""))
                return int(row["returncode"])
            rows.append(row)
            print(
                f"  {row['seconds']:.3f}s olean={row['olean_bytes']} "
                f"ilean={row['ilean_bytes']}",
                flush=True,
            )
        all_results["sizes"][str(size)] = {"summary": summarize(rows), "rows": rows}

    text = json.dumps(all_results, indent=2, sort_keys=True)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
