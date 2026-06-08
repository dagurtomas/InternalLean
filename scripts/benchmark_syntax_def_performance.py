#!/usr/bin/env python3
"""Benchmark checker and model-generation costs for ``syntax_def`` declarations."""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import time
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / ".lake" / "build" / "internallean-bench" / "syntax-def"


def checked_type_source(kind: str, count: int) -> str:
    theory_name = f"SyntaxDefCheckBench{kind}{count}"
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory_name} where",
        "  syntax_sort Obj",
    ]
    for i in range(count):
        if kind == "Sort":
            lines.append(f"  syntax_sort P{i:04d}")
        elif kind == "Admitted":
            lines.append(f"  syntax_def P{i:04d} : Type := sorry")
        elif kind == "Checked":
            lines.append(f"  syntax_def P{i:04d} : Type := Obj")
        else:
            raise ValueError(f"unknown kind: {kind}")
    lines.extend(["", f"#check_type_theory {theory_name}", ""])
    return "\n".join(lines)


def model_source(kind: str, fields: int) -> str:
    theory_name = f"SyntaxDefModelBench{kind}{fields}"
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory_name} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
    ]
    if kind == "Sort":
        lines.append("  syntax_sort P (x : Obj) : Type")
    elif kind == "Admitted":
        lines.append("  syntax_def P (x : Obj) : Type := sorry")
    elif kind == "Checked":
        lines.append("  syntax_def P (x : Obj) : Type := Obj")
    else:
        raise ValueError(f"unknown kind: {kind}")
    for i in range(fields):
        lines.append(f"  lf_opaque c{i:04d} : P o")
    lines.extend(
        [
            "",
            f"generate_model_interface {theory_name} as {theory_name}Model",
            "",
            f"#check {theory_name}.{theory_name}Model.c{fields - 1:04d}",
            "",
        ]
    )
    return "\n".join(lines)


def nested_sigma_type(families: int) -> str:
    body = f"P{families - 1} o"
    for i in range(families - 2, -1, -1):
        body = f"Σ p{i} : P{i} o, {body}"
    return body


def package_type(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"Σ x{i} : Obj, {body}"
    return body


def package_admission_source(kind: str, depth: int, admissions: int) -> str:
    theory_name = f"SyntaxDefPackageAdmissionBench{kind}{depth}x{admissions}"
    body = package_type(depth)
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory_name} where",
        "  syntax_sort Obj : Type",
        f"  syntax_abbrev Big := {body}",
    ]
    if kind == "Abbrev":
        type_name = "Big"
    elif kind == "CheckedDef":
        lines.append("  syntax_def BigDef : Type := Big")
        type_name = "BigDef"
    elif kind == "AdmittedDef":
        lines.append("  syntax_def BigDef : Type := sorry")
        type_name = "BigDef"
    else:
        raise ValueError(f"unknown kind: {kind}")
    lines.extend(["", f"namespace {theory_name}", "", "internal_defs where"])
    for i in range(admissions):
        lines.append(f"  def admitted{i:04d} : {type_name} := sorry")
    lines.extend(["", f"#check admitted{admissions - 1:04d}", "", f"end {theory_name}", ""])
    return "\n".join(lines)


def multi_model_source(kind: str, families: int, fields: int) -> str:
    theory_name = f"SyntaxDefMultiModelBench{kind}{families}x{fields}"
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory_name} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
    ]
    for i in range(families):
        if kind == "Sort":
            lines.append(f"  syntax_sort P{i} (x : Obj) : Type")
        elif kind == "Admitted":
            lines.append(f"  syntax_def P{i} (x : Obj) : Type := sorry")
        elif kind == "Checked":
            lines.append(f"  syntax_def P{i} (x : Obj) : Type := Obj")
        else:
            raise ValueError(f"unknown kind: {kind}")
    field_type = nested_sigma_type(families)
    for i in range(fields):
        lines.append(f"  lf_opaque c{i:04d} : {field_type}")
    lines.extend(
        [
            "",
            f"generate_model_interface {theory_name} as {theory_name}Model",
            "",
            f"#check {theory_name}.{theory_name}Model.c{fields - 1:04d}",
            "",
        ]
    )
    return "\n".join(lines)


def run_lean(path: Path, out_dir: Path, stem: str) -> dict[str, Any]:
    olean = out_dir / f"{stem}.olean"
    ilean = out_dir / f"{stem}.ilean"
    stdout = out_dir / f"{stem}.stdout"
    stderr = out_dir / f"{stem}.stderr"
    for out in [olean, ilean, stdout, stderr]:
        try:
            out.unlink()
        except FileNotFoundError:
            pass
    cmd = ["lake", "env", "lean", str(path), "-o", str(olean), "-i", str(ilean)]
    start = time.perf_counter()
    with stdout.open("wb") as out, stderr.open("wb") as err:
        proc = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=err)
    elapsed = time.perf_counter() - start
    stdout_text = stdout.read_text(errors="replace") if stdout.exists() else ""
    stderr_text = stderr.read_text(errors="replace") if stderr.exists() else ""
    text = stdout_text + stderr_text
    result: dict[str, Any] = {
        "seconds": elapsed,
        "returncode": proc.returncode,
        "warnings": text.count("warning:"),
        "stdout_bytes": len(stdout_text.encode()),
        "stderr_bytes": len(stderr_text.encode()),
        "olean_bytes": olean.stat().st_size if olean.exists() else 0,
        "ilean_bytes": ilean.stat().st_size if ilean.exists() else 0,
        "stdout": str(stdout),
        "stderr": str(stderr),
    }
    if proc.returncode != 0:
        result["output_tail"] = text[-4000:]
    return result


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    seconds = [float(row["seconds"]) for row in rows]
    return {
        "runs": len(rows),
        "mean_seconds": statistics.mean(seconds),
        "median_seconds": statistics.median(seconds),
        "min_seconds": min(seconds),
        "max_seconds": max(seconds),
        "warnings": rows[0]["warnings"],
        "mean_olean_bytes": statistics.mean(int(row["olean_bytes"]) for row in rows),
        "mean_ilean_bytes": statistics.mean(int(row["ilean_bytes"]) for row in rows),
    }


def benchmark_case(
    out_dir: Path,
    case_name: str,
    source: str,
    runs: int,
    warmup: bool,
) -> dict[str, Any]:
    path = out_dir / f"{case_name}.lean"
    path.write_text(source)
    if warmup:
        print(f"warmup {case_name}", flush=True)
        warmup_result = run_lean(path, out_dir, f"{case_name}_warmup")
        if warmup_result["returncode"] != 0:
            print(warmup_result.get("output_tail", ""))
            raise SystemExit(int(warmup_result["returncode"]))
    rows: list[dict[str, Any]] = []
    for i in range(runs):
        print(f"run {case_name} iter={i + 1}", flush=True)
        row = run_lean(path, out_dir, f"{case_name}_{i + 1}")
        if row["returncode"] != 0:
            print(row.get("output_tail", ""))
            raise SystemExit(int(row["returncode"]))
        rows.append(row)
        print(f"  {row['seconds']:.3f}s warnings={row['warnings']}", flush=True)
    return {"summary": summarize(rows), "rows": rows}


def parse_ints(text: str) -> list[int]:
    return [int(part.strip()) for part in text.split(",") if part.strip()]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-sizes", default="50,150,300,600")
    parser.add_argument("--model-sizes", default="20,80,200")
    parser.add_argument("--multi", default="3x200,6x200", help="families x fields list")
    parser.add_argument(
        "--package-depths",
        default="",
        help="optional nested package depths for Abbrev/CheckedDef/AdmittedDef admission cases",
    )
    parser.add_argument("--package-admissions", type=int, default=5)
    parser.add_argument("--runs", type=int, default=2)
    parser.add_argument("--no-warmup", action="store_true")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    warmup = not args.no_warmup
    results: dict[str, Any] = {"cases": {}, "runs": args.runs}

    for size in parse_ints(args.check_sizes):
        for kind in ["Sort", "Admitted", "Checked"]:
            case = f"check_{kind}_{size}"
            results["cases"][case] = benchmark_case(
                out_dir, case, checked_type_source(kind, size), args.runs, warmup
            )

    for size in parse_ints(args.model_sizes):
        for kind in ["Sort", "Admitted", "Checked"]:
            case = f"model_{kind}_{size}"
            results["cases"][case] = benchmark_case(
                out_dir, case, model_source(kind, size), args.runs, warmup
            )

    for item in [part.strip() for part in args.multi.split(",") if part.strip()]:
        families_text, fields_text = item.lower().split("x", 1)
        families = int(families_text)
        fields = int(fields_text)
        for kind in ["Sort", "Admitted", "Checked"]:
            case = f"multi_{kind}_{families}x{fields}"
            results["cases"][case] = benchmark_case(
                out_dir,
                case,
                multi_model_source(kind, families, fields),
                args.runs,
                warmup,
            )

    for depth in parse_ints(args.package_depths):
        for kind in ["Abbrev", "CheckedDef", "AdmittedDef"]:
            case = f"package_{kind}_{depth}x{args.package_admissions}"
            results["cases"][case] = benchmark_case(
                out_dir,
                case,
                package_admission_source(kind, depth, args.package_admissions),
                args.runs,
                warmup,
            )

    text = json.dumps(results, indent=2, sort_keys=True)
    json_path = args.json or (out_dir / "results.json")
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(text + "\n")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
