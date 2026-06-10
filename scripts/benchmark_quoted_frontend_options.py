#!/usr/bin/env python3
"""Compare InternalLean opt-in frontend/mirror options on generated fixtures.

This script is a diagnostic benchmark, not a deterministic CI test.  It generates small Lean files,
runs ``lake env lean`` under several option sets, and reports median wall-clock ratios.  The cases
are chosen to answer two common questions:

* do quoted/mirror opt-ins help on large structural ``Sigma``/``Pi`` bodies?
* how much overhead does prefer mode add on many small declarations or legacy structural syntax?

Interpretation notes:

* ``legacy-*`` cases use ordinary ``ttExpr`` structural syntax.  Quoted prefer mode may fall back to
  the legacy frontend on these fields; this measures fallback overhead.
* ``quoted-*`` cases use explicit ``InternalLean.LFQuote`` constructor names such as ``sigma`` and
  ``funArrowDep``.  These cases require the quoted theory-block frontend, so there is no direct
  opt-out run for exactly the same source text.
* ``mirror-fast`` estimates the body-check fast path with LF fallback on mirror failures.
  ``mirror-compare`` and ``global-compare`` intentionally also run LF checking for comparison, so
  they are expected to cost more.
* ``--parent-counts`` adds paired files that compare declaring a child theory with
  ``extends BigParent`` against incrementally reopening the big parent with ``extend_type_theory``.
"""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / ".lake" / "build" / "internallean-bench" / "quoted-options"

MODE_OPTIONS: dict[str, list[str]] = {
    "off": [],
    "quoted-theory": ["-DinternalLean.preferLeanQuotedTheoryBlocks=true"],
    "quoted-strict-theory": ["-DinternalLean.requireLeanQuotedTheoryBlocks=true"],
    "quoted-internal": ["-DinternalLean.preferLeanQuotedFrontend=true"],
    "mirror-fast": ["-DinternalLean.mirrorBackend.checkTheoryBodies=true"],
    "mirror-compare": [
        "-DinternalLean.mirrorBackend.checkTheoryBodies=true",
        "-DinternalLean.mirrorBackend.compareTheoryBodiesWithLF=true",
    ],
    "global-fast": [
        "-DinternalLean.preferLeanQuotedFrontend=true",
        "-DinternalLean.preferLeanQuotedTheoryBlocks=true",
        "-DinternalLean.mirrorBackend.checkTheoryBodies=true",
    ],
    "global-compare": [
        "-DinternalLean.preferLeanQuotedFrontend=true",
        "-DinternalLean.preferLeanQuotedTheoryBlocks=true",
        "-DinternalLean.mirrorBackend.compareWithLF=true",
        "-DinternalLean.mirrorBackend.checkTheoryBodies=true",
        "-DinternalLean.mirrorBackend.compareTheoryBodiesWithLF=true",
    ],
}

LEGACY_MODES = [
    "off",
    "quoted-theory",
    "mirror-fast",
    "mirror-compare",
    "global-fast",
    "global-compare",
]
QUOTED_THEORY_MODES = ["quoted-theory", "quoted-strict-theory", "global-fast"]
INTERNAL_MODES = ["off", "quoted-internal", "global-fast", "global-compare"]


@dataclass(frozen=True)
class Case:
    name: str
    size: int
    source: str
    modes: list[str]
    baseline_mode: str | None = "off"


@dataclass
class RunResult:
    seconds: float
    returncode: int
    stdout_bytes: int
    stderr_bytes: int
    olean_bytes: int
    ilean_bytes: int
    output_tail: str = ""


@dataclass
class CaseModeResult:
    case: str
    size: int
    mode: str
    times: list[float]
    warnings: int
    olean_bytes: int
    ilean_bytes: int

    @property
    def median(self) -> float:
        return statistics.median(self.times)

    def to_json(self) -> dict[str, object]:
        return {
            "case": self.case,
            "size": self.size,
            "mode": self.mode,
            "times": self.times,
            "median": self.median,
            "warnings": self.warnings,
            "olean_bytes": self.olean_bytes,
            "ilean_bytes": self.ilean_bytes,
        }


def nested_legacy_sigma(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"Σ x{i:03d} : Obj, {body}"
    return body


def nested_legacy_pi(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"(x{i:03d} : Obj) → {body}"
    return body


def nested_legacy_lf_arrow(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"(x{i:03d} : Obj) ⇒ {body}"
    return body


def nested_quoted_sigma(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"sigma Obj (fun x{i:03d} => {body})"
    return body


def nested_quoted_pi(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"funArrowDep Obj (fun x{i:03d} => {body})"
    return body


def nested_quoted_lf_arrow(depth: int) -> str:
    body = "Obj"
    for i in range(depth - 1, -1, -1):
        body = f"arrowDep Obj (fun x{i:03d} => {body})"
    return body


def sanitize_name(text: str) -> str:
    out = "".join(ch if ch.isalnum() else "_" for ch in text)
    return out.strip("_") or "Case"


def theory_with_syntax_defs(theory: str, body: str, repeats: int) -> str:
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory} where",
        "  syntax_sort Obj : Type",
    ]
    for i in range(repeats):
        lines.append(f"  syntax_def Big{i:03d} : Type := {body}")
    lines.append("")
    return "\n".join(lines)


def nested_pair_value(depth: int) -> str:
    body = "o"
    for _ in range(depth):
        body = f"⟨o, {body}⟩"
    return body


def nested_lambda_value(depth: int) -> str:
    binders = " ".join(f"x{i:03d}" for i in range(depth))
    return f"fun {binders} => o" if binders else "o"


def theory_with_object_defs(theory: str, type_expr: str, value: str, repeats: int) -> str:
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
    ]
    for i in range(repeats):
        lines.append(f"  lf_def d{i:03d} : {type_expr} := {value}")
    lines.append("")
    return "\n".join(lines)


def many_simple_theory(theory: str, count: int) -> str:
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
    ]
    for i in range(count):
        lines.append(f"  lf_opaque c{i:04d} : Obj")
        lines.append(f"  lf_def d{i:04d} : Obj := c{i:04d}")
    lines.append("")
    return "\n".join(lines)


def many_internal_defs(theory: str, count: int) -> str:
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {theory} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
        "",
        f"namespace {theory}",
        "",
    ]
    for i in range(count):
        lines.append(f"internal def d{i:04d} : Obj := o")
    lines.extend(["", f"#check d{count - 1:04d}", "", f"end {theory}", ""])
    return "\n".join(lines)


def parent_chain_source(parent: str, count: int, operation: str) -> str:
    last = f"d{count:04d}"
    lines = [
        "import InternalLean.Command",
        "",
        "open InternalLean",
        "set_option maxHeartbeats 0",
        "",
        f"declare_type_theory {parent} where",
        "  syntax_sort Obj",
        "  lf_opaque o : Obj",
        "  lf_def d0000 : Obj := o",
    ]
    for i in range(1, count + 1):
        lines.append(f"  lf_def d{i:04d} : Obj := d{i - 1:04d}")
    lines.append("")
    if operation == "child":
        child = parent + "Child"
        lines.extend(
            [
                f"declare_type_theory {child} extends {parent} where",
                f"  lf_def child : Obj := {last}",
                "",
            ]
        )
    elif operation == "extend":
        lines.extend(
            [
                f"extend_type_theory {parent} where",
                f"  lf_def child : Obj := {last}",
                "",
            ]
        )
    else:
        raise ValueError(f"unknown parent-chain operation: {operation}")
    return "\n".join(lines)


def make_structural_cases(depths: list[int], repeats: int) -> list[Case]:
    specs: list[tuple[str, Callable[[int], str], list[str], str | None]] = [
        ("syntax-def-legacy-sigma", nested_legacy_sigma, LEGACY_MODES, "off"),
        ("syntax-def-legacy-pi", nested_legacy_pi, LEGACY_MODES, "off"),
        ("syntax-def-legacy-lf-arrow", nested_legacy_lf_arrow, LEGACY_MODES, "off"),
        ("syntax-def-quoted-sigma", nested_quoted_sigma, QUOTED_THEORY_MODES, "quoted-theory"),
        ("syntax-def-quoted-pi", nested_quoted_pi, QUOTED_THEORY_MODES, "quoted-theory"),
        (
            "syntax-def-quoted-lf-arrow",
            nested_quoted_lf_arrow,
            QUOTED_THEORY_MODES,
            "quoted-theory",
        ),
    ]
    cases: list[Case] = []
    for depth in depths:
        for name, body_fn, modes, baseline in specs:
            theory = "Bench" + sanitize_name(name).title().replace("_", "") + str(depth)
            source = theory_with_syntax_defs(theory, body_fn(depth), repeats)
            cases.append(
                Case(
                    name=name,
                    size=depth,
                    source=source,
                    modes=modes,
                    baseline_mode=baseline,
                )
            )
        object_specs = [
            ("object-def-sigma-pair", nested_legacy_sigma(depth), nested_pair_value(depth)),
            ("object-def-pi-lambda", nested_legacy_pi(depth), nested_lambda_value(depth)),
        ]
        for name, type_expr, value in object_specs:
            theory = "Bench" + sanitize_name(name).title().replace("_", "") + str(depth)
            source = theory_with_object_defs(theory, type_expr, value, repeats)
            cases.append(Case(name=name, size=depth, source=source, modes=LEGACY_MODES))
    return cases


def make_simple_cases(counts: list[int]) -> list[Case]:
    cases: list[Case] = []
    for count in counts:
        theory = f"BenchManySimple{count}"
        cases.append(
            Case(
                name="many-simple-theory-items",
                size=count,
                source=many_simple_theory(theory, count),
                modes=LEGACY_MODES,
            )
        )
        theory = f"BenchManyInternal{count}"
        cases.append(
            Case(
                name="many-simple-internal-defs",
                size=count,
                source=many_internal_defs(theory, count),
                modes=INTERNAL_MODES,
            )
        )
    return cases


def make_parent_extension_cases(counts: list[int]) -> list[Case]:
    cases: list[Case] = []
    for count in counts:
        parent = f"BenchBigParentChild{count}"
        cases.append(
            Case(
                name="big-parent-declare-child-extends",
                size=count,
                source=parent_chain_source(parent, count, "child"),
                modes=LEGACY_MODES,
            )
        )
        parent = f"BenchBigParentInPlace{count}"
        cases.append(
            Case(
                name="big-parent-extend-in-place",
                size=count,
                source=parent_chain_source(parent, count, "extend"),
                modes=LEGACY_MODES,
            )
        )
    return cases


def run_lean(repo: Path, path: Path, out_dir: Path, stem: str, mode: str) -> RunResult:
    olean = out_dir / f"{stem}.olean"
    ilean = out_dir / f"{stem}.ilean"
    stdout = out_dir / f"{stem}.stdout"
    stderr = out_dir / f"{stem}.stderr"
    for output in [olean, ilean, stdout, stderr]:
        output.unlink(missing_ok=True)
    cmd = [
        "lake",
        "env",
        "lean",
        *MODE_OPTIONS[mode],
        str(path),
        "-o",
        str(olean),
        "-i",
        str(ilean),
    ]
    start = time.perf_counter()
    with stdout.open("wb") as out, stderr.open("wb") as err:
        proc = subprocess.run(cmd, cwd=repo, stdout=out, stderr=err)
    elapsed = time.perf_counter() - start
    stdout_text = stdout.read_text(errors="replace") if stdout.exists() else ""
    stderr_text = stderr.read_text(errors="replace") if stderr.exists() else ""
    text = stdout_text + stderr_text
    return RunResult(
        seconds=elapsed,
        returncode=proc.returncode,
        stdout_bytes=len(stdout_text.encode()),
        stderr_bytes=len(stderr_text.encode()),
        olean_bytes=olean.stat().st_size if olean.exists() else 0,
        ilean_bytes=ilean.stat().st_size if ilean.exists() else 0,
        output_tail=text[-4000:],
    )


def benchmark_case_mode(
    repo: Path,
    out_dir: Path,
    case: Case,
    mode: str,
    runs: int,
    warmup: bool,
) -> CaseModeResult:
    stem = f"{sanitize_name(case.name)}_{case.size}_{mode.replace('-', '_')}"
    path = out_dir / f"{stem}.lean"
    path.write_text(case.source)
    if warmup:
        print(f"warmup {case.name}@{case.size} {mode}", flush=True)
        result = run_lean(repo, path, out_dir, f"{stem}_warmup", mode)
        if result.returncode != 0:
            print(result.output_tail, file=sys.stderr)
            raise SystemExit(result.returncode)
    times: list[float] = []
    warnings = 0
    olean_bytes = 0
    ilean_bytes = 0
    for i in range(runs):
        print(f"run {case.name}@{case.size} {mode} iter={i + 1}", flush=True)
        result = run_lean(repo, path, out_dir, f"{stem}_{i + 1}", mode)
        if result.returncode != 0:
            print(result.output_tail, file=sys.stderr)
            raise SystemExit(result.returncode)
        times.append(result.seconds)
        warnings = result.output_tail.count("warning:")
        olean_bytes = result.olean_bytes
        ilean_bytes = result.ilean_bytes
        print(f"  {result.seconds:.3f}s", flush=True)
    return CaseModeResult(case.name, case.size, mode, times, warnings, olean_bytes, ilean_bytes)


def classify_ratio(ratio: float) -> str:
    if ratio < 0.90:
        return "faster"
    if ratio > 1.10:
        return "slower"
    return "similar"


def print_summary(results: list[CaseModeResult], cases: list[Case]) -> None:
    by_key = {(result.case, result.size, result.mode): result for result in results}
    print("\nSummary (ratio is mode median / baseline median):")
    for case in cases:
        baseline_mode = case.baseline_mode or case.modes[0]
        baseline = by_key.get((case.name, case.size, baseline_mode))
        if baseline is None:
            baseline_mode = case.modes[0]
            baseline = by_key[(case.name, case.size, baseline_mode)]
        print(f"\n{case.name}@{case.size} baseline={baseline_mode} {baseline.median:.3f}s")
        for mode in case.modes:
            result = by_key[(case.name, case.size, mode)]
            ratio = result.median / max(baseline.median, 1e-9)
            verdict = "baseline" if mode == baseline_mode else classify_ratio(ratio)
            print(f"  {mode:22s} {result.median:8.3f}s  ratio={ratio:6.2f}  {verdict}")


def parse_ints(text: str) -> list[int]:
    return [int(part.strip()) for part in text.split(",") if part.strip()]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT, help="repository root")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--json", type=Path, help="write JSON results to this path")
    parser.add_argument("--runs", type=int, default=2)
    parser.add_argument("--no-warmup", action="store_true")
    parser.add_argument("--quick", action="store_true", help="use smaller cases and one run")
    parser.add_argument("--full", action="store_true", help="use larger structural cases")
    parser.add_argument("--struct-depths", default="")
    parser.add_argument("--struct-repeats", type=int, default=3)
    parser.add_argument("--simple-counts", default="")
    parser.add_argument(
        "--parent-counts",
        default="",
        help="comma-separated parent chain sizes for declare-extends vs extend-in-place cases",
    )
    parser.add_argument(
        "--case-filter",
        action="append",
        default=[],
        help="substring filter for case names; repeat to include several substrings",
    )
    parser.add_argument(
        "--modes",
        default="",
        help="comma-separated mode filter, e.g. off,global-fast,global-compare",
    )
    args = parser.parse_args()

    repo = args.repo.resolve()
    out_dir = args.out_dir.resolve()
    out_dir.mkdir(parents=True, exist_ok=True)

    if args.quick:
        depths = [8, 20] if not args.struct_depths else parse_ints(args.struct_depths)
        simple_counts = [20] if not args.simple_counts else parse_ints(args.simple_counts)
        runs = 1
        warmup = False
    elif args.full:
        depths = [25, 75, 150] if not args.struct_depths else parse_ints(args.struct_depths)
        simple_counts = [50, 150] if not args.simple_counts else parse_ints(args.simple_counts)
        runs = args.runs
        warmup = not args.no_warmup
    else:
        depths = [15, 50] if not args.struct_depths else parse_ints(args.struct_depths)
        simple_counts = [40] if not args.simple_counts else parse_ints(args.simple_counts)
        runs = args.runs
        warmup = not args.no_warmup

    parent_counts = parse_ints(args.parent_counts) if args.parent_counts else []
    cases = (
        make_structural_cases(depths, args.struct_repeats) +
        make_simple_cases(simple_counts) +
        make_parent_extension_cases(parent_counts)
    )
    if args.case_filter:
        filters = [part.lower() for part in args.case_filter]
        cases = [case for case in cases if any(part in case.name.lower() for part in filters)]
    if args.modes:
        selected_modes = {part.strip() for part in args.modes.split(",") if part.strip()}
        unknown = selected_modes.difference(MODE_OPTIONS)
        if unknown:
            raise SystemExit(f"unknown mode(s): {', '.join(sorted(unknown))}")
        cases = [
            Case(
                name=case.name,
                size=case.size,
                source=case.source,
                modes=[mode for mode in case.modes if mode in selected_modes],
                baseline_mode=case.baseline_mode,
            )
            for case in cases
        ]
        cases = [case for case in cases if case.modes]
    if not cases:
        raise SystemExit("no benchmark cases selected")

    results: list[CaseModeResult] = []
    for case in cases:
        for mode in case.modes:
            result = benchmark_case_mode(repo, out_dir, case, mode, runs, warmup)
            results.append(result)

    print_summary(results, cases)
    data = {
        "runs": runs,
        "warmup": warmup,
        "struct_repeats": args.struct_repeats,
        "results": [result.to_json() for result in results],
    }
    json_path = args.json or (out_dir / "results.json")
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(f"\nWrote JSON results to {json_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
