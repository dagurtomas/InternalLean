#!/usr/bin/env python3
"""Standalone raw-free structural-kernel replay benchmark.

The generated Lean source imports ``InternalLean.Kernel`` and constructs only structural
``Kernel.KTerm``/``Kernel.Judgment`` replay payloads.  It does not lower through the legacy raw
``Raw`` API or through the high-level LF frontend.  The fixture is package-shaped: rule
metavariable annotations and instantiation annotations contain nested structural Sigma packages.
"""

from __future__ import annotations

import argparse
import json
import re
import statistics
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / ".lake" / "build" / "internallean-bench" / "structural-kernel"
RESULT_RE = re.compile(
    r"STRUCTURAL_KERNEL_BENCH\s+case=(?P<case>\S+)\s+iterations=(?P<iterations>\d+)\s+"
    r"ms=(?P<ms>\d+)"
)


@dataclass
class RunResult:
    wall_seconds: float
    lean_ms: int
    stdout: str
    stderr: str


@dataclass
class BenchCase:
    name: str
    depth: int
    iterations: int
    runs: list[RunResult]

    @property
    def lean_seconds(self) -> list[float]:
        return [r.lean_ms / 1000.0 for r in self.runs]

    @property
    def median_lean_seconds(self) -> float:
        return statistics.median(self.lean_seconds)

    @property
    def median_wall_seconds(self) -> float:
        return statistics.median(r.wall_seconds for r in self.runs)

    @property
    def median_microseconds_per_check(self) -> float:
        return self.median_lean_seconds * 1_000_000.0 / self.iterations

    def to_json(self) -> dict[str, Any]:
        data = {
            "name": self.name,
            "depth": self.depth,
            "iterations": self.iterations,
            "median_lean_seconds": self.median_lean_seconds,
            "median_wall_seconds": self.median_wall_seconds,
            "median_microseconds_per_check": self.median_microseconds_per_check,
            "runs": [
                {
                    "wall_seconds": r.wall_seconds,
                    "lean_ms": r.lean_ms,
                    "lean_seconds": r.lean_ms / 1000.0,
                    "stdout": r.stdout,
                    "stderr": r.stderr,
                }
                for r in self.runs
            ],
        }
        return data


def lean_source(case_name: str, depth: int, iterations: int) -> str:
    lean_case_name = json.dumps(case_name)
    return f"""import InternalLean.Kernel

namespace InternalLeanBench.StructuralKernel

abbrev caseName : String := {lean_case_name}
abbrev packageDepth : Nat := {depth}
abbrev iterationCount : Nat := {iterations}

def kn (n : Lean.Name) : InternalLean.Kernel.KName := InternalLean.Kernel.KName.ofName n

def head (n : Lean.Name) : InternalLean.Kernel.KHead := {{ name := kn n }}

def ident (n : Lean.Name) : InternalLean.Kernel.KTerm := .ident (head n)

def objTy : InternalLean.Kernel.KTerm := ident `Obj

def packageType : Nat → InternalLean.Kernel.KTerm
  | 0 => objTy
  | n + 1 => .sigma objTy (packageType n)

def packageValue : Nat → InternalLean.Kernel.KTerm
  | 0 => ident `base
  | n + 1 => .pair (ident (Lean.Name.str `payload s!"p{{n}}")) (packageValue n)

def packageStmt (term : InternalLean.Kernel.KTerm) : InternalLean.Kernel.Judgment := {{ head := kn `Pkg, args := [term] }}

def metaX : InternalLean.Kernel.RuleMetaVar := {{
  name := kn `x
  sort := .arg
  zone? := none
  type? := some (packageType packageDepth)
  evidence? := none
}}

def ruleSchema : InternalLean.Kernel.RuleSchema := {{
  name := kn `intro
  metavariables := [metaX]
  premises := []
  sideConditions := []
  sideConditionCertificates := []
  checkedSideConditionCertificates := []
  conclusionStmt := packageStmt (.mvar (kn `x) .arg)
}}

def signature : InternalLean.Kernel.Signature := {{
  name := kn `StructuralPackageBench
  constants := []
  contextZones := []
  binderClasses := []
  conversionPlugins := []
  rules := [ruleSchema]
}}

def instantiation : InternalLean.Kernel.ScopedInstantiation := {{
  entries := [{{
    name := kn `x
    sort := .arg
    zone? := none
    type? := some (packageType packageDepth)
    evidence? := none
    value := packageValue packageDepth }}]
}}

def statement : InternalLean.Kernel.Judgment := packageStmt (packageValue packageDepth)

def derivation : InternalLean.Kernel.KernelLFDerivation :=
  .ruleApp (kn `intro) statement instantiation [] []

partial def repeatCheck : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
      match InternalLean.Kernel.CheckedKernelLFDerivation.ofDerivation signature {{}} derivation with
      | Except.ok checked =>
          match checked.check with
          | Except.ok () => pure ()
          | Except.error err => throw <| IO.userError err
      | Except.error err => throw <| IO.userError err
      repeatCheck n

#eval show IO Unit from do
  let start ← IO.monoMsNow
  repeatCheck iterationCount
  let stop ← IO.monoMsNow
  IO.println s!"STRUCTURAL_KERNEL_BENCH case={{caseName}} iterations={{iterationCount}} ms={{stop - start}}"

end InternalLeanBench.StructuralKernel
"""


def run_case(out_dir: Path, case_name: str, depth: int, iterations: int, run_id: int) -> RunResult:
    path = out_dir / f"{case_name}-{run_id}.lean"
    source = lean_source(case_name, depth, iterations)
    path.write_text(source)
    stdout_path = out_dir / f"{case_name}-{run_id}.stdout"
    stderr_path = out_dir / f"{case_name}-{run_id}.stderr"
    start = time.perf_counter()
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        proc = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=ROOT,
            stdout=stdout,
            stderr=stderr,
        )
    wall = time.perf_counter() - start
    stdout = stdout_path.read_text(errors="replace")
    stderr = stderr_path.read_text(errors="replace")
    text = stdout + stderr
    if proc.returncode != 0:
        print(text[-4000:], file=sys.stderr)
        raise SystemExit(proc.returncode)
    match = RESULT_RE.search(text)
    if not match:
        print(text[-4000:], file=sys.stderr)
        raise SystemExit(f"benchmark marker missing for {case_name}")
    got_case = match.group("case")
    got_iterations = int(match.group("iterations"))
    if got_case != case_name or got_iterations != iterations:
        raise SystemExit(
            f"benchmark marker mismatch: got {got_case}@{got_iterations}, "
            f"expected {case_name}@{iterations}"
        )
    return RunResult(
        wall_seconds=wall,
        lean_ms=int(match.group("ms")),
        stdout=str(stdout_path),
        stderr=str(stderr_path),
    )


def parse_depths(text: str) -> list[int]:
    return [int(part.strip()) for part in text.split(",") if part.strip()]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depths", default="12,24", help="comma-separated package depths")
    parser.add_argument("--iterations", type=int, default=20000)
    parser.add_argument("--runs", type=int, default=3)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--json", type=Path)
    args = parser.parse_args()

    out_dir = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    cases: list[BenchCase] = []
    for depth in parse_depths(args.depths):
        case_name = f"structural_package_{depth}x{args.iterations}"
        runs: list[RunResult] = []
        for run_id in range(args.runs):
            print(f"run {case_name} iter={run_id + 1}", flush=True)
            result = run_case(out_dir, case_name, depth, args.iterations, run_id + 1)
            runs.append(result)
            print(
                f"  lean={result.lean_ms / 1000.0:.3f}s "
                f"wall={result.wall_seconds:.3f}s",
                flush=True,
            )
        case = BenchCase(case_name, depth, args.iterations, runs)
        cases.append(case)
        print(
            f"{case.name}: median lean={case.median_lean_seconds:.3f}s "
            f"({case.median_microseconds_per_check:.2f} µs/check), "
            f"median wall={case.median_wall_seconds:.3f}s",
            flush=True,
        )

    data = {
        "benchmark": "raw-free structural kernel package replay",
        "raw_free": True,
        "kernel_api": "InternalLean.Kernel",
        "cases": [case.to_json() for case in cases],
    }
    json_path = args.json or (out_dir / "results.json")
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(data, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
