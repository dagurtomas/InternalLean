# Examples and tests guide

This document explains the current example and regression files in the `InternalLean` repository.
The test suite is organized as a separate `InternalLeanTest` library, similar to a Mathlib-style
test tree.

## How to read examples

Most examples use:

```lean
import InternalLean.Command
```

or a module-style public import. They declare a type theory with `declare_type_theory`, add
internal declarations with `internal def`, and sometimes generate model interfaces or transports.

Start with TinyNat, then use the focused regression files when changing a particular subsystem.

## Intro exercises

File:

- `Examples/IntroExercises.lean`
- `Examples/IntroExercisesHints.lean`
- `Examples/IntroExercisesSolutions.lean`

A standalone exercise sheet for first-time users. It declares a tiny reachability type theory,
asks the reader to fill `internal def` proofs, and separates hints and worked solutions. The
solutions file also shows the generated model-interface and transport workflow on a trivial Lean
model.

## TinyNat

Files:

- `InternalLeanTest/TinyNat.lean`
- `InternalLeanTest/TinyNatModel.lean`
- `InternalLeanTest/NaturalNumbersTest.lean`
- `InternalLeanTest/EndToEndTinyNatTest.lean`

TinyNat is the smallest direct-LF arithmetic example. It declares object-level natural-number
syntax, wellformedness, conversion, primitive recursion, and internal equality proof objects.

It is useful for learning:

- `syntax_sort`, `judgment`, `lf_opaque`, and `rule`;
- `judgment_role` and `rule_role` metadata;
- computation rules for object `rw` and `simp`;
- internal declarations and tactic proofs;
- generated model-interface workflow over Lean `Nat`.

## Internal tactic tests

File:

- `InternalLeanTest/InternalTacticTest.lean`

This is the best place to see small internal tactic examples. It contains focused tests for
`exact`, `apply`, `assumption`, `show`, `change`, `rw`, `simp`, conversion plugins, fuel
diagnostics, and generated model transports for tactic-proved declarations.

## API and metadata tests

Files:

- `InternalLeanTest/APIExtensionTest.lean`
- `InternalLeanTest/LogicalFrameworkMetadataExamplesTest.lean`
- `InternalLeanTest/ModelWorkflowUXTest.lean`
- `InternalLeanTest/TransportPlanTest.lean`
- `InternalLeanTest/LFModelStressTest.lean`

These files are useful when changing frontend syntax, metadata validation, diagnostics, or model
workflow behavior. They include malformed metadata diagnostics, role validation, rewrite/transport
metadata, public/minimal model interfaces, generated transport signatures, and synthetic generated
interface stress cases.

## Useful builds

Library check:

```bash
lake build InternalLean
```

Test-library check:

```bash
lake build InternalLeanTest
```

Focused checks:

```bash
lake build InternalLean.Command InternalLeanTest.APIExtensionTest
lake build InternalLeanTest.InternalTacticTest
lake build InternalLeanTest.TinyNat InternalLeanTest.TinyNatModel
lake build InternalLeanTest.EndToEndTinyNatTest
```

## Example-specific caution

Examples should guide generic design but should not become core assumptions. If an example needs a
new feature, first ask whether it can be expressed using generic LF vocabulary:

- syntax sorts;
- judgments;
- rules and premises;
- context zones and binder classes;
- side-condition certificates;
- conversion plugins;
- rewrite and transport metadata;
- model-interface metadata;
- theory-local notation or macros.

Only add a new core primitive when the generic vocabulary is insufficient.
