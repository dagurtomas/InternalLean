# Examples and tests guide

This document explains the example files and regression tests in the `InternalLean` repository.
Use it to find a small file to read before trying a larger theory.

## How to read examples

Most examples import the public command surface:

```lean
import InternalLean.Command
```

They declare a type theory with `declare_type_theory`, add internal declarations with
`internal def`, and sometimes generate model interfaces or transports. Start with the intro
exercises or TinyNat, then use the focused regression files when you want to see a particular
feature in isolation.

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

TinyNat is the smallest direct-LF arithmetic example. It declares internal natural-number syntax,
wellformedness, conversion, primitive recursion, and internal equality proof terms.

It is useful for learning:

- `syntax_sort`, `judgment`, `lf_opaque`, and `rule`;
- `judgment_role` and `rule_role` metadata;
- computation rules for internal `rw` and `simp`;
- internal declarations and tactic proofs;
- generated model-interface workflow over Lean `Nat`.

## Internal tactic tests

File:

- `InternalLeanTest/InternalTacticTest.lean`

This is the best place to see small internal tactic examples. It contains focused tests for
`exact`, `apply`, `assumption`, `show`, `change`, `rw`, `simp`, conversion plugins, fuel
diagnostics, and generated model transports for tactic-proved declarations.

## API, metadata, and workflow tests

Files:

- `InternalLeanTest/APIExtensionTest.lean`
- `InternalLeanTest/LogicalFrameworkMetadataExamplesTest.lean`
- `InternalLeanTest/ModelWorkflowUXTest.lean`
- `InternalLeanTest/TransportPlanTest.lean`
- `InternalLeanTest/LFModelStressTest.lean`
- `InternalLeanTest/ModelStructuralEquivTest.lean`
- `InternalLeanTest/ModelUniverseLevelsTest.lean`
- `InternalLeanTest/NavigationTest.lean`
- `InternalLeanTest/ObjectNotationTest.lean`
- `InternalLeanTest/JudgmentAbbrevTest.lean`
- `InternalLeanTest/EvidencePremiseTest.lean`
- `InternalLeanTest/StructuralInternalAdmissionTest.lean`
- `InternalLeanTest/CorrectnessRegressionTest.lean`

These files show focused behavior for frontend syntax, metadata validation, diagnostics, model
workflow commands, source-navigation metadata, object notation, evidence premises, admissions, and
regression coverage. They include malformed metadata diagnostics, role validation,
rewrite/transport metadata, public/minimal model interfaces, generated transport signatures,
structural equivalence generation, syntax-sort universe levels, and synthetic generated-interface
stress cases.

## Checking examples

Useful commands for maintainers are:

```bash
lake build InternalLean
lake build InternalLeanTest
lake build InternalLeanTest.InternalTacticTest
lake build InternalLeanTest.TinyNat InternalLeanTest.TinyNatModel
```

Examples should guide generic design, but they should not become hard-coded assumptions in the
framework. More detailed design and checklists live in
`.agents/docs/InternalLeanDevelopmentNotes.md`.
