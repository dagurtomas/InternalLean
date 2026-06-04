# InternalLean

> [!WARNING]
> Most of the code in this repository was written by AI coding agents. Treat the implementation
> and documentation as research-prototype material that needs human review before reuse in
> high-assurance settings.

InternalLean is a standalone Lean project for declaring user-defined type theories, checking
internal artifacts, replaying derivations in a small logical framework (LF), and generating model
interfaces or transports from checked artifacts.

The core goal is to make reasoning inside declared type theories explicit. A declared theory
controls its own syntax, judgments, rules, equality/conversion evidence, side conditions, and model
obligations.
Example theories and regression tests are used to exercise the framework; they are not assumptions
baked into the core.

## Terminology

A **declared type theory** is a theory formalized inside the framework. InternalLean lets users
declare the syntax, judgments, rules, and equality structure needed for a wide range of synthetic
reasoning inside Lean, subject to the current LF features and checks. The theory's terms, typing
judgments, equality judgments, and rules are data declared to InternalLean. They are checked by
InternalLean's LF layer rather than being identified with Lean's own terms and theorems.

A **model interface** is a Lean structure generated from a checked type theory. It lists the
semantic data and laws a user must provide to interpret that theory in Lean or in a future backend.
For example, a model interface may ask for interpretations of syntax constructors, judgment
predicates, rules, side-condition certificates, and admitted LF constants.

A **model transport** is generated Lean code that takes a completed model interface and specializes
a checked internal declaration or LF theorem to that model. Transports are derived from checked LF
artifacts, so model generation should not depend on raw parser traces.

## Status

This is an active research prototype. The stable surface is the direct-LF declaration workflow,
`internal def`, internal tactic scripts, LF certificate checking, and generated
model-interface/transport commands. APIs may still change as the LF trust boundary, model backend,
and internal tactics are hardened.

## Build

Use the Lean toolchain pinned by `lean-toolchain`.

```bash
lake build InternalLean
```

For a quicker command/API smoke check:

```bash
lake build InternalLean.Command InternalLeanTest.APIExtensionTest
```

To build the Mathlib-style test library:

```bash
lake build InternalLeanTest
```

## Depending on InternalLean from another project

Another Lake project can depend on InternalLean through Git. The downstream project should use a
compatible Lean toolchain. Until compatibility ranges are tested, use the same toolchain as this
repository, currently:

```text
leanprover/lean4:v4.31.0-rc1
```

In a `lakefile.toml`, add the current compatibility tag:

```toml
[[require]]
name = "InternalLean"
git = "https://github.com/dagurtomas/InternalLean.git"
rev = "v4.31.0-rc1"
```

InternalLean compatibility tags normally match the Lean toolchain tag. For development against the
latest unreleased repository state, use `rev = "main"`; for reproducible projects, prefer a tag or
commit hash.

In a `lakefile.lean`, the equivalent tagged dependency is:

```lean
import Lake
open Lake DSL

package «MyProject» where

require InternalLean from git
  "https://github.com/dagurtomas/InternalLean.git" @ "v4.31.0-rc1"

@[default_target]
lean_lib «MyProject» where
```

Then import the user-facing command surface in Lean files:

```lean
import InternalLean.Command
```

Run `lake update InternalLean` after adding the dependency, then `lake build`.

## Where to start in the code

Good first files to inspect:

- `Examples/IntroExercises.lean` — first hands-on exercises for declaring a tiny type theory and
  filling internal proofs.
- `Examples/IntroExercisesHints.lean` and `Examples/IntroExercisesSolutions.lean` — hints and
  worked solutions for the exercises.
- `InternalLeanTest/TinyNat.lean` — small direct-LF type theory.
- `InternalLeanTest/TinyNatModel.lean` — generated model-interface workflow over TinyNat.
- `InternalLeanTest/InternalTacticTest.lean` — internal tactic examples and regressions.
- `InternalLeanTest/APIExtensionTest.lean` — focused command and LF metadata regression tests.
- `InternalLean/Command.lean` — public import aggregator for the command surface.

## Declaring a type theory

A type theory starts with `declare_type_theory T where`. Inside the block, declarations such as
`syntax_sort`, `judgment`, `lf_opaque`, and `rule` describe the theory's syntax, judgments,
primitive constants, and inference rules. For example:

```lean
declare_type_theory TinyNat where
  syntax_sort Nat
  judgment wfNat (n : Nat)
  lf_opaque zero : Nat
  rule zero_intro : wfNat zero
```

Syntax-sort carriers are small by default in generated model interfaces. Use a theory universe
parameter and a result annotation, such as `syntax_sort Obj : Type u`, when the intended semantic
carrier lives in a higher Lean universe.

After a theory has been declared, internal definitions and theorems live in its namespace and use
`internal def`:

```lean
namespace T

internal def f : J := term

internal def g : J := by
  exact term

internal def admitted : J := sorry

end T
```

Here `J` is a judgment or type in the declared theory. The basic form writes this judgment or type
explicitly after `:`.

Binder-style `internal def` declarations are also supported:

```lean
internal def f (x : A) : B := body
```

The generic LF frontend lowers this syntax to an explicit internal function type and internal
lambda. It still relies on the declared theory having suitable function/lambda LF structure for the
result to check. Large files can group declarations with `internal_defs where`; standalone
declarations and supported batches use incremental registration instead of rechecking all previous
internal definitions. All-direct checked object-definition blocks are checked as one batch, and
consecutive object admissions are appended through the opaque-cache path. Tactic, theorem-shaped,
placeholder, or mixed blocks still follow source-order paths. Use
`internal theorem name : J := sorry` for theorem-shaped admissions that remain lint-visible without
becoming model fields.

## Common commands

Theory, navigation, and docs:

```lean
#check_theory T
#check_type_theory_anchor T
#print_type_theory_anchor T
#lint_type_theory_docs T
#lint_type_theory_sorries T
#print_internal_registration_profile T
```

Internal tactics and side conditions:

```lean
internal def f : J := by
  exact term

#print_type_theory_side_conditions T
```

Model workflow:

```lean
#print_model_obligations T
#print_public_model_obligations T
#check_model_obligations T
#check_public_model_obligations T
#print_model_provenance T
#print_public_model_provenance T
#print_model_interface T as M
#print_public_model_interface T as M
generate_model_interface T as M
generate_public_model_interface T as M
#print_model_template T as M
#print_model_structural_equiv T for M
generate_model_structural_equiv T for M
#print_model_transport_status T for M
#print_model_transport_signature T f for M
generate_model_transport T f for M
#print_model_transports T for M
generate_model_transports T for M
generate_model_transports T only f g h for M
```

Run model-generation commands at the root namespace. `generate_model_interface` creates the model
structure; use `#print_model_provenance` when you need to explain generated fields or omissions.
Use `generate_model_structural_equiv` separately when a strict structure-preserving comparison type
is useful. Selected model transport generation includes checked theorem dependencies before
selected theorem transports.

Longer `#check_default_profile_lf_*`, `#print_default_profile_*`, `#print_lean_type_*`, and
`#print_lf_model_*` commands are developer diagnostics for inspecting replay/model internals.

## Trust boundary

High-level commands are elaborators. They parse convenient user syntax and produce LF artifacts.
The trusted artifact boundary is the checked LF signature plus derivation and conversion
certificates produced from those commands.

Here, LF means the project's small logical-framework language for representing a declared type
theory's syntax, judgments, rules, and proof terms. LF certificate checking means taking a
generated proof or conversion certificate and checking each step against the declared LF signature.
It checks the LF certificate directly rather than trusting the tactic/parser trace.

In particular, checked LF artifacts track:

- declared syntax sorts, judgments, rules, context zones, binder classes, and structural schemas;
- scoped locals, loose-variable rejection, and capture-safe instantiation under binders;
- explicit rule-premise proofs, theorem references, side-condition certificates, and evidence
  obligations;
- conversion/rewrite evidence such as β, δ, declared rewrites, congruence, symmetry, and
  transitivity where supported by the declared metadata;
- generated model obligations and transports derived from checked LF artifacts.

Remaining trusted leaves are explicit: opaque LF constants, opaque side-condition solvers or
certificates unless backed by checked hooks, and low-level raw replay payload constructors. Public
APIs should prefer checked replay wrappers such as `CheckedKernelLFDerivation.ofReplay`.

Model interpretation should consume checked LF artifacts, not parser traces alone.

## Deprecated compatibility commands

`object_def` and `object_theorem` are deprecated compatibility shims. New code should use
`internal def`.

## License

InternalLean is licensed under the Apache License, Version 2.0. See `LICENSE`.

## Further docs

- User guide: `Docs/UserGuide.md`
- Syntax reference: `Docs/Syntax.md`
- Architecture: `Docs/Architecture.md`
- Internal tactic guide: `Docs/ObjectTactics.md`
- Model workflow guide: `Docs/ModelWorkflow.md`
- LF trust boundary: `Docs/LFTrustBoundary.md`
- Examples and tests guide: `Docs/Examples.md`
- Release workflow: `Docs/Releases.md`
- Shared agent/maintainer notes: `.agents/README.md`
