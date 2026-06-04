---
name: internallean-framework
description: >-
  Use when editing InternalLean framework code, tests, examples, model generation, LF checking,
  internal tactics, or trust-boundary behavior in this repository.
---

# InternalLean framework workflow

Use this skill for implementation work in the standalone `InternalLean` repository.

## Core goal

InternalLean is generic infrastructure for user-declared object type theories. It checks internal LF
artifacts, compiles internal tactic scripts to internal proof terms, replays derivations, and
generates model interfaces and transports from checked artifacts.

Do not hard-code behavior for one downstream theory or example. Lower example-specific pressure to
generic LF vocabulary or metadata.

## Main files

- `InternalLean/Basic.lean`: low-level LF syntax, signatures, derivations, replay, and model hooks.
- `InternalLean/DSL.lean`: object-expression data and frontend declaration syntax.
- `InternalLean/Registry.lean`: persistent registries, admissions, source docs, and anchors.
- `InternalLean/LFElab.lean`: LF elaboration, checking, implicit arguments, and replay lowering.
- `InternalLean/Registration.lean`: theory and checked declaration registration.
- `InternalLean/InternalTactic.lean`: `internal def`, `internal theorem`, tactic scripts, batches.
- `InternalLean/Diagnostics.lean`: print, lint, notation, and audit commands.
- `InternalLean/ModelInterface.lean`: model obligations, interfaces, templates, provenance.
- `InternalLean/ModelTransport.lean`: model generation and transport commands.
- `InternalLean/Command.lean`: public command aggregator.
- `InternalLeanTest/*.lean`: regression tests and examples.
- `Examples/*.lean`: beginner exercises.
- `.agents/docs/InternalLeanDevelopmentNotes.md`: detailed workflow and design notes.

## Design rules

- Object-theory well-typedness is not Lean typing.
- Judgmental equality/conversion is object-theory data, not Lean equality.
- Raw LF syntax is extrinsic; checked derivations certify judgments about it.
- Scope, binders, substitution, context zones, and capture avoidance are trust-boundary concerns.
- Model interfaces should expose obligations rather than hiding missing semantics.
- Keep `syntax_abbrev` and `judgment_abbrev` checked; do not accept arbitrary untyped aliases.
- Keep admissions explicit and visible to diagnostics.

## Workflow

1. Inspect nearby definitions and tests before editing.
2. Preserve local style and module boundaries.
3. Add or update focused regression tests for trust-boundary or public-command changes.
4. Use the narrowest check that covers the edit.
5. Before handoff of substantial Lean changes, run the full public-library check set.

## Checks

For one file or module:

```bash
lake env lean path/to/File.lean
lake build InternalLean.SomeModule
lake build InternalLeanTest.SomeTest
```

For substantial changes:

```bash
lake build InternalLean.Command InternalLeanTest InternalLean Examples
python3 scripts/check_text_style.py --root .
python3 scripts/check_lean_line_lengths.py --max 100 --root .
git diff --check
```

For docs-only changes:

```bash
python3 scripts/check_text_style.py --root .
git diff --check
```
