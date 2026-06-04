# InternalLean development notes for coding agents

These notes preserve detailed guidance that is useful for coding agents and maintainers, while the
public docs in `Docs/` stay concise for human readers.

## Documentation split

- `README.md` and `Docs/` are public, human-facing documentation.
- `.agents/` is for detailed workflow notes, design warnings, status conventions, and reusable
  agent prompts.
- Avoid adding long agent-oriented cautions to tutorials when a shorter factual sentence is enough.
- Keep this directory free of local paths, private machine details, and tool-specific instructions.
- Keep the README warning that most code in this repository was written by AI coding agents.

A good public sentence is direct:

```text
Typed `lf_opaque` declarations usually become model-interface fields.
```

Longer operational advice belongs here.

## Core project goal

InternalLean is infrastructure for declaring user-defined object type theories inside Lean. A
checked theory controls its own syntax, judgments, rules, equality/conversion evidence, side
conditions, internal proof terms, and model obligations.

Preserve the generic framework boundary:

- object-theory well-typedness is not Lean typing;
- judgmental equality is object-theory data, not Lean equality;
- raw LF syntax may be ill-formed, and checked derivations certify judgments about it;
- substitution, scope, binders, context zones, and capture avoidance are trust-boundary details;
- model interfaces expose semantic obligations instead of hiding missing proofs;
- example theories and downstream SCT pressure are stress tests, not hard-coded core assumptions.

When a feature is needed for one example, first look for a generic representation: syntax sorts,
judgments, rules, structural evidence premises, context zones, binder classes, side-condition
certificates, conversion plugins, rewrite/transport metadata, theory-local notation, or a backend
hook.

## Main files

- `InternalLean/Basic.lean`: low-level LF syntax, signatures, derivations, replay, scoped
  instantiation, conversion certificates, and model hooks.
- `InternalLean/DSL.lean`: high-level object-expression and declaration data plus frontend syntax.
- `InternalLean/Registry.lean`: persistent theory data, admissions, source docs, anchors, and
  metadata registries.
- `InternalLean/LFElab.lean`: LF elaboration/checking, implicit arguments, abbreviation expansion,
  evidence checking, and replay lowering.
- `InternalLean/Registration.lean`: `declare_type_theory`, `extend_type_theory`, and registration
  of checked declarations.
- `InternalLean/InternalTactic.lean`: `internal def`, `internal theorem`, `internal_defs where`,
  internal tactic parsing/compilation, and goal snapshots.
- `InternalLean/Diagnostics.lean`: print, lint, object notation, and replay-audit commands.
- `InternalLean/ModelInterface.lean`: model obligations, interfaces, templates, provenance, and
  structural-equivalence rendering.
- `InternalLean/ModelTransport.lean`: model-interface generation commands and transport commands.
- `InternalLean/Command.lean`: public command aggregator.
- `InternalLeanTest/*.lean`: regression tests and compact example theories.
- `Examples/*.lean`: beginner-facing exercises and solutions.
- `Docs/*.md`: public documentation.

## Declaration and admission policy

Classify declarations before changing their semantics:

1. **Primitive vocabulary**: syntax sorts, judgments, rules, or typed/untyped `lf_opaque` constants.
2. **Derived definitions**: checked `lf_def` or checked object-shaped `internal def` declarations.
3. **Theorems**: checked `judgment_theorem`, checked theorem-shaped `internal def`, or checked
   `internal theorem` declarations.
4. **Formalization debt**: explicit `sorry` admissions that remain visible to diagnostics.

Do not weaken LF checking to accept arbitrary untyped abbreviations. `syntax_abbrev` values should
remain LF type expressions; `judgment_abbrev` values should remain judgment-headed expressions.

Important command distinctions:

- `lf_opaque` introduces primitive or trusted data. Typed constants usually become model fields.
- `lf_def` defines checked LF data inside a theory block and should not add a model field when the
  construction is definable from previous data.
- `judgment_theorem` is a checked theorem for a judgment-headed expression inside a theory block.
- `internal def` can register checked object definitions or theorem-shaped checked declarations.
- `internal theorem` is supported for explicit theorem-shaped declarations and admissions. It does
  not support `:= by` internal tactic scripts, and it is not currently an item form inside
  `internal_defs where`.
- `internal_defs where` batches all-direct checked object definitions and consecutive object
  admissions when possible; tactic, theorem-shaped, placeholder, or mixed blocks fall back to
  source-order paths.
- `internal theorem ... := sorry` records theorem-shaped debt without adding a model field.

## Object notation and macros

`object_notation` is parse-only notation for object expressions. It expands before LF checking,
replay, and model rendering. Current limitations are part of the public contract:

- the first pattern part must be a quoted literal token;
- identical concrete parser patterns are global and cannot be overloaded between theories;
- the built-in LF dependent arrow token `⇒` is reserved;
- pretty-printing still shows expanded expressions.

`object_macro` is diagnostic metadata. Checked declarations should use expanded expressions rather
than macro heads.

## Model workflow policy

Model generation should consume checked LF artifacts, not parser traces or unchecked tactic
scripts. When changing declarations that affect models, inspect obligations before and after:

```lean
#print_model_obligations T
#check_model_obligations T
#print_model_provenance T
#print_model_template T as TModel
#lint_type_theory_sorries T
```

For public/minimal interfaces, use the corresponding `public` commands. Provenance diagnostics are
especially useful when a field is surprising or omitted.

Generation commands must run at the root namespace. `generate_model_interface T as M` emits the
structure in namespace `T`, so the full name is `T.M`. Structural equivalences are opt-in via
`generate_model_structural_equiv T for M` and are strict comparisons of generated model fields.

Do not hide theorem-shaped debt by introducing new primitive model fields unless the source theory
really treats that data as primitive or axiomatic.

## Source navigation

InternalLean emits Lean declaration anchors and term info for declared type-theory names, top-level
internal declarations, and batched internal declarations. Same-module generated model projections
reuse source declaration ranges where Lean server support allows it. If navigation breaks, check
for duplicate anchor names and same-module assumptions before changing model rendering.

## Performance and regression notes

Recent performance work added compiled incremental LF checker caches, append-only cache updates,
map-based LF expression lookup, checked object-definition batching, and model-obligation rendering
plan reuse. Keep these paths generic and covered by regression tests.

Useful performance tools:

```bash
python3 scripts/benchmark_checker.py --quick
python3 scripts/benchmark_incremental_cache.py --size 2000 --runs 3
python3 scripts/benchmark_large_model_interface.py --sizes 60 --runs 2
```

Run or extend targeted regression tests when touching trust-boundary code, admissions, evidence
premises, object notation, abbreviation expansion, raw conversion, model rendering, navigation, or
incremental caches.

## Checks

Use narrow checks while editing:

```bash
lake env lean path/to/File.lean
lake build InternalLean.SomeModule
lake build InternalLeanTest.SomeTest
```

For substantial implementation changes:

```bash
lake build InternalLean.Command InternalLeanTest InternalLean Examples
python3 scripts/check_text_style.py --root .
python3 scripts/check_lean_line_lengths.py --max 100 --root .
git diff --check
```

For docs-only or `.agents` changes:

```bash
python3 scripts/check_text_style.py --root .
git diff --check
```

A full Lean build is not normally needed for docs-only edits unless examples or generated snippets
were changed in a way that should be checked.

## Release notes

Compatibility release tags should match Lean toolchain tags when possible, for example
`v4.31.0-rc1`. Mark releases for Lean release candidates or nightlies as GitHub prereleases.

Do not move a public release tag. If a fix is needed after a tag has been published, create a new
unique tag and update downstream projects to that tag.
