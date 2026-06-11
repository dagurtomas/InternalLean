# InternalLean architecture

InternalLean is organized around a small logical framework (LF). Users declare a type theory in Lean
syntax, the frontend lowers that declaration to checked LF artifacts, and model commands use those
checked artifacts to generate Lean interfaces and transports.

This document gives a public overview of the main layers and the design boundaries between them.

## Declared type theories

A declared type theory is a theory formalized inside InternalLean. Examples range from TinyNat-style
arithmetic to richer dependent or geometric signatures.

A declared type theory provides data such as:

- syntax sorts;
- judgment forms;
- primitive constants and LF opaque constants;
- inference rules and theorem declarations;
- conversion and rewrite metadata;
- side-condition and certificate requirements;
- optional model-visibility metadata.

These declarations describe the theory's own language. Internal terms, equality evidence, and
proofs are checked by InternalLean's LF layer. Lean remains the host language used to run the
checker, store declarations, and generate model code.

## Main layers

### 1. Kernel and LF layer

Main files:

- `InternalLean/Basic.lean`
- `InternalLean/Kernel.lean`

This layer contains the low-level representation of LF syntax, judgments, signatures, derivations,
and certificate checking. The checked replay boundary uses first-class structural kernel terms for
binders, products, functions, universes, and equality-shaped expressions, so former raw-kernel
constructor names are ordinary LF heads. Replay audit and certificate diagnostics render these
structural payloads directly. It is responsible for generic trust-boundary concerns such as:

- structural LF terms and checked judgments;
- rule schemas and derivations;
- scoped instantiation;
- binder and context-zone validation;
- side-condition certificate slots;
- conversion-certificate checking;
- model-interpretation hooks shared by backends.

The LF layer is generic. It should know about syntax sorts, judgment heads, rules, premises,
binders, context zones, and certificates. It should not contain branches for specific example
theories by name.

### 2. Frontend and registration layer

Main files:

- `InternalLean/DSL.lean`
- `InternalLean/Registry.lean`
- `InternalLean/LFElab.lean`
- `InternalLean/ReplayAudit.lean`
- `InternalLean/Registration.lean`
- `InternalLean/InternalTactic.lean`
- `InternalLean/Diagnostics.lean`
- `InternalLean/Command.lean`

This layer implements the user-facing Lean commands and diagnostics. Canonical `internal def` and
`internal theorem` bodies are Lean terms elaborated against generated quote stubs, reflected back to
LF, and checked by the LF layer; `internal_raw` is the legacy raw body escape hatch for tests and
debugging. The layer's responsibilities include:

- parsing `declare_type_theory` and `extend_type_theory` blocks;
- storing persistent theory registries and Lean-visible anchors;
- elaborating high-level declarations into checked LF artifacts;
- validating metadata such as rewrite, transport, congruence, and conversion-plugin declarations;
- registering checked or admitted `internal def` declarations;
- compiling internal tactic scripts into internal terms;
- exposing print commands, lints, status reports, and audit commands.

`InternalLean/Command.lean` is the public import aggregator for the command surface. Most
implementation details live in the focused files listed above.

Theory-specific conveniences should live in this layer as optional syntax, notation, or macros that
lower to generic LF artifacts.

### 3. Model interface and transport layer

Main files:

- `InternalLean/ModelInterface.lean`
- `InternalLean/ModelTransport.lean`

This layer generates Lean code from checked LF artifacts.

A model interface is a Lean structure listing the semantic data and laws needed to interpret a
checked type theory. Depending on the theory, fields may include interpretations of syntax sorts,
judgment predicates, rules, admitted LF constants, and side-condition certificates.

A model transport specializes a checked internal declaration or LF theorem to a completed model.
The generated code should be derived from checked LF artifacts rather than raw parser traces.
Generation commands run at the root namespace so emitted Lean names are deterministic; selected LF
transport generation includes transitive checked theorem dependencies before dependents.

Current model generation targets Lean structures. The architecture should also leave room for
future semantic backends, such as categorical, presheaf, sheaf, cohesive, modal, or custom semantic
interpretations.

## Declaration flow

A typical declaration moves through the system as follows:

1. The user writes a `declare_type_theory` block or an `internal def`.
2. The frontend parses the Lean syntax into high-level declaration data.
3. Elaboration checks names, binders, premises, metadata, and local dependencies.
4. Standalone and batched `internal def` declarations are checked incrementally against the stored
   checked signature when possible.
5. The declaration is lowered to checked LF artifacts.
6. The registry stores the checked theory data and creates Lean-visible anchors for navigation.
7. Diagnostics, internal tactics, and model commands consume the checked registry data.
8. Model-interface and transport commands generate Lean code from the checked artifacts.

The important boundary is between high-level elaboration and checked LF artifacts. Parser traces and
tactic scripts are conveniences. The checked LF artifacts are what later tools should rely on.

## Trust boundary

High-level commands are elaborators. They produce LF signatures, derivation certificates, and
conversion certificates. Certificate checking validates those artifacts against the declared LF
signature.

The main trusted leaves are explicit:

- opaque LF constants declared by the user;
- admitted internal declarations;
- side-condition solvers or certificates without checked hooks;
- declared external conversion certificates.

Everything else should be pushed toward checked LF rules, checked certificates, generated model
obligations, or checked replay wrappers at public API boundaries.

## Design principles

### Extrinsic syntax

Internal syntax is extrinsic: a term can be represented before the declared type theory has proved
that it has a particular judgment. Checked derivations certify judgments about structural kernel
terms. This keeps the framework flexible enough for many declared type theories and makes the
checking boundary explicit.

### Internal reasoning belongs to the declared type theory

Internal typehood, equality, functions, propositions, and proofs mean whatever the declared type
theory says they mean. Lean equality and Lean typing are used to implement the framework, but they
should not be silently substituted for internal judgments.

### Judgmental equality and internal equality are separate

Judgmental equality or conversion is represented by declared judgments or conversion artifacts.
Internal equality proofs are ordinary internal terms only when the declared type theory includes an
equality family and proof constructors.

### Scope and substitution are trust-boundary concerns

Binders, local variables, context zones, substitution, and capture avoidance need first-class
validation. These details are especially important for theories with dependent contexts, binders,
or geometric structure.

### Models are user-provided semantic data

Generated model interfaces expose obligations. They should avoid assuming a single semantic shape,
such as set-valued models, Lean `Type`-valued models, one fixed theory family, or any
specific example semantics.

### Prefer generic extensions

If an example needs a new feature, prefer adding generic LF vocabulary or metadata over adding
example-specific core code.

## Adding new features

New core primitives should be rare. Most extensions should first be tried as generic LF vocabulary:
syntax sorts, judgments, rules, binders, context zones, side-condition certificates,
conversion/rewrite metadata, theory-local notation, or backend hooks. This keeps the framework
independent of any one example theory.

For detailed implementation checklists, see `.agents/docs/InternalLeanDevelopmentNotes.md`.

## Related files

Useful entry points for reading the code:

- `InternalLean/Command.lean` — public command aggregator.
- `InternalLean/Basic.lean` — shared universe, metavariable-sort, and trust-boundary vocabulary.
- `InternalLean/Kernel.lean` — structural LF terms, signatures, derivations, and checking.
- `InternalLean/DSL.lean` — high-level declaration data and metadata structures.
- `InternalLean/LFElab.lean` — LF declaration elaboration and metadata validation.
- `InternalLean/Registration.lean` — theory and internal-declaration registration.
- `InternalLean/InternalTactic.lean` — internal tactic parsing and compilation.
- `InternalLean/ModelInterface.lean` — generated model interfaces.
- `InternalLean/ModelTransport.lean` — generated model transports.
- `InternalLeanTest/TinyNat.lean` — compact direct-LF example theory.
- `InternalLeanTest/InternalTacticTest.lean` — internal tactic regression examples.
