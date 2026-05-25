# InternalLean architecture

InternalLean is organized around a small logical framework (LF). Users declare an object theory in
Lean syntax, the frontend lowers that declaration to checked LF artifacts, and model commands use
those checked artifacts to generate Lean interfaces and transports.

This document gives a public overview of the main layers and the design boundaries between them.

## Object theories

An object theory is a theory formalized inside InternalLean. Examples range from TinyNat-style arithmetic to richer dependent or geometric signatures.

A declared object theory provides data such as:

- syntax sorts;
- judgment forms;
- primitive constants and LF opaque constants;
- inference rules and theorem declarations;
- conversion and rewrite metadata;
- side-condition and certificate requirements;
- optional model-visibility metadata.

These declarations describe the object theory's own language. Object terms, object equality, and
object proofs are checked by InternalLean's LF layer. Lean remains the host language used to run the
checker, store declarations, and generate model code.

## Main layers

### 1. Kernel and LF layer

Main file:

- `InternalLean/Basic.lean`

This layer contains the low-level representation of LF syntax, judgments, signatures, derivations,
and certificate checking. It is responsible for generic trust-boundary concerns such as:

- raw syntax and checked judgments;
- rule schemas and derivations;
- scoped instantiation;
- binder and context-zone validation;
- side-condition certificate slots;
- conversion-certificate checking;
- model-interpretation hooks shared by backends.

The LF layer is intentionally generic. It should know about syntax sorts, judgment heads, rules,
premises, binders, context zones, and certificates. It should not contain branches for
specific example theories by name.

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

This layer implements the user-facing Lean commands and diagnostics. Its responsibilities include:

- parsing `declare_type_theory` and `extend_type_theory` blocks;
- storing persistent theory registries and Lean-visible anchors;
- elaborating high-level declarations into checked LF artifacts;
- validating metadata such as rewrite, transport, congruence, and conversion-plugin declarations;
- registering checked or admitted `internal def` declarations;
- compiling object tactic scripts into object terms;
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
checked object theory. Depending on the theory, fields may include interpretations of syntax sorts,
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
4. The declaration is lowered to checked LF artifacts.
5. The registry stores the checked theory data and creates Lean-visible anchors for navigation.
6. Diagnostics, object tactics, and model commands consume the checked registry data.
7. Model-interface and transport commands generate Lean code from the checked artifacts.

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
- low-level raw replay payload constructors.

Everything else should be pushed toward checked LF rules, checked certificates, generated model
obligations, or checked replay wrappers at public API boundaries.

## Design principles

### Extrinsic syntax

Raw object syntax may be ill-formed. Checked derivations certify judgments about raw syntax. This
keeps the framework flexible enough for many object theories and makes the checking boundary
explicit.

### Object reasoning belongs to the object theory

Object-level typehood, equality, functions, propositions, and proofs mean whatever the declared
object theory says they mean. Lean equality and Lean typing are used to implement the framework, but
they should not be silently substituted for object-level judgments.

### Judgmental equality and internal equality are separate

Judgmental equality or conversion is represented by declared judgments or conversion artifacts.
Internal equality proofs are ordinary object terms only when the object theory declares an equality
family and proof constructors.

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

Before adding a new core primitive, ask whether the feature can be expressed using existing generic
vocabulary:

- a syntax sort;
- a judgment form;
- a rule with premises;
- a binder class or context-zone declaration;
- a side-condition certificate;
- a conversion plugin;
- rewrite, transport, symmetry, or congruence metadata;
- a theory-local macro or command alias;
- a semantic backend hook.

Core primitives should be reserved for features that cannot be represented cleanly through this
vocabulary.

## Related files

Useful entry points for reading the code:

- `InternalLean/Command.lean` — public command aggregator.
- `InternalLean/Basic.lean` — low-level LF syntax, signatures, derivations, and checking.
- `InternalLean/DSL.lean` — high-level declaration data and metadata structures.
- `InternalLean/LFElab.lean` — LF declaration elaboration and metadata validation.
- `InternalLean/Registration.lean` — theory and internal-declaration registration.
- `InternalLean/InternalTactic.lean` — object tactic parsing and compilation.
- `InternalLean/ModelInterface.lean` — generated model interfaces.
- `InternalLean/ModelTransport.lean` — generated model transports.
- `InternalLeanTest/TinyNat.lean` — compact direct-LF example theory.
- `InternalLeanTest/InternalTacticTest.lean` — object tactic regression examples.
