# LF trust boundary

This document explains what InternalLean checks, what it trusts, and why later tools should consume
checked LF artifacts rather than parser traces.

## High-level idea

InternalLean commands are elaborators. They parse convenient Lean syntax and produce artifacts in a
small logical framework (LF). Those LF artifacts are then checked against the declared type theory.

The trusted boundary is not the surface command text. The meaningful boundary is:

- the checked LF signature;
- checked LF definitions and judgment theorems;
- checked derivation and conversion certificates;
- explicit trusted leaves such as opaque constants and admitted declarations.

## What LF means here

LF is the project's internal logical-framework language for representing declared type-theory data:

- syntax sorts and derived syntax definitions;
- internal expressions;
- judgment forms;
- rules and premises;
- binders and scoped local variables;
- side-condition slots;
- proof or derivation terms;
- conversion certificates.

LF is not Lean's kernel. Lean hosts the implementation and generated code, while LF represents the
type theory being declared.

## What certificate checking means

Certificate checking takes a generated proof, derivation, or conversion certificate and checks each
step against the declared LF signature.

For example, a checked theorem must use declared rules, declared theorem references, and explicit
premise proofs in the right shape. A checked conversion certificate must justify each conversion
step by supported conversion evidence.

This is different from:

- trusting a parser trace;
- trusting an internal tactic script directly;
- asking Lean to prove the internal statement;
- treating internal equality as Lean equality.

Internal tactics and high-level commands are conveniences. Their output has to pass through checked
LF artifacts before model generation or transport should rely on it.

## Checked ingredients

The checker validates and stores information such as:

- declared syntax sorts, syntax definitions, and their parameters;
- declared judgment heads and their parameters;
- rule schemas, premises, side conditions, and conclusions;
- checked local references and telescope dependencies;
- duplicate-name and dependency checks;
- scoped binders and capture-safe instantiation;
- typed LF opaque constants where type information is supplied;
- checked syntax definitions, LF definitions, and theorem declarations;
- side-condition certificate slots and checked certificate evidence;
- conversion plugin declarations and supported step classes;
- rewrite, symmetry, congruence, transport, and transport-position metadata.

The exact checked data depends on the declaration kind and backend support.

## Internal equality is not Lean equality

A declared type theory controls its own equality and conversion judgments. For example:

```lean
judgment eqNat (lhs : Nat) (rhs : Nat)
judgment_role eqNat : term_conversion
```

This does not create Lean equality between `lhs` and `rhs`. It declares a conversion judgment that
InternalLean tooling may use when the required LF evidence is available.

Similarly, an internal equality type such as:

```lean
syntax_sort Eq (lhs : Nat) (rhs : Nat)
```

is just another internal family until the theory declares proof constructors and rules for it.
Judgmental conversion and internal equality proofs should not be conflated.

## Remaining trusted leaves

Some leaves are trusted or opaque by design. They should be explicit in source and diagnostics.

Current trusted leaves include:

- `lf_opaque` constants;
- admitted internal declarations written with `sorry`;
- opaque side-condition solvers and certificates unless backed by checked hooks;
- declared external conversion certificates;
- shallow built-in raw syntax constructors used by the LF representation.

A trusted leaf is not a bug by itself. The important requirement is that it be visible and tracked,
so users and model authors know where assumptions enter.

## Admissions

An admitted declaration can be written as:

```lean
internal def admitted : J := sorry
internal theorem admittedTheorem : J := sorry
syntax_def admittedFamily (x : A) : Type u := sorry
```

The annotation `J`, or the `syntax_def` header and result universe, is still checked in the
declared theory, but the admitted body is not checked. `internal theorem ... := sorry` records
theorem-shaped debt without adding a model field. An admitted `syntax_def` records derived-family
debt without becoming primitive model data. The admission is stored explicitly and can be inspected
with:

```lean
#lint_type_theory_sorries T
```

Generated transports depending on admissions may also be admitted on the Lean side. The lint command
reports these dependencies.

## Side conditions

Rules may include side conditions:

```lean
rule r (x : A) where
  side_condition ok by solver : input x
  conclusion : J x
```

A side-condition solver name is declared with:

```lean
side_condition_solver solver
```

Side-condition certificates are part of the LF trust boundary. If a solver is opaque, it is a
trusted leaf. If a checked hook is available, the resulting certificate can be checked and tracked.

Use:

```lean
#print_type_theory_side_conditions T
```

to inspect side-condition and certificate obligations.

## Conversion plugins

Conversion plugins are declared by metadata such as:

```lean
conversion_plugin beta_step executable [beta]
conversion_plugin external_step external_certificate [reindexing]
```

A plugin declaration records the trust mode and supported generic step classes. Executable checked
steps can be checked by the framework when support exists. External-certificate and opaque modes are
trusted leaves unless backed by additional checked evidence.

Internal `simp` currently uses registered executable `beta` plugin steps. Executable `eta` steps
check structural function eta for explicit raw `_app` redexes and structural Sigma eta for
`pair`/`fst`/`snd` redexes. Other step classes remain part of the conversion-certificate vocabulary
and future automation boundary.

## Rewriting and transport metadata

Internal `rw` and non-definitional `simp` can use metadata such as:

```lean
rewrite_relation R [lhs, rhs]
transport_rule tr for R [evidence, source]
transport_position tr : Head [0]
rewrite_symmetry symm for R [evidence]
rewrite_congruence congr for R under Head [0] [evidence]
```

This metadata is not proof by itself. It tells the internal tactic compiler where to find LF
evidence and how to build transport terms. The referenced rules or theorems still have to check.

## Why model generation uses checked artifacts

Model interfaces and transports should be generated from checked LF artifacts, not from source
syntax alone.

This matters because surface syntax can contain conveniences, macros, tactics, implicit arguments,
or notational abbreviations. Checked artifacts are the normalized and validated representation that
records what the theory actually declared and proved.

A model backend should distinguish:

1. declarations checked by the LF layer;
2. trusted leaves supplied by the user;
3. generated theorem or transport code derived from checked artifacts;
4. semantic fields supplied by the model author.

## Useful commands

Theory and trust-boundary inspection:

```lean
#check_theory T
#print_type_theory T
#print_type_theory_side_conditions T
#lint_type_theory_sorries T
#print_internal_registration_profile T
```

Model-generation consistency checks:

- `generate_model_interface` and related generation commands must run at the root namespace. They
  emit declarations in deterministic top-level namespaces named by the theory/model interface.
- Selective LF model transports include checked theorem-reference dependencies before the selected
  theorem transport.
- Generated model field and method names are validated before Lean structure elaboration; qualified
  names and reserved structure names such as `mk` are rejected.
- `object_macro` is diagnostic/ergonomic metadata. Checked LF declarations must use the expanded
  expression explicitly.

Developer-level LF diagnostics include:

```lean
#print_checked_logical_framework_metadata T
#print_checked_logical_framework_environment T
#print_logical_framework_rule_schemas T
#print_lf_replay_trust_summary T
```

Low-level replay payload constructors such as `KernelLFDerivation.ruleApp` are raw syntax. Public
APIs should prefer `CheckedKernelLFDerivation.ofReplay`,
`CheckedKernelLFDerivation.ofDerivation`, or `KernelLFReplayCertificate.toChecked`; these wrappers
rerun executable replay validation and are the supported trust-boundary tokens.

The developer diagnostics are useful for implementation work. Public examples should usually prefer
the shorter user-facing commands.
