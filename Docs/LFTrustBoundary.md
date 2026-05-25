# LF trust boundary

This document explains what InternalLean checks, what it trusts, and why later tools should consume
checked LF artifacts rather than parser traces.

## High-level idea

InternalLean commands are elaborators. They parse convenient Lean syntax and produce artifacts in a
small logical framework (LF). Those LF artifacts are then checked against the declared object
theory.

The trusted boundary is not the surface command text. The meaningful boundary is:

- the checked LF signature;
- checked LF definitions and judgment theorems;
- checked derivation and conversion certificates;
- explicit trusted leaves such as opaque constants and admitted declarations.

## What LF means here

LF is the project's internal logical-framework language for representing object-theory data:

- syntax sorts;
- object expressions;
- judgment forms;
- rules and premises;
- binders and scoped local variables;
- side-condition slots;
- proof or derivation terms;
- conversion certificates.

LF is not Lean's kernel. Lean hosts the implementation and generated code, while LF represents the
object theory being declared.

## What certificate checking means

Certificate checking takes a generated proof, derivation, or conversion certificate and checks each
step against the declared LF signature.

For example, a checked theorem must use declared rules, declared theorem references, and explicit
premise proofs in the right shape. A checked conversion certificate must justify each conversion
step by supported conversion evidence.

This is different from:

- trusting a parser trace;
- trusting an object tactic script directly;
- asking Lean to prove the object-theory statement;
- treating object equality as Lean equality.

Object tactics and high-level commands are conveniences. Their output has to pass through checked
LF artifacts before model generation or transport should rely on it.

## Checked ingredients

The checker validates and stores information such as:

- declared syntax sorts and their parameters;
- declared judgment heads and their parameters;
- rule schemas, premises, side conditions, and conclusions;
- checked local references and telescope dependencies;
- duplicate-name and dependency checks;
- scoped binders and capture-safe instantiation;
- typed LF opaque constants where type information is supplied;
- checked LF definitions and theorem declarations;
- side-condition certificate slots and checked certificate evidence;
- conversion plugin declarations and supported step classes;
- rewrite, symmetry, congruence, transport, and transport-position metadata.

The exact checked data depends on the declaration kind and backend support.

## Object equality is not Lean equality

A declared object theory controls its own equality and conversion judgments. For example:

```lean
judgment eqNat (lhs : Nat) (rhs : Nat)
judgment_role eqNat : term_conversion
```

This does not create Lean equality between `lhs` and `rhs`. It declares an object-theory conversion
judgment that InternalLean tooling may use when the required LF evidence is available.

Similarly, an internal equality type such as:

```lean
syntax_sort Eq (lhs : Nat) (rhs : Nat)
```

is just another object-theory family until the theory declares proof constructors and rules for it.
Judgmental conversion and internal equality proofs should not be conflated.

## Remaining trusted leaves

Some leaves are intentionally trusted or opaque. They should be explicit in source and diagnostics.

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
```

The annotation `J` is still checked as an object-theory judgment or type, but the body is not
checked. The admission is stored explicitly and can be inspected with:

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

Object `simp` currently uses registered executable `beta` plugin steps. Other step classes are part
of the conversion-certificate vocabulary and future automation boundary.

## Rewriting and transport metadata

Object `rw` and non-definitional object `simp` can use metadata such as:

```lean
rewrite_relation R [lhs, rhs]
transport_rule tr for R [evidence, source]
transport_position tr : Head [0]
rewrite_symmetry symm for R [evidence]
rewrite_congruence congr for R under Head [0] [evidence]
```

This metadata is not proof by itself. It tells the object-tactic compiler where to find LF evidence
and how to build transport terms. The referenced rules or theorems still have to check.

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
```

Developer-level LF diagnostics include:

```lean
#print_checked_logical_framework_metadata T
#print_checked_logical_framework_environment T
#print_logical_framework_rule_schemas T
#print_lf_replay_trust_summary T
```

The developer diagnostics are useful for implementation work. Public examples should usually prefer
the shorter user-facing commands.
