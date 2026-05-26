# Model workflow guide

This guide explains the public workflow for interpreting a checked object theory by generating a
Lean model interface and transporting checked declarations to a completed model.

For a shorter introduction, see `Docs/UserGuide.md`.

## What is a model interface?

A model interface is a Lean structure generated from a checked object theory. It lists the semantic
data and laws that a model author must provide.

Depending on the theory, the generated fields can include:

- interpretations of syntax sorts;
- interpretations of judgment forms;
- interpretations of typed `lf_opaque` constants;
- realizers for rules;
- side-condition predicates and certificate parameters;
- inherited fields from parent theories or generated chunks.

The interface is generated from checked LF artifacts. It should not depend on raw parser traces or
unchecked tactic scripts.

## Basic workflow

The usual workflow is:

1. Declare a theory.
2. Inspect its model obligations.
3. Generate a model interface.
4. Write an instance or structure value satisfying the interface.
5. Generate transports for checked internal declarations or LF theorems.

A small command sequence looks like this:

```lean
#check_theory TinyNat
#print_model_obligations TinyNat
#check_model_obligations TinyNat
#print_model_interface TinyNat as TinyNatModel
generate_model_interface TinyNat as TinyNatModel
```

Generation commands must be run at the root namespace so generated declarations have deterministic
names. After `generate_model_interface`, `TinyNatModel` is a Lean structure available in the
current environment.

## Inspecting obligations

```lean
#print_model_obligations T
```

Prints the obligations inferred from the checked theory. This is the best first command when you
want to know what a model author must provide.

```lean
#check_model_obligations T
```

Runs the model-obligation validator without printing the full generated interface.

Public/minimal variants are also available:

```lean
#print_public_model_obligations T
#check_public_model_obligations T
```

The public/minimal view omits declarations marked `model_internal` or `model_compat`, together with
public fields that depend on them.

## Printing and generating interfaces

```lean
#print_model_interface T as M
```

Prints the Lean commands that would define the model interface `M`. It does not add declarations to
the environment.

```lean
generate_model_interface T as M
```

Generates the model interface as Lean code. Run generation commands at the root namespace; if the
current namespace is non-root, InternalLean reports an error before emitting declarations.

Public/minimal variants:

```lean
#print_public_model_interface T as M
generate_public_model_interface T as M
```

Use the public/minimal variants when you want an interface intended for public model authors rather
than a full debug interface.

## Model templates

```lean
#print_model_template T as M
```

Prints a fillable template for constructing a value of the generated model interface. The template
is grouped by required fields, generated fields, blocked items, and omissions.

```lean
#print_public_model_template T as M
```

Prints the corresponding template for the public/minimal interface.

Templates are for authoring convenience. They do not generate declarations by themselves.

## Model visibility metadata

Inside a `declare_type_theory` or `extend_type_theory` block, model visibility can be controlled
with:

```lean
model_public decl
model_internal decl
model_compat decl
```

Meanings:

- `model_public decl` marks `decl` as public-facing.
- `model_internal decl` hides `decl` from public/minimal interfaces.
- `model_compat decl` keeps compatibility/debug declarations out of public/minimal interfaces.

Visibility metadata does not change object-theory checking. It only affects generated model
interfaces and templates.

## Model sections

Large theories can group model obligations into sections:

```lean
model_section SectionName
```

A `model_section` marker assigns later LF declarations to that section until another section marker
appears.

Useful inspection commands:

```lean
#print_model_sections T
#print_public_model_sections T
```

Per-section templates:

```lean
#print_model_section_template T Section as Bundle
#print_public_model_section_template T Section as Bundle
```

Standalone section-owned interfaces:

```lean
generate_model_section_interface T as M
generate_public_model_section_interface T as M
```

Fast wrappers over an already generated flat interface:

```lean
generate_model_sections T as Sectioned adapting Flat
generate_public_model_sections T as Sectioned adapting Flat
```

True section-bundle packages with an adapter to a flat interface:

```lean
#print_model_section_bundles T as Bundle adapting Flat
#print_public_model_section_bundles T as Bundle adapting Flat
generate_model_section_bundles T as Bundle adapting Flat
generate_public_model_section_bundles T as Bundle adapting Flat
```

For small theories, the flat `generate_model_interface` workflow is usually enough.

## What is a model transport?

A model transport specializes a checked internal declaration or LF theorem to a completed model.
For example, if an internal theorem was checked in `TinyNat`, a transport command can generate the
corresponding Lean theorem over a `TinyNatModel`.

Transport generation consumes checked LF artifacts. It should not inspect unchecked source terms or
raw tactic traces.

## Inspecting transport status

```lean
#print_model_transport_status T for M
```

Prints which declarations can be transported to model interface `M`, which are blocked, and why.
Use this before generating transports for a larger theory.

```lean
#print_model_transport_signature T f for M
```

Prints the Lean signature of the transport that would be generated for declaration `f`.

## Generating transports

```lean
generate_model_transport T f for M
```

Generates the transport for one declaration.

For direct LF workflows, selected and bulk transport commands are also available:

```lean
#print_lf_model_transports T for M
generate_lf_model_transports T for M
generate_lf_model_transports T only f g h for M
```

Use the selected form when you only want a small subset of declarations or when debugging one
transport at a time. Selected LF transports automatically include transitive checked theorem
references needed by the selected declarations, and dependencies are emitted before dependents.

## Admissions and generated transports

An admitted internal declaration uses `sorry`:

```lean
internal def admitted : J := sorry
```

Admissions are explicit. Generated transports that depend on admissions may also contain admitted
Lean bodies. Inspect them with:

```lean
#lint_type_theory_sorries T
```

A model workflow should distinguish:

1. checked internal declarations and LF theorems;
2. explicit admissions and opaque LF constants;
3. theorem-shaped internal admissions, which are lint-visible but not model fields;
4. generated transports derived from checked artifacts;
5. model fields supplied by the user.

## Common troubleshooting

If generation fails under a namespace, close the namespace and rerun the generation command at the
root. Printing commands such as `#print_model_interface` remain useful for inspection.

Use `#print_internal_registration_profile T` when many standalone `internal def` declarations or
`extend_type_theory` blocks are slow; it reports incremental registrations and full-signature
extension checks that reprocess old LF definitions/theorems.

If a model obligation is missing, check whether the declaration was hidden by `model_internal` or
`model_compat`.

If a transport is blocked, run:

```lean
#print_model_transport_status T for M
#print_model_transport_signature T f for M
```

If a generated interface is too large, consider section metadata and section-bundle generation.

If a theorem has side conditions, the generated theorem may require explicit certificate parameters.
Use:

```lean
#print_type_theory_side_conditions T
```

to inspect side-condition and certificate obligations.
