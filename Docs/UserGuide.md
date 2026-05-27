# InternalLean user guide

This guide introduces the public InternalLean workflow: declare an object theory, add internal
object-level declarations, inspect obligations, and generate model interfaces or transports.

InternalLean is still an active research prototype, so this guide focuses on the stable direct-LF
surface rather than every developer diagnostic command.

## Imports

Most user files should start from the public command aggregator:

```lean
import InternalLean.Command
```

Example and regression files in this repository often use module headers and public sections for
library organization, but the core user-facing commands are provided by this import.

## Declaring an object theory

A type theory declaration starts with:

```lean
declare_type_theory T where
  -- declarations go here
```

Inside the block, declarations describe the object theory's own syntax, judgments, primitive
constants, rules, and metadata.

A tiny example looks like this:

```lean
declare_type_theory TinyNat where
  syntax_sort Nat

  judgment wfNat (n : Nat)

  lf_opaque zero : Nat

  rule zero_intro : wfNat zero
```

This declares:

- a syntax sort `Nat` for object-level natural-number terms;
- a judgment `wfNat n` saying that an object-level natural number is wellformed;
- an LF opaque constant `zero : Nat`;
- a rule proving `wfNat zero`.

The names in this block belong to the object theory. They are represented inside InternalLean's LF
layer and should not be confused with Lean's own `Nat`, typing judgment, or theorem system.

## Syntax sorts

A syntax sort declares a family of object-language syntax.

```lean
syntax_sort Nat
syntax_sort Eq (lhs : Nat) (rhs : Nat)
```

The second declaration is indexed: `Eq lhs rhs` is a family of object syntax depending on two
object-level natural-number terms.

Roles can attach generic meaning to syntax sorts for tactics and model generation:

```lean
syntax_sort_role Nat : term_sort
```

Roles are metadata. They do not make `Nat` into Lean's `Nat`; they tell the framework how this
object-theory sort should be treated by generic tooling.

## Judgments

A judgment declares an object-theory predicate or relation.

```lean
judgment wfNat (n : Nat)
judgment eqNat (lhs : Nat) (rhs : Nat)
```

Judgment roles identify common classes of judgments:

```lean
judgment_role wfNat : term_typing
judgment_role eqNat : term_conversion
```

A conversion judgment such as `eqNat` represents judgmental equality or conversion for the object
theory. It is not Lean equality.

## LF opaque constants

`lf_opaque` introduces a primitive object-language constant or constructor.

```lean
lf_opaque zero : Nat
lf_opaque succ (n : Nat) : Nat
```

Opaque constants are trusted leaves of the object theory. Models must usually provide semantic
interpretations for them unless they are hidden by later generated or derived declarations.

## Rules

A rule declares an inference rule in the object theory.

A rule with no premises can be written directly:

```lean
rule zero_intro : wfNat zero
```

A rule with premises uses a `where` block:

```lean
rule succ_intro (n : Nat) where
  premise pred_ok : wfNat n
  conclusion : wfNat (succ n)
```

Rule roles are optional metadata used by generic tooling:

```lean
rule_role succ_intro : introduction
```

## Internal declarations

After a theory has been declared, object-level definitions and theorems live in its Lean namespace
and use `internal def`.

```lean
namespace TinyNat

internal def myZero : wfNat zero := zero_intro

end TinyNat
```

The annotation after `:` is an object-theory judgment or type. The body is checked as an
object-level term or proof for that judgment.

Binder-style declarations are also supported:

```lean
namespace T

internal def f (x : A) : B x := body

end T
```

This syntax lowers to an explicit object function type and object lambda. It still relies on the
object theory having suitable function/lambda LF structure for the result to check.

For large chapters, `internal_defs where` registers many internal declarations in source order
through the same incremental path:

```lean
namespace T

internal_defs where
  def f : A := value
  def g : B f := value'

end T
```

Use `internal theorem th : J := sorry` for theorem-shaped formalization debt that should be
reported by `#lint_type_theory_sorries` without becoming a model field.

## Object tactic mode

`internal def` also supports a small object tactic mode:

```lean
namespace TinyNat

internal def myZeroTac : wfNat zero := by
  exact zero_intro

end TinyNat
```

Object tactics compile to object terms, then the resulting declaration goes through the same checked
registration path as a term-style `internal def`.

Common tactics include:

- `exact`;
- `apply`;
- `assumption`;
- `show`;
- `change`;
- `rw` for object rewrites backed by declared metadata;
- `simp` for checked definition unfolding, selected rewrite rules, and supported conversion steps;
- `refine` with checked holes.

These tactics reason in the declared object theory. They should not be read as Lean tactics over
Lean goals. See `Docs/ObjectTactics.md` for the full object tactic guide.

## Admissions and side conditions

An admitted declaration can be written with `sorry`:

```lean
namespace TinyNat

internal def admittedFact : wfNat zero := sorry

end TinyNat
```

Admissions and registration profiles can be inspected with:

```lean
#lint_type_theory_sorries TinyNat
#print_internal_registration_profile TinyNat
```

Side-condition and certificate obligations can be inspected with:

```lean
#print_type_theory_side_conditions TinyNat
```

## Inspecting a theory

Use these commands when you want to check that a theory was registered, inspect its generated
navigation anchor, or find missing documentation/admissions.

```lean
#check_theory TinyNat
```

Checks that `TinyNat` is known to the registry and prints a compact workflow summary: parents,
checked LF artifacts, model-obligation status, admissions, and generated transports.

```lean
#check_type_theory_anchor TinyNat
```

Checks that the Lean-visible anchor for `TinyNat` exists. This is mostly useful when debugging
imports or namespace mistakes.

```lean
#print_type_theory_anchor TinyNat
```

Prints the generated anchor summary for the theory: source docstring, parents, level parameters,
and counts of syntax sorts, judgments, rules, LF opaques, LF definitions, and theorems.

```lean
#print_type_theory TinyNat
```

Prints the theory's high-level registered declarations in a readable summary form. This is the
quickest way to see what the frontend thinks the theory contains.

```lean
#lint_type_theory_docs TinyNat
```

Reports public declarations that are missing source documentation.

```lean
#lint_type_theory_sorries TinyNat
```

Reports admitted internal declarations and generated transports that depend on admissions.

These commands are intended for normal users. Longer `#print_lf_model_*`,
`#check_default_profile_lf_*`, and similar commands are developer diagnostics.

## Model interfaces

A model interface is a Lean structure generated from a checked object theory. It lists the semantic
data and laws needed to interpret that theory. For primitive object constants and rules, the model
usually needs corresponding semantic fields or laws.

Use these commands when you want to inspect or generate those obligations.

```lean
#print_model_obligations TinyNat
```

Prints the model obligations inferred from the checked theory: syntax-sort fields, judgment fields,
typed LF opaque fields, rule fields, side-condition predicates, and omitted/generated items.

```lean
#check_model_obligations TinyNat
```

Runs the obligation validator without printing the full generated interface. Use this as a quick
sanity check before generating model code.

```lean
#print_model_interface TinyNat as TinyNatModel
```

Prints the Lean structure commands that would be generated for `TinyNatModel`, but does not add
those declarations to the environment.

```lean
generate_model_interface TinyNat as TinyNatModel
```

Generates the Lean model-interface structure, inherited projection exports, and a nested strict
structural-equivalence structure. Run generation commands at the root namespace; InternalLean
rejects generation under wrapper namespaces to keep Lean names deterministic. After this command,
`TinyNatModel` is available as a Lean structure to instantiate.

The generated structural equivalence is available as
`TinyNat.TinyNatModel.StructuralEquiv`. A value of this type between two completed models contains
`InternalLean.TypeEquiv` fields for generated type families and `HEq` preservation fields for
operations and rules. It is a strict structure-preserving comparison of generated model fields.

```lean
#print_model_template TinyNat as TinyNatModel
```

Prints a fillable model-authoring template grouped by required fields, generated fields, blocked
items, and omitted declarations.

## Model transports

A model transport specializes a checked internal declaration or LF theorem to a completed model.
Transport generation consumes checked LF artifacts. It should not depend on raw parser traces or
unchecked tactic scripts. Selected LF transport generation automatically includes transitive checked
theorem dependencies before the selected theorem transport.

Use these commands after generating or importing a model interface.

```lean
#print_model_transport_status TinyNat for TinyNatModel
```

Prints which internal declarations can currently be transported to `TinyNatModel`, which are
blocked, and why blocked declarations cannot yet be generated.

```lean
#print_model_transport_signature TinyNat myZero for TinyNatModel
```

Prints the Lean type/signature of the transport that would be generated for the declaration
`myZero` over `TinyNatModel`.

```lean
generate_model_transport TinyNat myZero for TinyNatModel
```

Generates the Lean declaration specializing `TinyNat.myZero` to a model `TinyNatModel`.

`generate_model_interface` does not generate these transports. Use transport commands after the
interface exists. For bulk generation, use `#print_model_transports T for M` and then
`generate_model_transports T for M`, or the selected form
`generate_model_transports T only f g h for M`.

The older `generate_lf_model_derived_theorems T for M` command generates only checked LF
`judgment_theorem` methods and compatible admitted LF methods; new workflows should prefer
`generate_model_transport` or `generate_model_transports`. The older
`generate_lf_model_transports` spelling remains as a compatibility alias.

## Extending a theory

A checked theory can be extended later:

```lean
extend_type_theory TinyNat where
  -- more syntax, rules, metadata, or LF declarations
```

Extensions add a new layer of declarations while preserving the existing theory name and registry
entry. Use extensions for narrow additions rather than copying an existing theory block.

## Deprecated commands

`object_def` and `object_theorem` are deprecated compatibility shims. New code should use
`internal def`.

Regression files should avoid these compatibility shims except when intentionally testing legacy behavior.

## Good examples to read

- `InternalLeanTest/TinyNat.lean` — compact direct-LF arithmetic example.
- `InternalLeanTest/TinyNatModel.lean` — generated model-interface workflow.
- `InternalLeanTest/InternalTacticTest.lean` — object tactic examples and regressions.
- `InternalLeanTest/APIExtensionTest.lean` — focused frontend and metadata regressions.
- `InternalLeanTest/LogicalFrameworkMetadataExamplesTest.lean` — small LF metadata smoke tests.

## Next steps

After reading this guide, the next useful public docs are:

- frontend syntax reference: `Docs/Syntax.md`;
- architecture overview: `Docs/Architecture.md`;
- focused direct-LF declaration reference;
- object tactic guide: `Docs/ObjectTactics.md`;
- model workflow guide: `Docs/ModelWorkflow.md`;
- LF trust-boundary guide: `Docs/LFTrustBoundary.md`;
- examples guide: `Docs/Examples.md`.

Those focused guides will be added under `Docs/` as the public docs mature.
