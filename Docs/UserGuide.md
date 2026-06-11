# InternalLean user guide

This guide introduces the public InternalLean workflow: declare a type theory, add internal
declarations, inspect obligations, and generate model interfaces or transports.

InternalLean is still an active research prototype, so this guide focuses on the stable direct-LF
surface rather than every developer diagnostic command. Canonical `internal def` and
`internal theorem` bodies are Lean terms reflected to LF and then checked by the LF layer.

## Imports

Most user files should start from the public command aggregator:

```lean
import InternalLean.Command
```

Example and regression files in this repository often use module headers and public sections for
library organization, but the core user-facing commands are provided by this import.

## Declaring a type theory

A type theory declaration starts with:

```lean
declare_type_theory T where
  -- declarations go here
```

Inside the block, declarations describe the theory's syntax, judgments, primitive constants, rules,
and metadata.

A tiny example looks like this:

```lean
declare_type_theory TinyNat where
  syntax_sort Nat

  judgment wfNat (n : Nat)

  lf_opaque zero : Nat

  rule zero_intro : wfNat zero
```

This declares:

- a syntax sort `Nat` for internal natural-number terms;
- a judgment `wfNat n` saying that an internal natural number is wellformed;
- an LF opaque constant `zero : Nat`;
- a rule proving `wfNat zero`.

The names in this block belong to the declared type theory. They are represented inside
InternalLean's LF layer and should not be confused with Lean's own `Nat`, typing judgment, or
theorem system.

## Syntax sorts

A syntax sort declares a family of internal syntax.

```lean
syntax_sort Nat
syntax_sort Eq (lhs : Nat) (rhs : Nat)
```

The second declaration is indexed: `Eq lhs rhs` is a family of internal syntax depending on two
internal natural-number terms.

Unannotated syntax sorts generate small Lean carrier fields in model interfaces. If a model carrier
should live in a higher universe, declare theory universe parameters and annotate the result
universe:

```lean
declare_type_theory LargeExample{u, v} where
  syntax_sort Obj : Type u
  syntax_sort Hom (X : Obj) (Y : Obj) : Type v
```

Roles can attach generic meaning to syntax sorts for tactics and model generation:

```lean
syntax_sort_role Nat : term_sort
```

Roles are metadata. They do not make `Nat` into Lean's `Nat`; they tell the framework how this
sort should be treated by generic tooling.

## Syntax definitions

Use `syntax_def` for a named derived syntax family:

```lean
declare_type_theory PackageExample{u} where
  syntax_sort Obj : Type u
  syntax_def Package (x : Obj) : Type u := Σ y : Obj, Obj
  lf_opaque usePackage (x : Obj) (p : Package x) : Obj
```

A checked `syntax_def` unfolds during LF checking and model rendering. An admitted one marks design
debt without turning the derived family into primitive model data:

```lean
syntax_def SideStructure (x : Obj) : Type u := sorry
```

`#lint_type_theory_sorries` reports admitted syntax definitions. Model interfaces do not ask model
authors to provide fields for `syntax_def` declarations; field types that mention admitted syntax
definitions use generated sorry-backed local families until the body is filled in.

## Judgments

A judgment declares a predicate or relation in the declared type theory.

```lean
judgment wfNat (n : Nat)
judgment eqNat (lhs : Nat) (rhs : Nat)
```

Judgment roles identify common classes of judgments:

```lean
judgment_role wfNat : term_typing
judgment_role eqNat : term_conversion
```

A conversion judgment such as `eqNat` represents judgmental equality or conversion for the declared
type theory. It is not Lean equality.

## LF opaque constants

`lf_opaque` introduces a primitive internal constant or constructor.

```lean
lf_opaque zero : Nat
lf_opaque succ (n : Nat) : Nat
```

Opaque constants are trusted leaves of the declared type theory. Typed opaque constants usually
become model-interface obligations; public/minimal interfaces can omit them when model-visibility
metadata hides them or hides their dependencies.

## Rules

A rule declares an inference rule in the declared type theory.

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

After a theory has been declared, internal definitions and theorems live in its Lean namespace and
use `internal def`. The body is parsed as a Lean term against generated quote stubs, reflected back
to LF, and checked by the ordinary LF checker.

```lean
namespace TinyNat

internal def myZero : wfNat zero := zero_intro

end TinyNat
```

The annotation after `:` is a judgment or type in the declared theory. The reflected body is
checked as an internal term or proof for that judgment. Use Lean named-argument syntax such as
`(A := A)` in canonical internal bodies; the old raw marker `{A := A}` is only for `internal_raw`
compatibility and theory-block fallback syntax.

Binder-style declarations are also supported:

```lean
namespace T

internal def f (x : A) : B x := body

end T
```

This syntax lowers to an explicit internal function type and internal lambda. It still relies on the
declared theory having suitable function/lambda LF structure for the result to check.

For large chapters, `internal_defs where` registers many internal declarations in source order.
Supported object-definition and object-admission batches use incremental registration:

```lean
namespace T

internal_defs where
  def f : A := value
  def g : B f := value'

end T
```

Consecutive object admissions are appended through the opaque-cache path. Checked term bodies,
tactic entries, theorem-shaped entries, placeholder-heavy entries, and mixed blocks follow
source-order paths. Use `internal theorem th : J := sorry` for theorem-shaped formalization debt
that should be reported by `#lint_type_theory_sorries` without becoming a model field.

## Internal tactic scripts

`internal def` also supports a small internal tactic mode:

```lean
namespace TinyNat

internal def myZeroTac : wfNat zero := by
  exact zero_intro

end TinyNat
```

Internal tactic scripts use Lean's tactic syntax, compile to internal terms, then the resulting
declaration goes through the same checked registration path as a term-style `internal def`.

The previous raw body grammar and object-tactic compiler are still available as `internal_raw def`
and `internal_raw theorem` for framework regression tests and debugging. Prefer canonical
`internal def`/`internal theorem` in new code. When migrating old raw bodies, replace `{x := t}`
with Lean named arguments `(x := t)` and use `Sigma.fst p`/`Sigma.snd p` for structural
projections.

Common tactics include:

- `exact`;
- `apply`;
- `assumption`;
- `show`;
- `change`;
- `rw` for internal rewrites backed by declared metadata;
- `simp` for checked definition unfolding, selected rewrite rules, and supported conversion steps;
- `refine` with checked holes.

These tactics reason in the declared type theory. They should not be read as Lean tactics over Lean
goals. See `Docs/ObjectTactics.md` for the full internal tactic guide.

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
navigation anchor, or find missing documentation/admissions. InternalLean also emits editor
navigation metadata for source declarations and references, so Lean's ordinary go-to-definition can
jump to declarations inside theory blocks and top-level internal declarations when the relevant
module is available.

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

A model interface is a Lean structure generated from a checked type theory. It lists the semantic
data and laws needed to interpret that theory. For primitive constants and rules, the model usually
needs corresponding semantic fields or laws.

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
#print_model_provenance TinyNat
```

Prints where generated obligations came from, their generated roles, and which generated fields
their rendered types depend on. Use this when a model field is surprising or a public/minimal
interface omits something. The public/minimal variant is `#print_public_model_provenance`.

```lean
#print_model_interface TinyNat as TinyNatModel
```

Prints the Lean structure commands that would be generated for `TinyNatModel`, but does not add
those declarations to the environment.

```lean
generate_model_interface TinyNat as TinyNatModel
```

Generates the Lean model-interface structure and inherited projection exports. Run generation
commands at the root namespace; InternalLean rejects generation under wrapper namespaces to keep
Lean names deterministic. After this command, the full structure name is
`TinyNat.TinyNatModel`. Inside `namespace TinyNat`, or after `open TinyNat`, it can be referred to
as `TinyNatModel`.

Strict structural equivalences are optional. To inspect or generate one, use:

```lean
#print_model_structural_equiv TinyNat for TinyNatModel
generate_model_structural_equiv TinyNat for TinyNatModel
```

The generated structural equivalence is available as `TinyNat.TinyNatModel.StructuralEquiv`. A
value of this type between two completed models contains `InternalLean.TypeEquiv` fields for
generated type families and `HEq` preservation fields for operations and rules. It is a strict
structure-preserving comparison of generated model fields.

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

Generates the Lean declaration specializing `TinyNat.myZero` to a model of
`TinyNat.TinyNatModel`.

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

Regression files should avoid these compatibility shims except when they are testing legacy
behavior.

## Good examples to read

- `InternalLeanTest/TinyNat.lean` — compact direct-LF arithmetic example.
- `InternalLeanTest/TinyNatModel.lean` — generated model-interface workflow.
- `InternalLeanTest/InternalTacticTest.lean` — internal tactic examples and regressions.
- `InternalLeanTest/APIExtensionTest.lean` — focused frontend and metadata regressions.
- `InternalLeanTest/LogicalFrameworkMetadataExamplesTest.lean` — small LF metadata smoke tests.

## Next steps

After reading this guide, the next useful public docs are:

- frontend syntax reference: `Docs/Syntax.md`;
- architecture overview: `Docs/Architecture.md`;
- internal tactic guide: `Docs/ObjectTactics.md`;
- model workflow guide: `Docs/ModelWorkflow.md`;
- LF trust-boundary guide: `Docs/LFTrustBoundary.md`;
- examples and tests guide: `Docs/Examples.md`;
- release workflow: `Docs/Releases.md`.
