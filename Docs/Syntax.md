# InternalLean frontend syntax reference

This document records the public frontend syntax provided by `InternalLean.Command`. It focuses
on source syntax: theory declarations, LF declarations, metadata, `internal def`, internal
tactics, and user-facing model commands.

For a narrative introduction, see `Docs/UserGuide.md`.

## Import

```lean
import InternalLean.Command
```

## Theory commands

A theory declaration has one of these forms:

```lean
declare_type_theory T where
  ...

declare_type_theory T{u, v} where
  ...

declare_type_theory T extends Parent₁, Parent₂ where
  ...

declare_type_theory T{u, v} extends Parent₁, Parent₂ where
  ...
```

The braces after the theory name declare universe parameters for the type theory. They are not Lean
universe parameters, although backends may later translate them.

A previously declared theory can be reopened with:

```lean
extend_type_theory T where
  ...
```

Extensions append one declaration block to the existing theory and recheck the combined signature.
Use extensions for narrow additions instead of copying a theory block.

A docstring can precede `declare_type_theory` or `extend_type_theory`:

```lean
/-- Tiny natural numbers. -/
declare_type_theory TinyNat where
  ...
```

## Internal expression syntax

The declaration block uses a small internal expression language.

```lean
Type
Type u
Type max u v
x
_
(f x)
f x y
A → B
(x : A) → B
A ⇒ B
(x : A) ⇒ B
A × B
Σ x : A, B
⟨a, b⟩
fst p
snd p
fun x => body
fun x y => body
lhs ≡ rhs
{x := value}
```

Notes:

- `Type`, `Type u`, and `Type max u v` are internal universe expressions.
- `_` is an inferable placeholder in direct `internal def` terms when the surrounding expected
  type determines the omitted argument.
- `→` is compatibility notation for the framework's structural/function-family arrow.
- `⇒` is the explicit spelling of the same framework arrow for LF arities and dependent rule
  parameters. Use it when you want to avoid suggesting an internal function former.
- `fun x => body` builds an internal lambda.
- `A × B` and `Σ x : A, B` are structural product/record type expressions.
- `⟨a, b⟩`, `fst p`, and `snd p` build and project structural record values.
- `lhs ≡ rhs` is internal syntax for judgmental-equality-shaped expressions.
- `{x := value}` is an explicit implicit-argument marker used by the LF elaborator.

Binders in declaration telescopes use:

```lean
(x : A)
{x : A}
```

The second form marks an implicit LF binder.

## Declarations inside a theory block

Most declarations below can be preceded by a docstring. For example:

```lean
/-- Natural-number terms. -/
syntax_sort Nat
```

### Syntax sorts

```lean
syntax_sort S
syntax_sort S (x : A) {y : B}
syntax_sort Large : Type u
syntax_sort Family (x : Large) : Type v
```

A syntax sort declares an internal syntax family. Parameters may be explicit or implicit.
Unannotated syntax sorts use result universe `Type`, so their generated model field is a small
Lean type. Add `: Type u`, `: Type (u+1)`, or `: Type max u v` when a model carrier should live in
a higher Lean universe. Universe parameters used in result annotations must be declared on the
theory, for example `declare_type_theory T{u, v} where`.

```lean
syntax_sort_role S : role
```

`syntax_sort_role` is metadata. Common role names in examples include:

- `context`
- `type_sort`
- `term_sort`
- `side_structure`
- theory-specific names such as `cube_sort`, `tope_sort`, or `shape_sort`

Unknown role names are stored as metadata, but only recognized names affect generic automation.

### Syntax abbreviations

```lean
syntax_abbrev Name (x : A) {y : B} := value
```

A syntax abbreviation is public notation. It expands before checking and model-obligation
generation, so it normally does not become a model field. The value may be any checked LF type
expression, including structural function and Sigma/record types.

### Context zones and binder classes

```lean
context_zone Γ : Ctx
context_zone Δ : Ctx depends_on Γ, Θ

binder_class var : Tm in Γ
binder_class var : Tm in Γ depends_on Δ
```

Context zones and binder classes are metadata for scoped syntax and future multi-zone judgments.
They should describe generic binding structure, not example-specific behavior.

### Judgments

```lean
judgment J
judgment J (x : A) {y : B}
```

A judgment declares a predicate or relation in the declared type theory.

```lean
judgment_abbrev Alias (x : A) {y : B} := J x y
```

A judgment abbreviation is public notation for a judgment-headed expression. It expands before LF
checking and model-obligation generation, so it does not become a separate model field. Use it
when two judgment notations should share the same underlying judgment; use `judgment` only for a
new primitive judgment/model obligation. `syntax_abbrev` remains for LF type expressions and does
not alias judgments.

```lean
judgment_role J : role
```

Common judgment-role names include:

- `context_wellformedness`
- `type_formation`
- `term_typing`
- `type_conversion`
- `term_conversion`
- `substitution_wellformedness`
- `side_judgment`

The generic internal tactics currently use `type_conversion` and `term_conversion` to find
conversion judgments.

### LF opaque constants

```lean
lf_opaque c
lf_opaque c / 3
lf_opaque c (x : A) {y : B} : C
```

`lf_opaque` introduces a primitive LF constant or placeholder.

- The untyped form declares an opaque name with no type information.
- The arity form declares an untyped opaque name with an expected number of arguments.
- The typed form declares a constant with an LF telescope and result type. The result may be headed
  by a syntax sort or local family, or may be a structural function/Sigma package type.

Typed `lf_opaque` declarations usually become model-interface obligations unless hidden by model
visibility metadata.

### Rules

A rule with no premises can be written directly:

```lean
rule r (x : A) : J x
```

A rule with premises, evidence, side conditions, or a multiline conclusion uses `where`:

```lean
rule r (x : A) where
  premise p : J x
  evidence ev for x : K x
  side_condition ok by solver : input x
  conclusion : J (f x)
```

Rule items are:

```lean
premise name : judgment

evidence name for param : judgment

side_condition name by solver : input

conclusion : judgment
```

`evidence` declares that a rule parameter must come with an explicit premise proving a judgment
about that parameter. `side_condition` connects a side-condition input to a named solver.

Rule-role metadata has the form:

```lean
rule_role r : role
```

Recognized automation roles are:

```lean
formation
introduction
elimination
computation
structural
```

The `computation` role marks rules that prove conversion/equality consequences. Internal `simp`
uses these rules as rewrite candidates when they conclude in a judgment marked `type_conversion` or
`term_conversion`.

### Diagnostic macros and roles

```lean
object_macro T Name (x, y) => template
object_role T Name : role
object_role T Name : role for Related
#print_object_macros T
#print_object_roles T
#expand_object T expr
```

`object_macro` records theory-local diagnostic notation and can be expanded with `#expand_object`.
It is not part of checked LF elaboration: checked declarations should use the expanded expression.
If a macro head appears in a checked declaration, InternalLean rejects it with a diagnostic asking
for the expanded expression.

`object_role` attaches non-semantic role metadata to a declaration or macro.

### Rewrite and transport metadata

Internal `rw` and non-definitional `simp` steps use relation/transport metadata.

```lean
rewrite_relation R [lhs, rhs]
```

This says that `R` is a rewrite relation and names the parameters that are the left and right
endpoints.

```lean
transport_rule tr for R [evidence, source]
transport_position tr : Head [0]
```

A transport rule explains how evidence for relation `R` transports a source proof or value across a
larger judgment. `transport_position` tells automation which argument of `Head` is rewritten.

```lean
rewrite_symmetry symm for R [evidence]
```

A symmetry rule or theorem lets `rw ← h` synthesize reverse evidence for relation `R`.

```lean
rewrite_congruence congr for R under Head [0] [evidence]
```

A congruence rule or theorem lifts rewrite evidence through an argument position of `Head`. This is
used for nested internal rewrites.

### Side-condition solvers

```lean
side_condition_solver solver
```

This declares a theory-local side-condition solver handle. Side-condition certificates remain part
of the checked LF trust boundary; an opaque solver is a trusted leaf unless backed by a checked
hook.

### Conversion plugins

```lean
conversion_plugin c
conversion_plugin c opaque
conversion_plugin c external_certificate
conversion_plugin c executable
```

A conversion plugin may also declare supported generic step classes:

```lean
conversion_plugin c executable [beta]
conversion_plugin c opaque [beta, eta]
conversion_plugin c external_certificate [reindexing, side_condition]
```

Supported step names are:

```lean
beta
eta
reindexing
side_condition
sideCondition
plugin_axiom
pluginAxiom
```

Currently, internal `simp` can use registered executable `beta` steps. Other step classes are
metadata for the checked conversion-certificate boundary and future automation.

### Model visibility and sections

```lean
model_public decl
model_internal decl
model_compat decl
```

Visibility metadata affects generated public/minimal model interfaces.

- `model_public` marks a declaration as public-facing.
- `model_internal` hides a declaration from public/minimal interfaces.
- `model_compat` keeps compatibility/debug declarations out of public/minimal interfaces.

```lean
model_section SectionName
```

A model section marker groups following LF declarations into a named model-interface section until
another `model_section` marker appears. Repeating an existing section name resumes that section;
the first occurrence determines section-order diagnostics.

### Checked LF definitions and theorems

```lean
lf_def name : type := value
```

`lf_def` declares a checked LF definition. It unfolds during internal conversion and model
transport when supported.

```lean
judgment_theorem thm (x : A) {y : B} : J x y := proof
```

`judgment_theorem` declares a checked theorem for a custom judgment.

## Internal declarations

After a theory exists, internal declarations use `internal def`. Put unqualified declarations
inside the theory namespace:

```lean
namespace T

internal def f : J := value

internal def g : J := by
  exact value

internal def h : J := sorry

internal theorem th : J := proof

internal theorem admittedTh : J := sorry

end T
```

A qualified name can also select the target theory:

```lean
internal def T.f : J := value
```

Many declarations can be grouped in an incremental batch:

```lean
namespace T

internal_defs where
  def f : A := value
  def g : B f := value'
  def h : J := by
    exact proof
  def admitted : J := sorry

end T
```

Declarations in the batch are registered in source order; later declarations may refer to earlier
ones. Batched definitions support both direct terms and internal tactic scripts.
`internal theorem ... := sorry` records theorem-shaped formalization debt without adding a model
field.

Declaration-local universe parameters are supported:

```lean
internal def f{u, v} : J := value
```

Binder-style declarations are supported by the generic LF frontend:

```lean
internal def f (x : A) : B x := value

internal def g (x : A) : B x := by
  exact value

internal def admitted (x : A) : B x := sorry
```

Binder-style declarations lower to an explicit internal function type and internal lambda. The
binder syntax still depends on the theory having suitable function/lambda LF structure for the body
to check.

## Internal tactic syntax

Internal tactic mode is available after `:= by` in `internal def`.

```lean
exact term
exact head arg₁ arg₂
exact sorry
apply rule
assumption
show target
change target
rw h
rw ← h
rw [h₁, ← h₂]
simp
simp [rule₁, rule₂]
simp only [rule₁, rule₂]
intros x y
have h : J := proof
have h : J := by
  ...
end
refine term
refine head arg₁ _ ?_ (nested arg)
·
sorry
```

Internal tactic arguments for `exact head ...` and `refine head ...` are:

```lean
_
?_
name
(head arg₁ arg₂)
(term)
```

These tactics operate on internal goals, not Lean goals. They compile to internal terms before the
result is registered.

## User-facing diagnostic commands

Theory and declaration diagnostics:

```lean
#check_theory T
#check_type_theory_anchor T
#print_type_theory_anchor T
#print_type_theory T
#print_type_theories
#lint_type_theory_docs T
#lint_type_theory_sorries T
#print_internal_registration_profile T
#print_type_theory_side_conditions T
#expand_object T expr
```

Model workflow commands:

```lean
#print_model_obligations T
#print_public_model_obligations T
#check_model_obligations T
#check_public_model_obligations T
#print_model_interface T as M
#print_public_model_interface T as M
generate_model_interface T as M
generate_public_model_interface T as M
#print_model_template T as M
#print_public_model_template T as M
#print_model_structural_equiv T for M
#print_public_model_structural_equiv T for M
generate_model_structural_equiv T for M
generate_public_model_structural_equiv T for M
```

Generation commands must be run at the root namespace. Printing and checking commands are safe to
use for inspection before generation. Model interfaces do not include structural equivalences by
default; use `generate_model_structural_equiv T for M` when strict structure-preserving
comparisons between completed models are useful. Syntax-sort fields use the declared result
universe: unannotated sorts generate `S : Type`, while `syntax_sort S : Type u` generates
`S : Type u`.

`generate_lf_model_structure T as M` is the older direct-LF spelling for the same flat interface
generation path. Prefer `generate_model_interface T as M` in user-facing code.

Model sections:

```lean
#print_model_sections T
#print_public_model_sections T
#print_model_section_template T Section as Bundle
#print_public_model_section_template T Section as Bundle
generate_model_section_interface T as M
generate_public_model_section_interface T as M
generate_model_sections T as Sectioned adapting Flat
generate_public_model_sections T as Sectioned adapting Flat
#print_model_section_bundles T as Bundle adapting Flat
#print_public_model_section_bundles T as Bundle adapting Flat
generate_model_section_bundles T as Bundle adapting Flat
generate_public_model_section_bundles T as Bundle adapting Flat
```

Model transports:

```lean
#print_model_transport_status T for M
#print_model_transport_signature T f for M
generate_model_transport T f for M
#print_model_transports T for M
generate_model_transports T for M
generate_model_transports T only f g h for M
generate_lf_model_derived_theorems T for M
```

`generate_lf_model_derived_theorems` is an older theorem-only LF model method command. Prefer
`generate_model_transport` or `generate_model_transports` in new user-facing workflows. The older
`#print_lf_model_transports` and `generate_lf_model_transports` spellings remain as compatibility
aliases.

Developer diagnostics with names such as `#print_lf_model_*`, `#check_default_profile_lf_*`, and
`#print_checked_logical_framework_*` expose lower-level internals. Prefer the commands above in
public examples unless you are debugging the implementation.

## Deprecated syntax

`object_def` and `object_theorem` are deprecated compatibility shims. New code should use
`internal def`.

Regression files should avoid these shims except when they are testing legacy behavior.
