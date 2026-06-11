# Internal tactic guide

Internal tactic scripts are available in `internal def ... := by` declarations. They use Lean's
tactic syntax and infoview plumbing, while InternalLean handlers operate on goals in the declared
type theory and compile to internal terms before the declaration is checked.

The displayed goals are Lean editor handles for object-theory goals. Solving still happens by
building an internal LF term and replaying it through the LF checker.

## Basic form

```lean
namespace T

internal def f : J := by
  exact term

end T
```

The annotation after `:` is the internal goal. Each tactic step either closes the current goal or
changes it to another internal goal that must be solved by later steps.

Binder-style declarations are also supported:

```lean
namespace T

internal def f (x : A) : B x := by
  exact body

end T
```

The generic frontend lowers this to an explicit internal function type and internal lambda. The
result still has to check in the declared theory.

## Supported tactics

Current syntax:

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
have h : J := by
  ...
refine term
refine head arg₁ _ ?_ (nested arg)
·
sorry
```

Raw compatibility scripts also accept the old `have ... := by ... end` spelling under
`internal_raw def ... := by`. Canonical native scripts use ordinary Lean tactic-block structure.

Internal tactic arguments for `exact head ...` and `refine head ...` are:

```lean
_
?_
name
(head arg₁ arg₂)
(term)
```

## `exact`

```lean
exact term
```

Uses `term` as the proof or value for the current goal. The term is checked when the resulting
`internal def` is registered.

```lean
exact head arg₁ arg₂
```

Uses a named rule, theorem, or internal declaration as an application head. This form can help with
explicit arguments and simple candidate matching.

```lean
exact sorry
```

Marks the whole `internal def` as admitted. This is declaration-wide; it is not a local proof hole.
Admissions can be listed with:

```lean
#lint_type_theory_sorries T
```

## `apply`

```lean
apply rule
```

Applies a named rule, checked theorem, or internal declaration whose conclusion matches the current
goal. Premises become new internal subgoals.

Example shape:

```lean
internal def ex : Goal := by
  apply some_rule
  · exact proof_of_first_premise
  · exact proof_of_second_premise
```

Focus bullets are supported for subgoals. If you start using bullets for the subgoals of an
`apply`, the following subgoals for that application should also be introduced with bullets.

Limitations:

- `apply` does not do broad theorem search.
- Side conditions are only synthesized when the current internal tactic support knows how to solve
  them; opaque side-condition certificates cause diagnostics.
- Candidate matching is internal-syntax matching plus checked internal conversion, not Lean
  typeclass inference or Lean unification.

## `assumption`

```lean
assumption
```

Searches the current internal context for a local hypothesis whose type is convertible to the
current goal.

The search is local and deterministic. It does not search global declarations.

## `intro` and `intros`

```lean
intros x y
```

Introduces leading internal arrows or function arrows in the current goal and adds the new variables
to the internal context.

Limitations:

- The current goal must be headed by an internal arrow/function-arrow.
- Names must be fresh in the internal context.
- There is no pattern destructuring or implicit-introduction search.

## `show` and `change`

```lean
show target
change target
```

Both replace the current goal by `target` when the old and new goals are equal by checked internal
conversion.

Use `show` when you want to state the target you expect. Use `change` when you want to rewrite the
current target into a more convenient convertible form.

These tactics use checked conversion evidence. They do not use Lean equality or internal equality
proof terms.

## `have`

```lean
have h : J := by
  ...
```

Solves a local internal subgoal `J`, then makes `h : J` available in the remaining goal.

Current limitation: `have` is compiled by substituting the proof term for `h` in the continuation.
It is useful as tactic structure, but it is not yet a general internal let-binding facility.

## `refine`

```lean
refine term
refine head arg₁ _ ?_ (nested arg)
```

`refine term` provides an internal term directly. The direct term form does not support holes.

`refine head ...` uses a named rule, theorem, or internal declaration as an application head.
Arguments may contain:

- `_` for an argument inferred from matching;
- `?_` for a subgoal solved by following tactic steps;
- nested named applications such as `(head arg)`.

Limitations:

- Arbitrary holes inside `refine term` are rejected.
- Nested `_` placeholders need a candidate head; they are not full unification variables.
- `?_` holes are solved left-to-right, depth-first, by following tactic steps.

## `rw`

```lean
rw h
rw ← h
rw [h₁, ← h₂]
```

`rw` rewrites the current internal goal using a named direct-LF rewrite candidate.

A rewrite candidate is usually one of:

1. a rule marked as a computation rule whose conclusion is a conversion judgment;
2. a `judgment_theorem` whose conclusion is a conversion judgment.

For rule-based rewrites, the theory needs role metadata like this:

```lean
judgment eqNat (lhs : Nat) (rhs : Nat)
judgment_role eqNat : term_conversion

rule beta_zero (base : Nat) (step : NatRecursor) : eqNat (natRec base step zero) base
rule_role beta_zero : computation
```

The conversion judgment must be marked with `judgment_role ... : type_conversion` or
`judgment_role ... : term_conversion`. For rule declarations, the rule must be marked with
`rule_role ... : computation`.

If the rewritten goal is judgmentally convertible to the old goal, no extra transport proof is
needed. For non-definitional rewrites, `rw` needs transport metadata explaining how relation
evidence transports the surrounding goal.

Typical transport metadata looks like:

```lean
rewrite_relation Eq [lhs, rhs]
transport_rule transport_for_Eq for Eq [evidence, source]
transport_position transport_for_Eq : Head [0]
```

Reverse rewriting needs symmetry metadata:

```lean
rewrite_symmetry eq_symm for Eq [evidence]
```

Nested rewriting needs congruence metadata:

```lean
rewrite_congruence congr_f for Eq under f [0] [evidence]
```

Limitations:

- Rewriting is direct-LF internal rewriting, not Lean `rw`.
- Matching is syntactic internal-pattern matching, modulo the supported checked conversion steps.
- The endpoint convention for conversion judgments currently uses the last two judgment arguments.
- Reverse non-definitional rewriting needs declared `rewrite_symmetry` metadata.
- Nested non-definitional rewriting needs declared `rewrite_congruence` metadata for each lifted
  head/argument position.

## `simp`

```lean
simp
simp [rule₁, rule₂]
simp only [rule₁, rule₂]
```

`simp` is a bounded internal simplifier. It changes the current internal goal, then asks the
remaining tactic script to solve the simplified goal.

The current simplifier tries these steps:

1. unfold checked `lf_def` definitions in the goal;
2. if no definition unfolding changed the goal, run a bounded loop over executable `beta`
   conversion-plugin steps and computation rewrites;
3. when a computation rewrite is not definitional, reuse the same transport metadata as `rw`.

### Marking computation rules for `simp`

To make a rule available to default `simp`, mark its conclusion judgment as a conversion judgment
and mark the rule as `computation`:

```lean
judgment eqNat (lhs : Nat) (rhs : Nat)
judgment_role eqNat : term_conversion

rule beta_zero (base : Nat) (step : NatRecursor) : eqNat (natRec base step zero) base
rule_role beta_zero : computation
```

`simp` extracts the last two arguments of `eqNat` as the rewrite endpoints. The example above
rewrites:

```lean
natRec base step zero
```

to:

```lean
base
```

A `judgment_theorem` whose conclusion is a conversion judgment can also be named in a `simp` list.

### Conversion-plugin steps for `simp`

A registered executable `beta` conversion plugin can participate in internal `simp`:

```lean
conversion_plugin beta_step executable [beta]
```

Currently only executable `beta` plugin steps are used by internal `simp`. Executable `eta` steps
are checked at the conversion-certificate boundary but are not used by internal `simp` yet; other
plugin-step classes remain metadata for now.

### `simp`, `simp [...]`, and `simp only [...]`

Default `simp` may use:

- all checked `lf_def` unfoldings not blocked by local names;
- all rules marked `rule_role ... : computation` whose conclusions are conversion judgments;
- all registered executable `beta` conversion plugins.

```lean
simp [extra]
```

uses the default set and also makes explicitly named rewrite candidates available. This is useful
for adding a named `judgment_theorem` that is not a rule marked `computation`.

```lean
simp only [name₁, name₂]
```

restricts simplification to the named LF definitions, named rewrite candidates, and named
conversion plugins.

### Fuel and diagnostics

The rewrite/plugin loop is bounded. If more progress is still possible after the fuel is exhausted,
`simp` reports the used rewrite/plugin trace and the last goal.

Current limitation: success traces are still minimal; the detailed trace is mainly exposed in fuel
exhaustion diagnostics.

## Focus bullets

```lean
· exact p
```

A focus bullet marks the start of a subgoal proof, especially after `apply` or `refine` with holes.
InternalLean uses Lean focus bullets while keeping the LF goal state and post-step audit under its
own control.

## Current limitations

The internal tactic language is small by design. Important current limitations include:

- Tactics operate on displayed object-theory goals; Lean metavariables are editor handles only.
- There is no general theorem search or `apply?` yet.
- There is no full Lean-style simplifier database or simp attributes.
- Internal `simp` only uses checked LF definition unfolding, executable `beta` plugins, and
  computation rewrites from metadata.
- Non-`beta` conversion-plugin steps are not yet used by internal `simp`.
- The internal simplifier has bounded fuel and minimal success tracing.
- `rw` and `simp` need explicit relation, transport, symmetry, and congruence metadata for
  non-definitional proof-producing rewrites.
- `have` is compiled by substitution and is not yet a general internal let binding.
- `refine` holes are supported only in the structured head-application form.
- Side-condition solving is limited to declared/trivial cases; opaque certificates remain trusted
  leaves and are reported by diagnostics.
- Internal conversion is LF evidence, not Lean equality.

Legacy raw object-tactic scripts are still accepted with `internal_raw def ... := by`. They use the
compatibility object-tactic compiler and get only a minimal root-goal infoview snapshot, rather than
per-step native tactic goal updates.

When a tactic fails, read the diagnostic as a statement about the declared type theory and its LF
metadata. Adding the right `judgment_role`, `rule_role`, rewrite metadata, or transport metadata is
often the fix.
