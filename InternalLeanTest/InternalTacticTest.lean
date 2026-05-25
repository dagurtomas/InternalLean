/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Minimal object tactic tests

These tests exercise UX-4 `internal def ... := by` scripts.
-/

@[expose] public section

open Lean

declare_type_theory InternalTacticLFSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment Wf (x : Obj)
  judgment Cert (x : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  side_condition_solver trivial_side_condition
  lf_opaque a : Obj
  lf_opaque b : Obj
  lf_opaque f (x : Obj) : Obj
  lf_def aliasA : Obj := a
  lf_def aliasB : Obj := b
  rule rel_refl (x : Obj) : Rel x x
  rule rel_a : Rel a a
  rule rel_twice (x : Obj) where
    premise left : Rel x x
    premise right : Rel x x
    conclusion : Rel x x
  rule rel_pair (x : Obj) (y : Obj) where
    premise left : Rel x x
    premise right : Rel y y
    conclusion : Rel x y
  rule rel_copy (x : Obj) (y : Obj) where
    premise source : Rel x x
    conclusion : Rel y y
  rule rel_fb : Rel (f b) b
  rule wf_a : Wf a
  rule wf_b : Wf b
  rule wf_f (x : Obj) where
    premise source : Wf x
    conclusion : Wf (f x)
  rule rel_transport_left (x : Obj) (y : Obj) (z : Obj) where
    premise eq : EqObj x y
    premise source : Rel y z
    premise target_ok : Wf x
    side_condition ok by trivial_side_condition : Cert x
    conclusion : Rel x z
  transport_rule rel_transport_left for EqObj [eq, source]
  transport_position rel_transport_left : Rel [0]
  rule eq_symm (x : Obj) (y : Obj) where
    premise e : EqObj x y
    premise target_ok : Wf y
    side_condition ok by trivial_side_condition : Cert y
    conclusion : EqObj y x
  rewrite_symmetry eq_symm for EqObj [e]
  rule eq_f_congr (x : Obj) (y : Obj) where
    premise e : EqObj x y
    premise source_ok : Wf x
    side_condition ok by trivial_side_condition : Cert x
    conclusion : EqObj (f x) (f y)
  rewrite_congruence eq_f_congr for EqObj under f [0] [e]
  rule eq_aliasA_to_a : EqObj aliasA a
  rule_role eq_aliasA_to_a : computation
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation

namespace InternalTacticLFSmoke

internal def rel_aa_exact : Rel a a := by
  exact rel_refl a

internal def rel_aa_apply : Rel a a := by
  apply rel_refl

internal def rel_aa_focused : Rel a a := by
  apply rel_twice
  · apply rel_refl
  · exact rel_refl a

internal def rel_aa_exact_app_infers_params : Rel a a := by
  exact rel_pair _ _ rel_aa_exact rel_aa_exact

internal def rel_aa_refine_nested_app_arg : Rel a a := by
  refine rel_pair _ _ (rel_refl _) ?_
  · exact rel_aa_exact

internal def rel_aa_refine_nested_app_holes : Rel a a := by
  refine rel_pair _ _ (rel_twice _ ?_ (rel_refl _)) ?_
  · exact rel_refl a
  · exact rel_aa_exact

internal def rel_aa_refine_app_holes : Rel a a := by
  refine rel_pair _ _ ?_ ?_
  · apply rel_refl
  · exact rel_refl a

internal def rel_aa_exact_parenthesized_complete : Rel a a := by
  exact (rel_refl a)

internal def rel_alias_exact_rule : Rel aliasA aliasA := by
  exact rel_a

internal def rel_alias_explicit_arg : Rel a a := by
  exact rel_refl aliasA

internal def rel_alias_apply_rule : Rel aliasA aliasA := by
  apply rel_a

internal def rel_alias_show_rule : Rel aliasA aliasA := by
  show Rel a a
  exact rel_a

internal def rel_alias_change_rule : Rel aliasA aliasA := by
  change Rel a a
  exact rel_a

internal def rel_alias_rw_rule : Rel aliasA aliasA := by
  rw eq_aliasA_to_a
  exact rel_refl a

internal def rel_alias_rw_list_rule : Rel aliasA aliasA := by
  rw [eq_aliasA_to_a]
  exact rel_refl a

internal def rel_a_rw_list_reverse_rule : Rel a a := by
  rw [← eq_aliasA_to_a, ← eq_aliasA_to_a]
  exact rel_alias_exact_rule

internal def rel_alias_simp_rule : Rel aliasA aliasA := by
  simp
  exact rel_refl a

internal def rel_ab_rw_transport_rule : Rel a b := by
  rw eq_a_to_b
  exact rel_refl b

internal def rel_bb_rw_reverse_transport_rule : Rel b b := by
  rw ← eq_a_to_b
  exact rel_ab_rw_transport_rule

internal def rel_fa_b_rw_nested_congr_transport_rule : Rel (f a) b := by
  rw eq_a_to_b
  exact rel_fb

internal def rel_ab_simp_transport_rule : Rel a b := by
  simp
  exact rel_refl b

internal def rel_ab_simp_list_transport_rule : Rel a b := by
  simp [eq_a_to_b]
  exact rel_refl b

internal def rel_alias_simp_only_definition_rule : Rel aliasA aliasA := by
  simp only [aliasA]
  exact rel_refl a

internal def rel_fa_b_simp_nested_congr_transport_rule : Rel (f a) b := by
  simp
  exact rel_fb

internal def rel_fa_b_simp_only_nested_congr_transport_rule : Rel (f a) b := by
  simp only [eq_a_to_b]
  exact rel_fb

internal def const_obj_intro : (x : Obj) → Obj := by
  intro x
  exact a

internal def id_obj_intro : (x : Obj) → Obj := by
  intro y
  exact y

internal def const_obj_intros : (x : Obj) → (y : Obj) → Obj := by
  intros x y
  exact x

internal def rel_have_assumption : Rel a a := by
  have h : Rel a a := by
    exact rel_a
  end
  assumption

internal def rel_have_explicit_premise : Rel a a := by
  have h : Rel a a := by
    exact rel_a
  end
  exact rel_copy a a h

/-- error: object tactic `rw []` failed: rewrite list is empty -/
#guard_msgs (whitespace := lax) in
internal def badRwEmptyList : Rel a a := by
  rw []
  exact rel_a

#guard
  let sig : InternalLean.HLSignature := {
    name := `T,
    lfObjectDefs := #[{ name := `aliasA, typeExpr := .ident `Obj, value := .ident `a }] }
  let lhs := InternalLean.ObjExpr.app (.app (.ident `Rel) (.ident `aliasA)) (.ident `aliasA)
  let rhs := InternalLean.ObjExpr.app (.app (.ident `Rel) (.ident `a)) (.ident `a)
  match InternalLean.checkObjectGoalConversion sig #[] #[] lhs rhs with
  | .ok cert =>
      cert.steps.size == 1 && cert.steps[0]!.kind == .lfDefinitionUnfolding &&
        cert.steps[0]!.unfoldedDefinitions == #[`aliasA]
  | .error _ => false

#guard
  let sig : InternalLean.HLSignature := {
    name := `T,
    judgments := #[{ name := `EqObj }],
    judgmentRoles := #[{ judgmentName := `EqObj, kind := `term_conversion }],
    lfObjectDefs := #[{
      name := `aliasA, typeExpr := .ident `Obj, value := .ident `a }],
    rules := #[{
      name := `eq_aliasA_to_a,
      conclusionExpr := .app (.app (.ident `EqObj) (.ident `aliasA)) (.ident `a) }],
    ruleRoles := #[{ ruleName := `eq_aliasA_to_a, kind := `computation }] }
  let target : InternalLean.InternalDefTarget := {
    theoryName := `InternalTacticLFSmoke, localName := `rwSmoke, anchorName := `rwSmoke }
  let lhs := InternalLean.ObjExpr.app (.app (.ident `Rel) (.ident `aliasA)) (.ident `aliasA)
  let rhs := InternalLean.ObjExpr.app (.app (.ident `Rel) (.ident `a)) (.ident `aliasA)
  match InternalLean.checkObjectRewrite target sig #[] #[] lhs `eq_aliasA_to_a false with
  | .ok cert => cert.newGoal == rhs && cert.conversion.steps.size == 1
  | .error _ => false

internal def rel_a_from_alias_premise : Rel a a := by
  refine rel_copy a a rel_alias_exact_rule

internal def rel_alias_from_expanded_premise : Rel aliasA aliasA := by
  refine rel_copy aliasA aliasA rel_a

internal def rel_alias_assumption (h : Rel a a) : Rel aliasA aliasA := by
  assumption

internal def rel_shadow_alias_assumption
    (aliasA : Obj) (h : Rel aliasA aliasA) : Rel aliasA aliasA := by
  assumption

/-- error: object tactic `intro h` failed: current goal is not an object arrow
  goal: Rel a a -/
#guard_msgs (whitespace := lax) in
internal def badIntroNonArrow : Rel a a := by
  intro h
  exact rel_a

/-- error: object tactic `intro x` failed: local name 'x' is already in the object context -/
#guard_msgs (whitespace := lax) in
internal def badIntroDuplicate : (x : Obj) → (y : Obj) → Obj := by
  intros x x
  exact x

/-- error: object tactic `have h` failed: local name 'h' is already in the object context -/
#guard_msgs (whitespace := lax) in
internal def badHaveDuplicate (h : Rel a a) : Rel a a := by
  have h : Rel a a := by
    exact rel_a
  end
  assumption

/-- error: object tactic `assumption` failed for goal
  Rel aliasA aliasA

Available object hypotheses:
  aliasA : Obj
  h : Rel a a -/
#guard_msgs (whitespace := lax) in
internal def badShadowAliasAssumption (aliasA : Obj) (h : Rel a a) : Rel aliasA aliasA := by
  assumption

/-- error: object tactic `apply rel_a` failed: conclusion
  Rel a a
does not match current goal
  Rel aliasB aliasB

normalized actual: Rel a a
normalized expected: Rel b b
LF definitions mentioned before unfolding: aliasB
LF definitions unfolded: aliasB -/
#guard_msgs (whitespace := lax) in
internal def badAliasApplyRejected : Rel aliasB aliasB := by
  apply rel_a

/-- error: object tactic `refine rel_pair ...` supplied 3 argument(s)/hole(s), but 4 explicit
argument slot(s) are required.

Omitted explicit arguments are never turned into subgoals. Use `_` only for inferable parameters,
and write `?_` exactly where `refine` should create an object-theory subgoal. -/
#guard_msgs (whitespace := lax) in
internal def badRefineOmittedHole : Rel a a := by
  refine rel_pair _ _ ?_
  · apply rel_refl

/-- error: object tactic `exact rel_pair` does not accept refinement hole `?_`; use `refine` or
provide a complete argument -/
#guard_msgs (whitespace := lax) in
internal def badExactHole : Rel a a := by
  exact rel_pair _ _ ?_ (rel_refl a)

/-- error: object tactic `exact` does not accept nested refinement hole `?_` in application
`rel_twice`; use `refine` or provide a complete argument -/
#guard_msgs (whitespace := lax) in
internal def badExactNestedHole : Rel a a := by
  exact rel_pair _ _ (rel_twice _ ?_ (rel_refl _)) (rel_refl a)

/-- error: object tactic `refine rel_pair ...` supplied 5 argument(s)/hole(s), but rule or
declaration 'rel_pair' has only 4 explicit argument slot(s).

Omitted explicit arguments are never turned into subgoals. Use `_` only for inferable parameters,
and write `?_` exactly where `refine` should create an object-theory subgoal. -/
#guard_msgs (whitespace := lax) in
internal def badRefineOverApplied : Rel a a := by
  refine rel_pair _ _ ?_ ?_ ?_
  · apply rel_refl
  · apply rel_refl
  · apply rel_refl

/-- error: object tactic `refine rel_pair` expected focus bullet `·` before the next refinement hole
for rule or declaration 'rel_pair' -/
#guard_msgs (whitespace := lax) in
internal def badRefineMissingFocusBullet : Rel a a := by
  refine rel_pair _ _ ?_ ?_
  · apply rel_refl
  apply rel_refl

#check rel_aa_exact
#check rel_aa_apply
#check rel_aa_focused
#check rel_aa_exact_app_infers_params
#check rel_aa_refine_nested_app_arg
#check rel_aa_refine_nested_app_holes
#check rel_aa_refine_app_holes
#check rel_aa_exact_parenthesized_complete
#check rel_alias_exact_rule
#check rel_alias_explicit_arg
#check rel_alias_apply_rule
#check rel_alias_show_rule
#check rel_alias_change_rule
#check rel_alias_rw_rule
#check rel_alias_rw_list_rule
#check rel_a_rw_list_reverse_rule
#check rel_alias_simp_rule
#check rel_ab_rw_transport_rule
#check rel_bb_rw_reverse_transport_rule
#check rel_fa_b_rw_nested_congr_transport_rule
#check rel_ab_simp_transport_rule
#check rel_ab_simp_list_transport_rule
#check rel_alias_simp_only_definition_rule
#check rel_fa_b_simp_nested_congr_transport_rule
#check rel_fa_b_simp_only_nested_congr_transport_rule
#check const_obj_intro
#check id_obj_intro
#check const_obj_intros
#check rel_have_assumption
#check rel_have_explicit_premise
#check rel_a_from_alias_premise
#check rel_alias_from_expanded_premise
#check rel_alias_assumption
#check rel_shadow_alias_assumption

end InternalTacticLFSmoke

generate_model_interface InternalTacticLFSmoke as InternalTacticLFSmokeModel

generate_lf_model_transports InternalTacticLFSmoke only
  rel_aa_exact
  rel_aa_apply
  rel_aa_refine_nested_app_holes
  rel_alias_rw_rule
  rel_ab_rw_transport_rule
  rel_bb_rw_reverse_transport_rule
  rel_fa_b_rw_nested_congr_transport_rule
  rel_ab_simp_transport_rule
  rel_ab_simp_list_transport_rule
  rel_alias_simp_only_definition_rule
  rel_fa_b_simp_nested_congr_transport_rule
  rel_fa_b_simp_only_nested_congr_transport_rule
  const_obj_intro
  id_obj_intro
  rel_have_explicit_premise
for InternalTacticLFSmokeModel

namespace InternalTacticLFSmoke

#check InternalTacticLFSmokeModel.rel_aa_exact
#check InternalTacticLFSmokeModel.rel_aa_apply
#check InternalTacticLFSmokeModel.rel_aa_refine_nested_app_holes
#check InternalTacticLFSmokeModel.rel_alias_rw_rule
#check InternalTacticLFSmokeModel.rel_ab_rw_transport_rule
#check InternalTacticLFSmokeModel.rel_bb_rw_reverse_transport_rule
#check InternalTacticLFSmokeModel.rel_fa_b_rw_nested_congr_transport_rule
#check InternalTacticLFSmokeModel.rel_ab_simp_transport_rule
#check InternalTacticLFSmokeModel.rel_ab_simp_list_transport_rule
#check InternalTacticLFSmokeModel.rel_alias_simp_only_definition_rule
#check InternalTacticLFSmokeModel.rel_fa_b_simp_nested_congr_transport_rule
#check InternalTacticLFSmokeModel.rel_fa_b_simp_only_nested_congr_transport_rule
#check InternalTacticLFSmokeModel.const_obj_intro
#check InternalTacticLFSmokeModel.id_obj_intro
#check InternalTacticLFSmokeModel.rel_have_explicit_premise

variable (M : InternalTacticLFSmokeModel)

example : M.Rel M.a M.a :=
  InternalTacticLFSmokeModel.rel_aa_exact M

example : M.Rel M.a M.a :=
  InternalTacticLFSmokeModel.rel_aa_refine_nested_app_holes M

example (certA : M.Cert M.a) : M.Rel M.a M.b :=
  InternalTacticLFSmokeModel.rel_ab_rw_transport_rule M certA

example (certB₁ certB₂ : M.Cert M.b) (certA : M.Cert M.a) : M.Rel M.b M.b :=
  InternalTacticLFSmokeModel.rel_bb_rw_reverse_transport_rule M certB₁ certB₂ certA

example (certFa : M.Cert (M.f M.a)) (certA : M.Cert M.a) : M.Rel (M.f M.a) M.b :=
  InternalTacticLFSmokeModel.rel_fa_b_rw_nested_congr_transport_rule M certFa certA

example (certA : M.Cert M.a) : M.Rel M.a M.b :=
  InternalTacticLFSmokeModel.rel_ab_simp_transport_rule M certA

example (certA : M.Cert M.a) : M.Rel M.a M.b :=
  InternalTacticLFSmokeModel.rel_ab_simp_list_transport_rule M certA

example : M.Rel M.a M.a :=
  InternalTacticLFSmokeModel.rel_alias_simp_only_definition_rule M

example (certFa : M.Cert (M.f M.a)) (certA : M.Cert M.a) : M.Rel (M.f M.a) M.b :=
  InternalTacticLFSmokeModel.rel_fa_b_simp_nested_congr_transport_rule M certFa certA

example (certFa : M.Cert (M.f M.a)) (certA : M.Cert M.a) : M.Rel (M.f M.a) M.b :=
  InternalTacticLFSmokeModel.rel_fa_b_simp_only_nested_congr_transport_rule M certFa certA

example (x : M.Obj) : M.Obj :=
  InternalTacticLFSmokeModel.id_obj_intro M x

end InternalTacticLFSmoke

declare_type_theory InternalTacticSimpFuelSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  lf_opaque a : Obj
  lf_opaque b : Obj
  rule rel_refl (x : Obj) : Rel x x
  rule rel_transport_left (x : Obj) (y : Obj) (z : Obj) where
    premise eq : EqObj x y
    premise source : Rel y z
    conclusion : Rel x z
  transport_rule rel_transport_left for EqObj [eq, source]
  transport_position rel_transport_left : Rel [0]
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation
  rule eq_b_to_a : EqObj b a
  rule_role eq_b_to_a : computation

namespace InternalTacticSimpFuelSmoke

/-- error: object tactic `simp` exhausted its rewrite fuel
used rewrite rules:
  eq_a_to_b
  eq_b_to_a
  eq_a_to_b
  eq_b_to_a
  eq_a_to_b
  eq_b_to_a
  eq_a_to_b
  eq_b_to_a
last goal: Rel a a -/
#guard_msgs (whitespace := lax) in
internal def bad_simp_loop : Rel a a := by
  simp
  exact rel_refl a

end InternalTacticSimpFuelSmoke

declare_type_theory InternalTacticSimpPluginSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  lf_opaque a : Obj
  rule rel_a : Rel a a
  conversion_plugin beta_step executable [beta]

namespace InternalTacticSimpPluginSmoke

internal def beta_plugin_simp : Rel ((fun x => x) a) a := by
  simp only [beta_step]
  exact rel_a

internal def beta_plugin_simp_default : Rel ((fun x => x) a) a := by
  simp
  exact rel_a

#check beta_plugin_simp
#check beta_plugin_simp_default

end InternalTacticSimpPluginSmoke

declare_type_theory InternalTacticNoTransportSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  lf_opaque a : Obj
  lf_opaque b : Obj
  rule rel_refl (x : Obj) : Rel x x
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation

namespace InternalTacticNoTransportSmoke

/-- error: object tactic `rw eq_a_to_b` found rewrite candidate 'eq_a_to_b' (→)
and rewrote the current object goal, but the goal change is not justified by
the checked direct-LF conversion engine yet.
  old goal: Rel a b
  new goal: Rel b b
conversion failure: checked object conversion rejected the endpoints
No declared proof/evidence transport could justify this rewrite either.
object tactic `rw eq_a_to_b` found rewrite evidence for 'EqObj'
but no `transport_rule` metadata is declared for that relation -/
#guard_msgs (whitespace := lax) in
internal def bad_rw_missing_transport : Rel a b := by
  rw eq_a_to_b
  exact rel_refl b

end InternalTacticNoTransportSmoke

declare_type_theory InternalTacticNoSymmetrySmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  lf_opaque a : Obj
  lf_opaque b : Obj
  rule rel_refl (x : Obj) : Rel x x
  rule rel_transport_left (x : Obj) (y : Obj) (z : Obj) where
    premise eq : EqObj x y
    premise source : Rel y z
    conclusion : Rel x z
  transport_rule rel_transport_left for EqObj [eq, source]
  transport_position rel_transport_left : Rel [0]
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation

namespace InternalTacticNoSymmetrySmoke

internal def rel_ab_via_transport : Rel a b := by
  rw eq_a_to_b
  exact rel_refl b

/-- error: object tactic `rw eq_a_to_b` found rewrite candidate 'eq_a_to_b' (←)
and rewrote the current object goal, but the goal change is not justified by
the checked direct-LF conversion engine yet.
  old goal: Rel b b
  new goal: Rel a b
conversion failure: checked object conversion rejected the endpoints
No declared proof/evidence transport could justify this rewrite either.
object tactic `rw ← eq_a_to_b` needs reverse evidence for 'EqObj'
but no `rewrite_symmetry` metadata is declared for that relation -/
#guard_msgs (whitespace := lax) in
internal def bad_rw_reverse_missing_symmetry : Rel b b := by
  rw ← eq_a_to_b
  exact rel_ab_via_transport

end InternalTacticNoSymmetrySmoke

declare_type_theory InternalTacticNoCongruenceSmoke where
  syntax_sort Obj
  judgment Rel (x : Obj) (y : Obj)
  judgment EqObj (x : Obj) (y : Obj)
  judgment_role EqObj : term_conversion
  rewrite_relation EqObj [x, y]
  lf_opaque a : Obj
  lf_opaque b : Obj
  lf_opaque f (x : Obj) : Obj
  rule rel_fb : Rel (f b) b
  rule rel_transport_left (x : Obj) (y : Obj) (z : Obj) where
    premise eq : EqObj x y
    premise source : Rel y z
    conclusion : Rel x z
  transport_rule rel_transport_left for EqObj [eq, source]
  transport_position rel_transport_left : Rel [0]
  rule eq_a_to_b : EqObj a b
  rule_role eq_a_to_b : computation

namespace InternalTacticNoCongruenceSmoke

/-- error: object tactic `rw eq_a_to_b` found rewrite candidate 'eq_a_to_b' (→)
and rewrote the current object goal, but the goal change is not justified by
the checked direct-LF conversion engine yet.
  old goal: Rel (f a) b
  new goal: Rel (f b) b
conversion failure: checked object conversion rejected the endpoints
No declared proof/evidence transport could justify this rewrite either.
object tactic `rw eq_a_to_b` found rewrite evidence for 'EqObj'
and transport metadata for that relation, but no declared transport rule matched
  old goal: Rel (f a) b
  new goal: Rel (f b) b
  evidence: EqObj a b
The tactic expects a transport rule whose conclusion is the old goal,
whose evidence premise matches the oriented rewrite evidence, and whose
source premise matches the rewritten goal.
For nested rewrites, declare rewrite_congruence metadata for each lifted head. -/
#guard_msgs (whitespace := lax) in
internal def bad_rw_nested_missing_congruence : Rel (f a) b := by
  rw eq_a_to_b
  exact rel_fb

end InternalTacticNoCongruenceSmoke
