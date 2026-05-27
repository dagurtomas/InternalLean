/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Generated structural model equivalence tests

These tests check that strict structural-equivalence generation is an explicit opt-in command and
that downstream code can use its generated fields to transport model data.
-/

@[expose] public section

/-- A minimal LF theory with a type field, an element field, a judgment, and a rule. -/
declare_type_theory ModelStructuralEquivBasic where
  /-- Object sort. -/
  syntax_sort Obj
  /-- Distinguished object. -/
  lf_opaque a : Obj
  /-- Unary judgment. -/
  judgment Rel (x : Obj)
  /-- Rule proving the judgment for any object. -/
  rule rel_intro (x : Obj) : Rel x

generate_model_interface ModelStructuralEquivBasic as StructuralEquivBasicModel

/-- error: Unknown constant `ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv` -/
#guard_msgs in
#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv

generate_model_structural_equiv ModelStructuralEquivBasic for StructuralEquivBasicModel

#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv
#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv.Obj_equiv
#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv.a_preserve
#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv.Rel_equiv
#check ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv.rel_intro_preserve

/-- The identity equivalence on `Unit`, used to fill generated structural-equivalence fields. -/
def unitTypeEquiv : InternalLean.TypeEquiv Unit Unit where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- A concrete model of `ModelStructuralEquivBasic`. -/
def structuralEquivBasicModel : ModelStructuralEquivBasic.StructuralEquivBasicModel where
  Obj := Unit
  a := ()
  Rel := fun _ => Unit
  rel_intro := fun _ => ()

/-- The generated strict structural equivalence can be filled for the identity model. -/
def structuralEquivBasicRefl :
    ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv
      structuralEquivBasicModel structuralEquivBasicModel where
  Obj_equiv := unitTypeEquiv
  a_preserve := by
    rfl
  Rel_equiv := by
    intro x x_target x_rel
    exact unitTypeEquiv
  rel_intro_preserve := by
    intro x x_target x_rel
    rfl

/-- A generated equivalence field transports judgment witnesses along the preserved point. -/
def transportBasicRelAtA
    {M N : ModelStructuralEquivBasic.StructuralEquivBasicModel}
    (e : ModelStructuralEquivBasic.StructuralEquivBasicModel.StructuralEquiv M N)
    (p : M.Rel M.a) : N.Rel N.a :=
  e.Rel_equiv M.a N.a e.a_preserve p

#check transportBasicRelAtA structuralEquivBasicRefl

/-- A dependent syntax-sort theory checks relational parameters in generated equivalence fields. -/
declare_type_theory ModelStructuralEquivDependent where
  /-- Base object sort. -/
  syntax_sort Obj
  /-- Terms indexed by objects. -/
  syntax_sort Tm (x : Obj)
  /-- Distinguished object. -/
  lf_opaque a : Obj
  /-- Distinguished term over any object. -/
  lf_opaque mkTm (x : Obj) : Tm x

generate_model_interface ModelStructuralEquivDependent as StructuralEquivDependentModel
generate_model_structural_equiv ModelStructuralEquivDependent for StructuralEquivDependentModel

#check ModelStructuralEquivDependent.StructuralEquivDependentModel.StructuralEquiv.Tm_equiv
#check ModelStructuralEquivDependent.StructuralEquivDependentModel.StructuralEquiv.mkTm_preserve

/-- A concrete model of the dependent structural-equivalence fixture. -/
def structuralEquivDependentModel :
    ModelStructuralEquivDependent.StructuralEquivDependentModel where
  Obj := Unit
  Tm := fun _ => Unit
  a := ()
  mkTm := fun _ => ()

/-- The generated dependent structural equivalence can be filled for the identity model. -/
def structuralEquivDependentRefl :
    ModelStructuralEquivDependent.StructuralEquivDependentModel.StructuralEquiv
      structuralEquivDependentModel structuralEquivDependentModel where
  Obj_equiv := unitTypeEquiv
  Tm_equiv := by
    intro x x_target x_rel
    exact unitTypeEquiv
  a_preserve := by
    rfl
  mkTm_preserve := by
    intro x x_target x_rel
    rfl

/-- A dependent generated equivalence field transports indexed syntax data. -/
def transportTmAtA
    {M N : ModelStructuralEquivDependent.StructuralEquivDependentModel}
    (e : ModelStructuralEquivDependent.StructuralEquivDependentModel.StructuralEquiv M N)
    (t : M.Tm M.a) : N.Tm N.a :=
  e.Tm_equiv M.a N.a e.a_preserve t

#check transportTmAtA structuralEquivDependentRefl

/-- A source field named `StructuralEquiv` should not collide with the generated nested type. -/
declare_type_theory ModelStructuralEquivNameCollision where
  /-- Field whose generated projection uses the preferred structural-equivalence name. -/
  syntax_sort StructuralEquiv

generate_model_interface ModelStructuralEquivNameCollision as StructuralEquivNameCollisionModel
generate_model_structural_equiv ModelStructuralEquivNameCollision for
  StructuralEquivNameCollisionModel

#check ModelStructuralEquivNameCollision.StructuralEquivNameCollisionModel.StructuralEquiv
#check ModelStructuralEquivNameCollision.StructuralEquivNameCollisionModel.StructuralEquiv1
