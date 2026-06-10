/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Generic structural-metatheory smoke tests

These tests cover the first generic structural-metatheory milestone: checked rule metadata can be
organized into source-name-preserving induction cases without hard-coding any downstream theory.
-/

@[expose] public section

open InternalLean

declare_type_theory GenericInductionSimpleSmoke where
  syntax_sort Obj
  judgment Ok (x : Obj)

  lf_opaque base : Obj
  lf_opaque step (x : Obj) : Obj

  rule base_ok where
    conclusion : Ok base

  rule step_ok (x : Obj) where
    premise prev : Ok x
    conclusion : Ok (step x)

/--
info: rule induction for GenericInductionSimpleSmoke over Ok
cases: 2
recursive premises: 1

case base_ok
  parameters: none
  conclusion: Ok base

case step_ok
  parameters: (x : Obj)
  recursive premise prev : Ok x
  conclusion: Ok (step x)
-/
#guard_msgs (whitespace := lax) in
#print_judgment_induction GenericInductionSimpleSmoke Ok

/--
info: judgment induction metadata for GenericInductionSimpleSmoke.Ok: 2 case(s), 1 recursive
  premise(s)
-/
#guard_msgs (whitespace := lax) in
#check_judgment_induction GenericInductionSimpleSmoke Ok

generate_judgment_induction GenericInductionSimpleSmoke Ok
#check GenericInductionSimpleSmoke.OkDerivation
#check GenericInductionSimpleSmoke.OkDerivation.base_ok
#check GenericInductionSimpleSmoke.OkDerivation.step_ok

declare_type_theory GenericInductionMutualSmoke where
  syntax_sort Obj
  judgment Even (x : Obj)
  judgment Odd (x : Obj)

  lf_opaque zero : Obj
  lf_opaque succ (x : Obj) : Obj

  rule even_zero where
    conclusion : Even zero

  rule odd_succ (x : Obj) where
    premise prev : Even x
    conclusion : Odd (succ x)

  rule even_succ (x : Obj) where
    premise prev : Odd x
    conclusion : Even (succ x)

/--
info: rule induction for GenericInductionMutualSmoke over Even, Odd
cases: 3
recursive premises: 2

case even_zero
  parameters: none
  conclusion: Even zero

case odd_succ
  parameters: (x : Obj)
  recursive premise prev : Even x
  conclusion: Odd (succ x)

case even_succ
  parameters: (x : Obj)
  recursive premise prev : Odd x
  conclusion: Even (succ x)
-/
#guard_msgs (whitespace := lax) in
#print_rule_induction GenericInductionMutualSmoke for Even, Odd

/--
info: rule induction metadata for GenericInductionMutualSmoke over Even, Odd: 3 case(s), 2
  recursive premise(s)
-/
#guard_msgs (whitespace := lax) in
#check_rule_induction GenericInductionMutualSmoke for Even, Odd

generate_rule_induction GenericInductionMutualSmoke for Even, Odd
#check GenericInductionMutualSmoke.EvenDerivation
#check GenericInductionMutualSmoke.OddDerivation
#check GenericInductionMutualSmoke.EvenDerivation.even_zero
#check GenericInductionMutualSmoke.OddDerivation.odd_succ
#check GenericInductionMutualSmoke.EvenDerivation.even_succ

/--
error: rule-induction metadata for type theory 'GenericInductionSimpleSmoke' is not usable:
unknown judgment 'Missing' in checked type theory 'GenericInductionSimpleSmoke'
-/
#guard_msgs in
#check_judgment_induction GenericInductionSimpleSmoke Missing

declare_type_theory GenericStructuralMetadataSmoke where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx)
  syntax_sort_role Ctx : context
  syntax_sort_role Ty : type_sort
  syntax_sort_role Tm : term_sort
  context_zone ordinary : Ctx
  binder_class ordinaryVar : Tm in ordinary

  lf_opaque empty : Ctx
  lf_opaque baseTy (Γ : Ctx) : Ty Γ
  lf_opaque baseTm (Γ : Ctx) : Tm Γ
  lf_opaque ext (Γ : Ctx) (A : Ty Γ) : Ctx
  lf_opaque weakenTy (Γ : Ctx) (A : Ty Γ) : Ty (ext Γ A)
  lf_opaque substTy (Γ : Ctx) (A : Ty Γ) (a : Tm Γ) : Ty Γ

  judgment EqTm (Γ : Ctx) (a : Tm Γ) (b : Tm Γ) (A : Ty Γ)
  judgment_role EqTm : term_conversion

  lf_def baseTyAlias : Ty empty := baseTy empty

object_role GenericStructuralMetadataSmoke ext : context_extension
object_role GenericStructuralMetadataSmoke baseTm : newest_variable
object_role GenericStructuralMetadataSmoke weakenTy : structural_weakening for Ty
object_role GenericStructuralMetadataSmoke substTy : structural_substitution for Ty

#print_structural_metatheory GenericStructuralMetadataSmoke
#check_structural_metatheory GenericStructuralMetadataSmoke
#print_congruence_obligations GenericStructuralMetadataSmoke
#check_congruence_obligations GenericStructuralMetadataSmoke

/--
error: generic structural metadata for type theory 'GenericInductionSimpleSmoke' is incomplete:
no syntax_sort_role ... : context metadata is registered
no context_zone metadata is registered
no binder_class metadata is registered
no object_role ... : context_extension metadata is registered
no structural_weakening or structural_substitution object roles are registered
-/
#guard_msgs in
#check_structural_metatheory GenericInductionSimpleSmoke
