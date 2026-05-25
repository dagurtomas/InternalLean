/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Logical-framework metadata smoke tests

These tests exercise metadata-only direct-LF examples without depending on larger example suites.
-/

@[expose] public section

declare_type_theory DependentLFModelMetadata where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  syntax_sort Tm (Γ : Ctx) (A : Ty Γ)

  judgment wfCtx (Γ : Ctx)
  judgment wfTy (Γ : Ctx) (A : Ty Γ)
  judgment wfTm (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A)

  lf_opaque empty : Ctx
  lf_opaque U (Γ : Ctx) : Ty Γ
  lf_opaque pt (Γ : Ctx) : Tm Γ (U Γ)

  rule empty_wf where
    conclusion : wfCtx empty

  rule U_form (Γ : Ctx) where
    premise ctx : wfCtx Γ
    conclusion : wfTy Γ (U Γ)

  rule pt_intro (Γ : Ctx) where
    premise ctx : wfCtx Γ
    conclusion : wfTm Γ (U Γ) (pt Γ)

  judgment_theorem empty_ok : wfCtx empty := empty_wf

#print_lf_model_obligations DependentLFModelMetadata
#check_lf_model_obligations DependentLFModelMetadata
#print_lf_model_contract DependentLFModelMetadata
#print_lf_model_field_dependencies DependentLFModelMetadata
#print_lf_model_skeleton DependentLFModelMetadata
generate_lf_model_structure DependentLFModelMetadata as DependentLFModel
#print_lf_model_derived_statements DependentLFModelMetadata for DependentLFModel
#print_lf_model_derived_theorems DependentLFModelMetadata for DependentLFModel
generate_lf_model_derived_theorems DependentLFModelMetadata for DependentLFModel
#check DependentLFModelMetadata.DependentLFModel
#check DependentLFModelMetadata.DependentLFModel.Ty
#check DependentLFModelMetadata.DependentLFModel.Tm
#check DependentLFModelMetadata.DependentLFModel.empty_ok

declare_type_theory AbstractSideConditionMetadata where
  syntax_sort Obj
  judgment ok (x : Obj)
  side_condition_solver trivial_side_condition

  lf_opaque obj : Obj
  lf_opaque needsCert / 1

  rule ok_intro (x : Obj) where
    side_condition cert by trivial_side_condition : needsCert x
    conclusion : ok x

  judgment_theorem obj_ok : ok obj := ok_intro obj

#print_lf_model_obligations AbstractSideConditionMetadata
#check_lf_model_obligations AbstractSideConditionMetadata
#print_lf_model_summary AbstractSideConditionMetadata
#print_lf_model_skeleton AbstractSideConditionMetadata
generate_lf_model_structure AbstractSideConditionMetadata as AbstractSideConditionModel
#print_lf_model_derived_statements AbstractSideConditionMetadata for AbstractSideConditionModel
#print_lf_model_derived_theorems AbstractSideConditionMetadata for AbstractSideConditionModel
generate_lf_model_derived_theorems AbstractSideConditionMetadata for AbstractSideConditionModel
#check AbstractSideConditionMetadata.AbstractSideConditionModel
#check AbstractSideConditionMetadata.AbstractSideConditionModel.obj_ok

declare_type_theory AlgebraicRelationMetadata where
  syntax_sort Obj
  judgment relates (x : Obj) (y : Obj)

  lf_opaque unitObj : Obj
  lf_opaque mul (x : Obj) (y : Obj) : Obj

  rule unit_left (x : Obj) where
    conclusion : relates (mul unitObj x) x

  judgment_theorem unit_left_unit : relates (mul unitObj unitObj) unitObj :=
    unit_left unitObj

#print_lf_model_obligations AlgebraicRelationMetadata
#check_lf_model_obligations AlgebraicRelationMetadata
#print_lf_model_contract AlgebraicRelationMetadata
#print_lf_model_skeleton AlgebraicRelationMetadata
generate_lf_model_structure AlgebraicRelationMetadata as AlgebraicRelationModel
#print_lf_model_derived_theorems AlgebraicRelationMetadata for AlgebraicRelationModel
generate_lf_model_derived_theorems AlgebraicRelationMetadata for AlgebraicRelationModel
#check AlgebraicRelationMetadata.AlgebraicRelationModel
#check AlgebraicRelationMetadata.AlgebraicRelationModel.unit_left_unit

declare_type_theory LFDefinitionUnfoldingMetadata where
  syntax_sort Obj
  judgment ok (x : Obj)

  lf_opaque a : Obj
  lf_def aliasA : Obj := a

  rule ok_a : ok a

  judgment_theorem alias_ok_by_rule : ok aliasA := ok_a
  judgment_theorem alias_ok_by_ref : ok aliasA := alias_ok_by_rule

#check_type_theory LFDefinitionUnfoldingMetadata
#print_lf_model_artifacts LFDefinitionUnfoldingMetadata

declare_type_theory CertificateChainMetadata where
  syntax_sort Obj
  judgment ok (x : Obj)
  side_condition_solver trivial_side_condition

  lf_opaque a : Obj
  lf_opaque b : Obj
  lf_opaque needs_a / 1
  lf_opaque needs_b / 1

  rule ok_a (x : Obj) where
    side_condition cert_a by trivial_side_condition : needs_a x
    conclusion : ok x

  rule ok_b (x : Obj) (y : Obj) where
    premise previous : ok x
    side_condition cert_b by trivial_side_condition : needs_b y
    conclusion : ok y

  judgment_theorem a_ok : ok a := ok_a a
  judgment_theorem b_ok : ok b := ok_b a b a_ok

#print_lf_model_obligations CertificateChainMetadata
#check_lf_model_obligations CertificateChainMetadata
#print_lf_model_contract CertificateChainMetadata
#print_lf_model_summary CertificateChainMetadata
#print_lf_model_derived_statements CertificateChainMetadata for CertificateChainModel
#print_lf_model_skeleton CertificateChainMetadata
generate_lf_model_structure CertificateChainMetadata as CertificateChainModel
#print_lf_model_derived_theorems CertificateChainMetadata for CertificateChainModel
#check_lf_model_derived_theorems CertificateChainMetadata for CertificateChainModel
generate_lf_model_derived_theorems CertificateChainMetadata for CertificateChainModel
#check CertificateChainMetadata.CertificateChainModel
#check CertificateChainMetadata.CertificateChainModel.a_ok
#check CertificateChainMetadata.CertificateChainModel.b_ok

#check_lf_model_obligation_validation_self_tests
