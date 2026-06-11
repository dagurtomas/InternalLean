/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Checker performance smoke tests

Large direct-LF declarations should remain practical after checker hardening. This file is a
compilation smoke test; `scripts/benchmark_checker.py` provides wall-clock scaling checks.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

/-- Test helper asserting that a structural rule conclusion preserves a compact LF-definition
    head. -/
elab "#guard_kernel_rule_conclusion_first_arg_head " theory:ident ruleName:ident expected:ident :
    command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let sig ←
    match checkedSignatureToKSignature checked.name checked.lfSyntaxDefs checked.lfOpaqueConsts
        checked.lfContextZones checked.lfBinderClasses checked.lfConversionPlugins
        checked.lfRuleSchemas checked.lfObjectDefs checked.lfJudgmentTheorems with
    | .ok sig => pure sig
    | .error err => throwError err
  let some schema := sig.rules.find? (fun r =>
      r.name.raw.eraseMacroScopes == ruleName.getId.eraseMacroScopes)
    | throwError "no structural rule schema '{ruleName.getId}' for type theory '{theory.getId}'"
  let some actualHead :=
      match schema.conclusionStmt.args with
      | arg :: _ =>
          match arg with
          | .ident h => some h.name.raw.eraseMacroScopes
          | .app (.ident h) _ => some h.name.raw.eraseMacroScopes
          | _ => none
      | _ => none
    | throwError "structural rule schema '{ruleName.getId}' has no headed first conclusion argument"
  unless actualHead == expected.getId.eraseMacroScopes do
    throwError "structural rule schema '{ruleName.getId}' first conclusion argument head is \
      '{actualHead}', expected '{expected.getId.eraseMacroScopes}'"

declare_type_theory CheckerPerfDefChain50 where
  syntax_sort Obj
  lf_opaque base : Obj
  lf_def d00 : Obj := base
  lf_def d01 : Obj := d00
  lf_def d02 : Obj := d01
  lf_def d03 : Obj := d02
  lf_def d04 : Obj := d03
  lf_def d05 : Obj := d04
  lf_def d06 : Obj := d05
  lf_def d07 : Obj := d06
  lf_def d08 : Obj := d07
  lf_def d09 : Obj := d08
  lf_def d10 : Obj := d09
  lf_def d11 : Obj := d10
  lf_def d12 : Obj := d11
  lf_def d13 : Obj := d12
  lf_def d14 : Obj := d13
  lf_def d15 : Obj := d14
  lf_def d16 : Obj := d15
  lf_def d17 : Obj := d16
  lf_def d18 : Obj := d17
  lf_def d19 : Obj := d18
  lf_def d20 : Obj := d19
  lf_def d21 : Obj := d20
  lf_def d22 : Obj := d21
  lf_def d23 : Obj := d22
  lf_def d24 : Obj := d23
  lf_def d25 : Obj := d24
  lf_def d26 : Obj := d25
  lf_def d27 : Obj := d26
  lf_def d28 : Obj := d27
  lf_def d29 : Obj := d28
  lf_def d30 : Obj := d29
  lf_def d31 : Obj := d30
  lf_def d32 : Obj := d31
  lf_def d33 : Obj := d32
  lf_def d34 : Obj := d33
  lf_def d35 : Obj := d34
  lf_def d36 : Obj := d35
  lf_def d37 : Obj := d36
  lf_def d38 : Obj := d37
  lf_def d39 : Obj := d38
  lf_def d40 : Obj := d39
  lf_def d41 : Obj := d40
  lf_def d42 : Obj := d41
  lf_def d43 : Obj := d42
  lf_def d44 : Obj := d43
  lf_def d45 : Obj := d44
  lf_def d46 : Obj := d45
  lf_def d47 : Obj := d46
  lf_def d48 : Obj := d47
  lf_def d49 : Obj := d48
  lf_def d50 : Obj := d49

#check_type_theory CheckerPerfDefChain50

declare_type_theory CheckerPerfTheoremChain50 where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  rule intro (x : Obj) : J x
  judgment_theorem t00 : J base := intro base
  judgment_theorem t01 : J base := t00
  judgment_theorem t02 : J base := t01
  judgment_theorem t03 : J base := t02
  judgment_theorem t04 : J base := t03
  judgment_theorem t05 : J base := t04
  judgment_theorem t06 : J base := t05
  judgment_theorem t07 : J base := t06
  judgment_theorem t08 : J base := t07
  judgment_theorem t09 : J base := t08
  judgment_theorem t10 : J base := t09
  judgment_theorem t11 : J base := t10
  judgment_theorem t12 : J base := t11
  judgment_theorem t13 : J base := t12
  judgment_theorem t14 : J base := t13
  judgment_theorem t15 : J base := t14
  judgment_theorem t16 : J base := t15
  judgment_theorem t17 : J base := t16
  judgment_theorem t18 : J base := t17
  judgment_theorem t19 : J base := t18
  judgment_theorem t20 : J base := t19
  judgment_theorem t21 : J base := t20
  judgment_theorem t22 : J base := t21
  judgment_theorem t23 : J base := t22
  judgment_theorem t24 : J base := t23
  judgment_theorem t25 : J base := t24
  judgment_theorem t26 : J base := t25
  judgment_theorem t27 : J base := t26
  judgment_theorem t28 : J base := t27
  judgment_theorem t29 : J base := t28
  judgment_theorem t30 : J base := t29
  judgment_theorem t31 : J base := t30
  judgment_theorem t32 : J base := t31
  judgment_theorem t33 : J base := t32
  judgment_theorem t34 : J base := t33
  judgment_theorem t35 : J base := t34
  judgment_theorem t36 : J base := t35
  judgment_theorem t37 : J base := t36
  judgment_theorem t38 : J base := t37
  judgment_theorem t39 : J base := t38
  judgment_theorem t40 : J base := t39
  judgment_theorem t41 : J base := t40
  judgment_theorem t42 : J base := t41
  judgment_theorem t43 : J base := t42
  judgment_theorem t44 : J base := t43
  judgment_theorem t45 : J base := t44
  judgment_theorem t46 : J base := t45
  judgment_theorem t47 : J base := t46
  judgment_theorem t48 : J base := t47
  judgment_theorem t49 : J base := t48
  judgment_theorem t50 : J base := t49

#check_type_theory CheckerPerfTheoremChain50

declare_type_theory CheckerPerfLazyLFDefKernelSchemaSmoke where
  syntax_sort Ty
  judgment J (A : Ty)
  lf_opaque base : Ty
  lf_def alias : Ty := base
  rule usesAlias : J alias

#guard_kernel_rule_conclusion_first_arg_head CheckerPerfLazyLFDefKernelSchemaSmoke usesAlias alias

/-- Synthetic version of the HoTT/MLTT rule-extension cliff.  Rebuilding an expanded structural
signature for the child rule eagerly would unfold `d24` into a large duplicated `pairObj` tree, even
though the rule-only extension does not need theorem replay. -/
declare_type_theory CheckerPerfLazyStructuralBase where
  syntax_sort Obj
  judgment J (x : Obj)
  lf_opaque base : Obj
  lf_opaque pairObj (x : Obj) (y : Obj) : Obj
  lf_def d00 : Obj := base
  lf_def d01 : Obj := pairObj d00 d00
  lf_def d02 : Obj := pairObj d01 d01
  lf_def d03 : Obj := pairObj d02 d02
  lf_def d04 : Obj := pairObj d03 d03
  lf_def d05 : Obj := pairObj d04 d04
  lf_def d06 : Obj := pairObj d05 d05
  lf_def d07 : Obj := pairObj d06 d06
  lf_def d08 : Obj := pairObj d07 d07
  lf_def d09 : Obj := pairObj d08 d08
  lf_def d10 : Obj := pairObj d09 d09
  lf_def d11 : Obj := pairObj d10 d10
  lf_def d12 : Obj := pairObj d11 d11
  lf_def d13 : Obj := pairObj d12 d12
  lf_def d14 : Obj := pairObj d13 d13
  lf_def d15 : Obj := pairObj d14 d14
  lf_def d16 : Obj := pairObj d15 d15
  lf_def d17 : Obj := pairObj d16 d16
  lf_def d18 : Obj := pairObj d17 d17
  lf_def d19 : Obj := pairObj d18 d18
  lf_def d20 : Obj := pairObj d19 d19
  lf_def d21 : Obj := pairObj d20 d20
  lf_def d22 : Obj := pairObj d21 d21
  lf_def d23 : Obj := pairObj d22 d22
  lf_def d24 : Obj := pairObj d23 d23

declare_type_theory CheckerPerfLazyStructuralChild extends CheckerPerfLazyStructuralBase where
  rule introHuge : J d24

#guard_kernel_rule_conclusion_first_arg_head CheckerPerfLazyStructuralChild introHuge d24

declare_type_theory CheckerPerfLazyLFDefConversionFallbackSmoke where
  syntax_sort Ty
  judgment J (A : Ty)
  lf_opaque base : Ty
  lf_def alias : Ty := base
  rule intro : J base
  judgment_theorem aliasTheorem : J alias := intro

#check_type_theory CheckerPerfLazyLFDefConversionFallbackSmoke

/--
error: rule 'bad' in type theory 'CheckerPerfRejectedBadIndex' has conclusion for judgment
'J' argument 'Ctx ⇒ Ctx' whose type cannot be inferred: 'Ctx ⇒ Ctx', expected 'Ctx'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory CheckerPerfRejectedBadIndex where
  syntax_sort Ctx
  syntax_sort Ty (Γ : Ctx)
  judgment J (Γ : Ctx) (A : Ty Γ)
  lf_opaque mkTy (Γ : Ctx) : Ty Γ
  lf_opaque c00 : Ctx
  lf_opaque c01 : Ctx
  lf_opaque c02 : Ctx
  lf_opaque c03 : Ctx
  lf_opaque c04 : Ctx
  lf_opaque c05 : Ctx
  lf_opaque c06 : Ctx
  lf_opaque c07 : Ctx
  lf_opaque c08 : Ctx
  lf_opaque c09 : Ctx
  rule bad : J (Ctx ⇒ Ctx) (mkTy (Ctx ⇒ Ctx))
