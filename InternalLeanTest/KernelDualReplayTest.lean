/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command
public import InternalLean.LFElab.Kernel

/-!
# Phase-5b structural kernel dual-replay smoke tests

The structural kernel is opt-in during Phase 5b. These tests keep the option default off,
exercise checked-LF-expression lowering to `KTerm`, and run a small checked theorem with dual
replay enabled.
-/

@[expose] public section

open Lean InternalLean

run_cmd do
  if ← getBoolOption `internalLean.kernel.dualReplay then
    throwError "internalLean.kernel.dualReplay must default to false"

run_cmd do
  let xHead : CheckedLFHead := { name := `x, kind := .local }
  let expr : CheckedLFExpr := .lam #[`x] (.ident xHead)
  match checkedLFExprToKTerm expr with
  | .ok (.lam (.bvar 0)) => pure ()
  | .ok other => throwError "expected structural lambda over de Bruijn index 0, got {repr other}"
  | .error err => throwError "checked LF expression failed to lower to KTerm: {err}"

run_cmd do
  let xHead : CheckedLFHead := { name := `x, kind := .local }
  let yHead : CheckedLFHead := { name := `y, kind := .local }
  let xLam : CheckedLFExpr := .lam #[`x] (.ident xHead)
  let yLam : CheckedLFExpr := .lam #[`y] (.ident yHead)
  match checkedLFExprToKTerm xLam, checkedLFExprToKTerm yLam with
  | .ok xTerm, .ok yTerm =>
      unless Kernel.KTerm.alphaEq xTerm yTerm do
        throwError "alpha-renamed checked lambdas lowered to distinct KTerms"
  | .error err, _ | _, .error err => throwError "lambda lowering failed: {err}"

run_cmd do
  let objHead : CheckedLFHead := { name := `Obj, kind := .syntaxSort }
  let obj : CheckedLFExpr := .ident objHead
  let namedArrow : CheckedLFExpr := .arrow (some `x) obj obj
  let anonArrow : CheckedLFExpr := .arrow none obj obj
  let namedSigma : CheckedLFExpr := .sigma (some `x) obj obj
  let anonSigma : CheckedLFExpr := .sigma none obj obj
  match checkedLFExprToKTerm namedArrow, checkedLFExprToKTerm anonArrow,
      checkedLFExprToKTerm namedSigma, checkedLFExprToKTerm anonSigma with
  | .ok ka, .ok kb, .ok ks, .ok kt =>
      unless Kernel.KTerm.alphaEq ka kb do
        throwError "named and anonymous non-dependent arrows lowered differently"
      unless Kernel.KTerm.alphaEq ks kt do
        throwError "named and anonymous non-dependent sigmas lowered differently"
  | .error err, _, _, _ | _, .error err, _, _ | _, _, .error err, _ | _, _, _, .error err =>
      throwError "arrow/sigma lowering failed: {err}"

run_cmd do
  let ctx : Kernel.KernelLFCheckContext := { localParameters := [Kernel.KLocalName.ofName `x,
      Kernel.KLocalName.ofName `x] }
  match Kernel.ValidatedReplayContext.ofContext ctx with
  | .ok _ => throwError "duplicate local parameters were accepted by the structural kernel"
  | .error _ => pure ()

run_cmd do
  let lamConstant : Kernel.LFConstantSchema := {
    name := Kernel.KName.ofName `lam
    resultType := .univ .zero }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `FormerStructuralName
    constants := [lamConstant] }
  match Kernel.ValidatedSignature.ofSignature sig with
  | .ok _ => pure ()
  | .error err => throwError "structural kernel rejected an ordinary constant named 'lam': {err}"

set_option internalLean.kernel.dualReplay true

declare_type_theory KernelDualReplaySmoke where
  syntax_sort Obj
  judgment Good (x : Obj)
  lf_opaque o : Obj
  rule good_o : Good o
  judgment_theorem o_good : Good o := good_o

#check_type_theory KernelDualReplaySmoke
