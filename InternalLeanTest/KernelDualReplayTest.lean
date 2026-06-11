/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command
public import InternalLean.LFElab.Kernel

/-!
# Structural kernel replay smoke tests

These tests keep the legacy `dualReplay` disagreement option default off, exercise checked-LF
expression lowering to `KTerm`, and run small checked theories through structural replay.
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
  let sortHead : CheckedLFHead := { name := `SameHead, kind := .syntaxSort, arity? := some 2 }
  let opaqueHead : CheckedLFHead := { name := `SameHead, kind := .opaque }
  match checkedLFExprToKTerm (.ident sortHead), checkedLFExprToKTerm (.ident opaqueHead) with
  | .ok sortTerm, .ok opaqueTerm =>
      unless Kernel.KTerm.alphaEq sortTerm opaqueTerm && sortTerm == opaqueTerm do
        throwError "structural KTerm equality depended on diagnostic head metadata"
  | .error err, _ | _, .error err => throwError "head lowering failed: {err}"

run_cmd do
  let outer ← withFreshMacroScope <| MonadQuotation.addMacroScope `x
  let inner ← withFreshMacroScope <| MonadQuotation.addMacroScope `x
  unless outer.eraseMacroScopes == inner.eraseMacroScopes && outer != inner do
    throwError "expected distinct hygienic binders with the same erased name"
  let expr : CheckedLFExpr :=
    .lam #[outer] (.lam #[inner] (.ident { name := outer, kind := .local }))
  match checkedLFExprToKTerm expr with
  | .ok (.lam (.lam (.bvar 1))) => pure ()
  | .ok other => throwError "hygienic outer binder lowered to the wrong index: {repr other}"
  | .error err => throwError "hygienic binder lowering failed: {err}"

run_cmd do
  let outer ← withFreshMacroScope <| MonadQuotation.addMacroScope `x
  let inner ← withFreshMacroScope <| MonadQuotation.addMacroScope `x
  let expr : CheckedLFExpr :=
    .lam #[outer] (.lam #[inner] (.ident { name := `x, kind := .local }))
  match checkedLFExprToKTerm expr with
  | .ok other => throwError "ambiguous erased binder lowered instead of failing: {repr other}"
  | .error err =>
      unless err.contains "ambiguous local" do
        throwError "expected ambiguous local diagnostic, got: {err}"

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

run_cmd do
  let dupMeta : Kernel.RuleMetaVar := {
    name := Kernel.KName.ofName `_arg1
    type? := some (.univ .zero) }
  let dupConstant : Kernel.LFConstantSchema := {
    name := Kernel.KName.ofName `DupConstant
    params := [dupMeta, dupMeta]
    resultType := .univ .zero }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `DuplicateConstantParamSmoke
    constants := [dupConstant] }
  match Kernel.ValidatedSignature.ofSignature sig with
  | .ok _ => throwError "structural kernel accepted duplicate constant parameter names"
  | .error err =>
      unless err.contains "duplicate" && err.contains "parameter" do
        throwError "expected duplicate-parameter diagnostic, got: {err}"

run_cmd do
  let dupMeta : Kernel.RuleMetaVar := { name := Kernel.KName.ofName `x }
  let ruleSchema : Kernel.RuleSchema := {
    name := Kernel.KName.ofName `dupRule
    metavariables := [dupMeta, dupMeta]
    conclusionStmt := { head := Kernel.KName.ofName `J } }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `DuplicateRuleMetaSmoke
    rules := [ruleSchema] }
  match Kernel.ValidatedSignature.ofSignature sig with
  | .ok _ => throwError "structural kernel accepted duplicate rule metavariable names"
  | .error err =>
      unless err.contains "duplicate" && err.contains "metavariable" do
        throwError "expected duplicate-metavariable diagnostic, got: {err}"

run_cmd do
  let kn (n : Name) := Kernel.KName.ofName n
  let ident (n : Name) : Kernel.KTerm := .ident { name := kn n }
  let X := kn `X
  let t := kn `t
  let elOf (arg : Kernel.KTerm) := Kernel.KTerm.mkApps (ident `El) [arg]
  let goodEl (A t : Kernel.KTerm) : Kernel.Judgment := {
    head := kn `GoodEl
    args := [A, t] }
  let metavariables : List Kernel.RuleMetaVar := [{
    name := X
    type? := some (ident `Obj)
  }, {
    name := t
    type? := some (elOf (.mvar X .arg))
    evidence? := some (goodEl (.mvar X .arg) (.mvar t .arg))
  }]
  let inst : Kernel.ScopedInstantiation := { entries := [{
    name := X
    type? := some (ident `Obj)
    value := ident `A
  }, {
    name := t
    type? := some (elOf (ident `A))
    evidence? := some (goodEl (ident `A) (ident `a))
    value := ident `a
  }] }
  match inst.validateAgainst metavariables with
  | .ok _ => pure ()
  | .error err => throwError "dependent scoped instantiation was rejected: {err}"

run_cmd do
  let badStmt : Kernel.Judgment := {
    head := Kernel.KName.ofName `J
    args := [.bvar 0] }
  let badRule : Kernel.RuleSchema := {
    name := Kernel.KName.ofName `bad
    conclusionStmt := badStmt }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `LooseBVarSmoke
    rules := [badRule] }
  let deriv := Kernel.KernelLFDerivation.ruleApp (Kernel.KName.ofName `bad) badStmt {} [] []
  match Kernel.CheckedKernelLFDerivation.ofReplay sig {} badStmt deriv with
  | .ok _ => throwError "structural checked replay accepted a loose de Bruijn index"
  | .error err =>
      unless err.contains "loose de Bruijn" do
        throwError "expected a loose de Bruijn rejection, got: {err}"

#check Kernel.CheckedKernelLFDerivation.toContextDeriv?
#check Kernel.KernelLFDerivation.ContextDeriv.interp

set_option internalLean.kernel.dualReplay true

run_cmd do
  let kn (n : Name) := Kernel.KName.ofName n
  let stmt : Kernel.Judgment := { head := kn `J }
  let badStmt : Kernel.Judgment := { head := kn `K }
  let sig : Kernel.Signature := {
    name := kn `StructuralDivergenceSmoke
    rules := [{ name := kn `intro, conclusionStmt := stmt }] }
  let badDeriv := Kernel.KernelLFDerivation.ruleApp (kn `intro) badStmt {} [] []
  let mut rejected := false
  try
    Lean.Elab.Command.liftCoreM <|
      validateStructuralKernelDualReplay "deliberate divergence" sig {} stmt badDeriv
  catch _ =>
    rejected := true
  unless rejected do
    throwError "structural dual-replay divergence branch did not fire"

declare_type_theory KernelDualReplaySmoke where
  syntax_sort Obj
  judgment Good (x : Obj)
  lf_opaque o : Obj
  rule good_o : Good o
  judgment_theorem o_good : Good o := good_o

#check_type_theory KernelDualReplaySmoke

declare_type_theory KernelDualReplayIndexedExplicitSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  lf_opaque A : Obj
  lf_opaque a : El A
  judgment GoodEl (X : Obj) (t : El X)
  rule good_el (X : Obj) (t : El X) : GoodEl X t
  judgment_theorem a_good : GoodEl A a := good_el A a

#check_type_theory KernelDualReplayIndexedExplicitSmoke

declare_type_theory KernelDualReplayIndexedImplicitSmoke where
  syntax_sort Obj
  syntax_sort El (A : Obj)
  syntax_sort Hom (x : Obj) (y : Obj)
  lf_opaque A : Obj
  lf_opaque a : El A
  lf_opaque idf {X : Obj} (x : El X) : El X
  lf_opaque idm (x : Obj) : Hom x x
  lf_opaque comp {x : Obj} {y : Obj} {z : Obj}
    (f : Hom x y) (g : Hom y z) : Hom x z
  judgment Good (x : Obj)
  judgment GoodEl {A : Obj} (t : El A)
  rule good_A : Good A
  rule good_el (X : Obj) (t : El X) : GoodEl t
  judgment_theorem a_good : GoodEl a := good_el A a
  judgment_theorem idf_a_good : GoodEl (idf {X := A} a) := good_el A (idf {X := A} a)

namespace KernelDualReplayIndexedImplicitSmoke

set_option internalLean.preferLeanQuotedFrontend true

internal def viaQuoted (f : Hom A A) : Hom A A := comp f (comp f f)
internal def withUnderscore : Hom A A := idm _
internal theorem a_good_again : GoodEl a := good_el A a

end KernelDualReplayIndexedImplicitSmoke

#check_type_theory KernelDualReplayIndexedImplicitSmoke
