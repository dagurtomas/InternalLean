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

These tests exercise checked-LF expression lowering to `KTerm`, structural conversion
certificates, direct structural replay rejection, and small checked theories.
-/

@[expose] public section

open Lean InternalLean

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
  let kn (n : Name) := Kernel.KName.ofName n
  let stmt : Kernel.Judgment := { head := kn `J }
  let entry : Kernel.KernelLFTheoremEntry := { name := kn `dup, statement := stmt }
  let ctx : Kernel.KernelLFCheckContext := { theorems := [entry] }
  match Kernel.ValidatedReplayContext.ofContext ctx with
  | .ok validatedCtx =>
      match validatedCtx.addTheoremEntry entry with
      | .ok _ => throwError "incremental replay context accepted a duplicate theorem entry"
      | .error err =>
          unless err.contains "duplicate theorem" do
            throwError "expected duplicate-theorem diagnostic, got: {err}"
  | .error err => throwError "initial replay context validation failed: {err}"

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

run_cmd do
  let kn (n : Name) := Kernel.KName.ofName n
  let ident (n : Name) : Kernel.KTerm := .ident { name := kn n }
  let plugin : Kernel.ConversionPluginSchema := {
    name := kn `conv
    trust := .executableChecked
    supportedSteps := [.beta, .eta] }
  let sig : Kernel.Signature := {
    name := kn `StructuralConversionSmoke
    conversionPlugins := [plugin] }
  let checkStep (stmt : Kernel.ConversionStatement) (kind : ConversionStepKind) :=
    Kernel.CheckedKernelLFConversionCertificate.check sig {} stmt
      (.pluginStep stmt kind none [] "structural conversion test")
  let userLam := ident `lam
  let lamBody := Kernel.KTerm.mkApps userLam [.bvar 0, ident `a]
  let betaLhs := .app (.lam lamBody) (ident `a)
  let betaRhs := Kernel.KTerm.mkApps userLam [ident `a, ident `a]
  let betaStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := betaLhs
    rhs := betaRhs }
  match checkStep betaStmt .beta with
  | .ok _ => pure ()
  | .error err => throwError "structural beta conversion rejected user constant 'lam': {err}"
  let nestedBetaStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := .app (.lam (.lam (.bvar 1))) (ident `y)
    rhs := .lam (ident `y) }
  match checkStep nestedBetaStmt .beta with
  | .ok _ => pure ()
  | .error err => throwError "structural beta conversion captured a nested binder: {err}"
  let etaStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := .lam (.app (ident `f) (.bvar 0))
    rhs := ident `f }
  match checkStep etaStmt .eta with
  | .ok _ => pure ()
  | .error err => throwError "structural function eta conversion was rejected: {err}"
  let badEtaStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := .lam (.app (.app (ident `f) (.bvar 0)) (.bvar 0))
    rhs := ident `f }
  match checkStep badEtaStmt .eta with
  | .ok _ => throwError "structural function eta accepted a capturing redex"
  | .error err =>
      unless err.contains "eta step expected" do
        throwError "expected structural eta rejection, got: {err}"
  let pairStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := .pair (.fst (ident `p)) (.snd (ident `p))
    rhs := ident `p }
  match checkStep pairStmt .eta with
  | .ok _ => pure ()
  | .error err => throwError "structural sigma eta conversion was rejected: {err}"
  let badStmt : Kernel.ConversionStatement := {
    plugin := kn `conv
    lhs := betaLhs
    rhs := ident `a }
  match checkStep badStmt .beta with
  | .ok _ => throwError "structural beta conversion accepted the wrong reduct"
  | .error err =>
      unless err.contains "beta step reduces lhs" do
        throwError "expected structural beta mismatch diagnostic, got: {err}"

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
      discard <| checkStructuralKernelReplay "deliberate divergence" sig {} stmt badDeriv
  catch _ =>
    rejected := true
  unless rejected do
    throwError "structural replay divergence branch did not fire"

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
  judgment_theorem idf_a_good : GoodEl (idf (X := A) a) := good_el A (idf (X := A) a)

namespace KernelDualReplayIndexedImplicitSmoke

internal def viaQuoted (f : Hom A A) : Hom A A := comp f (comp f f)
internal def withUnderscore : Hom A A := idm _
internal theorem a_good_again : GoodEl a := good_el A a

end KernelDualReplayIndexedImplicitSmoke

#check_type_theory KernelDualReplayIndexedImplicitSmoke

declare_type_theory KernelDualReplayRP4ArtifactSmoke where
  syntax_sort Obj
  judgment Good (x : Obj)
  lf_opaque base : Obj
  lf_opaque step (x : Obj) : Obj
  rule base_ok where
    conclusion : Good base
  rule step_ok (x : Obj) where
    premise prev : Good x
    conclusion : Good (step x)
  judgment_theorem base_ok_thm : Good base := base_ok
  judgment_theorem base_ok_again : Good base := base_ok_thm
  judgment_theorem step_preserves_ok (x : Obj) (h : Good x) : Good (step x) :=
    step_ok x h
  judgment_theorem step_base_ok : Good (step base) :=
    step_preserves_ok base base_ok_thm

run_cmd do
  let some checked ← Lean.Elab.Command.liftCoreM <|
      getCheckedTheory? `KernelDualReplayRP4ArtifactSmoke
    | throwError "missing RP4 artifact smoke checked theory"
  let findTheorem (n : Name) : Lean.Elab.Command.CommandElabM CheckedLFJudgmentTheorem := do
    let some thm := checked.lfJudgmentTheorems.find? (fun t => t.name == n)
      | throwError "missing RP4 artifact smoke theorem '{n}'"
    pure thm
  let baseAgain ← findTheorem `base_ok_again
  let some baseArtifact := baseAgain.checkedStructuralReplay?
    | throwError "binder-free theorem reference did not get a compact replay artifact"
  if baseAgain.checkedStructuralKernelDerivation?.isSome ||
      baseAgain.structuralKernelDerivation?.isSome then
    throwError "compact replay theorem retained a full structural replay wrapper"
  unless baseArtifact.contextTheoremCount == 1 do
    throwError "binder-free theorem reference recorded wrong theorem-prefix count"
  match baseArtifact.derivation with
  | Kernel.KernelLFDerivation.theoremRef name _ =>
      unless name == Kernel.KName.ofName `base_ok_thm do
        throwError "binder-free theorem reference used the wrong replay-context entry"
  | _ => throwError "binder-free theorem reference did not lower to a context theorem reference"
  match checkedKernelLFReplayForTheorem checked baseAgain with
  | .ok checkedReplay =>
      unless checkedReplay.context.theorems.length == baseArtifact.contextTheoremCount do
        throwError "audit reconstruction used a different theorem-prefix length"
  | .error err => throwError "audit reconstruction of compact replay artifact failed: {err}"
  let signature ← match checkedSignatureToKSignature checked.name checked.lfSyntaxDefs
      checked.lfOpaqueConsts checked.lfContextZones checked.lfBinderClasses
      checked.lfConversionPlugins checked.lfRuleSchemas checked.lfObjectDefs
      checked.lfJudgmentTheorems with
    | .ok signature => pure signature
    | .error err => throwError "RP4 structural signature failed: {err}"
  let baseRule := Kernel.KName.ofName (lfJudgmentTheoremKernelRuleName `base_ok_thm)
  if signature.rules.any (fun r => r.name == baseRule) then
    throwError "binder-free theorem retained an unnecessary structural theorem-rule schema"
  let stepRule := Kernel.KName.ofName (lfJudgmentTheoremKernelRuleName `step_preserves_ok)
  unless signature.rules.any (fun r => r.name == stepRule) do
    throwError "theorem with binders lost its structural theorem-rule schema"
  let stepUse ← findTheorem `step_base_ok
  let some stepArtifact := stepUse.checkedStructuralReplay?
    | throwError "applied theorem reference did not get a compact replay artifact"
  match stepArtifact.derivation with
  | Kernel.KernelLFDerivation.ruleApp ruleName _ _ _ _ =>
      unless ruleName == stepRule do
        throwError "applied theorem reference used the wrong structural theorem-rule schema"
  | _ => throwError "applied theorem reference did not lower to a theorem-rule application"
  let corruptedArtifact := {
    baseArtifact with contextTheoremCount := baseArtifact.contextTheoremCount + 1 }
  let corrupted := { baseAgain with checkedStructuralReplay? := some corruptedArtifact }
  match kernelLFReplayCertificateForCheckedTheorem checked corrupted with
  | .ok _ => throwError "corrupted compact replay prefix count was accepted"
  | .error err =>
      unless err.contains "theorem-prefix count" do
        throwError "expected compact prefix-count diagnostic, got: {err}"


declare_type_theory AR1LazySchemaParent where
  syntax_sort Obj
  lf_opaque base : Obj
  judgment Good (x : Obj)
  rule good_intro (x : Obj) : Good x
  judgment_theorem parent_id (x : Obj) (h : Good x) : Good x := h

declare_type_theory AR1LazySchemaChild extends AR1LazySchemaParent where
  rule child_good_rule : Good base

namespace AR1LazySchemaChild

internal theorem child_good : Good base := child_good_rule
internal theorem use_parent_id : Good base := parent_id base child_good

end AR1LazySchemaChild

run_cmd do
  let some checked ← Lean.Elab.Command.liftCoreM <| getCheckedTheory? `AR1LazySchemaChild
    | throwError "missing AR1 lazy-schema child checked theory"
  let some parentTheorem := checked.lfJudgmentTheorems.find? (fun t =>
      t.name.eraseMacroScopes.getString! == "parent_id")
    | throwError "missing inherited parent_id theorem"
  let parentRule := Kernel.KName.ofName (lfJudgmentTheoremKernelRuleName parentTheorem.name)
  let noDemandFilter := StructuralTheoremSchemaFilter.demandOnly {}
  let noDemandStats := structuralTheoremSchemaFilterStats checked.lfJudgmentTheorems noDemandFilter
  unless noDemandStats.considered == 1 && noDemandStats.demanded == 0 &&
      noDemandStats.lowered == 0 do
    throwError "unexpected no-demand theorem-schema stats: {repr noDemandStats}"
  let noDemandSig ← match checkedSignatureToKSignature checked.name checked.lfSyntaxDefs
      checked.lfOpaqueConsts checked.lfContextZones checked.lfBinderClasses
      checked.lfConversionPlugins checked.lfRuleSchemas checked.lfObjectDefs
      checked.lfJudgmentTheorems false noDemandFilter with
    | .ok signature => pure signature
    | .error err => throwError "AR1 no-demand structural signature failed: {err}"
  if noDemandSig.rules.any (fun r => r.name == parentRule) then
    throwError "unrelated inherited theorem schema was lowered without demand"
  let demandFilter := StructuralTheoremSchemaFilter.demandOnly
    (({} : NameSet).insert parentTheorem.name.eraseMacroScopes)
  let demandStats := structuralTheoremSchemaFilterStats checked.lfJudgmentTheorems demandFilter
  unless demandStats.considered == 1 && demandStats.demanded == 1 &&
      demandStats.lowered == 1 do
    throwError "unexpected demanded theorem-schema stats: {repr demandStats}"
  let demandedSig ← match checkedSignatureToKSignature checked.name checked.lfSyntaxDefs
      checked.lfOpaqueConsts checked.lfContextZones checked.lfBinderClasses
      checked.lfConversionPlugins checked.lfRuleSchemas checked.lfObjectDefs
      checked.lfJudgmentTheorems false demandFilter with
    | .ok signature => pure signature
    | .error err => throwError "AR1 demanded structural signature failed: {err}"
  unless demandedSig.rules.any (fun r => r.name == parentRule) do
    throwError "demanded inherited theorem schema was not lowered"
  let some useParent := checked.lfJudgmentTheorems.find? (fun t =>
      t.name.eraseMacroScopes.getString! == "use_parent_id")
    | throwError "missing theorem that applies parent_id"
  let demandFromTheorem := structuralTheoremSchemaFilterForTheorem useParent
  unless demandFromTheorem.demandedTheorems.contains parentTheorem.name.eraseMacroScopes do
    throwError "applied theorem reference did not demand parent_id schema"


declare_type_theory RS1PrimitiveDemandParent where
  syntax_sort Obj
  lf_opaque base : Obj
  judgment Good (x : Obj)
  rule parent_good : Good base
  judgment_theorem parent_const (x : Obj) : Good base := parent_good


declare_type_theory RS1PrimitiveDemandChild extends RS1PrimitiveDemandParent where
  rule child_good_rule : Good base
  rule unrelated_rule (x : Obj) : Good x

namespace RS1PrimitiveDemandChild

internal theorem child_good : Good base := child_good_rule
internal theorem use_parent_const : Good base := parent_const base

end RS1PrimitiveDemandChild

run_cmd do
  let some checked ← Lean.Elab.Command.liftCoreM <| getCheckedTheory? `RS1PrimitiveDemandChild
    | throwError "missing RS1 primitive-demand child checked theory"
  let findTheorem (n : Name) : Lean.Elab.Command.CommandElabM CheckedLFJudgmentTheorem := do
    let some thm := checked.lfJudgmentTheorems.find? (fun t => t.name == n)
      | throwError "missing RS1 primitive-demand theorem '{n}'"
    pure thm
  let hasRule (signature : Kernel.Signature) (n : Name) : Bool :=
    signature.rules.any (fun r => r.name == Kernel.KName.ofName n)
  let signatureFor (t : CheckedLFJudgmentTheorem)
      (primitiveFilter : StructuralPrimitiveRuleSchemaFilter) :
      Lean.Elab.Command.CommandElabM Kernel.Signature := do
    match checkedSignatureToKSignature checked.name checked.lfSyntaxDefs checked.lfOpaqueConsts
        checked.lfContextZones checked.lfBinderClasses checked.lfConversionPlugins
        checked.lfRuleSchemas checked.lfObjectDefs checked.lfJudgmentTheorems false
        (structuralTheoremSchemaFilterForTheorem t) primitiveFilter with
    | .ok signature => pure signature
    | .error err => throwError "RS1 primitive-demand signature failed: {err}"
  let childGood ← findTheorem `child_good
  let childPrimitiveFilter := structuralPrimitiveRuleSchemaFilterForTheorem childGood
  let childStats := structuralPrimitiveRuleDemandStats checked.lfRuleSchemas childPrimitiveFilter
  unless childStats.considered == 3 && childStats.demanded == 1 &&
      childStats.lowered == 1 && childStats.demandedNames.contains `child_good_rule do
    throwError "unexpected direct primitive-demand stats: {repr childStats}"
  let childSig ← signatureFor childGood childPrimitiveFilter
  unless hasRule childSig `child_good_rule do
    throwError "demanded primitive rule was not lowered"
  if hasRule childSig `parent_good || hasRule childSig `unrelated_rule then
    throwError "undemanded primitive rule was lowered for direct primitive proof"
  let useParentConst ← findTheorem `use_parent_const
  let usePrimitiveFilter := structuralPrimitiveRuleSchemaFilterForTheorem useParentConst
  let useStats := structuralPrimitiveRuleDemandStats checked.lfRuleSchemas usePrimitiveFilter
  unless useStats.considered == 3 && useStats.demanded == 0 && useStats.lowered == 0 do
    throwError "unexpected theorem-reference primitive-demand stats: {repr useStats}"
  let useSig ← signatureFor useParentConst usePrimitiveFilter
  let parentConstRule := lfJudgmentTheoremKernelRuleName `parent_const
  unless hasRule useSig parentConstRule do
    throwError "demanded applied-theorem schema was not lowered"
  if hasRule useSig `parent_good || hasRule useSig `child_good_rule ||
      hasRule useSig `unrelated_rule then
    throwError "theorem-reference replay lowered an undemanded primitive rule"
  let emptyPrimitiveFilter := StructuralPrimitiveRuleSchemaFilter.demandOnly {}
  let missingSig ← signatureFor childGood emptyPrimitiveFilter
  let some shallowDeriv := childGood.derivation?
    | throwError "RS1 direct primitive theorem lost its checked derivation"
  let some sourceSig ← Lean.Elab.Command.liftCoreM <| getTheory? `RS1PrimitiveDemandChild
    | throwError "missing RS1 primitive-demand source theory"
  let flatSig ← Lean.Elab.Command.liftCoreM <| flattenSignature sourceSig
  let lfKernelDefValues :=
    lfDefinitionValueMapFromCheckedDefs checked.lfSyntaxDefs checked.lfObjectDefs
  let rejected ←
    try
      let _ ← Lean.Elab.Command.liftCoreM <|
        lowerLFDerivationToStructuralKernelWithMode flatSig (lfGlobalHeadInfo flatSig)
          lfKernelDefValues (theoremBinderFreeLocals childGood) childGood.name false
          missingSig shallowDeriv
      pure false
    catch _ =>
      pure true
  unless rejected do
    throwError "missing demanded primitive rule was accepted by structural lowering"

run_cmd do
  let some checked ← Lean.Elab.Command.liftCoreM <| getCheckedTheory? `RS1PrimitiveDemandChild
    | throwError "missing RS1 primitive-demand child checked theory"
  let some useParentConst := checked.lfJudgmentTheorems.find? (fun t =>
      t.name == `use_parent_const)
    | throwError "missing RS2 theorem-reference diagnostic theorem"
  let summary := renderStructuralReplaySignatureFilterSummary checked.lfRuleSchemas
    checked.lfJudgmentTheorems (structuralTheoremSchemaFilterForTheorem useParentConst)
    (structuralPrimitiveRuleSchemaFilterForTheorem useParentConst)
  for needle in #[
      "input_sizes=primitive_rules=3, judgment_theorems=3",
      "primitive_include_all=false",
      "primitive-rules considered=3, demanded=0, lowered=0",
      "theorem_include_all=false",
      "theorem-schemas considered=1, demanded=1, lowered=1",
      "demanded_names=parent_const"] do
    unless summary.contains needle do
      throwError "RS2 replay-signature diagnostic summary omitted '{needle}': {summary}"


declare_type_theory AR2CanonicalStatementSmoke where
  syntax_sort Obj
  lf_opaque base : Obj
  lf_def Alias : Obj := base
  lf_def idObj : Obj ⇒ Obj := fun x => x
  judgment Good (x : Obj)
  rule good_base : Good base
  judgment_theorem folded : Good Alias := good_base
  judgment_theorem expanded : Good base := good_base
  judgment_theorem folded_id (x : Obj) (h : Good (idObj x)) : Good (idObj x) := h
  judgment_theorem local_shadow (Alias : Obj) (h : Good Alias) : Good Alias := h

run_cmd do
  let some checked ← Lean.Elab.Command.liftCoreM <|
      getCheckedTheory? `AR2CanonicalStatementSmoke
    | throwError "missing AR2 canonical statement checked theory"
  let findTheorem (n : Name) : Lean.Elab.Command.CommandElabM CheckedLFJudgmentTheorem := do
    let some thm := checked.lfJudgmentTheorems.find? (fun t => t.name == n)
      | throwError "missing AR2 canonical statement theorem '{n}'"
    pure thm
  let folded ← findTheorem `folded
  let expanded ← findTheorem `expanded
  let foldedId ← findTheorem `folded_id
  let localShadow ← findTheorem `local_shadow
  let some foldedArtifact := folded.checkedStructuralReplay?
    | throwError "folded theorem did not get a replay artifact"
  let some expandedArtifact := expanded.checkedStructuralReplay?
    | throwError "expanded theorem did not get a replay artifact"
  let some foldedCanonical := foldedArtifact.canonicalStatement?
    | throwError "folded theorem did not cache canonical statement metadata"
  let some expandedCanonical := expandedArtifact.canonicalStatement?
    | throwError "expanded theorem did not cache canonical statement metadata"
  unless foldedCanonical.canonicalStatement.alphaEq expandedCanonical.canonicalStatement do
    throwError "folded and expanded theorem statements canonicalized differently"
  unless foldedCanonical.dependencies.contains `Alias do
    throwError "folded theorem canonical metadata did not record Alias as a dependency"
  unless !foldedCanonical.sourceStatement.alphaEq foldedCanonical.canonicalStatement do
    throwError "folded theorem source/canonical statements unexpectedly agree before unfolding"
  let replayCtx ← match kernelLFReplayContextOfTheoremsToK checked.lfJudgmentTheorems with
    | .ok ctx => pure ctx
    | .error err => throwError "AR2 replay context reconstruction failed: {err}"
  let foldedEntry? := replayCtx.theorems.find? (fun e => e.name == Kernel.KName.ofName `folded)
  let some foldedEntry := foldedEntry?
    | throwError "folded theorem missing from replay context"
  unless foldedEntry.statement.alphaEq foldedCanonical.canonicalStatement do
    throwError "replay context did not use the cached canonical folded theorem statement"
  match checkedKernelLFReplayForTheorem checked folded with
  | .ok checkedReplay =>
      unless checkedReplay.statement.alphaEq foldedArtifact.statement do
        throwError "audit replay payload stopped using the validated replay statement"
  | .error err => throwError "audit reconstruction for folded theorem failed: {err}"
  let defValues := checkedLFDefinitionValues checked.lfSyntaxDefs checked.lfObjectDefs
  let schema ← match kernelLFRuleSchemaOfTheoremToK false defValues foldedId with
    | .ok schema => pure schema
    | .error err => throwError "folded_id theorem schema lowering failed: {err}"
  if (structuralJudgmentGlobalHeadNames schema.conclusionStmt).contains `idObj then
    throwError "theorem schema conclusion reintroduced idObj instead of cached canonical form"
  let some localShadowCanonical := localShadow.checkedStructuralReplay?.bind
      (·.canonicalStatement?)
    | throwError "local-shadow theorem did not cache canonical statement metadata"
  if localShadowCanonical.dependencies.contains `Alias then
    throwError "local theorem binder activated a same-named global definition"
  let corruptedCanonical := {
    foldedCanonical with dependencies := foldedCanonical.dependencies.push `Bogus }
  let corruptedArtifact := { foldedArtifact with canonicalStatement? := some corruptedCanonical }
  let corrupted := { folded with checkedStructuralReplay? := some corruptedArtifact }
  match kernelLFReplayCertificateForCheckedTheorem checked corrupted with
  | .ok _ => throwError "audit accepted corrupted canonical dependency metadata"
  | .error err =>
      unless err.contains "dependency" do
        throwError "expected canonical dependency audit diagnostic, got: {err}"
