/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab

/-!
# LF replay audit and certificate helpers

This module contains checked replay-wrapper, compact certificate, and trust-dependency helpers.
Diagnostics and model rendering should use these APIs instead of rebuilding raw replay contexts
ad hoc.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Insert all names from `extra` into `names`, erasing macro scopes first. -/
def insertNameSet (names extra : NameSet) : NameSet :=
  extra.toList.foldl (fun acc n => acc.insert n.eraseMacroScopes) names

/-- Global LF constant/former names mentioned by a raw kernel expression. -/
partial def rawGlobalHeadNames : Raw → NameSet
  | .ctxNil | .ctxMeta _ | .tyMeta _ | .tmVar _ | .tmMeta _ | .substMeta _
  | .substEmpty | .leanParam _ => {}
  | .tyConst n | .tmConst n => {n.eraseMacroScopes}
  | .tyApp n args | .tmApp n args =>
      args.foldl
        (fun names arg => insertNameSet names (rawGlobalHeadNames arg))
        ({n.eraseMacroScopes} : NameSet)
  | .ctxExt Γ A | .tySubst Γ A | .tmSubst Γ A | .substComp Γ A | .substExt Γ A =>
      insertNameSet (rawGlobalHeadNames Γ) (rawGlobalHeadNames A)
  | .substId Γ => rawGlobalHeadNames Γ
  | .scopedBind _ _ _ ty body => insertNameSet (rawGlobalHeadNames ty)
      (rawGlobalHeadNames body)

/-- Global LF constant/former names mentioned by a kernel judgment. -/
def judgmentGlobalHeadNames : Judgment → NameSet
  | .wfCtx Γ => rawGlobalHeadNames Γ
  | .wfTy Γ A => insertNameSet (rawGlobalHeadNames Γ) (rawGlobalHeadNames A)
  | .wfTm Γ t A =>
      insertNameSet (insertNameSet (rawGlobalHeadNames Γ) (rawGlobalHeadNames t))
        (rawGlobalHeadNames A)
  | .wfSubst Δ σ Γ =>
      insertNameSet (insertNameSet (rawGlobalHeadNames Δ) (rawGlobalHeadNames σ))
        (rawGlobalHeadNames Γ)
  | .eqTy Γ A B =>
      insertNameSet (insertNameSet (rawGlobalHeadNames Γ) (rawGlobalHeadNames A))
        (rawGlobalHeadNames B)
  | .eqTm Γ t u A =>
      insertNameSet
        (insertNameSet (insertNameSet (rawGlobalHeadNames Γ) (rawGlobalHeadNames t))
          (rawGlobalHeadNames u))
        (rawGlobalHeadNames A)
  | .custom _ args => args.foldl (fun names arg => insertNameSet names
      (rawGlobalHeadNames arg)) {}

/-- Global LF names mentioned in one kernel rule schema. -/
def ruleSchemaGlobalHeadNames (r : RuleSchema) : NameSet := Id.run do
  let mut names : NameSet := {}
  for v in r.metavariables do
    if let some ty := v.type? then
      names := insertNameSet names (rawGlobalHeadNames ty)
    if let some ev := v.evidence? then
      names := insertNameSet names (judgmentGlobalHeadNames ev)
  for p in r.premises do
    names := insertNameSet names (judgmentGlobalHeadNames p)
  for sc in r.sideConditions do
    for arg in sc.args do
      names := insertNameSet names (rawGlobalHeadNames arg)
  for slot in r.sideConditionCertificates do
    for arg in slot.condition.args do
      names := insertNameSet names (rawGlobalHeadNames arg)
  for cert in r.checkedSideConditionCertificates do
    for arg in cert.condition.args do
      names := insertNameSet names (rawGlobalHeadNames arg)
  names := insertNameSet names (judgmentGlobalHeadNames r.conclusion)
  return names

/-- Global LF names mentioned in a scoped rule instantiation. -/
def scopedInstantiationGlobalHeadNames (inst : ScopedInstantiation) : NameSet := Id.run do
  let mut names : NameSet := {}
  for e in inst.entries do
    if let some ty := e.type? then
      names := insertNameSet names (rawGlobalHeadNames ty)
    if let some ev := e.evidence? then
      names := insertNameSet names (judgmentGlobalHeadNames ev)
    names := insertNameSet names (rawGlobalHeadNames e.value)
  return names

/-- Rule names actually used by a kernel-facing replay tree. -/
partial def kernelLFDerivationRuleAppNames : KernelLFDerivation → NameSet
  | .assumption .. | .theoremRef .. | .certificate .. => {}
  | .ruleApp ruleName _ _ premises _ =>
      List.foldl
        (fun names => fun prem => insertNameSet names (kernelLFDerivationRuleAppNames prem))
        ({ruleName.eraseMacroScopes} : NameSet) premises

/-- Global LF names mentioned by a kernel-facing replay tree. -/
partial def kernelLFDerivationGlobalHeadNames : KernelLFDerivation → NameSet
  | .assumption _ stmt | .theoremRef _ stmt | .certificate _ stmt _ =>
      judgmentGlobalHeadNames stmt
  | .ruleApp _ concl inst premises _ =>
      let names := insertNameSet (judgmentGlobalHeadNames concl)
        (scopedInstantiationGlobalHeadNames inst)
      List.foldl
        (fun names => fun prem => insertNameSet names
          (kernelLFDerivationGlobalHeadNames prem))
        names premises

/-- Exact replay-leaf dependencies used by a kernel-facing replay artifact. -/
structure KernelLFReplayDependencySummary where
  /-- Local theorem assumptions used by replay leaves. -/
  localAssumptions : NameSet := {}
  /-- Earlier closed theorem references used by replay leaves. -/
  theoremReferences : NameSet := {}
  /-- Certificate-obligation names used by replay leaves. -/
  certificateObligations : NameSet := {}
  /-- External certificate payload names used by replay leaves or side-condition slots. -/
  externalCertificates : NameSet := {}
  /-- Primitive or theorem-rule applications used by replay nodes. -/
  ruleApplications : NameSet := {}
  /-- Global LF constants/formers mentioned in statements and instantiations. -/
  globalHeads : NameSet := {}
  deriving Inhabited

namespace KernelLFReplayDependencySummary

/-- Merge two replay-dependency summaries. -/
def merge (a b : KernelLFReplayDependencySummary) : KernelLFReplayDependencySummary :=
  { localAssumptions := insertNameSet a.localAssumptions b.localAssumptions
    theoremReferences := insertNameSet a.theoremReferences b.theoremReferences
    certificateObligations := insertNameSet a.certificateObligations b.certificateObligations
    externalCertificates := insertNameSet a.externalCertificates b.externalCertificates
    ruleApplications := insertNameSet a.ruleApplications b.ruleApplications
    globalHeads := insertNameSet a.globalHeads b.globalHeads }

end KernelLFReplayDependencySummary

/-- Exact replay-leaf dependencies for a kernel-facing replay tree. -/
partial def kernelLFReplayDependencySummary : KernelLFDerivation → KernelLFReplayDependencySummary
  | .assumption name stmt =>
      { localAssumptions := {name.eraseMacroScopes}
        globalHeads := judgmentGlobalHeadNames stmt }
  | .theoremRef name stmt =>
      { theoremReferences := {name.eraseMacroScopes}
        globalHeads := judgmentGlobalHeadNames stmt }
  | .certificate name stmt certificateName =>
      { certificateObligations := {name.eraseMacroScopes}
        externalCertificates := {certificateName.eraseMacroScopes}
        globalHeads := judgmentGlobalHeadNames stmt }
  | .ruleApp ruleName concl inst premises certificateNames =>
      let own : KernelLFReplayDependencySummary :=
        { externalCertificates := certificateNames.foldl (fun s n => s.insert n.eraseMacroScopes) {}
          ruleApplications := {ruleName.eraseMacroScopes}
          globalHeads :=
            insertNameSet (judgmentGlobalHeadNames concl)
              (scopedInstantiationGlobalHeadNames inst) }
      premises.foldl (fun acc prem => acc.merge (kernelLFReplayDependencySummary prem)) own

/-- Names of LF opaque constants declared by a checked signature. -/
def checkedLFOpaqueNameSet (checked : CheckedSignature) : NameSet :=
  checked.lfOpaqueConsts.foldl (init := {}) fun names c => names.insert c.name.eraseMacroScopes

/-- LF opaque constants mentioned by a replay dependency summary. -/
def replayOpaqueHeadNames (checked : CheckedSignature)
    (deps : KernelLFReplayDependencySummary) : NameSet :=
  let opaqueNames := checkedLFOpaqueNameSet checked
  deps.globalHeads.toList.foldl (init := {}) fun names n =>
    if opaqueNames.contains n then names.insert n else names

/-- Stable short rendering for a set of names. -/
def nameSetSummary (names : NameSet) : String :=
  let xs := names.toList.map (fun n => toString n.eraseMacroScopes)
  if xs.isEmpty then "none" else String.intercalate ", " xs

/-- Source-ish rendering for an LF name in replay diagnostics. -/
def lfReplayNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Source-ish rendering for raw LF payload syntax, depth-limited for diagnostics. -/
partial def rawSourceStringWithDepth : Nat → Raw → String
  | 0, _ => "..."
  | _ + 1, .ctxNil => "emptyCtx"
  | _ + 1, .ctxMeta n => s!"?{lfReplayNameString n}"
  | depth + 1, .ctxExt Γ A =>
      s!"ctxExt ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | _ + 1, .tyMeta n => s!"?{lfReplayNameString n}"
  | _ + 1, .tyConst n => lfReplayNameString n
  | depth + 1, .tyApp n args =>
      let rendered := args.map (rawSourceStringWithDepth depth)
      s!"{lfReplayNameString n} {String.intercalate " " rendered}"
  | depth + 1, .tySubst Γ A =>
      s!"tySubst ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | _ + 1, .tmVar i => s!"#{i}"
  | _ + 1, .tmMeta n => s!"?{lfReplayNameString n}"
  | _ + 1, .tmConst n => lfReplayNameString n
  | depth + 1, .tmApp n args =>
      let rendered := args.map (rawSourceStringWithDepth depth)
      s!"{lfReplayNameString n} {String.intercalate " " rendered}"
  | depth + 1, .tmSubst Γ t =>
      s!"tmSubst ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t})"
  | depth + 1, .substId Γ => s!"substId ({rawSourceStringWithDepth depth Γ})"
  | _ + 1, .substMeta n => s!"?{lfReplayNameString n}"
  | depth + 1, .substComp σ τ =>
      s!"substComp ({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth τ})"
  | _ + 1, .substEmpty => "emptySubst"
  | depth + 1, .substExt σ t =>
      s!"substExt ({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth t})"
  | depth + 1, .scopedBind zone cls x ty body =>
      s!"bind {lfReplayNameString x} : {rawSourceStringWithDepth depth ty} in " ++
        s!"{rawSourceStringWithDepth depth body} [{lfReplayNameString zone}/" ++
        s!"{lfReplayNameString cls}]"
  | _ + 1, .leanParam n => lfReplayNameString n

/-- Source-ish rendering for a kernel judgment in replay diagnostics. -/
def judgmentSourceStringWithDepth (depth : Nat) : Judgment → String
  | .wfCtx Γ => s!"wfCtx {rawSourceStringWithDepth depth Γ}"
  | .wfTy Γ A =>
      s!"wfTy ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | .wfTm Γ t A =>
      s!"wfTm ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t}) " ++
        s!"({rawSourceStringWithDepth depth A})"
  | .wfSubst Δ σ Γ =>
      s!"wfSubst ({rawSourceStringWithDepth depth Δ}) " ++
        s!"({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth Γ})"
  | .eqTy Γ A B =>
      s!"eqTy ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A}) " ++
        s!"({rawSourceStringWithDepth depth B})"
  | .eqTm Γ t u A =>
      s!"eqTm ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t}) " ++
        s!"({rawSourceStringWithDepth depth u}) ({rawSourceStringWithDepth depth A})"
  | .custom n args =>
      let rendered := args.map (rawSourceStringWithDepth depth)
      s!"{lfReplayNameString n} {String.intercalate " " rendered}"

/-- Compact source-ish replay-tree rendering with a depth and size budget. -/
partial def kernelLFDerivationSourceStringWithDepth : Nat → KernelLFDerivation → String
  | 0, _ => "..."
  | depth + 1, .assumption name stmt =>
      s!"assumption {lfReplayNameString name} : {judgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .theoremRef name stmt =>
      s!"theorem {lfReplayNameString name} : {judgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .certificate name stmt cert =>
      s!"certificate {lfReplayNameString name} via {lfReplayNameString cert} : " ++
        s!"{judgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .ruleApp ruleName concl inst premises certs =>
      let entryNames := inst.entries.map (fun e => lfReplayNameString e.name)
      let premiseText := premises.take 3 |>.map (kernelLFDerivationSourceStringWithDepth depth)
      let morePremises := if premises.length > 3 then [s!"... +{premises.length - 3} more"] else []
      let certText := certs.map lfReplayNameString
      s!"rule {lfReplayNameString ruleName} : {judgmentSourceStringWithDepth depth concl}; " ++
        s!"inst [{String.intercalate ", " entryNames}]; " ++
        s!"premises [{String.intercalate "; " (premiseText ++ morePremises)}]; " ++
        s!"certificates [{String.intercalate ", " certText}]"

/-- Source-ish rendering for resolved checked LF expressions. -/
partial def checkedLFExprSourceStringWithDepth : Nat → CheckedLFExpr → String
  | 0, _ => "..."
  | _ + 1, .ident h => lfReplayNameString h.name
  | _ + 1, .sort => "Type"
  | _ + 1, .univ u => s!"Type {u}"
  | depth + 1, .app f a =>
      s!"({checkedLFExprSourceStringWithDepth depth f} " ++
        s!"{checkedLFExprSourceStringWithDepth depth a})"
  | depth + 1, .arrow none A B =>
      s!"({checkedLFExprSourceStringWithDepth depth A} ⇒ " ++
        s!"{checkedLFExprSourceStringWithDepth depth B})"
  | depth + 1, .arrow (some x) A B =>
      s!"(({lfReplayNameString x} : {checkedLFExprSourceStringWithDepth depth A}) ⇒ " ++
        s!"{checkedLFExprSourceStringWithDepth depth B})"
  | depth + 1, .lam xs body =>
      let binders := String.intercalate " " (xs.toList.map lfReplayNameString)
      s!"(fun {binders} => {checkedLFExprSourceStringWithDepth depth body})"
  | depth + 1, .jeq lhs rhs =>
      s!"({checkedLFExprSourceStringWithDepth depth lhs} ≡ " ++
        s!"{checkedLFExprSourceStringWithDepth depth rhs})"

/-- Source-ish rendering for shallow checked LF derivations. -/
partial def checkedLFDerivationSourceStringWithDepth : Nat → CheckedLFDerivation → String
  | 0, _ => "..."
  | _ + 1, .localAssumption name stmt =>
      s!"assumption {lfReplayNameString name} : {stmt}"
  | depth + 1, .theoremRef name stmt args premises =>
      let argText := if args.isEmpty then "" else s!" args={args.size}"
      let premiseText := premises.toList.take 3 |>.map
        (checkedLFDerivationSourceStringWithDepth depth)
      let morePremises := if premises.size > 3 then [s!"... +{premises.size - 3} more"] else []
      s!"theorem {lfReplayNameString name} : {stmt}{argText}; premises " ++
        s!"[{String.intercalate "; " (premiseText ++ morePremises)}]"
  | depth + 1, .ruleApp ruleName stmt args premises certs =>
      let argText := if args.isEmpty then "" else s!" args={args.size}"
      let premiseText := premises.toList.take 3 |>.map
        (checkedLFDerivationSourceStringWithDepth depth)
      let morePremises := if premises.size > 3 then [s!"... +{premises.size - 3} more"] else []
      let certText := certs.toList.map lfReplayNameString
      s!"rule {lfReplayNameString ruleName} : {stmt}{argText}; premises " ++
        s!"[{String.intercalate "; " (premiseText ++ morePremises)}]; certificates " ++
        s!"[{String.intercalate ", " certText}]"

/-- Default source-ish target rendering for replay-audit summaries. -/
def replayAuditTargetString (stmt : Judgment) : String :=
  truncateDiagnosticString 600 (judgmentSourceStringWithDepth 6 stmt)

/-- Default source-ish checked LF expression rendering for diagnostics. -/
def replayAuditCheckedLFExprString (expr : CheckedLFExpr) : String :=
  truncateDiagnosticString 600 (checkedLFExprSourceStringWithDepth 6 expr)

/-- Default source-ish shallow derivation rendering for diagnostics. -/
def replayAuditCheckedLFDerivationString (derivation : CheckedLFDerivation) : String :=
  truncateDiagnosticString 1200 (checkedLFDerivationSourceStringWithDepth 5 derivation)

/-- Default source-ish derivation rendering for replay-audit summaries. -/
def replayAuditDerivationString (derivation : KernelLFDerivation) : String :=
  truncateDiagnosticString 1200 (kernelLFDerivationSourceStringWithDepth 5 derivation)

/-- Kernel-facing signature fragment for a compact replay certificate. -/
def kernelLFReplayCertificateSignature (checked : CheckedSignature)
    (derivation : KernelLFDerivation) : Signature :=
  let usedRules := kernelLFDerivationRuleAppNames derivation
  let allRules :=
    (checked.lfKernelRuleSchemas ++
      kernelLFRuleSchemasOfTheorems (checkedLFDefinitionValues checked.lfObjectDefs)
        checked.lfJudgmentTheorems).toList
  let rules := allRules.filter (fun r => usedRules.contains r.name.eraseMacroScopes)
  let usedGlobals := rules.foldl
    (fun names r => insertNameSet names (ruleSchemaGlobalHeadNames r))
    (kernelLFDerivationGlobalHeadNames derivation)
  { name := checked.name
    constants := (checkedLFConstantsToKernel (checkedLFDefinitionValues checked.lfObjectDefs)
      checked.lfOpaqueConsts checked.lfObjectDefs |>.toList).filter (fun c =>
        usedGlobals.contains c.name.eraseMacroScopes)
    contextZones := checked.lfContextZones.toList.map checkedLFContextZoneToKernel
    binderClasses := checked.lfBinderClasses.toList.map checkedLFBinderClassToKernel
    conversionPlugins := checked.lfConversionPlugins.toList.map checkedLFConversionPluginToKernel
    rules := rules }

/-- Kernel-facing replay statement for a theorem, preferring checked cached replay wrappers. -/
def kernelLFReplayStatementOfTheorem? (t : CheckedLFJudgmentTheorem) : Option Judgment :=
  match t.checkedKernelDerivation? with
  | some checkedReplay => some checkedReplay.statement
  | none => KernelLFDerivation.statement <$> t.kernelDerivation?

/-- Kernel-facing replay payload for a theorem, preferring checked cached replay wrappers. -/
def kernelLFReplayPayloadOfTheorem? (t : CheckedLFJudgmentTheorem) :
    Option (Judgment × KernelLFDerivation) :=
  match t.checkedKernelDerivation? with
  | some checkedReplay => some (checkedReplay.statement, checkedReplay.derivation)
  | none =>
      match t.kernelDerivation? with
      | some derivation => some (KernelLFDerivation.statement derivation, derivation)
      | none => none

/-- Previously checked closed LF theorems that precede a theorem in source order. -/
def precedingClosedLFTheoremEntries (theorems : Array CheckedLFJudgmentTheorem)
    (theoremName : Name) : List KernelLFTheoremEntry := Id.run do
  let mut out : List KernelLFTheoremEntry := []
  for t in theorems do
    if t.name.eraseMacroScopes == theoremName.eraseMacroScopes then
      return out.reverse
    if t.binders.isEmpty then
      let statement :=
        (kernelLFReplayStatementOfTheorem? t).getD
          (checkedLFJudgmentExprToKernel t.checkedJudgmentExpr t.judgmentHead)
      out := { name := t.name, statement := statement } :: out
  return out.reverse

/-- Local theorem-assumption statements carried by a kernel replay tree. -/
partial def kernelLFDerivationLocalAssumptionStatementMap
    (derivation : KernelLFDerivation) (acc : NameMap Judgment := {}) : NameMap Judgment :=
  match derivation with
  | .assumption name statement => acc.insert name.eraseMacroScopes statement
  | .theoremRef .. | .certificate .. => acc
  | .ruleApp _ _ _ premises _ =>
      premises.foldl (fun acc d =>
        kernelLFDerivationLocalAssumptionStatementMap d acc) acc

/-- Extract local theorem assumptions, preferring the normalized statements in a replay tree. -/
def kernelLFLocalAssumptionEntriesForReplay (t : CheckedLFJudgmentTheorem)
    (derivation : KernelLFDerivation) : List KernelLFTheoremEntry :=
  let replayStatements := kernelLFDerivationLocalAssumptionStatementMap derivation
  t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          let statement :=
            match replayStatements.find? b.name.eraseMacroScopes with
            | some statement => statement
            | none => checkedLFJudgmentExprToKernel b.checkedTypeExpr head
          some { name := b.name, statement := statement }
        else
          none
    | none => none

/-- Build the compact replay context needed for one checked LF theorem. -/
def kernelLFReplayCertificateContextForTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) (derivation? : Option KernelLFDerivation := none) :
    KernelLFCheckContext :=
  { localParameters := t.binders.toList.map (fun b => b.name)
    assumptions :=
      match derivation? with
      | some derivation => kernelLFLocalAssumptionEntriesForReplay t derivation
      | none => kernelLFLocalAssumptionEntriesOfTheorem t
    theorems := precedingClosedLFTheoremEntries checked.lfJudgmentTheorems t.name
    certificates := kernelLFCertificateEntriesOfTheorems checked.lfJudgmentTheorems }

/-- Build a compact independently checkable replay certificate from a checked LF theorem. -/
def kernelLFReplayCertificateForCheckedTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : Except String KernelLFReplayCertificate := do
  let some (statement, derivation) := kernelLFReplayPayloadOfTheorem? t
    | throw s!"checked LF judgment theorem '{t.name}' has no kernel-facing replay derivation"
  pure { signature := kernelLFReplayCertificateSignature checked derivation
         context := kernelLFReplayCertificateContextForTheorem checked t (some derivation)
         statement := statement
         derivation := derivation }

/-- Build a checked replay wrapper for the kernel-facing artifact of a checked LF theorem. -/
def checkedKernelLFReplayForTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : Except String CheckedKernelLFDerivation :=
  match t.checkedKernelDerivation? with
  | some checkedReplay => .ok checkedReplay
  | none => do
      let cert ← kernelLFReplayCertificateForCheckedTheorem checked t
      cert.toChecked

/-- Build a compact independently checkable replay certificate for a named checked LF theorem. -/
def kernelLFReplayCertificateForTheorem (checked : CheckedSignature) (theoremName : Name) :
    CommandElabM KernelLFReplayCertificate := do
  let some t := checked.lfJudgmentTheorems.find? (fun t =>
      t.name.eraseMacroScopes == theoremName.eraseMacroScopes)
    | throwError "unknown checked LF judgment theorem '{theoremName}' in type theory \
        '{checked.name}'"
  match kernelLFReplayCertificateForCheckedTheorem checked t with
  | .ok cert => pure cert
  | .error err => throwError err

/-- Human-readable audit summary for a compact replay certificate. -/
def kernelLFReplayCertificateAuditString (theoryName theoremName : Name)
    (cert : KernelLFReplayCertificate) (checked? : Option CheckedSignature := none) : String :=
  let status := match cert.toChecked with | .ok _ => "ok" | .error err => s!"failed: {err}"
  let contextCount := cert.context.assumptions.length + cert.context.theorems.length +
    cert.context.certificates.length
  let ruleNames :=
    if cert.ruleNames.isEmpty then "none" else String.intercalate ", " (cert.ruleNames.map toString)
  let contextNames :=
    if cert.contextNames.isEmpty then "none" else
      String.intercalate ", " (cert.contextNames.map toString)
  let deps := kernelLFReplayDependencySummary cert.derivation
  let opaqueLine := checked?.map fun checked =>
    s!"opaque LF heads used: {nameSetSummary (replayOpaqueHeadNames checked deps)}"
  let lines := [
    s!"compact LF replay certificate for {theoryName.eraseMacroScopes}.\
      {theoremName.eraseMacroScopes}",
    s!"check: {status}",
    s!"signature fragment: {cert.signature.constants.length} constant(s), " ++
      s!"{cert.signature.contextZones.length} context zone(s), " ++
      s!"{cert.signature.binderClasses.length} binder class(es), " ++
      s!"{cert.signature.conversionPlugins.length} conversion plugin(s), " ++
      s!"{cert.signature.rules.length} rule(s)",
    s!"rule names: {ruleNames}",
    s!"context: {cert.context.localParameters.length} local parameter(s), " ++
      s!"{contextCount} theorem/certificate entry(ies)",
    s!"context names: {contextNames}",
    s!"local assumptions used: {nameSetSummary deps.localAssumptions}",
    s!"theorem references used: {nameSetSummary deps.theoremReferences}",
    s!"certificate obligations used: {nameSetSummary deps.certificateObligations}",
    s!"external certificates used: {nameSetSummary deps.externalCertificates}",
    s!"global LF heads used: {nameSetSummary deps.globalHeads}",
    s!"target: {replayAuditTargetString cert.statement}",
    s!"derivation: {replayAuditDerivationString cert.derivation}",
    "raw repr payload omitted; use #print_lf_replay_certificate_raw for debug output" ]
  String.intercalate "\n" <| match opaqueLine with
    | some line => lines.take 11 ++ [line] ++ lines.drop 11
    | none => lines


end InternalLean
