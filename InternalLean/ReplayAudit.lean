/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab

/-!
# LF replay audit and certificate helpers

This module contains checked structural replay-wrapper, certificate, and trust-dependency helpers.
Diagnostics and model rendering should use these APIs instead of rebuilding replay contexts ad hoc.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Insert all names from `extra` into `names`, erasing macro scopes first. -/
def insertNameSet (names extra : NameSet) : NameSet :=
  extra.toList.foldl (fun acc n => acc.insert n.eraseMacroScopes) names

/-- Global LF names mentioned by a structural kernel term. -/
partial def structuralKTermGlobalHeadNames : Kernel.KTerm → NameSet
  | .ident h => {h.name.raw.eraseMacroScopes}
  | .fvar _ | .bvar _ | .mvar _ _ | .univ _ => {}
  | .app f a | .arrow f a | .sigma f a | .pair f a | .jeq f a =>
      insertNameSet (structuralKTermGlobalHeadNames f) (structuralKTermGlobalHeadNames a)
  | .lam body | .fst body | .snd body => structuralKTermGlobalHeadNames body

/-- Global LF names mentioned by a structural kernel judgment. -/
def structuralJudgmentGlobalHeadNames (j : Kernel.Judgment) : NameSet :=
  j.args.foldl (fun names arg => insertNameSet names (structuralKTermGlobalHeadNames arg))
    {j.head.raw.eraseMacroScopes}

/-- Global LF names mentioned in a structural scoped rule instantiation. -/
def structuralScopedInstantiationGlobalHeadNames (inst : Kernel.ScopedInstantiation) :
    NameSet := Id.run do
  let mut names : NameSet := {}
  for e in inst.entries do
    if let some ty := e.type? then
      names := insertNameSet names (structuralKTermGlobalHeadNames ty)
    if let some ev := e.evidence? then
      names := insertNameSet names (structuralJudgmentGlobalHeadNames ev)
    names := insertNameSet names (structuralKTermGlobalHeadNames e.value)
  return names

/-- Global LF names mentioned in one structural kernel rule schema. -/
def structuralRuleSchemaGlobalHeadNames (r : Kernel.RuleSchema) : NameSet := Id.run do
  let mut names : NameSet := {}
  for v in r.metavariables do
    if let some ty := v.type? then
      names := insertNameSet names (structuralKTermGlobalHeadNames ty)
    if let some ev := v.evidence? then
      names := insertNameSet names (structuralJudgmentGlobalHeadNames ev)
  for p in r.premises do
    names := insertNameSet names (structuralJudgmentGlobalHeadNames p)
  for sc in r.sideConditions do
    for arg in sc.args do
      names := insertNameSet names (structuralKTermGlobalHeadNames arg)
  for slot in r.sideConditionCertificates do
    for arg in slot.condition.args do
      names := insertNameSet names (structuralKTermGlobalHeadNames arg)
  for cert in r.checkedSideConditionCertificates do
    for arg in cert.condition.args do
      names := insertNameSet names (structuralKTermGlobalHeadNames arg)
  names := insertNameSet names (structuralJudgmentGlobalHeadNames r.conclusionStmt)
  return names

/-- Rule names actually used by a structural kernel replay tree. -/
partial def structuralKernelLFDerivationRuleAppNames : Kernel.KernelLFDerivation → NameSet
  | .assumption .. | .theoremRef .. | .certificate .. => {}
  | .ruleApp ruleName _ _ premises _ =>
      premises.foldl
        (fun names prem => insertNameSet names (structuralKernelLFDerivationRuleAppNames prem))
        ({ruleName.raw.eraseMacroScopes} : NameSet)

/-- Global LF names mentioned by a structural kernel replay tree. -/
partial def structuralKernelLFDerivationGlobalHeadNames : Kernel.KernelLFDerivation → NameSet
  | .assumption _ stmt | .theoremRef _ stmt | .certificate _ stmt _ =>
      structuralJudgmentGlobalHeadNames stmt
  | .ruleApp _ concl inst premises _ =>
      let names := insertNameSet (structuralJudgmentGlobalHeadNames concl)
        (structuralScopedInstantiationGlobalHeadNames inst)
      premises.foldl (fun names prem => insertNameSet names
        (structuralKernelLFDerivationGlobalHeadNames prem)) names

/-- Exact replay-leaf dependencies used by a structural kernel replay artifact. -/
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
  /-- Global LF heads mentioned in statements and instantiations. -/
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

/-- Exact replay-leaf dependencies for a structural kernel replay tree. -/
partial def kernelLFReplayDependencySummary :
    Kernel.KernelLFDerivation → KernelLFReplayDependencySummary
  | .assumption name stmt =>
      { localAssumptions := {name.raw.eraseMacroScopes}
        globalHeads := structuralJudgmentGlobalHeadNames stmt }
  | .theoremRef name stmt =>
      { theoremReferences := {name.raw.eraseMacroScopes}
        globalHeads := structuralJudgmentGlobalHeadNames stmt }
  | .certificate name stmt certificateName =>
      { certificateObligations := {name.raw.eraseMacroScopes}
        externalCertificates := {certificateName.raw.eraseMacroScopes}
        globalHeads := structuralJudgmentGlobalHeadNames stmt }
  | .ruleApp ruleName concl inst premises certificateNames =>
      let own : KernelLFReplayDependencySummary :=
        { externalCertificates := certificateNames.foldl
            (fun s n => s.insert n.raw.eraseMacroScopes) {}
          ruleApplications := {ruleName.raw.eraseMacroScopes}
          globalHeads := insertNameSet (structuralJudgmentGlobalHeadNames concl)
            (structuralScopedInstantiationGlobalHeadNames inst) }
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

/-- Source-ish rendering for structural kernel terms. -/
partial def structuralKTermSourceStringWithDepth : Nat → Kernel.KTerm → String
  | 0, _ => "..."
  | _ + 1, .ident h => lfReplayNameString h.name.raw
  | _ + 1, .fvar name => lfReplayNameString name.raw
  | _ + 1, .bvar idx => s!"#{idx}"
  | _ + 1, .mvar name _ => s!"?{lfReplayNameString name.raw}"
  | depth + 1, .app f a =>
      s!"({structuralKTermSourceStringWithDepth depth f} " ++
        s!"{structuralKTermSourceStringWithDepth depth a})"
  | depth + 1, .lam body => s!"(fun => {structuralKTermSourceStringWithDepth depth body})"
  | depth + 1, .arrow A B =>
      s!"({structuralKTermSourceStringWithDepth depth A} ⇒ " ++
        s!"{structuralKTermSourceStringWithDepth depth B})"
  | depth + 1, .sigma A B =>
      s!"(Σ _ : {structuralKTermSourceStringWithDepth depth A}, " ++
        s!"{structuralKTermSourceStringWithDepth depth B})"
  | depth + 1, .pair a b =>
      s!"⟨{structuralKTermSourceStringWithDepth depth a}, " ++
        s!"{structuralKTermSourceStringWithDepth depth b}⟩"
  | depth + 1, .fst e => s!"(fst {structuralKTermSourceStringWithDepth depth e})"
  | depth + 1, .snd e => s!"(snd {structuralKTermSourceStringWithDepth depth e})"
  | _ + 1, .univ u => s!"Type {u}"
  | depth + 1, .jeq lhs rhs =>
      s!"({structuralKTermSourceStringWithDepth depth lhs} ≡ " ++
        s!"{structuralKTermSourceStringWithDepth depth rhs})"

/-- Source-ish rendering for structural kernel judgments. -/
def structuralJudgmentSourceStringWithDepth (depth : Nat) (j : Kernel.Judgment) : String :=
  let head := lfReplayNameString j.head.raw
  match j.args with
  | [] => head
  | args => s!"({String.intercalate " " (head :: args.map
      (structuralKTermSourceStringWithDepth depth))})"

/-- Compact source-ish structural replay-tree rendering with a depth and size budget. -/
partial def structuralKernelLFDerivationSourceStringWithDepth : Nat →
    Kernel.KernelLFDerivation → String
  | 0, _ => "..."
  | depth + 1, .assumption name stmt =>
      s!"assumption {lfReplayNameString name.raw} : " ++
        s!"{structuralJudgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .theoremRef name stmt =>
      s!"theorem {lfReplayNameString name.raw} : " ++
        s!"{structuralJudgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .certificate name stmt cert =>
      s!"certificate {lfReplayNameString name.raw} via {lfReplayNameString cert.raw} : " ++
        s!"{structuralJudgmentSourceStringWithDepth depth stmt}"
  | depth + 1, .ruleApp ruleName concl inst premises certs =>
      let entryNames := inst.entries.map (fun e => lfReplayNameString e.name.raw)
      let premiseText := premises.take 3 |>.map
        (structuralKernelLFDerivationSourceStringWithDepth depth)
      let morePremises := if premises.length > 3 then [s!"... +{premises.length - 3} more"] else []
      let certText := certs.map (fun c => lfReplayNameString c.raw)
      s!"rule {lfReplayNameString ruleName.raw} : " ++
        s!"{structuralJudgmentSourceStringWithDepth depth concl}; " ++
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
  | depth + 1, .sigma none A B =>
      s!"({checkedLFExprSourceStringWithDepth depth A} × " ++
        s!"{checkedLFExprSourceStringWithDepth depth B})"
  | depth + 1, .sigma (some x) A B =>
      s!"(Σ {lfReplayNameString x} : {checkedLFExprSourceStringWithDepth depth A}, " ++
        s!"{checkedLFExprSourceStringWithDepth depth B})"
  | depth + 1, .pair a b =>
      s!"⟨{checkedLFExprSourceStringWithDepth depth a}, " ++
        s!"{checkedLFExprSourceStringWithDepth depth b}⟩"
  | depth + 1, .fst e => s!"(fst {checkedLFExprSourceStringWithDepth depth e})"
  | depth + 1, .snd e => s!"(snd {checkedLFExprSourceStringWithDepth depth e})"
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

/-- Default source-ish checked LF expression rendering for diagnostics. -/
def replayAuditCheckedLFExprString (expr : CheckedLFExpr) : String :=
  truncateDiagnosticString 600 (checkedLFExprSourceStringWithDepth 6 expr)

/-- Default source-ish shallow derivation rendering for diagnostics. -/
def replayAuditCheckedLFDerivationString (derivation : CheckedLFDerivation) : String :=
  truncateDiagnosticString 1200 (checkedLFDerivationSourceStringWithDepth 5 derivation)

/-- Default source-ish structural target rendering for replay-audit summaries. -/
def replayAuditStructuralTargetString (stmt : Kernel.Judgment) : String :=
  truncateDiagnosticString 600 (structuralJudgmentSourceStringWithDepth 6 stmt)

/-- Default source-ish structural derivation rendering for replay-audit summaries. -/
def replayAuditStructuralDerivationString (derivation : Kernel.KernelLFDerivation) : String :=
  truncateDiagnosticString 1200 (structuralKernelLFDerivationSourceStringWithDepth 5 derivation)

/-- Structural replay statement for a theorem, preferring checked cached replay wrappers. -/
def structuralKernelLFReplayStatementOfTheorem? (t : CheckedLFJudgmentTheorem) :
    Option Kernel.Judgment :=
  match t.checkedStructuralKernelDerivation? with
  | some checkedReplay => some checkedReplay.statement
  | none => checkedLFJudgmentTheoremStatementToK t |>.toOption

/-- Structural replay payload for a theorem, preferring checked cached replay wrappers. -/
def structuralKernelLFReplayPayloadOfTheorem? (t : CheckedLFJudgmentTheorem) :
    Option (Kernel.Judgment × Kernel.KernelLFDerivation) :=
  match t.checkedStructuralKernelDerivation? with
  | some checkedReplay => some (checkedReplay.statement, checkedReplay.derivation)
  | none =>
      match t.structuralKernelDerivation? with
      | some derivation => some (Kernel.KernelLFDerivation.statement derivation, derivation)
      | none => none

/-- Previously checked closed LF theorems that precede a theorem in source order. -/
def precedingClosedLFTheoremEntriesToK (theorems : Array CheckedLFJudgmentTheorem)
    (theoremName : Name) : Except String (List Kernel.KernelLFTheoremEntry) := do
  let mut out : List Kernel.KernelLFTheoremEntry := []
  for t in theorems do
    if t.name.eraseMacroScopes == theoremName.eraseMacroScopes then
      return out.reverse
    if t.binders.isEmpty then
      let some statement := structuralKernelLFReplayStatementOfTheorem? t
        | throw s!"checked LF judgment theorem '{t.name}' has no structural replay statement"
      out := { name := Kernel.KName.ofName t.name, statement := statement } :: out
  return out.reverse

/-- Build the structural replay context needed for one checked LF theorem. -/
def kernelLFReplayCertificateContextForTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : Except String Kernel.KernelLFCheckContext := do
  let checkedLFDefValues := checkedLFDefinitionValues checked.lfSyntaxDefs checked.lfObjectDefs
  let assumptions ← kernelLFLocalAssumptionEntriesOfTheoremToK false checkedLFDefValues t
  let theorems ← precedingClosedLFTheoremEntriesToK checked.lfJudgmentTheorems t.name
  pure {
    localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
    assumptions := assumptions
    theorems := theorems
    certificates := kernelLFCertificateEntriesOfTheoremsToK checked.lfJudgmentTheorems }

/-- Build a structural independently checkable replay certificate from a checked LF theorem. -/
def kernelLFReplayCertificateForCheckedTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : Except String Kernel.KernelLFReplayCertificate := do
  let some (statement, derivation) := structuralKernelLFReplayPayloadOfTheorem? t
    | throw s!"checked LF judgment theorem '{t.name}' has no structural replay derivation"
  let signature ← checkedSignatureToKSignature checked.name checked.lfSyntaxDefs
    checked.lfOpaqueConsts checked.lfContextZones checked.lfBinderClasses
    checked.lfConversionPlugins checked.lfRuleSchemas checked.lfObjectDefs
    checked.lfJudgmentTheorems
  let usedRules := structuralKernelLFDerivationRuleAppNames derivation
  let rules := signature.rules.filter (fun r => usedRules.contains r.name.raw.eraseMacroScopes)
  let usedGlobals := rules.foldl
    (fun names r => insertNameSet names (structuralRuleSchemaGlobalHeadNames r))
    (structuralKernelLFDerivationGlobalHeadNames derivation)
  let constants := signature.constants.filter (fun c =>
    usedGlobals.contains c.name.raw.eraseMacroScopes)
  let signature := { signature with constants := constants, rules := rules }
  let context ← kernelLFReplayCertificateContextForTheorem checked t
  pure {
    signature := signature
    context := context
    statement := statement
    derivation := derivation }

/-- Build a checked replay wrapper for the structural artifact of a checked LF theorem. -/
def checkedKernelLFReplayForTheorem (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : Except String Kernel.CheckedKernelLFDerivation :=
  match t.checkedStructuralKernelDerivation? with
  | some checkedReplay => .ok checkedReplay
  | none => do
      let cert ← kernelLFReplayCertificateForCheckedTheorem checked t
      cert.toChecked

/-- Build a structural independently checkable replay certificate for a named checked LF theorem. -/
def kernelLFReplayCertificateForTheorem (checked : CheckedSignature) (theoremName : Name) :
    CommandElabM Kernel.KernelLFReplayCertificate := do
  let some t := checked.lfJudgmentTheorems.find? (fun t =>
      t.name.eraseMacroScopes == theoremName.eraseMacroScopes)
    | throwError "unknown checked LF judgment theorem '{theoremName}' in type theory \
        '{checked.name}'"
  match kernelLFReplayCertificateForCheckedTheorem checked t with
  | .ok cert => pure cert
  | .error err => throwError err

/-- Rule names used by a structural replay certificate. -/
def structuralReplayCertificateRuleNames (cert : Kernel.KernelLFReplayCertificate) : List Name :=
  structuralKernelLFDerivationRuleAppNames cert.derivation |>.toList

/-- Context names available to a structural replay certificate. -/
def structuralReplayCertificateContextNames (cert : Kernel.KernelLFReplayCertificate) : List Name :=
  cert.context.assumptions.map (fun e => e.name.raw) ++
    cert.context.theorems.map (fun e => e.name.raw) ++
      cert.context.certificates.map (fun e => e.name.raw)

/-- Human-readable audit summary for a structural replay certificate. -/
def kernelLFReplayCertificateAuditString (theoryName theoremName : Name)
    (cert : Kernel.KernelLFReplayCertificate) (checked? : Option CheckedSignature := none) :
    String :=
  let status := match cert.toChecked with | .ok _ => "ok" | .error err => s!"failed: {err}"
  let contextCount := cert.context.assumptions.length + cert.context.theorems.length +
    cert.context.certificates.length
  let certRuleNames := structuralReplayCertificateRuleNames cert
  let certContextNames := structuralReplayCertificateContextNames cert
  let ruleNames :=
    if certRuleNames.isEmpty then "none" else String.intercalate ", "
      (certRuleNames.map toString)
  let contextNames :=
    if certContextNames.isEmpty then "none" else String.intercalate ", "
      (certContextNames.map toString)
  let deps := kernelLFReplayDependencySummary cert.derivation
  let opaqueLine := checked?.map fun checked =>
    s!"opaque LF heads used: {nameSetSummary (replayOpaqueHeadNames checked deps)}"
  let lines := [
    s!"structural LF replay certificate for {theoryName.eraseMacroScopes}.\
      {theoremName.eraseMacroScopes}",
    s!"check: {status}",
    s!"signature: {cert.signature.constants.length} constant(s), " ++
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
    s!"target: {replayAuditStructuralTargetString cert.statement}",
    s!"derivation: {replayAuditStructuralDerivationString cert.derivation}" ]
  String.intercalate "\n" <| match opaqueLine with
    | some line => lines.take 11 ++ [line] ++ lines.drop 11
    | none => lines

end InternalLean
