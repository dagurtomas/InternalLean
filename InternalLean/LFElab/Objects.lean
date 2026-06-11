/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab.Check

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Check staged sorted LF/object definitions and custom-judgment theorems.

This is a shallow internal-language milestone: it validates known names, recursively resolves
all expressions, requires `judgment_theorem` statements to be headed by declared custom
judgments, and can replay a small rule-application proof shape. It does not yet construct
certified derivation trees. -/
def checkLFObjectArtifactsInSignature (sig : HLSignature) (rules : Array CheckedLFRule) :
    CoreM (Array CheckedLFObjectDef × Array CheckedLFJudgmentTheorem) := do
  let lfGlobals := lfKnownGlobalNames sig
  let opaqueArities := lfOpaqueArities sig
  let globalHeads := lfGlobalHeadInfo sig
  let lookup := mkLFCheckLookupContext sig
  let judgmentArities : NameMap Nat := sig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let syntaxSortArities : NameMap Nat := lfSyntaxFamilyArities sig
  let mut checkedDefs := #[]
  let mut knownLFDefTypes : LFLocalTypes := {}
  let mut knownLFDefValues : LFDefinitionValueMap := {}
  for d in sig.lfObjectDefs do
    let typeHead? ←
      checkLFObjectDefTypeAndResultHeadWithLookup? lookup sig globalHeads knownLFDefTypes d
    checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "value" d.value
    checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "value" d.value
    checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "value"
      (locals := {}) d.value
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "lf_def" d.name
      (lfCheckWhere "value") knownLFDefTypes d.value
    checkLFExprHasTypeWithLookup lookup sig "lf_def" d.name (lfCheckWhere "value")
      knownLFDefTypes d.value d.typeExpr
    let checkedType ← resolveLFExpr sig globalHeads {} "lf_def" d.name "type" d.typeExpr
    let checkedValue ← resolveLFExpr sig globalHeads {} "lf_def" d.name "value" d.value
    let valueHead? := checkedLFHead? globalHeads {} d.value
    if let some valueHead := valueHead? then
      if valueHead.kind == .lfDefinition then
        let valueName := valueHead.name.eraseMacroScopes
        unless knownLFDefTypes.contains valueName do
          throwError "lf_def '{d.name}' in type theory '{sig.name}' references LF definition \
            '{valueName}' before it is available"
        if let some actualType :=
            inferKnownLFExprTypeWithLookup? lookup knownLFDefTypes d.value then
          let expectedType := eraseObjExprScopes d.typeExpr
          let (normalizedActualType, normalizedExpectedType) :=
            normalizeLFTypeComparisonPairInLookup lookup actualType expectedType
          if !lfExprAlphaEq normalizedActualType normalizedExpectedType then
            throwError "lf_def '{d.name}' in type theory '{sig.name}' has value LF definition \
              '{valueName}' with type '{diagnosticObjExprString normalizedActualType}', expected \
              '{diagnosticObjExprString normalizedExpectedType}'"
    checkedDefs := checkedDefs.push {
      name := d.name.eraseMacroScopes
      typeExpr := d.typeExpr
      checkedTypeExpr := checkedType
      typeHead? := typeHead?
      value := d.value
      checkedValue := checkedValue
      valueHead? := valueHead? }
    knownLFDefTypes :=
      knownLFDefTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
    knownLFDefValues := knownLFDefValues.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)
  let mut checkedTheorems := #[]
  let mut availableLFTheoremStatements : NameMap ObjExpr := {}
  let mut availableLFTheoremNames : NameSet := {}
  for t in sig.lfJudgmentTheorems do
    checkNoDuplicateMetadataBinders sig "judgment_theorem" t.name t.binders
    let _ ←
      checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "judgment_theorem" t.name
        t.binders
    checkSyntaxSortApplicationsInBindings sig syntaxSortArities "judgment_theorem" t.name t.binders
    let (checkedBinders, theoremLocals) ←
      checkedLFBindings sig globalHeads "judgment_theorem" t.name t.binders
    let mut theoremKnownTypes := knownLFDefTypes
    let mut availableLocalStatements : NameMap ObjExpr := {}
    let mut priorTheoremLocals : NameSet := {}
    for b in t.binders do
      let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
      checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name where_ b.typeExpr
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
        (lfCheckWhere where_) theoremKnownTypes b.typeExpr
      checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
        (lfCheckWhere where_) theoremKnownTypes b.typeExpr
      checkLFEvidenceTypeWithLookup lookup sig globalHeads "judgment_theorem" t.name where_
        theoremKnownTypes priorTheoremLocals b.typeExpr
      let typeHead? := checkedLFHead? globalHeads priorTheoremLocals b.typeExpr
      if let some head := typeHead? then
        if head.kind == .judgment then
          availableLocalStatements :=
            availableLocalStatements.insert b.name.eraseMacroScopes (eraseObjExprScopes
              b.typeExpr)
      theoremKnownTypes :=
        theoremKnownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
      priorTheoremLocals := priorTheoremLocals.insert b.name.eraseMacroScopes
    checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
      "statement" t.judgmentExpr
    checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere "statement")
      theoremKnownTypes t.judgmentExpr
    checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere "statement") theoremKnownTypes t.judgmentExpr
    checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
      "proof" t.proof
    checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "proof" t.proof
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere "proof")
      theoremKnownTypes t.proof
    checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere "proof")
      theoremKnownTypes t.proof
    let judgmentHead ← checkRuleJudgmentHead sig judgmentArities t.name "statement" t.judgmentExpr
    let (_, judgmentArgs) := splitObjApp t.judgmentExpr
    checkLFJudgmentArgumentsWithKnownTypesAndLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere "statement") theoremKnownTypes judgmentHead.name judgmentArgs
    let checkedJudgment ←
      resolveLFExpr sig globalHeads theoremLocals "judgment_theorem" t.name "statement"
        t.judgmentExpr
    let checkedProof ←
      resolveLFExpr sig globalHeads theoremLocals "judgment_theorem" t.name "proof" t.proof
    let proofHead? := checkedLFHead? globalHeads theoremLocals t.proof
    let derivation? ←
      checkLFJudgmentDerivation sig rules globalHeads theoremKnownTypes knownLFDefValues
        theoremLocals availableLocalStatements availableLFTheoremStatements availableLFTheoremNames
        t.name t.judgmentExpr t.proof
    let some derivation := derivation?
      | throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has unchecked proof \
        '{diagnosticObjExprString t.proof}'; expected a local theorem assumption, checked \
          judgment theorem, or LF rule application"
    let kernelDerivation? ←
      tryLowerLFDerivationToKernel? sig rules globalHeads theoremKnownTypes knownLFDefValues
        theoremLocals t.name derivation
    let ruleSummary := summarizeLFRuleApplication? derivation
    checkedTheorems := checkedTheorems.push {
      name := t.name.eraseMacroScopes
      binders := checkedBinders
      judgmentExpr := t.judgmentExpr
      checkedJudgmentExpr := checkedJudgment
      judgmentHead := judgmentHead
      proof := t.proof
      checkedProof := checkedProof
      proofHead? := proofHead?
      proofRule? := ruleSummary.proofRule?
      proofRuleArgs := ruleSummary.proofRuleArgs
      premiseTheorems := ruleSummary.premiseTheorems
      sideConditionCertificateNames := ruleSummary.sideConditionCertificateNames
      derivation? := some derivation
      kernelDerivation? := kernelDerivation? }
    let stmt := match derivation with
      | .localAssumption _ stmt => stmt
      | .theoremRef _ stmt _ _ => stmt
      | .ruleApp _ stmt _ _ _ => stmt
    if t.binders.isEmpty then
      availableLFTheoremStatements :=
        availableLFTheoremStatements.insert t.name.eraseMacroScopes stmt
    availableLFTheoremNames := availableLFTheoremNames.insert t.name.eraseMacroScopes
  pure (checkedDefs, checkedTheorems)

/-- Previously checked LF definition and syntax-definition result types. -/
def checkedLFDefinitionTypeMapFromDefs (syntaxDefs : Array CheckedLFSyntaxDef)
    (defs : Array CheckedLFObjectDef) : LFLocalTypes := Id.run do
  let mut out : LFLocalTypes := {}
  for d in syntaxDefs do
    let params := d.params.map fun b =>
      ({ name := b.name, typeExpr := b.typeExpr, visibility := b.visibility } : HLBinding)
    out := out.insert d.name.eraseMacroScopes
      (eraseObjExprScopes (mkInternalDefFunctionType params (objExprTypeOfLevel d.resultLevel)))
  for d in defs do
    out := out.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  return out

/-- Declared LF definition result types from a source block. -/
def lfDefinitionTypeMapFromDecls (defs : Array LFObjectDefDecl) : LFLocalTypes :=
  defs.foldl (init := {}) fun m d =>
    m.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)

/-- Merge LF definition type maps, preferring entries from `extra`. -/
def mergeLFLocalTypes (base extra : LFLocalTypes) : LFLocalTypes := Id.run do
  let mut out := base
  for (n, e) in extra.toList do
    out := out.insert n e
  return out

/-- Previously checked syntax-definition values. -/
def lfSyntaxDefinitionValueMapFromCheckedDefs (syntaxDefs : Array CheckedLFSyntaxDef) :
    LFDefinitionValueMap := Id.run do
  let mut out : LFDefinitionValueMap := {}
  for d in syntaxDefs do
    if let some value := d.value? then
      let params := d.params.map fun b =>
        ({ name := b.name, typeExpr := b.typeExpr, visibility := b.visibility } : HLBinding)
      out := out.insert d.name.eraseMacroScopes
        (eraseObjExprScopes (mkInternalDefLambda params value))
  return out

/-- Previously checked LF object-definition values. -/
def lfObjectDefinitionValueMapFromCheckedDefs (defs : Array CheckedLFObjectDef) :
    LFDefinitionValueMap :=
  defs.foldl (init := {}) fun out d =>
    out.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)

/-- Previously checked LF definition values. -/
def lfDefinitionValueMapFromCheckedDefs (syntaxDefs : Array CheckedLFSyntaxDef)
    (defs : Array CheckedLFObjectDef) : LFDefinitionValueMap := Id.run do
  let mut out := lfSyntaxDefinitionValueMapFromCheckedDefs syntaxDefs
  for (n, value) in (lfObjectDefinitionValueMapFromCheckedDefs defs).toList do
    out := out.insert n value
  return out

/-- Statements available for binder-free checked LF theorem references. -/
def availableLFTheoremStatementsFromChecked (theorems : Array CheckedLFJudgmentTheorem) :
    NameMap ObjExpr := Id.run do
  let mut out : NameMap ObjExpr := {}
  for t in theorems do
    if t.binders.isEmpty then
      let stmt := match t.derivation? with
        | some (.localAssumption _ stmt) => stmt
        | some (.theoremRef _ stmt _ _) => stmt
        | some (.ruleApp _ stmt _ _ _) => stmt
        | none => t.judgmentExpr
      out := out.insert t.name.eraseMacroScopes (eraseObjExprScopes stmt)
  return out

/-- Names of checked LF theorems available for later theorem references. -/
def availableLFTheoremNamesFromChecked (theorems : Array CheckedLFJudgmentTheorem) : NameSet :=
  theorems.foldl (init := {}) fun names t => names.insert t.name.eraseMacroScopes

/-- Statement carried by a shallow checked LF derivation. -/
def checkedLFDerivationStatement : CheckedLFDerivation → ObjExpr
  | .localAssumption _ stmt => stmt
  | .theoremRef _ stmt _ _ => stmt
  | .ruleApp _ stmt _ _ _ => stmt

/-- Shared context for streaming LF object-definition and theorem checks inside one block. -/
structure IntraBlockLFCheckContext where
  /-- Owning type-theory name. -/
  theoryName : Name
  /-- Flat source/checking signature including the whole candidate block. -/
  flatSig : HLSignature
  /-- Known LF global names in `flatSig`. -/
  lfGlobals : NameSet
  /-- Declared LF opaque arities in `flatSig`. -/
  opaqueArities : NameMap (Option Nat)
  /-- Resolved LF global-head table in `flatSig`. -/
  globalHeads : NameMap (CheckedLFHeadKind × Option Nat)
  /-- Syntax-sort arities in `flatSig`. -/
  syntaxSortArities : NameMap Nat
  /-- Judgment arities in `flatSig`. -/
  judgmentArities : NameMap Nat
  /-- Declared side-condition solvers in `flatSig`. -/
  solvers : NameSet
  /-- Map-based lookup data for repeated LF expression checks in `flatSig`. -/
  lookup : LFCheckLookupContext
  /-- Checked rules available to theorem checking. -/
  checkedRules : Array CheckedLFRule := #[]
  /-- Checked rule schemas available to cached replay construction. -/
  checkedRuleSchemas : Array CheckedLFRuleSchema := #[]
  /-- Checked side-condition certificates available to cached replay construction. -/
  checkedSideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  /-- Available LF definition result types, updated as new definitions are accepted. -/
  knownLFDefTypes : LFLocalTypes := {}
  /-- Available LF definition values, updated as new definitions are accepted. -/
  knownLFDefValues : LFDefinitionValueMap := {}
  /-- New LF object definitions checked in this block. -/
  newObjectDefs : Array CheckedLFObjectDef := #[]
  /-- Available binder-free LF theorem statements, updated as new theorems are accepted. -/
  availableLFTheoremStatements : NameMap ObjExpr := {}
  /-- Available LF theorem names, updated as new theorems are accepted. -/
  availableLFTheoremNames : NameSet := {}
  /-- New LF judgment theorems checked in this block, before cached kernel replay. -/
  newJudgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  deriving Inhabited

/-- Construct the shared LF checking context for one candidate block. -/
def mkIntraBlockLFCheckContext (flatSig : HLSignature) (checkedBase : CheckedSignature)
    (newRules : Array CheckedLFRule := #[])
    (newRuleSchemas : Array CheckedLFRuleSchema := #[])
    (newCertificates : Array CheckedLFSideConditionCertificate := #[]) :
    IntraBlockLFCheckContext :=
  let lfGlobals := lfKnownGlobalNames flatSig
  let opaqueArities := lfOpaqueArities flatSig
  let globalHeads := lfGlobalHeadInfo flatSig
  let syntaxSortArities : NameMap Nat := lfSyntaxFamilyArities flatSig
  let judgmentArities : NameMap Nat := flatSig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let solvers : NameSet := flatSig.sideConditionSolvers.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes
  { theoryName := flatSig.name.eraseMacroScopes
    flatSig := flatSig
    lfGlobals := lfGlobals
    opaqueArities := opaqueArities
    globalHeads := globalHeads
    syntaxSortArities := syntaxSortArities
    judgmentArities := judgmentArities
    solvers := solvers
    lookup := mkLFCheckLookupContext flatSig
    checkedRules := checkedBase.lfRules ++ newRules
    checkedRuleSchemas := checkedBase.lfRuleSchemas ++ newRuleSchemas
    checkedSideConditionCertificates :=
      checkedBase.lfSideConditionCertificates ++ newCertificates
    knownLFDefTypes :=
      checkedLFDefinitionTypeMapFromDefs checkedBase.lfSyntaxDefs checkedBase.lfObjectDefs
    knownLFDefValues :=
      lfDefinitionValueMapFromCheckedDefs checkedBase.lfSyntaxDefs checkedBase.lfObjectDefs
    availableLFTheoremStatements :=
      availableLFTheoremStatementsFromChecked checkedBase.lfJudgmentTheorems
    availableLFTheoremNames :=
      availableLFTheoremNamesFromChecked checkedBase.lfJudgmentTheorems }

/-- Add candidate declaration names to a cached LF global-name set. -/
def overlayLFKnownGlobalNames (known : NameSet) (block : HLTheoryBlock) : NameSet := Id.run do
  let mut known := known
  for s in block.syntaxSorts do known := known.insert s.name.eraseMacroScopes
  for a in block.syntaxAbbrevs do known := known.insert a.name.eraseMacroScopes
  for d in block.syntaxDefs do known := known.insert d.name.eraseMacroScopes
  for a in block.judgmentAbbrevs do known := known.insert a.name.eraseMacroScopes
  for j in block.judgments do known := known.insert j.name.eraseMacroScopes
  for o in block.lfOpaqueConsts do known := known.insert o.name.eraseMacroScopes
  for r in block.rules do known := known.insert r.name.eraseMacroScopes
  for d in block.lfObjectDefs do known := known.insert d.name.eraseMacroScopes
  for t in block.lfJudgmentTheorems do known := known.insert t.name.eraseMacroScopes
  return known

/-- Add candidate opaque arities to a cached arity map. -/
def overlayLFOpaqueArities (arities : NameMap (Option Nat))
    (block : HLTheoryBlock) : NameMap (Option Nat) := Id.run do
  let mut arities := arities
  for o in block.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
      | none => o.arity?
    arities := arities.insert o.name.eraseMacroScopes arity?
  return arities

/-- Add candidate LF global heads to a cached head table. -/
def overlayLFGlobalHeads (heads : NameMap (CheckedLFHeadKind × Option Nat))
    (block : HLTheoryBlock) : NameMap (CheckedLFHeadKind × Option Nat) := Id.run do
  let mut heads := heads
  for s in block.syntaxSorts do
    heads := heads.insert s.name.eraseMacroScopes (.syntaxSort, some s.params.size)
  for d in block.syntaxDefs do
    heads := heads.insert d.name.eraseMacroScopes (.syntaxDef, some d.params.size)
  for j in block.judgments do
    heads := heads.insert j.name.eraseMacroScopes (.judgment, some j.params.size)
  for o in block.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
      | none => o.arity?
    heads := heads.insert o.name.eraseMacroScopes (.opaque, arity?)
  for r in block.rules do
    heads := heads.insert r.name.eraseMacroScopes (.lfRule, none)
  for d in block.lfObjectDefs do
    heads := heads.insert d.name.eraseMacroScopes (.lfDefinition,
      some (lfFunctionTypeArity d.typeExpr))
  for t in block.lfJudgmentTheorems do
    heads := heads.insert t.name.eraseMacroScopes (.lfTheorem, some t.binders.size)
  return heads

/-- Add candidate syntax-family arities to a cached arity map. -/
def overlaySyntaxSortArities (arities : NameMap Nat) (block : HLTheoryBlock) : NameMap Nat :=
  let arities := block.syntaxSorts.foldl (init := arities) fun arities s =>
    arities.insert s.name.eraseMacroScopes s.params.size
  block.syntaxDefs.foldl (init := arities) fun arities d =>
    arities.insert d.name.eraseMacroScopes d.params.size

/-- Add candidate judgment arities to a cached arity map. -/
def overlayJudgmentArities (arities : NameMap Nat) (block : HLTheoryBlock) : NameMap Nat :=
  block.judgments.foldl (init := arities) fun arities j =>
    arities.insert j.name.eraseMacroScopes j.params.size

/-- Add candidate side-condition solvers to a cached solver set. -/
def overlaySideConditionSolvers (solvers : NameSet) (block : HLTheoryBlock) : NameSet :=
  block.sideConditionSolvers.foldl (init := solvers) fun solvers s =>
    solvers.insert s.name.eraseMacroScopes

/-- Construct map-based LF expression lookup data from a compiled cache plus a small candidate
block, without rescanning all previously checked LF object definitions. -/
def mkLFCheckLookupContextFromCache (cache : CompiledLFCheckCache)
    (candidate : HLTheoryBlock := {}) : LFCheckLookupContext := Id.run do
  let checkedHLWithoutObjectDefs := { cache.checkedHL with lfObjectDefs := #[] }
  let candidateWithoutObjectDefs := { candidate with lfObjectDefs := #[] }
  let baseLookup :=
    mkLFCheckLookupContext (checkedHLWithoutObjectDefs.appendBlock candidateWithoutObjectDefs)
  let mut lfObjectDefTypes := cache.knownLFDefTypes
  let mut lfDefinitionValues := cache.knownLFDefValues
  let mut lfSyntaxDefValues := cache.knownLFSyntaxDefValues
  for d in candidate.syntaxDefs do
    let name := d.name.eraseMacroScopes
    unless lfObjectDefTypes.contains name do
      lfObjectDefTypes := lfObjectDefTypes.insert name (eraseObjExprScopes (syntaxDefTypeExpr d))
      if let some value := syntaxDefValueExpr? d then
        lfSyntaxDefValues := lfSyntaxDefValues.insert name (eraseObjExprScopes value)
  for d in candidate.lfObjectDefs do
    let name := d.name.eraseMacroScopes
    unless lfObjectDefTypes.contains name do
      lfObjectDefTypes := lfObjectDefTypes.insert name (eraseObjExprScopes d.typeExpr)
      lfDefinitionValues := lfDefinitionValues.insert name (eraseObjExprScopes d.value)
  return { baseLookup with lfObjectDefTypes, lfDefinitionValues, lfSyntaxDefValues }

/-- Construct implicit-argument callable lookup data from a compiled cache plus a small candidate
block, without rescanning all previously checked LF object definitions. -/
def mkImplicitCallableLookupContextFromCache (cache : CompiledLFCheckCache)
    (candidate : HLTheoryBlock := {}) : ImplicitCallableLookupContext := Id.run do
  let checkedHLWithoutObjectDefs := { cache.checkedHL with lfObjectDefs := #[] }
  let candidateWithoutObjectDefs := { candidate with lfObjectDefs := #[] }
  let baseLookup :=
    mkImplicitCallableLookupContext
      (checkedHLWithoutObjectDefs.appendBlock candidateWithoutObjectDefs)
  let mut callableInfos := baseLookup.callableInfos
  for (name, typeExpr) in cache.knownLFDefTypes.toList do
    unless callableInfos.contains name do
      callableInfos := callableInfos.insert name { params := #[], result? := some typeExpr }
  for d in candidate.lfObjectDefs do
    callableInfos := callableInfos.insert d.name.eraseMacroScopes {
      params := #[], result? := some (eraseObjExprScopes d.typeExpr) }
  return { callableInfos }

/-- Construct an intra-block LF checking context from a compiled cache plus a small candidate
block, without recomputing full-theory maps. -/
def mkIntraBlockLFCheckContextFromCache (cache : CompiledLFCheckCache)
    (candidate : HLTheoryBlock := {}) (newRules : Array CheckedLFRule := #[])
    (newRuleSchemas : Array CheckedLFRuleSchema := #[])
    (newCertificates : Array CheckedLFSideConditionCertificate := #[]) :
    IntraBlockLFCheckContext :=
  let flatSig := cache.checkedHL.appendBlock candidate
  { theoryName := flatSig.name.eraseMacroScopes
    flatSig := flatSig
    lfGlobals := overlayLFKnownGlobalNames cache.lfGlobals candidate
    opaqueArities := overlayLFOpaqueArities cache.opaqueArities candidate
    globalHeads := overlayLFGlobalHeads cache.globalHeads candidate
    syntaxSortArities := overlaySyntaxSortArities cache.syntaxSortArities candidate
    judgmentArities := overlayJudgmentArities cache.judgmentArities candidate
    solvers := overlaySideConditionSolvers cache.solvers candidate
    lookup := mkLFCheckLookupContextFromCache cache candidate
    checkedRules := cache.checkedRules ++ newRules
    checkedRuleSchemas := cache.checkedRuleSchemas ++ newRuleSchemas
    checkedSideConditionCertificates := cache.checkedSideConditionCertificates ++ newCertificates
    knownLFDefTypes := cache.knownLFDefTypes
    knownLFDefValues := Id.run do
      let mut values := cache.knownLFDefValues
      for (n, value) in cache.knownLFSyntaxDefValues.toList do
        values := values.insert n value
      return values
    availableLFTheoremStatements := cache.availableLFTheoremStatements
    availableLFTheoremNames := cache.availableLFTheoremNames }

/-- Check one LF object definition, updating the intra-block availability context. -/
def checkLFObjectDefInContext (ctx : IntraBlockLFCheckContext) (d : LFObjectDefDecl) :
    CoreM (CheckedLFObjectDef × IntraBlockLFCheckContext) := do
  let sig := ctx.flatSig
  let lfGlobals := ctx.lfGlobals
  let opaqueArities := ctx.opaqueArities
  let globalHeads := ctx.globalHeads
  let lookup := ctx.lookup
  let knownLFDefTypes := ctx.knownLFDefTypes
  let typeHead? ← profileLFCheckPhase m!"{d.name}: metadata prechecks" do
    let typeHead? ←
      checkLFObjectDefTypeAndResultHeadWithLookup? lookup sig globalHeads knownLFDefTypes d
    checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "value" d.value
    checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "value" d.value
    checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "value"
      (locals := {}) d.value
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "lf_def" d.name
      (lfCheckWhere "value") knownLFDefTypes d.value
    pure typeHead?
  profileLFCheckPhase m!"{d.name}: value has expected type" do
    checkLFExprHasTypeWithLookup lookup sig "lf_def" d.name (lfCheckWhere "value")
      knownLFDefTypes d.value d.typeExpr
  let checkedType ← profileLFCheckPhase m!"{d.name}: resolve type" do
    resolveLFExpr sig globalHeads {} "lf_def" d.name "type" d.typeExpr
  let checkedValue ← profileLFCheckPhase m!"{d.name}: resolve value" do
    resolveLFExpr sig globalHeads {} "lf_def" d.name "value" d.value
  let valueHead? := checkedLFHead? globalHeads {} d.value
  if let some valueHead := valueHead? then
    if valueHead.kind == .lfDefinition then
      let valueName := valueHead.name.eraseMacroScopes
      unless knownLFDefTypes.contains valueName do
        throwError "lf_def '{d.name}' in type theory '{sig.name}' references LF definition \
          '{valueName}' before it is available"
      if let some actualType := inferKnownLFExprTypeWithLookup? lookup knownLFDefTypes d.value then
        let expectedType := eraseObjExprScopes d.typeExpr
        let (normalizedActualType, normalizedExpectedType) :=
          normalizeLFTypeComparisonPairInLookup lookup actualType expectedType
        if !lfExprAlphaEq normalizedActualType normalizedExpectedType then
          throwError "lf_def '{d.name}' in type theory '{sig.name}' has value LF definition \
            '{valueName}' with type '{diagnosticObjExprString normalizedActualType}', expected \
            '{diagnosticObjExprString normalizedExpectedType}'"
  let checkedDef : CheckedLFObjectDef := {
    name := d.name.eraseMacroScopes
    typeExpr := d.typeExpr
    checkedTypeExpr := checkedType
    typeHead? := typeHead?
    value := d.value
    checkedValue := checkedValue
    valueHead? := valueHead? }
  let ctx := { ctx with
    knownLFDefTypes :=
      ctx.knownLFDefTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
    knownLFDefValues :=
      ctx.knownLFDefValues.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)
    newObjectDefs := ctx.newObjectDefs.push checkedDef }
  pure (checkedDef, ctx)

/-- Build the checked artifact and updated context after an external checker accepts an LF object
body. -/
def checkedLFObjectDefAfterExternalBodyCheck (ctx : IntraBlockLFCheckContext)
    (d : LFObjectDefDecl) : CoreM (CheckedLFObjectDef × IntraBlockLFCheckContext) := do
  let sig := ctx.flatSig
  let globalHeads := ctx.globalHeads
  let resultTypeExpr := eraseObjExprScopes (lfFunctionTypeResult d.typeExpr)
  let typeHead? := checkedLFHead? globalHeads {} resultTypeExpr
  match typeHead? with
  | some typeHead =>
      if typeHead.kind != .syntaxSort && typeHead.kind != .syntaxDef then
        throwError "lf_def '{d.name}' in type theory '{sig.name}' has result type headed by \
          {typeHead.kind.label} '{typeHead.name}', expected a syntax-family-headed or structural \
            record/Sigma type"
  | none =>
      unless lfObjectDefResultIsStructuralRecord resultTypeExpr do
        throwError "lf_def '{d.name}' in type theory '{sig.name}' has type not ending in a known \
          LF identifier or structural record/Sigma type: {d.typeExpr}"
  let checkedType ← profileLFCheckPhase m!"{d.name}: resolve type" do
    resolveLFExpr sig globalHeads {} "lf_def" d.name "type" d.typeExpr
  let checkedValue ← profileLFCheckPhase m!"{d.name}: resolve value" do
    resolveLFExpr sig globalHeads {} "lf_def" d.name "value" d.value
  let valueHead? := checkedLFHead? globalHeads {} d.value
  if let some valueHead := valueHead? then
    if valueHead.kind == .lfDefinition then
      let valueName := valueHead.name.eraseMacroScopes
      unless ctx.knownLFDefTypes.contains valueName do
        throwError "lf_def '{d.name}' in type theory '{sig.name}' references LF definition \
          '{valueName}' before it is available"
  let checkedDef : CheckedLFObjectDef := {
    name := d.name.eraseMacroScopes
    typeExpr := d.typeExpr
    checkedTypeExpr := checkedType
    typeHead? := typeHead?
    value := d.value
    checkedValue := checkedValue
    valueHead? := valueHead? }
  let ctx := { ctx with
    knownLFDefTypes :=
      ctx.knownLFDefTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
    knownLFDefValues :=
      ctx.knownLFDefValues.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)
    newObjectDefs := ctx.newObjectDefs.push checkedDef }
  pure (checkedDef, ctx)

/-- Prefix of a streaming LF-object-definition block that should be visible to the mirror. -/
def lfMirrorSignatureForObjectDefPrefix (ctx : IntraBlockLFCheckContext)
    (d : LFObjectDefDecl) : HLSignature :=
  let current := d.name.eraseMacroScopes
  let objectDefs := ctx.flatSig.lfObjectDefs.filter fun prior =>
    let priorName := prior.name.eraseMacroScopes
    priorName == current || ctx.knownLFDefTypes.contains priorName
  { ctx.flatSig with lfObjectDefs := objectDefs, lfJudgmentTheorems := #[], rules := #[] }

/-- Check one LF object definition using the opt-in Lean mirror theory-body checker. -/
def checkLFObjectDefInContextWithMirror (ctx : IntraBlockLFCheckContext) (d : LFObjectDefDecl) :
    CoreM (CheckedLFObjectDef × IntraBlockLFCheckContext) := do
  let mirrorSig := lfMirrorSignatureForObjectDefPrefix ctx d
  let compareWithLF ← getBoolOption `internalLean.mirrorBackend.compareTheoryBodiesWithLF
  try
    withRestoredCoreStateOnError do
      profileLFCheckPhase m!"{d.name}: mirror body check" do
        withLFMirrorFastPathHeartbeats do
          ensureLFMirrorForSignatureBestEffort mirrorSig
          addLFMirrorPendingDecl mirrorSig.name (lfMirrorLevelParamNamesForSignature mirrorSig)
            (lfMirrorLevelArgsForSignature mirrorSig) (.lfObjectDef d)
    if compareWithLF then
      checkLFObjectDefInContext ctx d
    else
      checkedLFObjectDefAfterExternalBodyCheck ctx d
  catch _ =>
    checkLFObjectDefInContext ctx d

/-- Check one LF object definition with the selected theory-body backend. -/
def checkLFObjectDefInContextSelected (ctx : IntraBlockLFCheckContext) (d : LFObjectDefDecl) :
    CoreM (CheckedLFObjectDef × IntraBlockLFCheckContext) := do
  let useMirror :=
    (← getBoolOption `internalLean.mirrorBackend.checkTheoryBodies) &&
      lfMirrorObjExprNodeCountLE lfMirrorBestEffortObjectDefNodeLimit d.value
  if useMirror then
    checkLFObjectDefInContextWithMirror ctx d
  else
    checkLFObjectDefInContext ctx d

/-- Check one LF judgment theorem, updating the intra-block availability context. -/
def checkLFJudgmentTheoremInContext (ctx : IntraBlockLFCheckContext)
    (t : LFJudgmentTheoremDecl) :
    CoreM (CheckedLFJudgmentTheorem × IntraBlockLFCheckContext) := do
  let sig := ctx.flatSig
  let lfGlobals := ctx.lfGlobals
  let opaqueArities := ctx.opaqueArities
  let globalHeads := ctx.globalHeads
  let judgmentArities := ctx.judgmentArities
  let syntaxSortArities := ctx.syntaxSortArities
  let rules := ctx.checkedRules
  let lookup := ctx.lookup
  let knownLFDefTypes := ctx.knownLFDefTypes
  let knownLFDefValues := ctx.knownLFDefValues
  let availableTheoremStatements := ctx.availableLFTheoremStatements
  let availableTheoremNames := ctx.availableLFTheoremNames
  checkNoDuplicateMetadataBinders sig "judgment_theorem" t.name t.binders
  let _ ← checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "judgment_theorem" t.name
    t.binders
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "judgment_theorem" t.name t.binders
  let (checkedBinders, theoremLocals) ←
    checkedLFBindings sig globalHeads "judgment_theorem" t.name t.binders
  let mut theoremKnownTypes := knownLFDefTypes
  let mut availableLocalStatements : NameMap ObjExpr := {}
  let mut priorTheoremLocals : NameSet := {}
  for b in t.binders do
    let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
    checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name where_ b.typeExpr
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere where_) theoremKnownTypes b.typeExpr
    checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
      (lfCheckWhere where_) theoremKnownTypes b.typeExpr
    checkLFEvidenceTypeWithLookup lookup sig globalHeads "judgment_theorem" t.name where_
      theoremKnownTypes priorTheoremLocals b.typeExpr
    let typeHead? := checkedLFHead? globalHeads priorTheoremLocals b.typeExpr
    if let some head := typeHead? then
      if head.kind == .judgment then
        availableLocalStatements :=
          availableLocalStatements.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    theoremKnownTypes :=
      theoremKnownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    priorTheoremLocals := priorTheoremLocals.insert b.name.eraseMacroScopes
  checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
    "statement" t.judgmentExpr
  checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
  checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
    (lfCheckWhere "statement") theoremKnownTypes t.judgmentExpr
  checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
    (lfCheckWhere "statement")
    theoremKnownTypes t.judgmentExpr
  checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
    "proof" t.proof
  checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "proof" t.proof
  checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "judgment_theorem" t.name
    (lfCheckWhere "proof") theoremKnownTypes t.proof
  checkLFInferableApplicationArgumentsWithLookup lookup sig "judgment_theorem" t.name
    (lfCheckWhere "proof") theoremKnownTypes t.proof
  let judgmentHead ← checkRuleJudgmentHead sig judgmentArities t.name "statement" t.judgmentExpr
  let (_, judgmentArgs) := splitObjApp t.judgmentExpr
  checkLFJudgmentArgumentsWithKnownTypesAndLookup lookup sig "judgment_theorem" t.name
    (lfCheckWhere "statement") theoremKnownTypes judgmentHead.name judgmentArgs
  let checkedJudgment ←
    resolveLFExpr sig globalHeads theoremLocals "judgment_theorem" t.name "statement"
      t.judgmentExpr
  let checkedProof ←
    resolveLFExpr sig globalHeads theoremLocals "judgment_theorem" t.name "proof" t.proof
  let proofHead? := checkedLFHead? globalHeads theoremLocals t.proof
  let derivation? ←
    checkLFJudgmentDerivation sig rules globalHeads theoremKnownTypes knownLFDefValues
      theoremLocals availableLocalStatements availableTheoremStatements availableTheoremNames
      t.name t.judgmentExpr t.proof
  let some derivation := derivation?
    | throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has unchecked proof \
      '{diagnosticObjExprString t.proof}'; expected a local theorem assumption, checked \
        judgment theorem, or LF rule application"
  let kernelDerivation? ←
    tryLowerLFDerivationToKernel? sig rules globalHeads theoremKnownTypes knownLFDefValues
      theoremLocals t.name derivation
  let ruleSummary := summarizeLFRuleApplication? derivation
  let checkedTheorem : CheckedLFJudgmentTheorem := {
    name := t.name.eraseMacroScopes
    binders := checkedBinders
    judgmentExpr := t.judgmentExpr
    checkedJudgmentExpr := checkedJudgment
    judgmentHead := judgmentHead
    proof := t.proof
    checkedProof := checkedProof
    proofHead? := proofHead?
    proofRule? := ruleSummary.proofRule?
    proofRuleArgs := ruleSummary.proofRuleArgs
    premiseTheorems := ruleSummary.premiseTheorems
    sideConditionCertificateNames := ruleSummary.sideConditionCertificateNames
    derivation? := some derivation
    kernelDerivation? := kernelDerivation? }
  let theoremName := t.name.eraseMacroScopes
  let availableStatements :=
    if t.binders.isEmpty then
      ctx.availableLFTheoremStatements.insert theoremName
        (eraseObjExprScopes (checkedLFDerivationStatement derivation))
    else
      ctx.availableLFTheoremStatements
  let ctx := { ctx with
    availableLFTheoremStatements := availableStatements
    availableLFTheoremNames := ctx.availableLFTheoremNames.insert theoremName
    newJudgmentTheorems := ctx.newJudgmentTheorems.push checkedTheorem }
  pure (checkedTheorem, ctx)

/-- Incrementally check one LF object definition against existing checked definitions. -/
def checkOneLFObjectDefArtifactInSignature (sig : HLSignature) (d : LFObjectDefDecl)
    (priorDefs : Array CheckedLFObjectDef) : CoreM CheckedLFObjectDef := do
  let checkedBase : CheckedSignature := { name := sig.name, lfObjectDefs := priorDefs }
  let ctx := mkIntraBlockLFCheckContext sig checkedBase
  let (checkedDef, _) ← checkLFObjectDefInContext ctx d
  pure checkedDef

/-- Incrementally check one LF judgment theorem against existing checked artifacts. -/
def checkOneLFJudgmentTheoremArtifactInSignature (sig : HLSignature) (rules : Array CheckedLFRule)
    (t : LFJudgmentTheoremDecl) (priorDefs : Array CheckedLFObjectDef)
    (priorTheorems : Array CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let checkedBase : CheckedSignature := {
    name := sig.name
    lfRules := rules
    lfObjectDefs := priorDefs
    lfJudgmentTheorems := priorTheorems }
  let ctx := mkIntraBlockLFCheckContext sig checkedBase
  let (checkedTheorem, _) ← checkLFJudgmentTheoremInContext ctx t
  pure checkedTheorem

/-- Incrementally check one LF object definition using a compiled checked-theory cache. -/
def checkOneLFObjectDefArtifactWithCache (cache : CompiledLFCheckCache)
    (d : LFObjectDefDecl) : CoreM CheckedLFObjectDef := do
  let ctx := mkIntraBlockLFCheckContextFromCache cache { lfObjectDefs := #[d] }
  let (checkedDef, _) ← checkLFObjectDefInContext ctx d
  pure checkedDef

/-- Incrementally check one LF judgment theorem using a compiled checked-theory cache. -/
def checkOneLFJudgmentTheoremArtifactWithCache (cache : CompiledLFCheckCache)
    (t : LFJudgmentTheoremDecl) : CoreM CheckedLFJudgmentTheorem := do
  let ctx := mkIntraBlockLFCheckContextFromCache cache { lfJudgmentTheorems := #[t] }
  let (checkedTheorem, _) ← checkLFJudgmentTheoremInContext ctx t
  pure checkedTheorem

/-- Stream-check all LF object definitions and theorem artifacts in a flat signature. -/
def checkLFObjectArtifactsInSignatureStreaming (sig : HLSignature)
    (rules : Array CheckedLFRule) :
    CoreM (Array CheckedLFObjectDef × Array CheckedLFJudgmentTheorem) := do
  let checkedBase : CheckedSignature := { name := sig.name }
  let mut ctx := mkIntraBlockLFCheckContext sig checkedBase rules
  for d in sig.lfObjectDefs do
    let (_, ctx') ← checkLFObjectDefInContextSelected ctx d
    ctx := ctx'
  for t in sig.lfJudgmentTheorems do
    let (_, ctx') ← checkLFJudgmentTheoremInContext ctx t
    ctx := ctx'
  pure (ctx.newObjectDefs, ctx.newJudgmentTheorems)

/-- Lightweight high-level LF occurrence check used for ordered metadata validation. -/
partial def lfExprContainsIdent (needle : Name) : ObjExpr → Bool
  | .ident n => n.eraseMacroScopes == needle.eraseMacroScopes
  | .sort | .univ .. => false
  | .app f a => lfExprContainsIdent needle f || lfExprContainsIdent needle a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      lfExprContainsIdent needle A ||
        if x.map Name.eraseMacroScopes == some needle.eraseMacroScopes then false else
          lfExprContainsIdent needle B
  | .pair a b => lfExprContainsIdent needle a || lfExprContainsIdent needle b
  | .fst e | .snd e => lfExprContainsIdent needle e
  | .lam xs body =>
      if xs.map Name.eraseMacroScopes |>.contains needle.eraseMacroScopes then false else
        lfExprContainsIdent needle body
  | .jeq lhs rhs => lfExprContainsIdent needle lhs || lfExprContainsIdent needle rhs

/-- Free LF identifiers as a set, respecting expression binders. -/
def lfExprFreeIdentifierSet (e : ObjExpr) : NameSet :=
  (freeLFObjectIdentifierArray e).foldl (init := {}) fun acc n =>
    acc.insert n.eraseMacroScopes

/-- Check that one `syntax_def` does not mention syntax definitions that are not yet available.

The old implementation traversed the declaration once per unavailable syntax definition. This
variant traverses each parameter type/body once, then preserves the old declaration-order diagnostic
priority with cheap set membership tests. -/
def checkNoUnavailableSyntaxDefRefsFrom (sig : HLSignature) (d : SyntaxDefDecl)
    (syntaxDefNames : Array Name) (startIndex : Nat) : CoreM Unit := do
  let paramRefs := d.params.map fun b =>
    (b.name.eraseMacroScopes, lfExprFreeIdentifierSet b.typeExpr)
  let valueRefs? := d.value?.map lfExprFreeIdentifierSet
  let mut idx := startIndex
  while idx < syntaxDefNames.size do
    let other := syntaxDefNames[idx]!.eraseMacroScopes
    for entry in paramRefs do
      if entry.2.contains other then
        throwError "syntax_def '{d.name}' in type theory '{sig.name}' references syntax_def \
          '{other}' before it is available in parameter '{entry.1}' type"
    if let some valueRefs := valueRefs? then
      if valueRefs.contains other then
        throwError "syntax_def '{d.name}' in type theory '{sig.name}' references syntax_def \
          '{other}' before it is available in value"
    idx := idx + 1

/-- Check one syntax-sort declaration's metadata. -/
def checkOneSyntaxSortMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat))
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (syntaxSortArities : NameMap Nat) (sort : SyntaxSortDecl) : CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "syntax_sort" sort.name sort.params
  discard <| checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "syntax_sort"
    sort.name sort.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "syntax_sort" sort.name
    sort.params
  checkLFSyntaxSortArgumentsInBindings sig "syntax_sort" sort.name sort.params
  checkLFBinderTypesInBindings sig globalHeads "syntax_sort" sort.name sort.params

/-- Check one syntax-abbreviation declaration's metadata. -/
def checkOneSyntaxAbbrevMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (abbr : SyntaxAbbrevDecl) :
    CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "syntax_abbrev" abbr.name abbr.params
  let abbrLocals ←
    checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "syntax_abbrev" abbr.name
      abbr.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "syntax_abbrev" abbr.name
    abbr.params
  checkLFSyntaxSortArgumentsInBindings sig "syntax_abbrev" abbr.name abbr.params
  checkLFBinderTypesInBindings sig globalHeads "syntax_abbrev" abbr.name abbr.params
  let abbrLocalTypes := lfLocalTypesOfBindings abbr.params
  checkKnownNamesInLFExpr sig lfGlobals abbrLocals opaqueArities "syntax_abbrev" abbr.name
    "value" abbr.value
  checkSyntaxSortApplicationsInExpr sig syntaxSortArities "syntax_abbrev" abbr.name "value"
    abbr.value
  checkLFSyntaxSortArgumentsInExpr sig "syntax_abbrev" abbr.name "value" abbrLocalTypes
    abbr.value
  checkLFInferableApplicationArguments sig "syntax_abbrev" abbr.name "value" abbrLocalTypes
    abbr.value
  checkLFBinderType sig globalHeads "syntax_abbrev" abbr.name "value" abbrLocalTypes
    abbrLocals false abbr.value

/-- Check one syntax-definition declaration's metadata using a reusable LF lookup context. -/
def checkOneSyntaxDefMetadataInSignatureWithLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (lfGlobals : NameSet) (opaqueArities : NameMap (Option Nat))
    (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (d : SyntaxDefDecl) :
    CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "syntax_def" d.name d.params
  let localNames ←
    checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "syntax_def" d.name d.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "syntax_def" d.name d.params
  checkLFSyntaxSortArgumentsInBindingsWithLookup lookup sig "syntax_def" d.name d.params
  checkLFBinderTypesInBindingsWithLookup lookup sig globalHeads "syntax_def" d.name d.params
  let localTypes := lfLocalTypesOfBindings d.params
  if let some value := d.value? then
    checkKnownNamesInLFExpr sig lfGlobals localNames opaqueArities "syntax_def" d.name "value"
      value
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities "syntax_def" d.name "value" value
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig "syntax_def" d.name
      (lfCheckWhere "value")
      localTypes value
    checkLFInferableApplicationArgumentsWithLookup lookup sig "syntax_def" d.name
      (lfCheckWhere "value")
      localTypes value
    checkLFBinderTypeWithLookup lookup sig globalHeads "syntax_def" d.name "value" localTypes
      localNames false value
    if let some actualLevel := inferLFTypeExprUniverseLevelWithLookup? lookup localTypes value then
      unless LevelExpr.equal actualLevel d.resultLevel do
        throwError "syntax_def '{d.name}' in type theory '{sig.name}' has value in universe \
          '{diagnosticObjExprString (objExprTypeOfLevel actualLevel)}', expected \
            '{diagnosticObjExprString (objExprTypeOfLevel d.resultLevel)}'"

/-- Check one syntax-definition declaration's metadata. -/
def checkOneSyntaxDefMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (d : SyntaxDefDecl) :
    CoreM Unit := do
  checkOneSyntaxDefMetadataInSignatureWithLookup (mkLFCheckLookupContext sig) sig lfGlobals
    opaqueArities syntaxSortArities globalHeads d

/-- Check the parameter telescope of one syntax-definition declaration. -/
def checkOneSyntaxDefParameterMetadataInSignatureWithLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (lfGlobals : NameSet) (opaqueArities : NameMap (Option Nat))
    (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (d : SyntaxDefDecl) :
    CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "syntax_def" d.name d.params
  discard <| checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "syntax_def" d.name
    d.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "syntax_def" d.name d.params
  checkLFSyntaxSortArgumentsInBindingsWithLookup lookup sig "syntax_def" d.name d.params
  checkLFBinderTypesInBindingsWithLookup lookup sig globalHeads "syntax_def" d.name d.params

/-- Check one syntax-definition declaration using the selected theory-body backend. -/
def checkOneSyntaxDefMetadataInSignatureSelected (mirrorSig : HLSignature)
    (lookup : LFCheckLookupContext) (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (d : SyntaxDefDecl) :
    CoreM Unit := do
  let useMirror :=
    (← getBoolOption `internalLean.mirrorBackend.checkTheoryBodies) &&
      match d.value? with
      | some value => lfMirrorObjExprNodeCountLE lfMirrorTheoryBodySyntaxDefCheckNodeLimit value
      | none => false
  if useMirror then
    checkOneSyntaxDefParameterMetadataInSignatureWithLookup lookup sig lfGlobals opaqueArities
      syntaxSortArities globalHeads d
    let compareWithLF ← getBoolOption `internalLean.mirrorBackend.compareTheoryBodiesWithLF
    try
      withRestoredCoreStateOnError do
        profileLFCheckPhase m!"{d.name}: mirror syntax_def body check" do
          withLFMirrorFastPathHeartbeats do
            ensureLFMirrorForSignatureBestEffort mirrorSig
            addLFMirrorPendingDecl mirrorSig.name (lfMirrorLevelParamNamesForSignature mirrorSig)
              (lfMirrorLevelArgsForSignature mirrorSig) (.syntaxDef d)
      if compareWithLF then
        checkOneSyntaxDefMetadataInSignatureWithLookup lookup sig lfGlobals opaqueArities
          syntaxSortArities globalHeads d
    catch _ =>
      checkOneSyntaxDefMetadataInSignatureWithLookup lookup sig lfGlobals opaqueArities
        syntaxSortArities globalHeads d
  else
    checkOneSyntaxDefMetadataInSignatureWithLookup lookup sig lfGlobals opaqueArities
      syntaxSortArities globalHeads d

/-- Check one judgment-abbreviation declaration's metadata. -/
def checkOneJudgmentAbbrevMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (abbr : JudgmentAbbrevDecl) :
    CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "judgment_abbrev" abbr.name abbr.params
  let abbrLocals ←
    checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "judgment_abbrev" abbr.name
      abbr.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "judgment_abbrev" abbr.name
    abbr.params
  checkLFSyntaxSortArgumentsInBindings sig "judgment_abbrev" abbr.name abbr.params
  checkLFBinderTypesInBindings sig globalHeads "judgment_abbrev" abbr.name abbr.params
  let abbrLocalTypes := lfLocalTypesOfBindings abbr.params
  checkKnownNamesInLFExpr sig lfGlobals abbrLocals opaqueArities "judgment_abbrev" abbr.name
    "value" abbr.value
  checkSyntaxSortApplicationsInExpr sig syntaxSortArities "judgment_abbrev" abbr.name "value"
    abbr.value
  checkLFSyntaxSortArgumentsInExpr sig "judgment_abbrev" abbr.name "value" abbrLocalTypes
    abbr.value
  checkLFInferableApplicationArguments sig "judgment_abbrev" abbr.name "value" abbrLocalTypes
    abbr.value
  checkLFBinderType sig globalHeads "judgment_abbrev" abbr.name "value" abbrLocalTypes
    abbrLocals true abbr.value
  match checkedLFHead? globalHeads abbrLocals abbr.value with
  | some head =>
      unless head.kind == .judgment do
        throwError "judgment_abbrev '{abbr.name}' in type theory '{sig.name}' has value headed \
          by {head.kind.label} '{head.name}', expected a judgment-headed expression"
  | none =>
      throwError "judgment_abbrev '{abbr.name}' in type theory '{sig.name}' has value not headed \
        by a known judgment: {diagnosticObjExprString abbr.value}"

/-- Check one judgment declaration's metadata. -/
def checkOneJudgmentMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat))
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (syntaxSortArities : NameMap Nat) (j : JudgmentDecl) : CoreM Unit := do
  checkNoDuplicateMetadataBinders sig "judgment" j.name j.params
  discard <| checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "judgment" j.name
    j.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "judgment" j.name j.params
  checkLFSyntaxSortArgumentsInBindings sig "judgment" j.name j.params
  checkLFBinderTypesInBindings sig globalHeads "judgment" j.name j.params

/-- Check one typed LF-opaque declaration's metadata. Untyped opaques are accepted directly. -/
def checkOneLFOpaqueConstMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (syntaxSortArities : NameMap Nat)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (opaqueDecl : LFOpaqueConstDecl)
    (knownLFDefTypes : LFLocalTypes := {}) : CoreM Unit := do
  if opaqueDecl.typeExpr?.isSome then
    checkNoDuplicateMetadataBinders sig "lf_opaque" opaqueDecl.name opaqueDecl.params
    let opaqueLocals ←
      checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "lf_opaque" opaqueDecl.name
        opaqueDecl.params
    checkSyntaxSortApplicationsInBindings sig syntaxSortArities "lf_opaque" opaqueDecl.name
      opaqueDecl.params
    checkLFSyntaxSortArgumentsInBindings sig "lf_opaque" opaqueDecl.name opaqueDecl.params
    checkLFBinderTypesInBindings sig globalHeads "lf_opaque" opaqueDecl.name opaqueDecl.params
    let opaqueLocalTypes := opaqueDecl.params.foldl (init := knownLFDefTypes) fun acc b =>
      acc.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    if let some typeExpr := opaqueDecl.typeExpr? then
      discard <| checkLFObjectOrStructuralType sig globalHeads opaqueLocalTypes opaqueLocals
        "lf_opaque" opaqueDecl.name "result type" typeExpr

/-- Check one conversion-plugin declaration's step metadata. -/
def checkOneConversionPluginMetadataInSignature (sig : HLSignature)
    (plugin : ConversionPluginDecl) : CoreM Unit := do
  let pluginName := plugin.name.eraseMacroScopes
  let mut steps : Array ConversionStepKind := #[]
  for step in plugin.supportedSteps do
    if steps.contains step then
      let msg := s!"duplicate conversion_plugin step '{step.label}' for plugin " ++
        s!"'{pluginName}' in type theory '{sig.name}'"
      throwError "{msg}"
    steps := steps.push step

/-- Check one rule declaration using the same metadata validation as the full signature checker. -/
def checkOneRuleMetadataInSignature (sig : HLSignature) (lfGlobals : NameSet)
    (opaqueArities : NameMap (Option Nat))
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (syntaxSortArities judgmentArities : NameMap Nat) (solvers : NameSet) (r : RuleDecl) :
    CoreM CheckedLFRule := do
  checkNoDuplicateMetadataBinders sig "rule" r.name r.params
  let ruleParamLocals ←
    checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "rule" r.name r.params
  checkSyntaxSortApplicationsInBindings sig syntaxSortArities "rule" r.name r.params
  checkLFSyntaxSortArgumentsInBindings sig "rule" r.name r.params
  checkLFBinderTypesInBindings sig globalHeads "rule" r.name r.params
  let (checkedParams, _) ← checkedLFBindings sig globalHeads "rule" r.name r.params
  let ruleLocalTypes := lfLocalTypesOfBindings r.params
  let paramNames : NameSet := r.params.foldl (init := {}) fun acc p =>
    acc.insert p.name.eraseMacroScopes
  let mut evidenceParamNames : NameSet := {}
  let mut checkedParamEvidences : Array CheckedLFRuleParamEvidence := #[]
  for ev in r.paramEvidences do
    let paramName := ev.paramName.eraseMacroScopes
    if !paramNames.contains paramName then
      throwError "rule '{r.name}' in type theory '{sig.name}' has evidence for unknown \
        parameter '{ev.paramName}'"
    if evidenceParamNames.contains paramName then
      throwError "rule '{r.name}' in type theory '{sig.name}' has duplicate evidence for \
        parameter '{ev.paramName}'"
    evidenceParamNames := evidenceParamNames.insert paramName
    let some paramIndex := r.params.findIdx? (fun p => p.name.eraseMacroScopes == paramName)
      | throwError "rule '{r.name}' in type theory '{sig.name}' has evidence for unknown \
        parameter '{ev.paramName}'"
    for later in r.params.toList.drop (paramIndex + 1) do
      if lfExprContainsIdent later.name ev.judgmentExpr then
        throwError "rule '{r.name}' in type theory '{sig.name}' has evidence for parameter \
          '{ev.paramName}' referencing later parameter '{later.name}'"
    checkKnownNamesInLFExpr sig lfGlobals ruleParamLocals opaqueArities "rule" r.name
      s!"evidence for parameter '{ev.paramName}'" ev.judgmentExpr
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities "rule" r.name s!"evidence for \
      parameter '{ev.paramName}'" ev.judgmentExpr
    checkLFSyntaxSortArgumentsInExpr sig "rule" r.name s!"evidence for parameter \
      '{ev.paramName}'" ruleLocalTypes ev.judgmentExpr
    let head ←
      checkRuleJudgmentHead sig judgmentArities r.name s!"evidence for parameter \
        '{ev.paramName}'" ev.judgmentExpr
    let (_, evidenceArgs) := splitObjApp ev.judgmentExpr
    checkLFJudgmentArguments sig r.name s!"evidence for parameter \
      '{ev.paramName}'" ruleLocalTypes head.name evidenceArgs
    let checkedJudgmentExpr ←
      resolveLFExpr sig globalHeads ruleParamLocals "rule" r.name s!"evidence for parameter \
        '{ev.paramName}'" ev.judgmentExpr
    checkedParamEvidences := checkedParamEvidences.push {
      name := ev.name.eraseMacroScopes
      paramName := paramName
      judgmentExpr := ev.judgmentExpr
      checkedJudgmentExpr := checkedJudgmentExpr
      head := head }
  let mut localNames : NameSet := {}
  let mut checkedPremises : Array CheckedLFRulePremise := #[]
  for p in r.premises do
    let premiseName := p.name.eraseMacroScopes
    if localNames.contains premiseName then
      throwError "duplicate premise/side-condition name '{p.name}' in rule '{r.name}' of type \
        theory '{sig.name}'"
    localNames := localNames.insert premiseName
    checkKnownNamesInLFExpr sig lfGlobals ruleParamLocals opaqueArities "rule" r.name
      s!"premise '{p.name}'" p.judgmentExpr
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities "rule" r.name s!"premise '{p.name}'"
      p.judgmentExpr
    checkLFSyntaxSortArgumentsInExpr sig "rule" r.name s!"premise '{p.name}'" ruleLocalTypes
      p.judgmentExpr
    checkLFEvidenceType sig globalHeads "rule" r.name s!"premise '{p.name}'" ruleLocalTypes
      ruleParamLocals p.judgmentExpr
    let head? := checkedLFHead? globalHeads ruleParamLocals p.judgmentExpr
    let checkedJudgmentExpr ←
      resolveLFExpr sig globalHeads ruleParamLocals "rule" r.name s!"premise '{p.name}'"
        p.judgmentExpr
    checkedPremises := checkedPremises.push {
      name := premiseName
      judgmentExpr := p.judgmentExpr
      checkedJudgmentExpr := checkedJudgmentExpr
      head? := head?
    }
  let mut checkedSideConditions : Array CheckedLFRuleSideCondition := #[]
  for sc in r.sideConditions do
    let sideConditionName := sc.name.eraseMacroScopes
    if localNames.contains sideConditionName then
      throwError "duplicate premise/side-condition name '{sc.name}' in rule '{r.name}' of type \
        theory '{sig.name}'"
    localNames := localNames.insert sideConditionName
    if !solvers.contains sc.solver then
      throwError "rule '{r.name}' in type theory '{sig.name}' uses unknown side-condition \
        solver '{sc.solver}'"
    checkKnownNamesInLFExpr sig lfGlobals ruleParamLocals opaqueArities "rule" r.name
      s!"side-condition '{sc.name}'" sc.input
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities "rule" r.name s!"side-condition \
      '{sc.name}'" sc.input
    checkLFSyntaxSortArgumentsInExpr sig "rule" r.name s!"side-condition \
      '{sc.name}'" ruleLocalTypes sc.input
    let some sideHead := checkedLFHead? globalHeads ruleParamLocals sc.input
      | throwError "rule '{r.name}' in type theory '{sig.name}' has side-condition '{sc.name}' \
        not headed by a known LF identifier: {sc.input}"
    if sideHead.kind == .local then
      throwError "rule '{r.name}' in type theory '{sig.name}' has side-condition '{sc.name}' \
        headed by local parameter '{sideHead.name}'; declare a judgment or lf_opaque \
          placeholder instead"
    if sideHead.kind == .judgment then
      let (_, sideArgs) := splitObjApp sc.input
      checkLFJudgmentArguments sig r.name s!"side-condition \
        '{sc.name}'" ruleLocalTypes sideHead.name sideArgs
    let checkedInput ←
      resolveLFExpr sig globalHeads ruleParamLocals "rule" r.name s!"side-condition \
        '{sc.name}'" sc.input
    checkedSideConditions := checkedSideConditions.push {
      name := sideConditionName
      solver := sc.solver.eraseMacroScopes
      input := sc.input
      checkedInput := checkedInput
      head? := some sideHead }
  checkKnownNamesInLFExpr sig lfGlobals ruleParamLocals opaqueArities "rule" r.name "conclusion"
    r.conclusionExpr
  checkNoCaptureUnsafeBetaInLFExpr sig "rule" r.name "conclusion" r.conclusionExpr
  checkSyntaxSortApplicationsInExpr sig syntaxSortArities "rule" r.name "conclusion"
    r.conclusionExpr
  checkLFSyntaxSortArgumentsInExpr sig "rule" r.name "conclusion" ruleLocalTypes r.conclusionExpr
  let conclusionHead ←
    checkRuleJudgmentHead sig judgmentArities r.name "conclusion" r.conclusionExpr
  let (_, conclusionArgs) := splitObjApp r.conclusionExpr
  checkLFJudgmentArguments sig r.name "conclusion" ruleLocalTypes conclusionHead.name
    conclusionArgs
  let checkedConclusionExpr ←
    resolveLFExpr sig globalHeads ruleParamLocals "rule" r.name "conclusion" r.conclusionExpr
  pure {
    name := r.name.eraseMacroScopes
    params := checkedParams
    premises := checkedPremises
    paramEvidences := checkedParamEvidences
    sideConditions := checkedSideConditions
    conclusionExpr := r.conclusionExpr
    checkedConclusionExpr := checkedConclusionExpr
    conclusionHead := conclusionHead }

/-- Check Phase-1 logical-framework metadata for local name clashes and known references,
returning checked LF rule artifacts for later phases. -/
def checkRuleMetadataInSignature (sig : HLSignature) : CoreM (Array CheckedLFRule) := do
  let lfGlobals := lfKnownGlobalNames sig
  let opaqueArities := lfOpaqueArities sig
  let globalHeads := lfGlobalHeadInfo sig
  let lookup := mkLFCheckLookupContext sig
  let syntaxSortNames : NameSet := sig.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes
  let syntaxFamilyNames : NameSet := sig.syntaxDefs.foldl (init := syntaxSortNames) fun acc d =>
    acc.insert d.name.eraseMacroScopes
  let syntaxSortArities : NameMap Nat := lfSyntaxFamilyArities sig
  for sort in sig.syntaxSorts do
    checkOneSyntaxSortMetadataInSignature sig lfGlobals opaqueArities globalHeads
      syntaxSortArities sort
  for abbr in sig.syntaxAbbrevs do
    checkOneSyntaxAbbrevMetadataInSignature sig lfGlobals opaqueArities syntaxSortArities
      globalHeads abbr
  let syntaxDefNames := sig.syntaxDefs.map (fun d => d.name.eraseMacroScopes)
  for _h : i in [:sig.syntaxDefs.size] do
    let d := sig.syntaxDefs[i]!
    checkNoUnavailableSyntaxDefRefsFrom sig d syntaxDefNames i
    let mirrorSig := {
      sig with
      syntaxDefs := sig.syntaxDefs.extract 0 (i + 1)
      lfObjectDefs := #[]
      lfJudgmentTheorems := #[]
      rules := #[] }
    checkOneSyntaxDefMetadataInSignatureSelected mirrorSig lookup sig lfGlobals opaqueArities
      syntaxSortArities globalHeads d
  for abbr in sig.judgmentAbbrevs do
    checkOneJudgmentAbbrevMetadataInSignature sig lfGlobals opaqueArities syntaxSortArities
      globalHeads abbr
  let mut seenSortRoles : NameMap NameSet := {}
  for role in sig.syntaxSortRoles do
    if !syntaxFamilyNames.contains role.sortName then
      throwError "syntax_sort_role for unknown syntax family '{role.sortName}' in type theory \
        '{sig.name}'"
    let kinds := (seenSortRoles.find? role.sortName).getD {}
    if kinds.contains role.kind then
      throwError "duplicate syntax_sort_role '{role.kind}' for syntax sort '{role.sortName}' in \
        type theory '{sig.name}'"
    seenSortRoles := seenSortRoles.insert role.sortName (kinds.insert role.kind)
  let mut seenZones : NameSet := {}
  for zone in sig.contextZones do
    let zoneName := zone.name.eraseMacroScopes
    let sortName := zone.sortName.eraseMacroScopes
    if !syntaxSortNames.contains sortName then
      throwError "context_zone '{zone.name}' in type theory '{sig.name}' uses unknown syntax sort \
        '{zone.sortName}'"
    let mut seenDeps : NameSet := {}
    for dep in zone.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{sig.name}' has duplicate \
          dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !seenZones.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{sig.name}' depends on unknown or \
          later zone '{dep}'"
    seenZones := seenZones.insert zoneName
  let mut seenBinderClasses : NameSet := {}
  for binderClass in sig.binderClasses do
    let binderName := binderClass.name.eraseMacroScopes
    let sortName := binderClass.boundSortName.eraseMacroScopes
    let zoneName := binderClass.zoneName.eraseMacroScopes
    if seenBinderClasses.contains binderName then
      throwError "duplicate binder_class '{binderName}' in type theory '{sig.name}'"
    seenBinderClasses := seenBinderClasses.insert binderName
    if !syntaxSortNames.contains sortName then
      throwError "binder_class '{binderClass.name}' in type theory '{sig.name}' uses unknown \
        syntax sort '{binderClass.boundSortName}'"
    if !seenZones.contains zoneName then
      throwError "binder_class '{binderClass.name}' in type theory '{sig.name}' uses unknown \
        context zone '{binderClass.zoneName}'"
    let mut seenDeps : NameSet := {}
    for dep in binderClass.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{sig.name}' has duplicate \
          dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !seenZones.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{sig.name}' depends on \
          unknown context zone '{dep}'"
  let judgmentNames : NameSet := sig.judgments.foldl (init := {}) fun acc j => acc.insert j.name
  let judgmentArities : NameMap Nat := sig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name j.params.size
  for j in sig.judgments do
    checkOneJudgmentMetadataInSignature sig lfGlobals opaqueArities globalHeads syntaxSortArities j
  let mut seenRoles : NameMap NameSet := {}
  for role in sig.judgmentRoles do
    if !judgmentNames.contains role.judgmentName then
      throwError "judgment_role for unknown judgment '{role.judgmentName}' in type theory \
        '{sig.name}'"
    let kinds := (seenRoles.find? role.judgmentName).getD {}
    if kinds.contains role.kind then
      throwError "duplicate judgment_role '{role.kind}' for judgment '{role.judgmentName}' in \
        type theory '{sig.name}'"
    seenRoles := seenRoles.insert role.judgmentName (kinds.insert role.kind)
  let ruleNames : NameSet := sig.rules.foldl (init := {}) fun acc r => acc.insert r.name
  let mut seenRuleRoles : NameMap NameSet := {}
  for role in sig.ruleRoles do
    if !ruleNames.contains role.ruleName then
      throwError "rule_role for unknown rule '{role.ruleName}' in type theory '{sig.name}'"
    let kinds := (seenRuleRoles.find? role.ruleName).getD {}
    if kinds.contains role.kind then
      throwError "duplicate rule_role '{role.kind}' for rule '{role.ruleName}' in type theory \
        '{sig.name}'"
    seenRuleRoles := seenRuleRoles.insert role.ruleName (kinds.insert role.kind)
  let mut solvers : NameSet := {}
  for solver in sig.sideConditionSolvers do
    let solverName := solver.name.eraseMacroScopes
    if solvers.contains solverName then
      throwError "duplicate side_condition_solver '{solverName}' in type theory '{sig.name}'"
    solvers := solvers.insert solverName
  let mut plugins : NameSet := {}
  for plugin in sig.conversionPlugins do
    let pluginName := plugin.name.eraseMacroScopes
    if plugins.contains pluginName then
      throwError "duplicate conversion_plugin '{pluginName}' in type theory '{sig.name}'"
    plugins := plugins.insert pluginName
    checkOneConversionPluginMetadataInSignature sig plugin
  let knownLFDefTypes := lfDefinitionTypeMapFromDecls sig.lfObjectDefs
  for opaqueDecl in sig.lfOpaqueConsts do
    checkOneLFOpaqueConstMetadataInSignature sig lfGlobals opaqueArities syntaxSortArities
      globalHeads opaqueDecl knownLFDefTypes
  let mut checkedRules : Array CheckedLFRule := #[]
  for r in sig.rules do
    checkedRules := checkedRules.push (← checkOneRuleMetadataInSignature sig lfGlobals
      opaqueArities globalHeads syntaxSortArities judgmentArities solvers r)
  pure checkedRules

/-- Explicit parameter names for a global LF head that can be marked as a rewrite relation. -/
def lfRewriteRelationParams? (sig : HLSignature) (relationName : Name) : Option (Array Name) :=
  let relationName := relationName.eraseMacroScopes
  if let some j := sig.judgments.find? (fun j => j.name.eraseMacroScopes == relationName) then
    some (j.params.map (fun b => b.name.eraseMacroScopes))
  else if let some s := sig.syntaxSorts.find? (fun s =>
      s.name.eraseMacroScopes == relationName) then
    some (s.params.map (fun b => b.name.eraseMacroScopes))
  else
    match sig.lfOpaqueConsts.find? (fun o => o.name.eraseMacroScopes == relationName) with
    | some o => some (o.params.map (fun b => b.name.eraseMacroScopes))
    | none => none

/-- Validate that a symmetry declaration swaps the endpoints of a rewrite relation. -/
def checkLFRewriteSymmetryShape (sig : HLSignature) (symmName relationName evidenceName : Name)
    (evidenceExpr conclusionExpr : ObjExpr) : CoreM Unit := do
  let relationName := relationName.eraseMacroScopes
  let some rel := sig.rewriteRelations.find? (fun r =>
      r.relationName.eraseMacroScopes == relationName)
    | throwError "internal error: missing rewrite_relation '{relationName}'"
  let some params := lfRewriteRelationParams? sig relationName
    | throwError "internal error: missing relation head '{relationName}'"
  let some lhsIdx := params.findIdx? (fun n => n == rel.lhsParam.eraseMacroScopes)
    | throwError "internal error: missing lhs parameter for '{relationName}'"
  let some rhsIdx := params.findIdx? (fun n => n == rel.rhsParam.eraseMacroScopes)
    | throwError "internal error: missing rhs parameter for '{relationName}'"
  match splitObjApp evidenceExpr, splitObjApp conclusionExpr with
  | (.ident evHead, evArgs), (.ident conclHead, conclArgs) =>
      unless evHead.eraseMacroScopes == relationName do
        let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
          s!"has evidence '{evidenceName}' headed by '{evHead}', expected '{relationName}'"
        throwError "{msg}"
      unless conclHead.eraseMacroScopes == relationName do
        let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
          s!"has conclusion headed by '{conclHead}', expected '{relationName}'"
        throwError "{msg}"
      unless evArgs.size == params.size && conclArgs.size == params.size do
        let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
          s!"does not use the declared arity of relation '{relationName}'"
        throwError "{msg}"
      unless eraseObjExprScopes evArgs[lhsIdx]! == eraseObjExprScopes conclArgs[rhsIdx]! &&
          eraseObjExprScopes evArgs[rhsIdx]! == eraseObjExprScopes conclArgs[lhsIdx]! do
        let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
          s!"does not swap endpoints '{rel.lhsParam}' and '{rel.rhsParam}'"
        throwError "{msg}"
      for i in [:params.size] do
        if i != lhsIdx && i != rhsIdx then
          unless eraseObjExprScopes evArgs[i]! == eraseObjExprScopes conclArgs[i]! do
            let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
              s!"changes non-endpoint argument {i} of relation '{relationName}'"
            throwError "{msg}"
  | _, _ =>
      let msg := s!"rewrite_symmetry '{symmName}' in type theory '{sig.name}' " ++
        "requires headed relation applications for evidence and conclusion"
      throwError "{msg}"

/-- Validate that a congruence declaration maps relation evidence under one head. -/
def checkLFRewriteCongruenceShape (sig : HLSignature) (congrName relationName targetHead
    evidenceName : Name) (argumentIndex : Nat) (evidenceExpr conclusionExpr : ObjExpr) :
    CoreM Unit := do
  let relationName := relationName.eraseMacroScopes
  let targetHead := targetHead.eraseMacroScopes
  let some rel := sig.rewriteRelations.find? (fun r =>
      r.relationName.eraseMacroScopes == relationName)
    | throwError "internal error: missing rewrite_relation '{relationName}'"
  let some relParams := lfRewriteRelationParams? sig relationName
    | throwError "internal error: missing relation head '{relationName}'"
  let some targetParams := lfRewriteRelationParams? sig targetHead
    | throwError "internal error: missing target head '{targetHead}'"
  unless argumentIndex < targetParams.size do
    let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
      s!"uses argument index {argumentIndex}, but '{targetHead}' has " ++
      s!"{targetParams.size} parameter(s)"
    throwError "{msg}"
  let some lhsIdx := relParams.findIdx? (fun n => n == rel.lhsParam.eraseMacroScopes)
    | throwError "internal error: missing lhs parameter for '{relationName}'"
  let some rhsIdx := relParams.findIdx? (fun n => n == rel.rhsParam.eraseMacroScopes)
    | throwError "internal error: missing rhs parameter for '{relationName}'"
  match splitObjApp evidenceExpr, splitObjApp conclusionExpr with
  | (.ident evHead, evArgs), (.ident conclHead, conclArgs) =>
      unless evHead.eraseMacroScopes == relationName do
        let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
          s!"has evidence '{evidenceName}' headed by '{evHead}', expected '{relationName}'"
        throwError "{msg}"
      unless conclHead.eraseMacroScopes == relationName do
        let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
          s!"has conclusion headed by '{conclHead}', expected '{relationName}'"
        throwError "{msg}"
      unless evArgs.size == relParams.size && conclArgs.size == relParams.size do
        let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
          s!"does not use the declared arity of relation '{relationName}'"
        throwError "{msg}"
      let (lhsHead, lhsArgs) := splitObjApp conclArgs[lhsIdx]!
      let (rhsHead, rhsArgs) := splitObjApp conclArgs[rhsIdx]!
      match lhsHead, rhsHead with
      | .ident lhsHeadName, .ident rhsHeadName =>
          unless lhsHeadName.eraseMacroScopes == targetHead &&
              rhsHeadName.eraseMacroScopes == targetHead do
            let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
              s!"does not conclude endpoints headed by '{targetHead}'"
            throwError "{msg}"
      | _, _ =>
          let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
            s!"requires relation endpoints headed by '{targetHead}'"
          throwError "{msg}"
      unless lhsArgs.size == targetParams.size && rhsArgs.size == targetParams.size do
        let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
          s!"does not use the declared arity of target head '{targetHead}'"
        throwError "{msg}"
      unless eraseObjExprScopes lhsArgs[argumentIndex]! == eraseObjExprScopes evArgs[lhsIdx]! &&
          eraseObjExprScopes rhsArgs[argumentIndex]! == eraseObjExprScopes evArgs[rhsIdx]! do
        let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
          s!"does not lift endpoints through '{targetHead}[{argumentIndex}]'"
        throwError "{msg}"
      for i in [:targetParams.size] do
        if i != argumentIndex then
          unless eraseObjExprScopes lhsArgs[i]! == eraseObjExprScopes rhsArgs[i]! do
            let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
              s!"changes non-target argument {i} of '{targetHead}'"
            throwError "{msg}"
      for i in [:relParams.size] do
        if i != lhsIdx && i != rhsIdx then
          unless eraseObjExprScopes evArgs[i]! == eraseObjExprScopes conclArgs[i]! do
            let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
              s!"changes non-endpoint argument {i} of relation '{relationName}'"
            throwError "{msg}"
  | _, _ =>
      let msg := s!"rewrite_congruence '{congrName}' in type theory '{sig.name}' " ++
        "requires headed relation applications for evidence and conclusion"
      throwError "{msg}"

/-- Check rewrite-relation and transport-rule metadata for known references. -/
def checkLFRewriteTransportMetadata (sig : HLSignature) : CoreM Unit := do
  let mut seenRelations : NameSet := {}
  for rel in sig.rewriteRelations do
    let relationName := rel.relationName.eraseMacroScopes
    if seenRelations.contains relationName then
      let msg := "duplicate rewrite_relation metadata for " ++
        s!"'{rel.relationName}' in type theory '{sig.name}'"
      throwError "{msg}"
    seenRelations := seenRelations.insert relationName
    let some params := lfRewriteRelationParams? sig relationName
      | let msg := "rewrite_relation for unknown LF head " ++
          s!"'{rel.relationName}' in type theory '{sig.name}'"
        throwError "{msg}"
    let lhs := rel.lhsParam.eraseMacroScopes
    let rhs := rel.rhsParam.eraseMacroScopes
    if lhs == rhs then
      let msg := s!"rewrite_relation '{rel.relationName}' in type theory " ++
        s!"'{sig.name}' uses the same lhs and rhs parameter '{lhs}'"
      throwError "{msg}"
    unless params.contains lhs do
      let msg := s!"rewrite_relation '{rel.relationName}' in type theory " ++
        s!"'{sig.name}' has unknown lhs parameter '{rel.lhsParam}'"
      throwError "{msg}"
    unless params.contains rhs do
      let msg := s!"rewrite_relation '{rel.relationName}' in type theory " ++
        s!"'{sig.name}' has unknown rhs parameter '{rel.rhsParam}'"
      throwError "{msg}"
  let relationNames : NameSet := sig.rewriteRelations.foldl (init := {}) fun acc rel =>
    acc.insert rel.relationName.eraseMacroScopes
  let mut seenSymmetries : NameSet := {}
  for symm in sig.rewriteSymmetries do
    let symmName := symm.symmetryName.eraseMacroScopes
    if seenSymmetries.contains symmName then
      let msg := "duplicate rewrite_symmetry metadata for " ++
        s!"'{symm.symmetryName}' in type theory '{sig.name}'"
      throwError "{msg}"
    seenSymmetries := seenSymmetries.insert symmName
    unless relationNames.contains symm.relationName.eraseMacroScopes do
      let msg := s!"rewrite_symmetry '{symm.symmetryName}' in type theory '{sig.name}' " ++
        s!"references undeclared rewrite_relation '{symm.relationName}'"
      throwError "{msg}"
    if let some ruleDecl := sig.rules.find? (fun r => r.name.eraseMacroScopes == symmName) then
      let some evPremise := ruleDecl.premises.find? (fun p =>
          p.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes)
        | let msg := s!"rewrite_symmetry '{symm.symmetryName}' in type theory " ++
            s!"'{sig.name}' has unknown evidence premise '{symm.evidenceParam}'"
          throwError "{msg}"
      checkLFRewriteSymmetryShape sig symm.symmetryName symm.relationName symm.evidenceParam
        evPremise.judgmentExpr ruleDecl.conclusionExpr
    else if let some thm := sig.lfJudgmentTheorems.find? (fun t =>
        t.name.eraseMacroScopes == symmName) then
      let some evBinder := thm.binders.find? (fun b =>
          b.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes)
        | let msg := s!"rewrite_symmetry '{symm.symmetryName}' in type theory " ++
            s!"'{sig.name}' has unknown evidence binder '{symm.evidenceParam}'"
          throwError "{msg}"
      checkLFRewriteSymmetryShape sig symm.symmetryName symm.relationName symm.evidenceParam
        evBinder.typeExpr thm.judgmentExpr
    else
      let msg := s!"rewrite_symmetry for unknown rule/theorem '{symm.symmetryName}' " ++
        s!"in type theory '{sig.name}'"
      throwError "{msg}"
  let mut seenCongruences : NameSet := {}
  for congr in sig.rewriteCongruences do
    let congrName := congr.congruenceName.eraseMacroScopes
    if seenCongruences.contains congrName then
      let msg := "duplicate rewrite_congruence metadata for " ++
        s!"'{congr.congruenceName}' in type theory '{sig.name}'"
      throwError "{msg}"
    seenCongruences := seenCongruences.insert congrName
    unless relationNames.contains congr.relationName.eraseMacroScopes do
      let msg := s!"rewrite_congruence '{congr.congruenceName}' in type theory " ++
        s!"'{sig.name}' references undeclared rewrite_relation '{congr.relationName}'"
      throwError "{msg}"
    unless (lfRewriteRelationParams? sig congr.targetHead).isSome do
      let msg := s!"rewrite_congruence '{congr.congruenceName}' in type theory " ++
        s!"'{sig.name}' references unknown LF head '{congr.targetHead}'"
      throwError "{msg}"
    if let some ruleDecl := sig.rules.find? (fun r => r.name.eraseMacroScopes == congrName) then
      let some evPremise := ruleDecl.premises.find? (fun p =>
          p.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes)
        | let msg := s!"rewrite_congruence '{congr.congruenceName}' in type theory " ++
            s!"'{sig.name}' has unknown evidence premise '{congr.evidenceParam}'"
          throwError "{msg}"
      checkLFRewriteCongruenceShape sig congr.congruenceName congr.relationName
        congr.targetHead congr.evidenceParam congr.argumentIndex evPremise.judgmentExpr
        ruleDecl.conclusionExpr
    else if let some thm := sig.lfJudgmentTheorems.find? (fun t =>
        t.name.eraseMacroScopes == congrName) then
      let some evBinder := thm.binders.find? (fun b =>
          b.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes)
        | let msg := s!"rewrite_congruence '{congr.congruenceName}' in type theory " ++
            s!"'{sig.name}' has unknown evidence binder '{congr.evidenceParam}'"
          throwError "{msg}"
      checkLFRewriteCongruenceShape sig congr.congruenceName congr.relationName
        congr.targetHead congr.evidenceParam congr.argumentIndex evBinder.typeExpr
        thm.judgmentExpr
    else
      let msg := s!"rewrite_congruence for unknown rule/theorem '{congr.congruenceName}' " ++
        s!"in type theory '{sig.name}'"
      throwError "{msg}"
  let mut seenTransportRules : NameSet := {}
  for tr in sig.transportRules do
    let ruleName := tr.ruleName.eraseMacroScopes
    if seenTransportRules.contains ruleName then
      let msg := "duplicate transport_rule metadata for rule " ++
        s!"'{tr.ruleName}' in type theory '{sig.name}'"
      throwError "{msg}"
    seenTransportRules := seenTransportRules.insert ruleName
    unless relationNames.contains tr.relationName.eraseMacroScopes do
      let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
        s!"references undeclared rewrite_relation '{tr.relationName}'"
      throwError "{msg}"
    let some ruleDecl := sig.rules.find? (fun r => r.name.eraseMacroScopes == ruleName)
      | throwError "transport_rule for unknown rule '{tr.ruleName}' in type theory '{sig.name}'"
    let premiseNames : NameSet := ruleDecl.premises.foldl (init := {}) fun acc p =>
      acc.insert p.name.eraseMacroScopes
    unless premiseNames.contains tr.evidencePremise.eraseMacroScopes do
      let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
        s!"has unknown evidence premise '{tr.evidencePremise}'"
      throwError "{msg}"
    unless premiseNames.contains tr.sourcePremise.eraseMacroScopes do
      let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
        s!"has unknown source premise '{tr.sourcePremise}'"
      throwError "{msg}"
    if tr.evidencePremise.eraseMacroScopes == tr.sourcePremise.eraseMacroScopes then
      let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
        s!"uses the same evidence and source premise '{tr.evidencePremise}'"
      throwError "{msg}"
    let some evPremise := ruleDecl.premises.find? (fun p =>
        p.name.eraseMacroScopes == tr.evidencePremise.eraseMacroScopes)
      | let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
          s!"has unknown evidence premise '{tr.evidencePremise}'"
        throwError "{msg}"
    match splitObjApp evPremise.judgmentExpr with
    | (.ident head, _) =>
        unless head.eraseMacroScopes == tr.relationName.eraseMacroScopes do
          let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
            s!"has evidence premise '{tr.evidencePremise}' headed by '{head}', " ++
            s!"expected rewrite_relation '{tr.relationName}'"
          throwError "{msg}"
    | _ =>
        let msg := s!"transport_rule '{tr.ruleName}' in type theory '{sig.name}' " ++
          s!"has evidence premise '{tr.evidencePremise}' not headed by a relation identifier"
        throwError "{msg}"
  let transportRuleNames : NameSet := sig.transportRules.foldl (init := {}) fun acc tr =>
    acc.insert tr.ruleName.eraseMacroScopes
  let mut seenPositions : Array (Name × Name × Nat) := #[]
  for pos in sig.transportPositions do
    let ruleName := pos.ruleName.eraseMacroScopes
    let targetHead := pos.targetHead.eraseMacroScopes
    let key := (ruleName, targetHead, pos.argumentIndex)
    if seenPositions.contains key then
      let msg := s!"duplicate transport_position metadata for rule '{pos.ruleName}' " ++
        s!"at '{pos.targetHead}[{pos.argumentIndex}]' in type theory '{sig.name}'"
      throwError "{msg}"
    seenPositions := seenPositions.push key
    unless transportRuleNames.contains ruleName do
      let msg := s!"transport_position for unknown transport_rule '{pos.ruleName}' " ++
        s!"in type theory '{sig.name}'"
      throwError "{msg}"
    unless (lfRewriteRelationParams? sig targetHead).isSome do
      let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
        s!"references unknown LF head '{pos.targetHead}'"
      throwError "{msg}"
    let some tr := sig.transportRules.find? (fun tr =>
        tr.ruleName.eraseMacroScopes == ruleName)
      | throwError "internal error: missing transport_rule '{pos.ruleName}'"
    let some ruleDecl := sig.rules.find? (fun r => r.name.eraseMacroScopes == ruleName)
      | throwError "internal error: missing transport rule declaration '{pos.ruleName}'"
    let some sourcePremise := ruleDecl.premises.find? (fun p =>
        p.name.eraseMacroScopes == tr.sourcePremise.eraseMacroScopes)
      | throwError "internal error: missing transport source premise '{tr.sourcePremise}'"
    match splitObjApp ruleDecl.conclusionExpr, splitObjApp sourcePremise.judgmentExpr with
    | (.ident conclusionHead, conclusionArgs), (.ident sourceHead, sourceArgs) =>
        unless conclusionHead.eraseMacroScopes == targetHead do
          let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
            s!"declares target head '{pos.targetHead}', but the rule conclusion is " ++
            s!"headed by '{conclusionHead}'"
          throwError "{msg}"
        unless sourceHead.eraseMacroScopes == targetHead do
          let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
            s!"declares target head '{pos.targetHead}', but source premise " ++
            s!"'{tr.sourcePremise}' is headed by '{sourceHead}'"
          throwError "{msg}"
        unless conclusionArgs.size == sourceArgs.size do
          let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
            s!"has mismatched source/conclusion arities for head '{pos.targetHead}'"
          throwError "{msg}"
        unless pos.argumentIndex < conclusionArgs.size do
          let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
            s!"uses argument index {pos.argumentIndex}, but '{pos.targetHead}' has " ++
            s!"{conclusionArgs.size} argument(s) here"
          throwError "{msg}"
        if conclusionArgs[pos.argumentIndex]! == sourceArgs[pos.argumentIndex]! then
          let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
            s!"does not change argument {pos.argumentIndex} of '{pos.targetHead}'"
          throwError "{msg}"
    | _, _ =>
        let msg := s!"transport_position '{pos.ruleName}' in type theory '{sig.name}' " ++
          "requires the transport rule conclusion and source premise to be headed applications"
        throwError "{msg}"

end InternalLean
