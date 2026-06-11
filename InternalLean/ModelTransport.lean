/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.ModelInterface

/-!
# LF model transports and workflow commands

This file contains model-interface command elaborators, generated LF model method
commands, admitted transport generation, and user-facing model workflow wrappers.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Reject generation commands under a non-root namespace.

Generated declarations are intentionally placed in deterministic top-level namespaces named by the
source theory and model structure. Running these commands under another namespace would otherwise
produce nested Lean names that differ from preview diagnostics. -/
def requireRootNamespaceForModelGeneration (commandName : String) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  unless ns == .anonymous do
    throwError "{commandName} must be run at the root namespace; current namespace is '{ns}'. \
      Close the namespace before generating model interfaces or transports."

def elabGeneratedCommandSyntaxInTheoryNamespace (theoryName : Name) (cmd : Syntax) :
  CommandElabM Unit := do
  let nsId := mkIdent theoryName
  elabCommand <| ← `(command| namespace $nsId:ident)
  elabCommand cmd
  elabCommand <| ← `(command| end $nsId:ident)

/-- Elaborate a generated command with unlimited heartbeats inside the theory namespace.

Large section-bundle structures can spend many heartbeats in Lean's structure elaborator even
though the generated code is finite and mechanical.  This mirrors a user-written
`set_option maxHeartbeats 0 in generate_model_section_bundles ...` without changing the user's
ambient options. -/
def elabGeneratedCommandSyntaxInTheoryNamespaceNoHeartbeats (theoryName : Name) (cmd : Syntax) :
  CommandElabM Unit := do
  let nsId := mkIdent theoryName
  let cmdStx : TSyntax `command := ⟨cmd⟩
  let wrapped ← `(command| set_option maxHeartbeats 0 in $cmdStx:command)
  elabCommand <| ← `(command| namespace $nsId:ident)
  elabCommand wrapped
  elabCommand <| ← `(command| end $nsId:ident)

/-- Elaborate generated command syntax inside the namespace of a generated model interface.
Definitions placed here are available through Lean dot notation on model instances. -/
def elabGeneratedCommandSyntaxInModelNamespace (theoryName structureName : Name) (cmd : Syntax) :
  CommandElabM Unit := do
  let theoryId := mkIdent theoryName
  let structureId := mkIdent structureName
  elabCommand <| ← `(command| namespace $theoryId:ident)
  elabCommand <| ← `(command| namespace $structureId:ident)
  elabCommand cmd
  elabCommand <| ← `(command| end $structureId:ident)
  elabCommand <| ← `(command| end $theoryId:ident)

/-- Elaborate generated model-namespace syntax with unlimited heartbeats. -/
def elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats (theoryName structureName : Name) (cmd :
  Syntax) : CommandElabM Unit := do
  let theoryId := mkIdent theoryName
  let structureId := mkIdent structureName
  let cmdStx : TSyntax `command := ⟨cmd⟩
  let wrapped ← `(command| set_option maxHeartbeats 0 in $cmdStx:command)
  elabCommand <| ← `(command| namespace $theoryId:ident)
  elabCommand <| ← `(command| namespace $structureId:ident)
  elabCommand wrapped
  elabCommand <| ← `(command| end $structureId:ident)
  elabCommand <| ← `(command| end $theoryId:ident)

/-- Print the generic LF model-obligation IR for a checked theory. -/
elab "#print_lf_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  logInfo m!"{LeanTypeModelGeneration.lfModelObligationSummaryString checked admittedNames}"
  if obs.isEmpty then
    logInfo m!"  no LF model obligations generated"
  else
    for o in obs do
      logInfo o.summary

/-- Check structural consistency of the generic LF model-obligation IR. -/
elab "#check_lf_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  logInfo m!"{LeanTypeModelGeneration.lfModelObligationSummaryString checked admittedNames}"

/-- Run pure negative tests for generated LF model-obligation name validation.
This is a developer regression command used by the test suite. -/
elab "#check_lf_model_obligation_validation_self_tests" : command => do
  let mk (source : LeanTypeModelGeneration.LFModelObligationSource)
      (role : LeanTypeModelGeneration.LFModelGeneratedRole) (generated : Name) :
      LeanTypeModelGeneration.LFModelObligation :=
    { name := generated, source := source, generatedRole := role, generatedName? := some generated }
  let expectFailure (obs : Array LeanTypeModelGeneration.LFModelObligation) (snippet : String) :
    CommandElabM Unit := do
    match LeanTypeModelGeneration.validateLFModelObligationArray `ContractNegative obs with
    | .ok () => throwError "expected LF model obligation validation failure containing '{snippet}'"
    | .error msg =>
        unless msg.contains snippet do
          throwError "unexpected LF model obligation validation failure: {msg}"
  expectFailure #[mk .syntaxSort .field `dup, mk .judgment .field `dup]
    "duplicate field name 'dup'"
  expectFailure #[mk .syntaxSort .field `clash, mk .judgmentTheorem .derivedDeclaration `clash]
    "field/derived-declaration name collision 'clash'"
  expectFailure #[mk .syntaxSort .field `cert,
    mk .theoremSideConditionCertificate .derivedParameter `cert]
    "derived parameter 'cert' that collides with a model field name"
  expectFailure #[mk .theoremSideConditionCertificate .derivedParameter `cert,
      mk .theoremSideConditionCertificate .derivedParameter `cert]
    "duplicate derived parameter name 'cert'"
  expectFailure #[mk .syntaxSort .field `mk]
    "invalid field name 'mk'"
  expectFailure #[mk .syntaxSort .field `Qualified.field]
    "invalid field name 'Qualified.field'"
  logInfo m!"LF model obligation validation self-tests passed"

/-- Print the stable contract for generated LF model obligations and names. -/
elab "#print_lf_model_contract " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  logInfo m!"{LeanTypeModelGeneration.lfModelContractString checked}"

/-- Print generated LF-model field dependencies computed from the obligation IR. -/
elab "#print_lf_model_field_dependencies " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let lines ← LeanTypeModelGeneration.lfModelFieldDependencySummaries checked admittedNames
  logInfo m!"LF model field dependencies for {checked.name}: {lines.size} generated field(s)"
  for line in lines do
    logInfo line

/-- Print source/provenance diagnostics for generated LF model obligations. -/
elab "#print_lf_model_provenance " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.lfModelObligationProvenanceString checked admittedNames}"

/-- Print public/minimal source/provenance diagnostics for generated LF model obligations. -/
elab "#print_public_lf_model_provenance " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.lfModelObligationProvenanceString checked admittedNames
    .publicMode}"

/-- Print a summary of fields generated by the LF-model backend. -/
elab "#print_lf_model_summary " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{LeanTypeModelGeneration.lfModelSummaryString checked admittedNames}"

/-- Print LF metadata omitted by the LF-model backend. -/
elab "#print_lf_model_omissions " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{LeanTypeModelGeneration.lfModelOmissionsString checked admittedNames}"

/-- Print checked LF definitions/theorems as consumed by the LF-model backend. -/
elab "#print_lf_model_artifacts " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let defValues := LeanTypeModelGeneration.lfDefinitionValueMap checked
  logInfo m!"LF-model checked artifacts for {checked.name}: {checked.lfObjectDefs.size} expanded \
    LF definition(s), {checked.lfJudgmentTheorems.size} available judgment theorem(s)"
  if checked.lfObjectDefs.isEmpty then
    logInfo m!"  no LF definitions expanded by model rendering"
  else
    for d in checked.lfObjectDefs do
      let typeStx ← LeanTypeModelGeneration.lfExprSyntaxInModel defValues [] d.checkedTypeExpr
      let valueStx ← LeanTypeModelGeneration.lfExprSyntaxInModel defValues [] d.checkedValue
      let typeText ← LeanTypeModelGeneration.ppTermSyntaxString typeStx
      let valueText ← LeanTypeModelGeneration.ppTermSyntaxString valueStx
      logInfo m!"  lf_def {d.name}: {typeText} := {valueText}"
  if checked.lfJudgmentTheorems.isEmpty then
    logInfo m!"  no checked judgment theorems available to model diagnostics"
  else
    for t in checked.lfJudgmentTheorems do
      let statementStx ←
        LeanTypeModelGeneration.lfExprSyntaxInModel defValues [] t.checkedJudgmentExpr
      let statementText ← LeanTypeModelGeneration.ppTermSyntaxString statementStx
      let proofHead := match t.proofHead? with
        | some h => m!", proof head {h.summary}"
        | none => m!", proof head unresolved"
      let derivationStatus := if t.derivation?.isSome then "checked derivation" else
        "opaque proof artifact"
      let replayStatus :=
        if t.checkedStructuralKernelDerivation?.isSome then
          "checked structural kernel replay artifact"
        else
          "no checked structural kernel replay artifact"
      logInfo m!"  judgment_theorem {t.name}: {statementText}{proofHead}; {derivationStatus}, \
        {replayStatus}"

/-- Print the LF-model structure generated from checked LF metadata. -/
elab "#print_lf_model_skeleton " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let structureName := theory.getId ++ `LFModel
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let cmds ← LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName
    obs
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations structureName
      obs ownerMap
  let parts ← (cmds ++ exportCmds).mapM LeanTypeModelGeneration.ppCommandSyntaxString
  logInfo m!"{String.intercalate "\n" parts.toList}"

/-- Print derived LF theorem statements over a model, computed from derived-declaration obligations.
-/
elab "#print_lf_model_derived_statements " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let lines ←
    LeanTypeModelGeneration.lfModelDerivedStatementSummaries checked structureName.getId
      admittedNames
  if lines.isEmpty then
    logInfo m!"no LF derived declaration statements generated from model obligations"
  else
    for line in lines do
      logInfo line

/-- Print derived LF theorem declarations generated by replaying checked LF derivations over a
model. -/
elab "#print_lf_model_derived_theorems " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  logInfo m!"{LeanTypeModelGeneration.lfModelDerivedTheoremSummaryString checked}"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let cmds ←
    LeanTypeModelGeneration.lfJudgmentTheoremInterpretationSyntaxes checked structureName.getId
      admittedNames
  if cmds.isEmpty then
    logInfo m!"no LF derived theorem declarations generated"
  else
    for cmd in cmds do
      logInfo m!"{← LeanTypeModelGeneration.ppCommandSyntaxString cmd}"

/-- Generate an LF-model structure from checked LF metadata. -/
elab "generate_lf_model_structure " theory:ident " as " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_lf_model_structure"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  if let some warning :=
      LeanTypeModelGeneration.lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    logWarning m!"{warning}"
  let cmds ←
    LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName.getId obs
  LeanTypeModelGeneration.addLFModelInterfaceLibrarySuggestionDenyList structureName.getId cmds.size
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName.getId obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations
      structureName.getId obs ownerMap
  for cmd in exportCmds do
    elabGeneratedCommandSyntaxInModelNamespace theory.getId structureName.getId cmd
  LeanTypeModelGeneration.addLFModelStructureFieldDocStringsFromObligations theory.getId
    structureName.getId obs ownerMap

/-- Print the strict structural-equivalence structure for an LF-model interface. -/
elab "#print_lf_model_structural_equiv " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames
  logInfo m!"{← LeanTypeModelGeneration.ppCommandSyntaxString equivCmd}"

/-- Generate the strict structural-equivalence structure for an LF-model interface. -/
elab "generate_lf_model_structural_equiv " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_lf_model_structural_equiv"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames
  elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats theory.getId structureName.getId equivCmd

/-- Check that every checked LF theorem derivation has a generated derived theorem term. -/
elab "#check_lf_model_derived_theorems " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let mut generated := 0
  let mut missing : Array Name := #[]
  for t in checked.lfJudgmentTheorems do
    match ←
      LeanTypeModelGeneration.lfJudgmentTheoremInterpretationSyntax? checked structureName.getId t
        admittedNames with
    | some _ => generated := generated + 1
    | none =>
        let (_, renderable, _) :=
          LeanTypeModelGeneration.lfJudgmentTheoremObligationStatus checked t
        if t.derivation?.isSome && renderable then
          missing := missing.push t.name
  unless missing.isEmpty do
    let names := String.intercalate ", " (missing.toList.map LeanTypeModelGeneration.nameString)
    throwError "LF model derived theorem generation for '{theory.getId}' missed checked \
      derivation(s): {names}"
  logInfo m!"LF model derived theorem generation for {checked.name}: \
    {generated}/{checked.lfJudgmentTheorems.size} theorem declaration(s) generated; no checked \
      derivation was missed"

/-- Whether an admission can be generated as an LF model-interface method. -/
def isLFModelAdmission (checked : CheckedSignature) (admittedNames : NameSet)
    (a : InternalAdmission) : Bool :=
  let tempFields :=
    LeanTypeModelGeneration.lfModelTemporaryAdmissionFieldNames checked admittedNames
  match a.kind with
  | .lfOpaque =>
      if tempFields.contains a.declName.eraseMacroScopes then
        false
      else
        match checked.lfOpaqueConsts.find? (fun c =>
          c.name.eraseMacroScopes == a.declName.eraseMacroScopes) with
        | some c => c.checkedTypeExpr?.isSome
        | none => false
  | .judgmentTheorem => LeanTypeModelGeneration.isLFJudgmentAdmission checked a
  | .syntaxDef => false

/-- Check whether a generated LF model-interface method name is available. -/
def ensureLFModelMethodNameAvailable (theoryName structureName methodName : Name) :
  CommandElabM Unit := do
  let fullName := theoryName ++ structureName ++ methodName
  if (← getEnv).contains fullName then
    throwError "cannot generate LF model method '{fullName}': a Lean declaration with that name \
      already exists"

/-- Generate one LF theorem model-interface method and attach source documentation when available.
-/
def generateLFTheoremModelMethod (theoryName structureName : Name) (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) (admittedNames : NameSet := {}) : CommandElabM Bool := do
  match ←
    LeanTypeModelGeneration.lfJudgmentTheoremInterpretationSyntax? checked structureName t
      admittedNames with
  | none => pure false
  | some cmd =>
      ensureLFModelMethodNameAvailable theoryName structureName t.name
      elabGeneratedCommandSyntaxInModelNamespace theoryName structureName cmd
      let sourceDoc? ← liftCoreM <| findInternalSourceDoc? theoryName t.name
      let doc :=
        generatedModelMethodDocString theoryName structureName t.name t.name "LF model derived \
          theorem generation" "derived model-interface method over a model" sourceDoc?
      liftCoreM <| addDocStringCore (theoryName ++ structureName ++ t.name) doc
      pure true

/-- Generate one checked LF definition model-interface method and attach source documentation when
available. -/
def generateLFObjectDefModelMethod (theoryName structureName : Name) (checked : CheckedSignature)
    (d : CheckedLFObjectDef) (admittedNames : NameSet := {}) : CommandElabM Bool := do
  match ←
    LeanTypeModelGeneration.lfObjectDefInterpretationSyntaxAs? checked structureName d.name d
      admittedNames with
  | none => pure false
  | some cmd =>
      ensureLFModelMethodNameAvailable theoryName structureName d.name
      elabGeneratedCommandSyntaxInModelNamespace theoryName structureName cmd
      let sourceDoc? ← liftCoreM <| findInternalSourceDoc? theoryName d.name
      let doc :=
        generatedModelMethodDocString theoryName structureName d.name d.name "LF model definition \
          transport" "transported LF definition as a model-interface method" sourceDoc?
      liftCoreM <| addDocStringCore (theoryName ++ structureName ++ d.name) doc
      pure true

/-- Generate one admitted LF opaque as a model-interface method whose body intentionally uses Lean
`sorry`. -/
def generateLFAdmissionModelMethod (theoryName structureName : Name) (checked : CheckedSignature)
    (admittedNames : NameSet) (a : InternalAdmission) : CommandElabM Bool := do
  unless isLFModelAdmission checked admittedNames a do
    return false
  let cmd ←
    LeanTypeModelGeneration.admittedModelInterpretationSyntax checked structureName a.declName a
  ensureLFModelMethodNameAvailable theoryName structureName a.declName
  elabGeneratedCommandSyntaxInModelNamespace theoryName structureName cmd
  let sourceDoc? ← liftCoreM <| findInternalSourceDoc? theoryName a.declName
  let doc :=
    generatedModelMethodDocString theoryName structureName a.declName a.declName "admitted LF \
      model transport" "Lean sorry-backed admitted model-interface method" sourceDoc?
  liftCoreM <| addDocStringCore (theoryName ++ structureName ++ a.declName) doc
  liftCoreM <| registerInternalAdmissionTransport {
    theoryName := theoryName
    declName := a.declName
    structureName := structureName
    generatedName := theoryName ++ structureName ++ a.declName
  }
  pure true

/-- Generate derived LF theorem declarations by replaying checked LF derivations over a model. -/
elab "generate_lf_model_derived_theorems " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_lf_model_derived_theorems"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  LeanTypeModelGeneration.addLFModelInterfaceLibrarySuggestionDenyList structureName.getId 1
  for a in admissions do
    discard <|
      generateLFAdmissionModelMethod theory.getId structureName.getId checked admittedNames a
  for t in checked.lfJudgmentTheorems do
    discard <| generateLFTheoremModelMethod theory.getId structureName.getId checked t admittedNames

/-- Preview the methods that `generate_lf_model_transports` would generate. -/
def lfModelTransportPreviewString (theoryName structureName : Name) (checked : CheckedSignature)
    (admissions : Array InternalAdmission) : CommandElabM String := do
  let mut admissionLines : Array String := #[]
  let mut defLines : Array String := #[]
  let mut theoremLines : Array String := #[]
  let mut skippedLines : Array String := #[]
  let methodLine (kind : String) (sourceName methodName : Name) (extra : String := "") :
    CommandElabM String := do
    let fullName := theoryName ++ structureName ++ methodName
    let collision := if (← getEnv).contains fullName then " [name collision]" else ""
    pure s!"  {kind} {sourceName.eraseMacroScopes} → {fullName.eraseMacroScopes}; dot: \
      M.{methodName.eraseMacroScopes}{extra}{collision}"
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let tempFields :=
    LeanTypeModelGeneration.lfModelTemporaryAdmissionFieldNames checked admittedNames
  let mut generated := 0
  let mut skipped := 0
  for a in admissions do
    if isLFModelAdmission checked admittedNames a then
      let kind := s!"admitted {a.kind.label}"
      admissionLines :=
        admissionLines.push (← methodLine kind a.declName a.declName "; Lean sorry-backed")
      generated := generated + 1
    else
      let reason :=
        if tempFields.contains a.declName.eraseMacroScopes then
          "already a temporary admitted-definition model field; no transport needed"
        else
          "not a typed LF opaque or LF judgment admission for this backend"
      skippedLines := skippedLines.push s!"  admitted {a.declName.eraseMacroScopes}: {reason}"
      skipped := skipped + 1
  for d in checked.lfObjectDefs do
    let (ok, diag?) := LeanTypeModelGeneration.lfObjectDefTransportStatus checked d
    if ok then
      defLines := defLines.push (← methodLine "lf_def" d.name d.name)
      generated := generated + 1
    else
      skippedLines :=
        skippedLines.push s!"  lf_def {d.name.eraseMacroScopes}: {(diag?).getD "not renderable"}"
      skipped := skipped + 1
  for t in checked.lfJudgmentTheorems do
    let (_, ok, diag?) := LeanTypeModelGeneration.lfJudgmentTheoremObligationStatus checked t
    if ok then
      let certs := LeanTypeModelGeneration.lfTheoremSideConditionFieldsForTheorem checked t.name
      let certText :=
        if certs.isEmpty then ""
        else s!"; certificate parameter(s): {String.intercalate ",
          " (certs.toList.map (fun c => toString c.fieldName.eraseMacroScopes))}"
      theoremLines := theoremLines.push (← methodLine "judgment_theorem" t.name t.name certText)
      generated := generated + 1
    else
      skippedLines :=
        skippedLines.push s!"  judgment_theorem {t.name.eraseMacroScopes}: \
          {(diag?).getD "not renderable"}"
      skipped := skipped + 1
  let mkSection (title : String) (xs : Array String) : Array String :=
    if xs.isEmpty then #[s!"{title}: none"] else #[s!"{title}:"] ++ xs
  let lines :=
    #[s!"LF model transports for {theoryName.eraseMacroScopes} as {structureName.eraseMacroScopes}",
      s!"summary: {generated} method(s) would be generated, {skipped} item(s) skipped",
      "methods are generated in the model-interface namespace and are available by dot notation \
        on model instances"] ++
    mkSection "admitted methods" admissionLines ++
    mkSection "checked LF definition methods" defLines ++
    mkSection "checked LF theorem methods" theoremLines ++
    mkSection "skipped items" skippedLines ++
    #[s!"next action: run `generate_model_transports {theoryName.eraseMacroScopes} for \
      {structureName.eraseMacroScopes}` after `generate_model_interface` and after checking \
        name-collision notes above"]
  pure (String.intercalate "\n" lines.toList)

/-- Print a preview of all renderable checked LF definitions and judgment theorems generated as
model-interface methods. -/
elab "#print_model_transports " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  logInfo m!"{← lfModelTransportPreviewString theory.getId structureName.getId checked admissions}"

/-- Legacy direct-LF spelling of `#print_model_transports`. -/
elab "#print_lf_model_transports " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  logInfo m!"{← lfModelTransportPreviewString theory.getId structureName.getId checked admissions}"

/-- Theorem heads syntactically mentioned in a checked LF expression. -/
partial def lfTheoremRefsInCheckedLFExpr : CheckedLFExpr → Array Name
  | .ident h => if h.kind == .lfTheorem then #[h.name.eraseMacroScopes] else #[]
  | .sort | .univ _ => #[]
  | .app f a => lfTheoremRefsInCheckedLFExpr f ++ lfTheoremRefsInCheckedLFExpr a
  | .arrow _ A B | .sigma _ A B => lfTheoremRefsInCheckedLFExpr A ++ lfTheoremRefsInCheckedLFExpr B
  | .pair a b => lfTheoremRefsInCheckedLFExpr a ++ lfTheoremRefsInCheckedLFExpr b
  | .fst e | .snd e => lfTheoremRefsInCheckedLFExpr e
  | .lam _ body => lfTheoremRefsInCheckedLFExpr body
  | .jeq lhs rhs => lfTheoremRefsInCheckedLFExpr lhs ++ lfTheoremRefsInCheckedLFExpr rhs

/-- Transitive theorem references needed by a selected theorem transport. -/
partial def lfModelTransportTheoremDependencyClosure (checked : CheckedSignature)
    (name : Name) (visited : NameSet := {}) : NameSet := Id.run do
  let name := name.eraseMacroScopes
  if visited.contains name then
    return visited
  let visited := visited.insert name
  let some t := LeanTypeModelGeneration.findCheckedLFJudgmentTheorem? checked.lfJudgmentTheorems
    name
    | return visited
  let mut refs := t.premiseTheorems.map Name.eraseMacroScopes
  match t.proofHead? with
  | some h =>
      if h.kind == .lfTheorem then
        refs := refs.push h.name.eraseMacroScopes
  | none => pure ()
  refs := refs ++ lfTheoremRefsInCheckedLFExpr t.checkedProof
  if let some derivation := t.derivation? then
    refs := refs ++ LeanTypeModelGeneration.lfTheoremRefsInDerivation derivation
  let mut out := visited
  for ref in refs do
    out := lfModelTransportTheoremDependencyClosure checked ref out
  return out

/-- Add transitive theorem dependencies to a selected transport set. -/
def expandSelectedLFModelTransportSet (checked : CheckedSignature) (selected : NameSet) : NameSet :=
  Id.run do
  let mut out := selected
  for t in checked.lfJudgmentTheorems do
    if selected.contains t.name.eraseMacroScopes then
      for dep in (lfModelTransportTheoremDependencyClosure checked t.name {}).toList do
        out := out.insert dep.eraseMacroScopes
  return out

/-- Generate selected checked/admitted LF declarations as model-interface methods. -/
def generateSelectedLFModelMethods (theoryName structureName : Name) (checked : CheckedSignature)
    (admissions : Array InternalAdmission) (selected? : Option NameSet := none) :
      CommandElabM Unit := do
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let tempFields :=
    LeanTypeModelGeneration.lfModelTemporaryAdmissionFieldNames checked admittedNames
  let selectedExpanded? := match selected? with
    | none => none
    | some selected => some (expandSelectedLFModelTransportSet checked selected)
  let wanted (n : Name) : Bool :=
    match selectedExpanded? with
    | none => true
    | some names => names.contains n.eraseMacroScopes
  LeanTypeModelGeneration.addLFModelInterfaceLibrarySuggestionDenyList structureName 1
  let mut generated : NameSet := {}
  for a in admissions do
    if wanted a.declName then
      if tempFields.contains a.declName.eraseMacroScopes then
        generated := generated.insert a.declName.eraseMacroScopes
      else if (← getEnv).contains (theoryName ++ structureName ++ a.declName) then
        generated := generated.insert a.declName.eraseMacroScopes
      else if (←
          generateLFAdmissionModelMethod theoryName structureName checked admittedNames a) then
        generated := generated.insert a.declName.eraseMacroScopes
  for d in checked.lfObjectDefs do
    if wanted d.name then
      if (← getEnv).contains (theoryName ++ structureName ++ d.name) then
        generated := generated.insert d.name.eraseMacroScopes
      else if (←
          generateLFObjectDefModelMethod theoryName structureName checked d admittedNames) then
        generated := generated.insert d.name.eraseMacroScopes
  for t in checked.lfJudgmentTheorems do
    if wanted t.name then
      if (← getEnv).contains (theoryName ++ structureName ++ t.name) then
        generated := generated.insert t.name.eraseMacroScopes
      else if (← generateLFTheoremModelMethod theoryName structureName checked t admittedNames) then
        generated := generated.insert t.name.eraseMacroScopes
  if let some selected := selected? then
    let missing := selected.toList.filter (fun n => !generated.contains n.eraseMacroScopes)
    unless missing.isEmpty do
      let names := String.intercalate ", " (missing.map (fun n => toString n.eraseMacroScopes))
      throwError "selected LF model transport(s) were not generated for type theory \
        '{theoryName}': {names}"

/-- Generate all renderable checked LF definitions and judgment theorems as model-interface methods.
-/
elab "generate_model_transports " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_transports"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  generateSelectedLFModelMethods theory.getId structureName.getId checked admissions

/-- Generate only the named checked/admitted LF declarations as model-interface methods. -/
elab "generate_model_transports \
  " theory:ident " only " decls:ident* " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_transports"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let selected : NameSet := decls.foldl (init := {}) fun acc id =>
    acc.insert id.getId.eraseMacroScopes
  generateSelectedLFModelMethods theory.getId structureName.getId checked admissions (some selected)

/-- Legacy direct-LF spelling of `generate_model_transports`. -/
elab "generate_lf_model_transports " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_lf_model_transports"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  generateSelectedLFModelMethods theory.getId structureName.getId checked admissions

/-- Legacy direct-LF spelling of selected `generate_model_transports`. -/
elab "generate_lf_model_transports \
  " theory:ident " only " decls:ident* " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_lf_model_transports"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let selected : NameSet := decls.foldl (init := {}) fun acc id =>
    acc.insert id.getId.eraseMacroScopes
  generateSelectedLFModelMethods theory.getId structureName.getId checked admissions (some selected)

/-- Docstring for a generated model transport of an admitted internal declaration. -/
def generatedAdmissionTransportDocString (theoryName sourceName generatedName structureName : Name)
    (sourceDoc? : Option String) : String :=
  let sourceDocLines :=
    match sourceDoc? with
    | some doc => ["", "Source documentation:", trimCapturedDoc doc]
    | none => ["",
      "Source documentation: missing; run `#lint_type_theory_docs` on the source theory."]
  String.intercalate "\n" <|
    [ s!"Generated declaration `{theoryName.eraseMacroScopes}.{generatedName.eraseMacroScopes}`.",
      s!"Source internal declaration: {sourceName.eraseMacroScopes}.",
      s!"Model/interface: {structureName.eraseMacroScopes}.",
      "Admission transport: the source internal declaration was admitted by `sorry`.",
      "The generated Lean body intentionally uses `sorry`, so Lean axiom tracking exposes the \
        dependency as `sorryAx`.",
      s!"Run `#lint_type_theory_sorries {theoryName.eraseMacroScopes}` to list source admissions \
        and generated admitted transports." ] ++ sourceDocLines

/-- Docstring for an admitted LF opaque generated as a model-interface method. -/
def generatedAdmissionModelMethodDocString (theoryName structureName sourceName methodName : Name)
    (sourceDoc? : Option String) : String :=
  let sourceDocLines :=
    match sourceDoc? with
    | some doc => ["", "Source documentation:", trimCapturedDoc doc]
    | none => ["",
      "Source documentation: missing; run `#lint_type_theory_docs` on the source theory."]
  String.intercalate "\n" <|
    [ s!"Generated model-interface method \
      `{theoryName.eraseMacroScopes}.{structureName.eraseMacroScopes}.\
      {methodName.eraseMacroScopes}`.",
      s!"Source internal declaration: {sourceName.eraseMacroScopes}.",
      s!"Dot notation: `M.{methodName.eraseMacroScopes}` for `M : \
        {theoryName.eraseMacroScopes}.{structureName.eraseMacroScopes}`.",
      "Admission transport: the source internal declaration was admitted by `sorry`.",
      "The generated Lean body intentionally uses `sorry`, so Lean axiom tracking exposes the \
        dependency as `sorryAx`.",
      s!"Run `#lint_type_theory_sorries {theoryName.eraseMacroScopes}` to list source admissions \
        and generated admitted transports." ] ++ sourceDocLines

/-- Find an admitted internal declaration by theory-local name. -/
def findInternalAdmission? (admissions : Array InternalAdmission) (declName : Name) :
  Option InternalAdmission :=
  admissions.find? fun a => a.declName.eraseMacroScopes == declName.eraseMacroScopes

/-- Print a concise theory/replay/model workflow status. -/
elab "#check_theory " theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | do
        if let some failed ← currentFileFailedTheoryDeclaration? theory.getId then
          throwError (failedTheoryDeclarationMessage failed)
        throwError "unknown type theory '{theory.getId}'"
  liftCoreM <| requireTheoryAnchor theory.getId
  let flatSig ← liftCoreM <| flattenSignature sig
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let transports ← liftCoreM <| getInternalAdmissionTransportsFor theory.getId
  let summary :=
    LeanTypeModelGeneration.theoryWorkflowSummaryString flatSig checked admissions.size
      transports.size
  logInfo m!"{summary}"

/-- Print user-facing model obligations for the LF workflow backend. -/
elab "#print_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.modelObligationsUXString checked admittedNames}"

/-- Print public/minimal model obligations for the LF workflow backend. -/
elab "#print_public_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.modelObligationsUXString checked admittedNames .publicMode}"

/-- Print user-facing source/provenance diagnostics for model obligations. -/
elab "#print_model_provenance " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.lfModelObligationProvenanceString checked admittedNames}"

/-- Print public/minimal source/provenance diagnostics for model obligations. -/
elab "#print_public_model_provenance " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.lfModelObligationProvenanceString checked admittedNames
    .publicMode}"

/-- Print user-facing section grouping for generated LF model interfaces. -/
elab "#print_model_sections " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.modelSectionsUXString checked admittedNames}"

/-- Print public/minimal section grouping for generated LF model interfaces. -/
elab "#print_public_model_sections " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  logInfo m!"{← LeanTypeModelGeneration.modelSectionsUXString checked admittedNames .publicMode}"

/-- Print a fillable template for one theory-local model-section bundle record. -/
elab "#print_model_section_template " theory:ident sectionName:ident " as " bundleName:ident :
  command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let template ←
    LeanTypeModelGeneration.modelSectionTemplateString theory.getId sectionName.getId
      bundleName.getId checked admittedNames
  logInfo m!"{template}"

/-- Print a public/minimal fillable template for one theory-local model-section bundle record. -/
elab "#print_public_model_section_template \
  " theory:ident sectionName:ident " as " bundleName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let template ←
    LeanTypeModelGeneration.modelSectionTemplateString theory.getId sectionName.getId
      bundleName.getId checked admittedNames .publicMode
  logInfo m!"{template}"

/-- Check model obligations for the LF workflow backend. -/
elab "#check_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  logInfo m!"model obligations for {theory.getId} check for the selected workflow backend \
    ({LeanTypeModelGeneration.uxModelBackendLabel})"

/-- Check public/minimal model obligations for the LF workflow backend. -/
elab "#check_public_model_obligations " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames .publicMode
  logInfo m!"public model obligations for {theory.getId} check for the selected workflow backend \
    ({LeanTypeModelGeneration.uxModelBackendLabel})"

/-- Print the model interface generated by the LF workflow backend. -/
elab "#print_model_interface " theory:ident " as " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  let cmds ←
    LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName.getId obs
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName.getId obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations
      structureName.getId obs ownerMap
  let parts ← (cmds ++ exportCmds).mapM LeanTypeModelGeneration.ppCommandSyntaxString
  let guide ←
    LeanTypeModelGeneration.lfModelInterfaceGuideString theory.getId structureName.getId checked
      admittedNames
  logInfo m!"{guide}\n\n{String.intercalate "\n" parts.toList}"

/-- Print the public/minimal model interface generated by the LF workflow backend. -/
elab "#print_public_model_interface " theory:ident " as " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames .publicMode
  let cmds ←
    LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName.getId obs
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName.getId obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations
      structureName.getId obs ownerMap
  let parts ← (cmds ++ exportCmds).mapM LeanTypeModelGeneration.ppCommandSyntaxString
  let guide ←
    LeanTypeModelGeneration.lfModelInterfaceGuideString theory.getId structureName.getId checked
      admittedNames .publicMode
  logInfo m!"{guide}\n\n{String.intercalate "\n" parts.toList}"

/-- Print the optional strict structural-equivalence structure for a model interface. -/
elab "#print_model_structural_equiv " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames
  logInfo m!"{← LeanTypeModelGeneration.ppCommandSyntaxString equivCmd}"

/-- Print the optional public/minimal strict structural-equivalence structure. -/
elab "#print_public_model_structural_equiv \
  " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames .publicMode
  logInfo m!"{← LeanTypeModelGeneration.ppCommandSyntaxString equivCmd}"

/-- Generate the optional strict structural-equivalence structure for a model interface. -/
elab "generate_model_structural_equiv " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_structural_equiv"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames
  elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats theory.getId structureName.getId equivCmd

/-- Generate the optional public/minimal strict structural-equivalence structure. -/
elab "generate_public_model_structural_equiv \
  " theory:ident " for " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_public_model_structural_equiv"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let equivCmd ←
    LeanTypeModelGeneration.lfModelStructuralEquivCommandSyntax checked structureName.getId
      admittedNames .publicMode
  elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats theory.getId structureName.getId equivCmd

/-- Generate a model interface using the LF workflow backend. -/
elab "generate_model_interface " theory:ident " as " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_interface"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  if let some warning :=
      LeanTypeModelGeneration.lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    logWarning m!"{warning}"
  let cmds ←
    LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName.getId obs
  LeanTypeModelGeneration.addLFModelInterfaceLibrarySuggestionDenyList structureName.getId cmds.size
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName.getId obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations
      structureName.getId obs ownerMap
  for cmd in exportCmds do
    elabGeneratedCommandSyntaxInModelNamespace theory.getId structureName.getId cmd
  LeanTypeModelGeneration.addLFModelStructureFieldDocStringsFromObligations theory.getId
    structureName.getId obs ownerMap

/-- Generate a public/minimal model interface using the LF workflow backend. -/
elab "generate_public_model_interface " theory:ident " as " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_public_model_interface"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let obs ← LeanTypeModelGeneration.validateLFModelObligations checked admittedNames .publicMode
  if let some warning :=
      LeanTypeModelGeneration.lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    logWarning m!"{warning}"
  let cmds ←
    LeanTypeModelGeneration.lfModelStructureSyntaxesFromObligations checked structureName.getId obs
  LeanTypeModelGeneration.addLFModelInterfaceLibrarySuggestionDenyList structureName.getId cmds.size
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd
  let ownerMap :=
    LeanTypeModelGeneration.lfModelStructureFieldOwnerMapFromObligations structureName.getId obs
  let exportCmds ←
    LeanTypeModelGeneration.lfModelInheritedProjectionExportSyntaxesFromObligations
      structureName.getId obs ownerMap
  for cmd in exportCmds do
    elabGeneratedCommandSyntaxInModelNamespace theory.getId structureName.getId cmd
  LeanTypeModelGeneration.addLFModelStructureFieldDocStringsFromObligations theory.getId
    structureName.getId obs ownerMap

/-- Generate a sectioned model interface from theory-local `model_section` metadata. -/
elab "generate_model_section_interface " theory:ident " as " structureName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_section_interface"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  LeanTypeModelGeneration.warnTemporaryAdmissionFieldsIfAny checked admittedNames
  let (cmds, generatedNames) ←
    LeanTypeModelGeneration.lfModelSectionStructureSyntaxes checked structureName.getId
      admittedNames
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList generatedNames
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd

/-- Generate a public/minimal sectioned model interface from theory-local `model_section` metadata.
-/
elab "generate_public_model_section_interface " theory:ident " as " structureName:ident :
  command => do
  requireRootNamespaceForModelGeneration "generate_public_model_section_interface"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  LeanTypeModelGeneration.warnTemporaryAdmissionFieldsIfAny checked admittedNames .publicMode
  let (cmds, generatedNames) ←
    LeanTypeModelGeneration.lfModelSectionStructureSyntaxes checked structureName.getId
      admittedNames .publicMode
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList generatedNames
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd

/-- Generate a fast sectioned model-interface wrapper over an existing flat interface.

The generated type extends the flat target, so Lean provides the inherited `toFlat` adapter
projection without elaborating a duplicate large sectioned telescope. Use
`generate_model_section_interface` for a standalone section-owned interface. -/
elab "generate_model_sections \
  " theory:ident " as " structureName:ident " adapting " flatName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_sections"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList #[structureName.getId]
  let cmd ←
    LeanTypeModelGeneration.lfModelSectionWrapperCommandSyntax structureName.getId flatName.getId
  elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd

/-- Generate a fast public/minimal sectioned model-interface wrapper over an existing flat
interface. -/
elab "generate_public_model_sections \
  " theory:ident " as " structureName:ident " adapting " flatName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_public_model_sections"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  discard <| LeanTypeModelGeneration.validateLFModelObligations checked admittedNames .publicMode
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList #[structureName.getId]
  let cmd ←
    LeanTypeModelGeneration.lfModelSectionWrapperCommandSyntax structureName.getId flatName.getId
  elabGeneratedCommandSyntaxInTheoryNamespace theory.getId cmd

/-- Print true model-section bundle structures plus an adapter to an existing flat interface. -/
elab "#print_model_section_bundles \
  " theory:ident " as " bundleName:ident " adapting " flatName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let (cmds, adapterCmd, _) ←
    LeanTypeModelGeneration.lfModelSectionBundleSyntaxes checked bundleName.getId flatName.getId
      admittedNames
  let parts ← (cmds.push adapterCmd).mapM LeanTypeModelGeneration.ppCommandSyntaxString
  let guide ←
    LeanTypeModelGeneration.modelSectionBundleGuideString checked bundleName.getId flatName.getId
      admittedNames
  logInfo m!"{guide}\n\n{String.intercalate "\n" parts.toList}"

/-- Print true public/minimal model-section bundle structures plus an adapter to an existing flat
interface. -/
elab "#print_public_model_section_bundles \
  " theory:ident " as " bundleName:ident " adapting " flatName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let (cmds, adapterCmd, _) ←
    LeanTypeModelGeneration.lfModelSectionBundleSyntaxes checked bundleName.getId flatName.getId
      admittedNames .publicMode
  let parts ← (cmds.push adapterCmd).mapM LeanTypeModelGeneration.ppCommandSyntaxString
  let guide ←
    LeanTypeModelGeneration.modelSectionBundleGuideString checked bundleName.getId flatName.getId
      admittedNames .publicMode
  logInfo m!"{guide}\n\n{String.intercalate "\n" parts.toList}"

/-- Generate true model-section bundle structures plus an adapter to an existing flat interface. -/
elab "generate_model_section_bundles \
  " theory:ident " as " bundleName:ident " adapting " flatName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_model_section_bundles"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  LeanTypeModelGeneration.warnTemporaryAdmissionFieldsIfAny checked admittedNames
  let (cmds, adapterCmd, generatedNames) ←
    LeanTypeModelGeneration.lfModelSectionBundleSyntaxes checked bundleName.getId flatName.getId
      admittedNames
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList generatedNames
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespaceNoHeartbeats theory.getId cmd
  elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats theory.getId bundleName.getId adapterCmd

/-- Generate true public/minimal model-section bundle structures plus an adapter to an existing flat
interface. -/
elab "generate_public_model_section_bundles \
  " theory:ident " as " bundleName:ident " adapting " flatName:ident : command => do
  requireRootNamespaceForModelGeneration "generate_public_model_section_bundles"
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  LeanTypeModelGeneration.warnTemporaryAdmissionFieldsIfAny checked admittedNames .publicMode
  let (cmds, adapterCmd, generatedNames) ←
    LeanTypeModelGeneration.lfModelSectionBundleSyntaxes checked bundleName.getId flatName.getId
      admittedNames .publicMode
  LeanTypeModelGeneration.addLFModelInterfaceNamesLibrarySuggestionDenyList generatedNames
  for cmd in cmds do
    elabGeneratedCommandSyntaxInTheoryNamespaceNoHeartbeats theory.getId cmd
  elabGeneratedCommandSyntaxInModelNamespaceNoHeartbeats theory.getId bundleName.getId adapterCmd

/-- Print a fillable LF model template with grouped holes and source documentation hints. -/
elab "#print_model_template " theory:ident " as " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let template ←
    LeanTypeModelGeneration.modelTemplateString theory.getId structureName.getId checked
      admittedNames
  logInfo m!"{template}"

/-- Print a public/minimal fillable LF model template. -/
elab "#print_public_model_template " theory:ident " as " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let template ←
    LeanTypeModelGeneration.modelTemplateString theory.getId structureName.getId checked
      admittedNames .publicMode
  logInfo m!"{template}"

/-- Print user-facing transport readiness for generated model declarations. -/
elab "#print_model_transport_status " theory:ident " for " structureName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  let status :=
    LeanTypeModelGeneration.modelTransportStatusString theory.getId structureName.getId checked
      admissions
  logInfo m!"{status}"

/-- Namespace where a generated model-transport command should be elaborated. -/
inductive ModelTransportTargetNamespace where
  | theory
  | modelInterface
  deriving Inhabited, BEq, Repr

/-- Syntax and naming metadata for one generated model transport. -/
structure ModelTransportCommand where
  cmd : Syntax
  outputName : Name
  admitted : Bool
  targetNamespace : ModelTransportTargetNamespace := .theory
  deriving Inhabited

/-- Full Lean declaration name for a generated model transport. -/
def modelTransportFullName (theoryName structureName : Name) (transport : ModelTransportCommand) :
  Name :=
  match transport.targetNamespace with
  | .theory => theoryName ++ transport.outputName
  | .modelInterface => theoryName ++ structureName ++ transport.outputName

/-- Build the selected UX-level model transport command for a declaration. -/
def modelTransportCommandSyntax? (theoryName declName structureName : Name) :
  CommandElabM (Option ModelTransportCommand) := do
  let some checked ← liftCoreM <| getCheckedTheory? theoryName
    | throwError "no checked artifact stored for type theory '{theoryName}'"
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theoryName
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let tempFields :=
    LeanTypeModelGeneration.lfModelTemporaryAdmissionFieldNames checked admittedNames
  if let some a := findInternalAdmission? admissions declName then
    if tempFields.contains a.declName.eraseMacroScopes then
      throwError "admitted internal declaration '{declName}' is already a temporary \
        admitted-definition field in model interface '{structureName}'; no transport command is \
          needed"
    else if isLFModelAdmission checked admittedNames a then
      let cmd ←
        LeanTypeModelGeneration.admittedModelInterpretationSyntax checked structureName a.declName a
      return some { cmd, outputName := a.declName, admitted := true, targetNamespace :=
        .modelInterface }
    else
      throwError "admitted internal declaration '{declName}' is not available for LF \
        model-interface transport"
  if let some d := checked.lfObjectDefs.find? (fun d =>
    d.name.eraseMacroScopes == declName.eraseMacroScopes) then
    match ←
      LeanTypeModelGeneration.lfObjectDefInterpretationSyntaxAs? checked structureName d.name d
        admittedNames with
    | some cmd => return some { cmd, outputName := d.name, admitted := false, targetNamespace :=
      .modelInterface }
    | none =>
        let (_, diag?) := LeanTypeModelGeneration.lfObjectDefTransportStatus checked d
        throwError "internal declaration '{declName}' has no renderable LF-model transport for \
          interface '{structureName}': {(diag?).getD "not renderable"}. Run \
            `#print_model_transport_status {theoryName} for {structureName}` and \
              `#print_lf_model_omissions {theoryName}` for details."
  if let some t := checked.lfJudgmentTheorems.find? (fun t =>
    t.name.eraseMacroScopes == declName.eraseMacroScopes) then
    match ←
      LeanTypeModelGeneration.lfJudgmentTheoremInterpretationSyntaxAs? checked structureName t.name
        t admittedNames with
    | some cmd => return some { cmd, outputName := t.name, admitted := false, targetNamespace :=
      .modelInterface }
    | none =>
      throwError "internal declaration '{declName}' has no renderable LF-model transport for \
        interface '{structureName}'. Run `#print_model_transport_status {theoryName} for \
          {structureName}` and `#print_lf_model_omissions {theoryName}` for details."
  return none

/-- Check that a generated model-transport declaration name is still available. -/
def ensureModelTransportNameAvailable (theoryName structureName : Name) (transport :
  ModelTransportCommand) : CommandElabM Unit := do
  let fullName := modelTransportFullName theoryName structureName transport
  if (← getEnv).contains fullName then
    throwError "cannot generate model transport '{fullName}': a Lean declaration with that name \
      already exists (possibly an existing generated transport or internal declaration anchor)"

/-- Elaborate a generated model transport in its target namespace. -/
def elabModelTransportCommand (theoryName structureName : Name) (transport :
  ModelTransportCommand) : CommandElabM Unit := do
  match transport.targetNamespace with
  | .theory => elabGeneratedCommandSyntaxInTheoryNamespace theoryName transport.cmd
  | .modelInterface =>
    elabGeneratedCommandSyntaxInModelNamespace theoryName structureName transport.cmd

/-- Print the generated transport declaration for one internal declaration. -/
elab "#print_model_transport_signature " theory:ident declName:ident " for " structureName:ident :
  command => do
  match ← modelTransportCommandSyntax? theory.getId declName.getId structureName.getId with
  | some transport =>
      let note := if transport.admitted then
        "\n-- admission note: generated body uses Lean `sorry`/`sorryAx`." else ""
      let namespaceNote := match transport.targetNamespace with
        | .theory => ""
        | .modelInterface =>
          s!"\n-- generated in namespace {theory.getId}.{structureName.getId}; use dot notation \
            such as M.{transport.outputName}."
      let commandText ← LeanTypeModelGeneration.ppCommandSyntaxString transport.cmd
      logInfo m!"{commandText}{namespaceNote}{note}"
  | none =>
      throwError "no checked or admitted internal declaration '{declName.getId}' is available for \
        model transport in type theory '{theory.getId}'"

/-- Generate the model transport declaration for one internal declaration. -/
elab "generate_model_transport " theory:ident declName:ident " for " structureName:ident :
  command => do
  requireRootNamespaceForModelGeneration "generate_model_transport"
  match ← modelTransportCommandSyntax? theory.getId declName.getId structureName.getId with
  | some transport =>
      ensureModelTransportNameAvailable theory.getId structureName.getId transport
      elabModelTransportCommand theory.getId structureName.getId transport
      let sourceDoc? ← liftCoreM <| findInternalSourceDoc? theory.getId declName.getId
      if transport.targetNamespace == .theory then
        liftCoreM <| registerSemanticTransport theory.getId declName.getId transport.outputName
      if transport.admitted then
        let doc :=
          match transport.targetNamespace with
          | .theory =>
              generatedAdmissionTransportDocString theory.getId declName.getId transport.outputName
                structureName.getId sourceDoc?
          | .modelInterface =>
              generatedAdmissionModelMethodDocString theory.getId structureName.getId
                declName.getId transport.outputName sourceDoc?
        liftCoreM



















          <| addDocStringCore (modelTransportFullName theory.getId structureName.getId transport)
            doc
        liftCoreM <| registerInternalAdmissionTransport {
          theoryName := theory.getId
          declName := declName.getId
          structureName := structureName.getId
          generatedName := modelTransportFullName theory.getId structureName.getId transport
        }
      else
        let doc :=
          match transport.targetNamespace with
          | .theory =>
              generatedDeclarationDocString theory.getId transport.outputName "model workflow \
                transport" s!"transported declaration for source {declName.getId}" sourceDoc?
          | .modelInterface =>
              generatedModelMethodDocString theory.getId structureName.getId transport.outputName
                declName.getId "model workflow transport"
                s!"transported model-interface method for source {declName.getId}" sourceDoc?
        liftCoreM



















          <| addDocStringCore (modelTransportFullName theory.getId structureName.getId transport)
            doc
  | none =>
      throwError "no checked or admitted internal declaration '{declName.getId}' is available for \
        model transport in type theory '{theory.getId}'"

end InternalLean
