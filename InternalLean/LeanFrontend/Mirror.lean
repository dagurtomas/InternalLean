/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.InternalTactic

/-!
# Experimental Lean mirror checker backend commands

The mirror core translates checked InternalLean LF signatures and candidate LF terms to hidden Lean
declarations under `T.LFMirror`. This command module exposes opt-in diagnostics and compare-mode
entry points while registration remains under the direct-LF checker unless a mirror fast-path option
is explicitly enabled.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Check one staged LF object definition with the ordinary LF checker without registering it. -/
def checkLFObjectDefForMirrorCompare (cache : CompiledLFCheckCache) (d : LFObjectDefDecl) :
    CoreM Unit := do
  let knownTypes := cache.knownLFDefTypes
  let rawBlock : HLTheoryBlock := { lfObjectDefs := #[d] }
  let flatSigWithRaw := cache.checkedHL.appendBlock rawBlock
  let implicitLookup := mkImplicitCallableLookupContextFromCache cache rawBlock
  let dForRegistry ←
    elaborateImplicitAppsInLFObjectDefWithLookup implicitLookup flatSigWithRaw knownTypes d
  let flatSigWithNew := cache.checkedHL.appendBlock { lfObjectDefs := #[dForRegistry] }
  let typeExpr ←
    expandSyntaxAbbrevsInExpr flatSigWithNew "lf_def" dForRegistry.name "type" {}
      (lfAbbrevExpansionFuel flatSigWithNew) dForRegistry.typeExpr
  let value ←
    expandSyntaxAbbrevsInExpr flatSigWithNew "lf_def" dForRegistry.name "value" {}
      (lfAbbrevExpansionFuel flatSigWithNew) dForRegistry.value
  let dForCheck := {
    dForRegistry with
    name := dForRegistry.name.eraseMacroScopes
    typeExpr := typeExpr
    value := value }
  discard <| checkOneLFObjectDefArtifactWithCache cache dForCheck

/-- Check one staged LF judgment theorem with the ordinary LF checker without registering it. -/
def checkLFJudgmentTheoremForMirrorCompare (cache : CompiledLFCheckCache)
    (t : LFJudgmentTheoremDecl) : CoreM Unit := do
  let knownTypes := cache.knownLFDefTypes
  let rawBlock : HLTheoryBlock := { lfJudgmentTheorems := #[t] }
  let flatSigWithRaw := cache.checkedHL.appendBlock rawBlock
  let implicitLookup := mkImplicitCallableLookupContextFromCache cache rawBlock
  let tForRegistry ←
    elaborateImplicitAppsInLFJudgmentTheoremWithLookup implicitLookup flatSigWithRaw knownTypes t
  let flatSigWithNew := cache.checkedHL.appendBlock { lfJudgmentTheorems := #[tForRegistry] }
  let binders ← expandSyntaxAbbrevsInBindings flatSigWithNew "judgment_theorem"
    tForRegistry.name tForRegistry.binders
  let locals := binders.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
  let judgmentExpr ←
    expandSyntaxAbbrevsInExpr flatSigWithNew "judgment_theorem" tForRegistry.name "statement"
      locals (lfAbbrevExpansionFuel flatSigWithNew) tForRegistry.judgmentExpr
  let proof ←
    expandSyntaxAbbrevsInExpr flatSigWithNew "judgment_theorem" tForRegistry.name "proof"
      locals (lfAbbrevExpansionFuel flatSigWithNew) tForRegistry.proof
  let tForCheck := {
    tForRegistry with
    name := tForRegistry.name.eraseMacroScopes
    binders := binders
    judgmentExpr := judgmentExpr
    proof := proof }
  let checkedTheoremRaw ← checkOneLFJudgmentTheoremArtifactWithCache cache tForCheck
  discard <| validateIncrementalLFTheoremKernelReplayWithCache cache checkedTheoremRaw

/-- Strip lambda binders from a mirror-compare candidate and rename them to LF telescope names. -/
partial def stripMirrorCompareLambdaBinders? (params : Array HLBinding) :
    ObjExpr → Option ObjExpr :=
  let rec go (i : Nat) (value : ObjExpr) : Option ObjExpr :=
    if h : i < params.size then
      match value with
      | .lam xs body =>
          if hxs : 0 < xs.size then
            let sourceName := xs[0]!.eraseMacroScopes
            let targetName := params[i].name.eraseMacroScopes
            let rest := xs.extract 1 xs.size
            let body := if rest.isEmpty then body else .lam rest body
            go (i + 1) (substSingleLFParam sourceName (.ident targetName) body)
          else
            none
      | _ => none
    else
      some value
  go 0

/-- Check a closed function-to-judgment candidate as a binder-style LF theorem, if possible. -/
def checkLFArrowTheoremForMirrorCompare? (cache : CompiledLFCheckCache) (compareName : Name)
    (typeExpr valueExpr : ObjExpr) : Option (CoreM Unit) :=
  let (binders, judgmentExpr) := splitObjectTelescope typeExpr
  if binders.isEmpty then
    none
  else
    match stripMirrorCompareLambdaBinders? binders valueExpr with
    | none => none
    | some proof =>
        let theoremDecl : LFJudgmentTheoremDecl := {
          name := compareName
          binders := binders
          judgmentExpr := judgmentExpr
          proof := proof }
        some (checkLFJudgmentTheoremForMirrorCompare cache theoremDecl)

/-- Detect an LF expression shape that Lean accepts by Sigma eta. -/
partial def lfMirrorContainsSigmaEtaShape : ObjExpr → Bool
  | .pair (.fst p) (.snd q) => lfExprAlphaEq p q
  | .app f a => lfMirrorContainsSigmaEtaShape f || lfMirrorContainsSigmaEtaShape a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      lfMirrorContainsSigmaEtaShape A || lfMirrorContainsSigmaEtaShape B
  | .pair a b => lfMirrorContainsSigmaEtaShape a || lfMirrorContainsSigmaEtaShape b
  | .fst e | .snd e | .lam _ e => lfMirrorContainsSigmaEtaShape e
  | .jeq lhs rhs => lfMirrorContainsSigmaEtaShape lhs || lfMirrorContainsSigmaEtaShape rhs
  | .ident _ | .sort | .univ _ => false

/-- Detect an LF expression shape that Lean accepts by function eta. -/
partial def lfMirrorContainsFunctionEtaShape : ObjExpr → Bool
  | .lam xs (.app f (.ident x)) =>
      xs.size == 1 && xs[0]!.eraseMacroScopes == x.eraseMacroScopes &&
        !internalObjExprMentionsName x.eraseMacroScopes f
  | .app f a => lfMirrorContainsFunctionEtaShape f || lfMirrorContainsFunctionEtaShape a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      lfMirrorContainsFunctionEtaShape A || lfMirrorContainsFunctionEtaShape B
  | .pair a b => lfMirrorContainsFunctionEtaShape a || lfMirrorContainsFunctionEtaShape b
  | .fst e | .snd e | .lam _ e => lfMirrorContainsFunctionEtaShape e
  | .jeq lhs rhs => lfMirrorContainsFunctionEtaShape lhs || lfMirrorContainsFunctionEtaShape rhs
  | .ident _ | .sort | .univ _ => false

/-- Human-oriented note for known mirror/LF conversion-policy gaps. -/
def lfMirrorComparePitfallHint? (typeExpr valueExpr : ObjExpr) : Option String :=
  let sigmaEta := lfMirrorContainsSigmaEtaShape typeExpr || lfMirrorContainsSigmaEtaShape valueExpr
  let funEta :=
    lfMirrorContainsFunctionEtaShape typeExpr || lfMirrorContainsFunctionEtaShape valueExpr
  if sigmaEta || funEta then
    some <| String.intercalate "\n" [
      "The translated Lean term uses structural eta, which is part of the ordinary LF",
      "conversion policy. Any LF rejection here is therefore a different LF/mirror shape",
      "or classification mismatch rather than an eta-conversion mismatch."]
  else
    none

/-- Check one LF value against one LF type using the ordinary LF checker, without registration. -/
def checkWithLFForMirrorCompare (theoryName : Name) (params : Array HLBinding)
    (typeExpr valueExpr : ObjExpr) : CoreM Unit := do
  let some checked ← getCheckedTheory? theoryName
    | throwError "no checked artifact stored for type theory '{theoryName}'"
  let cacheLookup ← getOrBuildCompiledLFCheckCache theoryName checked
  let cache := cacheLookup.cache
  let compareName := `_internalLeanMirrorCompare
  let theoremDecl : LFJudgmentTheoremDecl := {
    name := compareName
    binders := params
    judgmentExpr := typeExpr
    proof := valueExpr }
  let objectDef : LFObjectDefDecl := {
    name := compareName
    typeExpr := mkInternalDefFunctionType params typeExpr
    value := mkInternalDefLambda params valueExpr }
  let checkObject := checkLFObjectDefForMirrorCompare cache objectDef
  let checkTheorem := checkLFJudgmentTheoremForMirrorCompare cache theoremDecl
  try
    if params.isEmpty then
      checkObject
    else
      checkTheorem
  catch firstEx =>
    try
      if params.isEmpty then
        checkTheorem
      else
        checkObject
    catch secondEx =>
      match checkLFArrowTheoremForMirrorCompare? cache compareName typeExpr valueExpr with
      | some checkArrowTheorem =>
          try
            checkArrowTheorem
          catch thirdEx =>
            let etaNote :=
              match lfMirrorComparePitfallHint? typeExpr valueExpr with
              | some hint => m!"\n\nNote:\n{hint}"
              | none => m!""
            let msg :=
              m!"Lean mirror accepted a term in type theory '{theoryName}',\nbut the \
                ordinary LF checker rejected it.{etaNote}\n\nFirst LF path:\n" ++
              m!"{exceptionMessageData firstEx}\n\nSecond LF path:\n" ++
              m!"{exceptionMessageData secondEx}\n\nTelescope LF path:\n" ++
              m!"{exceptionMessageData thirdEx}"
            throwError msg
      | none =>
          let etaNote :=
            match lfMirrorComparePitfallHint? typeExpr valueExpr with
            | some hint => m!"\n\nNote:\n{hint}"
            | none => m!""
          let msg :=
            m!"Lean mirror accepted a term in type theory '{theoryName}',\nbut the \
              ordinary LF checker rejected it.{etaNote}\n\nFirst LF path:\n" ++
            m!"{exceptionMessageData firstEx}\n\nSecond LF path:\n" ++
            m!"{exceptionMessageData secondEx}"
          throwError msg

/-- Check one LF value using the mirror and, optionally, the ordinary LF checker. -/
def checkWithLFMirror (theoryName : Name) (params : Array HLBinding) (typeExpr valueExpr : ObjExpr)
    (compareWithLF : Bool := false) : CommandElabM Unit := do
  liftCoreM <| checkWithLFMirrorOnly theoryName params typeExpr valueExpr
  let optionCompare ← liftCoreM <| getBoolOption `internalLean.mirrorBackend.compareWithLF
  if compareWithLF || optionCompare then
    liftCoreM <| checkWithLFForMirrorCompare theoryName params typeExpr valueExpr

/-- Mirror-check body-bearing declarations in an already checked theory and report coverage. -/
def compareLFMirrorTheory (theoryName : Name) : CommandElabM Unit := do
  let some checkedHL ← liftCoreM <| getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  liftCoreM <| ensureLFMirrorForTheory theoryName
  for d in checkedHL.syntaxAbbrevs do
    liftCoreM <| checkLFMirrorTypeLikeBodyInSignature checkedHL "syntax_abbrev" d.name
      d.params d.value
  for d in checkedHL.judgmentAbbrevs do
    liftCoreM <| checkLFMirrorTypeLikeBodyInSignature checkedHL "judgment_abbrev" d.name
      d.params d.value
  for d in checkedHL.syntaxDefs do
    if let some value := d.value? then
      liftCoreM <| checkLFMirrorSyntaxDefBodyInSignature checkedHL d value
  for d in checkedHL.lfObjectDefs do
    liftCoreM <| checkLFMirrorLFObjectDefBodyInSignature checkedHL d
  let checkedSyntaxDefs := checkedSyntaxDefBodyCount checkedHL
  let admittedSyntaxDefs := checkedHL.syntaxDefs.size - checkedSyntaxDefs
  let typedOpaques := typedLFOpaqueCount checkedHL
  let untypedOpaques := checkedHL.lfOpaqueConsts.size - typedOpaques
  logInfo m!"Lean mirror theory compare accepted '{theoryName}'.\n\nRepresented declarations:\n  \
    syntax_sort: {checkedHL.syntaxSorts.size}\n  judgment: {checkedHL.judgments.size}\n  \
    typed lf_opaque: {typedOpaques}\n  untyped/admitted lf_opaque: {untypedOpaques}\n  \
    rule axiom: {checkedHL.rules.size}\n  judgment theorem axiom: \
      {checkedHL.lfJudgmentTheorems.size}\n\nChecked mirror bodies:\n  syntax_abbrev: \
      {checkedHL.syntaxAbbrevs.size}\n  judgment_abbrev: {checkedHL.judgmentAbbrevs.size}\n  \
    checked syntax_def: {checkedSyntaxDefs}\n  admitted syntax_def: {admittedSyntaxDefs}\n  \
    lf_def: {checkedHL.lfObjectDefs.size}"

/-- Mirror-check every checked high-level theory currently registered in the environment. -/
def compareAllLFMirrorTheories : CommandElabM Unit := do
  let sigs ← liftCoreM getCheckedHLSignatures
  let mut count := 0
  for (theoryName, _) in sigs.toList do
    compareLFMirrorTheory theoryName
    count := count + 1
  logInfo m!"Lean mirror theory compare accepted {count} checked type theor(ies)."

syntax (name := checkLFMirror)
  "#check_lf_mirror " ident " : " ttExpr " := " ttExpr : command
syntax (name := compareLFMirror)
  "#compare_lf_mirror " ident " : " ttExpr " := " ttExpr : command
syntax (name := compareLFMirrorTheoryCmd)
  "#compare_lf_mirror_theory " ident : command
syntax (name := compareAllLFMirrorTheoriesCmd)
  "#compare_all_lf_mirror_theories" : command

elab_rules : command
  | `(#check_lf_mirror $theory:ident : $typeStx:ttExpr := $valueStx:ttExpr) => do
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror theory.getId #[] typeExpr valueExpr
      logInfo m!"Lean mirror checker accepted term in type theory '{theory.getId}'"
  | `(#compare_lf_mirror $theory:ident : $typeStx:ttExpr := $valueStx:ttExpr) => do
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror theory.getId #[] typeExpr valueExpr (compareWithLF := true)
      logInfo m!"Lean mirror and LF checker accepted term in type theory '{theory.getId}'"
  | `(#compare_lf_mirror_theory $theory:ident) => do
      compareLFMirrorTheory theory.getId
  | `(#compare_all_lf_mirror_theories) => do
      compareAllLFMirrorTheories

syntax (name := internalMirrorDef)
  docComment ? "internal_mirror " "def " ident " : " ttExpr " := " ttExpr : command
syntax (name := internalMirrorDefBinder)
  docComment ? "internal_mirror " "def " ident ttBinder+ " : " ttExpr " := " ttExpr : command

elab_rules (kind := internalMirrorDef) : command
  | `($[$doc?:docComment]? internal_mirror def $declName:ident : $typeStx:ttExpr :=
      $valueStx:ttExpr) => do
      let target ← resolveInternalDefTarget declName.getId
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror target.theoryName #[] typeExpr valueExpr (compareWithLF := true)
      elabInternalDefCheckedExpr doc? declName declName.getId #[] typeExpr valueExpr
      addInternalDefExprNavigationInfo declName.getId #[] typeStx valueStx

elab_rules (kind := internalMirrorDefBinder) : command
  | `($[$doc?:docComment]? internal_mirror def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $valueStx:ttExpr) => do
      let target ← resolveInternalDefTarget declName.getId
      let params ← binders.mapM elabHLBinding
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror target.theoryName params typeExpr valueExpr (compareWithLF := true)
      elabInternalDefCheckedWithBindersExpr doc? declName declName.getId #[] params typeExpr
        valueExpr
      addInternalDefExprNavigationInfo declName.getId binders typeStx valueStx

end InternalLean
