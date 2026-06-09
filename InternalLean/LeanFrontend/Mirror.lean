/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.InternalTactic
public meta import Lean.Elab.Term

/-!
# Experimental Lean mirror checker backend

This module contains an opt-in prototype that translates a checked InternalLean LF signature and
candidate LF terms to hidden Lean declarations under `T.LFMirror`, then asks Lean's kernel to check
the translated expression.  The mirror remains a prototype: registration commands still run the
ordinary LF checker, and compare mode can run the current LF checker after a mirror acceptance.
-/

@[expose] public meta section

open Lean Elab Command Term Meta

namespace InternalLean

register_option internalLean.mirrorBackend.compareWithLF : Bool := {
  defValue := false
  descr := "after a successful experimental Lean mirror check, also run the ordinary LF checker"
}

/-- Convert an object-level universe to the corresponding Lean sort for the mirror backend. -/
def lfMirrorLeanSortOfLevel (u : LevelExpr) : Expr :=
  -- Prototype: collapse object-level universe expressions to Lean `Type`.  This keeps the first
  -- mirror backend fragment focused on structural checking.  Universe-accurate mirroring belongs
  -- in a later soundness pass.
  let _ := u
  mkSort (Level.succ .zero)

/-- Local LF-to-Lean mirror translation environment. -/
abbrev LFMirrorLocalMap := NameMap Expr

/-- Translate one LF expression to the experimental Lean mirror expression. -/
partial def lfMirrorExpr (theoryName : Name) (locals : LFMirrorLocalMap) : ObjExpr → MetaM Expr
  | .ident n => do
      if let some e := locals.find? n.eraseMacroScopes then
        pure e
      else
        pure (mkConst (lfMirrorDeclName theoryName n))
  | .sort => pure (lfMirrorLeanSortOfLevel .zero)
  | .univ u => pure (lfMirrorLeanSortOfLevel u)
  | .app f a => do
      let fExpr ← lfMirrorExpr theoryName locals f
      let fType ← whnf (← inferType fExpr)
      match fType with
      | .forallE _ domain _ _ =>
          pure (mkApp fExpr (← lfMirrorExprWithLeanExpected theoryName locals domain a))
      | _ =>
          pure (mkApp fExpr (← lfMirrorExpr theoryName locals a))
  | .arrow binder? A B | .funArrow binder? A B => do
      let AExpr ← lfMirrorExpr theoryName locals A
      let binderName := (binder?.getD `_arg).eraseMacroScopes
      withLocalDecl binderName .default AExpr fun x => do
        let locals :=
          match binder? with
          | some n => locals.insert n.eraseMacroScopes x
          | none => locals
        let BExpr ← lfMirrorExpr theoryName locals B
        mkForallFVars #[x] BExpr
  | .sigma binder? A B => do
      let (AExpr, betaExpr) ← lfMirrorSigmaParts theoryName locals binder? A B
      pure (mkApp2 (mkConst ``Sigma [Level.zero, Level.zero]) AExpr betaExpr)
  | .pair a b => do
      -- Without an expected type, infer a nondependent Sigma package from component mirror types.
      -- Dependent pairs should use `lfMirrorTermWithExpected`, which has the LF Sigma type.
      let aExpr ← lfMirrorExpr theoryName locals a
      let bExpr ← lfMirrorExpr theoryName locals b
      let AExpr ← inferType aExpr
      let BExpr ← inferType bExpr
      let betaExpr ← withLocalDecl `_fst .default AExpr fun x => mkLambdaFVars #[x] BExpr
      pure (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) AExpr betaExpr aExpr bExpr)
  | .fst e => do
      let eExpr ← lfMirrorExpr theoryName locals e
      let eType ← whnf (← inferType eExpr)
      let some (AExpr, betaExpr) := lfMirrorSigmaType? eType
        | throwError "cannot translate LF fst; mirror term does not have Sigma type:\n  {eType}"
      pure (mkApp3 (mkConst ``Sigma.fst [Level.zero, Level.zero]) AExpr betaExpr eExpr)
  | .snd e => do
      let eExpr ← lfMirrorExpr theoryName locals e
      let eType ← whnf (← inferType eExpr)
      let some (AExpr, betaExpr) := lfMirrorSigmaType? eType
        | throwError "cannot translate LF snd; mirror term does not have Sigma type:\n  {eType}"
      pure (mkApp3 (mkConst ``Sigma.snd [Level.zero, Level.zero]) AExpr betaExpr eExpr)
  | .lam xs _body => do
      throwError "cannot translate LF lambda with binders {xs.toList} to the Lean mirror without \
        an expected function type"
  | .jeq lhs rhs => do
      -- Judgmental equality expressions are mirror-encoded as an opaque type family only in later
      -- phases.  Current mirror checks should use declared judgment heads instead.
      throwError "Lean mirror backend does not yet support raw judgmental equality expression \
        '{ObjExpr.toString (.jeq lhs rhs)}'"
where
  /-- Translate an LF term using an expected Lean mirror type. -/
  lfMirrorExprWithLeanExpected (theoryName : Name) (locals : LFMirrorLocalMap)
      (expected : Expr) : ObjExpr → MetaM Expr
    | .lam xs body => do
        let rec go (i : Nat) (expected : Expr) (locals : LFMirrorLocalMap) : MetaM Expr := do
          if _h : i < xs.size then
            match ← whnf expected with
            | .forallE _ domain range _ =>
                let sourceName := xs[i]!.eraseMacroScopes
                withLocalDecl sourceName .default domain fun x => do
                  let locals := locals.insert sourceName x
                  let bodyExpr ← go (i + 1) (range.instantiate1 x) locals
                  mkLambdaFVars #[x] bodyExpr
            | expected => throwError "Lean mirror expected a function type while translating \
                lambda, got\n  {expected}"
          else
            lfMirrorExprWithLeanExpected theoryName locals expected body
        go 0 expected locals
    | .pair a b => do
        let expected ← whnf expected
        let some (AExpr, betaExpr) := lfMirrorSigmaType? expected
          | throwError "Lean mirror expected a Sigma type while translating pair, got\n  \
              {expected}"
        let aExpr ← lfMirrorExprWithLeanExpected theoryName locals AExpr a
        let bExpected ← whnf (mkApp betaExpr aExpr)
        let bExpr ← lfMirrorExprWithLeanExpected theoryName locals bExpected b
        pure (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) AExpr betaExpr aExpr bExpr)
    | e => do
        let eExpr ← lfMirrorExpr theoryName locals e
        let actual ← inferType eExpr
        unless ← isDefEq actual expected do
          throwError "Lean mirror translated LF term with type\n  {actual}\nexpected\n  {expected}"
        pure eExpr

  /-- Translate the components of an LF Sigma type to Lean mirror `Sigma` components. -/
  lfMirrorSigmaParts (theoryName : Name) (locals : LFMirrorLocalMap) (binder? : Option Name)
      (A B : ObjExpr) : MetaM (Expr × Expr) := do
    let AExpr ← lfMirrorExpr theoryName locals A
    let binderName := (binder?.getD `_fst).eraseMacroScopes
    withLocalDecl binderName .default AExpr fun x => do
      let locals :=
        match binder? with
        | some n => locals.insert n.eraseMacroScopes x
        | none => locals
      let BExpr ← lfMirrorExpr theoryName locals B
      let beta ← mkLambdaFVars #[x] BExpr
      pure (AExpr, beta)

  /-- Recognize a Lean mirror Sigma type. -/
  lfMirrorSigmaType? (e : Expr) : Option (Expr × Expr) :=
    match e.getAppFnArgs with
    | (n, #[AExpr, betaExpr]) =>
        if n == ``Sigma then some (AExpr, betaExpr) else none
    | _ => none

/-- Translate an LF term to the Lean mirror while using an expected LF type when needed. -/
partial def lfMirrorTermWithExpected (theoryName : Name) (locals : LFMirrorLocalMap)
    (expected : ObjExpr) : ObjExpr → MetaM Expr
  | .lam xs body => do
      let rec go (i : Nat) (expected : ObjExpr) (locals : LFMirrorLocalMap) : MetaM Expr := do
        if _h : i < xs.size then
          match expected with
          | .arrow binder? A B | .funArrow binder? A B => do
              let AExpr ← lfMirrorExpr theoryName locals A
              let sourceName := xs[i]!.eraseMacroScopes
              withLocalDecl sourceName .default AExpr fun x => do
                let binderName := (binder?.getD sourceName).eraseMacroScopes
                let locals := locals.insert sourceName x |>.insert binderName x
                let nextExpected :=
                  match binder? with
                  | some n => substSingleLFParam n (.ident sourceName) B
                  | none => B
                let bodyExpr ← go (i + 1) nextExpected locals
                mkLambdaFVars #[x] bodyExpr
          | _ => throwError "Lean mirror expected a function type while translating lambda, got \
              '{ObjExpr.toString expected}'"
        else
          lfMirrorTermWithExpected theoryName locals expected body
      go 0 expected locals
  | .pair a b => do
      match expected with
      | .sigma binder? A B => do
          let (AExpr, betaExpr) ← lfMirrorExpr.lfMirrorSigmaParts theoryName locals binder? A B
          let aExpr ← lfMirrorTermWithExpected theoryName locals A a
          let bExpected :=
            match binder? with
            | some n => substSingleLFParam n (eraseObjExprScopes a) B
            | none => B
          let bExpr ← lfMirrorTermWithExpected theoryName locals bExpected b
          pure (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) AExpr betaExpr aExpr bExpr)
      | _ => throwError "Lean mirror expected a Sigma type while translating pair, got \
          '{ObjExpr.toString expected}'"
  | e => do
      let expectedLean ← lfMirrorExpr theoryName locals expected
      let eExpr ← lfMirrorExpr theoryName locals e
      let actual ← inferType eExpr
      unless ← isDefEq actual expectedLean do
        throwError "Lean mirror translated LF term with type\n  {actual}\nexpected\n  \
          {expectedLean}"
      pure eExpr

/-- Build a Lean mirror function type from LF parameters and a result expression. -/
def lfMirrorForallType (theoryName : Name) (params : Array HLBinding)
    (result : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) (fvars : Array Expr) : MetaM Expr := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExpr theoryName locals p.typeExpr
      withLocalDecl p.name.eraseMacroScopes (lfQuoteBinderInfoOfVisibility p.visibility) ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x) (fvars.push x)
    else
      mkForallFVars fvars (← result locals)
  go 0 {} #[]

/-- Build a closed Lean mirror lambda from LF parameters and a body expression. -/
def lfMirrorLambdaValue (theoryName : Name) (params : Array HLBinding)
    (body : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) (fvars : Array Expr) : MetaM Expr := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExpr theoryName locals p.typeExpr
      withLocalDecl p.name.eraseMacroScopes (lfQuoteBinderInfoOfVisibility p.visibility) ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x) (fvars.push x)
    else
      mkLambdaFVars fvars (← body locals)
  go 0 {} #[]

/-- Run a mirror-meta computation under local LF parameters. -/
def withLFMirrorLocals {α : Type} (theoryName : Name) (params : Array HLBinding)
    (k : LFMirrorLocalMap → TermElabM α) : TermElabM α := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) : TermElabM α := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExpr theoryName locals p.typeExpr
      withLocalDecl p.name.eraseMacroScopes (lfQuoteBinderInfoOfVisibility p.visibility) ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x)
    else
      k locals
  go 0 {}

/-- Add one experimental Lean mirror axiom if it is not already present. -/
def addLFMirrorAxiomIfMissing (declName : Name) (type : Expr) : CommandElabM Unit := do
  unless (← getEnv).contains declName do
    liftCoreM do
      addAndCompile (Declaration.axiomDecl {
        name := declName
        levelParams := []
        type := type
        isUnsafe := false })

/-- Add one experimental Lean mirror definition if it is not already present. -/
def addLFMirrorDefinitionIfMissing (declName : Name) (type value : Expr) : CommandElabM Unit := do
  unless (← getEnv).contains declName do
    liftCoreM do
      let defVal : DefinitionVal := {
        name := declName
        levelParams := []
        type := type
        value := value
        hints := ReducibilityHints.abbrev
        safety := DefinitionSafety.safe }
      addDecl (Declaration.defnDecl defVal)

/-- Ensure that experimental Lean mirror declarations exist for the currently checked signature. -/
def ensureLFMirrorForTheory (theoryName : Name) : CommandElabM Unit := do
  let some checkedHL ← liftCoreM <| getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  for d in checkedHL.syntaxSorts do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.syntaxAbbrevs do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params fun locals => do
      inferType (← lfMirrorExpr theoryName locals d.value)
    let value ← liftTermElabM <| lfMirrorLambdaValue theoryName d.params
      (fun locals => lfMirrorExpr theoryName locals d.value)
    addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) type value
  for d in checkedHL.syntaxDefs do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
    match d.value? with
    | some value =>
        let value ← liftTermElabM <| lfMirrorLambdaValue theoryName d.params
          (fun locals => lfMirrorExpr theoryName locals value)
        addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) type value
    | none =>
        addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.judgments do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (mkSort (Level.succ .zero)))
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.judgmentAbbrevs do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params fun locals => do
      inferType (← lfMirrorExpr theoryName locals d.value)
    let value ← liftTermElabM <| lfMirrorLambdaValue theoryName d.params
      (fun locals => lfMirrorExpr theoryName locals d.value)
    addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) type value
  for d in checkedHL.lfOpaqueConsts do
    if let some typeExpr := d.typeExpr? then
      let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
        (fun locals => lfMirrorExpr theoryName locals typeExpr)
      addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.rules do
    let type ← liftTermElabM do
      let premiseParams := d.premises.map fun p =>
        ({ name := p.name, typeExpr := p.judgmentExpr, visibility := .explicit } : HLBinding)
      lfMirrorForallType theoryName (d.params ++ premiseParams)
        (fun locals => lfMirrorExpr theoryName locals d.conclusionExpr)
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.lfObjectDefs do
    let type ← liftTermElabM <| lfMirrorExpr theoryName {} d.typeExpr
    let value ← liftTermElabM <| lfMirrorTermWithExpected theoryName {} d.typeExpr d.value
    addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) type value
  for d in checkedHL.lfJudgmentTheorems do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.binders
      (fun locals => lfMirrorExpr theoryName locals d.judgmentExpr)
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type

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
  if sigmaEta then
    some <| String.intercalate "\n" [
      "Recognized mirror/LF conversion gap: the translated Lean term uses Sigma eta.",
      "The current LF conversion policy does not identify `⟨fst p, snd p⟩` with `p`."]
  else if funEta then
    some <| String.intercalate "\n" [
      "Recognized mirror/LF conversion gap: the translated Lean term uses function eta.",
      "The current LF conversion policy does not identify `fun x => f x` with `f`."]
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
      if let some hint := lfMirrorComparePitfallHint? typeExpr valueExpr then
        throwError "Lean mirror accepted a term in type theory '{theoryName}',\nbut the \
          ordinary LF checker rejected it.\n\n{hint}"
      else
        let msg :=
          m!"Lean mirror accepted a term in type theory '{theoryName}',\nbut the ordinary LF \
            checker rejected it.\n\nFirst LF path:\n{exceptionMessageData firstEx}\n\nSecond LF \
              path:\n{exceptionMessageData secondEx}"
        throwError msg

/-- Check one LF value against an LF type using only the experimental Lean mirror backend. -/
def checkWithLFMirrorOnly (theoryName : Name) (params : Array HLBinding)
    (typeExpr valueExpr : ObjExpr) : CommandElabM Unit := do
  ensureLFMirrorForTheory theoryName
  liftTermElabM do
    withLFMirrorLocals theoryName params fun locals => do
      let typeLean ← lfMirrorExpr theoryName locals typeExpr
      let valueLean ← lfMirrorTermWithExpected theoryName locals typeExpr valueExpr
      let actual ← inferType valueLean
      unless ← isDefEq actual typeLean do
        let msg :=
          m!"Lean mirror checker inferred\n  {actual}\nfor translated value, expected\n  {typeLean}"
        throwError msg

/-- Check one LF value using the mirror and, optionally, the ordinary LF checker. -/
def checkWithLFMirror (theoryName : Name) (params : Array HLBinding) (typeExpr valueExpr : ObjExpr)
    (compareWithLF : Bool := false) : CommandElabM Unit := do
  checkWithLFMirrorOnly theoryName params typeExpr valueExpr
  let optionCompare ← liftCoreM <| getBoolOption `internalLean.mirrorBackend.compareWithLF
  if compareWithLF || optionCompare then
    liftCoreM <| checkWithLFForMirrorCompare theoryName params typeExpr valueExpr

syntax (name := checkLFMirror)
  "#check_lf_mirror " ident " : " ttExpr " := " ttExpr : command
syntax (name := compareLFMirror)
  "#compare_lf_mirror " ident " : " ttExpr " := " ttExpr : command

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
      checkWithLFMirror target.theoryName #[] typeExpr valueExpr
      elabInternalDefCheckedExpr doc? declName declName.getId #[] typeExpr valueExpr
      addInternalDefExprNavigationInfo declName.getId #[] typeStx valueStx

elab_rules (kind := internalMirrorDefBinder) : command
  | `($[$doc?:docComment]? internal_mirror def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $valueStx:ttExpr) => do
      let target ← resolveInternalDefTarget declName.getId
      let params ← binders.mapM elabHLBinding
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror target.theoryName params typeExpr valueExpr
      elabInternalDefCheckedWithBindersExpr doc? declName declName.getId #[] params typeExpr
        valueExpr
      addInternalDefExprNavigationInfo declName.getId binders typeStx valueStx

end InternalLean
