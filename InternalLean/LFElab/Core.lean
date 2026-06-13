/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LeanFrontend.MirrorCore

/-!
# LF elaboration and checking for user-declared type theories

This file contains frontend expansion, direct-LF metadata checking, LF-definition unfolding,
and replay lowering.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

register_option internalLean.profileLFCheckPhases : Bool := {
  defValue := false
  descr := "log coarse phase timings for LF object-definition checking"
}

register_option internalLean.conversion.profile : Bool := {
  defValue := false
  descr := "log InternalLean LF/object conversion profile entries"
}

register_option internalLean.conversion.traceFallbacks : Bool := {
  defValue := false
  descr := "log InternalLean LF/object conversion entries that run full unfolding fallback"
}

register_option internalLean.conversion.slowThresholdMs : Nat := {
  defValue := 50
  descr := "elapsed-time threshold for InternalLean conversion profile entries"
}

register_option internalLean.conversion.sizeGrowthThreshold : Nat := {
  defValue := 10
  descr := "normalized-size growth threshold for InternalLean conversion profile entries"
}

initialize registerTraceClass `InternalLean.conversion
initialize registerTraceClass `InternalLean.conversion.unfold

/-- Time an LF elaboration/checking phase when `internalLean.profileLFCheckPhases` is enabled. -/
def profileLFCheckPhase (label : MessageData) (x : CoreM α) : CoreM α := do
  if (← getBoolOption `internalLean.profileLFCheckPhases) then
    let start ← IO.monoMsNow
    let result ← x
    let stop ← IO.monoMsNow
    logInfo m!"LF check phase {label}: {stop - start}ms"
    return result
  else
    x

/-- Run a speculative core action, restoring the environment and message/info state if it fails.

The Lean mirror backend is a best-effort optimization/comparison path.  Failed mirror declaration
construction should leave no partial generated declarations or kernel diagnostics when the ordinary
LF checker can still be used as the authoritative fallback. -/
def withRestoredCoreStateOnError (x : CoreM α) : CoreM α := do
  let savedState ← Core.saveState
  try
    x
  catch ex =>
    Core.SavedState.restore savedState
    throw ex

/-- Substitute object-expression parameters by object-expression arguments in a macro template. -/
partial def substObjectMacroParams (subst : NameMap ObjExpr) : ObjExpr → ObjExpr
  | .ident n =>
      match subst.find? n.eraseMacroScopes with
      | some e => e
      | none => .ident n
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (substObjectMacroParams subst f) (substObjectMacroParams subst a)
  | .arrow x A B =>
      let A := substObjectMacroParams subst A
      let subst :=
        match x with
        | some x => subst.erase x.eraseMacroScopes
        | none => subst
      .arrow x A (substObjectMacroParams subst B)
  | .funArrow x A B =>
      let A := substObjectMacroParams subst A
      let subst :=
        match x with
        | some x => subst.erase x.eraseMacroScopes
        | none => subst
      .funArrow x A (substObjectMacroParams subst B)
  | .sigma x A B =>
      let A := substObjectMacroParams subst A
      let subst :=
        match x with
        | some x => subst.erase x.eraseMacroScopes
        | none => subst
      .sigma x A (substObjectMacroParams subst B)
  | .pair a b => .pair (substObjectMacroParams subst a) (substObjectMacroParams subst b)
  | .fst e => .fst (substObjectMacroParams subst e)
  | .snd e => .snd (substObjectMacroParams subst e)
  | .lam xs body =>
      let subst := xs.foldl (fun subst x => subst.erase x.eraseMacroScopes) subst
      .lam xs (substObjectMacroParams subst body)
  | .jeq lhs rhs => .jeq (substObjectMacroParams subst lhs) (substObjectMacroParams subst rhs)

/-- Split an object application into its head and spine. -/
partial def splitObjApp : ObjExpr → ObjExpr × Array ObjExpr
  | .app f a =>
      let (h, args) := splitObjApp f
      (h, args.push a)
  | e => (e, #[])

/-- Rebuild an object application from a head and spine. -/
def mkObjApp (head : ObjExpr) (args : Array ObjExpr) : ObjExpr :=
  args.foldl (fun f a => .app f a) head

/-- Find the latest macro for a name in a flattened signature. -/
def findObjectMacro? (sig : HLSignature) (n : Name) : Option ObjectMacro := Id.run do
  let mut out := none
  for mac in sig.macros do
    if sameObjectName mac.name n then
      out := some mac
  return out

/-- Expand theory-local object macros in an object expression.

This is an ergonomic frontend pass only: macro heads have no trusted semantics and the
expanded expression is what the direct-LF checker sees. Expansion is deliberately
first-order and positional in this first version. -/
partial def expandObjectMacrosInExpr (sig : HLSignature) (e : ObjExpr) : CoreM ObjExpr := do
  let rec go (e : ObjExpr) : CoreM ObjExpr := do
    match e with
    | .ident _ | .sort | .univ _ => pure e
    | .arrow x A B => return .arrow x (← go A) (← go B)
    | .funArrow x A B => return .funArrow x (← go A) (← go B)
    | .sigma x A B => return .sigma x (← go A) (← go B)
    | .pair a b => return .pair (← go a) (← go b)
    | .fst e => return .fst (← go e)
    | .snd e => return .snd (← go e)
    | .lam xs body => return .lam xs (← go body)
    | .jeq lhs rhs => return .jeq (← go lhs) (← go rhs)
    | .app .. =>
        let (head, args) := splitObjApp e
        let head ← go head
        let args ← args.mapM go
        match head with
        | .ident n =>
            match findObjectMacro? sig n with
            | some mac =>
                if args.size < mac.params.size then
                  pure (mkObjApp head args)
                else
                  let used := args[:mac.params.size]
                  let rest := args[mac.params.size:]
                  let subst := Id.run do
                    let mut m : NameMap ObjExpr := {}
                    for param in mac.params, arg in used do
                      m := m.insert param.eraseMacroScopes arg
                    return m
                  let expanded := substObjectMacroParams subst mac.template
                  go (mkObjApp expanded rest)
            | none => pure (mkObjApp head args)
        | _ => pure (mkObjApp head args)
  go e

/-- Expand theory-local object macros in a binder. -/
def expandObjectMacrosInBinding (sig : HLSignature) (b : HLBinding) : CoreM HLBinding := do
  return { b with typeExpr := (← expandObjectMacrosInExpr sig b.typeExpr) }

/-- Named checkpoint for source-level surface function notation.

Today this preserves `→` as the structural/function-family arrow. -/
def expandSurfaceFunctionsInSignature (sig : HLSignature) : CoreM HLSignature :=
  pure sig

/-- Return whether a name is already used directly in a high-level signature. -/
def HLSignature.containsName (sig : HLSignature) (n : Name) : Bool :=
  sig.syntaxSorts.any (fun d => d.name == n) || sig.syntaxAbbrevs.any (fun d => d.name == n) ||
    sig.syntaxDefs.any (fun d => d.name == n) ||
    sig.judgmentAbbrevs.any (fun d => d.name == n) ||
    sig.contextZones.any (fun d => d.name == n) || sig.binderClasses.any (fun d => d.name == n) ||
    sig.judgments.any (fun d => d.name == n) || sig.rules.any (fun d => d.name == n) ||
    sig.sideConditionSolvers.any (fun d => d.name == n) ||
    sig.conversionPlugins.any (fun d => d.name == n) ||
    sig.lfOpaqueConsts.any (fun d => d.name == n) ||
    sig.lfObjectDefs.any (fun d => d.name == n) || sig.lfJudgmentTheorems.any (fun d => d.name == n)

/-- One source declaration contributing to a flattened theory. -/
structure FlattenContribution where
  /-- Declaration-local name after macro-scope erasure. -/
  name : Name
  /-- Human-readable declaration category. -/
  kind : String
  /-- Source theory that directly declared the item. -/
  sourceTheory : Name
  /-- One root-to-source parent path witnessing how the item was inherited. -/
  path : Array Name
  deriving Inhabited, Repr

/-- State for parent-DAG flattening. -/
structure FlattenState where
  /-- Source theories already contributed to the flattened signature. -/
  visited : NameSet := {}
  /-- Named declarations already contributed, used only for conflict diagnostics. -/
  contributions : Array FlattenContribution := #[]
  /-- Accumulated flattened signature. -/
  flat : HLSignature

/-- Render a parent path for composition diagnostics. -/
def flattenParentPathString (path : Array Name) : String :=
  String.intercalate " -> " (path.toList.map (toString ·.eraseMacroScopes))

/-- Empty flattened signature with the requested final name. -/
def emptyFlattenedSignature (name : Name) : HLSignature := {
  name := name.eraseMacroScopes
  parents := #[] }

/-- Append one theory's own direct declarations and metadata to an accumulated flattened result. -/
def appendDirectSignatureContribution (flat source : HLSignature) : HLSignature := {
  flat with
  levelParams := flat.levelParams ++ source.levelParams
  syntaxSorts := flat.syntaxSorts ++ source.syntaxSorts
  syntaxAbbrevs := flat.syntaxAbbrevs ++ source.syntaxAbbrevs
  syntaxDefs := flat.syntaxDefs ++ source.syntaxDefs
  judgmentAbbrevs := flat.judgmentAbbrevs ++ source.judgmentAbbrevs
  syntaxSortRoles := flat.syntaxSortRoles ++ source.syntaxSortRoles
  contextZones := flat.contextZones ++ source.contextZones
  binderClasses := flat.binderClasses ++ source.binderClasses
  judgments := flat.judgments ++ source.judgments
  judgmentRoles := flat.judgmentRoles ++ source.judgmentRoles
  rules := flat.rules ++ source.rules
  ruleRoles := flat.ruleRoles ++ source.ruleRoles
  rewriteRelations := flat.rewriteRelations ++ source.rewriteRelations
  rewriteSymmetries := flat.rewriteSymmetries ++ source.rewriteSymmetries
  rewriteCongruences := flat.rewriteCongruences ++ source.rewriteCongruences
  transportRules := flat.transportRules ++ source.transportRules
  transportPositions := flat.transportPositions ++ source.transportPositions
  sideConditionSolvers := flat.sideConditionSolvers ++ source.sideConditionSolvers
  conversionPlugins := flat.conversionPlugins ++ source.conversionPlugins
  levelNormalizerProfiles := flat.levelNormalizerProfiles ++ source.levelNormalizerProfiles
  lfOpaqueConsts := flat.lfOpaqueConsts ++ source.lfOpaqueConsts
  modelVisibilities := flat.modelVisibilities ++ source.modelVisibilities
  modelSections := flat.modelSections ++ source.modelSections
  modelSectionMemberships := flat.modelSectionMemberships ++ source.modelSectionMemberships
  lfObjectDefs := flat.lfObjectDefs ++ source.lfObjectDefs
  lfJudgmentTheorems := flat.lfJudgmentTheorems ++ source.lfJudgmentTheorems
  macros := flat.macros ++ source.macros
  roles := flat.roles ++ source.roles }

/-- Record one named contribution, rejecting independent declarations with the same local name. -/
def recordFlattenContribution (rootName sourceName : Name) (path : Array Name)
    (kind : String) (rawName : Name) (state : FlattenState) : CoreM FlattenState := do
  let n := rawName.eraseMacroScopes
  let sourceName := sourceName.eraseMacroScopes
  let path := path.map Name.eraseMacroScopes
  let isLevelParam := kind == "universe level parameter"
  match state.contributions.find? (fun old =>
      old.name == n && (old.kind == "universe level parameter") == isLevelParam) with
  | none =>
      pure { state with
        contributions := state.contributions.push {
          name := n
          kind := kind
          sourceTheory := sourceName
          path := path } }
  | some old =>
      if old.sourceTheory == sourceName then
        throwError "duplicate {kind} declaration '{n}' in flattened type theory \
          '{rootName.eraseMacroScopes}'"
      else
        throwError "conflicting inherited declaration '{n}' in type theory \
          '{rootName.eraseMacroScopes}'\nfrom parent path {flattenParentPathString old.path} and \
          parent path {flattenParentPathString path}\nexisting declaration is {old.kind} from \
          '{old.sourceTheory}', new declaration is {kind} from '{sourceName}'"

/-- Record all directly named declarations of one source theory for flattening diagnostics. -/
def recordDirectSignatureContributions (rootName : Name) (source : HLSignature)
    (path : Array Name) (state : FlattenState) : CoreM FlattenState := do
  let mut state := state
  for u in source.levelParams do
    state ← recordFlattenContribution rootName source.name path "universe level parameter" u state
  for d in source.syntaxSorts do
    state ← recordFlattenContribution rootName source.name path "syntax-sort" d.name state
  for d in source.syntaxAbbrevs do
    state ← recordFlattenContribution rootName source.name path "syntax abbreviation" d.name state
  for d in source.syntaxDefs do
    state ← recordFlattenContribution rootName source.name path "syntax definition" d.name state
  for d in source.judgmentAbbrevs do
    state ← recordFlattenContribution rootName source.name path "judgment abbreviation" d.name state
  for d in source.contextZones do
    state ← recordFlattenContribution rootName source.name path "context-zone" d.name state
  for d in source.binderClasses do
    state ← recordFlattenContribution rootName source.name path "binder class" d.name state
  for d in source.judgments do
    state ← recordFlattenContribution rootName source.name path "judgment" d.name state
  for d in source.rules do
    state ← recordFlattenContribution rootName source.name path "rule" d.name state
  for d in source.sideConditionSolvers do
    state ← recordFlattenContribution rootName source.name path "side-condition solver" d.name state
  for d in source.conversionPlugins do
    state ← recordFlattenContribution rootName source.name path "conversion plugin" d.name state
  for d in source.lfOpaqueConsts do
    state ← recordFlattenContribution rootName source.name path "LF opaque constant" d.name state
  for d in source.lfObjectDefs do
    state ← recordFlattenContribution rootName source.name path "LF object definition" d.name state
  for d in source.lfJudgmentTheorems do
    state ← recordFlattenContribution rootName source.name path "LF judgment theorem" d.name state
  pure state

/-- Visit a theory in deterministic left-to-right parent post-order. -/
partial def flattenSignatureVisit (rootName : Name) (sig : HLSignature) (path : Array Name)
    (active : NameSet) (state : FlattenState) : CoreM FlattenState := do
  let sigName := sig.name.eraseMacroScopes
  if active.contains sigName then
    throwError "cyclic type-theory extension involving '{sigName}'"
  if state.visited.contains sigName then
    return state
  let active := active.insert sigName
  let mut state := state
  for parentName in sig.parents do
    let parentName := parentName.eraseMacroScopes
    let some parent ← getTheory? parentName
      | throwError "unknown parent type theory '{parentName}' for '{rootName.eraseMacroScopes}'"
    state ← flattenSignatureVisit rootName parent (path.push parentName) active state
  state ← recordDirectSignatureContributions rootName sig path state
  pure {
    state with
    visited := state.visited.insert sigName
    flat := appendDirectSignatureContribution state.flat sig }

/-- Flatten a signature's parent DAG before its own declarations.

Each source theory contributes at most once, so ordinary diamonds inherit a shared ancestor only
once. Independent declarations with the same local name remain conflicts. -/
partial def flattenSignature (sig : HLSignature) (seen : NameSet := {}) : CoreM HLSignature := do
  let initial : FlattenState := {
    visited := seen
    flat := emptyFlattenedSignature sig.name }
  let state ← flattenSignatureVisit sig.name sig #[sig.name.eraseMacroScopes] {} initial
  pure state.flat

/-- Visit the parent DAG and report whether a source theory is reachable through two paths. -/
partial def parentDagSharedVisit (rootName : Name) (sig : HLSignature) (active visited : NameSet) :
    CoreM (Bool × NameSet) := do
  let sigName := sig.name.eraseMacroScopes
  if active.contains sigName then
    throwError "cyclic type-theory extension involving '{sigName}'"
  if visited.contains sigName then
    return (true, visited)
  let active := active.insert sigName
  let mut visited := visited.insert sigName
  let mut shared := false
  for parentName in sig.parents do
    let parentName := parentName.eraseMacroScopes
    let some parent ← getTheory? parentName
      | throwError "unknown parent type theory '{parentName}' for '{rootName.eraseMacroScopes}'"
    let (parentShared, visited') ← parentDagSharedVisit rootName parent active visited
    shared := shared || parentShared
    visited := visited'
  return (shared, visited)

/-- Whether a signature's parent DAG has a shared ancestor requiring full-path registration. -/
def parentDagHasSharedAncestor (sig : HLSignature) : CoreM Bool := do
  let mut visited : NameSet := {}
  let mut shared := false
  for parentName in sig.parents do
    let parentName := parentName.eraseMacroScopes
    let some parent ← getTheory? parentName
      | throwError "unknown parent type theory '{parentName}' for '{sig.name.eraseMacroScopes}'"
    let (parentShared, visited') ← parentDagSharedVisit sig.name parent {} visited
    shared := shared || parentShared
    visited := visited'
  pure shared

/-- Check that model-interface visibility annotations are unique and refer to known declarations. -/
def checkModelVisibilityMetadataInSignature (sig : HLSignature) : CoreM Unit := do
  let mut seen : NameSet := {}
  for v in sig.modelVisibilities do
    let n := v.declName.eraseMacroScopes
    if seen.contains n then
      throwError "duplicate model visibility annotation for '{n}' in type theory '{sig.name}'"
    seen := seen.insert n
    unless sig.containsName n do
      throwError "model visibility annotation refers to unknown declaration '{n}' in type theory \
        '{sig.name}'"

/-- All directly declared names in a high-level signature. -/
def HLSignature.nameSet (sig : HLSignature) : NameSet := Id.run do
  let mut out : NameSet := {}
  for d in sig.syntaxSorts do out := out.insert d.name.eraseMacroScopes
  for d in sig.syntaxAbbrevs do out := out.insert d.name.eraseMacroScopes
  for d in sig.syntaxDefs do out := out.insert d.name.eraseMacroScopes
  for d in sig.judgmentAbbrevs do out := out.insert d.name.eraseMacroScopes
  for d in sig.contextZones do out := out.insert d.name.eraseMacroScopes
  for d in sig.binderClasses do out := out.insert d.name.eraseMacroScopes
  for d in sig.judgments do out := out.insert d.name.eraseMacroScopes
  for d in sig.rules do out := out.insert d.name.eraseMacroScopes
  for d in sig.sideConditionSolvers do out := out.insert d.name.eraseMacroScopes
  for d in sig.conversionPlugins do out := out.insert d.name.eraseMacroScopes
  for d in sig.lfOpaqueConsts do out := out.insert d.name.eraseMacroScopes
  for d in sig.lfObjectDefs do out := out.insert d.name.eraseMacroScopes
  for d in sig.lfJudgmentTheorems do out := out.insert d.name.eraseMacroScopes
  return out

/-- Deduplicate model-section resume markers while preserving first declaration order. -/
def dedupeModelSections (sections : Array ModelSectionDecl) : Array ModelSectionDecl := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  for s in sections do
    let n := s.name.eraseMacroScopes
    unless seen.contains n do
      seen := seen.insert n
      out := out.push { s with name := n }
  return out

/-- Check that user-facing model-section metadata is coherent. -/
def checkModelSectionMetadataInSignature (sig : HLSignature) : CoreM Unit := do
  let declNames := sig.nameSet
  let mut seenSections : NameSet := {}
  for s in sig.modelSections do
    let n := s.name.eraseMacroScopes
    seenSections := seenSections.insert n
  for m in sig.modelSectionMemberships do
    let sectionName := m.sectionName.eraseMacroScopes
    let declName := m.declName.eraseMacroScopes
    unless seenSections.contains sectionName do
      throwError "model section membership for '{declName}' refers to unknown section \
        '{sectionName}' in type theory '{sig.name}'"
    unless declNames.contains declName do
      throwError "model section membership refers to unknown declaration '{declName}' in type \
        theory '{sig.name}'"

/-- Check that all declaration names in a flattened signature are unique. -/
def checkNoDuplicateNamesInSignature (sig : HLSignature) : CoreM Unit := do
  let mut seen : NameSet := {}
  for (kind, n) in
      (sig.syntaxSorts.map (fun d => ("syntax-sort", d.name)) ++
        sig.syntaxAbbrevs.map (fun d => ("syntax abbreviation", d.name)) ++
        sig.syntaxDefs.map (fun d => ("syntax definition", d.name)) ++
        sig.judgmentAbbrevs.map (fun d => ("judgment abbreviation", d.name)) ++
        sig.contextZones.map (fun d => ("context-zone", d.name)) ++
        sig.binderClasses.map (fun d => ("binder class", d.name)) ++
        sig.judgments.map (fun d => ("judgment", d.name)) ++
        sig.rules.map (fun d => ("rule", d.name)) ++
        sig.sideConditionSolvers.map (fun d => ("side-condition solver", d.name)) ++
        sig.conversionPlugins.map (fun d => ("conversion plugin", d.name)) ++
        sig.lfOpaqueConsts.map (fun d => ("LF opaque constant", d.name)) ++
        sig.lfObjectDefs.map (fun d => ("LF object definition", d.name)) ++
        sig.lfJudgmentTheorems.map (fun d => ("LF judgment theorem", d.name))) do
    if seen.contains n then
      throwError "duplicate {kind} declaration '{n}' in flattened type theory '{sig.name}'"
    seen := seen.insert n

/-- Check that a theory's opt-in object universe-level parameter telescope has no repeats. -/
def checkNoDuplicateLevelParamsInSignature (sig : HLSignature) : CoreM Unit := do
  let mut seen : NameSet := {}
  for u in sig.levelParams do
    let u := u.eraseMacroScopes
    if seen.contains u then
      throwError "duplicate universe level parameter '{u}' in type theory '{sig.name}'"
    seen := seen.insert u

/-- Check that all universe parameters mentioned in an LF expression were explicitly opted into
by the surrounding theory. Numeric levels are always allowed. -/
def checkDeclaredLevelParamsInLFExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (e : ObjExpr) : CoreM Unit := do
  let allowed : NameSet := sig.levelParams.foldl (fun acc u => acc.insert u.eraseMacroScopes) {}
  for u in e.levelParams do
    let u := u.eraseMacroScopes
    unless allowed.contains u do
      let optIn := if sig.levelParams.isEmpty then "none" else
        String.intercalate ", " (sig.levelParams.toList.map (toString ·.eraseMacroScopes))
      throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' uses undeclared universe \
        level parameter '{u}' in {where_}; declare it in the theory-level parameter list \
          containing '{u}' or use a numeric level. Currently declared level parameter(s): {optIn}"

/-- Check that all universe parameters mentioned in a level expression were explicitly opted into
by the surrounding theory. -/
def checkDeclaredLevelParamsInLevelExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (level : LevelExpr) : CoreM Unit := do
  let allowed : NameSet := sig.levelParams.foldl (fun acc u => acc.insert u.eraseMacroScopes) {}
  for u in level.params do
    let u := u.eraseMacroScopes
    unless allowed.contains u do
      let optIn := if sig.levelParams.isEmpty then "none" else
        String.intercalate ", " (sig.levelParams.toList.map (toString ·.eraseMacroScopes))
      throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' uses undeclared universe \
        level parameter '{u}' in {where_}; declare it in the theory-level parameter list \
          containing '{u}' or use a numeric level. Currently declared level parameter(s): {optIn}"

/-- Check one LF metadata binder for undeclared universe-level parameters. -/
def checkDeclaredLevelParamsInLFBinding (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (b : HLBinding) : CoreM Unit :=
  checkDeclaredLevelParamsInLFExpr sig ownerKind ownerName
    s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr

/-- Reject nested LF binders that reuse an already-bound name. -/
def checkNoLFLocalBinderShadowingInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (e : ObjExpr)
    (baseLocals : NameSet := {}) : CoreM Unit := do
  let rec go (locals : NameSet) (e : ObjExpr) : CoreM Unit := do
    match e with
    | .ident _ | .sort | .univ _ => pure ()
    | .app f a => go locals f *> go locals a
    | .arrow x A B | .funArrow x A B | .sigma x A B => do
        go locals A
        let locals ← match x with
          | some x =>
              let x := x.eraseMacroScopes
              if locals.contains x then
                throwError "duplicate LF binder '{x}' in {where_} of {ownerKind} '{ownerName}' \
                  in type theory '{sig.name}'"
              pure (locals.insert x)
          | none => pure locals
        go locals B
    | .pair a b => go locals a *> go locals b
    | .fst e | .snd e => go locals e
    | .lam xs body => do
        let mut seen : NameSet := {}
        for x in xs do
          let x := x.eraseMacroScopes
          if seen.contains x then
            throwError "duplicate lambda binder '{x}' in {where_} of {ownerKind} '{ownerName}' \
              in type theory '{sig.name}'"
          seen := seen.insert x
        go locals body
    | .jeq lhs rhs => go locals lhs *> go locals rhs
  go baseLocals e

/-- Check one LF metadata binder for source-level binder hygiene. -/
def checkNoLFLocalBinderShadowingInBinding (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (b : HLBinding) : CoreM Unit :=
  checkNoLFLocalBinderShadowingInExpr sig ownerKind ownerName
    s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr

/-- Check all LF metadata expressions for source-level binder hygiene. -/
def checkLFLocalBinderHygieneMetadata (sig : HLSignature) : CoreM Unit := do
  for s in sig.syntaxSorts do
    for b in s.params do
      checkNoLFLocalBinderShadowingInBinding sig "syntax_sort" s.name b
  for a in sig.syntaxAbbrevs do
    for b in a.params do
      checkNoLFLocalBinderShadowingInBinding sig "syntax_abbrev" a.name b
    checkNoLFLocalBinderShadowingInExpr sig "syntax_abbrev" a.name "value" a.value
  for d in sig.syntaxDefs do
    for b in d.params do
      checkNoLFLocalBinderShadowingInBinding sig "syntax_def" d.name b
    if let some value := d.value? then
      checkNoLFLocalBinderShadowingInExpr sig "syntax_def" d.name "value" value
  for a in sig.judgmentAbbrevs do
    for b in a.params do
      checkNoLFLocalBinderShadowingInBinding sig "judgment_abbrev" a.name b
    checkNoLFLocalBinderShadowingInExpr sig "judgment_abbrev" a.name "value" a.value
  for j in sig.judgments do
    for b in j.params do
      checkNoLFLocalBinderShadowingInBinding sig "judgment" j.name b
  for o in sig.lfOpaqueConsts do
    for b in o.params do
      checkNoLFLocalBinderShadowingInBinding sig "lf_opaque" o.name b
    if let some ty := o.typeExpr? then
      checkNoLFLocalBinderShadowingInExpr sig "lf_opaque" o.name "result type" ty
  for r in sig.rules do
    for b in r.params do
      checkNoLFLocalBinderShadowingInBinding sig "rule" r.name b
    for p in r.premises do
      checkNoLFLocalBinderShadowingInExpr sig "rule" r.name s!"premise \
        '{p.name.eraseMacroScopes}'" p.judgmentExpr
    for e in r.paramEvidences do
      checkNoLFLocalBinderShadowingInExpr sig "rule" r.name s!"evidence \
        '{e.name.eraseMacroScopes}'" e.judgmentExpr
    for sc in r.sideConditions do
      checkNoLFLocalBinderShadowingInExpr sig "rule" r.name s!"side-condition \
        '{sc.name.eraseMacroScopes}'" sc.input
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name "conclusion" r.conclusionExpr
  for d in sig.lfObjectDefs do
    checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "type" d.typeExpr
    checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "value" d.value
  for t in sig.lfJudgmentTheorems do
    for b in t.binders do
      checkNoLFLocalBinderShadowingInBinding sig "judgment_theorem" t.name b
    checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "statement"
      t.judgmentExpr
    checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Whether an object expression is a scope-erased reference to one identifier. -/
def objExprIsIdentErased (expr : ObjExpr) (name : Name) : Bool :=
  match expr with
  | .ident n => n.eraseMacroScopes == name.eraseMacroScopes
  | _ => false

/-- Check one binder has explicit visibility and the profiled level sort. -/
def checkLevelNormalizerLevelBinding (sig : HLSignature) (profile : LFLevelNormalizerProfileDecl)
    (ownerKind : String) (ownerName : Name) (b : HLBinding) : CoreM Unit := do
  unless b.visibility == .explicit do
    throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' must use explicit \
      profiled level parameters for level_normalizer"
  unless objExprIsIdentErased b.typeExpr profile.levelSortName do
    throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has parameter \
      '{b.name}' of type '{b.typeExpr}', expected profiled level sort \
      '{profile.levelSortName}'"

/-- Check executable level-normalizer profiles against the flattened signature. -/
def checkLFLevelNormalizerProfilesInSignature (sig : HLSignature) : CoreM Unit := do
  if sig.levelNormalizerProfiles.size > 1 then
    throwError "type theory '{sig.name}' has multiple level_normalizer profiles after parent \
      flattening; keep the executable normalizer opt-in unambiguous"
  for profile in sig.levelNormalizerProfiles do
    unless profile.trust == .executableChecked do
      throwError "level_normalizer in type theory '{sig.name}' currently supports only trust \
        executable_checked, got '{profile.trust.label}'"
    let levelName := profile.levelSortName.eraseMacroScopes
    unless sig.syntaxSorts.any (fun s => s.name.eraseMacroScopes == levelName) do
      throwError "level_normalizer in type theory '{sig.name}' refers to unknown level sort \
        '{profile.levelSortName}'"
    let checkResultLevel (ownerKind : String) (ownerName : Name) (typeExpr? : Option ObjExpr) := do
      let some typeExpr := typeExpr?
        | throwError "level_normalizer in type theory '{sig.name}' requires typed {ownerKind} \
          '{ownerName}'"
      unless objExprIsIdentErased typeExpr levelName do
        throwError "level_normalizer in type theory '{sig.name}' expected {ownerKind} \
          '{ownerName}' to return '{levelName}', got '{typeExpr}'"
    let some zeroDecl := sig.lfOpaqueConsts.find? (fun o =>
        o.name.eraseMacroScopes == profile.zeroName.eraseMacroScopes)
      | throwError "level_normalizer in type theory '{sig.name}' refers to unknown zero \
        constructor '{profile.zeroName}'"
    unless zeroDecl.params.isEmpty do
      throwError "level_normalizer zero constructor '{profile.zeroName}' in type theory \
        '{sig.name}' must have no parameters"
    checkResultLevel "zero constructor" profile.zeroName zeroDecl.typeExpr?
    let some succDecl := sig.lfOpaqueConsts.find? (fun o =>
        o.name.eraseMacroScopes == profile.succName.eraseMacroScopes)
      | throwError "level_normalizer in type theory '{sig.name}' refers to unknown succ \
        constructor '{profile.succName}'"
    unless succDecl.params.size == 1 do
      throwError "level_normalizer succ constructor '{profile.succName}' in type theory \
        '{sig.name}' must have one parameter"
    checkLevelNormalizerLevelBinding sig profile "level_normalizer succ constructor"
      profile.succName succDecl.params[0]!
    checkResultLevel "succ constructor" profile.succName succDecl.typeExpr?
    let some maxDecl := sig.lfOpaqueConsts.find? (fun o =>
        o.name.eraseMacroScopes == profile.maxName.eraseMacroScopes)
      | throwError "level_normalizer in type theory '{sig.name}' refers to unknown max \
        constructor '{profile.maxName}'"
    unless maxDecl.params.size == 2 do
      throwError "level_normalizer max constructor '{profile.maxName}' in type theory \
        '{sig.name}' must have two parameters"
    for b in maxDecl.params do
      checkLevelNormalizerLevelBinding sig profile "level_normalizer max constructor"
        profile.maxName b
    checkResultLevel "max constructor" profile.maxName maxDecl.typeExpr?
    let some leDecl := sig.judgments.find? (fun j =>
        j.name.eraseMacroScopes == profile.leName.eraseMacroScopes)
      | throwError "level_normalizer in type theory '{sig.name}' refers to unknown order \
        judgment '{profile.leName}'"
    unless leDecl.params.size == 2 do
      throwError "level_normalizer order judgment '{profile.leName}' in type theory \
        '{sig.name}' must have two parameters"
    for b in leDecl.params do
      checkLevelNormalizerLevelBinding sig profile "level_normalizer order judgment"
        profile.leName b

/-- Check LF metadata for opt-in universe-level discipline. -/
def checkLFUniverseLevelMetadata (sig : HLSignature) : CoreM Unit := do
  checkNoDuplicateLevelParamsInSignature sig
  for s in sig.syntaxSorts do
    for b in s.params do
      checkDeclaredLevelParamsInLFBinding sig "syntax_sort" s.name b
    checkDeclaredLevelParamsInLevelExpr sig "syntax_sort" s.name "result universe"
      s.resultLevel
  for a in sig.syntaxAbbrevs do
    for b in a.params do
      checkDeclaredLevelParamsInLFBinding sig "syntax_abbrev" a.name b
    checkDeclaredLevelParamsInLFExpr sig "syntax_abbrev" a.name "value" a.value
  for d in sig.syntaxDefs do
    for b in d.params do
      checkDeclaredLevelParamsInLFBinding sig "syntax_def" d.name b
    checkDeclaredLevelParamsInLevelExpr sig "syntax_def" d.name "result universe" d.resultLevel
    if let some value := d.value? then
      checkDeclaredLevelParamsInLFExpr sig "syntax_def" d.name "value" value
  for a in sig.judgmentAbbrevs do
    for b in a.params do
      checkDeclaredLevelParamsInLFBinding sig "judgment_abbrev" a.name b
    checkDeclaredLevelParamsInLFExpr sig "judgment_abbrev" a.name "value" a.value
  for j in sig.judgments do
    for b in j.params do
      checkDeclaredLevelParamsInLFBinding sig "judgment" j.name b
  for o in sig.lfOpaqueConsts do
    for b in o.params do
      checkDeclaredLevelParamsInLFBinding sig "lf_opaque" o.name b
    if let some ty := o.typeExpr? then
      checkDeclaredLevelParamsInLFExpr sig "lf_opaque" o.name "result type" ty
  for r in sig.rules do
    for b in r.params do
      checkDeclaredLevelParamsInLFBinding sig "rule" r.name b
    for p in r.premises do
      checkDeclaredLevelParamsInLFExpr sig "rule" r.name s!"premise '{p.name.eraseMacroScopes}'"
        p.judgmentExpr
    for e in r.paramEvidences do
      checkDeclaredLevelParamsInLFExpr sig "rule" r.name s!"evidence '{e.name.eraseMacroScopes}'"
        e.judgmentExpr
    for sc in r.sideConditions do
      checkDeclaredLevelParamsInLFExpr sig "rule" r.name s!"side-condition \
        '{sc.name.eraseMacroScopes}'" sc.input
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name "conclusion" r.conclusionExpr
  for d in sig.lfObjectDefs do
    checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "type" d.typeExpr
    checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "value" d.value
  for t in sig.lfJudgmentTheorems do
    for b in t.binders do
      checkDeclaredLevelParamsInLFBinding sig "judgment_theorem" t.name b
    checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
    checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Check that a metadata telescope has no repeated binder names. -/
def checkNoDuplicateMetadataBinders (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (bs : Array HLBinding) : CoreM Unit := do
  let mut seen : NameSet := {}
  for b in bs do
    let n := b.name.eraseMacroScopes
    if seen.contains n then
      throwError "duplicate parameter name '{n}' in {ownerKind} '{ownerName}' of type theory \
        '{sig.name}'"
    seen := seen.insert n

/-- Check uses of declared `syntax_sort` names inside metadata telescope types.

This intentionally does not typecheck the arguments. It only catches obvious arity
mistakes when a telescope type is syntactically headed by a declared syntax sort. -/
partial def checkSyntaxSortApplicationsInExpr (sig : HLSignature) (syntaxSortArities : NameMap Nat)
    (ownerKind : String) (ownerName : Name) (where_ : String) (e : ObjExpr) : CoreM Unit := do
  let rec go (e : ObjExpr) : CoreM Unit := do
    match e with
    | .ident head =>
        match syntaxSortArities.find? head with
        | some arity =>
            if arity != 0 then
              throwError "{ownerKind} '{ownerName}' {where_} in type theory '{sig.name}' uses \
                syntax sort '{head}' with 0 argument(s), expected {arity}"
        | none => pure ()
    | .sort | .univ _ => pure ()
    | .app .. =>
        match splitObjApp e with
        | (.ident head, args) =>
            match syntaxSortArities.find? head with
            | some arity =>
                if args.size != arity then
                  throwError "{ownerKind} '{ownerName}' {where_} in type theory '{sig.name}' uses \
                    syntax sort '{head}' with {args.size} argument(s), expected {arity}"
            | none => pure ()
            for arg in args do
              go arg
        | (head, args) =>
            go head
            for arg in args do
              go arg
    | .arrow _ A B | .funArrow _ A B | .sigma _ A B => go A *> go B
    | .pair a b => go a *> go b
    | .fst e | .snd e => go e
    | .lam _ body => go body
    | .jeq lhs rhs => go lhs *> go rhs
  go e

/-- Check a metadata telescope for declared syntax-sort application arities. -/
def checkSyntaxSortApplicationsInBindings (sig : HLSignature) (syntaxSortArities : NameMap Nat)
    (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) : CoreM Unit := do
  for b in bs do
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities ownerKind ownerName
      s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr

/-- Arity map for type-valued syntax families accepted in binder/type positions. -/
def lfSyntaxFamilyArities (sig : HLSignature) : NameMap Nat := Id.run do
  let mut out : NameMap Nat := {}
  for s in sig.syntaxSorts do
    out := out.insert s.name.eraseMacroScopes s.params.size
  for d in sig.syntaxDefs do
    out := out.insert d.name.eraseMacroScopes d.params.size
  return out

/-- Collect globally known names for lightweight LF metadata expression validation. -/
def lfKnownGlobalNames (sig : HLSignature) : NameSet := Id.run do
  let mut known : NameSet := {}
  for s in sig.syntaxSorts do
    known := known.insert s.name.eraseMacroScopes
  for a in sig.syntaxAbbrevs do
    known := known.insert a.name.eraseMacroScopes
  for d in sig.syntaxDefs do
    known := known.insert d.name.eraseMacroScopes
  for a in sig.judgmentAbbrevs do
    known := known.insert a.name.eraseMacroScopes
  for j in sig.judgments do
    known := known.insert j.name.eraseMacroScopes
  for o in sig.lfOpaqueConsts do
    known := known.insert o.name.eraseMacroScopes
  for r in sig.rules do
    known := known.insert r.name.eraseMacroScopes
  for d in sig.lfObjectDefs do
    known := known.insert d.name.eraseMacroScopes
  for t in sig.lfJudgmentTheorems do
    known := known.insert t.name.eraseMacroScopes
  return known

/-- Count leading framework function arrows in an LF object type. -/
partial def lfFunctionTypeArity : ObjExpr → Nat
  | .arrow _ _ B | .funArrow _ _ B => lfFunctionTypeArity B + 1
  | _ => 0

/-- Declared application arity for a typed LF opaque when lightweight arity checking is exact.

A typed opaque whose result is itself a structural function can be used either as a function value
or applied to structural arguments, so exact syntactic arity checking is deferred to the LF type
checker. -/
def lfTypedOpaqueExactArity? (o : LFOpaqueConstDecl) (typeExpr : ObjExpr) : Option Nat :=
  if lfFunctionTypeArity typeExpr == 0 then some o.params.size else none

/-- Opaque LF placeholder arities declared in a signature. -/
def lfOpaqueArities (sig : HLSignature) : NameMap (Option Nat) := Id.run do
  let mut arities : NameMap (Option Nat) := {}
  for o in sig.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some typeExpr => lfTypedOpaqueExactArity? o typeExpr
      | none => o.arity?
    arities := arities.insert o.name.eraseMacroScopes arity?
  return arities

/-- Check that an opaque LF placeholder use has the declared arity, if any. -/
def checkLFOpaqueArity (sig : HLSignature) (opaqueArities : NameMap (Option Nat))
    (ownerKind : String) (ownerName : Name) (where_ : String) (head : Name) (args :
      Array ObjExpr) : CoreM Unit := do
  match opaqueArities.find? head.eraseMacroScopes with
  | some (some arity) =>
      if args.size != arity then
        throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' uses lf_opaque '{head}' \
          in {where_} with {args.size} argument(s), expected {arity}"
  | _ => pure ()

/-- Return the result type after peeling leading framework function arrows. -/
partial def lfFunctionTypeResult : ObjExpr → ObjExpr
  | .arrow _ _ B | .funArrow _ _ B => lfFunctionTypeResult B
  | e => e

/-- Whether a checked LF object-definition result is a structural record/Sigma type.

Most object definitions still end in a syntax-sort-headed type. A Sigma-shaped package has no
rigid identifier head after peeling leading function arrows, so it needs this structural case. -/
def lfObjectDefResultIsStructuralRecord : ObjExpr → Bool
  | .sigma .. => true
  | _ => false

/-- Whether a typed opaque constant has a structural result type that can be rendered as a model
field even though it is not headed by a syntax sort.

Opaque constants may be primitive package constructors whose result is a public abbreviation
expanding to a function or Sigma type. These still correspond to ordinary model fields. -/
def lfOpaqueResultIsStructuralType : ObjExpr → Bool
  | .arrow .. | .funArrow .. | .sigma .. => true
  | _ => false

/-- Build the explicit framework function type for a binder-style `internal def`. -/
def mkInternalDefFunctionType (params : Array HLBinding) (result : ObjExpr) : ObjExpr :=
  params.foldr (init := result) fun b acc => .funArrow (some b.name) b.typeExpr acc

/-- Build the lambda body for a binder-style `internal def`. -/
def mkInternalDefLambda (params : Array HLBinding) (body : ObjExpr) : ObjExpr :=
  if params.isEmpty then body else .lam (params.map (·.name)) body

/-- Explicit LF type of a `syntax_def` family. -/
def syntaxDefTypeExpr (d : SyntaxDefDecl) : ObjExpr :=
  mkInternalDefFunctionType d.params (objExprTypeOfLevel d.resultLevel)

/-- Lambda value of a checked `syntax_def`, when it has a body. -/
def syntaxDefValueExpr? (d : SyntaxDefDecl) : Option ObjExpr :=
  d.value?.map (mkInternalDefLambda d.params)

/-- Declared global LF heads together with their syntactic head class and optional arity. -/
def lfGlobalHeadInfo (sig : HLSignature) : NameMap (CheckedLFHeadKind × Option Nat) := Id.run do
  let mut heads : NameMap (CheckedLFHeadKind × Option Nat) := {}
  for s in sig.syntaxSorts do
    heads := heads.insert s.name.eraseMacroScopes (.syntaxSort, some s.params.size)
  for d in sig.syntaxDefs do
    heads := heads.insert d.name.eraseMacroScopes (.syntaxDef, some d.params.size)
  for j in sig.judgments do
    heads := heads.insert j.name.eraseMacroScopes (.judgment, some j.params.size)
  for o in sig.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some typeExpr => lfTypedOpaqueExactArity? o typeExpr
      | none => o.arity?
    heads := heads.insert o.name.eraseMacroScopes (.opaque, arity?)
  for r in sig.rules do
    heads := heads.insert r.name.eraseMacroScopes (.lfRule, none)
  for d in sig.lfObjectDefs do
    heads := heads.insert d.name.eraseMacroScopes (.lfDefinition,
      some (lfFunctionTypeArity d.typeExpr))
  for t in sig.lfJudgmentTheorems do
    heads := heads.insert t.name.eraseMacroScopes (.lfTheorem, some t.binders.size)
  return heads

/-- Resolve the identifier head of an LF metadata expression, when it has one. -/
def checkedLFHead? (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (locals : NameSet) (e : ObjExpr) : Option CheckedLFHead :=
  match splitObjApp e with
  | (.ident head, args) =>
      let head := head.eraseMacroScopes
      if locals.contains head then
        some { name := head, kind := .local, arity? := none, actualArity := args.size }
      else
        match globalHeads.find? head with
        | some (kind, arity?) =>
            some {
              name := head
              kind := kind
              arity? := arity?
              actualArity := args.size
            }
        | none => none
  | _ => none

/-- Identifier head of an object expression, if any. -/
def lfExprHeadIdent? (e : ObjExpr) : Option Name :=
  match splitObjApp e with
  | (.ident head, _) => some head.eraseMacroScopes
  | _ => none

/-- Names whose applications are custom-judgment statements. -/
def lfJudgmentHeadNames (sig : HLSignature) : NameSet := Id.run do
  let mut names : NameSet := {}
  for j in sig.judgments do
    names := names.insert j.name.eraseMacroScopes
  for j in sig.judgmentAbbrevs do
    names := names.insert j.name.eraseMacroScopes
  return names

/-- Names whose applications are object type/sort heads. -/
def lfObjectTypeHeadNames (sig : HLSignature) : NameSet := Id.run do
  let mut names : NameSet := {}
  for s in sig.syntaxSorts do
    names := names.insert s.name.eraseMacroScopes
  for s in sig.syntaxAbbrevs do
    names := names.insert s.name.eraseMacroScopes
  for s in sig.syntaxDefs do
    names := names.insert s.name.eraseMacroScopes
  return names

/-- Whether an expression is headed by a declared custom judgment or judgment abbreviation. -/
def lfExprIsJudgmentHeaded (sig : HLSignature) (e : ObjExpr) : Bool :=
  match lfExprHeadIdent? e with
  | some head => (lfJudgmentHeadNames sig).contains head
  | none => false

/-- Whether an expression is visibly an object type for declaration classification. -/
partial def lfExprIsObjectTypeLike (sig : HLSignature) : ObjExpr → Bool
  | .sort | .univ _ => true
  | .sigma .. => true
  | .arrow _ _ B | .funArrow _ _ B => lfExprIsObjectTypeLike sig B
  | e =>
      match lfExprHeadIdent? e with
      | some head => (lfObjectTypeHeadNames sig).contains head
      | none => false

/-- User-facing label for a checked LF head kind. -/
def CheckedLFHeadKind.label : CheckedLFHeadKind → String
  | .local => "local"
  | .syntaxSort => "syntax_sort"
  | .syntaxDef => "syntax_def"
  | .lfDefinition => "lf_definition"
  | .lfTheorem => "lf_theorem"
  | .lfRule => "lf_rule"
  | .judgment => "judgment"
  | .primitive => "primitive"
  | .definition => "definition"
  | .theorem => "theorem"
  | .opaque => "lf_opaque"

/-- Enforce any declared arity on a resolved LF head occurrence. -/
def checkCheckedLFHeadArity (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (where_ : String) (head : CheckedLFHead) : CoreM Unit := do
  if let some arity := head.arity? then
    if head.actualArity != arity then
      throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' uses {head.kind.label} \
        '{head.name}' in {where_} with {head.actualArity} argument(s), expected {arity}"

/-- Recursively resolve an LF metadata expression into a checked syntactic artifact. -/
partial def resolveLFExpr (sig : HLSignature) (globalHeads :
  NameMap (CheckedLFHeadKind × Option Nat))
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String) :
    ObjExpr → CoreM CheckedLFExpr
  | .ident n => do
      let n := n.eraseMacroScopes
      let head ←
        if locals.contains n then
          pure { name := n, kind := .local, arity? := none, actualArity := 0 }
        else
          match globalHeads.find? n with
          | some (kind, arity?) => pure { name := n, kind := kind, arity? := arity?, actualArity :=
            0 }
          | none =>
            throwError "unknown identifier '{n}' in {where_} of {ownerKind} '{ownerName}' in type \
              theory '{sig.name}'"
      checkCheckedLFHeadArity sig ownerKind ownerName where_ head
      pure (.ident head)
  | .sort => pure .sort
  | .univ u => pure (.univ u)
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident headName, args) =>
          let headName := headName.eraseMacroScopes
          let head ←
            if locals.contains headName then
              pure { name := headName, kind := .local, arity? := none, actualArity := args.size }
            else
              match globalHeads.find? headName with
              | some (kind, arity?) =>
                  pure {
                    name := headName
                    kind := kind
                    arity? := arity?
                    actualArity := args.size
                  }
              | none =>
                throwError "unknown identifier '{headName}' in {where_} of {ownerKind} \
                  '{ownerName}' in type theory '{sig.name}'"
          checkCheckedLFHeadArity sig ownerKind ownerName where_ head
          let mut out : CheckedLFExpr := .ident head
          for arg in args do
            out := .app out (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ arg)
          pure out
      | (head, args) => do
          let mut out ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ head
          for arg in args do
            out := .app out (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ arg)
          pure out
  | .arrow x A B => do
      let A ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ B
      pure (.arrow (x.map Name.eraseMacroScopes) A B)
  | .funArrow x A B => do
      let A ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ B
      pure (.arrow (x.map Name.eraseMacroScopes) A B)
  | .sigma x A B => do
      let A ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ B
      pure (.sigma (x.map Name.eraseMacroScopes) A B)
  | .pair a b => do
      pure (.pair (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ a)
        (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ b))
  | .fst e => do
      pure (.fst (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ e))
  | .snd e => do
      pure (.snd (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ e))
  | .lam xs body => do
      let clean := xs.map Name.eraseMacroScopes
      let locals := clean.foldl (fun locals x => locals.insert x) locals
      pure (.lam clean (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ body))
  | .jeq lhs rhs => do
      pure (.jeq (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ lhs)
        (← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ rhs))

/-- Resolve an LF rule-parameter telescope into checked metadata binders. -/
def checkedLFBindings (sig : HLSignature) (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) :
      CoreM (Array CheckedLFBinding × NameSet) := do
  let mut locals : NameSet := {}
  let mut out := #[]
  for b in bs do
    let name := b.name.eraseMacroScopes
    let checkedTypeExpr ←
      resolveLFExpr sig globalHeads locals ownerKind ownerName s!"parameter '{name}' \
        type" b.typeExpr
    let head? := checkedLFHead? globalHeads locals b.typeExpr
    out := out.push {
      name := name
      typeExpr := b.typeExpr
      visibility := b.visibility
      checkedTypeExpr := checkedTypeExpr
      head? := head?
    }
    locals := locals.insert name
  return (out, locals)

/-- Erase macro scopes throughout an LF metadata expression for stable comparisons. -/
partial def eraseObjExprScopes : ObjExpr → ObjExpr
  | .ident n => .ident n.eraseMacroScopes
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (eraseObjExprScopes f) (eraseObjExprScopes a)
  | .arrow x A B => .arrow (x.map Name.eraseMacroScopes) (eraseObjExprScopes A) (
    eraseObjExprScopes B)
  | .funArrow x A B => .funArrow (x.map Name.eraseMacroScopes) (eraseObjExprScopes A) (
    eraseObjExprScopes B)
  | .sigma x A B => .sigma (x.map Name.eraseMacroScopes) (eraseObjExprScopes A) (
    eraseObjExprScopes B)
  | .pair a b => .pair (eraseObjExprScopes a) (eraseObjExprScopes b)
  | .fst e => .fst (eraseObjExprScopes e)
  | .snd e => .snd (eraseObjExprScopes e)
  | .lam xs body => .lam (xs.map Name.eraseMacroScopes) (eraseObjExprScopes body)
  | .jeq lhs rhs => .jeq (eraseObjExprScopes lhs) (eraseObjExprScopes rhs)

/-- Free object-level identifiers in an LF metadata expression. -/
partial def freeLFObjectIdentifiers : ObjExpr → NameSet
  | .ident n => ({} : NameSet).insert n.eraseMacroScopes
  | .sort | .univ _ => {}
  | .app f a => freeLFObjectIdentifiers f ++ freeLFObjectIdentifiers a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let free := freeLFObjectIdentifiers A ++ freeLFObjectIdentifiers B
      match x with
      | some x => free.erase x.eraseMacroScopes
      | none => free
  | .pair a b => freeLFObjectIdentifiers a ++ freeLFObjectIdentifiers b
  | .fst e | .snd e => freeLFObjectIdentifiers e
  | .lam xs body =>
      let free := freeLFObjectIdentifiers body
      xs.foldl (fun free x => free.erase x.eraseMacroScopes) free
  | .jeq lhs rhs => freeLFObjectIdentifiers lhs ++ freeLFObjectIdentifiers rhs

/-- Free object-level identifiers as a duplicate-free worklist, respecting local binders. -/
partial def freeLFObjectIdentifierArrayWithLocals (locals : NameSet) (seen : NameSet)
    (acc : Array Name) : ObjExpr → NameSet × Array Name
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n || seen.contains n then
        (seen, acc)
      else
        (seen.insert n, acc.push n)
  | .sort | .univ _ => (seen, acc)
  | .app f a =>
      let (seen, acc) := freeLFObjectIdentifierArrayWithLocals locals seen acc f
      freeLFObjectIdentifierArrayWithLocals locals seen acc a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let (seen, acc) := freeLFObjectIdentifierArrayWithLocals locals seen acc A
      let locals := match x with
        | some x => locals.insert x.eraseMacroScopes
        | none => locals
      freeLFObjectIdentifierArrayWithLocals locals seen acc B
  | .pair a b =>
      let (seen, acc) := freeLFObjectIdentifierArrayWithLocals locals seen acc a
      freeLFObjectIdentifierArrayWithLocals locals seen acc b
  | .fst e | .snd e => freeLFObjectIdentifierArrayWithLocals locals seen acc e
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      freeLFObjectIdentifierArrayWithLocals locals seen acc body
  | .jeq lhs rhs =>
      let (seen, acc) := freeLFObjectIdentifierArrayWithLocals locals seen acc lhs
      freeLFObjectIdentifierArrayWithLocals locals seen acc rhs

/-- Free object-level identifiers as a duplicate-free worklist. -/
def freeLFObjectIdentifierArray (e : ObjExpr) : Array Name :=
  (freeLFObjectIdentifierArrayWithLocals {} {} #[] e).2

/-- Lookup the canonical representative for a locally-bound LF name. -/
def lookupLFAlphaLocal? : List (Name × Name) → Name → Option Name
  | [], _ => none
  | (oldName, newName) :: rest, n =>
      if oldName.eraseMacroScopes == n.eraseMacroScopes then some newName else
        lookupLFAlphaLocal? rest n

/-- Pick a deterministic alpha-normalization binder name avoiding free identifiers. -/
def canonicalLFAlphaBinderName (idx : Nat) (avoid : NameSet) : Name :=
  let base : Name := .str `_lfBound s!"b{idx}"
  let rec go : Nat → Nat → Name
    | 0, n => .str base s!"_{n}"
    | fuel + 1, n =>
        let candidate := if n == 0 then base else .str base s!"_{n}"
        if avoid.contains candidate then go fuel (n + 1) else candidate
  go (avoid.size + 32) 0

/-- Alpha-normalize LF binders to deterministic globally fresh binder identifiers. -/
partial def alphaNormalizeLFExprWithAvoid (avoid : NameSet) (e : ObjExpr) : ObjExpr :=
  let rec go (locals : List (Name × Name)) (next : Nat) : ObjExpr → ObjExpr × Nat
    | .ident n =>
        let n := n.eraseMacroScopes
        match lookupLFAlphaLocal? locals n with
        | some n' => (.ident n', next)
        | none => (.ident n, next)
    | .sort => (.sort, next)
    | .univ u => (.univ u, next)
    | .app f a =>
        let (f, next) := go locals next f
        let (a, next) := go locals next a
        (.app f a, next)
    | .arrow x A B =>
        let (A, next) := go locals next A
        match x with
        | some x =>
            let x := x.eraseMacroScopes
            let x' := canonicalLFAlphaBinderName next avoid
            let (B, next) := go ((x, x') :: locals) (next + 1) B
            (.arrow (some x') A B, next)
        | none =>
            let (B, next) := go locals next B
            (.arrow none A B, next)
    | .funArrow x A B =>
        let (A, next) := go locals next A
        match x with
        | some x =>
            let x := x.eraseMacroScopes
            let x' := canonicalLFAlphaBinderName next avoid
            let (B, next) := go ((x, x') :: locals) (next + 1) B
            (.funArrow (some x') A B, next)
        | none =>
            let (B, next) := go locals next B
            (.funArrow none A B, next)
    | .sigma x A B =>
        let (A, next) := go locals next A
        match x with
        | some x =>
            let x := x.eraseMacroScopes
            let x' := canonicalLFAlphaBinderName next avoid
            let (B, next) := go ((x, x') :: locals) (next + 1) B
            (.sigma (some x') A B, next)
        | none =>
            let (B, next) := go locals next B
            (.sigma none A B, next)
    | .pair a b =>
        let (a, next) := go locals next a
        let (b, next) := go locals next b
        (.pair a b, next)
    | .fst e =>
        let (e, next) := go locals next e
        (.fst e, next)
    | .snd e =>
        let (e, next) := go locals next e
        (.snd e, next)
    | .lam xs body =>
        let clean := xs.map Name.eraseMacroScopes
        let (xs', locals, next) := Id.run do
          let mut out := #[]
          let mut locals := locals
          let mut next := next
          for x in clean do
            let x' := canonicalLFAlphaBinderName next avoid
            out := out.push x'
            locals := (x, x') :: locals
            next := next + 1
          return (out, locals, next)
        let (body, next) := go locals next body
        (.lam xs' body, next)
    | .jeq lhs rhs =>
        let (lhs, next) := go locals next lhs
        let (rhs, next) := go locals next rhs
        (.jeq lhs rhs, next)
  (go [] 0 (eraseObjExprScopes e)).1

/-- Alpha-normalize an LF expression, avoiding its free identifiers. -/
def alphaNormalizeLFExpr (e : ObjExpr) : ObjExpr :=
  alphaNormalizeLFExprWithAvoid (freeLFObjectIdentifiers e) e

/-- Alpha-equivalence for LF expressions. -/
def lfExprAlphaEq (a b : ObjExpr) : Bool :=
  let avoid := freeLFObjectIdentifiers a ++ freeLFObjectIdentifiers b
  alphaNormalizeLFExprWithAvoid avoid a == alphaNormalizeLFExprWithAvoid avoid b

/-- Names occurring in the range of a substitution. -/
def lfSubstRangeFreeIdentifiers (subst : NameMap ObjExpr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (_, value) in subst.toList do
    out := out ++ freeLFObjectIdentifiers value
  return out

/-- Keys occurring in a substitution. -/
def lfSubstKeys (subst : NameMap ObjExpr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (n, _) in subst.toList do
    out := out.insert n.eraseMacroScopes
  return out

/-- Pick a deterministic fresh name avoiding a finite set. -/
def freshLFNameAvoiding (base : Name) (avoid : NameSet) : Name :=
  let base := base.eraseMacroScopes
  let rec go : Nat → Nat → Name
    | 0, n => .str base s!"_hyg{n}"
    | fuel + 1, n =>
        let candidate := .str base s!"_hyg{n}"
        if avoid.contains candidate then go fuel (n + 1) else candidate
  if avoid.contains base then go (avoid.size + 32) 0 else base

/-- Rename occurrences of a currently-bound identifier, respecting nested binders. -/
partial def renameLFBoundOccurrences (oldName newName : Name) : ObjExpr → ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      if n == oldName.eraseMacroScopes then .ident newName.eraseMacroScopes else .ident n
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (renameLFBoundOccurrences oldName newName f)
      (renameLFBoundOccurrences oldName newName a)
  | .arrow x A B =>
      let A := renameLFBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            renameLFBoundOccurrences oldName newName B
          .arrow (some x) A B
      | none => .arrow none A (renameLFBoundOccurrences oldName newName B)
  | .funArrow x A B =>
      let A := renameLFBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            renameLFBoundOccurrences oldName newName B
          .funArrow (some x) A B
      | none => .funArrow none A (renameLFBoundOccurrences oldName newName B)
  | .sigma x A B =>
      let A := renameLFBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            renameLFBoundOccurrences oldName newName B
          .sigma (some x) A B
      | none => .sigma none A (renameLFBoundOccurrences oldName newName B)
  | .pair a b => .pair (renameLFBoundOccurrences oldName newName a)
      (renameLFBoundOccurrences oldName newName b)
  | .fst e => .fst (renameLFBoundOccurrences oldName newName e)
  | .snd e => .snd (renameLFBoundOccurrences oldName newName e)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      let body := if clean.contains oldName.eraseMacroScopes then body else
        renameLFBoundOccurrences oldName newName body
      .lam clean body
  | .jeq lhs rhs => .jeq (renameLFBoundOccurrences oldName newName lhs)
      (renameLFBoundOccurrences oldName newName rhs)

/-- Whether substituting under `binder` would capture a free identifier from the substitution. -/
def lfSubstWouldCaptureUnderBinder (binder : Name) (subst : NameMap ObjExpr)
    (body : ObjExpr) : Bool :=
  let binder := binder.eraseMacroScopes
  let bodyFree := freeLFObjectIdentifiers body
  subst.toList.any fun (n, value) =>
    let n := n.eraseMacroScopes
    n != binder && bodyFree.contains n && (freeLFObjectIdentifiers value).contains binder

/-- Substitute identifiers in an LF metadata expression, respecting expression binders. -/
partial def substLFParams (subst : NameMap ObjExpr) : ObjExpr → ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      (subst.find? n).getD (.ident n)
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (substLFParams subst f) (substLFParams subst a)
  | .arrow x A B =>
      let A := substLFParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfSubstWouldCaptureUnderBinder x subst B then
              let avoid := freeLFObjectIdentifiers B ++ lfSubstRangeFreeIdentifiers subst ++
                lfSubstKeys subst |>.insert x
              let y := freshLFNameAvoiding x avoid
              (y, renameLFBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .arrow (some x) A (substLFParams subst B)
      | none => .arrow none A (substLFParams subst B)
  | .funArrow x A B =>
      let A := substLFParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfSubstWouldCaptureUnderBinder x subst B then
              let avoid := freeLFObjectIdentifiers B ++ lfSubstRangeFreeIdentifiers subst ++
                lfSubstKeys subst |>.insert x
              let y := freshLFNameAvoiding x avoid
              (y, renameLFBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .funArrow (some x) A (substLFParams subst B)
      | none => .funArrow none A (substLFParams subst B)
  | .sigma x A B =>
      let A := substLFParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfSubstWouldCaptureUnderBinder x subst B then
              let avoid := freeLFObjectIdentifiers B ++ lfSubstRangeFreeIdentifiers subst ++
                lfSubstKeys subst |>.insert x
              let y := freshLFNameAvoiding x avoid
              (y, renameLFBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .sigma (some x) A (substLFParams subst B)
      | none => .sigma none A (substLFParams subst B)
  | .pair a b => .pair (substLFParams subst a) (substLFParams subst b)
  | .fst e => .fst (substLFParams subst e)
  | .snd e => .snd (substLFParams subst e)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      let (clean, body, subst) := Id.run do
        let mut out := #[]
        let mut body := body
        let mut subst := subst
        for x in clean do
          let substBase := subst.erase x
          if lfSubstWouldCaptureUnderBinder x substBase body then
            let avoid := freeLFObjectIdentifiers body ++ lfSubstRangeFreeIdentifiers substBase ++
              lfSubstKeys substBase |>.insert x
            let y := freshLFNameAvoiding x avoid
            body := renameLFBoundOccurrences x y body
            subst := substBase.erase y
            out := out.push y
          else
            subst := substBase
            out := out.push x
        return (out, body, subst)
      .lam clean (substLFParams subst body)
  | .jeq lhs rhs => .jeq (substLFParams subst lhs) (substLFParams subst rhs)

/-- A shallow LF typing context for Phase-1 metadata validation. -/
abbrev LFLocalTypes := NameMap ObjExpr

/-- Substitute one LF/object identifier in an expression. -/
def substSingleLFParam (x : Name) (value body : ObjExpr) : ObjExpr :=
  let subst : NameMap ObjExpr := {}
  let subst := subst.insert x.eraseMacroScopes value
  substLFParams subst body

/-- Values of checked LF definitions available for definitional unfolding. -/
abbrev LFDefinitionValueMap := NameMap ObjExpr

/-- Number of object-expression nodes, used only for bounded conversion diagnostics. -/
partial def objExprNodeCount : ObjExpr → Nat
  | .ident _ | .sort | .univ _ => 1
  | .app f a => 1 + objExprNodeCount f + objExprNodeCount a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      1 + objExprNodeCount A + objExprNodeCount B
  | .pair a b => 1 + objExprNodeCount a + objExprNodeCount b
  | .fst e | .snd e => 1 + objExprNodeCount e
  | .lam _ body => 1 + objExprNodeCount body
  | .jeq lhs rhs => 1 + objExprNodeCount lhs + objExprNodeCount rhs

/-- Increment one name counter in a conversion-profile map. -/
def incrementLFConversionNameCount (counts : NameMap Nat) (n : Name) : NameMap Nat :=
  let n := n.eraseMacroScopes
  counts.insert n ((counts.find? n).getD 0 + 1)

/-- Merge two conversion-profile name-count maps. -/
def mergeLFConversionNameCounts (lhs rhs : NameMap Nat) : NameMap Nat := Id.run do
  let mut out := lhs
  for (n, count) in rhs.toList do
    out := out.insert n ((out.find? n).getD 0 + count)
  return out

/-- Fuel for deterministic LF-definition unfolding. Ordered LF-definition availability rejects
cycles, but a small explicit bound keeps diagnostics robust if malformed metadata reaches this
helper through a future path. -/
def lfDefinitionUnfoldFuel (defs : LFDefinitionValueMap) : Nat :=
  defs.size * 4 + 32

/-- Free identifiers occurring in the range of available LF-definition values. -/
def lfDefinitionValuesFreeIdentifiers (defs : LFDefinitionValueMap) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (_, value) in defs.toList do
    out := out ++ freeLFObjectIdentifiers value
  return out

/-- Freshen a binder before unfolding definitions whose free identifiers would otherwise collide. -/
def freshLFUnfoldBinder (defs : LFDefinitionValueMap) (locals : NameSet) (binder : Name)
    (body : ObjExpr) : Name × ObjExpr :=
  let binder := binder.eraseMacroScopes
  let defFree := lfDefinitionValuesFreeIdentifiers defs
  if defFree.contains binder || locals.contains binder then
    let avoid := freeLFObjectIdentifiers body ++ defFree ++ locals |>.insert binder
    let binder' := freshLFNameAvoiding binder avoid
    (binder', renameLFBoundOccurrences binder binder' body)
  else
    (binder, body)

/-- Unfold checked LF-definition aliases in an object expression, respecting local binders. -/
partial def unfoldLFDefinitionsInExprCore (defs : LFDefinitionValueMap) (locals : NameSet)
    (fuel : Nat) (e : ObjExpr) : ObjExpr :=
  match fuel with
  | 0 => e
  | fuel + 1 =>
      match e with
      | .ident n =>
          let key := n.eraseMacroScopes
          if locals.contains key then
            .ident key
          else
            match defs.find? key with
            | some value => unfoldLFDefinitionsInExprCore defs locals fuel value
            | none => .ident key
      | .sort => .sort
      | .univ u => .univ u
      | .app f a =>
          let f := unfoldLFDefinitionsInExprCore defs locals fuel f
          let a := unfoldLFDefinitionsInExprCore defs locals fuel a
          match f with
          | .lam xs body =>
              if h : 0 < xs.size then
                let x := xs[0]
                let rest := xs.extract 1 xs.size
                let target := if rest.isEmpty then body else .lam rest body
                unfoldLFDefinitionsInExprCore defs locals fuel (substSingleLFParam x a target)
              else
                .app f a
          | _ => .app f a
      | .arrow x A B =>
          let A := unfoldLFDefinitionsInExprCore defs locals fuel A
          match x with
          | some x =>
              let (x, B) := freshLFUnfoldBinder defs locals x B
              let locals := locals.insert x.eraseMacroScopes
              .arrow (some x) A (unfoldLFDefinitionsInExprCore defs locals fuel B)
          | none => .arrow none A (unfoldLFDefinitionsInExprCore defs locals fuel B)
      | .funArrow x A B =>
          let A := unfoldLFDefinitionsInExprCore defs locals fuel A
          match x with
          | some x =>
              let (x, B) := freshLFUnfoldBinder defs locals x B
              let locals := locals.insert x.eraseMacroScopes
              .funArrow (some x) A (unfoldLFDefinitionsInExprCore defs locals fuel B)
          | none => .funArrow none A (unfoldLFDefinitionsInExprCore defs locals fuel B)
      | .sigma x A B =>
          let A := unfoldLFDefinitionsInExprCore defs locals fuel A
          match x with
          | some x =>
              let (x, B) := freshLFUnfoldBinder defs locals x B
              let locals := locals.insert x.eraseMacroScopes
              .sigma (some x) A (unfoldLFDefinitionsInExprCore defs locals fuel B)
          | none => .sigma none A (unfoldLFDefinitionsInExprCore defs locals fuel B)
      | .pair a b =>
          .pair (unfoldLFDefinitionsInExprCore defs locals fuel a)
            (unfoldLFDefinitionsInExprCore defs locals fuel b)
      | .fst e =>
          match unfoldLFDefinitionsInExprCore defs locals fuel e with
          | .pair a _ => a
          | e => .fst e
      | .snd e =>
          match unfoldLFDefinitionsInExprCore defs locals fuel e with
          | .pair _ b => b
          | e => .snd e
      | .lam xs body =>
          let (xs, body, locals) := Id.run do
            let mut out := #[]
            let mut body := body
            let mut locals := locals
            for x in xs.map Name.eraseMacroScopes do
              let (x, body') := freshLFUnfoldBinder defs locals x body
              out := out.push x
              body := body'
              locals := locals.insert x.eraseMacroScopes
            return (out, body, locals)
          .lam xs (unfoldLFDefinitionsInExprCore defs locals fuel body)
      | .jeq lhs rhs =>
          .jeq (unfoldLFDefinitionsInExprCore defs locals fuel lhs)
            (unfoldLFDefinitionsInExprCore defs locals fuel rhs)

/-- Deterministic bounded unfolding of checked LF definitions in a closed expression. -/
def unfoldLFDefinitionsInExpr (defs : LFDefinitionValueMap) (e : ObjExpr) : ObjExpr :=
  unfoldLFDefinitionsInExprCore defs {} (lfDefinitionUnfoldFuel defs) (eraseObjExprScopes e)

/-- Deterministic bounded unfolding of checked LF definitions under a local LF context. -/
def unfoldLFDefinitionsInExprWithLocals (defs : LFDefinitionValueMap) (locals : NameSet) (e :
  ObjExpr) : ObjExpr :=
  unfoldLFDefinitionsInExprCore defs locals (lfDefinitionUnfoldFuel defs) (eraseObjExprScopes e)

/-- Count LF definitions expanded by the bounded unfolding policy, respecting local binders. -/
partial def countLFDefinitionUnfoldsCore (defs : LFDefinitionValueMap) (locals : NameSet)
    (fuel : Nat) (counts : NameMap Nat) : ObjExpr → NameMap Nat
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        counts
      else
        match fuel, defs.find? n with
        | 0, _ | _, none => counts
        | fuel + 1, some value =>
            countLFDefinitionUnfoldsCore defs locals fuel
              (incrementLFConversionNameCount counts n) value
  | .sort | .univ _ => counts
  | .app f a =>
      countLFDefinitionUnfoldsCore defs locals fuel
        (countLFDefinitionUnfoldsCore defs locals fuel counts f) a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let counts := countLFDefinitionUnfoldsCore defs locals fuel counts A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      countLFDefinitionUnfoldsCore defs locals fuel counts B
  | .pair a b =>
      countLFDefinitionUnfoldsCore defs locals fuel
        (countLFDefinitionUnfoldsCore defs locals fuel counts a) b
  | .fst e | .snd e => countLFDefinitionUnfoldsCore defs locals fuel counts e
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      countLFDefinitionUnfoldsCore defs locals fuel counts body
  | .jeq lhs rhs =>
      countLFDefinitionUnfoldsCore defs locals fuel
        (countLFDefinitionUnfoldsCore defs locals fuel counts lhs) rhs

/-- Count LF definitions expanded by the bounded unfolding policy. -/
def countLFDefinitionUnfolds (defs : LFDefinitionValueMap) (locals : NameSet) (e : ObjExpr) :
    NameMap Nat :=
  countLFDefinitionUnfoldsCore defs locals (lfDefinitionUnfoldFuel defs) {} (eraseObjExprScopes e)

/-- LF-definition values declared in a high-level signature, keyed by erased names. -/
def lfDefinitionValuesOfSignature (sig : HLSignature) : LFDefinitionValueMap := Id.run do
  let mut out : LFDefinitionValueMap := {}
  for d in sig.syntaxDefs do
    if let some value := syntaxDefValueExpr? d then
      out := out.insert d.name.eraseMacroScopes (eraseObjExprScopes value)
  for d in sig.lfObjectDefs do
    out := out.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)
  return out

/-- LF-definition values from `allDefs` reachable while unfolding a particular expression. -/
partial def lfDefinitionValuesFromMapForWorklist (allDefs : LFDefinitionValueMap)
    (seen : NameSet) (out : LFDefinitionValueMap) : List Name → LFDefinitionValueMap
  | [] => out
  | n :: rest =>
      let n := n.eraseMacroScopes
      if seen.contains n then
        lfDefinitionValuesFromMapForWorklist allDefs seen out rest
      else
        let seen := seen.insert n
        match allDefs.find? n with
        | none => lfDefinitionValuesFromMapForWorklist allDefs seen out rest
        | some value =>
            let deps := freeLFObjectIdentifierArray value
            lfDefinitionValuesFromMapForWorklist allDefs seen (out.insert n value)
              (deps.toList ++ rest)

/-- LF-definition values from `allDefs` reachable while unfolding a particular expression. -/
def lfDefinitionValuesOfMapForExpr (allDefs : LFDefinitionValueMap) (e : ObjExpr) :
    LFDefinitionValueMap :=
  lfDefinitionValuesFromMapForWorklist allDefs {} {} (freeLFObjectIdentifierArray e).toList

/-- LF-definition values that may be reached while unfolding a particular expression. -/
def lfDefinitionValuesOfSignatureForExpr (sig : HLSignature) (e : ObjExpr) : LFDefinitionValueMap :=
  lfDefinitionValuesOfMapForExpr (lfDefinitionValuesOfSignature sig) e

/-- Return the name of an LF eta argument, when it is a variable occurrence. -/
def lfEtaArgumentName? : ObjExpr → Option Name
  | .ident n => some n.eraseMacroScopes
  | _ => none

/-- Try to contract a structural function eta-redex after recursive normalization. -/
def contractLFFunctionEta? (xs : Array Name) (body : ObjExpr) : Option ObjExpr :=
  let binders := xs.toList.map Name.eraseMacroScopes
  if binders.isEmpty then
    none
  else
    let (head, args) := splitObjApp body
    let args := args.toList
    if args.length < binders.length then
      none
    else
      let prefixLength := args.length - binders.length
      match (args.drop prefixLength).mapM lfEtaArgumentName? with
      | none => none
      | some suffixNames =>
          if suffixNames == binders then
            let prefixExpr := mkObjApp head (args.take prefixLength).toArray
            let freePrefix := freeLFObjectIdentifiers prefixExpr
            if binders.any (fun x => freePrefix.contains x) then none else some prefixExpr
          else
            none

/-- Normalize structural function and Sigma eta-redexes in an already beta/delta-normal LF
expression. -/
partial def normalizeLFExprEtaOnly : ObjExpr → ObjExpr
  | .ident n => .ident n.eraseMacroScopes
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (normalizeLFExprEtaOnly f) (normalizeLFExprEtaOnly a)
  | .arrow x A B => .arrow (x.map Name.eraseMacroScopes) (normalizeLFExprEtaOnly A) (
    normalizeLFExprEtaOnly B)
  | .funArrow x A B => .funArrow (x.map Name.eraseMacroScopes) (normalizeLFExprEtaOnly A) (
    normalizeLFExprEtaOnly B)
  | .sigma x A B => .sigma (x.map Name.eraseMacroScopes) (normalizeLFExprEtaOnly A) (
    normalizeLFExprEtaOnly B)
  | .pair a b =>
      let a := normalizeLFExprEtaOnly a
      let b := normalizeLFExprEtaOnly b
      match a, b with
      | .fst p, .snd q => if lfExprAlphaEq p q then p else .pair a b
      | _, _ => .pair a b
  | .fst e =>
      match normalizeLFExprEtaOnly e with
      | .pair a _ => a
      | e => .fst e
  | .snd e =>
      match normalizeLFExprEtaOnly e with
      | .pair _ b => b
      | e => .snd e
  | .lam xs body =>
      let xs := xs.map Name.eraseMacroScopes
      let body := normalizeLFExprEtaOnly body
      match contractLFFunctionEta? xs body with
      | some f => f
      | none => .lam xs body
  | .jeq lhs rhs => .jeq (normalizeLFExprEtaOnly lhs) (normalizeLFExprEtaOnly rhs)

/-- Normalize an LF expression for conversion using checked definitions under local binders. -/
def normalizeLFExprForConversionWithLocals (defs : LFDefinitionValueMap) (locals : NameSet)
    (e : ObjExpr) : ObjExpr :=
  normalizeLFExprEtaOnly (unfoldLFDefinitionsInExprWithLocals defs locals e)

/-- Normalize an LF expression for conversion using an available definition map. -/
def normalizeLFExprForConversionWithDefs (defs : LFDefinitionValueMap) (e : ObjExpr) :
    ObjExpr :=
  normalizeLFExprForConversionWithLocals (lfDefinitionValuesOfMapForExpr defs e) {} e

/-- Normalize an LF expression for shallow type comparisons using an available definition map. -/
def normalizeLFExprForTypeComparisonWithDefs (defs : LFDefinitionValueMap) (e : ObjExpr) :
    ObjExpr :=
  normalizeLFExprForConversionWithDefs defs e

/-- Normalize an LF expression for shallow type comparisons. -/
def normalizeLFExprForTypeComparison (sig : HLSignature) (e : ObjExpr) : ObjExpr :=
  normalizeLFExprForConversionWithDefs (lfDefinitionValuesOfSignatureForExpr sig e) e

/-- Shallow equality of LF types after beta/eta-reduction and LF-definition unfolding using an
available definition map. -/
def lfTypeCompareEqWithDefs (defs : LFDefinitionValueMap) (actual expected : ObjExpr) : Bool :=
  lfExprAlphaEq (normalizeLFExprForTypeComparisonWithDefs defs actual)
    (normalizeLFExprForTypeComparisonWithDefs defs expected)

/-- Shallow equality of LF types after beta/eta-reduction and LF-definition unfolding. -/
def lfTypeCompareEq (sig : HLSignature) (actual expected : ObjExpr) : Bool :=
  lfExprAlphaEq (normalizeLFExprForTypeComparison sig actual)
    (normalizeLFExprForTypeComparison sig expected)

/-- Build the local type map for an LF rule telescope. -/
def lfLocalTypesOfBindings (bs : Array HLBinding) : LFLocalTypes := Id.run do
  let mut locals : LFLocalTypes := {}
  for b in bs do
    locals := locals.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
  return locals

/-- Look up a declared judgment by name. -/
def findJudgmentDecl? (sig : HLSignature) (name : Name) : Option JudgmentDecl :=
  let name := name.eraseMacroScopes
  sig.judgments.find? (fun j => j.name.eraseMacroScopes == name)

/-- Look up a declared syntax sort by name. -/
def findSyntaxSortDecl? (sig : HLSignature) (name : Name) : Option SyntaxSortDecl :=
  let name := name.eraseMacroScopes
  sig.syntaxSorts.find? (fun s => s.name.eraseMacroScopes == name)

/-- Look up a declared syntax abbreviation by name. -/
def findSyntaxAbbrevDecl? (sig : HLSignature) (name : Name) : Option SyntaxAbbrevDecl :=
  let name := name.eraseMacroScopes
  sig.syntaxAbbrevs.find? (fun a => a.name.eraseMacroScopes == name)

/-- Look up a declared syntax definition by name. -/
def findSyntaxDefDecl? (sig : HLSignature) (name : Name) : Option SyntaxDefDecl :=
  let name := name.eraseMacroScopes
  sig.syntaxDefs.find? (fun d => d.name.eraseMacroScopes == name)

/-- Look up a declared judgment abbreviation by name. -/
def findJudgmentAbbrevDecl? (sig : HLSignature) (name : Name) : Option JudgmentAbbrevDecl :=
  let name := name.eraseMacroScopes
  sig.judgmentAbbrevs.find? (fun a => a.name.eraseMacroScopes == name)

/-- Lightweight common view of source-level LF abbreviations. -/
structure LFAbbrevExpansionInfo where
  kindLabel : String
  params : Array HLBinding := #[]
  value : ObjExpr

/-- Look up any source-level LF abbreviation by name. -/
def findLFAbbrevExpansion? (sig : HLSignature) (name : Name) : Option LFAbbrevExpansionInfo :=
  match findSyntaxAbbrevDecl? sig name with
  | some a => some { kindLabel := "syntax_abbrev", params := a.params, value := a.value }
  | none =>
      match findJudgmentAbbrevDecl? sig name with
      | some a => some { kindLabel := "judgment_abbrev", params := a.params, value := a.value }
      | none => none

/-- Fuel bound for source-level LF abbreviation expansion. -/
def lfAbbrevExpansionFuel (sig : HLSignature) : Nat :=
  sig.syntaxAbbrevs.size + sig.judgmentAbbrevs.size + 1

/-- Expand public syntax and judgment abbreviations in an LF expression.

Expansion respects local binders and checks abbreviation arity. The fuel bound turns cycles
such as `syntax_abbrev A := A` into an explicit diagnostic instead of nontermination. -/
partial def expandSyntaxAbbrevsInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (locals : NameSet)
    (fuel : Nat) (e : ObjExpr) : CoreM ObjExpr := do
  match e with
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        pure (.ident n)
      else
        match findLFAbbrevExpansion? sig n with
        | none => pure (.ident n)
        | some a =>
            if fuel == 0 then
              throwError "cyclic or too-deep LF abbreviation expansion in {where_} of \
                {ownerKind} '{ownerName}' in type theory '{sig.name}'"
            if a.params.size != 0 then
              throwError "{ownerKind} '{ownerName}' uses {a.kindLabel} '{n}' in {where_} with \
                0 argument(s), expected {a.params.size}"
            expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals (fuel - 1) a.value
  | .sort => pure .sort
  | .univ u => pure (.univ u)
  | .app .. =>
      let (head, args) := splitObjApp e
      match head with
      | .ident headName =>
          let headName := headName.eraseMacroScopes
          if locals.contains headName then
            let args ←
              args.mapM (expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel)
            pure (mkObjApp (.ident headName) args)
          else
            match findLFAbbrevExpansion? sig headName with
            | some a =>
                if fuel == 0 then
                  throwError "cyclic or too-deep LF abbreviation expansion in {where_} of \
                    {ownerKind} '{ownerName}' in type theory '{sig.name}'"
                if args.size != a.params.size then
                  throwError "{ownerKind} '{ownerName}' uses {a.kindLabel} '{headName}' in \
                    {where_} with {args.size} argument(s), expected {a.params.size}"
                let mut subst : NameMap ObjExpr := {}
                for _h : i in [:args.size] do
                  let arg ←
                    expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel args[i]!
                  subst := subst.insert a.params[i]!.name.eraseMacroScopes (eraseObjExprScopes arg)
                let expanded := substLFParams subst a.value
                expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals (fuel - 1) expanded
            | none =>
                let args ←
                  args.mapM (expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel)
                pure (mkObjApp (.ident headName) args)
      | _ =>
          let head ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel head
          let args ←
            args.mapM (expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel)
          pure (mkObjApp head args)
  | .arrow x A B => do
      let A ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel B
      pure (.arrow (x.map Name.eraseMacroScopes) A B)
  | .funArrow x A B => do
      let A ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel B
      pure (.funArrow (x.map Name.eraseMacroScopes) A B)
  | .sigma x A B => do
      let A ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      let B ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel B
      pure (.sigma (x.map Name.eraseMacroScopes) A B)
  | .pair a b => do
      pure (.pair (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel a)
        (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel b))
  | .fst e => do
      pure (.fst (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel e))
  | .snd e => do
      pure (.snd (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel e))
  | .lam xs body => do
      let clean := xs.map Name.eraseMacroScopes
      let locals := clean.foldl (fun locals x => locals.insert x) locals
      pure (.lam clean (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel
        body))
  | .jeq lhs rhs => do
      pure (.jeq (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel lhs)
        (← expandSyntaxAbbrevsInExpr sig ownerKind ownerName where_ locals fuel rhs))

/-- Expand syntax abbreviations in a metadata binder telescope. -/
def expandSyntaxAbbrevsInBindings (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (bs : Array HLBinding) : CoreM (Array HLBinding) := do
  let mut out := #[]
  let mut locals : NameSet := {}
  for b in bs do
    let typeExpr ← expandSyntaxAbbrevsInExpr sig ownerKind ownerName
      s!"parameter '{b.name.eraseMacroScopes}' type" locals (lfAbbrevExpansionFuel sig) b.typeExpr
    let b := { b with name := b.name.eraseMacroScopes, typeExpr }
    out := out.push b
    locals := locals.insert b.name.eraseMacroScopes
  pure out

/-- Expand syntax and judgment abbreviations throughout a high-level signature while keeping the
abbreviation metadata for diagnostics/templates. -/
def expandSyntaxAbbrevsInSignature (sig : HLSignature) : CoreM HLSignature := do
  let syntaxAbbrevs ← sig.syntaxAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sig "syntax_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sig "syntax_abbrev" a.name "value" locals
        (lfAbbrevExpansionFuel sig) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let judgmentAbbrevs ← sig.judgmentAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sig "judgment_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sig "judgment_abbrev" a.name "value" locals
        (lfAbbrevExpansionFuel sig) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let sigForRest := { sig with syntaxAbbrevs, judgmentAbbrevs }
  let syntaxDefs ← sigForRest.syntaxDefs.mapM fun d => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "syntax_def" d.name d.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value? ←
      d.value?.mapM (expandSyntaxAbbrevsInExpr sigForRest "syntax_def" d.name "value" locals
        (lfAbbrevExpansionFuel sigForRest))
    pure { d with name := d.name.eraseMacroScopes, params, value? }
  let sigForRest := { sigForRest with syntaxDefs }
  let syntaxSorts ← sigForRest.syntaxSorts.mapM fun s => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "syntax_sort" s.name s.params
    pure { s with name := s.name.eraseMacroScopes, params }
  let judgments ← sigForRest.judgments.mapM fun j => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "judgment" j.name j.params
    pure { j with name := j.name.eraseMacroScopes, params }
  let lfOpaqueConsts ← sigForRest.lfOpaqueConsts.mapM fun o => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "lf_opaque" o.name o.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let typeExpr? ←
      o.typeExpr?.mapM (expandSyntaxAbbrevsInExpr sigForRest "lf_opaque" o.name "result type"
        locals (lfAbbrevExpansionFuel sigForRest))
    pure { o with name := o.name.eraseMacroScopes, params, typeExpr? }
  let rules ← sigForRest.rules.mapM fun r => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "rule" r.name r.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let premises ← r.premises.mapM fun p => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name s!"premise '{p.name.eraseMacroScopes}'"
          locals (lfAbbrevExpansionFuel sigForRest) p.judgmentExpr
      pure { p with judgmentExpr }
    let sideConditions ← r.sideConditions.mapM fun sc => do
      let input ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name s!"side-condition \
          '{sc.name.eraseMacroScopes}'" locals (lfAbbrevExpansionFuel sigForRest) sc.input
      pure { sc with input }
    let paramEvidences ← r.paramEvidences.mapM fun ev => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"evidence '{ev.name.eraseMacroScopes}'" locals (lfAbbrevExpansionFuel sigForRest)
          ev.judgmentExpr
      pure { ev with judgmentExpr }
    let conclusionExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "rule" r.name "conclusion" locals
        (lfAbbrevExpansionFuel sigForRest) r.conclusionExpr
    pure {
      r with
      name := r.name.eraseMacroScopes
      params := params
      premises := premises
      sideConditions := sideConditions
      paramEvidences := paramEvidences
      conclusionExpr := conclusionExpr
    }
  let lfObjectDefs ← sigForRest.lfObjectDefs.mapM fun d => do
    let typeExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "type" {}
        (lfAbbrevExpansionFuel sigForRest) d.typeExpr
    let value ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "value" {}
        (lfAbbrevExpansionFuel sigForRest) d.value
    pure { d with name := d.name.eraseMacroScopes, typeExpr, value }
  let lfJudgmentTheorems ← sigForRest.lfJudgmentTheorems.mapM fun t => do
    let binders ← expandSyntaxAbbrevsInBindings sigForRest "judgment_theorem" t.name t.binders
    let locals := binders.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let judgmentExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "statement" locals
        (lfAbbrevExpansionFuel sigForRest) t.judgmentExpr
    let proof ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "proof" locals
        (lfAbbrevExpansionFuel sigForRest) t.proof
    pure { t with name := t.name.eraseMacroScopes, binders, judgmentExpr, proof }
  pure { sigForRest with
    syntaxSorts := syntaxSorts
    syntaxDefs := syntaxDefs
    judgmentAbbrevs := judgmentAbbrevs
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    modelSections := sigForRest.modelSections.map (fun s => { s with name :=
      s.name.eraseMacroScopes })
    modelSectionMemberships := sigForRest.modelSectionMemberships.map (fun m =>
      { m with sectionName := m.sectionName.eraseMacroScopes, declName :=
      m.declName.eraseMacroScopes })
    rules := rules
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

/-- Type information for global object constants that can be used as LF constructors in
shallow metadata checks. -/
structure LFGlobalTypeInfo where
  /-- Explicit parameter telescope of the global constant. -/
  binders : Array HLBinding := #[]
  /-- Result type of the global constant. -/
  typeExpr : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Convert a rule premise to a proof/evidence binder for shallow type lookup. -/
def rulePremiseAsTypeInfoBinder (p : RulePremiseDecl) : HLBinding :=
  { name := p.name.eraseMacroScopes, typeExpr := p.judgmentExpr, visibility := .explicit }

/-- Map-based lookup data for repeated LF expression checks in one signature. -/
structure LFCheckLookupContext where
  /-- Typed global object constructors, normally typed LF opaques. -/
  globalTypeInfos : NameMap LFGlobalTypeInfo := {}
  /-- Rule and theorem proof constants. -/
  proofTypeInfos : NameMap LFGlobalTypeInfo := {}
  /-- Source LF object-definition and syntax-definition result types. -/
  lfObjectDefTypes : LFLocalTypes := {}
  /-- Checked LF object-definition values, unfolded only as a conversion fallback. -/
  lfDefinitionValues : LFDefinitionValueMap := {}
  /-- Checked syntax-definition values, unfolded only as a conversion fallback. -/
  lfSyntaxDefValues : LFDefinitionValueMap := {}
  /-- Syntax-sort declarations by erased name. -/
  syntaxSortDecls : NameMap SyntaxSortDecl := {}
  /-- Judgment declarations by erased name. -/
  judgmentDecls : NameMap JudgmentDecl := {}
  /-- Untyped LF opaque placeholders and their accepted arities. -/
  untypedOpaqueArities : NameMap (Array (Option Nat)) := {}
  deriving Inhabited

/-- Build map-based lookup data for repeated LF expression checks. -/
def mkLFCheckLookupContext (sig : HLSignature) : LFCheckLookupContext := Id.run do
  let mut globalTypeInfos : NameMap LFGlobalTypeInfo := {}
  let mut proofTypeInfos : NameMap LFGlobalTypeInfo := {}
  let mut lfObjectDefTypes : LFLocalTypes := {}
  let mut lfDefinitionValues : LFDefinitionValueMap := {}
  let mut syntaxSortDecls : NameMap SyntaxSortDecl := {}
  let mut judgmentDecls : NameMap JudgmentDecl := {}
  let mut untypedOpaqueArities : NameMap (Array (Option Nat)) := {}
  let mut lfSyntaxDefValues : LFDefinitionValueMap := {}
  for s in sig.syntaxSorts do
    let name := s.name.eraseMacroScopes
    unless syntaxSortDecls.contains name do
      syntaxSortDecls := syntaxSortDecls.insert name s
  for j in sig.judgments do
    let name := j.name.eraseMacroScopes
    unless judgmentDecls.contains name do
      judgmentDecls := judgmentDecls.insert name j
  for d in sig.syntaxDefs do
    let name := d.name.eraseMacroScopes
    unless lfObjectDefTypes.contains name do
      lfObjectDefTypes := lfObjectDefTypes.insert name (eraseObjExprScopes (syntaxDefTypeExpr d))
      if let some value := syntaxDefValueExpr? d then
        lfSyntaxDefValues := lfSyntaxDefValues.insert name (eraseObjExprScopes value)
  for o in sig.lfOpaqueConsts do
    let name := o.name.eraseMacroScopes
    match o.typeExpr? with
    | some typeExpr =>
        globalTypeInfos := globalTypeInfos.insert name { binders := o.params, typeExpr }
    | none =>
        let arities := match untypedOpaqueArities.find? name with
          | some arities => arities
          | none => #[]
        untypedOpaqueArities := untypedOpaqueArities.insert name (arities.push o.arity?)
  for r in sig.rules do
    let name := r.name.eraseMacroScopes
    proofTypeInfos := proofTypeInfos.insert name {
      binders := r.params ++ r.premises.map rulePremiseAsTypeInfoBinder
      typeExpr := r.conclusionExpr }
  for d in sig.lfObjectDefs do
    let name := d.name.eraseMacroScopes
    unless lfObjectDefTypes.contains name do
      lfObjectDefTypes := lfObjectDefTypes.insert name (eraseObjExprScopes d.typeExpr)
      lfDefinitionValues := lfDefinitionValues.insert name (eraseObjExprScopes d.value)
  for t in sig.lfJudgmentTheorems do
    let name := t.name.eraseMacroScopes
    proofTypeInfos := proofTypeInfos.insert name {
      binders := t.binders
      typeExpr := t.judgmentExpr }
  return {
    globalTypeInfos := globalTypeInfos
    proofTypeInfos := proofTypeInfos
    lfObjectDefTypes := lfObjectDefTypes
    lfDefinitionValues := lfDefinitionValues
    lfSyntaxDefValues := lfSyntaxDefValues
    syntaxSortDecls := syntaxSortDecls
    judgmentDecls := judgmentDecls
    untypedOpaqueArities := untypedOpaqueArities }

/-- Map-based typed global constructor lookup. -/
def findLFGlobalTypeInfoIn? (lookup : LFCheckLookupContext) (name : Name) :
    Option LFGlobalTypeInfo :=
  lookup.globalTypeInfos.find? name.eraseMacroScopes

/-- Map-based rule/theorem proof-constant lookup. -/
def findLFProofTypeInfoIn? (lookup : LFCheckLookupContext) (name : Name) :
    Option LFGlobalTypeInfo :=
  lookup.proofTypeInfos.find? name.eraseMacroScopes

/-- Map-based type lookup used by shallow inference, including proof constants. -/
def findLFInferableTypeInfoIn? (lookup : LFCheckLookupContext) (name : Name) :
    Option LFGlobalTypeInfo :=
  match findLFGlobalTypeInfoIn? lookup name with
  | some info => some info
  | none => findLFProofTypeInfoIn? lookup name

/-- Map-based syntax-sort lookup. -/
def findSyntaxSortDeclIn? (lookup : LFCheckLookupContext) (name : Name) :
    Option SyntaxSortDecl :=
  lookup.syntaxSortDecls.find? name.eraseMacroScopes

/-- Map-based judgment lookup. -/
def findJudgmentDeclIn? (lookup : LFCheckLookupContext) (name : Name) : Option JudgmentDecl :=
  lookup.judgmentDecls.find? name.eraseMacroScopes

/-- LF-definition values including lazily unfolded checked syntax definitions. -/
def lfDefinitionValuesWithSyntaxDefs (lookup : LFCheckLookupContext) : LFDefinitionValueMap :=
  Id.run do
  let mut out := lookup.lfDefinitionValues
  for (n, value) in lookup.lfSyntaxDefValues.toList do
    out := out.insert n value
  return out

/-- Normalized pair plus whether the compact beta/eta-only path accepted it. -/
structure LFTypeComparisonNormalizationResult where
  actual : ObjExpr
  expected : ObjExpr
  compactSucceeded : Bool
  deriving Inhabited, Repr, BEq

/-- Normalize a pair, unfolding checked LF and syntax definitions only after compact mismatch. -/
def normalizeLFTypeComparisonPairInLookupDetailed (lookup : LFCheckLookupContext)
    (actual expected : ObjExpr) : LFTypeComparisonNormalizationResult :=
  let actualCheap := normalizeLFExprForTypeComparisonWithDefs {} actual
  let expectedCheap := normalizeLFExprForTypeComparisonWithDefs {} expected
  if lfExprAlphaEq actualCheap expectedCheap then
    { actual := actualCheap, expected := expectedCheap, compactSucceeded := true }
  else
    let defs := lfDefinitionValuesWithSyntaxDefs lookup
    if defs.isEmpty then
      { actual := actualCheap, expected := expectedCheap, compactSucceeded := false }
    else
      { actual := normalizeLFExprForTypeComparisonWithDefs defs actual
        expected := normalizeLFExprForTypeComparisonWithDefs defs expected
        compactSucceeded := false }

/-- Normalize a pair for diagnostics, unfolding checked LF and syntax definitions only if the
beta/eta-only compact normal forms do not already match. -/
def normalizeLFTypeComparisonPairInLookup (lookup : LFCheckLookupContext)
    (actual expected : ObjExpr) : ObjExpr × ObjExpr :=
  let result := normalizeLFTypeComparisonPairInLookupDetailed lookup actual expected
  (result.actual, result.expected)

/-- Shallow beta/eta type comparison using the lookup context's LF-definition map. Checked LF and
syntax definitions are unfolded only as a fallback after compact comparison fails. -/
def lfTypeCompareEqInLookup (lookup : LFCheckLookupContext) (actual expected : ObjExpr) : Bool :=
  let (actualN, expectedN) := normalizeLFTypeComparisonPairInLookup lookup actual expected
  lfExprAlphaEq actualN expectedN

/-- Optional owner metadata for LF conversion-profile lines. -/
structure LFConversionProfileOwner where
  theoryName : Option Name := none
  ownerKind : Option String := none
  ownerName : Option Name := none
  deriving Inhabited, Repr, BEq

/-- One bounded diagnostic summary for a conversion or unfolding check. -/
structure LFConversionProfileEntry where
  site : String
  owner : LFConversionProfileOwner := {}
  actualHead? : Option Name := none
  expectedHead? : Option Name := none
  actualSize : Nat := 0
  expectedSize : Nat := 0
  normalizedActualSize? : Option Nat := none
  normalizedExpectedSize? : Option Nat := none
  elapsedMs? : Option Nat := none
  compactSucceeded : Bool := false
  fullUnfoldFallback : Bool := false
  accepted : Bool := true
  unfoldedCounts : NameMap Nat := {}
  deriving Inhabited, Repr

/-- Render optional owner metadata for a conversion-profile line. -/
def renderLFConversionProfileOwner (owner : LFConversionProfileOwner) : String :=
  let theory := match owner.theoryName with | some n => toString n | none => "-"
  let kind := owner.ownerKind.getD "-"
  let name := match owner.ownerName with | some n => toString n | none => "-"
  s!"theory={theory}, owner={kind}:{name}"

/-- Render a compact name-count list for conversion-profile lines. -/
def renderLFConversionNameCounts (counts : NameMap Nat) : String :=
  let items := counts.toList
  if items.isEmpty then
    "none"
  else
    let items := items.take 8 |>.map fun (n, count) => s!"{n}:{count}"
    String.intercalate ", " items

/-- Maximum size growth observed by a conversion-profile entry. -/
def LFConversionProfileEntry.maxSizeGrowth (entry : LFConversionProfileEntry) : Nat :=
  let actualGrowth := match entry.normalizedActualSize? with
    | some n => n / (Nat.max 1 entry.actualSize)
    | none => 0
  let expectedGrowth := match entry.normalizedExpectedSize? with
    | some n => n / (Nat.max 1 entry.expectedSize)
    | none => 0
  Nat.max actualGrowth expectedGrowth

/-- Render one bounded conversion-profile entry. -/
def renderLFConversionProfileEntry (entry : LFConversionProfileEntry) : String :=
  let actualHead := entry.actualHead?.map toString |>.getD "-"
  let expectedHead := entry.expectedHead?.map toString |>.getD "-"
  let actualNorm := entry.normalizedActualSize?.map toString |>.getD "-"
  let expectedNorm := entry.normalizedExpectedSize?.map toString |>.getD "-"
  let elapsed := entry.elapsedMs?.map (fun n => s!"{n}ms") |>.getD "-"
  s!"LF conversion profile site={entry.site}, {renderLFConversionProfileOwner entry.owner}, " ++
    s!"heads={actualHead}/{expectedHead}, sizes={entry.actualSize}/{entry.expectedSize}, " ++
    s!"normalized_sizes={actualNorm}/{expectedNorm}, elapsed={elapsed}, " ++
    s!"compact={entry.compactSucceeded}, fallback={entry.fullUnfoldFallback}, " ++
    s!"accepted={entry.accepted}, unfolded={renderLFConversionNameCounts entry.unfoldedCounts}"

/-- Log a conversion-profile entry when profiling or fallback tracing requests it. -/
def logLFConversionProfileEntry (entry : LFConversionProfileEntry) : CoreM Unit := do
  let profile ← getBoolOption `internalLean.conversion.profile
  let traceFallbacks ← getBoolOption `internalLean.conversion.traceFallbacks
  let slowThreshold ← getNatOption `internalLean.conversion.slowThresholdMs 50
  let growthThreshold ← getNatOption `internalLean.conversion.sizeGrowthThreshold 10
  let slow := match entry.elapsedMs? with
    | some ms => slowThreshold > 0 && ms >= slowThreshold
    | none => false
  let growth := growthThreshold > 0 && entry.maxSizeGrowth >= growthThreshold
  if profile || (traceFallbacks && (entry.fullUnfoldFallback || slow || growth)) then
    logInfo m!"{renderLFConversionProfileEntry entry}"

/-- Acceptedness for the current cheap-then-full LF-definition comparison policy. -/
def lfDefinitionComparisonAccepted (defs : LFDefinitionValueMap) (locals : NameSet)
    (actual expected : ObjExpr) : Bool :=
  let actual := eraseObjExprScopes actual
  let expected := eraseObjExprScopes expected
  if lfExprAlphaEq actual expected then
    true
  else
    let actualCheap := normalizeLFExprForConversionWithLocals {} locals actual
    let expectedCheap := normalizeLFExprForConversionWithLocals {} locals expected
    if lfExprAlphaEq actualCheap expectedCheap then
      true
    else
      lfExprAlphaEq (normalizeLFExprForConversionWithLocals defs locals actual)
        (normalizeLFExprForConversionWithLocals defs locals expected)

/-- Build a diagnostic entry for the current cheap-then-full comparison policy. -/
def lfDefinitionComparisonProfileEntry (site : String) (owner : LFConversionProfileOwner)
    (defs : LFDefinitionValueMap) (locals : NameSet) (actual expected : ObjExpr)
    (elapsedMs? : Option Nat := none) : LFConversionProfileEntry :=
  let actual := eraseObjExprScopes actual
  let expected := eraseObjExprScopes expected
  let alphaSucceeded := lfExprAlphaEq actual expected
  let actualCheap := normalizeLFExprForConversionWithLocals {} locals actual
  let expectedCheap := normalizeLFExprForConversionWithLocals {} locals expected
  let compactSucceeded := alphaSucceeded || lfExprAlphaEq actualCheap expectedCheap
  let fallbackRan := !compactSucceeded
  let (accepted, normActual?, normExpected?, counts) :=
    if fallbackRan then
      let actualFull := normalizeLFExprForConversionWithLocals defs locals actual
      let expectedFull := normalizeLFExprForConversionWithLocals defs locals expected
      let counts :=
        mergeLFConversionNameCounts (countLFDefinitionUnfolds defs locals actual)
          (countLFDefinitionUnfolds defs locals expected)
      (lfExprAlphaEq actualFull expectedFull, some (objExprNodeCount actualFull),
        some (objExprNodeCount expectedFull), counts)
    else
      (true, none, none, {})
  {
    site, owner
    actualHead? := lfExprHeadIdent? actual
    expectedHead? := lfExprHeadIdent? expected
    actualSize := objExprNodeCount actual
    expectedSize := objExprNodeCount expected
    normalizedActualSize? := normActual?
    normalizedExpectedSize? := normExpected?
    elapsedMs?, compactSucceeded, fullUnfoldFallback := fallbackRan
    accepted, unfoldedCounts := counts }

/-- Profile one source-level LF-definition comparison without changing acceptance. -/
def lfExprEqModuloDefinitionsWithLocalsProfiled (site : String)
    (owner : LFConversionProfileOwner) (defs : LFDefinitionValueMap) (locals : NameSet)
    (actual expected : ObjExpr) : CoreM Bool := do
  let profile ← getBoolOption `internalLean.conversion.profile
  let traceFallbacks ← getBoolOption `internalLean.conversion.traceFallbacks
  if profile || traceFallbacks then
    let start ← IO.monoMsNow
    let entry := lfDefinitionComparisonProfileEntry site owner defs locals actual expected
    let stop ← IO.monoMsNow
    let entry := { entry with elapsedMs? := some (stop - start) }
    logLFConversionProfileEntry entry
    pure entry.accepted
  else
    pure <| lfDefinitionComparisonAccepted defs locals actual expected

/-- Profile a lookup type-comparison pair without changing the returned normalized pair. -/
def normalizeLFTypeComparisonPairInLookupProfiled (site : String)
    (owner : LFConversionProfileOwner) (lookup : LFCheckLookupContext)
    (actual expected : ObjExpr) : CoreM (ObjExpr × ObjExpr) := do
  let profile ← getBoolOption `internalLean.conversion.profile
  let traceFallbacks ← getBoolOption `internalLean.conversion.traceFallbacks
  if profile || traceFallbacks then
    let start ← IO.monoMsNow
    let result := normalizeLFTypeComparisonPairInLookupDetailed lookup actual expected
    let stop ← IO.monoMsNow
    let actual := eraseObjExprScopes actual
    let expected := eraseObjExprScopes expected
    let defs := lfDefinitionValuesWithSyntaxDefs lookup
    let fallbackRan := !result.compactSucceeded
    let counts :=
      if fallbackRan then
        mergeLFConversionNameCounts (countLFDefinitionUnfolds defs {} actual)
          (countLFDefinitionUnfolds defs {} expected)
      else
        {}
    let entry : LFConversionProfileEntry := {
      site, owner
      actualHead? := lfExprHeadIdent? actual
      expectedHead? := lfExprHeadIdent? expected
      actualSize := objExprNodeCount actual
      expectedSize := objExprNodeCount expected
      normalizedActualSize? := some (objExprNodeCount result.actual)
      normalizedExpectedSize? := some (objExprNodeCount result.expected)
      elapsedMs? := some (stop - start)
      compactSucceeded := result.compactSucceeded
      fullUnfoldFallback := fallbackRan
      accepted := lfExprAlphaEq result.actual result.expected
      unfoldedCounts := counts }
    logLFConversionProfileEntry entry
    pure (result.actual, result.expected)
  else
    pure <| normalizeLFTypeComparisonPairInLookup lookup actual expected

/-- Infer a shallow LF/object type using a reusable lookup context.

This handles local/LF-definition identifiers from `knownTypes` and global object constants with
explicit telescopes. It returns `none` for untyped opaque placeholders and other untyped staging
heads. -/
partial def inferKnownLFExprTypeWithLookup? (lookup : LFCheckLookupContext)
    (knownTypes : LFLocalTypes) : ObjExpr → Option ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      match knownTypes.find? n with
      | some typeExpr => some typeExpr
      | none =>
          match findLFInferableTypeInfoIn? lookup n with
          | some info =>
              if info.binders.isEmpty then some (eraseObjExprScopes info.typeExpr) else none
          | none =>
              match lookup.lfObjectDefTypes.find? n with
              | some typeExpr => some (eraseObjExprScopes typeExpr)
              | none =>
                  match findSyntaxSortDeclIn? lookup n with
                  | some s =>
                      if s.params.isEmpty then some (objExprTypeOfLevel s.resultLevel) else none
                  | none =>
                      match findJudgmentDeclIn? lookup n with
                      | some j => if j.params.isEmpty then some .sort else none
                      | none => none
  | .sort | .univ _ | .arrow .. | .funArrow .. | .sigma .. | .pair .. | .lam .. => none
  | .jeq .. => none
  | .fst e => do
      match inferKnownLFExprTypeWithLookup? lookup knownTypes e with
      | some (.sigma _ A _) => some (eraseObjExprScopes A)
      | _ => none
  | .snd e => do
      match inferKnownLFExprTypeWithLookup? lookup knownTypes e with
      | some (.sigma binder? _ B) =>
          let B := match binder? with
            | some x => substSingleLFParam x (.fst (eraseObjExprScopes e)) B
            | none => B
          some (eraseObjExprScopes B)
      | _ => none
  | e@(.app f a) =>
      match inferKnownLFExprTypeWithLookup? lookup knownTypes f with
      | some (.arrow binder? expected result) | some (.funArrow binder? expected result) =>
          match inferKnownLFExprTypeWithLookup? lookup knownTypes a with
          | some actual =>
              if !lfTypeCompareEqInLookup lookup actual expected then
                none
              else
                let result := match binder? with
                  | some x => substSingleLFParam x (eraseObjExprScopes a) result
                  | none => result
                some (eraseObjExprScopes result)
          | none =>
              let result := match binder? with
                | some x => substSingleLFParam x (eraseObjExprScopes a) result
                | none => result
              some (eraseObjExprScopes result)
      | _ =>
          match splitObjApp e with
          | (.ident head, args) =>
              let head := head.eraseMacroScopes
              let typeExpr? := match knownTypes.find? head with
                | some typeExpr => some typeExpr
                | none => lookup.lfObjectDefTypes.find? head
              match typeExpr? with
              | some typeExpr => Id.run do
                  let mut current := eraseObjExprScopes typeExpr
                  let mut ok := true
                  for arg in args do
                    match current with
                    | .arrow binder? expected result | .funArrow binder? expected result =>
                        match inferKnownLFExprTypeWithLookup? lookup knownTypes arg with
                        | some actual =>
                            if !lfTypeCompareEqInLookup lookup actual expected then
                              ok := false
                        | none => pure ()
                        current := match binder? with
                          | some x => substSingleLFParam x (eraseObjExprScopes arg) result
                          | none => result
                    | _ => ok := false
                  if ok then some (eraseObjExprScopes current) else none
              | none =>
                  match findSyntaxSortDeclIn? lookup head with
                  | some s =>
                      if args.size == s.params.size then
                        some (objExprTypeOfLevel s.resultLevel)
                      else
                        none
                  | none =>
                      match findJudgmentDeclIn? lookup head with
                      | some j =>
                          if args.size == j.params.size then some .sort else none
                      | none =>
                          match findLFInferableTypeInfoIn? lookup head with
                          | none => none
                          | some info =>
                              if args.size != info.binders.size then
                                none
                              else Id.run do
                                let mut subst : NameMap ObjExpr := {}
                                let mut ok := true
                                for b in info.binders, arg in args do
                                  let expected := eraseObjExprScopes (substLFParams subst
                                    b.typeExpr)
                                  match inferKnownLFExprTypeWithLookup? lookup knownTypes arg with
                                  | some actual =>
                                      if !lfTypeCompareEqInLookup lookup actual expected then
                                        ok := false
                                  | none => pure ()
                                  subst := subst.insert b.name.eraseMacroScopes
                                    (eraseObjExprScopes arg)
                                if ok then
                                  return some (eraseObjExprScopes (substLFParams subst
                                    info.typeExpr))
                                else
                                  return none
          | _ => none

/-- Infer a shallow LF/object type for expressions whose head has known type metadata. -/
def inferKnownLFExprType? (sig : HLSignature) (knownTypes : LFLocalTypes) (e : ObjExpr) :
    Option ObjExpr :=
  inferKnownLFExprTypeWithLookup? (mkLFCheckLookupContext sig) knownTypes e

/-- Truncate diagnostic text to a fixed character budget. -/
def truncateDiagnosticString (maxChars : Nat) (s : String) : String :=
  let chars := s.toList
  if chars.length ≤ maxChars then
    s
  else
    String.ofList (chars.take maxChars) ++ "..."

/-- Source-ish, depth-limited rendering for high-level object expressions. -/
partial def objExprSourceStringWithDepth : Nat → ObjExpr → String
  | 0, _ => "..."
  | _ + 1, .ident n => toString n.eraseMacroScopes
  | _ + 1, .sort => "Type"
  | _ + 1, .univ .zero => "Type"
  | _ + 1, .univ u => s!"Type {u}"
  | depth + 1, .app f a =>
      s!"({objExprSourceStringWithDepth depth f} {objExprSourceStringWithDepth depth a})"
  | depth + 1, .arrow none A B =>
      s!"({objExprSourceStringWithDepth depth A} ⇒ {objExprSourceStringWithDepth depth B})"
  | depth + 1, .arrow (some x) A B =>
      s!"(({x.eraseMacroScopes} : {objExprSourceStringWithDepth depth A}) ⇒ " ++
        s!"{objExprSourceStringWithDepth depth B})"
  | depth + 1, .funArrow none A B =>
      s!"({objExprSourceStringWithDepth depth A} → {objExprSourceStringWithDepth depth B})"
  | depth + 1, .funArrow (some x) A B =>
      s!"(({x.eraseMacroScopes} : {objExprSourceStringWithDepth depth A}) → " ++
        s!"{objExprSourceStringWithDepth depth B})"
  | depth + 1, .sigma none A B =>
      s!"({objExprSourceStringWithDepth depth A} × {objExprSourceStringWithDepth depth B})"
  | depth + 1, .sigma (some x) A B =>
      s!"(Σ {x.eraseMacroScopes} : {objExprSourceStringWithDepth depth A}, " ++
        s!"{objExprSourceStringWithDepth depth B})"
  | depth + 1, .pair a b =>
      s!"⟨{objExprSourceStringWithDepth depth a}, {objExprSourceStringWithDepth depth b}⟩"
  | depth + 1, .fst e => s!"(Sigma.fst {objExprSourceStringWithDepth depth e})"
  | depth + 1, .snd e => s!"(Sigma.snd {objExprSourceStringWithDepth depth e})"
  | depth + 1, .lam xs body =>
      let binders := String.intercalate " " (xs.toList.map (fun x => toString x.eraseMacroScopes))
      s!"(fun {binders} => {objExprSourceStringWithDepth depth body})"
  | depth + 1, .jeq lhs rhs =>
      s!"({objExprSourceStringWithDepth depth lhs} ≡ " ++
        s!"{objExprSourceStringWithDepth depth rhs})"

/-- Maximum object-expression size rendered with the full recursive `ToString` instance. -/
def diagnosticObjExprFullRenderNodeLimit : Nat := 120

/-- Depth used when an object expression is too large for full diagnostic rendering. -/
def diagnosticObjExprLargeRenderDepth : Nat := 8

/-- Budgeted object-expression rendering for diagnostics that avoids rendering huge full terms. -/
def diagnosticObjExprStringWithBudget (maxChars : Nat) (e : ObjExpr) : String :=
  let nodes := objExprNodeCount e
  if nodes ≤ diagnosticObjExprFullRenderNodeLimit then
    truncateDiagnosticString maxChars (toString e)
  else
    let head := (lfExprHeadIdent? e).map (fun n => toString n.eraseMacroScopes) |>.getD "-"
    let rendered := objExprSourceStringWithDepth diagnosticObjExprLargeRenderDepth e
    let summary := s!"[truncated diagnostic rendering; nodes={nodes}; head={head}] {rendered}"
    truncateDiagnosticString maxChars summary

/-- Default budgeted object-expression rendering for diagnostics. -/
def diagnosticObjExprString (e : ObjExpr) : String :=
  diagnosticObjExprStringWithBudget 600 e

/-- Shorter one-line object-expression rendering for nested mismatch diagnostics. -/
def diagnosticObjExprShortString (e : ObjExpr) : String :=
  diagnosticObjExprStringWithBudget 240 e

/-- Match a rigid object-expression pattern, solving only the listed implicit variables. -/
partial def matchImplicitObjectPattern (vars : NameSet) (pattern actual : ObjExpr)
    (subst : NameMap ObjExpr) : Except String (NameMap ObjExpr) := do
  let pattern := eraseObjExprScopes pattern
  let actual := eraseObjExprScopes actual
  match pattern with
  | .ident n =>
      let key := n.eraseMacroScopes
      if vars.contains key then
        match subst.find? key with
        | some old =>
            if old == actual then
              pure subst
            else
              throw s!"implicit parameter '{key}' is constrained to both \
                '{diagnosticObjExprString old}' and '{diagnosticObjExprString actual}'"
        | none => pure (subst.insert key actual)
      else if pattern == actual then
        pure subst
      else
        throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .sort | .univ _ =>
      if pattern == actual then pure subst else throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .app pf pa =>
      match actual with
      | .app af aa =>
          let subst ← matchImplicitObjectPattern vars pf af subst
          matchImplicitObjectPattern vars pa aa subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .arrow px pA pB =>
      match actual with
      | .arrow ax aA aB | .funArrow ax aA aB =>
          if px.map Name.eraseMacroScopes != ax.map Name.eraseMacroScopes then
            throw s!"binder names do not match while inferring implicits: expected '{px}', got \
              '{ax}'"
          let subst ← matchImplicitObjectPattern vars pA aA subst
          matchImplicitObjectPattern vars pB aB subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .funArrow px pA pB =>
      match actual with
      | .arrow ax aA aB | .funArrow ax aA aB =>
          if px.map Name.eraseMacroScopes != ax.map Name.eraseMacroScopes then
            throw s!"binder names do not match while inferring implicits: expected '{px}', got \
              '{ax}'"
          let subst ← matchImplicitObjectPattern vars pA aA subst
          matchImplicitObjectPattern vars pB aB subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .sigma px pA pB =>
      match actual with
      | .sigma ax aA aB =>
          if px.map Name.eraseMacroScopes != ax.map Name.eraseMacroScopes then
            throw s!"binder names do not match while inferring implicits: expected '{px}', got \
              '{ax}'"
          let subst ← matchImplicitObjectPattern vars pA aA subst
          matchImplicitObjectPattern vars pB aB subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .pair pa pb =>
      match actual with
      | .pair aa ab =>
          let subst ← matchImplicitObjectPattern vars pa aa subst
          matchImplicitObjectPattern vars pb ab subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .fst pe =>
      match actual with
      | .fst ae => matchImplicitObjectPattern vars pe ae subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .snd pe =>
      match actual with
      | .snd ae => matchImplicitObjectPattern vars pe ae subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .lam pxs pbody =>
      match actual with
      | .lam axs abody =>
          if pxs.map Name.eraseMacroScopes != axs.map Name.eraseMacroScopes then
            throw s!"lambda binders do not match while inferring implicits"
          matchImplicitObjectPattern vars pbody abody subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"
  | .jeq pl pr =>
      match actual with
      | .jeq al ar =>
          let subst ← matchImplicitObjectPattern vars pl al subst
          matchImplicitObjectPattern vars pr ar subst
      | _ => throw s!"rigid expressions do not match: expected \
          '{diagnosticObjExprString pattern}', got '{diagnosticObjExprString actual}'"

end InternalLean
