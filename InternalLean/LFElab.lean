/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Registry

/-!
# LF elaboration and checking for user-declared type theories

This file contains frontend expansion, direct-LF metadata checking, LF-definition unfolding,
and replay lowering.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean


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

/-- Return whether a flattened signature has the constants for a future object-level
`FunctionCore` expansion mode. The current surface keeps `→` as structural compatibility syntax. -/
def hasFunctionCoreSurface (sig : HLSignature) : Bool :=
  let contains (n : Name) : Bool :=
    sig.lfOpaqueConsts.any (fun d => d.name == n) ||
      sig.lfObjectDefs.any (fun d => d.name == n) ||
      sig.lfJudgmentTheorems.any (fun t => t.name == n)
  contains `Fun && contains `lam && contains `app

/-- Elaborate source `→` arrows through `FunctionCore.Fun` for a future explicit expansion mode.

The current checker does not call this helper: both `→` and `⇒` remain structural/framework arrows
for compatibility with existing direct-LF theories. -/
partial def expandSurfaceFunctionsInExpr (sig : HLSignature) (e : ObjExpr) : CoreM ObjExpr := do
  let rec go : ObjExpr → CoreM ObjExpr
    | .ident n => pure (.ident n)
    | .sort => pure .sort
    | .univ u => pure (.univ u)
    | .app f a => return .app (← go f) (← go a)
    | .arrow x A B => return .arrow x (← go A) (← go B)
    | .funArrow x A B => do
        unless hasFunctionCoreSurface sig do
          throwError "surface function arrow '→' requires FunctionCore; use explicit structural \
            arrow '⇒' for framework-level arities"
        let A ← go A
        let binder := x.getD `_
        let B ← go B
        pure (.app (.app (.ident `Fun) A) (.lam #[binder] B))
    | .lam xs body => return .lam xs (← go body)
    | .jeq lhs rhs => return .jeq (← go lhs) (← go rhs)
  go e

/-- Elaborate surface function notation in a binder type. -/
def expandSurfaceFunctionsInBinding (sig : HLSignature) (b : HLBinding) : CoreM HLBinding := do
  return { b with typeExpr := (← expandSurfaceFunctionsInExpr sig b.typeExpr) }

/-- Expand theory-local object macros in a binder. -/
def expandObjectMacrosInBinding (sig : HLSignature) (b : HLBinding) : CoreM HLBinding := do
  return { b with typeExpr := (← expandObjectMacrosInExpr sig b.typeExpr) }

/-- Named checkpoint for source-level surface function notation.

Today this intentionally preserves `→` as the structural/function-family arrow. If a future mode
expands through `FunctionCore`, it should happen here before checker validation. -/
def expandSurfaceFunctionsInSignature (sig : HLSignature) : CoreM HLSignature :=
  pure sig

/-- Return whether a name is already used directly in a high-level signature. -/
def HLSignature.containsName (sig : HLSignature) (n : Name) : Bool :=
  sig.syntaxSorts.any (fun d => d.name == n) || sig.syntaxAbbrevs.any (fun d => d.name == n) ||
    sig.contextZones.any (fun d => d.name == n) || sig.binderClasses.any (fun d => d.name == n) ||
    sig.judgments.any (fun d => d.name == n) || sig.rules.any (fun d => d.name == n) ||
    sig.sideConditionSolvers.any (fun d => d.name == n) ||
    sig.conversionPlugins.any (fun d => d.name == n) ||
    sig.lfOpaqueConsts.any (fun d => d.name == n) ||
    sig.lfObjectDefs.any (fun d => d.name == n) || sig.lfJudgmentTheorems.any (fun d => d.name == n)

/-- Flatten a signature's parent theories before its own declarations.

This concatenates parent declarations/definitions/theorems into the child signature and keeps the
child's name. It rejects parent cycles; namespacing and selective imports are intentionally left to
future extensions. -/
partial def flattenSignature (sig : HLSignature) (seen : NameSet := {}) : CoreM HLSignature := do
  if seen.contains sig.name then
    throwError "cyclic type-theory extension involving '{sig.name}'"
  let seen := seen.insert sig.name
  let mut syntaxSorts := #[]
  let mut syntaxAbbrevs := #[]
  let mut syntaxSortRoles := #[]
  let mut contextZones := #[]
  let mut binderClasses := #[]
  let mut judgments := #[]
  let mut judgmentRoles := #[]
  let mut rules := #[]
  let mut ruleRoles := #[]
  let mut rewriteRelations := #[]
  let mut rewriteSymmetries := #[]
  let mut rewriteCongruences := #[]
  let mut transportRules := #[]
  let mut transportPositions := #[]
  let mut sideConditionSolvers := #[]
  let mut conversionPlugins := #[]
  let mut lfOpaqueConsts := #[]
  let mut modelVisibilities := #[]
  let mut modelSections := #[]
  let mut modelSectionMemberships := #[]
  let mut lfObjectDefs := #[]
  let mut lfJudgmentTheorems := #[]
  let mut macros := #[]
  let mut roles := #[]
  let mut levelParams := #[]
  for parentName in sig.parents do
    let some parent ← getTheory? parentName
      | throwError "unknown parent type theory '{parentName}' for '{sig.name}'"
    let parentFlat ← flattenSignature parent seen
    syntaxSorts := syntaxSorts ++ parentFlat.syntaxSorts
    syntaxAbbrevs := syntaxAbbrevs ++ parentFlat.syntaxAbbrevs
    syntaxSortRoles := syntaxSortRoles ++ parentFlat.syntaxSortRoles
    contextZones := contextZones ++ parentFlat.contextZones
    binderClasses := binderClasses ++ parentFlat.binderClasses
    judgments := judgments ++ parentFlat.judgments
    judgmentRoles := judgmentRoles ++ parentFlat.judgmentRoles
    rules := rules ++ parentFlat.rules
    ruleRoles := ruleRoles ++ parentFlat.ruleRoles
    rewriteRelations := rewriteRelations ++ parentFlat.rewriteRelations
    rewriteSymmetries := rewriteSymmetries ++ parentFlat.rewriteSymmetries
    rewriteCongruences := rewriteCongruences ++ parentFlat.rewriteCongruences
    transportRules := transportRules ++ parentFlat.transportRules
    transportPositions := transportPositions ++ parentFlat.transportPositions
    sideConditionSolvers := sideConditionSolvers ++ parentFlat.sideConditionSolvers
    conversionPlugins := conversionPlugins ++ parentFlat.conversionPlugins
    lfOpaqueConsts := lfOpaqueConsts ++ parentFlat.lfOpaqueConsts
    modelVisibilities := modelVisibilities ++ parentFlat.modelVisibilities
    modelSections := modelSections ++ parentFlat.modelSections
    modelSectionMemberships := modelSectionMemberships ++ parentFlat.modelSectionMemberships
    lfObjectDefs := lfObjectDefs ++ parentFlat.lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems ++ parentFlat.lfJudgmentTheorems
    macros := macros ++ parentFlat.macros
    roles := roles ++ parentFlat.roles
    levelParams := levelParams ++ parentFlat.levelParams
  return {
    name := sig.name
    parents := #[]
    levelParams := levelParams ++ sig.levelParams
    syntaxSorts := syntaxSorts ++ sig.syntaxSorts
    syntaxAbbrevs := syntaxAbbrevs ++ sig.syntaxAbbrevs
    syntaxSortRoles := syntaxSortRoles ++ sig.syntaxSortRoles
    contextZones := contextZones ++ sig.contextZones
    binderClasses := binderClasses ++ sig.binderClasses
    judgments := judgments ++ sig.judgments
    judgmentRoles := judgmentRoles ++ sig.judgmentRoles
    rules := rules ++ sig.rules
    ruleRoles := ruleRoles ++ sig.ruleRoles
    rewriteRelations := rewriteRelations ++ sig.rewriteRelations
    rewriteSymmetries := rewriteSymmetries ++ sig.rewriteSymmetries
    rewriteCongruences := rewriteCongruences ++ sig.rewriteCongruences
    transportRules := transportRules ++ sig.transportRules
    transportPositions := transportPositions ++ sig.transportPositions
    sideConditionSolvers := sideConditionSolvers ++ sig.sideConditionSolvers
    conversionPlugins := conversionPlugins ++ sig.conversionPlugins
    lfOpaqueConsts := lfOpaqueConsts ++ sig.lfOpaqueConsts
    modelVisibilities := modelVisibilities ++ sig.modelVisibilities
    modelSections := modelSections ++ sig.modelSections
    modelSectionMemberships := modelSectionMemberships ++ sig.modelSectionMemberships
    lfObjectDefs := lfObjectDefs ++ sig.lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems ++ sig.lfJudgmentTheorems
    macros := macros ++ sig.macros
    roles := roles ++ sig.roles }

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

/-- Check one LF metadata binder for undeclared universe-level parameters. -/
def checkDeclaredLevelParamsInLFBinding (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (b : HLBinding) : CoreM Unit :=
  checkDeclaredLevelParamsInLFExpr sig ownerKind ownerName
    s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr

/-- Reject nested LF binders that reuse an already-bound name. -/
def checkNoLFLocalBinderShadowingInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (e : ObjExpr) : CoreM Unit := do
  let rec go (locals : NameSet) (e : ObjExpr) : CoreM Unit := do
    match e with
    | .ident _ | .sort | .univ _ => pure ()
    | .app f a => go locals f *> go locals a
    | .arrow _ A B | .funArrow _ A B => do
        go locals A
        go locals B
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
  go {} e

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

/-- Check LF metadata for opt-in universe-level discipline. -/
def checkLFUniverseLevelMetadata (sig : HLSignature) : CoreM Unit := do
  checkNoDuplicateLevelParamsInSignature sig
  for s in sig.syntaxSorts do
    for b in s.params do
      checkDeclaredLevelParamsInLFBinding sig "syntax_sort" s.name b
  for a in sig.syntaxAbbrevs do
    for b in a.params do
      checkDeclaredLevelParamsInLFBinding sig "syntax_abbrev" a.name b
    checkDeclaredLevelParamsInLFExpr sig "syntax_abbrev" a.name "value" a.value
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
    | .arrow _ A B | .funArrow _ A B => go A *> go B
    | .lam _ body => go body
    | .jeq lhs rhs => go lhs *> go rhs
  go e

/-- Check a metadata telescope for declared syntax-sort application arities. -/
def checkSyntaxSortApplicationsInBindings (sig : HLSignature) (syntaxSortArities : NameMap Nat)
    (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) : CoreM Unit := do
  for b in bs do
    checkSyntaxSortApplicationsInExpr sig syntaxSortArities ownerKind ownerName
      s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr

/-- Collect globally known names for lightweight LF metadata expression validation. -/
def lfKnownGlobalNames (sig : HLSignature) : NameSet := Id.run do
  let mut known : NameSet := {}
  for s in sig.syntaxSorts do
    known := known.insert s.name.eraseMacroScopes
  for a in sig.syntaxAbbrevs do
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

/-- Opaque LF placeholder arities declared in a signature. -/
def lfOpaqueArities (sig : HLSignature) : NameMap (Option Nat) := Id.run do
  let mut arities : NameMap (Option Nat) := {}
  for o in sig.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
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

/-- Count leading framework function arrows in an LF object-definition type. -/
partial def lfFunctionTypeArity : ObjExpr → Nat
  | .arrow _ _ B | .funArrow _ _ B => lfFunctionTypeArity B + 1
  | _ => 0

/-- Return the result type after peeling leading framework function arrows. -/
partial def lfFunctionTypeResult : ObjExpr → ObjExpr
  | .arrow _ _ B | .funArrow _ _ B => lfFunctionTypeResult B
  | e => e

/-- Build the explicit framework function type for a binder-style `internal def`. -/
def mkInternalDefFunctionType (params : Array HLBinding) (result : ObjExpr) : ObjExpr :=
  params.foldr (init := result) fun b acc => .funArrow (some b.name) b.typeExpr acc

/-- Build the lambda body for a binder-style `internal def`. -/
def mkInternalDefLambda (params : Array HLBinding) (body : ObjExpr) : ObjExpr :=
  if params.isEmpty then body else .lam (params.map (·.name)) body

/-- Declared global LF heads together with their syntactic head class and optional arity. -/
def lfGlobalHeadInfo (sig : HLSignature) : NameMap (CheckedLFHeadKind × Option Nat) := Id.run do
  let mut heads : NameMap (CheckedLFHeadKind × Option Nat) := {}
  for s in sig.syntaxSorts do
    heads := heads.insert s.name.eraseMacroScopes (.syntaxSort, some s.params.size)
  for j in sig.judgments do
    heads := heads.insert j.name.eraseMacroScopes (.judgment, some j.params.size)
  for o in sig.lfOpaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
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

/-- User-facing label for a checked LF head kind. -/
def CheckedLFHeadKind.label : CheckedLFHeadKind → String
  | .local => "local"
  | .syntaxSort => "syntax_sort"
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
  | .lam xs body => .lam (xs.map Name.eraseMacroScopes) (eraseObjExprScopes body)
  | .jeq lhs rhs => .jeq (eraseObjExprScopes lhs) (eraseObjExprScopes rhs)

/-- Free object-level identifiers in an LF metadata expression. -/
partial def freeLFObjectIdentifiers : ObjExpr → NameSet
  | .ident n => ({} : NameSet).insert n.eraseMacroScopes
  | .sort | .univ _ => {}
  | .app f a => freeLFObjectIdentifiers f ++ freeLFObjectIdentifiers a
  | .arrow x A B | .funArrow x A B =>
      let free := freeLFObjectIdentifiers A ++ freeLFObjectIdentifiers B
      match x with
      | some x => free.erase x.eraseMacroScopes
      | none => free
  | .lam xs body =>
      let free := freeLFObjectIdentifiers body
      xs.foldl (fun free x => free.erase x.eraseMacroScopes) free
  | .jeq lhs rhs => freeLFObjectIdentifiers lhs ++ freeLFObjectIdentifiers rhs

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

/-- LF-definition values declared in a high-level signature, keyed by erased names. -/
def lfDefinitionValuesOfSignature (sig : HLSignature) : LFDefinitionValueMap := Id.run do
  let mut out : LFDefinitionValueMap := {}
  for d in sig.lfObjectDefs do
    out := out.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)
  return out

/-- Normalize an LF expression for shallow type comparisons. -/
def normalizeLFExprForTypeComparison (sig : HLSignature) (e : ObjExpr) : ObjExpr :=
  unfoldLFDefinitionsInExpr (lfDefinitionValuesOfSignature sig) e

/-- Shallow equality of LF types after beta-reduction and LF-definition unfolding. -/
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
def findJudgmentDecl? (sig : HLSignature) (name : Name) : Option JudgmentDecl := Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for j in sig.judgments do
    if j.name.eraseMacroScopes == name then
      out := some j
  return out

/-- Look up a declared syntax sort by name. -/
def findSyntaxSortDecl? (sig : HLSignature) (name : Name) : Option SyntaxSortDecl := Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for s in sig.syntaxSorts do
    if s.name.eraseMacroScopes == name then
      out := some s
  return out

/-- Look up a declared syntax abbreviation by name. -/
def findSyntaxAbbrevDecl? (sig : HLSignature) (name : Name) : Option SyntaxAbbrevDecl := Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for a in sig.syntaxAbbrevs do
    if a.name.eraseMacroScopes == name then
      out := some a
  return out

/-- Expand public syntax abbreviations in an LF expression.

Expansion respects local binders and checks abbreviation arity. The fuel bound turns cycles
such as `syntax_abbrev A := A` into an explicit diagnostic instead of nontermination. -/
partial def expandSyntaxAbbrevsInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (locals : NameSet)
    (fuel : Nat) (e : ObjExpr) : CoreM ObjExpr := do
  if fuel == 0 then
    throwError "cyclic or too-deep syntax_abbrev expansion in {where_} of {ownerKind} \
      '{ownerName}' in type theory '{sig.name}'"
  match e with
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        pure (.ident n)
      else
        match findSyntaxAbbrevDecl? sig n with
        | none => pure (.ident n)
        | some a =>
            if a.params.size != 0 then
              throwError "{ownerKind} '{ownerName}' uses syntax_abbrev '{n}' in {where_} with 0 \
                argument(s), expected {a.params.size}"
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
            match findSyntaxAbbrevDecl? sig headName with
            | some a =>
                if args.size != a.params.size then
                  throwError "{ownerKind} '{ownerName}' uses syntax_abbrev '{headName}' in \
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
      s!"parameter '{b.name.eraseMacroScopes}' type" locals (sig.syntaxAbbrevs.size + 1) b.typeExpr
    let b := { b with name := b.name.eraseMacroScopes, typeExpr }
    out := out.push b
    locals := locals.insert b.name.eraseMacroScopes
  pure out

/-- Expand syntax abbreviations throughout a high-level signature while keeping the abbreviation
metadata for diagnostics/templates. -/
def expandSyntaxAbbrevsInSignature (sig : HLSignature) : CoreM HLSignature := do
  let syntaxAbbrevs ← sig.syntaxAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sig "syntax_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sig "syntax_abbrev" a.name "value" locals (sig.syntaxAbbrevs.size +
        1) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let sigForRest := { sig with syntaxAbbrevs }
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
        locals (sigForRest.syntaxAbbrevs.size + 1))
    pure { o with name := o.name.eraseMacroScopes, params, typeExpr? }
  let rules ← sigForRest.rules.mapM fun r => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "rule" r.name r.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let premises ← r.premises.mapM fun p => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name s!"premise '{p.name.eraseMacroScopes}'"
          locals (sigForRest.syntaxAbbrevs.size + 1) p.judgmentExpr
      pure { p with judgmentExpr }
    let sideConditions ← r.sideConditions.mapM fun sc => do
      let input ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name s!"side-condition \
          '{sc.name.eraseMacroScopes}'" locals (sigForRest.syntaxAbbrevs.size + 1) sc.input
      pure { sc with input }
    let paramEvidences ← r.paramEvidences.mapM fun ev => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"evidence '{ev.name.eraseMacroScopes}'" locals (sigForRest.syntaxAbbrevs.size + 1)
          ev.judgmentExpr
      pure { ev with judgmentExpr }
    let conclusionExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "rule" r.name "conclusion" locals
        (sigForRest.syntaxAbbrevs.size + 1) r.conclusionExpr
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
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "type" {} (sigForRest.syntaxAbbrevs.size
        + 1) d.typeExpr
    let value ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "value" {}
        (sigForRest.syntaxAbbrevs.size + 1) d.value
    pure { d with name := d.name.eraseMacroScopes, typeExpr, value }
  let lfJudgmentTheorems ← sigForRest.lfJudgmentTheorems.mapM fun t => do
    let binders ← expandSyntaxAbbrevsInBindings sigForRest "judgment_theorem" t.name t.binders
    let locals := binders.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let judgmentExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "statement" locals
        (sigForRest.syntaxAbbrevs.size + 1) t.judgmentExpr
    let proof ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "proof" locals
        (sigForRest.syntaxAbbrevs.size + 1) t.proof
    pure { t with name := t.name.eraseMacroScopes, binders, judgmentExpr, proof }
  pure { sigForRest with
    syntaxSorts := syntaxSorts
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

/-- Look up the declared object type of a global constant-like head. This is intentionally
limited to declarations that carry an explicit result type, including typed opaque LF
placeholders used as staging constructors. -/
def findLFGlobalTypeInfo? (sig : HLSignature) (name : Name) : Option LFGlobalTypeInfo := Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for o in sig.lfOpaqueConsts do
    if o.name.eraseMacroScopes == name then
      if let some typeExpr := o.typeExpr? then
        out := some { binders := o.params, typeExpr := typeExpr }
  return out

/-- Infer a shallow LF/object type for expressions whose head has known type metadata.
This handles local/LF-definition identifiers from `knownTypes` and global object constants
with explicit telescopes. It returns `none` for untyped opaque placeholders and other untyped
staging heads. -/
partial def inferKnownLFExprType? (sig : HLSignature) (knownTypes : LFLocalTypes) :
    ObjExpr → Option ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      match knownTypes.find? n with
      | some typeExpr => some typeExpr
      | none =>
          match findLFGlobalTypeInfo? sig n with
          | some info => if info.binders.isEmpty then some (eraseObjExprScopes info.typeExpr) else
            none
          | none =>
              match sig.lfObjectDefs.find? (fun d => d.name.eraseMacroScopes == n) with
              | some d => some (eraseObjExprScopes d.typeExpr)
              | none =>
                  match findSyntaxSortDecl? sig n with
                  | some s => if s.params.isEmpty then some .sort else none
                  | none =>
                      match findJudgmentDecl? sig n with
                      | some j => if j.params.isEmpty then some .sort else none
                      | none => none
  | .sort | .univ _ | .arrow .. | .funArrow .. | .lam .. | .jeq .. => none
  | e@(.app f a) =>
      match inferKnownLFExprType? sig knownTypes f with
      | some (.arrow binder? expected result) | some (.funArrow binder? expected result) =>
          match inferKnownLFExprType? sig knownTypes a with
          | some actual =>
              if !lfTypeCompareEq sig actual expected then
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
              match knownTypes.find? head with
              | some typeExpr => Id.run do
                  let mut current := eraseObjExprScopes typeExpr
                  let mut ok := true
                  for arg in args do
                    match current with
                    | .arrow binder? expected result | .funArrow binder? expected result =>
                        match inferKnownLFExprType? sig knownTypes arg with
                        | some actual =>
                            if !lfTypeCompareEq sig actual expected then
                              ok := false
                        | none => pure ()
                        current := match binder? with
                          | some x => substSingleLFParam x (eraseObjExprScopes arg) result
                          | none => result
                    | _ => ok := false
                  if ok then some (eraseObjExprScopes current) else none
              | none =>
                  match sig.lfObjectDefs.find? (fun d => d.name.eraseMacroScopes == head) with
                  | some d => Id.run do
                      let mut current := eraseObjExprScopes d.typeExpr
                      let mut ok := true
                      for arg in args do
                        match current with
                        | .arrow binder? expected result | .funArrow binder? expected result =>
                            match inferKnownLFExprType? sig knownTypes arg with
                            | some actual =>
                                if !lfTypeCompareEq sig actual expected then
                                  ok := false
                            | none => pure ()
                            current := match binder? with
                              | some x => substSingleLFParam x (eraseObjExprScopes arg) result
                              | none => result
                        | _ => ok := false
                      if ok then some (eraseObjExprScopes current) else none
                  | none =>
                      match findSyntaxSortDecl? sig head with
                      | some s =>
                          if args.size == s.params.size then
                            some .sort
                          else
                            none
                      | none =>
                          match findJudgmentDecl? sig head with
                          | some j =>
                              if args.size == j.params.size then
                                some .sort
                              else
                                none
                          | none =>
                              match findLFGlobalTypeInfo? sig head with
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
                                      match inferKnownLFExprType? sig knownTypes arg with
                                      | some actual =>
                                          if !lfTypeCompareEq sig actual expected then
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
  | depth + 1, .lam xs body =>
      let binders := String.intercalate " " (xs.toList.map (fun x => toString x.eraseMacroScopes))
      s!"(fun {binders} => {objExprSourceStringWithDepth depth body})"
  | depth + 1, .jeq lhs rhs =>
      s!"({objExprSourceStringWithDepth depth lhs} ≡ " ++
        s!"{objExprSourceStringWithDepth depth rhs})"

/-- Default budgeted object-expression rendering for diagnostics. -/
def diagnosticObjExprString (e : ObjExpr) : String :=
  truncateDiagnosticString 600 (toString e)

/-- Shorter one-line object-expression rendering for nested mismatch diagnostics. -/
def diagnosticObjExprShortString (e : ObjExpr) : String :=
  truncateDiagnosticString 240 (toString e)

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

/-- Callable LF head information for implicit-argument elaboration. -/
structure ImplicitCallableInfo where
  params : Array HLBinding := #[]
  result? : Option ObjExpr := none
  trailingExplicitArgs : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Look up a callable head and the telescope whose implicit arguments may be inserted. -/
def findImplicitCallableInfo? (sig : HLSignature) (name : Name) : Option ImplicitCallableInfo :=
  Id.run do
  let name := name.eraseMacroScopes
  let mut out : Option ImplicitCallableInfo := none
  for s in sig.syntaxSorts do
    if s.name.eraseMacroScopes == name then
      out := some { params := s.params, result? := some .sort }
  for a in sig.syntaxAbbrevs do
    if a.name.eraseMacroScopes == name then
      out := some { params := a.params, result? := some a.value }
  for j in sig.judgments do
    if j.name.eraseMacroScopes == name then
      out := some { params := j.params }
  for o in sig.lfOpaqueConsts do
    if o.name.eraseMacroScopes == name then
      if let some typeExpr := o.typeExpr? then
        out := some { params := o.params, result? := some typeExpr }
  for r in sig.rules do
    if r.name.eraseMacroScopes == name then
      out := some {
        params := r.params
        result? := some r.conclusionExpr
        -- Rule proofs explicitly supply premise derivations. Side-condition certificates are
        -- synthesized by checked side-condition hooks during LF replay, not source args.
        trailingExplicitArgs := r.premises.size }
  for d in sig.lfObjectDefs do
    if d.name.eraseMacroScopes == name then
      out := some { params := #[], result? := some d.typeExpr }
  for t in sig.lfJudgmentTheorems do
    if t.name.eraseMacroScopes == name then
      out := some { params := #[], result? := some t.judgmentExpr }
  return out

/-- Implicit variables associated to a callable telescope. -/
def implicitVarsOfParams (params : Array HLBinding) : NameSet := Id.run do
  let mut vars : NameSet := {}
  for p in params do
    if p.visibility == .implicit then
      vars := vars.insert p.name.eraseMacroScopes
  return vars

/-- Collect and remove named implicit arguments from an application spine. -/
def collectNamedImplicitArgs (ownerKind : String) (ownerName : Name) (headName : Name)
    (args : Array ObjExpr) : CoreM (NameMap ObjExpr × Array ObjExpr) := do
  let mut named : NameMap ObjExpr := {}
  let mut positional := #[]
  for arg in args do
    match implicitNamedArg? arg with
    | some (n, value) =>
        if (named.find? n).isSome then
          throwError "{ownerKind} '{ownerName}' has duplicate named implicit argument '{n}' in \
            application '{headName}'"
        named := named.insert n value
    | none => positional := positional.push arg
  pure (named, positional)

mutual
  /-- Elaborate implicit arguments in an object expression using shallow LF type metadata. -/
  partial def elaborateImplicitAppsInExpr (sig : HLSignature) (knownTypes : LFLocalTypes)
      (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
      (expected? : Option ObjExpr := none) : ObjExpr → CoreM ObjExpr
    | .ident n => do
        let nClean := n.eraseMacroScopes
        if locals.contains nClean then
          pure (.ident nClean)
        else
          match findImplicitCallableInfo? sig nClean with
          | some info =>
            elaborateImplicitHeadApp sig knownTypes locals ownerKind ownerName where_ nClean info
              #[] expected?
          | none => pure (.ident nClean)
    | .sort => pure .sort
    | .univ u => pure (.univ u)
    | .arrow x A B => do
        let A ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        let locals := match x with
          | some x => locals.insert x.eraseMacroScopes
          | none => locals
        let B ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none B
        pure (.arrow (x.map Name.eraseMacroScopes) A B)
    | .funArrow x A B => do
        let A ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        let locals := match x with
          | some x => locals.insert x.eraseMacroScopes
          | none => locals
        let B ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none B
        pure (.funArrow (x.map Name.eraseMacroScopes) A B)
    | .lam xs body => do
        let clean := xs.map Name.eraseMacroScopes
        let locals := clean.foldl (fun locals x => locals.insert x) locals
        pure (.lam clean (← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
          where_ none body))
    | .jeq lhs rhs => do
        pure (.jeq (← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_
          none lhs)
          (← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none rhs))
    | e@(.app ..) => do
        if let some (n, _) := implicitNamedArg? e then
          throwError "{ownerKind} '{ownerName}' has named implicit argument '{n}' outside a known \
            head application in {where_}"
        let (head, args) := splitObjApp e
        match head with
        | .ident headName =>
            let headName := headName.eraseMacroScopes
            if locals.contains headName then
              let head := .ident headName
              let args ←
                args.mapM (elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
                  where_ none)
              pure (mkObjApp head args)
            else
              match findImplicitCallableInfo? sig headName with
              | some info =>
                  let hasImplicit := info.params.any (fun p => p.visibility == .implicit)
                  if !hasImplicit && info.trailingExplicitArgs == 0
                    && args.size < info.params.size then
                    let args ←
                      args.mapM (elaborateImplicitAppsInExpr sig knownTypes locals ownerKind
                        ownerName where_ none)
                    pure (mkObjApp (.ident headName) args)
                  else if info.params.isEmpty && info.trailingExplicitArgs == 0
                    && !args.isEmpty then
                    let args ←
                      args.mapM (elaborateImplicitAppsInExpr sig knownTypes locals ownerKind
                        ownerName where_ none)
                    pure (mkObjApp (.ident headName) args)
                  else
                    elaborateImplicitHeadApp sig knownTypes locals ownerKind ownerName where_
                      headName info args expected?
              | none =>
                  let head ←
                    elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_
                      none head
                  let args ←
                    args.mapM (elaborateImplicitAppsInExpr sig knownTypes locals ownerKind
                      ownerName where_ none)
                  pure (mkObjApp head args)
        | _ =>
            let head ←
              elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName where_ none head
            let args ←
              args.mapM (elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
                where_ none)
            pure (mkObjApp head args)

  /-- Elaborate one known-head application, inserting omitted ordinary implicit arguments. -/
  partial def elaborateImplicitHeadApp (sig : HLSignature) (knownTypes : LFLocalTypes)
      (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
      (headName : Name) (info : ImplicitCallableInfo) (rawArgs : Array ObjExpr)
      (expected? : Option ObjExpr) : CoreM ObjExpr := do
    let (named, positional) ← collectNamedImplicitArgs ownerKind ownerName headName rawArgs
    let hasNamed := positional.size != rawArgs.size
    let fullPositional := !hasNamed
      && positional.size == info.params.size + info.trailingExplicitArgs
    let implicitVars := implicitVarsOfParams info.params
    let mut subst : NameMap ObjExpr := {}
    let mut argsByParam : Array (Option ObjExpr) := (List.replicate info.params.size none).toArray
    let mut posIdx := 0
    if fullPositional then
      for h : i in [:info.params.size] do
        let param := info.params[i]
        let raw := positional[i]!
        let expectedParam := substLFParams subst param.typeExpr
        let arg ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
          s!"{where_} argument '{param.name.eraseMacroScopes}' of \
            '{headName}'" (some expectedParam) raw
        argsByParam := argsByParam.set! i (some arg)
        subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)
      posIdx := info.params.size
    else
      for h : i in [:info.params.size] do
        let param := info.params[i]
        let pName := param.name.eraseMacroScopes
        let expectedParam := substLFParams subst param.typeExpr
        match named.find? pName with
        | some rawNamed =>
            if param.visibility != .implicit then
              throwError "{ownerKind} '{ownerName}' supplies named implicit argument '{pName}' \
                for explicit parameter '{pName}' in application '{headName}'"
            let arg ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
              s!"{where_} named implicit argument '{pName}' of \
                '{headName}'" (some expectedParam) rawNamed
            argsByParam := argsByParam.set! i (some arg)
            subst := subst.insert pName (eraseObjExprScopes arg)
        | none =>
            if param.visibility == .implicit then
              pure ()
            else
              let some raw := positional[posIdx]?
                | throwError "{ownerKind} '{ownerName}' omits explicit argument '{pName}' in \
                  application '{headName}' in {where_}"
              posIdx := posIdx + 1
              let arg ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
                s!"{where_} argument '{pName}' of '{headName}'" (some expectedParam) raw
              if let some actualType := inferKnownLFExprType? sig knownTypes arg then
                match matchImplicitObjectPattern implicitVars expectedParam actualType subst with
                | .ok subst' => subst := subst'
                | .error _ => pure ()
              argsByParam := argsByParam.set! i (some arg)
              subst := subst.insert pName (eraseObjExprScopes arg)
      for (n, _) in named.toList do
        unless info.params.any (fun p => p.name.eraseMacroScopes == n
          && p.visibility == .implicit) do
          throwError "{ownerKind} '{ownerName}' supplies unknown named implicit argument '{n}' in \
            application '{headName}'"
    if let some expected := expected? then
      if let some result := info.result? then
        let result := substLFParams subst result
        match matchImplicitObjectPattern implicitVars result expected subst with
        | .ok subst' => subst := subst'
        | .error err =>
            if implicitVars.isEmpty then pure () else
              throwError "{ownerKind} '{ownerName}' could not infer implicit arguments for \
                application '{headName}' in {where_} from expected expression\n  \
                  {expected}\nwhile matching result\n  {result}\nreason: {err}"
    let mut outArgs := #[]
    for h : i in [:info.params.size] do
      let param := info.params[i]
      let pName := param.name.eraseMacroScopes
      match argsByParam[i]! with
      | some arg => outArgs := outArgs.push arg
      | none =>
          match subst.find? pName with
          | some inferred => outArgs := outArgs.push inferred
          | none =>
              throwError "{ownerKind} '{ownerName}' could not infer implicit argument '{pName} : \
                {param.typeExpr}' in application '{headName}' in {where_}; use a named implicit \
                  argument or supply all arguments explicitly"
    let remaining := positional[posIdx:]
    if remaining.size != info.trailingExplicitArgs then
      if info.trailingExplicitArgs == 0 then
        throwError "{ownerKind} '{ownerName}' supplied too many explicit argument(s) to \
          application '{headName}' in {where_}; expected {info.params.size} total argument \
            slot(s) after elaboration"
      else
        throwError "{ownerKind} '{ownerName}' supplied {remaining.size} trailing \
          proof/certificate argument(s) to application '{headName}' in {where_}, expected \
            {info.trailingExplicitArgs}"
    for raw in remaining do
      outArgs :=
        outArgs.push (← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
          where_ none raw)
    pure (mkObjApp (.ident headName) outArgs)
end

/-- Elaborate implicit applications in a telescope, extending the local shallow-type context. -/
def elaborateImplicitAppsInBindings (sig : HLSignature) (knownTypes : LFLocalTypes)
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) :
    CoreM (Array HLBinding × LFLocalTypes × NameSet) := do
  let mut out := #[]
  let mut knownTypes := knownTypes
  let mut locals := locals
  for b in bs do
    let typeExpr ← elaborateImplicitAppsInExpr sig knownTypes locals ownerKind ownerName
      s!"parameter '{b.name.eraseMacroScopes}' type" none b.typeExpr
    let b := { b with name := b.name.eraseMacroScopes, typeExpr := typeExpr }
    out := out.push b
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes typeExpr)
    locals := locals.insert b.name.eraseMacroScopes
  pure (out, knownTypes, locals)

/-- Elaborate implicit applications in an LF syntax-sort declaration. -/
def elaborateImplicitAppsInSyntaxSortDecl (sig : HLSignature) (d : SyntaxSortDecl) :
  CoreM SyntaxSortDecl := do
  let (params, _, _) ← elaborateImplicitAppsInBindings sig {} {} "syntax_sort" d.name d.params
  pure { d with params }

/-- Elaborate implicit applications in a syntax abbreviation declaration. -/
def elaborateImplicitAppsInSyntaxAbbrevDecl (sig : HLSignature) (d : SyntaxAbbrevDecl) :
  CoreM SyntaxAbbrevDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindings sig {} {} "syntax_abbrev" d.name d.params
  let value ←
    elaborateImplicitAppsInExpr sig knownTypes locals "syntax_abbrev" d.name "value" none d.value
  pure { d with params, value }

/-- Elaborate implicit applications in an LF judgment declaration. -/
def elaborateImplicitAppsInJudgmentDecl (sig : HLSignature) (d : JudgmentDecl) :
  CoreM JudgmentDecl := do
  let (params, _, _) ← elaborateImplicitAppsInBindings sig {} {} "judgment" d.name d.params
  pure { d with params }

/-- Elaborate implicit applications in an LF opaque declaration. -/
def elaborateImplicitAppsInLFOpaqueConstDecl (sig : HLSignature) (d : LFOpaqueConstDecl) :
  CoreM LFOpaqueConstDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindings sig {} {} "lf_opaque" d.name d.params
  let typeExpr? ← match d.typeExpr? with
    | some typeExpr =>
      some <$> elaborateImplicitAppsInExpr sig knownTypes locals "lf_opaque" d.name "result type"
        none typeExpr
    | none => pure none
  pure { d with params, typeExpr? }

/-- Elaborate implicit applications in an LF rule declaration. -/
def elaborateImplicitAppsInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM RuleDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindings sig {} {} "rule" r.name r.params
  let premises ← r.premises.mapM fun p => do
    let judgmentExpr ← elaborateImplicitAppsInExpr sig knownTypes locals "rule" r.name
      s!"premise '{p.name.eraseMacroScopes}'" none p.judgmentExpr
    pure { p with judgmentExpr }
  let sideConditions ← r.sideConditions.mapM fun sc => do
    let input ← elaborateImplicitAppsInExpr sig knownTypes locals "rule" r.name
      s!"side condition '{sc.name.eraseMacroScopes}'" none sc.input
    pure { sc with input }
  let paramEvidences ← r.paramEvidences.mapM fun ev => do
    let judgmentExpr ← elaborateImplicitAppsInExpr sig knownTypes locals "rule" r.name
      s!"evidence '{ev.name.eraseMacroScopes}'" none ev.judgmentExpr
    pure { ev with judgmentExpr }
  let conclusionExpr ←
    elaborateImplicitAppsInExpr sig knownTypes locals "rule" r.name "conclusion" none
      r.conclusionExpr
  pure { r with params, premises, sideConditions, paramEvidences, conclusionExpr }

/-- Elaborate implicit applications in an LF object definition. -/
def elaborateImplicitAppsInLFObjectDef (sig : HLSignature) (knownTypes : LFLocalTypes)
    (d : LFObjectDefDecl) : CoreM LFObjectDefDecl := do
  let typeExpr ←
    elaborateImplicitAppsInExpr sig knownTypes {} "lf_def" d.name "type" none d.typeExpr
  let value ←
    elaborateImplicitAppsInExpr sig knownTypes {} "lf_def" d.name "value" (some typeExpr) d.value
  pure { d with typeExpr, value }

/-- Elaborate implicit applications in an LF judgment theorem. -/
def elaborateImplicitAppsInLFJudgmentTheorem (sig : HLSignature) (knownTypes : LFLocalTypes)
    (t : LFJudgmentTheoremDecl) : CoreM LFJudgmentTheoremDecl := do
  let (binders, theoremKnownTypes, locals) ←
    elaborateImplicitAppsInBindings sig knownTypes {} "judgment_theorem" t.name t.binders
  let judgmentExpr ←
    elaborateImplicitAppsInExpr sig theoremKnownTypes locals "judgment_theorem" t.name "statement"
      none t.judgmentExpr
  let proof ←
    elaborateImplicitAppsInExpr sig theoremKnownTypes locals "judgment_theorem" t.name "proof"
      (some judgmentExpr) t.proof
  pure { t with binders, judgmentExpr, proof }

/-- Elaborate implicit applications throughout a high-level signature, using `headSig` as the
callable-head environment. The returned signature is still ordinary explicit `ObjExpr` syntax;
implicit arguments have been inserted before checking. -/
def elaborateImplicitAppsInSignatureWithEnv (headSig sig : HLSignature) : CoreM HLSignature := do
  let sig0 := headSig
  let syntaxSorts ← sig.syntaxSorts.mapM (elaborateImplicitAppsInSyntaxSortDecl sig0)
  let syntaxAbbrevs ← sig.syntaxAbbrevs.mapM (elaborateImplicitAppsInSyntaxAbbrevDecl sig0)
  let judgments ← sig.judgments.mapM (elaborateImplicitAppsInJudgmentDecl sig0)
  let lfOpaqueConsts ← sig.lfOpaqueConsts.mapM (elaborateImplicitAppsInLFOpaqueConstDecl sig0)
  let rules ← sig.rules.mapM (elaborateImplicitAppsInRuleDecl sig0)
  let sig1 := { sig with syntaxSorts, syntaxAbbrevs, judgments, lfOpaqueConsts, rules }
  let mut knownTypes : LFLocalTypes := {}
  let mut lfObjectDefs := #[]
  for d in sig.lfObjectDefs do
    let d ← elaborateImplicitAppsInLFObjectDef sig1 knownTypes d
    lfObjectDefs := lfObjectDefs.push d
    knownTypes := knownTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  let lfJudgmentTheorems ←
    sig.lfJudgmentTheorems.mapM (elaborateImplicitAppsInLFJudgmentTheorem sig1 knownTypes)
  pure { sig1 with lfObjectDefs, lfJudgmentTheorems }

/-- Elaborate implicit applications throughout a high-level signature using its own heads. -/
def elaborateImplicitAppsInSignature (sig : HLSignature) : CoreM HLSignature :=
  elaborateImplicitAppsInSignatureWithEnv sig sig

/-- Whether an expression mentions a named LF object definition from the signature. -/
partial def lfExprMentionsLFObjectDef (sig : HLSignature) : ObjExpr → Bool
  | .ident n => sig.lfObjectDefs.any (fun d => d.name.eraseMacroScopes == n.eraseMacroScopes)
  | .sort | .univ _ => false
  | .app f a => lfExprMentionsLFObjectDef sig f || lfExprMentionsLFObjectDef sig a
  | .arrow _ A B | .funArrow _ A B =>
      lfExprMentionsLFObjectDef sig A || lfExprMentionsLFObjectDef sig B
  | .lam _ body => lfExprMentionsLFObjectDef sig body
  | .jeq lhs rhs => lfExprMentionsLFObjectDef sig lhs || lfExprMentionsLFObjectDef sig rhs

/-- Normalize explicit object-level lambda applications without unfolding named definitions. -/
partial def normalizeLFExprBetaOnly : ObjExpr → ObjExpr
  | .ident n => .ident n.eraseMacroScopes
  | .sort => .sort
  | .univ u => .univ u
  | .app f a =>
      let f := normalizeLFExprBetaOnly f
      let a := normalizeLFExprBetaOnly a
      match f with
      | .lam xs body =>
          if h : 0 < xs.size then
            let x := xs[0]
            let rest := xs.extract 1 xs.size
            let target := if rest.isEmpty then body else .lam rest body
            normalizeLFExprBetaOnly (substSingleLFParam x a target)
          else
            .app f a
      | _ => .app f a
  | .arrow x A B => .arrow (x.map Name.eraseMacroScopes) (normalizeLFExprBetaOnly A) (
    normalizeLFExprBetaOnly B)
  | .funArrow x A B => .funArrow (x.map Name.eraseMacroScopes) (normalizeLFExprBetaOnly A) (
    normalizeLFExprBetaOnly B)
  | .lam xs body => .lam (xs.map Name.eraseMacroScopes) (normalizeLFExprBetaOnly body)
  | .jeq lhs rhs => .jeq (normalizeLFExprBetaOnly lhs) (normalizeLFExprBetaOnly rhs)

/-- Whether an expression is a declared untyped opaque LF placeholder with matching arity.

Untyped placeholders are the only non-inferable expressions accepted by the bidirectional checker.
They model an explicit boundary where the user provided a syntactic LF payload without a result
sort, so the checker treats them as holes at the expected type rather than silently accepting
arbitrary untyped expressions. -/
def isUntypedLFOpaquePlaceholder (sig : HLSignature) (knownTypes : LFLocalTypes)
    (expr : ObjExpr) : Bool :=
  match splitObjApp (eraseObjExprScopes expr) with
  | (.ident head, args) =>
      let head := head.eraseMacroScopes
      if (knownTypes.find? head).isSome then
        false
      else
        sig.lfOpaqueConsts.any fun o =>
          o.name.eraseMacroScopes == head && o.typeExpr?.isNone &&
            match o.arity? with
            | some arity => args.size == arity
            | none => args.isEmpty
  | _ => false

/-- Check, when possible, that an LF expression has an expected type.

This is a bidirectional checker for the supported LF staging fragment. Lambda expressions are
checked against expected dependent arrows, applications with known typed heads recursively check
their arguments, and non-lambda expressions must infer a type matching the expected type. The only
non-inferable expressions accepted at an expected type are explicitly declared untyped opaque LF
placeholders, which remain a visible trust boundary for staged payloads. -/
partial def checkLFExprHasType (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (where_ : String) (knownTypes : LFLocalTypes) (expr expected : ObjExpr) : CoreM Unit := do
  let rec checkInferableApps (knownTypes : LFLocalTypes) (expr : ObjExpr) : CoreM Unit := do
    match eraseObjExprScopes expr with
    | .ident _ | .sort | .univ _ => pure ()
    | e@(.app ..) =>
        match splitObjApp e with
        | (.ident head, args) =>
            let head := head.eraseMacroScopes
            match findLFGlobalTypeInfo? sig head with
            | some info =>
                if args.size == info.binders.size then
                  let mut subst : NameMap ObjExpr := {}
                  for b in info.binders, arg in args do
                    let expected := substLFParams subst b.typeExpr
                    checkLFExprHasType sig ownerKind ownerName
                      s!"{where_} for constructor '{head}' parameter \
                        '{b.name.eraseMacroScopes}'" knownTypes arg expected
                    checkInferableApps knownTypes arg
                    subst := subst.insert b.name.eraseMacroScopes (eraseObjExprScopes arg)
                else
                  for arg in args do
                    checkInferableApps knownTypes arg
            | none =>
                match knownTypes.find? head with
                | some typeExpr =>
                    let mut current := eraseObjExprScopes typeExpr
                    for arg in args do
                      match current with
                      | .arrow binder? expected result | .funArrow binder? expected result =>
                          checkLFExprHasType sig ownerKind ownerName
                            s!"{where_} for local function '{head}' argument" knownTypes arg
                            expected
                          checkInferableApps knownTypes arg
                          current := match binder? with
                            | some x => substSingleLFParam x (eraseObjExprScopes arg) result
                            | none => result
                      | _ =>
                          checkInferableApps knownTypes arg
                | none =>
                    for arg in args do
                      checkInferableApps knownTypes arg
        | (head, args) =>
            checkInferableApps knownTypes head
            for arg in args do
              checkInferableApps knownTypes arg
    | .arrow x A B | .funArrow x A B =>
        checkInferableApps knownTypes A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        checkInferableApps knownTypes B
    | .lam _ _body =>
        pure ()
    | .jeq lhs rhs =>
        checkInferableApps knownTypes lhs
        checkInferableApps knownTypes rhs
  let expr := normalizeLFExprBetaOnly (eraseObjExprScopes expr)
  let expected := normalizeLFExprBetaOnly expected
  match expr with
  | .lam xs body =>
      if h : 0 < xs.size then
        match expected with
        | .arrow expectedBinder? expectedDomain expectedBody
        | .funArrow expectedBinder? expectedDomain expectedBody =>
            let x := xs[0].eraseMacroScopes
            let rest := xs.extract 1 xs.size
            let bodyExpr := if rest.isEmpty then body else .lam rest body
            let expectedBody := match expectedBinder? with
              | some y => substSingleLFParam y (.ident x) expectedBody
              | none => expectedBody
            let knownTypes := knownTypes.insert x (eraseObjExprScopes expectedDomain)
            checkLFExprHasType sig ownerKind ownerName where_ knownTypes bodyExpr expectedBody
        | _ =>
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} as \
              lambda expression '{diagnosticObjExprString expr}', expected non-function type \
                '{diagnosticObjExprString expected}'"
      else
        throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} as an \
          empty lambda expression"
  | _ =>
      checkInferableApps knownTypes expr
      match inferKnownLFExprType? sig knownTypes expr with
      | some actualType =>
          let actualType := normalizeLFExprBetaOnly actualType
          let normalizedActualType := normalizeLFExprForTypeComparison sig actualType
          let normalizedExpected := normalizeLFExprForTypeComparison sig expected
          if !lfExprAlphaEq normalizedActualType normalizedExpected then
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} with \
              type '{diagnosticObjExprString normalizedActualType}', expected \
                '{diagnosticObjExprString normalizedExpected}'"
      | none =>
          unless isUntypedLFOpaquePlaceholder sig knownTypes expr do
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} whose \
              type cannot be inferred: '{diagnosticObjExprString expr}', expected \
                '{diagnosticObjExprString expected}'"

/-- Check an LF argument against a known expected type.

Expected argument positions are checked bidirectionally even when the argument has no shallow
inferred type. The only non-inferable arguments accepted by this path are explicitly declared
untyped LF placeholders, which remain visible trust-boundary holes. -/
def checkLFKnownArgumentType (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (where_ : String) (knownTypes : LFLocalTypes) (arg expected : ObjExpr) : CoreM Unit := do
  checkLFExprHasType sig ownerKind ownerName
    s!"{where_} argument '{diagnosticObjExprShortString (eraseObjExprScopes arg)}'"
    knownTypes arg expected

/-- Compatibility hook retained for call sites from the former capture-safety barrier.

Beta normalization now uses capture-avoiding LF substitution with deterministic alpha-renaming, so
explicit beta-redexes are checked by normal comparison rather than rejected preemptively. -/
def checkNoCaptureUnsafeBetaInLFExpr (_sig : HLSignature) (_ownerKind : String)
    (_ownerName : Name) (_where_ : String) (_e : ObjExpr) : CoreM Unit :=
  pure ()

/-- Check, when possible, that a local LF argument has the expected syntax-sort-shaped type. -/
def checkLFLocalArgumentType (sig : HLSignature) (ruleName : Name) (where_ : String)
    (locals : LFLocalTypes) (arg expected : ObjExpr) : CoreM Unit :=
  checkLFKnownArgumentType sig "rule" ruleName where_ locals arg expected

/-- Recursively validate arguments of global constructor applications whose parameter
telescope is known. This catches ill-typed constructor applications even when an enclosing
expression would otherwise be left opaque by shallow inference. -/
partial def checkLFInferableApplicationArguments (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) : ObjExpr → CoreM Unit
  | .ident _ | .sort | .univ _ => pure ()
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident head, args) =>
          let head := head.eraseMacroScopes
          if let some info := findLFGlobalTypeInfo? sig head then
            if args.size == info.binders.size then
              let mut subst : NameMap ObjExpr := {}
              for b in info.binders, arg in args do
                let expected := substLFParams subst b.typeExpr
                checkLFKnownArgumentType sig ownerKind ownerName
                  s!"{where_} for constructor '{head}' parameter '{b.name.eraseMacroScopes}'"
                  knownTypes arg expected
                checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes arg
                subst := subst.insert b.name.eraseMacroScopes (eraseObjExprScopes arg)
            else
              for arg in args do
                checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes arg
          else
            for arg in args do
              checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes arg
      | (head, args) =>
          checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes head
          for arg in args do
            checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes arg
  | .arrow x A B | .funArrow x A B => do
      checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes B
  | .lam _ _body =>
      pure ()
  | .jeq lhs rhs => do
      checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes lhs
      checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes rhs

/-- Shallowly check the argument list of a judgment-headed LF expression against the judgment
declaration telescope using a supplied known-type context. -/
def checkLFJudgmentArgumentsWithKnownTypes (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (judgmentName : Name)
    (args : Array ObjExpr) : CoreM Unit := do
  let some j := findJudgmentDecl? sig judgmentName
    | pure ()
  let mut subst : NameMap ObjExpr := {}
  for h : i in [:j.params.size] do
    let param := j.params[i]
    let arg := args[i]!
    let expected := substLFParams subst param.typeExpr
    checkLFKnownArgumentType sig ownerKind ownerName
      s!"{where_} for judgment '{judgmentName.eraseMacroScopes}'" knownTypes arg expected
    checkLFInferableApplicationArguments sig ownerKind ownerName
      s!"{where_} for judgment '{judgmentName.eraseMacroScopes}'" knownTypes arg
    subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)

/-- Shallowly check the argument list of a judgment-headed rule expression against the
judgment declaration telescope. -/
def checkLFJudgmentArguments (sig : HLSignature) (ruleName : Name) (where_ : String)
    (locals : LFLocalTypes) (judgmentName : Name) (args : Array ObjExpr) : CoreM Unit :=
  checkLFJudgmentArgumentsWithKnownTypes sig "rule" ruleName where_ locals judgmentName args

/-- Shallowly check the argument list of a syntax-sort-headed LF expression against the
syntax sort telescope using a supplied known-type context. -/
def checkLFSyntaxSortArgumentsWithKnownTypes (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (sortName : Name)
    (args : Array ObjExpr) : CoreM Unit := do
  let some s := findSyntaxSortDecl? sig sortName
    | pure ()
  let mut subst : NameMap ObjExpr := {}
  for _h : i in [:min s.params.size args.size] do
    let param := s.params[i]!
    let arg := args[i]!
    let expected := substLFParams subst param.typeExpr
    checkLFKnownArgumentType sig ownerKind ownerName
      s!"{where_} for syntax_sort '{sortName.eraseMacroScopes}'" knownTypes arg expected
    checkLFInferableApplicationArguments sig ownerKind ownerName
      s!"{where_} for syntax_sort '{sortName.eraseMacroScopes}'" knownTypes arg
    subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)

/-- Recursively check syntax-sort-headed subexpressions against syntax-sort telescopes when
arguments are known local or LF-definition identifiers. -/
partial def checkLFSyntaxSortArgumentsInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) : ObjExpr → CoreM Unit
  | .ident n => do
      if (findSyntaxSortDecl? sig n).isSome then
        checkLFSyntaxSortArgumentsWithKnownTypes sig ownerKind ownerName where_ knownTypes n #[]
  | .sort | .univ _ => pure ()
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident head, args) =>
          if (findSyntaxSortDecl? sig head).isSome then
            checkLFSyntaxSortArgumentsWithKnownTypes sig ownerKind ownerName where_ knownTypes head
              args
          for arg in args do
            checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes arg
      | (head, args) =>
          checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes head
          for arg in args do
            checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes arg
  | .arrow x A B | .funArrow x A B => do
      checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes B
  | .lam _ _body =>
      pure ()
  | .jeq lhs rhs => do
      checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes lhs
      checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes rhs

/-- Check a metadata telescope sequentially, so later binder types can use earlier binders
as arguments to dependent syntax sorts. -/
def checkLFSyntaxSortArgumentsInBindings (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) : CoreM Unit := do
  let mut knownTypes : LFLocalTypes := {}
  for b in bs do
    let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
    checkLFSyntaxSortArgumentsInExpr sig ownerKind ownerName where_ knownTypes b.typeExpr
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)

/-- Whether a shallow inferred LF type certifies that an expression is itself a type. -/
def inferredLFTypeIsUniverse (sig : HLSignature) (actualType : ObjExpr) : Bool :=
  match normalizeLFExprForTypeComparison sig actualType with
  | .sort | .univ _ => true
  | _ => false

/-- Check that an expression is valid in a metadata telescope binder type position.

Binder types are allowed to be universe expressions, syntax-sort-headed type expressions, local or
opaque type-family applications whose inferred kind is a universe, and dependent arrows between
valid binder types. Theorem binders may additionally be judgment-headed local assumptions. -/
partial def checkLFBinderType (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (locals : NameSet)
    (allowJudgment : Bool) (typeExpr : ObjExpr) : CoreM Unit := do
  let typeExpr := eraseObjExprScopes typeExpr
  match typeExpr with
  | .sort | .univ _ => pure ()
  | .arrow x A B | .funArrow x A B =>
      checkLFBinderType sig globalHeads ownerKind ownerName where_ knownTypes locals false A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      let locals := match x with
        | some x => locals.insert x.eraseMacroScopes
        | none => locals
      checkLFBinderType sig globalHeads ownerKind ownerName where_ knownTypes locals false B
  | _ =>
      let head? := checkedLFHead? globalHeads locals typeExpr
      match head? with
      | some head =>
          checkCheckedLFHeadArity sig ownerKind ownerName where_ head
          if head.kind == .judgment then
            unless allowJudgment do
              throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                headed by judgment '{head.name}', expected an LF type expression"
            let (_, args) := splitObjApp typeExpr
            checkLFJudgmentArgumentsWithKnownTypes sig ownerKind ownerName where_ knownTypes
              head.name args
          else if head.kind == .syntaxSort then
            let (_, args) := splitObjApp typeExpr
            checkLFSyntaxSortArgumentsWithKnownTypes sig ownerKind ownerName where_ knownTypes
              head.name args
          else
            checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes typeExpr
            match inferKnownLFExprType? sig knownTypes typeExpr with
            | some actualType =>
                unless inferredLFTypeIsUniverse sig actualType do
                  throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                    whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                      universe-valued LF type expression"
            | none =>
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose type cannot be inferred: '{diagnosticObjExprString typeExpr}', expected \
                    an LF type expression"
      | none =>
          checkLFInferableApplicationArguments sig ownerKind ownerName where_ knownTypes typeExpr
          match inferKnownLFExprType? sig knownTypes typeExpr with
          | some actualType =>
              unless inferredLFTypeIsUniverse sig actualType do
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                    universe-valued LF type expression"
          | none =>
              throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                not headed by a known LF type or judgment: {diagnosticObjExprString typeExpr}"

/-- Check a metadata telescope sequentially with the binder-type kind discipline. -/
def checkLFBinderTypesInBindings (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) (allowJudgment : Bool := false)
    (baseKnownTypes : LFLocalTypes := {}) : CoreM Unit := do
  let mut knownTypes := baseKnownTypes
  let mut locals : NameSet := {}
  for b in bs do
    let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
    checkLFBinderType sig globalHeads ownerKind ownerName where_ knownTypes locals allowJudgment
      b.typeExpr
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    locals := locals.insert b.name.eraseMacroScopes

/-- Classify a declared side-condition solver name into the executable hook registry.

Only `trivial_side_condition` is executable. Other declared solvers remain opaque handles for
trusted/checkable plugins. -/
def classifySideConditionHook (n : Name) : CheckedLFSideConditionHookKind :=
  if n.eraseMacroScopes == `trivial_side_condition then .builtinTrivial else .opaque

/-- Build the checked artifact for one syntax-sort declaration. -/
def checkedLFSyntaxSortDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (s : SyntaxSortDecl) :
    CoreM CheckedLFSyntaxSort := do
  let (params, _) ← checkedLFBindings sig globalHeads "syntax_sort" s.name s.params
  pure { name := s.name.eraseMacroScopes, params := params, arity := s.params.size }

/-- Build the checked artifact for one syntax-abbreviation declaration. -/
def checkedLFSyntaxAbbrevDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (a : SyntaxAbbrevDecl) :
    CoreM CheckedLFSyntaxAbbrev := do
  let (params, locals) ← checkedLFBindings sig globalHeads "syntax_abbrev" a.name a.params
  let checkedValue ← resolveLFExpr sig globalHeads locals "syntax_abbrev" a.name "value" a.value
  let head? := checkedLFHead? globalHeads locals a.value
  pure {
    name := a.name.eraseMacroScopes
    params := params
    value := a.value
    checkedValue := checkedValue
    head? := head? }

/-- Build the checked artifact for one context-zone declaration. -/
def checkedLFContextZoneDeclArtifact (z : ContextZoneDecl) : CheckedLFContextZone :=
  { name := z.name.eraseMacroScopes
    sortName := z.sortName.eraseMacroScopes
    dependsOn := z.dependsOn.map Name.eraseMacroScopes }

/-- Build the checked artifact for one binder-class declaration. -/
def checkedLFBinderClassDeclArtifact (b : BinderClassDecl) : CheckedLFBinderClass :=
  { name := b.name.eraseMacroScopes
    boundSortName := b.boundSortName.eraseMacroScopes
    zoneName := b.zoneName.eraseMacroScopes
    dependsOn := b.dependsOn.map Name.eraseMacroScopes }

/-- Build the checked artifact for one judgment declaration. -/
def checkedLFJudgmentDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (j : JudgmentDecl) :
    CoreM CheckedLFJudgment := do
  let (params, _) ← checkedLFBindings sig globalHeads "judgment" j.name j.params
  pure { name := j.name.eraseMacroScopes, params := params, arity := j.params.size }

/-- Build the checked artifact for one LF opaque declaration. -/
def checkedLFOpaqueConstDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (o : LFOpaqueConstDecl) :
    CoreM CheckedLFOpaqueConst := do
  let (params, locals) ← checkedLFBindings sig globalHeads "lf_opaque" o.name o.params
  let (checkedTypeExpr?, typeHead?) ← match o.typeExpr? with
    | none => pure (none, none)
    | some typeExpr => do
        let checkedTypeExpr ←
          resolveLFExpr sig globalHeads locals "lf_opaque" o.name "result type" typeExpr
        let typeHead? := checkedLFHead? globalHeads locals typeExpr
        pure (some checkedTypeExpr, typeHead?)
  pure {
    name := o.name.eraseMacroScopes
    arity? := o.arity?
    params := params
    typeExpr? := o.typeExpr?
    checkedTypeExpr? := checkedTypeExpr?
    typeHead? := typeHead? }

/-- Build the checked artifact for one side-condition solver declaration. -/
def checkedLFSideConditionSolverDeclArtifact (s : SideConditionSolverDecl) :
    CheckedLFSideConditionSolver :=
  { name := s.name.eraseMacroScopes, hookKind := classifySideConditionHook s.name }

/-- Build the checked artifact for one conversion-plugin declaration. -/
def checkedLFConversionPluginDeclArtifact (p : ConversionPluginDecl) : CheckedLFConversionPlugin :=
  { name := p.name.eraseMacroScopes
    trust := p.trust
    supportedSteps := p.supportedSteps }

/-- Build checked LF declaration artifacts for syntax sorts, context zones, binder classes,
judgments, and opaque placeholders. -/
def checkedLFDeclarations (sig : HLSignature) :
    CoreM (Array CheckedLFSyntaxSort × Array CheckedLFSyntaxAbbrev × Array CheckedLFContextZone ×
      Array CheckedLFBinderClass × Array CheckedLFJudgment × Array CheckedLFOpaqueConst ×
      Array CheckedLFSideConditionSolver × Array CheckedLFConversionPlugin) := do
  let globalHeads := lfGlobalHeadInfo sig
  let syntaxSorts ← sig.syntaxSorts.mapM (checkedLFSyntaxSortDeclArtifact sig globalHeads)
  let syntaxAbbrevs ← sig.syntaxAbbrevs.mapM (checkedLFSyntaxAbbrevDeclArtifact sig globalHeads)
  let contextZones := sig.contextZones.map checkedLFContextZoneDeclArtifact
  let binderClasses := sig.binderClasses.map checkedLFBinderClassDeclArtifact
  let judgments ← sig.judgments.mapM (checkedLFJudgmentDeclArtifact sig globalHeads)
  let opaques ← sig.lfOpaqueConsts.mapM (checkedLFOpaqueConstDeclArtifact sig globalHeads)
  let solvers := sig.sideConditionSolvers.map checkedLFSideConditionSolverDeclArtifact
  let plugins := sig.conversionPlugins.map checkedLFConversionPluginDeclArtifact
  pure (syntaxSorts, syntaxAbbrevs, contextZones, binderClasses, judgments, opaques, solvers,
    plugins)

/-- Check that identifiers in an LF metadata expression are known globals or local binders.

This is still syntactic validation only: it does not infer types or solve dependencies.
Applications headed by declared syntax sorts, judgment forms, primitive object constants,
definitions, theorems, or `lf_opaque` placeholders are accepted. Other identifiers must be
local variables bound by the surrounding metadata telescope or by an expression binder. -/
partial def checkKnownNamesInLFExpr (sig : HLSignature) (globals locals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (ownerKind : String) (ownerName : Name)
    (where_ : String) : ObjExpr → CoreM Unit
  | .ident n => do
      let n := n.eraseMacroScopes
      if !(locals.contains n) && !(globals.contains n) then
        if (findObjectMacro? sig n).isSome then
          throwError "object_macro '{n}' in type theory '{sig.name}' is diagnostic-only and \
            cannot appear in checked LF declarations; expand it before writing {where_} of \
              {ownerKind} '{ownerName}'"
        else
          throwError "unknown identifier '{n}' in {where_} of {ownerKind} '{ownerName}' in type \
            theory '{sig.name}'"
      if let some (some arity) := opaqueArities.find? n then
        if arity != 0 then
          throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' uses lf_opaque '{n}' \
            in {where_} with 0 argument(s), expected {arity}"
  | .sort | .univ _ => pure ()
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident head, args) =>
          let head := head.eraseMacroScopes
          if !(locals.contains head) && !(globals.contains head) then
            if (findObjectMacro? sig head).isSome then
              throwError "object_macro '{head}' in type theory '{sig.name}' is diagnostic-only \
                and cannot appear in checked LF declarations; expand it before writing {where_} \
                  of {ownerKind} '{ownerName}'"
            else
              throwError "unknown identifier '{head}' in {where_} of {ownerKind} '{ownerName}' \
                in type theory '{sig.name}'"
          checkLFOpaqueArity sig opaqueArities ownerKind ownerName where_ head args
          for arg in args do
            checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ arg
      | (head, args) =>
          checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ head
          for arg in args do
            checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ arg
  | .arrow x A B | .funArrow x A B => do
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ B
  | .lam xs body => do
      let mut seen : NameSet := {}
      for x in xs do
        let x := x.eraseMacroScopes
        if seen.contains x then
          throwError "duplicate lambda binder '{x}' in {where_} of {ownerKind} '{ownerName}' in \
            type theory '{sig.name}'"
        seen := seen.insert x
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ body
  | .jeq lhs rhs => do
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ lhs
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ rhs

/-- Check known-name use in a metadata telescope, threading earlier binders into scope. -/
def checkKnownNamesInMetadataBindings (sig : HLSignature) (globals : NameSet)
    (opaqueArities : NameMap (Option Nat)) (ownerKind : String) (ownerName : Name)
    (bs : Array HLBinding) : CoreM NameSet := do
  let mut locals : NameSet := {}
  for b in bs do
    checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName
      s!"parameter '{b.name.eraseMacroScopes}' type" b.typeExpr
    locals := locals.insert b.name.eraseMacroScopes
  pure locals

/-- Check that a rule premise/conclusion is syntactically headed by a declared judgment form.

This is a deliberately lightweight Phase-1 validation pass. It does not typecheck the
judgment arguments or interpret side-condition payloads; it catches misspelled judgment
names and obvious arity mismatches in ordinary rule premises and conclusions. -/
def checkRuleJudgmentHead (sig : HLSignature) (judgmentArities : NameMap Nat) (ruleName : Name)
    (where_ : String) (e : ObjExpr) : CoreM CheckedLFHead := do
  match splitObjApp e with
  | (.ident head, args) =>
      let head := head.eraseMacroScopes
      match judgmentArities.find? head with
      | some arity =>
          if args.size != arity then
            throwError "rule '{ruleName}' in type theory '{sig.name}' has {where_} for judgment \
              '{head}' with {args.size} argument(s), expected {arity}"
          pure { name := head, kind := .judgment, arity? := some arity, actualArity := args.size }
      | none =>
          throwError "rule '{ruleName}' in type theory '{sig.name}' has {where_} headed by \
            unknown judgment '{head}'"
  | _ =>
      throwError "rule '{ruleName}' in type theory '{sig.name}' has {where_} not headed by a \
        judgment identifier: {e}"

/-- Find a checked LF rule by name. -/
def findCheckedLFRule? (rules : Array CheckedLFRule) (name : Name) : Option CheckedLFRule :=
  Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for r in rules do
    if r.name == name then
      out := some r
  return out

/-- Find a source LF judgment theorem declaration by name. -/
def findLFJudgmentTheoremDecl? (sig : HLSignature) (name : Name) : Option LFJudgmentTheoremDecl :=
  Id.run do
  let name := name.eraseMacroScopes
  let mut out := none
  for t in sig.lfJudgmentTheorems do
    if t.name.eraseMacroScopes == name then
      out := some t
  return out

/-- Split a checked LF expression application into head and arguments. -/
partial def splitCheckedLFApp (e : CheckedLFExpr) : CheckedLFExpr × Array CheckedLFExpr :=
  let rec go (e : CheckedLFExpr) (args : Array CheckedLFExpr) :=
    match e with
    | .app f a => go f (args.push a)
    | e => (e, args.reverse)
  go e #[]

/-- Values of checked LF definitions available while normalizing checked LF expressions. -/
abbrev CheckedLFDefinitionValueMap := NameMap CheckedLFExpr

/-- Free checked local identifiers in a checked LF expression. -/
partial def freeCheckedLFLocalIdentifiers : CheckedLFExpr → NameSet
  | .ident h =>
      if h.kind == .local then ({} : NameSet).insert h.name.eraseMacroScopes else {}
  | .sort | .univ _ => {}
  | .app f a => freeCheckedLFLocalIdentifiers f ++ freeCheckedLFLocalIdentifiers a
  | .arrow x A B =>
      let free := freeCheckedLFLocalIdentifiers A ++ freeCheckedLFLocalIdentifiers B
      match x with
      | some x => free.erase x.eraseMacroScopes
      | none => free
  | .lam xs body =>
      xs.foldl (fun free x => free.erase x.eraseMacroScopes) (freeCheckedLFLocalIdentifiers body)
  | .jeq lhs rhs => freeCheckedLFLocalIdentifiers lhs ++ freeCheckedLFLocalIdentifiers rhs

/-- Rename occurrences of a checked local binder, respecting nested binders. -/
partial def renameCheckedLFBoundOccurrences (oldName newName : Name) :
    CheckedLFExpr → CheckedLFExpr
  | .ident h =>
      if h.kind == .local && h.name.eraseMacroScopes == oldName.eraseMacroScopes then
        .ident { h with name := newName.eraseMacroScopes }
      else
        .ident h
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (renameCheckedLFBoundOccurrences oldName newName f)
      (renameCheckedLFBoundOccurrences oldName newName a)
  | .arrow x A B =>
      let A := renameCheckedLFBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            renameCheckedLFBoundOccurrences oldName newName B
          .arrow (some x) A B
      | none => .arrow none A (renameCheckedLFBoundOccurrences oldName newName B)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      let body := if clean.contains oldName.eraseMacroScopes then body else
        renameCheckedLFBoundOccurrences oldName newName body
      .lam clean body
  | .jeq lhs rhs => .jeq (renameCheckedLFBoundOccurrences oldName newName lhs)
      (renameCheckedLFBoundOccurrences oldName newName rhs)

/-- Substitute one checked LF parameter, alpha-renaming binders when needed. -/
partial def substSingleCheckedLFParam (x : Name) (value : CheckedLFExpr) :
    CheckedLFExpr → CheckedLFExpr
  | .ident h =>
      if h.kind == .local && h.name.eraseMacroScopes == x.eraseMacroScopes then value else .ident h
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (substSingleCheckedLFParam x value f) (substSingleCheckedLFParam x value a)
  | .arrow y A B =>
      let A := substSingleCheckedLFParam x value A
      match y with
      | some y =>
          let y := y.eraseMacroScopes
          if y == x.eraseMacroScopes then
            .arrow (some y) A B
          else
            let (y, B) :=
              if (freeCheckedLFLocalIdentifiers value).contains y &&
                  (freeCheckedLFLocalIdentifiers B).contains x.eraseMacroScopes then
                let avoid := freeCheckedLFLocalIdentifiers value ++ freeCheckedLFLocalIdentifiers B
                  |>.insert y
                let y' := freshLFNameAvoiding y avoid
                (y', renameCheckedLFBoundOccurrences y y' B)
              else
                (y, B)
            .arrow (some y) A (substSingleCheckedLFParam x value B)
      | none => .arrow none A (substSingleCheckedLFParam x value B)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      if clean.contains x.eraseMacroScopes then
        .lam clean body
      else
        let (clean, body) := Id.run do
          let mut out := #[]
          let mut body := body
          for y in clean do
            if (freeCheckedLFLocalIdentifiers value).contains y &&
                (freeCheckedLFLocalIdentifiers body).contains x.eraseMacroScopes then
              let avoid := freeCheckedLFLocalIdentifiers value ++ freeCheckedLFLocalIdentifiers body
                |>.insert y
              let y' := freshLFNameAvoiding y avoid
              body := renameCheckedLFBoundOccurrences y y' body
              out := out.push y'
            else
              out := out.push y
          return (out, body)
        .lam clean (substSingleCheckedLFParam x value body)
  | .jeq lhs rhs =>
      .jeq (substSingleCheckedLFParam x value lhs) (substSingleCheckedLFParam x value rhs)

/-- Free checked local identifiers occurring in checked LF-definition values. -/
def checkedLFDefinitionValuesFreeIdentifiers (defs : CheckedLFDefinitionValueMap) : NameSet :=
  Id.run do
  let mut out : NameSet := {}
  for (_, value) in defs.toList do
    out := out ++ freeCheckedLFLocalIdentifiers value
  return out

/-- Freshen a checked binder before unfolding checked definitions. -/
def freshCheckedLFUnfoldBinder (defs : CheckedLFDefinitionValueMap) (locals : NameSet)
    (binder : Name) (body : CheckedLFExpr) : Name × CheckedLFExpr :=
  let binder := binder.eraseMacroScopes
  let defFree := checkedLFDefinitionValuesFreeIdentifiers defs
  if defFree.contains binder || locals.contains binder then
    let avoid := freeCheckedLFLocalIdentifiers body ++ defFree ++ locals |>.insert binder
    let binder' := freshLFNameAvoiding binder avoid
    (binder', renameCheckedLFBoundOccurrences binder binder' body)
  else
    (binder, body)

/-- Unfold checked LF-definition aliases in a checked expression, respecting local binders. -/
partial def unfoldLFDefinitionsInCheckedExprCore (defs : CheckedLFDefinitionValueMap)
    (locals : NameSet) (fuel : Nat) : CheckedLFExpr → CheckedLFExpr
  | e =>
      match fuel with
      | 0 => e
      | fuel + 1 =>
          match e with
          | .ident h =>
              let key := h.name.eraseMacroScopes
              if locals.contains key then
                .ident { h with name := key }
              else
                match defs.find? key with
                | some value => unfoldLFDefinitionsInCheckedExprCore defs locals fuel value
                | none => .ident { h with name := key }
          | .sort => .sort
          | .univ u => .univ u
          | .app f a =>
              let f := unfoldLFDefinitionsInCheckedExprCore defs locals fuel f
              let a := unfoldLFDefinitionsInCheckedExprCore defs locals fuel a
              match f with
              | .lam xs body =>
                  if h : 0 < xs.size then
                    let x := xs[0]
                    let rest := xs.extract 1 xs.size
                    let body := substSingleCheckedLFParam x a body
                    let reduced := if rest.isEmpty then body else .lam rest body
                    unfoldLFDefinitionsInCheckedExprCore defs locals fuel reduced
                  else
                    .app f a
              | _ => .app f a
          | .arrow x A B =>
              let A := unfoldLFDefinitionsInCheckedExprCore defs locals fuel A
              match x with
              | some x =>
                  let (x, B) := freshCheckedLFUnfoldBinder defs locals x B
                  let locals := locals.insert x.eraseMacroScopes
                  .arrow (some x) A (unfoldLFDefinitionsInCheckedExprCore defs locals fuel B)
              | none => .arrow none A (unfoldLFDefinitionsInCheckedExprCore defs locals fuel B)
          | .lam xs body =>
              let (xs, body, locals) := Id.run do
                let mut out := #[]
                let mut body := body
                let mut locals := locals
                for x in xs.map Name.eraseMacroScopes do
                  let (x, body') := freshCheckedLFUnfoldBinder defs locals x body
                  out := out.push x
                  body := body'
                  locals := locals.insert x.eraseMacroScopes
                return (out, body, locals)
              .lam xs (unfoldLFDefinitionsInCheckedExprCore defs locals fuel body)
          | .jeq lhs rhs =>
              .jeq (unfoldLFDefinitionsInCheckedExprCore defs locals fuel lhs)
                (unfoldLFDefinitionsInCheckedExprCore defs locals fuel rhs)

/-- Deterministically unfold checked LF definitions in a checked expression. -/
def unfoldLFDefinitionsInCheckedExpr (defs : CheckedLFDefinitionValueMap) (locals : NameSet)
    (e : CheckedLFExpr) : CheckedLFExpr :=
  unfoldLFDefinitionsInCheckedExprCore defs locals (defs.size * 4 + 32) e

/-- Convert a checked LF expression to low-level kernel syntax.

This is deliberately lossy and diagnostic/staging-oriented: it preserves head names and
application structure without claiming a certified LF typing derivation. -/
partial def checkedLFExprToRaw : CheckedLFExpr → Raw
  | .ident h =>
      match h.kind with
      | .local => .leanParam h.name
      | .syntaxSort => .tyConst h.name
      | .lfDefinition | .lfTheorem | .lfRule => .tmConst h.name
      | .judgment => .leanParam h.name
      | .primitive | .definition | .theorem | .opaque => .tmConst h.name
  | .sort => .tyConst `Type
  | .univ u => .tyApp `Type [.leanParam (.str .anonymous u.toString)]
  | e@(.app _ _) =>
      let (head, args) := splitCheckedLFApp e
      let rawArgs := args.map checkedLFExprToRaw |>.toList
      match head with
      | .ident h =>
          match h.kind with
          | .syntaxSort => .tyApp h.name rawArgs
          | .local => .tmApp h.name rawArgs
          | .lfDefinition | .lfTheorem | .lfRule => .tmApp h.name rawArgs
          | .judgment => .tmApp h.name rawArgs
          | .primitive | .definition | .theorem | .opaque => .tmApp h.name rawArgs
      | other => .tmApp `_app (checkedLFExprToRaw other :: rawArgs)
  | .arrow _ A B => .tyApp `arrow [checkedLFExprToRaw A, checkedLFExprToRaw B]
  | .lam xs body => .tmApp `lam ((xs.toList.map Raw.leanParam) ++ [checkedLFExprToRaw body])
  | .jeq lhs rhs => .tmApp `jeq [checkedLFExprToRaw lhs, checkedLFExprToRaw rhs]

/-- Convert a checked LF judgment-headed expression into a low-level custom judgment. -/
def checkedLFJudgmentExprToKernel (e : CheckedLFExpr) (head : CheckedLFHead) : Judgment :=
  let (_, args) := splitCheckedLFApp e
  .custom head.name (args.toList.map checkedLFExprToRaw)

/-- Expected Phase-3 certificate name for a rule side-condition slot. -/
def lfSideConditionCertificateName (ruleName sideConditionName : Name) : Name :=
  .str (.str ruleName.eraseMacroScopes "side_condition") (
    toString sideConditionName.eraseMacroScopes)

/-- Push a name into a diagnostic list once, modulo macro scopes. -/
def pushUniqueDiagnosticName (xs : Array Name) (n : Name) : Array Name :=
  let n := n.eraseMacroScopes
  if xs.contains n then xs else xs.push n

/-- Collect LF-definition names syntactically mentioned in an expression, respecting local binders.
-/
partial def collectLFDefinitionMentions (defs : LFDefinitionValueMap) (locals : NameSet)
    (acc : Array Name) : ObjExpr → Array Name
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then acc else if (defs.find? n).isSome then
        pushUniqueDiagnosticName acc n else acc
  | .sort | .univ _ => acc
  | .app f a =>
    collectLFDefinitionMentions defs locals (collectLFDefinitionMentions defs locals acc f) a
  | .arrow x A B | .funArrow x A B =>
      let acc := collectLFDefinitionMentions defs locals acc A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      collectLFDefinitionMentions defs locals acc B
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      collectLFDefinitionMentions defs locals acc body
  | .jeq lhs rhs =>
    collectLFDefinitionMentions defs locals (collectLFDefinitionMentions defs locals acc lhs) rhs

/-- Collect LF definitions actually expanded by bounded unfolding diagnostics. -/
partial def collectLFDefinitionUnfoldsCore (defs : LFDefinitionValueMap) (locals : NameSet)
    (fuel : Nat) (acc : Array Name) : ObjExpr → Array Name
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        acc
      else
        match fuel, defs.find? n with
        | 0, _ | _, none => acc
        | fuel + 1, some value =>
            collectLFDefinitionUnfoldsCore defs locals fuel (pushUniqueDiagnosticName acc n)
              value
  | .sort | .univ _ => acc
  | .app f a =>
      collectLFDefinitionUnfoldsCore defs locals fuel
        (collectLFDefinitionUnfoldsCore defs locals fuel acc f) a
  | .arrow x A B | .funArrow x A B =>
      let acc := collectLFDefinitionUnfoldsCore defs locals fuel acc A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      collectLFDefinitionUnfoldsCore defs locals fuel acc B
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      collectLFDefinitionUnfoldsCore defs locals fuel acc body
  | .jeq lhs rhs =>
      collectLFDefinitionUnfoldsCore defs locals fuel
        (collectLFDefinitionUnfoldsCore defs locals fuel acc lhs) rhs

/-- Collect LF definitions expanded by the same bounded unfolding policy used for matching. -/
def collectLFDefinitionUnfolds (defs : LFDefinitionValueMap) (locals : NameSet)
    (acc : Array Name) (e : ObjExpr) : Array Name :=
  collectLFDefinitionUnfoldsCore defs locals (lfDefinitionUnfoldFuel defs) acc e

/-- Equality modulo macro scopes and checked LF-definition unfolding under local binders. -/
def lfExprEqModuloDefinitionsWithLocals (defs : LFDefinitionValueMap) (locals : NameSet)
    (a b : ObjExpr) : Bool :=
  lfExprAlphaEq (unfoldLFDefinitionsInExprWithLocals defs locals a)
    (unfoldLFDefinitionsInExprWithLocals defs locals b)

/-- Equality modulo macro scopes and checked LF-definition unfolding. -/
def lfExprEqModuloDefinitions (defs : LFDefinitionValueMap) (a b : ObjExpr) : Bool :=
  lfExprEqModuloDefinitionsWithLocals defs {} a b

/-- Stable comma-separated diagnostic rendering of LF definition names. -/
def diagnosticNameListString (xs : Array Name) : String :=
  if xs.isEmpty then "none" else String.intercalate ", " (xs.toList.map toString)

/-- Rich diagnostic for failed LF-definition/beta normalization matching. -/
def lfDefinitionNormalizationMismatchMessage (defs : LFDefinitionValueMap) (locals : NameSet)
    (actual expected : ObjExpr) : MessageData :=
  let actualN := unfoldLFDefinitionsInExprWithLocals defs locals actual
  let expectedN := unfoldLFDefinitionsInExprWithLocals defs locals expected
  let mentioned :=
    collectLFDefinitionMentions defs locals (collectLFDefinitionMentions defs locals #[] actual)
      expected
  let unfolded :=
    collectLFDefinitionUnfolds defs locals (collectLFDefinitionUnfolds defs locals #[] actual)
      expected
  let remaining :=
    collectLFDefinitionMentions defs locals (collectLFDefinitionMentions defs locals #[] actualN)
      expectedN
  let remainingLines :=
    if remaining.isEmpty then []
    else [s!"Definition head(s) still present after bounded unfolding: \
      {diagnosticNameListString remaining}. This can indicate a cycle, depth-limit hit, \
      or compact-certificate artifact missing an explicit unfolding step."]
  let lines := [
    "LF-definition normalization could not match expressions.",
    s!"actual: {diagnosticObjExprString actual}",
    s!"expected: {diagnosticObjExprString expected}",
    s!"normalized actual: {diagnosticObjExprString actualN}",
    s!"normalized expected: {diagnosticObjExprString expectedN}",
    s!"LF definitions mentioned before unfolding: {diagnosticNameListString mentioned}",
    s!"LF definitions unfolded: {diagnosticNameListString unfolded}"] ++
      remainingLines ++ [
    "Normalization policy: LF matching unfolds earlier checked `lf_def` values, beta-reduces",
    "explicit LF lambdas, and alpha-renames binders to avoid local-binder capture."]
  m!"{String.intercalate "\n" lines}"

/-- Shallow rule-application metadata collected at the outermost theorem proof. -/
structure LFRuleApplicationSummary where
  /-- Applied rule name, if the outer proof is rule-headed. -/
  proofRule? : Option Name := none
  /-- Explicit rule metavariable arguments supplied by the proof expression. -/
  proofRuleArgs : Array ObjExpr := #[]
  /-- Premise theorem references occurring immediately under the outer rule application. -/
  premiseTheorems : Array Name := #[]
  /-- Side-condition certificate names matched from the applied rule schema. -/
  sideConditionCertificateNames : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- Shallowly validate a `judgment_theorem` proof against an expected custom judgment.

A proof may be a theorem reference whose statement matches the expected judgment, or a
rule application. In a rule application, the first arguments instantiate the rule
parameter telescope and the remaining arguments are recursively checked premise
derivations. Side-condition certificates are matched from executable side-condition slots;
currently only the built-in trivial hook yields such certificates. This is intentionally
still syntactic replay, not a trusted LF kernel. -/
partial def checkLFJudgmentDerivation (sig : HLSignature) (rules : Array CheckedLFRule)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (defValues : LFDefinitionValueMap) (localNames : NameSet)
    (availableLocalStatements availableTheoremStatements : NameMap ObjExpr)
    (availableTheoremNames : NameSet) (theoremName : Name) (expectedStatement proof : ObjExpr) :
      CoreM (Option CheckedLFDerivation) := do
  let some proofHead := checkedLFHead? globalHeads localNames proof
    | return none
  match proofHead.kind with
  | .local =>
      let localName := proofHead.name
      match availableLocalStatements.find? localName.eraseMacroScopes with
      | some actualStatement =>
          let expectedStatement := eraseObjExprScopes expectedStatement
          if !lfExprEqModuloDefinitionsWithLocals defValues localNames actualStatement
            expectedStatement then
            let mentioned :=
              collectLFDefinitionMentions defValues localNames (collectLFDefinitionMentions
                defValues localNames #[] actualStatement) expectedStatement
            if mentioned.isEmpty then
              throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses \
                local theorem assumption '{localName}' with statement \
                '{diagnosticObjExprString actualStatement}', expected \
                '{diagnosticObjExprString expectedStatement}'"
            else
              let mismatch :=
                lfDefinitionNormalizationMismatchMessage defValues localNames actualStatement
                  expectedStatement
              throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses \
                local theorem assumption '{localName}' with a statement that does not match after \
                LF-definition normalization:\n{mismatch}"
          return some (.localAssumption localName actualStatement)
      | none =>
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses local \
            parameter '{localName}' as a proof, but that local is not a judgment assumption"
  | .lfTheorem =>
      let theoremRefName := proofHead.name
      let some premiseTheorem := findLFJudgmentTheoremDecl? sig theoremRefName
        | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses unknown \
          premise theorem '{theoremRefName}'"
      unless availableTheoremNames.contains theoremRefName.eraseMacroScopes do
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses premise \
          theorem '{theoremRefName}' before it is available"
      let (_, proofArgs) := splitObjApp proof
      if proofArgs.size != premiseTheorem.binders.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies premise \
          theorem '{theoremRefName}' with {proofArgs.size} argument(s), expected \
            {premiseTheorem.binders.size} local binder argument(s)"
      let mut subst : NameMap ObjExpr := {}
      let mut theoremArgs : Array ObjExpr := #[]
      let mut premiseDerivations : Array CheckedLFDerivation := #[]
      for b in premiseTheorem.binders, arg in proofArgs do
        let expectedBinderType := eraseObjExprScopes (substLFParams subst b.typeExpr)
        let some binderHead := checkedLFHead? globalHeads localNames expectedBinderType
          | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
            premise theorem '{theoremRefName}' but binder '{b.name.eraseMacroScopes}' has type \
              not headed by a known LF identifier: {expectedBinderType}"
        if binderHead.kind == .judgment then
          let some premiseDeriv ←
            checkLFJudgmentDerivation sig rules globalHeads knownTypes defValues localNames
              availableLocalStatements availableTheoremStatements availableTheoremNames theoremName
              expectedBinderType arg
            | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
              premise theorem '{theoremRefName}' with unchecked proof argument '{arg}' for local \
                hypothesis '{b.name.eraseMacroScopes}'"
          premiseDerivations := premiseDerivations.push premiseDeriv
        else
          checkLFKnownArgumentType sig "judgment_theorem" theoremName
            s!"argument for premise theorem '{theoremRefName}' binder \
              '{b.name.eraseMacroScopes}'" knownTypes arg expectedBinderType
          checkLFInferableApplicationArguments sig "judgment_theorem" theoremName
            s!"argument for premise theorem '{theoremRefName}' binder \
              '{b.name.eraseMacroScopes}'" knownTypes arg
          checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" theoremName
            s!"argument for premise theorem '{theoremRefName}' binder \
              '{b.name.eraseMacroScopes}'" knownTypes arg
          theoremArgs := theoremArgs.push (eraseObjExprScopes arg)
          subst := subst.insert b.name.eraseMacroScopes (eraseObjExprScopes arg)
      let actualStatement := eraseObjExprScopes (substLFParams subst premiseTheorem.judgmentExpr)
      let expectedStatement := eraseObjExprScopes expectedStatement
      if !lfExprEqModuloDefinitionsWithLocals defValues localNames actualStatement
        expectedStatement then
        let mentioned :=
          collectLFDefinitionMentions defValues localNames (collectLFDefinitionMentions defValues
            localNames #[] actualStatement) expectedStatement
        if mentioned.isEmpty then
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses \
            premise theorem '{theoremRefName}' with statement \
            '{diagnosticObjExprString actualStatement}', expected \
            '{diagnosticObjExprString expectedStatement}'"
        else
          let mismatch :=
            lfDefinitionNormalizationMismatchMessage defValues localNames actualStatement
              expectedStatement
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses premise \
            theorem '{theoremRefName}' with a statement that does not match after LF-definition \
            normalization:\n{mismatch}"
      let replayStatement :=
        if premiseTheorem.binders.isEmpty then
          (availableTheoremStatements.find? theoremRefName.eraseMacroScopes).getD actualStatement
        else
          actualStatement
      return some (.theoremRef theoremRefName replayStatement theoremArgs premiseDerivations)
  | .lfRule =>
      let ruleName := proofHead.name
      let some appliedRule := findCheckedLFRule? rules ruleName
        | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses unknown \
          LF rule '{ruleName}' as proof head"
      let (_, proofArgs) := splitObjApp proof
      let expectedArgs := appliedRule.params.size + appliedRule.premises.size
      if proofArgs.size != expectedArgs then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies rule \
          '{ruleName}' with {proofArgs.size} argument(s), expected {expectedArgs} \
            ({appliedRule.params.size} parameter argument(s) and {appliedRule.premises.size} \
              premise derivation(s))"
      let ruleArgs := proofArgs[:appliedRule.params.size]
      let premiseArgs := proofArgs[appliedRule.params.size:]
      let mut subst : NameMap ObjExpr := {}
      for param in appliedRule.params, arg in ruleArgs do
        let expectedParamType := substLFParams subst param.typeExpr
        checkLFKnownArgumentType sig "judgment_theorem" theoremName
          s!"proof argument for rule '{ruleName}' parameter \
            '{param.name}'" knownTypes arg expectedParamType
        checkLFInferableApplicationArguments sig "judgment_theorem" theoremName
          s!"proof argument for rule '{ruleName}' parameter '{param.name}'" knownTypes arg
        checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" theoremName
          s!"proof argument for rule '{ruleName}' parameter '{param.name}'" knownTypes arg
        subst := subst.insert param.name (eraseObjExprScopes arg)
      let expectedConclusion := eraseObjExprScopes (substLFParams subst appliedRule.conclusionExpr)
      let actualStatement := eraseObjExprScopes expectedStatement
      if !lfExprEqModuloDefinitionsWithLocals defValues localNames actualStatement
        expectedConclusion then
        let mentioned :=
          collectLFDefinitionMentions defValues localNames (collectLFDefinitionMentions defValues
            localNames #[] actualStatement) expectedConclusion
        if mentioned.isEmpty then
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
            rule '{ruleName}' but its statement is '{diagnosticObjExprString actualStatement}', \
            expected rule conclusion '{diagnosticObjExprString expectedConclusion}'"
        else
          let mismatch :=
            lfDefinitionNormalizationMismatchMessage defValues localNames actualStatement
              expectedConclusion
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies rule \
            '{ruleName}' but the statement does not match the rule conclusion after \
            LF-definition normalization:\n{mismatch}"
      let mut premiseDerivations := #[]
      for p in appliedRule.premises, arg in premiseArgs do
        let expectedPremise := eraseObjExprScopes (substLFParams subst p.judgmentExpr)
        let some premiseDeriv ←
          checkLFJudgmentDerivation sig rules globalHeads knownTypes defValues localNames
            availableLocalStatements availableTheoremStatements availableTheoremNames theoremName
            expectedPremise arg
          | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
              rule '{ruleName}' with unchecked premise proof argument \
              '{diagnosticObjExprString arg}' for expected premise \
              '{diagnosticObjExprString expectedPremise}'"
        premiseDerivations := premiseDerivations.push premiseDeriv
      let mut sideCertificateNames := #[]
      for sc in appliedRule.sideConditions do
        match classifySideConditionHook sc.solver with
        | .opaque =>
            throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies rule \
              '{ruleName}' but side-condition '{sc.name}' uses opaque solver '{sc.solver}' with \
                no checked certificate"
        | .builtinTrivial =>
            sideCertificateNames :=
              sideCertificateNames.push (lfSideConditionCertificateName appliedRule.name sc.name)
      return some (.ruleApp ruleName expectedConclusion ruleArgs premiseDerivations
        sideCertificateNames)
  | _ =>
      return none

/-- Extract the conclusion/statement carried by a kernel-facing derivation tree. -/
def kernelLFDerivationStatement : KernelLFDerivation → Judgment
  | .assumption _ stmt => stmt
  | .theoremRef _ stmt => stmt
  | .certificate _ stmt _ => stmt
  | .ruleApp _ concl _ _ _ => concl

/-- Alpha-equivalence for kernel-facing judgments. -/
def judgmentAlphaEq : Judgment → Judgment → Bool :=
  Judgment.alphaEq

/-- Internal kernel rule name used to replay an instantiated locally quantified LF theorem. -/
def lfJudgmentTheoremKernelRuleName (theoremName : Name) : Name :=
  `_lfTheoremRule ++ theoremName.eraseMacroScopes

/-- Convert a source custom-judgment expression to the low-level kernel-facing judgment
shape, reusing the same head/arity checks as LF rule metadata. -/
def lfJudgmentObjExprToKernel (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (e : ObjExpr) (locals : NameSet := {}) : CoreM Judgment := do
  let judgmentArities : NameMap Nat := sig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let head ← checkRuleJudgmentHead sig judgmentArities ownerName ownerKind e
  let checked ← resolveLFExpr sig globalHeads locals ownerKind ownerName "kernel-facing statement" e
  pure (checkedLFJudgmentExprToKernel checked head)

/-- Infer the unique source context zone for a syntax-sort-headed rule parameter, if any.

This helper intentionally uses the flattened source signature rather than the later checked
rule-schema artifact because kernel-facing derivation lowering happens before we have the
final checked signature value available. -/
def inferLFParamZoneFromSignature? (sig : HLSignature) (param : CheckedLFBinding) : Option Name :=
  do
  let h ← param.head?
  if h.kind != .syntaxSort then
    none
  else
    let sortName := h.name.eraseMacroScopes
    let candidates := sig.contextZones.filter (fun z => z.sortName.eraseMacroScopes == sortName)
    if candidates.size == 1 then
      some candidates[0]!.name.eraseMacroScopes
    else
      none

/-- Infer the unique source binder class for a syntax-sort-headed rule parameter, if any. -/
def inferLFParamBinderClassFromSignature? (sig : HLSignature) (param : CheckedLFBinding)
    (zoneName : Name) : Option Name := do
  let h ← param.head?
  if h.kind != .syntaxSort then
    none
  else
    let sortName := h.name.eraseMacroScopes
    let zoneName := zoneName.eraseMacroScopes
    let candidates := sig.binderClasses.filter (fun b =>
      b.boundSortName.eraseMacroScopes == sortName && b.zoneName.eraseMacroScopes == zoneName)
    if candidates.size == 1 then
      some candidates[0]!.name.eraseMacroScopes
    else
      none

/-- Lower a shallow checked LF derivation to a kernel-facing derivation tree with low-level
judgments, scoped typed instantiations, and explicit certificate names.

This is still a staging checker, not a trusted-evidence producer, but it is intentionally closer
to the eventual trusted kernel boundary: rule instantiations are finite typed telescopes and
premise/conclusion matching is replayed on instantiated low-level `Judgment`s. -/
partial def lowerLFDerivationToKernel (sig : HLSignature) (rules : Array CheckedLFRule)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name) :
    CheckedLFDerivation → CoreM KernelLFDerivation
  | .localAssumption name stmt => do
      let kernelStmtExpr := unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
      let kernelStmt ← lfJudgmentObjExprToKernel sig globalHeads "local theorem assumption"
        theoremName kernelStmtExpr localNames
      match kernelStmt.validateBuiltinConstructorDiscipline s!"judgment_theorem '{theoremName}' \
        in type theory '{sig.name}'" s!"kernel-facing local theorem assumption '{name}'" with
      | .ok () => pure ()
      | .error err => throwError err
      pure (.assumption name kernelStmt)
  | .theoremRef name stmt args premises => do
      let kernelStmtExpr := unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
      let kernelStmt ← lfJudgmentObjExprToKernel sig globalHeads "theorem reference" theoremName
        kernelStmtExpr localNames
      match kernelStmt.validateBuiltinConstructorDiscipline s!"judgment_theorem '{theoremName}' \
        in type theory '{sig.name}'" s!"kernel-facing theorem reference '{name}'" with
      | .ok () => pure ()
      | .error err => throwError err
      if args.isEmpty && premises.isEmpty then
        pure (.theoremRef name kernelStmt)
      else
        let some appliedTheorem := findLFJudgmentTheoremDecl? sig name
          | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
            unknown theorem reference '{name}'"
        let mut entries := []
        let mut rawSubst : NameMap Raw := {}
        let mut objSubst : NameMap ObjExpr := {}
        let mut argIndex := 0
        for b in appliedTheorem.binders do
          let expectedBinderType := eraseObjExprScopes (substLFParams objSubst b.typeExpr)
          let some binderHead := checkedLFHead? globalHeads localNames expectedBinderType
            | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
              theorem reference '{name}' but binder '{b.name.eraseMacroScopes}' has type not \
                headed by a known LF identifier: {expectedBinderType}"
          unless binderHead.kind == .judgment do
            let some arg := args[argIndex]?
              | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
                theorem reference '{name}' with too few syntax arguments"
            let priorInst : Instantiation := fun x =>
              (rawSubst.find? x.eraseMacroScopes).getD (.leanParam x)
            let kernelArg := unfoldLFDefinitionsInExprWithLocals defValues localNames arg
            let kernelExpectedBinderType :=
              unfoldLFDefinitionsInExprWithLocals defValues localNames expectedBinderType
            let checkedArg ← resolveLFExpr sig globalHeads localNames
              "kernel-facing theorem reference" theoremName
              s!"argument for theorem '{name}' binder '{b.name.eraseMacroScopes}'" kernelArg
            let checkedArgRaw := checkedLFExprToRaw checkedArg
            let checkedBinderType ← resolveLFExpr sig globalHeads localNames
              "kernel-facing theorem reference" theoremName
              s!"type of theorem '{name}' binder '{b.name.eraseMacroScopes}'"
              kernelExpectedBinderType
            let sort := if binderHead.kind == .syntaxSort then
              RawMetaSort.custom binderHead.name else .arg
            entries := entries ++ [{
              name := b.name.eraseMacroScopes
              sort := sort
              zone? := none
              type? := some (Raw.instantiate priorInst (checkedLFExprToRaw checkedBinderType))
              evidence? := none
              value := checkedArgRaw }]
            rawSubst := rawSubst.insert b.name.eraseMacroScopes checkedArgRaw
            objSubst := objSubst.insert b.name.eraseMacroScopes kernelArg
            argIndex := argIndex + 1
        if argIndex != args.size then
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers theorem \
            reference '{name}' with unused syntax arguments"
        let mut loweredPremises := []
        for premiseDeriv in premises do
          loweredPremises := loweredPremises ++
            [← lowerLFDerivationToKernel sig rules globalHeads knownTypes defValues localNames
              theoremName premiseDeriv]
        pure (.ruleApp (lfJudgmentTheoremKernelRuleName name) kernelStmt { entries := entries }
          loweredPremises [])
  | .ruleApp ruleName stmt ruleArgs premises certs => do
      let some appliedRule := findCheckedLFRule? rules ruleName
        | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers unknown \
          LF rule '{ruleName}'"
      if ruleArgs.size != appliedRule.params.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with {ruleArgs.size} scoped instantiation entry/entries, expected \
            {appliedRule.params.size}"
      if premises.size != appliedRule.premises.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with {premises.size} premise derivation(s), expected \
            {appliedRule.premises.size}"
      let mut entries := []
      let mut rawSubst : NameMap Raw := {}
      let mut objSubst : NameMap ObjExpr := {}
      for param in appliedRule.params, arg in ruleArgs do
        let priorInst : Instantiation := fun x =>
          (rawSubst.find? x.eraseMacroScopes).getD (.leanParam x)
        let expectedParamType := substLFParams objSubst param.typeExpr
        let kernelArg := unfoldLFDefinitionsInExprWithLocals defValues localNames arg
        checkLFExprHasType sig "judgment_theorem" theoremName
          s!"kernel-facing replay argument for rule '{ruleName}' parameter '{param.name}'"
          knownTypes arg expectedParamType
        checkLFInferableApplicationArguments sig "judgment_theorem" theoremName
          s!"kernel-facing replay argument for rule '{ruleName}' parameter '{param.name}'"
          knownTypes arg
        let checkedArg ← resolveLFExpr sig globalHeads localNames "kernel-facing derivation"
          theoremName s!"argument for '{param.name}'" kernelArg
        let checkedArgRaw := checkedLFExprToRaw checkedArg
        let sort := match param.head? with
          | some h => if h.kind == .syntaxSort then RawMetaSort.custom h.name else .arg
          | none => .arg
        let zone? := inferLFParamZoneFromSignature? sig param
        let _binderClass? := zone?.bind (inferLFParamBinderClassFromSignature? sig param)
        let rawSubstWithCurrent : NameMap Raw :=
          rawSubst.insert param.name.eraseMacroScopes checkedArgRaw
        let entryInst : Instantiation := fun x =>
          (rawSubstWithCurrent.find? x.eraseMacroScopes).getD (.leanParam x)
        let evidenceOpt ←
          match appliedRule.paramEvidences.find? (fun ev =>
            ev.paramName == param.name.eraseMacroScopes) with
          | none => pure none
          | some ev => do
              let evidenceTemplate := checkedLFJudgmentExprToKernel ev.checkedJudgmentExpr ev.head
              match evidenceTemplate.instantiateChecked entryInst with
              | .ok evJudgment => pure (some evJudgment)
              | .error err =>
                throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
                  kernel-facing replay of rule '{ruleName}' has capture-unsafe evidence for \
                    parameter '{param.name}': {err}"
        entries := entries ++ [{
          name := param.name
          sort := sort
          zone? := zone?
          type? := some (Raw.instantiate priorInst (checkedLFExprToRaw param.checkedTypeExpr))
          evidence? := evidenceOpt
          value := checkedArgRaw }]
        rawSubst := rawSubstWithCurrent
        objSubst := objSubst.insert param.name.eraseMacroScopes kernelArg
      let inst : ScopedInstantiation := { entries := entries }
      let kernelStmtExpr := unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
      let kernelStmt ← lfJudgmentObjExprToKernel sig globalHeads "rule application" theoremName
        kernelStmtExpr localNames
      match kernelStmt.validateBuiltinConstructorDiscipline s!"judgment_theorem '{theoremName}' \
        in type theory '{sig.name}'" s!"kernel-facing replay statement for rule '{ruleName}'" with
      | .ok () => pure ()
      | .error err => throwError err
      let ruleLocals : NameSet := appliedRule.params.foldl (init := {}) fun acc p =>
        acc.insert p.name
      let ruleConclusionExpr :=
        unfoldLFDefinitionsInExprWithLocals defValues ruleLocals appliedRule.conclusionExpr
      let ruleConclusion ← lfJudgmentObjExprToKernel sig globalHeads "rule conclusion"
        appliedRule.name ruleConclusionExpr ruleLocals
      let expectedConclusion ←
        match ruleConclusion.instantiateChecked inst.asInstantiation with
        | .ok expectedConclusion => pure expectedConclusion
        | .error err =>
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' kernel-facing \
            replay of rule '{ruleName}' has capture-unsafe conclusion instantiation: {err}"
      match expectedConclusion.validateBuiltinConstructorDiscipline s!"judgment_theorem \
        '{theoremName}' in type theory '{sig.name}'" s!"kernel-facing replay conclusion for rule \
          '{ruleName}'" with
      | .ok () => pure ()
      | .error err => throwError err
      if !judgmentAlphaEq kernelStmt expectedConclusion then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' kernel-facing \
          replay of rule '{ruleName}' has conclusion '{reprStr kernelStmt}', expected \
            instantiated rule conclusion '{reprStr expectedConclusion}'"
      let mut loweredPremises := []
      for p in appliedRule.premises, premiseDeriv in premises do
        let lowered ← lowerLFDerivationToKernel sig rules globalHeads knownTypes defValues
          localNames theoremName premiseDeriv
        let rulePremiseExpr :=
          unfoldLFDefinitionsInExprWithLocals defValues ruleLocals p.judgmentExpr
        let rulePremise ← lfJudgmentObjExprToKernel sig globalHeads "rule premise"
          appliedRule.name rulePremiseExpr ruleLocals
        let expectedPremise ←
          match rulePremise.instantiateChecked inst.asInstantiation with
          | .ok expectedPremise => pure expectedPremise
          | .error err =>
            throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
              kernel-facing replay of rule '{ruleName}' has capture-unsafe premise instantiation: \
                {err}"
        match expectedPremise.validateBuiltinConstructorDiscipline s!"judgment_theorem \
          '{theoremName}' in type theory '{sig.name}'" s!"kernel-facing replay premise for rule \
            '{ruleName}'" with
        | .ok () => pure ()
        | .error err => throwError err
        let actualPremise := kernelLFDerivationStatement lowered
        if !judgmentAlphaEq actualPremise expectedPremise then
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' kernel-facing \
            replay of rule '{ruleName}' has premise '{reprStr actualPremise}', expected \
              instantiated premise '{reprStr expectedPremise}'"
        loweredPremises := loweredPremises ++ [lowered]
      pure (.ruleApp ruleName kernelStmt inst loweredPremises certs.toList)

/-- Summarize the outer layer of a shallow checked LF derivation for legacy diagnostics. -/
def summarizeLFRuleApplication? : CheckedLFDerivation → LFRuleApplicationSummary
  | .localAssumption .. => {}
  | .theoremRef .. => {}
  | .ruleApp ruleName _ ruleArgs premises sideConditionCertificateNames =>
      let premiseTheorems := premises.filterMap fun
        | .theoremRef name _ _ _ => some name
        | _ => none
      { proofRule? := some ruleName
        proofRuleArgs := ruleArgs
        premiseTheorems := premiseTheorems
        sideConditionCertificateNames := sideConditionCertificateNames }

/-- Reject LF definition references that are not available at the current source point.

The flattened signature contributes all LF definition names to global head resolution, so a
separate ordered-availability check is needed while processing `lf_def`s. This catches nested
future references such as constructor arguments, not only direct `lf_def A := B` aliases. -/
partial def checkLFDefinitionReferencesAvailable (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (ownerKind : String) (ownerName : Name) (where_ : String) (locals : NameSet := {}) :
    ObjExpr → CoreM Unit
  | .ident n => do
      let n := n.eraseMacroScopes
      if !locals.contains n then
        match globalHeads.find? n with
        | some (.lfDefinition, _) =>
            if (knownTypes.find? n).isNone then
              throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' references LF \
                definition '{n}' before it is available in {where_}"
        | _ => pure ()
  | .sort | .univ _ => pure ()
  | .app f a => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals f
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals a
  | .arrow x A B | .funArrow x A B => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals B
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals body
  | .jeq lhs rhs => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals lhs
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals rhs

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
  let judgmentArities : NameMap Nat := sig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let syntaxSortArities : NameMap Nat := sig.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes s.params.size
  let mut checkedDefs := #[]
  let mut knownLFDefTypes : LFLocalTypes := {}
  let mut knownLFDefValues : LFDefinitionValueMap := {}
  for d in sig.lfObjectDefs do
    checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "type" d.typeExpr
    checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "type" d.typeExpr
    checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "type"
      (locals := {}) d.typeExpr
    checkLFSyntaxSortArgumentsInExpr sig "lf_def" d.name "type" knownLFDefTypes d.typeExpr
    checkLFInferableApplicationArguments sig "lf_def" d.name "type" knownLFDefTypes d.typeExpr
    checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "value" d.value
    checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "value" d.value
    checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "value"
      (locals := {}) d.value
    checkLFSyntaxSortArgumentsInExpr sig "lf_def" d.name "value" knownLFDefTypes d.value
    checkLFInferableApplicationArguments sig "lf_def" d.name "value" knownLFDefTypes d.value
    checkLFExprHasType sig "lf_def" d.name "value" knownLFDefTypes d.value d.typeExpr
    let checkedType ← resolveLFExpr sig globalHeads {} "lf_def" d.name "type" d.typeExpr
    let checkedValue ← resolveLFExpr sig globalHeads {} "lf_def" d.name "value" d.value
    let resultTypeExpr := lfFunctionTypeResult d.typeExpr
    let some typeHead := checkedLFHead? globalHeads {} resultTypeExpr
      | throwError "lf_def '{d.name}' in type theory '{sig.name}' has type not ending in a known \
        LF identifier: {d.typeExpr}"
    if typeHead.kind != .syntaxSort then
      throwError "lf_def '{d.name}' in type theory '{sig.name}' has result type headed by \
        {typeHead.kind.label} '{typeHead.name}', expected a syntax_sort-headed type"
    let valueHead? := checkedLFHead? globalHeads {} d.value
    if let some valueHead := valueHead? then
      if valueHead.kind == .lfDefinition then
        let valueName := valueHead.name.eraseMacroScopes
        unless knownLFDefTypes.contains valueName do
          throwError "lf_def '{d.name}' in type theory '{sig.name}' references LF definition \
            '{valueName}' before it is available"
        if let some actualType := inferKnownLFExprType? sig knownLFDefTypes d.value then
          let expectedType := eraseObjExprScopes d.typeExpr
          let normalizedActualType := normalizeLFExprForTypeComparison sig actualType
          let normalizedExpectedType := normalizeLFExprForTypeComparison sig expectedType
          if !lfExprAlphaEq normalizedActualType normalizedExpectedType then
            throwError "lf_def '{d.name}' in type theory '{sig.name}' has value LF definition \
              '{valueName}' with type '{diagnosticObjExprString normalizedActualType}', expected \
              '{diagnosticObjExprString normalizedExpectedType}'"
    checkedDefs := checkedDefs.push {
      name := d.name.eraseMacroScopes
      typeExpr := d.typeExpr
      checkedTypeExpr := checkedType
      typeHead? := some typeHead
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
      checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name where_ theoremKnownTypes
        b.typeExpr
      checkLFInferableApplicationArguments sig "judgment_theorem" t.name where_ theoremKnownTypes
        b.typeExpr
      checkLFBinderType sig globalHeads "judgment_theorem" t.name where_ theoremKnownTypes
        priorTheoremLocals true b.typeExpr
      let typeHead? := checkedLFHead? globalHeads priorTheoremLocals b.typeExpr
      match typeHead? with
      | some head =>
          if head.kind == .judgment then
            let (_, args) := splitObjApp b.typeExpr
            checkLFJudgmentArgumentsWithKnownTypes sig "judgment_theorem" t.name where_
              theoremKnownTypes head.name args
            availableLocalStatements :=
              availableLocalStatements.insert b.name.eraseMacroScopes (eraseObjExprScopes
                b.typeExpr)
          else if head.kind == .syntaxSort then
            pure ()
          else
            throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has parameter \
              '{b.name.eraseMacroScopes}' type headed by {head.kind.label} '{head.name}', \
                expected a syntax_sort or judgment"
      | none =>
          throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has parameter \
            '{b.name.eraseMacroScopes}' type not headed by a known LF identifier: {b.typeExpr}"
      theoremKnownTypes :=
        theoremKnownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
      priorTheoremLocals := priorTheoremLocals.insert b.name.eraseMacroScopes
    checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
      "statement" t.judgmentExpr
    checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
    checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name "statement" theoremKnownTypes
      t.judgmentExpr
    checkLFInferableApplicationArguments sig "judgment_theorem" t.name "statement"
      theoremKnownTypes t.judgmentExpr
    checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
      "proof" t.proof
    checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "proof" t.proof
    checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name "proof" theoremKnownTypes t.proof
    checkLFInferableApplicationArguments sig "judgment_theorem" t.name "proof" theoremKnownTypes
      t.proof
    let judgmentHead ← checkRuleJudgmentHead sig judgmentArities t.name "statement" t.judgmentExpr
    let (_, judgmentArgs) := splitObjApp t.judgmentExpr
    checkLFJudgmentArgumentsWithKnownTypes sig "judgment_theorem" t.name "statement"
      theoremKnownTypes judgmentHead.name judgmentArgs
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
    let kernelDerivation ←
      lowerLFDerivationToKernel sig rules globalHeads theoremKnownTypes knownLFDefValues
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
      kernelDerivation? := some kernelDerivation }
    let stmt := match derivation with
      | .localAssumption _ stmt => stmt
      | .theoremRef _ stmt _ _ => stmt
      | .ruleApp _ stmt _ _ _ => stmt
    if t.binders.isEmpty then
      availableLFTheoremStatements :=
        availableLFTheoremStatements.insert t.name.eraseMacroScopes stmt
    availableLFTheoremNames := availableLFTheoremNames.insert t.name.eraseMacroScopes
  pure (checkedDefs, checkedTheorems)

/-- Previously checked LF definition result types. -/
def checkedLFDefinitionTypeMapFromDefs (defs : Array CheckedLFObjectDef) : LFLocalTypes :=
  defs.foldl (init := {}) fun m d =>
    m.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)

/-- Previously checked LF definition values. -/
def lfDefinitionValueMapFromCheckedDefs (defs : Array CheckedLFObjectDef) : LFDefinitionValueMap :=
  defs.foldl (init := {}) fun m d =>
    m.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)

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
  let syntaxSortArities : NameMap Nat := flatSig.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes s.params.size
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
    checkedRules := checkedBase.lfRules ++ newRules
    checkedRuleSchemas := checkedBase.lfRuleSchemas ++ newRuleSchemas
    checkedSideConditionCertificates :=
      checkedBase.lfSideConditionCertificates ++ newCertificates
    knownLFDefTypes := checkedLFDefinitionTypeMapFromDefs checkedBase.lfObjectDefs
    knownLFDefValues := lfDefinitionValueMapFromCheckedDefs checkedBase.lfObjectDefs
    availableLFTheoremStatements :=
      availableLFTheoremStatementsFromChecked checkedBase.lfJudgmentTheorems
    availableLFTheoremNames :=
      availableLFTheoremNamesFromChecked checkedBase.lfJudgmentTheorems }

/-- Check one LF object definition, updating the intra-block availability context. -/
def checkLFObjectDefInContext (ctx : IntraBlockLFCheckContext) (d : LFObjectDefDecl) :
    CoreM (CheckedLFObjectDef × IntraBlockLFCheckContext) := do
  let sig := ctx.flatSig
  let lfGlobals := ctx.lfGlobals
  let opaqueArities := ctx.opaqueArities
  let globalHeads := ctx.globalHeads
  let knownLFDefTypes := ctx.knownLFDefTypes
  checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "type" d.typeExpr
  checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "type" d.typeExpr
  checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "type"
    (locals := {}) d.typeExpr
  checkLFSyntaxSortArgumentsInExpr sig "lf_def" d.name "type" knownLFDefTypes d.typeExpr
  checkLFInferableApplicationArguments sig "lf_def" d.name "type" knownLFDefTypes d.typeExpr
  checkKnownNamesInLFExpr sig lfGlobals {} opaqueArities "lf_def" d.name "value" d.value
  checkNoCaptureUnsafeBetaInLFExpr sig "lf_def" d.name "value" d.value
  checkLFDefinitionReferencesAvailable sig globalHeads knownLFDefTypes "lf_def" d.name "value"
    (locals := {}) d.value
  checkLFSyntaxSortArgumentsInExpr sig "lf_def" d.name "value" knownLFDefTypes d.value
  checkLFInferableApplicationArguments sig "lf_def" d.name "value" knownLFDefTypes d.value
  checkLFExprHasType sig "lf_def" d.name "value" knownLFDefTypes d.value d.typeExpr
  let checkedType ← resolveLFExpr sig globalHeads {} "lf_def" d.name "type" d.typeExpr
  let checkedValue ← resolveLFExpr sig globalHeads {} "lf_def" d.name "value" d.value
  let resultTypeExpr := lfFunctionTypeResult d.typeExpr
  let some typeHead := checkedLFHead? globalHeads {} resultTypeExpr
    | throwError "lf_def '{d.name}' in type theory '{sig.name}' has type not ending in a known \
      LF identifier: {d.typeExpr}"
  if typeHead.kind != .syntaxSort then
    throwError "lf_def '{d.name}' in type theory '{sig.name}' has result type headed by \
      {typeHead.kind.label} '{typeHead.name}', expected a syntax_sort-headed type"
  let valueHead? := checkedLFHead? globalHeads {} d.value
  if let some valueHead := valueHead? then
    if valueHead.kind == .lfDefinition then
      let valueName := valueHead.name.eraseMacroScopes
      unless knownLFDefTypes.contains valueName do
        throwError "lf_def '{d.name}' in type theory '{sig.name}' references LF definition \
          '{valueName}' before it is available"
      if let some actualType := inferKnownLFExprType? sig knownLFDefTypes d.value then
        let expectedType := eraseObjExprScopes d.typeExpr
        let normalizedActualType := normalizeLFExprForTypeComparison sig actualType
        let normalizedExpectedType := normalizeLFExprForTypeComparison sig expectedType
        if !lfExprAlphaEq normalizedActualType normalizedExpectedType then
          throwError "lf_def '{d.name}' in type theory '{sig.name}' has value LF definition \
            '{valueName}' with type '{diagnosticObjExprString normalizedActualType}', expected \
            '{diagnosticObjExprString normalizedExpectedType}'"
  let checkedDef : CheckedLFObjectDef := {
    name := d.name.eraseMacroScopes
    typeExpr := d.typeExpr
    checkedTypeExpr := checkedType
    typeHead? := some typeHead
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
    checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name where_ theoremKnownTypes
      b.typeExpr
    checkLFInferableApplicationArguments sig "judgment_theorem" t.name where_ theoremKnownTypes
      b.typeExpr
    checkLFBinderType sig globalHeads "judgment_theorem" t.name where_ theoremKnownTypes
      priorTheoremLocals true b.typeExpr
    let typeHead? := checkedLFHead? globalHeads priorTheoremLocals b.typeExpr
    match typeHead? with
    | some head =>
        if head.kind == .judgment then
          let (_, args) := splitObjApp b.typeExpr
          checkLFJudgmentArgumentsWithKnownTypes sig "judgment_theorem" t.name where_
            theoremKnownTypes head.name args
          availableLocalStatements :=
            availableLocalStatements.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
        else if head.kind == .syntaxSort then
          pure ()
        else
          throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has parameter \
            '{b.name.eraseMacroScopes}' type headed by {head.kind.label} '{head.name}', \
              expected a syntax_sort or judgment"
    | none =>
        throwError "judgment_theorem '{t.name}' in type theory '{sig.name}' has parameter \
          '{b.name.eraseMacroScopes}' type not headed by a known LF identifier: {b.typeExpr}"
    theoremKnownTypes :=
      theoremKnownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    priorTheoremLocals := priorTheoremLocals.insert b.name.eraseMacroScopes
  checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
    "statement" t.judgmentExpr
  checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
  checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name "statement" theoremKnownTypes
    t.judgmentExpr
  checkLFInferableApplicationArguments sig "judgment_theorem" t.name "statement" theoremKnownTypes
    t.judgmentExpr
  checkKnownNamesInLFExpr sig lfGlobals theoremLocals opaqueArities "judgment_theorem" t.name
    "proof" t.proof
  checkNoCaptureUnsafeBetaInLFExpr sig "judgment_theorem" t.name "proof" t.proof
  checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" t.name "proof" theoremKnownTypes t.proof
  checkLFInferableApplicationArguments sig "judgment_theorem" t.name "proof" theoremKnownTypes
    t.proof
  let judgmentHead ← checkRuleJudgmentHead sig judgmentArities t.name "statement" t.judgmentExpr
  let (_, judgmentArgs) := splitObjApp t.judgmentExpr
  checkLFJudgmentArgumentsWithKnownTypes sig "judgment_theorem" t.name "statement"
    theoremKnownTypes judgmentHead.name judgmentArgs
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
  let kernelDerivation ←
    lowerLFDerivationToKernel sig rules globalHeads theoremKnownTypes knownLFDefValues theoremLocals
      t.name derivation
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
    kernelDerivation? := some kernelDerivation }
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

/-- Stream-check all LF object definitions and theorem artifacts in a flat signature. -/
def checkLFObjectArtifactsInSignatureStreaming (sig : HLSignature)
    (rules : Array CheckedLFRule) :
    CoreM (Array CheckedLFObjectDef × Array CheckedLFJudgmentTheorem) := do
  let checkedBase : CheckedSignature := { name := sig.name }
  let mut ctx := mkIntraBlockLFCheckContext sig checkedBase rules
  for d in sig.lfObjectDefs do
    let (_, ctx') ← checkLFObjectDefInContext ctx d
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
  | .arrow x A B | .funArrow x A B =>
      lfExprContainsIdent needle A ||
        if x.map Name.eraseMacroScopes == some needle.eraseMacroScopes then false else
          lfExprContainsIdent needle B
  | .lam xs body =>
      if xs.map Name.eraseMacroScopes |>.contains needle.eraseMacroScopes then false else
        lfExprContainsIdent needle body
  | .jeq lhs rhs => lfExprContainsIdent needle lhs || lfExprContainsIdent needle rhs

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
  let some head := checkedLFHead? globalHeads abbrLocals abbr.value
    | throwError "syntax_abbrev '{abbr.name}' in type theory '{sig.name}' has value not headed \
      by a known LF identifier: {abbr.value}"
  if head.kind != .syntaxSort && head.kind != .local then
    throwError "syntax_abbrev '{abbr.name}' in type theory '{sig.name}' has value headed by \
      {head.kind.label} '{head.name}', expected a syntax_sort- or local-family-headed type"

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
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (opaqueDecl : LFOpaqueConstDecl) :
    CoreM Unit := do
  if opaqueDecl.typeExpr?.isSome then
    checkNoDuplicateMetadataBinders sig "lf_opaque" opaqueDecl.name opaqueDecl.params
    let opaqueLocals ←
      checkKnownNamesInMetadataBindings sig lfGlobals opaqueArities "lf_opaque" opaqueDecl.name
        opaqueDecl.params
    checkSyntaxSortApplicationsInBindings sig syntaxSortArities "lf_opaque" opaqueDecl.name
      opaqueDecl.params
    checkLFSyntaxSortArgumentsInBindings sig "lf_opaque" opaqueDecl.name opaqueDecl.params
    checkLFBinderTypesInBindings sig globalHeads "lf_opaque" opaqueDecl.name opaqueDecl.params
    let opaqueLocalTypes := lfLocalTypesOfBindings opaqueDecl.params
    if let some typeExpr := opaqueDecl.typeExpr? then
      checkKnownNamesInLFExpr sig lfGlobals opaqueLocals opaqueArities "lf_opaque"
        opaqueDecl.name "result type" typeExpr
      checkSyntaxSortApplicationsInExpr sig syntaxSortArities "lf_opaque" opaqueDecl.name
        "result type" typeExpr
      checkLFSyntaxSortArgumentsInExpr sig "lf_opaque" opaqueDecl.name "result type"
        opaqueLocalTypes typeExpr
      checkLFInferableApplicationArguments sig "lf_opaque" opaqueDecl.name "result type"
        opaqueLocalTypes typeExpr
      checkLFBinderType sig globalHeads "lf_opaque" opaqueDecl.name "result type"
        opaqueLocalTypes opaqueLocals false typeExpr
      let some typeHead := checkedLFHead? globalHeads opaqueLocals typeExpr
        | throwError "lf_opaque '{opaqueDecl.name}' in type theory '{sig.name}' has result type \
          not headed by a known LF identifier: {typeExpr}"
      if typeHead.kind != .syntaxSort && typeHead.kind != .local then
        throwError "lf_opaque '{opaqueDecl.name}' in type theory '{sig.name}' has result type \
          headed by {typeHead.kind.label} '{typeHead.name}', expected a syntax_sort- or \
            local-family-headed type"

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
    let head ←
      checkRuleJudgmentHead sig judgmentArities r.name s!"premise '{p.name}'" p.judgmentExpr
    let (_, premiseArgs) := splitObjApp p.judgmentExpr
    checkLFJudgmentArguments sig r.name s!"premise '{p.name}'" ruleLocalTypes head.name
      premiseArgs
    let checkedJudgmentExpr ←
      resolveLFExpr sig globalHeads ruleParamLocals "rule" r.name s!"premise '{p.name}'"
        p.judgmentExpr
    checkedPremises := checkedPremises.push {
      name := premiseName
      judgmentExpr := p.judgmentExpr
      checkedJudgmentExpr := checkedJudgmentExpr
      head := head
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
  let syntaxSortNames : NameSet := sig.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes
  let syntaxSortArities : NameMap Nat := sig.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes s.params.size
  for sort in sig.syntaxSorts do
    checkOneSyntaxSortMetadataInSignature sig lfGlobals opaqueArities globalHeads
      syntaxSortArities sort
  for abbr in sig.syntaxAbbrevs do
    checkOneSyntaxAbbrevMetadataInSignature sig lfGlobals opaqueArities syntaxSortArities
      globalHeads abbr
  let mut seenSortRoles : NameMap NameSet := {}
  for role in sig.syntaxSortRoles do
    if !syntaxSortNames.contains role.sortName then
      throwError "syntax_sort_role for unknown syntax sort '{role.sortName}' in type theory \
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
  for opaqueDecl in sig.lfOpaqueConsts do
    checkOneLFOpaqueConstMetadataInSignature sig lfGlobals opaqueArities syntaxSortArities
      globalHeads opaqueDecl
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

/-- Find the unique checked context zone whose entry sort matches `sortName`, if any. -/
def uniqueZoneForSort? (zones : Array CheckedLFContextZone) (sortName : Name) : Option Name :=
  let candidates := zones.filter (fun z => z.sortName == sortName.eraseMacroScopes)
  if candidates.size == 1 then candidates[0]!.name else none

/-- Find the unique binder class for a sort/zone pair, if any. -/
def uniqueBinderClassFor? (classes : Array CheckedLFBinderClass) (sortName zoneName : Name) :
  Option Name :=
  let sortName := sortName.eraseMacroScopes
  let zoneName := zoneName.eraseMacroScopes
  let candidates := classes.filter (fun b => b.boundSortName == sortName && b.zoneName == zoneName)
  if candidates.size == 1 then candidates[0]!.name else none

/-- Extract a typed LF local schema from a checked metadata binder. -/
def checkedLFTypedLocalOfBinding (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (evidence? : Option CheckedLFRuleParamEvidence) (b : CheckedLFBinding) : CheckedLFTypedLocal :=
  let sortHead? := b.head?.filter (fun h => h.kind == .syntaxSort)
  let zoneName? := sortHead?.bind (fun h => uniqueZoneForSort? zones h.name)
  let binderClass? := match sortHead?, zoneName? with
    | some h, some z => uniqueBinderClassFor? classes h.name z
    | _, _ => none
  { name := b.name
    typeExpr := b.typeExpr
    checkedTypeExpr := b.checkedTypeExpr
    sortHead? := sortHead?
    zoneName? := zoneName?
    binderClass? := binderClass?
    evidence? := evidence? }

/-- Extract multi-zone locals from a rule metavariable telescope. -/
def checkedLFMultiContextOfLocals (locals : Array CheckedLFTypedLocal) : CheckedLFMultiContext :=
  { locals := locals.filterMap fun v =>
      match v.zoneName? with
      | some zoneName => some {
          name := v.name
          zoneName := zoneName
          binderClass? := v.binderClass?
          typeExpr := v.typeExpr
          checkedTypeExpr := v.checkedTypeExpr }
      | none => none }

/-- Run the current built-in executable side-condition hooks for one checked side condition.

The Phase-3 hook API is deliberately tiny: the built-in trivial hook accepts any side
condition that already passed LF metadata validation and records a provenance certificate.
Opaque solver names return no certificate. -/
def checkLFSideCondition? (ruleName : Name) (sc : CheckedLFRuleSideCondition) :
    Option CheckedLFSideConditionCertificate :=
  match classifySideConditionHook sc.solver with
  | .opaque => none
  | .builtinTrivial =>
      some {
        name := sc.name
        solver := sc.solver.eraseMacroScopes
        input := sc.input
        checkedInput := sc.checkedInput
        inputHead? := sc.head?
        kind := .builtinTrivial
        certificateName := .str (.str ruleName.eraseMacroScopes "side_condition") (
          toString sc.name.eraseMacroScopes)
        diagnostic := "accepted unconditionally by built-in trivial side-condition hook" }

/-- Derive a Phase-2/3/4 LF rule schema from a checked LF rule artifact. -/
def checkedLFRuleSchemaOfRule (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (r : CheckedLFRule) : CheckedLFRuleSchema :=
  let evidenceFor (paramName : Name) : Option CheckedLFRuleParamEvidence :=
    r.paramEvidences.find? (fun ev => ev.paramName == paramName.eraseMacroScopes)
  let metavariables := r.params.map (fun p =>
    checkedLFTypedLocalOfBinding zones classes (evidenceFor p.name) p)
  { name := r.name
    metavariables := metavariables
    multiContext := checkedLFMultiContextOfLocals metavariables
    premises := r.premises.map fun p =>
      { name := p.name
        judgmentHead := p.head
        checkedJudgmentExpr := p.checkedJudgmentExpr }
    sideConditionSlots := r.sideConditions.map fun sc =>
      let cert? := checkLFSideCondition? r.name sc
      { name := sc.name
        solver := sc.solver
        checkedInput := sc.checkedInput
        inputHead? := sc.head?
        certificate? := cert? }
    checkedConclusionExpr := r.checkedConclusionExpr
    conclusionHead := r.conclusionHead }

/-- Derive all Phase-2/3/4 LF rule schemas from checked LF rule metadata. -/
def checkedLFRuleSchemasOfRules (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (rules : Array CheckedLFRule) : Array CheckedLFRuleSchema :=
  rules.map (checkedLFRuleSchemaOfRule zones classes)

/-- Collect checked side-condition certificates from derived rule schemas. -/
def checkedLFSideConditionCertificatesOfSchemas (rules : Array CheckedLFRuleSchema) :
    Array CheckedLFSideConditionCertificate := Id.run do
  let mut out := #[]
  for r in rules do
    for sc in r.sideConditionSlots do
      if let some cert := sc.certificate? then
        out := out.push cert
  return out

/-- Convert a checked LF side-condition certificate to the low-level kernel form. -/
def checkedLFSideConditionCertificateToKernel (cert : CheckedLFSideConditionCertificate) :
    SideConditionCertificate :=
  { name := cert.certificateName
    condition := { name := cert.solver, args := [checkedLFExprToRaw cert.checkedInput] }
    kind := .builtinTrivial
    payload := cert.diagnostic }

/-- Convert a checked LF binder to a low-level raw metavariable declaration. -/
def checkedLFBindingToKernelMetaVar (v : CheckedLFBinding) : RuleMetaVar :=
  { name := v.name
    sort := match v.head? with | some h => .custom h.name | none => .arg
    type? := some (checkedLFExprToRaw v.checkedTypeExpr) }

/-- Convert a checked context zone to a low-level kernel replay zone schema. -/
def checkedLFContextZoneToKernel (z : CheckedLFContextZone) : ContextZoneSchema :=
  { name := z.name
    sort := .custom z.sortName
    dependsOn := z.dependsOn.toList }

/-- Convert a checked binder class to a low-level kernel replay binder-class schema. -/
def checkedLFBinderClassToKernel (b : CheckedLFBinderClass) : BinderClassSchema :=
  { name := b.name
    zone := b.zoneName
    boundSort := .custom b.boundSortName
    dependsOn := b.dependsOn.toList }

/-- Convert a typed LF opaque placeholder to a typed kernel replay constant, when possible. -/
def checkedLFOpaqueConstToKernelConstant? (defValues : CheckedLFDefinitionValueMap)
    (c : CheckedLFOpaqueConst) : Option LFConstantSchema := do
  let result ← c.checkedTypeExpr?
  let locals := c.params.foldl (init := {}) fun locals p => locals.insert p.name.eraseMacroScopes
  let result := unfoldLFDefinitionsInCheckedExpr defValues locals result
  return LFConstantSchema.mk c.name (c.params.toList.map checkedLFBindingToKernelMetaVar)
    (checkedLFExprToRaw result)

/-- Split a checked LF function type into a low-level constant telescope and result type.

The kernel-facing replay checker only needs a finite first-order telescope for typed LF
constant applications.  Function-valued `lf_def`s therefore expose their leading structural
arrows as generated constant parameters; named dependent arrows keep their source name, while
nondependent arrows receive deterministic `_argN` names. -/
partial def checkedLFTypeToKernelConstantTelescope (e : CheckedLFExpr) (i : Nat := 1) :
  List RuleMetaVar × Raw :=
  match e with
  | .arrow binder? A B =>
      let name := (binder?.getD (Name.mkSimple s!"_arg{i}")).eraseMacroScopes
      let param : RuleMetaVar := {
        name := name
        sort := .arg
        type? := some (checkedLFExprToRaw A)
      }
      let (params, result) := checkedLFTypeToKernelConstantTelescope B (i + 1)
      (param :: params, result)
  | e => ([], checkedLFExprToRaw e)

/-- Convert a checked LF definition to a typed kernel replay constant. -/
def checkedLFObjectDefToKernelConstant (defValues : CheckedLFDefinitionValueMap)
    (d : CheckedLFObjectDef) : LFConstantSchema :=
  let typeExpr := unfoldLFDefinitionsInCheckedExpr defValues {} d.checkedTypeExpr
  let (params, result) := checkedLFTypeToKernelConstantTelescope typeExpr
  LFConstantSchema.mk d.name params result

/-- Convert checked LF constants/definitions to typed kernel replay constants. -/
def checkedLFConstantsToKernel (defValues : CheckedLFDefinitionValueMap)
    (opaqueConsts : Array CheckedLFOpaqueConst) (objectDefs : Array CheckedLFObjectDef) :
    Array LFConstantSchema :=
  (opaqueConsts.filterMap (checkedLFOpaqueConstToKernelConstant? defValues)) ++
    (objectDefs.map (checkedLFObjectDefToKernelConstant defValues))

/-- Convert a checked conversion-plugin handle to the low-level kernel replay schema. -/
def checkedLFConversionPluginToKernel (p : CheckedLFConversionPlugin) : ConversionPluginSchema :=
  { name := p.name
    trust := p.trust
    supportedSteps := p.supportedSteps.toList }

/-- Checked LF-definition values keyed by definition name. -/
def checkedLFDefinitionValues (defs : Array CheckedLFObjectDef) : CheckedLFDefinitionValueMap :=
  defs.foldl (init := {}) fun values d => values.insert d.name.eraseMacroScopes d.checkedValue

/-- Convert a Phase-2/3 LF rule schema to the low-level kernel `RuleSchema` shape. -/
def checkedLFRuleSchemaToKernel (defValues : CheckedLFDefinitionValueMap)
    (r : CheckedLFRuleSchema) : RuleSchema :=
  let locals := r.metavariables.foldl (init := {}) fun locals v =>
    locals.insert v.name.eraseMacroScopes
  let norm := unfoldLFDefinitionsInCheckedExpr defValues locals
  let sideConditions := r.sideConditionSlots.toList.map fun sc =>
    ({ name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] } : SideCondition)
  let certificateSlots := r.sideConditionSlots.toList.map fun sc =>
    let condition : SideCondition :=
      { name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] }
    ({ name := sc.name, condition := condition } : SideConditionCertificateSlot)
  let checkedCertificates := r.sideConditionSlots.toList.filterMap fun sc =>
    sc.certificate?.map checkedLFSideConditionCertificateToKernel
  RuleSchema.mk r.name
    (r.metavariables.toList.map (fun v =>
      { name := v.name
        sort := match v.sortHead? with | some h => .custom h.name | none => .arg
        zone? := v.zoneName?
        type? := some (checkedLFExprToRaw v.checkedTypeExpr)
        evidence? := v.evidence?.map (fun ev =>
          checkedLFJudgmentExprToKernel ev.checkedJudgmentExpr ev.head) }))
    (r.premises.toList.map (fun p =>
      checkedLFJudgmentExprToKernel (norm p.checkedJudgmentExpr) p.judgmentHead))
    sideConditions
    certificateSlots
    checkedCertificates
    (checkedLFJudgmentExprToKernel (norm r.checkedConclusionExpr) r.conclusionHead)

/-- Convert all Phase-2 LF rule schemas to kernel `RuleSchema` staging artifacts. -/
def checkedLFRuleSchemasToKernel (defValues : CheckedLFDefinitionValueMap)
    (rules : Array CheckedLFRuleSchema) : Array RuleSchema :=
  rules.map (checkedLFRuleSchemaToKernel defValues)

/-- Extract checked local theorem-assumption entries from a locally quantified LF theorem. -/
def kernelLFLocalAssumptionEntriesOfTheorem (t : CheckedLFJudgmentTheorem) :
    List KernelLFTheoremEntry :=
  t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          some { name := b.name, statement := checkedLFJudgmentExprToKernel b.checkedTypeExpr head }
        else
          none
    | none => none

/-- Extract checked local theorem assumptions after LF-definition normalization. -/
def kernelLFLocalAssumptionEntriesOfTheoremNormalized (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (defValues : LFDefinitionValueMap)
    (t : CheckedLFJudgmentTheorem) : CoreM (List KernelLFTheoremEntry) := do
  let theoremLocals := t.binders.foldl (init := {}) fun locals b =>
    locals.insert b.name.eraseMacroScopes
  let mut out := []
  for b in t.binders do
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          let expr := unfoldLFDefinitionsInExprWithLocals defValues theoremLocals b.typeExpr
          let statement ← lfJudgmentObjExprToKernel sig globalHeads "local theorem assumption"
            t.name expr theoremLocals
          out := out ++ [{ name := b.name, statement := statement }]
    | none => pure ()
  pure out

/-- Kernel rule schema used when a checked LF theorem with local binders is referenced as a premise.
-/
def kernelLFRuleSchemaOfTheorem (defValues : CheckedLFDefinitionValueMap)
    (t : CheckedLFJudgmentTheorem) : RuleSchema :=
  let locals := t.binders.foldl (init := {}) fun locals b => locals.insert b.name.eraseMacroScopes
  let norm := unfoldLFDefinitionsInCheckedExpr defValues locals
  let metavariables := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then none
        else
          some ({ name := b.name
                  sort := if head.kind == .syntaxSort then .custom head.name else .arg
                  type? := some (checkedLFExprToRaw (norm b.checkedTypeExpr)) } : RuleMetaVar)
    | none => none
  let premises := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          some (checkedLFJudgmentExprToKernel (norm b.checkedTypeExpr) head)
        else none
    | none => none
  RuleSchema.mk (lfJudgmentTheoremKernelRuleName t.name) metavariables premises [] [] []
    (checkedLFJudgmentExprToKernel (norm t.checkedJudgmentExpr) t.judgmentHead)

/-- Kernel rule schemas for checked LF theorems, used by instantiated theorem references. -/
def kernelLFRuleSchemasOfTheorems (defValues : CheckedLFDefinitionValueMap)
    (theorems : Array CheckedLFJudgmentTheorem) : Array RuleSchema :=
  theorems.map (kernelLFRuleSchemaOfTheorem defValues)

/-- Extract checked external-certificate entries exposed by theorem-like bridge artifacts. -/
def kernelLFCertificateEntriesOfTheorems (theorems : Array CheckedLFJudgmentTheorem) :
    List KernelLFCertificateEntry :=
  theorems.toList.filterMap fun t =>
    match t.kernelDerivation? with
    | some (.certificate name stmt certificateName) =>
        some { name := name, statement := stmt, certificateName := certificateName }
    | _ => none

/-- Add checked kernel replay validation to one incrementally checked LF theorem. -/
def validateIncrementalLFTheoremKernelReplay (sig : HLSignature) (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let some kernelDeriv := t.kernelDerivation?
    | pure t
  let lfCheckedDefValues := checkedLFDefinitionValues checked.lfObjectDefs
  let kernelSig : Signature := {
    name := sig.name.eraseMacroScopes
    constants := (checkedLFConstantsToKernel lfCheckedDefValues checked.lfOpaqueConsts
      checked.lfObjectDefs).toList
    contextZones := checked.lfContextZones.toList.map checkedLFContextZoneToKernel
    binderClasses := checked.lfBinderClasses.toList.map checkedLFBinderClassToKernel
    conversionPlugins := checked.lfConversionPlugins.toList.map checkedLFConversionPluginToKernel
    rules := (checkedLFRuleSchemasToKernel lfCheckedDefValues checked.lfRuleSchemas ++
      kernelLFRuleSchemasOfTheorems lfCheckedDefValues checked.lfJudgmentTheorems).toList }
  let mut replayCtx : KernelLFCheckContext := {
    certificates := kernelLFCertificateEntriesOfTheorems checked.lfJudgmentTheorems }
  for prior in checked.lfJudgmentTheorems do
    if prior.binders.isEmpty then
      if let some priorKernel := prior.kernelDerivation? then
        replayCtx := replayCtx.addTheorem prior.name (KernelLFDerivation.statement priorKernel)
  let lfKernelGlobalHeads := lfGlobalHeadInfo sig
  let lfKernelDefValues := lfDefinitionValueMapFromCheckedDefs checked.lfObjectDefs
  let assumptions ← kernelLFLocalAssumptionEntriesOfTheoremNormalized sig lfKernelGlobalHeads
    lfKernelDefValues t
  let localReplayCtx := { replayCtx with
    localParameters := t.binders.toList.map (fun b => b.name)
    assumptions := assumptions }
  match CheckedKernelLFDerivation.ofReplay kernelSig localReplayCtx
      (KernelLFDerivation.statement kernelDeriv) kernelDeriv with
  | .ok checkedReplay => pure { t with checkedKernelDerivation? := some checkedReplay }
  | .error err =>
      throwError "kernel-facing replay check failed for judgment_theorem '{t.name}' in type theory \
        '{sig.name}': {err}"


/-- Convert a checked LF binding back to the high-level declaration shape used for checking
new extension deltas against an already checked baseline. -/
def checkedLFBindingToHLBinding (b : CheckedLFBinding) : HLBinding :=
  { name := b.name, typeExpr := b.typeExpr, visibility := b.visibility }

/-- Convert a checked syntax-sort artifact to a high-level declaration. -/
def checkedLFSyntaxSortToHLDecl (s : CheckedLFSyntaxSort) : SyntaxSortDecl :=
  { name := s.name, params := s.params.map checkedLFBindingToHLBinding }

/-- Convert a checked syntax-abbreviation artifact to a high-level declaration. -/
def checkedLFSyntaxAbbrevToHLDecl (a : CheckedLFSyntaxAbbrev) : SyntaxAbbrevDecl :=
  { name := a.name, params := a.params.map checkedLFBindingToHLBinding, value := a.value }

/-- Convert a checked context-zone artifact to a high-level declaration. -/
def checkedLFContextZoneToHLDecl (z : CheckedLFContextZone) : ContextZoneDecl :=
  { name := z.name, sortName := z.sortName, dependsOn := z.dependsOn }

/-- Convert a checked binder-class artifact to a high-level declaration. -/
def checkedLFBinderClassToHLDecl (b : CheckedLFBinderClass) : BinderClassDecl :=
  { name := b.name
    boundSortName := b.boundSortName
    zoneName := b.zoneName
    dependsOn := b.dependsOn }

/-- Convert a checked judgment artifact to a high-level declaration. -/
def checkedLFJudgmentToHLDecl (j : CheckedLFJudgment) : JudgmentDecl :=
  { name := j.name, params := j.params.map checkedLFBindingToHLBinding }

/-- Convert a checked LF opaque artifact to a high-level declaration. -/
def checkedLFOpaqueConstToHLDecl (o : CheckedLFOpaqueConst) : LFOpaqueConstDecl :=
  { name := o.name
    arity? := o.arity?
    params := o.params.map checkedLFBindingToHLBinding
    typeExpr? := o.typeExpr? }

/-- Convert a checked side-condition solver artifact to a high-level declaration. -/
def checkedLFSideConditionSolverToHLDecl (s : CheckedLFSideConditionSolver) :
    SideConditionSolverDecl :=
  { name := s.name }

/-- Convert a checked conversion-plugin artifact to a high-level declaration. -/
def checkedLFConversionPluginToHLDecl (p : CheckedLFConversionPlugin) : ConversionPluginDecl :=
  { name := p.name, trust := p.trust, supportedSteps := p.supportedSteps }

/-- Convert a checked LF rule artifact to a high-level declaration. -/
def checkedLFRuleToHLDecl (r : CheckedLFRule) : RuleDecl :=
  { name := r.name
    params := r.params.map checkedLFBindingToHLBinding
    premises := r.premises.map fun p =>
      ({ name := p.name, judgmentExpr := p.judgmentExpr } : RulePremiseDecl)
    sideConditions := r.sideConditions.map fun sc =>
      ({ name := sc.name, solver := sc.solver, input := sc.input } : RuleSideConditionDecl)
    paramEvidences := r.paramEvidences.map fun ev =>
      ({ name := ev.name, paramName := ev.paramName, judgmentExpr := ev.judgmentExpr } :
        RuleParamEvidenceDecl)
    conclusionExpr := r.conclusionExpr }

/-- Convert a checked LF object definition to a high-level declaration. -/
def checkedLFObjectDefToHLDecl (d : CheckedLFObjectDef) : LFObjectDefDecl :=
  { name := d.name, typeExpr := d.typeExpr, value := d.value }

/-- Convert a checked LF judgment theorem to a high-level declaration. -/
def checkedLFJudgmentTheoremToHLDecl (t : CheckedLFJudgmentTheorem) :
    LFJudgmentTheoremDecl :=
  { name := t.name
    binders := t.binders.map checkedLFBindingToHLBinding
    judgmentExpr := t.judgmentExpr
    proof := t.proof }

/-- Reconstruct a flat high-level signature from checked artifacts for incremental checking.
The source baseline contributes non-checking metadata such as object macros. -/
def checkedSignatureToHLSignature (sourceBase : HLSignature) (checked : CheckedSignature) :
    HLSignature :=
  { name := checked.name
    parents := #[]
    levelParams := checked.levelParams
    syntaxSorts := checked.lfSyntaxSorts.map checkedLFSyntaxSortToHLDecl
    syntaxAbbrevs := checked.lfSyntaxAbbrevs.map checkedLFSyntaxAbbrevToHLDecl
    syntaxSortRoles := checked.lfSyntaxSortRoles
    contextZones := checked.lfContextZones.map checkedLFContextZoneToHLDecl
    binderClasses := checked.lfBinderClasses.map checkedLFBinderClassToHLDecl
    judgments := checked.lfJudgments.map checkedLFJudgmentToHLDecl
    judgmentRoles := checked.lfJudgmentRoles
    rules := checked.lfRules.map checkedLFRuleToHLDecl
    ruleRoles := checked.lfRuleRoles
    rewriteRelations := checked.lfRewriteRelations
    rewriteSymmetries := checked.lfRewriteSymmetries
    rewriteCongruences := checked.lfRewriteCongruences
    transportRules := checked.lfTransportRules
    transportPositions := checked.lfTransportPositions
    sideConditionSolvers :=
      checked.lfSideConditionSolvers.map checkedLFSideConditionSolverToHLDecl
    conversionPlugins := checked.lfConversionPlugins.map checkedLFConversionPluginToHLDecl
    lfOpaqueConsts := checked.lfOpaqueConsts.map checkedLFOpaqueConstToHLDecl
    modelVisibilities := checked.modelVisibilities
    modelSections := checked.modelSections
    modelSectionMemberships := checked.modelSectionMemberships
    lfObjectDefs := checked.lfObjectDefs.map checkedLFObjectDefToHLDecl
    lfJudgmentTheorems := checked.lfJudgmentTheorems.map checkedLFJudgmentTheoremToHLDecl
    macros := sourceBase.macros
    roles := sourceBase.roles }

/-- Return a fallback reason when a block still needs the full checker. -/
def unsupportedIncrementalTheoryBlockReason? (block : HLTheoryBlock) : Option String :=
  if !block.rewriteRelations.isEmpty then
    some "unsupported incremental declaration kind: rewrite_relation"
  else if !block.rewriteSymmetries.isEmpty then
    some "unsupported incremental declaration kind: rewrite_symmetry"
  else if !block.rewriteCongruences.isEmpty then
    some "unsupported incremental declaration kind: rewrite_congruence"
  else if !block.transportRules.isEmpty then
    some "unsupported incremental declaration kind: transport_rule"
  else if !block.transportPositions.isEmpty then
    some "unsupported incremental declaration kind: transport_position"
  else
    none

/-- Count declarations/metadata entries handled by the incremental extension checker. -/
def theoryBlockIncrementalDeclCount (block : HLTheoryBlock) : Nat :=
  block.syntaxSorts.size + block.syntaxAbbrevs.size + block.syntaxSortRoles.size +
    block.contextZones.size + block.binderClasses.size + block.judgments.size +
    block.judgmentRoles.size + block.rules.size + block.ruleRoles.size +
    block.sideConditionSolvers.size + block.conversionPlugins.size + block.lfOpaqueConsts.size +
    block.modelVisibilities.size + block.modelSections.size + block.lfObjectDefs.size +
    block.lfJudgmentTheorems.size

/-- Check that new declaration names do not collide with the already flattened baseline. -/
def checkNoExtensionNameCollisions (flatBase : HLSignature) (block : HLTheoryBlock) :
    CoreM Unit := do
  let existing := flatBase.nameSet
  let checkName (seen : NameSet) (kind : String) (rawName : Name) : CoreM NameSet := do
    let n := rawName.eraseMacroScopes
    if seen.contains n then
      throwError "duplicate {kind} declaration '{rawName}' in type-theory block"
    if existing.contains n then
      throwError "declaration '{rawName}' already exists in type theory '{flatBase.name}' or one \
        of its parents"
    pure (seen.insert n)
  let mut seen : NameSet := {}
  for d in block.syntaxSorts do
    seen ← checkName seen "syntax-sort" d.name
  for d in block.syntaxAbbrevs do
    seen ← checkName seen "syntax abbreviation" d.name
  for d in block.contextZones do
    seen ← checkName seen "context zone" d.name
  for d in block.binderClasses do
    seen ← checkName seen "binder class" d.name
  for d in block.judgments do
    seen ← checkName seen "judgment" d.name
  for d in block.rules do
    seen ← checkName seen "rule" d.name
  for d in block.sideConditionSolvers do
    seen ← checkName seen "side-condition solver" d.name
  for d in block.conversionPlugins do
    seen ← checkName seen "conversion plugin" d.name
  for d in block.lfOpaqueConsts do
    seen ← checkName seen "LF opaque constant" d.name
  for d in block.lfObjectDefs do
    seen ← checkName seen "LF object definition" d.name
  for d in block.lfJudgmentTheorems do
    seen ← checkName seen "LF judgment theorem" d.name

/-- Elaborate implicit applications in just the new extension block. -/
def elaborateImplicitAppsInTheoryBlockExtension (flatBase : HLSignature)
    (priorKnownTypes : LFLocalTypes) (block : HLTheoryBlock) : CoreM HLTheoryBlock := do
  let headSig := flatBase.appendBlock block
  let syntaxSorts ← block.syntaxSorts.mapM (elaborateImplicitAppsInSyntaxSortDecl headSig)
  let syntaxAbbrevs ←
    block.syntaxAbbrevs.mapM (elaborateImplicitAppsInSyntaxAbbrevDecl headSig)
  let judgments ← block.judgments.mapM (elaborateImplicitAppsInJudgmentDecl headSig)
  let lfOpaqueConsts ←
    block.lfOpaqueConsts.mapM (elaborateImplicitAppsInLFOpaqueConstDecl headSig)
  let rules ← block.rules.mapM (elaborateImplicitAppsInRuleDecl headSig)
  let metaBlock := {
    block with
    syntaxSorts := syntaxSorts
    syntaxAbbrevs := syntaxAbbrevs
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    rules := rules }
  let sigForObjects := flatBase.appendBlock metaBlock
  let mut knownTypes := priorKnownTypes
  let mut lfObjectDefs := #[]
  for d in block.lfObjectDefs do
    let d ← elaborateImplicitAppsInLFObjectDef sigForObjects knownTypes d
    lfObjectDefs := lfObjectDefs.push d
    knownTypes := knownTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  let blockForTheorems := { metaBlock with lfObjectDefs := lfObjectDefs }
  let sigForTheorems := flatBase.appendBlock blockForTheorems
  let lfJudgmentTheorems ←
    block.lfJudgmentTheorems.mapM
      (elaborateImplicitAppsInLFJudgmentTheorem sigForTheorems knownTypes)
  pure { blockForTheorems with lfJudgmentTheorems := lfJudgmentTheorems }

/-- Expand syntax abbreviations in just the new extension block. -/
def expandSyntaxAbbrevsInTheoryBlockExtension (checkedBase : HLSignature)
    (block : HLTheoryBlock) : CoreM HLTheoryBlock := do
  let sigWithRawBlock := checkedBase.appendBlock block
  let syntaxAbbrevs ← block.syntaxAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sigWithRawBlock "syntax_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sigWithRawBlock "syntax_abbrev" a.name "value" locals
        (sigWithRawBlock.syntaxAbbrevs.size + 1) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let blockWithAbbrevs := { block with syntaxAbbrevs := syntaxAbbrevs }
  let sigForRest := checkedBase.appendBlock blockWithAbbrevs
  let syntaxSorts ← block.syntaxSorts.mapM fun s => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "syntax_sort" s.name s.params
    pure { s with name := s.name.eraseMacroScopes, params }
  let judgments ← block.judgments.mapM fun j => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "judgment" j.name j.params
    pure { j with name := j.name.eraseMacroScopes, params }
  let lfOpaqueConsts ← block.lfOpaqueConsts.mapM fun o => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "lf_opaque" o.name o.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let typeExpr? ←
      o.typeExpr?.mapM (expandSyntaxAbbrevsInExpr sigForRest "lf_opaque" o.name
        "result type" locals (sigForRest.syntaxAbbrevs.size + 1))
    pure { o with name := o.name.eraseMacroScopes, params, typeExpr? }
  let rules ← block.rules.mapM fun r => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "rule" r.name r.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let premises ← r.premises.mapM fun p => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"premise '{p.name.eraseMacroScopes}'" locals
          (sigForRest.syntaxAbbrevs.size + 1) p.judgmentExpr
      pure { p with judgmentExpr }
    let sideConditions ← r.sideConditions.mapM fun sc => do
      let input ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"side-condition '{sc.name.eraseMacroScopes}'" locals
          (sigForRest.syntaxAbbrevs.size + 1) sc.input
      pure { sc with input }
    let paramEvidences ← r.paramEvidences.mapM fun ev => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"evidence '{ev.name.eraseMacroScopes}'" locals
          (sigForRest.syntaxAbbrevs.size + 1) ev.judgmentExpr
      pure { ev with judgmentExpr }
    let conclusionExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "rule" r.name "conclusion" locals
        (sigForRest.syntaxAbbrevs.size + 1) r.conclusionExpr
    pure {
      r with
      name := r.name.eraseMacroScopes
      params := params
      premises := premises
      sideConditions := sideConditions
      paramEvidences := paramEvidences
      conclusionExpr := conclusionExpr }
  let lfObjectDefs ← block.lfObjectDefs.mapM fun d => do
    let typeExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "type" {}
        (sigForRest.syntaxAbbrevs.size + 1) d.typeExpr
    let value ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "value" {}
        (sigForRest.syntaxAbbrevs.size + 1) d.value
    pure { d with name := d.name.eraseMacroScopes, typeExpr, value }
  let lfJudgmentTheorems ← block.lfJudgmentTheorems.mapM fun t => do
    let binders ← expandSyntaxAbbrevsInBindings sigForRest "judgment_theorem" t.name t.binders
    let locals := binders.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let judgmentExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "statement" locals
        (sigForRest.syntaxAbbrevs.size + 1) t.judgmentExpr
    let proof ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "proof" locals
        (sigForRest.syntaxAbbrevs.size + 1) t.proof
    pure { t with name := t.name.eraseMacroScopes, binders, judgmentExpr, proof }
  pure {
    blockWithAbbrevs with
    syntaxSorts := syntaxSorts
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := block.modelVisibilities.map fun v =>
      { v with declName := v.declName.eraseMacroScopes }
    modelSections := block.modelSections.map fun s => { s with name := s.name.eraseMacroScopes }
    modelSectionMemberships := block.modelSectionMemberships.map fun m =>
      { m with
        sectionName := m.sectionName.eraseMacroScopes
        declName := m.declName.eraseMacroScopes }
    rules := rules
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

/-- Check model-visibility metadata added by an incremental extension. -/
def checkModelVisibilityMetadataForExtension (baseSig candidateSig : HLSignature)
    (block : HLTheoryBlock) : CoreM Unit := do
  let declNames := candidateSig.nameSet
  let mut seen : NameSet := {}
  for v in baseSig.modelVisibilities do
    seen := seen.insert v.declName.eraseMacroScopes
  for v in block.modelVisibilities do
    let n := v.declName.eraseMacroScopes
    if seen.contains n then
      throwError "duplicate model visibility annotation for '{n}' in type theory \
        '{candidateSig.name}'"
    seen := seen.insert n
    unless declNames.contains n do
      throwError "model visibility annotation refers to unknown declaration '{n}' in type theory \
        '{candidateSig.name}'"

/-- Check model-section metadata affected by an incremental extension. -/
def checkModelSectionMetadataForExtension (candidateSig : HLSignature)
    (block : HLTheoryBlock) : CoreM Unit := do
  let declNames := candidateSig.nameSet
  let mut sections : NameSet := {}
  for s in candidateSig.modelSections do
    sections := sections.insert s.name.eraseMacroScopes
  for m in block.modelSectionMemberships do
    let sectionName := m.sectionName.eraseMacroScopes
    let declName := m.declName.eraseMacroScopes
    unless sections.contains sectionName do
      throwError "model section membership for '{declName}' refers to unknown section \
        '{sectionName}' in type theory '{candidateSig.name}'"
    unless declNames.contains declName do
      throwError "model section membership refers to unknown declaration '{declName}' in type \
        theory '{candidateSig.name}'"

/-- Check binder hygiene for one syntax-sort declaration. -/
def checkLFLocalBinderHygieneInSyntaxSortDecl (sig : HLSignature) (s : SyntaxSortDecl) :
    CoreM Unit := do
  for b in s.params do
    checkNoLFLocalBinderShadowingInBinding sig "syntax_sort" s.name b

/-- Check binder hygiene for one syntax-abbreviation declaration. -/
def checkLFLocalBinderHygieneInSyntaxAbbrevDecl (sig : HLSignature) (a : SyntaxAbbrevDecl) :
    CoreM Unit := do
  for b in a.params do
    checkNoLFLocalBinderShadowingInBinding sig "syntax_abbrev" a.name b
  checkNoLFLocalBinderShadowingInExpr sig "syntax_abbrev" a.name "value" a.value

/-- Check binder hygiene for one judgment declaration. -/
def checkLFLocalBinderHygieneInJudgmentDecl (sig : HLSignature) (j : JudgmentDecl) :
    CoreM Unit := do
  for b in j.params do
    checkNoLFLocalBinderShadowingInBinding sig "judgment" j.name b

/-- Check binder hygiene for one LF opaque declaration. -/
def checkLFLocalBinderHygieneInLFOpaqueConstDecl (sig : HLSignature) (o : LFOpaqueConstDecl) :
    CoreM Unit := do
  for b in o.params do
    checkNoLFLocalBinderShadowingInBinding sig "lf_opaque" o.name b
  if let some ty := o.typeExpr? then
    checkNoLFLocalBinderShadowingInExpr sig "lf_opaque" o.name "result type" ty

/-- Check binder hygiene for one rule declaration. -/
def checkLFLocalBinderHygieneInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM Unit := do
  for b in r.params do
    checkNoLFLocalBinderShadowingInBinding sig "rule" r.name b
  for p in r.premises do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"premise '{p.name.eraseMacroScopes}'" p.judgmentExpr
  for e in r.paramEvidences do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"evidence '{e.name.eraseMacroScopes}'" e.judgmentExpr
  for sc in r.sideConditions do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"side-condition '{sc.name.eraseMacroScopes}'" sc.input
  checkNoLFLocalBinderShadowingInExpr sig "rule" r.name "conclusion" r.conclusionExpr

/-- Check binder hygiene for one LF object definition. -/
def checkLFLocalBinderHygieneInLFObjectDefDecl (sig : HLSignature) (d : LFObjectDefDecl) :
    CoreM Unit := do
  checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "type" d.typeExpr
  checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "value" d.value

/-- Check binder hygiene for one LF judgment theorem. -/
def checkLFLocalBinderHygieneInLFJudgmentTheoremDecl (sig : HLSignature)
    (t : LFJudgmentTheoremDecl) : CoreM Unit := do
  for b in t.binders do
    checkNoLFLocalBinderShadowingInBinding sig "judgment_theorem" t.name b
  checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "statement"
    t.judgmentExpr
  checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Check universe parameters for one syntax-sort declaration. -/
def checkLFUniverseLevelInSyntaxSortDecl (sig : HLSignature) (s : SyntaxSortDecl) :
    CoreM Unit := do
  for b in s.params do
    checkDeclaredLevelParamsInLFBinding sig "syntax_sort" s.name b

/-- Check universe parameters for one syntax-abbreviation declaration. -/
def checkLFUniverseLevelInSyntaxAbbrevDecl (sig : HLSignature) (a : SyntaxAbbrevDecl) :
    CoreM Unit := do
  for b in a.params do
    checkDeclaredLevelParamsInLFBinding sig "syntax_abbrev" a.name b
  checkDeclaredLevelParamsInLFExpr sig "syntax_abbrev" a.name "value" a.value

/-- Check universe parameters for one judgment declaration. -/
def checkLFUniverseLevelInJudgmentDecl (sig : HLSignature) (j : JudgmentDecl) : CoreM Unit := do
  for b in j.params do
    checkDeclaredLevelParamsInLFBinding sig "judgment" j.name b

/-- Check universe parameters for one LF opaque declaration. -/
def checkLFUniverseLevelInLFOpaqueConstDecl (sig : HLSignature) (o : LFOpaqueConstDecl) :
    CoreM Unit := do
  for b in o.params do
    checkDeclaredLevelParamsInLFBinding sig "lf_opaque" o.name b
  if let some ty := o.typeExpr? then
    checkDeclaredLevelParamsInLFExpr sig "lf_opaque" o.name "result type" ty

/-- Check universe parameters for one rule declaration. -/
def checkLFUniverseLevelInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM Unit := do
  for b in r.params do
    checkDeclaredLevelParamsInLFBinding sig "rule" r.name b
  for p in r.premises do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"premise '{p.name.eraseMacroScopes}'" p.judgmentExpr
  for e in r.paramEvidences do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"evidence '{e.name.eraseMacroScopes}'" e.judgmentExpr
  for sc in r.sideConditions do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"side-condition '{sc.name.eraseMacroScopes}'" sc.input
  checkDeclaredLevelParamsInLFExpr sig "rule" r.name "conclusion" r.conclusionExpr

/-- Check universe parameters for one LF object definition. -/
def checkLFUniverseLevelInLFObjectDefDecl (sig : HLSignature) (d : LFObjectDefDecl) :
    CoreM Unit := do
  checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "type" d.typeExpr
  checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "value" d.value

/-- Check universe parameters for one LF judgment theorem. -/
def checkLFUniverseLevelInLFJudgmentTheoremDecl (sig : HLSignature)
    (t : LFJudgmentTheoremDecl) : CoreM Unit := do
  for b in t.binders do
    checkDeclaredLevelParamsInLFBinding sig "judgment_theorem" t.name b
  checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
  checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Checked artifacts produced by an incremental theory-extension pass. -/
structure CheckedTheoryDelta where
  syntaxSorts : Array CheckedLFSyntaxSort := #[]
  syntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  syntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  contextZones : Array CheckedLFContextZone := #[]
  binderClasses : Array CheckedLFBinderClass := #[]
  judgments : Array CheckedLFJudgment := #[]
  judgmentRoles : Array JudgmentRoleDecl := #[]
  opaqueConsts : Array CheckedLFOpaqueConst := #[]
  sideConditionSolvers : Array CheckedLFSideConditionSolver := #[]
  conversionPlugins : Array CheckedLFConversionPlugin := #[]
  rules : Array CheckedLFRule := #[]
  ruleRoles : Array RuleRoleDecl := #[]
  rewriteRelations : Array LFRewriteRelationDecl := #[]
  rewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  rewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  transportRules : Array LFTransportRuleDecl := #[]
  transportPositions : Array LFTransportPositionDecl := #[]
  ruleSchemas : Array CheckedLFRuleSchema := #[]
  sideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  objectDefs : Array CheckedLFObjectDef := #[]
  judgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  modelVisibilities : Array ModelVisibilityDecl := #[]
  modelSections : Array ModelSectionDecl := #[]
  modelSectionMemberships : Array ModelSectionMembershipDecl := #[]
  deriving Inhabited, Repr, BEq

/-- Append an incrementally checked delta and refresh derived checked-signature caches. -/
def appendCheckedTheoryDelta (checked : CheckedSignature) (delta : CheckedTheoryDelta) :
    CheckedSignature :=
  let lfSyntaxSorts := checked.lfSyntaxSorts ++ delta.syntaxSorts
  let lfSyntaxAbbrevs := checked.lfSyntaxAbbrevs ++ delta.syntaxAbbrevs
  let lfSyntaxSortRoles := checked.lfSyntaxSortRoles ++ delta.syntaxSortRoles
  let lfContextZones := checked.lfContextZones ++ delta.contextZones
  let lfBinderClasses := checked.lfBinderClasses ++ delta.binderClasses
  let lfJudgments := checked.lfJudgments ++ delta.judgments
  let lfJudgmentRoles := checked.lfJudgmentRoles ++ delta.judgmentRoles
  let lfOpaqueConsts := checked.lfOpaqueConsts ++ delta.opaqueConsts
  let lfSideConditionSolvers := checked.lfSideConditionSolvers ++ delta.sideConditionSolvers
  let lfConversionPlugins := checked.lfConversionPlugins ++ delta.conversionPlugins
  let lfRules := checked.lfRules ++ delta.rules
  let lfRuleRoles := checked.lfRuleRoles ++ delta.ruleRoles
  let lfRewriteRelations := checked.lfRewriteRelations ++ delta.rewriteRelations
  let lfRewriteSymmetries := checked.lfRewriteSymmetries ++ delta.rewriteSymmetries
  let lfRewriteCongruences := checked.lfRewriteCongruences ++ delta.rewriteCongruences
  let lfTransportRules := checked.lfTransportRules ++ delta.transportRules
  let lfTransportPositions := checked.lfTransportPositions ++ delta.transportPositions
  let lfRuleSchemas := checked.lfRuleSchemas ++ delta.ruleSchemas
  let lfSideConditionCertificates :=
    checked.lfSideConditionCertificates ++ delta.sideConditionCertificates
  let lfObjectDefs := checked.lfObjectDefs ++ delta.objectDefs
  let lfJudgmentTheorems := checked.lfJudgmentTheorems ++ delta.judgmentTheorems
  let modelVisibilities := checked.modelVisibilities ++ delta.modelVisibilities
  let modelSections := dedupeModelSections (checked.modelSections ++ delta.modelSections)
  let modelSectionMemberships :=
    checked.modelSectionMemberships ++ delta.modelSectionMemberships
  let defValues := checkedLFDefinitionValues lfObjectDefs
  let lfKernelRuleSchemas :=
    if delta.objectDefs.isEmpty && delta.ruleSchemas.isEmpty then
      checked.lfKernelRuleSchemas
    else
      checkedLFRuleSchemasToKernel defValues lfRuleSchemas
  let lfEnvironment : CheckedLFEnvironment := {
    checked.lfEnvironment with
    syntaxSorts := lfSyntaxSorts
    syntaxAbbrevs := lfSyntaxAbbrevs
    syntaxSortRoles := lfSyntaxSortRoles
    contextZones := lfContextZones
    binderClasses := lfBinderClasses
    judgments := lfJudgments
    judgmentRoles := lfJudgmentRoles
    opaqueConsts := lfOpaqueConsts
    sideConditionSolvers := lfSideConditionSolvers
    conversionPlugins := lfConversionPlugins
    rules := lfRules
    ruleRoles := lfRuleRoles
    rewriteRelations := lfRewriteRelations
    rewriteSymmetries := lfRewriteSymmetries
    rewriteCongruences := lfRewriteCongruences
    transportRules := lfTransportRules
    transportPositions := lfTransportPositions
    ruleSchemas := lfRuleSchemas
    sideConditionCertificates := lfSideConditionCertificates
    objectDefs := lfObjectDefs
    judgmentTheorems := lfJudgmentTheorems }
  { checked with
    lfSyntaxSorts := lfSyntaxSorts
    lfSyntaxAbbrevs := lfSyntaxAbbrevs
    lfSyntaxSortRoles := lfSyntaxSortRoles
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfJudgments := lfJudgments
    lfJudgmentRoles := lfJudgmentRoles
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := modelVisibilities
    modelSections := modelSections
    modelSectionMemberships := modelSectionMemberships
    lfSideConditionSolvers := lfSideConditionSolvers
    lfConversionPlugins := lfConversionPlugins
    lfRules := lfRules
    lfRuleRoles := lfRuleRoles
    lfRewriteRelations := lfRewriteRelations
    lfRewriteSymmetries := lfRewriteSymmetries
    lfRewriteCongruences := lfRewriteCongruences
    lfTransportRules := lfTransportRules
    lfTransportPositions := lfTransportPositions
    lfRuleSchemas := lfRuleSchemas
    lfEnvironment := lfEnvironment
    lfKernelRuleSchemas := lfKernelRuleSchemas
    lfSideConditionCertificates := lfSideConditionCertificates
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

/-- Cached kernel-facing replay state shared by all theorem checks in one block. -/
structure IntraBlockKernelReplayContext where
  /-- Low-level kernel signature built once for the candidate block. -/
  kernelSig : Signature
  /-- Replay context containing prior checked theorems and certificates. -/
  replayCtx : KernelLFCheckContext
  /-- Global LF heads used to lower local theorem assumptions. -/
  lfKernelGlobalHeads : NameMap (CheckedLFHeadKind × Option Nat)
  /-- LF definition values available while normalizing replay statements. -/
  lfKernelDefValues : LFDefinitionValueMap
  deriving Inhabited

/-- Build cached replay state for a checked baseline plus one checked block delta. -/
def mkIntraBlockKernelReplayContext (sig : HLSignature) (checked : CheckedSignature)
    (delta : CheckedTheoryDelta := {}) (objectDefs : Array CheckedLFObjectDef := #[])
    (theoremCandidates : Array CheckedLFJudgmentTheorem := #[]) :
    IntraBlockKernelReplayContext :=
  let lfOpaqueConsts := checked.lfOpaqueConsts ++ delta.opaqueConsts
  let lfContextZones := checked.lfContextZones ++ delta.contextZones
  let lfBinderClasses := checked.lfBinderClasses ++ delta.binderClasses
  let lfConversionPlugins := checked.lfConversionPlugins ++ delta.conversionPlugins
  let lfRuleSchemas := checked.lfRuleSchemas ++ delta.ruleSchemas
  let lfObjectDefs := checked.lfObjectDefs ++ objectDefs
  let lfJudgmentTheorems := checked.lfJudgmentTheorems ++ theoremCandidates
  let lfCheckedDefValues := checkedLFDefinitionValues lfObjectDefs
  let kernelSig : Signature := {
    name := sig.name.eraseMacroScopes
    constants := (checkedLFConstantsToKernel lfCheckedDefValues lfOpaqueConsts lfObjectDefs).toList
    contextZones := lfContextZones.toList.map checkedLFContextZoneToKernel
    binderClasses := lfBinderClasses.toList.map checkedLFBinderClassToKernel
    conversionPlugins := lfConversionPlugins.toList.map checkedLFConversionPluginToKernel
    rules :=
      (checkedLFRuleSchemasToKernel lfCheckedDefValues lfRuleSchemas ++
        kernelLFRuleSchemasOfTheorems lfCheckedDefValues lfJudgmentTheorems).toList }
  let replayCtx : KernelLFCheckContext := Id.run do
    let mut replayCtx : KernelLFCheckContext := {
      certificates := kernelLFCertificateEntriesOfTheorems lfJudgmentTheorems }
    for prior in checked.lfJudgmentTheorems do
      if prior.binders.isEmpty then
        if let some priorKernel := prior.kernelDerivation? then
          replayCtx := replayCtx.addTheorem prior.name (KernelLFDerivation.statement priorKernel)
    return replayCtx
  { kernelSig := kernelSig
    replayCtx := replayCtx
    lfKernelGlobalHeads := lfGlobalHeadInfo sig
    lfKernelDefValues := lfDefinitionValueMapFromCheckedDefs lfObjectDefs }

/-- Replay-check one theorem against cached block-level kernel state and update availability. -/
def validateLFTheoremKernelReplayInContext (sig : HLSignature)
    (ctx : IntraBlockKernelReplayContext) (t : CheckedLFJudgmentTheorem) :
    CoreM (CheckedLFJudgmentTheorem × IntraBlockKernelReplayContext) := do
  let some kernelDeriv := t.kernelDerivation?
    | pure (t, ctx)
  let stmt := KernelLFDerivation.statement kernelDeriv
  let assumptions ← kernelLFLocalAssumptionEntriesOfTheoremNormalized sig
    ctx.lfKernelGlobalHeads ctx.lfKernelDefValues t
  let localReplayCtx := { ctx.replayCtx with
    localParameters := t.binders.toList.map (fun b => b.name)
    assumptions := assumptions }
  match CheckedKernelLFDerivation.ofReplay ctx.kernelSig localReplayCtx stmt kernelDeriv with
  | .ok checkedReplay =>
      let t := { t with checkedKernelDerivation? := some checkedReplay }
      let replayCtx :=
        if t.binders.isEmpty then ctx.replayCtx.addTheorem t.name stmt else ctx.replayCtx
      pure (t, { ctx with replayCtx := replayCtx })
  | .error err =>
      throwError "kernel-facing replay check failed for judgment_theorem '{t.name}' in type theory \
        '{sig.name}': {err}"

/-- Replay-check all new theorem artifacts in one block using one cached kernel signature. -/
def validateLFTheoremKernelReplayBlock (sig : HLSignature)
    (ctx : IntraBlockKernelReplayContext) (theorems : Array CheckedLFJudgmentTheorem) :
    CoreM (Array CheckedLFJudgmentTheorem × IntraBlockKernelReplayContext) := do
  let mut ctx := ctx
  let mut checkedTheorems := #[]
  for t in theorems do
    let (t, ctx') ← validateLFTheoremKernelReplayInContext sig ctx t
    ctx := ctx'
    checkedTheorems := checkedTheorems.push t
  pure (checkedTheorems, ctx)

/-- Check simple role metadata added by one incremental extension block. -/
def checkIncrementalRoleMetadataDelta (flatForCheck : HLSignature)
    (checkedBase : CheckedSignature) (block : HLTheoryBlock) :
    CoreM (Array SyntaxSortRoleDecl × Array JudgmentRoleDecl × Array RuleRoleDecl) := do
  let syntaxSortNames : NameSet :=
    flatForCheck.syntaxSorts.foldl (init := {}) fun acc s => acc.insert s.name.eraseMacroScopes
  let judgmentNames : NameSet :=
    flatForCheck.judgments.foldl (init := {}) fun acc j => acc.insert j.name.eraseMacroScopes
  let ruleNames : NameSet :=
    flatForCheck.rules.foldl (init := {}) fun acc r => acc.insert r.name.eraseMacroScopes
  let mut seenSortRoles : NameMap NameSet := {}
  for role in checkedBase.lfSyntaxSortRoles do
    let sortName := role.sortName.eraseMacroScopes
    let kinds := (seenSortRoles.find? sortName).getD {}
    seenSortRoles := seenSortRoles.insert sortName (kinds.insert role.kind.eraseMacroScopes)
  let mut syntaxSortRoles := #[]
  for role in block.syntaxSortRoles do
    let sortName := role.sortName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !syntaxSortNames.contains sortName then
      throwError "syntax_sort_role for unknown syntax sort '{role.sortName}' in type theory \
        '{flatForCheck.name}'"
    let kinds := (seenSortRoles.find? sortName).getD {}
    if kinds.contains kind then
      throwError "duplicate syntax_sort_role '{role.kind}' for syntax sort '{role.sortName}' in \
        type theory '{flatForCheck.name}'"
    seenSortRoles := seenSortRoles.insert sortName (kinds.insert kind)
    syntaxSortRoles := syntaxSortRoles.push { sortName := sortName, kind := kind }
  let mut seenJudgmentRoles : NameMap NameSet := {}
  for role in checkedBase.lfJudgmentRoles do
    let judgmentName := role.judgmentName.eraseMacroScopes
    let kinds := (seenJudgmentRoles.find? judgmentName).getD {}
    seenJudgmentRoles :=
      seenJudgmentRoles.insert judgmentName (kinds.insert role.kind.eraseMacroScopes)
  let mut judgmentRoles := #[]
  for role in block.judgmentRoles do
    let judgmentName := role.judgmentName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !judgmentNames.contains judgmentName then
      throwError "judgment_role for unknown judgment '{role.judgmentName}' in type theory \
        '{flatForCheck.name}'"
    let kinds := (seenJudgmentRoles.find? judgmentName).getD {}
    if kinds.contains kind then
      throwError "duplicate judgment_role '{role.kind}' for judgment '{role.judgmentName}' in \
        type theory '{flatForCheck.name}'"
    seenJudgmentRoles := seenJudgmentRoles.insert judgmentName (kinds.insert kind)
    judgmentRoles := judgmentRoles.push { judgmentName := judgmentName, kind := kind }
  let mut seenRuleRoles : NameMap NameSet := {}
  for role in checkedBase.lfRuleRoles do
    let ruleName := role.ruleName.eraseMacroScopes
    let kinds := (seenRuleRoles.find? ruleName).getD {}
    seenRuleRoles := seenRuleRoles.insert ruleName (kinds.insert role.kind.eraseMacroScopes)
  let mut ruleRoles := #[]
  for role in block.ruleRoles do
    let ruleName := role.ruleName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !ruleNames.contains ruleName then
      throwError "rule_role for unknown rule '{role.ruleName}' in type theory '{flatForCheck.name}'"
    let kinds := (seenRuleRoles.find? ruleName).getD {}
    if kinds.contains kind then
      throwError "duplicate rule_role '{role.kind}' for rule '{role.ruleName}' in type theory \
        '{flatForCheck.name}'"
    seenRuleRoles := seenRuleRoles.insert ruleName (kinds.insert kind)
    ruleRoles := ruleRoles.push { ruleName := ruleName, kind := kind }
  pure (syntaxSortRoles, judgmentRoles, ruleRoles)

/-- Check context-zone and binder-class metadata added by one incremental extension block. -/
def checkIncrementalContextBinderMetadataDelta (flatForCheck : HLSignature)
    (checkedBase : CheckedSignature) (block : HLTheoryBlock) :
    CoreM (Array CheckedLFContextZone × Array CheckedLFBinderClass) := do
  let syntaxSortNames : NameSet :=
    flatForCheck.syntaxSorts.foldl (init := {}) fun acc s => acc.insert s.name.eraseMacroScopes
  let mut seenZones : NameSet :=
    checkedBase.lfContextZones.foldl (init := {}) fun acc z => acc.insert z.name.eraseMacroScopes
  let mut checkedContextZones := #[]
  for zone in block.contextZones do
    let zoneName := zone.name.eraseMacroScopes
    let sortName := zone.sortName.eraseMacroScopes
    if seenZones.contains zoneName then
      throwError "duplicate context_zone '{zoneName}' in type theory '{flatForCheck.name}'"
    if !syntaxSortNames.contains sortName then
      throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' uses unknown \
        syntax sort '{zone.sortName}'"
    let mut seenDeps : NameSet := {}
    for dep in zone.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' has \
          duplicate dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !seenZones.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' depends on \
          unknown or later zone '{dep}'"
    seenZones := seenZones.insert zoneName
    checkedContextZones := checkedContextZones.push (checkedLFContextZoneDeclArtifact zone)
  let mut seenBinderClasses : NameSet :=
    checkedBase.lfBinderClasses.foldl (init := {}) fun acc b =>
      acc.insert b.name.eraseMacroScopes
  let allZones : NameSet :=
    flatForCheck.contextZones.foldl (init := {}) fun acc z => acc.insert z.name.eraseMacroScopes
  let mut checkedBinderClasses := #[]
  for binderClass in block.binderClasses do
    let binderName := binderClass.name.eraseMacroScopes
    let sortName := binderClass.boundSortName.eraseMacroScopes
    let zoneName := binderClass.zoneName.eraseMacroScopes
    if seenBinderClasses.contains binderName then
      throwError "duplicate binder_class '{binderName}' in type theory '{flatForCheck.name}'"
    seenBinderClasses := seenBinderClasses.insert binderName
    if !syntaxSortNames.contains sortName then
      throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' uses \
        unknown syntax sort '{binderClass.boundSortName}'"
    if !allZones.contains zoneName then
      throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' uses \
        unknown context zone '{binderClass.zoneName}'"
    let mut seenDeps : NameSet := {}
    for dep in binderClass.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' has \
          duplicate dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !allZones.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' \
          depends on unknown context zone '{dep}'"
    checkedBinderClasses := checkedBinderClasses.push (checkedLFBinderClassDeclArtifact binderClass)
  pure (checkedContextZones, checkedBinderClasses)

/-- Check metadata declarations in a theory block and collect checked delta artifacts. -/
def checkTheoryBlockMetadataDelta (flatForCheck : HLSignature) (checkedBase : CheckedSignature)
    (block : HLTheoryBlock) : CoreM CheckedTheoryDelta := do
  let lfGlobals := lfKnownGlobalNames flatForCheck
  let opaqueArities := lfOpaqueArities flatForCheck
  let globalHeads := lfGlobalHeadInfo flatForCheck
  let syntaxSortArities : NameMap Nat := flatForCheck.syntaxSorts.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes s.params.size
  let judgmentArities : NameMap Nat := flatForCheck.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let solvers : NameSet := flatForCheck.sideConditionSolvers.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes
  let mut checkedSyntaxSorts : Array CheckedLFSyntaxSort := #[]
  for s in block.syntaxSorts do
    checkLFLocalBinderHygieneInSyntaxSortDecl flatForCheck s
    checkLFUniverseLevelInSyntaxSortDecl flatForCheck s
    checkOneSyntaxSortMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
      syntaxSortArities s
    checkedSyntaxSorts :=
      checkedSyntaxSorts.push (← checkedLFSyntaxSortDeclArtifact flatForCheck globalHeads s)
  let mut checkedSyntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  for a in block.syntaxAbbrevs do
    checkLFLocalBinderHygieneInSyntaxAbbrevDecl flatForCheck a
    checkLFUniverseLevelInSyntaxAbbrevDecl flatForCheck a
    checkOneSyntaxAbbrevMetadataInSignature flatForCheck lfGlobals opaqueArities
      syntaxSortArities globalHeads a
    checkedSyntaxAbbrevs :=
      checkedSyntaxAbbrevs.push (← checkedLFSyntaxAbbrevDeclArtifact flatForCheck globalHeads a)
  let (checkedSyntaxSortRoles, checkedJudgmentRoles, checkedRuleRoles) ←
    checkIncrementalRoleMetadataDelta flatForCheck checkedBase block
  let (checkedContextZones, checkedBinderClasses) ←
    checkIncrementalContextBinderMetadataDelta flatForCheck checkedBase block
  let mut checkedJudgments : Array CheckedLFJudgment := #[]
  for j in block.judgments do
    checkLFLocalBinderHygieneInJudgmentDecl flatForCheck j
    checkLFUniverseLevelInJudgmentDecl flatForCheck j
    checkOneJudgmentMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
      syntaxSortArities j
    checkedJudgments :=
      checkedJudgments.push (← checkedLFJudgmentDeclArtifact flatForCheck globalHeads j)
  let mut checkedOpaques : Array CheckedLFOpaqueConst := #[]
  for o in block.lfOpaqueConsts do
    checkLFLocalBinderHygieneInLFOpaqueConstDecl flatForCheck o
    checkLFUniverseLevelInLFOpaqueConstDecl flatForCheck o
    checkOneLFOpaqueConstMetadataInSignature flatForCheck lfGlobals opaqueArities
      syntaxSortArities globalHeads o
    checkedOpaques :=
      checkedOpaques.push (← checkedLFOpaqueConstDeclArtifact flatForCheck globalHeads o)
  let checkedSolvers := block.sideConditionSolvers.map checkedLFSideConditionSolverDeclArtifact
  let mut checkedPlugins : Array CheckedLFConversionPlugin := #[]
  for p in block.conversionPlugins do
    checkOneConversionPluginMetadataInSignature flatForCheck p
    checkedPlugins := checkedPlugins.push (checkedLFConversionPluginDeclArtifact p)
  let mut checkedRules : Array CheckedLFRule := #[]
  for r in block.rules do
    checkLFLocalBinderHygieneInRuleDecl flatForCheck r
    checkLFUniverseLevelInRuleDecl flatForCheck r
    let checkedRule ←
      checkOneRuleMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
        syntaxSortArities judgmentArities solvers r
    checkedRules := checkedRules.push checkedRule
  let checkedRuleSchemas := checkedRules.map
    (checkedLFRuleSchemaOfRule (checkedBase.lfContextZones ++ checkedContextZones)
      (checkedBase.lfBinderClasses ++ checkedBinderClasses))
  let checkedCertificates := checkedLFSideConditionCertificatesOfSchemas checkedRuleSchemas
  pure {
    syntaxSorts := checkedSyntaxSorts
    syntaxAbbrevs := checkedSyntaxAbbrevs
    syntaxSortRoles := checkedSyntaxSortRoles
    contextZones := checkedContextZones
    binderClasses := checkedBinderClasses
    judgments := checkedJudgments
    judgmentRoles := checkedJudgmentRoles
    opaqueConsts := checkedOpaques
    sideConditionSolvers := checkedSolvers
    conversionPlugins := checkedPlugins
    rules := checkedRules
    ruleRoles := checkedRuleRoles
    ruleSchemas := checkedRuleSchemas
    sideConditionCertificates := checkedCertificates
    modelVisibilities := block.modelVisibilities
    modelSections := block.modelSections
    modelSectionMemberships := block.modelSectionMemberships }

/-- Stream-check all artifacts in one theory block and return a single appendable delta. -/
def checkTheoryBlockDeltaStreaming (flatForCheck : HLSignature) (checkedBase : CheckedSignature)
    (block : HLTheoryBlock) : CoreM CheckedTheoryDelta := do
  let metadataDelta ← checkTheoryBlockMetadataDelta flatForCheck checkedBase block
  let mut ctx := mkIntraBlockLFCheckContext flatForCheck checkedBase metadataDelta.rules
    metadataDelta.ruleSchemas metadataDelta.sideConditionCertificates
  for d in block.lfObjectDefs do
    checkLFLocalBinderHygieneInLFObjectDefDecl flatForCheck d
    checkLFUniverseLevelInLFObjectDefDecl flatForCheck d
    let (_, ctx') ← checkLFObjectDefInContext ctx d
    ctx := ctx'
  for t in block.lfJudgmentTheorems do
    checkLFLocalBinderHygieneInLFJudgmentTheoremDecl flatForCheck t
    checkLFUniverseLevelInLFJudgmentTheoremDecl flatForCheck t
    let (_, ctx') ← checkLFJudgmentTheoremInContext ctx t
    ctx := ctx'
  let replayCtx := mkIntraBlockKernelReplayContext flatForCheck checkedBase metadataDelta
    ctx.newObjectDefs ctx.newJudgmentTheorems
  let (checkedTheorems, _) ←
    validateLFTheoremKernelReplayBlock flatForCheck replayCtx ctx.newJudgmentTheorems
  pure { metadataDelta with
    objectDefs := ctx.newObjectDefs
    judgmentTheorems := checkedTheorems }

/-- Incrementally check a supported `extend_type_theory` block against a checked baseline. -/
def checkTheoryBlockExtensionIncremental (theoryName : Name) (sig : HLSignature)
    (checked : CheckedSignature) (block : HLTheoryBlock) :
    CoreM (HLTheoryBlock × CheckedSignature) := do
  if let some reason := unsupportedIncrementalTheoryBlockReason? block then
    throwError "cannot incrementally register extension for type theory '{theoryName}': {reason}"
  let flatSourceBase ← flattenSignature sig
  checkNoExtensionNameCollisions flatSourceBase block
  let priorKnownTypes := checkedLFDefinitionTypeMapFromDefs checked.lfObjectDefs
  let blockForRegistry ←
    elaborateImplicitAppsInTheoryBlockExtension flatSourceBase priorKnownTypes block
  let checkedBase := checkedSignatureToHLSignature flatSourceBase checked
  let blockForCheck ← expandSyntaxAbbrevsInTheoryBlockExtension checkedBase blockForRegistry
  let flatForCheck := checkedBase.appendBlock blockForCheck
  checkModelVisibilityMetadataForExtension checkedBase flatForCheck blockForCheck
  checkModelSectionMetadataForExtension flatForCheck blockForCheck
  let delta ← checkTheoryBlockDeltaStreaming flatForCheck checked blockForCheck
  let checked := appendCheckedTheoryDelta checked delta
  pure (blockForRegistry, checked)

/-- Check a candidate signature with the direct-LF checker and report command errors. -/
def checkSignatureForRegistration (sig : HLSignature) : CoreM CheckedSignature := do
  let flat ← flattenSignature sig
  checkNoDuplicateNamesInSignature flat
  checkModelVisibilityMetadataInSignature flat
  checkModelSectionMetadataInSignature flat
  let flat ← expandSyntaxAbbrevsInSignature flat
  checkLFLocalBinderHygieneMetadata flat
  checkLFUniverseLevelMetadata flat
  let lfRules ← checkRuleMetadataInSignature flat
  checkLFRewriteTransportMetadata flat
  let (lfObjectDefsFromDecls, lfJudgmentTheoremsFromDecls) ←
    checkLFObjectArtifactsInSignatureStreaming flat lfRules
  let lfObjectDefs := lfObjectDefsFromDecls
  let lfJudgmentTheoremsRaw := lfJudgmentTheoremsFromDecls
  let (lfSyntaxSorts, lfSyntaxAbbrevs, lfContextZones, lfBinderClasses, lfJudgments, lfOpaqueConsts,
    lfSideConditionSolvers, lfConversionPlugins) ← checkedLFDeclarations flat
  let lfSyntaxSortRoles := flat.syntaxSortRoles.map fun r =>
    { sortName := r.sortName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfJudgmentRoles := flat.judgmentRoles.map fun r =>
    { judgmentName := r.judgmentName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfRuleRoles := flat.ruleRoles.map fun r =>
    { ruleName := r.ruleName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfRewriteRelations := flat.rewriteRelations.map fun r =>
    { relationName := r.relationName.eraseMacroScopes
      lhsParam := r.lhsParam.eraseMacroScopes
      rhsParam := r.rhsParam.eraseMacroScopes }
  let lfRewriteSymmetries := flat.rewriteSymmetries.map fun r =>
    { symmetryName := r.symmetryName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      evidenceParam := r.evidenceParam.eraseMacroScopes }
  let lfRewriteCongruences := flat.rewriteCongruences.map fun r =>
    { congruenceName := r.congruenceName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      targetHead := r.targetHead.eraseMacroScopes
      argumentIndex := r.argumentIndex
      evidenceParam := r.evidenceParam.eraseMacroScopes }
  let lfTransportRules := flat.transportRules.map fun r =>
    { ruleName := r.ruleName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      evidencePremise := r.evidencePremise.eraseMacroScopes
      sourcePremise := r.sourcePremise.eraseMacroScopes }
  let lfTransportPositions := flat.transportPositions.map fun p =>
    { ruleName := p.ruleName.eraseMacroScopes
      targetHead := p.targetHead.eraseMacroScopes
      argumentIndex := p.argumentIndex }
  let lfRuleSchemas := checkedLFRuleSchemasOfRules lfContextZones lfBinderClasses lfRules
  let lfSideConditionCertificates := checkedLFSideConditionCertificatesOfSchemas lfRuleSchemas
  let lfCheckedDefValues := checkedLFDefinitionValues lfObjectDefs
  let lfKernelRuleSchemas := checkedLFRuleSchemasToKernel lfCheckedDefValues lfRuleSchemas
  let replayDelta : CheckedTheoryDelta := {
    syntaxSorts := lfSyntaxSorts
    syntaxAbbrevs := lfSyntaxAbbrevs
    syntaxSortRoles := lfSyntaxSortRoles
    contextZones := lfContextZones
    binderClasses := lfBinderClasses
    judgments := lfJudgments
    judgmentRoles := lfJudgmentRoles
    opaqueConsts := lfOpaqueConsts
    sideConditionSolvers := lfSideConditionSolvers
    conversionPlugins := lfConversionPlugins
    rules := lfRules
    ruleRoles := lfRuleRoles
    rewriteRelations := lfRewriteRelations
    rewriteSymmetries := lfRewriteSymmetries
    rewriteCongruences := lfRewriteCongruences
    transportRules := lfTransportRules
    transportPositions := lfTransportPositions
    ruleSchemas := lfRuleSchemas
    sideConditionCertificates := lfSideConditionCertificates }
  let replayBase : CheckedSignature := {
    name := flat.name.eraseMacroScopes
    levelParams := flat.levelParams.map Name.eraseMacroScopes }
  let replayCtx := mkIntraBlockKernelReplayContext flat replayBase replayDelta lfObjectDefs
    lfJudgmentTheoremsRaw
  let (lfJudgmentTheorems, _) ←
    validateLFTheoremKernelReplayBlock flat replayCtx lfJudgmentTheoremsRaw
  let flat ← expandSurfaceFunctionsInSignature flat
  let lfEnvironment : CheckedLFEnvironment :=
    { theoryName := flat.name.eraseMacroScopes
      levelParams := flat.levelParams.map Name.eraseMacroScopes
      syntaxSorts := lfSyntaxSorts
      syntaxAbbrevs := lfSyntaxAbbrevs
      syntaxSortRoles := lfSyntaxSortRoles
      contextZones := lfContextZones
      binderClasses := lfBinderClasses
      judgments := lfJudgments
      judgmentRoles := lfJudgmentRoles
      opaqueConsts := lfOpaqueConsts
      sideConditionSolvers := lfSideConditionSolvers
      conversionPlugins := lfConversionPlugins
      rules := lfRules
      ruleRoles := lfRuleRoles
      rewriteRelations := lfRewriteRelations
      rewriteSymmetries := lfRewriteSymmetries
      rewriteCongruences := lfRewriteCongruences
      transportRules := lfTransportRules
      transportPositions := lfTransportPositions
      ruleSchemas := lfRuleSchemas
      sideConditionCertificates := lfSideConditionCertificates
      objectDefs := lfObjectDefs
      judgmentTheorems := lfJudgmentTheorems }
  pure {
    name := flat.name
    levelParams := flat.levelParams.map Name.eraseMacroScopes
    lfSyntaxSorts := lfSyntaxSorts
    lfSyntaxAbbrevs := lfSyntaxAbbrevs
    lfSyntaxSortRoles := lfSyntaxSortRoles
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfJudgments := lfJudgments
    lfJudgmentRoles := lfJudgmentRoles
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := flat.modelVisibilities.map (fun v =>
      { v with declName := v.declName.eraseMacroScopes })
    modelSections := dedupeModelSections flat.modelSections
    modelSectionMemberships := flat.modelSectionMemberships.map (fun m =>
      { m with
        sectionName := m.sectionName.eraseMacroScopes
        declName := m.declName.eraseMacroScopes })
    lfSideConditionSolvers := lfSideConditionSolvers
    lfConversionPlugins := lfConversionPlugins
    lfRules := lfRules
    lfRuleRoles := lfRuleRoles
    lfRewriteRelations := lfRewriteRelations
    lfRewriteSymmetries := lfRewriteSymmetries
    lfRewriteCongruences := lfRewriteCongruences
    lfTransportRules := lfTransportRules
    lfTransportPositions := lfTransportPositions
    lfRuleSchemas := lfRuleSchemas
    lfEnvironment := lfEnvironment
    lfKernelRuleSchemas := lfKernelRuleSchemas
    lfSideConditionCertificates := lfSideConditionCertificates
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }


end InternalLean
