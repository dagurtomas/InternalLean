/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.InternalTactic
public meta import Lean.Elab.Term

/-!
# Experimental Lean-elaborated LF frontend

This module implements the first vertical slice of a Lean-elaborated frontend.  Term bodies are
elaborated by Lean against generated `T.LFQuote` stubs, reflected back to `ObjExpr`, and then
registered through the existing InternalLean LF checker.
-/

@[expose] public meta section

open Lean Elab Command Term Meta

namespace InternalLean

/-- Local Lean free variables introduced for an experimental quoted-LF elaboration. -/
abbrev LFQuoteLocalMap := Array (FVarId × Name)

/-- Find the LF source name for a quoted local Lean free variable. -/
def findLFQuoteLocal? (locals : LFQuoteLocalMap) (fvarId : FVarId) : Option Name :=
  Id.run do
  for (fid, n) in locals do
    if fid == fvarId then
      return some n
  return none

/-- Return the source LF name encoded by a quote-stub constant for `theoryName`. -/
def lfQuoteSourceNameOfConst? (theoryName : Name) (constName : Name) : Option Name :=
  let ns := lfQuoteNamespace theoryName
  if ns.isPrefixOf constName then
    let localName := constName.replacePrefix ns .anonymous
    if localName.isAnonymous then none else some localName.eraseMacroScopes
  else
    none

/-- Reflect one Lean expression elaborated against quoted-LF stubs back to an `ObjExpr`. -/
partial def reflectLFQuoteExpr (theoryName : Name) (locals : LFQuoteLocalMap) :
    Expr → MetaM ObjExpr
  | .mdata _ e => reflectLFQuoteExpr theoryName locals e
  | .const n _ => do
      match lfQuoteSourceNameOfConst? theoryName n with
      | some localName => pure (.ident localName)
      | none => throwError "Lean-elaborated LF term uses non-LF constant '{n}'. Only generated \
          stubs in namespace '{lfQuoteNamespace theoryName}' are accepted by this prototype."
  | .fvar fvarId => do
      match findLFQuoteLocal? locals fvarId with
      | some localName => pure (.ident localName)
      | none => throwError "Lean-elaborated LF term uses local variable '{mkFVar fvarId}' that \
          was not introduced by the InternalLean declaration frontend"
  | .app f a => do
      pure (.app (← reflectLFQuoteExpr theoryName locals f)
        (← reflectLFQuoteExpr theoryName locals a))
  | e@(.lam ..) => do
      lambdaTelescope e fun xs body => do
        let mut locals := locals
        let mut names := #[]
        for x in xs do
          let localDecl ← x.fvarId!.getDecl
          let userName := localDecl.userName.eraseMacroScopes
          locals := locals.push (x.fvarId!, userName)
          names := names.push userName
        pure (.lam names (← reflectLFQuoteExpr theoryName locals body))
  | .mvar _ => do
      -- Lean metavariables introduced for omitted implicit quote-stub arguments are reflected as
      -- ordinary InternalLean placeholders.  InternalLean's own implicit-argument elaboration and
      -- final LF checking remain responsible for accepting or rejecting them.
      pure (.ident `_)
  | e => throwError "unsupported Lean-elaborated LF expression after elaboration:\n  {e}"

/-- Elaborate `body` as a quoted LF term and reflect it to `ObjExpr`. -/
def elabLeanQuotedLFBody (target : InternalDefTarget) (params : Array HLBinding)
    (typeExpr : ObjExpr) (body : TSyntax `term) : CommandElabM ObjExpr := do
  let quoteNs := mkIdent (lfQuoteNamespace target.theoryName)
  let quoteOpenDecl ← `(Lean.Parser.Command.openDecl| $quoteNs:ident)
  let body ← `(term| open $quoteOpenDecl in $body)
  liftTermElabM do
    let expectedType := lfQuoteLeanTypeOfObjType typeExpr
    let rec withLocals (i : Nat) (locals : LFQuoteLocalMap) : TermElabM ObjExpr := do
      if h : i < params.size then
        let p := params[i]
        withLocalDecl p.name.eraseMacroScopes (lfQuoteBinderInfoOfVisibility p.visibility)
            (lfQuoteLeanTypeOfBinding p) fun fvar =>
          withLocals (i + 1) (locals.push (fvar.fvarId!, p.name.eraseMacroScopes))
      else
        let value ← Term.elabTerm body (some expectedType)
        Term.synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        reflectLFQuoteExpr target.theoryName locals value
    withLocals 0 #[]

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
      pure (mkApp (← lfMirrorExpr theoryName locals f) (← lfMirrorExpr theoryName locals a))
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
  | e => lfMirrorExpr theoryName locals e

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

/-- Add one experimental Lean mirror axiom if it is not already present. -/
def addLFMirrorAxiomIfMissing (declName : Name) (type : Expr) : CommandElabM Unit := do
  unless (← getEnv).contains declName do
    liftCoreM do
      addAndCompile (Declaration.axiomDecl {
        name := declName
        levelParams := []
        type := type
        isUnsafe := false })

/-- Ensure that experimental Lean mirror declarations exist for the currently checked signature. -/
def ensureLFMirrorForTheory (theoryName : Name) : CommandElabM Unit := do
  let some checkedHL ← liftCoreM <| getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  for d in checkedHL.syntaxSorts do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.syntaxDefs do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.judgments do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.params
      (fun _ => pure (mkSort (Level.succ .zero)))
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
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
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type
  for d in checkedHL.lfJudgmentTheorems do
    let type ← liftTermElabM <| lfMirrorForallType theoryName d.binders
      (fun locals => lfMirrorExpr theoryName locals d.judgmentExpr)
    addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) type

/-- Check one LF value against an LF type using the experimental Lean mirror backend. -/
def checkWithLFMirror (theoryName : Name) (typeExpr valueExpr : ObjExpr) : CommandElabM Unit := do
  ensureLFMirrorForTheory theoryName
  liftTermElabM do
    let typeLean ← lfMirrorExpr theoryName {} typeExpr
    let valueLean ← lfMirrorTermWithExpected theoryName {} typeExpr valueExpr
    let actual ← inferType valueLean
    unless ← isDefEq actual typeLean do
      let msg :=
        m!"Lean mirror checker inferred\n  {actual}\nfor translated value, expected\n  {typeLean}"
      throwError msg

syntax (name := checkLFMirror)
  "#check_lf_mirror " ident " : " ttExpr " := " ttExpr : command

elab_rules : command
  | `(#check_lf_mirror $theory:ident : $typeStx:ttExpr := $valueStx:ttExpr) => do
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror theory.getId typeExpr valueExpr
      logInfo m!"Lean mirror checker accepted term in type theory '{theory.getId}'"

syntax (name := internalMirrorDef)
  docComment ? "internal_mirror " "def " ident " : " ttExpr " := " ttExpr : command

elab_rules (kind := internalMirrorDef) : command
  | `($[$doc?:docComment]? internal_mirror def $declName:ident : $typeStx:ttExpr :=
      $valueStx:ttExpr) => do
      let target ← resolveInternalDefTarget declName.getId
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabObjExpr valueStx
      checkWithLFMirror target.theoryName typeExpr valueExpr
      elabInternalDefCheckedExpr doc? declName declName.getId #[] typeExpr valueExpr
      addInternalDefExprNavigationInfo declName.getId #[] typeStx valueStx

/-- Render one generated quote-stub summary line. -/
def lfQuoteStubSummaryLine (theoryName : Name) (role : String) (sourceName : Name)
    (params : Array HLBinding) : String :=
  s!"{role} {sourceName.eraseMacroScopes} -> {lfQuoteDeclName theoryName sourceName} / \
    {params.size} parameter(s)"

syntax (name := printLFQuoteStubs) "#print_lf_quote_stubs " ident : command

elab_rules : command
  | `(#print_lf_quote_stubs $theory:ident) => do
      let some checkedHL ← liftCoreM <| getCheckedHLSignature? theory.getId
        | throwError "no checked high-level signature stored for type theory '{theory.getId}'"
      let mut lines := #[s!"quoted LF stubs for {theory.getId.eraseMacroScopes}:"]
      for d in checkedHL.syntaxSorts do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "syntax_sort" d.name d.params)
      for d in checkedHL.syntaxAbbrevs do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "syntax_abbrev" d.name d.params)
      for d in checkedHL.syntaxDefs do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "syntax_def" d.name d.params)
      for d in checkedHL.judgmentAbbrevs do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "judgment_abbrev" d.name
          d.params)
      for d in checkedHL.judgments do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "judgment" d.name d.params)
      for d in checkedHL.rules do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "rule" d.name
          (lfQuoteParamsOfRule d))
      for d in checkedHL.lfOpaqueConsts do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "lf_opaque" d.name
          (lfQuoteParamsOfLFOpaqueConst d))
      for d in checkedHL.lfObjectDefs do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "lf_def" d.name #[])
      for d in checkedHL.lfJudgmentTheorems do
        lines := lines.push (lfQuoteStubSummaryLine theory.getId "judgment_theorem" d.name
          d.binders)
      logInfo m!"{String.intercalate "\n" lines.toList}"

syntax (name := internalLeanQuotedDef)
  docComment ? "internal_lean " "def " ident " : " ttExpr " := " term : command
syntax (name := internalLeanQuotedDefBinder)
  docComment ? "internal_lean " "def " ident ttBinder+ " : " ttExpr " := " term : command
syntax (name := internalLeanQuotedDefSorry)
  docComment ? "internal_lean " "def " ident " : " ttExpr " := " "sorry" : command
syntax (name := internalLeanQuotedDefBinderSorry)
  docComment ? "internal_lean " "def " ident ttBinder+ " : " ttExpr " := " "sorry" : command

elab_rules (kind := internalLeanQuotedDefSorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalDefSorry doc? declName declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedDefBinderSorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      elabInternalDefSorryWithBinders doc? declName declName.getId #[] binders typeStx

elab_rules (kind := internalLeanQuotedDef) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident : $typeStx:ttExpr :=
      $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabLeanQuotedLFBody target #[] typeExpr body
      elabInternalDefCheckedExpr doc? declName declName.getId #[] typeExpr valueExpr
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedDefBinder) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let params ← binders.mapM elabHLBinding
      let typeExpr ← elabObjExpr typeStx
      let valueExpr ← elabLeanQuotedLFBody target params typeExpr body
      elabInternalDefCheckedWithBindersExpr doc? declName declName.getId #[] params typeExpr
        valueExpr
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx

end InternalLean
