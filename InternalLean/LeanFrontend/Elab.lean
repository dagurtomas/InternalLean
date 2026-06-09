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
syntax (name := internalLeanQuotedDefBySorry)
  docComment ? "internal_lean " "def " ident " : " ttExpr " := " "by" ppLine "sorry" : command
syntax (name := internalLeanQuotedDefBinderBySorry)
  docComment ? "internal_lean " "def " ident ttBinder+ " : " ttExpr " := " "by" ppLine
    "sorry" : command

elab_rules (kind := internalLeanQuotedDefSorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalDefSorry doc? declName declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedDefBinderSorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      elabInternalDefSorryWithBinders doc? declName declName.getId #[] binders typeStx

elab_rules (kind := internalLeanQuotedDefBySorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident : $typeStx:ttExpr := by
      sorry) =>
      elabInternalDefSorry doc? declName declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedDefBinderBySorry) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := by
      sorry) =>
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
