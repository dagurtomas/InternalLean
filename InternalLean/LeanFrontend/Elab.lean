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

register_option internalLean.preferLeanQuotedFrontend : Bool := {
  defValue := true
  descr := "legacy compatibility option; canonical `internal def` and theorem term bodies use \
    the Lean-quoted frontend. Use `internal_raw` for the raw InternalLean body grammar."
}

register_option internalLean.preferLeanQuotedTheoryBlocks : Bool := {
  defValue := true
  descr := "try the Lean-quoted frontend for `declare_type_theory` and `extend_type_theory` \
    expression fields before falling back to the raw InternalLean frontend"
}

register_option internalLean.requireLeanQuotedTheoryBlocks : Bool := {
  defValue := false
  descr := "require the Lean-quoted frontend for `declare_type_theory` and \
    `extend_type_theory` expression fields instead of falling back to the raw frontend"
}

register_option internalLean.frontend.logFallbacks : Bool := {
  defValue := false
  descr := "log warnings when the Lean-quoted frontend falls back to the legacy InternalLean \
    parser/checking path"
}

register_option internalLean.frontend.compareLegacy : Bool := {
  defValue := false
  descr := "for canonical internal def/theorem bodies accepted by the Lean-quoted frontend, also \
    elaborate the legacy body and error if the reflected LF bodies differ"
}

/-- One recorded fallback/skip in the Lean-quoted frontend. -/
structure InternalFrontendFallbackEntry where
  /-- Source file that recorded this entry. -/
  fileName : String := ""
  /-- Stable command/fallback class. -/
  kind : Name
  /-- Human-readable source position when available. -/
  position? : Option String := none
  /-- Exception or skip message recorded at the fallback boundary. -/
  message : String := ""
  deriving Inhabited, Repr, BEq

/-- Fallback profile state that survives command-elaborator fallthrough and state restoration. -/
initialize internalFrontendFallbackStore : IO.Ref (Array InternalFrontendFallbackEntry) ←
  IO.mkRef #[]

/-- Render a source position for a fallback diagnostic. -/
def frontendFallbackPositionString? (stx : Syntax) : CommandElabM (Option String) := do
  match stx.getPos? (canonicalOnly := true) with
  | none => pure none
  | some pos =>
      let p := (← getFileMap).toPosition pos
      pure <| some s!"line {p.line}, column {p.column}"

/-- Whether fallback warnings are enabled. -/
def logInternalFrontendFallbacks : CommandElabM Bool :=
  getBoolOption `internalLean.frontend.logFallbacks

/-- Whether canonical internal declarations should compare with the legacy frontend. -/
def compareLeanQuotedWithLegacyFrontend : CommandElabM Bool :=
  getBoolOption `internalLean.frontend.compareLegacy

/-- Record one Lean-quoted frontend fallback or compare-mode skip. -/
def recordInternalFrontendFallback (kind : Name) (stx : Syntax) (message : MessageData) :
    CommandElabM Unit := do
  let fileName ← getFileName
  let position? ← frontendFallbackPositionString? stx
  let text ← message.toString
  liftIO <| internalFrontendFallbackStore.modify fun entries => entries.push {
    fileName := fileName
    kind := kind.eraseMacroScopes
    position?
    message := text }
  if ← logInternalFrontendFallbacks then
    let positionText := position?.getD "at unknown position"
    withRef stx <| logWarning m!"Lean-quoted frontend fallback [{kind.eraseMacroScopes}] \
      {positionText}: {message}"

/-- Record one caught exception before falling back from the Lean-quoted frontend. -/
def recordInternalFrontendFallbackException (kind : Name) (stx : Syntax) (ex : Exception) :
    CommandElabM Unit :=
  recordInternalFrontendFallback kind stx ex.toMessageData

/-- Remove duplicate fallback entries, useful across editor re-elaborations. -/
def dedupeInternalFrontendFallbackEntries (entries : Array InternalFrontendFallbackEntry) :
    Array InternalFrontendFallbackEntry := Id.run do
  let mut out := #[]
  for entry in entries do
    unless out.contains entry do
      out := out.push entry
  return out

/-- Read fallback entries recorded for the current source file. -/
def currentFileInternalFrontendFallbackEntries : CommandElabM
    (Array InternalFrontendFallbackEntry) := do
  let fileName ← getFileName
  let entries ← liftIO internalFrontendFallbackStore.get
  pure <| dedupeInternalFrontendFallbackEntries <|
    entries.filter fun entry => entry.fileName == fileName

/-- Summarize current-file fallback counters. -/
def internalFrontendFallbackProfileString (entries : Array InternalFrontendFallbackEntry) :
    String := Id.run do
  let mut kinds : Array Name := #[]
  let mut counts : NameMap Nat := {}
  for entry in entries do
    let kind := entry.kind.eraseMacroScopes
    if (counts.find? kind).isNone then
      kinds := kinds.push kind
    counts := counts.insert kind ((counts.find? kind).getD 0 + 1)
  let mut lines := #["internal frontend fallback profile for current file:"]
  if kinds.isEmpty then
    lines := lines.push "  no fallbacks"
  else
    for kind in kinds do
      lines := lines.push s!"  {kind}: {(counts.find? kind).getD 0}"
  String.intercalate "\n" lines.toList

/-- Print the current file's Lean-quoted frontend fallback counters. -/
elab "#print_internal_frontend_fallback_profile" : command => do
  let profile := internalFrontendFallbackProfileString
    (← currentFileInternalFrontendFallbackEntries)
  logInfo m!"{profile}"

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

/-- Cached quoted-frontend metadata for one LF signature. -/
structure LFQuoteSignatureContext where
  /-- Source LF head arities keyed by erased local source name. -/
  sourceArities : NameMap Nat := {}

/-- Insert an arity in quoted-frontend source lookup metadata. -/
def insertLFQuoteSourceArity (arities : NameMap Nat) (name : Name) (arity : Nat) :
    NameMap Nat :=
  arities.insert name.eraseMacroScopes arity

/-- Count explicit source arguments encoded by a function-shaped LF object definition type. -/
partial def lfQuoteSourceArityOfLFObjectDefType : ObjExpr → Nat
  | .arrow _ _ body | .funArrow _ _ body => 1 + lfQuoteSourceArityOfLFObjectDefType body
  | _ => 0

/-- Build the quoted-frontend source-arity map once for a signature. -/
def mkLFQuoteSourceArityMap (sig : HLSignature) : NameMap Nat := Id.run do
  let mut arities : NameMap Nat := {}
  for d in sig.syntaxSorts do
    arities := insertLFQuoteSourceArity arities d.name d.params.size
  for d in sig.syntaxAbbrevs do
    arities := insertLFQuoteSourceArity arities d.name d.params.size
  for d in sig.syntaxDefs do
    arities := insertLFQuoteSourceArity arities d.name d.params.size
  for d in sig.judgmentAbbrevs do
    arities := insertLFQuoteSourceArity arities d.name d.params.size
  for d in sig.judgments do
    arities := insertLFQuoteSourceArity arities d.name d.params.size
  for d in sig.rules do
    arities := insertLFQuoteSourceArity arities d.name (lfQuoteParamsOfRule d).size
  for d in sig.lfOpaqueConsts do
    arities := insertLFQuoteSourceArity arities d.name (lfQuoteParamsOfLFOpaqueConst d).size
  for d in sig.lfObjectDefs do
    arities := insertLFQuoteSourceArity arities d.name
      (lfQuoteSourceArityOfLFObjectDefType d.typeExpr)
  for d in sig.lfJudgmentTheorems do
    arities := insertLFQuoteSourceArity arities d.name d.binders.size
  return arities

/-- Build quoted-frontend lookup metadata once for a signature. -/
def mkLFQuoteSignatureContext (sig : HLSignature) : LFQuoteSignatureContext :=
  { sourceArities := mkLFQuoteSourceArityMap sig }

/-- Number of source LF parameters expected by a quoted declaration head. -/
def lfQuoteSourceArityIn? (ctx : LFQuoteSignatureContext) (sourceName : Name) : Option Nat :=
  ctx.sourceArities.find? sourceName.eraseMacroScopes

/-- Resolve a Lean constant against quoted-frontend lookup metadata. -/
def lfQuoteSourceNameAndArityOfConstInContext? (theoryName : Name)
    (ctx : LFQuoteSignatureContext) (constName : Name) : Option (Name × Nat × Bool) :=
  if let some localName := lfQuoteSourceNameOfConst? theoryName constName then
    some (localName, (lfQuoteSourceArityIn? ctx localName).getD 0, false)
  else if constName.isAnonymous then
    none
  else
    let candidate := Name.mkSimple constName.getString!
    match lfQuoteSourceArityIn? ctx candidate with
    | some arity => some (candidate, arity, true)
    | none => none

/-- Resolve a Lean constant through supplied quoted-frontend lookup metadata. -/
def lfQuoteSourceNameAndArityOfConstFrom? (theoryName : Name)
    (ctx? : Option LFQuoteSignatureContext) (constName : Name) : Option (Name × Nat × Bool) :=
  match ctx? with
  | some ctx => lfQuoteSourceNameAndArityOfConstInContext? theoryName ctx constName
  | none => none

/-- Drop Lean-only arguments from a fallback application that resolved to an LF head. -/
def lfQuoteArgsForSourceArity (constName : Name) (arity : Nat) (args : Array Expr) : Array Expr :=
  let args :=
    if constName == ``id && 0 < args.size then
      args.extract 1 args.size
    else
      args
  if arity < args.size then
    args.extract (args.size - arity) args.size
  else
    args

/-- Return whether a Lean name is a simple source identifier. -/
def isSimpleLFQuoteSourceName : Name → Bool
  | .str .anonymous _ => true
  | _ => false

/-- Collect binder names from a Lean `fun` binder list. -/
partial def collectLFQuoteFunBinderNames (stx : Syntax) (acc : NameSet) : NameSet :=
  match stx with
  | stx@(.ident ..) => acc.insert stx.getId.eraseMacroScopes
  | .node _ `Lean.Parser.Term.typeAscription args =>
      match args[1]? with
      | some stx =>
          match stx with
          | .ident .. => acc.insert stx.getId.eraseMacroScopes
          | _ => acc
      | none => acc
  | .node _ _ args => args.foldl (fun acc arg => collectLFQuoteFunBinderNames arg acc) acc
  | _ => acc

/-- Collect simple Lean lambda-binder names that should not be rewritten as LF globals. -/
partial def collectLFQuoteBinderNames (stx : Syntax) (acc : NameSet := {}) : NameSet :=
  match stx with
  | .node _ `Lean.Parser.Term.basicFun args =>
      let acc :=
        match args[0]? with
        | some binders => collectLFQuoteFunBinderNames binders acc
        | none => acc
      match args[3]? with
      | some body => collectLFQuoteBinderNames body acc
      | none => acc
  | .node _ _ args => args.foldl (fun acc arg => collectLFQuoteBinderNames arg acc) acc
  | _ => acc

/-- Qualify simple LF head identifiers so Lean resolution prefers the current theory. -/
partial def qualifyLFQuoteSourceIdents (theoryName : Name) (sig : HLSignature)
    (protectedNames : NameSet) : Syntax → Syntax
  | stx@(.ident ..) =>
      let n := stx.getId.eraseMacroScopes
      if isSimpleLFQuoteSourceName n && !protectedNames.contains n && sig.containsName n then
        mkIdentFrom stx (lfQuoteDeclName theoryName n)
      else
        stx
  | .node info kind args =>
      .node info kind (args.map (qualifyLFQuoteSourceIdents theoryName sig protectedNames))
  | stx => stx

mutual

/-- Reflect a unary binder argument to a quoted LF structural constructor. -/
partial def reflectLFQuoteUnaryBinder (theoryName : Name) (ctx? : Option LFQuoteSignatureContext)
    (locals : LFQuoteLocalMap) (e : Expr) : MetaM (Name × ObjExpr) := do
  lambdaTelescope e fun xs body => do
    unless xs.size == 1 do
      throwError "quoted LF structural binder expected one Lean binder, but elaborated to \
        {xs.size} binder(s)"
    let x := xs[0]!
    let localDecl ← x.fvarId!.getDecl
    let userName := localDecl.userName.eraseMacroScopes
    let locals := locals.push (x.fvarId!, userName)
    pure (userName, ← reflectLFQuoteExprWithSignature theoryName ctx? locals body)

/-- Reflect an application of one built-in quoted LF structural constructor, if present. -/
partial def reflectLFQuoteBuiltinApp? (theoryName : Name) (ctx? : Option LFQuoteSignatureContext)
    (locals : LFQuoteLocalMap) (constName : Name) (args : Array Expr) :
    MetaM (Option ObjExpr) := do
  let explicitArgs (expected : Nat) : Array Expr :=
    if expected <= args.size then args.extract (args.size - expected) args.size else args
  let binary (ctor : ObjExpr → ObjExpr → ObjExpr) : MetaM (Option ObjExpr) := do
    let args := explicitArgs 2
    unless args.size == 2 do
      throwError "quoted LF constructor '{constName}' expected 2 explicit argument(s), got \
        {args.size}"
    pure <| some <| ctor (← reflectLFQuoteExprWithSignature theoryName ctx? locals args[0]!)
      (← reflectLFQuoteExprWithSignature theoryName ctx? locals args[1]!)
  let dependent (ctor : Option Name → ObjExpr → ObjExpr → ObjExpr) :
      MetaM (Option ObjExpr) := do
    let args := explicitArgs 2
    unless args.size == 2 do
      throwError "quoted LF constructor '{constName}' expected 2 explicit argument(s), got \
        {args.size}"
    let domain ← reflectLFQuoteExprWithSignature theoryName ctx? locals args[0]!
    let (binderName, codomain) ← reflectLFQuoteUnaryBinder theoryName ctx? locals args[1]!
    pure <| some <| ctor (some binderName) domain codomain
  let unary (ctor : ObjExpr → ObjExpr) : MetaM (Option ObjExpr) := do
    let args := explicitArgs 1
    unless args.size == 1 do
      throwError "quoted LF constructor '{constName}' expected 1 explicit argument(s), got \
        {args.size}"
    pure <| some <| ctor (← reflectLFQuoteExprWithSignature theoryName ctx? locals args[0]!)
  if constName == ``InternalLean.LFQuote.arrow then
    binary (fun A B => .arrow none A B)
  else if constName == ``InternalLean.LFQuote.arrowDep then
    dependent (fun x A B => .arrow x A B)
  else if constName == ``InternalLean.LFQuote.funArrow then
    binary (fun A B => .funArrow none A B)
  else if constName == ``InternalLean.LFQuote.funArrowDep then
    dependent (fun x A B => .funArrow x A B)
  else if constName == ``InternalLean.LFQuote.prod then
    binary (fun A B => .sigma none A B)
  else if constName == ``InternalLean.LFQuote.jeq then
    binary (fun lhs rhs => .jeq lhs rhs)
  else if constName == ``InternalLean.LFQuote.sigma then
    dependent (fun x A B => .sigma x A B)
  else if constName == ``InternalLean.LFQuote.pair then
    binary (fun a b => .pair a b)
  else if constName == ``InternalLean.LFQuote.projFst then
    unary (fun e => .fst e)
  else if constName == ``InternalLean.LFQuote.projSnd then
    unary (fun e => .snd e)
  else
    pure none

/-- Reflect one Lean expression elaborated against quoted-LF stubs back to an `ObjExpr`. -/
partial def reflectLFQuoteExprWithSignature (theoryName : Name)
    (ctx? : Option LFQuoteSignatureContext) (locals : LFQuoteLocalMap) :
    Expr → MetaM ObjExpr
  | .mdata _ e => reflectLFQuoteExprWithSignature theoryName ctx? locals e
  | e@(.app ..) => do
      match e.getAppFn with
      | .const n _ =>
          match ← reflectLFQuoteBuiltinApp? theoryName ctx? locals n e.getAppArgs with
          | some out => pure out
          | none =>
              match lfQuoteSourceNameAndArityOfConstFrom? theoryName ctx? n with
              | some (localName, arity, _) =>
                  let args := lfQuoteArgsForSourceArity n arity e.getAppArgs
                  let mut out : ObjExpr := .ident localName
                  for arg in args do
                    out := .app out
                      (← reflectLFQuoteExprWithSignature theoryName ctx? locals arg)
                  pure out
              | none =>
                  pure (.app (← reflectLFQuoteExprWithSignature theoryName ctx? locals e.appFn!)
                    (← reflectLFQuoteExprWithSignature theoryName ctx? locals e.appArg!))
      | _ =>
          pure (.app (← reflectLFQuoteExprWithSignature theoryName ctx? locals e.appFn!)
            (← reflectLFQuoteExprWithSignature theoryName ctx? locals e.appArg!))
  | .const n _ => do
      if n == ``InternalLean.LFQuote.sort then
        pure .sort
      else
        match lfQuoteSourceNameAndArityOfConstFrom? theoryName ctx? n with
        | some (localName, _, _) =>
            pure (.ident localName)
        | none =>
            if n.eraseMacroScopes == `sorryAx then
              throwError "Lean-elaborated LF term uses Lean `sorry`. Lean `sorry` cannot become \
                a checked internal proof; use `:= sorry` for an explicit InternalLean admission."
            else
              throwError "Lean-elaborated LF term uses Lean constant '{n}', which is not part \
                of the quoted LF signature for type theory '{theoryName}'. Use a generated \
                  declaration in namespace '{lfQuoteNamespace theoryName}', or an LF declaration \
                    name available in the checked theory."
  | .fvar fvarId => do
      match findLFQuoteLocal? locals fvarId with
      | some localName => pure (.ident localName)
      | none => throwError "Lean-elaborated LF term uses local variable '{mkFVar fvarId}' that \
          was not introduced by the InternalLean declaration frontend"
  | e@(.lam ..) => do
      lambdaTelescope e fun xs body => do
        let mut locals := locals
        let mut names := #[]
        for x in xs do
          let localDecl ← x.fvarId!.getDecl
          let userName := localDecl.userName.eraseMacroScopes
          locals := locals.push (x.fvarId!, userName)
          names := names.push userName
        pure (.lam names (← reflectLFQuoteExprWithSignature theoryName ctx? locals body))
  | .mvar _ => do
      -- Lean metavariables introduced for omitted implicit quote-stub arguments are reflected as
      -- ordinary InternalLean placeholders.  InternalLean's own implicit-argument elaboration and
      -- final LF checking remain responsible for accepting or rejecting them.
      pure (.ident `_)
  | e => throwError "unsupported Lean-elaborated LF expression after elaboration:\n  {e}"

end

/-- Reflect one Lean expression through the checked registry for its theory. -/
def reflectLFQuoteExpr (theoryName : Name) (locals : LFQuoteLocalMap) (e : Expr) :
    MetaM ObjExpr := do
  let ctx? := (← getCheckedHLSignature? theoryName).map mkLFQuoteSignatureContext
  reflectLFQuoteExprWithSignature theoryName ctx? locals e

/-- Elaborate `body` as a quoted LF term and reflect it to `ObjExpr`. -/
def elabLeanQuotedLFBody (target : InternalDefTarget) (params : Array HLBinding)
    (typeExpr : ObjExpr) (body : TSyntax `term) : CommandElabM ObjExpr := do
  let builtinQuoteOpenDecl ← `(Lean.Parser.Command.openDecl| InternalLean.LFQuote)
  let quoteNs := mkIdent (lfQuoteNamespace target.theoryName)
  let quoteOpenDecl ← `(Lean.Parser.Command.openDecl| $quoteNs:ident)
  let protectedNames := params.foldl (init := collectLFQuoteBinderNames body.raw) fun names p =>
    names.insert p.name.eraseMacroScopes
  let body :=
    match ← liftCoreM <| getCheckedHLSignature? target.theoryName with
    | some sig => qualifyLFQuoteSourceIdents target.theoryName sig protectedNames body
    | none => body.raw
  let body ← `(term| open $builtinQuoteOpenDecl in open $quoteOpenDecl in $(⟨body⟩):term)
  liftTermElabM do
    let rec withLocals (i : Nat) (locals : LFQuoteLocalMap)
        (typeLocals : LFQuoteLeanLocalMap) (untypedLocals : NameSet) : TermElabM ObjExpr := do
      if h : i < params.size then
        let p := params[i]
        let env ← getEnv
        let pName := p.name.eraseMacroScopes
        let pSupported := lfQuoteSupportsIndexedQuoteType env target.theoryName
          (lfQuoteLeanLocalNames typeLocals) untypedLocals p.typeExpr
        let binderType := lfQuoteLeanTypeOfBinding env target.theoryName typeLocals untypedLocals p
        let untypedLocals := if pSupported then untypedLocals else untypedLocals.insert pName
        withLocalDecl pName (lfQuoteBinderInfoOfVisibility p.visibility) binderType fun fvar =>
          withLocals (i + 1) (locals.push (fvar.fvarId!, pName))
            (typeLocals.push (pName, fvar)) untypedLocals
      else
        let expectedType :=
          lfQuoteLeanTypeOfObjType (← getEnv) target.theoryName typeLocals untypedLocals typeExpr
        let value ← withEnableInfoTree false do
          let value ← withoutErrToSorry <| Term.elabTerm body (some expectedType)
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars value
        reflectLFQuoteExpr target.theoryName locals value
    withLocals 0 #[] #[] {}

/-- Collect names from the binder-pattern side of a Lean typed `fun` binder. -/
partial def collectLFQuoteFunBinderPatternNames (stx : Syntax) (acc : Array Name := #[]) :
    Array Name :=
  match stx with
  | stx@(.ident ..) => acc.push stx.getId.eraseMacroScopes
  | .node _ _ args => args.foldl (fun acc arg => collectLFQuoteFunBinderPatternNames arg acc) acc
  | _ => acc

/-- Collect the source names from a Lean `fun` binder list, preserving order. -/
partial def collectLFQuoteFunBinderNamesOrdered (stx : Syntax) (acc : Array Name := #[]) :
    Array Name :=
  match stx with
  | stx@(.ident ..) => acc.push stx.getId.eraseMacroScopes
  | .node _ `Lean.Parser.Term.typeAscription args =>
      match args[1]? with
      | some pattern => collectLFQuoteFunBinderPatternNames pattern acc
      | none => acc
  | .node _ _ args => args.foldl (fun acc arg => collectLFQuoteFunBinderNamesOrdered arg acc) acc
  | _ => acc

/-- If `stx` is a Lean `fun`, return its binder names and body syntax. -/
partial def leanQuotedFunView? (stx : Syntax) : Option (Array Name × Syntax) :=
  match stx with
  | .node _ `Lean.Parser.Term.fun args =>
      match args[1]? with
      | some body => leanQuotedFunView? body
      | none => none
  | .node _ `Lean.Parser.Term.basicFun args => do
      let binders ← args[0]?
      let body ← args[3]?
      some (collectLFQuoteFunBinderNamesOrdered binders, body)
  | _ => none

/-- Save one Lean infoview goal marker over a quoted-LF body syntax node. -/
def saveLeanQuotedLFGoalInfo (target : InternalDefTarget) (goal : InternalObjectGoal)
    (stx : Syntax) : CommandElabM Unit := do
  let snapshot ← liftTermElabM do
    let displayGoal := mkInternalGoalDisplayGoal goal.ctx goal.target
    let snapshot ← mkInternalObjectGoalDisplaySnapshot target #[displayGoal]
    pushInfoLeaf <| .ofTacticInfo {
      elaborator := `InternalLean.leanQuotedLFBodyInfo
      stx := mkNullNode #[stx]
      mctxBefore := snapshot.mctx
      goalsBefore := snapshot.goals
      mctxAfter := snapshot.mctx
      goalsAfter := snapshot.goals }
    pure snapshot
  recordInternalGoalDisplayFallbacks stx snapshot.fallbacks

/-- Collect direct tactic syntax nodes from a Lean tactic sequence. -/
partial def collectLeanQuotedTacticSteps (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ `Lean.Parser.Term.byTactic args =>
      match args[1]? with
      | some seq => collectLeanQuotedTacticSteps seq
      | none => #[]
  | .node _ `Lean.Parser.Tactic.tacticSeq args =>
      args.foldl (fun acc arg => acc ++ collectLeanQuotedTacticSteps arg) #[]
  | .node _ `Lean.Parser.Tactic.tacticSeq1Indented args =>
      args.foldl (fun acc arg =>
        if arg.isMissing then acc
        else if arg.isOfKind nullKind then acc ++ collectLeanQuotedTacticSteps arg
        else acc.push arg) #[]
  | .node _ `Lean.Parser.Tactic.tacticSeqBracketed args =>
      args.foldl (fun acc arg => acc ++ collectLeanQuotedTacticSteps arg) #[]
  | .node _ k args =>
      if k == nullKind then
        args.foldl (fun acc arg =>
          if arg.isMissing then acc
          else if arg.isOfKind nullKind then acc ++ collectLeanQuotedTacticSteps arg
          else acc.push arg) #[]
      else
        #[]
  | _ => #[]

/-- Return the first identifier contained in a Lean tactic syntax node. -/
def firstLeanQuotedTacticIdent? (stx : Syntax) : Option Name := Id.run do
  for identStx in collectInternalIdentSyntaxes stx do
    if let some n := internalSyntaxIdentName? identStx then
      return some n
  return none

/-- Return every identifier contained in a Lean tactic syntax node. -/
def leanQuotedTacticIdents (stx : Syntax) : Array Name := Id.run do
  let mut out := #[]
  for identStx in collectInternalIdentSyntaxes stx do
    if let some n := internalSyntaxIdentName? identStx then
      out := out.push n
  return out

/-- Diagnostic subgoals for Lean's ordinary `apply` over quote stubs.

Unlike object tactic `apply`, Lean only sees explicit arguments to `LFQuoteTerm` stubs, so explicit
source parameters become visible Lean subgoals even when the LF conclusion would determine them. -/
def leanQuotedApplyDiagnosticSubgoals (target : InternalDefTarget) (sig : HLSignature)
    (goal : InternalObjectGoal) (rawName : Name) : Except String (Array InternalObjectGoal) := do
  let (_, innerGoal) := autoIntroGoal goal
  let some cand := findInternalApplyCandidate? target sig rawName
    | throw s!"quoted LF `apply {rawName}` failed: unknown rule or internal declaration"
  let some subst0 := matchInternalCandidateConclusion? sig innerGoal.ctx cand.params
      cand.conclusionExpr innerGoal.target
    | throw s!"quoted LF `apply {rawName}` failed: conclusion does not match current goal"
  let mut subst := subst0
  let mut newGoals : Array InternalObjectGoal := #[]
  for param in cand.params do
    let key := param.name.eraseMacroScopes
    let paramTy := substObjectVars subst param.typeExpr
    if param.visibility == .explicit then
      newGoals := newGoals.push { ctx := innerGoal.ctx, target := paramTy }
      subst := subst.insert key (internalObjectGoalPlaceholder param.name)
    else if (subst.find? key).isNone then
      subst := subst.insert key (internalObjectGoalPlaceholder param.name)
  for premiseTarget in cand.subgoalTargets do
    newGoals := newGoals.push {
      ctx := innerGoal.ctx
      target := substObjectVars subst premiseTarget }
  pure newGoals

/-- Simulate one Lean tactic step as object-goal metadata for quoted-LF bodies. -/
def stepLeanQuotedTacticInfoState (target : InternalDefTarget) (sig : HLSignature)
    (goals : Array InternalObjectGoal) (stx : Syntax) :
    Except String (Array InternalObjectGoal) := do
  let some goal := goals[0]?
    | throw "no remaining object goals"
  let rest := goals.extract 1 goals.size
  if stx.isOfKind `Lean.Parser.Tactic.exact then
    pure rest
  else if stx.isOfKind `Lean.Parser.Tactic.apply then
    let some rawName := firstLeanQuotedTacticIdent? stx
      | throw "quoted LF `apply` tactic has no identifier head"
    let subgoals ← leanQuotedApplyDiagnosticSubgoals target sig goal rawName
    pure (subgoals ++ rest)
  else if stx.isOfKind `Lean.Parser.Tactic.intro then
    let mut goal := goal
    for n in leanQuotedTacticIdents stx do
      goal ← introObjectGoal goal n
    pure (#[goal] ++ rest)
  else if stx.isOfKind `Lean.Parser.Tactic.assumption then
    let (_, innerGoal) := autoIntroGoal goal
    let some _ := findAssumption? sig #[] innerGoal.ctx innerGoal.target
      | throw "quoted LF `assumption` tactic failed"
    pure rest
  else
    pure goals

/-- Build per-tactic LF goal snapshots for a Lean `by` proof in the quoted frontend. -/
def collectLeanQuotedByTacticInfo (target : InternalDefTarget) (sig : HLSignature)
    (goal : InternalObjectGoal) (stx : Syntax) : Array InternalObjectTacticInfo := Id.run do
  let mut goals := #[goal]
  let mut infos := #[]
  for stepStx in collectLeanQuotedTacticSteps stx do
    let before := goals
    let (after, stale) :=
      match stepLeanQuotedTacticInfoState target sig goals stepStx with
      | .ok goals => (goals, false)
      | .error _ => (goals, true)
    infos := infos.push {
      stx := stepStx
      goalsBefore := before
      goalsAfter := after
      goalsAfterStale := stale }
    goals := after
  return infos

/-- Follow leading Lean lambdas so the infoview inside the body shows LF locals. -/
partial def saveLeanQuotedLFBodyGoalInfo (target : InternalDefTarget) (flatSig : HLSignature)
    (goal : InternalObjectGoal) (stx : Syntax) : CommandElabM Unit := do
  match leanQuotedFunView? stx with
  | some (names, bodyStx) =>
      let mut goal := goal
      let mut ok := true
      for n in names do
        match introObjectGoal goal n with
        | .ok next => goal := next
        | .error _ => ok := false
      if ok then
        saveLeanQuotedLFBodyGoalInfo target flatSig goal bodyStx
      else
        saveLeanQuotedLFGoalInfo target goal stx
        saveInternalObjectHoverInfo target flatSig {
          stx := stx
          goalsBefore := #[goal]
          goalsAfter := #[goal] }
  | none =>
      let byInfos := collectLeanQuotedByTacticInfo target flatSig goal stx
      if byInfos.isEmpty then
        saveLeanQuotedLFGoalInfo target goal stx
        saveInternalObjectHoverInfo target flatSig {
          stx := stx
          goalsBefore := #[goal]
          goalsAfter := #[goal] }
      else
        saveInternalObjectTacticInfo target flatSig byInfos

/-- Save Lean infoview and hover metadata for a Lean-quoted LF declaration body. -/
def saveLeanQuotedLFBodyInfo (target : InternalDefTarget) (params : Array HLBinding)
    (typeExpr : ObjExpr) (bodyStx : Syntax) : CommandElabM Unit := do
  let goal : InternalObjectGoal := { ctx := params, target := typeExpr }
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | return ()
  let flatSig ← liftCoreM <| flattenSignature sig
  saveLeanQuotedLFBodyGoalInfo target flatSig goal bodyStx

/-- Whether a Lean term body is exactly `sorry` or `by sorry`, preserving admissions. -/
def leanQuotedTermIsSorryAdmission (stx : Syntax) : Bool :=
  stx.isOfKind `Lean.Parser.Term.sorry ||
    stx.isOfKind `Lean.Parser.Term.byTactic &&
      let steps := collectLeanQuotedTacticSteps stx
      steps.size == 1 && steps[0]!.isOfKind `Lean.Parser.Tactic.tacticSorry

/-- Run the existing LF implicit elaborator on a Lean-quoted declaration header.

Term bodies can then use Lean's implicit insertion against a fully elaborated expected quote type,
while the trusted LF checker still validates the reflected declaration. -/
def elaborateLeanQuotedHeaderImplicits (target : InternalDefTarget) (params : Array HLBinding)
    (typeExpr : ObjExpr) : CommandElabM (Array HLBinding × ObjExpr) := do
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  liftCoreM do
    let (params, knownTypes, locals) ←
      elaborateImplicitAppsInBindings flatSig {} {} "internal declaration" target.localName params
    let typeExpr ←
      elaborateImplicitAppsInExpr flatSig knownTypes locals "internal declaration" target.localName
        "type" none typeExpr
    pure (params, typeExpr)

/-- Elaborate and reflect a quoted LF term for diagnostics. -/
def elabAndReflectLFQuoteTerm (theoryName : Name) (body : TSyntax `term) :
    CommandElabM ObjExpr := do
  let builtinQuoteOpenDecl ← `(Lean.Parser.Command.openDecl| InternalLean.LFQuote)
  let quoteNs := mkIdent (lfQuoteNamespace theoryName)
  let quoteOpenDecl ← `(Lean.Parser.Command.openDecl| $quoteNs:ident)
  let protectedNames := collectLFQuoteBinderNames body.raw
  let body :=
    match ← liftCoreM <| getCheckedHLSignature? theoryName with
    | some sig => qualifyLFQuoteSourceIdents theoryName sig protectedNames body
    | none => body.raw
  let body ← `(term| open $builtinQuoteOpenDecl in open $quoteOpenDecl in $(⟨body⟩):term)
  liftTermElabM do
    let value ← Term.elabTerm body none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    reflectLFQuoteExpr theoryName #[] value

syntax (name := reflectLFQuote) "#reflect_lf_quote " ident " : " term : command

elab_rules : command
  | `(#reflect_lf_quote $theory:ident : $body:term) => do
      unless (← liftCoreM <| getCheckedHLSignature? theory.getId).isSome do
        throwError "no checked high-level signature stored for type theory '{theory.getId}'"
      let valueExpr ← elabAndReflectLFQuoteTerm theory.getId body
      logInfo m!"reflected LF term in type theory '{theory.getId}':\n  \
        {diagnosticObjExprString valueExpr}"

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

/-- Register a Lean-quoted theorem-shaped internal declaration from reflected LF expressions. -/
def elabLeanQuotedInternalTheoremCheckedExpr
    (doc? : Option (TSyntax ``Parser.Command.docComment)) (declNameStx : Syntax)
    (declName : Name) (params : Array HLBinding) (typeExpr valueExpr : ObjExpr)
    (sourceCommand : String := "internal theorem (Lean-quoted)") : CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let valueExpr ←
    match elaborateInternalDirectTermPlaceholders target flatSig params typeExpr valueExpr with
    | .ok valueExpr => pure valueExpr
    | .error err => throwError err
  let lfTheorem : LFJudgmentTheoremDecl := {
    name := target.localName
    binders := params
    judgmentExpr := typeExpr
    proof := valueExpr }
  liftCoreM <| registerLFJudgmentTheorem target.theoryName lfTheorem
  if let some doc := sourceDoc? then
    liftCoreM <| registerSourceDoc target.theoryName .internalDef target.localName doc
  addInternalDeclarationAnchor target (mkInternalDefFunctionType params typeExpr)
    .checkedJudgmentTheorem params (some valueExpr) sourceCommand sourceDoc? (← getRef)
    declNameStx
  addInternalDeclarationQuoteStub target params typeExpr
  refreshLFMirrorAfterInternalRegistration target.theoryName

/-- Run a command elaboration step with configurable state restoration. -/
def withRestoredCommandStateCore (restoreOnSuccess : Bool) (x : CommandElabM α) :
    CommandElabM α := do
  let savedState ← get
  try
    let out ← x
    if restoreOnSuccess then
      set savedState
    pure out
  catch ex =>
    set savedState
    throw ex

/-- Run a speculative command elaboration step, restoring command state if it fails.

Prefer-mode quoted elaboration uses this wrapper before falling back to the legacy frontend.  Lean
term elaboration and generated-declaration checks can leave messages or partial info state behind
before throwing; those diagnostics should not survive a successful legacy fallback. -/
def withRestoredCommandStateOnError (x : CommandElabM α) : CommandElabM α :=
  withRestoredCommandStateCore false x

/-- Run a command elaboration probe and restore command state whether it succeeds or fails. -/
def withRestoredCommandState (x : CommandElabM α) : CommandElabM α :=
  withRestoredCommandStateCore true x

/-- Elaborate one object-language expression field as a Lean-quoted LF term.

The supplied signature prefix is the LF signature visible to the field, and `stagedEnv?` can
include quote stubs for a checked same-block prefix that has not been committed to the command
environment.  The reflected `ObjExpr` must still be checked by the LF checker before
registration. -/
def elabLeanQuotedObjTerm (theoryName : Name) (sigPrefix : HLSignature)
    (locals : Array HLBinding) (expected? : Option ObjExpr) (body : TSyntax `term)
    (stagedEnv? : Option Environment := none) : CommandElabM ObjExpr := do
  let run : CommandElabM ObjExpr := do
    let builtinQuoteOpenDecl ← `(Lean.Parser.Command.openDecl| InternalLean.LFQuote)
    let quoteNs := mkIdent (lfQuoteNamespace theoryName)
    let quoteOpenDecl ← `(Lean.Parser.Command.openDecl| $quoteNs:ident)
    let protectedNames :=
      locals.foldl (init := collectLFQuoteBinderNames body.raw) fun names p =>
        names.insert p.name.eraseMacroScopes
    let body := qualifyLFQuoteSourceIdents theoryName sigPrefix protectedNames body
    let body ← `(term| open $builtinQuoteOpenDecl in open $quoteOpenDecl in $(⟨body⟩):term)
    liftTermElabM do
      let rec withLocals (i : Nat) (reflectedLocals : LFQuoteLocalMap)
          (typeLocals : LFQuoteLeanLocalMap) (untypedLocals : NameSet) : TermElabM ObjExpr := do
        if h : i < locals.size then
          let p := locals[i]
          let env ← getEnv
          let pName := p.name.eraseMacroScopes
          let pSupported := lfQuoteSupportsIndexedQuoteType env theoryName
            (lfQuoteLeanLocalNames typeLocals) untypedLocals p.typeExpr
          let binderType := lfQuoteLeanTypeOfBinding env theoryName typeLocals untypedLocals p
          let untypedLocals := if pSupported then untypedLocals else untypedLocals.insert pName
          withLocalDecl pName (lfQuoteBinderInfoOfVisibility p.visibility) binderType fun fvar =>
            withLocals (i + 1) (reflectedLocals.push (fvar.fvarId!, pName))
              (typeLocals.push (pName, fvar)) untypedLocals
        else
          let env ← getEnv
          let expectedType? :=
            expected?.map fun expected =>
              lfQuoteLeanTypeOfObjType env theoryName typeLocals untypedLocals expected
          let value ← withEnableInfoTree false do
            let value ← withoutErrToSorry <| Term.elabTerm body expectedType?
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars value
          reflectLFQuoteExprWithSignature theoryName (some (mkLFQuoteSignatureContext sigPrefix))
            reflectedLocals value
      withLocals 0 #[] #[] {}
  match stagedEnv? with
  | some env => withEnv env run
  | none => run

/-- Parse a legacy theory-field source range as a Lean term.

Theory blocks still parse expression fields with the `ttExpr` category while the quoted block
frontend soaks behind a fallback. Canonical internal declaration bodies are parsed as Lean terms by
the command grammar and do not use this compatibility parser. -/
def parseLeanTermFromTheoryFieldSource (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let some startPos := stx.getPos? (canonicalOnly := true)
    | throwError "cannot recover source range for Lean-quoted theory expression"
  let some stopPos := stx.getTailPos? (canonicalOnly := true)
    | throwError "cannot recover source range for Lean-quoted theory expression"
  let source := String.Pos.Raw.extract (← getFileMap).source startPos stopPos
  match Lean.Parser.runParserCategory (← getEnv) `term source with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwError "could not parse theory expression as a Lean term: {err}"

/-- Parse a legacy theory expression, elaborate it as quoted LF, and reflect it. -/
def elabLeanQuotedObjExpr (theoryName : Name) (sigPrefix : HLSignature)
    (locals : Array HLBinding) (expected? : Option ObjExpr) (stx : Syntax)
    (stagedEnv? : Option Environment := none) : CommandElabM ObjExpr := do
  let term ← parseLeanTermFromTheoryFieldSource stx
  elabLeanQuotedObjTerm theoryName sigPrefix locals expected? term stagedEnv?

/-- Elaborate a theory-block expression with the Lean-quoted frontend.

In preference mode, unsupported quoted expressions fall back to the legacy object-expression parser
for this field, so existing object-universe and structural syntax can continue to migrate in small
steps.  In strict mode, the quoted elaboration error is reported. -/
def elabLeanQuotedTheoryObjExpr (theoryName : Name) (sigPrefix : HLSignature)
    (stagedEnv : Environment) (strict : Bool) (locals : Array HLBinding)
    (expected? : Option ObjExpr) (stx : TSyntax `ttExpr) : CommandElabM ObjExpr := do
  if strict then
    elabLeanQuotedObjExpr theoryName sigPrefix locals expected? stx.raw (some stagedEnv)
  else
    try
      withRestoredCommandStateOnError <|
        elabLeanQuotedObjExpr theoryName sigPrefix locals expected? stx.raw (some stagedEnv)
    catch ex =>
      recordInternalFrontendFallbackException `theoryObjExpr stx.raw ex
      elabObjExpr stx

/-- Elaborate a telescope of theory-block binders through the quoted frontend. -/
def elabLeanQuotedTheoryBinders (theoryName : Name) (sigPrefix : HLSignature)
    (stagedEnv : Environment) (strict : Bool) (binders : TSyntaxArray `ttBinder) :
    CommandElabM (Array HLBinding) := do
  let mut out : Array HLBinding := #[]
  for binder in binders do
    match binder with
    | `(ttBinder| ($x:ident : $ty:ttExpr)) => do
        let typeExpr ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict out none ty
        out := out.push { name := x.getId, typeExpr, visibility := .explicit }
    | `(ttBinder| {$x:ident : $ty:ttExpr}) => do
        let typeExpr ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict out none ty
        out := out.push { name := x.getId, typeExpr, visibility := .implicit }
    | stx => throwError "unsupported type-theory binder syntax:{indentD stx}"
  pure out

/-- Elaborate one rule-block item, returning any premise local it introduces. -/
def elabLeanQuotedTheoryRuleItem (theoryName : Name) (sigPrefix : HLSignature)
    (stagedEnv : Environment) (strict : Bool) (locals : Array HLBinding)
    (item : TSyntax `ttRuleItem) : CommandElabM (ParsedRuleItem × Option HLBinding) := do
  match item with
  | `(ttRuleItem| premise $n:ident : $j:ttExpr) => do
      let judgmentExpr ←
        elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict locals none j
      let premiseDecl : RulePremiseDecl := { name := n.getId, judgmentExpr }
      let localBinding : HLBinding := { name := n.getId, typeExpr := judgmentExpr, visibility :=
        .explicit }
      pure (.premise premiseDecl, some localBinding)
  | `(ttRuleItem| evidence $h:ident for $n:ident : $j:ttExpr) => do
      let judgmentExpr ←
        elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict locals none j
      let evidenceDecl : RuleParamEvidenceDecl := {
        name := h.getId
        paramName := n.getId
        judgmentExpr
      }
      let localBinding : HLBinding := { name := h.getId, typeExpr := judgmentExpr, visibility :=
        .explicit }
      pure (.evidence evidenceDecl, some localBinding)
  | `(ttRuleItem| side_condition $n:ident by $solver:ident : $input:ttExpr) => do
      let input ←
        elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict locals none input
      pure (.sideCondition { name := n.getId, solver := solver.getId, input }, none)
  | `(ttRuleItem| conclusion : $j:ttExpr) => do
      let conclusionExpr ←
        elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict locals none j
      pure (.concl conclusionExpr, none)
  | stx => throwError "unsupported rule item syntax:{indentD stx}"

/-- Elaborate a rule `where` block through the quoted frontend. -/
def elabLeanQuotedTheoryRuleItems (theoryName : Name) (sigPrefix : HLSignature)
    (stagedEnv : Environment) (strict : Bool) (params : Array HLBinding)
    (items : TSyntaxArray `ttRuleItem) : CommandElabM (Array ParsedRuleItem) := do
  let mut locals := params
  let mut out : Array ParsedRuleItem := #[]
  for item in items do
    let (parsed, local?) ←
      elabLeanQuotedTheoryRuleItem theoryName sigPrefix stagedEnv strict locals item
    out := out.push parsed
    if let some localBinding := local? then
      locals := locals.push localBinding
  pure out

/-- Add generated quote stubs for a high-level signature to a staged environment. -/
def addLFQuoteStubsForHLSignatureToEnvIfMissing (env : Environment) (theoryName : Name)
    (sig : HLSignature) : CoreM Environment := do
  let mut env := env
  for d in sig.syntaxSorts do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  for d in sig.syntaxAbbrevs do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  for d in sig.syntaxDefs do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  for d in sig.judgmentAbbrevs do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  for d in sig.lfOpaqueConsts do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name
        (lfQuoteParamsOfLFOpaqueConst d) d.typeExpr?
  for d in sig.judgments do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  for d in sig.rules do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name (lfQuoteParamsOfRule d)
        (some d.conclusionExpr)
  for d in sig.lfObjectDefs do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name #[] (some d.typeExpr)
  for d in sig.lfJudgmentTheorems do
    unless env.contains (lfQuoteDeclName theoryName d.name) do
      env ← addLFQuoteStubDeclarationToEnv env theoryName d.name d.binders
        (some d.judgmentExpr)
  pure env

/-- Add a generated quote stub for one theory-block item to a staged environment. -/
def addLFQuoteStubForTheoryItemToEnvIfMissing (env : Environment) (theoryName : Name)
    (item : HLTheoryItem) : CoreM Environment := do
  match item with
  | .syntaxSort d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  | .syntaxAbbrev d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  | .syntaxDef d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  | .judgmentAbbrev d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  | .judgment d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.params
  | .rule d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name (lfQuoteParamsOfRule d)
          (some d.conclusionExpr)
  | .lfOpaqueConst d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name (lfQuoteParamsOfLFOpaqueConst d)
          d.typeExpr?
  | .lfObjectDef d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name #[] (some d.typeExpr)
  | .lfJudgmentTheorem d =>
      if env.contains (lfQuoteDeclName theoryName d.name) then
        pure env
      else
        addLFQuoteStubDeclarationToEnv env theoryName d.name d.binders (some d.judgmentExpr)
  | _ => pure env

/-- Known LF definition result types from a high-level signature prefix. -/
def lfKnownTypesOfHLSignature (sig : HLSignature) : LFLocalTypes := Id.run do
  let mut out : LFLocalTypes := {}
  for d in sig.syntaxDefs do
    out := out.insert d.name.eraseMacroScopes <|
      eraseObjExprScopes (mkInternalDefFunctionType d.params (objExprTypeOfLevel d.resultLevel))
  for d in sig.lfObjectDefs do
    out := out.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  return out

/-- Extend known LF definition result types with one item, if it introduces one. -/
def insertKnownTypesForTheoryItem (knownTypes : LFLocalTypes) (item : HLTheoryItem) :
    LFLocalTypes :=
  match item with
  | .syntaxDef d =>
      knownTypes.insert d.name.eraseMacroScopes <|
        eraseObjExprScopes (mkInternalDefFunctionType d.params (objExprTypeOfLevel d.resultLevel))
  | .lfObjectDef d =>
      knownTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  | _ => knownTypes

/-- State threaded through sequential Lean-quoted theory-block elaboration. -/
structure LeanQuotedTheoryBlockState where
  /-- Signature prefix visible to the next item. -/
  sigPrefix : HLSignature
  /-- Staged Lean environment containing quote stubs for the visible prefix. -/
  stagedEnv : Environment
  /-- Known LF definition result types for the visible prefix. -/
  knownTypes : LFLocalTypes
  /-- Elaborated items in source order. -/
  items : Array HLTheoryItem := #[]

/-- Extract the single elaborated item matching `original` from a one-item block. -/
def implicitElaboratedTheoryItemFromBlock (original : HLTheoryItem) (block : HLTheoryBlock) :
    HLTheoryItem :=
  match original with
  | .syntaxSort _ => .syntaxSort block.syntaxSorts[0]!
  | .syntaxAbbrev _ => .syntaxAbbrev block.syntaxAbbrevs[0]!
  | .syntaxDef _ => .syntaxDef block.syntaxDefs[0]!
  | .judgmentAbbrev _ => .judgmentAbbrev block.judgmentAbbrevs[0]!
  | .judgment _ => .judgment block.judgments[0]!
  | .rule _ => .rule block.rules[0]!
  | .lfOpaqueConst _ => .lfOpaqueConst block.lfOpaqueConsts[0]!
  | .lfObjectDef _ => .lfObjectDef block.lfObjectDefs[0]!
  | .lfJudgmentTheorem _ => .lfJudgmentTheorem block.lfJudgmentTheorems[0]!
  | _ => original

/-- Run the existing LF implicit-argument elaborator on one staged theory-block item. -/
def elaborateImplicitAppsInLeanQuotedTheoryItem (state : LeanQuotedTheoryBlockState)
    (item : HLTheoryItem) : CoreM HLTheoryItem := do
  let block ← elaborateImplicitAppsInTheoryBlockExtension state.sigPrefix state.knownTypes <|
    HLTheoryBlock.ofItems #[item]
  pure <| implicitElaboratedTheoryItemFromBlock item block

/-- Append one quoted-elaborated theory item to the staged prefix. -/
def LeanQuotedTheoryBlockState.pushItem (theoryName : Name) (state : LeanQuotedTheoryBlockState)
    (rawItem : HLTheoryItem) : CommandElabM LeanQuotedTheoryBlockState := do
  let item ← liftCoreM <| elaborateImplicitAppsInLeanQuotedTheoryItem state rawItem
  let stagedEnv ←
    liftCoreM <| addLFQuoteStubForTheoryItemToEnvIfMissing state.stagedEnv theoryName item
  let sigPrefix := state.sigPrefix.appendBlock (HLTheoryBlock.ofItems #[item])
  let knownTypes := insertKnownTypesForTheoryItem state.knownTypes item
  pure { sigPrefix, stagedEnv, knownTypes, items := state.items.push item }

/-- Elaborate one theory-block item through the Lean-quoted frontend where it has expressions. -/
def elabLeanQuotedTheoryItem (theoryName : Name) (sigPrefix : HLSignature)
    (stagedEnv : Environment) (strict : Bool) (decl : TSyntax `ttDecl) :
    CommandElabM HLTheoryItem := do
  match decl with
  | `(ttDecl| $[$doc?:docComment]? syntax_sort $n:ident $bs:ttBinder*) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      pure <| .syntaxSort { name := n.getId, params := bs }
  | `(ttDecl| $[$doc?:docComment]? syntax_sort $n:ident $bs:ttBinder* : $result:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      pure <| .syntaxSort {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result) }
  | `(ttDecl| $[$doc?:docComment]? syntax_abbrev $n:ident $bs:ttBinder* :=
      $value:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let value ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs none value
      pure <| .syntaxAbbrev { name := n.getId, params := bs, value }
  | `(ttDecl| $[$doc?:docComment]? syntax_def $n:ident $bs:ttBinder* : $result:ttExpr :=
      sorry) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      pure <| .syntaxDef {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result "syntax_def")
        value? := none }
  | `(ttDecl| $[$doc?:docComment]? syntax_def $n:ident $bs:ttBinder* : $result:ttExpr :=
      $value:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let value ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs none value
      pure <| .syntaxDef {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result "syntax_def")
        value? := some value }
  | `(ttDecl| $[$doc?:docComment]? judgment_abbrev $n:ident $bs:ttBinder* :=
      $value:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let value ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs none value
      pure <| .judgmentAbbrev { name := n.getId, params := bs, value }
  | `(ttDecl| $[$doc?:docComment]? judgment $n:ident $bs:ttBinder*) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      pure <| .judgment { name := n.getId, params := bs }
  | `(ttDecl| $[$doc?:docComment]? rule $n:ident $bs:ttBinder* : $conclStx:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let conclusionExpr ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs
        none conclStx
      pure <| .rule { name := n.getId, params := bs, conclusionExpr }
  | `(ttDecl| $[$doc?:docComment]? rule $n:ident $bs:ttBinder* where $items:ttRuleItem*) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let items ← elabLeanQuotedTheoryRuleItems theoryName sigPrefix stagedEnv strict bs items
      pure <| .rule (← mkRuleDeclFromItems n.getId bs items)
  | `(ttDecl| $[$doc?:docComment]? lf_opaque $n:ident $bs:ttBinder* : $ty:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let typeExpr? ←
        some <$> elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs none ty
      pure <| .lfOpaqueConst { name := n.getId, arity? := some bs.size, params := bs, typeExpr? }
  | `(ttDecl| $[$doc?:docComment]? lf_def $n:ident : $ty:ttExpr := $value:ttExpr) => do
      let typeExpr ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict #[] none ty
      let value ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict #[]
        (some typeExpr) value
      pure <| .lfObjectDef { name := n.getId, typeExpr, value }
  | `(ttDecl| $[$doc?:docComment]? judgment_theorem $n:ident $bs:ttBinder* : $j:ttExpr :=
      $proof:ttExpr) => do
      let bs ← elabLeanQuotedTheoryBinders theoryName sigPrefix stagedEnv strict bs
      let judgmentExpr ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs none j
      let proof ← elabLeanQuotedTheoryObjExpr theoryName sigPrefix stagedEnv strict bs
        (some judgmentExpr) proof
      pure <| .lfJudgmentTheorem { name := n.getId, binders := bs, judgmentExpr, proof }
  | stx => elabHLTheoryItem stx

/-- Elaborate a whole theory block in source order with staged same-block quote stubs. -/
def elabLeanQuotedTheoryBlock (theoryName : Name) (basePrefix : HLSignature)
    (decls : TSyntaxArray `ttDecl) (strict : Bool) : CommandElabM HLTheoryBlock := do
  let env ← getEnv
  let stagedEnv ←
    liftCoreM <| addLFQuoteStubsForHLSignatureToEnvIfMissing env theoryName basePrefix
  let knownTypes := lfKnownTypesOfHLSignature basePrefix
  let mut state : LeanQuotedTheoryBlockState := { sigPrefix := basePrefix, stagedEnv, knownTypes }
  for decl in decls do
    let item ← elabLeanQuotedTheoryItem theoryName state.sigPrefix state.stagedEnv strict decl
    state ← state.pushItem theoryName item
  pure <| HLTheoryBlock.ofItems state.items

/-- Shape used to run the same implicit-elaboration path as registration in compare mode. -/
inductive InternalFrontendCompareShape where
  /-- Compare an `internal def` body as an LF object definition. -/
  | objectDef
  /-- Compare an `internal theorem` body as an LF judgment theorem. -/
  | judgmentTheorem

/-- Run the direct-term placeholder elaborator used before registering internal declarations. -/
def elaborateInternalFrontendComparePlaceholders (target : InternalDefTarget)
    (params : Array HLBinding) (typeExpr valueExpr : ObjExpr) : CommandElabM ObjExpr := do
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  match elaborateInternalDirectTermPlaceholders target flatSig params typeExpr valueExpr with
  | .ok valueExpr => pure valueExpr
  | .error err => throwError err

/-- Elaborate a compare-mode candidate through the object-definition implicit-app path. -/
def elaborateInternalFrontendCompareObjectDef (target : InternalDefTarget)
    (params : Array HLBinding) (typeExpr valueExpr : ObjExpr) : CommandElabM ObjExpr := do
  let some checked ← liftCoreM <| getCheckedTheory? target.theoryName
    | throwError "no checked artifact stored for type theory '{target.theoryName}'"
  let cacheLookup ← liftCoreM <| getOrBuildCompiledLFCheckCache target.theoryName checked
  let cache := cacheLookup.cache
  let d : LFObjectDefDecl := {
    name := target.localName
    typeExpr := mkInternalDefFunctionType params typeExpr
    value := mkInternalDefLambda params valueExpr }
  let rawBlock : HLTheoryBlock := { lfObjectDefs := #[d] }
  let flatSigWithRaw := cache.checkedHL.appendBlock rawBlock
  let implicitLookup := mkImplicitCallableLookupContextFromCache cache rawBlock
  let d ← liftCoreM <|
    elaborateImplicitAppsInLFObjectDefWithLookup implicitLookup flatSigWithRaw
      cache.knownLFDefTypes d
  pure d.value

/-- Elaborate a compare-mode candidate through the judgment-theorem implicit-app path. -/
def elaborateInternalFrontendCompareTheorem (target : InternalDefTarget)
    (params : Array HLBinding) (typeExpr valueExpr : ObjExpr) : CommandElabM ObjExpr := do
  let some checked ← liftCoreM <| getCheckedTheory? target.theoryName
    | throwError "no checked artifact stored for type theory '{target.theoryName}'"
  let cacheLookup ← liftCoreM <| getOrBuildCompiledLFCheckCache target.theoryName checked
  let cache := cacheLookup.cache
  let t : LFJudgmentTheoremDecl := {
    name := target.localName
    binders := params
    judgmentExpr := typeExpr
    proof := valueExpr }
  let rawBlock : HLTheoryBlock := { lfJudgmentTheorems := #[t] }
  let flatSigWithRaw := cache.checkedHL.appendBlock rawBlock
  let implicitLookup := mkImplicitCallableLookupContextFromCache cache rawBlock
  let t ← liftCoreM <|
    elaborateImplicitAppsInLFJudgmentTheoremWithLookup implicitLookup flatSigWithRaw
      cache.knownLFDefTypes t
  pure t.proof

/-- Elaborate a compare-mode body through placeholders and registration-style implicits. -/
def elaborateInternalFrontendCompareValue (shape : InternalFrontendCompareShape)
    (target : InternalDefTarget) (params : Array HLBinding) (typeExpr valueExpr : ObjExpr) :
    CommandElabM ObjExpr := do
  let valueExpr ← elaborateInternalFrontendComparePlaceholders target params typeExpr valueExpr
  match shape with
  | .objectDef => elaborateInternalFrontendCompareObjectDef target params typeExpr valueExpr
  | .judgmentTheorem => elaborateInternalFrontendCompareTheorem target params typeExpr valueExpr

/-- Parse a canonical Lean-term body source through the legacy `ttExpr` grammar for compare mode. -/
def parseLegacyObjExprFromTermSource (stx : Syntax) : CommandElabM (TSyntax `ttExpr) := do
  let some startPos := stx.getPos? (canonicalOnly := true)
    | throwError "cannot recover source range for legacy frontend comparison"
  let some stopPos := stx.getTailPos? (canonicalOnly := true)
    | throwError "cannot recover source range for legacy frontend comparison"
  let source := String.Pos.Raw.extract (← getFileMap).source startPos stopPos
  match Lean.Parser.runParserCategory (← getEnv) `ttExpr source with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwError "legacy frontend cannot parse Lean-term body: {err}"

/-- Elaborate a canonical body through the legacy frontend for compare mode, if possible. -/
def legacyInternalFrontendBodyForCompare? (shape : InternalFrontendCompareShape)
    (fallbackKind : Name) (target : InternalDefTarget) (params : Array HLBinding)
    (typeExpr : ObjExpr) (bodyStx : TSyntax `term) : CommandElabM (Option ObjExpr) := do
  try
    let valueExpr ← withRestoredCommandState do
      let legacyStx ← parseLegacyObjExprFromTermSource bodyStx.raw
      let valueExpr ← elabObjExpr legacyStx
      elaborateInternalFrontendCompareValue shape target params typeExpr valueExpr
    pure (some valueExpr)
  catch ex =>
    recordInternalFrontendFallbackException fallbackKind bodyStx.raw ex
    pure none

/-- Compare a successful Lean-quoted body with the legacy frontend when requested. -/
def compareLeanQuotedBodyWithLegacyIfEnabled (shape : InternalFrontendCompareShape)
    (fallbackKind : Name) (declName : Name) (target : InternalDefTarget)
    (params : Array HLBinding) (typeExpr quotedValue : ObjExpr) (bodyStx : TSyntax `term) :
    CommandElabM Unit := do
  unless ← compareLeanQuotedWithLegacyFrontend do
    return ()
  let some quotedValue ←
      try
        some <$> withRestoredCommandState do
          elaborateInternalFrontendCompareValue shape target params typeExpr quotedValue
      catch ex =>
        recordInternalFrontendFallbackException fallbackKind bodyStx.raw ex
        pure none
    | return ()
  let some legacyValue ← legacyInternalFrontendBodyForCompare? shape fallbackKind target params
      typeExpr bodyStx
    | return ()
  unless lfExprAlphaEq quotedValue legacyValue do
    let quotedText := diagnosticObjExprString quotedValue
    let legacyText := diagnosticObjExprString legacyValue
    throwError "Lean-quoted frontend and legacy frontend produced different LF bodies for \
      internal declaration '{declName.eraseMacroScopes}'.\n\nLean-quoted body:\n  \
      {quotedText}\n\nLegacy body:\n  {legacyText}"

/-- Whether canonical internal declarations should use the quoted frontend. -/
def preferLeanQuotedFrontend : CommandElabM Bool :=
  return (← getOptions).getBool `internalLean.preferLeanQuotedFrontend true

/-- Whether theory-block commands should try the quoted frontend first. -/
def preferLeanQuotedTheoryBlocks : CommandElabM Bool :=
  return (← getOptions).getBool `internalLean.preferLeanQuotedTheoryBlocks true

/-- Whether theory-block commands must use the quoted frontend. -/
def requireLeanQuotedTheoryBlocks : CommandElabM Bool :=
  getBoolOption `internalLean.requireLeanQuotedTheoryBlocks

/-- Ensure the quoted theory-block frontend is enabled for this command elaborator. -/
def ensureLeanQuotedTheoryBlockFrontendEnabled : CommandElabM Bool := do
  let strict ← requireLeanQuotedTheoryBlocks
  unless strict || (← preferLeanQuotedTheoryBlocks) do
    throwUnsupportedSyntax
  pure strict

/-- Try the Lean-quoted frontend for one `declare_type_theory` command. -/
def elabDeclareInternalLeanQuoted (doc? : Option (TSyntax ``Parser.Command.docComment))
    (nm : Ident) (levelParams parents : Array Name) (decls : TSyntaxArray `ttDecl) :
    CommandElabM Unit := do
  let strict ← ensureLeanQuotedTheoryBlockFrontendEnabled
  if strict then
    try
      let basePrefix ← liftCoreM <| flattenSignature { name := nm.getId, parents, levelParams }
      let block ← elabLeanQuotedTheoryBlock nm.getId basePrefix decls strict
      elabDeclareInternalLeanWithBlock doc? nm levelParams parents decls block
    catch ex =>
      recordFailedTheoryDeclarationFromSyntax nm
      throw ex
  else
    try
      withRestoredCommandStateOnError do
        let basePrefix ← liftCoreM <| flattenSignature { name := nm.getId, parents, levelParams }
        let block ← elabLeanQuotedTheoryBlock nm.getId basePrefix decls strict
        elabDeclareInternalLeanWithBlock doc? nm levelParams parents decls block
    catch ex =>
      recordInternalFrontendFallbackException `declareTypeTheory nm.raw ex
      elabDeclareInternalLean doc? nm levelParams parents decls

/-- Try the Lean-quoted frontend for one `extend_type_theory` command. -/
def elabExtendInternalLeanQuoted (doc? : Option (TSyntax ``Parser.Command.docComment))
    (nm : Ident) (decls : TSyntaxArray `ttDecl) : CommandElabM Unit := do
  let strict ← ensureLeanQuotedTheoryBlockFrontendEnabled
  if strict then
    let some basePrefix ← liftCoreM <| getCheckedHLSignature? nm.getId
      | throwError "unknown type theory '{nm.getId}'; use `declare_type_theory {nm.getId} \
          where ...` before `extend_type_theory`"
    let block ← elabLeanQuotedTheoryBlock nm.getId basePrefix decls strict
    elabExtendInternalLeanWithBlock doc? nm decls block
  else
    try
      withRestoredCommandStateOnError do
        let some basePrefix ← liftCoreM <| getCheckedHLSignature? nm.getId
          | throwUnsupportedSyntax
        let block ← elabLeanQuotedTheoryBlock nm.getId basePrefix decls strict
        elabExtendInternalLeanWithBlock doc? nm decls block
    catch ex =>
      recordInternalFrontendFallbackException `extendTypeTheory nm.raw ex
      elabExtendInternalLean doc? nm decls

/-- Native tactic elaboration state used while pre-elaborating term arguments. -/
structure InternalNativePreElabGoal where
  ctx : Array HLBinding := #[]
  target : ObjExpr

/-- Parse one legacy `internalTactic` source span as a Lean tactic. -/
def parseInternalNativeLeanTacticFromSource (stx : Syntax) : CommandElabM (TSyntax `tactic) := do
  let some startPos := stx.getPos? (canonicalOnly := true)
    | throwErrorAt stx "cannot recover source range for native tactic parsing"
  let some stopPos := stx.getTailPos? (canonicalOnly := true)
    | throwErrorAt stx "cannot recover source range for native tactic parsing"
  let source := String.Pos.Raw.extract (← getFileMap).source startPos stopPos
  let trimmedSource := source.trimAscii.toString
  /- Legacy `internalTactic` focus bullets are standalone markers; Lean-native focus bullets are
  grouped by the Lean parser in canonical `by` terms.  Preserve the legacy marker as a no-op so
  existing object-tactic-style bullet scripts keep their goal order. -/
  if trimmedSource == "·" then
    return ⟨(← `(tactic| skip)).raw⟩
  /- Legacy tactic-form `have` uses a closing `end`; Lean's tactic parser expects the nested `by`
  term without it. -/
  let source :=
    if trimmedSource.startsWith "have " && trimmedSource.endsWith "end" then
      (trimmedSource.dropEnd 3).toString
    else
      source
  /- The Lean parser in this environment accepts named synthetic holes but not anonymous `?_` in
  this source-reparse path.  Rewriting to a named hole keeps legacy `_` as infer-only while
  preserving `?_` as a native refine subgoal. -/
  let source := source.replace "?_" "?nativeHole"
  match Lean.Parser.runParserCategory (← getEnv) `tactic source with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwErrorAt stx "could not parse InternalLean native tactic as Lean tactic: \
      {err}"

/-- Known LF local types for a native tactic context. -/
def internalNativeKnownTypesOfContext (ctx : Array HLBinding) : LFLocalTypes := Id.run do
  let mut out : LFLocalTypes := {}
  for b in ctx do
    out := out.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
  out

/-- Elaborate a Lean-quoted object term in a native tactic context. -/
def elabInternalNativeQuotedTerm (target : InternalDefTarget) (sig : HLSignature)
    (ctx : Array HLBinding) (expected? : Option ObjExpr) (term : TSyntax `term) :
    CommandElabM ObjExpr :=
  elabLeanQuotedObjTerm target.theoryName sig ctx expected? term

/-- Extract the object-theory candidate name from a native `apply` argument. -/
def internalNativeApplyTermName? (term : TSyntax `term) : Option Name :=
  match term.raw with
  | .ident _ _ n _ => some n
  | _ => none

/-- Build the native `apply` plan and its immediate object subgoals. -/
def mkInternalNativeApplyPlan (target : InternalDefTarget) (sig : HLSignature)
    (goal : InternalNativePreElabGoal) (rawName : Name) (ref : Syntax) :
    CommandElabM (InternalNativeApplyPlan × Array InternalNativePreElabGoal) := do
  let some cand := findInternalApplyCandidate? target sig rawName
    | throwErrorAt ref "native tactic `apply {rawName}` failed: unknown rule or internal \
        declaration '{rawName}' in type theory '{target.theoryName}'"
  let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
      cand.conclusionExpr goal.target
    | throwErrorAt ref ("native tactic `apply {rawName}` failed: " ++
        internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target)
  let mut subst := subst0
  let mut args : Array InternalNativeApplyArg := #[]
  let mut newGoals : Array InternalNativePreElabGoal := #[]
  for param in cand.params do
    let key := param.name.eraseMacroScopes
    match subst.find? key with
    | some arg => args := args.push (.closed arg)
    | none =>
        let paramTy := substObjectVars subst param.typeExpr
        args := args.push (.subgoal paramTy)
        newGoals := newGoals.push { ctx := goal.ctx, target := paramTy }
        subst := subst.insert key (internalObjectGoalPlaceholder param.name)
  for premiseTarget in cand.subgoalTargets do
    let premiseTarget := substObjectVars subst premiseTarget
    args := args.push (.subgoal premiseTarget)
    newGoals := newGoals.push { ctx := goal.ctx, target := premiseTarget }
  for sc in cand.sideConditions do
    let scInput := substObjectVars subst sc.input
    match classifySideConditionHook sc.solver with
    | .builtinTrivial => pure ()
    | .opaque =>
        throwErrorAt ref
          (internalOpaqueSideConditionMessage "apply" rawName cand.name sc.name sc.solver scInput)
  pure ({ rawName, candidateName := cand.name, args }, newGoals)

/-- True when a Lean term syntax contains an anonymous or synthetic hole. -/
partial def internalNativeTermSyntaxHasHole : Syntax → Bool
  | .node _ `Lean.Parser.Term.hole _ => true
  | .node _ `Lean.Parser.Term.syntheticHole _ => true
  | .node _ _ args => args.any internalNativeTermSyntaxHasHole
  | _ => false

/-- Convert a Lean term from a native `refine` into object-tactic argument syntax. -/
partial def elabInternalNativeTacticArgSyntax (target : InternalDefTarget) (sig : HLSignature)
    (ctx : Array HLBinding) (term : Syntax) : CommandElabM InternalTacticArg := do
  let fallback : CommandElabM InternalTacticArg := do
    pure (.expr (← elabInternalNativeQuotedTerm target sig ctx none ⟨term⟩))
  match term with
  | .node _ `Lean.Parser.Term.paren args =>
      match args[1]? with
      | some inner => elabInternalNativeTacticArgSyntax target sig ctx inner
      | none => fallback
  | .node _ `Lean.Parser.Term.hole _ => pure .inferPlaceholder
  | .node _ `Lean.Parser.Term.syntheticHole _ => pure .refineHole
  | .ident _ _ n _ => pure (.expr (.ident n))
  | .node _ `Lean.Parser.Term.app args =>
      match args[0]?, args[1]? with
      | some head, some argList =>
          match head with
          | .ident _ _ rawName _ =>
              let useCandidate := (findInternalApplyCandidate? target sig rawName).isSome ||
                internalNativeTermSyntaxHasHole term
              if useCandidate then
                pure (.app rawName (← argList.getArgs.mapM
                  (elabInternalNativeTacticArgSyntax target sig ctx)))
              else
                fallback
          | _ => fallback
      | _, _ => fallback
  | _ => fallback

/-- Throw a string-valued object-tactic diagnostic at native tactic source. -/
def throwInternalNativeObjectTacticErrorAt (ref : Syntax) (x : Except String α) :
    CommandElabM α :=
  match x with
  | .ok value => pure value
  | .error err => throwErrorAt ref err

/-- Whether a native plan argument contains a user-created proof subgoal. -/
partial def internalNativeApplyArgHasSubgoal : InternalNativeApplyArg → Bool
  | .closed _ => false
  | .subgoal _ => true
  | .candidateApp _ args => args.any internalNativeApplyArgHasSubgoal

mutual
  /-- Build a nested native `refine` plan argument and a diagnostic expression for dependencies. -/
  partial def mkInternalNativeRefinePlanArg (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (goal : InternalNativePreElabGoal) (arg : InternalTacticArg)
      (allowHoles : Bool) (tacticName : String) (ref : Syntax) :
      CommandElabM (InternalNativeApplyArg × ObjExpr × Array InternalNativePreElabGoal) := do
    match arg with
    | .expr e => pure (.closed e, e, #[])
    | .inferPlaceholder =>
        throwErrorAt ref
          (m!"native tactic `{tacticName}` cannot infer nested placeholder `_` without a \
            candidate head")
    | .refineHole =>
        unless allowHoles do
          throwErrorAt ref "native tactic `exact` does not accept nested refinement hole `?_`"
        let placeholder := internalObjectGoalPlaceholder `_nested
        pure (.subgoal goal.target, placeholder, #[goal])
    | .app rawName args =>
        mkInternalNativeRefineCandidateArg target sig levels goal rawName args allowHoles
          tacticName ref

  /-- Build a nested native `refine` candidate application. -/
  partial def mkInternalNativeRefineCandidateArg (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (goal : InternalNativePreElabGoal) (rawName : Name)
      (suppliedArgs : Array InternalTacticArg) (allowHoles : Bool) (tacticName : String)
      (ref : Syntax) :
      CommandElabM (InternalNativeApplyArg × ObjExpr × Array InternalNativePreElabGoal) := do
    let (candidateName, args, diagArgs, newGoals) ←
      mkInternalNativeRefinePlanParts target sig levels goal rawName suppliedArgs allowHoles
        tacticName ref
    pure (.candidateApp candidateName args, mkObjectApps (.ident candidateName) diagArgs,
      newGoals)

  /-- Build native `refine` plan arguments and immediate object subgoals. -/
  partial def mkInternalNativeRefinePlanParts (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (goal : InternalNativePreElabGoal) (rawName : Name)
      (suppliedArgs : Array InternalTacticArg) (allowHoles : Bool) (tacticName : String)
      (ref : Syntax) :
      CommandElabM
        (Name × Array InternalNativeApplyArg × Array ObjExpr ×
          Array InternalNativePreElabGoal) := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throwErrorAt ref s!"native tactic `{tacticName} {rawName}` failed: unknown rule or \
          internal declaration '{rawName}' in type theory '{target.theoryName}'"
    discard <| throwInternalNativeObjectTacticErrorAt ref <|
      checkInternalCandidateAppArity tacticName rawName suppliedArgs.size cand
    let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throwErrorAt ref (s!"native tactic `{tacticName} {rawName}` failed: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target)
    let mut planArgs : Array InternalNativeApplyArg := #[]
    let mut diagArgs : Array ObjExpr := #[]
    let mut newGoals : Array InternalNativePreElabGoal := #[]
    let mut subst := subst0
    let useFullExplicit := internalCandidateUsesFullExplicit cand suppliedArgs.size
    let mut argIdx := 0
    for param in cand.params do
      let key := param.name.eraseMacroScopes
      let paramTy := substObjectVars subst param.typeExpr
      let argSpec? :=
        if useFullExplicit || param.visibility == .explicit then
          suppliedArgs[argIdx]?
        else
          none
      match argSpec? with
      | none =>
          match subst.find? key with
          | some inferred =>
              planArgs := planArgs.push (.closed inferred)
              diagArgs := diagArgs.push inferred
          | none =>
              throwErrorAt ref (internalCannotInferParameterMessage tacticName rawName
                param.name paramTy false false)
      | some argSpec =>
          argIdx := argIdx + 1
          match argSpec with
          | .inferPlaceholder =>
              match subst.find? key with
              | some inferred =>
                  planArgs := planArgs.push (.closed inferred)
                  diagArgs := diagArgs.push inferred
              | none =>
                  throwErrorAt ref (internalCannotInferParameterMessage tacticName rawName
                    param.name paramTy true false)
          | .refineHole =>
              unless allowHoles do
                throwErrorAt ref s!"native tactic `exact {rawName}` does not accept refinement \
                  hole `?_`; use `refine` or provide a complete argument"
              let placeholder := internalObjectGoalPlaceholder param.name
              let subgoal := { goal with target := paramTy }
              planArgs := planArgs.push (.subgoal paramTy)
              diagArgs := diagArgs.push placeholder
              newGoals := newGoals.push subgoal
              subst := subst.insert key placeholder
          | .expr e =>
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig levels goal.ctx e inferred do
                    throwErrorAt ref (internalArgumentMismatchMessage tacticName rawName
                      param.name e inferred)
              | none => subst := subst.insert key e
              planArgs := planArgs.push (.closed e)
              diagArgs := diagArgs.push e
          | .app _ _ =>
              let (planArg, diag, nestedGoals) ←
                mkInternalNativeRefinePlanArg target sig levels { goal with target := paramTy }
                  argSpec allowHoles tacticName ref
              newGoals := newGoals ++ nestedGoals
              match subst.find? key with
              | some inferred =>
                  unless internalNativeApplyArgHasSubgoal planArg do
                    unless objectGoalsConvertible sig levels goal.ctx diag inferred do
                      throwErrorAt ref (internalArgumentMismatchMessage tacticName rawName
                        param.name diag inferred true)
              | none => subst := subst.insert key diag
              planArgs := planArgs.push planArg
              diagArgs := diagArgs.push diag
    for premiseTarget in cand.subgoalTargets do
      let some argSpec := suppliedArgs[argIdx]?
        | throwErrorAt ref "internal error: missing checked native refine argument"
      argIdx := argIdx + 1
      let premiseGoal := substObjectVars subst premiseTarget
      match argSpec with
      | .inferPlaceholder =>
          throwErrorAt ref (s!"native tactic `{tacticName} {rawName}` cannot infer \
            placeholder `_` for a premise; write an explicit proof term or `?_`.\n\n" ++
            internalObjectTacticPlaceholderAdvice tacticName)
      | .refineHole =>
          unless allowHoles do
            throwErrorAt ref s!"native tactic `exact {rawName}` does not accept refinement \
              hole `?_`; use `refine` or provide a complete argument"
          let placeholder := internalObjectGoalPlaceholder (.str rawName.eraseMacroScopes
            s!"premise{argIdx}")
          planArgs := planArgs.push (.subgoal premiseGoal)
          diagArgs := diagArgs.push placeholder
          newGoals := newGoals.push { goal with target := premiseGoal }
      | .expr e =>
          discard <| throwInternalNativeObjectTacticErrorAt ref <|
            checkInternalPremiseProofExpr target sig levels goal.ctx e premiseGoal tacticName
              rawName
          planArgs := planArgs.push (.closed e)
          diagArgs := diagArgs.push e
      | .app _ _ =>
          let (planArg, diag, nestedGoals) ←
            mkInternalNativeRefinePlanArg target sig levels { goal with target := premiseGoal }
              argSpec allowHoles tacticName ref
          newGoals := newGoals ++ nestedGoals
          planArgs := planArgs.push planArg
          diagArgs := diagArgs.push diag
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throwErrorAt ref (internalOpaqueSideConditionMessage tacticName rawName cand.name
            sc.name sc.solver scInput)
    pure (cand.name, planArgs, diagArgs, newGoals)
end

/-- Build a native `refine` plan and the immediate object subgoals for its holes. -/
def mkInternalNativeRefinePlan (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (goal : InternalNativePreElabGoal) (rawName : Name)
    (args : Array InternalTacticArg) (ref : Syntax) :
    CommandElabM (InternalNativeApplyPlan × Array InternalNativePreElabGoal) := do
  let (candidateName, planArgs, _, newGoals) ←
    mkInternalNativeRefinePlanParts target sig levels goal rawName args true "refine" ref
  pure ({ rawName, candidateName, args := planArgs }, newGoals)

/-- Check and normalize a native `exact`/`have` proof term against an LF target. -/
def checkInternalNativeProofTerm (target : InternalDefTarget) (sig : HLSignature)
    (ctx : Array HLBinding) (expected proof : ObjExpr) (tacticName : String) (ref : Syntax) :
    CommandElabM ObjExpr := withRef ref do
  let proof ←
    match elaborateInternalDirectTermPlaceholders target sig ctx expected proof with
    | .ok proof => pure proof
    | .error err => throwError err
  try
    liftCoreM <| checkLFExprHasType sig "native tactic" target.localName
      s!"{tacticName} proof" (internalNativeKnownTypesOfContext ctx) proof expected
  catch ex =>
    throwError "native tactic `{tacticName}` failed to check proof against the current object \
      goal:\n{exceptionMessageData ex}"
  pure proof

mutual
  /-- Pre-elaborate one native tactic step enough that execution need not run Lean proof search.
  Unsupported steps are still passed to Lean and then rejected/audited, which catches user macros
  that assign display metavariables. -/
  partial def elabInternalNativeResolvedStep (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (goal : InternalNativePreElabGoal) (stx : Syntax) :
      CommandElabM (Array InternalNativeResolvedStep × Array InternalNativePreElabGoal) := do
    let unsupported : CommandElabM
        (Array InternalNativeResolvedStep × Array InternalNativePreElabGoal) :=
      pure (#[{ stx, step := .evalLeanForAudit }], #[goal])
    if let some bodySteps := internalNativeFocusBodySteps? stx then
      let (body, _) ← elabInternalNativeResolvedStepsForGoals target sig levels
        [{ ctx := goal.ctx, target := goal.target }] bodySteps
      return (#[{ stx, step := .focus body }], #[])
    match (⟨stx⟩ : TSyntax `tactic) with
    | `(tactic| skip) => pure (#[{ stx, step := .skip }], #[goal])
    | `(tactic| intro $name:ident) =>
        let goal' ←
          match introObjectGoal { ctx := goal.ctx, target := goal.target } name.getId with
          | .ok goal' => pure goal'
          | .error err => throwErrorAt stx err
        pure (#[{ stx, step := .intro name.getId }],
          #[{ ctx := goal'.ctx, target := goal'.target }])
    | `(tactic| intros $names:ident*) =>
        let rawNames := names.map (·.getId)
        let (introNames, goal') ←
          if rawNames.isEmpty then
            let (introNames, goal') := autoIntroGoal { ctx := goal.ctx, target := goal.target }
            pure (introNames, goal')
          else
            match introsObjectGoal { ctx := goal.ctx, target := goal.target } rawNames with
            | .ok goal' => pure (rawNames, goal')
            | .error err => throwErrorAt stx err
        pure (#[{ stx, step := .intros introNames }],
          #[{ ctx := goal'.ctx, target := goal'.target }])
    | `(tactic| exact $proof:term) =>
        let proofExpr ← withRef proof.raw <|
          elabInternalNativeQuotedTerm target sig goal.ctx (some goal.target) proof
        let proofExpr ← checkInternalNativeProofTerm target sig goal.ctx goal.target proofExpr
          "exact" proof.raw
        pure (#[{ stx, step := .exact proofExpr }], #[])
    | `(tactic| refine $proof:term) =>
        let arg ← elabInternalNativeTacticArgSyntax target sig goal.ctx proof.raw
        match arg with
        | .app rawName args =>
            let (plan, newGoals) ← mkInternalNativeRefinePlan target sig levels goal rawName
              args proof.raw
            pure (#[{ stx, step := .applyPlan plan }], newGoals)
        | .expr proofExpr =>
            let proofExpr ← checkInternalNativeProofTerm target sig goal.ctx goal.target proofExpr
              "refine" proof.raw
            pure (#[{ stx, step := .exact proofExpr }], #[])
        | .inferPlaceholder | .refineHole =>
            throwErrorAt proof.raw "native tactic `refine` needs a proof term or an application \
              headed by an object rule, theorem, or declaration"
    | `(tactic| assumption) =>
        let some _ := findAssumption? sig levels goal.ctx goal.target
          | throwErrorAt stx (String.intercalate "\n" [
              "native tactic `assumption` failed for object goal",
              s!"  {diagnosticObjExprString goal.target}",
              "",
              "Available object hypotheses:",
              renderInternalObjectContext goal.ctx])
        pure (#[{ stx, step := .assumption }], #[])
    | `(tactic| show $newTarget:term) =>
        let newTargetExpr ← withRef newTarget.raw <|
          elabInternalNativeQuotedTerm target sig goal.ctx none newTarget
        unless objectGoalsConvertible sig levels goal.ctx goal.target newTargetExpr do
          throwErrorAt newTarget.raw (String.intercalate "\n" [
            "native tactic `show` cannot replace the current object goal",
            s!"  {diagnosticObjExprString goal.target}",
            "with non-convertible/non-identical object goal",
            s!"  {diagnosticObjExprString newTargetExpr}",
            "",
            "This is object judgmental conversion, not Lean equality."])
        pure (#[{ stx, step := .showGoal newTargetExpr }],
          #[{ goal with target := newTargetExpr }])
    | `(tactic| change $newTarget:term) =>
        let newTargetExpr ← withRef newTarget.raw <|
          elabInternalNativeQuotedTerm target sig goal.ctx none newTarget
        match objectGoalConversionCheck sig levels goal.ctx goal.target newTargetExpr with
        | .ok _ =>
            pure (#[{ stx, step := .changeGoal newTargetExpr }],
              #[{ goal with target := newTargetExpr }])
        | .error err =>
            if objectGoalsConvertible sig levels goal.ctx goal.target newTargetExpr then
              pure (#[{ stx, step := .changeGoal newTargetExpr }],
                #[{ goal with target := newTargetExpr }])
            else
              throwErrorAt newTarget.raw (String.intercalate "\n" [
                "native tactic `change` cannot replace the current object goal",
                s!"  {diagnosticObjExprString goal.target}",
                s!"with\n  {diagnosticObjExprString newTargetExpr}",
                "",
                "The endpoints are not judgmentally convertible in the active object theory.",
                "This tactic checks object conversion evidence; it does not use Lean equality or \
                  an internal equality proof.",
                "",
                s!"conversion failure: {err}",
                "",
                objectGoalNormalizationMismatchString sig goal.ctx goal.target newTargetExpr])
    | `(tactic| have $name:ident : $typeTerm:term := $proofTerm:term) =>
        if internalObjectContextHasName goal.ctx name.getId then
          throwErrorAt name.raw "native tactic `have {name.getId}` failed: local name \
            '{name.getId}' is already in the object context"
        let typeExpr ← withRef typeTerm.raw <|
          elabInternalNativeQuotedTerm target sig goal.ctx none typeTerm
        let goal' := {
          ctx := goal.ctx.push { name := name.getId, typeExpr, visibility := .explicit }
          target := goal.target }
        if let some proofSteps := internalNativeLeanBySteps? proofTerm.raw then
          let (proofResolved, _) ← elabInternalNativeResolvedStepsForGoals target sig levels
            [{ ctx := goal.ctx, target := typeExpr }] proofSteps
          pure (#[]
            |>.push { stx, step := .haveStart name.getId typeExpr }
            |>.push { stx := proofTerm.raw, step := .focus proofResolved }, #[goal'])
        else
          let proofExpr ← withRef proofTerm.raw <|
            elabInternalNativeQuotedTerm target sig goal.ctx (some typeExpr) proofTerm
          let proofExpr ← checkInternalNativeProofTerm target sig goal.ctx typeExpr proofExpr
            "have" proofTerm.raw
          pure (#[{ stx, step := .haveTerm name.getId typeExpr proofExpr }], #[goal'])
    | `(tactic| apply $candidate:term) =>
        let some rawName := internalNativeApplyTermName? candidate
          | throwErrorAt candidate.raw "native tactic `apply` expects an object rule, theorem, \
            or declaration name"
        let (plan, newGoals) ← mkInternalNativeApplyPlan target sig goal rawName stx
        pure (#[{ stx, step := .applyPlan plan }], newGoals)
    | _ => unsupported

  /-- Pre-elaborate native tactic steps from an explicit object-goal list. -/
  partial def elabInternalNativeResolvedStepsForGoals (target : InternalDefTarget)
      (sig : HLSignature) (levels : Array Name) (initialGoals : List InternalNativePreElabGoal)
      (steps : Array Syntax) :
      CommandElabM (Array InternalNativeResolvedStep × List InternalNativePreElabGoal) := do
    let mut goals := initialGoals
    let mut out := #[]
    for stx in steps do
      let some goal := goals.head?
        | throwErrorAt stx "no remaining InternalLean native goals"
      let (resolved, newGoals) ← elabInternalNativeResolvedStep target sig levels goal stx
      out := out ++ resolved
      goals := newGoals.toList ++ goals.tail
    pure (out, goals)
end

/-- Pre-elaborate a native tactic block. -/
def elabInternalNativeResolvedSteps (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (targetExpr : ObjExpr)
    (steps : Array Syntax) : CommandElabM (Array InternalNativeResolvedStep) := do
  let (resolved, _) ← elabInternalNativeResolvedStepsForGoals target sig levels
    [{ ctx, target := targetExpr }] steps
  pure resolved

/-- Run a native tactic block and return its finalized LF proof/body term. -/
def elabInternalNativeByTerm (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (targetExpr : ObjExpr) (bodyStx : Syntax)
    (steps : Array Syntax) : CommandElabM ObjExpr := do
  let resolved ← elabInternalNativeResolvedSteps target sig levels ctx targetExpr steps
  let result ← runInternalNativeResolvedTactic target sig levels ctx targetExpr resolved
  finalizeInternalNativeTacticResult bodyStx result

/-- Elaborate a canonical checked `internal def` Lean-term body through the quoted frontend. -/
def elabCanonicalLeanQuotedDefChecked (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (binders : TSyntaxArray `ttBinder)
    (params : Array HLBinding) (typeStx : TSyntax `ttExpr) (bodyStx : TSyntax `term) :
    CommandElabM Unit := do
  if leanQuotedTermIsSorryAdmission bodyStx.raw then
    elabInternalDefSorryWithBinders doc? declNameStx declName #[] binders typeStx
    return ()
  let target ← resolveInternalDefTarget declName
  let typeExpr ← elabObjExpr typeStx
  let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target params typeExpr
  if (← liftCoreM internalNativeTacticModeEnabled) then
    if let some steps := internalNativeLeanBySteps? bodyStx.raw then
      if internalNativeStepsContainDirectSorry steps then
        elabInternalDefSorryWithBinders doc? declNameStx declName #[] binders typeStx
        return ()
      let some sig ← liftCoreM <| getTheory? target.theoryName
        | throwError "unknown type theory '{target.theoryName}'"
      let flatSig ← liftCoreM <| flattenSignature sig
      let valueExpr ← elabInternalNativeByTerm target flatSig #[] params typeExpr bodyStx.raw steps
      if params.isEmpty then
        elabInternalDefCheckedExpr doc? declNameStx declName #[] typeExpr valueExpr
          "internal def := by (native)"
      else
        elabInternalDefCheckedWithBindersExpr doc? declNameStx declName #[] params typeExpr
          valueExpr "internal def := by (native)"
      return ()
  let valueExpr ← elabLeanQuotedLFBody target params typeExpr bodyStx
  compareLeanQuotedBodyWithLegacyIfEnabled .objectDef `compareLegacyInternalDef declName target
    params typeExpr valueExpr bodyStx
  saveLeanQuotedLFBodyInfo target params typeExpr bodyStx.raw
  if params.isEmpty then
    elabInternalDefCheckedExpr doc? declNameStx declName #[] typeExpr valueExpr
      "internal def (Lean-quoted)"
  else
    elabInternalDefCheckedWithBindersExpr doc? declNameStx declName #[] params typeExpr
      valueExpr "internal def (Lean-quoted)"

/-- Elaborate a canonical checked `internal theorem` Lean-term body through the quoted frontend. -/
def elabCanonicalLeanQuotedTheoremChecked (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (binders : TSyntaxArray `ttBinder)
    (params : Array HLBinding) (typeStx : TSyntax `ttExpr) (bodyStx : TSyntax `term) :
    CommandElabM Unit := do
  if leanQuotedTermIsSorryAdmission bodyStx.raw then
    elabInternalTheoremSorryWithBinders doc? declNameStx declName #[] binders typeStx
    return ()
  let target ← resolveInternalDefTarget declName
  let typeExpr ← elabObjExpr typeStx
  let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target params typeExpr
  if (← liftCoreM internalNativeTacticModeEnabled) then
    if let some steps := internalNativeLeanBySteps? bodyStx.raw then
      if internalNativeStepsContainDirectSorry steps then
        elabInternalTheoremSorryWithBinders doc? declNameStx declName #[] binders typeStx
        return ()
      let some sig ← liftCoreM <| getTheory? target.theoryName
        | throwError "unknown type theory '{target.theoryName}'"
      let flatSig ← liftCoreM <| flattenSignature sig
      let valueExpr ← elabInternalNativeByTerm target flatSig #[] params typeExpr bodyStx.raw steps
      elabLeanQuotedInternalTheoremCheckedExpr doc? declNameStx declName params typeExpr
        valueExpr "internal theorem := by (native)"
      return ()
  let valueExpr ← elabLeanQuotedLFBody target params typeExpr bodyStx
  compareLeanQuotedBodyWithLegacyIfEnabled .judgmentTheorem `compareLegacyInternalTheorem
    declName target params typeExpr valueExpr bodyStx
  saveLeanQuotedLFBodyInfo target params typeExpr bodyStx.raw
  elabLeanQuotedInternalTheoremCheckedExpr doc? declNameStx declName params typeExpr valueExpr

/-- Elaborate a legacy-parsed `internal def ... := by` block through native tactic mode when the
native option is enabled.  This lets borrowed Lean spellings such as `exact h` and `intro x` use
the canonical quoted frontend instead of the compatibility object-tactic compiler. -/
def elabNativeInternalDefByFromParsedTactics
    (doc? : Option (TSyntax ``Parser.Command.docComment)) (declNameStx : Syntax)
    (declName : Name) (levels : Array Name) (binders : TSyntaxArray `ttBinder)
    (typeStx : TSyntax `ttExpr) (tactics : TSyntaxArray `internalTactic) : CommandElabM Unit := do
  unless (← liftCoreM internalNativeTacticModeEnabled) do
    throwUnsupportedSyntax
  let steps ← tactics.mapM fun tac => parseInternalNativeLeanTacticFromSource tac.raw
  let stepSyntax := steps.map (·.raw)
  if internalNativeStepsContainDirectSorry stepSyntax then
    elabInternalDefSorryWithBinders doc? declNameStx declName levels binders typeStx
    return ()
  let target ← resolveInternalDefTarget declName
  let params ← binders.mapM elabHLBinding
  let typeExpr ← elabObjExpr typeStx
  let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target params typeExpr
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let bodyRef := (tactics[0]?).map (·.raw) |>.getD declNameStx
  let valueExpr ← elabInternalNativeByTerm target flatSig levels params typeExpr bodyRef stepSyntax
  if params.isEmpty then
    elabInternalDefCheckedExpr doc? declNameStx declName levels typeExpr valueExpr
      "internal def := by (native)"
  else
    elabInternalDefCheckedWithBindersExpr doc? declNameStx declName levels params typeExpr
      valueExpr "internal def := by (native)"

elab_rules (kind := internalDefBy) : command
  | `($[$doc?:docComment]? internal def $declName:ident : $typeStx:ttExpr := by
      $tactics:internalTactic*) =>
      elabNativeInternalDefByFromParsedTactics doc? declName declName.getId #[] #[] typeStx
        tactics

elab_rules (kind := internalDefLevelBy) : command
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*} : $typeStx:ttExpr :=
      by $tactics:internalTactic*) =>
      elabNativeInternalDefByFromParsedTactics doc? declName declName.getId
        (levels.getElems.map (·.getId)) #[] typeStx tactics

elab_rules (kind := internalDefBinderBy) : command
  | `($[$doc?:docComment]? internal def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := by $tactics:internalTactic*) =>
      elabNativeInternalDefByFromParsedTactics doc? declName declName.getId #[] binders typeStx
        tactics

elab_rules (kind := internalDefLevelBinderBy) : command
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*}
      $binders:ttBinder* : $typeStx:ttExpr := by $tactics:internalTactic*) =>
      elabNativeInternalDefByFromParsedTactics doc? declName declName.getId
        (levels.getElems.map (·.getId)) binders typeStx tactics

/-- Elaborate one `internal_defs where` Lean-term declaration through the quoted frontend. -/
partial def elabLeanQuotedInternalDefsDecl (decl : TSyntax `internalDefsDecl) :
    CommandElabM Unit := do
  if decl.raw.isOfKind choiceKind then
    let mut last? : Option Exception := none
    for alt in decl.raw.getArgs do
      try
        withRestoredCommandStateOnError <| elabLeanQuotedInternalDefsDecl ⟨alt⟩
        return ()
      catch ex =>
        last? := some ex
    match last? with
    | some ex => throw ex
    | none => throwError "unsupported internal_defs declaration:{indentD decl}"
  match decl with
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident : $typeStx:ttExpr := by
      $tactics:internalTactic*) =>
      elabInternalDefBy doc? declName declName.getId #[] typeStx tactics
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := by $tactics:internalTactic*) =>
      elabInternalDefByWithBinders doc? declName declName.getId #[] binders typeStx tactics
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalDefSorry doc? declName declName.getId #[] typeStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      elabInternalDefSorryWithBinders doc? declName declName.getId #[] binders typeStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident : $typeStx:ttExpr :=
      $bodyStx:term) => do
      elabCanonicalLeanQuotedDefChecked doc? declName declName.getId #[] #[] typeStx bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $bodyStx:term) => do
      let params ← binders.mapM elabHLBinding
      elabCanonicalLeanQuotedDefChecked doc? declName declName.getId binders params typeStx
        bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx
  | stx => throwError "unsupported internal_defs declaration:{indentD stx}"

/-- Elaborate an `internal_defs where` block, preserving consecutive opaque-admission batches. -/
def elabLeanQuotedInternalDefsDeclsWithSorryOpaqueBatches
    (decls : Array (TSyntax `internalDefsDecl)) : CommandElabM Unit := do
  let flush (items : Array InternalDefsSorryBatchItem) : CommandElabM Unit := do
    if items.isEmpty then
      return ()
    let theoryName := items[0]!.target.theoryName
    let requests := items.map fun item =>
      ({ localName := item.target.localName
         anchorName := item.target.anchorName
         params := item.params
         typeExpr := item.typeExpr } : AdmittedInternalLFOpaqueRequest)
    liftCoreM <| registerAdmittedInternalLFOpaqueBatch theoryName requests
    for item in items do
      if let some doc := item.sourceDoc? then
        liftCoreM <| registerSourceDoc item.target.theoryName .internalDef
          item.target.localName doc
      addInternalDeclarationAnchor item.target item.typeExpr .admittedLFOpaque item.params none
        "internal_defs admitted opaque batch" item.sourceDoc? item.declStx item.declNameStx
      addInternalDefsDeclNavigationInfo item.target.theoryName item.declStx
      logWarning m!"internal declaration '{item.target.anchorName}' was admitted by `sorry`; the \
        annotation was checked in theory '{item.target.theoryName}', but the body was not \
        checked. Use `#lint_type_theory_sorries {item.target.theoryName}` to list current \
        admissions."
    refreshLFMirrorAfterInternalRegistration theoryName
  let mut batch : Array InternalDefsSorryBatchItem := #[]
  for decl in decls do
    match ← elabInternalDefsSorryBatchItem? decl with
    | some item =>
        match ← liftCoreM <| classifyInternalSorryAdmissionShape item.target.theoryName
            item.target.localName item.params item.typeExpr with
        | .lfOpaque =>
            if let some first := batch[0]? then
              if first.target.theoryName != item.target.theoryName then
                flush batch
                batch := #[]
            let localName := item.target.localName.eraseMacroScopes
            if batch.any (fun old => old.target.localName.eraseMacroScopes == localName) then
              throwError "duplicate internal_defs declaration '{item.target.localName}' in type \
                theory '{item.target.theoryName}'"
            batch := batch.push item
        | .judgmentTheorem | .unsupported _ =>
            flush batch
            batch := #[]
            elabLeanQuotedInternalDefsDecl decl
    | none =>
        flush batch
        batch := #[]
        elabLeanQuotedInternalDefsDecl decl
  flush batch

elab_rules (kind := internalDefsBlock) : command
  | `(internal_defs where $decls:internalDefsDecl*) => do
      unless ← tryElabInternalDefsSorryOpaqueBatch decls do
        elabLeanQuotedInternalDefsDeclsWithSorryOpaqueBatches decls

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
syntax (name := internalLeanQuotedTheorem)
  docComment ? "internal_lean " "theorem " ident " : " ttExpr " := " term : command
syntax (name := internalLeanQuotedTheoremBinder)
  docComment ? "internal_lean " "theorem " ident ttBinder+ " : " ttExpr " := " term : command
syntax (name := internalLeanQuotedTheoremSorry)
  docComment ? "internal_lean " "theorem " ident " : " ttExpr " := " "sorry" : command
syntax (name := internalLeanQuotedTheoremBinderSorry)
  docComment ? "internal_lean " "theorem " ident ttBinder+ " : " ttExpr " := " "sorry" : command
syntax (name := internalLeanQuotedTheoremBySorry)
  docComment ? "internal_lean " "theorem " ident " : " ttExpr " := " "by" ppLine
    "sorry" : command
syntax (name := internalLeanQuotedTheoremBinderBySorry)
  docComment ? "internal_lean " "theorem " ident ttBinder+ " : " ttExpr " := " "by" ppLine
    "sorry" : command

elab_rules (kind := declareInternalLeanWhere) : command
  | `($[$doc?:docComment]? declare_type_theory $nm:ident where $decls:ttDecl*) => do
      elabDeclareInternalLeanQuoted doc? nm #[] #[] decls

elab_rules (kind := declareInternalLeanLevelWhere) : command
  | `($[$doc?:docComment]? declare_type_theory $nm:ident {$levels:ident,*} where
      $decls:ttDecl*) => do
      elabDeclareInternalLeanQuoted doc? nm (levels.getElems.map (·.getId)) #[] decls

elab_rules (kind := declareInternalLeanExtendsWhere) : command
  | `($[$doc?:docComment]? declare_type_theory $nm:ident extends $parents:ident,* where
      $decls:ttDecl*) => do
      elabDeclareInternalLeanQuoted doc? nm #[] (parents.getElems.map (·.getId)) decls

elab_rules (kind := declareInternalLeanLevelExtendsWhere) : command
  | `($[$doc?:docComment]? declare_type_theory $nm:ident {$levels:ident,*} extends
      $parents:ident,* where $decls:ttDecl*) => do
      elabDeclareInternalLeanQuoted doc? nm (levels.getElems.map (·.getId))
        (parents.getElems.map (·.getId)) decls

elab_rules (kind := extendInternalLeanWhere) : command
  | `($[$doc?:docComment]? extend_type_theory $nm:ident where $decls:ttDecl*) => do
      elabExtendInternalLeanQuoted doc? nm decls

elab_rules (kind := internalDef) : command
  | `($[$doc?:docComment]? internal def $declName:ident : $typeStx:ttExpr :=
      $bodyStx:term) => do
      elabCanonicalLeanQuotedDefChecked doc? declName declName.getId #[] #[] typeStx bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx

elab_rules (kind := internalDefBinderUnsupported) : command
  | `($[$doc?:docComment]? internal def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $bodyStx:term) => do
      let params ← binders.mapM elabHLBinding
      elabCanonicalLeanQuotedDefChecked doc? declName declName.getId binders params typeStx
        bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx

elab_rules (kind := internalTheorem) : command
  | `($[$doc?:docComment]? internal theorem $declName:ident : $typeStx:ttExpr :=
      $bodyStx:term) => do
      elabCanonicalLeanQuotedTheoremChecked doc? declName declName.getId #[] #[] typeStx
        bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx

elab_rules (kind := internalTheoremBinder) : command
  | `($[$doc?:docComment]? internal theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $bodyStx:term) => do
      let params ← binders.mapM elabHLBinding
      elabCanonicalLeanQuotedTheoremChecked doc? declName declName.getId binders params typeStx
        bodyStx
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx

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

elab_rules (kind := internalLeanQuotedTheoremSorry) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] #[] typeStx

elab_rules (kind := internalLeanQuotedTheoremBinderSorry) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] binders typeStx

elab_rules (kind := internalLeanQuotedTheoremBySorry) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident : $typeStx:ttExpr := by
      sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] #[] typeStx

elab_rules (kind := internalLeanQuotedTheoremBinderBySorry) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := by
      sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] binders typeStx

elab_rules (kind := internalLeanQuotedTheorem) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident : $typeStx:ttExpr :=
      $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let typeExpr ← elabObjExpr typeStx
      let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target #[] typeExpr
      saveLeanQuotedLFBodyInfo target params typeExpr body
      let valueExpr ← elabLeanQuotedLFBody target params typeExpr body
      elabLeanQuotedInternalTheoremCheckedExpr doc? declName declName.getId params typeExpr
        valueExpr "internal_lean theorem"
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedTheoremBinder) : command
  | `($[$doc?:docComment]? internal_lean theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let params ← binders.mapM elabHLBinding
      let typeExpr ← elabObjExpr typeStx
      let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target params typeExpr
      saveLeanQuotedLFBodyInfo target params typeExpr body
      let valueExpr ← elabLeanQuotedLFBody target params typeExpr body
      elabLeanQuotedInternalTheoremCheckedExpr doc? declName declName.getId params typeExpr
        valueExpr "internal_lean theorem"
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx

elab_rules (kind := internalLeanQuotedDef) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident : $typeStx:ttExpr :=
      $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let typeExpr ← elabObjExpr typeStx
      let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target #[] typeExpr
      saveLeanQuotedLFBodyInfo target params typeExpr body
      let valueExpr ← elabLeanQuotedLFBody target params typeExpr body
      elabInternalDefCheckedExpr doc? declName declName.getId #[] typeExpr valueExpr
        "internal_lean def"
      addInternalDefAnnotationNavigationInfo declName.getId #[] typeStx

elab_rules (kind := internalLeanQuotedDefBinder) : command
  | `($[$doc?:docComment]? internal_lean def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $body:term) => do
      let target ← resolveInternalDefTarget declName.getId
      let params ← binders.mapM elabHLBinding
      let typeExpr ← elabObjExpr typeStx
      let (params, typeExpr) ← elaborateLeanQuotedHeaderImplicits target params typeExpr
      saveLeanQuotedLFBodyInfo target params typeExpr body
      let valueExpr ← elabLeanQuotedLFBody target params typeExpr body
      elabInternalDefCheckedWithBindersExpr doc? declName declName.getId #[] params typeExpr
        valueExpr "internal_lean def"
      addInternalDefAnnotationNavigationInfo declName.getId binders typeStx

end InternalLean
