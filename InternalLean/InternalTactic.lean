/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Registration
public meta import Lean.PrettyPrinter

/-!
# Internal object tactics

This file contains the parser, elaborator, diagnostics, and infoview support for
`internal def ... := by` object-theory tactic scripts.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

declare_syntax_cat internalTactic
declare_syntax_cat internalTacticArg
declare_syntax_cat internalRwItem

syntax "_" : internalTacticArg
syntax "?_" : internalTacticArg
syntax ident : internalTacticArg
syntax "(" ident internalTacticArg* ")" : internalTacticArg
syntax "(" ttExpr ")" : internalTacticArg
syntax ident : internalRwItem
syntax "← " ident : internalRwItem
syntax (name := internalTacticExactSorry) "exact " "sorry" : internalTactic
syntax (name := internalTacticExactApp) "exact " ident internalTacticArg* : internalTactic
syntax (name := internalTacticExact) "exact " ttExpr : internalTactic
syntax (name := internalTacticApply) "apply " ident : internalTactic
syntax (name := internalTacticAssumption) "assumption" : internalTactic
syntax (name := internalTacticShow) "show " ttExpr : internalTactic
syntax (name := internalTacticChange) "change " ttExpr : internalTactic
syntax (name := internalTacticRw) "rw " ident : internalTactic
syntax (name := internalTacticRwRev) "rw " "← " ident : internalTactic
syntax (name := internalTacticRwSeq) "rw " "[" internalRwItem,* "]" : internalTactic
syntax (name := internalTacticSimp) "simp" : internalTactic
syntax (name := internalTacticSimpList) "simp " "[" ident,* "]" : internalTactic
syntax (name := internalTacticSimpOnly) "simp " "only " "[" ident,* "]" : internalTactic
syntax (name := internalTacticIntros) "intros " ident+ : internalTactic
syntax (name := internalTacticHave) "have " ident " : " ttExpr " := " "by" ppLine
  internalTactic* "end" : internalTactic
syntax (name := internalTacticHaveTerm) "have " ident " : " ttExpr " := " ttExpr : internalTactic
syntax (name := internalTacticHaveMissingEnd) "have " ident " : " ttExpr " := " "by" ppLine
  internalTactic* : internalTactic
syntax (name := internalTacticRefineApp) "refine " ident internalTacticArg* : internalTactic
syntax (name := internalTacticRefine) "refine " ttExpr : internalTactic
syntax (name := internalTacticFocus) "·" : internalTactic
syntax (name := internalTacticIdentArg) ident ident : internalTactic
syntax (name := internalTacticSorry) "sorry" : internalTactic

syntax (name := internalDef)
  docComment ? "internal " "def " ident " : " ttExpr " := " ttExpr : command
syntax (name := internalDefLevel)
  docComment ? "internal " "def " ident "{" ident,* "}" " : " ttExpr " := " ttExpr : command
syntax (name := internalDefBy)
  docComment ? "internal " "def " ident " : " ttExpr " := " "by" ppLine internalTactic* : command
syntax (name := internalDefLevelBy)
  docComment ? "internal " "def " ident "{" ident,* "}" " : " ttExpr " := " "by" ppLine
    internalTactic* : command
syntax (name := internalDefSorry)
  docComment ? "internal " "def " ident " : " ttExpr " := " "sorry" : command
syntax (name := internalDefLevelSorry)
  docComment ? "internal " "def " ident "{" ident,* "}" " : " ttExpr " := " "sorry" : command
syntax (name := internalDefBinderBy)
  docComment ? "internal " "def " ident ttBinder+ " : " ttExpr " := " "by" ppLine
    internalTactic* : command
syntax (name := internalDefLevelBinderBy)
  docComment ? "internal " "def " ident "{" ident,* "}" ttBinder+ " : " ttExpr " := " "by"
    ppLine internalTactic* : command
syntax (name := internalDefBinderUnsupported)
  docComment ? "internal " "def " ident ttBinder+ " : " ttExpr " := " ttExpr : command
syntax (name := internalTheorem)
  docComment ? "internal " "theorem " ident " : " ttExpr " := " ttExpr : command
syntax (name := internalTheoremSorry)
  docComment ? "internal " "theorem " ident " : " ttExpr " := " "sorry" : command
syntax (name := internalTheoremBinder)
  docComment ? "internal " "theorem " ident ttBinder+ " : " ttExpr " := " ttExpr : command
syntax (name := internalTheoremBinderSorry)
  docComment ? "internal " "theorem " ident ttBinder+ " : " ttExpr " := " "sorry" : command
syntax (name := internalDefLevelBinderUnsupported)
  docComment ? "internal " "def " ident "{" ident,* "}" ttBinder+ " : " ttExpr " := " ttExpr :
    command

declare_syntax_cat internalDefsDecl
syntax (name := internalDefsDeclChecked)
  docComment ? "def " ident " : " ttExpr " := " ttExpr : internalDefsDecl
syntax (name := internalDefsDeclSorry)
  docComment ? "def " ident " : " ttExpr " := " "sorry" : internalDefsDecl
syntax (name := internalDefsDeclBinderChecked)
  docComment ? "def " ident ttBinder+ " : " ttExpr " := " ttExpr : internalDefsDecl
syntax (name := internalDefsDeclBinderSorry)
  docComment ? "def " ident ttBinder+ " : " ttExpr " := " "sorry" : internalDefsDecl
syntax (name := internalDefsDeclBy)
  docComment ? "def " ident " : " ttExpr " := " "by" ppLine internalTactic* : internalDefsDecl
syntax (name := internalDefsDeclBinderBy)
  docComment ? "def " ident ttBinder+ " : " ttExpr " := " "by" ppLine internalTactic* :
    internalDefsDecl
syntax (name := internalDefsBlock) "internal_defs" "where" ppLine internalDefsDecl* : command

/-- Reject `internal def` binder sugar when no profile-specific elaborator accepts it. -/
def throwInternalDefBinderUnsupported (declName : Name) : CommandElabM α :=
  throwError "unsupported binder syntax in `internal def` for '{declName}'\n\nBinder syntax is \
    profile-specific sugar and no generic LF binder elaborator is installed. Direct LF \
      definitions/theorems must use an explicit object judgment/type after `:` and an explicit \
        proof/body."

/-- Wrap a result type in a telescope of explicit object arrows. -/
def objectArrowTelescope (binders : Array HLBinding) (result : ObjExpr) : ObjExpr :=
  binders.foldr (init := result) fun b acc => .arrow (some b.name) b.typeExpr acc

/-- Wrap a body in object lambdas for a binder telescope. -/
def objectLambdaTelescope (binders : Array HLBinding) (body : ObjExpr) : ObjExpr :=
  if binders.isEmpty then body else .lam (binders.map (·.name)) body

/-- Extract user-facing message data from an elaboration exception. -/
def exceptionMessageData : Exception → MessageData
  | .error _ msg => msg
  | .internal _ _ => m!"internal exception"

/-- One tactic-only argument in an object `exact`/`refine` head application. -/
inductive InternalTacticArg where
  | expr : ObjExpr → InternalTacticArg
  | inferPlaceholder : InternalTacticArg
  | refineHole : InternalTacticArg
  | app : Name → Array InternalTacticArg → InternalTacticArg
  deriving Inhabited, Repr

/-- One parsed step in the minimal object tactic language for `internal def ... := by`. -/
inductive InternalTacticStep where
  | exactTerm : ObjExpr → InternalTacticStep
  | exactApp : Name → Array InternalTacticArg → InternalTacticStep
  | applyName : Name → InternalTacticStep
  | assumption : InternalTacticStep
  | showGoal : ObjExpr → InternalTacticStep
  | changeGoal : ObjExpr → InternalTacticStep
  | rwRule : Name → Bool → InternalTacticStep
  | rwRules : Array (Name × Bool) → InternalTacticStep
  | simp : InternalTacticStep
  | simpRules : Array Name → Bool → InternalTacticStep
  | refineTerm : ObjExpr → InternalTacticStep
  | refineApp : Name → Array InternalTacticArg → InternalTacticStep
  | focusBullet : InternalTacticStep
  | intro : Name → InternalTacticStep
  | intros : Array Name → InternalTacticStep
  | haveDecl : Name → ObjExpr → Array InternalTacticStep → InternalTacticStep
  | haveTerm : Name → ObjExpr → ObjExpr → InternalTacticStep
  | haveMissingEnd : Name → InternalTacticStep
  | sorry : InternalTacticStep
  deriving Inhabited, Repr

/-- Parse one tactic-only object argument, distinguishing inference placeholders from holes. -/
partial def elabInternalTacticArg : TSyntax `internalTacticArg → CommandElabM InternalTacticArg
  | stx => do
      if stx.raw.getKind == `choice then
        let mut lastMsg : MessageData :=
          m!"unsupported internal object tactic argument syntax:{indentD stx}"
        for alt in stx.raw.getArgs do
          try
            return (← elabInternalTacticArg ⟨alt⟩)
          catch ex =>
            lastMsg := exceptionMessageData ex
        throwError lastMsg
      else
        match stx with
        | `(internalTacticArg| _) => pure .inferPlaceholder
        | `(internalTacticArg| ?_) => pure .refineHole
        | `(internalTacticArg| $x:ident) => pure <| .expr (.ident x.getId)
        | `(internalTacticArg| ($head:ident $args:internalTacticArg*)) => do
            if args.isEmpty then
              pure <| .expr (.ident head.getId)
            else
              pure <| .app head.getId (← args.mapM elabInternalTacticArg)
        | `(internalTacticArg| ($e:ttExpr)) => do pure <| .expr (← elabObjExpr e)
        | _ => throwError "unsupported internal object tactic argument syntax:{indentD stx}"

/-- Parse one object rewrite item. -/
def elabInternalRwItem : TSyntax `internalRwItem → CommandElabM (Name × Bool)
  | stx => do
      match stx with
      | `(internalRwItem| $n:ident) => pure (n.getId, false)
      | `(internalRwItem| ← $n:ident) => pure (n.getId, true)
      | _ => throwError "unsupported internal object rewrite item syntax:{indentD stx}"

/-- Parse an internal object tactic. -/
partial def elabInternalTacticStep : TSyntax `internalTactic → CommandElabM InternalTacticStep
  | stx => do
      if stx.raw.getKind == `choice then
        let mut lastMsg : MessageData := m!"unsupported internal object tactic syntax:{indentD stx}"
        for alt in stx.raw.getArgs do
          try
            return (← elabInternalTacticStep ⟨alt⟩)
          catch ex =>
            lastMsg := exceptionMessageData ex
        throwError lastMsg
      else
        match stx with
        | `(internalTactic| exact sorry) => pure .sorry
        | `(internalTactic| exact $head:ident $args:internalTacticArg*) => do
            pure <| .exactApp head.getId (← args.mapM elabInternalTacticArg)
        | `(internalTactic| exact $e:ttExpr) => do pure <| .exactTerm (← elabObjExpr e)
        | `(internalTactic| apply $n:ident) => pure <| .applyName n.getId
        | `(internalTactic| assumption) => pure .assumption
        | `(internalTactic| show $e:ttExpr) => do pure <| .showGoal (← elabObjExpr e)
        | `(internalTactic| change $e:ttExpr) => do pure <| .changeGoal (← elabObjExpr e)
        | `(internalTactic| rw $n:ident) => pure <| .rwRule n.getId false
        | `(internalTactic| rw ← $n:ident) => pure <| .rwRule n.getId true
        | `(internalTactic| rw [$items:internalRwItem,*]) => do
            pure <| .rwRules (← items.getElems.mapM elabInternalRwItem)
        | `(internalTactic| simp) => pure .simp
        | `(internalTactic| simp [$rules:ident,*]) =>
            pure <| .simpRules (rules.getElems.map (·.getId)) false
        | `(internalTactic| simp only [$rules:ident,*]) =>
            pure <| .simpRules (rules.getElems.map (·.getId)) true
        | `(internalTactic| refine $head:ident $args:internalTacticArg*) => do
            pure <| .refineApp head.getId (← args.mapM elabInternalTacticArg)
        | `(internalTactic| refine $e:ttExpr) => do pure <| .refineTerm (← elabObjExpr e)
        | `(internalTactic| intros $ns:ident*) => pure <| .intros (ns.map (·.getId))
        | `(internalTactic| have $n:ident : $type:ttExpr := by $body:internalTactic* end) => do
            pure <| .haveDecl n.getId (← elabObjExpr type) (← body.mapM elabInternalTacticStep)
        | `(internalTactic| have $n:ident : $type:ttExpr := $proof:ttExpr) => do
            pure <| .haveTerm n.getId (← elabObjExpr type) (← elabObjExpr proof)
        | `(internalTactic| have $n:ident : $type:ttExpr := by $body:internalTactic*) => do
            let _ := type
            let _ := body
            pure <| .haveMissingEnd n.getId
        | `(internalTactic| ·) => pure .focusBullet
        | `(internalTactic| $kw:ident $n:ident) =>
            if kw.getId.eraseMacroScopes == `intro then
              pure <| .intro n.getId
            else
              throwError "unsupported internal object tactic \
                '{kw.getId.eraseMacroScopes}'{indentD kw.raw}"
        | `(internalTactic| sorry) => pure .sorry
        | _ => throwError "unsupported internal object tactic syntax:{indentD stx}"

/-- Compare object expressions modulo macro scopes on names. -/
partial def objectExprEq (a b : ObjExpr) : Bool :=
  match a, b with
  | .ident n, .ident m => sameObjectName n m
  | .sort, .sort => true
  | .univ u, .univ v => u == v
  | .app f x, .app g y => objectExprEq f g && objectExprEq x y
  | .arrow x A B, .arrow y A' B' | .funArrow x A B, .funArrow y A' B' =>
      x.map (·.eraseMacroScopes) == y.map (·.eraseMacroScopes) && objectExprEq A A'
        && objectExprEq B B'
  | .arrow x A B, .funArrow y A' B' | .funArrow x A B, .arrow y A' B' =>
      x.map (·.eraseMacroScopes) == y.map (·.eraseMacroScopes) && objectExprEq A A'
        && objectExprEq B B'
  | .lam xs body, .lam ys body' =>
      xs.map (·.eraseMacroScopes) == ys.map (·.eraseMacroScopes) && objectExprEq body body'
  | .jeq l r, .jeq l' r' => objectExprEq l l' && objectExprEq r r'
  | _, _ => false

/-- Substitute named object variables in an object expression, alpha-renaming binders as needed. -/
def substObjectVars (subst : NameMap ObjExpr) (e : ObjExpr) : ObjExpr :=
  substLFParams subst e

/-- Match a pattern against an object expression, treating selected names as pattern variables. -/
partial def matchObjectPattern (vars : NameSet) (pattern actual : ObjExpr)
    (subst : NameMap ObjExpr) : Option (NameMap ObjExpr) :=
  match pattern with
  | .ident n =>
      let key := n.eraseMacroScopes
      if vars.contains key then
        match subst.find? key with
        | none => some (subst.insert key actual)
        | some old => if objectExprEq old actual then some subst else none
      else
        match actual with
        | .ident m => if sameObjectName n m then some subst else none
        | _ => none
  | .sort => match actual with | .sort => some subst | _ => none
  | .univ u => match actual with | .univ v => if u == v then some subst else none | _ => none
  | .app f a =>
      match actual with
      | .app g b => do
          let subst ← matchObjectPattern vars f g subst
          matchObjectPattern vars a b subst
      | _ => none
  | .arrow x A B =>
      match actual with
      | .arrow y A' B' | .funArrow y A' B' =>
          if x.map (·.eraseMacroScopes) == y.map (·.eraseMacroScopes) then do
            let subst ← matchObjectPattern vars A A' subst
            matchObjectPattern vars B B' subst
          else none
      | _ => none
  | .funArrow x A B =>
      match actual with
      | .arrow y A' B' | .funArrow y A' B' =>
          if x.map (·.eraseMacroScopes) == y.map (·.eraseMacroScopes) then do
            let subst ← matchObjectPattern vars A A' subst
            matchObjectPattern vars B B' subst
          else none
      | _ => none
  | .lam xs body =>
      match actual with
      | .lam ys body' =>
          if xs.map (·.eraseMacroScopes) == ys.map (·.eraseMacroScopes) then
            matchObjectPattern vars body body' subst
          else none
      | _ => none
  | .jeq l r =>
      match actual with
      | .jeq l' r' => do
          let subst ← matchObjectPattern vars l l' subst
          matchObjectPattern vars r r' subst
      | _ => none

/-- Split an object function/judgment telescope into binders and a final result. -/
partial def splitObjectTelescope : ObjExpr → Array HLBinding × ObjExpr
  | .arrow x A B | .funArrow x A B =>
      let binderName := x.getD `_arg
      let (bs, result) := splitObjectTelescope B
      (#[{ name := binderName, typeExpr := A, visibility := .explicit }] ++ bs, result)
  | e => (#[], e)

/-- Build an object application. -/
def mkObjectApps (head : ObjExpr) (args : Array ObjExpr) : ObjExpr :=
  args.foldl (init := head) fun acc arg => .app acc arg

/-- A side-condition obligation exposed by object tactics when applying an LF rule. -/
structure InternalTacticSideCondition where
  name : Name
  solver : Name
  input : ObjExpr
  deriving Inhabited, Repr, BEq

/-- A candidate that can be used by the minimal `apply` tactic. -/
structure InternalApplyCandidate where
  name : Name
  params : Array HLBinding := #[]
  conclusionExpr : ObjExpr
  subgoalTargets : Array ObjExpr := #[]
  sideConditions : Array InternalTacticSideCondition := #[]
  deriving Inhabited, Repr

/-- Drop a theory namespace prefix from a tactic identifier when it names an object declaration. -/
def internalTacticObjectName (target : InternalDefTarget) (n : Name) : Name :=
  if n.getPrefix.eraseMacroScopes == target.theoryName.eraseMacroScopes then
    nameLastComponent n
  else
    n

/-- Find declarations/rules usable by the minimal object `apply` tactic. -/
def findInternalApplyCandidate? (target : InternalDefTarget) (sig : HLSignature) (rawName : Name) :
  Option InternalApplyCandidate := Id.run do
  let n := internalTacticObjectName target rawName
  if let some d := sig.lfObjectDefs.find? (fun d => sameObjectName d.name n) then
    let (params, conclusionResult) := splitObjectTelescope d.typeExpr
    return some { name := n, params, conclusionExpr := conclusionResult }
  if let some c := sig.lfOpaqueConsts.find? (fun c => sameObjectName c.name n) then
    if let some typeExpr := c.typeExpr? then
      let (params, conclusionResult) := splitObjectTelescope typeExpr
      return some { name := n, params, conclusionExpr := conclusionResult }
  if let some thm := sig.lfJudgmentTheorems.find? (fun t => sameObjectName t.name n) then
    return some { name := n, params := thm.binders, conclusionExpr := thm.judgmentExpr }
  if let some ruleDecl := sig.rules.find? (fun r => sameObjectName r.name n) then
    let subgoals := ruleDecl.premises.map (fun prem => prem.judgmentExpr)
    let sideConditions := ruleDecl.sideConditions.map fun sc =>
      { name := sc.name, solver := sc.solver, input := sc.input }
    return some {
      name := n
      params := ruleDecl.params
      conclusionExpr := ruleDecl.conclusionExpr
      subgoalTargets := subgoals
      sideConditions := sideConditions
    }
  return none

/-- Checked LF-definition values available to object-tactic conversion. -/
def objectTacticLFDefinitionValues (sig : HLSignature) : LFDefinitionValueMap :=
  sig.lfObjectDefs.foldl (init := {}) fun defs d =>
    defs.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)

/-- Local object names that should block LF-definition unfolding under a tactic goal. -/
def internalObjectLocalNames (ctx : Array HLBinding) : NameSet :=
  ctx.foldl (init := {}) fun locals b => locals.insert b.name.eraseMacroScopes

/-- Convert high-level conversion-plugin metadata to the kernel-facing schema. -/
def conversionPluginDeclToKernelSchema (p : ConversionPluginDecl) : ConversionPluginSchema :=
  { name := p.name.eraseMacroScopes, trust := p.trust,
    supportedSteps := p.supportedSteps.toList }

/-- Kernel-facing plugin signature used by object-tactic conversion checks. -/
def objectConversionPluginSignature (sig : HLSignature) : Signature :=
  { name := sig.name.eraseMacroScopes,
    conversionPlugins := sig.conversionPlugins.toList.map conversionPluginDeclToKernelSchema }

/-- Raw conversion view of an object expression for generic plugin-step checking. -/
partial def objectExprToConversionRaw (sig : HLSignature) (locals : NameSet) : ObjExpr → Raw
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        .leanParam n
      else if sig.syntaxSorts.any (fun s => sameObjectName s.name n) then
        .tyConst n
      else
        .tmConst n
  | .sort => .tyConst `Type
  | .univ u => .tyApp `Type [.leanParam (.str .anonymous u.toString)]
  | e@(.app ..) =>
      let (head, args) := splitObjApp e
      let rawArgs := args.toList.map (objectExprToConversionRaw sig locals)
      match head with
      | .ident n =>
          let n := n.eraseMacroScopes
          if sig.syntaxSorts.any (fun s => sameObjectName s.name n) then
            .tyApp n rawArgs
          else
            .tmApp n rawArgs
      | other => .tmApp `_app (objectExprToConversionRaw sig locals other :: rawArgs)
  | .arrow _ A B =>
      .tyApp `arrow [objectExprToConversionRaw sig locals A, objectExprToConversionRaw sig locals B]
  | .funArrow _ A B =>
      .tyApp `arrow [objectExprToConversionRaw sig locals A, objectExprToConversionRaw sig locals B]
  | .lam xs body =>
      let locals := xs.foldl (fun acc x => acc.insert x.eraseMacroScopes) locals
      .tmApp `lam ((xs.toList.map fun x => Raw.leanParam x.eraseMacroScopes) ++
        [objectExprToConversionRaw sig locals body])
  | .jeq lhs rhs =>
      .tmApp `jeq [objectExprToConversionRaw sig locals lhs,
        objectExprToConversionRaw sig locals rhs]

/-- Validate one object conversion plugin step through the kernel-facing checker. -/
def checkObjectConversionPluginStep (sig : HLSignature) (ctx : Array HLBinding)
    (pluginName : Name) (kind : ConversionStepKind) (lhs rhs : ObjExpr) : Except String Unit := do
  let locals := internalObjectLocalNames ctx
  let stmt : ConversionStatement := {
    plugin := pluginName.eraseMacroScopes,
    lhs := objectExprToConversionRaw sig locals lhs,
    rhs := objectExprToConversionRaw sig locals rhs }
  let cert := KernelLFConversionCertificate.pluginStep stmt kind none [] "object tactic simp"
  KernelLFConversionCertificate.check (objectConversionPluginSignature sig) cert stmt

/-- Checked object-conversion step kind used by direct-LF tactics. -/
inductive LFObjectConversionStepKind where
  /-- Endpoints are syntactically identical modulo object-name scopes. -/
  | syntacticRefl
  /-- Endpoints agree after bounded unfolding of checked LF definitions. -/
  | lfDefinitionUnfolding
  deriving Inhabited, Repr, BEq

namespace LFObjectConversionStepKind

/-- User-facing label for an object-conversion step kind. -/
def label : LFObjectConversionStepKind → String
  | .syntacticRefl => "syntactic_refl"
  | .lfDefinitionUnfolding => "lf_definition_unfolding"

end LFObjectConversionStepKind

/-- One checked direct-LF object-conversion step. -/
structure LFObjectConversionStep where
  /-- Step class. -/
  kind : LFObjectConversionStepKind
  /-- Source endpoint before this step. -/
  lhs : ObjExpr
  /-- Target endpoint after this step. -/
  rhs : ObjExpr
  /-- LF definitions actually unfolded while checking this step. -/
  unfoldedDefinitions : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- Result certificate produced by the direct-LF object conversion checker. -/
structure CheckedLFObjectConversion where
  /-- Source endpoint requested by the caller. -/
  lhs : ObjExpr
  /-- Target endpoint requested by the caller. -/
  rhs : ObjExpr
  /-- Normalized source endpoint under the bounded LF-definition policy. -/
  normalizedLhs : ObjExpr
  /-- Normalized target endpoint under the bounded LF-definition policy. -/
  normalizedRhs : ObjExpr
  /-- Explicit checked steps that justify the conversion. -/
  steps : Array LFObjectConversionStep := #[]
  /-- Local names that blocked LF-definition unfolding in older checker versions. -/
  blockedLocalNames : Array Name := #[]
  /-- Definition heads still present after bounded unfolding. -/
  remainingDefinitionHeads : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- Check object goals through the direct-LF conversion interface. -/
def checkObjectGoalConversion (sig : HLSignature) (_levels : Array Name) (ctx : Array HLBinding)
    (a b : ObjExpr) : Except String CheckedLFObjectConversion :=
  let defs := objectTacticLFDefinitionValues sig
  let locals := internalObjectLocalNames ctx
  let aN := unfoldLFDefinitionsInExprWithLocals defs locals a
  let bN := unfoldLFDefinitionsInExprWithLocals defs locals b
  let blocked : Array Name := #[]
  let remaining := collectLFDefinitionMentions defs locals #[] aN
  let remaining := collectLFDefinitionMentions defs locals remaining bN
  if objectExprEq a b then
    .ok {
      lhs := a, rhs := b, normalizedLhs := aN, normalizedRhs := bN,
      steps := #[{ kind := .syntacticRefl, lhs := a, rhs := b }],
      blockedLocalNames := blocked, remainingDefinitionHeads := remaining }
  else if lfExprAlphaEq aN bN then
    let unfolded := collectLFDefinitionUnfolds defs locals #[] a
    let unfolded := collectLFDefinitionUnfolds defs locals unfolded b
    .ok {
      lhs := a, rhs := b, normalizedLhs := aN, normalizedRhs := bN,
      steps := #[{
        kind := .lfDefinitionUnfolding, lhs := a, rhs := b,
        unfoldedDefinitions := unfolded }],
      blockedLocalNames := blocked, remainingDefinitionHeads := remaining }
  else
    .error "unsupported LF conversion: endpoints are not syntactically identical and do not \
      match after bounded checked LF-definition unfolding"

/-- Check object goals modulo exact syntax and checked LF definitions. -/
def objectGoalConversionCheck (sig : HLSignature) (levels : Array Name) (ctx : Array HLBinding)
    (a b : ObjExpr) : Except String Unit := do
  discard <| checkObjectGoalConversion sig levels ctx a b

/-- Compare object goals modulo exact syntax and checked LF definitions. -/
def objectGoalsConvertible (sig : HLSignature) (levels : Array Name) (ctx : Array HLBinding)
    (a b : ObjExpr) : Bool :=
  match checkObjectGoalConversion sig levels ctx a b with
  | .ok _ => true
  | .error _ => false

/-- Explain why two object goals were not accepted as LF-definition-convertible. -/
def objectGoalNormalizationMismatchString (sig : HLSignature) (ctx : Array HLBinding)
    (actual expected : ObjExpr) : String :=
  let defs := objectTacticLFDefinitionValues sig
  let locals := internalObjectLocalNames ctx
  let actualN := unfoldLFDefinitionsInExprWithLocals defs locals actual
  let expectedN := unfoldLFDefinitionsInExprWithLocals defs locals expected
  let mentioned := collectLFDefinitionMentions defs locals #[] actual
  let mentioned := collectLFDefinitionMentions defs locals mentioned expected
  let unfolded := collectLFDefinitionUnfolds defs locals #[] actual
  let unfolded := collectLFDefinitionUnfolds defs locals unfolded expected
  let remaining := collectLFDefinitionMentions defs locals #[] actualN
  let remaining := collectLFDefinitionMentions defs locals remaining expectedN
  let remainingLine :=
    if remaining.isEmpty then []
    else [s!"Definition head(s) still present after bounded unfolding: \
      {diagnosticNameListString remaining}"]
  String.intercalate "\n" <| [
    s!"normalized actual: {diagnosticObjExprString actualN}",
    s!"normalized expected: {diagnosticObjExprString expectedN}",
    s!"LF definitions mentioned before unfolding: {diagnosticNameListString mentioned}",
    s!"LF definitions unfolded: {diagnosticNameListString unfolded}"] ++
      remainingLine

/-- Split an object application into a head and spine. -/
partial def objectAppHeadAndArgs : ObjExpr → ObjExpr × Array ObjExpr
  | .app f a =>
      let (head, args) := objectAppHeadAndArgs f
      (head, args.push a)
  | e => (e, #[])

/-- Names of judgment forms marked as type/term conversion judgments. -/
def objectConversionJudgmentNames (sig : HLSignature) : NameSet := Id.run do
  let mut names : NameSet := {}
  for j in sig.judgments do
    let classes := conversionJudgmentClassesOfKinds (sig.judgmentRoleKinds j.name)
    if !classes.isEmpty then
      names := names.insert j.name.eraseMacroScopes
  return names

/-- Extract the two oriented endpoints from a conversion-judgment expression.

Prototype convention: a judgment marked `type_conversion` or `term_conversion` contributes its
last two arguments as the rewrite endpoints. This covers TinyNat and simple direct-LF smoke
tests; richer dependent term-conversion profiles can later provide explicit rewrite metadata. -/
def conversionJudgmentEndpoints? (conversionJudgments : NameSet) (e : ObjExpr) :
    Option (ObjExpr × ObjExpr) :=
  let (head, args) := objectAppHeadAndArgs e
  match head with
  | .ident n =>
      if conversionJudgments.contains n.eraseMacroScopes && args.size >= 2 then
        some (args[args.size - 2]!, args[args.size - 1]!)
      else
        none
  | _ => none

/-- A direct-LF rewrite candidate extracted from role metadata and conversion judgments. -/
structure LFObjectRewriteCandidate where
  /-- Rule or theorem name used by the tactic. -/
  name : Name
  /-- Pattern variables coming from a rule/theorem telescope. -/
  params : Array HLBinding := #[]
  /-- Source pattern. -/
  lhs : ObjExpr
  /-- Target pattern. -/
  rhs : ObjExpr
  /-- Judgment expression that provides evidence for the rewrite. -/
  evidenceExpr : ObjExpr
  /-- Whether the candidate was selected through a `rule_role ... : computation` marker. -/
  computationRole : Bool := false
  deriving Inhabited, Repr

/-- Direct-LF rewrite candidates available by name. -/
def findLFObjectRewriteCandidate? (target : InternalDefTarget) (sig : HLSignature)
    (rawName : Name) : Option LFObjectRewriteCandidate := Id.run do
  let n := internalTacticObjectName target rawName
  let conversionJudgments := objectConversionJudgmentNames sig
  if let some ruleDecl := sig.rules.find? (fun r => sameObjectName r.name n) then
    let classes := ruleAutomationClassesOfKinds (sig.ruleRoleKinds ruleDecl.name)
    if classes.contains .computation then
      if let some (lhs, rhs) := conversionJudgmentEndpoints? conversionJudgments
          ruleDecl.conclusionExpr then
        return some {
          name := n, params := ruleDecl.params, lhs := lhs, rhs := rhs,
          evidenceExpr := ruleDecl.conclusionExpr, computationRole := true }
  if let some thm := sig.lfJudgmentTheorems.find? (fun t => sameObjectName t.name n) then
    if let some (lhs, rhs) := conversionJudgmentEndpoints? conversionJudgments thm.judgmentExpr then
      return some {
        name := n, params := thm.binders, lhs := lhs, rhs := rhs,
        evidenceExpr := thm.judgmentExpr }
  return none

/-- Instantiate a rewrite endpoint using matched object-pattern variables. -/
def instantiateRewriteEndpoint (subst : NameMap ObjExpr) (e : ObjExpr) : ObjExpr :=
  substObjectVars subst e

/-- Rewrite the first matching subexpression in preorder and return the pattern match. -/
partial def rewriteFirstObjectSubexprWithSubst? (vars : NameSet) (lhs rhs target : ObjExpr) :
    Option (NameMap ObjExpr × ObjExpr) :=
  match matchObjectPattern vars lhs target {} with
  | some subst => some (subst, instantiateRewriteEndpoint subst rhs)
  | none =>
      match target with
      | .app f a =>
          match rewriteFirstObjectSubexprWithSubst? vars lhs rhs f with
          | some (subst, f') => some (subst, .app f' a)
          | none => do
              let (subst, a') ← rewriteFirstObjectSubexprWithSubst? vars lhs rhs a
              some (subst, .app f a')
      | .arrow x A B =>
          match rewriteFirstObjectSubexprWithSubst? vars lhs rhs A with
          | some (subst, A') => some (subst, .arrow x A' B)
          | none => do
              let (subst, B') ← rewriteFirstObjectSubexprWithSubst? vars lhs rhs B
              some (subst, .arrow x A B')
      | .funArrow x A B =>
          match rewriteFirstObjectSubexprWithSubst? vars lhs rhs A with
          | some (subst, A') => some (subst, .funArrow x A' B)
          | none => do
              let (subst, B') ← rewriteFirstObjectSubexprWithSubst? vars lhs rhs B
              some (subst, .funArrow x A B')
      | .lam xs body => do
          let (subst, body') ← rewriteFirstObjectSubexprWithSubst? vars lhs rhs body
          some (subst, .lam xs body')
      | .jeq l r =>
          match rewriteFirstObjectSubexprWithSubst? vars lhs rhs l with
          | some (subst, l') => some (subst, .jeq l' r)
          | none => do
              let (subst, r') ← rewriteFirstObjectSubexprWithSubst? vars lhs rhs r
              some (subst, .jeq l r')
      | .ident _ | .sort | .univ _ => none

/-- Rewrite the first matching subexpression in preorder. -/
def rewriteFirstObjectSubexpr? (vars : NameSet) (lhs rhs target : ObjExpr) :
    Option ObjExpr :=
  Prod.snd <$> rewriteFirstObjectSubexprWithSubst? vars lhs rhs target

/-- Build the pattern-variable set for a rewrite candidate. -/
def rewritePatternVars (cand : LFObjectRewriteCandidate) : NameSet :=
  cand.params.foldl (init := {}) fun vars b => vars.insert b.name.eraseMacroScopes

/-- One syntactic application of a direct-LF object rewrite candidate to a goal. -/
structure LFObjectRewriteApplication where
  /-- Selected rewrite candidate. -/
  candidate : LFObjectRewriteCandidate
  /-- Oriented source endpoint used for matching. -/
  lhs : ObjExpr
  /-- Oriented target endpoint used for replacement. -/
  rhs : ObjExpr
  /-- Whether the selected rewrite uses the reverse orientation. -/
  reversed : Bool := false
  /-- Pattern substitution produced by matching the source endpoint. -/
  rewriteSubst : NameMap ObjExpr
  /-- Goal before rewriting. -/
  oldGoal : ObjExpr
  /-- Goal after rewriting. -/
  newGoal : ObjExpr

/-- Checked evidence that one direct-LF object rewrite changed a tactic goal. -/
structure CheckedLFObjectRewrite where
  /-- Rule or theorem selected by the rewrite tactic. -/
  candidateName : Name
  /-- Oriented source endpoint used for matching. -/
  lhs : ObjExpr
  /-- Oriented target endpoint used for replacement. -/
  rhs : ObjExpr
  /-- Goal before rewriting. -/
  oldGoal : ObjExpr
  /-- Goal after rewriting. -/
  newGoal : ObjExpr
  /-- Checked conversion evidence that currently justifies changing the whole goal. -/
  conversion : CheckedLFObjectConversion
  deriving Inhabited, Repr

/-- Locate one direct-LF object-level rewrite candidate application to a goal target. -/
def findObjectRewriteApplication (target : InternalDefTarget) (sig : HLSignature)
    (goalTarget : ObjExpr) (rawName : Name) (symm : Bool) :
    Except String LFObjectRewriteApplication := do
  let some cand := findLFObjectRewriteCandidate? target sig rawName
    | throw s!"object tactic `rw {rawName}` failed: no direct-LF rewrite candidate named \
        '{rawName}' was found. Add `judgment_role ... : term_conversion` or \
        `type_conversion` and mark rules with `rule_role ... : computation`."
  let (lhs, rhs) := if symm then (cand.rhs, cand.lhs) else (cand.lhs, cand.rhs)
  let vars := rewritePatternVars cand
  match rewriteFirstObjectSubexprWithSubst? vars lhs rhs goalTarget with
  | some (subst, newGoal) =>
      pure {
        candidate := cand, lhs, rhs, reversed := symm, rewriteSubst := subst,
        oldGoal := goalTarget, newGoal := newGoal }
  | none =>
      let arrow := if symm then "←" else "→"
      throw <| String.intercalate "\n" [
        s!"object tactic `rw {rawName}` found rewrite candidate '{cand.name}' ({arrow})",
        s!"but no subexpression of the current object goal matched",
        s!"  lhs: {diagnosticObjExprString lhs}",
        s!"  goal: {diagnosticObjExprString goalTarget}",
        "This is direct-LF object rewriting, not Lean `rw`."]

/-- Message for a rewrite that changed the goal but failed conversion checking. -/
def objectRewriteConversionFailureMessage (app : LFObjectRewriteApplication)
    (rawName : Name) (symm : Bool) : String :=
  let arrow := if symm then "←" else "→"
  String.intercalate "\n" [
    s!"object tactic `rw {rawName}` found rewrite candidate '{app.candidate.name}' ({arrow})",
    "and rewrote the current object goal, but the goal change is not justified by",
    "the checked direct-LF conversion engine yet.",
    s!"  old goal: {diagnosticObjExprString app.oldGoal}",
    s!"  new goal: {diagnosticObjExprString app.newGoal}",
    "conversion failure: checked object conversion rejected the endpoints"]

/-- Check one direct-LF object-level rewrite candidate against a goal target. -/
def checkObjectRewrite (target : InternalDefTarget) (sig : HLSignature) (levels : Array Name)
    (ctx : Array HLBinding) (goalTarget : ObjExpr) (rawName : Name) (symm : Bool) :
    Except String CheckedLFObjectRewrite := do
  let app ← findObjectRewriteApplication target sig goalTarget rawName symm
  match checkObjectGoalConversion sig levels ctx goalTarget app.newGoal with
  | .ok conversion =>
      pure {
        candidateName := app.candidate.name, lhs := app.lhs, rhs := app.rhs,
        oldGoal := goalTarget, newGoal := app.newGoal, conversion := conversion }
  | .error _ =>
      throw <| String.intercalate "\n" [
        objectRewriteConversionFailureMessage app rawName symm,
        "For now, direct-LF `rw` is limited to rewrites whose goal change is also",
        "accepted by checked object conversion. A future transport-producing `rw` can",
        "use non-definitional equality or conversion proof terms."]

/-- Head identifier of an object application, if it has one. -/
def objectAppHeadName? (e : ObjExpr) : Option Name :=
  match objectAppHeadAndArgs e with
  | (.ident n, _) => some n.eraseMacroScopes
  | _ => none

/-- Top-level head/argument position changed between two goal expressions, when unique. -/
def changedObjectHeadArgument? (oldGoal newGoal : ObjExpr) : Option (Name × Nat) :=
  let (oldHead, oldArgs) := objectAppHeadAndArgs oldGoal
  let (newHead, newArgs) := objectAppHeadAndArgs newGoal
  match oldHead, newHead with
  | .ident oldName, .ident newName =>
      if sameObjectName oldName newName && oldArgs.size == newArgs.size then
        let diffs := oldArgs.zipIdx.filter fun (arg, idx) =>
          !objectExprEq arg newArgs[idx]!
        if diffs.size == 1 then
          some (oldName.eraseMacroScopes, diffs[0]!.2)
        else
          none
      else
        none
  | _, _ => none

/-- Whether optional transport-position metadata allows this transport rule for the rewrite. -/
def transportPositionAllows (sig : HLSignature) (app : LFObjectRewriteApplication)
    (ruleName : Name) : Bool :=
  let positions := sig.transportPositions.filter fun pos => sameObjectName pos.ruleName ruleName
  if positions.isEmpty then
    true
  else
    match changedObjectHeadArgument? app.oldGoal app.newGoal with
    | some (head, idx) =>
        positions.any fun pos =>
          sameObjectName pos.targetHead head && pos.argumentIndex == idx
    | none => false

/-- Match a no-user-input candidate conclusion against a premise to synthesize. -/
def matchObjectSynthesisCandidate? (sig : HLSignature) (ctx : Array HLBinding)
    (params : Array HLBinding) (candidateConclusion expected : ObjExpr) :
    Option (NameMap ObjExpr) :=
  let paramVars := params.foldl (init := {}) fun acc p => acc.insert p.name.eraseMacroScopes
  match matchObjectPattern paramVars candidateConclusion expected {} with
  | some subst => some subst
  | none =>
      let defs := objectTacticLFDefinitionValues sig
      let paramLocals := params.foldl (init := internalObjectLocalNames ctx) fun locals b =>
        locals.insert b.name.eraseMacroScopes
      let candidateConclusion := unfoldLFDefinitionsInExprWithLocals defs paramLocals
        candidateConclusion
      let expected := unfoldLFDefinitionsInExprWithLocals defs paramLocals expected
      matchObjectPattern paramVars candidateConclusion expected {}

/-- Whether all side conditions of a synthesized helper are discharged by the built-in hook. -/
def objectSideConditionsAreBuiltinTrivial (sideConditions : Array RuleSideConditionDecl) : Bool :=
  sideConditions.all fun sc => classifySideConditionHook sc.solver == .builtinTrivial

/-- Check selected rewrite-helper side conditions, accepting only the built-in trivial hook. -/
def checkRewriteHelperSideConditions (rawName helperKind helperName : Name)
    (sideConditions : Array RuleSideConditionDecl) (subst : NameMap ObjExpr) :
    Except String Unit := do
  for sc in sideConditions do
    let scInput := substObjectVars subst sc.input
    match classifySideConditionHook sc.solver with
    | .builtinTrivial => pure ()
    | .opaque =>
        throw <| String.intercalate "\n" [
          s!"object tactic `rw {rawName}` cannot synthesize side-condition certificate " ++
            s!"'{sc.name.eraseMacroScopes}' for {helperKind.eraseMacroScopes} " ++
            s!"'{helperName.eraseMacroScopes}'",
          s!"solver: {sc.solver.eraseMacroScopes}",
          s!"input: {diagnosticObjExprString scInput}"]

/-- Try to synthesize a premise proof from locals and simple already-declared LF facts. -/
partial def synthesizeObjectPremiseProof? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (expected : ObjExpr) (fuel : Nat := 2) :
    Except String (Option ObjExpr) := do
  for h in ctx.reverse do
    if objectGoalsConvertible sig levels ctx h.typeExpr expected then
      return some (.ident h.name)
  if fuel == 0 then
    return none
  for d in sig.lfObjectDefs do
    let (params, conclusionExpr) := splitObjectTelescope d.typeExpr
    if let some subst :=
        matchObjectSynthesisCandidate? sig ctx params conclusionExpr expected then
      let mut args := #[]
      let mut ok := true
      for param in params do
        match subst.find? param.name.eraseMacroScopes with
        | some arg => args := args.push arg
        | none => ok := false
      if ok then
        return some (mkObjectApps (.ident d.name) args)
  for c in sig.lfOpaqueConsts do
    if let some typeExpr := c.typeExpr? then
      let (params, conclusionExpr) := splitObjectTelescope typeExpr
      if let some subst :=
          matchObjectSynthesisCandidate? sig ctx params conclusionExpr expected then
        let mut args := #[]
        let mut ok := true
        for param in params do
          match subst.find? param.name.eraseMacroScopes with
          | some arg => args := args.push arg
          | none => ok := false
        if ok then
          return some (mkObjectApps (.ident c.name) args)
  for thm in sig.lfJudgmentTheorems do
    if let some subst0 := matchObjectSynthesisCandidate? sig ctx thm.binders
        thm.judgmentExpr expected then
      let mut subst := subst0
      let mut args := #[]
      let mut ok := true
      for binder in thm.binders do
        match subst.find? binder.name.eraseMacroScopes with
        | some arg => args := args.push arg
        | none =>
            let binderType := substObjectVars subst binder.typeExpr
            match ← synthesizeObjectPremiseProof? target sig levels ctx binderType (fuel - 1) with
            | some proof =>
                args := args.push proof
                subst := subst.insert binder.name.eraseMacroScopes proof
            | none => ok := false
      if ok then
        return some (mkObjectApps (.ident thm.name) args)
  for ruleDecl in sig.rules do
    if !objectSideConditionsAreBuiltinTrivial ruleDecl.sideConditions then
      continue
    if let some subst0 := matchObjectSynthesisCandidate? sig ctx ruleDecl.params
        ruleDecl.conclusionExpr expected then
      let mut subst := subst0
      let mut args := #[]
      let mut ok := true
      for param in ruleDecl.params do
        match subst.find? param.name.eraseMacroScopes with
        | some arg => args := args.push arg
        | none => ok := false
      for prem in ruleDecl.premises do
        if ok then
          let premiseExpected := substObjectVars subst prem.judgmentExpr
          match ← synthesizeObjectPremiseProof? target sig levels ctx premiseExpected
              (fuel - 1) with
          | some proof =>
              args := args.push proof
              subst := subst.insert prem.name.eraseMacroScopes proof
          | none => ok := false
      if ok then
        return some (mkObjectApps (.ident ruleDecl.name) args)
  return none

/-- Synthesize an extra rewrite-helper premise or report the missing obligation. -/
def synthesizeRewriteHelperPremise (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (rawName helperKind helperName : Name)
    (premName : Name) (expected : ObjExpr) : Except String ObjExpr := do
  match ← synthesizeObjectPremiseProof? target sig levels ctx expected with
  | some proof => pure proof
  | none =>
      throw <| String.intercalate "\n" [
        s!"object tactic `rw {rawName}` found {helperKind.eraseMacroScopes} " ++
          s!"'{helperName.eraseMacroScopes}', but could not synthesize extra premise " ++
          s!"'{premName.eraseMacroScopes}'",
        s!"required premise:\n  {diagnosticObjExprString expected}"]

/-- Build the proof term witnessing the rewrite evidence selected by `rw`. -/
def objectRewriteEvidenceTerm (app : LFObjectRewriteApplication) : Except String ObjExpr := do
  let mut args := #[]
  for param in app.candidate.params do
    match app.rewriteSubst.find? param.name.eraseMacroScopes with
    | some arg => args := args.push arg
    | none =>
        throw <| s!"object tactic `rw` could not instantiate rewrite evidence parameter " ++
          s!"'{param.name.eraseMacroScopes}' for '{app.candidate.name}'"
  pure <| mkObjectApps (.ident app.candidate.name) args

/-- Try to synthesize reverse rewrite evidence with a declared symmetry rule. -/
def objectRewriteSymmetryRuleTerm? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (rawName : Name)
    (_app : LFObjectRewriteApplication)
    (symm : LFRewriteSymmetryDecl) (ruleDecl : RuleDecl) (directTerm directActual : ObjExpr) :
    Except String (Option (ObjExpr × ObjExpr)) := do
  let some evPremise := ruleDecl.premises.find? (fun p =>
      p.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes)
    | pure none
  let vars := ruleDecl.params.foldl (init := {}) fun acc p =>
    acc.insert p.name.eraseMacroScopes
  let some subst := matchObjectPattern vars evPremise.judgmentExpr directActual {}
    | pure none
  let mut args := #[]
  let mut ok := true
  for param in ruleDecl.params do
    match subst.find? param.name.eraseMacroScopes with
    | some arg => args := args.push arg
    | none => ok := false
  if !ok then
    return none
  let mut subst := subst
  for prem in ruleDecl.premises do
    if prem.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes then
      args := args.push directTerm
      subst := subst.insert prem.name.eraseMacroScopes directTerm
    else
      let expected := substObjectVars subst prem.judgmentExpr
      let proof ← synthesizeRewriteHelperPremise target sig levels ctx rawName `rewrite_symmetry
        symm.symmetryName prem.name expected
      args := args.push proof
      subst := subst.insert prem.name.eraseMacroScopes proof
  checkRewriteHelperSideConditions rawName `rewrite_symmetry symm.symmetryName
    ruleDecl.sideConditions subst
  pure <| some (mkObjectApps (.ident ruleDecl.name) args,
    substObjectVars subst ruleDecl.conclusionExpr)

/-- Try to synthesize reverse rewrite evidence with a declared symmetry theorem. -/
def objectRewriteSymmetryTheoremTerm? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (_rawName : Name)
    (_app : LFObjectRewriteApplication)
    (symm : LFRewriteSymmetryDecl) (thm : LFJudgmentTheoremDecl)
    (directTerm directActual : ObjExpr) : Except String (Option (ObjExpr × ObjExpr)) := do
  let some evBinder := thm.binders.find? (fun b =>
      b.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes)
    | pure none
  let vars := thm.binders.foldl (init := {}) fun acc b =>
    if b.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes then acc
    else acc.insert b.name.eraseMacroScopes
  let some subst := matchObjectPattern vars evBinder.typeExpr directActual {}
    | pure none
  let mut args := #[]
  let mut ok := true
  let mut subst := subst
  for binder in thm.binders do
    if binder.name.eraseMacroScopes == symm.evidenceParam.eraseMacroScopes then
      args := args.push directTerm
      subst := subst.insert binder.name.eraseMacroScopes directTerm
    else
      match subst.find? binder.name.eraseMacroScopes with
      | some arg => args := args.push arg
      | none =>
          let expected := substObjectVars subst binder.typeExpr
          match ← synthesizeObjectPremiseProof? target sig levels ctx expected with
          | some proof =>
              args := args.push proof
              subst := subst.insert binder.name.eraseMacroScopes proof
          | none => ok := false
  if !ok then
    return none
  pure <| some (mkObjectApps (.ident thm.name) args, substObjectVars subst thm.judgmentExpr)

/-- Try to lift rewrite evidence through one congruence rule. -/
def objectRewriteCongruenceRuleTerm? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (rawName : Name)
    (congr : LFRewriteCongruenceDecl)
    (ruleDecl : RuleDecl) (sourceTerm sourceActual : ObjExpr) :
    Except String (Option (ObjExpr × ObjExpr)) := do
  let some evPremise := ruleDecl.premises.find? (fun p =>
      p.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes)
    | pure none
  let vars := ruleDecl.params.foldl (init := {}) fun acc p =>
    acc.insert p.name.eraseMacroScopes
  let some subst := matchObjectPattern vars evPremise.judgmentExpr sourceActual {}
    | pure none
  let mut args := #[]
  let mut ok := true
  for param in ruleDecl.params do
    match subst.find? param.name.eraseMacroScopes with
    | some arg => args := args.push arg
    | none => ok := false
  if !ok then
    return none
  let mut subst := subst
  for prem in ruleDecl.premises do
    if prem.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes then
      args := args.push sourceTerm
      subst := subst.insert prem.name.eraseMacroScopes sourceTerm
    else
      let expected := substObjectVars subst prem.judgmentExpr
      match ← synthesizeObjectPremiseProof? target sig levels ctx expected with
      | some proof =>
          args := args.push proof
          subst := subst.insert prem.name.eraseMacroScopes proof
      | none => ok := false
  if !ok then
    return none
  checkRewriteHelperSideConditions rawName `rewrite_congruence congr.congruenceName
    ruleDecl.sideConditions subst
  pure <| some (mkObjectApps (.ident ruleDecl.name) args,
    substObjectVars subst ruleDecl.conclusionExpr)

/-- Try to lift rewrite evidence through one congruence theorem. -/
def objectRewriteCongruenceTheoremTerm? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (_rawName : Name)
    (congr : LFRewriteCongruenceDecl)
    (thm : LFJudgmentTheoremDecl) (sourceTerm sourceActual : ObjExpr) :
    Except String (Option (ObjExpr × ObjExpr)) := do
  let some evBinder := thm.binders.find? (fun b =>
      b.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes)
    | pure none
  let vars := thm.binders.foldl (init := {}) fun acc b =>
    if b.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes then acc
    else acc.insert b.name.eraseMacroScopes
  let some subst := matchObjectPattern vars evBinder.typeExpr sourceActual {}
    | pure none
  let mut args := #[]
  let mut ok := true
  let mut subst := subst
  for binder in thm.binders do
    if binder.name.eraseMacroScopes == congr.evidenceParam.eraseMacroScopes then
      args := args.push sourceTerm
      subst := subst.insert binder.name.eraseMacroScopes sourceTerm
    else
      match subst.find? binder.name.eraseMacroScopes with
      | some arg => args := args.push arg
      | none =>
          let expected := substObjectVars subst binder.typeExpr
          match ← synthesizeObjectPremiseProof? target sig levels ctx expected with
          | some proof =>
              args := args.push proof
              subst := subst.insert binder.name.eraseMacroScopes proof
          | none => ok := false
  if !ok then
    return none
  pure <| some (mkObjectApps (.ident thm.name) args, substObjectVars subst thm.judgmentExpr)

/-- Generate relation evidence candidates by repeatedly applying congruence metadata. -/
partial def objectRewriteEvidenceCongruenceCandidates (target : InternalDefTarget)
    (sig : HLSignature) (levels : Array Name) (ctx : Array HLBinding) (rawName relationName : Name)
    (fuel : Nat) (sourceTerm sourceActual : ObjExpr) :
    Except String (Array (ObjExpr × ObjExpr)) := do
  let mut out := #[(sourceTerm, sourceActual)]
  if fuel == 0 then
    return out
  for congr in sig.rewriteCongruences do
    unless sameObjectName congr.relationName relationName do
      continue
    let lifted? ←
      if let some ruleDecl := sig.rules.find? (fun r =>
          sameObjectName r.name congr.congruenceName) then
        objectRewriteCongruenceRuleTerm? target sig levels ctx rawName congr ruleDecl
          sourceTerm sourceActual
      else if let some thm := sig.lfJudgmentTheorems.find? (fun t =>
          sameObjectName t.name congr.congruenceName) then
        objectRewriteCongruenceTheoremTerm? target sig levels ctx rawName congr thm
          sourceTerm sourceActual
      else
        pure none
    match lifted? with
    | some (term, actual) =>
        let nested ← objectRewriteEvidenceCongruenceCandidates target sig levels ctx rawName
          relationName (fuel - 1) term actual
        out := out ++ nested
    | none => pure ()
  return out

/-- Build oriented relation evidence for a transport rule, applying symmetry if needed. -/
def objectRewriteOrientedEvidenceForTransport (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (app : LFObjectRewriteApplication)
    (rawName : Name) : Except String (ObjExpr × ObjExpr) := do
  let directTerm ← objectRewriteEvidenceTerm app
  let directActual := substObjectVars app.rewriteSubst app.candidate.evidenceExpr
  if !app.reversed then
    return (directTerm, directActual)
  let some relationName := objectAppHeadName? directActual
    | throw <| s!"object tactic `rw {rawName}` needs reverse rewrite evidence, but the " ++
        "selected evidence is not headed by a relation identifier"
  let symmetries := sig.rewriteSymmetries.filter fun symm =>
    sameObjectName symm.relationName relationName
  if symmetries.isEmpty then
    throw <| String.intercalate "\n" [
      s!"object tactic `rw ← {rawName}` needs reverse evidence for '{relationName}'",
      "but no `rewrite_symmetry` metadata is declared for that relation"]
  for symm in symmetries do
    if let some ruleDecl := sig.rules.find? (fun r => sameObjectName r.name symm.symmetryName) then
      match ← objectRewriteSymmetryRuleTerm? target sig levels ctx rawName app symm ruleDecl
          directTerm directActual with
      | some out => return out
      | none => pure ()
    else if let some thm := sig.lfJudgmentTheorems.find? (fun t =>
        sameObjectName t.name symm.symmetryName) then
      match ← objectRewriteSymmetryTheoremTerm? target sig levels ctx rawName app symm thm
          directTerm directActual with
      | some out => return out
      | none => pure ()
  throw <| String.intercalate "\n" [
    s!"object tactic `rw ← {rawName}` found rewrite_symmetry metadata for '{relationName}'",
    "but no declared symmetry rule/theorem matched the selected evidence",
    s!"  evidence: {diagnosticObjExprString directActual}"]

/-- Try to wrap a proof of the rewritten goal with a declared transport rule. -/
def buildObjectRewriteTransportTerm (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (app : LFObjectRewriteApplication)
    (rawName : Name) (sourceProof : ObjExpr) : Except String ObjExpr := do
  let some relationName := objectAppHeadName? app.candidate.evidenceExpr
    | throw s!"object tactic `rw {rawName}` found rewrite evidence, but its statement is \
        not headed by a relation identifier"
  unless sig.rewriteRelations.any (fun r => sameObjectName r.relationName relationName) do
    throw <| String.intercalate "\n" [
      s!"object tactic `rw {rawName}` found rewrite evidence for '{relationName}'",
      "but no `rewrite_relation` metadata is declared for that relation"]
  let transports := sig.transportRules.filter fun tr =>
    sameObjectName tr.relationName relationName
  if transports.isEmpty then
    throw <| String.intercalate "\n" [
      s!"object tactic `rw {rawName}` found rewrite evidence for '{relationName}'",
      "but no `transport_rule` metadata is declared for that relation"]
  let (baseEvidenceTerm, baseEvidenceActual) ←
    objectRewriteOrientedEvidenceForTransport target sig levels ctx app rawName
  let evidenceCandidates ← objectRewriteEvidenceCongruenceCandidates target sig levels ctx rawName
    relationName 4 baseEvidenceTerm baseEvidenceActual
  for tr in transports do
    let some ruleDecl := sig.rules.find? (fun r => sameObjectName r.name tr.ruleName)
      | continue
    unless transportPositionAllows sig app ruleDecl.name do
      continue
    let some evPremise := ruleDecl.premises.find? (fun p =>
        p.name.eraseMacroScopes == tr.evidencePremise.eraseMacroScopes)
      | continue
    let some srcPremise := ruleDecl.premises.find? (fun p =>
        p.name.eraseMacroScopes == tr.sourcePremise.eraseMacroScopes)
      | continue
    let vars := ruleDecl.params.foldl (init := {}) fun acc p =>
      acc.insert p.name.eraseMacroScopes
    let some subst1 := matchObjectPattern vars ruleDecl.conclusionExpr app.oldGoal {}
      | continue
    let evidenceExpected := substObjectVars subst1 evPremise.judgmentExpr
    let mut matchedEvidence? : Option (ObjExpr × NameMap ObjExpr) := none
    for (candidateTerm, candidateActual) in evidenceCandidates do
      match matchObjectPattern vars evidenceExpected candidateActual subst1 with
      | some subst2 => matchedEvidence? := some (candidateTerm, subst2)
      | none => pure ()
    let some (evidenceTerm, subst2) := matchedEvidence?
      | continue
    let sourceExpected := substObjectVars subst2 srcPremise.judgmentExpr
    let some subst3 := matchObjectPattern vars sourceExpected app.newGoal subst2
      | continue
    let mut args := #[]
    let mut ok := true
    for param in ruleDecl.params do
      match subst3.find? param.name.eraseMacroScopes with
      | some arg => args := args.push arg
      | none => ok := false
    unless ok do
      continue
    let mut substArgs := subst3
    for prem in ruleDecl.premises do
      if prem.name.eraseMacroScopes == tr.evidencePremise.eraseMacroScopes then
        args := args.push evidenceTerm
        substArgs := substArgs.insert prem.name.eraseMacroScopes evidenceTerm
      else if prem.name.eraseMacroScopes == tr.sourcePremise.eraseMacroScopes then
        args := args.push sourceProof
        substArgs := substArgs.insert prem.name.eraseMacroScopes sourceProof
      else
        let expected := substObjectVars substArgs prem.judgmentExpr
        let proof ← synthesizeRewriteHelperPremise target sig levels ctx rawName
          `transport_rule tr.ruleName prem.name expected
        args := args.push proof
        substArgs := substArgs.insert prem.name.eraseMacroScopes proof
    checkRewriteHelperSideConditions rawName `transport_rule tr.ruleName ruleDecl.sideConditions
      substArgs
    return mkObjectApps (.ident ruleDecl.name) args
  throw <| String.intercalate "\n" [
    s!"object tactic `rw {rawName}` found rewrite evidence for '{relationName}'",
    "and transport metadata for that relation, but no declared transport rule matched",
    s!"  old goal: {diagnosticObjExprString app.oldGoal}",
    s!"  new goal: {diagnosticObjExprString app.newGoal}",
    s!"  evidence: {diagnosticObjExprString baseEvidenceActual}",
    "The tactic expects a transport rule whose conclusion is the old goal,",
    "whose evidence premise matches the oriented rewrite evidence, and whose",
    "source premise matches the rewritten goal.",
    "For nested rewrites, declare rewrite_congruence metadata for each lifted head."]

/-- Check that a rewrite step is usable by conversion or by declared transport metadata. -/
def rewriteObjectGoalForTactic (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (goalTarget : ObjExpr) (rawName : Name)
    (symm : Bool) : Except String ObjExpr := do
  let app ← findObjectRewriteApplication target sig goalTarget rawName symm
  match checkObjectGoalConversion sig levels ctx goalTarget app.newGoal with
  | .ok _ => pure app.newGoal
  | .error _ =>
      discard <| buildObjectRewriteTransportTerm target sig levels ctx app rawName
        (.ident (.str .anonymous "?rw_source"))
      pure app.newGoal

/-- Apply a sequence of tactic-usable object rewrites to a goal target. -/
def rewriteObjectGoalSeqForTactic (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (goalTarget : ObjExpr)
    (items : Array (Name × Bool)) : Except String ObjExpr := do
  if items.isEmpty then
    throw "object tactic `rw []` failed: rewrite list is empty"
  let mut goal := goalTarget
  for (rawName, symm) in items do
    goal ← rewriteObjectGoalForTactic target sig levels ctx goal rawName symm
  pure goal

/-- Apply one checked direct-LF object-level rewrite candidate to a goal target. -/
def rewriteObjectGoal (target : InternalDefTarget) (sig : HLSignature) (levels : Array Name)
    (ctx : Array HLBinding) (goalTarget : ObjExpr) (rawName : Name) (symm : Bool) :
    Except String ObjExpr := do
  return (← checkObjectRewrite target sig levels ctx goalTarget rawName symm).newGoal

/-- Apply a sequence of checked direct-LF object rewrite candidates to a goal target. -/
def rewriteObjectGoalSeq (target : InternalDefTarget) (sig : HLSignature) (levels : Array Name)
    (ctx : Array HLBinding) (goalTarget : ObjExpr) (items : Array (Name × Bool)) :
    Except String ObjExpr := do
  if items.isEmpty then
    throw "object tactic `rw []` failed: rewrite list is empty"
  let mut goal := goalTarget
  for (rawName, symm) in items do
    goal ← rewriteObjectGoal target sig levels ctx goal rawName symm
  pure goal

/-- One rewrite or conversion-plugin step selected by object `simp`. -/
structure ObjectSimpRewriteStep where
  rawName : Name
  newGoal : ObjExpr
  app? : Option LFObjectRewriteApplication := none
  needsTransport : Bool := false
  pluginStep? : Option ConversionStepKind := none

/-- Configuration for object `simp`. -/
structure ObjectSimpConfig where
  names : Array Name := #[]
  onlyMode : Bool := false

/-- Result of bounded object simplification. -/
structure ObjectSimpResult where
  newGoal : ObjExpr
  rewrites : Array ObjectSimpRewriteStep := #[]
  unfoldedDefinitions : Array Name := #[]

/-- Whether a simp configuration names an LF declaration. -/
def objectSimpConfigContains (config : ObjectSimpConfig) (name : Name) : Bool :=
  config.names.any fun n => sameObjectName n name

/-- Append a simp rewrite name if no previous name with the same user-facing head exists. -/
def pushObjectSimpRewriteName (names : Array Name) (name : Name) : Array Name :=
  if names.any fun old => sameObjectName old name then names else names.push name

/-- LF definitions that object `simp` may unfold under the current configuration. -/
def objectSimpLFDefinitionValues (sig : HLSignature) (config : ObjectSimpConfig) :
    LFDefinitionValueMap :=
  sig.lfObjectDefs.foldl (init := {}) fun defs d =>
    if config.onlyMode && !objectSimpConfigContains config d.name then
      defs
    else
      defs.insert d.name.eraseMacroScopes (eraseObjExprScopes d.value)

/-- Computation-rule names eligible for the object `simp` rewrite loop. -/
def objectSimpRewriteNames (target : InternalDefTarget) (sig : HLSignature)
    (config : ObjectSimpConfig) : Array Name := Id.run do
  let mut names := #[]
  for rawName in config.names do
    if (findLFObjectRewriteCandidate? target sig rawName).isSome then
      names := pushObjectSimpRewriteName names rawName
  unless config.onlyMode do
    for ruleDecl in sig.rules do
      let classes := ruleAutomationClassesOfKinds (sig.ruleRoleKinds ruleDecl.name)
      if classes.contains .computation then
        names := pushObjectSimpRewriteName names ruleDecl.name
  return names

/-- Conversion plugins eligible for the object `simp` plugin-step loop. -/
def objectSimpConversionPlugins (sig : HLSignature) (config : ObjectSimpConfig) :
    Array ConversionPluginDecl := Id.run do
  let mut plugins := #[]
  for plugin in sig.conversionPlugins do
    if plugin.trust == .executableChecked && plugin.supportedSteps.contains .beta then
      if !config.onlyMode || objectSimpConfigContains config plugin.name then
        if !plugins.any (fun old => sameObjectName old.name plugin.name) then
          plugins := plugins.push plugin
  return plugins

/-- One object β redex contracted while simplifying the whole goal. -/
structure ObjectPluginReduction where
  redex : ObjExpr
  reduct : ObjExpr
  newGoal : ObjExpr

/-- First object β step exposed through the generic conversion-plugin vocabulary. -/
partial def objectBetaReduceOne? (e : ObjExpr) : Option ObjectPluginReduction :=
  let e := eraseObjExprScopes e
  match e with
  | .app (.lam xs body) arg =>
      if h : 0 < xs.size then
        let x := xs[0]
        let rest := xs.extract 1 xs.size
        let body := substSingleLFParam x arg body
        let reduct := if rest.isEmpty then body else .lam rest body
        some { redex := e, reduct, newGoal := reduct }
      else
        none
  | .app f a =>
      match objectBetaReduceOne? f with
      | some r => some { r with newGoal := .app r.newGoal a }
      | none =>
          match objectBetaReduceOne? a with
          | some r => some { r with newGoal := .app f r.newGoal }
          | none => none
  | .arrow x A B =>
      match objectBetaReduceOne? A with
      | some r => some { r with newGoal := .arrow x r.newGoal B }
      | none =>
          match objectBetaReduceOne? B with
          | some r => some { r with newGoal := .arrow x A r.newGoal }
          | none => none
  | .funArrow x A B =>
      match objectBetaReduceOne? A with
      | some r => some { r with newGoal := .funArrow x r.newGoal B }
      | none =>
          match objectBetaReduceOne? B with
          | some r => some { r with newGoal := .funArrow x A r.newGoal }
          | none => none
  | .lam xs body =>
      match objectBetaReduceOne? body with
      | some r => some { r with newGoal := .lam xs r.newGoal }
      | none => none
  | .jeq lhs rhs =>
      match objectBetaReduceOne? lhs with
      | some r => some { r with newGoal := .jeq r.newGoal rhs }
      | none =>
          match objectBetaReduceOne? rhs with
          | some r => some { r with newGoal := .jeq lhs r.newGoal }
          | none => none
  | .ident _ | .sort | .univ _ => none

/-- Try one checked conversion-plugin simplification step. -/
def findObjectSimpPluginStep? (sig : HLSignature) (ctx : Array HLBinding)
    (config : ObjectSimpConfig) (goalTarget : ObjExpr) :
    Except String (Option ObjectSimpRewriteStep) := do
  for plugin in objectSimpConversionPlugins sig config do
    if let some reduction := objectBetaReduceOne? goalTarget then
      match checkObjectConversionPluginStep sig ctx plugin.name .beta
          reduction.redex reduction.reduct with
      | .ok _ =>
          return some {
            rawName := plugin.name, newGoal := reduction.newGoal, pluginStep? := some .beta }
      | .error _ => pure ()
  return none

/-- Compact trace of simplification steps used by object `simp`. -/
def objectSimpRewriteTrace (steps : Array ObjectSimpRewriteStep) : String :=
  if steps.isEmpty then " none"
  else
    "\n  " ++ String.intercalate "\n  " (steps.toList.map fun step =>
      match step.pluginStep? with
      | some kind => s!"{step.rawName.eraseMacroScopes}:{kind.label}"
      | none => toString step.rawName.eraseMacroScopes)

/-- Try one computation rewrite that is justified by conversion or declared transport. -/
def findObjectSimpRewrite? (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (config : ObjectSimpConfig)
    (goalTarget : ObjExpr) : Except String (Option ObjectSimpRewriteStep) := do
  for rawName in objectSimpRewriteNames target sig config do
    match findObjectRewriteApplication target sig goalTarget rawName false with
    | .error _ => pure ()
    | .ok app =>
        match checkObjectGoalConversion sig levels ctx goalTarget app.newGoal with
        | .ok _ => return some { rawName, newGoal := app.newGoal, app? := some app }
        | .error _ =>
            match buildObjectRewriteTransportTerm target sig levels ctx app rawName
                (.ident (.str .anonymous "?simp_source")) with
            | .ok _ =>
                return some {
                  rawName, newGoal := app.newGoal, app? := some app, needsTransport := true }
            | .error _ => pure ()
  return none

/-- Bounded object simplification over LF definitions, then computation rewrite rules. -/
partial def simpObjectGoalDetailed (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (goalTarget : ObjExpr)
    (config : ObjectSimpConfig := {}) (fuel : Nat := 8) : Except String ObjectSimpResult := do
  let defs := objectSimpLFDefinitionValues sig config
  let locals := internalObjectLocalNames ctx
  let unfolded := unfoldLFDefinitionsInExprWithLocals defs locals goalTarget
  let unfoldedNames := collectLFDefinitionUnfolds defs locals #[] goalTarget
  if !unfoldedNames.isEmpty && !objectExprEq unfolded goalTarget then
    return { newGoal := unfolded, unfoldedDefinitions := unfoldedNames }
  let findStep? (goal : ObjExpr) : Except String (Option ObjectSimpRewriteStep) := do
    match ← findObjectSimpPluginStep? sig ctx config goal with
    | some step => pure (some step)
    | none => findObjectSimpRewrite? target sig levels ctx config goal
  let rec loop (fuel : Nat) (goal : ObjExpr) (rewrites : Array ObjectSimpRewriteStep) :
      Except String ObjectSimpResult := do
    if fuel == 0 then
      if (← findStep? goal).isSome then
        throw <| String.intercalate "\n" [
          "object tactic `simp` exhausted its rewrite fuel",
          s!"used rewrite rules:{objectSimpRewriteTrace rewrites}",
          s!"last goal: {diagnosticObjExprString goal}"]
      return { newGoal := goal, rewrites, unfoldedDefinitions := unfoldedNames }
    match ← findStep? goal with
    | none => return { newGoal := goal, rewrites, unfoldedDefinitions := unfoldedNames }
    | some step => loop (fuel - 1) step.newGoal (rewrites.push step)
  let result ← loop fuel goalTarget #[]
  if objectExprEq result.newGoal goalTarget then
    throw "object tactic `simp` made no progress; the simplifier unfolds checked LF definitions \
      and applies eligible computation rewrites"
  pure result

/-- One bounded object simplification pass over LF definitions and computation rewrite rules. -/
def simpObjectGoal (target : InternalDefTarget) (sig : HLSignature) (levels : Array Name)
    (ctx : Array HLBinding) (goalTarget : ObjExpr) (config : ObjectSimpConfig := {}) :
    Except String ObjExpr := do
  pure (← simpObjectGoalDetailed target sig levels ctx goalTarget config).newGoal

/-- Wrap a proof of a simplified goal with transport evidence used by object `simp`. -/
def wrapObjectSimpTransports (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (steps : Array ObjectSimpRewriteStep)
    (sourceProof : ObjExpr) : Except String ObjExpr := do
  let mut proof := sourceProof
  for step in steps.reverse do
    if step.needsTransport then
      match step.app? with
      | some app =>
          proof ← buildObjectRewriteTransportTerm target sig levels ctx app step.rawName proof
      | none => throw "internal error: object simp transport step has no rewrite application"
  return proof

/-- A tactic compilation goal. -/
structure InternalObjectGoal where
  ctx : Array HLBinding := #[]
  target : ObjExpr
  deriving Inhabited, Repr

/-- Generate a deterministic name for an anonymous auto-introduced object binder. -/
def generatedObjectBinderName (ctx : Array HLBinding) : Name :=
  .str .anonymous s!"x{ctx.size + 1}"

/-- Introduce leading object arrows for tactics that operate under local hypotheses. -/
partial def autoIntroGoal (goal : InternalObjectGoal) : Array Name × InternalObjectGoal :=
  match goal.target with
  | .arrow x A B | .funArrow x A B =>
      let n := x.getD (generatedObjectBinderName goal.ctx)
      let goal' := {
        ctx := goal.ctx.push { name := n, typeExpr := A, visibility := .explicit },
        target := B }
      let (names, goal') := autoIntroGoal goal'
      (#[n] ++ names, goal')
  | _ => (#[], goal)

/-- Whether an object local name is already present in a tactic context. -/
def internalObjectContextHasName (ctx : Array HLBinding) (n : Name) : Bool :=
  ctx.any fun b => b.name.eraseMacroScopes == n.eraseMacroScopes

/-- Substitute the source binder name of an object arrow by the user-chosen intro name. -/
def renameIntroBinderTarget (binder? : Option Name) (newName : Name) (target : ObjExpr) : ObjExpr :=
  match binder? with
  | some oldName =>
      if sameObjectName oldName newName then
        target
      else
        substObjectVars (({} : NameMap ObjExpr).insert oldName.eraseMacroScopes (.ident newName))
          target
  | none => target

/-- Introduce one explicit object arrow/function-arrow binder. -/
def introObjectGoal (goal : InternalObjectGoal) (n : Name) : Except String InternalObjectGoal := do
  if internalObjectContextHasName goal.ctx n then
    throw s!"object tactic `intro {n}` failed: local name '{n}' is already in the object context"
  match goal.target with
  | .arrow x A B | .funArrow x A B =>
      pure {
        ctx := goal.ctx.push { name := n, typeExpr := A, visibility := .explicit },
        target := renameIntroBinderTarget x n B }
  | _ =>
      throw <| String.intercalate "\n" [
        s!"object tactic `intro {n}` failed: current goal is not an object arrow",
        s!"  goal: {diagnosticObjExprString goal.target}"]

/-- Introduce a list of explicit object arrow/function-arrow binders. -/
def introsObjectGoal (goal : InternalObjectGoal) (names : Array Name) :
    Except String InternalObjectGoal := do
  let mut goal := goal
  for n in names do
    goal ← introObjectGoal goal n
  pure goal

/-- Wrap a compiled term in lambdas introduced by `autoIntroGoal`. -/
def wrapObjectLambdas (names : Array Name) (body : ObjExpr) : ObjExpr :=
  if names.isEmpty then body else .lam names body

/-- Check whether an object tactic script contains an explicit `sorry`. -/
partial def internalTacticStepsContainSorry (steps : Array InternalTacticStep) : Bool :=
  steps.any fun
    | .sorry => true
    | .haveDecl _ _ body => internalTacticStepsContainSorry body
    | .haveTerm _ _ _ => false
    | _ => false

/-- Whether an object tactic step is a focus bullet. -/
def internalTacticStepIsFocusBullet : InternalTacticStep → Bool
  | .focusBullet => true
  | _ => false

/-- Whether the tactic script has a focus bullet at a given step index. -/
def internalTacticStepAtIsFocusBullet (steps : Array InternalTacticStep) (idx : Nat) : Bool :=
  match steps[idx]? with
  | some step => internalTacticStepIsFocusBullet step
  | none => false

/-- Whether an object expression mentions a name, used to reject first-pass `refine` holes. -/
partial def internalObjExprMentionsName (needle : Name) : ObjExpr → Bool
  | .ident n => sameObjectName n needle
  | .sort | .univ .. => false
  | .app f a => internalObjExprMentionsName needle f || internalObjExprMentionsName needle a
  | .arrow _ A B | .funArrow _ A B => internalObjExprMentionsName needle A
    || internalObjExprMentionsName needle B
  | .lam _ body => internalObjExprMentionsName needle body
  | .jeq lhs rhs => internalObjExprMentionsName needle lhs || internalObjExprMentionsName needle rhs

/-- Render the local object context shown by tactic errors. -/
def renderInternalObjectContext (ctx : Array HLBinding) : String :=
  if ctx.isEmpty then
    "  (empty object context)"
  else
    String.intercalate "\n" <| ctx.toList.map fun b =>
      s!"  {b.name.eraseMacroScopes} : {diagnosticObjExprString b.typeExpr}"

/-- Match a candidate conclusion against a goal, unfolding checked LF definitions if needed. -/
def matchInternalCandidateConclusion? (sig : HLSignature) (ctx : Array HLBinding)
    (params : Array HLBinding) (candidateConclusion goalTarget : ObjExpr) :
    Option (NameMap ObjExpr) :=
  let paramVars := params.foldl (init := {}) fun vars b => vars.insert b.name.eraseMacroScopes
  match matchObjectPattern paramVars candidateConclusion goalTarget {} with
  | some subst => some subst
  | none =>
      let defs := objectTacticLFDefinitionValues sig
      let paramLocals := params.foldl (init := internalObjectLocalNames ctx) fun locals b =>
        locals.insert b.name.eraseMacroScopes
      let candidateConclusion :=
        unfoldLFDefinitionsInExprWithLocals defs paramLocals candidateConclusion
      let goalTarget := unfoldLFDefinitionsInExprWithLocals defs paramLocals goalTarget
      matchObjectPattern paramVars candidateConclusion goalTarget {}

/-- Diagnostic message for a failed candidate-conclusion/object-goal match. -/
def internalCandidateConclusionMismatchMessage (sig : HLSignature) (ctx : Array HLBinding)
    (candidateConclusion goalTarget : ObjExpr) : String :=
  String.intercalate "\n" [
    s!"conclusion\n  {diagnosticObjExprString candidateConclusion}",
    s!"does not match current goal\n  {diagnosticObjExprString goalTarget}",
    "",
    objectGoalNormalizationMismatchString sig ctx candidateConclusion goalTarget]

/-- Diagnostic for supplied object arguments rejected by inferred candidate parameters. -/
def internalArgumentMismatchMessage (tacticName : String) (rawName : Name) (paramName : Name)
    (supplied inferred : ObjExpr) (nested : Bool := false) : String :=
  let what := if nested then "nested application" else "argument"
  String.intercalate "\n" [
    s!"object tactic `{tacticName} {rawName}` supplied {what}",
    s!"  {diagnosticObjExprString supplied}",
    s!"for parameter '{paramName.eraseMacroScopes}', but the current goal inferred",
    s!"  {diagnosticObjExprString inferred}"]

/-- Diagnostic for solved refinement holes rejected by inferred candidate parameters. -/
def internalRefineHoleMismatchMessage (tacticName : String) (rawName : Name) (paramName : Name)
    (supplied inferred : ObjExpr) : String :=
  String.intercalate "\n" [
    s!"object tactic `{tacticName} {rawName}` solved refinement hole for parameter \
      '{paramName.eraseMacroScopes}' with",
    s!"  {diagnosticObjExprString supplied}",
    "but the current goal inferred",
    s!"  {diagnosticObjExprString inferred}"]

/-- Render a side-condition obligation with a diagnostic budget. -/
def internalSideConditionString (scName solver : Name) (input : ObjExpr) : String :=
  s!"{scName.eraseMacroScopes} by {solver.eraseMacroScopes} : {diagnosticObjExprString input}"

/-- Diagnostic for failed object-tactic parameter inference. -/
def internalCannotInferParameterMessage (tacticName : String) (rawName paramName : Name)
    (paramTy : ObjExpr) (placeholder : Bool) (nested : Bool) : String :=
  let slot := if placeholder then "placeholder `_` for parameter" else "implicit parameter"
  let nestedText := if nested then "nested " else ""
  String.intercalate "\n" [
    s!"object tactic `{tacticName}` could not infer {nestedText}{slot} \
      '{paramName.eraseMacroScopes}' in application `{rawName}`",
    "",
    s!"Current parameter target:\n  {diagnosticObjExprString paramTy}"]

/-- Diagnostic for opaque side-condition obligations in object tactic mode. -/
def internalOpaqueSideConditionMessage (tacticName : String) (rawName candName : Name)
    (scName solver : Name) (input : ObjExpr) : String :=
  String.intercalate "\n" [
    s!"object tactic `{tacticName} {rawName}` cannot synthesize side-condition certificate \
      '{scName.eraseMacroScopes}' for rule or declaration '{candName.eraseMacroScopes}'",
    "",
    s!"required side condition:\n  {internalSideConditionString scName solver input}",
    "",
    s!"The solver '{solver.eraseMacroScopes}' is opaque to core object tactic mode. Side \
      conditions are certificate obligations at the LF replay boundary; they are not Lean goals.",
    "Use a checked side-condition solver such as `trivial_side_condition`, supply a \
      `judgment_theorem`, or use a profile tactic that produces an explicit certificate."]

/-- Find a local hypothesis whose type matches a goal. -/
def findAssumption? (sig : HLSignature) (levels : Array Name) (ctx : Array HLBinding) (target :
  ObjExpr) : Option Name := Id.run do
  for h in ctx.reverse do
    if objectGoalsConvertible sig levels ctx h.typeExpr target then
      return some h.name
  return none

/-- Check a named premise proof against its expected premise when the name is resolvable. -/
def checkInternalPremiseProofExpr (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (proof expected : ObjExpr)
    (tacticName : String) (rawName : Name) : Except String Unit := do
  match proof with
  | .ident n =>
      if let some h := ctx.find? (fun h => sameObjectName h.name n) then
        unless objectGoalsConvertible sig levels ctx h.typeExpr expected do
          throw <| String.intercalate "\n" [
            s!"object tactic `{tacticName} {rawName}` supplied local hypothesis '{n}'",
            s!"with type\n  {diagnosticObjExprString h.typeExpr}",
            s!"for premise\n  {diagnosticObjExprString expected}",
            "",
            objectGoalNormalizationMismatchString sig ctx h.typeExpr expected]
      else if let some cand := findInternalApplyCandidate? target sig n then
        if cand.params.isEmpty && cand.subgoalTargets.isEmpty && cand.sideConditions.isEmpty then
          unless objectGoalsConvertible sig levels ctx cand.conclusionExpr expected do
            throw <| String.intercalate "\n" [
              s!"object tactic `{tacticName} {rawName}` supplied proof '{n}'",
              s!"with statement\n  {diagnosticObjExprString cand.conclusionExpr}",
              s!"for premise\n  {diagnosticObjExprString expected}",
              "",
              objectGoalNormalizationMismatchString sig ctx cand.conclusionExpr expected]
      else
        pure ()
  | _ => pure ()

/-- One infoview snapshot for a source object-tactic step. -/
structure InternalObjectTacticInfo where
  stx : Syntax
  goalsBefore : Array InternalObjectGoal
  goalsAfter : Array InternalObjectGoal
  deriving Inhabited

/-- Placeholder object term used in infoview-only dependent subgoals created by `apply`. -/
def internalObjectGoalPlaceholder (n : Name) : ObjExpr :=
  .ident (.str .anonymous s!"?{n.eraseMacroScopes}")

/-- Number of fully explicit argument slots in a candidate head application. -/
def internalApplyCandidateSlotCount (cand : InternalApplyCandidate) : Nat :=
  cand.params.size + cand.subgoalTargets.size

/-- Number of ordinary visible argument slots after omitting implicit candidate parameters. -/
def internalApplyCandidateVisibleSlotCount (cand : InternalApplyCandidate) : Nat :=
  cand.params.foldl (init := 0) (fun n p => if p.visibility == .implicit then n else n + 1) +
    cand.subgoalTargets.size

/-- Whether a supplied object tactic application is using the old fully explicit positional form. -/
def internalCandidateUsesFullExplicit (cand : InternalApplyCandidate) (supplied : Nat) : Bool :=
  internalApplyCandidateVisibleSlotCount cand != internalApplyCandidateSlotCount cand &&
    supplied == internalApplyCandidateSlotCount cand

/-- Advice appended to object tactic arity/placeholder diagnostics. -/
def internalObjectTacticPlaceholderAdvice (tacticName : String) : String :=
  if tacticName == "refine" then
    "Omitted explicit arguments are never turned into subgoals. Use `_` only for inferable \
      parameters, and write `?_` exactly where `refine` should create an object-theory subgoal."
  else
    "Omitted explicit arguments are never inferred as subgoals. `_` is infer-only, and `exact` \
      does not accept `?_`; provide complete argument terms instead."

/-- Check user-supplied argument count for an object tactic head application. -/
def checkInternalCandidateAppArity (tacticName : String) (rawName : Name)
    (supplied : Nat) (cand : InternalApplyCandidate) : Except String Unit := do
  let visible := internalApplyCandidateVisibleSlotCount cand
  let total := internalApplyCandidateSlotCount cand
  if internalCandidateUsesFullExplicit cand supplied then
    return ()
  let slotWord := if visible == total then "explicit" else "visible"
  if supplied < visible then
    throw s!"object tactic `{tacticName} {rawName} ...` supplied {supplied} argument(s)/hole(s), \
      but {visible} {slotWord} argument slot(s) are \
        required.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
  if supplied > visible then
    if visible == total then
      throw s!"object tactic `{tacticName} {rawName} ...` supplied {supplied} \
        argument(s)/hole(s), but rule or declaration '{rawName}' has only {visible} explicit \
          argument slot(s).\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
    else
      throw s!"object tactic `{tacticName} {rawName} ...` supplied {supplied} \
        argument(s)/hole(s), but rule or declaration '{rawName}' has only {visible} visible \
          argument slot(s) ({total} with implicit parameters supplied \
            explicitly).\n\n{internalObjectTacticPlaceholderAdvice tacticName}"

mutual
  /-- Elaborate a nested complete tactic argument against an expected object goal.

  This supports parenthesized head applications such as
  `(extend_cube_ctx _ _ empty_cube_ctx wfInterval)` in argument position. Nested `?_` holes are
  intentionally rejected for now; top-level `refine` arguments still create the user-facing
  subgoals. -/
  partial def compileInternalCompleteTacticArg (target : InternalDefTarget) (sig : HLSignature)
      (goal : InternalObjectGoal) (arg : InternalTacticArg) (tacticName : String) :
        Except String ObjExpr := do
    match arg with
    | .expr e => pure e
    | .inferPlaceholder =>
        throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` without a \
          candidate head"
    | .refineHole =>
        throw s!"object tactic `{tacticName}` does not accept nested refinement hole `?_`; use \
          `refine` or provide a complete argument"
    | .app rawName args =>
        compileInternalCompleteCandidateArg target sig goal rawName args tacticName

  /-- Compile a nested complete head application used as one supplied argument. -/
  partial def compileInternalCompleteCandidateArg (target : InternalDefTarget) (sig : HLSignature)
      (goal : InternalObjectGoal) (rawName : Name) (suppliedArgs : Array InternalTacticArg)
      (tacticName : String) : Except String ObjExpr := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throw s!"object tactic `{tacticName}` failed to elaborate nested application `{rawName}`: \
        unknown rule or internal declaration '{rawName}' in type theory '{target.theoryName}'"
    checkInternalCandidateAppArity tacticName rawName suppliedArgs.size cand
    let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throw <| s!"object tactic `{tacticName}` failed to elaborate nested application " ++
          s!"`{rawName}`: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target
    let mut outArgs : Array ObjExpr := #[]
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
          | some inferred => outArgs := outArgs.push inferred
          | none =>
              throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                false true
      | some argSpec =>
          argIdx := argIdx + 1
          match argSpec with
          | .inferPlaceholder =>
              match subst.find? key with
              | some inferred => outArgs := outArgs.push inferred
              | none =>
                  throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                    true true
          | .refineHole =>
              throw s!"object tactic `{tacticName}` does not accept nested refinement hole `?_` \
                in application `{rawName}`; use `refine` or provide a complete argument"
          | .expr e =>
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred
              | none => subst := subst.insert key e
              outArgs := outArgs.push e
          | .app _ _ =>
              let arg ← compileInternalCompleteTacticArg target sig { goal with target := paramTy }
                argSpec tacticName
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name arg
                      inferred true
              | none => subst := subst.insert key arg
              outArgs := outArgs.push arg
    for premiseTarget in cand.subgoalTargets do
      let some argSpec := suppliedArgs[argIdx]?
        | throw s!"internal error: missing checked object tactic argument"
      argIdx := argIdx + 1
      let premiseGoal := substObjectVars subst premiseTarget
      match argSpec with
      | .inferPlaceholder =>
          throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` for a premise \
            in application `{rawName}`; write an explicit proof term"
      | .refineHole =>
          throw s!"object tactic `{tacticName}` does not accept nested refinement hole `?_` in \
            application `{rawName}`; use `refine` or provide a complete argument"
      | .expr e =>
          checkInternalPremiseProofExpr target sig #[] goal.ctx e premiseGoal tacticName rawName
          outArgs := outArgs.push e
      | .app _ _ =>
          outArgs :=
            outArgs.push (← compileInternalCompleteTacticArg target sig { goal with target :=
            premiseGoal } argSpec tacticName)
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throw <| internalOpaqueSideConditionMessage tacticName rawName rawName sc.name
            sc.solver scInput
    pure (mkObjectApps (.ident cand.name) outArgs)
end

/-- Compute a candidate's conclusion after the compiled application has supplied its parameters. -/
def internalCandidateConclusionFromCompiledApp? (cand : InternalApplyCandidate) (value : ObjExpr) :
    Option ObjExpr :=
  let args := (splitObjApp value).2
  if args.size < cand.params.size then
    none
  else Id.run do
    let mut subst : NameMap ObjExpr := {}
    for param in cand.params, arg in args.extract 0 cand.params.size do
      subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)
    some (substObjectVars subst cand.conclusionExpr)

/-- Convert a direct internal term with `_` placeholders into tactic-argument syntax. -/
partial def internalDirectTermTacticArg (e : ObjExpr) : InternalTacticArg :=
  let e := eraseObjExprScopes e
  match e with
  | .ident n =>
      if n.eraseMacroScopes == `_ then .inferPlaceholder else .expr e
  | _ =>
      let (head, args) := splitObjApp e
      match head with
      | .ident n =>
          if args.any (internalObjExprMentionsName `_) then
            .app n (args.map internalDirectTermTacticArg)
          else
            .expr e
      | _ => .expr e

/-- Elaborate `_` placeholders in a direct internal term against a known expected type. -/
def elaborateInternalDirectTermPlaceholders (target : InternalDefTarget) (sig : HLSignature)
    (ctx : Array HLBinding) (expected value : ObjExpr) : Except String ObjExpr := do
  let value := eraseObjExprScopes value
  unless internalObjExprMentionsName `_ value do
    return value
  let contextMsg :=
    if ctx.isEmpty then "" else s!"\n\nInternal context:\n{renderInternalObjectContext ctx}"
  let (head, args) := splitObjApp value
  match head with
  | .ident n =>
      if n.eraseMacroScopes == `_ && args.isEmpty then
        throw s!"cannot infer direct internal placeholder `_` for expected type\n  \
          {diagnosticObjExprString expected}{contextMsg}"
      else
        match compileInternalCompleteCandidateArg target sig { ctx := ctx, target := expected } n
            (args.map internalDirectTermTacticArg) "direct term" with
        | .ok value => pure value
        | .error err =>
            throw <| String.intercalate "\n" [
              err,
              "",
              s!"Expected internal type:\n  {diagnosticObjExprString expected}" ++ contextMsg]
  | _ =>
      throw <| String.intercalate "\n" [
        s!"unsupported direct internal placeholder in term\n  {diagnosticObjExprString value}",
        "",
        "Placeholders are currently supported in applications headed by a rule, theorem, or \
          internal declaration." ]

/-- Elaborate and check a term-mode `have` proof against its annotated internal type. -/
def elaborateInternalHaveTermProof (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (ctx : Array HLBinding) (expected proof : ObjExpr) (haveName : Name) :
    Except String ObjExpr := do
  let proof ← elaborateInternalDirectTermPlaceholders target sig ctx expected proof
  let (head, args) := splitObjApp proof
  match head with
  | .ident n =>
      if let some cand := findInternalApplyCandidate? target sig n then
        let proof ←
          compileInternalCompleteCandidateArg target sig { ctx := ctx, target := expected } n
            (args.map fun arg => InternalTacticArg.expr arg) "have"
        if let some actual := internalCandidateConclusionFromCompiledApp? cand proof then
          unless objectGoalsConvertible sig levels ctx actual expected do
            throw <| String.intercalate "\n" [
              s!"object tactic `have {haveName}` supplied proof '{n}'",
              s!"with statement\n  {diagnosticObjExprString actual}",
              s!"for annotated type\n  {diagnosticObjExprString expected}",
              "",
              objectGoalNormalizationMismatchString sig ctx actual expected]
        pure proof
      else
        checkInternalPremiseProofExpr target sig levels ctx proof expected "have" haveName
        pure proof
  | _ => pure proof

mutual
  /-- Diagnostic elaboration of a nested tactic argument, replacing each `?_` by a stable
  placeholder and returning the object subgoals that the real `refine` compiler will consume. -/
  partial def diagnoseInternalTacticArgWithHoles (target : InternalDefTarget) (sig : HLSignature)
      (goal : InternalObjectGoal) (arg : InternalTacticArg) (allowHoles : Bool) (tacticName :
        String) :
      Except String (ObjExpr × Array InternalObjectGoal) := do
    match arg with
    | .expr e => pure (e, #[])
    | .inferPlaceholder =>
        throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` without a \
          candidate head.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
    | .refineHole =>
        unless allowHoles do
          throw s!"object tactic `exact` does not accept nested refinement hole `?_`; provide a \
            complete argument"
        pure (internalObjectGoalPlaceholder `_nested, #[goal])
    | .app rawName args =>
        diagnoseInternalCandidateArgWithHoles target sig goal rawName args allowHoles tacticName

  /-- Diagnostic elaboration of a nested head application with possible nested `?_` holes. -/
  partial def diagnoseInternalCandidateArgWithHoles (target : InternalDefTarget) (sig : HLSignature)
      (goal : InternalObjectGoal) (rawName : Name) (suppliedArgs : Array InternalTacticArg)
      (allowHoles : Bool) (tacticName : String) :
        Except String (ObjExpr × Array InternalObjectGoal) := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throw s!"object tactic `{tacticName}` failed to elaborate nested application `{rawName}`: \
        unknown rule or internal declaration '{rawName}' in type theory '{target.theoryName}'"
    checkInternalCandidateAppArity tacticName rawName suppliedArgs.size cand
    let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throw <| s!"object tactic `{tacticName}` failed to elaborate nested application " ++
          s!"`{rawName}`: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target
    let mut outArgs : Array ObjExpr := #[]
    let mut newGoals : Array InternalObjectGoal := #[]
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
          | some inferred => outArgs := outArgs.push inferred
          | none =>
              throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                false true
      | some argSpec =>
          argIdx := argIdx + 1
          match argSpec with
          | .inferPlaceholder =>
              match subst.find? key with
              | some inferred => outArgs := outArgs.push inferred
              | none =>
                  throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                    true true
          | .refineHole =>
              unless allowHoles do
                throw s!"object tactic `exact` does not accept nested refinement hole `?_`; \
                  provide a complete argument"
              newGoals := newGoals.push { ctx := goal.ctx, target := paramTy }
              let hole := internalObjectGoalPlaceholder param.name
              subst := subst.insert key hole
              outArgs := outArgs.push hole
          | .expr e =>
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred
              | none => subst := subst.insert key e
              outArgs := outArgs.push e
          | .app _ _ =>
              let (arg, nestedGoals) ←
                diagnoseInternalTacticArgWithHoles target sig { goal with target := paramTy }
                argSpec allowHoles tacticName
              newGoals := newGoals ++ nestedGoals
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name arg
                      inferred true
              | none => subst := subst.insert key arg
              outArgs := outArgs.push arg
    for premiseTarget in cand.subgoalTargets do
      let some argSpec := suppliedArgs[argIdx]?
        | throw s!"internal error: missing checked object tactic argument"
      argIdx := argIdx + 1
      let premiseGoal := substObjectVars subst premiseTarget
      match argSpec with
      | .inferPlaceholder =>
          throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` for a premise \
            in application `{rawName}`; write an explicit proof term or \
              `?_`.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
      | .refineHole =>
          unless allowHoles do
            throw s!"object tactic `exact` does not accept nested refinement hole `?_`; provide a \
              complete argument"
          newGoals := newGoals.push { ctx := goal.ctx, target := premiseGoal }
          outArgs :=
            outArgs.push (internalObjectGoalPlaceholder (.str rawName.eraseMacroScopes
              s!"premise{argIdx}"))
      | .expr e => outArgs := outArgs.push e
      | .app _ _ =>
          let (arg, nestedGoals) ←
            diagnoseInternalTacticArgWithHoles target sig { goal with target := premiseGoal }
            argSpec allowHoles tacticName
          newGoals := newGoals ++ nestedGoals
          outArgs := outArgs.push arg
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throw <| internalOpaqueSideConditionMessage tacticName rawName rawName sc.name
            sc.solver scInput
    pure (mkObjectApps (.ident cand.name) outArgs, newGoals)
end

/-- Compute diagnostic subgoals created by `refine head ... ?_ ...`.
This mirrors the argument/placeholder discipline of the real compiler but uses placeholders for
hole solutions so later dependent diagnostic targets remain stable before compilation. -/
def internalObjectRefineDiagnosticSubgoals (target : InternalDefTarget) (sig : HLSignature)
    (goal : InternalObjectGoal) (rawName : Name) (args : Array InternalTacticArg)
    (allowHoles : Bool) (tacticName : String) : Except String (Array InternalObjectGoal) := do
  let (_, innerGoal) := autoIntroGoal goal
  let some cand := findInternalApplyCandidate? target sig rawName
    | throw s!"object tactic `{tacticName} {rawName}` failed: unknown rule or internal \
      declaration '{rawName}' in type theory '{target.theoryName}'"
  checkInternalCandidateAppArity tacticName rawName args.size cand
  let some subst0 := matchInternalCandidateConclusion? sig innerGoal.ctx cand.params
      cand.conclusionExpr innerGoal.target
    | throw <| s!"object tactic `{tacticName} {rawName}` failed: " ++
        internalCandidateConclusionMismatchMessage
          sig innerGoal.ctx cand.conclusionExpr innerGoal.target
  let mut subst := subst0
  let mut newGoals : Array InternalObjectGoal := #[]
  let useFullExplicit := internalCandidateUsesFullExplicit cand args.size
  let mut argIdx := 0
  for param in cand.params do
    let key := param.name.eraseMacroScopes
    let paramTy := substObjectVars subst param.typeExpr
    let argSpec? :=
      if useFullExplicit || param.visibility == .explicit then
        args[argIdx]?
      else
        none
    match argSpec? with
    | none =>
        unless (subst.find? key).isSome do
          throw s!"object tactic `{tacticName} {rawName}` could not infer implicit parameter \
            '{param.name}'\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
    | some argSpec =>
        argIdx := argIdx + 1
        match argSpec with
        | .inferPlaceholder =>
            match subst.find? key with
            | some _ => pure ()
            | none =>
              throw s!"object tactic `{tacticName} {rawName}` could not infer placeholder `_` for \
                parameter '{param.name}'\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
        | .expr e =>
            match subst.find? key with
            | some inferred =>
                unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                  throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred
            | none => subst := subst.insert key e
        | .app _ _ =>
            let (e, nestedGoals) ←
              diagnoseInternalTacticArgWithHoles target sig { innerGoal with target := paramTy }
              argSpec allowHoles tacticName
            newGoals := newGoals ++ nestedGoals
            match subst.find? key with
            | some inferred =>
                unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                  throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred true
            | none => subst := subst.insert key e
        | .refineHole =>
            unless allowHoles do
              throw s!"object tactic `exact {rawName}` does not accept refinement hole `?_`; use \
                `refine` or provide a complete argument"
            newGoals := newGoals.push { ctx := innerGoal.ctx, target := paramTy }
            subst := subst.insert key (internalObjectGoalPlaceholder param.name)
  for premiseTarget in cand.subgoalTargets do
    let some argSpec := args[argIdx]?
      | throw s!"internal error: missing checked object tactic argument"
    argIdx := argIdx + 1
    let premiseGoal := substObjectVars subst premiseTarget
    match argSpec with
    | .inferPlaceholder =>
        throw s!"object tactic `{tacticName} {rawName}` cannot infer placeholder `_` for a \
          premise; write an explicit proof term or \
            `?_`.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
    | .expr _ => pure ()
    | .app _ _ =>
        let (_, nestedGoals) ←
          diagnoseInternalTacticArgWithHoles target sig { innerGoal with target := premiseGoal }
          argSpec allowHoles tacticName
        newGoals := newGoals ++ nestedGoals
    | .refineHole =>
        unless allowHoles do
          throw s!"object tactic `exact {rawName}` does not accept refinement hole `?_`; use \
            `refine` or provide a complete argument"
        newGoals := newGoals.push { ctx := innerGoal.ctx, target := premiseGoal }
  for sc in cand.sideConditions do
    match classifySideConditionHook sc.solver with
    | .builtinTrivial => pure ()
    | .opaque =>
      throw s!"object tactic `{tacticName} {rawName}` cannot synthesize side-condition \
        certificate '{sc.name}'"
  pure newGoals

/-- Simulate one object tactic step as a goal-stack transformation for editor infoview state.
The real checker still uses `compileInternalObjectTactics`; this pass is diagnostic only. -/
def stepInternalObjectTacticInfoState (target : InternalDefTarget) (sig : HLSignature) (levels :
  Array Name)
    (goals : Array InternalObjectGoal) (step : InternalTacticStep) :
      Except String (Array InternalObjectGoal) := do
  let some goal := goals[0]?
    | throw s!"no remaining object goals"
  let rest := goals.extract 1 goals.size
  match step with
  | .exactTerm _ | .refineTerm _ | .exactApp _ _ =>
      pure rest
  | .refineApp n args =>
      let subgoals ← internalObjectRefineDiagnosticSubgoals target sig goal n args true "refine"
      pure (subgoals ++ rest)
  | .showGoal newGoal =>
      unless objectGoalsConvertible sig levels goal.ctx goal.target newGoal do
        throw s!"object tactic `show` cannot replace current goal"
      pure (#[{ goal with target := newGoal }] ++ rest)
  | .changeGoal newGoal =>
      match objectGoalConversionCheck sig levels goal.ctx goal.target newGoal with
      | .ok _ => pure (#[{ goal with target := newGoal }] ++ rest)
      | .error _ =>
          if objectGoalsConvertible sig levels goal.ctx goal.target newGoal then
            pure (#[{ goal with target := newGoal }] ++ rest)
          else
            throw s!"object tactic `change` cannot replace current goal"
  | .rwRule n symm =>
      let newGoal ← rewriteObjectGoalForTactic target sig levels goal.ctx goal.target n symm
      pure (#[{ goal with target := newGoal }] ++ rest)
  | .rwRules items =>
      let newGoal ← rewriteObjectGoalSeqForTactic target sig levels goal.ctx goal.target items
      pure (#[{ goal with target := newGoal }] ++ rest)
  | .simp =>
      let newGoal ← simpObjectGoal target sig levels goal.ctx goal.target
      pure (#[{ goal with target := newGoal }] ++ rest)
  | .simpRules names onlyMode =>
      let newGoal ← simpObjectGoal target sig levels goal.ctx goal.target { names, onlyMode }
      pure (#[{ goal with target := newGoal }] ++ rest)
  | .assumption =>
      let (_, innerGoal) := autoIntroGoal goal
      let some _ := findAssumption? sig levels innerGoal.ctx innerGoal.target
        | throw s!"object tactic `assumption` failed"
      pure rest
  | .applyName n =>
      let (_, innerGoal) := autoIntroGoal goal
      let some cand := findInternalApplyCandidate? target sig n
        | throw s!"object tactic `apply {n}` failed: unknown rule or internal declaration"
      let some subst0 := matchInternalCandidateConclusion? sig innerGoal.ctx cand.params
          cand.conclusionExpr innerGoal.target
        | throw s!"object tactic `apply {n}` failed: conclusion does not match current goal"
      let mut subst := subst0
      let mut newGoals : Array InternalObjectGoal := #[]
      for param in cand.params do
        let key := param.name.eraseMacroScopes
        match subst.find? key with
        | some _ => pure ()
        | none =>
            let paramTy := substObjectVars subst param.typeExpr
            newGoals := newGoals.push { ctx := innerGoal.ctx, target := paramTy }
            subst := subst.insert key (internalObjectGoalPlaceholder param.name)
      for premiseTarget in cand.subgoalTargets do
        newGoals := newGoals.push {
          ctx := innerGoal.ctx
          target := substObjectVars subst premiseTarget
        }
      for sc in cand.sideConditions do
        match classifySideConditionHook sc.solver with
        | .builtinTrivial => pure ()
        | .opaque =>
          throw s!"object tactic `apply {n}` cannot synthesize side-condition certificate \
            '{sc.name}'"
      pure (newGoals ++ rest)
  | .focusBullet =>
      pure goals
  | .intro n =>
      pure (#[← introObjectGoal goal n] ++ rest)
  | .intros ns =>
      pure (#[← introsObjectGoal goal ns] ++ rest)
  | .haveDecl n type _ | .haveTerm n type _ =>
      if internalObjectContextHasName goal.ctx n then
        throw s!"object tactic `have {n}` failed: local name '{n}' is already in the object context"
      let nextGoal := {
        goal with ctx := goal.ctx.push { name := n, typeExpr := type, visibility := .explicit } }
      pure (#[nextGoal] ++ rest)
  | .haveMissingEnd n =>
      throw s!"object tactic `have {n}` is missing `end`; write `have {n} : ... := by ... end` \
        or use term-mode `have {n} : ... := proof`"
  | .sorry =>
      pure rest

/-- Syntax span for a tactic step, with a harmless fallback for malformed arrays. -/
def internalTacticStepSyntaxAt (stepStxs : Array Syntax) (idx : Nat) : Syntax :=
  stepStxs[idx]?.getD Syntax.missing

/-- Append one object-tactic infoview snapshot. -/
def pushInternalObjectTacticInfo (infos : Array InternalObjectTacticInfo) (stepStxs : Array Syntax)
    (idx : Nat) (before after : Array InternalObjectGoal) : Array InternalObjectTacticInfo :=
  infos.push { stx := internalTacticStepSyntaxAt stepStxs idx, goalsBefore := before, goalsAfter :=
    after }

/-- Compute the diagnostic subgoals created by an object `apply` step.
This mirrors the real compiler enough to drive infoview state; dependent unsolved parameters are
represented by placeholders until their proof terms have been compiled by the authoritative path. -/
def internalObjectApplyDiagnosticSubgoals (target : InternalDefTarget) (sig : HLSignature)
    (goal : InternalObjectGoal) (rawName : Name) : Except String (Array InternalObjectGoal) := do
  let (_, innerGoal) := autoIntroGoal goal
  let some cand := findInternalApplyCandidate? target sig rawName
    | throw s!"object tactic `apply {rawName}` failed: unknown rule or internal declaration"
  let some subst0 := matchInternalCandidateConclusion? sig innerGoal.ctx cand.params
      cand.conclusionExpr innerGoal.target
    | throw s!"object tactic `apply {rawName}` failed: conclusion does not match current goal"
  let mut subst := subst0
  let mut newGoals : Array InternalObjectGoal := #[]
  for param in cand.params do
    let key := param.name.eraseMacroScopes
    match subst.find? key with
    | some _ => pure ()
    | none =>
        let paramTy := substObjectVars subst param.typeExpr
        newGoals := newGoals.push { ctx := innerGoal.ctx, target := paramTy }
        subst := subst.insert key (internalObjectGoalPlaceholder param.name)
  for premiseTarget in cand.subgoalTargets do
    newGoals := newGoals.push {
      ctx := innerGoal.ctx
      target := substObjectVars subst premiseTarget
    }
  for sc in cand.sideConditions do
    match classifySideConditionHook sc.solver with
    | .builtinTrivial => pure ()
    | .opaque =>
      throw s!"object tactic `apply {rawName}` cannot synthesize side-condition certificate \
        '{sc.name}'"
  pure newGoals

mutual
  /-- Collect infoview snapshots while recursively following focused subgoal blocks. -/
  partial def collectInternalObjectTacticGoalInfo (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (stepStxs : Array Syntax)
      (idx : Nat) (goal : InternalObjectGoal) : Array InternalObjectTacticInfo × Nat := Id.run do
    let some step := steps[idx]?
      | return (#[], idx)
    let before := #[goal]
    match step with
    | .focusBullet =>
        collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1) goal
    | .exactTerm _ | .refineTerm _ | .exactApp _ _ | .assumption | .sorry =>
        return (pushInternalObjectTacticInfo #[] stepStxs idx before #[], idx + 1)
    | .showGoal newGoal =>
        if objectGoalsConvertible sig levels goal.ctx goal.target newGoal then
          let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[{ goal with target :=
            newGoal }]
          let (tail, nextIdx) :=
            collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1) { goal
              with target := newGoal }
          return (head ++ tail, nextIdx)
        else
          return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .changeGoal newGoal =>
        let ok :=
          match objectGoalConversionCheck sig levels goal.ctx goal.target newGoal with
          | .ok _ => true
          | .error _ => objectGoalsConvertible sig levels goal.ctx goal.target newGoal
        if ok then
          let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[{ goal with target :=
            newGoal }]
          let (tail, nextIdx) :=
            collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1) { goal
              with target := newGoal }
          return (head ++ tail, nextIdx)
        else
          return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .rwRule n symm =>
        match rewriteObjectGoalForTactic target sig levels goal.ctx goal.target n symm with
        | .ok newGoal =>
            let nextGoal := { goal with target := newGoal }
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .rwRules items =>
        match rewriteObjectGoalSeqForTactic target sig levels goal.ctx goal.target items with
        | .ok newGoal =>
            let nextGoal := { goal with target := newGoal }
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .simp =>
        match simpObjectGoal target sig levels goal.ctx goal.target with
        | .ok newGoal =>
            let nextGoal := { goal with target := newGoal }
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .simpRules names onlyMode =>
        match simpObjectGoal target sig levels goal.ctx goal.target { names, onlyMode } with
        | .ok newGoal =>
            let nextGoal := { goal with target := newGoal }
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .applyName n =>
        match internalObjectApplyDiagnosticSubgoals target sig goal n with
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
        | .ok subgoals =>
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before subgoals
            let (tail, nextIdx) :=
              collectInternalObjectTacticSubgoalsInfo target sig levels steps stepStxs (idx + 1)
                subgoals
            return (head ++ tail, nextIdx)
    | .refineApp n args =>
        match internalObjectRefineDiagnosticSubgoals target sig goal n args true "refine" with
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
        | .ok subgoals =>
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before subgoals
            let (tail, nextIdx) :=
              collectInternalObjectTacticSubgoalsInfo target sig levels steps stepStxs (idx + 1)
                subgoals
            return (head ++ tail, nextIdx)
    | .intro n =>
        match introObjectGoal goal n with
        | .ok nextGoal =>
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .intros ns =>
        match introsObjectGoal goal ns with
        | .ok nextGoal =>
            let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
            let (tail, nextIdx) :=
              collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1)
                nextGoal
            return (head ++ tail, nextIdx)
        | .error _ =>
            return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
    | .haveDecl n type body =>
        if internalObjectContextHasName goal.ctx n then
          return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
        let haveGoal := { goal with target := type }
        let subStxs := body.map fun _ => Syntax.missing
        let (subInfos, _) := collectInternalObjectTacticGoalInfo target sig levels body subStxs 0
          haveGoal
        let nextGoal := {
          goal with ctx := goal.ctx.push { name := n, typeExpr := type, visibility := .explicit } }
        let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[haveGoal, nextGoal]
        let (tail, nextIdx) :=
          collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1) nextGoal
        return (head ++ subInfos ++ tail, nextIdx)
    | .haveTerm n type _ =>
        if internalObjectContextHasName goal.ctx n then
          return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)
        let nextGoal := {
          goal with ctx := goal.ctx.push { name := n, typeExpr := type, visibility := .explicit } }
        let head := pushInternalObjectTacticInfo #[] stepStxs idx before #[nextGoal]
        let (tail, nextIdx) :=
          collectInternalObjectTacticGoalInfo target sig levels steps stepStxs (idx + 1) nextGoal
        return (head ++ tail, nextIdx)
    | .haveMissingEnd _ =>
        return (pushInternalObjectTacticInfo #[] stepStxs idx before before, idx + 1)

  /-- Collect snapshots for subgoals produced by an `apply`, honoring Lean-style focus bullets. -/
  partial def collectInternalObjectTacticSubgoalsInfo (target : InternalDefTarget) (sig :
    HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (stepStxs : Array Syntax)
      (idx : Nat) (subgoals : Array InternalObjectGoal) : Array InternalObjectTacticInfo × Nat :=
        Id.run do
    let useBullets := internalTacticStepAtIsFocusBullet steps idx
    let mut infos := #[]
    let mut nextIdx := idx
    for subgoal in subgoals do
      if useBullets then
        if internalTacticStepAtIsFocusBullet steps nextIdx then
          infos := pushInternalObjectTacticInfo infos stepStxs nextIdx #[subgoal] #[subgoal]
          nextIdx := nextIdx + 1
        else
          return (infos, nextIdx)
      let (subInfos, nextIdx') :=
        collectInternalObjectTacticGoalInfo target sig levels steps stepStxs nextIdx subgoal
      infos := infos ++ subInfos
      nextIdx := nextIdx'
    return (infos, nextIdx)
end

/-- Build diagnostic goal-state entries for an internal object tactic script.
This pass is editor-only and deliberately mirrors subgoal focus: tactic snapshots inside a `·`
block display only the focused object goal, while the real checker below remains authoritative. -/
def collectInternalObjectTacticInfo (target : InternalDefTarget) (sig : HLSignature) (levels :
  Array Name)
    (typeExpr : ObjExpr) (steps : Array InternalTacticStep) (stepStxs : Array Syntax) :
      Array InternalObjectTacticInfo :=
  (collectInternalObjectTacticGoalInfo target sig levels steps stepStxs 0 { target := typeExpr }).1

/-- Lean proposition type used for one object-theory goal in the ordinary Lean infoview. -/
def internalObjectGoalViewType (target : InternalDefTarget) (goal : InternalObjectGoal) : Expr :=
  mkApp3 (mkConst ``InternalObjectGoalView)
    (mkStrLit target.theoryName.eraseMacroScopes.toString)
    (mkStrLit (renderInternalObjectContext goal.ctx))
    (mkStrLit (toString goal.target))

/-- Create Lean metavariables whose targets encode object-theory goals for infoview display. -/
def mkInternalObjectGoalMVars (target : InternalDefTarget) (goals : Array InternalObjectGoal) :
  TermElabM (List MVarId) := do
  goals.toList.mapM fun goal => do
    let mvar ← Meta.mkFreshExprMVar (some (internalObjectGoalViewType target goal)) .natural `object
    pure mvar.mvarId!

/-- Description shown when hovering over a name in an internal tactic script. -/
structure InternalObjectHover where
  kind : String
  name : Name
  typeOrStatement : String
  deriving Inhabited, Repr, BEq

/-- Resolve a tactic identifier to a small hover payload. -/
def internalObjectHover? (target : InternalDefTarget) (sig : HLSignature) (goal :
    InternalObjectGoal) (rawName : Name) : Option InternalObjectHover := Id.run do
  let n := internalTacticObjectName target rawName
  if let some h := goal.ctx.find? (fun h => sameObjectName h.name n) then
    return some {
      kind := "local assumption"
      name := n
      typeOrStatement := diagnosticObjExprString h.typeExpr }
  if let some d := sig.lfObjectDefs.find? (fun d => sameObjectName d.name n) then
    return some {
      kind := "internal definition"
      name := n
      typeOrStatement := diagnosticObjExprString d.typeExpr }
  if let some c := sig.lfOpaqueConsts.find? (fun c => sameObjectName c.name n) then
    let ty? := c.typeExpr?.map fun ty =>
      if c.params.isEmpty then ty else objectArrowTelescope c.params ty
    return some {
      kind := "LF constant"
      name := n
      typeOrStatement := (ty?.map diagnosticObjExprString).getD "untyped" }
  if let some t := sig.lfJudgmentTheorems.find? (fun t => sameObjectName t.name n) then
    let statement :=
      if t.binders.isEmpty then t.judgmentExpr else objectArrowTelescope t.binders t.judgmentExpr
    return some {
      kind := "theorem"
      name := n
      typeOrStatement := diagnosticObjExprString statement }
  if let some r := sig.rules.find? (fun r => sameObjectName r.name n) then
    let premiseBinders := r.premises.map fun p => {
      name := p.name, typeExpr := p.judgmentExpr, visibility := BinderVisibility.explicit }
    let statement := objectArrowTelescope (r.params ++ premiseBinders) r.conclusionExpr
    return some {
      kind := "rule"
      name := n
      typeOrStatement := diagnosticObjExprString statement }
  if let some s := sig.syntaxSorts.find? (fun s => sameObjectName s.name n) then
    let ty := diagnosticObjExprString <|
      if s.params.isEmpty then .sort else objectArrowTelescope s.params .sort
    return some { kind := "syntax sort", name := n, typeOrStatement := ty }
  if let some j := sig.judgments.find? (fun j => sameObjectName j.name n) then
    let ty := diagnosticObjExprString <|
      if j.params.isEmpty then .sort else objectArrowTelescope j.params .sort
    return some { kind := "judgment", name := n, typeOrStatement := ty }
  return none

/-- Extract the resolved name from identifier syntax. -/
def internalSyntaxIdentName? : Syntax → Option Name
  | .ident _ _ val _ => some val
  | _ => none

/-- Collect identifier syntax nodes below a tactic syntax node. -/
partial def collectInternalIdentSyntaxes (stx : Syntax) : Array Syntax :=
  match stx with
  | .ident .. => #[stx]
  | _ =>
      stx.getArgs.foldl (init := #[]) fun acc child => acc ++ collectInternalIdentSyntaxes child

/-- Build the Lean marker type used for hover text. -/
def internalHoverViewType (target : InternalDefTarget) (hover : InternalObjectHover) : Expr :=
  mkApp4 (mkConst ``InternalHoverView)
    (mkStrLit target.theoryName.eraseMacroScopes.toString)
    (mkStrLit hover.kind)
    (mkStrLit hover.name.eraseMacroScopes.toString)
    (mkStrLit hover.typeOrStatement)

/-- Save hover term-info nodes for recognized names in one internal tactic step. -/
def saveInternalObjectHoverInfo (target : InternalDefTarget) (sig : HLSignature)
    (info : InternalObjectTacticInfo) : CommandElabM Unit := do
  let some goal := info.goalsBefore[0]?
    | return ()
  for stx in collectInternalIdentSyntaxes info.stx do
    let some rawName := internalSyntaxIdentName? stx
      | pure ()
    if let some hover := internalObjectHover? target sig goal rawName then
      liftTermElabM do
        let expr ← Meta.mkFreshExprMVar (some (internalHoverViewType target hover)) .natural
          `internal_hover
        pushInfoLeaf <| .ofTermInfo {
          elaborator := `InternalLean.internalObjectHoverInfo
          stx := stx
          lctx := (← getLCtx)
          expectedType? := none
          expr := expr
          isBinder := false
          isDisplayableTerm := false
        }

/-- Save ordinary Lean `TacticInfo` nodes for object-theory tactic steps, so VS Code/infoview
can show the current object context and target while editing `internal def ... := by`. -/
def saveInternalObjectTacticInfo (target : InternalDefTarget) (sig : HLSignature)
    (infos : Array InternalObjectTacticInfo) : CommandElabM Unit := do
  for info in infos do
    liftTermElabM do
      let goalsBefore ← mkInternalObjectGoalMVars target info.goalsBefore
      let mctxBefore ← getMCtx
      let goalsAfter ← mkInternalObjectGoalMVars target info.goalsAfter
      let mctxAfter ← getMCtx
      pushInfoLeaf <| .ofTacticInfo {
        elaborator := `InternalLean.internalObjectTacticInfo
        stx := info.stx
        mctxBefore := mctxBefore
        goalsBefore := goalsBefore
        mctxAfter := mctxAfter
        goalsAfter := goalsAfter
      }
    saveInternalObjectHoverInfo target sig info

/-- Prefix used internally to carry the source tactic index through recursive compilation. -/
def internalStepErrorPrefix : String := "__internal_object_tactic_step__"

/-- Encode a tactic-step index in an error without changing the user-facing message after decoding.
-/
def encodeInternalStepError (idx : Nat) (err : String) : String :=
  s!"{internalStepErrorPrefix}{idx}\n{err}"

/-- Decode an internally tagged tactic-step error. -/
def decodeInternalStepError? (err : String) : Option (Nat × String) :=
  if err.startsWith internalStepErrorPrefix then
    let rest := (err.drop internalStepErrorPrefix.length).toString
    match rest.splitOn "\n" with
    | idx :: msgLines => do
        let idx ← idx.toNat?
        some (idx, String.intercalate "\n" msgLines)
    | [] => none
  else
    none

mutual
  /-- Compile one object tactic goal, returning the synthesized term and next unconsumed step index.
  -/
  partial def compileInternalObjectGoal (target : InternalDefTarget) (sig : HLSignature) (levels :
    Array Name)
      (steps : Array InternalTacticStep) (idx : Nat) (goal : InternalObjectGoal) :
        Except String (ObjExpr × Nat) := do
    let some step := steps[idx]?
      | throw <| String.intercalate "\n" [
          s!"unsolved object goal in `internal def {target.anchorName}`:",
          s!"  {diagnosticObjExprString goal.target}",
          "",
          "Remaining goal context:",
          renderInternalObjectContext goal.ctx]
    try match step with
    | .focusBullet =>
        compileInternalObjectGoal target sig levels steps (idx + 1) goal
    | .exactTerm e =>
        let e ← elaborateInternalDirectTermPlaceholders target sig goal.ctx goal.target e
        pure (e, idx + 1)
    | .exactApp n args =>
        let (introNames, innerGoal) := autoIntroGoal goal
        let (termExpr, nextIdx) ←
          compileInternalCandidateApp target sig levels steps (idx + 1) innerGoal n args false
            "exact"
        pure (wrapObjectLambdas introNames termExpr, nextIdx)
    | .refineTerm e =>
        let e ← elaborateInternalDirectTermPlaceholders target sig goal.ctx goal.target e
        pure (e, idx + 1)
    | .refineApp n args =>
        let (introNames, innerGoal) := autoIntroGoal goal
        let (termExpr, nextIdx) ←
          compileInternalCandidateApp target sig levels steps (idx + 1) innerGoal n args true
            "refine"
        pure (wrapObjectLambdas introNames termExpr, nextIdx)
    | .showGoal newGoal =>
        unless objectGoalsConvertible sig levels goal.ctx goal.target newGoal do
          throw <| String.intercalate "\n" [
            "object tactic `show` cannot replace goal",
            s!"  {diagnosticObjExprString goal.target}",
            "with non-convertible/non-identical object goal",
            s!"  {diagnosticObjExprString newGoal}",
            "",
            "This is object judgmental conversion, not Lean equality."]
        compileInternalObjectGoal target sig levels steps (idx + 1) { goal with target := newGoal }
    | .changeGoal newGoal =>
        match objectGoalConversionCheck sig levels goal.ctx goal.target newGoal with
        | .ok _ =>
          compileInternalObjectGoal target sig levels steps (idx + 1) { goal with target :=
          newGoal }
        | .error err =>
            if objectGoalsConvertible sig levels goal.ctx goal.target newGoal then
              compileInternalObjectGoal target sig levels steps (idx + 1) { goal with target :=
                newGoal }
            else
              throw <| String.intercalate "\n" [
                s!"object tactic `change` cannot replace goal\n  \
                  {diagnosticObjExprString goal.target}",
                s!"with\n  {diagnosticObjExprString newGoal}",
                "",
                "The endpoints are not judgmentally convertible in the active object theory. ",
                "This tactic checks object conversion evidence; it does not use Lean equality ",
                "or an internal equality proof.",
                "",
                s!"conversion failure: {err}",
                "",
                objectGoalNormalizationMismatchString sig goal.ctx goal.target newGoal]
    | .rwRule n symm =>
        compileInternalObjectRwStep target sig levels steps (idx + 1) goal n symm
    | .rwRules items =>
        if items.isEmpty then
          throw "object tactic `rw []` failed: rewrite list is empty"
        compileInternalObjectRwSeq target sig levels steps (idx + 1) goal items 0
    | .simp =>
        let simpResult ← simpObjectGoalDetailed target sig levels goal.ctx goal.target
        let (sourceProof, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          { goal with target := simpResult.newGoal }
        let proof ← wrapObjectSimpTransports target sig levels goal.ctx simpResult.rewrites
          sourceProof
        pure (proof, nextIdx)
    | .simpRules names onlyMode =>
        let simpResult ← simpObjectGoalDetailed target sig levels goal.ctx goal.target
          { names, onlyMode }
        let (sourceProof, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          { goal with target := simpResult.newGoal }
        let proof ← wrapObjectSimpTransports target sig levels goal.ctx simpResult.rewrites
          sourceProof
        pure (proof, nextIdx)
    | .assumption =>
        let (introNames, innerGoal) := autoIntroGoal goal
        let some hypName := findAssumption? sig levels innerGoal.ctx innerGoal.target
          | throw <| String.intercalate "\n" [
              "object tactic `assumption` failed for goal",
              s!"  {diagnosticObjExprString innerGoal.target}",
              "",
              "Available object hypotheses:",
              renderInternalObjectContext innerGoal.ctx]
        pure (wrapObjectLambdas introNames (.ident hypName), idx + 1)
    | .applyName n =>
        let (introNames, innerGoal) := autoIntroGoal goal
        let (termExpr, nextIdx) ← compileInternalApply target sig levels steps (idx + 1) innerGoal n
        pure (wrapObjectLambdas introNames termExpr, nextIdx)
    | .intro n =>
        let goal' ← introObjectGoal goal n
        let (termExpr, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          goal'
        pure (wrapObjectLambdas #[n] termExpr, nextIdx)
    | .intros ns =>
        let goal' ← introsObjectGoal goal ns
        let (termExpr, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          goal'
        pure (wrapObjectLambdas ns termExpr, nextIdx)
    | .haveDecl n type body =>
        if internalObjectContextHasName goal.ctx n then
          throw <| s!"object tactic `have {n}` failed: local name '{n}' is already " ++
            "in the object context"
        let (proofExpr, proofNextIdx) ← compileInternalObjectGoal target sig levels body 0
          { goal with target := type }
        unless proofNextIdx == body.size do
          throw <| s!"object tactic `have {n}` proof left unused tactic step(s) " ++
            s!"starting at index {proofNextIdx}"
        let nextGoal := {
          goal with ctx := goal.ctx.push { name := n, typeExpr := type, visibility := .explicit } }
        let (termExpr, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          nextGoal
        let subst := ({} : NameMap ObjExpr).insert n.eraseMacroScopes proofExpr
        pure (substObjectVars subst termExpr, nextIdx)
    | .haveTerm n type proof =>
        if internalObjectContextHasName goal.ctx n then
          throw <| s!"object tactic `have {n}` failed: local name '{n}' is already " ++
            "in the object context"
        let proofExpr ← elaborateInternalHaveTermProof target sig levels goal.ctx type proof n
        let nextGoal := {
          goal with ctx := goal.ctx.push { name := n, typeExpr := type, visibility := .explicit } }
        let (termExpr, nextIdx) ← compileInternalObjectGoal target sig levels steps (idx + 1)
          nextGoal
        let subst := ({} : NameMap ObjExpr).insert n.eraseMacroScopes proofExpr
        pure (substObjectVars subst termExpr, nextIdx)
    | .haveMissingEnd n =>
        throw s!"object tactic `have {n}` is missing `end`; write `have {n} : ... := by ... end` \
          or use term-mode `have {n} : ... := proof`"
    | .sorry =>
        throw s!"internal object tactic `sorry` is handled as a declaration-wide admission before \
          tactic compilation"
    catch err =>
      match decodeInternalStepError? err with
      | some _ => throw err
      | none => throw (encodeInternalStepError idx err)

  /-- Compile after one `rw` and wrap the resulting proof if transport is needed. -/
  partial def compileInternalObjectRwStep (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (nextIdx : Nat)
      (goal : InternalObjectGoal) (rawName : Name) (symm : Bool) :
      Except String (ObjExpr × Nat) := do
    let app ← findObjectRewriteApplication target sig goal.target rawName symm
    match checkObjectGoalConversion sig levels goal.ctx goal.target app.newGoal with
    | .ok _ =>
        compileInternalObjectGoal target sig levels steps nextIdx
          { goal with target := app.newGoal }
    | .error _ =>
        match buildObjectRewriteTransportTerm target sig levels goal.ctx app rawName
            (.ident (.str .anonymous "?rw_source")) with
        | .error transportError =>
            throw <| String.intercalate "\n" [
              objectRewriteConversionFailureMessage app rawName symm,
              "No declared proof/evidence transport could justify this rewrite either.",
              transportError]
        | .ok _ =>
            let (sourceProof, nextIdx') ← compileInternalObjectGoal target sig levels steps
              nextIdx { goal with target := app.newGoal }
            let transported ← buildObjectRewriteTransportTerm target sig levels goal.ctx app rawName
              sourceProof
            pure (transported, nextIdx')

  /-- Compile the continuation after a `rw [...]` sequence, wrapping transports inside-out. -/
  partial def compileInternalObjectRwSeq (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (nextIdx : Nat)
      (goal : InternalObjectGoal) (items : Array (Name × Bool)) (itemIdx : Nat) :
      Except String (ObjExpr × Nat) := do
    let some item := items[itemIdx]?
      | compileInternalObjectGoal target sig levels steps nextIdx goal
    let (rawName, symm) := item
    let app ← findObjectRewriteApplication target sig goal.target rawName symm
    match checkObjectGoalConversion sig levels goal.ctx goal.target app.newGoal with
    | .ok _ =>
        compileInternalObjectRwSeq target sig levels steps nextIdx
          { goal with target := app.newGoal } items (itemIdx + 1)
    | .error _ =>
        match buildObjectRewriteTransportTerm target sig levels goal.ctx app rawName
            (.ident (.str .anonymous "?rw_source")) with
        | .error transportError =>
            throw <| String.intercalate "\n" [
              objectRewriteConversionFailureMessage app rawName symm,
              "No declared proof/evidence transport could justify this rewrite either.",
              transportError]
        | .ok _ =>
            let (sourceProof, nextIdx') ← compileInternalObjectRwSeq target sig levels steps
              nextIdx { goal with target := app.newGoal } items (itemIdx + 1)
            let transported ← buildObjectRewriteTransportTerm target sig levels goal.ctx app rawName
              sourceProof
            pure (transported, nextIdx')

  /-- Consume one `refine` hole, preserving the surrounding focus-bullet discipline. -/
  partial def compileInternalRefineHole (target : InternalDefTarget) (sig : HLSignature) (levels :
    Array Name)
      (steps : Array InternalTacticStep) (idx : Nat) (goal : InternalObjectGoal)
      (rawName candName : Name) (useBullets? : Option Bool) (tacticName : String) :
      Except String (ObjExpr × Nat × Option Bool) := do
    let useBullets? := match useBullets? with
      | some b => some b
      | none => some (internalTacticStepAtIsFocusBullet steps idx)
    let useBullets := useBullets?.getD false
    if useBullets && !internalTacticStepAtIsFocusBullet steps idx then
      throw s!"object tactic `{tacticName} {rawName}` expected focus bullet `·` before the next \
        refinement hole for rule or declaration '{candName}'"
    let startIdx := if useBullets then idx + 1 else idx
    let (arg, nextIdx) ← compileInternalObjectGoal target sig levels steps startIdx goal
    pure (arg, nextIdx, useBullets?)

  /-- Compile a nested `refine` argument. Nested `?_` holes are solved by following tactic
  steps in depth-first left-to-right order. -/
  partial def compileInternalTacticArgWithHoles (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (idx : Nat)
      (goal : InternalObjectGoal) (arg : InternalTacticArg) (allowHoles : Bool)
      (tacticName : String) (useBullets? : Option Bool) :
      Except String (ObjExpr × Nat × Option Bool) := do
    match arg with
    | .expr e => pure (e, idx, useBullets?)
    | .inferPlaceholder =>
        throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` without a \
          candidate head.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
    | .refineHole =>
        unless allowHoles do
          throw s!"object tactic `exact` does not accept nested refinement hole `?_`; provide a \
            complete argument"
        compileInternalRefineHole target sig levels steps idx goal `_nested `_nested useBullets?
          tacticName
    | .app rawName args =>
        compileInternalCandidateArgWithHoles target sig levels steps idx goal rawName args
          allowHoles tacticName useBullets?

  /-- Compile a nested head application, allowing nested `?_` holes when called from `refine`. -/
  partial def compileInternalCandidateArgWithHoles (target : InternalDefTarget) (sig : HLSignature)
      (levels : Array Name) (steps : Array InternalTacticStep) (idx : Nat) (goal :
        InternalObjectGoal)
      (rawName : Name) (suppliedArgs : Array InternalTacticArg) (allowHoles : Bool)
      (tacticName : String) (useBullets? : Option Bool) :
        Except String (ObjExpr × Nat × Option Bool) := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throw s!"object tactic `{tacticName}` failed to elaborate nested application `{rawName}`: \
        unknown rule or internal declaration '{rawName}' in type theory '{target.theoryName}'"
    checkInternalCandidateAppArity tacticName rawName suppliedArgs.size cand
    let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throw <| s!"object tactic `{tacticName}` failed to elaborate nested application " ++
          s!"`{rawName}`: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target
    let mut outArgs : Array ObjExpr := #[]
    let mut subst := subst0
    let mut nextIdx := idx
    let mut useBullets? := useBullets?
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
          | some inferred => outArgs := outArgs.push inferred
          | none =>
              throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                false true
      | some argSpec =>
          argIdx := argIdx + 1
          match argSpec with
          | .inferPlaceholder =>
              match subst.find? key with
              | some inferred => outArgs := outArgs.push inferred
              | none =>
                  throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                    true true
          | .refineHole =>
              unless allowHoles do
                throw s!"object tactic `exact` does not accept nested refinement hole `?_`; \
                  provide a complete argument"
              let (arg, nextIdx', useBullets') ←
                compileInternalRefineHole target sig levels steps nextIdx { goal with target :=
                paramTy } rawName cand.name useBullets? tacticName
              nextIdx := nextIdx'
              useBullets? := useBullets'
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalRefineHoleMismatchMessage tacticName rawName param.name arg
                      inferred
              | none => pure ()
              subst := subst.insert key arg
              outArgs := outArgs.push arg
          | .expr e =>
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred
              | none => subst := subst.insert key e
              outArgs := outArgs.push e
          | .app _ _ =>
              let (arg, nextIdx', useBullets') ←
                compileInternalTacticArgWithHoles target sig levels steps nextIdx { goal with
                  target := paramTy } argSpec allowHoles tacticName useBullets?
              nextIdx := nextIdx'
              useBullets? := useBullets'
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name arg
                      inferred true
              | none => subst := subst.insert key arg
              outArgs := outArgs.push arg
    for premiseTarget in cand.subgoalTargets do
      let some argSpec := suppliedArgs[argIdx]?
        | throw s!"internal error: missing checked object tactic argument"
      argIdx := argIdx + 1
      let premiseGoal := substObjectVars subst premiseTarget
      match argSpec with
      | .inferPlaceholder =>
          throw s!"object tactic `{tacticName}` cannot infer nested placeholder `_` for a premise \
            in application `{rawName}`; write an explicit proof term or \
              `?_`.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
      | .refineHole =>
          unless allowHoles do
            throw s!"object tactic `exact` does not accept nested refinement hole `?_`; provide a \
              complete argument"
          let (arg, nextIdx', useBullets') ←
            compileInternalRefineHole target sig levels steps nextIdx { goal with target :=
            premiseGoal } rawName cand.name useBullets? tacticName
          nextIdx := nextIdx'
          useBullets? := useBullets'
          outArgs := outArgs.push arg
      | .expr e =>
          checkInternalPremiseProofExpr target sig levels goal.ctx e premiseGoal tacticName rawName
          outArgs := outArgs.push e
      | .app _ _ =>
          let (arg, nextIdx', useBullets') ←
            compileInternalTacticArgWithHoles target sig levels steps nextIdx { goal with target :=
            premiseGoal } argSpec allowHoles tacticName useBullets?
          nextIdx := nextIdx'
          useBullets? := useBullets'
          outArgs := outArgs.push arg
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throw <| internalOpaqueSideConditionMessage tacticName rawName rawName sc.name
            sc.solver scInput
    pure (mkObjectApps (.ident cand.name) outArgs, nextIdx, useBullets?)

  /-- Compile a goal-directed `exact`/`refine` head application.

  The argument list is fully explicit: `_` consumes an inferred slot without creating a
  subgoal, while `?_` (only for `refine`) creates exactly one object-theory subgoal. -/
  partial def compileInternalCandidateApp (target : InternalDefTarget) (sig : HLSignature) (
    levels : Array Name)
      (steps : Array InternalTacticStep) (idx : Nat) (goal : InternalObjectGoal) (rawName : Name)
      (suppliedArgs : Array InternalTacticArg) (allowHoles : Bool) (tacticName : String) :
        Except String (ObjExpr × Nat) := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throw s!"object tactic `{tacticName} {rawName}` failed: unknown rule or internal \
        declaration '{rawName}' in type theory '{target.theoryName}'"
    checkInternalCandidateAppArity tacticName rawName suppliedArgs.size cand
    let some subst0 := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throw <| s!"object tactic `{tacticName} {rawName}` failed: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target
    let mut args : Array ObjExpr := #[]
    let mut subst := subst0
    let mut nextIdx := idx
    let mut useBullets? : Option Bool := none
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
          | some inferred => args := args.push inferred
          | none =>
              throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                false false
      | some argSpec =>
          argIdx := argIdx + 1
          match argSpec with
          | .inferPlaceholder =>
              match subst.find? key with
              | some inferred => args := args.push inferred
              | none =>
                  throw <| internalCannotInferParameterMessage tacticName rawName param.name paramTy
                    true false
          | .expr e =>
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx e inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name e
                      inferred
              | none => subst := subst.insert key e
              args := args.push e
          | .app _ _ =>
              let arg ←
                if allowHoles then
                  let (arg, nextIdx', useBullets') ←
                    compileInternalTacticArgWithHoles target sig levels steps nextIdx { goal with
                      target := paramTy } argSpec allowHoles tacticName useBullets?
                  nextIdx := nextIdx'
                  useBullets? := useBullets'
                  pure arg
                else
                  compileInternalCompleteTacticArg target sig { goal with target := paramTy }
                    argSpec tacticName
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalArgumentMismatchMessage tacticName rawName param.name arg
                      inferred true
              | none => subst := subst.insert key arg
              args := args.push arg
          | .refineHole =>
              unless allowHoles do
                throw s!"object tactic `exact {rawName}` does not accept refinement hole `?_`; \
                  use `refine` or provide a complete argument"
              if useBullets?.isNone then
                useBullets? := some (internalTacticStepAtIsFocusBullet steps nextIdx)
              let useBullets := useBullets?.getD false
              if useBullets && !internalTacticStepAtIsFocusBullet steps nextIdx then
                throw s!"object tactic `{tacticName} {rawName}` expected focus bullet `·` before \
                  the next refinement hole for rule or declaration '{cand.name}'"
              let startIdx := if useBullets then nextIdx + 1 else nextIdx
              let (arg, nextIdx') ←
                compileInternalObjectGoal target sig levels steps startIdx { goal with target :=
                paramTy }
              nextIdx := nextIdx'
              match subst.find? key with
              | some inferred =>
                  unless objectGoalsConvertible sig #[] goal.ctx arg inferred do
                    throw <| internalRefineHoleMismatchMessage tacticName rawName param.name arg
                      inferred
              | none => pure ()
              subst := subst.insert key arg
              args := args.push arg
    for premiseTarget in cand.subgoalTargets do
      let some argSpec := suppliedArgs[argIdx]?
        | throw s!"internal error: missing checked object tactic argument"
      argIdx := argIdx + 1
      let premiseGoal := substObjectVars subst premiseTarget
      match argSpec with
      | .inferPlaceholder =>
          throw s!"object tactic `{tacticName} {rawName}` cannot infer placeholder `_` for a \
            premise; write an explicit proof term or \
              `?_`.\n\n{internalObjectTacticPlaceholderAdvice tacticName}"
      | .expr e =>
          checkInternalPremiseProofExpr target sig levels goal.ctx e premiseGoal tacticName rawName
          args := args.push e
      | .app _ _ =>
          let arg ←
            if allowHoles then
              let (arg, nextIdx', useBullets') ←
                compileInternalTacticArgWithHoles target sig levels steps nextIdx { goal with
                  target := premiseGoal } argSpec allowHoles tacticName useBullets?
              nextIdx := nextIdx'
              useBullets? := useBullets'
              pure arg
            else
              compileInternalCompleteTacticArg target sig { goal with target := premiseGoal }
                argSpec tacticName
          args := args.push arg
      | .refineHole =>
          unless allowHoles do
            throw s!"object tactic `exact {rawName}` does not accept refinement hole `?_`; use \
              `refine` or provide a complete argument"
          if useBullets?.isNone then
            useBullets? := some (internalTacticStepAtIsFocusBullet steps nextIdx)
          let useBullets := useBullets?.getD false
          if useBullets && !internalTacticStepAtIsFocusBullet steps nextIdx then
            throw s!"object tactic `{tacticName} {rawName}` expected focus bullet `·` before the \
              next refinement hole for rule or declaration '{cand.name}'"
          let startIdx := if useBullets then nextIdx + 1 else nextIdx
          let (arg, nextIdx') ←
            compileInternalObjectGoal target sig levels steps startIdx { goal with target :=
            premiseGoal }
          nextIdx := nextIdx'
          args := args.push arg
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throw <| internalOpaqueSideConditionMessage tacticName rawName cand.name sc.name
            sc.solver scInput
    pure (mkObjectApps (.ident cand.name) args, nextIdx)

  /-- Compile an `apply` step and recursively solve any argument/premise subgoals it creates. -/
  partial def compileInternalApply (target : InternalDefTarget) (sig : HLSignature) (levels :
    Array Name)
      (steps : Array InternalTacticStep) (idx : Nat) (goal : InternalObjectGoal) (rawName : Name) :
        Except String (ObjExpr × Nat) := do
    let some cand := findInternalApplyCandidate? target sig rawName
      | throw s!"object tactic `apply {rawName}` failed: unknown rule or internal declaration \
        '{rawName}' in type theory '{target.theoryName}'"
    let some subst := matchInternalCandidateConclusion? sig goal.ctx cand.params
        cand.conclusionExpr goal.target
      | throw <| s!"object tactic `apply {rawName}` failed: " ++
          internalCandidateConclusionMismatchMessage sig goal.ctx cand.conclusionExpr goal.target
    let mut args := #[]
    let mut subst := subst
    let mut nextIdx := idx
    let mut useBullets? : Option Bool := none
    for param in cand.params do
      let key := param.name.eraseMacroScopes
      let paramTy := substObjectVars subst param.typeExpr
      match subst.find? key with
      | some arg =>
          args := args.push arg
      | none =>
          if useBullets?.isNone then
            useBullets? := some (internalTacticStepAtIsFocusBullet steps nextIdx)
          let useBullets := useBullets?.getD false
          if useBullets && !internalTacticStepAtIsFocusBullet steps nextIdx then
            throw s!"object tactic `apply {rawName}` expected focus bullet `·` before the next \
              subgoal for rule or declaration '{cand.name}'"
          let startIdx := if useBullets then nextIdx + 1 else nextIdx
          let (arg, nextIdx') ←
            compileInternalObjectGoal target sig levels steps startIdx { goal with target :=
            paramTy }
          nextIdx := nextIdx'
          args := args.push arg
          subst := subst.insert key arg
    for premiseTarget in cand.subgoalTargets do
      let premiseGoal := substObjectVars subst premiseTarget
      if useBullets?.isNone then
        useBullets? := some (internalTacticStepAtIsFocusBullet steps nextIdx)
      let useBullets := useBullets?.getD false
      if useBullets && !internalTacticStepAtIsFocusBullet steps nextIdx then
        throw s!"object tactic `apply {rawName}` expected focus bullet `·` before the next \
          subgoal for rule or declaration '{cand.name}'"
      let startIdx := if useBullets then nextIdx + 1 else nextIdx
      let (arg, nextIdx') ←
        compileInternalObjectGoal target sig levels steps startIdx { goal with target :=
        premiseGoal }
      nextIdx := nextIdx'
      args := args.push arg
    for sc in cand.sideConditions do
      let scInput := substObjectVars subst sc.input
      match classifySideConditionHook sc.solver with
      | .builtinTrivial => pure ()
      | .opaque =>
          throw <| internalOpaqueSideConditionMessage "apply" rawName cand.name sc.name
            sc.solver scInput
    pure (mkObjectApps (.ident cand.name) args, nextIdx)
end

/-- Compile a minimal object tactic script into an object term for the given initial goal. -/
def compileInternalObjectTacticsWithGoal (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (goal : InternalObjectGoal) (steps : Array InternalTacticStep)
    (stepStxs : Array Syntax := #[]) : CommandElabM ObjExpr := do
  if steps.isEmpty then
    throwError "empty object tactic script in `internal def {target.anchorName}`"
  let errorRef := stepStxs[0]?.getD (← getRef)
  match compileInternalObjectGoal target sig levels steps 0 goal with
  | .error err =>
      match decodeInternalStepError? err with
      | some (idx, msg) =>
          let errorRef := stepStxs[idx]?.getD errorRef
          withRef errorRef <| throwError msg
      | none => withRef errorRef <| throwError err
  | .ok (termExpr, nextIdx) =>
      if nextIdx != steps.size then
        let errorRef := stepStxs[nextIdx]?.getD errorRef
        withRef errorRef <|
          throwError "object tactic script for `internal def {target.anchorName}` left unused \
            tactic step(s) starting at index {nextIdx}"
      pure termExpr

/-- Compile a minimal object tactic script into an object term. -/
def compileInternalObjectTactics (target : InternalDefTarget) (sig : HLSignature)
    (levels : Array Name) (typeExpr : ObjExpr) (steps : Array InternalTacticStep)
    (stepStxs : Array Syntax := #[]) : CommandElabM ObjExpr :=
  compileInternalObjectTacticsWithGoal target sig levels { target := typeExpr } steps stepStxs

/-- Register a non-admitted top-level `internal def` through the current checked-artifact paths. -/
def elabInternalDefCheckedExpr (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (typeExpr valueExpr : ObjExpr) : CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  if !levels.isEmpty then
    throwError "internal LF declarations do not support declaration-local universe parameters"
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let valueExpr ←
    match elaborateInternalDirectTermPlaceholders target flatSig #[] typeExpr valueExpr with
    | .ok valueExpr => pure valueExpr
    | .error err => throwError err
  let lfDef : LFObjectDefDecl := { name := target.localName, typeExpr, value := valueExpr }
  try
    liftCoreM <| registerLFObjectDef target.theoryName lfDef
  catch lfDefEx =>
    let lfTheorem : LFJudgmentTheoremDecl := {
      name := target.localName
      judgmentExpr := typeExpr
      proof := valueExpr
    }
    try
      liftCoreM <| registerLFJudgmentTheorem target.theoryName lfTheorem
    catch lfThmEx =>
      throwError "failed to check internal LF declaration '{target.anchorName}' in type theory \
        '{target.theoryName}'\n\nLF object definition path:\n{exceptionMessageData lfDefEx}\n\nLF \
          judgment theorem path:\n{exceptionMessageData lfThmEx}"
  if let some doc := sourceDoc? then
    liftCoreM <| registerSourceDoc target.theoryName .internalDef target.localName doc
  addInternalDeclarationAnchor target typeExpr false sourceDoc? (← getRef) declNameStx

/-- Parse and register a non-admitted top-level `internal def`. -/
def elabInternalDefChecked (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (typeStx valueStx : TSyntax `ttExpr) : CommandElabM Unit := do
  elabInternalDefCheckedExpr doc? declNameStx declName levels (← elabObjExpr typeStx) (
    ← elabObjExpr valueStx)

/-- Register a binder-style checked `internal def` from already elaborated expressions.

If the result annotation is a judgment, the binders become local LF parameters/hypotheses
of a `judgment_theorem`. Otherwise the same surface sugar elaborates to an LF function
object definition. -/
def elabInternalDefCheckedWithBindersExpr (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (params : Array HLBinding) (typeExpr valueExpr : ObjExpr) : CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  if !levels.isEmpty then
    throwError "internal LF declarations do not support declaration-local universe parameters"
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let valueExpr ←
    match elaborateInternalDirectTermPlaceholders target flatSig params typeExpr valueExpr with
    | .ok valueExpr => pure valueExpr
    | .error err => throwError err
  let fullType := mkInternalDefFunctionType params typeExpr
  let fullValue := mkInternalDefLambda params valueExpr
  try
    let lfTheorem : LFJudgmentTheoremDecl := {
      name := target.localName, binders := params, judgmentExpr := typeExpr, proof := valueExpr }
    liftCoreM <| registerLFJudgmentTheorem target.theoryName lfTheorem
  catch lfThmEx =>
    try
      let lfDef : LFObjectDefDecl := {
        name := target.localName,
        typeExpr := fullType,
        value := fullValue }
      liftCoreM <| registerLFObjectDef target.theoryName lfDef
    catch lfDefEx =>
      throwError "failed to check binder-style internal LF declaration '{target.anchorName}' in \
        type theory '{target.theoryName}'\n\nLF judgment theorem \
          path:\n{exceptionMessageData lfThmEx}\n\nLF object definition \
            path:\n{exceptionMessageData lfDefEx}"
  if let some doc := sourceDoc? then
    liftCoreM <| registerSourceDoc target.theoryName .internalDef target.localName doc
  addInternalDeclarationAnchor target fullType false sourceDoc? (← getRef) declNameStx

/-- Elaborate a binder-style checked `internal def`. -/
def elabInternalDefCheckedWithBinders (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (binders : TSyntaxArray `ttBinder) (typeStx valueStx : TSyntax `ttExpr) :
    CommandElabM Unit := do
  let params ← binders.mapM elabHLBinding
  let typeExpr ← elabObjExpr typeStx
  let valueExpr ← elabObjExpr valueStx
  elabInternalDefCheckedWithBindersExpr doc? declNameStx declName levels params typeExpr valueExpr

/-- Register an admitted top-level `internal def` after checking its annotation as an object type.
-/
def elabInternalDefSorryWithBinders (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (binders : TSyntaxArray `ttBinder) (typeStx : TSyntax `ttExpr) : CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  let typeExpr ← elabObjExpr typeStx
  let params ← binders.mapM elabHLBinding
  if !levels.isEmpty then
    throwError "admitted internal declarations do not support declaration-local universe \
      parameters"
  match ← liftCoreM <| classifyInternalSorryAdmissionShape target.theoryName target.localName
      params typeExpr with
  | .lfOpaque =>
      liftCoreM <| registerAdmittedInternalLFOpaque target.theoryName target.anchorName
        target.localName params typeExpr
  | .judgmentTheorem =>
      liftCoreM <| registerAdmittedInternalLFJudgmentTheorem target.theoryName
        target.anchorName target.localName params typeExpr
  | .unsupported reason =>
      throwError "failed to classify admitted internal LF declaration '{target.anchorName}' in \
        type theory '{target.theoryName}': {reason}\n\nAccepted forms are object-shaped \
        admissions such as `internal def c : Obj := sorry` and theorem-shaped admissions such as \
        `internal theorem h : J a := sorry`."
  if let some doc := sourceDoc? then
    liftCoreM <| registerSourceDoc target.theoryName .internalDef target.localName doc
  addInternalDeclarationAnchor target typeExpr true sourceDoc? (← getRef) declNameStx
  logWarning m!"internal declaration '{target.anchorName}' was admitted by `sorry`; the \
    annotation was checked in theory '{target.theoryName}', but the body was not checked. Use \
      `#lint_type_theory_sorries {target.theoryName}` to list current admissions."

/-- Register an admitted top-level `internal def` after checking its annotation as an object type.
-/
def elabInternalDefSorry (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (typeStx : TSyntax `ttExpr) : CommandElabM Unit := do
  elabInternalDefSorryWithBinders doc? declNameStx declName levels #[] typeStx

/-- Register an explicit checked theorem-shaped internal declaration. -/
def elabInternalTheoremCheckedWithBinders (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (binders : TSyntaxArray `ttBinder) (typeStx valueStx : TSyntax `ttExpr) :
    CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  if !levels.isEmpty then
    throwError "internal LF theorem declarations do not support declaration-local universe \
      parameters"
  let params ← binders.mapM elabHLBinding
  let typeExpr ← elabObjExpr typeStx
  let valueExpr ← elabObjExpr valueStx
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
  addInternalDeclarationAnchor target (mkInternalDefFunctionType params typeExpr) false sourceDoc?
    (← getRef) declNameStx

/-- Register an explicit non-model-facing admitted internal theorem. -/
def elabInternalTheoremSorryWithBinders (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (binders : TSyntaxArray `ttBinder) (typeStx : TSyntax `ttExpr) : CommandElabM Unit := do
  let target ← resolveInternalDefTarget declName
  ensureInternalDeclarationNamesAvailable target
  let sourceDoc? ← optDocCommentString? doc?
  if !levels.isEmpty then
    throwError "internal LF theorem admissions do not support declaration-local universe \
      parameters"
  let params ← binders.mapM elabHLBinding
  let typeExpr ← elabObjExpr typeStx
  liftCoreM <| registerAdmittedInternalLFJudgmentTheorem target.theoryName target.anchorName
    target.localName params typeExpr
  if let some doc := sourceDoc? then
    liftCoreM <| registerSourceDoc target.theoryName .internalDef target.localName doc
  addInternalDeclarationAnchor target (mkInternalDefFunctionType params typeExpr) true sourceDoc?
    (← getRef) declNameStx
  logWarning m!"internal theorem '{target.anchorName}' was admitted by `sorry`; the statement was \
    checked in theory '{target.theoryName}', but the proof was not checked. Use \
      `#lint_type_theory_sorries {target.theoryName}` to list current admissions."

/-- Elaborate and register a top-level `internal def ... := by` object tactic script. -/
def elabInternalDefBy (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (typeStx : TSyntax `ttExpr) (tactics : TSyntaxArray `internalTactic) : CommandElabM Unit := do
  let steps ← tactics.mapM fun tac => withRef tac.raw <| elabInternalTacticStep tac
  let target ← resolveInternalDefTarget declName
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let typeExpr ← elabObjExpr typeStx
  let infos :=
    collectInternalObjectTacticInfo target flatSig levels typeExpr steps (tactics.map (·.raw))
  saveInternalObjectTacticInfo target flatSig infos
  if internalTacticStepsContainSorry steps then
    elabInternalDefSorry doc? declNameStx declName levels typeStx
  else
    let valueExpr ← compileInternalObjectTactics target flatSig levels typeExpr steps
      (tactics.map (·.raw))
    elabInternalDefCheckedExpr doc? declNameStx declName levels typeExpr valueExpr

/-- Elaborate and register a binder-style `internal def ... := by` object tactic script. -/
def elabInternalDefByWithBinders (doc? : Option (TSyntax ``Parser.Command.docComment))
    (declNameStx : Syntax) (declName : Name) (levels : Array Name)
    (binders : TSyntaxArray `ttBinder) (typeStx : TSyntax `ttExpr)
    (tactics : TSyntaxArray `internalTactic) : CommandElabM Unit := do
  let steps ← tactics.mapM fun tac => withRef tac.raw <| elabInternalTacticStep tac
  let target ← resolveInternalDefTarget declName
  let some sig ← liftCoreM <| getTheory? target.theoryName
    | throwError "unknown type theory '{target.theoryName}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let params ← binders.mapM elabHLBinding
  let typeExpr ← elabObjExpr typeStx
  let fullType := mkInternalDefFunctionType params typeExpr
  let infos :=
    collectInternalObjectTacticInfo target flatSig levels fullType steps (tactics.map (·.raw))
  saveInternalObjectTacticInfo target flatSig infos
  if internalTacticStepsContainSorry steps then
    elabInternalDefSorryWithBinders doc? declNameStx declName levels binders typeStx
  else
    let goal : InternalObjectGoal := { ctx := params, target := typeExpr }
    let valueExpr ← compileInternalObjectTacticsWithGoal target flatSig levels goal steps
      (tactics.map (·.raw))
    elabInternalDefCheckedWithBindersExpr doc? declNameStx declName levels params typeExpr valueExpr

/-- Recognize `sorry` when it was parsed through the object-expression identifier syntax. -/
def isSorryObjExprSyntax (stx : Syntax) : Bool :=
  match stx with
  | .ident _ _ val _ => val.eraseMacroScopes == `sorry
  | _ => false

/-- Parsed admitted declaration inside an `internal_defs where` batch. -/
structure InternalDefsSorryBatchItem where
  /-- Original declaration syntax, used for range metadata. -/
  declStx : Syntax
  /-- Declaration identifier syntax. -/
  declNameStx : Syntax
  /-- Resolved target theory/local name. -/
  target : InternalDefTarget
  /-- Source-level documentation, if present. -/
  sourceDoc? : Option String := none
  /-- Elaborated source binders. -/
  params : Array HLBinding := #[]
  /-- Elaborated source annotation. -/
  typeExpr : ObjExpr
  deriving Inhabited

/-- Parse one admitted declaration in an `internal_defs where` batch, if it is admitted. -/
def elabInternalDefsSorryBatchItem? (decl : TSyntax `internalDefsDecl) :
    CommandElabM (Option InternalDefsSorryBatchItem) := do
  let mkItem (doc? : Option (TSyntax ``Parser.Command.docComment)) (declNameStx : Syntax)
      (declName : Name) (binders : TSyntaxArray `ttBinder) (typeStx : TSyntax `ttExpr) := do
    let target ← resolveInternalDefTarget declName
    ensureInternalDeclarationNamesAvailable target
    let sourceDoc? ← optDocCommentString? doc?
    let params ← binders.mapM elabHLBinding
    let typeExpr ← elabObjExpr typeStx
    pure (some {
      declStx := decl.raw
      declNameStx := declNameStx
      target := target
      sourceDoc? := sourceDoc?
      params := params
      typeExpr := typeExpr })
  match decl with
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident : $typeStx:ttExpr := sorry) =>
      mkItem doc? declName declName.getId #[] typeStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      mkItem doc? declName declName.getId binders typeStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident : $typeStx:ttExpr :=
      $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        mkItem doc? declName declName.getId #[] typeStx
      else
        pure none
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        mkItem doc? declName declName.getId binders typeStx
      else
        pure none
  | _ => pure none

/-- Try to register an all-opaque-admission `internal_defs where` block as one checked delta. -/
def tryElabInternalDefsSorryOpaqueBatch (decls : Array (TSyntax `internalDefsDecl)) :
    CommandElabM Bool := do
  if decls.isEmpty then
    return false
  let mut items : Array InternalDefsSorryBatchItem := #[]
  for decl in decls do
    match ← elabInternalDefsSorryBatchItem? decl with
    | some item => items := items.push item
    | none => return false
  let some first := items[0]?
    | return false
  let theoryName := first.target.theoryName
  let mut seenLocals : NameSet := {}
  let mut seenAnchors : NameSet := {}
  let mut requests : Array AdmittedInternalLFOpaqueRequest := #[]
  for item in items do
    if item.target.theoryName != theoryName then
      return false
    let localName := item.target.localName.eraseMacroScopes
    if seenLocals.contains localName then
      throwError "duplicate internal_defs declaration '{item.target.localName}' in type theory \
        '{theoryName}'"
    seenLocals := seenLocals.insert localName
    let anchorName := item.target.anchorName.eraseMacroScopes
    if seenAnchors.contains anchorName then
      throwError "duplicate Lean-visible internal_defs anchor '{item.target.anchorName}'"
    seenAnchors := seenAnchors.insert anchorName
    requests := requests.push {
      localName := item.target.localName
      anchorName := item.target.anchorName
      params := item.params
      typeExpr := item.typeExpr }
  let shapes ← liftCoreM <| classifyInternalSorryAdmissionShapes theoryName requests
  unless shapes.all (· == .lfOpaque) do
    return false
  liftCoreM <| registerAdmittedInternalLFOpaqueBatch theoryName requests
  for item in items do
    if let some doc := item.sourceDoc? then
      liftCoreM <| registerSourceDoc item.target.theoryName .internalDef item.target.localName doc
    addInternalDeclarationAnchor item.target item.typeExpr true item.sourceDoc? item.declStx
      item.declNameStx
    logWarning m!"internal declaration '{item.target.anchorName}' was admitted by `sorry`; the \
      annotation was checked in theory '{item.target.theoryName}', but the body was not checked. \
      Use `#lint_type_theory_sorries {item.target.theoryName}` to list current admissions."
  return true

/-- Elaborate one declaration in an `internal_defs where` batch. -/
def elabInternalDefsDecl : TSyntax `internalDefsDecl → CommandElabM Unit
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
      $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        elabInternalDefSorry doc? declName declName.getId #[] typeStx
      else
        elabInternalDefChecked doc? declName declName.getId #[] typeStx valueStx
  | `(internalDefsDecl| $[$doc?:docComment]? def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        elabInternalDefSorryWithBinders doc? declName declName.getId #[] binders typeStx
      else
        elabInternalDefCheckedWithBinders doc? declName declName.getId #[] binders typeStx valueStx
  | stx => throwError "unsupported internal_defs declaration:{indentD stx}"

/-- Elaborate an `internal_defs where` block, batching consecutive LF-opaque admissions. -/
def elabInternalDefsDeclsWithSorryOpaqueBatches (decls : Array (TSyntax `internalDefsDecl)) :
    CommandElabM Unit := do
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
      addInternalDeclarationAnchor item.target item.typeExpr true item.sourceDoc? item.declStx
        item.declNameStx
      logWarning m!"internal declaration '{item.target.anchorName}' was admitted by `sorry`; the \
        annotation was checked in theory '{item.target.theoryName}', but the body was not \
        checked. Use `#lint_type_theory_sorries {item.target.theoryName}` to list current \
        admissions."
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
            elabInternalDefsDecl decl
    | none =>
        flush batch
        batch := #[]
        elabInternalDefsDecl decl
  flush batch

elab_rules : command
  | `(internal_defs where $decls:internalDefsDecl*) => do
      unless ← tryElabInternalDefsSorryOpaqueBatch decls do
        elabInternalDefsDeclsWithSorryOpaqueBatches decls
  | `($[$doc?:docComment]? internal theorem $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] #[] typeStx
  | `($[$doc?:docComment]? internal theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := sorry) =>
      elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] binders typeStx
  | `($[$doc?:docComment]? internal theorem $declName:ident : $typeStx:ttExpr :=
      $valueStx:ttExpr) =>
      elabInternalTheoremCheckedWithBinders doc? declName declName.getId #[] #[] typeStx valueStx
  | `($[$doc?:docComment]? internal theorem $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        elabInternalTheoremSorryWithBinders doc? declName declName.getId #[] binders typeStx
      else
        elabInternalTheoremCheckedWithBinders doc? declName declName.getId #[] binders typeStx
          valueStx
  | `($[$doc?:docComment]? internal def $declName:ident : $typeStx:ttExpr := sorry) =>
      elabInternalDefSorry doc? declName declName.getId #[] typeStx
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*} : $typeStx:ttExpr :=
    sorry) =>
      elabInternalDefSorry doc? declName declName.getId (levels.getElems.map (·.getId)) typeStx
  | `($[$doc?:docComment]? internal def $declName:ident : $typeStx:ttExpr :=
    by $tactics:internalTactic*) =>
      elabInternalDefBy doc? declName declName.getId #[] typeStx tactics
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*} : $typeStx:ttExpr :=
    by $tactics:internalTactic*) =>
      elabInternalDefBy doc? declName declName.getId (levels.getElems.map (·.getId)) typeStx tactics
  | `($[$doc?:docComment]? internal def $declName:ident $binders:ttBinder* :
      $typeStx:ttExpr := by $tactics:internalTactic*) =>
      elabInternalDefByWithBinders doc? declName declName.getId #[] binders typeStx tactics
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*}
      $binders:ttBinder* : $typeStx:ttExpr := by $tactics:internalTactic*) =>
      elabInternalDefByWithBinders doc? declName declName.getId
        (levels.getElems.map (·.getId)) binders typeStx tactics
  | `($[$doc?:docComment]? internal def $declName:ident : $typeStx:ttExpr := $valueStx:ttExpr) =>
      elabInternalDefChecked doc? declName declName.getId #[] typeStx valueStx
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*} : $typeStx:ttExpr :=
    $valueStx:ttExpr) =>
      elabInternalDefChecked doc? declName declName.getId (levels.getElems.map (·.getId)) typeStx
        valueStx
  | `($[$doc?:docComment]? internal def $declName:ident $binders:ttBinder* : $typeStx:ttExpr :=
    $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        elabInternalDefSorryWithBinders doc? declName declName.getId #[] binders typeStx
      else
        elabInternalDefCheckedWithBinders doc? declName declName.getId #[] binders typeStx valueStx
  | `($[$doc?:docComment]? internal def $declName:ident {$levels:ident,*} $binders:ttBinder* :
    $typeStx:ttExpr := $valueStx:ttExpr) =>
      if isSorryObjExprSyntax valueStx.raw then
        elabInternalDefSorryWithBinders doc? declName declName.getId (levels.getElems.map
          (·.getId)) binders typeStx
      else
        elabInternalDefCheckedWithBinders doc? declName declName.getId (levels.getElems.map
          (·.getId)) binders typeStx valueStx


end InternalLean
