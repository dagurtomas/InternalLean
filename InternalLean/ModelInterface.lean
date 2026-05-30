/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Diagnostics

/-!
# LF model-interface generation

This file contains the LF model-obligation IR, Lean syntax rendering for generated
model interfaces, and checked direct-LF model method rendering.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

namespace LeanTypeModelGeneration

/-- Pretty-print generated command syntax for diagnostic `#print_...` commands.

Generated declarations should be built as syntax; source strings are only a diagnostic
presentation. -/
def ppCommandSyntaxString (cmd : Syntax) : CommandElabM String := do
  let fmt ← liftCoreM <| Lean.PrettyPrinter.ppCommand ⟨cmd⟩
  pure fmt.pretty

/-- Pretty-print generated term syntax for LF-model diagnostics. -/
def ppTermSyntaxString (stx : TSyntax `term) : CommandElabM String := do
  let fmt ← liftCoreM <| Lean.PrettyPrinter.ppTerm stx
  pure fmt.pretty

/-- Render a name as surface syntax for generated model code. -/
def nameString (n : Name) : String :=
  ObjExpr.userNameString n

/-- Components of a Lean name, used when deriving stable generated field names. -/
partial def nameComponents : Name → List String
  | .anonymous => []
  | .str p s => nameComponents p ++ [s]
  | .num p n => nameComponents p ++ [toString n]

/-- Flatten a Lean name into a single identifier-friendly component. -/
def flatNameString (n : Name) : String :=
  match nameComponents n.eraseMacroScopes with
  | [] => "anonymous"
  | cs => String.intercalate "_" cs

/-- Build an application term, keeping explicit-head syntax such as `@M.f` attached to the
whole argument spine rather than only to the first argument. -/
def mkTermAppSyntax (fn : TSyntax `term) (args : Array (TSyntax `term)) :
  CommandElabM (TSyntax `term) := do
  if args.isEmpty then
    pure fn
  else
    `(term| $fn $args:term*)

/-- Render an object expression as a Lean expression in the scope of a generated model structure.

This diagnostic printer covers the dependent-function fragment used by the generated model
interface. Generated declarations use syntax construction rather than this presentation string. -/
partial def exprString : ObjExpr → String
  | .ident n => nameString n
  | .sort => "Type"
  | .univ .zero => "Type"
  | .univ u => s!"Type {u}"
  | .app f a => s!"{exprString f} {atomString a}"
  | .arrow none A B => s!"{atomString A} → {exprString B}"
  | .arrow (some x) A B => s!"({nameString x} : {exprString A}) → {exprString B}"
  | .funArrow none A B => s!"{atomString A} → {exprString B}"
  | .funArrow (some x) A B => s!"({nameString x} : {exprString A}) → {exprString B}"
  | .sigma none A B => s!"{atomString A} × {exprString B}"
  | .sigma (some x) A B => s!"Sigma (fun {nameString x} : {exprString A} => {exprString B})"
  | .pair a b => s!"⟨{exprString a}, {exprString b}⟩"
  | .fst e => s!"{atomString e}.1"
  | .snd e => s!"{atomString e}.2"
  | .lam xs body =>
      let names := xs.toList.map nameString
      s!"fun {String.intercalate " " names} => {exprString body}"
  | .jeq lhs rhs => s!"{exprString lhs} = {exprString rhs}"
where
  atomString : ObjExpr → String
    | .ident n => nameString n
    | .sort => "Type"
    | .univ .zero => "Type"
    | .univ u => s!"Type {u}"
    | e => s!"({exprString e})"

/-- Return whether an object expression contains a free occurrence of a name.

This lightweight occurrence check is used only to avoid generated unused-binder
warnings in generated model structures. It is name-based on high-level syntax, not a full scoped
free-variable calculation. -/
partial def containsIdent (needle : Name) : ObjExpr → Bool
  | .ident n => n == needle
  | .sort | .univ .. => false
  | .app f a => containsIdent needle f || containsIdent needle a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      containsIdent needle A ||
        if x.map Name.eraseMacroScopes == some needle.eraseMacroScopes then false else
          containsIdent needle B
  | .pair a b => containsIdent needle a || containsIdent needle b
  | .fst e | .snd e => containsIdent needle e
  | .lam xs body =>
      if xs.map Name.eraseMacroScopes |>.contains needle.eraseMacroScopes then false else
        containsIdent needle body
  | .jeq lhs rhs => containsIdent needle lhs || containsIdent needle rhs

/-- Return whether a binder name is used by later binder types or the final result. -/
def binderUsedAfter (binders : Array HLBinding) (result : ObjExpr) (i : Nat) : Bool :=
  match binders[i]? with
  | none => false
  | some b =>
      containsIdent b.name result ||
        ((binders.toList.drop (i + 1)).any fun later => containsIdent b.name later.typeExpr)

/-- Name of a generated declaration inside a theory namespace. -/
def generatedInTheoryName (theoryName localName : Name) : Name :=
  theoryName ++ localName

/-- Render an object universe expression as Lean universe syntax. -/
partial def levelExprLeanSyntaxString : LevelExpr → String
  | .zero => "0"
  | .lit n => s!"{n}"
  | .param n => s!"{n.eraseMacroScopes}"
  | .succ u => s!"({levelExprLeanSyntaxString u} + 1)"
  | .max u v => s!"max {atomString u} {atomString v}"
where
  atomString : LevelExpr → String
    | .zero => "0"
    | .lit n => s!"{n}"
    | .param n => s!"{n.eraseMacroScopes}"
    | u => s!"({levelExprLeanSyntaxString u})"

/-- Interpret an object universe annotation as a Lean type universe in generated models.
Direct-LF model interfaces are universe-polymorphic through their fields; this renderer preserves
explicit LF universe parameters as Lean universe levels. -/
def typeSyntaxOfLevel (u : LevelExpr) : CommandElabM (TSyntax `term) := do
  let u := LevelExpr.normalize u
  let source := if LevelExpr.equal u .zero then "Type" else
    s!"Type {levelExprLeanSyntaxString u}"
  match Lean.Parser.runParserCategory (← getEnv) `term source with
  | .ok stx => pure ⟨stx⟩
  | .error err => throwError "failed to render generated universe syntax '{source}': {err}"

abbrev LFLocalSyntaxCtx := List (Name × Ident)

/-- Source LF names bound in the current generated-code rendering context. -/
def lfLocalSyntaxSourceNames (locals : LFLocalSyntaxCtx) : NameSet :=
  locals.foldl (init := {}) fun names entry => names.insert entry.fst.eraseMacroScopes

/-- Names reserved by Lean syntax or by generated model renderers for local binders. -/
def lfReservedLeanLocalNames : NameSet :=
  [`Type, `fun, `let, `match, `if, `then, `else, `by, `where, `do, `forall].foldl
    (init := {}) fun acc n => acc.insert n.eraseMacroScopes

/-- Whether a source name can be emitted directly as one Lean identifier token. -/
def isAtomicLeanLocalName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str .anonymous s => !s.isEmpty
  | _ => false

/-- Sanitize a source LF local name into a simple Lean identifier base. -/
def lfLeanLocalBaseName (n : Name) : Name :=
  if isAtomicLeanLocalName n then n.eraseMacroScopes else Name.mkSimple (flatNameString n)

/-- Lean local identifiers already chosen for a rendering context. -/
def lfLocalSyntaxUsedNames (locals : LFLocalSyntaxCtx) : NameSet :=
  locals.foldl (init := {}) fun used (_, id) => used.insert id.getId.eraseMacroScopes

/-- Pick a deterministic Lean local name avoiding reserved and already-used names. -/
def freshLFLeanLocalName (source : Name) (avoid : NameSet) : Name :=
  let base := lfLeanLocalBaseName source
  let avoid := avoid ++ lfReservedLeanLocalNames
  let rec go : Nat → Nat → Name
    | 0, n => Name.mkSimple s!"{flatNameString base}_hyg{n}"
    | fuel + 1, n =>
        let candidate := Name.mkSimple s!"{flatNameString base}_hyg{n}"
        if avoid.contains candidate then go fuel (n + 1) else candidate
  if avoid.contains base then go (avoid.size + 32) 0 else base

/-- Fresh local identifier for generated LF code without a model-instance variable. -/
def freshLFLocalIdent (source : Name) (locals : LFLocalSyntaxCtx)
    (reserved : NameSet := {}) : Ident :=
  mkIdent (freshLFLeanLocalName source (reserved ++ lfLocalSyntaxUsedNames locals))

/-- Fresh local identifier for generated LF code projected from a model instance. -/
def freshLFModelLocalIdent (source : Name) (modelIdent : Ident) (locals : LFLocalSyntaxCtx)
    (reserved : NameSet := {}) : Ident :=
  freshLFLocalIdent source locals (reserved.insert modelIdent.getId.eraseMacroScopes)

/-- Source visibility of a callable LF head's parameter telescope, used when rendering Lean
applications. -/
abbrev LFParamVisibilityMap := NameMap (Array BinderVisibility)

/-- Split a checked LF expression into head and argument spine. -/
partial def splitCheckedLFExprApp : CheckedLFExpr → CheckedLFExpr × Array CheckedLFExpr
  | .app f a =>
      let (h, args) := splitCheckedLFExprApp f
      (h, args.push a)
  | e => (e, #[])

/-- Rebuild a checked LF application from a head and argument spine. -/
def checkedLFExprAppOfArgs (head : CheckedLFExpr) (args : Array CheckedLFExpr) :
    CheckedLFExpr :=
  args.foldl (init := head) fun f a => .app f a

/-- Apply a checked LF lambda to arguments, using LF-level substitution instead of relying on
Lean to elaborate a generated beta-redex under a dependent expected type. -/
def checkedLFExprBetaApply (fn : CheckedLFExpr) (args : Array CheckedLFExpr) : CheckedLFExpr :=
  match fn with
  | .lam binders body =>
      let rec consume (i : Nat) (body : CheckedLFExpr) : CheckedLFExpr :=
        if hArg : i < args.size then
          if hBinder : i < binders.size then
            consume (i + 1) (substSingleCheckedLFParam binders[i] args[i] body)
          else
            checkedLFExprAppOfArgs body (args.extract i args.size)
        else if hBinder : i < binders.size then
          .lam (binders.extract i binders.size) body
        else
          body
      consume 0 body
  | _ => checkedLFExprAppOfArgs fn args

/-- Reduce a checked LF lambda when it appears as an application head. -/
def reduceCheckedLFLambdaHeadApp? (e : CheckedLFExpr) : Option CheckedLFExpr :=
  let (head, args) := splitCheckedLFExprApp e
  if args.isEmpty then
    none
  else
    match head with
    | .lam .. =>
        let reduced := checkedLFExprBetaApply head args
        if reduced == e then none else some reduced
    | _ => none

/-- Unfold a checked LF definition when it appears as the head of an application and perform the
corresponding LF beta-reduction. This mirrors the old generated Lean beta-redex but avoids Lean
elaboration failures for dependent Sigma result types. -/
def reduceCheckedLFDefinitionHeadApp? (defs : CheckedLFDefinitionValueMap) (locals : NameSet)
    (e : CheckedLFExpr) : Option CheckedLFExpr :=
  let (head, args) := splitCheckedLFExprApp e
  if args.isEmpty then
    none
  else
    match head with
    | .ident h =>
        let key := h.name.eraseMacroScopes
        if h.kind == .lfDefinition && !locals.contains key then
          match defs.find? key with
          | some value =>
              let reduced := checkedLFExprBetaApply value args
              if reduced == e then none else some reduced
          | none => none
        else
          none
    | _ => none

/-- Unfold a nullary checked LF definition at a value occurrence. -/
def reduceCheckedLFDefinitionValue? (defs : CheckedLFDefinitionValueMap) (locals : NameSet)
    (e : CheckedLFExpr) : Option CheckedLFExpr :=
  match e with
  | .ident h =>
      let key := h.name.eraseMacroScopes
      if h.kind == .lfDefinition && !locals.contains key then
        match defs.find? key with
        | some value => if value == e then none else some value
        | none => none
      else
        none
  | _ => none

/-- Reduce one LF-level redex that matters before rendering model syntax. -/
def reduceCheckedLFHeadRedex? (defs : CheckedLFDefinitionValueMap) (locals : NameSet)
    (e : CheckedLFExpr) : Option CheckedLFExpr :=
  match reduceCheckedLFLambdaHeadApp? e with
  | some reduced => some reduced
  | none =>
      match reduceCheckedLFDefinitionHeadApp? defs locals e with
      | some reduced => some reduced
      | none => reduceCheckedLFDefinitionValue? defs locals e

/-- Normalize the LF redexes that Lean should not have to infer while rendering model code.

This reducer is projection-aware: it unfolds checked LF definitions or lambda applications only
when they are at the current head, then contracts `fst`/`snd` from checked pairs and repeats. It is
used at rendering sites for checked LF expressions, so local identifiers shadowing global checked
definitions remain opaque. -/
partial def normalizeCheckedLFExprForModel (defs : CheckedLFDefinitionValueMap)
    (locals : NameSet) (e : CheckedLFExpr) : CheckedLFExpr :=
  match reduceCheckedLFHeadRedex? defs locals e with
  | some reduced => normalizeCheckedLFExprForModel defs locals reduced
  | none =>
      match e with
      | .fst value =>
          let value := normalizeCheckedLFExprForModel defs locals value
          match value with
          | .pair first _ => normalizeCheckedLFExprForModel defs locals first
          | _ => .fst value
      | .snd value =>
          let value := normalizeCheckedLFExprForModel defs locals value
          match value with
          | .pair _ second => normalizeCheckedLFExprForModel defs locals second
          | _ => .snd value
      | _ => e

/-- Model field types keep most LF-definition applications as generated Lean beta-redexes for
compactness, but pair-valued definitions must be reduced before Lean sees a dependent Sigma
expected type. -/
def reduceCheckedLFDefinitionHeadPairApp? (defs : CheckedLFDefinitionValueMap)
    (locals : NameSet) (e : CheckedLFExpr) : Option CheckedLFExpr := do
  let reduced ← reduceCheckedLFHeadRedex? defs locals e
  match reduced with
  | .pair .. => some reduced
  | _ => none

/-- Split a source LF expression into head and argument spine. -/
partial def splitObjExprAppForModel : ObjExpr → ObjExpr × Array ObjExpr
  | .app f a =>
      let (h, args) := splitObjExprAppForModel f
      (h, args.push a)
  | e => (e, #[])

/-- Head name of a checked LF expression, when it is a global/local identifier. -/
def checkedLFExprHeadName? : CheckedLFExpr → Option Name
  | .ident h => some h.name
  | _ => none

/-- Head name of a source LF expression, when it is an identifier. -/
def objExprHeadName? : ObjExpr → Option Name
  | .ident n => some n.eraseMacroScopes
  | _ => none

/-- Whether applications of a head should be rendered with explicit implicit arguments. -/
def lfHeadHasImplicitParams (paramVis : LFParamVisibilityMap) (n : Name) : Bool :=
  match paramVis.find? n.eraseMacroScopes with
  | some vis => vis.any (· == .implicit)
  | none => false

/-- Make a Lean term head explicit, so source-explicit LF argument spines can still apply it
when the generated Lean signature renders some source binders as implicit. -/
def explicitLeanHeadSyntax (head : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(term| @$head:term)

/-- Look up a local LF syntax identifier by checked name. -/
def findLFLocalIdent? (locals : LFLocalSyntaxCtx) (n : Name) : Option Ident :=
  (locals.find? (fun p => p.fst == n)).map (·.snd)

/-- Names of untyped LF opaque placeholders. These are raw handles, so the first LF-model
backend omits fields/rules that would require assigning them Lean types. -/
def untypedLFOpaqueNames (checked : CheckedSignature) : NameSet := Id.run do
  let mut out := {}
  for c in checked.lfOpaqueConsts do
    if c.typeExpr?.isNone then
      out := out.insert c.name
  return out

/-- Prototype side-condition predicate inferred for an untyped opaque placeholder used as a
rule side-condition input. -/
structure LFSideConditionPredicate where
  /-- Placeholder/predicate name. -/
  name : Name
  /-- Inferred parameter telescope from a side-condition occurrence. -/
  params : Array CheckedLFBinding := #[]
  deriving Inhabited, Repr, BEq

/-- Split a checked LF application into its head and spine arguments. -/
partial def checkedLFExprHeadArgs? (e : CheckedLFExpr) :
  Option (CheckedLFHead × Array CheckedLFExpr) :=
  let rec go (e : CheckedLFExpr) (args : List CheckedLFExpr) :
    Option (CheckedLFHead × Array CheckedLFExpr) :=
    match e with
    | .ident h => some (h, args.toArray)
    | .app f a => go f (a :: args)
    | _ => none
  go e []

/-- Local variable name represented by a checked LF expression, when it is a local identifier. -/
def checkedLFLocalName? : CheckedLFExpr → Option Name
  | .ident h => if h.kind == .local then some h.name else none
  | _ => none

/-- Find a checked LF binding by name. -/
def findLFBinding? (bs : Array CheckedLFBinding) (n : Name) : Option CheckedLFBinding :=
  bs.find? (fun b => b.name == n)

/-- Infer a side-condition predicate field from a side-condition occurrence headed by an
untyped opaque placeholder. This first pass supports the common LF-metadata shape where
all predicate arguments are rule parameters. -/
def lfSideConditionPredicateOf? (untyped : NameSet) (r : CheckedLFRule)
    (sc : CheckedLFRuleSideCondition) : Option LFSideConditionPredicate := do
  let (head, args) ← checkedLFExprHeadArgs? sc.checkedInput
  guard (untyped.contains head.name)
  let mut params := #[]
  let mut seen : NameSet := {}
  for arg in args do
    let n ← checkedLFLocalName? arg
    guard (!seen.contains n)
    seen := seen.insert n
    let b ← findLFBinding? r.params n
    params := params.push b
  some { name := head.name, params := params }

/-- Side-condition predicates inferred from checked rule side-condition inputs. -/
def lfSideConditionPredicates (checked : CheckedSignature) : Array LFSideConditionPredicate :=
  Id.run do
  let untyped := untypedLFOpaqueNames checked
  let mut out := #[]
  let mut seen : NameSet := {}
  for r in checked.lfRules do
    for sc in r.sideConditions do
      if let some p := lfSideConditionPredicateOf? untyped r sc then
        if !seen.contains p.name then
          seen := seen.insert p.name
          out := out.push p
  return out

/-- Names of untyped opaque placeholders that are generated as side-condition predicate
fields rather than omitted raw handles. -/
def lfSideConditionPredicateNames (checked : CheckedSignature) : NameSet :=
  (lfSideConditionPredicates checked).foldl (init := {}) fun acc p => acc.insert p.name

/-- Untyped opaque names that still block LF-model rendering after side-condition predicate
inference. -/
def blockingUntypedLFOpaqueNames (checked : CheckedSignature) : NameSet := Id.run do
  let sidePreds := lfSideConditionPredicateNames checked
  let mut out := {}
  for c in checked.lfOpaqueConsts do
    if c.typeExpr?.isNone && !sidePreds.contains c.name then
      out := out.insert c.name
  return out

/-- Whether a checked LF expression mentions an untyped opaque placeholder. -/
partial def lfExprMentionsAny (names : NameSet) : CheckedLFExpr → Bool
  | .ident h => names.contains h.name
  | .sort => false
  | .univ _ => false
  | .app f a => lfExprMentionsAny names f || lfExprMentionsAny names a
  | .arrow _ A B | .sigma _ A B => lfExprMentionsAny names A || lfExprMentionsAny names B
  | .pair a b => lfExprMentionsAny names a || lfExprMentionsAny names b
  | .fst e | .snd e => lfExprMentionsAny names e
  | .lam _ body => lfExprMentionsAny names body
  | .jeq lhs rhs => lfExprMentionsAny names lhs || lfExprMentionsAny names rhs

/-- Global LF heads mentioned by a checked expression, excluding local binders. -/
partial def lfExprGlobalHeadNames : CheckedLFExpr → NameSet
  | .ident h =>
      if h.kind == .local then {} else ({h.name.eraseMacroScopes} : NameSet)
  | .sort => {}
  | .univ _ => {}
  | .app f a => insertNameSet (lfExprGlobalHeadNames f) (lfExprGlobalHeadNames a)
  | .arrow _ A B | .sigma _ A B => insertNameSet (lfExprGlobalHeadNames A) (lfExprGlobalHeadNames B)
  | .pair a b => insertNameSet (lfExprGlobalHeadNames a) (lfExprGlobalHeadNames b)
  | .fst e | .snd e => lfExprGlobalHeadNames e
  | .lam _ body => lfExprGlobalHeadNames body
  | .jeq lhs rhs => insertNameSet (lfExprGlobalHeadNames lhs) (lfExprGlobalHeadNames rhs)

/-- Global LF heads mentioned by a source expression. Used only for model-field dependency ordering
diagnostics. -/
partial def objExprGlobalHeadNames : ObjExpr → NameSet
  | .ident n => ({n.eraseMacroScopes} : NameSet)
  | .sort => {}
  | .univ _ => {}
  | .app f a => insertNameSet (objExprGlobalHeadNames f) (objExprGlobalHeadNames a)
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      insertNameSet (objExprGlobalHeadNames A) (objExprGlobalHeadNames B)
  | .pair a b => insertNameSet (objExprGlobalHeadNames a) (objExprGlobalHeadNames b)
  | .fst e | .snd e => objExprGlobalHeadNames e
  | .lam _ body => objExprGlobalHeadNames body
  | .jeq lhs rhs => insertNameSet (objExprGlobalHeadNames lhs) (objExprGlobalHeadNames rhs)

/-- Whether a checked LF binding type mentions one of the given heads. -/
def lfBindingMentionsAny (names : NameSet) (b : CheckedLFBinding) : Bool :=
  lfExprMentionsAny names b.checkedTypeExpr

/-- Checked LF object definitions available for model-side rendering, keyed by definition name. -/
def lfDefinitionValueMap (checked : CheckedSignature) : NameMap CheckedLFExpr :=
  checked.lfObjectDefs.foldl (init := {}) fun acc d => acc.insert d.name d.checkedValue

/-- Lookup an LF definition value, tolerating harmless macro-scope differences in the key. -/
def lfDefinitionValue? (defValues : NameMap CheckedLFExpr) (n : Name) : Option CheckedLFExpr :=
  match defValues.find? n with
  | some value => some value
  | none => defValues.find? n.eraseMacroScopes

/-- Whether a checked LF expression can currently be rendered in an LF-model field type.
The first LF-model backend has fields for locals, syntax sorts, judgments, typed opaque
constants, inferred side-condition predicates, and rules. Staged LF object definitions are
renderable when their checked values can be rendered. -/
partial def lfExprRenderableInModel (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) : CheckedLFExpr → Bool
  | .ident h =>
      match h.kind with
      | .local | .syntaxSort | .judgment | .opaque | .lfRule =>
          !blockingUntyped.contains h.name || sidePredicateNames.contains h.name
      | .lfDefinition =>
          match lfDefinitionValue? defValues h.name with
          | some value => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames value
          | none => false
      | .lfTheorem | .primitive | .definition | .theorem => false
  | .sort => true
  | .univ _ => true
  | .app f a => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames f &&
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames a
  | .arrow _ A B | .sigma _ A B =>
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames A &&
        lfExprRenderableInModel defValues blockingUntyped sidePredicateNames B
  | .pair a b => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames a &&
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames b
  | .fst e | .snd e => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames e
  | .lam _ body => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames body
  | .jeq lhs rhs => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames lhs &&
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames rhs

/-- Syntax for a checked LF expression in an LF-model structure field. -/
partial def lfExprSyntax (locals : LFLocalSyntaxCtx) : CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h => pure <| (findLFLocalIdent? locals h.name).getD (mkIdent h.name)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | .app f a => do
      let f ← lfExprSyntax locals f
      let a ← lfExprSyntax locals a
      `($f $a)
  | .arrow none A B => do
      let A ← lfExprSyntax locals A
      let B ← lfExprSyntax locals B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ← lfExprSyntax locals A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntax ((x, xId) :: locals) B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfExprSyntax locals A
      let B ← lfExprSyntax locals B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfExprSyntax locals A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntax ((x, xId) :: locals) B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfExprSyntax locals a
      let b ← lfExprSyntax locals b
      `(⟨$a, $b⟩)
  | .fst e => do
      let e ← lfExprSyntax locals e
      `(($e).1)
  | .snd e => do
      let e ← lfExprSyntax locals e
      `(($e).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let xId := freshLFLocalIdent x locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntax locals body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfExprSyntax locals lhs
      let rhs ← lfExprSyntax locals rhs
      `($lhs = $rhs)

/-- Syntax for a checked LF expression in an LF-model structure field, expanding staged LF
object definitions to their checked values. -/
partial def lfExprSyntaxInModel (defValues : NameMap CheckedLFExpr)
    (locals : LFLocalSyntaxCtx) : CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h =>
      match h.kind, lfDefinitionValue? defValues h.name with
      | .lfDefinition, some value => lfExprSyntaxInModel defValues locals value
      | _, _ => pure <| (findLFLocalIdent? locals h.name).getD (mkIdent h.name)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app f a) => do
      if let some reduced := reduceCheckedLFHeadRedex? defValues
          (lfLocalSyntaxSourceNames locals) e then
        lfExprSyntaxInModel defValues locals reduced
      else
        let f ← lfExprSyntaxInModel defValues locals f
        let a ← lfExprSyntaxInModel defValues locals a
        `($f $a)
  | .arrow none A B => do
      let A ← lfExprSyntaxInModel defValues locals A
      let B ← lfExprSyntaxInModel defValues locals B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ← lfExprSyntaxInModel defValues locals A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntaxInModel defValues ((x, xId) :: locals) B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfExprSyntaxInModel defValues locals A
      let B ← lfExprSyntaxInModel defValues locals B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfExprSyntaxInModel defValues locals A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntaxInModel defValues ((x, xId) :: locals) B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfExprSyntaxInModel defValues locals a
      let b ← lfExprSyntaxInModel defValues locals b
      `(⟨$a, $b⟩)
  | e@(.fst value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModel defValues locals reduced
      else
        let value ← lfExprSyntaxInModel defValues locals value
        `(($value).1)
  | e@(.snd value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModel defValues locals reduced
      else
        let value ← lfExprSyntaxInModel defValues locals value
        `(($value).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let xId := freshLFLocalIdent x locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntaxInModel defValues locals body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfExprSyntaxInModel defValues locals lhs
      let rhs ← lfExprSyntaxInModel defValues locals rhs
      `($lhs = $rhs)

/-- Syntax for a checked LF expression projected from a concrete LF model instance. -/
partial def lfExprSyntaxInModelInstance (defValues : NameMap CheckedLFExpr)
    (modelIdent : Ident) (locals : LFLocalSyntaxCtx) : CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h =>
      match findLFLocalIdent? locals h.name with
      | some localId => pure localId
      | none =>
          match h.kind, lfDefinitionValue? defValues h.name with
          | .lfDefinition, some value =>
            lfExprSyntaxInModelInstance defValues modelIdent locals value
          | _, _ => do
              let field := mkIdent h.name
              `($modelIdent.$field:ident)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app f a) => do
      if let some reduced := reduceCheckedLFHeadRedex? defValues
          (lfLocalSyntaxSourceNames locals) e then
        lfExprSyntaxInModelInstance defValues modelIdent locals reduced
      else
        let f ← lfExprSyntaxInModelInstance defValues modelIdent locals f
        let a ← lfExprSyntaxInModelInstance defValues modelIdent locals a
        `($f $a)
  | .arrow none A B => do
      let A ← lfExprSyntaxInModelInstance defValues modelIdent locals A
      let B ← lfExprSyntaxInModelInstance defValues modelIdent locals B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ← lfExprSyntaxInModelInstance defValues modelIdent locals A
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfExprSyntaxInModelInstance defValues modelIdent ((x, xId) :: locals) B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfExprSyntaxInModelInstance defValues modelIdent locals A
      let B ← lfExprSyntaxInModelInstance defValues modelIdent locals B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfExprSyntaxInModelInstance defValues modelIdent locals A
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfExprSyntaxInModelInstance defValues modelIdent ((x, xId) :: locals) B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfExprSyntaxInModelInstance defValues modelIdent locals a
      let b ← lfExprSyntaxInModelInstance defValues modelIdent locals b
      `(⟨$a, $b⟩)
  | e@(.fst value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstance defValues modelIdent locals reduced
      else
        let value ← lfExprSyntaxInModelInstance defValues modelIdent locals value
        `(($value).1)
  | e@(.snd value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstance defValues modelIdent locals reduced
      else
        let value ← lfExprSyntaxInModelInstance defValues modelIdent locals value
        `(($value).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let xId := freshLFModelLocalIdent x modelIdent locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntaxInModelInstance defValues modelIdent locals body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfExprSyntaxInModelInstance defValues modelIdent locals lhs
      let rhs ← lfExprSyntaxInModelInstance defValues modelIdent locals rhs
      `($lhs = $rhs)

/-- Whether a source LF expression can be rendered in the LF-model backend after staged
LF definitions are expanded. This is used for instantiated side-condition certificates. -/
partial def lfObjExprRenderableInModel (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) : ObjExpr → Bool
  | .ident n =>
      let n := n.eraseMacroScopes
      match lfDefinitionValue? defValues n with
      | some value => lfExprRenderableInModel defValues blockingUntyped sidePredicateNames value
      | none => !blockingUntyped.contains n || sidePredicateNames.contains n
  | .sort => true
  | .univ _ => true
  | .app f a => lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames f &&
      lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames A &&
      lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames B
  | .pair a b => lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames a &&
      lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames b
  | .fst e | .snd e => lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames e
  | .lam _ body => lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames body
  | .jeq lhs rhs => lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames lhs &&
      lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames rhs

/-- Syntax for a source LF expression in an LF-model structure field, expanding staged LF
definitions to their checked values. -/
partial def lfObjExprSyntaxInModel (defValues : NameMap CheckedLFExpr)
    (locals : LFLocalSyntaxCtx) : ObjExpr → CommandElabM (TSyntax `term)
  | .ident n =>
      let n := n.eraseMacroScopes
      match findLFLocalIdent? locals n, lfDefinitionValue? defValues n with
      | some localId, _ => pure localId
      | none, some value => lfExprSyntaxInModel defValues locals value
      | none, none => pure (mkIdent n)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | .app f a => do
      let f ← lfObjExprSyntaxInModel defValues locals f
      let a ← lfObjExprSyntaxInModel defValues locals a
      `($f $a)
  | .arrow none A B | .funArrow none A B => do
      let A ← lfObjExprSyntaxInModel defValues locals A
      let B ← lfObjExprSyntaxInModel defValues locals B
      `($A → $B)
  | .arrow (some x) A B | .funArrow (some x) A B => do
      let A ← lfObjExprSyntaxInModel defValues locals A
      let x := x.eraseMacroScopes
      let xId := freshLFLocalIdent x locals
      let B ← lfObjExprSyntaxInModel defValues ((x, xId) :: locals) B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfObjExprSyntaxInModel defValues locals A
      let B ← lfObjExprSyntaxInModel defValues locals B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfObjExprSyntaxInModel defValues locals A
      let x := x.eraseMacroScopes
      let xId := freshLFLocalIdent x locals
      let B ← lfObjExprSyntaxInModel defValues ((x, xId) :: locals) B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfObjExprSyntaxInModel defValues locals a
      let b ← lfObjExprSyntaxInModel defValues locals b
      `(⟨$a, $b⟩)
  | .fst e => do
      let e ← lfObjExprSyntaxInModel defValues locals e
      `(($e).1)
  | .snd e => do
      let e ← lfObjExprSyntaxInModel defValues locals e
      `(($e).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if i < xs.size then
          let x := xs[i]!.eraseMacroScopes
          let xId := freshLFLocalIdent x locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfObjExprSyntaxInModel defValues locals body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfObjExprSyntaxInModel defValues locals lhs
      let rhs ← lfObjExprSyntaxInModel defValues locals rhs
      `($lhs = $rhs)

/-- Syntax for a source LF expression projected from a concrete LF model instance. -/
partial def lfObjExprSyntaxInModelInstance (defValues : NameMap CheckedLFExpr)
    (modelIdent : Ident) (locals : LFLocalSyntaxCtx) : ObjExpr → CommandElabM (TSyntax `term)
  | .ident n =>
      let n := n.eraseMacroScopes
      match findLFLocalIdent? locals n, lfDefinitionValue? defValues n with
      | some localId, _ => pure localId
      | none, some value => lfExprSyntaxInModelInstance defValues modelIdent locals value
      | none, none => do
          let field := mkIdent n
          `($modelIdent.$field:ident)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | .app f a => do
      let f ← lfObjExprSyntaxInModelInstance defValues modelIdent locals f
      let a ← lfObjExprSyntaxInModelInstance defValues modelIdent locals a
      `($f $a)
  | .arrow none A B | .funArrow none A B => do
      let A ← lfObjExprSyntaxInModelInstance defValues modelIdent locals A
      let B ← lfObjExprSyntaxInModelInstance defValues modelIdent locals B
      `($A → $B)
  | .arrow (some x) A B | .funArrow (some x) A B => do
      let A ← lfObjExprSyntaxInModelInstance defValues modelIdent locals A
      let x := x.eraseMacroScopes
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfObjExprSyntaxInModelInstance defValues modelIdent ((x, xId) :: locals) B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfObjExprSyntaxInModelInstance defValues modelIdent locals A
      let B ← lfObjExprSyntaxInModelInstance defValues modelIdent locals B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfObjExprSyntaxInModelInstance defValues modelIdent locals A
      let x := x.eraseMacroScopes
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfObjExprSyntaxInModelInstance defValues modelIdent ((x, xId) :: locals) B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfObjExprSyntaxInModelInstance defValues modelIdent locals a
      let b ← lfObjExprSyntaxInModelInstance defValues modelIdent locals b
      `(⟨$a, $b⟩)
  | .fst e => do
      let e ← lfObjExprSyntaxInModelInstance defValues modelIdent locals e
      `(($e).1)
  | .snd e => do
      let e ← lfObjExprSyntaxInModelInstance defValues modelIdent locals e
      `(($e).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if i < xs.size then
          let x := xs[i]!.eraseMacroScopes
          let xId := freshLFModelLocalIdent x modelIdent locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfObjExprSyntaxInModelInstance defValues modelIdent locals body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfObjExprSyntaxInModelInstance defValues modelIdent locals lhs
      let rhs ← lfObjExprSyntaxInModelInstance defValues modelIdent locals rhs
      `($lhs = $rhs)

/-- Already-rendered LF model binder, retaining source explicit/implicit visibility. -/
structure LFRenderedBinder where
  /-- Binder name. -/
  name : Name
  /-- Rendered Lean type. -/
  typeStx : TSyntax `term
  /-- Source object-binder visibility. -/
  visibility : BinderVisibility := .explicit

/-- Render one LF model binder as a Lean binder. -/
def lfRenderedBinderSyntax (b : LFRenderedBinder) :
  CommandElabM (TSyntax ``Lean.Parser.Term.bracketedBinder) := do
  let id := mkIdent b.name
  let ty := b.typeStx
  match b.visibility with
  | .explicit => `(bracketedBinder|($id:ident : $ty))
  | .implicit => `(bracketedBinder|{$id:ident : $ty})

/-- Build a dependent function type from already-rendered named LF binders. -/
partial def lfRenderedTelescopeSyntax (binders : Array LFRenderedBinder) (result : TSyntax `term)
    (i : Nat := 0) : CommandElabM (TSyntax `term) := do
  if h : i < binders.size then
    let b ← lfRenderedBinderSyntax binders[i]
    let rest ← lfRenderedTelescopeSyntax binders result (i + 1)
    `($b:bracketedBinder → $rest)
  else
    pure result

/-- Build a dependent function type from checked LF binders. -/
partial def lfTelescopeSyntax (binders : Array CheckedLFBinding) (result : TSyntax `term)
    (locals : LFLocalSyntaxCtx := []) (i : Nat := 0) : CommandElabM (TSyntax `term) := do
  if h : i < binders.size then
    let b := binders[i]
    let ty ← lfExprSyntax locals b.checkedTypeExpr
    let xId := freshLFLocalIdent b.name locals
    let rest ← lfTelescopeSyntax binders result ((b.name, xId) :: locals) (i + 1)
    let binder ← lfRenderedBinderSyntax { name := xId.getId, typeStx := ty, visibility :=
      b.visibility }
    `($binder:bracketedBinder → $rest)
  else
    pure result

/-- Build a dependent function type from already-rendered named LF binders. -/
partial def lfTermTelescopeSyntax (binders : Array (Name × TSyntax `term)) (result : TSyntax `term)
    (i : Nat := 0) : CommandElabM (TSyntax `term) := do
  let rendered := binders.map fun (n, ty) => ({ name := n, typeStx := ty } : LFRenderedBinder)
  lfRenderedTelescopeSyntax rendered result i

/-- Build a dependent function type from checked LF binders while expanding LF definitions. -/
partial def lfTelescopeSyntaxInModel (defValues : NameMap CheckedLFExpr)
    (binders : Array CheckedLFBinding) (result : TSyntax `term)
    (locals : LFLocalSyntaxCtx := []) (i : Nat := 0) : CommandElabM (TSyntax `term) := do
  if h : i < binders.size then
    let b := binders[i]
    let ty ← lfExprSyntaxInModel defValues locals b.checkedTypeExpr
    let xId := freshLFLocalIdent b.name locals
    let rest ← lfTelescopeSyntaxInModel defValues binders result ((b.name, xId) :: locals) (i + 1)
    let binder ← lfRenderedBinderSyntax { name := xId.getId, typeStx := ty, visibility :=
      b.visibility }
    `($binder:bracketedBinder → $rest)
  else
    pure result

/-- Syntax for one generated LF-model field. -/
def lfFieldSyntax (doc : String) (name : Name) (typeStx : TSyntax `term) :
    CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let fieldId := mkIdent name
  if doc == "admitted lf_opaque" then
    `(Lean.Parser.Command.structSimpleBinder|
      /-- TEMPORARY admitted-definition field. Prefer closing the source internal `sorry` and
      regenerating the model interface; fill this field only as a model-development escape hatch. -/
      $fieldId:ident : $typeStx)
  else
    `(Lean.Parser.Command.structSimpleBinder|
      /-- Generated LF model field. -/
      $fieldId:ident : $typeStx)

/-- Field for a checked LF syntax sort, interpreted as a Lean type family. -/
def lfSyntaxSortFieldSyntax (defValues : NameMap CheckedLFExpr) (s : CheckedLFSyntaxSort) :
    CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let result ← typeSyntaxOfLevel s.resultLevel
  let ty ← lfTelescopeSyntaxInModel defValues s.params result
  lfFieldSyntax "syntax sort" s.name ty

/-- Field for a checked LF judgment, interpreted as a proof-relevant Lean type family. -/
def lfJudgmentFieldSyntax (defValues : NameMap CheckedLFExpr) (j : CheckedLFJudgment) :
    CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let result ← `(Type)
  let ty ← lfTelescopeSyntaxInModel defValues j.params result
  lfFieldSyntax "judgment" j.name ty

/-- Field for a typed LF opaque constant. Untyped placeholders are intentionally omitted. -/
def lfOpaqueFieldSyntax? (defValues : NameMap CheckedLFExpr) (c : CheckedLFOpaqueConst) :
    CommandElabM (Option (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  match c.checkedTypeExpr? with
  | none => pure none
  | some typeExpr =>
      let result ← lfExprSyntaxInModel defValues [] typeExpr
      let ty ← lfTelescopeSyntaxInModel defValues c.params result
      let field ← lfFieldSyntax "opaque LF constant" c.name ty
      pure (some field)

/-- Field for an inferred side-condition predicate. -/
def lfSideConditionPredicateFieldSyntax (defValues : NameMap CheckedLFExpr) (p :
  LFSideConditionPredicate) :
    CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let result ← `(Type)
  let ty ← lfTelescopeSyntaxInModel defValues p.params result
  lfFieldSyntax "side-condition predicate" p.name ty

/-- Whether the first LF-model backend can render this rule as a typed model operation. -/
def lfRuleRenderable (untyped : NameSet) (r : CheckedLFRule) : Bool :=
  !(r.params.any (lfBindingMentionsAny untyped)) &&
    !(r.premises.any (fun p => lfExprMentionsAny untyped p.checkedJudgmentExpr)) &&
    !(r.paramEvidences.any (fun e => lfExprMentionsAny untyped e.checkedJudgmentExpr)) &&
    !(lfExprMentionsAny untyped r.checkedConclusionExpr)

/-- Field for a checked LF rule, interpreted as an operation from premises and side-condition
certificates to its conclusion. Side-condition inputs are represented by their checked
obligation types when those types can be rendered; solver-specific semantics can refine
these slots later. -/
def lfRuleFieldSyntax? (defValues : NameMap CheckedLFExpr) (blockingUntyped sidePredicateNames :
  NameSet)
    (r : CheckedLFRule) :
      CommandElabM (Option (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  unless lfRuleRenderable blockingUntyped r do
    return none
  let mut locals : LFLocalSyntaxCtx := []
  let mut binders : Array LFRenderedBinder := #[]
  for p in r.params do
    let ty ← lfExprSyntaxInModel defValues locals p.checkedTypeExpr
    let id := freshLFLocalIdent p.name locals
    binders := binders.push { name := id.getId, typeStx := ty, visibility := p.visibility }
    locals := (p.name, id) :: locals
  for p in r.premises do
    let ty ← lfExprSyntaxInModel defValues locals p.checkedJudgmentExpr
    binders := binders.push { name := p.name, typeStx := ty }
  for e in r.paramEvidences do
    let ty ← lfExprSyntaxInModel defValues locals e.checkedJudgmentExpr
    binders := binders.push { name := e.name, typeStx := ty }
  for sc in r.sideConditions do
    let ty ←
      if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames sc.checkedInput then
        lfExprSyntaxInModel defValues locals sc.checkedInput
      else
        `(Type)
    binders := binders.push { name := sc.name, typeStx := ty }
  let concl ← lfExprSyntaxInModel defValues locals r.checkedConclusionExpr
  let ty ← lfRenderedTelescopeSyntax binders concl
  let field ← lfFieldSyntax "LF rule" r.name ty
  pure (some field)

/-- A theorem-local semantic certificate required to replay one theorem side condition.

These are generated as derived-theorem parameters, not as global model fields, so a model
instance is not forced to carry certificates for every theorem the user might replay. -/
structure LFTheoremSideConditionField where
  /-- Checked theorem whose replay consumes this side condition. -/
  theoremName : Name
  /-- Path to the rule application inside the theorem proof tree. -/
  path : Array Nat := #[]
  /-- Applied LF rule. -/
  ruleName : Name
  /-- Side-condition slot name. -/
  sideConditionName : Name
  /-- Generated theorem-parameter name. -/
  fieldName : Name
  /-- Instantiated, closed side-condition input. -/
  input : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Generated parameter name for a theorem-specific side-condition certificate. -/
def lfTheoremSideConditionFieldName (theoremName : Name) (path : Array Nat) (sideConditionName :
  Name) : Name :=
  let pathText := if path.isEmpty then "root" else String.intercalate "_" (path.toList.map toString)
  Name.mkSimple s!"{flatNameString theoremName}_side_{pathText}_{flatNameString sideConditionName}"

/-- Source-level substitution produced by a rule application's explicit parameter arguments. -/
def lfRuleArgSubst (r : CheckedLFRule) (ruleArgs : Array ObjExpr) : NameMap ObjExpr := Id.run do
  let mut subst := {}
  for p in r.params, arg in ruleArgs do
    subst := subst.insert p.name.eraseMacroScopes (eraseObjExprScopes arg)
  return subst

/-- Deduplicate theorem certificate requirements by generated parameter name. -/
def dedupeLFTheoremSideConditionFields (fields : Array LFTheoremSideConditionField) :
  Array LFTheoremSideConditionField := Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  for f in fields do
    if !seen.contains f.fieldName then
      seen := seen.insert f.fieldName
      out := out.push f
  return out

/-- Find a checked LF theorem by name. -/
def findCheckedLFJudgmentTheorem? (theorems : Array CheckedLFJudgmentTheorem) (name : Name) :
    Option CheckedLFJudgmentTheorem :=
  theorems.find? fun t => t.name == name.eraseMacroScopes

/-- Collect direct theorem-specific side-condition parameters needed by one proof tree.
Theorem references are handled separately by `lfTheoremSideConditionFieldsForTheorem`, so
parameter names remain attached to the theorem that originally needs the certificate. -/
partial def collectDirectLFTheoremSideConditionFieldsInDerivation (rules : Array CheckedLFRule)
    (theoremName : Name) (path : Array Nat) :
      CheckedLFDerivation → Array LFTheoremSideConditionField
  | .localAssumption .. => #[]
  | .theoremRef _ _ _ premises => Id.run do
      let mut out := #[]
      for i in List.range premises.size do
        match premises[i]? with
        | none => pure ()
        | some prem =>
            out := out



















              ++ collectDirectLFTheoremSideConditionFieldsInDerivation rules theoremName (path.push
                i) prem
      return out
  | .ruleApp ruleName _ ruleArgs premises _ => Id.run do
      let mut out := #[]
      if let some r := findCheckedLFRule? rules ruleName then
        let subst := lfRuleArgSubst r ruleArgs
        for sc in r.sideConditions do
          let input := eraseObjExprScopes (substLFParams subst sc.input)
          out := out.push {
            theoremName := theoremName
            path := path
            ruleName := ruleName
            sideConditionName := sc.name
            fieldName := lfTheoremSideConditionFieldName theoremName path sc.name
            input := input }
      for i in List.range premises.size do
        match premises[i]? with
        | none => pure ()
        | some prem =>
            out := out



















              ++ collectDirectLFTheoremSideConditionFieldsInDerivation rules theoremName (path.push
                i) prem
      return out

/-- Collect theorem references occurring in a checked LF derivation. -/
partial def lfTheoremRefsInDerivation : CheckedLFDerivation → Array Name
  | .localAssumption .. => #[]
  | .theoremRef name _ _ premises => Id.run do
      let mut out := #[name.eraseMacroScopes]
      for prem in premises do
        out := out ++ lfTheoremRefsInDerivation prem
      return out
  | .ruleApp _ _ _ premises _ => Id.run do
      let mut out := #[]
      for prem in premises do
        out := out ++ lfTheoremRefsInDerivation prem
      return out

/-- Collect certificate parameters needed to replay a theorem, including parameters needed
by referenced derived theorems. Cycles are ignored defensively; ordered theorem checking
already rejects future theorem references in normal inputs. -/
partial def lfTheoremSideConditionFieldsForTheorem (checked : CheckedSignature) (theoremName : Name)
    (visited : NameSet := {}) : Array LFTheoremSideConditionField := Id.run do
  let theoremName := theoremName.eraseMacroScopes
  if visited.contains theoremName then
    return #[]
  let visited := visited.insert theoremName
  let some t := findCheckedLFJudgmentTheorem? checked.lfJudgmentTheorems theoremName
    | return #[]
  let some derivation := t.derivation?
    | return #[]
  let mut out :=
    collectDirectLFTheoremSideConditionFieldsInDerivation checked.lfRules theoremName #[] derivation
  for refName in lfTheoremRefsInDerivation derivation do
    out := out ++ lfTheoremSideConditionFieldsForTheorem checked refName visited
  return dedupeLFTheoremSideConditionFields out

/-- Collect theorem-specific side-condition parameters from all checked LF theorem replays. -/
def lfTheoremSideConditionFields (checked : CheckedSignature) :
  Array LFTheoremSideConditionField := Id.run do
  let mut out := #[]
  for t in checked.lfJudgmentTheorems do
    if let some derivation := t.derivation? then
      out := out



















        ++ collectDirectLFTheoremSideConditionFieldsInDerivation checked.lfRules t.name #[]
          derivation
  return dedupeLFTheoremSideConditionFields out

/-- Whether a theorem-specific side-condition certificate parameter is renderable. -/
def lfTheoremSideConditionFieldRenderable (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) (f : LFTheoremSideConditionField) : Bool :=
  lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames f.input

/-- Source declaration class for a generic LF model obligation.

This IR is intentionally LF-shaped: it classifies checked LF metadata and generated LF replay
artifacts for the model-interface backend. -/
inductive LFModelObligationSource where
  | syntaxSort
  | judgment
  | typedOpaque
  | admittedOpaque
  | untypedOpaque
  | sideConditionPredicate
  | theoremSideConditionCertificate
  | rule
  | objectDefinition
  | judgmentTheorem
  deriving Inhabited, Repr, BEq

namespace LFModelObligationSource

/-- Human-readable source declaration class for model-obligation diagnostics. -/
def label : LFModelObligationSource → String
  | .syntaxSort => "syntax_sort"
  | .judgment => "judgment"
  | .typedOpaque => "typed lf_opaque"
  | .admittedOpaque => "admitted lf_opaque"
  | .untypedOpaque => "untyped lf_opaque"
  | .sideConditionPredicate => "side-condition predicate"
  | .theoremSideConditionCertificate => "theorem side-condition certificate"
  | .rule => "rule"
  | .objectDefinition => "lf_def"
  | .judgmentTheorem => "judgment_theorem"

end LFModelObligationSource

/-- Intended generated Lean role for a generic LF model obligation. -/
inductive LFModelGeneratedRole where
  | field
  | derivedDeclaration
  | derivedParameter
  | replayArtifact
  | metadataExpansion
  | omitted
  deriving Inhabited, Repr, BEq

namespace LFModelGeneratedRole

/-- Human-readable generated role for model-obligation diagnostics. -/
def label : LFModelGeneratedRole → String
  | .field => "model field"
  | .derivedDeclaration => "derived declaration"
  | .derivedParameter => "derived parameter"
  | .replayArtifact => "replay artifact"
  | .metadataExpansion => "metadata expansion"
  | .omitted => "omitted"

end LFModelGeneratedRole

/-- Generation/filtering mode for LF model interfaces. -/
inductive LFModelInterfaceMode where
  /-- Full/debug interface preserving all current generated obligations. -/
  | full
  /-- Public/minimal interface omitting declarations marked `model_internal`/`model_compat` and
  obligations depending on them. -/
  | publicMode
  deriving Inhabited, Repr, BEq

namespace LFModelInterfaceMode

/-- Human-readable mode label. -/
def label : LFModelInterfaceMode → String
  | .full => "full/debug"
  | .publicMode => "public/minimal"

/-- Command spelling used in next-action hints. -/
def commandPrefix : LFModelInterfaceMode → String
  | .full => ""
  | .publicMode => "public_"

end LFModelInterfaceMode

/-- Generic LF model-obligation IR.

The IR is the staging boundary between checked LF/profile artifacts and concrete Lean
model-interface generation. Later milestones should generate dependent structure fields
from this data rather than re-inspecting frontend-specific traces. -/
structure LFModelObligation where
  /-- Source or generated artifact name. -/
  name : Name
  /-- Source LF/profile declaration class. -/
  source : LFModelObligationSource
  /-- Intended generated Lean role. -/
  generatedRole : LFModelGeneratedRole
  /-- Generated field/declaration name, when one exists. -/
  generatedName? : Option Name := none
  /-- Checked dependent LF parameters when available. -/
  params : Array CheckedLFBinding := #[]
  /-- Parameter count when the full checked binder telescope is encoded in the LF expression. -/
  paramCount : Nat := 0
  /-- Main checked LF type/statement/result attached to the obligation. -/
  typeExpr? : Option CheckedLFExpr := none
  /-- Additional checked LF statements, e.g. type/body replay statements for declarations. -/
  extraStatements : Array CheckedLFExpr := #[]
  /-- Source LF/object expression attached to the obligation when it is not represented by
  `typeExpr?`. -/
  sourceObjExpr? : Option ObjExpr := none
  /-- Rule premises when this obligation is a generated rule field. -/
  premises : Array CheckedLFRulePremise := #[]
  /-- Rule parameter-evidence premises when this obligation is a generated rule field. -/
  paramEvidences : Array CheckedLFRuleParamEvidence := #[]
  /-- Rule side-condition slots when this obligation is a generated rule field. -/
  sideConditions : Array CheckedLFRuleSideCondition := #[]
  /-- Rule premise count, for rule-like obligations. -/
  premiseCount : Nat := 0
  /-- Rule side-condition count, for rule-like obligations. -/
  sideConditionCount : Nat := 0
  /-- Whether the current generic backend can render this obligation. -/
  renderable : Bool := true
  /-- Model-interface visibility inherited from source metadata. -/
  visibility : ModelVisibilityKind := .public_
  /-- Diagnostic explaining an omission or special staging status. -/
  diagnostic? : Option String := none
  deriving Inhabited, Repr, BEq

/-- Diagnostic label for an obligation's renderability. -/
def LFModelObligation.statusLabel (o : LFModelObligation) : String :=
  if o.renderable then "ready" else "blocked"

/-- Diagnostic summary for a generic LF model obligation. -/
def LFModelObligation.summary (o : LFModelObligation) : MessageData :=
  let generated := match o.generatedName? with
    | some n => m!", generated={n}"
    | none => m!""
  let params :=
    if o.paramCount == 0 then m!"" else m!", params={o.paramCount}"
  let premises :=
    if o.premiseCount == 0 then m!"" else m!", premises={o.premiseCount}"
  let sides :=
    if o.sideConditionCount == 0 then m!"" else m!", side_conditions={o.sideConditionCount}"
  let ty := match o.typeExpr? with
    | some e => m!", type={e.summary}"
    | none => m!""
  let extra :=
    if o.extraStatements.isEmpty then m!"" else m!", extra_statements={o.extraStatements.size}"
  let visibility := if o.visibility == .public_ then m!"" else m!", visibility={o.visibility.label}"
  let diagnostic := match o.diagnostic? with
    | some d => m!", note={d}"
    | none => m!""
  m!"[{o.statusLabel}] {o.generatedRole.label}: {o.source.label} \
    {o.name}{generated}{params}{premises}{sides}{ty}{extra}{visibility}{diagnostic}"

/-- Count model obligations satisfying a predicate. -/
def countLFModelObligations (obs : Array LFModelObligation) (p : LFModelObligation → Bool) : Nat :=
  obs.foldl (init := 0) fun n o => if p o then n + 1 else n

/-- Names of admitted LF opaque constants, before temporary-field promotion is computed. -/
def internalAdmissionNameSet (admissions : Array InternalAdmission) : NameSet :=
  admissions.foldl (init := {}) fun names a =>
    if a.kind == .lfOpaque then names.insert a.declName.eraseMacroScopes else names

/-- Whether a checked LF type is a structural function/package type rather than a rigid head. -/
def checkedLFExprIsStructuralObjectType : CheckedLFExpr → Bool
  | .arrow .. | .sigma .. => true
  | _ => false

/-- Union of two name sets. -/
def unionNameSet (xs ys : NameSet) : NameSet := Id.run do
  let mut out := xs
  for n in ys.toList do
    out := out.insert n
  return out

/-- Model-visibility annotations keyed by source declaration name. -/
def lfModelVisibilityMap (checked : CheckedSignature) : NameMap ModelVisibilityKind := Id.run do
  let mut out : NameMap ModelVisibilityKind := {}
  for v in checked.modelVisibilities do
    out := out.insert v.declName.eraseMacroScopes v.visibility
  return out

/-- Source visibility for a declaration, defaulting to public. -/
def lfModelVisibilityOf (checked : CheckedSignature) (n : Name) : ModelVisibilityKind :=
  (lfModelVisibilityMap checked).find? n.eraseMacroScopes |>.getD .public_

/-- Names hidden from public/minimal LF model interfaces. -/
def lfModelPublicHiddenNames (checked : CheckedSignature) : NameSet := Id.run do
  let mut out : NameSet := {}
  for v in checked.modelVisibilities do
    if v.visibility == .internal || v.visibility == .compat then
      out := out.insert v.declName.eraseMacroScopes
  return out

/-- Whether an obligation mentions any hidden model-interface dependency. -/
def lfModelObligationMentionsAny (names : NameSet) (o : LFModelObligation) : Bool :=
  o.params.any (lfBindingMentionsAny names) ||
    (match o.typeExpr? with | some e => lfExprMentionsAny names e | none => false) ||
    o.extraStatements.any (lfExprMentionsAny names) ||
    o.premises.any (fun p => lfExprMentionsAny names p.checkedJudgmentExpr) ||
    o.paramEvidences.any (fun e => lfExprMentionsAny names e.checkedJudgmentExpr) ||
    o.sideConditions.any (fun s => lfExprMentionsAny names s.checkedInput)

/-- Whether an obligation is a temporary field for a `sorry`-admitted internal definition. -/
def LFModelObligation.isTemporaryAdmissionField (o : LFModelObligation) : Bool :=
  o.source == .admittedOpaque && o.generatedRole == .field && o.renderable

/-- Dependency singleton for a rendered LF-model source name. -/
def lfModelRenderedDependency (targetNames : NameSet) (n : Name) : NameSet :=
  let n := n.eraseMacroScopes
  if targetNames.contains n then ({n} : NameSet) else {}

/-- Dependencies introduced by rendering a checked LF expression in a model structure.

This mirrors `lfExprSyntaxInModelWithFields`: checked LF definitions are expanded before syntax is
produced, so generated-field dependencies introduced by their bodies must be attributed to the
field being rendered. -/
partial def lfExprRenderedFieldDependencies (defValues : NameMap CheckedLFExpr)
    (targetNames locals visitedDefs : NameSet) : CheckedLFExpr → NameSet
  | .ident h =>
      let n := h.name.eraseMacroScopes
      if h.kind == .local || locals.contains n then
        {}
      else if h.kind == .lfDefinition then
        match lfDefinitionValue? defValues n with
        | some value =>
            if visitedDefs.contains n then {}
            else lfExprRenderedFieldDependencies defValues targetNames locals
              (visitedDefs.insert n) value
        | none => lfModelRenderedDependency targetNames n
      else
        lfModelRenderedDependency targetNames n
  | .sort => {}
  | .univ _ => {}
  | .app f a =>
      insertNameSet
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs f)
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs a)
  | .arrow none A B | .sigma none A B =>
      insertNameSet
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs A)
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs B)
  | .arrow (some x) A B | .sigma (some x) A B =>
      let depsA := lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs A
      let locals := locals.insert x.eraseMacroScopes
      insertNameSet depsA
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs B)
  | .pair a b =>
      insertNameSet
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs a)
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs b)
  | .fst e | .snd e =>
      lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs e
  | .lam xs body =>
      let locals := xs.foldl (fun acc x => acc.insert x.eraseMacroScopes) locals
      lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs body
  | .jeq lhs rhs =>
      insertNameSet
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs lhs)
        (lfExprRenderedFieldDependencies defValues targetNames locals visitedDefs rhs)

/-- Dependencies introduced by rendering a source LF expression in a model structure. -/
partial def lfObjExprRenderedFieldDependencies (defValues : NameMap CheckedLFExpr)
    (targetNames locals visitedDefs : NameSet) : ObjExpr → NameSet
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        {}
      else
        match lfDefinitionValue? defValues n with
        | some value =>
            if visitedDefs.contains n then {}
            else lfExprRenderedFieldDependencies defValues targetNames locals
              (visitedDefs.insert n) value
        | none => lfModelRenderedDependency targetNames n
  | .sort => {}
  | .univ _ => {}
  | .app f a =>
      insertNameSet
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs f)
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs a)
  | .arrow none A B | .funArrow none A B | .sigma none A B =>
      insertNameSet
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs A)
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs B)
  | .arrow (some x) A B | .funArrow (some x) A B | .sigma (some x) A B =>
      let depsA := lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs A
      let locals := locals.insert x.eraseMacroScopes
      insertNameSet depsA
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs B)
  | .pair a b =>
      insertNameSet
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs a)
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs b)
  | .fst e | .snd e =>
      lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs e
  | .lam xs body =>
      let locals := xs.foldl (fun acc x => acc.insert x.eraseMacroScopes) locals
      lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs body
  | .jeq lhs rhs =>
      insertNameSet
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs lhs)
        (lfObjExprRenderedFieldDependencies defValues targetNames locals visitedDefs rhs)

/-- Target source names mentioned by an LF model obligation after renderer-style expansion. -/
def lfModelObligationRenderedFieldDependencies (defValues : NameMap CheckedLFExpr)
    (targetNames : NameSet) (o : LFModelObligation) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut locals : NameSet := {}
  for p in o.params do
    out := insertNameSet out <|
      lfExprRenderedFieldDependencies defValues targetNames locals {} p.checkedTypeExpr
    locals := locals.insert p.name.eraseMacroScopes
  if let some e := o.typeExpr? then
    out := insertNameSet out <| lfExprRenderedFieldDependencies defValues targetNames locals {} e
  for e in o.extraStatements do
    out := insertNameSet out <| lfExprRenderedFieldDependencies defValues targetNames locals {} e
  if let some e := o.sourceObjExpr? then
    out := insertNameSet out <| lfObjExprRenderedFieldDependencies defValues targetNames locals {} e
  for p in o.premises do
    out := insertNameSet out <|
      lfExprRenderedFieldDependencies defValues targetNames locals {} p.checkedJudgmentExpr
  for e in o.paramEvidences do
    out := insertNameSet out <|
      lfExprRenderedFieldDependencies defValues targetNames locals {} e.checkedJudgmentExpr
  for s in o.sideConditions do
    out := insertNameSet out <|
      lfExprRenderedFieldDependencies defValues targetNames locals {} s.checkedInput
  return out

/-- Universe-level parameters occurring in one object-level universe expression. -/
def levelExprParamSet (u : LevelExpr) : NameSet :=
  u.params.foldl (fun acc n => acc.insert n.eraseMacroScopes) {}

/-- Universe parameters introduced by rendering a checked LF expression in a model structure.

This mirrors field rendering: checked LF definitions are expanded before syntax is produced. -/
partial def lfExprRenderedLevelParams (defValues : NameMap CheckedLFExpr)
    (locals visitedDefs : NameSet) : CheckedLFExpr → NameSet
  | .ident h =>
      let n := h.name.eraseMacroScopes
      if h.kind == .local || locals.contains n then
        {}
      else if h.kind == .lfDefinition then
        match lfDefinitionValue? defValues n with
        | some value =>
            if visitedDefs.contains n then {}
            else lfExprRenderedLevelParams defValues locals (visitedDefs.insert n) value
        | none => {}
      else
        {}
  | .sort => {}
  | .univ u => levelExprParamSet u
  | .app f a =>
      insertNameSet (lfExprRenderedLevelParams defValues locals visitedDefs f)
        (lfExprRenderedLevelParams defValues locals visitedDefs a)
  | .arrow none A B | .sigma none A B =>
      insertNameSet (lfExprRenderedLevelParams defValues locals visitedDefs A)
        (lfExprRenderedLevelParams defValues locals visitedDefs B)
  | .arrow (some x) A B | .sigma (some x) A B =>
      let paramsA := lfExprRenderedLevelParams defValues locals visitedDefs A
      let locals := locals.insert x.eraseMacroScopes
      insertNameSet paramsA (lfExprRenderedLevelParams defValues locals visitedDefs B)
  | .pair a b =>
      insertNameSet (lfExprRenderedLevelParams defValues locals visitedDefs a)
        (lfExprRenderedLevelParams defValues locals visitedDefs b)
  | .fst e | .snd e => lfExprRenderedLevelParams defValues locals visitedDefs e
  | .lam xs body =>
      let locals := xs.foldl (fun acc x => acc.insert x.eraseMacroScopes) locals
      lfExprRenderedLevelParams defValues locals visitedDefs body
  | .jeq lhs rhs =>
      insertNameSet (lfExprRenderedLevelParams defValues locals visitedDefs lhs)
        (lfExprRenderedLevelParams defValues locals visitedDefs rhs)

/-- Universe parameters introduced by rendering a source LF expression in a model structure. -/
partial def lfObjExprRenderedLevelParams (defValues : NameMap CheckedLFExpr)
    (locals visitedDefs : NameSet) : ObjExpr → NameSet
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then
        {}
      else
        match lfDefinitionValue? defValues n with
        | some value =>
            if visitedDefs.contains n then {}
            else lfExprRenderedLevelParams defValues locals (visitedDefs.insert n) value
        | none => {}
  | .sort => {}
  | .univ u => levelExprParamSet u
  | .app f a =>
      insertNameSet (lfObjExprRenderedLevelParams defValues locals visitedDefs f)
        (lfObjExprRenderedLevelParams defValues locals visitedDefs a)
  | .arrow none A B | .funArrow none A B | .sigma none A B =>
      insertNameSet (lfObjExprRenderedLevelParams defValues locals visitedDefs A)
        (lfObjExprRenderedLevelParams defValues locals visitedDefs B)
  | .arrow (some x) A B | .funArrow (some x) A B | .sigma (some x) A B =>
      let paramsA := lfObjExprRenderedLevelParams defValues locals visitedDefs A
      let locals := locals.insert x.eraseMacroScopes
      insertNameSet paramsA (lfObjExprRenderedLevelParams defValues locals visitedDefs B)
  | .pair a b =>
      insertNameSet (lfObjExprRenderedLevelParams defValues locals visitedDefs a)
        (lfObjExprRenderedLevelParams defValues locals visitedDefs b)
  | .fst e | .snd e => lfObjExprRenderedLevelParams defValues locals visitedDefs e
  | .lam xs body =>
      let locals := xs.foldl (fun acc x => acc.insert x.eraseMacroScopes) locals
      lfObjExprRenderedLevelParams defValues locals visitedDefs body
  | .jeq lhs rhs =>
      insertNameSet (lfObjExprRenderedLevelParams defValues locals visitedDefs lhs)
        (lfObjExprRenderedLevelParams defValues locals visitedDefs rhs)

/-- Universe parameters that can occur in the rendered type of one model-interface field. -/
def lfModelObligationRenderedLevelParams (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) (o : LFModelObligation) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut locals : NameSet := {}
  for p in o.params do
    out := insertNameSet out <| lfExprRenderedLevelParams defValues locals {} p.checkedTypeExpr
    locals := locals.insert p.name.eraseMacroScopes
  if let some e := o.typeExpr? then
    out := insertNameSet out <| lfExprRenderedLevelParams defValues locals {} e
  if let some e := o.sourceObjExpr? then
    out := insertNameSet out <| lfObjExprRenderedLevelParams defValues locals {} e
  for p in o.premises do
    out := insertNameSet out <| lfExprRenderedLevelParams defValues locals {}
      p.checkedJudgmentExpr
  for e in o.paramEvidences do
    out := insertNameSet out <| lfExprRenderedLevelParams defValues locals {}
      e.checkedJudgmentExpr
  for s in o.sideConditions do
    if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames s.checkedInput then
      out := insertNameSet out <| lfExprRenderedLevelParams defValues locals {} s.checkedInput
  return out

/-- Keep level parameters in the order declared by the checked theory. -/
def orderedModelLevelParams (checked : CheckedSignature) (used : NameSet) : Array Name :=
  checked.levelParams.filter (fun u => used.contains u.eraseMacroScopes)

/-- Ordered union of several generated structure universe-parameter lists. -/
def orderedModelLevelParamUnion (checked : CheckedSignature) (levelSets : Array (Array Name)) :
    Array Name :=
  let used := levelSets.foldl (init := {}) fun acc levels =>
    levels.foldl (fun acc u => acc.insert u.eraseMacroScopes) acc
  orderedModelLevelParams checked used

/-- Typed admitted opaque obligations, i.e. admissions that can become temporary model fields. -/
def lfModelTypedAdmittedObligationNames (obs : Array LFModelObligation) : NameSet :=
  obs.foldl (init := {}) fun acc o =>
    if o.source == .admittedOpaque && o.typeExpr?.isSome then
      acc.insert o.name.eraseMacroScopes
    else
      acc

/-- Diagnostic attached to temporary model fields for `sorry`-admitted internal definitions. -/
def lfModelTemporaryAdmissionFieldDiagnostic : String :=
  "temporary model field for a sorry-admitted internal definition used by model-facing " ++
    "obligations; preferred fix: replace the internal `sorry` with a checked internal " ++
      "definition or internal proof term, then regenerate the model interface"

/-- Admitted internal definitions that must temporarily be fields because model fields mention
them.

The closure step accounts for temporary fields whose own types mention admitted definitions. -/
def lfModelTemporaryAdmissionFieldNamesFromObligations (defValues : NameMap CheckedLFExpr)
    (admittedNames : NameSet) (obs : Array LFModelObligation) : NameSet := Id.run do
  let typedAdmitted := lfModelTypedAdmittedObligationNames obs
  let admittedTargets := typedAdmitted.toList.foldl (init := {}) fun acc n =>
    if admittedNames.contains n.eraseMacroScopes then acc.insert n.eraseMacroScopes else acc
  let mut out : NameSet := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      out := insertNameSet out <|
        lfModelObligationRenderedFieldDependencies defValues admittedTargets o
  let mut changed := true
  while changed do
    changed := false
    for o in obs do
      let n := o.name.eraseMacroScopes
      if o.source == .admittedOpaque && out.contains n then
        let deps := lfModelObligationRenderedFieldDependencies defValues admittedTargets o
        for dep in deps.toList do
          let dep := dep.eraseMacroScopes
          if !out.contains dep then
            out := out.insert dep
            changed := true
  return out

/-- Explain why a checked LF rule is not renderable by the current generic LF model backend. -/
def lfRuleOmissionReason (blockingUntyped : NameSet) (r : CheckedLFRule) : String := Id.run do
  let mut reasons : Array String := #[]
  if r.params.any (lfBindingMentionsAny blockingUntyped) then
    reasons := reasons.push "parameter type mentions an untyped opaque placeholder"
  if r.premises.any (fun p => lfExprMentionsAny blockingUntyped p.checkedJudgmentExpr) then
    reasons := reasons.push "premise mentions an untyped opaque placeholder"
  if r.paramEvidences.any (fun e => lfExprMentionsAny blockingUntyped e.checkedJudgmentExpr) then
    reasons := reasons.push "parameter evidence mentions an untyped opaque placeholder"
  if lfExprMentionsAny blockingUntyped r.checkedConclusionExpr then
    reasons := reasons.push "conclusion mentions an untyped opaque placeholder"
  if reasons.isEmpty then "unsupported rule shape" else String.intercalate "; " reasons.toList

/-- Explain whether a checked LF object definition can be transported over a model. -/
def lfObjectDefTransportStatus (checked : CheckedSignature) (d : CheckedLFObjectDef) :
    Bool × Option String :=
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  if !lfExprRenderableInModel defValues blockingUntyped sidePredicateNames d.checkedTypeExpr then
    (false, some "definition type is not renderable by the LF-model backend")
  else if !lfExprRenderableInModel defValues blockingUntyped sidePredicateNames d.checkedValue then
    (false, some "definition value is not renderable by the LF-model backend")
  else
    (true, none)

/-- Explain the current generated role for a checked LF theorem over a model. -/
def lfJudgmentTheoremObligationStatus (checked : CheckedSignature) (t : CheckedLFJudgmentTheorem) :
    LFModelGeneratedRole × Bool × Option String :=
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  if t.derivation?.isNone then
    (.omitted, false, some "no checked derivation tree")
  else if t.checkedKernelDerivation?.isNone then
    (.omitted, false, some "no checked kernel replay artifact")
  else if t.binders.any (fun b =>
      !lfExprRenderableInModel defValues blockingUntyped sidePredicateNames b.checkedTypeExpr) then
    (.omitted, false, some "local binder type is not renderable by the LF-model backend")
  else if !lfExprRenderableInModel defValues blockingUntyped sidePredicateNames
      t.checkedJudgmentExpr then
    (.omitted, false, some "statement is not renderable by the LF-model backend")
  else if (lfTheoremSideConditionFieldsForTheorem checked t.name).any (fun f =>
      !lfTheoremSideConditionFieldRenderable defValues blockingUntyped sidePredicateNames f) then
    let reason :=
      "required side-condition certificate parameter is not renderable by " ++
        "the LF-model backend"
    (.omitted, false, some reason)
  else
    (.derivedDeclaration, true, none)

/-- Generic LF model obligations extracted from checked LF metadata and generated LF replay
artifacts.
`admittedNames` are typed LF opaque constants introduced by `internal def ... := sorry`.
Admitted opaque constants remain generated Lean declarations with `sorry` bodies unless the
dependency closure of a model-facing field needs them. Structural package-shaped admissions use the
same path, keeping proof debt lint-visible without adding user model fields. -/
def lfModelObligations (checked : CheckedSignature) (admittedNames : NameSet := {}) :
  Array LFModelObligation := Id.run do
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicates := lfSideConditionPredicates checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut out : Array LFModelObligation := #[]
  for s in checked.lfSyntaxSorts do
    out := out.push {
      name := s.name, source := .syntaxSort, generatedRole := .field,
      generatedName? := some s.name, params := s.params, paramCount := s.params.size,
      typeExpr? := some (checkedLFTypeOfLevel s.resultLevel) }
  for c in checked.lfOpaqueConsts do
    match c.checkedTypeExpr? with
    | some ty =>
        if admittedNames.contains c.name.eraseMacroScopes then
          out := out.push {
            name := c.name, source := .admittedOpaque, generatedRole := .derivedDeclaration,
            generatedName? := some c.name, params := c.params, paramCount := c.params.size,
            typeExpr? := some ty,
            diagnostic? := some
              "generated as a Lean declaration whose body uses sorry, not as a model field" }
        else
          out := out.push {
            name := c.name, source := .typedOpaque, generatedRole := .field,
            generatedName? := some c.name, params := c.params, paramCount := c.params.size,
            typeExpr? := some ty }
    | none =>
        if !sidePredicateNames.contains c.name then
          out := out.push {
            name := c.name, source := .untypedOpaque, generatedRole := .omitted,
            generatedName? := none, renderable := false,
            diagnostic? :=
              some "untyped opaque placeholder has no Lean model type; if it is a predicate, use \
                it as a rule side-condition head" }
  for j in checked.lfJudgments do
    out := out.push {
      name := j.name, source := .judgment, generatedRole := .field,
      generatedName? := some j.name, params := j.params, paramCount := j.params.size,
      typeExpr? := some .sort }
  for p in sidePredicates do
    out := out.push {
      name := p.name, source := .sideConditionPredicate, generatedRole := .field,
      generatedName? := some p.name, params := p.params, paramCount := p.params.size,
      typeExpr? := some .sort }
  for cert in lfTheoremSideConditionFields checked do
    let renderable :=
      lfTheoremSideConditionFieldRenderable defValues blockingUntyped sidePredicateNames cert
    out := out.push {
      name := cert.fieldName, source := .theoremSideConditionCertificate,
      generatedRole := if renderable then .derivedParameter else .omitted,
      generatedName? := if renderable then some cert.fieldName else none,
      sourceObjExpr? := some cert.input,
      renderable := renderable,
      diagnostic? := if renderable then some "generated as a derived-theorem parameter" else
        some "instantiated side-condition input is not renderable by the LF-model backend" }
  for r in checked.lfRules do
    let renderable := lfRuleRenderable blockingUntyped r
    out := out.push {
      name := r.name, source := .rule,
      generatedRole := if renderable then .field else .omitted,
      generatedName? := if renderable then some r.name else none,
      params := r.params, paramCount := r.params.size,
      typeExpr? := some r.checkedConclusionExpr,
      premises := r.premises,
      paramEvidences := r.paramEvidences,
      sideConditions := r.sideConditions,
      premiseCount := r.premises.size + r.paramEvidences.size,
      sideConditionCount := r.sideConditions.size,
      renderable := renderable,
      diagnostic? := if renderable then none else some (lfRuleOmissionReason blockingUntyped r) }
  for d in checked.lfObjectDefs do
    let renderable :=
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames d.checkedTypeExpr &&
      lfExprRenderableInModel defValues blockingUntyped sidePredicateNames d.checkedValue
    out := out.push {
      name := d.name, source := .objectDefinition,
      generatedRole := if renderable then .metadataExpansion else .omitted,
      generatedName? := some d.name,
      typeExpr? := some d.checkedTypeExpr,
      extraStatements := #[d.checkedValue], renderable := renderable,
      diagnostic? := if renderable then some "expanded during model expression rendering" else
        some "definition type or value is not renderable by the LF-model backend" }
  for t in checked.lfJudgmentTheorems do
    let (role, renderable, diagnostic?) := lfJudgmentTheoremObligationStatus checked t
    out := out.push {
      name := t.name, source := .judgmentTheorem, generatedRole := role,
      generatedName? := if renderable then some t.name else none,
      typeExpr? := some t.checkedJudgmentExpr, renderable := renderable,
      diagnostic? := diagnostic? }
  let tempAdmissions :=
    lfModelTemporaryAdmissionFieldNamesFromObligations defValues admittedNames out
  return out.map fun o =>
    let o :=
      if o.source == .admittedOpaque && tempAdmissions.contains o.name.eraseMacroScopes then
        { o with
          generatedRole := .field,
          generatedName? := some o.name,
          renderable := true,
          diagnostic? := some lfModelTemporaryAdmissionFieldDiagnostic }
      else
        o
    { o with visibility := lfModelVisibilityOf checked o.name }

/-- Apply a public/full model-interface mode to raw LF model obligations. -/
def lfModelObligationsForMode (checked : CheckedSignature) (mode : LFModelInterfaceMode)
    (obs : Array LFModelObligation) : Array LFModelObligation :=
  match mode with
  | .full => obs
  | .publicMode =>
      let hidden := lfModelPublicHiddenNames checked
      obs.map fun o =>
        if o.visibility == .internal then
          { o with
            generatedRole := .omitted
            generatedName? := none
            renderable := false
            diagnostic? :=
              some "internal helper omitted from public/minimal model interface; use the \
                full/debug interface to inspect it" }
        else if o.visibility == .compat then
          { o with
            generatedRole := .omitted
            generatedName? := none
            renderable := false
            diagnostic? :=
              some "compatibility artifact omitted from public/minimal model interface; use the \
                full/debug interface for legacy fields" }
        else if lfModelObligationMentionsAny hidden o then
          { o with
            generatedRole := .omitted
            generatedName? := none
            renderable := false
            diagnostic? :=
              some "depends on a declaration marked model_internal/model_compat; omitted from \
                public/minimal model interface" }
        else
          o

/-- Temporary admitted-definition fields selected for the current model-interface mode. -/
def lfModelTemporaryAdmissionFieldNames (checked : CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : NameSet :=
  let obs := lfModelObligationsForMode checked mode (lfModelObligations checked admittedNames)
  obs.foldl (init := {}) fun acc o =>
    if o.isTemporaryAdmissionField then acc.insert o.name.eraseMacroScopes else acc

/-- Summary for the generic LF model-obligation IR. -/
def lfModelObligationSummaryString (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : String :=
  let obs := lfModelObligationsForMode checked mode (lfModelObligations checked admittedNames)
  let fields := countLFModelObligations obs (fun o => o.generatedRole == .field && o.renderable)
  let derived := countLFModelObligations obs (fun o => o.generatedRole == .derivedDeclaration
    && o.renderable)
  let params := countLFModelObligations obs (fun o => o.generatedRole == .derivedParameter
    && o.renderable)
  let replay := countLFModelObligations obs (fun o => o.generatedRole == .replayArtifact
    && o.renderable)
  let expanded := countLFModelObligations obs (fun o => o.generatedRole == .metadataExpansion
    && o.renderable)
  let omitted := countLFModelObligations obs (fun o => o.generatedRole == .omitted || !o.renderable)
  let abbrevCount := checked.lfSyntaxAbbrevs.size + checked.lfJudgmentAbbrevs.size
  let abbrevText := if abbrevCount == 0 then "" else
    s!", {abbrevCount} LF abbreviation(s) expanded before fields"
  let modeText := if mode == .full then "" else s!" [{mode.label}]"
  s!"LF model obligations for {nameString checked.name}{modeText}: {obs.size} obligation(s), \
    {fields} user field(s), {derived} generated method/declaration(s), {params} theorem-local \
      certificate parameter(s), {replay} replay artifact(s), {expanded} metadata expansion(s), \
        {omitted} blocked/omitted obligation(s){abbrevText}"

/-- Compact counts for renderable LF model fields grouped by source role. -/
def lfModelFieldSourceBreakdown (obs : Array LFModelObligation) : String :=
  let count (source : LFModelObligationSource) :=
    countLFModelObligations obs (fun o => o.source == source && o.generatedRole == .field
      && o.renderable)
  let entries := #[
    ("syntax_sort", count .syntaxSort),
    ("judgment", count .judgment),
    ("typed lf_opaque", count .typedOpaque),
    ("temporary admitted-definition", count .admittedOpaque),
    ("side-condition predicate", count .sideConditionPredicate),
    ("rule", count .rule)]
  let shown := entries.filter (fun (_, n) => n != 0)
  if shown.isEmpty then "none" else String.intercalate ", " (shown.toList.map fun (label, n) =>
    s!"{n} {label}")

/-- Size measure used to surface the most dependency-heavy generated LF model fields. -/
def lfModelObligationDependencyWeight (o : LFModelObligation) : Nat :=
  o.paramCount + o.premiseCount + o.sideConditionCount

/-- One-line implementation hint for a user-provided model field. -/
def lfModelFieldImplementationHint (o : LFModelObligation) : String :=
  let generated := nameString ((o.generatedName?).getD o.name)
  let implicitParams := o.params.foldl (init := 0) fun n p => if p.visibility == .implicit then
    n + 1 else n
  let implicitText := if implicitParams == 0 then "" else s!", {implicitParams} implicit"
  let premiseText := if o.premiseCount == 0 then "" else s!", {o.premiseCount} premise/evidence"
  let sideText := if o.sideConditionCount == 0 then "" else
    s!", {o.sideConditionCount} side-condition certificate"
  s!"  {generated}: {o.source.label} {nameString o.name} ({o.paramCount} \
    parameter(s){implicitText}{premiseText}{sideText})"

/-- Model-facing fields whose rendered types mention the selected temporary admission. -/
def lfModelTemporaryAdmissionDependents (defValues : NameMap CheckedLFExpr)
    (obs : Array LFModelObligation) (admissionName : Name) : Array LFModelObligation :=
  let target : NameSet := {admissionName.eraseMacroScopes}
  obs.filter fun o =>
    o.generatedRole == .field && o.renderable && o.name.eraseMacroScopes !=
      admissionName.eraseMacroScopes &&
        (lfModelObligationRenderedFieldDependencies defValues target o).contains
          admissionName.eraseMacroScopes

/-- Warning text for temporary admitted-definition fields, if the interface needs any. -/
def lfModelTemporaryAdmissionWarningStringFromObligations (checked : CheckedSignature)
    (obs : Array LFModelObligation) : Option String := Id.run do
  let temps := obs.filter (·.isTemporaryAdmissionField)
  if temps.isEmpty then
    return none
  let defValues := lfDefinitionValueMap checked
  let mut lines := #[
    s!"generated model interface for {nameString checked.name} includes {temps.size} temporary \
      admitted-definition field(s).",
    "These fields interpret `sorry`-admitted internal definitions because model-facing \
      obligations mention them.",
    "Preferred fix: replace the corresponding internal `sorry`s with checked internal \
      definitions or internal proof terms, then regenerate the model interface.",
    "Filling these Lean fields is a temporary model-development escape hatch.",
    "temporary admitted-definition fields:" ]
  for o in temps.take 12 do
    let deps := lfModelTemporaryAdmissionDependents defValues obs o.name
    let depNames := deps.toList.take 6 |>.map fun d => nameString ((d.generatedName?).getD d.name)
    let depText := if depNames.isEmpty then "<dependency closure>" else
      String.intercalate ", " depNames
    let more := if deps.size > 6 then s!", ... {deps.size - 6} more" else ""
    lines := lines.push s!"  {nameString o.name}: needed by {depText}{more}"
  if temps.size > 12 then
    lines := lines.push s!"  ... {temps.size - 12} more temporary field(s)"
  return some (String.intercalate "\n" lines.toList)

/-- User-facing guide printed before generated LF model-interface source. -/
def lfModelInterfaceGuideString (theoryName structureName : Name) (checked : CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM String :=
      do
  let obs := lfModelObligationsForMode checked mode (lfModelObligations checked admittedNames)
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let derived := obs.filter (fun o => o.generatedRole == .derivedDeclaration && o.renderable)
  let params := obs.filter (fun o => o.generatedRole == .derivedParameter && o.renderable)
  let omitted := obs.filter (fun o => o.generatedRole == .omitted || !o.renderable)
  let heavy := fields.filter (fun o => lfModelObligationDependencyWeight o >= 2)
  let mut lines := #[
    s!"model-interface guide for {nameString theoryName} as {nameString structureName} (generic \
      LF-model backend, {mode.label} mode)",
    s!"user-provided fields: {fields.size} ({lfModelFieldSourceBreakdown obs})",
    s!"generated methods/declarations: {derived.size}; theorem-local certificate parameters: \
      {params.size}; blocked/omitted: {omitted.size}"]
  let abbrevCount := checked.lfSyntaxAbbrevs.size + checked.lfJudgmentAbbrevs.size
  if abbrevCount != 0 then
    lines :=
      lines.push s!"LF abbreviations expanded before fields: {abbrevCount}; they are public \
        notation, not model obligations."
  if let some warning := lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    lines := lines.push s!"WARNING: {warning}"
  if !heavy.isEmpty then
    lines := lines.push "dependency-heavy fields to inspect first:"
    for o in heavy.take 8 do
      lines := lines.push (lfModelFieldImplementationHint o)
  else if !fields.isEmpty then
    lines := lines.push "fields are small; fill them in the order printed by the structure."
  if !omitted.isEmpty then
    lines :=
      lines.push "blocked items have diagnostics in `#print_lf_model_omissions`; they are not \
        required fields."
  if derived.isEmpty then
    lines :=
      lines.push "after filling the structure, no checked LF methods are currently generated."
  else
    lines :=
      lines.push s!"after filling the structure, run `#print_model_transports \
        {nameString theoryName} for {nameString structureName}` and then \
          `generate_model_transports {nameString theoryName} for {nameString structureName}`."
  let templateCmd := if mode == .publicMode then "#print_public_model_template" else
    "#print_model_template"
  lines :=
    lines.push s!"template command: `{templateCmd} {nameString theoryName} as \
      {nameString structureName}`"
  let structuralPrintCmd := if mode == .publicMode then "#print_public_model_structural_equiv"
    else "#print_model_structural_equiv"
  let structuralGenerateCmd := if mode == .publicMode then "generate_public_model_structural_equiv"
    else "generate_model_structural_equiv"
  lines :=
    lines.push s!"optional strict structural equivalence: `{structuralPrintCmd} \
      {nameString theoryName} for {nameString structureName}` or `{structuralGenerateCmd} \
        {nameString theoryName} for {nameString structureName}`"
  pure <| String.intercalate "\n" lines.toList

/-- Human-readable contract for the generic LF model-obligation roles. -/
def lfModelContractString (checked : CheckedSignature) : String :=
  String.intercalate "\n" [
    s!"LF model contract for {nameString checked.name}",
    "generated roles:",
    "  model field: data or operation the user/model instance must provide in the generated \
      structure",
    "  derived declaration: theorem/definition generated over a model from checked LF replay, not \
      a required field",
    "  derived parameter: theorem-local certificate argument supplied when generating a derived \
      declaration",
    "  replay artifact: checked/generated LF replay evidence used as a gate, not a user field",
    "  metadata expansion: checked lf_def expanded during model expression rendering",
    "  omitted: blocked obligation with an actionable diagnostic",
    "source classes:",
    "  syntax_sort/judgment/typed lf_opaque/rule: normally become model fields",
    "  syntax_abbrev/judgment_abbrev: public notation expanded before model obligations, not a \
      model field",
    "  admitted lf_opaque: admissions stay generated declarations unless needed by \
      model-field dependencies, including structural package-shaped admissions",
    "  side-condition predicate: inferred model predicate field used by rule evidence arguments",
    "  theorem side-condition certificate: derived theorem parameter when renderable",
    "  lf_def: expanded metadata, not a field when renderable",
    "  judgment_theorem: derived declaration when replay and certificate inputs are renderable",
    "naming/universe contract:",
    "  generated names are deterministic source names unless a role-specific suffix was already \
      generated upstream",
    "  field names are checked for duplicates and field/derived-declaration collisions",
    "  derived theorem parameter names are checked for duplicates and model-field collisions",
    "  generic LF-model structure fields render unannotated syntax sorts as Lean Type and \
      preserve explicit LF universe levels from LF syntax"]

/-- Whether a generated Lean model field/declaration name is a safe simple identifier. -/
def isSafeGeneratedLFModelName (n : Name) : Bool :=
  match n.eraseMacroScopes with
  | .str .anonymous s => s != "mk" && s != "rec" && s != "noConfusion"
  | _ => false

/-- Check one generated LF model name before it reaches Lean structure elaboration. -/
def checkSafeGeneratedLFModelName (theoryName : Name) (role : String) (sourceName : Name)
    (generatedName : Name) : Except String Unit := do
  unless isSafeGeneratedLFModelName generatedName do
    throw s!"LF model obligations for '{theoryName}' generate invalid {role} name \
      '{generatedName}' from source declaration '{sourceName}'. Generated names must be simple \
      unqualified identifiers and may not be reserved structure names such as 'mk'."

/-- Pure structural validation for a generic LF model-obligation array.

This helper is separate from environment-backed obligation extraction so regression tests can
exercise generated-name collision diagnostics directly. -/
def validateLFModelObligationArray (theoryName : Name) (obs : Array LFModelObligation) :
  Except String Unit := Id.run do
  let mut seenFields : NameSet := {}
  let mut seenDerivedDecls : NameSet := {}
  let mut seenDerivedParams : NameSet := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      match o.generatedName? with
      | none =>
        return .error s!"LF model obligation '{o.name}' is a renderable field but has no \
          generated field name"
      | some n =>
          match checkSafeGeneratedLFModelName theoryName "field" o.name n with
          | .error msg => return .error msg
          | .ok () => pure ()
          if seenFields.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate duplicate field \
              name '{n}'"
          if seenDerivedDecls.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate \
              field/derived-declaration name collision '{n}'"
          if seenDerivedParams.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate model field '{n}' \
              that collides with a derived parameter name"
          seenFields := seenFields.insert n
    if o.generatedRole == .derivedDeclaration && o.renderable then
      match o.generatedName? with
      | none =>
        return .error s!"LF model obligation '{o.name}' is a renderable derived declaration but \
          has no generated declaration name"
      | some n =>
          match checkSafeGeneratedLFModelName theoryName "derived declaration" o.name n with
          | .error msg => return .error msg
          | .ok () => pure ()
          if seenDerivedDecls.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate duplicate derived \
              declaration name '{n}'"
          if seenFields.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate \
              field/derived-declaration name collision '{n}'"
          seenDerivedDecls := seenDerivedDecls.insert n
    if o.generatedRole == .derivedParameter && o.renderable then
      match o.generatedName? with
      | none =>
        return .error s!"LF model obligation '{o.name}' is a renderable derived parameter but has \
          no generated parameter name"
      | some n =>
          match checkSafeGeneratedLFModelName theoryName "derived parameter" o.name n with
          | .error msg => return .error msg
          | .ok () => pure ()
          if seenDerivedParams.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate duplicate derived \
              parameter name '{n}'"
          if seenFields.contains n then
            return .error s!"LF model obligations for '{theoryName}' generate derived parameter \
              '{n}' that collides with a model field name"
          seenDerivedParams := seenDerivedParams.insert n
  return .ok ()

/-- Unemitted generated fields that a field still depends on. -/
def unresolvedLFModelFieldDependencies (defValues : NameMap CheckedLFExpr)
    (fieldSourceNames emitted : NameSet) (o : LFModelObligation) : List Name :=
  (lfModelObligationRenderedFieldDependencies defValues fieldSourceNames o).toList.filter fun n =>
    fieldSourceNames.contains n && n != o.name.eraseMacroScopes && !emitted.contains n

/-- Diagnostic for a dependency cycle among generated model fields. -/
def lfModelFieldDependencyCycleMessage (defValues : NameMap CheckedLFExpr)
    (fieldSourceNames emitted : NameSet) (remaining : Array LFModelObligation) : String :=
  let lines := remaining.toList.take 10 |>.map fun o =>
    let deps := unresolvedLFModelFieldDependencies defValues fieldSourceNames emitted o
    let depText := String.intercalate ", " (deps.map nameString)
    let generated := nameString ((o.generatedName?).getD o.name)
    s!"  {generated} depends on not-yet-generated field(s): {depText}"
  String.intercalate "\n" <|
    ["generated LF model fields have a dependency cycle or an unsatisfied rendered dependency",
     "The model interface backend will not emit malformed Lean structure fields.",
     "Blocked fields:"] ++ lines

/-- Field obligations ordered so each generated structure field appears after generated fields
mentioned by its rendered type, preserving the original order whenever there is no dependency
pressure. -/
def orderLFModelFieldObligations (checked : CheckedSignature) (obs : Array LFModelObligation) :
    Except String (Array LFModelObligation) := do
  let defValues := lfDefinitionValueMap checked
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let nonFields := obs.filter (fun o => !(o.generatedRole == .field && o.renderable))
  let fieldSourceNames : NameSet := fields.foldl (init := {}) fun acc o =>
    acc.insert o.name.eraseMacroScopes
  let mut emitted : NameSet := {}
  let mut remaining := fields
  let mut ordered := #[]
  while !remaining.isEmpty do
    let mut progress := false
    let mut next := #[]
    for o in remaining do
      let deps := unresolvedLFModelFieldDependencies defValues fieldSourceNames emitted o
      if deps.isEmpty then
        ordered := ordered.push o
        emitted := emitted.insert o.name.eraseMacroScopes
        progress := true
      else
        next := next.push o
    if progress then
      remaining := next
    else
      throw <| lfModelFieldDependencyCycleMessage defValues fieldSourceNames emitted remaining
  return ordered ++ nonFields

/-- Validate structural consistency of the generic LF model-obligation IR. -/
def validateLFModelObligations (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : CommandElabM (Array LFModelObligation) := do
  let obs := lfModelObligationsForMode checked mode (lfModelObligations checked admittedNames)
  match validateLFModelObligationArray checked.name obs with
  | .error msg => throwError msg
  | .ok () =>
      match orderLFModelFieldObligations checked obs with
      | .ok obs => pure obs
      | .error msg => throwError msg

/-- Universe parameters used by all renderable model fields in one generated interface mode. -/
def lfModelInterfaceLevelParams (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : CommandElabM (Array Name) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut used : NameSet := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      used := insertNameSet used <|
        lfModelObligationRenderedLevelParams defValues blockingUntyped sidePredicateNames o
  pure (orderedModelLevelParams checked used)

/-- Emit the default warning for temporary admitted-definition model fields, if any. -/
def warnTemporaryAdmissionFieldsIfAny (checked : CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM Unit :=
  do
  let obs ← validateLFModelObligations checked admittedNames mode
  if let some warning := lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    logWarning m!"{warning}"

/-- Generated field-name map induced by renderable field obligations. -/
def lfModelFieldNameMap (obs : Array LFModelObligation) : NameMap Name := Id.run do
  let mut out : NameMap Name := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      if let some generatedName := o.generatedName? then
        out := out.insert o.name.eraseMacroScopes generatedName.eraseMacroScopes
  return out

/-- Generated field name for an LF global, defaulting to the original name when no model field
exists. -/
def lfModelFieldName (fieldNames : NameMap Name) (n : Name) : Name :=
  match fieldNames.find? n with
  | some fieldName => fieldName
  | none => (fieldNames.find? n.eraseMacroScopes).getD n.eraseMacroScopes

/-- Source parameter visibility map induced by LF model obligations. -/
def lfParamVisibilityMapOfObligations (obs : Array LFModelObligation) : LFParamVisibilityMap :=
  Id.run do
  let mut out : LFParamVisibilityMap := {}
  for o in obs do
    if !o.params.isEmpty then
      out := out.insert o.name.eraseMacroScopes (o.params.map (·.visibility))
  return out

/-- Syntax for a checked LF expression in an LF-model structure field, using generated names
from the model-obligation IR and expanding staged LF definitions. -/
partial def lfExprSyntaxInModelWithFields (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (locals : LFLocalSyntaxCtx) (paramVis :
      LFParamVisibilityMap := {}) :
    CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h =>
      match findLFLocalIdent? locals h.name, h.kind, lfDefinitionValue? defValues h.name with
      | some localId, _, _ => pure localId
      | none, .lfDefinition, some value =>
        lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis value
      | none, _, _ => pure <| mkIdent (lfModelFieldName fieldNames h.name)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app ..) => do
      if let some reduced := reduceCheckedLFDefinitionHeadPairApp? defValues
          (lfLocalSyntaxSourceNames locals) e then
        lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis reduced
      else
      let (head, args) := splitCheckedLFExprApp e
      if let some n := checkedLFExprHeadName? head then
        if lfHeadHasImplicitParams paramVis n then
          let head ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis head
          let head ← explicitLeanHeadSyntax head
          let args ← args.mapM (lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis)
          return ← mkTermAppSyntax head args
      match e with
      | .app f a =>
          let f ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis f
          let a ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis a
          `($f $a)
      | _ => throwError "internal error: expected LF application while rendering model expression"
  | .arrow none A B => do
      let A ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let B ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntaxInModelWithFields fieldNames defValues ((x, xId) :: locals) paramVis B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let B ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let xId := freshLFLocalIdent x locals
      let B ← lfExprSyntaxInModelWithFields fieldNames defValues ((x, xId) :: locals) paramVis B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis a
      let b ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis b
      `(⟨$a, $b⟩)
  | e@(.fst value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis reduced
      else
        let value ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis value
        `(($value).1)
  | e@(.snd value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis reduced
      else
        let value ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis value
        `(($value).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let xId := freshLFLocalIdent x locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis lhs
      let rhs ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis rhs
      `($lhs = $rhs)

/-- Syntax for a source LF expression in an LF-model structure field, using generated names
from the model-obligation IR and expanding staged LF definitions. -/
partial def lfObjExprSyntaxInModelWithFields (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (locals : LFLocalSyntaxCtx) (paramVis :
      LFParamVisibilityMap := {}) :
    ObjExpr → CommandElabM (TSyntax `term)
  | .ident n =>
      let n := n.eraseMacroScopes
      match findLFLocalIdent? locals n, lfDefinitionValue? defValues n with
      | some localId, _ => pure localId
      | none, some value => lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis value
      | none, none => pure (mkIdent (lfModelFieldName fieldNames n))
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app ..) => do
      let (head, args) := splitObjExprAppForModel e
      if let some n := objExprHeadName? head then
        if lfHeadHasImplicitParams paramVis n then
          let head ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis head
          let head ← explicitLeanHeadSyntax head
          let args ←
            args.mapM (lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis)
          return ← mkTermAppSyntax head args
      match e with
      | .app f a =>
          let f ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis f
          let a ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis a
          `($f $a)
      | _ => throwError "internal error: expected LF application while rendering model expression"
  | .arrow none A B | .funArrow none A B => do
      let A ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let B ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis B
      `($A → $B)
  | .arrow (some x) A B | .funArrow (some x) A B => do
      let A ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let x := x.eraseMacroScopes
      let xId := freshLFLocalIdent x locals
      let B ← lfObjExprSyntaxInModelWithFields fieldNames defValues ((x, xId) :: locals) paramVis B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let B ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis A
      let x := x.eraseMacroScopes
      let xId := freshLFLocalIdent x locals
      let B ← lfObjExprSyntaxInModelWithFields fieldNames defValues ((x, xId) :: locals) paramVis B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis a
      let b ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis b
      `(⟨$a, $b⟩)
  | .fst e => do
      let e ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis e
      `(($e).1)
  | .snd e => do
      let e ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis e
      `(($e).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if i < xs.size then
          let x := xs[i]!.eraseMacroScopes
          let xId := freshLFLocalIdent x locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis lhs
      let rhs ← lfObjExprSyntaxInModelWithFields fieldNames defValues locals paramVis rhs
      `($lhs = $rhs)

/-- Syntax for a checked LF expression projected from a concrete LF model instance, using
generated names from the model-obligation IR and expanding staged LF definitions. -/
partial def lfExprSyntaxInModelInstanceWithFields (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (modelIdent : Ident) (locals : LFLocalSyntaxCtx)
    (paramVis : LFParamVisibilityMap := {}) : CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h =>
      match findLFLocalIdent? locals h.name with
      | some localId => pure localId
      | none =>
          match h.kind, lfDefinitionValue? defValues h.name with
          | .lfDefinition, some value =>
            lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
              value
          | _, _ => do
              let field := mkIdent (lfModelFieldName fieldNames h.name)
              `($modelIdent.$field:ident)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app ..) => do
      if let some reduced := reduceCheckedLFHeadRedex? defValues
          (lfLocalSyntaxSourceNames locals) e then
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
          reduced
      else
      let (head, args) := splitCheckedLFExprApp e
      if let some n := checkedLFExprHeadName? head then
        if lfHeadHasImplicitParams paramVis n then
          let head ←
            lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
              head
          let head ← explicitLeanHeadSyntax head
          let args ←
            args.mapM (lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals
              paramVis)
          return ← mkTermAppSyntax head args
      match e with
      | .app f a =>
          let f ←
            lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis f
          let a ←
            lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis a
          `($f $a)
      | _ => throwError "internal error: expected LF application while rendering model expression"
  | .arrow none A B => do
      let A ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let B ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let B ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis a
      let b ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis b
      `(⟨$a, $b⟩)
  | e@(.fst value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
          reduced
      else
        let value ←
          lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
            value
        `(($value).1)
  | e@(.snd value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
          reduced
      else
        let value ←
          lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
            value
        `(($value).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let xId := freshLFModelLocalIdent x modelIdent locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis lhs
      let rhs ←
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis rhs
      `($lhs = $rhs)

/-- Syntax for a source LF expression projected from a concrete LF model instance, using
generated names from the model-obligation IR and expanding staged LF definitions. -/
partial def lfObjExprSyntaxInModelInstanceWithFields (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (modelIdent : Ident) (locals : LFLocalSyntaxCtx)
    (paramVis : LFParamVisibilityMap := {}) : ObjExpr → CommandElabM (TSyntax `term)
  | .ident n =>
      let n := n.eraseMacroScopes
      match findLFLocalIdent? locals n, lfDefinitionValue? defValues n with
      | some localId, _ => pure localId
      | none, some value =>
        lfExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis value
      | none, none => do
          let field := mkIdent (lfModelFieldName fieldNames n)
          `($modelIdent.$field:ident)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app ..) => do
      let (head, args) := splitObjExprAppForModel e
      if let some n := objExprHeadName? head then
        if lfHeadHasImplicitParams paramVis n then
          let head ←
            lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals
              paramVis head
          let head ← explicitLeanHeadSyntax head
          let args ←
            args.mapM (lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent
              locals paramVis)
          return ← mkTermAppSyntax head args
      match e with
      | .app f a =>
          let f ←
            lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals
              paramVis f
          let a ←
            lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals
              paramVis a
          `($f $a)
      | _ => throwError "internal error: expected LF application while rendering model expression"
  | .arrow none A B | .funArrow none A B => do
      let A ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let B ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis B
      `($A → $B)
  | .arrow (some x) A B | .funArrow (some x) A B => do
      let A ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let x := x.eraseMacroScopes
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let B ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis A
      let x := x.eraseMacroScopes
      let xId := freshLFModelLocalIdent x modelIdent locals
      let B ← lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis a
      let b ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis b
      `(⟨$a, $b⟩)
  | .fst e => do
      let e ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis e
      `(($e).1)
  | .snd e => do
      let e ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis e
      `(($e).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
        if i < xs.size then
          let x := xs[i]!.eraseMacroScopes
          let xId := freshLFModelLocalIdent x modelIdent locals
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
            body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis lhs
      let rhs ←
        lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis rhs
      `($lhs = $rhs)

/-- Build a dependent function type from checked LF binders using generated model field names. -/
partial def lfTelescopeSyntaxInModelWithFields (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (binders : Array CheckedLFBinding) (result : TSyntax `term)
    (locals : LFLocalSyntaxCtx := []) (i : Nat := 0) (paramVis : LFParamVisibilityMap := {}) :
      CommandElabM (TSyntax `term) := do
  if h : i < binders.size then
    let b := binders[i]
    let ty ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis b.checkedTypeExpr
    let xId := freshLFLocalIdent b.name locals
    let rest ← lfTelescopeSyntaxInModelWithFields fieldNames defValues binders result ((b.name,
      xId) :: locals) (i + 1) paramVis
    let binder ← lfRenderedBinderSyntax { name := xId.getId, typeStx := ty, visibility :=
      b.visibility }
    `($binder:bracketedBinder → $rest)
  else
    pure result

/-- Local terms used while rendering structural-equivalence fields. -/
abbrev LFLocalTermCtx := List (Name × TSyntax `term)

/-- Source LF names bound in a rendering context whose locals are arbitrary Lean terms. -/
def lfLocalTermSourceNames (locals : LFLocalTermCtx) : NameSet :=
  locals.foldl (init := {}) fun names entry => names.insert entry.fst.eraseMacroScopes

/-- Look up a rendered local term by checked LF source name. -/
def findLFLocalTerm? (locals : LFLocalTermCtx) (n : Name) : Option (TSyntax `term) :=
  (locals.find? (fun p => p.fst == n.eraseMacroScopes)).map (·.snd)

/-- Syntax for a checked LF expression projected from a model instance, allowing local variables
that render as arbitrary terms rather than only identifiers. -/
partial def lfExprSyntaxInModelInstanceWithTermLocals (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (modelIdent : Ident) (locals : LFLocalTermCtx)
    (paramVis : LFParamVisibilityMap := {}) : CheckedLFExpr → CommandElabM (TSyntax `term)
  | .ident h =>
      match findLFLocalTerm? locals h.name with
      | some localTerm => pure localTerm
      | none =>
          match h.kind, lfDefinitionValue? defValues h.name with
          | .lfDefinition, some value =>
            lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
              paramVis value
          | _, _ => do
              let field := mkIdent (lfModelFieldName fieldNames h.name)
              `($modelIdent.$field:ident)
  | .sort => `(Type)
  | .univ u => typeSyntaxOfLevel u
  | e@(.app ..) => do
      if let some reduced := reduceCheckedLFHeadRedex? defValues
          (lfLocalTermSourceNames locals) e then
        lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals paramVis
          reduced
      else
      let (head, args) := splitCheckedLFExprApp e
      if let some n := checkedLFExprHeadName? head then
        if lfHeadHasImplicitParams paramVis n then
          let head ←
            lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
              paramVis head
          let head ← explicitLeanHeadSyntax head
          let args ←
            args.mapM (lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent
              locals paramVis)
          return ← mkTermAppSyntax head args
      match e with
      | .app f a => do
          let f ←
            lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
              paramVis f
          let a ←
            lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
              paramVis a
          `($f $a)
      | _ => throwError "internal error: expected LF application while rendering structural \
          equivalence expression"
  | .arrow none A B => do
      let A ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis A
      let B ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis B
      `($A → $B)
  | .arrow (some x) A B => do
      let A ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis A
      let reserved : NameSet := {modelIdent.getId.eraseMacroScopes}
      let xId := freshLFLocalIdent x [] reserved
      let B ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(($xId:ident : $A) → $B)
  | .sigma none A B => do
      let A ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis A
      let B ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis B
      `($A × $B)
  | .sigma (some x) A B => do
      let A ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis A
      let reserved : NameSet := {modelIdent.getId.eraseMacroScopes}
      let xId := freshLFLocalIdent x [] reserved
      let B ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent ((x,
        xId) :: locals) paramVis B
      `(Sigma (fun $xId:ident : $A => $B))
  | .pair a b => do
      let a ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis a
      let b ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis b
      `(⟨$a, $b⟩)
  | e@(.fst value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalTermSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals paramVis
          reduced
      else
        let value ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
          paramVis value
        `(($value).1)
  | e@(.snd value) => do
      let reduced := normalizeCheckedLFExprForModel defValues (lfLocalTermSourceNames locals) e
      if reduced != e then
        lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals paramVis
          reduced
      else
        let value ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
          paramVis value
        `(($value).2)
  | .lam xs body => do
      let rec go (i : Nat) (locals : LFLocalTermCtx) : CommandElabM (TSyntax `term) := do
        if h : i < xs.size then
          let x := xs[i]
          let reserved : NameSet := {modelIdent.getId.eraseMacroScopes}
          let xId := freshLFLocalIdent x [] reserved
          let body ← go (i + 1) ((x, xId) :: locals)
          `(fun $xId:ident => $body)
        else
          lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
            paramVis body
      go 0 locals
  | .jeq lhs rhs => do
      let lhs ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis lhs
      let rhs ← lfExprSyntaxInModelInstanceWithTermLocals fieldNames defValues modelIdent locals
        paramVis rhs
      `($lhs = $rhs)

/-- One binder in a generated structural-equivalence field telescope. A missing type expression
means the model interface rendered the corresponding side-condition input as plain `Type`. -/
structure LFStructuralBinder where
  /-- Source binder name. -/
  name : Name
  /-- Checked source type, if the generated model field retained it. -/
  typeExpr? : Option CheckedLFExpr := none
  /-- Source visibility. -/
  visibility : BinderVisibility := .explicit
  deriving Inhabited, Repr, BEq

/-- Convert a checked LF binder to a structural-equivalence binder. -/
def LFStructuralBinder.ofChecked (b : CheckedLFBinding) : LFStructuralBinder :=
  { name := b.name, typeExpr? := some b.checkedTypeExpr, visibility := b.visibility }

/-- Convert a source-model binder name to the matching target-model binder name. -/
def structuralTargetBinderName (n : Name) : Name :=
  Name.mkSimple s!"{flatNameString n}_target"

/-- Convert a source-model binder name to its generated relation-witness binder name. -/
def structuralRelationBinderName (n : Name) : Name :=
  Name.mkSimple s!"{flatNameString n}_rel"

/-- Add generated-field suffixes while avoiding collisions with earlier generated names. -/
def freshStructuralFieldName (used : NameSet) (base : Name) (suffix : String) : Name × NameSet :=
  let baseComponent := flatNameString base
  let rec go : Nat → Name
    | 0 => Name.mkSimple s!"{baseComponent}{suffix}"
    | n + 1 => Name.mkSimple s!"{baseComponent}{suffix}{n + 1}"
  let rec pick : Nat → Nat → Name
    | 0, n => go n
    | fuel + 1, n =>
        let candidate := go n
        if !used.contains candidate.eraseMacroScopes then
          candidate
        else
          pick fuel (n + 1)
  let candidate := pick (used.size + 64) 0
  (candidate, used.insert candidate.eraseMacroScopes)

/-- Pick the nested structural-equivalence structure name, avoiding generated model-namespace
constants such as model projections and derived declarations. -/
def lfStructuralEquivStructureName (obs : Array LFModelObligation) : Name := Id.run do
  let mut used : NameSet := {}
  for o in obs do
    if let some generated := o.generatedName? then
      used := used.insert generated.eraseMacroScopes
  let base := `StructuralEquiv
  let rec pick : Nat → Nat → Name
    | 0, n => Name.mkSimple s!"StructuralEquiv{n}"
    | fuel + 1, n =>
        let candidate := Name.mkSimple s!"StructuralEquiv{n}"
        if used.contains candidate.eraseMacroScopes then pick fuel (n + 1) else candidate
  return if used.contains base then pick (used.size + 64) 1 else base

/-- Collect explicit function-domain binders from a checked LF type expression. -/
partial def collectLFStructuralArrowBinders (defValues : NameMap CheckedLFExpr) (owner : Name)
    (start : Nat) : CheckedLFExpr → Array LFStructuralBinder × CheckedLFExpr
  | .ident h =>
      match h.kind, lfDefinitionValue? defValues h.name with
      | .lfDefinition, some value => collectLFStructuralArrowBinders defValues owner start value
      | _, _ => (#[], .ident h)
  | .arrow x? A B =>
      let name := x?.getD (Name.mkSimple s!"{flatNameString owner}_arg{start}")
      let (rest, result) := collectLFStructuralArrowBinders defValues owner (start + 1) B
      (#[{ name := name.eraseMacroScopes, typeExpr? := some A }] ++ rest, result)
  | e => (#[], e)

/-- Whether an LF expression is an object universe after expanding a bare LF definition head. -/
partial def lfStructuralResultIsType (defValues : NameMap CheckedLFExpr) : CheckedLFExpr → Bool
  | .sort | .univ _ => true
  | .ident h =>
      match h.kind, lfDefinitionValue? defValues h.name with
      | .lfDefinition, some value => lfStructuralResultIsType defValues value
      | _, _ => false
  | _ => false

/-- Binders and final result type represented by one generated model-field obligation. -/
def lfStructuralFieldBindersAndResult? (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) (o : LFModelObligation) :
      Option (Array LFStructuralBinder × CheckedLFExpr) :=
  match o.source with
  | .syntaxSort | .judgment | .sideConditionPredicate =>
      some (o.params.map LFStructuralBinder.ofChecked, o.typeExpr?.getD .sort)
  | .typedOpaque | .admittedOpaque => do
      let typeExpr ← o.typeExpr?
      let (arrowBinders, result) :=
        collectLFStructuralArrowBinders defValues o.name o.params.size typeExpr
      some (o.params.map LFStructuralBinder.ofChecked ++ arrowBinders, result)
  | .rule => do
      let conclusionExpr ← o.typeExpr?
      let mut binders := o.params.map LFStructuralBinder.ofChecked
      for p in o.premises do
        binders := binders.push { name := p.name, typeExpr? := some p.checkedJudgmentExpr }
      for e in o.paramEvidences do
        binders := binders.push { name := e.name, typeExpr? := some e.checkedJudgmentExpr }
      for sc in o.sideConditions do
        if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames sc.checkedInput then
          binders := binders.push { name := sc.name, typeExpr? := some sc.checkedInput }
        else
          binders := binders.push { name := sc.name, typeExpr? := none }
      some (binders, conclusionExpr)
  | .theoremSideConditionCertificate | .untypedOpaque | .objectDefinition | .judgmentTheorem =>
      none

/-- Whether a generated model-field obligation is interpreted as a type family in structural
equivalence generation. -/
def lfStructuralObligationIsTypeFamily (defValues : NameMap CheckedLFExpr)
    (blockingUntyped sidePredicateNames : NameSet) (o : LFModelObligation) : Bool :=
  match lfStructuralFieldBindersAndResult? defValues blockingUntyped sidePredicateNames o with
  | some (_, result) => lfStructuralResultIsType defValues result
  | none => false

/-- Generated field names used by the structural-equivalence structure. -/
structure LFStructuralEquivNameMaps where
  /-- Source field to generated type-family equivalence field. -/
  equivNames : NameMap Name := {}
  /-- Source field to generated operation/rule preservation field. -/
  preserveNames : NameMap Name := {}
  deriving Inhabited, Repr

/-- Compute generated structural-equivalence field names from ordered model obligations. -/
def lfStructuralEquivNameMaps (checked : CheckedSignature) (obs : Array LFModelObligation) :
    LFStructuralEquivNameMaps := Id.run do
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut used : NameSet := {lfStructuralEquivStructureName obs}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      if let some generated := o.generatedName? then
        used := used.insert generated.eraseMacroScopes
  let mut equivNames : NameMap Name := {}
  let mut preserveNames : NameMap Name := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      if let some generated := o.generatedName? then
        if lfStructuralObligationIsTypeFamily defValues blockingUntyped sidePredicateNames o then
          let (name, nextUsed) := freshStructuralFieldName used generated "_equiv"
          used := nextUsed
          equivNames := equivNames.insert o.name.eraseMacroScopes name
        else if (lfStructuralFieldBindersAndResult? defValues blockingUntyped
            sidePredicateNames o).isSome then
          let (name, nextUsed) := freshStructuralFieldName used generated "_preserve"
          used := nextUsed
          preserveNames := preserveNames.insert o.name.eraseMacroScopes name
  return { equivNames, preserveNames }

/-- Values of a `NameMap Name` as a set of reserved generated names. -/
def nameMapValueNameSet (m : NameMap Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (_, n) in m.toList do
    out := out.insert n.eraseMacroScopes
  return out

/-- Apply a model projection to generated term arguments. -/
def structuralModelFieldApp (modelIdent : Ident) (fieldName : Name)
    (args : Array (TSyntax `term)) (renderExplicit : Bool := false) :
      CommandElabM (TSyntax `term) := do
  let fieldId := mkIdent fieldName
  let head ← `(term| $modelIdent.$fieldId:ident)
  let head ← if renderExplicit then explicitLeanHeadSyntax head else pure head
  mkTermAppSyntax head args

/-- Split an LF application into a global head and argument spine after expanding bare LF
definition heads. -/
partial def structuralHeadArgs? (defValues : NameMap CheckedLFExpr) :
    CheckedLFExpr → Option (CheckedLFHead × Array CheckedLFExpr)
  | .ident h =>
      match h.kind, lfDefinitionValue? defValues h.name with
      | .lfDefinition, some value => structuralHeadArgs? defValues value
      | _, _ => some (h, #[])
  | .app f a => do
      let (h, args) ← structuralHeadArgs? defValues f
      some (h, args.push a)
  | _ => none

/-- Rendering context for one generated structural-equivalence field type. -/
structure LFStructuralRenderCtx where
  /-- Generated type-family equivalence field names. -/
  equivNames : NameMap Name := {}
  /-- Generated operation/rule preservation field names. -/
  preserveNames : NameMap Name := {}
  /-- Binders and result type for each generated model field. -/
  fieldBinders : NameMap (Array LFStructuralBinder × CheckedLFExpr) := {}
  /-- Model field-name map. -/
  fieldNames : NameMap Name := {}
  /-- Expanded LF definitions. -/
  defValues : NameMap CheckedLFExpr := {}
  /-- Source parameter visibility map. -/
  paramVis : LFParamVisibilityMap := {}
  /-- Left/source model variable. -/
  sourceModel : Ident := mkIdent `M
  /-- Right/target model variable. -/
  targetModel : Ident := mkIdent `N
  /-- Source-side local terms. -/
  sourceLocals : LFLocalTermCtx := []
  /-- Target-side local terms. -/
  targetLocals : LFLocalTermCtx := []
  /-- Relation witnesses for local terms. -/
  relationLocals : LFLocalTermCtx := []

/-- Parameter types for a field head in structural-equivalence generation. -/
def structuralHeadParamTypes (ctx : LFStructuralRenderCtx) (headName : Name) :
    Array LFStructuralBinder :=
  match ctx.fieldBinders.find? headName.eraseMacroScopes with
  | some (binders, _) => binders
  | none => #[]

/-- Render an LF expression over the source model in a structural-equivalence field. -/
def structuralSourceExprSyntax (ctx : LFStructuralRenderCtx) (e : CheckedLFExpr) :
    CommandElabM (TSyntax `term) :=
  lfExprSyntaxInModelInstanceWithTermLocals ctx.fieldNames ctx.defValues ctx.sourceModel
    ctx.sourceLocals ctx.paramVis e

/-- Render an LF expression over the target model in a structural-equivalence field. -/
def structuralTargetExprSyntax (ctx : LFStructuralRenderCtx) (e : CheckedLFExpr) :
    CommandElabM (TSyntax `term) :=
  lfExprSyntaxInModelInstanceWithTermLocals ctx.fieldNames ctx.defValues ctx.targetModel
    ctx.targetLocals ctx.paramVis e

mutual

/-- Term for the generated equivalence between the source and target interpretations of a type
expression, when the expression is headed by a generated type-family field. -/
partial def structuralTypeEquivTerm? (ctx : LFStructuralRenderCtx) (typeExpr : CheckedLFExpr) :
    CommandElabM (Option (TSyntax `term)) := do
  let some (head, args) := structuralHeadArgs? ctx.defValues typeExpr
    | return none
  let some equivName := ctx.equivNames.find? head.name.eraseMacroScopes
    | match ctx.fieldBinders.find? head.name.eraseMacroScopes with
      | some (_, result) =>
          if lfStructuralResultIsType ctx.defValues result then
            throwError "structural equivalence for type-family dependency '{head.name}' was not \
              generated before it was needed"
          else
            return none
      | none => return none
  let mut appArgs : Array (TSyntax `term) := #[]
  let paramTypes := structuralHeadParamTypes ctx head.name
  for h : i in [:args.size] do
    let arg := args[i]
    appArgs := appArgs.push (← structuralSourceExprSyntax ctx arg)
    if let some paramBinder := paramTypes[i]? then
      if let some paramTy := paramBinder.typeExpr? then
        if (← structuralTypeEquivTerm? ctx paramTy).isSome then
          appArgs := appArgs.push (← structuralTargetExprSyntax ctx arg)
          match ← structuralTermRelationTerm? ctx paramTy arg with
          | some rel => appArgs := appArgs.push rel
          | none =>
              throwError "unsupported dependent relation argument for parameter {i} of \
                '{head.name}'"
  let headTerm : TSyntax `term := mkIdent equivName
  let headTerm ← if lfHeadHasImplicitParams ctx.paramVis head.name then
      explicitLeanHeadSyntax headTerm
    else
      pure headTerm
  some <$> mkTermAppSyntax headTerm appArgs

/-- Relation witness between the mapped source interpretation of a term and its target-model
interpretation at a specified LF type. -/
partial def structuralTermRelationTerm? (ctx : LFStructuralRenderCtx) (typeExpr termExpr :
    CheckedLFExpr) : CommandElabM (Option (TSyntax `term)) := do
  match termExpr with
  | .ident h =>
      if h.kind == .local then
        return findLFLocalTerm? ctx.relationLocals h.name
      else if h.kind == .lfDefinition then
        match lfDefinitionValue? ctx.defValues h.name with
        | some value => return ← structuralTermRelationTerm? ctx typeExpr value
        | none => pure ()
      else
        pure ()
  | _ => pure ()
  let some (head, args) := structuralHeadArgs? ctx.defValues termExpr
    | return none
  let some preserveName := ctx.preserveNames.find? head.name.eraseMacroScopes
    | return none
  let paramTypes := structuralHeadParamTypes ctx head.name
  let mut appArgs : Array (TSyntax `term) := #[]
  for h : i in [:args.size] do
    let arg := args[i]
    appArgs := appArgs.push (← structuralSourceExprSyntax ctx arg)
    if let some paramBinder := paramTypes[i]? then
      if let some paramTy := paramBinder.typeExpr? then
        if (← structuralTypeEquivTerm? ctx paramTy).isSome then
          appArgs := appArgs.push (← structuralTargetExprSyntax ctx arg)
          match ← structuralTermRelationTerm? ctx paramTy arg with
          | some rel => appArgs := appArgs.push rel
          | none =>
              throwError "unsupported dependent relation argument for term parameter {i} of \
                '{head.name}'"
  let preserveTerm : TSyntax `term := mkIdent preserveName
  let renderExplicit := paramTypes.any (fun b => b.visibility == .implicit)
  let preserveTerm ←
    if renderExplicit then explicitLeanHeadSyntax preserveTerm else pure preserveTerm
  some <$> mkTermAppSyntax preserveTerm appArgs

end

/-- Syntax for the small equivalence type used by generated structural-equivalence fields. -/
def structuralTypeEquivTypeSyntax (source target : TSyntax `term) :
    CommandElabM (TSyntax `term) :=
  mkTermAppSyntax (mkIdent ``InternalLean.TypeEquiv) #[source, target]

/-- Syntax for heterogeneous equality in generated preservation clauses. -/
def structuralHEqSyntax (lhs rhs : TSyntax `term) : CommandElabM (TSyntax `term) :=
  mkTermAppSyntax (mkIdent ``HEq) #[lhs, rhs]

/-- Whether an LF expression mentions a generated model field in structural-equivalence
rendering.  If such a type has no generated equivalence of its own, sharing one source-side
binder on the target side is unsound and usually ill-typed. -/
partial def structuralExprMentionsGeneratedField (ctx : LFStructuralRenderCtx) :
    CheckedLFExpr → Bool
  | .ident h =>
      if h.kind == .local then
        false
      else
        match h.kind, lfDefinitionValue? ctx.defValues h.name with
        | .lfDefinition, some value => structuralExprMentionsGeneratedField ctx value
        | _, _ => ctx.fieldBinders.contains h.name.eraseMacroScopes
  | .sort | .univ _ => false
  | .app f a => structuralExprMentionsGeneratedField ctx f ||
      structuralExprMentionsGeneratedField ctx a
  | .arrow _ A B | .sigma _ A B => structuralExprMentionsGeneratedField ctx A ||
      structuralExprMentionsGeneratedField ctx B
  | .pair a b => structuralExprMentionsGeneratedField ctx a ||
      structuralExprMentionsGeneratedField ctx b
  | .fst e | .snd e => structuralExprMentionsGeneratedField ctx e
  | .lam _ body => structuralExprMentionsGeneratedField ctx body
  | .jeq lhs rhs => structuralExprMentionsGeneratedField ctx lhs ||
      structuralExprMentionsGeneratedField ctx rhs

/-- Render the left/source side of a structural binder. -/
def structuralBinderSourceType (ctx : LFStructuralRenderCtx) (b : LFStructuralBinder) :
    CommandElabM (TSyntax `term) :=
  match b.typeExpr? with
  | some typeExpr => structuralSourceExprSyntax ctx typeExpr
  | none => `(Type)

/-- Render the right/target side of a structural binder. -/
def structuralBinderTargetType (ctx : LFStructuralRenderCtx) (b : LFStructuralBinder) :
    CommandElabM (TSyntax `term) :=
  match b.typeExpr? with
  | some typeExpr => structuralTargetExprSyntax ctx typeExpr
  | none => `(Type)

/-- Extend a structural-equivalence telescope with one source binder and, when the binder type has
a generated equivalence, a target binder plus a heterogeneous relation witness. -/
def pushStructuralBinder (ctx : LFStructuralRenderCtx) (rendered : Array LFRenderedBinder)
    (sourceArgs targetArgs : Array (TSyntax `term)) (b : LFStructuralBinder) :
    CommandElabM (LFStructuralRenderCtx × Array LFRenderedBinder × Array (TSyntax `term) ×
      Array (TSyntax `term)) := do
  let sourceTy ← structuralBinderSourceType ctx b
  let usedNames : NameSet :=
    rendered.foldl (init := {}) fun acc b => acc.insert b.name.eraseMacroScopes
  let structuralFieldNames := nameMapValueNameSet ctx.equivNames ++
    nameMapValueNameSet ctx.preserveNames
  let reserved :=
    ((usedNames ++ structuralFieldNames).insert ctx.sourceModel.getId.eraseMacroScopes).insert
      ctx.targetModel.getId.eraseMacroScopes
  let sourceId := freshLFLocalIdent b.name [] reserved
  let sourceTerm : TSyntax `term := sourceId
  let rendered := rendered.push { name := sourceId.getId, typeStx := sourceTy, visibility :=
    b.visibility }
  let sourceArgs := sourceArgs.push sourceTerm
  let ctxWithSource := { ctx with sourceLocals := (b.name.eraseMacroScopes, sourceTerm) ::
    ctx.sourceLocals }
  match b.typeExpr? with
  | some typeExpr =>
      match ← structuralTypeEquivTerm? ctx typeExpr with
      | some equivTerm =>
          let targetTy ← structuralBinderTargetType ctxWithSource b
          let reserved := reserved.insert sourceId.getId.eraseMacroScopes
          let targetId := freshLFLocalIdent (structuralTargetBinderName b.name) [] reserved
          let targetTerm : TSyntax `term := targetId
          let rendered := rendered.push { name := targetId.getId, typeStx := targetTy, visibility :=
            b.visibility }
          let relLhs ← mkTermAppSyntax equivTerm #[sourceTerm]
          let relTy ← structuralHEqSyntax relLhs targetTerm
          let reserved := reserved.insert targetId.getId.eraseMacroScopes
          let relId := freshLFLocalIdent (structuralRelationBinderName b.name) [] reserved
          let rendered := rendered.push { name := relId.getId, typeStx := relTy }
          let relTerm : TSyntax `term := relId
          let ctx := { ctxWithSource with
            targetLocals := (b.name.eraseMacroScopes, targetTerm) :: ctx.targetLocals
            relationLocals := (b.name.eraseMacroScopes, relTerm) :: ctx.relationLocals }
          pure (ctx, rendered, sourceArgs, targetArgs.push targetTerm)
      | none =>
          if structuralExprMentionsGeneratedField ctx typeExpr then
            throwError "unsupported structural-equivalence binder type for '{b.name}'; the type \
              mentions generated model fields but has no generated equivalence"
          let ctx := { ctxWithSource with targetLocals := (b.name.eraseMacroScopes,
            sourceTerm) :: ctx.targetLocals }
          pure (ctx, rendered, sourceArgs, targetArgs.push sourceTerm)
  | none =>
      let ctx := { ctxWithSource with targetLocals := (b.name.eraseMacroScopes, sourceTerm) ::
        ctx.targetLocals }
      pure (ctx, rendered, sourceArgs, targetArgs.push sourceTerm)

/-- Render the relational telescope for a structural-equivalence field. -/
def structuralBinderTelescope (ctx : LFStructuralRenderCtx)
    (binders : Array LFStructuralBinder) : CommandElabM (LFStructuralRenderCtx ×
      Array LFRenderedBinder × Array (TSyntax `term) × Array (TSyntax `term)) := do
  let mut ctx := ctx
  let mut rendered : Array LFRenderedBinder := #[]
  let mut sourceArgs : Array (TSyntax `term) := #[]
  let mut targetArgs : Array (TSyntax `term) := #[]
  for b in binders do
    let (nextCtx, nextRendered, nextSourceArgs, nextTargetArgs) ←
      pushStructuralBinder ctx rendered sourceArgs targetArgs b
    ctx := nextCtx
    rendered := nextRendered
    sourceArgs := nextSourceArgs
    targetArgs := nextTargetArgs
  pure (ctx, rendered, sourceArgs, targetArgs)

/-- Syntax for one generated structural-equivalence field. -/
def structuralEquivFieldSyntax (name : Name) (typeStx : TSyntax `term) :
    CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let fieldId := mkIdent name
  `(Lean.Parser.Command.structSimpleBinder|
    /-- Generated strict structural-equivalence field. -/
    $fieldId:ident : $typeStx)

/-- Syntax for the type-family equivalence clause attached to one model field. -/
def structuralTypeFamilyFieldSyntax (ctx : LFStructuralRenderCtx) (sourceName fieldName
    equivName : Name) (binders : Array LFStructuralBinder) :
      CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let (ctx, rendered, sourceArgs, targetArgs) ← structuralBinderTelescope ctx binders
  let renderExplicit := lfHeadHasImplicitParams ctx.paramVis sourceName
  let sourceField ← structuralModelFieldApp ctx.sourceModel fieldName sourceArgs renderExplicit
  let targetField ← structuralModelFieldApp ctx.targetModel fieldName targetArgs renderExplicit
  let result ← structuralTypeEquivTypeSyntax sourceField targetField
  let ty ← lfRenderedTelescopeSyntax rendered result
  structuralEquivFieldSyntax equivName ty

/-- Syntax for the operation/rule preservation clause attached to one model field. -/
def structuralPreservationFieldSyntax (ctx : LFStructuralRenderCtx) (sourceName fieldName
    preserveName : Name) (binders : Array LFStructuralBinder) (resultExpr : CheckedLFExpr) :
      CommandElabM (TSyntax `Lean.Parser.Command.structSimpleBinder) := do
  let (ctx, rendered, sourceArgs, targetArgs) ← structuralBinderTelescope ctx binders
  let renderExplicit := lfHeadHasImplicitParams ctx.paramVis sourceName
  let sourceField ← structuralModelFieldApp ctx.sourceModel fieldName sourceArgs renderExplicit
  let targetField ← structuralModelFieldApp ctx.targetModel fieldName targetArgs renderExplicit
  let lhs ←
    match ← structuralTypeEquivTerm? ctx resultExpr with
    | some equivTerm => `($equivTerm $sourceField)
    | none => pure sourceField
  let result ← structuralHEqSyntax lhs targetField
  let ty ← lfRenderedTelescopeSyntax rendered result
  structuralEquivFieldSyntax preserveName ty

/-- Extract a compact message from a structural-equivalence generation exception. -/
def lfStructuralExceptionMessageData : Exception → MessageData
  | .error _ msg => msg
  | .internal _ _ => m!"internal exception"

/-- Field syntaxes for the generated strict structural-equivalence structure. -/
def lfModelStructuralEquivFieldSyntaxes (checked : CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fieldObs := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let fieldNames := lfModelFieldNameMap obs
  let defValues := lfDefinitionValueMap checked
  let paramVis := lfParamVisibilityMapOfObligations obs
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let nameMaps := lfStructuralEquivNameMaps checked obs
  let mut fieldBinders : NameMap (Array LFStructuralBinder × CheckedLFExpr) := {}
  for o in fieldObs do
    if let some data := lfStructuralFieldBindersAndResult? defValues blockingUntyped
        sidePredicateNames o then
      fieldBinders := fieldBinders.insert o.name.eraseMacroScopes data
  let mut activeCtx : LFStructuralRenderCtx := {
    fieldBinders := fieldBinders
    fieldNames := fieldNames
    defValues := defValues
    paramVis := paramVis
    sourceModel := mkIdent `M
    targetModel := mkIdent `N }
  let mut fields := #[]
  let mut skipped : Array MessageData := #[]
  for o in fieldObs do
    if let some fieldName := o.generatedName? then
      if let some (binders, resultExpr) := fieldBinders.find? o.name.eraseMacroScopes then
        if let some equivName := nameMaps.equivNames.find? o.name.eraseMacroScopes then
          try
            let field ← structuralTypeFamilyFieldSyntax activeCtx o.name fieldName equivName binders
            fields := fields.push field
            let equivNames := activeCtx.equivNames.insert o.name.eraseMacroScopes equivName
            activeCtx := { activeCtx with equivNames := equivNames }
          catch ex =>
            skipped := skipped.push m!"{fieldName}: {lfStructuralExceptionMessageData ex}"
        else if let some preserveName := nameMaps.preserveNames.find? o.name.eraseMacroScopes then
          try
            let field ← structuralPreservationFieldSyntax activeCtx o.name fieldName preserveName
              binders resultExpr
            fields := fields.push field
            let preserveNames := activeCtx.preserveNames.insert o.name.eraseMacroScopes preserveName
            activeCtx := { activeCtx with preserveNames := preserveNames }
          catch ex =>
            skipped := skipped.push m!"{fieldName}: {lfStructuralExceptionMessageData ex}"
  unless skipped.isEmpty do
    let shown := skipped.toList.take 10
    let more := if skipped.size > 10 then m!"\n  ... and {skipped.size - 10} more" else m!""
    logWarning m!"structural-equivalence generation for {checked.name} skipped {skipped.size} \
      field(s) whose dependent preservation clauses are not supported by the generic renderer:\n  \
      {MessageData.joinSep shown m!"\n  "}{more}"
  pure fields

/-- Syntax for the generated strict structural-equivalence structure. -/
def lfModelStructuralEquivCommandSyntax (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM Syntax :=
      do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields ← lfModelStructuralEquivFieldSyntaxes checked admittedNames mode
  let equivId := mkIdent (lfStructuralEquivStructureName obs)
  let modelId := mkIdent structureName
  let M := mkIdent `M
  let N := mkIdent `N
  let levelParams ← lfModelInterfaceLevelParams checked admittedNames mode
  let levelIds := levelParams.map (mkIdent ·.eraseMacroScopes)
  let cmd ←
    if levelIds.isEmpty then
      `(command| /-- Strict structural equivalence between generated LF model instances. -/
        structure $equivId:ident ($M:ident $N:ident : $modelId:ident) where
          $[$fields:structSimpleBinder]*)
    else
      `(command| /-- Strict structural equivalence between generated LF model instances. -/
        structure $equivId:ident.{$[$levelIds:ident],*}
            ($M:ident $N:ident : $modelId:ident.{$[$levelIds:ident],*}) where
          $[$fields:structSimpleBinder]*)
  let autoImplicitOpt := mkIdent `autoImplicit
  let wrapped ← `(command| set_option $autoImplicitOpt:ident false in $cmd:command)
  pure wrapped.raw

/-- Source-doc role usually associated with an LF model obligation. -/
def sourceDocRoleForLFModelObligation? (o : LFModelObligation) : Option SourceDocRole :=
  match o.source with
  | .syntaxSort => some .syntaxSort
  | .judgment => some .judgment
  | .typedOpaque | .admittedOpaque | .untypedOpaque | .sideConditionPredicate => some .lfOpaque
  | .rule => some .rule
  | .objectDefinition => some .lfObjectDef
  | .judgmentTheorem => some .lfJudgmentTheorem
  | .theoremSideConditionCertificate => none

/-- Source documentation for a model obligation, falling back across roles when generated artifacts
rename it. -/
def sourceDocForLFModelObligation? (theoryName : Name) (o : LFModelObligation) :
  CommandElabM (Option String) := do
  if let some role := sourceDocRoleForLFModelObligation? o then
    if let some doc ← liftCoreM <| findSourceDoc? theoryName role o.name then
      return some doc
  if let some generated := o.generatedName? then
    if let some doc ← liftCoreM <| findAnySourceDocForName? theoryName generated then
      return some doc
  liftCoreM <| findAnySourceDocForName? theoryName o.name

/-- Compact pure rendering of a checked LF expression for comments/docstrings. -/
partial def checkedLFExprSummaryString : CheckedLFExpr → String
  | .ident h => nameString h.name
  | .sort => "Type"
  | .univ u => s!"Type {u}"
  | .app f a => s!"({checkedLFExprSummaryString f} {checkedLFExprSummaryString a})"
  | .arrow none A B => s!"({checkedLFExprSummaryString A} → {checkedLFExprSummaryString B})"
  | .arrow (some x) A B =>
    s!"(({nameString x} : {checkedLFExprSummaryString A}) → {checkedLFExprSummaryString B})"
  | .sigma none A B => s!"({checkedLFExprSummaryString A} × {checkedLFExprSummaryString B})"
  | .sigma (some x) A B =>
    s!"(Sigma (fun {nameString x} : {checkedLFExprSummaryString A} => " ++
      s!"{checkedLFExprSummaryString B}))"
  | .pair a b => s!"⟨{checkedLFExprSummaryString a}, {checkedLFExprSummaryString b}⟩"
  | .fst e => s!"({checkedLFExprSummaryString e}.1)"
  | .snd e => s!"({checkedLFExprSummaryString e}.2)"
  | .lam xs body =>
    s!"(fun {String.intercalate " " (xs.toList.map nameString)} => \
      {checkedLFExprSummaryString body})"
  | .jeq lhs rhs => s!"({checkedLFExprSummaryString lhs} ≡ {checkedLFExprSummaryString rhs})"

/-- Generated hover docstring for one LF-model field projection. -/
def lfModelFieldDocString (theoryName structureName : Name) (o : LFModelObligation) :
  CommandElabM String := do
  let sourceDoc? ← sourceDocForLFModelObligation? theoryName o
  let generated := (o.generatedName?).getD o.name
  let params := if o.paramCount == 0 then "none" else toString o.paramCount
  let implicitParams := o.params.foldl (init := 0) (fun n p => if p.visibility == .implicit then
    n + 1 else n)
  let implicitText := if implicitParams == 0 then "none" else toString implicitParams
  let premises := if o.premiseCount == 0 then "none" else toString o.premiseCount
  let sides := if o.sideConditionCount == 0 then "none" else toString o.sideConditionCount
  let sourceSummary := match o.typeExpr? with
    | some e => checkedLFExprSummaryString e
    | none => match o.sourceObjExpr? with
      | some e => toString e
      | none => "not available"
  let sourceDocLines :=
    match sourceDoc? with
    | some doc => ["", "Source documentation:", trimCapturedDoc doc]
    | none => ["",
      "Source documentation: missing; run `#lint_type_theory_docs` on the source theory."]
  let temporaryAdmissionLines :=
    if o.isTemporaryAdmissionField then
      ["",
       "TEMPORARY admitted-definition field:",
       "This field interprets a `sorry`-admitted internal definition because later model \
        obligations mention it.",
       "Preferred fix: replace the internal `sorry` with a checked internal definition or \
        internal proof term, then regenerate the model interface."]
    else
      []
  pure <| String.intercalate "\n" <|
    [ s!"LF model field \
      `{theoryName.eraseMacroScopes}.{structureName.eraseMacroScopes}.\
      {generated.eraseMacroScopes}`.",
      s!"Source declaration: {o.source.label} {o.name.eraseMacroScopes}.",
      s!"Generated role: {o.generatedRole.label}.",
      s!"Obligation status: {o.statusLabel}.",
      s!"Parameters: {params}; implicit parameters rendered as Lean implicit binders: \
        {implicitText}; premises: {premises}; side conditions: {sides}.",
      s!"Source type/statement summary: {sourceSummary}.",
      s!"Template stub: `{generated.eraseMacroScopes} := by exact ?{generated.eraseMacroScopes}` \
        inside a model instance.",
      "Generated names are deterministic source names unless collision validation reports \
        otherwise.",
      "This field is part of a generated model interface; checked LF/profile artifacts remain the \
        trust boundary." ] ++ temporaryAdmissionLines ++ sourceDocLines

/-- Maximum number of generated LF-model fields per generated structure chunk.

Large dependent structure telescopes scale poorly in Lean.  Chunking with `extends` keeps the
public interface and dot notation while giving Lean several smaller telescopes to elaborate. -/
def lfModelStructureChunkSize : Nat := 75

/-- Maximum field count for generated section-run chunks.

Sectioned interfaces already split the global field telescope at user-facing section boundaries.
Using a slightly larger per-section chunk size avoids long chains of tiny `extends` structures
for large theories while keeping each section-run telescope below the monolithic-structure
slow path that motivated flat-interface chunking. -/
def lfModelSectionStructureChunkSize : Nat := 150

/-- Add a suffix to the final component of a generated structure name. -/
def nameWithLastComponentSuffix (n : Name) (suffix : String) : Name :=
  match n.eraseMacroScopes with
  | .anonymous => .str .anonymous s!"generated{suffix}"
  | .str p s => .str p s!"{s}{suffix}"
  | .num p k => .str p s!"_{k}{suffix}"

/-- Internal chunk structure name for a public generated LF-model interface. -/
def lfModelStructureChunkName (structureName : Name) (i : Nat) : Name :=
  nameWithLastComponentSuffix structureName s!"_chunk{i}"

/-- Map generated LF-model field names to the structure that owns their Lean projection. -/
def lfModelStructureFieldOwnerMap (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (NameMap Name) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let chunkSize := if lfModelStructureChunkSize == 0 then fields.size else lfModelStructureChunkSize
  let chunkCount := if fields.isEmpty then 1 else (fields.size + chunkSize - 1) / chunkSize
  let mut out : NameMap Name := {}
  for h : i in [:fields.size] do
    let o := fields[i]
    if let some fieldName := o.generatedName? then
      let chunkIndex := if chunkSize == 0 then 0 else i / chunkSize
      let owner := if chunkCount <= 1 || chunkIndex + 1 == chunkCount then structureName else
        lfModelStructureChunkName structureName chunkIndex
      out := out.insert fieldName owner
  pure out

/-- Last string component of a generated Lean name, if any. -/
def nameLastStringComponent? : Name → Option String
  | .anonymous => none
  | .str _ s => some s
  | .num p _ => nameLastStringComponent? p

/-- Exclude generated model-interface namespaces from Lean's library-suggestion premise scan.

The declarations generated below are implementation artifacts and can have very large dependent
types.  Lean's library-suggestion symbol-frequency extension scans theorem signatures at module
export; denying these generated name components keeps module writing from spending heartbeats on
non-user premise candidates. -/
def addLFModelInterfaceLibrarySuggestionDenyList (structureName : Name) (chunkCount : Nat) :
  CommandElabM Unit := do
  let addComponent (n : Name) : CommandElabM Unit := do
    if let some component := nameLastStringComponent? n.eraseMacroScopes then
      modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env component
  addComponent structureName
  if chunkCount > 1 then
    for i in [:chunkCount - 1] do
      addComponent (lfModelStructureChunkName structureName i)

/-- Exclude arbitrary generated model-interface structure names from library-suggestion scans. -/
def addLFModelInterfaceNamesLibrarySuggestionDenyList (names : Array Name) : CommandElabM Unit := do
  for n in names do
    if let some component := nameLastStringComponent? n.eraseMacroScopes then
      modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env component

/-- Add docstrings to generated LF-model structure fields after elaborating the structure. -/
def addLFModelStructureFieldDocStrings (theoryName structureName : Name) (checked :
  CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM Unit := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let ownerMap ← lfModelStructureFieldOwnerMap checked structureName admittedNames mode
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      if let some fieldName := o.generatedName? then
        let doc ← lfModelFieldDocString theoryName structureName o
        let owner := (ownerMap.find? fieldName).getD structureName
        liftCoreM <| addDocStringCore (theoryName ++ owner ++ fieldName) doc

/-- Syntax for one generated LF-model field with a custom global-field term map.

This is used by true bundled section packages: fields owned by earlier bundles are rendered as
projections from bundle parameters, while fields owned by the current bundle remain ordinary
structure-field names. -/
partial def lfModelObligationFieldSyntaxWithTermMap? (fieldNames : NameMap Name)
    (fieldTerms : NameMap (TSyntax `term)) (defValues : NameMap CheckedLFExpr)
    (paramVis : LFParamVisibilityMap) (blockingUntyped sidePredicateNames : NameSet) (o :
      LFModelObligation) :
    CommandElabM (Option (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  let fieldTerm (n : Name) : TSyntax `term :=
    let fieldName := lfModelFieldName fieldNames n
    (fieldTerms.find? fieldName).getD (mkIdent fieldName)
  let rec expr (locals : LFLocalSyntaxCtx) : CheckedLFExpr → CommandElabM (TSyntax `term)
    | .ident h =>
        match findLFLocalIdent? locals h.name, h.kind, lfDefinitionValue? defValues h.name with
        | some localId, _, _ => pure localId
        | none, .lfDefinition, some value => expr locals value
        | none, _, _ => pure (fieldTerm h.name)
    | .sort => `(Type)
    | .univ u => typeSyntaxOfLevel u
    | e@(.app ..) => do
        if let some reduced := reduceCheckedLFDefinitionHeadPairApp? defValues
            (lfLocalSyntaxSourceNames locals) e then
          expr locals reduced
        else
        let (head, args) := splitCheckedLFExprApp e
        if let some n := checkedLFExprHeadName? head then
          if lfHeadHasImplicitParams paramVis n then
            let head ← expr locals head
            let head ← explicitLeanHeadSyntax head
            let args ← args.mapM (expr locals)
            return ← mkTermAppSyntax head args
        match e with
        | .app f a => do
            let f ← expr locals f
            let a ← expr locals a
            `($f $a)
        | _ =>
          throwError "internal error: expected LF application while rendering bundled model \
            expression"
    | .arrow none A B => do
        let A ← expr locals A
        let B ← expr locals B
        `($A → $B)
    | .arrow (some x) A B => do
        let A ← expr locals A
        let xId := freshLFLocalIdent x locals
        let B ← expr ((x, xId) :: locals) B
        `(($xId:ident : $A) → $B)
    | .sigma none A B => do
        let A ← expr locals A
        let B ← expr locals B
        `($A × $B)
    | .sigma (some x) A B => do
        let A ← expr locals A
        let xId := freshLFLocalIdent x locals
        let B ← expr ((x, xId) :: locals) B
        `(Sigma (fun $xId:ident : $A => $B))
    | .pair a b => do
        let a ← expr locals a
        let b ← expr locals b
        `(⟨$a, $b⟩)
    | e@(.fst value) => do
        let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
        if reduced != e then
          expr locals reduced
        else
          let value ← expr locals value
          `(($value).1)
    | e@(.snd value) => do
        let reduced := normalizeCheckedLFExprForModel defValues (lfLocalSyntaxSourceNames locals) e
        if reduced != e then
          expr locals reduced
        else
          let value ← expr locals value
          `(($value).2)
    | .lam xs body => do
        let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
          if h : i < xs.size then
            let x := xs[i]
            let xId := freshLFLocalIdent x locals
            let body ← go (i + 1) ((x, xId) :: locals)
            `(fun $xId:ident => $body)
          else
            expr locals body
        go 0 locals
    | .jeq lhs rhs => do
        let lhs ← expr locals lhs
        let rhs ← expr locals rhs
        `($lhs = $rhs)
  let rec obj (locals : LFLocalSyntaxCtx) : ObjExpr → CommandElabM (TSyntax `term)
    | .ident n =>
        let n := n.eraseMacroScopes
        match findLFLocalIdent? locals n, lfDefinitionValue? defValues n with
        | some localId, _ => pure localId
        | none, some value => expr locals value
        | none, none => pure (fieldTerm n)
    | .sort => `(Type)
    | .univ u => typeSyntaxOfLevel u
    | e@(.app ..) => do
        let (head, args) := splitObjExprAppForModel e
        if let some n := objExprHeadName? head then
          if lfHeadHasImplicitParams paramVis n then
            let head ← obj locals head
            let head ← explicitLeanHeadSyntax head
            let args ← args.mapM (obj locals)
            return ← mkTermAppSyntax head args
        match e with
        | .app f a => do
            let f ← obj locals f
            let a ← obj locals a
            `($f $a)
        | _ =>
          throwError "internal error: expected LF application while rendering bundled model \
            object expression"
    | .arrow none A B | .funArrow none A B => do
        let A ← obj locals A
        let B ← obj locals B
        `($A → $B)
    | .arrow (some x) A B | .funArrow (some x) A B => do
        let A ← obj locals A
        let x := x.eraseMacroScopes
        let xId := freshLFLocalIdent x locals
        let B ← obj ((x, xId) :: locals) B
        `(($xId:ident : $A) → $B)
    | .sigma none A B => do
        let A ← obj locals A
        let B ← obj locals B
        `($A × $B)
    | .sigma (some x) A B => do
        let A ← obj locals A
        let x := x.eraseMacroScopes
        let xId := freshLFLocalIdent x locals
        let B ← obj ((x, xId) :: locals) B
        `(Sigma (fun $xId:ident : $A => $B))
    | .pair a b => do
        let a ← obj locals a
        let b ← obj locals b
        `(⟨$a, $b⟩)
    | .fst e => do
        let e ← obj locals e
        `(($e).1)
    | .snd e => do
        let e ← obj locals e
        `(($e).2)
    | .lam xs body => do
        let rec go (i : Nat) (locals : LFLocalSyntaxCtx) : CommandElabM (TSyntax `term) := do
          if i < xs.size then
            let x := xs[i]!.eraseMacroScopes
            let xId := freshLFLocalIdent x locals
            let body ← go (i + 1) ((x, xId) :: locals)
            `(fun $xId:ident => $body)
          else
            obj locals body
        go 0 locals
    | .jeq lhs rhs => do
        let lhs ← obj locals lhs
        let rhs ← obj locals rhs
        `($lhs = $rhs)
  let rec telescope (binders : Array CheckedLFBinding) (result : TSyntax `term)
      (locals : LFLocalSyntaxCtx := []) (i : Nat := 0) : CommandElabM (TSyntax `term) := do
    if h : i < binders.size then
      let b := binders[i]
      let ty ← expr locals b.checkedTypeExpr
      let xId := freshLFLocalIdent b.name locals
      let rest ← telescope binders result ((b.name, xId) :: locals) (i + 1)
      let binder ← lfRenderedBinderSyntax { name := xId.getId, typeStx := ty, visibility :=
        b.visibility }
      `($binder:bracketedBinder → $rest)
    else
      pure result
  unless o.generatedRole == .field && o.renderable do
    return none
  let some generatedName := o.generatedName?
    | throwError "LF model obligation '{o.name}' is a renderable field but has no generated field \
      name"
  match o.source with
  | .syntaxSort | .judgment | .sideConditionPredicate =>
      let some typeExpr := o.typeExpr?
        | throwError "LF model field obligation '{o.name}' has no checked type expression"
      let result ← expr [] typeExpr
      let ty ← telescope o.params result
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .typedOpaque | .admittedOpaque =>
      let some typeExpr := o.typeExpr?
        | throwError "LF model field obligation '{o.name}' has no checked type expression"
      let result ← expr [] typeExpr
      let ty ← telescope o.params result
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .theoremSideConditionCertificate =>
      let some input := o.sourceObjExpr?
        | throwError "LF theorem side-condition obligation '{o.name}' has no source input \
          expression"
      let ty ← obj [] input
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .rule =>
      let some conclusionExpr := o.typeExpr?
        | throwError "LF rule field obligation '{o.name}' has no checked conclusion expression"
      let mut locals : LFLocalSyntaxCtx := []
      let mut binders : Array LFRenderedBinder := #[]
      for p in o.params do
        let ty ← expr locals p.checkedTypeExpr
        let id := freshLFLocalIdent p.name locals
        binders := binders.push { name := id.getId, typeStx := ty, visibility := p.visibility }
        locals := (p.name, id) :: locals
      for p in o.premises do
        let ty ← expr locals p.checkedJudgmentExpr
        binders := binders.push { name := p.name, typeStx := ty }
      for e in o.paramEvidences do
        let ty ← expr locals e.checkedJudgmentExpr
        binders := binders.push { name := e.name, typeStx := ty }
      for sc in o.sideConditions do
        let ty ←
          if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames sc.checkedInput
            then
            expr locals sc.checkedInput
          else
            `(Type)
        binders := binders.push { name := sc.name, typeStx := ty }
      let concl ← expr locals conclusionExpr
      let ty ← lfRenderedTelescopeSyntax binders concl
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .untypedOpaque | .objectDefinition | .judgmentTheorem =>
      return none

/-- Syntax for one generated LF-model field, driven by the generic obligation IR. -/
def lfModelObligationFieldSyntax? (fieldNames : NameMap Name) (defValues : NameMap CheckedLFExpr)
    (paramVis : LFParamVisibilityMap) (blockingUntyped sidePredicateNames : NameSet) (o :
      LFModelObligation) :
    CommandElabM (Option (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  unless o.generatedRole == .field && o.renderable do
    return none
  let some generatedName := o.generatedName?
    | throwError "LF model obligation '{o.name}' is a renderable field but has no generated field \
      name"
  match o.source with
  | .syntaxSort | .judgment | .sideConditionPredicate =>
      let some typeExpr := o.typeExpr?
        | throwError "LF model field obligation '{o.name}' has no checked type expression"
      let result ← lfExprSyntaxInModelWithFields fieldNames defValues [] paramVis typeExpr
      let ty ← lfTelescopeSyntaxInModelWithFields fieldNames defValues o.params result [] 0 paramVis
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .typedOpaque | .admittedOpaque =>
      let some typeExpr := o.typeExpr?
        | throwError "LF model field obligation '{o.name}' has no checked type expression"
      let result ← lfExprSyntaxInModelWithFields fieldNames defValues [] paramVis typeExpr
      let ty ← lfTelescopeSyntaxInModelWithFields fieldNames defValues o.params result [] 0 paramVis
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .theoremSideConditionCertificate =>
      let some input := o.sourceObjExpr?
        | throwError "LF theorem side-condition obligation '{o.name}' has no source input \
          expression"
      let ty ← lfObjExprSyntaxInModelWithFields fieldNames defValues [] paramVis input
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .rule =>
      let some conclusionExpr := o.typeExpr?
        | throwError "LF rule field obligation '{o.name}' has no checked conclusion expression"
      let mut locals : LFLocalSyntaxCtx := []
      let mut binders : Array LFRenderedBinder := #[]
      for p in o.params do
        let ty ←
          lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis p.checkedTypeExpr
        let id := freshLFLocalIdent p.name locals
        binders := binders.push { name := id.getId, typeStx := ty, visibility := p.visibility }
        locals := (p.name, id) :: locals
      for p in o.premises do
        let ty ←
          lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis p.checkedJudgmentExpr
        binders := binders.push { name := p.name, typeStx := ty }
      for e in o.paramEvidences do
        let ty ←
          lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis e.checkedJudgmentExpr
        binders := binders.push { name := e.name, typeStx := ty }
      for sc in o.sideConditions do
        let ty ←
          if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames sc.checkedInput
            then
            lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis sc.checkedInput
          else
            `(Type)
        binders := binders.push { name := sc.name, typeStx := ty }
      let concl ← lfExprSyntaxInModelWithFields fieldNames defValues locals paramVis conclusionExpr
      let ty ← lfRenderedTelescopeSyntax binders concl
      some <$> lfFieldSyntax o.source.label generatedName ty
  | .untypedOpaque | .objectDefinition | .judgmentTheorem =>
      return none

/-- Field-dependency diagnostics for generated LF-model fields. -/
def lfModelFieldDependencySummaries (checked : CheckedSignature) (admittedNames : NameSet := {}) :
  CommandElabM (Array MessageData) := do
  let obs ← validateLFModelObligations checked admittedNames
  let mut out := #[]
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      let generated := match o.generatedName? with
        | some n => m!"{n}"
        | none => m!"<missing>"
      let extra :=
        if o.premiseCount == 0 && o.sideConditionCount == 0 then m!""
        else m!", premises={o.premiseCount}, side_conditions={o.sideConditionCount}"
      out := out.push m!"{generated}: source={o.source.label}, params={o.paramCount}{extra}"
  pure out

/-- Statement diagnostics for replayed LF derived declarations over a generated model. -/
def lfModelDerivedStatementSummaries (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) : CommandElabM (Array MessageData) := do
  let obs ← validateLFModelObligations checked admittedNames
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let M := mkIdent `M
  let structTy := mkIdent structureName
  let mut out := #[]
  for o in obs do
    if o.generatedRole == .derivedDeclaration && o.renderable then
      if let some statement := o.typeExpr? then
        let generated := (o.generatedName?).getD o.name
        let theoremBinders := match checked.lfJudgmentTheorems.find? (fun t =>
          t.name == o.name) with
          | some t => t.binders
          | none => #[]
        let mut locals : LFLocalSyntaxCtx := []
        let mut binderText : Array MessageData := #[]
        for b in theoremBinders do
          let ty ←
            lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis
              b.checkedTypeExpr
          let openDelim := if b.visibility == .implicit then "{" else "("
          let closeDelim := if b.visibility == .implicit then "}" else ")"
          let id := freshLFModelLocalIdent b.name M locals
          binderText := binderText.push m!" {openDelim}{id} : {ty}{closeDelim}"
          locals := (b.name, id) :: locals
        let ty ←
          lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis statement
        let certParams := lfTheoremSideConditionFieldsForTheorem checked o.name
        let certText :=
          if certParams.isEmpty then m!""
          else m!", certificate_params={certParams.size}"
        out :=
          out.push m!"def {generated} ({M} : \
            {structTy}){certText}{MessageData.joinSep binderText.toList m!""} : {ty}"
  pure out

/-- Summary of LF-model fields that can be generated from checked LF metadata. -/
def lfModelSummaryString (checked : CheckedSignature) (admittedNames : NameSet := {}) : String :=
  let obs := lfModelObligations checked admittedNames
  let countFields (source : LFModelObligationSource) :=
    countLFModelObligations obs fun o =>
      o.source == source && o.generatedRole == .field && o.renderable
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let certParams := countLFModelObligations obs fun o =>
    o.source == .theoremSideConditionCertificate && o.generatedRole == .derivedParameter &&
      o.renderable
  let typedOpaque := countFields .typedOpaque
  let tempAdmissions := countFields .admittedOpaque
  let sidePredicates := countFields .sideConditionPredicate
  let renderableRules := countFields .rule
  let tempText := if tempAdmissions == 0 then "" else
    s!", {tempAdmissions} temporary admitted-definition field(s)"
  let abbrevCount := checked.lfSyntaxAbbrevs.size + checked.lfJudgmentAbbrevs.size
  let abbrevText := if abbrevCount == 0 then "" else
    s!", {abbrevCount} LF abbreviation(s) expanded"
  s!"LF model summary for {nameString checked.name}: {checked.lfSyntaxSorts.size} syntax sort \
    field(s){abbrevText}, {checked.lfJudgments.size} judgment field(s), {typedOpaque} typed \
      opaque constant field(s){tempText}, {sidePredicates} side-condition predicate field(s), \
        {certParams} theorem side-condition certificate parameter(s), \
          {renderableRules}/{checked.lfRules.size} rule field(s); omitted {blockingUntyped.size} \
            untyped opaque placeholder(s)"

/-- Explain which LF metadata declarations the LF-model backend omits. -/
def lfModelOmissionsString (checked : CheckedSignature) (admittedNames : NameSet := {}) : String :=
  let obs := lfModelObligations checked admittedNames
  let omitted := obs.filter (fun o => o.generatedRole == .omitted || !o.renderable)
  let generatedNotes := obs.filterMap fun o =>
    match o.source, o.generatedRole, o.diagnostic? with
    | .sideConditionPredicate, .field, _ =>
      some s!"side-condition predicate generated: {nameString o.name} / {o.paramCount}"
    | .theoremSideConditionCertificate, .derivedParameter, some d =>
      some s!"theorem side-condition certificate parameter generated: \
        {nameString ((o.generatedName?).getD o.name)} ({d})"
    | .admittedOpaque, .field, some d =>
      some s!"temporary admitted-definition model field: {nameString o.name} ({d})"
    | .admittedOpaque, .derivedDeclaration, some d =>
      some s!"admitted opaque generated as Lean sorry declaration, not model field: \
        {nameString o.name} ({d})"
    | _, _, _ => none
  let omittedLines := omitted.map fun o =>
    let generated := match o.generatedName? with
      | some n => s!", generated candidate {nameString n}"
      | none => ""
    let diag := (o.diagnostic?).getD "not renderable by the LF-model backend"
    let next := match o.source with
      | .untypedOpaque =>
        "add a checked LF type, or use this opaque only as a side-condition predicate head"
      | .rule =>
        "inspect the listed dependency and avoid untyped placeholders in rendered rule types"
      | .objectDefinition =>
        "check that both the lf_def type and value render over the generated model interface"
      | .judgmentTheorem =>
        "check derivation/replay availability and renderability of local binders, statement, and \
          certificate inputs"
      | .theoremSideConditionCertificate =>
        "make the side-condition input renderable or supply a theorem-specific certificate \
          parameter manually"
      | _ => "inspect the source declaration and generated model obligation"
    s!"omitted {o.source.label} {nameString o.name}{generated}: {diag}; next action: {next}"
  let lines := generatedNotes.toList ++ omittedLines.toList
  if lines.isEmpty then
    s!"LF model omissions for {nameString checked.name}: none"
  else
    String.intercalate "\n" (s!"LF model omissions for {nameString checked.name}:" :: lines)

/-- Split generated structure fields into nonempty chunks, preserving order. -/
def chunkLFModelStructureFields (fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder))
    (chunkSize : Nat := lfModelStructureChunkSize) :
      Array (Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) := Id.run do
  if fields.isEmpty then
    return #[#[]]
  let chunkSize := if chunkSize == 0 then fields.size else chunkSize
  let mut chunks := #[]
  let mut current := #[]
  for field in fields do
    current := current.push field
    if current.size == chunkSize then
      chunks := chunks.push current
      current := #[]
  unless current.isEmpty do
    chunks := chunks.push current
  return chunks

/-- Rendered model field together with the universe parameters needed by its type. -/
structure LFRenderedModelField where
  obligation : LFModelObligation
  fieldSyntax : TSyntax `Lean.Parser.Command.structSimpleBinder
  levelParams : Array Name

/-- Split rendered generated structure fields into nonempty chunks, preserving order. -/
def chunkLFRenderedModelFields (fields : Array LFRenderedModelField)
    (chunkSize : Nat := lfModelStructureChunkSize) : Array (Array LFRenderedModelField) := Id.run do
  if fields.isEmpty then
    return #[#[]]
  let chunkSize := if chunkSize == 0 then fields.size else chunkSize
  let mut chunks := #[]
  let mut current := #[]
  for field in fields do
    current := current.push field
    if current.size == chunkSize then
      chunks := chunks.push current
      current := #[]
  unless current.isEmpty do
    chunks := chunks.push current
  return chunks

/-- Render all generated LF-model fields from the generic model-obligation IR. -/
def lfModelStructureRenderedFields (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : CommandElabM (Array LFRenderedModelField) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut fields := #[]
  for o in obs do
    if let some field ←
      lfModelObligationFieldSyntax? fieldNames defValues paramVis blockingUntyped
        sidePredicateNames o then
      let used :=
        lfModelObligationRenderedLevelParams defValues blockingUntyped sidePredicateNames o
      fields := fields.push {
        obligation := o
        fieldSyntax := field
        levelParams := orderedModelLevelParams checked used }
  pure fields

/-- Render all generated LF-model field syntaxes from the generic model-obligation IR. -/
def lfModelStructureFieldSyntaxes (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) :
    CommandElabM (Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  let fields ← lfModelStructureRenderedFields checked admittedNames mode
  pure (fields.map (·.fieldSyntax))

/-- Syntax for one generated LF-model structure or internal structure chunk. -/
def lfModelStructureCommandSyntax (_checked : CheckedSignature) (structureName : Name)
    (fields : Array (TSyntax `Lean.Parser.Command.structSimpleBinder))
    (levelParams : Array Name := #[]) (parent? : Option (Name × Array Name) := none)
    (internalChunk : Bool := false) : CommandElabM Syntax := do
  let structId := mkIdent structureName
  let levelIds := levelParams.map (mkIdent ·.eraseMacroScopes)
  let cmd ←
    match parent? with
    | none =>
        if levelIds.isEmpty then
          if internalChunk then
            `(command| /-- Internal chunk of a generated LF model interface. -/
              structure $structId:ident where
                $[$fields:structSimpleBinder]*)
          else
            `(command| /-- Prototype generated LF model interface from checked LF model
              obligations. -/
              structure $structId:ident where
                $[$fields:structSimpleBinder]*)
        else
          if internalChunk then
            `(command| /-- Internal chunk of a generated LF model interface. -/
              structure $structId:ident.{$[$levelIds:ident],*} where
                $[$fields:structSimpleBinder]*)
          else
            `(command| /-- Prototype generated LF model interface from checked LF model
              obligations. -/
              structure $structId:ident.{$[$levelIds:ident],*} where
                $[$fields:structSimpleBinder]*)
    | some (parent, parentLevels) =>
        let parentId := mkIdent parent
        let parentLevelIds := parentLevels.map (mkIdent ·.eraseMacroScopes)
        if levelIds.isEmpty then
          if internalChunk then
            `(command| /-- Internal chunk of a generated LF model interface. -/
              structure $structId:ident extends $parentId:ident where
                $[$fields:structSimpleBinder]*)
          else
            `(command| /-- Prototype generated LF model interface from checked LF model
              obligations. -/
              structure $structId:ident extends $parentId:ident where
                $[$fields:structSimpleBinder]*)
        else if parentLevelIds.isEmpty then
          if internalChunk then
            `(command| /-- Internal chunk of a generated LF model interface. -/
              structure $structId:ident.{$[$levelIds:ident],*} extends $parentId:ident where
                $[$fields:structSimpleBinder]*)
          else
            `(command| /-- Prototype generated LF model interface from checked LF model
              obligations. -/
              structure $structId:ident.{$[$levelIds:ident],*} extends $parentId:ident where
                $[$fields:structSimpleBinder]*)
        else
          if internalChunk then
            `(command| /-- Internal chunk of a generated LF model interface. -/
              structure $structId:ident.{$[$levelIds:ident],*} extends
                $parentId:ident.{$[$parentLevelIds:ident],*} where
                $[$fields:structSimpleBinder]*)
          else
            `(command| /-- Prototype generated LF model interface from checked LF model
              obligations. -/
              structure $structId:ident.{$[$levelIds:ident],*} extends
                $parentId:ident.{$[$parentLevelIds:ident],*} where
                $[$fields:structSimpleBinder]*)
  let autoImplicitOpt := mkIdent `autoImplicit
  let wrapped ← `(command| set_option $autoImplicitOpt:ident false in $cmd:command)
  pure wrapped.raw

/-- Syntax-level generated LF model structures from the generic LF model-obligation IR.

Small interfaces remain a single public structure.  Large interfaces are emitted as ordered
internal chunks whose final structure keeps the requested public name. -/
def lfModelStructureSyntaxes (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (Array Syntax) := do
  let fields ← lfModelStructureRenderedFields checked admittedNames mode
  let chunks := chunkLFRenderedModelFields fields
  let mut cmds := #[]
  let mut parent? : Option (Name × Array Name) := none
  let mut parentLevels : Array Name := #[]
  for h : i in [:chunks.size] do
    let chunkFields := chunks[i]
    let isFinal := i + 1 == chunks.size
    let owner := if chunks.size <= 1 || isFinal then structureName else
      lfModelStructureChunkName structureName i
    let ownLevels := orderedModelLevelParamUnion checked (chunkFields.map (·.levelParams))
    let thisLevels := orderedModelLevelParamUnion checked #[parentLevels, ownLevels]
    let syntaxFields := chunkFields.map (·.fieldSyntax)
    cmds := cmds.push (← lfModelStructureCommandSyntax checked owner syntaxFields thisLevels
      parent? (!isFinal))
    parent? := some (owner, thisLevels)
    parentLevels := thisLevels
  pure cmds

/-- User-facing section assigned to a source LF declaration, if any. -/
def lfModelSectionMap (checked : CheckedSignature) : NameMap Name := Id.run do
  let mut out : NameMap Name := {}
  for m in checked.modelSectionMemberships do
    out := out.insert m.declName.eraseMacroScopes m.sectionName.eraseMacroScopes
  return out

/-- Section label for an obligation in a sectioned generated model interface. -/
def lfModelSectionOfObligation (sectionMap : NameMap Name) (o : LFModelObligation) : Name :=
  (sectionMap.find? o.name.eraseMacroScopes).getD `Other

/-- A contiguous dependency-ordered run of generated fields with the same user-facing section. -/
structure LFModelSectionRun where
  sectionName : Name
  occurrence : Nat
  fields : Array LFModelObligation
  deriving Inhabited, Repr, BEq

/-- Split renderable fields into dependency-ordered section runs.

Runs, rather than one structure per section name, preserve the dependency order computed by
`orderLFModelFieldObligations`.  If a user puts a field in a section whose dependencies are
introduced by a later source section, the backend may emit a second run for that section rather
than invalid Lean structure fields that mention future projections. -/
def lfModelSectionRuns (checked : CheckedSignature) (obs : Array LFModelObligation) :
  Array LFModelSectionRun := Id.run do
  let sectionMap := lfModelSectionMap checked
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  if fields.isEmpty then
    return #[{ sectionName := `Empty, occurrence := 1, fields := #[] }]
  let mut runs : Array LFModelSectionRun := #[]
  let mut occurrences : NameMap Nat := {}
  let mut currentName := lfModelSectionOfObligation sectionMap fields[0]!
  let mut currentFields := #[]
  for o in fields do
    let sectionName := lfModelSectionOfObligation sectionMap o
    if sectionName == currentName then
      currentFields := currentFields.push o
    else
      let nextOccurrence := ((occurrences.find? currentName).getD 0) + 1
      runs := runs.push { sectionName := currentName, occurrence := nextOccurrence, fields :=
        currentFields }
      occurrences := occurrences.insert currentName nextOccurrence
      currentName := sectionName
      currentFields := #[o]
  let nextOccurrence := ((occurrences.find? currentName).getD 0) + 1
  runs := runs.push { sectionName := currentName, occurrence := nextOccurrence, fields :=
    currentFields }
  return runs

/-- Suffix used for a user-provided model section in generated structure names. -/
def lfModelSectionNameSuffix (run : LFModelSectionRun) : String :=
  let base :=
    (nameLastStringComponent? run.sectionName.eraseMacroScopes).getD (toString
      run.sectionName.eraseMacroScopes)
  if run.occurrence <= 1 then s!"_{base}" else s!"_{base}_part{run.occurrence}"

/-- Render fields for selected obligations, using the full field map. -/
def lfModelStructureRenderedFieldsForObligations (checked : CheckedSignature) (allObs runObs :
  Array LFModelObligation) : CommandElabM (Array LFRenderedModelField) := do
  let fieldNames := lfModelFieldNameMap allObs
  let paramVis := lfParamVisibilityMapOfObligations allObs
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut fields := #[]
  for o in runObs do
    if let some field ←
      lfModelObligationFieldSyntax? fieldNames defValues paramVis blockingUntyped
        sidePredicateNames o then
      let used :=
        lfModelObligationRenderedLevelParams defValues blockingUntyped sidePredicateNames o
      fields := fields.push {
        obligation := o
        fieldSyntax := field
        levelParams := orderedModelLevelParams checked used }
  pure fields

/-- Render field syntaxes for a selected set of model obligations, using the full field map. -/
def lfModelStructureFieldSyntaxesForObligations (checked : CheckedSignature) (allObs runObs :
  Array LFModelObligation) :
    CommandElabM (Array (TSyntax `Lean.Parser.Command.structSimpleBinder)) := do
  let fields ← lfModelStructureRenderedFieldsForObligations checked allObs runObs
  pure (fields.map (·.fieldSyntax))

/-- Generated sectioned LF model-interface structures from the generic obligation IR.

This uses user-provided `model_section` metadata for readable bundle boundaries and still
splits oversized sections into `extends` chunks using the same field-count threshold as the
flat generator.  The requested final structure name remains the last generated structure. -/
def lfModelSectionStructureSyntaxes (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (Array Syntax × Array Name) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let runs := lfModelSectionRuns checked obs
  let mut cmds := #[]
  let mut names := #[]
  let mut parent? : Option (Name × Array Name) := none
  let mut parentLevels : Array Name := #[]
  for hRun : runIndex in [:runs.size] do
    let run := runs[runIndex]
    let renderedFields ← lfModelStructureRenderedFieldsForObligations checked obs run.fields
    let chunks := chunkLFRenderedModelFields renderedFields lfModelSectionStructureChunkSize
    for hChunk : chunkIndex in [:chunks.size] do
      let isFinalGlobal := runIndex + 1 == runs.size && chunkIndex + 1 == chunks.size
      let baseName := nameWithLastComponentSuffix structureName (lfModelSectionNameSuffix run)
      let owner :=
        if isFinalGlobal then structureName
        else if chunks.size == 1 then baseName
        else nameWithLastComponentSuffix baseName s!"_chunk{chunkIndex}"
      let chunkFields := chunks[chunkIndex]!
      let ownLevels := orderedModelLevelParamUnion checked (chunkFields.map (·.levelParams))
      let thisLevels := orderedModelLevelParamUnion checked #[parentLevels, ownLevels]
      let syntaxFields := chunkFields.map (·.fieldSyntax)
      cmds := cmds.push (← lfModelStructureCommandSyntax checked owner syntaxFields thisLevels
        parent? (!isFinalGlobal))
      names := names.push owner
      parent? := some (owner, thisLevels)
      parentLevels := thisLevels
  pure (cmds, names)

/-- Names of the generated flat-interface structures/chunks for a field count. -/
def lfModelFlatChunkStructureNames (structureName : Name) (fieldCount : Nat) : Array Name :=
  Id.run do
  let chunkSize := if lfModelStructureChunkSize == 0 then fieldCount else lfModelStructureChunkSize
  let chunkCount := if fieldCount == 0 then 1 else (fieldCount + chunkSize - 1) / chunkSize
  let mut out := #[]
  for i in [:chunkCount] do
    let isFinal := i + 1 == chunkCount
    out := out.push (if chunkCount <= 1 || isFinal then structureName else
      lfModelStructureChunkName structureName i)
  return out

/-- Build a chunked structure-literal term for a target generated model interface.

Large adapters are split along the target flat interface's own chunks, avoiding one enormous
structure literal while preserving ordinary projection/dot-notation behavior. -/
partial def lfModelChunkedAdapterBodyTerm (targetName : Name) (fields : Array LFModelObligation)
    (sourceModel : Ident) : CommandElabM (TSyntax `term) := do
  let chunkSize := if fields.isEmpty then 1 else if lfModelStructureChunkSize == 0 then
    fields.size else lfModelStructureChunkSize
  let chunkCount := if fields.isEmpty then 1 else (fields.size + chunkSize - 1) / chunkSize
  let targetNames := lfModelFlatChunkStructureNames targetName fields.size
  let rec build (i : Nat) (prev? : Option Ident) : CommandElabM (TSyntax `term) := do
    if i < chunkCount then
      let start := i * chunkSize
      let stop := Nat.min fields.size (start + chunkSize)
      let slice := fields.extract start stop
      let fieldIds := slice.filterMap (fun o => o.generatedName?.map mkIdent)
      let mut values : Array (TSyntax `term) := #[]
      for fieldId in fieldIds do
        values := values.push (← `(term| $sourceModel:ident.$fieldId:ident))
      let value ←
        match prev? with
        | none => `(term| { $[$fieldIds:ident := $values:term]* })
        | some prev => `(term| { $prev:ident with $[$fieldIds:ident := $values:term]* })
      let var := mkIdent (Name.mkSimple s!"adapterChunk{i}")
      let ty := mkIdent targetNames[i]!
      let rest ← build (i + 1) (some var)
      `(term| let $var:ident : $ty:ident := $value:term; $rest:term)
    else
      match prev? with
      | some prev => pure prev
      | none => `(term| {})
  build 0 none

/-- Build the generated adapter from a standalone sectioned interface to a flat LF model interface.
-/
def lfModelToFlatAdapterCommandSyntax (checked : CheckedSignature) (
  sourceName targetName adapterName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM Syntax :=
      do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let M := mkIdent `M
  let sourceId := mkIdent sourceName
  let targetId := mkIdent targetName
  let adapterId := mkIdent adapterName
  let body ← lfModelChunkedAdapterBodyTerm targetName fields M
  `(command| /-- Generated adapter from a sectioned LF model interface to the flat LF model
    interface. -/
    def $adapterId:ident ($M:ident : $sourceId:ident) : $targetId:ident :=
      $body:term)

/-- Fast sectioned-interface wrapper for the common `... adapting Flat` workflow.

When a flat interface is already available, the adapter path can reuse it directly instead of
elaborating a second huge dependent structure telescope and an 800-field projection shuffle.
The generated sectioned name remains a distinct type and Lean automatically provides the
`toFlat` projection used as the adapter; use `generate_model_section_interface` when a
standalone section-owned interface is needed. -/
def lfModelSectionWrapperCommandSyntax (sourceName targetName : Name) : CommandElabM Syntax := do
  let sourceId := mkIdent sourceName
  let targetId := mkIdent targetName
  `(command| /-- Fast sectioned LF model interface wrapper over an already generated flat interface.

  The flat parent supplies the fields and the inherited `to...` projection is the adapter.
  Use `#print_model_sections` to inspect the theory-local grouping metadata. -/
    structure $sourceId:ident extends $targetId:ident where)

/-- Structure name for a generated model-bundle section run. -/
def lfModelBundleRunStructureName (bundleName : Name) (run : LFModelSectionRun) : Name :=
  nameWithLastComponentSuffix bundleName (lfModelSectionNameSuffix run)

/-- Structure name for a chunk of a generated model-bundle section run. -/
def lfModelBundleRunChunkStructureName (bundleName : Name) (run : LFModelSectionRun) (
  chunkIndex chunkCount : Nat) : Name :=
  let baseName := lfModelBundleRunStructureName bundleName run
  if chunkCount <= 1 || chunkIndex == 0 then baseName
  else nameWithLastComponentSuffix baseName s!"_chunk{chunkIndex}"

/-- Generate true section-bundle structures as an `extends` chain plus a final flat adapter.

Each dependency-ordered section run gets one or more structures.  Later section structures extend
earlier ones, so users can either fill the final bundle directly or build section records with
ordinary Lean parent fields such as `toBundle_Core`.  The requested bundle name is a final wrapper
extending the last section structure and owns the generated `toFlat` adapter method. -/
def lfModelSectionBundleSyntaxes (checked : CheckedSignature) (bundleName flatName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (Array Syntax × Syntax × Array Name) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let runs := lfModelSectionRuns checked obs
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let mut cmds := #[]
  let mut generatedNames := #[]
  let mut previousFieldTerms : NameMap (TSyntax `term) := {}
  let mut parent? : Option Name := none
  for run in runs do
    let chunkSize :=
      if run.fields.isEmpty then 1
      else if lfModelSectionStructureChunkSize == 0 then run.fields.size
      else lfModelSectionStructureChunkSize
    let chunkCount := if run.fields.isEmpty then 1 else
      (run.fields.size + chunkSize - 1) / chunkSize
    for chunkIndex in [:chunkCount] do
      let start := chunkIndex * chunkSize
      let stop := Nat.min run.fields.size (start + chunkSize)
      let chunkFields := run.fields.extract start stop
      let structName := lfModelBundleRunChunkStructureName bundleName run chunkIndex chunkCount
      let structId := mkIdent structName
      let mut fieldTerms := previousFieldTerms
      for o in chunkFields do
        if let some fieldName := o.generatedName? then
          fieldTerms := fieldTerms.insert fieldName (mkIdent fieldName)
      let mut structFields := #[]
      for o in chunkFields do
        if let some stx ←
          lfModelObligationFieldSyntaxWithTermMap? fieldNames fieldTerms defValues paramVis
            blockingUntyped sidePredicateNames o then
          structFields := structFields.push stx
      let cmd ←
        match parent? with
        | none => `(command| /-- Generated model-bundle section in an `extends` chain. -/
            structure $structId:ident where
              $[$structFields:structSimpleBinder]*)
        | some parent =>
            let parentId := mkIdent parent
            `(command| /-- Generated model-bundle section in an `extends` chain. -/
              structure $structId:ident extends $parentId:ident where
                $[$structFields:structSimpleBinder]*)
      cmds := cmds.push cmd.raw
      generatedNames := generatedNames.push structName
      parent? := some structName
      for o in chunkFields do
        if let some fieldName := o.generatedName? then
          previousFieldTerms := previousFieldTerms.insert fieldName (mkIdent fieldName)
  let bundleId := mkIdent bundleName
  let finalCmd ←
    match parent? with
    | none => `(command| /-- Final generated model-section bundle. -/
        structure $bundleId:ident where)
    | some parent =>
        let parentId := mkIdent parent
        `(command| /-- Final generated model-section bundle. -/
          structure $bundleId:ident extends $parentId:ident where)
  cmds := cmds.push finalCmd.raw
  generatedNames := generatedNames.push bundleName
  let M := mkIdent `M
  let flatId := mkIdent flatName
  let adapterName :=
    let component :=
      (nameLastStringComponent? flatName.eraseMacroScopes).getD (toString flatName.eraseMacroScopes)
    Name.mkSimple s!"to{component}"
  let adapterId := mkIdent adapterName
  let body ← lfModelChunkedAdapterBodyTerm flatName fields M
  let adapterCmd ←
    `(command| /-- Assemble a generated section bundle into the flat LF model interface. -/
    def $adapterId:ident ($M:ident : $bundleId:ident) : $flatId:ident :=
      $body:term)
  pure (cmds, adapterCmd.raw, generatedNames)

/-- Name for the generated sectioned-to-flat adapter. -/
def lfModelToFlatAdapterName (flatName : Name) : Name :=
  let component :=
    (nameLastStringComponent? flatName.eraseMacroScopes).getD (toString flatName.eraseMacroScopes)
  Name.mkSimple s!"to{component}"

/-- Compatibility wrapper for code paths that still expect one generated structure command. -/
def lfModelStructureSyntax (checked : CheckedSignature) (structureName : Name) (admittedNames :
  NameSet := {}) : CommandElabM Syntax := do
  let cmds ← lfModelStructureSyntaxes checked structureName admittedNames
  if h : cmds.size = 1 then
    pure cmds[0]
  else
    throwError "LF model interface for '{checked.name}' is chunked into {cmds.size} structures; \
      use lfModelStructureSyntaxes"

/-- Export inherited chunk projections through the public model-interface namespace.

Lean's `extends` keeps inherited fields available by dot notation but does not create constants
such as `Final.field` for fields owned by parent chunks.  `export Parent (field)` restores those
qualified names without changing the public structure shape. -/
def lfModelInheritedProjectionExportSyntaxes (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) :
      CommandElabM (Array Syntax) := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let ownerMap ← lfModelStructureFieldOwnerMap checked structureName admittedNames mode
  let mut groups : NameMap (Array Name) := {}
  for o in obs do
    if o.generatedRole == .field && o.renderable then
      if let some fieldName := o.generatedName? then
        let owner := (ownerMap.find? fieldName).getD structureName
        if owner != structureName then
          groups := groups.insert owner (((groups.find? owner).getD #[]).push fieldName)
  let mut cmds := #[]
  for (owner, fieldNames) in groups.toList do
    let ownerId := mkIdent owner
    let fieldIds := fieldNames.map mkIdent
    let cmd ← `(command| export $ownerId:ident ($[$fieldIds:ident]*))
    cmds := cmds.push cmd.raw
  pure cmds

/-- Generate binders for theorem-local side-condition certificate parameters. -/
def lfTheoremSideConditionParamBinders (checked : CheckedSignature) (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (paramVis : LFParamVisibilityMap) (
      blockingUntyped sidePredicateNames : NameSet)
    (modelIdent : Ident) (theoremName : Name) :
    CommandElabM (Option (Array Ident × Array (TSyntax `term) × NameMap Name)) := do
  let certParams := lfTheoremSideConditionFieldsForTheorem checked theoremName
  let mut paramIds := #[]
  let mut paramTypes := #[]
  let mut paramNames : NameMap Name := {}
  for f in certParams do
    unless lfTheoremSideConditionFieldRenderable defValues blockingUntyped sidePredicateNames f do
      return none
    let ty ←
      lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent [] paramVis f.input
    paramIds := paramIds.push (mkIdent f.fieldName)
    paramTypes := paramTypes.push ty
    paramNames := paramNames.insert f.fieldName f.fieldName
  pure (some (paramIds, paramTypes, paramNames))

/-- Render a checked LF derivation as a derived theorem term over a concrete LF model,
when the model backend can interpret every rule/certificate leaf. -/
partial def lfDerivationTermSyntax? (checked : CheckedSignature) (fieldNames : NameMap Name)
    (defValues : NameMap CheckedLFExpr) (paramVis : LFParamVisibilityMap) (
      blockingUntyped sidePredicateNames : NameSet)
    (certParamNames localAssumptionNames : NameMap Name) (modelIdent : Ident)
    (locals : LFLocalSyntaxCtx) (theoremName : Name) (path : Array Nat) :
    CheckedLFDerivation → CommandElabM (Option (TSyntax `term))
  | .localAssumption name _ => do
      match localAssumptionNames.find? name.eraseMacroScopes with
      | some localName => return some (mkIdent localName)
      | none => return none
  | .theoremRef name _ theoremArgs theoremPremises => do
      let thm := mkIdent name
      let some refTheorem := findCheckedLFJudgmentTheorem? checked.lfJudgmentTheorems name
        | return none
      let renderExplicit := refTheorem.binders.any (fun b => b.visibility == .implicit)
      let head ← if renderExplicit then `(term| @$thm:ident) else `($thm $modelIdent)
      let mut args : Array (TSyntax `term) := #[]
      if renderExplicit then
        args := args.push modelIdent
      for f in lfTheoremSideConditionFieldsForTheorem checked name do
        match certParamNames.find? f.fieldName with
        | none => return none
        | some paramName => args := args.push (mkIdent paramName)
      let mut argIndex := 0
      let mut premiseIndex := 0
      for b in refTheorem.binders do
        match b.head? with
        | some h =>
            if h.kind == .judgment then do
              let some premDeriv := theoremPremises[premiseIndex]?
                | return none
              let some premiseTerm ←
                lfDerivationTermSyntax? checked fieldNames defValues paramVis blockingUntyped
                  sidePredicateNames certParamNames localAssumptionNames modelIdent locals
                  theoremName (path.push premiseIndex) premDeriv
                | return none
              args := args.push premiseTerm
              premiseIndex := premiseIndex + 1
            else do
              let some arg := theoremArgs[argIndex]?
                | return none
              unless lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames arg do
                return none
              args :=
                args.push (← lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues
                  modelIdent locals paramVis arg)
              argIndex := argIndex + 1
        | none => return none
      if argIndex != theoremArgs.size || premiseIndex != theoremPremises.size then
        return none
      some <$> mkTermAppSyntax head args
  | .ruleApp ruleName _ ruleArgs premises _ => do
      let some r := findCheckedLFRule? checked.lfRules ruleName
        | return none
      unless (fieldNames.find? ruleName).isSome do
        return none
      unless lfRuleRenderable blockingUntyped r do
        return none
      let mut args : Array (TSyntax `term) := #[]
      let mut subst : NameMap ObjExpr := {}
      for p in r.params, arg in ruleArgs do
        let arg := eraseObjExprScopes arg
        unless lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames arg do
          return none
        args :=
          args.push (← lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent
            locals paramVis arg)
        subst := subst.insert p.name.eraseMacroScopes arg
      for i in List.range premises.size do
        match premises[i]? with
        | none => return none
        | some prem =>
            let maybePremiseTerm ←
              lfDerivationTermSyntax? checked fieldNames defValues paramVis blockingUntyped
                sidePredicateNames certParamNames localAssumptionNames modelIdent locals
                theoremName (path.push i) prem
            match maybePremiseTerm with
            | none => return none
            | some premiseTerm => args := args.push premiseTerm
      for ev in r.paramEvidences do
        let mut premiseIndex? : Option Nat := none
        for i in List.range r.premises.size do
          if let some p := r.premises[i]? then
            if p.name == ev.name then
              premiseIndex? := some i
        match premiseIndex? with
        | none => return none
        | some i =>
            match premises[i]? with
            | none => return none
            | some prem =>
                let maybeEvTerm ←
                  lfDerivationTermSyntax? checked fieldNames defValues paramVis blockingUntyped
                    sidePredicateNames certParamNames localAssumptionNames modelIdent locals
                    theoremName (path.push i) prem
                match maybeEvTerm with
                | none => return none
                | some evTerm => args := args.push evTerm
      for sc in r.sideConditions do
        let instantiatedInput := eraseObjExprScopes (substLFParams subst sc.input)
        if lfExprRenderableInModel defValues blockingUntyped sidePredicateNames sc.checkedInput &&
            lfObjExprRenderableInModel defValues blockingUntyped sidePredicateNames
              instantiatedInput then
          let certName := lfTheoremSideConditionFieldName theoremName path sc.name
          match certParamNames.find? certName with
          | none => return none
          | some paramName => args := args.push (mkIdent paramName)
        else
          return none
      let ruleField := mkIdent (lfModelFieldName fieldNames ruleName)
      let head ← `($modelIdent.$ruleField:ident)
      let head ← if r.params.any (fun p => p.visibility == .implicit) then
        explicitLeanHeadSyntax head else pure head
      some <$> mkTermAppSyntax head args

/-- Syntax-level derived LF theorem generated by replaying a checked LF derivation over a model,
using a chosen generated Lean declaration name. -/
def lfJudgmentTheoremInterpretationSyntaxAs? (checked : CheckedSignature) (
  structureName outputName : Name)
    (t : CheckedLFJudgmentTheorem) (admittedNames : NameSet := {}) :
      CommandElabM (Option Syntax) := do
  let some derivation := t.derivation?
    | return none
  -- Derived theorem generation consumes only theorem artifacts that reached and re-check at
  -- the kernel-facing replay layer, even though the current term renderer still walks the
  -- richer checked LF derivation tree for source-level argument names.
  match checkedKernelLFReplayForTheorem checked t with
  | .ok _checkedReplay => pure ()
  | .error _err => return none
  let obs ← validateLFModelObligations checked admittedNames
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let blockingUntyped := blockingUntypedLFOpaqueNames checked
  let sidePredicateNames := lfSideConditionPredicateNames checked
  let M := mkIdent `M
  let some (certParamIds, certParamTypes, certParamNames) ←
      lfTheoremSideConditionParamBinders checked fieldNames defValues paramVis blockingUntyped
        sidePredicateNames M t.name
    | return none
  let mut locals : LFLocalSyntaxCtx := []
  let mut localAssumptionNames : NameMap Name := {}
  let reservedTheoremLocals : NameSet := certParamNames.toList.foldl (init := {}) fun names p =>
    names.insert p.2.eraseMacroScopes
  let mut theoremBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for b in t.binders do
    unless lfExprRenderableInModel defValues blockingUntyped sidePredicateNames b.checkedTypeExpr do
      return none
    let ty ←
      lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis b.checkedTypeExpr
    let id := freshLFModelLocalIdent b.name M locals reservedTheoremLocals
    let binder ← lfRenderedBinderSyntax {
      name := id.getId
      typeStx := ty
      visibility := b.visibility
    }
    theoremBinders := theoremBinders.push binder
    if let some head := b.head? then
      if head.kind == .judgment then
        localAssumptionNames := localAssumptionNames.insert b.name.eraseMacroScopes id.getId
    locals := (b.name, id) :: locals
  let some body ←
    lfDerivationTermSyntax? checked fieldNames defValues paramVis blockingUntyped
      sidePredicateNames certParamNames localAssumptionNames M locals t.name #[] derivation
    | return none
  unless lfExprRenderableInModel defValues blockingUntyped sidePredicateNames t.checkedJudgmentExpr
    do
    return none
  let theoremId := mkIdent outputName
  let structTy := mkIdent structureName
  let mut certBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for certId in certParamIds, certTy in certParamTypes do
    certBinders := certBinders.push (← lfRenderedBinderSyntax { name := certId.getId, typeStx :=
      certTy })
  let ty ←
    lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis
      t.checkedJudgmentExpr
  let modelBinder ← lfRenderedBinderSyntax { name := M.getId, typeStx := structTy }
  let cmd ←
    `(command| /-- Derived LF theorem generated by replaying a checked LF derivation over the model
      interface. -/
    def $theoremId:ident $modelBinder:bracketedBinder $certBinders:bracketedBinder*
      $theoremBinders:bracketedBinder* : $ty := $body)
  pure (some cmd.raw)

/-- Syntax-level LF object definition transported over a concrete model instance, using a
chosen generated Lean declaration name. -/
def lfObjectDefInterpretationSyntaxAs? (checked : CheckedSignature) (structureName outputName :
  Name)
    (d : CheckedLFObjectDef) (admittedNames : NameSet := {}) : CommandElabM (Option Syntax) := do
  let (renderable, _) := lfObjectDefTransportStatus checked d
  unless renderable do
    return none
  let obs ← validateLFModelObligations checked admittedNames
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let M := mkIdent `M
  let defId := mkIdent outputName
  let structTy := mkIdent structureName
  let ty ←
    lfExprSyntaxInModelInstanceWithFields fieldNames defValues M [] paramVis d.checkedTypeExpr
  let body ← lfExprSyntaxInModelInstanceWithFields fieldNames defValues M [] paramVis d.checkedValue
  let cmd ← `(command| /-- LF object definition transported over the model interface. -/
    def $defId:ident ($M:ident : $structTy) : $ty := $body)
  pure (some cmd.raw)

/-- Syntax-level derived LF theorem generated by replaying a checked LF derivation over a model. -/
def lfJudgmentTheoremInterpretationSyntax? (checked : CheckedSignature) (structureName : Name)
    (t : CheckedLFJudgmentTheorem) (admittedNames : NameSet := {}) : CommandElabM (Option Syntax) :=
  lfJudgmentTheoremInterpretationSyntaxAs? checked structureName t.name t admittedNames

/-- Commands for all LF judgment theorems whose derivations can currently be replayed over a model.
-/
def lfJudgmentTheoremInterpretationSyntaxes (checked : CheckedSignature) (structureName : Name)
    (admittedNames : NameSet := {}) : CommandElabM (Array Syntax) := do
  let mut out := #[]
  for t in checked.lfJudgmentTheorems do
    if let some cmd ←
      lfJudgmentTheoremInterpretationSyntax? checked structureName t admittedNames then
      out := out.push cmd
  pure out

/-- Diagnostic summary for LF theorem replay into derived model declarations. -/
def lfModelDerivedTheoremSummaryString (checked : CheckedSignature) : String :=
  let derivable := checked.lfJudgmentTheorems.foldl (init := 0) fun n t =>
    let (_, renderable, _) := lfJudgmentTheoremObligationStatus checked t
    if renderable then n + 1 else n
  s!"LF derived theorem replay for {nameString checked.name}: " ++
    s!"{derivable}/{checked.lfJudgmentTheorems.size} checked judgment theorem(s) " ++
    "have checked kernel replay artifacts, renderable statements, and " ++
    "renderable side-condition certificate parameters"

/-- Generated transport names used by the UX-level model workflow commands. They avoid
collisions with Lean-visible internal declaration anchors such as `T.f`. -/
def modelTransportDeclName (structureName sourceName : Name) : Name :=
  Name.mkSimple s!"{sourceName.eraseMacroScopes}_for_{structureName.eraseMacroScopes}"

/-- Whether an admission's annotation is headed by a checked LF judgment. -/
def isLFJudgmentAdmission (checked : CheckedSignature) (a : InternalAdmission) : Bool :=
  if a.kind != .judgmentTheorem then
    false
  else
    let (head, _) := splitObjApp a.typeExpr
    match head with
    | .ident n => checked.lfJudgments.any (fun j => j.name.eraseMacroScopes == n.eraseMacroScopes)
    | _ => false

/-- Render the model type of an admitted LF judgment statement, if applicable. -/
def admittedLFJudgmentTypeSyntax? (checked : CheckedSignature) (modelIdent : Ident)
    (a : InternalAdmission) : CommandElabM (Option (TSyntax `term)) := do
  unless isLFJudgmentAdmission checked a do
    return none
  let obs ← validateLFModelObligations checked
  let fieldNames := lfModelFieldNameMap obs
  let paramVis := lfParamVisibilityMapOfObligations obs
  let defValues := lfDefinitionValueMap checked
  let mut locals : LFLocalSyntaxCtx := []
  let mut binders : Array LFRenderedBinder := #[]
  for p in a.params do
    let ty ←
      lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals paramVis
        p.typeExpr
    let id := freshLFModelLocalIdent p.name modelIdent locals
    binders := binders.push { name := id.getId, typeStx := ty, visibility := p.visibility }
    locals := (p.name, id) :: locals
  let result ← lfObjExprSyntaxInModelInstanceWithFields fieldNames defValues modelIdent locals
    paramVis a.typeExpr
  some <$> lfRenderedTelescopeSyntax binders result

/-- Syntax-level model declaration for an admitted internal declaration. The statement is
rendered in the chosen model backend, while the body intentionally uses Lean `sorry`, making
the resulting dependency visible to Lean axiom tracking as `sorryAx`. -/
def admittedModelInterpretationSyntax (checked : CheckedSignature) (structureName outputName : Name)
    (a : InternalAdmission) : CommandElabM Syntax := do
  let M := mkIdent `M
  let structTy := mkIdent structureName
  let defId := mkIdent outputName
  let ty ←
    match checked.lfOpaqueConsts.find? (fun c =>
      c.name.eraseMacroScopes == a.declName.eraseMacroScopes) with
    | some c =>
        match c.checkedTypeExpr? with
        | some checkedType =>
            let obs ← validateLFModelObligations checked
            let fieldNames := lfModelFieldNameMap obs
            let paramVis := lfParamVisibilityMapOfObligations obs
            let defValues := lfDefinitionValueMap checked
            let mut locals : LFLocalSyntaxCtx := []
            let mut binders : Array LFRenderedBinder := #[]
            for p in c.params do
              let ty ←
                lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis
                  p.checkedTypeExpr
              let id := freshLFModelLocalIdent p.name M locals
              binders := binders.push { name := id.getId, typeStx := ty, visibility :=
                p.visibility }
              locals := (p.name, id) :: locals
            let result ←
              lfExprSyntaxInModelInstanceWithFields fieldNames defValues M locals paramVis
                checkedType
            lfRenderedTelescopeSyntax binders result
        | none =>
            throwError "admitted LF opaque '{a.declName}' has no checked type expression"
    | none =>
        match ← admittedLFJudgmentTypeSyntax? checked M a with
        | some ty => pure ty
        | none =>
            throwError "admitted internal declaration '{a.declName}' is not a typed LF opaque or \
              LF judgment admission"
  `(command| /-- Model interpretation of an admitted internal declaration; body intentionally uses
    `sorry`. -/
    def $defId:ident ($M:ident : $structTy) : $ty := by
      exact sorry)

/-- Concise UX-level theory/replay/model status summary. -/
def theoryWorkflowSummaryString (sig : HLSignature) (checked : CheckedSignature)
    (admissions transports : Nat) : String :=
  let lfTheorems := checked.lfJudgmentTheorems.size
  String.intercalate "\n" #[
    "type theory " ++ nameString sig.name ++ ": direct-LF signature",
    s!"Lean-visible anchor: {nameString (theoryAnchorName sig.name)}",
    "internal declarations: " ++
      toString (sig.lfObjectDefs.size + sig.lfJudgmentTheorems.size) ++
      s!" checked/replayed, {admissions} admitted by `sorry`",
    "LF metadata: " ++
      s!"{checked.lfSyntaxSorts.size} syntax sort(s), " ++
      s!"{checked.lfSyntaxAbbrevs.size} syntax abbreviation(s), " ++
      s!"{checked.lfJudgmentAbbrevs.size} judgment abbreviation(s), " ++
      s!"{checked.lfJudgments.size} judgment(s), {checked.lfRules.size} rule(s), " ++
      s!"{lfTheorems} checked judgment theorem(s)",
    s!"generated admitted transports recorded: {transports}",
    "user workflow: `#print_model_obligations`, `generate_model_interface`, \
      `#print_model_template`, `#print_model_transport_status`, `generate_model_transport`, \
        `generate_model_transports`"
  ].toList

/-- User-facing name for the model backend used by short UX commands. -/
def uxModelBackendLabel : String := "generic LF-model backend"

/-- Concise user-facing model-obligation summary for the LF model backend. -/
def modelObligationsUXString (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : CommandElabM String := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let summary := lfModelObligationSummaryString checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let derived := obs.filter (fun o => o.generatedRole == .derivedDeclaration && o.renderable)
  let params := obs.filter (fun o => o.generatedRole == .derivedParameter && o.renderable)
  let omitted := obs.filter (fun o => o.generatedRole == .omitted || !o.renderable)
  let group (title : String) (xs : Array LFModelObligation) : Array String :=
    if xs.isEmpty then #[s!"{title}: none"]
    else #[s!"{title}:"] ++ xs.map (fun o =>
      let note := match o.diagnostic? with
        | some d => s!" ({d})"
        | none => ""
      s!"  {nameString ((o.generatedName?).getD o.name)} ← {o.source.label} {nameString o.name}: \
        {o.statusLabel}{note}")
  let interfaceCmd := if mode == .publicMode then "#print_public_model_interface" else
    "#print_model_interface"
  let nextAction :=
    if fields.isEmpty then
      s!"next action: inspect blocked items with `#print_lf_model_omissions \
        {nameString checked.name}`"
    else if mode == .publicMode then
      s!"next action: run `{interfaceCmd} {nameString checked.name} as <Name>`, then fill the \
        {fields.size} user field(s); checked LF definitions/theorems can be generated afterward \
          when their dependencies remain public with `#print_model_transports`."
    else
      s!"next action: run `#print_model_interface {nameString checked.name} as <Name>`, then fill \
        the {fields.size} user field(s); checked LF definitions/theorems can be generated \
          afterward with `#print_model_transports`."
  let modeText := if mode == .full then uxModelBackendLabel else
    s!"{uxModelBackendLabel}, {mode.label} mode"
  let warningLines :=
    match lfModelTemporaryAdmissionWarningStringFromObligations checked obs with
    | some warning => [s!"WARNING: {warning}"]
    | none => []
  pure <| String.intercalate "\n" <|
    ([s!"model obligations for {nameString checked.name} ({modeText})", summary,
      s!"field breakdown: {lfModelFieldSourceBreakdown obs}", nextAction] ++ warningLines ++
      (group "fields to provide" fields).toList ++
      (group "derived declarations generated from replay" derived).toList ++
      (group "theorem-local certificate parameters" params).toList ++
      (group "blocked/omitted" omitted).toList)

/-- User-facing summary of generated model-interface sections. -/
def modelSectionsUXString (checked : CheckedSignature) (admittedNames : NameSet := {})
    (mode : LFModelInterfaceMode := .full) : CommandElabM String := do
  let obs ← validateLFModelObligations checked admittedNames mode
  let runs := lfModelSectionRuns checked obs
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let declared :=
    if checked.modelSections.isEmpty then "none"
    else String.intercalate ", " (checked.modelSections.toList.map fun s => nameString s.name)
  let mut lines := #[s!"model sections for {nameString checked.name} ({mode.label} mode)",
    s!"declared sections: {declared}",
    s!"renderable fields: {fields.size}; emitted section run(s): {runs.size}",
    "sectioned interfaces preserve dependency order; if section dependencies cross, a section may \
      be split into multiple runs",
    "oversized section runs are still chunked with `extends`, preserving the large-interface \
      optimization"]
  for run in runs do
    let label := if run.occurrence <= 1 then nameString run.sectionName else
      s!"{nameString run.sectionName} (part {run.occurrence})"
    lines := lines.push s!"  {label}: {run.fields.size} field(s)"
    for o in run.fields.take 12 do
      lines :=
        lines.push s!"    {nameString ((o.generatedName?).getD o.name)} ← {o.source.label} \
          {nameString o.name}"
    if run.fields.size > 12 then
      lines := lines.push s!"    ... {run.fields.size - 12} more field(s)"
  pure (String.intercalate "\n" lines.toList)

/-- One fillable template field block. -/
def templateFieldLines (source generated role details doc : String) : Array String :=
  #[s!"  /- must provide ({role}): {source}",
    s!"     {details}",
    s!"     source doc: {doc} -/",
    s!"  {generated} := by",
    s!"    exact ?{generated}"]

/-- One-line doc/comment block for a non-field item in a fillable model template. -/
def templateNonFieldLine (o : LFModelObligation) (doc : String) : Array String :=
  let generated := nameString ((o.generatedName?).getD o.name)
  let source := s!"{o.source.label} {nameString o.name}"
  let visibility := if o.visibility == .public_ then "" else s!", visibility={o.visibility.label}"
  let note := match o.diagnostic? with
    | some d => s!", note={d}"
    | none => ""
  #[s!"  --   {o.generatedRole.label}: {generated} ← {source}{visibility}{note}",
    s!"  --      source doc: {doc}"]

/-- Fillable Lean source template for the selected UX model backend. -/
def modelTemplateString (theoryName structureName : Name) (checked : CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM String :=
      do
  let mut lines :=
    #[s!"/- Fillable model template for {nameString theoryName} using {uxModelBackendLabel} \
      ({mode.label} mode).",
    "   Paste this near your model, replace each hole, then run the check/generation commands. -/",
    s!"def {nameString structureName.eraseMacroScopes}Example : \
      {nameString (theoryName ++ structureName)} where"]
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let nonFields := obs.filter (fun o => o.generatedRole != .field && o.generatedRole != .omitted
    && o.renderable)
  let omitted := obs.filter (fun o => o.generatedRole == .omitted || !o.renderable)
  lines :=
    lines.push s!"  -- must provide: {fields.size} field(s) ({lfModelFieldSourceBreakdown obs})"
  lines :=
    lines.push s!"  -- generated/non-field after checking: {nonFields.size} item(s); \
      blocked/omitted in this mode: {omitted.size}"
  if let some warning := lfModelTemporaryAdmissionWarningStringFromObligations checked obs then
    lines := lines.push s!"  -- WARNING: {warning.replace "\n" "\n  -- "}"
  if !checked.lfSyntaxAbbrevs.isEmpty || !checked.lfJudgmentAbbrevs.isEmpty then
    lines :=
      lines.push "  -- derived notation (non-field LF abbreviation item(s), expanded before model \
        obligations)"
    for a in checked.lfSyntaxAbbrevs do
      let params := String.intercalate " " (a.params.toList.map fun b =>
        s!"({nameString b.name} : {b.typeExpr})")
      let params := if params.isEmpty then "" else " " ++ params
      lines := lines.push s!"  --   syntax_abbrev {nameString a.name}{params} := {a.value}"
    for a in checked.lfJudgmentAbbrevs do
      let params := String.intercalate " " (a.params.toList.map fun b =>
        s!"({nameString b.name} : {b.typeExpr})")
      let params := if params.isEmpty then "" else " " ++ params
      lines := lines.push s!"  --   judgment_abbrev {nameString a.name}{params} := {a.value}"
  if fields.isEmpty then
    lines := lines.push "  -- no LF model fields were generated"
  else
    lines := lines.push "  -- required model fields"
  let mut lastSource? : Option LFModelObligationSource := none
  for o in fields do
    if lastSource? != some o.source then
      lines := lines.push s!"  -- {o.source.label} field(s)"
      lastSource? := some o.source
    let generated := nameString ((o.generatedName?).getD o.name)
    let source := s!"{o.source.label} {nameString o.name}"
    let implicitParams := o.params.foldl (init := 0) fun n p => if p.visibility == .implicit then
      n + 1 else n
    let typeSummary := match o.typeExpr? with
      | some e => checkedLFExprSummaryString e
      | none => match o.sourceObjExpr? with
        | some e => toString e
        | none => "not available"
    let note := match o.diagnostic? with
      | some d => s!", note={d}"
      | none => ""
    let details :=
      s!"params={o.paramCount} (implicit={implicitParams}), premises/evidence={o.premiseCount}, \
        side_conditions={o.sideConditionCount}, source_summary={typeSummary}{note}"
    let doc := match ← sourceDocForLFModelObligation? theoryName o with
      | some d => (trimCapturedDoc d).replace "\n" " "
      | none => "source documentation missing"
    lines := lines ++ templateFieldLines source generated o.generatedRole.label details doc
  if !nonFields.isEmpty then
    lines := lines.push "  -- generated/non-field items; not fields to fill by hand"
    lines :=
      lines.push "  -- run `#print_model_transports` / `generate_model_transports` after \
        filling required fields"
    let mut lastNonFieldRole? : Option LFModelGeneratedRole := none
    for o in nonFields do
      if lastNonFieldRole? != some o.generatedRole then
        lines := lines.push s!"  -- {o.generatedRole.label} item(s)"
        lastNonFieldRole? := some o.generatedRole
      let doc := match ← sourceDocForLFModelObligation? theoryName o with
        | some d => (trimCapturedDoc d).replace "\n" " "
        | none => "source documentation missing"
      lines := lines ++ templateNonFieldLine o doc
  if !omitted.isEmpty then
    lines := lines.push "  -- blocked/omitted items in this template mode"
    for o in omitted do
      let doc := match ← sourceDocForLFModelObligation? theoryName o with
        | some d => (trimCapturedDoc d).replace "\n" " "
        | none => "source documentation missing"
      lines := lines ++ templateNonFieldLine o doc
  lines := lines.push ""
  lines := lines.push "-- After filling the required fields, try:"
  let checkCmd := if mode == .publicMode then "#check_public_model_obligations" else
    "#check_model_obligations"
  lines := lines.push s!"--   {checkCmd} {nameString theoryName}"
  lines :=
    lines.push s!"--   #print_model_transport_status {nameString theoryName} for \
      {nameString structureName.eraseMacroScopes}"
  lines :=
    lines.push s!"--   #print_model_transports {nameString theoryName} for \
      {nameString structureName.eraseMacroScopes}"
  lines :=
    lines.push s!"--   generate_model_transports {nameString theoryName} for \
      {nameString structureName.eraseMacroScopes}"
  pure <| String.intercalate "\n" lines.toList

/-- Readable label for a dependency-ordered model-section run. -/
def lfModelSectionRunLabel (run : LFModelSectionRun) : String :=
  if run.occurrence <= 1 then nameString run.sectionName
  else s!"{nameString run.sectionName} (part {run.occurrence})"

/-- Parent-field name Lean creates for a generated `extends` parent. -/
def lfModelExtendsParentFieldName (parentName : Name) : Name :=
  let component :=
    (nameLastStringComponent? parentName.eraseMacroScopes).getD (toString
      parentName.eraseMacroScopes)
  Name.mkSimple s!"to{component}"

/-- Field count used when chunking one model-section bundle run. -/
def lfModelSectionRunChunkSize (run : LFModelSectionRun) : Nat :=
  if run.fields.isEmpty then 1
  else if lfModelSectionStructureChunkSize == 0 then run.fields.size
  else lfModelSectionStructureChunkSize

/-- Number of generated chunks for one model-section bundle run. -/
def lfModelSectionRunChunkCount (run : LFModelSectionRun) : Nat :=
  let chunkSize := lfModelSectionRunChunkSize run
  if run.fields.isEmpty then 1 else (run.fields.size + chunkSize - 1) / chunkSize

/-- Field slice owned by a generated chunk of one model-section bundle run. -/
def lfModelSectionRunChunkFields (run : LFModelSectionRun) (chunkIndex : Nat) :
  Array LFModelObligation :=
  let chunkSize := lfModelSectionRunChunkSize run
  let start := chunkIndex * chunkSize
  let stop := Nat.min run.fields.size (start + chunkSize)
  run.fields.extract start stop

/-- User-facing guide printed before true model-section bundle source. -/
def modelSectionBundleGuideString (checked : CheckedSignature) (bundleName flatName : Name)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM String :=
      do
  let obs ← validateLFModelObligations checked admittedNames mode
  let fields := obs.filter (fun o => o.generatedRole == .field && o.renderable)
  let omitted := obs.filter (fun o => o.generatedRole == .omitted || !o.renderable)
  let runs := lfModelSectionRuns checked obs
  let mut generatedRecords := 1 -- final bundle wrapper
  for run in runs do
    generatedRecords := generatedRecords + lfModelSectionRunChunkCount run
  let mut lines := #[
    s!"model-section bundle guide for {nameString checked.name} as {nameString bundleName}, \
      adapting {nameString flatName} ({mode.label} mode)",
    s!"user-provided fields: {fields.size} ({lfModelFieldSourceBreakdown obs}); blocked/omitted \
      in this mode: {omitted.size}",
    s!"emitted section run(s): {runs.size}; generated record(s), including final wrapper: \
      {generatedRecords}",
    "the generated records form an `extends` chain; later records may mention earlier projections \
      directly",
    s!"adapter: {nameString bundleName}.{nameString (lfModelToFlatAdapterName flatName)} turns \
      the final bundle into {nameString flatName}",
    s!"section templates: use `#print_model_section_template {nameString checked.name} <Section> \
      as {nameString bundleName}` for fillable per-section field blocks"
  ]
  for run in runs.take 12 do
    let chunkCount := lfModelSectionRunChunkCount run
    let chunkText := if chunkCount <= 1 then "" else s!", chunked into {chunkCount} record(s)"
    lines := lines.push s!"  {lfModelSectionRunLabel run}: {run.fields.size} field(s){chunkText}"
  if runs.size > 12 then
    lines := lines.push s!"  ... {runs.size - 12} more section run(s)"
  if fields.size > 200 then
    lines :=
      lines.push "large-interface note: generated source follows and may be long; prefer section \
        templates while authoring fields."
  pure <| String.intercalate "\n" lines.toList

/-- Fillable Lean source template for one theory-local model-section bundle run. -/
def modelSectionTemplateString (theoryName sectionName bundleName : Name) (checked :
  CheckedSignature)
    (admittedNames : NameSet := {}) (mode : LFModelInterfaceMode := .full) : CommandElabM String :=
      do
  let obs ← validateLFModelObligations checked admittedNames mode
  let sectionMap := lfModelSectionMap checked
  let runs := lfModelSectionRuns checked obs
  let target := sectionName.eraseMacroScopes
  let selectedRuns := runs.filter (fun run => run.sectionName.eraseMacroScopes == target)
  let nonFields := obs.filter (fun o =>
    o.generatedRole != .field && o.generatedRole != .omitted && o.renderable &&
      (lfModelSectionOfObligation sectionMap o).eraseMacroScopes == target)
  let omitted := obs.filter (fun o =>
    (o.generatedRole == .omitted || !o.renderable) &&
      (lfModelSectionOfObligation sectionMap o).eraseMacroScopes == target)
  if selectedRuns.isEmpty && nonFields.isEmpty && omitted.isEmpty then
    let available :=
      if runs.isEmpty then "none"
      else String.intercalate ", " ((runs.map (fun run =>
        nameString run.sectionName)).toList.eraseDups)
    throwError "no model-section obligations found for section '{sectionName}' in type theory \
      '{theoryName}'; available emitted section names: {available}"
  let fields := selectedRuns.foldl (init := #[]) fun acc run => acc ++ run.fields
  let commandPrefix := if mode == .publicMode then "public_" else ""
  let mut lines := #[
    s!"/- Fillable model-section template for {nameString theoryName}, section \
      {nameString sectionName} ({mode.label} mode).",
    s!"   Target bundle prefix: {nameString bundleName}.",
    s!"   Generate the real section records with `generate_{commandPrefix}model_section_bundles \
      {nameString theoryName} as {nameString bundleName} adapting <FlatInterface>`.",
    s!"   Section fields: {fields.size} ({lfModelFieldSourceBreakdown fields}); \
      generated/non-field: {nonFields.size}; blocked/omitted: {omitted.size}.",
    "   Fill the parent field first when this section extends an earlier generated record. -/"
  ]
  let mut parent? : Option Name := none
  for run in runs do
    let chunkCount := lfModelSectionRunChunkCount run
    for chunkIndex in [:chunkCount] do
      let structName := lfModelBundleRunChunkStructureName bundleName run chunkIndex chunkCount
      let chunkFields := lfModelSectionRunChunkFields run chunkIndex
      if run.sectionName.eraseMacroScopes == target then
        let structType := theoryName ++ structName
        let exampleName := nameWithLastComponentSuffix structName "Example"
        lines := lines.push ""
        lines :=
          lines.push s!"/- Section run: {lfModelSectionRunLabel run}; generated record: \
            {nameString structType}; chunk {chunkIndex + 1}/{chunkCount}. -/"
        lines := lines.push s!"def {nameString exampleName} : {nameString structType} where"
        match parent? with
        | none =>
            lines := lines.push "  -- no parent section is required for this first record"
        | some parent =>
            let parentField := lfModelExtendsParentFieldName parent
            lines :=
              lines.push s!"  -- parent section required by the generated `extends` chain: \
                {nameString (theoryName ++ parent)}"
            lines := lines.push s!"  {nameString parentField} := by"
            lines := lines.push s!"    exact ?{nameString parentField}"
        if chunkFields.isEmpty then
          lines := lines.push "  -- no fields are owned by this emitted record"
        else
          lines :=
            lines.push s!"  -- must provide: {chunkFields.size} field(s) in this record \
              ({lfModelFieldSourceBreakdown chunkFields})"
          let mut lastSource? : Option LFModelObligationSource := none
          for o in chunkFields do
            if lastSource? != some o.source then
              lines := lines.push s!"  -- {o.source.label} field(s)"
              lastSource? := some o.source
            let generated := nameString ((o.generatedName?).getD o.name)
            let source := s!"{o.source.label} {nameString o.name}"
            let implicitParams := o.params.foldl (init := 0) fun n p =>
              if p.visibility == .implicit then n + 1 else n
            let typeSummary := match o.typeExpr? with
              | some e => checkedLFExprSummaryString e
              | none => match o.sourceObjExpr? with
                | some e => toString e
                | none => "not available"
            let details :=
              s!"params={o.paramCount} (implicit={implicitParams}), \
                premises/evidence={o.premiseCount}, side_conditions={o.sideConditionCount}, \
                  source_summary={typeSummary}"
            let doc := match ← sourceDocForLFModelObligation? theoryName o with
              | some d => (trimCapturedDoc d).replace "\n" " "
              | none => "source documentation missing"
            lines := lines ++ templateFieldLines source generated o.generatedRole.label details doc
      parent? := some structName
  if !nonFields.isEmpty then
    lines := lines.push ""
    lines :=
      lines.push "-- Generated/non-field items assigned to this section; these are not fields to \
        fill by hand."
    for o in nonFields do
      let doc := match ← sourceDocForLFModelObligation? theoryName o with
        | some d => (trimCapturedDoc d).replace "\n" " "
        | none => "source documentation missing"
      lines := lines ++ templateNonFieldLine o doc
  if !omitted.isEmpty then
    lines := lines.push ""
    lines :=
      lines.push s!"-- Compatibility/internal/blocked items assigned to this section in \
        {mode.label} mode."
    for o in omitted do
      let doc := match ← sourceDocForLFModelObligation? theoryName o with
        | some d => (trimCapturedDoc d).replace "\n" " "
        | none => "source documentation missing"
      lines := lines ++ templateNonFieldLine o doc
  lines := lines.push ""
  lines := lines.push "-- Useful follow-up commands:"
  let cmdPrefix := commandPrefix
  lines := lines.push s!"--   #print_{cmdPrefix}model_sections {nameString theoryName}"
  lines :=
    lines.push s!"--   #print_{cmdPrefix}model_section_bundles {nameString theoryName} as \
      {nameString bundleName} adapting <FlatInterface>"
  lines :=
    lines.push s!"--   generate_{cmdPrefix}model_section_bundles {nameString theoryName} as \
      {nameString bundleName} adapting <FlatInterface>"
  pure <| String.intercalate "\n" lines.toList

/-- Status of declarations that the UX-level transport command can currently generate. -/
def modelTransportStatusString (theoryName structureName : Name) (checked : CheckedSignature)
    (admissions : Array InternalAdmission) : String := Id.run do
  let mut lines :=
    #[s!"model transport status for {nameString theoryName} using {nameString structureName}"]
  lines := lines.push "checked LF definitions/theorems: direct-LF artifact source"
  let lfDefRenderable := checked.lfObjectDefs.foldl (init := 0) fun n d =>
    let (ok, _) := lfObjectDefTransportStatus checked d
    if ok then n + 1 else n
  lines :=
    lines.push s!"LF object definitions: {lfDefRenderable}/{checked.lfObjectDefs.size} renderable \
      as model-interface methods"
  for d in checked.lfObjectDefs do
    let (ok, diag?) := lfObjectDefTransportStatus checked d
    let status := if ok then
      s!"→ {nameString (structureName ++ d.name)} (dot: M.{nameString d.name})" else
      s!"blocked: {(diag?).getD "not renderable"}"
    lines := lines.push s!"  lf_def {nameString d.name} {status}"
  let lfRenderable := checked.lfJudgmentTheorems.foldl (init := 0) fun n t =>
    let (_, ok, _) := lfJudgmentTheoremObligationStatus checked t
    if ok then n + 1 else n
  lines :=
    lines.push s!"LF judgment theorems: {lfRenderable}/{checked.lfJudgmentTheorems.size} \
      renderable as model-interface methods"
  for t in checked.lfJudgmentTheorems do
    let (_, ok, diag?) := lfJudgmentTheoremObligationStatus checked t
    let status := if ok then
      s!"→ {nameString (structureName ++ t.name)} (dot: M.{nameString t.name})" else
      s!"blocked: {(diag?).getD "not renderable"}"
    lines := lines.push s!"  {nameString t.name} {status}"
  if admissions.isEmpty then
    lines := lines.push "admitted internal declarations: none"
  else
    let admittedNames := internalAdmissionNameSet admissions
    let tempFields := lfModelTemporaryAdmissionFieldNames checked admittedNames
    lines :=
      lines.push s!"admitted internal declarations: {admissions.size}; generated transports use \
        Lean `sorry`/`sorryAx` visibly unless the admission is already a temporary model field"
    for a in admissions do
      let isLF :=
        checked.lfOpaqueConsts.any (fun c =>
          c.name.eraseMacroScopes == a.declName.eraseMacroScopes && c.checkedTypeExpr?.isSome) ||
          isLFJudgmentAdmission checked a
      let kind := a.kind.label
      if tempFields.contains a.declName.eraseMacroScopes then
        lines :=
          lines.push s!"  admitted {kind} {nameString a.declName} is a temporary \
            admitted-definition model field (dot: M.{nameString a.declName}; no transport needed)"
      else if isLF then
        lines :=
          lines.push s!"  admitted {kind} {nameString a.declName} → \
            {nameString (structureName ++ a.declName)} (dot: M.{nameString a.declName}; Lean \
              sorry-backed method)"
      else
        lines :=
          lines.push s!"  admitted {kind} {nameString a.declName} → \
            {nameString (modelTransportDeclName structureName a.declName)}"
  return String.intercalate "\n" lines.toList

end LeanTypeModelGeneration

end InternalLean
