/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab.Core

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

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
      out := some { params := s.params, result? := some (objExprTypeOfLevel s.resultLevel) }
  for a in sig.syntaxAbbrevs do
    if a.name.eraseMacroScopes == name then
      out := some { params := a.params, result? := some a.value }
  for d in sig.syntaxDefs do
    if d.name.eraseMacroScopes == name then
      out := some { params := d.params, result? := some (objExprTypeOfLevel d.resultLevel) }
  for a in sig.judgmentAbbrevs do
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

/-- Map-based callable-head lookup for repeated implicit-argument elaboration. -/
structure ImplicitCallableLookupContext where
  /-- Callable LF heads and their implicit-argument metadata. -/
  callableInfos : NameMap ImplicitCallableInfo := {}
  deriving Inhabited, Repr

/-- Build map-based callable-head lookup data for implicit-argument elaboration. -/
def mkImplicitCallableLookupContext (sig : HLSignature) : ImplicitCallableLookupContext :=
  Id.run do
  let mut callableInfos : NameMap ImplicitCallableInfo := {}
  for s in sig.syntaxSorts do
    callableInfos := callableInfos.insert s.name.eraseMacroScopes {
      params := s.params, result? := some (objExprTypeOfLevel s.resultLevel) }
  for a in sig.syntaxAbbrevs do
    callableInfos := callableInfos.insert a.name.eraseMacroScopes {
      params := a.params, result? := some a.value }
  for d in sig.syntaxDefs do
    callableInfos := callableInfos.insert d.name.eraseMacroScopes {
      params := d.params, result? := some (objExprTypeOfLevel d.resultLevel) }
  for a in sig.judgmentAbbrevs do
    callableInfos := callableInfos.insert a.name.eraseMacroScopes {
      params := a.params, result? := some a.value }
  for j in sig.judgments do
    callableInfos := callableInfos.insert j.name.eraseMacroScopes { params := j.params }
  for o in sig.lfOpaqueConsts do
    if let some typeExpr := o.typeExpr? then
      callableInfos := callableInfos.insert o.name.eraseMacroScopes {
        params := o.params, result? := some typeExpr }
  for r in sig.rules do
    callableInfos := callableInfos.insert r.name.eraseMacroScopes {
      params := r.params
      result? := some r.conclusionExpr
      -- Rule proofs explicitly supply premise derivations. Side-condition certificates are
      -- synthesized by checked side-condition hooks during LF replay, not source args.
      trailingExplicitArgs := r.premises.size }
  for d in sig.lfObjectDefs do
    callableInfos := callableInfos.insert d.name.eraseMacroScopes {
      params := #[], result? := some d.typeExpr }
  for t in sig.lfJudgmentTheorems do
    callableInfos := callableInfos.insert t.name.eraseMacroScopes {
      params := #[], result? := some t.judgmentExpr }
  return { callableInfos }

/-- Map-based callable-head lookup. -/
def findImplicitCallableInfoIn? (lookup : ImplicitCallableLookupContext) (name : Name) :
    Option ImplicitCallableInfo :=
  lookup.callableInfos.find? name.eraseMacroScopes

/-- Implicit variables associated to a callable telescope. -/
def implicitVarsOfParams (params : Array HLBinding) : NameSet := Id.run do
  let mut vars : NameSet := {}
  for p in params do
    if p.visibility == .implicit then
      vars := vars.insert p.name.eraseMacroScopes
  return vars

/-- One source callable parameter freshened for a single implicit-inference problem. -/
structure FreshImplicitParam where
  sourceName : Name
  freshName : Name
  visibility : BinderVisibility
  sourceTypeExpr : ObjExpr
  typeExpr : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Implicit variables associated to a freshened callable telescope. -/
def implicitVarsOfFreshParams (params : Array FreshImplicitParam) : NameSet := Id.run do
  let mut vars : NameSet := {}
  for p in params do
    if p.visibility == .implicit then
      vars := vars.insert p.freshName.eraseMacroScopes
  return vars

/-- Names to avoid when freshening one callable-head telescope for implicit inference. -/
def implicitFreshAvoidSet (sig : HLSignature) (knownTypes : LFLocalTypes) (locals : NameSet)
    (info : ImplicitCallableInfo) (rawArgs : Array ObjExpr) (expected? : Option ObjExpr) :
    NameSet := Id.run do
  let mut avoid := sig.nameSet ++ locals
  for (n, ty) in knownTypes.toList do
    avoid := avoid.insert n.eraseMacroScopes
    avoid := avoid ++ freeLFObjectIdentifiers ty
  for p in info.params do
    avoid := avoid.insert p.name.eraseMacroScopes
    avoid := avoid ++ freeLFObjectIdentifiers p.typeExpr
  if let some result := info.result? then
    avoid := avoid ++ freeLFObjectIdentifiers result
  for arg in rawArgs do
    avoid := avoid ++ freeLFObjectIdentifiers arg
  if let some expected := expected? then
    avoid := avoid ++ freeLFObjectIdentifiers expected
  return avoid

/-- Whether a name is one of the internal fresh implicit-inference names. -/
partial def isImplicitFreshName : Name → Bool
  | .anonymous => false
  | .str parent _ => parent == `_ilImplicit || isImplicitFreshName parent
  | .num parent _ => isImplicitFreshName parent

/-- Deterministic internal name for one fresh implicit-inference parameter. -/
def freshImplicitParamName (idx : Nat) (avoid : NameSet) : Name :=
  freshLFNameAvoiding (.str `_ilImplicit s!"p{idx}") avoid

/-- Whether an expression mentions an implicit-inference fresh name not owned by this
application. -/
def objExprMentionsForeignImplicitFresh (vars : NameSet) (e : ObjExpr) : Bool :=
  (freeLFObjectIdentifiers e).toList.any fun n =>
    isImplicitFreshName n && !vars.contains n.eraseMacroScopes

/-- Alpha-freshen one callable telescope so nested heads with the same source binder names do not
share one implicit-inference metavariable namespace. -/
def freshImplicitCallableParams (sig : HLSignature) (knownTypes : LFLocalTypes)
    (locals : NameSet) (info : ImplicitCallableInfo) (rawArgs : Array ObjExpr)
    (expected? : Option ObjExpr) :
    Array FreshImplicitParam × Option ObjExpr := Id.run do
  let mut avoid := implicitFreshAvoidSet sig knownTypes locals info rawArgs expected?
  let mut subst : NameMap ObjExpr := {}
  let mut out : Array FreshImplicitParam := #[]
  for h : i in [:info.params.size] do
    let p := info.params[i]
    let sourceName := p.name.eraseMacroScopes
    let freshName := freshImplicitParamName i avoid
    avoid := avoid.insert freshName.eraseMacroScopes
    let typeExpr := substLFParams subst p.typeExpr
    out := out.push {
      sourceName := sourceName
      freshName := freshName.eraseMacroScopes
      visibility := p.visibility
      sourceTypeExpr := p.typeExpr
      typeExpr := typeExpr }
    subst := subst.insert sourceName (.ident freshName.eraseMacroScopes)
  let result? := info.result?.map (substLFParams subst)
  return (out, result?)

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
  partial def elaborateImplicitAppsInExprWithLookup (lookup : ImplicitCallableLookupContext)
      (sig : HLSignature) (knownTypes : LFLocalTypes)
      (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
      (expected? : Option ObjExpr := none) : ObjExpr → CoreM ObjExpr
    | .ident n => do
        let nClean := n.eraseMacroScopes
        if locals.contains nClean then
          pure (.ident nClean)
        else
          match findImplicitCallableInfoIn? lookup nClean with
          | some info =>
            elaborateImplicitHeadAppWithLookup lookup sig knownTypes locals ownerKind ownerName
              where_ nClean info #[] expected?
          | none => pure (.ident nClean)
    | .sort => pure .sort
    | .univ u => pure (.univ u)
    | .arrow x A B => do
        let A ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        let locals := match x with
          | some x => locals.insert x.eraseMacroScopes
          | none => locals
        let B ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none B
        pure (.arrow (x.map Name.eraseMacroScopes) A B)
    | .funArrow x A B => do
        let A ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        let locals := match x with
          | some x => locals.insert x.eraseMacroScopes
          | none => locals
        let B ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none B
        pure (.funArrow (x.map Name.eraseMacroScopes) A B)
    | .sigma x A B => do
        let A ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        let locals := match x with
          | some x => locals.insert x.eraseMacroScopes
          | none => locals
        let B ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none B
        pure (.sigma (x.map Name.eraseMacroScopes) A B)
    | .pair a b => do
        let (expectedA?, expectedB?) :=
          match expected?.map eraseObjExprScopes with
          | some (.sigma binder? A B) =>
              let aForB := match binder? with
                | some x => some (fun a => substSingleLFParam x (eraseObjExprScopes a) B)
                | none => some (fun _ => B)
              (some A, aForB)
          | _ => (none, none)
        let a ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ expectedA? a
        let expectedB? := expectedB?.map (fun mk => mk a)
        let b ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ expectedB? b
        pure (.pair a b)
    | .fst e => do
        let e ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none e
        pure (.fst e)
    | .snd e => do
        let e ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none e
        pure (.snd e)
    | .lam xs body => do
        let clean := xs.map Name.eraseMacroScopes
        let locals := clean.foldl (fun locals x => locals.insert x) locals
        let body ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none body
        pure (.lam clean body)
    | .jeq lhs rhs => do
        let lhs ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none lhs
        let rhs ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            where_ none rhs
        pure (.jeq lhs rhs)
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
                args.mapM (elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals
                  ownerKind ownerName where_ none)
              pure (mkObjApp head args)
            else
              match findImplicitCallableInfoIn? lookup headName with
              | some info =>
                  let hasImplicit := info.params.any (fun p => p.visibility == .implicit)
                  if !hasImplicit && info.trailingExplicitArgs == 0
                    && args.size < info.params.size then
                    let args ←
                      args.mapM (elaborateImplicitAppsInExprWithLookup lookup sig knownTypes
                        locals ownerKind ownerName where_ none)
                    pure (mkObjApp (.ident headName) args)
                  else if info.params.isEmpty && info.trailingExplicitArgs == 0
                    && !args.isEmpty then
                    let args ←
                      args.mapM (elaborateImplicitAppsInExprWithLookup lookup sig knownTypes
                        locals ownerKind ownerName where_ none)
                    pure (mkObjApp (.ident headName) args)
                  else
                    elaborateImplicitHeadAppWithLookup lookup sig knownTypes locals ownerKind
                      ownerName where_ headName info args expected?
              | none =>
                  let head ←
                    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind
                      ownerName where_ none head
                  let args ←
                    args.mapM (elaborateImplicitAppsInExprWithLookup lookup sig knownTypes
                      locals ownerKind ownerName where_ none)
                  pure (mkObjApp head args)
        | _ =>
            let head ←
              elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind
                ownerName where_ none head
            let args ←
              args.mapM (elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals
                ownerKind ownerName where_ none)
            pure (mkObjApp head args)

  /-- Elaborate one known-head application, inserting omitted ordinary implicit arguments. -/
  partial def elaborateImplicitHeadAppWithLookup (lookup : ImplicitCallableLookupContext)
      (sig : HLSignature) (knownTypes : LFLocalTypes)
      (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
      (headName : Name) (info : ImplicitCallableInfo) (rawArgs : Array ObjExpr)
      (expected? : Option ObjExpr) : CoreM ObjExpr := do
    let (named, positional) ← collectNamedImplicitArgs ownerKind ownerName headName rawArgs
    let (params, result?) :=
      freshImplicitCallableParams sig knownTypes locals info rawArgs expected?
    let hasNamed := positional.size != rawArgs.size
    let fullPositional := !hasNamed
      && positional.size == params.size + info.trailingExplicitArgs
    let implicitVars := implicitVarsOfFreshParams params
    let mut subst : NameMap ObjExpr := {}
    let mut argsByParam : Array (Option ObjExpr) := (List.replicate params.size none).toArray
    let mut posIdx := 0
    if fullPositional then
      for h : i in [:params.size] do
        let param := params[i]
        let raw := positional[i]!
        let expectedParam := substLFParams subst param.typeExpr
        let arg ←
          elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
            s!"{where_} argument '{param.sourceName}' of \
              '{headName}'" (some expectedParam) raw
        argsByParam := argsByParam.set! i (some arg)
        subst := subst.insert param.freshName (eraseObjExprScopes arg)
      posIdx := params.size
    else
      for h : i in [:params.size] do
        let param := params[i]
        let pName := param.sourceName.eraseMacroScopes
        let expectedParam := substLFParams subst param.typeExpr
        match named.find? pName with
        | some rawNamed =>
            if param.visibility != .implicit then
              throwError "{ownerKind} '{ownerName}' supplies named implicit argument '{pName}' \
                for explicit parameter '{pName}' in application '{headName}'"
            let arg ←
              elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
                s!"{where_} named implicit argument '{pName}' of \
                  '{headName}'" (some expectedParam) rawNamed
            argsByParam := argsByParam.set! i (some arg)
            subst := subst.insert param.freshName (eraseObjExprScopes arg)
        | none =>
            if param.visibility == .implicit then
              pure ()
            else
              let some raw := positional[posIdx]?
                | throwError "{ownerKind} '{ownerName}' omits explicit argument '{pName}' in \
                  application '{headName}' in {where_}"
              posIdx := posIdx + 1
              let arg ←
                elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind
                  ownerName s!"{where_} argument '{pName}' of '{headName}'"
                  (some expectedParam) raw
              if let some actualType := inferKnownLFExprType? sig knownTypes arg then
                match matchImplicitObjectPattern implicitVars expectedParam actualType subst with
                | .ok subst' => subst := subst'
                | .error _ => pure ()
              argsByParam := argsByParam.set! i (some arg)
              subst := subst.insert param.freshName (eraseObjExprScopes arg)
      for (n, _) in named.toList do
        unless params.any (fun p => p.sourceName.eraseMacroScopes == n
          && p.visibility == .implicit) do
          throwError "{ownerKind} '{ownerName}' supplies unknown named implicit argument '{n}' in \
            application '{headName}'"
    if let some expected := expected? then
      if let some result := result? then
        let result := substLFParams subst result
        match matchImplicitObjectPattern implicitVars result expected subst with
        | .ok subst' => subst := subst'
        | .error err =>
            let hasForeignFresh :=
              objExprMentionsForeignImplicitFresh implicitVars expected ||
                objExprMentionsForeignImplicitFresh implicitVars result
            let allImplicitArgsSourceSupplied := fullPositional ||
              params.all fun p =>
                p.visibility != .implicit || (named.find? p.sourceName.eraseMacroScopes).isSome
            if implicitVars.isEmpty || allImplicitArgsSourceSupplied || hasForeignFresh then
              pure ()
            else
              throwError "{ownerKind} '{ownerName}' could not infer implicit arguments for \
                application '{headName}' in {where_} from expected expression\n  \
                  {expected}\nwhile matching result\n  {result}\nreason: {err}"
    let mut outArgs := #[]
    for h : i in [:params.size] do
      let param := params[i]
      let pName := param.sourceName.eraseMacroScopes
      match argsByParam[i]! with
      | some arg => outArgs := outArgs.push arg
      | none =>
          match subst.find? param.freshName with
          | some inferred => outArgs := outArgs.push (substLFParams subst inferred)
          | none =>
              throwError "{ownerKind} '{ownerName}' could not infer implicit argument '{pName} : \
                {param.sourceTypeExpr}' in application '{headName}' in {where_}; use a named \
                  implicit argument or supply all arguments explicitly"
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
      let arg ←
        elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
          where_ none raw
      outArgs := outArgs.push arg
    pure (mkObjApp (.ident headName) outArgs)
end

/-- Elaborate implicit applications in an object expression using a fresh lookup context. -/
def elaborateImplicitAppsInExpr (sig : HLSignature) (knownTypes : LFLocalTypes)
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
    (expected? : Option ObjExpr := none) (e : ObjExpr) : CoreM ObjExpr :=
  elaborateImplicitAppsInExprWithLookup (mkImplicitCallableLookupContext sig) sig knownTypes
    locals ownerKind ownerName where_ expected? e

/-- Elaborate implicit applications in a telescope, extending the local shallow-type context. -/
def elaborateImplicitAppsInBindingsWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (knownTypes : LFLocalTypes) (locals : NameSet) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) :
    CoreM (Array HLBinding × LFLocalTypes × NameSet) := do
  let mut out := #[]
  let mut knownTypes := knownTypes
  let mut locals := locals
  for b in bs do
    let typeExpr ←
      elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals ownerKind ownerName
        s!"parameter '{b.name.eraseMacroScopes}' type" none b.typeExpr
    let b := { b with name := b.name.eraseMacroScopes, typeExpr := typeExpr }
    out := out.push b
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes typeExpr)
    locals := locals.insert b.name.eraseMacroScopes
  pure (out, knownTypes, locals)

/-- Elaborate implicit applications in a telescope, extending the local shallow-type context. -/
def elaborateImplicitAppsInBindings (sig : HLSignature) (knownTypes : LFLocalTypes)
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) :
    CoreM (Array HLBinding × LFLocalTypes × NameSet) :=
  elaborateImplicitAppsInBindingsWithLookup (mkImplicitCallableLookupContext sig) sig knownTypes
    locals ownerKind ownerName bs

/-- Elaborate implicit applications in an LF syntax-sort declaration. -/
def elaborateImplicitAppsInSyntaxSortDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : SyntaxSortDecl) : CoreM SyntaxSortDecl := do
  let (params, _, _) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "syntax_sort" d.name d.params
  pure { d with params }

/-- Elaborate implicit applications in an LF syntax-sort declaration. -/
def elaborateImplicitAppsInSyntaxSortDecl (sig : HLSignature) (d : SyntaxSortDecl) :
    CoreM SyntaxSortDecl :=
  elaborateImplicitAppsInSyntaxSortDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in a syntax abbreviation declaration. -/
def elaborateImplicitAppsInSyntaxAbbrevDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : SyntaxAbbrevDecl) : CoreM SyntaxAbbrevDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "syntax_abbrev" d.name d.params
  let value ←
    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "syntax_abbrev" d.name
      "value" none d.value
  pure { d with params, value }

/-- Elaborate implicit applications in a syntax abbreviation declaration. -/
def elaborateImplicitAppsInSyntaxAbbrevDecl (sig : HLSignature) (d : SyntaxAbbrevDecl) :
    CoreM SyntaxAbbrevDecl :=
  elaborateImplicitAppsInSyntaxAbbrevDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in a syntax definition declaration. -/
def elaborateImplicitAppsInSyntaxDefDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : SyntaxDefDecl) : CoreM SyntaxDefDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "syntax_def" d.name d.params
  let value? ← match d.value? with
    | some value =>
        some <$> elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "syntax_def"
          d.name "value" (some (objExprTypeOfLevel d.resultLevel)) value
    | none => pure none
  pure { d with params, value? }

/-- Elaborate implicit applications in a syntax definition declaration. -/
def elaborateImplicitAppsInSyntaxDefDecl (sig : HLSignature) (d : SyntaxDefDecl) :
    CoreM SyntaxDefDecl :=
  elaborateImplicitAppsInSyntaxDefDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in a judgment abbreviation declaration. -/
def elaborateImplicitAppsInJudgmentAbbrevDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : JudgmentAbbrevDecl) : CoreM JudgmentAbbrevDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "judgment_abbrev" d.name d.params
  let value ←
    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "judgment_abbrev" d.name
      "value" none d.value
  pure { d with params, value }

/-- Elaborate implicit applications in a judgment abbreviation declaration. -/
def elaborateImplicitAppsInJudgmentAbbrevDecl (sig : HLSignature) (d : JudgmentAbbrevDecl) :
    CoreM JudgmentAbbrevDecl :=
  elaborateImplicitAppsInJudgmentAbbrevDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in an LF judgment declaration. -/
def elaborateImplicitAppsInJudgmentDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : JudgmentDecl) : CoreM JudgmentDecl := do
  let (params, _, _) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "judgment" d.name d.params
  pure { d with params }

/-- Elaborate implicit applications in an LF judgment declaration. -/
def elaborateImplicitAppsInJudgmentDecl (sig : HLSignature) (d : JudgmentDecl) :
    CoreM JudgmentDecl :=
  elaborateImplicitAppsInJudgmentDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in an LF opaque declaration. -/
def elaborateImplicitAppsInLFOpaqueConstDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (d : LFOpaqueConstDecl) : CoreM LFOpaqueConstDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "lf_opaque" d.name d.params
  let typeExpr? ← match d.typeExpr? with
    | some typeExpr =>
      some <$> elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "lf_opaque"
        d.name "result type" none typeExpr
    | none => pure none
  pure { d with params, typeExpr? }

/-- Elaborate implicit applications in an LF opaque declaration. -/
def elaborateImplicitAppsInLFOpaqueConstDecl (sig : HLSignature) (d : LFOpaqueConstDecl) :
    CoreM LFOpaqueConstDecl :=
  elaborateImplicitAppsInLFOpaqueConstDeclWithLookup (mkImplicitCallableLookupContext sig) sig d

/-- Elaborate implicit applications in an LF rule declaration. -/
def elaborateImplicitAppsInRuleDeclWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (r : RuleDecl) : CoreM RuleDecl := do
  let (params, knownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig {} {} "rule" r.name r.params
  let premises ← r.premises.mapM fun p => do
    let judgmentExpr ← elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "rule"
      r.name s!"premise '{p.name.eraseMacroScopes}'" none p.judgmentExpr
    pure { p with judgmentExpr }
  let sideConditions ← r.sideConditions.mapM fun sc => do
    let input ← elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "rule" r.name
      s!"side condition '{sc.name.eraseMacroScopes}'" none sc.input
    pure { sc with input }
  let paramEvidences ← r.paramEvidences.mapM fun ev => do
    let judgmentExpr ← elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "rule"
      r.name s!"evidence '{ev.name.eraseMacroScopes}'" none ev.judgmentExpr
    pure { ev with judgmentExpr }
  let conclusionExpr ←
    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes locals "rule" r.name
      "conclusion" none r.conclusionExpr
  pure { r with params, premises, sideConditions, paramEvidences, conclusionExpr }

/-- Elaborate implicit applications in an LF rule declaration. -/
def elaborateImplicitAppsInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM RuleDecl :=
  elaborateImplicitAppsInRuleDeclWithLookup (mkImplicitCallableLookupContext sig) sig r

/-- Elaborate implicit applications in an LF object definition. -/
def elaborateImplicitAppsInLFObjectDefWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (knownTypes : LFLocalTypes) (d : LFObjectDefDecl) :
    CoreM LFObjectDefDecl := do
  let typeExpr ←
    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes {} "lf_def" d.name "type" none
      d.typeExpr
  let value ←
    elaborateImplicitAppsInExprWithLookup lookup sig knownTypes {} "lf_def" d.name "value"
      (some typeExpr) d.value
  pure { d with typeExpr, value }

/-- Elaborate implicit applications in an LF object definition. -/
def elaborateImplicitAppsInLFObjectDef (sig : HLSignature) (knownTypes : LFLocalTypes)
    (d : LFObjectDefDecl) : CoreM LFObjectDefDecl :=
  elaborateImplicitAppsInLFObjectDefWithLookup (mkImplicitCallableLookupContext sig) sig
    knownTypes d

/-- Elaborate implicit applications in an LF judgment theorem. -/
def elaborateImplicitAppsInLFJudgmentTheoremWithLookup (lookup : ImplicitCallableLookupContext)
    (sig : HLSignature) (knownTypes : LFLocalTypes) (t : LFJudgmentTheoremDecl) :
    CoreM LFJudgmentTheoremDecl := do
  let (binders, theoremKnownTypes, locals) ←
    elaborateImplicitAppsInBindingsWithLookup lookup sig knownTypes {} "judgment_theorem" t.name
      t.binders
  let judgmentExpr ←
    elaborateImplicitAppsInExprWithLookup lookup sig theoremKnownTypes locals "judgment_theorem"
      t.name "statement" none t.judgmentExpr
  let proof ←
    elaborateImplicitAppsInExprWithLookup lookup sig theoremKnownTypes locals "judgment_theorem"
      t.name "proof" (some judgmentExpr) t.proof
  pure { t with binders, judgmentExpr, proof }

/-- Elaborate implicit applications in an LF judgment theorem. -/
def elaborateImplicitAppsInLFJudgmentTheorem (sig : HLSignature) (knownTypes : LFLocalTypes)
    (t : LFJudgmentTheoremDecl) : CoreM LFJudgmentTheoremDecl :=
  elaborateImplicitAppsInLFJudgmentTheoremWithLookup (mkImplicitCallableLookupContext sig) sig
    knownTypes t

/-- Elaborate implicit applications throughout a high-level signature, using `headSig` as the
callable-head environment. The returned signature is still ordinary explicit `ObjExpr` syntax;
implicit arguments have been inserted before checking. -/
def elaborateImplicitAppsInSignatureWithEnv (headSig sig : HLSignature) : CoreM HLSignature := do
  let sig0 := headSig
  let lookup0 := mkImplicitCallableLookupContext sig0
  let syntaxSorts ←
    sig.syntaxSorts.mapM (elaborateImplicitAppsInSyntaxSortDeclWithLookup lookup0 sig0)
  let syntaxAbbrevs ←
    sig.syntaxAbbrevs.mapM (elaborateImplicitAppsInSyntaxAbbrevDeclWithLookup lookup0 sig0)
  let syntaxDefs ←
    sig.syntaxDefs.mapM (elaborateImplicitAppsInSyntaxDefDeclWithLookup lookup0 sig0)
  let judgmentAbbrevs ←
    sig.judgmentAbbrevs.mapM
      (elaborateImplicitAppsInJudgmentAbbrevDeclWithLookup lookup0 sig0)
  let judgments ←
    sig.judgments.mapM (elaborateImplicitAppsInJudgmentDeclWithLookup lookup0 sig0)
  let lfOpaqueConsts ←
    sig.lfOpaqueConsts.mapM (elaborateImplicitAppsInLFOpaqueConstDeclWithLookup lookup0 sig0)
  let rules ← sig.rules.mapM (elaborateImplicitAppsInRuleDeclWithLookup lookup0 sig0)
  let sig1 := {
    sig with
    syntaxSorts := syntaxSorts
    syntaxAbbrevs := syntaxAbbrevs
    syntaxDefs := syntaxDefs
    judgmentAbbrevs := judgmentAbbrevs
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    rules := rules }
  let lookup1 := mkImplicitCallableLookupContext sig1
  let mut knownTypes : LFLocalTypes := {}
  let mut lfObjectDefs := #[]
  for d in sig.lfObjectDefs do
    let d ← elaborateImplicitAppsInLFObjectDefWithLookup lookup1 sig1 knownTypes d
    lfObjectDefs := lfObjectDefs.push d
    knownTypes := knownTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  let lfJudgmentTheorems ←
    sig.lfJudgmentTheorems.mapM
      (elaborateImplicitAppsInLFJudgmentTheoremWithLookup lookup1 sig1 knownTypes)
  pure { sig1 with lfObjectDefs, lfJudgmentTheorems }

/-- Elaborate implicit applications throughout a high-level signature using its own heads. -/
def elaborateImplicitAppsInSignature (sig : HLSignature) : CoreM HLSignature :=
  elaborateImplicitAppsInSignatureWithEnv sig sig

/-- Whether an expression mentions a named LF object definition from the signature. -/
partial def lfExprMentionsLFObjectDef (sig : HLSignature) : ObjExpr → Bool
  | .ident n => sig.lfObjectDefs.any (fun d => d.name.eraseMacroScopes == n.eraseMacroScopes)
  | .sort | .univ _ => false
  | .app f a => lfExprMentionsLFObjectDef sig f || lfExprMentionsLFObjectDef sig a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      lfExprMentionsLFObjectDef sig A || lfExprMentionsLFObjectDef sig B
  | .pair a b => lfExprMentionsLFObjectDef sig a || lfExprMentionsLFObjectDef sig b
  | .fst e | .snd e => lfExprMentionsLFObjectDef sig e
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
  | .sigma x A B => .sigma (x.map Name.eraseMacroScopes) (normalizeLFExprBetaOnly A) (
    normalizeLFExprBetaOnly B)
  | .pair a b => .pair (normalizeLFExprBetaOnly a) (normalizeLFExprBetaOnly b)
  | .fst e =>
      let e := normalizeLFExprBetaOnly e
      match e with
      | .pair a _ => a
      | _ => .fst e
  | .snd e =>
      let e := normalizeLFExprBetaOnly e
      match e with
      | .pair _ b => b
      | _ => .snd e
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

end InternalLean
