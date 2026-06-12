/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Lean

/-!
# Shared LF vocabulary and legacy raw compatibility

This file keeps shared universe, metavariable-sort, conversion-step, and trust-boundary vocabulary
used by InternalLean's logical-framework layer. It also contains the legacy raw replay syntax and
checker retained for low-level compatibility tests; registered LF theorem replay and executable
conversion-plugin checking now use the structural kernel in `InternalLean.Kernel`.

Design notes for the legacy raw layer:

* Object syntax is raw syntax. Object typing/equality is represented by explicit judgments and
  derivations.
* Object equality is not Lean equality and raw syntax is not quotiented by equality.
* Substitutions may appear either as theory-declared LF syntax/judgments or as the low-level raw
  constructors `tySubst`, `tmSubst`, `substId`, `substComp`, `substEmpty`, and `substExt`. The raw
  constructors carry only syntactic shape: replay checks their child constructor families and
  capture hazards, while source/target well-formedness must be supplied by LF rules, premises, or
  explicit evidence.
* Legacy raw rule schemas carry a metavariable context and side-condition slots. Current LF proof
  metadata is lowered to structural replay trees with scoped instantiations and checked certificate
  references.
-/

@[expose] public section

namespace InternalLean

open Lean

/-- Object-level universe expressions.

These are deliberately separate from Lean universe levels. The Lean-type backend may
later translate them to Lean level parameters, but the object checker tracks them in
its own syntax first. -/
inductive LevelExpr where
  /-- The universe level `0`. -/
  | zero : LevelExpr
  /-- A numeric universe level. `lit 0` is normalized to `zero` by constructors below. -/
  | lit : Nat → LevelExpr
  /-- A universe-level parameter such as `u`. -/
  | param : Name → LevelExpr
  /-- Successor universe level. -/
  | succ : LevelExpr → LevelExpr
  /-- Maximum of two universe levels. -/
  | max : LevelExpr → LevelExpr → LevelExpr
  deriving Inhabited, Repr, BEq

namespace LevelExpr

/-- Construct a numeric universe level. -/
def ofNat : Nat → LevelExpr
  | 0 => .zero
  | n => .lit n

/-- Translate an object universe expression to Lean's universe-level syntax.

The object level language is still separate from Lean's universe parameters, but Lean's
`Level.normalize` already implements the max/successor canonicalization we want to
imitate. We therefore translate through `Lean.Level` for normalization. -/
partial def toLeanLevel : LevelExpr → Lean.Level
  | .zero => .zero
  | .lit n => Lean.Level.ofNat n
  | .param u => .param u.eraseMacroScopes
  | .succ u => Lean.mkLevelSucc (toLeanLevel u)
  | .max u v => Lean.mkLevelMax (toLeanLevel u) (toLeanLevel v)

/-- Translate a normalized Lean universe level back to the object universe language. -/
partial def ofLeanLevel : Lean.Level → LevelExpr
  | .zero => .zero
  | .succ u =>
      match ofLeanLevel u with
      | .zero => .lit 1
      | .lit n => .lit (n + 1)
      | u => .succ u
  | .max u v => .max (ofLeanLevel u) (ofLeanLevel v)
  | .param u => .param u
  | .imax u v => .max (ofLeanLevel u) (ofLeanLevel v)
  | .mvar u => .param u.name

/-- Normalize a universe expression using Lean's own universe normalizer. -/
def normalize (u : LevelExpr) : LevelExpr :=
  ofLeanLevel (toLeanLevel u).normalize

/-- Successor of a universe expression, normalized Lean-style. -/
def succ' (u : LevelExpr) : LevelExpr :=
  normalize (.succ u)

/-- Maximum of two universe expressions, normalized Lean-style. -/
def max' (u v : LevelExpr) : LevelExpr :=
  normalize (.max u v)

/-- Equality of universe expressions after Lean-style normalization. -/
def equal (u v : LevelExpr) : Bool :=
  normalize u == normalize v

/-- Render a universe expression that is already in normal form. -/
partial def toStringRaw : LevelExpr → String
  | .zero => "0"
  | .lit n => s!"{n}"
  | .param n => s!"{n.eraseMacroScopes}"
  | .succ u => s!"({toStringRaw u}+1)"
  | .max u v => s!"max {atomString u} {atomString v}"
where
  /-- Render a universe expression atom. -/
  atomString : LevelExpr → String
    | .zero => "0"
    | .lit n => s!"{n}"
    | .param n => s!"{n.eraseMacroScopes}"
    | u => s!"({toStringRaw u})"

/-- Render an object-level universe expression after Lean-style normalization. -/
def toString (u : LevelExpr) : String :=
  toStringRaw (normalize u)

instance : ToString LevelExpr := ⟨toString⟩

/-- Collect universe parameter names occurring in a level expression. -/
partial def params : LevelExpr → Array Name
  | .zero | .lit _ => #[]
  | .param u => #[u.eraseMacroScopes]
  | .succ u => params u
  | .max u v => params u ++ params v

/-- Substitute universe parameters in a level expression. -/
partial def substParams (σ : NameMap LevelExpr) : LevelExpr → LevelExpr
  | .zero => .zero
  | .lit n => .lit n
  | .param u => (σ.find? u.eraseMacroScopes).getD (.param u)
  | .succ u => succ' (substParams σ u)
  | .max u v => max' (substParams σ u) (substParams σ v)

end LevelExpr


/-- LF head names that still collide with surface grammar tokens after the structural cutover. -/
public def lfKernelReservedNameList : List Name :=
  [`Type]

/-- Set of LF head names that still collide with surface grammar tokens. -/
public def lfKernelReservedNames : NameSet :=
  lfKernelReservedNameList.foldl (init := {}) fun names n => names.insert n

/-- Human-readable list of kernel-reserved LF head names. -/
public def lfKernelReservedNamesString : String :=
  String.intercalate ", " (lfKernelReservedNameList.map (fun n => toString n))

/-- Whether a user LF declaration name is still reserved by surface grammar. -/
public def isLFKernelReservedName (n : Name) : Bool :=
  lfKernelReservedNames.contains n.eraseMacroScopes

/-- Shared user-facing diagnostic for a reserved LF declaration name. -/
public def lfKernelReservedNameError (kind : String) (rawName : Name) : String :=
  let n := rawName.eraseMacroScopes
  let label :=
    if kind == "internal declaration" || kind == "admitted internal declaration" then
      kind
    else
      s!"{kind} declaration"
  s!"{label} '{rawName}' uses reserved name '{n}', which is reserved by InternalLean syntax. \
    Reserved LF names: {lfKernelReservedNamesString}"

/-- A small universe-polymorphic equivalence type used by generated structural model
equivalence interfaces. InternalLean avoids depending on an external `Equiv` definition here so
generated model code remains available in the minimal project environment. -/
structure TypeEquiv.{u, v} (α : Sort u) (β : Sort v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- The inverse is a left inverse of the forward map. -/
  left_inv : ∀ x, invFun (toFun x) = x
  /-- The inverse is a right inverse of the forward map. -/
  right_inv : ∀ y, toFun (invFun y) = y

namespace TypeEquiv

/-- Apply a generated `TypeEquiv` by function application. -/
instance {α : Sort u} {β : Sort v} : CoeFun (TypeEquiv α β) (fun _ => α → β) where
  coe e := e.toFun

end TypeEquiv

/-- Untyped raw object syntax.

The aliases `RawCtx`, `RawTy`, `RawTm`, `RawSubst`, and `RawArg` below document the
intended sort of a raw expression. The kernel remains extrinsic: sort correctness,
typing, substitution well-formedness, and equality are all explicit judgments. -/
inductive Raw where
  /-- Empty object context. -/
  | ctxNil : Raw
  /-- Named context metavariable/placeholder. -/
  | ctxMeta : Name → Raw
  /-- Context extension by a type. -/
  | ctxExt : Raw → Raw → Raw
  /-- Named type metavariable/placeholder. -/
  | tyMeta : Name → Raw
  /-- Primitive type constant/former. -/
  | tyConst : Name → Raw
  /-- Application of a type former to mixed raw arguments. -/
  | tyApp : Name → List Raw → Raw
  /-- Explicit substitution into a type. -/
  | tySubst : Raw → Raw → Raw
  /-- De Bruijn variable. -/
  | tmVar : Nat → Raw
  /-- Named term metavariable/placeholder. -/
  | tmMeta : Name → Raw
  /-- Primitive term constant/former. -/
  | tmConst : Name → Raw
  /-- Application of a term former to mixed raw arguments. -/
  | tmApp : Name → List Raw → Raw
  /-- Explicit substitution into a term. -/
  | tmSubst : Raw → Raw → Raw
  /-- Identity substitution on a context. -/
  | substId : Raw → Raw
  /-- Named substitution metavariable/placeholder. -/
  | substMeta : Name → Raw
  /-- Composition of substitutions. -/
  | substComp : Raw → Raw → Raw
  /-- Empty substitution into the empty context. -/
  | substEmpty : Raw
  /-- Extend a substitution by one term. -/
  | substExt : Raw → Raw → Raw
  /-- Scoped binder node for multi-zone logical-framework staging data.
  `zone` identifies the context zone being extended and `binderClass` records the
  declared binding discipline. This is syntax only; replay validation checks declared
  zones/classes and prevents the bound name from leaking out of the binder body. -/
  | scopedBind : Name → Name → Name → Raw → Raw → Raw
  /-- Lean-side named parameter placeholder. -/
  | leanParam : Name → Raw
  deriving Inhabited, Repr, BEq

/-- Raw context syntax, extrinsically sorted. -/
abbrev RawCtx := Raw

/-- Raw type syntax, extrinsically sorted. -/
abbrev RawTy := Raw

/-- Raw term syntax, extrinsically sorted. -/
abbrev RawTm := Raw

/-- Raw substitution syntax, extrinsically sorted. -/
abbrev RawSubst := Raw

/-- Raw mixed argument syntax. -/
abbrev RawArg := Raw

/-- An instantiation of object-level metavariables by raw syntax. -/
abbrev Instantiation := Name → Raw

/-- User-facing name shown in local/binder diagnostics, ignoring hygienic identity tags. -/
def localDisplayName (n : Name) : String :=
  s!"'{n.eraseMacroScopes}'"

/-- Optional stable-identity suffix for local/binder diagnostics. -/
def localIdentitySuffix (n : Name) : String :=
  if n == n.eraseMacroScopes then "" else s!" (identity {reprStr n})"

/-- User-facing local name with a stable identity suffix when the name is hygienic. -/
def localDiagnosticName (n : Name) : String :=
  localDisplayName n ++ localIdentitySuffix n

namespace Raw

/-- Instantiate raw metavariables in raw syntax, avoiding names bound by `scopedBind`.

All metavariable constructors still share the same namespace. The `scopedBind` node is a
staging binder, so substitutions do not rewrite references to its bound name in the body. A
trusted replay path separately checks instantiation entries so that context metavariables are
instantiated by contexts, type metavariables by types, etc. -/
partial def instantiate (σ : Instantiation) (raw : Raw) : Raw :=
  let rec go (blocked : List Name) : Raw → Raw
    | .ctxNil => .ctxNil
    | .ctxMeta x => if blocked.contains x then .ctxMeta x else σ x
    | .ctxExt Γ A => .ctxExt (go blocked Γ) (go blocked A)
    | .tyMeta x => if blocked.contains x then .tyMeta x else σ x
    | .tyConst c => .tyConst c
    | .tyApp f args => .tyApp f (args.map (go blocked))
    | .tySubst A τ => .tySubst (go blocked A) (go blocked τ)
    | .tmVar i => .tmVar i
    | .tmMeta x => if blocked.contains x then .tmMeta x else σ x
    | .tmConst c => .tmConst c
    | .tmApp f args =>
        if f == `lam then
          match args.reverse with
          | [] => .tmApp f []
          | body :: revBinders =>
              let binders := revBinders.reverse
              if binders.all (fun | .leanParam _ => true | _ => false) then
                let cleanBinders := binders.map fun
                  | .leanParam x => .leanParam x.eraseMacroScopes
                  | other => other
                let blocked' := cleanBinders.filterMap (fun | .leanParam x => some x | _ => none)
                .tmApp f (cleanBinders ++ [go (blocked' ++ blocked) body])
              else
                .tmApp f (args.map (go blocked))
        else
          .tmApp f (args.map (go blocked))
    | .tmSubst t τ => .tmSubst (go blocked t) (go blocked τ)
    | .substId Γ => .substId (go blocked Γ)
    | .substMeta x => if blocked.contains x then .substMeta x else σ x
    | .substComp τ υ => .substComp (go blocked τ) (go blocked υ)
    | .substEmpty => .substEmpty
    | .substExt τ t => .substExt (go blocked τ) (go blocked t)
    | .scopedBind zone cls x ty body =>
        .scopedBind zone cls x (go blocked ty) (go (x :: blocked) body)
    | .leanParam x => if blocked.contains x then .leanParam x else σ x
  go [] raw

/-- Names of local/metavariable placeholders occurring in raw syntax.

This is a syntactic dependency approximation used by the kernel-facing replay checker. It is
binder-aware for `scopedBind`, but it is not a full free-variable analysis for future binder
forms. -/
partial def localRefNames : Raw → List Name
  | .ctxNil => []
  | .ctxMeta x => [x]
  | .ctxExt Γ A => localRefNames Γ ++ localRefNames A
  | .tyMeta x => [x]
  | .tyConst _ => []
  | .tyApp _ args => args.flatMap localRefNames
  | .tySubst A τ => localRefNames A ++ localRefNames τ
  | .tmVar _ => []
  | .tmMeta x => [x]
  | .tmConst _ => []
  | .tmApp f args =>
      if f == `lam then
        match args.reverse with
        | [] => []
        | body :: revBinders =>
            let rawBinders := revBinders.reverse
            if rawBinders.all (fun | .leanParam _ => true | _ => false) then
              let binders := rawBinders.filterMap fun
                | .leanParam x => some x.eraseMacroScopes
                | _ => none
              (localRefNames body).filter (fun y => !binders.contains y.eraseMacroScopes)
            else
              args.flatMap localRefNames
      else
        args.flatMap localRefNames
  | .tmSubst t τ => localRefNames t ++ localRefNames τ
  | .substId Γ => localRefNames Γ
  | .substMeta x => [x]
  | .substComp τ υ => localRefNames τ ++ localRefNames υ
  | .substEmpty => []
  | .substExt τ t => localRefNames τ ++ localRefNames t
  | .scopedBind _ _ x ty body =>
      localRefNames ty ++ (localRefNames body).filter (fun y => y != x)
  | .leanParam x => [x]

/-- Lookup a canonical alpha-normalization representative for a raw local name. -/
def lookupAlphaLocal? : List (Name × Name) → Name → Option Name
  | [], _ => none
  | (oldName, newName) :: rest, n =>
      if oldName.eraseMacroScopes == n.eraseMacroScopes then some newName else
        lookupAlphaLocal? rest n

/-- Deterministic binder name used by raw alpha-normalization. -/
def alphaBinderName (idx : Nat) (avoid : List Name) : Name :=
  let base : Name := .str `_lfBound s!"b{idx}"
  let rec go : Nat → Nat → Name
    | 0, n => .str base s!"_{n}"
    | fuel + 1, n =>
        let candidate := if n == 0 then base else .str base s!"_{n}"
        if avoid.contains candidate then go fuel (n + 1) else candidate
  go (avoid.length + 32) 0

/-- Alpha-normalize raw replay payload binders emitted for LF lambdas and scoped binders. -/
partial def alphaNormalizeWithAvoid (avoid : List Name) (raw : Raw) : Raw :=
  let renameLocal (locals : List (Name × Name)) (mk : Name → Raw) (x : Name) : Raw :=
    let x := x.eraseMacroScopes
    match lookupAlphaLocal? locals x with
    | some y => mk y
    | none => mk x
  let rec go (locals : List (Name × Name)) (next : Nat) : Raw → Raw × Nat
    | .ctxNil => (.ctxNil, next)
    | .ctxMeta x => (renameLocal locals .ctxMeta x, next)
    | .ctxExt Γ A =>
        let (Γ, next) := go locals next Γ
        let (A, next) := go locals next A
        (.ctxExt Γ A, next)
    | .tyMeta x => (renameLocal locals .tyMeta x, next)
    | .tyConst c => (.tyConst c, next)
    | .tyApp f args =>
        let (args, next) := Id.run do
          let mut out := []
          let mut next := next
          for arg in args do
            let (arg, next') := go locals next arg
            out := out ++ [arg]
            next := next'
          return (out, next)
        (.tyApp f args, next)
    | .tySubst A τ =>
        let (A, next) := go locals next A
        let (τ, next) := go locals next τ
        (.tySubst A τ, next)
    | .tmVar i => (.tmVar i, next)
    | .tmMeta x => (renameLocal locals .tmMeta x, next)
    | .tmConst c => (.tmConst c, next)
    | .tmApp f args =>
        if f == `lam then
          match args.reverse with
          | [] => (.tmApp `lam [], next)
          | body :: revBinders =>
              let binders := revBinders.reverse
              if binders.all (fun | .leanParam _ => true | _ => false) then
                let (binderArgs, locals, next) := binders.foldl
                  (init := ([], locals, next)) fun (out, locals, next) binder =>
                    match binder with
                    | .leanParam x =>
                        let x := x.eraseMacroScopes
                        let x' := alphaBinderName next avoid
                        (out ++ [.leanParam x'], (x, x') :: locals, next + 1)
                    | _ => (out, locals, next)
                let (body, next) := go locals next body
                (.tmApp `lam (binderArgs ++ [body]), next)
              else
                let (args, next) := Id.run do
                  let mut out := []
                  let mut next := next
                  for arg in args do
                    let (arg, next') := go locals next arg
                    out := out ++ [arg]
                    next := next'
                  return (out, next)
                (.tmApp `lam args, next)
        else
          let (args, next) := Id.run do
            let mut out := []
            let mut next := next
            for arg in args do
              let (arg, next') := go locals next arg
              out := out ++ [arg]
              next := next'
            return (out, next)
          (.tmApp f args, next)
    | .tmSubst t τ =>
        let (t, next) := go locals next t
        let (τ, next) := go locals next τ
        (.tmSubst t τ, next)
    | .substId Γ =>
        let (Γ, next) := go locals next Γ
        (.substId Γ, next)
    | .substMeta x => (renameLocal locals .substMeta x, next)
    | .substComp τ υ =>
        let (τ, next) := go locals next τ
        let (υ, next) := go locals next υ
        (.substComp τ υ, next)
    | .substEmpty => (.substEmpty, next)
    | .substExt τ t =>
        let (τ, next) := go locals next τ
        let (t, next) := go locals next t
        (.substExt τ t, next)
    | .scopedBind zone cls x ty body =>
        let (ty, next) := go locals next ty
        let x := x.eraseMacroScopes
        let x' := alphaBinderName next avoid
        let (body, next) := go ((x, x') :: locals) (next + 1) body
        (.scopedBind zone cls x' ty body, next)
    | .leanParam x => (renameLocal locals .leanParam x, next)
  (go [] 0 raw).1

/-- Alpha-equivalence for raw replay payloads. -/
def alphaEq (a b : Raw) : Bool :=
  let avoid :=
    a.localRefNames.map Name.eraseMacroScopes ++ b.localRefNames.map Name.eraseMacroScopes
  alphaNormalizeWithAvoid avoid a == alphaNormalizeWithAvoid avoid b

/-- Capture-checking variant of `instantiate` for replay validation.

The pure `instantiate` function is intentionally lightweight. This checked variant is used at
trust boundaries: when substituting under a `scopedBind`, it rejects any substitution image
whose local references include the binder name currently in scope. The implementation does not
alpha-rename, so rejecting capture-prone artifacts is the conservative safe behavior. -/
partial def instantiateChecked (σ : Instantiation) (raw : Raw) : Except String Raw :=
  let rec go (blocked : List Name) : Raw → Except String Raw
    | .ctxNil => pure .ctxNil
    | .ctxMeta x => subst blocked .ctxMeta x
    | .ctxExt Γ A => return .ctxExt (← go blocked Γ) (← go blocked A)
    | .tyMeta x => subst blocked .tyMeta x
    | .tyConst c => pure (.tyConst c)
    | .tyApp f args => return .tyApp f (← args.mapM (go blocked))
    | .tySubst A τ => return .tySubst (← go blocked A) (← go blocked τ)
    | .tmVar i => pure (.tmVar i)
    | .tmMeta x => subst blocked .tmMeta x
    | .tmConst c => pure (.tmConst c)
    | .tmApp f args =>
        if f == `lam then
          match args.reverse with
          | [] => pure (.tmApp f [])
          | body :: revBinders =>
              let binders := revBinders.reverse
              if binders.all (fun | .leanParam _ => true | _ => false) then
                let cleanBinders := binders.map fun
                  | .leanParam x => .leanParam x.eraseMacroScopes
                  | other => other
                let blocked' := cleanBinders.filterMap fun
                  | .leanParam x => some x
                  | _ => none
                return .tmApp f (cleanBinders ++ [← go (blocked' ++ blocked) body])
              else
                return .tmApp f (← args.mapM (go blocked))
        else
          return .tmApp f (← args.mapM (go blocked))
    | .tmSubst t τ => return .tmSubst (← go blocked t) (← go blocked τ)
    | .substId Γ => return .substId (← go blocked Γ)
    | .substMeta x => subst blocked .substMeta x
    | .substComp τ υ => return .substComp (← go blocked τ) (← go blocked υ)
    | .substEmpty => pure .substEmpty
    | .substExt τ t => return .substExt (← go blocked τ) (← go blocked t)
    | .scopedBind zone cls x ty body =>
        return .scopedBind zone cls x (← go blocked ty) (← go (x :: blocked) body)
    | .leanParam x => subst blocked .leanParam x
  go [] raw
where
  subst (blocked : List Name) (mk : Name → Raw) (x : Name) : Except String Raw := do
    if blocked.contains x then
      pure (mk x)
    else
      let value := σ x
      for ref in value.localRefNames do
        if let some binder := blocked.find? (fun b => b == ref) then
          throw s!"instantiating '{x.eraseMacroScopes}' would capture local \
            '{ref.eraseMacroScopes}' under scoped binder named \
              '{binder.eraseMacroScopes}'{localIdentitySuffix binder}"
      pure value

/-- Name-list membership after erasing macro scopes. -/
def rawNameListContains (names : List Name) (x : Name) : Bool :=
  names.any fun y => y.eraseMacroScopes == x.eraseMacroScopes

/-- Pick a deterministic raw local name avoiding a finite set. -/
def freshRawLocalNameAvoiding (base : Name) (avoid : List Name) : Name :=
  let base := base.eraseMacroScopes
  let rec go : Nat → Nat → Name
    | 0, n => .str base s!"_hyg{n}"
    | fuel + 1, n =>
        let candidate := .str base s!"_hyg{n}"
        if rawNameListContains avoid candidate then go fuel (n + 1) else candidate
  if rawNameListContains avoid base then go (avoid.length + 32) 0 else base

/-- Rename raw local occurrences while respecting raw lambda and scoped binders. -/
partial def renameRawLocalOccurrences (oldName newName : Name) : Raw → Raw
  | .ctxNil => .ctxNil
  | .ctxMeta y => if y.eraseMacroScopes == oldName.eraseMacroScopes then
      .ctxMeta newName.eraseMacroScopes else .ctxMeta y.eraseMacroScopes
  | .ctxExt Γ A => .ctxExt (renameRawLocalOccurrences oldName newName Γ)
      (renameRawLocalOccurrences oldName newName A)
  | .tyMeta y => if y.eraseMacroScopes == oldName.eraseMacroScopes then
      .tyMeta newName.eraseMacroScopes else .tyMeta y.eraseMacroScopes
  | .tyConst c => .tyConst c
  | .tyApp f args => .tyApp f (args.map (renameRawLocalOccurrences oldName newName))
  | .tySubst A τ => .tySubst (renameRawLocalOccurrences oldName newName A)
      (renameRawLocalOccurrences oldName newName τ)
  | .tmVar i => .tmVar i
  | .tmMeta y => if y.eraseMacroScopes == oldName.eraseMacroScopes then
      .tmMeta newName.eraseMacroScopes else .tmMeta y.eraseMacroScopes
  | .tmConst c => .tmConst c
  | .tmApp f args =>
      if f == `lam then
        match args.reverse with
        | [] => .tmApp f []
        | body :: revBinders =>
            let binders := revBinders.reverse
            if binders.all (fun | .leanParam _ => true | _ => false) then
              let cleanBinders := binders.map fun
                | .leanParam y => .leanParam y.eraseMacroScopes
                | other => other
              let binderNames := cleanBinders.filterMap fun
                | .leanParam y => some y
                | _ => none
              if rawNameListContains binderNames oldName then
                .tmApp f (cleanBinders ++ [body])
              else
                .tmApp f (cleanBinders ++ [renameRawLocalOccurrences oldName newName body])
            else
              .tmApp f (args.map (renameRawLocalOccurrences oldName newName))
      else
        .tmApp f (args.map (renameRawLocalOccurrences oldName newName))
  | .tmSubst t τ => .tmSubst (renameRawLocalOccurrences oldName newName t)
      (renameRawLocalOccurrences oldName newName τ)
  | .substId Γ => .substId (renameRawLocalOccurrences oldName newName Γ)
  | .substMeta y => if y.eraseMacroScopes == oldName.eraseMacroScopes then
      .substMeta newName.eraseMacroScopes else .substMeta y.eraseMacroScopes
  | .substComp τ υ => .substComp (renameRawLocalOccurrences oldName newName τ)
      (renameRawLocalOccurrences oldName newName υ)
  | .substEmpty => .substEmpty
  | .substExt τ t => .substExt (renameRawLocalOccurrences oldName newName τ)
      (renameRawLocalOccurrences oldName newName t)
  | .scopedBind zone cls y ty body =>
      let y := y.eraseMacroScopes
      let ty := renameRawLocalOccurrences oldName newName ty
      if y == oldName.eraseMacroScopes then
        .scopedBind zone cls y ty body
      else
        .scopedBind zone cls y ty (renameRawLocalOccurrences oldName newName body)
  | .leanParam y => if y.eraseMacroScopes == oldName.eraseMacroScopes then
      .leanParam newName.eraseMacroScopes else .leanParam y.eraseMacroScopes

/-- Substitute a raw Lean-parameter placeholder by raw syntax, alpha-renaming binders as needed.

The generic conversion-certificate beta engine uses this helper at a trust boundary, so it must not
capture free raw locals from the substitution value under raw lambda or scoped binders. -/
partial def substLeanParam (x : Name) (value : Raw) : Raw → Raw
  | .ctxNil => .ctxNil
  | .ctxMeta y => .ctxMeta y.eraseMacroScopes
  | .ctxExt Γ A => .ctxExt (substLeanParam x value Γ) (substLeanParam x value A)
  | .tyMeta y => .tyMeta y.eraseMacroScopes
  | .tyConst c => .tyConst c
  | .tyApp f args => .tyApp f (args.map (substLeanParam x value))
  | .tySubst A τ => .tySubst (substLeanParam x value A) (substLeanParam x value τ)
  | .tmVar i => .tmVar i
  | .tmMeta y => .tmMeta y.eraseMacroScopes
  | .tmConst c => .tmConst c
  | .tmApp f args =>
      if f == `lam then
        match args.reverse with
        | [] => .tmApp f []
        | body :: revBinders =>
            let binders := revBinders.reverse
            if binders.all (fun | .leanParam _ => true | _ => false) then
              let (cleanBinders, body) := Id.run do
                let mut out := []
                let mut body := body
                for binder in binders do
                  match binder with
                  | .leanParam y =>
                      let y := y.eraseMacroScopes
                      if rawNameListContains [x.eraseMacroScopes] y then
                        out := out ++ [.leanParam y]
                      else if rawNameListContains value.localRefNames y &&
                          rawNameListContains body.localRefNames x then
                        let avoid := value.localRefNames ++ body.localRefNames ++ [x, y]
                        let y' := freshRawLocalNameAvoiding y avoid
                        body := renameRawLocalOccurrences y y' body
                        out := out ++ [.leanParam y']
                      else
                        out := out ++ [.leanParam y]
                  | other => out := out ++ [other]
                return (out, body)
              let binderNames := cleanBinders.filterMap fun
                | .leanParam y => some y
                | _ => none
              if rawNameListContains binderNames x then
                .tmApp f (cleanBinders ++ [body])
              else
                .tmApp f (cleanBinders ++ [substLeanParam x value body])
            else
              .tmApp f (args.map (substLeanParam x value))
      else
        .tmApp f (args.map (substLeanParam x value))
  | .tmSubst t τ => .tmSubst (substLeanParam x value t) (substLeanParam x value τ)
  | .substId Γ => .substId (substLeanParam x value Γ)
  | .substMeta y => .substMeta y.eraseMacroScopes
  | .substComp τ υ => .substComp (substLeanParam x value τ) (substLeanParam x value υ)
  | .substEmpty => .substEmpty
  | .substExt τ t => .substExt (substLeanParam x value τ) (substLeanParam x value t)
  | .scopedBind zone cls y ty body =>
      let y := y.eraseMacroScopes
      let ty := substLeanParam x value ty
      if y == x.eraseMacroScopes then
        .scopedBind zone cls y ty body
      else
        let (y, body) :=
          if rawNameListContains value.localRefNames y && rawNameListContains body.localRefNames x
          then
            let avoid := value.localRefNames ++ body.localRefNames ++ [x, y]
            let y' := freshRawLocalNameAvoiding y avoid
            (y', renameRawLocalOccurrences y y' body)
          else
            (y, body)
        .scopedBind zone cls y ty (substLeanParam x value body)
  | .leanParam y =>
      if y.eraseMacroScopes == x.eraseMacroScopes then value else .leanParam y.eraseMacroScopes

/-- One-step β reduction for the legacy raw `_app`/`lam` convention.

Structural-kernel conversion uses first-class binders. This helper remains for low-level legacy raw
API tests and compatibility smoke checks. -/
def betaReduce? : Raw → Option Raw
  | .tmApp `_app [.tmApp `lam [.leanParam x, body], arg] =>
      some (Raw.substLeanParam x arg body)
  | _ => none

/-- One-step structural η reduction for raw conversion certificates.

Function eta is recognized for the explicit `_app` convention, and Sigma eta is recognized for the
structural `pair`/`fst`/`snd` convention. -/
def etaReduce? : Raw → Option Raw
  | .tmApp `lam [.leanParam x, .tmApp `_app [f, .leanParam y]] =>
      if x.eraseMacroScopes == y.eraseMacroScopes &&
          !(f.localRefNames.map Name.eraseMacroScopes).contains x.eraseMacroScopes then
        some f
      else
        none
  | .tmApp `pair [.tmApp `fst [p], .tmApp `snd [q]] =>
      if p.alphaEq q then some p else none
  | _ => none

end Raw

/-- Built-in low-level object judgments supported by the replay checker. -/
inductive Judgment where
  /-- `⊢ Γ ctx`. -/
  | wfCtx : RawCtx → Judgment
  /-- `Γ ⊢ A type`. -/
  | wfTy : RawCtx → RawTy → Judgment
  /-- `Γ ⊢ t : A`. -/
  | wfTm : RawCtx → RawTm → RawTy → Judgment
  /-- `Δ ⊢ σ : Γ`. -/
  | wfSubst : RawCtx → RawSubst → RawCtx → Judgment
  /-- `Γ ⊢ A ≡ B type`; this is object equality, not Lean equality. -/
  | eqTy : RawCtx → RawTy → RawTy → Judgment
  /-- `Γ ⊢ t ≡ u : A`; this is object equality, not Lean equality. -/
  | eqTm : RawCtx → RawTm → RawTm → RawTy → Judgment
  /-- Placeholder for proof-relevant, theory-specific equality/path/cell judgments. -/
  | custom : Name → List RawArg → Judgment
  deriving Inhabited, Repr, BEq

namespace Judgment

/-- Instantiate metavariables in a judgment. -/
def instantiate (σ : Instantiation) : Judgment → Judgment
  | .wfCtx Γ => .wfCtx (Γ.instantiate σ)
  | .wfTy Γ A => .wfTy (Γ.instantiate σ) (A.instantiate σ)
  | .wfTm Γ t A => .wfTm (Γ.instantiate σ) (t.instantiate σ) (A.instantiate σ)
  | .wfSubst Δ τ Γ => .wfSubst (Δ.instantiate σ) (τ.instantiate σ) (Γ.instantiate σ)
  | .eqTy Γ A B => .eqTy (Γ.instantiate σ) (A.instantiate σ) (B.instantiate σ)
  | .eqTm Γ t u A =>
      .eqTm (Γ.instantiate σ) (t.instantiate σ) (u.instantiate σ) (A.instantiate σ)
  | .custom k args => .custom k (args.map (Raw.instantiate σ))

/-- Capture-checking judgment instantiation used at replay trust boundaries. -/
def instantiateChecked (σ : Instantiation) : Judgment → Except String Judgment
  | .wfCtx Γ => return .wfCtx (← Γ.instantiateChecked σ)
  | .wfTy Γ A => return .wfTy (← Γ.instantiateChecked σ) (← A.instantiateChecked σ)
  | .wfTm Γ t A => return .wfTm (← Γ.instantiateChecked σ) (← t.instantiateChecked σ) (
    ← A.instantiateChecked σ)
  | .wfSubst Δ τ Γ => return .wfSubst (← Δ.instantiateChecked σ) (← τ.instantiateChecked σ) (
    ← Γ.instantiateChecked σ)
  | .eqTy Γ A B => return .eqTy (← Γ.instantiateChecked σ) (← A.instantiateChecked σ) (
    ← B.instantiateChecked σ)
  | .eqTm Γ t u A =>
      return .eqTm (← Γ.instantiateChecked σ) (← t.instantiateChecked σ) (
        ← u.instantiateChecked σ) (← A.instantiateChecked σ)
  | .custom k args => return .custom k (← args.mapM (Raw.instantiateChecked σ))

/-- Names of local/metavariable placeholders occurring in a judgment. -/
def localRefNames : Judgment → List Name
  | .wfCtx Γ => Γ.localRefNames
  | .wfTy Γ A => Γ.localRefNames ++ A.localRefNames
  | .wfTm Γ t A => Γ.localRefNames ++ t.localRefNames ++ A.localRefNames
  | .wfSubst Δ τ Γ => Δ.localRefNames ++ τ.localRefNames ++ Γ.localRefNames
  | .eqTy Γ A B => Γ.localRefNames ++ A.localRefNames ++ B.localRefNames
  | .eqTm Γ t u A => Γ.localRefNames ++ t.localRefNames ++ u.localRefNames ++ A.localRefNames
  | .custom _ args => args.flatMap Raw.localRefNames

/-- Alpha-equivalence for kernel-facing judgments. -/
def alphaEq : Judgment → Judgment → Bool
  | .wfCtx Γ, .wfCtx Γ' => Raw.alphaEq Γ Γ'
  | .wfTy Γ A, .wfTy Γ' A' => Raw.alphaEq Γ Γ' && Raw.alphaEq A A'
  | .wfTm Γ t A, .wfTm Γ' t' A' =>
      Raw.alphaEq Γ Γ' && Raw.alphaEq t t' && Raw.alphaEq A A'
  | .wfSubst Δ τ Γ, .wfSubst Δ' τ' Γ' =>
      Raw.alphaEq Δ Δ' && Raw.alphaEq τ τ' && Raw.alphaEq Γ Γ'
  | .eqTy Γ A B, .eqTy Γ' A' B' =>
      Raw.alphaEq Γ Γ' && Raw.alphaEq A A' && Raw.alphaEq B B'
  | .eqTm Γ t u A, .eqTm Γ' t' u' A' =>
      Raw.alphaEq Γ Γ' && Raw.alphaEq t t' && Raw.alphaEq u u' && Raw.alphaEq A A'
  | .custom k args, .custom k' args' =>
      k == k' && args.length == args'.length && (args.zip args').all (fun (a, b) =>
        Raw.alphaEq a b)
  | _, _ => false

end Judgment

/-- Extrinsic sort of a raw metavariable in a rule schema. -/
inductive RawMetaSort where
  /-- Context metavariable. -/
  | ctx
  /-- Type metavariable. -/
  | ty
  /-- Term metavariable. -/
  | tm
  /-- Substitution metavariable. -/
  | subst
  /-- Mixed raw argument metavariable. -/
  | arg
  /-- Theory-specific syntactic sort. -/
  | custom (name : Name)
  deriving Inhabited, Repr, BEq

namespace RawMetaSort

/-- Whether an expected metavariable sort has a fixed built-in raw constructor family.
Custom LF sorts are checked through explicit LF type annotations instead. -/
def isBuiltin : RawMetaSort → Bool
  | .ctx | .ty | .tm | .subst => true
  | .arg | .custom _ => false

/-- Check a shallow raw constructor sort against an expected metavariable sort.
The catch-all and custom sorts deliberately accept any shallow constructor here; custom sorts
are constrained by LF type annotations and typed constants. -/
def acceptsShallowValueSort (expected actual : RawMetaSort) : Bool :=
  if expected.isBuiltin then expected == actual else true

end RawMetaSort

namespace Raw

/-- The built-in raw constructor family at the head of a syntax node, when one is known.
This is intentionally shallow: typed LF constants may represent custom contexts, types, or
terms, so deeper argument discipline is left to LF type annotations and rule premises. -/
def shallowMetaSort? : Raw → Option RawMetaSort
  | .ctxNil | .ctxMeta _ | .ctxExt _ _ => some .ctx
  | .tyMeta _ | .tyConst _ | .tyApp _ _ | .tySubst _ _ => some .ty
  | .tmVar _ | .tmMeta _ | .tmConst _ | .tmApp _ _ | .tmSubst _ _ => some .tm
  | .substId _ | .substMeta _ | .substComp _ _ | .substEmpty | .substExt _ _ => some .subst
  | .scopedBind .. | .leanParam _ => none

/-- Check the trusted built-in constructor discipline for raw syntax.

This remains intentionally shallow and syntactic. It validates exactly the fixed raw
constructor families around explicit substitution nodes (`tySubst`, `tmSubst`, `substId`,
`substComp`, `substEmpty`, and `substExt`) and context extension when a child has a known
built-in head sort. It does not prove source/target compatibility of substitutions,
substitution laws, weakening, or reindexing semantics. Those facts must be represented by
ordinary LF judgments/rules/premises/evidence in the object theory. Unknown or custom
LF-headed children are left to typed LF annotations and rule premises. -/
partial def validateBuiltinConstructorDiscipline (owner field : String) (raw : Raw) :
  Except String Unit :=
  let checkArg (ctor argName : String) (expected : RawMetaSort) (arg : Raw) : Except String Unit :=
    do
    if let some actual := arg.shallowMetaSort? then
      if actual != expected then
        throw s!"{owner} has {field} with {ctor} {argName} headed by sort '{reprStr actual}', \
          expected '{reprStr expected}'"
  let rec go : Raw → Except String Unit
    | .ctxNil | .ctxMeta _ | .tyMeta _ | .tyConst _ | .tmVar _ | .tmMeta _ |
      .tmConst _ | .substMeta _ | .substEmpty | .leanParam _ => pure ()
    | .ctxExt Γ A => do
        checkArg "ctxExt" "context argument" .ctx Γ
        checkArg "ctxExt" "type argument" .ty A
        go Γ
        go A
    | .tyApp _ args | .tmApp _ args => args.forM go
    | .tySubst A τ => do
        checkArg "tySubst" "type argument" .ty A
        checkArg "tySubst" "substitution argument" .subst τ
        go A
        go τ
    | .tmSubst t τ => do
        checkArg "tmSubst" "term argument" .tm t
        checkArg "tmSubst" "substitution argument" .subst τ
        go t
        go τ
    | .substId Γ => do
        checkArg "substId" "context argument" .ctx Γ
        go Γ
    | .substComp τ υ => do
        checkArg "substComp" "left substitution argument" .subst τ
        checkArg "substComp" "right substitution argument" .subst υ
        go τ
        go υ
    | .substExt τ t => do
        checkArg "substExt" "substitution argument" .subst τ
        checkArg "substExt" "term argument" .tm t
        go τ
        go t
    | .scopedBind _ _ _ ty body => do
        go ty
        go body
  go raw

end Raw

namespace Judgment

/-- Validate shallow built-in raw constructor discipline throughout a judgment. -/
def validateBuiltinConstructorDiscipline (owner field : String) : Judgment → Except String Unit
  | .wfCtx Γ => Γ.validateBuiltinConstructorDiscipline owner field
  | .wfTy Γ A => do
      Γ.validateBuiltinConstructorDiscipline owner field
      A.validateBuiltinConstructorDiscipline owner field
  | .wfTm Γ t A => do
      Γ.validateBuiltinConstructorDiscipline owner field
      t.validateBuiltinConstructorDiscipline owner field
      A.validateBuiltinConstructorDiscipline owner field
  | .wfSubst Δ τ Γ => do
      Δ.validateBuiltinConstructorDiscipline owner field
      τ.validateBuiltinConstructorDiscipline owner field
      Γ.validateBuiltinConstructorDiscipline owner field
  | .eqTy Γ A B => do
      Γ.validateBuiltinConstructorDiscipline owner field
      A.validateBuiltinConstructorDiscipline owner field
      B.validateBuiltinConstructorDiscipline owner field
  | .eqTm Γ t u A => do
      Γ.validateBuiltinConstructorDiscipline owner field
      t.validateBuiltinConstructorDiscipline owner field
      u.validateBuiltinConstructorDiscipline owner field
      A.validateBuiltinConstructorDiscipline owner field
  | .custom _ args => args.forM (Raw.validateBuiltinConstructorDiscipline owner field)

end Judgment

/-- Source-ish rendering for an LF name in replay diagnostics. -/
def lfReplayNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Source-ish rendering for an applied LF head in replay diagnostics. -/
def lfReplayAppString (n : Name) (args : List String) : String :=
  match args with
  | [] => lfReplayNameString n
  | _ => s!"{lfReplayNameString n} {String.intercalate " " args}"

/-- Source-ish rendering for raw LF payload syntax, depth-limited for diagnostics. -/
partial def rawSourceStringWithDepth : Nat → Raw → String
  | 0, _ => "..."
  | _ + 1, .ctxNil => "emptyCtx"
  | _ + 1, .ctxMeta n => s!"?{lfReplayNameString n}"
  | depth + 1, .ctxExt Γ A =>
      s!"ctxExt ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | _ + 1, .tyMeta n => s!"?{lfReplayNameString n}"
  | _ + 1, .tyConst n => lfReplayNameString n
  | depth + 1, .tyApp n args =>
      lfReplayAppString n (args.map (rawSourceStringWithDepth depth))
  | depth + 1, .tySubst Γ A =>
      s!"tySubst ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | _ + 1, .tmVar i => s!"#{i}"
  | _ + 1, .tmMeta n => s!"?{lfReplayNameString n}"
  | _ + 1, .tmConst n => lfReplayNameString n
  | depth + 1, .tmApp n args =>
      lfReplayAppString n (args.map (rawSourceStringWithDepth depth))
  | depth + 1, .tmSubst Γ t =>
      s!"tmSubst ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t})"
  | depth + 1, .substId Γ => s!"substId ({rawSourceStringWithDepth depth Γ})"
  | _ + 1, .substMeta n => s!"?{lfReplayNameString n}"
  | depth + 1, .substComp σ τ =>
      s!"substComp ({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth τ})"
  | _ + 1, .substEmpty => "emptySubst"
  | depth + 1, .substExt σ t =>
      s!"substExt ({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth t})"
  | depth + 1, .scopedBind zone cls x ty body =>
      s!"bind {lfReplayNameString x} : {rawSourceStringWithDepth depth ty} in " ++
        s!"{rawSourceStringWithDepth depth body} [{lfReplayNameString zone}/" ++
        s!"{lfReplayNameString cls}]"
  | _ + 1, .leanParam n => lfReplayNameString n

/-- Default source-ish raw LF rendering for diagnostics. -/
def rawSourceString (raw : Raw) : String :=
  rawSourceStringWithDepth 6 raw

/-- Source-ish rendering for optional raw LF payload syntax. -/
def rawOptionSourceString (raw? : Option Raw) : String :=
  match raw? with
  | none => "none"
  | some raw => rawSourceString raw

/-- Source-ish rendering for a kernel judgment in replay diagnostics. -/
def judgmentSourceStringWithDepth (depth : Nat) : Judgment → String
  | .wfCtx Γ => s!"wfCtx {rawSourceStringWithDepth depth Γ}"
  | .wfTy Γ A =>
      s!"wfTy ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A})"
  | .wfTm Γ t A =>
      s!"wfTm ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t}) " ++
        s!"({rawSourceStringWithDepth depth A})"
  | .wfSubst Δ σ Γ =>
      s!"wfSubst ({rawSourceStringWithDepth depth Δ}) " ++
        s!"({rawSourceStringWithDepth depth σ}) ({rawSourceStringWithDepth depth Γ})"
  | .eqTy Γ A B =>
      s!"eqTy ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth A}) " ++
        s!"({rawSourceStringWithDepth depth B})"
  | .eqTm Γ t u A =>
      s!"eqTm ({rawSourceStringWithDepth depth Γ}) ({rawSourceStringWithDepth depth t}) " ++
        s!"({rawSourceStringWithDepth depth u}) ({rawSourceStringWithDepth depth A})"
  | .custom n args =>
      lfReplayAppString n (args.map (rawSourceStringWithDepth depth))

/-- Default source-ish kernel-judgment rendering for diagnostics. -/
def judgmentSourceString (stmt : Judgment) : String :=
  judgmentSourceStringWithDepth 6 stmt

/-- Source-ish rendering for optional kernel judgments. -/
def judgmentOptionSourceString (stmt? : Option Judgment) : String :=
  match stmt? with
  | none => "none"
  | some stmt => judgmentSourceString stmt

/-- Low-level context-zone schema for multi-zone logical-framework staging.

Operationally, a zone classifies LF rule/theorem parameters whose type is headed by the
zone's syntax sort.  Replay does not invent weakening/substitution semantics for a zone; it
uses the zone annotation to validate that scoped instantiations, local parameters, and
binder-class entries follow the declared dependency order. -/
structure ContextZoneSchema where
  /-- Zone name, e.g. `cube`, `tope`, or `type`. -/
  name : Name
  /-- Raw sort name governing entries in this zone. -/
  sort : RawMetaSort := .arg
  /-- Earlier zones this zone may depend on. -/
  dependsOn : List Name := []
  deriving Inhabited, Repr, BEq

/-- Low-level binder-class schema for scoped raw syntax.

A binder class says which sort of local variable may extend a zone.  It is checked as
structural replay metadata; object-theory weakening, exchange, and reindexing still have to
be supplied as LF rules, premises, or parameter evidence. -/
structure BinderClassSchema where
  /-- Binder-class name. -/
  name : Name
  /-- Context zone extended by this binder class. -/
  zone : Name
  /-- Raw sort/class of the variable introduced by this binder. -/
  boundSort : RawMetaSort := .arg
  /-- Earlier zones this binder may refer to. -/
  dependsOn : List Name := []
  deriving Inhabited, Repr, BEq

/-- One local entry in a staged multi-zone context. -/
structure ContextZoneLocal where
  /-- Zone containing the local. -/
  zone : Name
  /-- Local name. -/
  name : Name
  /-- Binder class that introduced this local, if known. -/
  binderClass? : Option Name := none
  /-- Optional raw type/sort annotation. -/
  type? : Option Raw := none
  deriving Inhabited, Repr, BEq

/-- Staged multi-zone local context. -/
structure MultiZoneContext where
  /-- Local entries across all declared zones, in source order. -/
  locals : List ContextZoneLocal := []
  deriving Inhabited, Repr, BEq

/-- Metavariable declaration in a low-level rule schema. -/
structure RuleMetaVar where
  /-- Metavariable name. -/
  name : Name
  /-- Extrinsic sort/class of raw syntax expected for this metavariable. -/
  sort : RawMetaSort := .arg
  /-- Optional context zone for multi-zone LF rules. -/
  zone? : Option Name := none
  /-- Optional dependency/type annotation for the metavariable. -/
  type? : Option Raw := none
  /-- Optional judgmental evidence expected for an instantiated metavariable.

  This is primarily for substitution-shaped parameters: a rule can require that an
  instantiation entry preserve an explicit `wfSubst` (or theory-specific) judgment about
  the supplied raw value, instead of trusting raw substitution syntax alone. -/
  evidence? : Option Judgment := none
  deriving Inhabited, Repr, BEq

/-- A simple description of a Lean-side side condition.

For now this is only a name plus arguments. Later it should point to a checked Lean
procedure/proof obligation. -/
structure SideCondition where
  /-- Name of the side-condition hook. -/
  name : Name
  /-- Raw arguments supplied to the hook. -/
  args : List RawArg := []
  deriving Inhabited, Repr, BEq

namespace SideCondition

/-- Capture-checking instantiation of the raw side-condition arguments. -/
def instantiateChecked (sc : SideCondition) (σ : Instantiation) : Except String SideCondition := do
  return { sc with args := ← sc.args.mapM (Raw.instantiateChecked σ) }

/-- Validate trusted built-in raw constructor discipline in side-condition arguments. -/
def validateBuiltinConstructorDiscipline (owner field : String) (sc : SideCondition) :
  Except String Unit :=
  sc.args.forM (Raw.validateBuiltinConstructorDiscipline owner field)

end SideCondition

/-- A placeholder for checked side-condition evidence.

The low-level replay layer records the side condition whose evidence is required. Executable hooks
may produce checked certificates, but these slots remain the stable obligations expected by a
certified rule application. -/
structure SideConditionCertificateSlot where
  /-- Stable slot name. -/
  name : Name
  /-- Side condition to certify. -/
  condition : SideCondition
  deriving Inhabited, Repr, BEq

/-- Kind/provenance of a low-level side-condition certificate. -/
inductive SideConditionCertificateKind where
  /-- Certificate produced by the built-in trivial side-condition hook. -/
  | builtinTrivial
  /-- Certificate produced by the executable object-level universe normalizer. -/
  | levelNormalizer
  deriving Inhabited, Repr, BEq

namespace SideConditionCertificateKind

/-- User-facing label for a side-condition certificate kind. -/
def label : SideConditionCertificateKind → String
  | .builtinTrivial => "builtin_trivial"
  | .levelNormalizer => "level_normalizer"

end SideConditionCertificateKind

/-- Checked evidence record for a side condition.

This is intentionally small and provenance-oriented: it records which hook accepted which
raw side-condition obligation. Nontrivial future solvers should attach proof-carrying LF
or Lean evidence rather than relying on this diagnostic payload alone. -/
structure SideConditionCertificate where
  /-- Stable certificate name, usually derived from the side-condition slot. -/
  name : Name
  /-- Certified side condition. -/
  condition : SideCondition
  /-- Certificate kind/provenance. -/
  kind : SideConditionCertificateKind
  /-- Optional diagnostic payload. -/
  payload : String := ""
  deriving Inhabited, Repr, BEq

/-- Trust/provenance class for a conversion plugin.

The conversion boundary is explicit: a future plugin step is either checked by an executable
core hook, backed by an externally supplied certificate entry, or recorded as an opaque
assumption.  Plain metadata declarations default to opaque and do not become executable
conversion rules unless a schema lists supported steps. -/
inductive ConversionPluginTrustKind where
  /-- The plugin step is checked by executable trusted code registered with the kernel-facing
  checker. -/
  | executableChecked
  /-- The plugin step is accepted only when an explicit external certificate entry is present. -/
  | externalCertificate
  /-- The plugin step is an intentionally opaque assumption, accepted only as a visible trusted
  leaf. -/
  | opaqueAssumption
  deriving Inhabited, Repr, BEq

namespace ConversionPluginTrustKind

/-- User-facing label for a conversion-plugin trust kind. -/
def label : ConversionPluginTrustKind → String
  | .executableChecked => "executable_checked"
  | .externalCertificate => "external_certificate"
  | .opaqueAssumption => "opaque_assumption"

end ConversionPluginTrustKind

/-- First small vocabulary of generic conversion-certificate steps.

The checker does not give these names theory-specific meaning.  They classify leaves so the
trusted boundary can distinguish β/η, explicit substitution, reindexing, side-condition
sensitive conversion, and fully opaque plugin axioms without adding theory-specific
conversion branches. -/
inductive ConversionStepKind where
  | beta
  | eta
  | explicitSubstitution
  | reindexing
  | sideCondition
  | pluginAxiom
  deriving Inhabited, Repr, BEq

/-- Coarse reason a conversion-certificate check failed.

The categories intentionally separate ordinary unsupported conversion from malformed certificate
syntax and visible trust-boundary failures.  Callers that only need a legacy string can use
`ConversionCheckFailure.message`. -/
inductive ConversionCheckFailureKind where
  /-- The requested step is not implemented or not supported by the declared plugin. -/
  | unsupportedConversion
  /-- The certificate tree or endpoint data is malformed. -/
  | malformedCertificate
  /-- An external-certificate-backed step is missing or disagrees with the replay context. -/
  | externalCertificate
  /-- An opaque plugin leaf violates the visible-trust-boundary discipline. -/
  | opaquePlugin
  deriving Inhabited, Repr, BEq

/-- Structured failure from conversion-certificate checking. -/
structure ConversionCheckFailure where
  /-- Failure class. -/
  kind : ConversionCheckFailureKind
  /-- Human-readable diagnostic. -/
  message : String
  deriving Inhabited, Repr, BEq

namespace ConversionStepKind

/-- User-facing label for a conversion-certificate step kind. -/
def label : ConversionStepKind → String
  | .beta => "beta"
  | .eta => "eta"
  | .explicitSubstitution => "explicit_substitution"
  | .reindexing => "reindexing"
  | .sideCondition => "side_condition"
  | .pluginAxiom => "plugin_axiom"

end ConversionStepKind

/-- Raw conversion profile for an object-language level normalizer. -/
structure LevelNormalizerRawProfile where
  /-- Object-level zero constructor. -/
  zeroName : Name
  /-- Object-level successor constructor. -/
  succName : Name
  /-- Object-level maximum constructor. -/
  maxName : Name
  deriving Inhabited, Repr, BEq

/-- Kernel-facing conversion-plugin schema.

`supportedSteps` is deliberately explicit.  An empty list means the plugin is only a named
metadata/trust-boundary marker and cannot justify conversion leaves. -/
structure ConversionPluginSchema where
  /-- Plugin name. -/
  name : Name
  /-- How leaves for this plugin are trusted. -/
  trust : ConversionPluginTrustKind := .opaqueAssumption
  /-- Step classes this plugin is allowed to justify. -/
  supportedSteps : List ConversionStepKind := []
  /-- Optional executable level-normalizer profile for reindexing leaves. -/
  levelNormalizer? : Option LevelNormalizerRawProfile := none
  deriving Inhabited, Repr, BEq

/-- A generic conversion statement carried by conversion certificates.

The endpoints are raw LF/object syntax.  `context?` is intentionally just syntax here; any
source/target well-formedness, reindexing law, or binder-sensitive side condition must be
provided by the plugin step kind and/or explicit side-condition certificate references. -/
structure ConversionStatement where
  /-- Plugin whose boundary is used for this conversion. -/
  plugin : Name
  /-- Optional raw context/indexing payload for the conversion. -/
  context? : Option Raw := none
  /-- Source endpoint. -/
  lhs : Raw
  /-- Target endpoint. -/
  rhs : Raw
  deriving Inhabited, Repr, BEq

namespace ConversionStatement

/-- Source-ish rendering for a conversion statement. -/
def sourceStringWithDepth (depth : Nat) (stmt : ConversionStatement) : String :=
  let ctx := match stmt.context? with
    | none => ""
    | some Γ => s!" in {rawSourceStringWithDepth depth Γ}"
  s!"{lfReplayNameString stmt.plugin}{ctx}: {rawSourceStringWithDepth depth stmt.lhs} ≡ \
    {rawSourceStringWithDepth depth stmt.rhs}"

/-- Default source-ish conversion-statement rendering for diagnostics. -/
def sourceString (stmt : ConversionStatement) : String :=
  sourceStringWithDepth 6 stmt

/-- Validate trusted built-in raw constructor discipline in a conversion statement. -/
def validateBuiltinConstructorDiscipline (owner : String) (stmt : ConversionStatement) :
  Except String Unit := do
  if let some Γ := stmt.context? then
    Γ.validateBuiltinConstructorDiscipline owner "conversion context"
  stmt.lhs.validateBuiltinConstructorDiscipline owner "conversion lhs"
  stmt.rhs.validateBuiltinConstructorDiscipline owner "conversion rhs"

/-- Reverse a conversion statement, preserving the plugin and context payload. -/
def symm (stmt : ConversionStatement) : ConversionStatement :=
  { stmt with lhs := stmt.rhs, rhs := stmt.lhs }

/-- Replace the target endpoint, preserving plugin/context. -/
def withRhs (stmt : ConversionStatement) (rhs : Raw) : ConversionStatement :=
  { stmt with rhs := rhs }

/-- Replace the source endpoint, preserving plugin/context. -/
def withLhs (stmt : ConversionStatement) (lhs : Raw) : ConversionStatement :=
  { stmt with lhs := lhs }

end ConversionStatement

/-- External conversion-certificate entry available to kernel-facing replay. -/
structure KernelLFConversionCertificateEntry where
  /-- Stable certificate/provenance token. -/
  certificateName : Name
  /-- Certified conversion statement. -/
  statement : ConversionStatement
  /-- Certified step class. -/
  stepKind : ConversionStepKind
  deriving Inhabited, Repr, BEq

/-- Small generic conversion-certificate tree.

Structural nodes (`refl`, `symm`, `trans`) are independently checked.  `pluginStep` is the
only leaf that crosses a plugin trust boundary, and validation classifies it as executable,
external-certificate-backed, or opaque according to the declared plugin schema. -/
inductive KernelLFConversionCertificate where
  | refl (statement : ConversionStatement) : KernelLFConversionCertificate
  | symm (statement : ConversionStatement) (child : KernelLFConversionCertificate) :
    KernelLFConversionCertificate
  | trans (statement : ConversionStatement) (middle : Raw)
      (left right : KernelLFConversionCertificate) : KernelLFConversionCertificate
  | pluginStep (statement : ConversionStatement) (stepKind : ConversionStepKind)
      (externalCertificateName? : Option Name) (sideConditionCertificateNames : List Name)
      (payload : String) : KernelLFConversionCertificate
  deriving Inhabited, Repr, BEq

/-- One entry in a scoped, typed rule-instantiation spine for kernel-facing replay. -/
structure ScopedInstantiationEntry where
  /-- Metavariable being instantiated. -/
  name : Name
  /-- Extrinsic sort/class expected for this metavariable. -/
  sort : RawMetaSort := .arg
  /-- Optional context zone for multi-zone LF rules. -/
  zone? : Option Name := none
  /-- Optional raw type/sort annotation for this metavariable. -/
  type? : Option Raw := none
  /-- Optional instantiated judgmental evidence carried with this entry. -/
  evidence? : Option Judgment := none
  /-- Raw value supplied for the metavariable. -/
  value : Raw
  deriving Inhabited, Repr, BEq

/-- Scoped, typed instantiation data consumed by the kernel-facing derivation replay.

This is deliberately finite and inspectable, unlike the function-valued `Instantiation` used
by the low-level replay layer. It records the domain, zones, and types that trusted
checking must validate. -/
structure ScopedInstantiation where
  /-- Entries in telescope/source order. -/
  entries : List ScopedInstantiationEntry := []
  deriving Inhabited, Repr, BEq

/-- A typed LF constant available to kernel-facing replay.

This includes typed opaque placeholders and checked nullary LF definitions, represented by a
raw parameter telescope and raw result type. It is still a staging schema rather than a
trusted global declaration. -/
structure LFConstantSchema where
  /-- Constant name. -/
  name : Name
  /-- Parameter telescope for applications of this constant. -/
  params : List RuleMetaVar := []
  /-- Result type after instantiating the parameter telescope. -/
  resultType : Raw
  deriving Inhabited, Repr, BEq

namespace ScopedInstantiation

/-- Interpret a finite scoped instantiation as the current functional instantiation shape.
Unmentioned metavariables are left as Lean-parameter placeholders. -/
def asInstantiation (σ : ScopedInstantiation) : Instantiation := fun x =>
  match σ.entries.find? (fun e => e.name == x.eraseMacroScopes) with
  | some e => e.value
  | none => .leanParam x

/-- The custom sort named by a raw LF type annotation, when it has the conventional
`Sort args` shape produced by LF syntax-sort declarations. -/
def annotationCustomSort? : Raw → Option Name
  | .tyConst n => some n
  | .tyApp n _ => if n == `arrow || n == `sigma then none else some n
  | _ => none

/-- Find kernel-facing typed LF constant schemas by name and arity. More than one match is
ambiguous and should be rejected by validation callers. -/
def findConstantsByNameAndArity (constants : List LFConstantSchema) (name : Name) (arity : Nat) :
  List LFConstantSchema :=
  constants.filter (fun c => c.name == name.eraseMacroScopes && c.params.length == arity)

/-- Find a kernel-facing typed LF constant schema by name and arity, selecting the first match.
Use `findConstantsByNameAndArity` in validation paths so duplicate schemas can be rejected. -/
def findConstant? (constants : List LFConstantSchema) (name : Name) (arity : Nat) :
  Option LFConstantSchema :=
  (findConstantsByNameAndArity constants name arity).head?

/-- Build an instantiation from a constant-parameter telescope and raw arguments. -/
def instOfParams (params : List RuleMetaVar) (args : List Raw) : Instantiation := fun x =>
  match (params.zip args).find? (fun p => p.1.name == x.eraseMacroScopes) with
  | some p => p.2
  | none => .leanParam x

/-- Typed LF constant schemas with a given name, ignoring arity. -/
def findConstantsByName (constants : List LFConstantSchema) (name : Name) : List LFConstantSchema :=
  constants.filter (fun c => c.name == name.eraseMacroScopes)

/-- Whether a raw value is headed by a typed LF constant schema, ignoring arity. -/
def isKnownConstantValue (constants : List LFConstantSchema) : Raw → Bool
  | .tmConst n | .tyConst n => !(findConstantsByName constants n).isEmpty
  | .tmApp f _ | .tyApp f _ => !(findConstantsByName constants f).isEmpty
  | _ => false

/-- Find kernel-facing context-zone schemas by name. More than one match is ambiguous. -/
def contextZoneSchemasByName (zones : List ContextZoneSchema) (name : Name) :
  List ContextZoneSchema :=
  zones.filter (fun z => z.name == name.eraseMacroScopes)

/-- Find a kernel-facing context-zone schema by name. Validation paths should also reject
duplicate matches. -/
def findContextZoneSchema? (zones : List ContextZoneSchema) (name : Name) :
  Option ContextZoneSchema :=
  (contextZoneSchemasByName zones name).head?

/-- Find kernel-facing binder-class schemas by name. More than one match is ambiguous. -/
def binderClassSchemasByName (classes : List BinderClassSchema) (name : Name) :
  List BinderClassSchema :=
  classes.filter (fun c => c.name == name.eraseMacroScopes)

/-- Find a kernel-facing binder-class schema by name. Validation paths should also reject
duplicate matches. -/
def findBinderClassSchema? (classes : List BinderClassSchema) (name : Name) :
  Option BinderClassSchema :=
  (binderClassSchemasByName classes name).head?

/-- Format the arities available for a typed LF constant name. -/
def expectedConstantAritiesMessage (schemas : List LFConstantSchema) : String :=
  match schemas.map (fun c => c.params.length) with
  | [] => "no registered arity"
  | [n] => s!"{n} argument(s)"
  | ns => "one of " ++ String.intercalate ", " (ns.map (fun n => s!"{n} argument(s)"))

/-- Binder names carried by the raw LF lambda convention, if any. -/
def rawLamBinderNames? : Raw → Option (List Name)
  | .tmApp f args =>
      if f == `lam then
        match args.reverse with
        | [] => some []
        | _body :: revBinders =>
            let binders := revBinders.reverse
            binders.mapM fun
              | .leanParam x => some x.eraseMacroScopes
              | _ => none
      else
        none
  | _ => none

/-- A tiny kernel-facing type lookup for scoped-instantiation values, with diagnostics.

It trusts references to earlier scoped entries and typed LF constants/applications recorded on
the low-level signature. Application argument checking is shallow and first-order; when a
known typed LF constant is malformed, this reports the offending arity or argument type. -/
partial def inferValueTypeDetailed? (constants : List LFConstantSchema)
    (processed : List ScopedInstantiationEntry) : Raw → Except String (Option Raw)
  | .leanParam x | .ctxMeta x | .tyMeta x | .tmMeta x | .substMeta x =>
      pure ((processed.find? (fun e => e.name == x.eraseMacroScopes)).bind (fun e => e.type?))
  | .tmConst n | .tyConst n =>
      match findConstantsByNameAndArity constants n 0 with
      | [c] => pure (some c.resultType)
      | [] =>
          match findConstantsByName constants n with
          | [] => pure none
          | schemas =>
              throw s!"typed LF constant '{n}' is used with 0 argument(s), expected \
                {expectedConstantAritiesMessage schemas}"
      | _ =>
          throw s!"typed LF constant '{n}' with 0 argument(s) is ambiguous: duplicate typed LF \
            constant schemas"
  | .tmApp f args | .tyApp f args =>
      match findConstantsByNameAndArity constants f args.length with
      | [] =>
          match findConstantsByName constants f with
          | [] => pure none
          | schemas =>
              throw s!"typed LF constant '{f}' is used with {args.length} argument(s), expected \
                {expectedConstantAritiesMessage schemas}"
      | [c] => do
          checkArgs f args c.params
          pure (some (c.resultType.instantiate (instOfParams c.params args)))
      | _ =>
          throw s!"typed LF constant '{f}' with {args.length} argument(s) is ambiguous: duplicate \
            typed LF constant schemas"
  | _ => pure none
where
  checkArgs (f : Name) (args : List Raw) (params : List RuleMetaVar) : Except String Unit :=
    let rec go (idx : Nat) (priorArgs : List ScopedInstantiationEntry) :
      List Raw → List RuleMetaVar → Except String Unit
      | [], [] => pure ()
      | arg :: args, param :: params => do
          let expectedType? := param.type?.map (Raw.instantiate (instOf priorArgs))
          if let some expectedType := expectedType? then
            match ← inferValueTypeDetailed? constants (processed ++ priorArgs) arg with
            | some inferredType =>
                if inferredType != expectedType then
                  throw s!"argument {idx} of typed LF constant '{f}' has inferred type \
                    '{rawSourceString inferredType}', expected '{rawSourceString expectedType}'"
            | none => pure ()
          let entry : ScopedInstantiationEntry := {
            name := param.name
            sort := param.sort
            type? := expectedType?
            value := arg
          }
          go (idx + 1) (priorArgs ++ [entry]) args params
      | _, _ => throw s!"typed LF constant '{f}' argument count changed during checking"
    go 1 [] args params
  instOf (processed : List ScopedInstantiationEntry) : Instantiation := fun x =>
    match processed.find? (fun e => e.name == x.eraseMacroScopes) with
    | some e => e.value
    | none => .leanParam x

/-- A tiny kernel-facing type lookup for scoped-instantiation values.

This option-valued wrapper is useful for guards that only need success/failure; use
`inferValueTypeDetailed?` when reporting diagnostics. -/
def inferValueType? (constants : List LFConstantSchema) (processed : List ScopedInstantiationEntry)
    (value : Raw) : Option Raw :=
  match inferValueTypeDetailed? constants processed value with
  | .ok ty? => ty?
  | .error _ => none

/-- Validate a finite scoped instantiation against a rule metavariable telescope.

This is intentionally syntactic but kernel-facing: the domain, order, raw metavariable sorts,
zones, optional type annotations, references to earlier scoped entries, and any inferable
reference/constant value types must match the rule schema after substituting previous scoped
entries. -/
def validateAgainstWithConstants (constants : List LFConstantSchema)
    (σ : ScopedInstantiation) (metavariables : List RuleMetaVar) (ambientLocals : List Name :=
      []) : Except String Unit := do
  let rec firstDuplicate (seen : List Name) : List Name → Option Name
    | [] => none
    | n :: ns =>
        let n := n.eraseMacroScopes
        if seen.contains n then some n else firstDuplicate (n :: seen) ns
  if let some dup := firstDuplicate [] (metavariables.map (fun v => v.name)) then
    throw s!"rule metavariable telescope has duplicate name '{dup}'"
  if let some dup := firstDuplicate [] (σ.entries.map (fun e => e.name)) then
    throw s!"scoped instantiation has duplicate entry name '{dup}'"
  if σ.entries.length != metavariables.length then
    throw s!"scoped instantiation has {σ.entries.length} entrie(s), expected {metavariables.length}"
  let telescopeNames := metavariables.map (fun v => v.name)
  let sameDisplayButDifferentIdentity (ref : Name) (names : List Name) : List Name :=
    names.filter (fun n => n != ref && n.eraseMacroScopes == ref.eraseMacroScopes)
  let identitiesText (names : List Name) : String :=
    String.intercalate ", " (names.map localDiagnosticName)
  let checkOneScopedRef (entryName : Name) (field : String) (available : List Name) (ref : Name) :
    Except String Unit := do
    if available.contains ref || ambientLocals.contains ref then
      pure ()
    else if telescopeNames.contains ref then
      throw s!"scoped instantiation entry '{entryName}' has {field} referencing later \
        metavariable '{ref.eraseMacroScopes}'"
    else
      let sameAvailable := sameDisplayButDifferentIdentity ref (available ++ ambientLocals)
      if sameAvailable.length > 1 then
        throw s!"scoped instantiation entry '{entryName}' has {field} referencing ambiguous local \
          binder '{ref.eraseMacroScopes}'; available local identities are \
            {identitiesText sameAvailable}"
      else if let some current := sameAvailable.head? then
        throw s!"scoped instantiation entry '{entryName}' has {field} referencing stale local \
          '{ref.eraseMacroScopes}'; the available local with this printed name has identity \
            {localDiagnosticName current}, but the reference is {localDiagnosticName ref}"
      else
        let sameLater := sameDisplayButDifferentIdentity ref telescopeNames
        if !sameLater.isEmpty then
          throw s!"scoped instantiation entry '{entryName}' has {field} referencing later \
            metavariable '{ref.eraseMacroScopes}' with stale local identity \
              {localDiagnosticName ref}"
        else
          let staleHint := if ref == ref.eraseMacroScopes then "" else
            s!" (stale binder identity {reprStr ref})"
          throw s!"scoped instantiation entry '{entryName}' has {field} referencing unknown or \
            out-of-scope local '{ref.eraseMacroScopes}'{staleHint}"
  let checkScopedRefs (entryName : Name) (field : String) (available : List Name) (raw : Raw) :
    Except String Unit := do
    for ref in raw.localRefNames do
      checkOneScopedRef entryName field available ref
  let checkScopedJudgmentRefs (entryName : Name) (field : String) (available : List Name) (
    judgment : Judgment) : Except String Unit := do
    for ref in judgment.localRefNames do
      checkOneScopedRef entryName field available ref
  let instOf (processed : List ScopedInstantiationEntry) : Instantiation := fun x =>
    match processed.find? (fun e => e.name == x.eraseMacroScopes) with
    | some e => e.value
    | none => .leanParam x
  let rec go :
    List Name → List ScopedInstantiationEntry → List ScopedInstantiationEntry → List RuleMetaVar →
      Except String Unit
    | _, _, [], [] => pure ()
    | available, processed, e :: es, v :: vs => do
        if e.name != v.name then
          throw s!"scoped instantiation entry for '{e.name}' appears where metavariable \
            '{v.name}' was expected"
        if e.sort != v.sort then
          throw s!"scoped instantiation entry '{e.name}' has sort '{reprStr e.sort}', expected \
            '{reprStr v.sort}'"
        if e.zone? != v.zone? then
          throw s!"scoped instantiation entry '{e.name}' has zone '{reprStr e.zone?}', expected \
            '{reprStr v.zone?}'"
        let expectedType? := v.type?.map (Raw.instantiate (instOf processed))
        if e.type? != expectedType? then
          throw s!"scoped instantiation entry '{e.name}' has type annotation \
            '{rawOptionSourceString e.type?}', expected scoped type annotation \
              '{rawOptionSourceString expectedType?}'"
        if let some ty := e.type? then
          let ownBinders := (rawLamBinderNames? e.value).getD []
          checkScopedRefs e.name "type annotation" (available ++ ownBinders) ty
          ty.validateBuiltinConstructorDiscipline s!"scoped instantiation entry \
            '{e.name}'" "type annotation"
          if let some sortName := annotationCustomSort? ty then
            if e.sort != .custom sortName then
              throw s!"scoped instantiation entry '{e.name}' has type annotation headed by sort \
                '{sortName}', expected sort '{reprStr e.sort}'"
        checkScopedRefs e.name "value" available e.value
        e.value.validateBuiltinConstructorDiscipline s!"scoped instantiation entry \
          '{e.name}'" "value"
        if let some valueSort := e.value.shallowMetaSort? then
          if !e.sort.acceptsShallowValueSort valueSort then
            throw s!"scoped instantiation entry '{e.name}' has value headed by sort \
              '{reprStr valueSort}', expected '{reprStr e.sort}'"
        match ← inferValueTypeDetailed? constants processed e.value with
        | some inferredType =>
            if e.type? != some inferredType then
              throw s!"scoped instantiation entry '{e.name}' has value with inferred type \
                '{rawSourceString inferredType}', expected '{rawOptionSourceString e.type?}'"
        | none => pure ()
        if let some evidence := v.evidence? then
          checkScopedJudgmentRefs e.name "evidence annotation" (available ++ [e.name]) evidence
        let expectedEvidence? ←
          match v.evidence? with
          | some evidence =>
              match evidence.instantiateChecked (instOf (processed ++ [e])) with
              | .ok evidence => pure (some evidence)
              | .error err =>
                throw s!"scoped instantiation entry '{e.name}' has capture-unsafe evidence \
                  annotation: {err}"
          | none => pure none
        if e.evidence? != expectedEvidence? then
          throw s!"scoped instantiation entry '{e.name}' has evidence \
            '{judgmentOptionSourceString e.evidence?}', expected scoped evidence \
              '{judgmentOptionSourceString expectedEvidence?}'"
        if let some evidence := e.evidence? then
          checkScopedJudgmentRefs e.name "evidence" available evidence
          evidence.validateBuiltinConstructorDiscipline s!"scoped instantiation entry \
            '{e.name}'" "evidence"
        go (available ++ [e.name]) (processed ++ [e]) es vs
    | _, _, _, _ => throw "internal scoped-instantiation length mismatch"
  go [] [] σ.entries metavariables

/-- Validate scoped binder nodes appearing inside an instantiation against declared zone and
binder-class schemas. This is still a shallow syntactic pass, but it rejects replay artifacts
that mention unknown binder classes/zones or annotate a binder with an incompatible sort. -/
partial def validateScopedBinders (zones : List ContextZoneSchema) (classes :
  List BinderClassSchema)
    (owner : Name) (field : String) (raw : Raw) : Except String Unit :=
  let binderLabel (depth : Nat) (x : Name) : String :=
    s!"scoped binder #{depth} named '{x.eraseMacroScopes}'{localIdentitySuffix x}"
  let rec go (path : String) (binders : List Name) (depth : Nat) : Raw → Except String Unit
    | .ctxNil | .tmVar _ | .tmConst _ | .tyConst _ | .substEmpty | .leanParam _ |
      .ctxMeta _ | .tyMeta _ | .tmMeta _ | .substMeta _ => pure ()
    | .ctxExt Γ A | .tySubst Γ A | .tmSubst Γ A | .substComp Γ A | .substExt Γ A => do
        go (path ++ " / left child") binders depth Γ
        go (path ++ " / right child") binders depth A
    | .tyApp _ args | .tmApp _ args =>
        args.zipIdx.forM fun (arg, i) => go (path ++ s!" / argument {i + 1}") binders depth arg
    | .substId Γ =>
        go (path ++ " / substId context") binders depth Γ
    | .scopedBind zone cls x ty body => do
        let thisDepth := depth + 1
        let label := binderLabel thisDepth x
        if let some shadowed := binders.find? (fun y =>
          y.eraseMacroScopes == x.eraseMacroScopes) then
          let relation := if shadowed == x then "reusing" else "shadowing"
          throw s!"scoped instantiation entry '{owner}' has {path} with {label} {relation} \
            earlier binder identity {localDiagnosticName shadowed}; rename one binder or preserve \
              a stable hygienic reference"
        let zoneName := zone.eraseMacroScopes
        let clsName := cls.eraseMacroScopes
        let zoneSchema ←
          match contextZoneSchemasByName zones zoneName with
          | [] =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} in unknown \
              context zone '{zoneName}'"
          | [zoneSchema] => pure zoneSchema
          | _ =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} in ambiguous \
              context zone '{zoneName}': duplicate context-zone schemas"
        let classSchema ←
          match binderClassSchemasByName classes clsName with
          | [] =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} using unknown \
              binder class '{clsName}'"
          | [classSchema] => pure classSchema
          | _ =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} using ambiguous \
              binder class '{clsName}': duplicate binder-class schemas"
        if classSchema.zone != zoneSchema.name then
          throw s!"scoped instantiation entry '{owner}' has {path} with {label} using binder \
            class '{clsName}' in zone '{zoneName}', expected zone '{classSchema.zone}'"
        if let some sortName := annotationCustomSort? ty then
          if classSchema.boundSort != .custom sortName then
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} over type sort \
              '{sortName}', expected bound sort '{reprStr classSchema.boundSort}'"
        for dep in classSchema.dependsOn do
          match contextZoneSchemasByName zones dep with
          | [] =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} depending on \
              unknown context zone '{dep}'"
          | [_] => pure ()
          | _ =>
            throw s!"scoped instantiation entry '{owner}' has {path} with {label} depending on \
              ambiguous context zone '{dep}': duplicate context-zone schemas"
        go (path ++ s!" / {label} type") binders thisDepth ty
        go (path ++ s!" / {label} body") (x :: binders) thisDepth body
  go field [] 0 raw

/-- Validate a scoped instantiation against a rule telescope and the kernel-facing signature
metadata for typed constants, context zones, and binder classes. -/
def validateAgainstWithSignature (constants : List LFConstantSchema) (zones :
  List ContextZoneSchema)
    (classes : List BinderClassSchema) (σ : ScopedInstantiation)
    (metavariables : List RuleMetaVar) (ambientLocals : List Name := []) : Except String Unit := do
  validateAgainstWithConstants constants σ metavariables ambientLocals
  for e in σ.entries do
    if let some ty := e.type? then
      validateScopedBinders zones classes e.name "type annotation" ty
    validateScopedBinders zones classes e.name "value" e.value

/-- Validate a scoped instantiation without any signature-level LF constants in scope. -/
def validateAgainst (σ : ScopedInstantiation) (metavariables : List RuleMetaVar) :
  Except String Unit :=
  validateAgainstWithConstants [] σ metavariables

end ScopedInstantiation

/-- A raw kernel-facing, recursively replayed LF derivation tree.

The constructors are public syntax for replay payloads, not a trust boundary. Consumers that need
validated evidence should use `CheckedKernelLFDerivation.ofReplay`,
`CheckedKernelLFDerivation.ofDerivation`, or `KernelLFReplayCertificate.toChecked`; those wrappers
rerun executable replay validation against an explicit signature and context. Compared with the
older shallow `CheckedLFDerivation`, this payload is expressed in terms of low-level `Judgment`s,
finite scoped instantiations, typed metavariable entries, and certificate names. -/
inductive KernelLFDerivation where
  /-- Reference to a local theorem assumption in the ambient replay context. -/
  | assumption (name : Name) (statement : Judgment) : KernelLFDerivation
  /-- Reference to a previously checked theorem. -/
  | theoremRef (name : Name) (statement : Judgment) : KernelLFDerivation
  /-- Certificate-backed derivation leaf for an externally checked side-condition/theorem. -/
  | certificate (name : Name) (statement : Judgment) (certificateName : Name) : KernelLFDerivation
  /-- Rule application with a scoped instantiation, recursively replayed premises, and
  matched side-condition certificate names. -/
  | ruleApp (ruleName : Name) (conclusion : Judgment) (instantiation : ScopedInstantiation)
      (premises : List KernelLFDerivation) (sideConditionCertificateNames : List Name) :
      KernelLFDerivation
  deriving Inhabited, Repr, BEq

/-- A first-order rule schema with a metavariable context and certificate slots.

This records the low-level shape needed by replay validation: metavariables, premises,
side-condition slots, checked certificates, and the rule conclusion. -/
structure RuleSchema where
  /-- Rule name. -/
  name : Name
  /-- Metavariable context for this rule. -/
  metavariables : List RuleMetaVar := []
  /-- Premises that must be derived before applying the rule. -/
  premises : List Judgment := []
  /-- Side conditions that must be certified before applying the rule. -/
  sideConditions : List SideCondition := []
  /-- Stable certificate slots corresponding to the side conditions. -/
  sideConditionCertificates : List SideConditionCertificateSlot := []
  /-- Checked side-condition certificates already produced by executable hooks. -/
  checkedSideConditionCertificates : List SideConditionCertificate := []
  /-- Conclusion produced by the rule. -/
  conclusion : Judgment
  deriving Inhabited, Repr, BEq

namespace RuleSchema

/-- Instantiate the premises of a rule schema. -/
def instantiatePremises (r : RuleSchema) (σ : Instantiation) : List Judgment :=
  r.premises.map (Judgment.instantiate σ)

/-- Instantiate the conclusion of a rule schema. -/
def instantiateConclusion (r : RuleSchema) (σ : Instantiation) : Judgment :=
  r.conclusion.instantiate σ

/-- Capture-checking instantiation of one rule premise. -/
def instantiatePremiseChecked (_r : RuleSchema) (σ : Instantiation) (premise : Judgment) :
  Except String Judgment :=
  premise.instantiateChecked σ

/-- Capture-checking instantiation of the conclusion of a rule schema. -/
def instantiateConclusionChecked (r : RuleSchema) (σ : Instantiation) : Except String Judgment :=
  r.conclusion.instantiateChecked σ

end RuleSchema

/-- A user-declared object theory signature. -/
structure Signature where
  /-- Name of the theory. -/
  name : Name
  /-- Typed LF constants currently known to kernel-facing replay. -/
  constants : List LFConstantSchema := []
  /-- Context-zone schemas known to kernel-facing replay. -/
  contextZones : List ContextZoneSchema := []
  /-- Binder-class schemas known to kernel-facing replay. -/
  binderClasses : List BinderClassSchema := []
  /-- Conversion-plugin schemas known to kernel-facing replay. -/
  conversionPlugins : List ConversionPluginSchema := []
  /-- Primitive rule schemas currently registered for this theory. -/
  rules : List RuleSchema := []
  deriving Inhabited, Repr, BEq

namespace Signature

/-- All context-zone schemas with a given name. More than one match is ambiguous. -/
def contextZonesByName (sig : Signature) (zoneName : Name) : List ContextZoneSchema :=
  sig.contextZones.filter (fun z => z.name == zoneName.eraseMacroScopes)

/-- Find a context-zone schema by name. Validation paths should also reject duplicate matches. -/
def findContextZone? (sig : Signature) (zoneName : Name) : Option ContextZoneSchema :=
  (sig.contextZonesByName zoneName).head?

/-- Validate context-zone schemas for duplicate names and ordered dependencies. -/
def validateContextZoneSchemas (sig : Signature) : Except String Unit := do
  let rec go (seen : List Name) : List ContextZoneSchema → Except String Unit
    | [] => pure ()
    | z :: zs => do
        let zName := z.name.eraseMacroScopes
        if seen.contains zName then
          throw s!"signature '{sig.name}' has duplicate context-zone schema '{z.name}'"
        for dep in z.dependsOn do
          unless seen.contains dep.eraseMacroScopes do
            throw s!"context-zone schema '{z.name}' in signature '{sig.name}' depends on unknown \
              or later zone '{dep}'"
        go (zName :: seen) zs
  go [] sig.contextZones

/-- Validate binder-class schemas for duplicate names and declared zone dependencies. -/
def validateBinderClassSchemas (sig : Signature) : Except String Unit := do
  let rec go (seen : List Name) : List BinderClassSchema → Except String Unit
    | [] => pure ()
    | c :: cs => do
        let cName := c.name.eraseMacroScopes
        if seen.contains cName then
          throw s!"signature '{sig.name}' has duplicate binder-class schema '{c.name}'"
        match sig.contextZonesByName c.zone with
        | [] =>
          throw s!"binder-class schema '{c.name}' in signature '{sig.name}' uses unknown context \
            zone '{c.zone}'"
        | [_] => pure ()
        | _ =>
          throw s!"binder-class schema '{c.name}' in signature '{sig.name}' uses ambiguous \
            context zone '{c.zone}'"
        for dep in c.dependsOn do
          match sig.contextZonesByName dep with
          | [] =>
            throw s!"binder-class schema '{c.name}' in signature '{sig.name}' depends on unknown \
              context zone '{dep}'"
          | [_] => pure ()
          | _ =>
            throw s!"binder-class schema '{c.name}' in signature '{sig.name}' depends on \
              ambiguous context zone '{dep}'"
        go (cName :: seen) cs
  go [] sig.binderClasses

/-- All conversion-plugin schemas with a given name. More than one match is ambiguous. -/
def conversionPluginsByName (sig : Signature) (pluginName : Name) : List ConversionPluginSchema :=
  sig.conversionPlugins.filter (fun p => p.name == pluginName.eraseMacroScopes)

/-- Find a conversion-plugin schema by name. Validation paths should also reject duplicate matches.
-/
def findConversionPlugin? (sig : Signature) (pluginName : Name) : Option ConversionPluginSchema :=
  (sig.conversionPluginsByName pluginName).head?

/-- Validate that kernel-facing constants and rules do not use reserved LF names. -/
def validateNoKernelReservedNames (sig : Signature) : Except String Unit := do
  for c in sig.constants do
    if isLFKernelReservedName c.name then
      throw <| lfKernelReservedNameError "kernel LF constant" c.name
  for r in sig.rules do
    if isLFKernelReservedName r.name then
      throw <| lfKernelReservedNameError "kernel LF rule" r.name

/-- Validate conversion-plugin schemas for duplicate names and duplicate supported step kinds. -/
def validateConversionPluginSchemas (sig : Signature) : Except String Unit := do
  let rec goPlugins (seen : List Name) : List ConversionPluginSchema → Except String Unit
    | [] => pure ()
    | p :: ps => do
        let pName := p.name.eraseMacroScopes
        if seen.contains pName then
          throw s!"signature '{sig.name}' has duplicate conversion-plugin schema '{p.name}'"
        let rec goSteps (seenSteps : List ConversionStepKind) :
          List ConversionStepKind → Except String Unit
          | [] => pure ()
          | k :: ks => do
              if seenSteps.contains k then
                throw s!"conversion-plugin schema '{p.name}' in signature '{sig.name}' lists \
                  duplicate supported step '{k.label}'"
              goSteps (k :: seenSteps) ks
        goSteps [] p.supportedSteps
        goPlugins (pName :: seen) ps
  goPlugins [] sig.conversionPlugins

/-- Validate low-level structural schemas before replay consumes a signature. -/
def validateStructuralSchemas (sig : Signature) : Except String Unit := do
  sig.validateContextZoneSchemas
  sig.validateBinderClassSchemas
  sig.validateConversionPluginSchemas

/-- Check that a rule's zone annotations refer to declared zones with compatible raw sorts. -/
def validateRuleZones (sig : Signature) (ruleName : Name) (metavariables : List RuleMetaVar) :
  Except String Unit := do
  for v in metavariables do
    if let some zoneName := v.zone? then
      let zone ←
        match sig.contextZonesByName zoneName with
        | [] =>
          throw s!"rule '{ruleName}' metavariable '{v.name}' uses unknown context zone '{zoneName}'"
        | [zone] => pure zone
        | _ =>
          throw s!"rule '{ruleName}' metavariable '{v.name}' uses ambiguous context zone \
            '{zoneName}': duplicate context-zone schemas"
      if v.sort != zone.sort then
        throw s!"rule '{ruleName}' metavariable '{v.name}' has sort '{reprStr v.sort}' in context \
          zone '{zoneName}', expected zone sort '{reprStr zone.sort}'"

end Signature

/-- A previously checked LF theorem available to kernel-facing replay. -/
structure KernelLFTheoremEntry where
  /-- The theorem name. -/
  name : Name
  /-- The low-level judgment established by the theorem. -/
  statement : Judgment
  deriving Inhabited, Repr, BEq

/-- A checked external certificate available to kernel-facing replay. -/
structure KernelLFCertificateEntry where
  /-- The certified obligation name, e.g. a shape-inclusion theorem name. -/
  name : Name
  /-- The low-level statement certified by the external certificate. -/
  statement : Judgment
  /-- The checked certificate name/provenance token. -/
  certificateName : Name
  deriving Inhabited, Repr, BEq

/-- Trusted-context inputs for checking a kernel-facing replay tree.

The replay checker may use ambient local LF parameters, local theorem assumptions, earlier
checked LF theorems, and checked external certificates, but it validates references against
this explicit context rather than accepting arbitrary names in the tree. -/
structure KernelLFCheckContext where
  /-- Local LF parameters available while replaying a locally quantified LF theorem. -/
  localParameters : List Name := []
  /-- Local theorem assumptions available while replaying a locally quantified LF theorem. -/
  assumptions : List KernelLFTheoremEntry := []
  /-- Previously checked theorem statements. -/
  theorems : List KernelLFTheoremEntry := []
  /-- Checked external side-condition/theorem certificate statements. -/
  certificates : List KernelLFCertificateEntry := []
  /-- Checked external conversion certificates. -/
  conversionCertificates : List KernelLFConversionCertificateEntry := []
  deriving Inhabited, Repr, BEq

namespace KernelLFCheckContext

/-- All local theorem-assumption entries with a given name. More than one is an ambiguous replay
context. -/
def assumptionEntriesByName (ctx : KernelLFCheckContext) (name : Name) :
  List KernelLFTheoremEntry :=
  ctx.assumptions.filter (fun e => e.name == name.eraseMacroScopes)

/-- Find a local theorem-assumption entry by name. Prefer `assumptionEntriesByName` for validation
so duplicates
can be rejected rather than silently selecting the first entry. -/
def findAssumption? (ctx : KernelLFCheckContext) (name : Name) : Option KernelLFTheoremEntry :=
  ctx.assumptionEntriesByName name |>.head?

/-- All theorem entries with a given name. More than one is an ambiguous replay context. -/
def theoremEntriesByName (ctx : KernelLFCheckContext) (name : Name) : List KernelLFTheoremEntry :=
  ctx.theorems.filter (fun e => e.name == name.eraseMacroScopes)

/-- Find a theorem entry by name. Prefer `theoremEntriesByName` for validation so duplicates
can be rejected rather than silently selecting the first entry. -/
def findTheorem? (ctx : KernelLFCheckContext) (name : Name) : Option KernelLFTheoremEntry :=
  ctx.theoremEntriesByName name |>.head?

/-- All certificate entries with a given obligation name. More than one is ambiguous. -/
def certificateEntriesByName (ctx : KernelLFCheckContext) (name : Name) :
  List KernelLFCertificateEntry :=
  ctx.certificates.filter (fun e => e.name == name.eraseMacroScopes)

/-- Find a certificate entry by obligation name. Prefer `certificateEntriesByName` for
validation so duplicates can be rejected rather than silently selecting the first entry. -/
def findCertificate? (ctx : KernelLFCheckContext) (name : Name) : Option KernelLFCertificateEntry :=
  ctx.certificateEntriesByName name |>.head?

/-- All side-condition/theorem certificate entries with a given certificate token. -/
def certificateEntriesByCertificateName (ctx : KernelLFCheckContext) (certificateName : Name) :
  List KernelLFCertificateEntry :=
  ctx.certificates.filter (fun e => e.certificateName == certificateName.eraseMacroScopes)

/-- All external conversion-certificate entries with a given certificate token. -/
def conversionCertificateEntriesByCertificateName (ctx : KernelLFCheckContext)
    (certificateName : Name) : List KernelLFConversionCertificateEntry :=
  ctx.conversionCertificates.filter (fun e => e.certificateName == certificateName.eraseMacroScopes)

/-- Add a local theorem-assumption entry to the replay context. -/
def addAssumption (ctx : KernelLFCheckContext) (name : Name) (statement : Judgment) :
  KernelLFCheckContext :=
  { ctx with assumptions := ctx.assumptions ++ [{ name := name.eraseMacroScopes, statement :=
    statement }] }

/-- Add a checked theorem entry to the replay context. -/
def addTheorem (ctx : KernelLFCheckContext) (name : Name) (statement : Judgment) :
  KernelLFCheckContext :=
  { ctx with theorems := ctx.theorems ++ [{ name := name.eraseMacroScopes, statement :=
    statement }] }

end KernelLFCheckContext

namespace KernelLFConversionCertificate

/-- Statement/conclusion carried by a conversion-certificate tree. -/
def statement : KernelLFConversionCertificate → ConversionStatement
  | .refl stmt => stmt
  | .symm stmt _ => stmt
  | .trans stmt _ _ _ => stmt
  | .pluginStep stmt _ _ _ _ => stmt

/-- First duplicate name in a list, after erasing macro scopes. -/
def firstDuplicateName? (names : List Name) : Option Name :=
  let rec go (seen : List Name) : List Name → Option Name
    | [] => none
    | n :: ns =>
        let n := n.eraseMacroScopes
        if seen.contains n then some n else go (n :: seen) ns
  go [] names

/-- Raise a structured conversion-check failure. -/
def throwFailure (kind : ConversionCheckFailureKind) (message : String) :
    Except ConversionCheckFailure α :=
  throw (ConversionCheckFailure.mk kind message)

/-- Normalizer budget for raw executable level-conversion leaves. -/
def levelNormalizerRawFuelLimit : Nat := 4096

/-- Normal form for the first-order level fragment over raw syntax.

This mirrors `Kernel.LevelNormalizerKNF` and `LFElab.Kernel.LevelNormalizerObjNF`. The copies stay
separate so the compatibility raw checker and structural checker do not share trusted syntax. -/
structure LevelNormalizerRawNF where
  floor : Nat := 0
  atoms : List (Name × Nat) := []
  deriving Inhabited, Repr, BEq

namespace LevelNormalizerRawNF

/-- Look up an atom offset. -/
def atomOffset? (nf : LevelNormalizerRawNF) (atom : Name) : Option Nat :=
  (nf.atoms.find? (fun entry => entry.1 == atom.eraseMacroScopes)).map Prod.snd

/-- Set one atom to the maximum of the old and new offsets. -/
def setAtomMax (nf : LevelNormalizerRawNF) (atom : Name) (offset : Nat) :
    LevelNormalizerRawNF :=
  let atom := atom.eraseMacroScopes
  let rec go : List (Name × Nat) → List (Name × Nat)
    | [] => [(atom, offset)]
    | (name, old) :: rest =>
        if name == atom then
          (name, Nat.max old offset) :: rest
        else
          (name, old) :: go rest
  { nf with atoms := go nf.atoms }

/-- Successor of a raw level normal form. -/
def succ (nf : LevelNormalizerRawNF) : LevelNormalizerRawNF :=
  { floor := nf.floor + 1
    atoms := nf.atoms.map (fun entry => (entry.1, entry.2 + 1)) }

/-- Maximum of two raw level normal forms. -/
def max (lhs rhs : LevelNormalizerRawNF) : LevelNormalizerRawNF := Id.run do
  let mut out := { lhs with floor := Nat.max lhs.floor rhs.floor }
  for (atom, offset) in rhs.atoms do
    out := out.setAtomMax atom offset
  return out

/-- Equality of raw level normal forms, ignoring atom insertion order. -/
def equal (lhs rhs : LevelNormalizerRawNF) : Bool :=
  lhs.floor == rhs.floor && lhs.atoms.length == rhs.atoms.length &&
    lhs.atoms.all (fun entry => rhs.atomOffset? entry.1 == some entry.2)

/-- Render a compact normal-form summary. -/
def format (nf : LevelNormalizerRawNF) : String :=
  let floorPart := if nf.floor == 0 then [] else [toString nf.floor]
  let atomPart := nf.atoms.map fun (atom, offset) =>
    if offset == 0 then toString atom else s!"{atom}+{offset}"
  match floorPart ++ atomPart with
  | [] => "0"
  | [part] => part
  | parts => s!"max({String.intercalate ", " parts})"

end LevelNormalizerRawNF

/-- Normalize one raw level term for an executable conversion plugin. -/
def normalizeRawLevel (profile : LevelNormalizerRawProfile) (term : Raw)
    (fuel : Nat := levelNormalizerRawFuelLimit) :
    Except ConversionCheckFailure LevelNormalizerRawNF := do
  match fuel with
  | 0 =>
      throwFailure .unsupportedConversion <|
        s!"level normalizer budget exhausted while normalizing raw term \
          '{rawSourceString term}'"
  | fuel + 1 =>
      match term with
      | .tmConst n =>
          if n.eraseMacroScopes == profile.zeroName.eraseMacroScopes then
            pure {}
          else
            throwFailure .unsupportedConversion <|
              s!"level normalizer does not support raw closed constant \
                '{n.eraseMacroScopes}' as a neutral atom"
      | .tmMeta n | .leanParam n =>
          pure { atoms := [(n.eraseMacroScopes, 0)] }
      | .tyMeta n =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer raw atom '{n.eraseMacroScopes}' has type-metavariable sort; \
              only term metavariables and Lean parameters are supported as raw neutral levels"
      | .ctxMeta n =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer raw atom '{n.eraseMacroScopes}' has context-metavariable sort; \
              only term metavariables and Lean parameters are supported as raw neutral levels"
      | .substMeta n =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer raw atom '{n.eraseMacroScopes}' has substitution-metavariable \
              sort; only term metavariables and Lean parameters are supported as raw neutral \
              levels"
      | .tmApp f [arg] =>
          if f.eraseMacroScopes == profile.succName.eraseMacroScopes then
            return (← normalizeRawLevel profile arg fuel).succ
          else
            throwFailure .unsupportedConversion <|
              s!"level normalizer does not support raw application headed by \
                '{f.eraseMacroScopes}'"
      | .tmApp f [lhs, rhs] =>
          if f.eraseMacroScopes == profile.maxName.eraseMacroScopes then
            return LevelNormalizerRawNF.max (← normalizeRawLevel profile lhs fuel)
              (← normalizeRawLevel profile rhs fuel)
          else
            throwFailure .unsupportedConversion <|
              s!"level normalizer does not support raw application headed by \
                '{f.eraseMacroScopes}'"
      | .tmApp f _ =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer does not support raw application headed by '{f.eraseMacroScopes}'"
      | other =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer does not support raw term '{rawSourceString other}'"

/-- Validate a raw level-normalization conversion leaf. -/
def validateRawLevelNormalization (profile : LevelNormalizerRawProfile)
    (stmt : ConversionStatement) : Except ConversionCheckFailure Unit := do
  let lhs ← normalizeRawLevel profile stmt.lhs
  let rhs ← normalizeRawLevel profile stmt.rhs
  unless lhs.equal rhs do
    throwFailure .malformedCertificate <|
      s!"level-normalizer conversion failed: lhs normal form {lhs.format}, rhs normal form \
        {rhs.format}"

/-- Validate the currently implemented generic executable conversion step. -/
def validateExecutableStep (plugin : ConversionPluginSchema) (stmt : ConversionStatement)
    (kind : ConversionStepKind) : Except ConversionCheckFailure Unit := do
  match plugin.levelNormalizer?, kind with
  | some profile, .reindexing =>
      validateRawLevelNormalization profile stmt
  | _, .beta =>
      match stmt.lhs.betaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{plugin.name}' beta step reduces lhs to " ++
              s!"'{rawSourceString rhs}', expected rhs '{rawSourceString stmt.rhs}'"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{plugin.name}' beta step expected a raw `_app` " ++
            "redex whose function is a one-argument `lam`"
  | _, .eta =>
      match stmt.lhs.etaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{plugin.name}' eta step contracts lhs to " ++
              s!"'{rawSourceString rhs}', expected rhs '{rawSourceString stmt.rhs}'"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{plugin.name}' eta step expected a raw structural " ++
            "function or Sigma eta-redex"
  | _, _ =>
      throwFailure .unsupportedConversion <|
        s!"checked conversion plugin '{plugin.name}' has no generic executable engine for " ++
        s!"step '{kind.label}'"

/-- Validate a plugin-step leaf against the declared plugin trust boundary and context. -/
def validatePluginStepWithContextDetailed (ctx : KernelLFCheckContext) (sig : Signature)
    (stmt : ConversionStatement) (kind : ConversionStepKind)
    (externalCertificateName? : Option Name) (sideConditionCertificateNames : List Name)
    (payload : String) : Except ConversionCheckFailure Unit := do
  match stmt.validateBuiltinConstructorDiscipline s!"conversion plugin step '{stmt.plugin}'" with
  | .ok () => pure ()
  | .error err => throwFailure .malformedCertificate err
  let plugin ←
    match sig.conversionPluginsByName stmt.plugin with
    | [] =>
        throwFailure .unsupportedConversion
          s!"conversion certificate plugin step uses unknown conversion plugin '{stmt.plugin}'"
    | [plugin] => pure plugin
    | _ =>
        throwFailure .malformedCertificate <|
          s!"conversion certificate plugin step for '{stmt.plugin}' is ambiguous: " ++
          "signature contains duplicate conversion-plugin schemas"
  unless plugin.supportedSteps.contains kind do
    let supported :=
      if plugin.supportedSteps.isEmpty then "no supported step kinds"
      else String.intercalate ", " (plugin.supportedSteps.map ConversionStepKind.label)
    throwFailure .unsupportedConversion <|
      s!"conversion plugin '{plugin.name}' does not support step '{kind.label}' " ++
      s!"(supported: {supported})"
  if let some dup := firstDuplicateName? sideConditionCertificateNames then
    throwFailure .malformedCertificate <|
      s!"conversion plugin step for '{plugin.name}' has duplicate side-condition " ++
      s!"certificate reference '{dup}'"
  for certName in sideConditionCertificateNames do
    match ctx.certificateEntriesByCertificateName certName with
    | [] =>
        throwFailure .malformedCertificate <|
          s!"conversion plugin step for '{plugin.name}' references unavailable " ++
          s!"side-condition certificate '{certName}'"
    | [_] => pure ()
    | _ =>
        throwFailure .malformedCertificate <|
          s!"conversion plugin step for '{plugin.name}' references ambiguous " ++
          s!"side-condition certificate '{certName}'"
  match plugin.trust with
  | .executableChecked =>
      if externalCertificateName?.isSome then
        throwFailure .malformedCertificate <|
          s!"checked conversion plugin '{plugin.name}' must not use an external " ++
          "certificate token"
      validateExecutableStep plugin stmt kind
  | .externalCertificate =>
      let certName ←
        match externalCertificateName? with
        | some certName => pure certName
        | none =>
            throwFailure .externalCertificate <|
              s!"external-certificate conversion plugin '{plugin.name}' requires an " ++
              "external conversion certificate token"
      let entry ←
        match ctx.conversionCertificateEntriesByCertificateName certName with
        | [] =>
            throwFailure .externalCertificate <|
              s!"external conversion certificate '{certName}' is not available in the " ++
              "checked replay context"
        | [entry] => pure entry
        | _ =>
            throwFailure .externalCertificate <|
              s!"external conversion certificate '{certName}' is ambiguous in the " ++
              "checked replay context"
      if entry.statement != stmt then
        throwFailure .externalCertificate <|
          s!"external conversion certificate '{certName}' certifies statement " ++
          s!"'{entry.statement.sourceString}', expected '{stmt.sourceString}'"
      if entry.stepKind != kind then
        throwFailure .externalCertificate <|
          s!"external conversion certificate '{certName}' certifies step " ++
          s!"'{entry.stepKind.label}', expected '{kind.label}'"
  | .opaqueAssumption =>
      if externalCertificateName?.isSome then
        throwFailure .opaquePlugin <|
          s!"opaque conversion plugin '{plugin.name}' must not use an external " ++
          "certificate token"
      if payload == "" then
        throwFailure .opaquePlugin <|
          s!"opaque conversion plugin '{plugin.name}' requires a visible nonempty " ++
          "payload/diagnostic"

/-- Legacy string-returning plugin-step validation. -/
def validatePluginStepWithContext (ctx : KernelLFCheckContext) (sig : Signature)
    (stmt : ConversionStatement) (kind : ConversionStepKind)
    (externalCertificateName? : Option Name) (sideConditionCertificateNames : List Name)
    (payload : String) : Except String Unit :=
  match validatePluginStepWithContextDetailed ctx sig stmt kind externalCertificateName?
      sideConditionCertificateNames payload with
  | .ok () => .ok ()
  | .error err => .error err.message

/-- Recursive conversion-certificate checker after signature-level guards have run. -/
partial def checkWithContextDetailedCore (ctx : KernelLFCheckContext) (sig : Signature) :
    KernelLFConversionCertificate → ConversionStatement → Except ConversionCheckFailure Unit
  | .refl stmt, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate
          s!"conversion refl has statement '{stmt.sourceString}', expected \
            '{expected.sourceString}'"
      match stmt.validateBuiltinConstructorDiscipline s!"conversion refl for '{stmt.plugin}'" with
      | .ok () => pure ()
      | .error err => throwFailure .malformedCertificate err
      if stmt.lhs != stmt.rhs then
        throwFailure .malformedCertificate
          s!"conversion refl for plugin '{stmt.plugin}' has non-identical endpoints"
  | .symm stmt child, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate
          s!"conversion symm has statement '{stmt.sourceString}', expected \
            '{expected.sourceString}'"
      match stmt.validateBuiltinConstructorDiscipline s!"conversion symm for '{stmt.plugin}'" with
      | .ok () => pure ()
      | .error err => throwFailure .malformedCertificate err
      checkWithContextDetailedCore ctx sig child stmt.symm
  | .trans stmt middle left right, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate
          s!"conversion trans has statement '{stmt.sourceString}', expected \
            '{expected.sourceString}'"
      match stmt.validateBuiltinConstructorDiscipline s!"conversion trans for '{stmt.plugin}'" with
      | .ok () => pure ()
      | .error err => throwFailure .malformedCertificate err
      match middle.validateBuiltinConstructorDiscipline
          s!"conversion trans for '{stmt.plugin}'" "middle endpoint" with
      | .ok () => pure ()
      | .error err => throwFailure .malformedCertificate err
      checkWithContextDetailedCore ctx sig left (stmt.withRhs middle)
      checkWithContextDetailedCore ctx sig right (stmt.withLhs middle)
  | .pluginStep stmt kind externalCertificateName? sideConditionCertificateNames payload,
      expected => do
      if stmt != expected then
        throwFailure .malformedCertificate <|
          s!"conversion plugin step has statement '{stmt.sourceString}', expected " ++
          s!"'{expected.sourceString}'"
      validatePluginStepWithContextDetailed ctx sig stmt kind externalCertificateName?
        sideConditionCertificateNames payload

/-- Validate a generic conversion certificate against a declared plugin signature and context.

This entry validates kernel-reserved signature names once before recursive certificate checking. -/
def checkWithContextDetailed (ctx : KernelLFCheckContext) (sig : Signature)
    (cert : KernelLFConversionCertificate) (expected : ConversionStatement) :
    Except ConversionCheckFailure Unit := do
  match sig.validateNoKernelReservedNames with
  | .ok () => pure ()
  | .error err => throwFailure .malformedCertificate err
  checkWithContextDetailedCore ctx sig cert expected

/-- Validate a generic conversion certificate against a declared plugin signature and context. -/
def checkWithContext (ctx : KernelLFCheckContext) (sig : Signature)
    (cert : KernelLFConversionCertificate) (expected : ConversionStatement) : Except String Unit :=
  match checkWithContextDetailed ctx sig cert expected with
  | .ok () => .ok ()
  | .error err => .error err.message

/-- Validate a generic conversion certificate without any theorem/certificate context. -/
partial def checkDetailed (sig : Signature) (d : KernelLFConversionCertificate)
    (expected : ConversionStatement) : Except ConversionCheckFailure Unit :=
  checkWithContextDetailed {} sig d expected

/-- Validate a generic conversion certificate without any theorem/certificate context. -/
partial def check (sig : Signature) (d : KernelLFConversionCertificate)
    (expected : ConversionStatement) : Except String Unit :=
  checkWithContext {} sig d expected

end KernelLFConversionCertificate

/-- Checked wrapper for a kernel LF conversion certificate. -/
structure CheckedKernelLFConversionCertificate where
  /-- Kernel signature used for checking. -/
  signature : Signature
  /-- Replay/certificate context used for checking. -/
  context : KernelLFCheckContext := {}
  /-- Certified conversion statement. -/
  statement : ConversionStatement
  /-- Raw conversion-certificate tree that checked against `statement`. -/
  certificate : KernelLFConversionCertificate
  deriving Inhabited, Repr, BEq

namespace CheckedKernelLFConversionCertificate

/-- Check and wrap a kernel LF conversion certificate, preserving structured failures. -/
def checkDetailed (signature : Signature) (context : KernelLFCheckContext)
    (statement : ConversionStatement) (certificate : KernelLFConversionCertificate) :
    Except ConversionCheckFailure CheckedKernelLFConversionCertificate := do
  KernelLFConversionCertificate.checkWithContextDetailed context signature certificate statement
  pure { signature, context, statement, certificate }

/-- Check and wrap a kernel LF conversion certificate. -/
def check (signature : Signature) (context : KernelLFCheckContext)
    (statement : ConversionStatement) (certificate : KernelLFConversionCertificate) :
    Except String CheckedKernelLFConversionCertificate :=
  match checkDetailed signature context statement certificate with
  | .ok checked => .ok checked
  | .error err => .error err.message

/-- Check and wrap a certificate using the certificate's own statement. -/
def ofCertificate (signature : Signature) (context : KernelLFCheckContext)
    (certificate : KernelLFConversionCertificate) :
    Except String CheckedKernelLFConversionCertificate :=
  check signature context certificate.statement certificate

end CheckedKernelLFConversionCertificate

namespace KernelLFDerivation

/-- Statement/conclusion carried by a kernel-facing replay tree. -/
def statement : KernelLFDerivation → Judgment
  | .assumption _ stmt => stmt
  | .theoremRef _ stmt => stmt
  | .certificate _ stmt _ => stmt
  | .ruleApp _ conclusion _ _ _ => conclusion

/-- All rule schemas with a given name. More than one match is ambiguous. -/
def ruleSchemasByName (sig : Signature) (ruleName : Name) : List RuleSchema :=
  sig.rules.filter (fun r => r.name == ruleName.eraseMacroScopes)

/-- Find a rule schema by name. Validation paths should also reject duplicate matches. -/
def findRule? (sig : Signature) (ruleName : Name) : Option RuleSchema :=
  (ruleSchemasByName sig ruleName).head?

/-- Checked certificate names expected by a rule schema. -/
def expectedCertificateNames (r : RuleSchema) : List Name :=
  r.checkedSideConditionCertificates.map (fun c => c.name)

/-- First duplicate name in a list, after erasing macro scopes. -/
def firstDuplicateName? (names : List Name) : Option Name :=
  let rec go (seen : List Name) : List Name → Option Name
    | [] => none
    | n :: ns =>
        let n := n.eraseMacroScopes
        if seen.contains n then some n else go (n :: seen) ns
  go [] names

/-- Common validation for a kernel-facing rule-application replay node.

All replay consumers should call this helper before trusting the instantiated rule shape. It
checks zone annotations, scoped instantiation entries, scoped binders, instantiated conclusion,
premise count, and checked side-condition certificate names. -/
def validateRuleApplicationAgainstRule (sig : Signature) (ruleName : Name) (r : RuleSchema)
    (conclusion : Judgment) (inst : ScopedInstantiation) (premiseCount : Nat)
    (certificateNames : List Name) (ambientLocals : List Name := []) : Except String Unit := do
  sig.validateStructuralSchemas
  match ruleSchemasByName sig ruleName with
  | [] => throw s!"rule application uses unknown rule '{ruleName}'"
  | [_] => pure ()
  | _ =>
    throw s!"rule application '{ruleName}' is ambiguous: signature contains duplicate rule schemas"
  sig.validateRuleZones ruleName r.metavariables
  inst.validateAgainstWithSignature sig.constants sig.contextZones sig.binderClasses
    r.metavariables ambientLocals
  let expectedConclusion ←
    match r.instantiateConclusionChecked inst.asInstantiation with
    | .ok expectedConclusion => pure expectedConclusion
    | .error err =>
      throw s!"rule application '{ruleName}' has capture-unsafe conclusion instantiation: {err}"
  expectedConclusion.validateBuiltinConstructorDiscipline s!"rule application \
    '{ruleName}'" "instantiated conclusion"
  conclusion.validateBuiltinConstructorDiscipline s!"rule application '{ruleName}'" "conclusion"
  if !conclusion.alphaEq expectedConclusion then
    throw s!"rule application '{ruleName}' has conclusion '{judgmentSourceString conclusion}', \
      expected instantiated rule conclusion '{judgmentSourceString expectedConclusion}'"
  if premiseCount != r.premises.length then
    throw s!"rule application '{ruleName}' has {premiseCount} premise(s), expected \
      {r.premises.length}"
  for premise in r.premises do
    let expectedPremise ←
      match premise.instantiateChecked inst.asInstantiation with
      | .ok expectedPremise => pure expectedPremise
      | .error err =>
        throw s!"rule application '{ruleName}' has capture-unsafe premise instantiation: {err}"
    expectedPremise.validateBuiltinConstructorDiscipline s!"rule application \
      '{ruleName}'" "instantiated premise"
  if r.sideConditionCertificates.length != r.sideConditions.length then
    throw s!"rule application '{ruleName}' has {r.sideConditionCertificates.length} \
      side-condition certificate slot(s), expected {r.sideConditions.length}"
  if let some dup := firstDuplicateName? (r.sideConditions.map (fun sc => sc.name)) then
    throw s!"rule application '{ruleName}' has duplicate side-condition name '{dup}'"
  if let some dup := firstDuplicateName? (r.sideConditionCertificates.map (fun slot =>
    slot.name)) then
    throw s!"rule application '{ruleName}' has duplicate side-condition certificate slot name \
      '{dup}'"
  if r.checkedSideConditionCertificates.length != r.sideConditionCertificates.length then
    throw s!"rule application '{ruleName}' has {r.sideConditionCertificates.length} \
      side-condition certificate slot(s) but only {r.checkedSideConditionCertificates.length} \
        checked certificate(s)"
  for sc in r.sideConditions do
    let expectedCondition ←
      match sc.instantiateChecked inst.asInstantiation with
      | .ok expectedCondition => pure expectedCondition
      | .error err =>
        throw s!"rule application '{ruleName}' has capture-unsafe side-condition instantiation \
          for '{sc.name}': {err}"
    expectedCondition.validateBuiltinConstructorDiscipline s!"rule application \
      '{ruleName}'" s!"instantiated side-condition '{sc.name}'"
  for slot in r.sideConditionCertificates do
    slot.condition.validateBuiltinConstructorDiscipline s!"rule application \
      '{ruleName}'" s!"side-condition certificate slot '{slot.name}'"
  for cert in r.checkedSideConditionCertificates do
    cert.condition.validateBuiltinConstructorDiscipline s!"rule application \
      '{ruleName}'" s!"checked side-condition certificate '{cert.name}'"
    match r.sideConditionCertificates.filter (fun slot => slot.condition == cert.condition) with
    | [] =>
        throw s!"rule application '{ruleName}' has checked certificate '{cert.name}' whose \
          condition does not match any side-condition certificate slot"
    | [_] => pure ()
    | _ =>
        throw s!"rule application '{ruleName}' has checked certificate '{cert.name}' whose \
          condition ambiguously matches multiple side-condition certificate slots"
  for slot in r.sideConditionCertificates do
    match r.checkedSideConditionCertificates.filter (fun cert =>
      cert.condition == slot.condition) with
    | [] =>
        throw s!"rule application '{ruleName}' has side-condition certificate slot '{slot.name}' \
          with no matching checked certificate"
    | [_] => pure ()
    | _ =>
        throw s!"rule application '{ruleName}' has side-condition certificate slot '{slot.name}' \
          with multiple matching checked certificates"
  let expectedCerts := expectedCertificateNames r
  if let some dup := firstDuplicateName? expectedCerts then
    throw s!"rule application '{ruleName}' has duplicate checked side-condition certificate name \
      '{dup}'"
  if certificateNames != expectedCerts then
    throw s!"rule application '{ruleName}' has certificate names '{reprStr certificateNames}', \
      expected '{reprStr expectedCerts}'"

/-- Common validation for a local-assumption replay leaf against an explicit replay context. -/
def validateAssumptionWithContext (ctx : KernelLFCheckContext) (name : Name)
    (stmt : Judgment) : Except String Unit := do
  stmt.validateBuiltinConstructorDiscipline s!"local theorem assumption '{name}'" "statement"
  let entries := ctx.assumptionEntriesByName name
  let entry ←
    match entries with
    | [] =>
      throw s!"local theorem assumption '{name}' is not available in the checked replay context"
    | [entry] => pure entry
    | _ =>
      throw s!"local theorem assumption '{name}' is ambiguous: checked replay context contains \
        duplicate assumption entries"
  if !entry.statement.alphaEq stmt then
    throw s!"local theorem assumption '{name}' has statement '{judgmentSourceString stmt}', but \
      replay context records '{judgmentSourceString entry.statement}'"

/-- Common validation for a theorem-reference replay leaf against an explicit replay context. -/
def validateTheoremReferenceWithContext (ctx : KernelLFCheckContext) (name : Name)
    (stmt : Judgment) : Except String Unit := do
  stmt.validateBuiltinConstructorDiscipline s!"theorem reference '{name}'" "statement"
  let entries := ctx.theoremEntriesByName name
  let entry ←
    match entries with
    | [] => throw s!"theorem reference '{name}' is not available in the checked replay context"
    | [entry] => pure entry
    | _ =>
      throw s!"theorem reference '{name}' is ambiguous: checked replay context contains duplicate \
        theorem entries"
  if !entry.statement.alphaEq stmt then
    throw s!"theorem reference '{name}' has statement '{judgmentSourceString stmt}', but replay \
      context records '{judgmentSourceString entry.statement}'"

/-- Common validation for a certificate-backed replay leaf against an explicit certificate context.
-/
def validateCertificateWithContext (ctx : KernelLFCheckContext) (name : Name)
    (stmt : Judgment) (certificateName : Name) : Except String Unit := do
  stmt.validateBuiltinConstructorDiscipline s!"certificate-backed derivation '{name}'" "statement"
  let entries := ctx.certificateEntriesByName name
  let entry ←
    match entries with
    | [] =>
      throw s!"certificate-backed derivation '{name}' is not available in the checked certificate \
        context"
    | [entry] => pure entry
    | _ =>
      throw s!"certificate-backed derivation '{name}' is ambiguous: checked certificate context \
        contains duplicate entries"
  if !entry.statement.alphaEq stmt then
    throw s!"certificate-backed derivation '{name}' has statement \
      '{judgmentSourceString stmt}', but certificate context records \
        '{judgmentSourceString entry.statement}'"
  if entry.certificateName != certificateName then
    throw s!"certificate-backed derivation '{name}' uses certificate '{certificateName}', \
      expected '{entry.certificateName}'"

/-- Recursive worker for kernel-facing LF replay after signature-level guards have run.

This is the executable checker for the first-order replay shape. It validates rule membership,
finite scoped instantiations, recursive premise replay, instantiated conclusion equality, and exact
checked side-condition certificate names. -/
partial def checkWithContextCore (ctx : KernelLFCheckContext) (sig : Signature) :
    KernelLFDerivation → Judgment → Except String Unit
  | .assumption name stmt, expected => do
      if !stmt.alphaEq expected then
        throw s!"local theorem assumption '{name}' has statement \
          '{judgmentSourceString stmt}', expected '{judgmentSourceString expected}'"
      validateAssumptionWithContext ctx name stmt
  | .theoremRef name stmt, expected => do
      if !stmt.alphaEq expected then
        throw s!"theorem reference '{name}' has statement '{judgmentSourceString stmt}', \
          expected '{judgmentSourceString expected}'"
      validateTheoremReferenceWithContext ctx name stmt
  | .certificate name stmt certificateName, expected => do
      if !stmt.alphaEq expected then
        throw s!"certificate-backed derivation '{name}' has statement \
          '{judgmentSourceString stmt}', expected '{judgmentSourceString expected}'"
      validateCertificateWithContext ctx name stmt certificateName
  | .ruleApp ruleName conclusion inst premises certificateNames, expected => do
      if !conclusion.alphaEq expected then
        throw s!"rule application '{ruleName}' has conclusion \
          '{judgmentSourceString conclusion}', expected '{judgmentSourceString expected}'"
      let some r := findRule? sig ruleName
        | throw s!"rule application uses unknown rule '{ruleName}'"
      validateRuleApplicationAgainstRule sig ruleName r conclusion inst premises.length
        certificateNames ctx.localParameters
      for premiseDeriv in premises, premise in r.premises do
        let expectedPremise ←
          match premise.instantiateChecked inst.asInstantiation with
          | .ok expectedPremise => pure expectedPremise
          | .error err =>
            throw s!"rule application '{ruleName}' has capture-unsafe premise instantiation: {err}"
        checkWithContextCore ctx sig premiseDeriv expectedPremise

/-- Small trusted checker for kernel-facing LF replay artifacts.

This entry validates kernel-reserved signature names once before recursive replay checking. -/
def checkWithContext (ctx : KernelLFCheckContext) (sig : Signature)
    (d : KernelLFDerivation) (expected : Judgment) : Except String Unit := do
  sig.validateNoKernelReservedNames
  checkWithContextCore ctx sig d expected

/-- Small trusted checker for kernel-facing LF replay artifacts without theorem/certificate
references in scope. Prefer `checkWithContext` when checking user artifacts. -/
partial def check (sig : Signature) (d : KernelLFDerivation) (expected : Judgment) :
  Except String Unit :=
  checkWithContext {} sig d expected

end KernelLFDerivation

/-- A replay tree paired with the signature/context/statement it has been checked against.

Prefer this wrapper at API boundaries that consume replay evidence. `KernelLFDerivation` remains a
raw payload tree; this structure records the exact executable check that accepted it. -/
structure CheckedKernelLFDerivation where
  /-- Kernel-facing signature fragment used by the replay checker. -/
  signature : Signature
  /-- Theorem/certificate/local context used by the replay checker. -/
  context : KernelLFCheckContext := {}
  /-- Target judgment accepted by the replay checker. -/
  statement : Judgment
  /-- Raw replay payload that checked against `statement`. -/
  derivation : KernelLFDerivation
  deriving Inhabited, Repr, BEq

namespace CheckedKernelLFDerivation

/-- Re-run the executable replay check for this checked-wrapper payload. -/
def check (checked : CheckedKernelLFDerivation) : Except String Unit :=
  KernelLFDerivation.checkWithContext checked.context checked.signature checked.derivation
    checked.statement

/-- Build a checked replay wrapper from a raw replay payload and explicit target statement. -/
def ofReplay (signature : Signature) (context : KernelLFCheckContext) (statement : Judgment)
    (derivation : KernelLFDerivation) : Except String CheckedKernelLFDerivation := do
  KernelLFDerivation.checkWithContext context signature derivation statement
  pure { signature, context, statement, derivation }

/-- Build a checked replay wrapper using the replay tree's own carried statement. -/
def ofDerivation (signature : Signature) (context : KernelLFCheckContext)
    (derivation : KernelLFDerivation) : Except String CheckedKernelLFDerivation :=
  ofReplay signature context (KernelLFDerivation.statement derivation) derivation

end CheckedKernelLFDerivation

/-- A compact, independently checkable LF replay certificate.

This separates the small kernel-facing payload from renderer/model-generation conveniences:
a finite signature fragment, a replay context of already checked assumptions/certificates,
the target judgment, and the derivation tree.  It intentionally reuses
`KernelLFConversionCertificate` for conversion leaves rather than embedding conversion
engine details here. -/
structure KernelLFReplayCertificate where
  /-- Kernel-facing signature fragment needed to replay the derivation. -/
  signature : Signature
  /-- Previously checked local/theorem/certificate entries available to leaves. -/
  context : KernelLFCheckContext := {}
  /-- Target judgment checked by the certificate. -/
  statement : Judgment
  /-- Kernel-facing derivation tree for `statement`. -/
  derivation : KernelLFDerivation
  deriving Inhabited, Repr, BEq

namespace KernelLFReplayCertificate

/-- Validate a compact LF replay certificate using only the kernel-facing checker. -/
def check (cert : KernelLFReplayCertificate) : Except String Unit :=
  KernelLFDerivation.checkWithContext cert.context cert.signature cert.derivation cert.statement

/-- Convert a compact certificate to the preferred checked replay wrapper. -/
def toChecked (cert : KernelLFReplayCertificate) : Except String CheckedKernelLFDerivation :=
  CheckedKernelLFDerivation.ofReplay cert.signature cert.context cert.statement cert.derivation

/-- Rule names mentioned by the certificate's finite signature fragment. -/
def ruleNames (cert : KernelLFReplayCertificate) : List Name :=
  cert.signature.rules.map (fun r => r.name)

/-- External theorem/certificate names available to leaves in the replay context. -/
def contextNames (cert : KernelLFReplayCertificate) : List Name :=
  cert.context.assumptions.map (fun e => e.name) ++
    cert.context.theorems.map (fun e => e.name) ++
    cert.context.certificates.map (fun e => e.name)

end KernelLFReplayCertificate

namespace KernelLFDerivation

/- Context-relative replay evidence below is the preferred kernel-facing Lean witness.

Primitive-rule-only replay trees are raw payloads, while checked replay wrappers and
`KernelLFDerivation.ContextDeriv` record the signature and replay context that were validated. -/

/-- Find a rule schema by name together with its membership proof in a rule list. -/
def findRuleInListWithProof? (ruleName : Name) :
    (rules : List RuleSchema) → Option { r : RuleSchema // r ∈ rules }
  | [] => none
  | r :: rs =>
      if r.name == ruleName.eraseMacroScopes then
        some ⟨r, List.Mem.head _⟩
      else
        match findRuleInListWithProof? ruleName rs with
        | some ⟨r', h⟩ => some ⟨r', List.Mem.tail _ h⟩
        | none => none

/-- Find a rule schema by name together with its membership proof in a signature. -/
def findRuleWithProof? (sig : Signature) (ruleName : Name) :
    Option { r : RuleSchema // r ∈ sig.rules } :=
  findRuleInListWithProof? ruleName sig.rules

/-- Find a theorem-context entry by name together with its membership proof. -/
def findTheoremEntryInListWithProof? (name : Name) :
    (theorems : List KernelLFTheoremEntry) → Option { e : KernelLFTheoremEntry // e ∈ theorems }
  | [] => none
  | e :: es =>
      if e.name == name.eraseMacroScopes then
        some ⟨e, List.Mem.head _⟩
      else
        match findTheoremEntryInListWithProof? name es with
        | some ⟨e', h⟩ => some ⟨e', List.Mem.tail _ h⟩
        | none => none

/-- Find a theorem-context entry by name together with its membership proof. -/
def findTheoremEntryWithProof? (ctx : KernelLFCheckContext) (name : Name) :
    Option { e : KernelLFTheoremEntry // e ∈ ctx.theorems } :=
  findTheoremEntryInListWithProof? name ctx.theorems

/-- Find a certificate-context entry by obligation name together with its membership proof. -/
def findCertificateEntryInListWithProof? (name : Name) :
    (certificates : List KernelLFCertificateEntry) →
      Option { e : KernelLFCertificateEntry // e ∈ certificates }
  | [] => none
  | e :: es =>
      if e.name == name.eraseMacroScopes then
        some ⟨e, List.Mem.head _⟩
      else
        match findCertificateEntryInListWithProof? name es with
        | some ⟨e', h⟩ => some ⟨e', List.Mem.tail _ h⟩
        | none => none

/-- Find a certificate-context entry by obligation name together with its membership proof. -/
def findCertificateEntryWithProof? (ctx : KernelLFCheckContext) (name : Name) :
    Option { e : KernelLFCertificateEntry // e ∈ ctx.certificates } :=
  findCertificateEntryInListWithProof? name ctx.certificates

/- Trusted kernel evidence relative to an explicit theorem/certificate replay context.

This evidence records scoped assumptions for previously checked LF theorems and checked external
certificates. It does not make those assumptions absolute Lean theorems; rather, it records exactly
which context entry a replay leaf uses, so later model interpretation or kernel hardening can audit
the remaining trusted boundary. -/
mutual
  /-- Trusted kernel evidence relative to an explicit theorem/certificate replay context. -/
  inductive ContextDeriv (sig : Signature) (ctx : KernelLFCheckContext) : Judgment → Type 1 where
    /-- Use a local theorem assumption from the replay context. -/
    | assumption (e : KernelLFTheoremEntry) :
        e ∈ ctx.assumptions →
        ContextDeriv sig ctx e.statement
    /-- Use a previously checked theorem from the replay context. -/
    | theorem (e : KernelLFTheoremEntry) :
        e ∈ ctx.theorems →
        ContextDeriv sig ctx e.statement
    /-- Use a checked external certificate from the replay context. -/
    | certificate (e : KernelLFCertificateEntry) :
        e ∈ ctx.certificates →
        ContextDeriv sig ctx e.statement
    /-- Apply an instantiated primitive rule from the signature. -/
    | rule (r : RuleSchema) (σ : Instantiation) :
        r ∈ sig.rules →
        ContextDerivList sig ctx σ r.premises →
        ContextDeriv sig ctx (r.instantiateConclusion σ)

  /-- Trusted kernel evidence for a list of instantiated premises. -/
  inductive ContextDerivList (sig : Signature) (ctx : KernelLFCheckContext) :
      Instantiation → List Judgment → Type 1 where
    /-- No premises. -/
    | nil {σ : Instantiation} : ContextDerivList sig ctx σ []
    /-- A derivation of the first premise and derivations of the remaining premises. -/
    | cons {σ : Instantiation} {p : Judgment} {ps : List Judgment} :
        ContextDeriv sig ctx (p.instantiate σ) →
        ContextDerivList sig ctx σ ps →
        ContextDerivList sig ctx σ (p :: ps)
end

noncomputable section KernelLFContextDerivProducer

mutual
  /-- Convert a checked kernel-facing replay tree into trusted evidence relative to an
  explicit theorem/certificate context. The checker `checkWithContext` remains the executable
  validation step; this producer repeats the equality/provenance checks needed for dependent
  casts and produces an auditable `ContextDeriv` witness. -/
  partial def toContextDeriv? (ctx : KernelLFCheckContext) (sig : Signature) :
      (d : KernelLFDerivation) → Except String (ContextDeriv sig ctx (statement d))
    | .assumption name stmt => do
        match validateAssumptionWithContext ctx name stmt with
        | .ok () => pure PUnit.unit
        | .error err => throw err
        let some ⟨entry, hmem⟩ := findTheoremEntryInListWithProof? name ctx.assumptions
          | throw s!"local theorem assumption '{name}' is not available in the checked replay \
            context"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.assumption entry hmem)
        else
          throw s!"local theorem assumption '{name}' has statement \
            '{judgmentSourceString stmt}', but replay context records \
              '{judgmentSourceString entry.statement}'"
    | .theoremRef name stmt => do
        match validateTheoremReferenceWithContext ctx name stmt with
        | .ok () => pure PUnit.unit
        | .error err => throw err
        let some ⟨entry, hmem⟩ := findTheoremEntryWithProof? ctx name
          | throw s!"theorem reference '{name}' is not available in the checked replay context"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.theorem entry hmem)
        else
          throw s!"theorem reference '{name}' has statement '{judgmentSourceString stmt}', but \
            replay context records '{judgmentSourceString entry.statement}'"
    | .certificate name stmt certificateName => do
        match validateCertificateWithContext ctx name stmt certificateName with
        | .ok () => pure PUnit.unit
        | .error err => throw err
        let some ⟨entry, hmem⟩ := findCertificateEntryWithProof? ctx name
          | throw s!"certificate-backed derivation '{name}' is not available in the checked \
            certificate context"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.certificate entry hmem)
        else
          throw s!"certificate-backed derivation '{name}' has statement \
            '{judgmentSourceString stmt}', but certificate context records \
              '{judgmentSourceString entry.statement}'"
    | .ruleApp ruleName conclusion inst premises certificateNames => do
        let some ⟨r, hr⟩ := findRuleWithProof? sig ruleName
          | throw s!"rule application uses unknown rule '{ruleName}'"
        match validateRuleApplicationAgainstRule sig ruleName r conclusion inst premises.length
          certificateNames ctx.localParameters with
        | .ok () => pure PUnit.unit
        | .error err => throw err
        let σ := inst.asInstantiation
        let premiseDerivs ← toContextDerivList? ctx sig σ premises r.premises
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : r.instantiateConclusion σ = conclusion then
          pure (h ▸ ContextDeriv.rule r σ hr premiseDerivs)
        else
          throw s!"rule application '{ruleName}' has conclusion \
            '{judgmentSourceString conclusion}', expected instantiated rule conclusion \
              '{judgmentSourceString (r.instantiateConclusion σ)}'"

  /-- Convert a list of replay premise trees into trusted context-relative premise evidence. -/
  partial def toContextDerivList? (ctx : KernelLFCheckContext) (sig : Signature) (σ :
    Instantiation) :
      (ds : List KernelLFDerivation) → (ps : List Judgment) →
        Except String (ContextDerivList sig ctx σ ps)
    | [], [] => pure ContextDerivList.nil
    | d :: ds, p :: ps => do
        match p.instantiateChecked σ with
        | .ok _ => pure PUnit.unit
        | .error err =>
          throw s!"context derivation producer has capture-unsafe premise instantiation: {err}"
        let dDeriv ← toContextDeriv? ctx sig d
        let rest ← toContextDerivList? ctx sig σ ds ps
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : statement d = p.instantiate σ then
          pure (ContextDerivList.cons (h ▸ dDeriv) rest)
        else
          throw s!"premise replay has statement '{judgmentSourceString (statement d)}', \
            expected '{judgmentSourceString (p.instantiate σ)}'"
    | ds, ps =>
        throw s!"context derivation producer has {ds.length} premise derivation(s), expected \
          {ps.length}"
end

end KernelLFContextDerivProducer

end KernelLFDerivation

namespace CheckedKernelLFDerivation

noncomputable section ContextDerivProducer

/-- Produce context-relative trusted evidence from a checked kernel replay wrapper.

This is the preferred producer at trust boundaries: it re-runs the executable check recorded by the
wrapper before extracting the dependent `ContextDeriv` witness. -/
def toContextDeriv? (checked : CheckedKernelLFDerivation) :
    Except String
      (KernelLFDerivation.ContextDeriv checked.signature checked.context checked.statement) :=
  match checked.check with
  | .error err => throw err
  | .ok () => do
      let derivation ← KernelLFDerivation.toContextDeriv? checked.context checked.signature
        checked.derivation
      let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
      if h : KernelLFDerivation.statement checked.derivation = checked.statement then
        pure (h ▸ derivation)
      else
        let carried := KernelLFDerivation.statement checked.derivation
        throw <|
          s!"checked replay wrapper has statement '{judgmentSourceString checked.statement}', " ++
            s!"but its derivation carries '{judgmentSourceString carried}'"

end ContextDerivProducer

end CheckedKernelLFDerivation

/-- Interpretation data for a list of premises. -/
def InterpPremises (interpJudgment : Judgment → Type) (σ : Instantiation) :
    List Judgment → Type
  | [] => PUnit
  | p :: ps => interpJudgment (p.instantiate σ) × InterpPremises interpJudgment σ ps

/-- A semantic model interface for a signature.

The user provides the interpretation of every judgment and every primitive rule.
The interpretation target is `Type`, not `Prop`, so equality/path/cell judgments may
be proof-relevant. -/
structure Model (sig : Signature) where
  /-- Interpretation of an object judgment as Lean data. -/
  interpJudgment : Judgment → Type
  /-- Interpretation/realizer for each primitive rule. -/
  interpRule :
    (r : RuleSchema) →
    (σ : Instantiation) →
    r ∈ sig.rules →
    InterpPremises interpJudgment σ r.premises →
    interpJudgment (r.instantiateConclusion σ)

/-- A semantic model for a signature together with realizers for an explicit kernel replay
context of previously checked LF theorems and external certificates. -/
structure ContextModel (sig : Signature) (ctx : KernelLFCheckContext) extends Model sig where
  /-- Interpretation/realizer for each local theorem assumption in the replay context. -/
  interpAssumption :
    (e : KernelLFTheoremEntry) →
    e ∈ ctx.assumptions →
    interpJudgment e.statement
  /-- Interpretation/realizer for each theorem assumption in the replay context. -/
  interpTheorem :
    (e : KernelLFTheoremEntry) →
    e ∈ ctx.theorems →
    interpJudgment e.statement
  /-- Interpretation/realizer for each checked external certificate assumption in the replay
  context. -/
  interpCertificate :
    (e : KernelLFCertificateEntry) →
    e ∈ ctx.certificates →
    interpJudgment e.statement

namespace KernelLFDerivation

mutual
  /-- Soundness/interpretation of context-relative trusted replay evidence in a
  context model. The model must provide realizers for theorem/certificate leaves. -/
  def ContextDeriv.interp {sig : Signature} {ctx : KernelLFCheckContext}
      (M : ContextModel sig ctx) :
      {J : Judgment} → ContextDeriv sig ctx J → M.interpJudgment J
    | _, .assumption e h => M.interpAssumption e h
    | _, .theorem e h => M.interpTheorem e h
    | _, .certificate e h => M.interpCertificate e h
    | _, .rule r σ hr premises =>
        M.interpRule r σ hr (ContextDerivList.interp M premises)

  /-- Interpret context-relative trusted replay evidence for a list of premises. -/
  def ContextDerivList.interp {sig : Signature} {ctx : KernelLFCheckContext}
      (M : ContextModel sig ctx) :
      {σ : Instantiation} → {ps : List Judgment} → ContextDerivList sig ctx σ ps →
        InterpPremises M.interpJudgment σ ps
    | _, [], .nil => PUnit.unit
    | _, _ :: _, .cons d ds => ⟨ContextDeriv.interp M d, ContextDerivList.interp M ds⟩
end

end KernelLFDerivation

end InternalLean
