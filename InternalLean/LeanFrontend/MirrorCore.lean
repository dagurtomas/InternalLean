/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Registry
public meta import Lean.Elab.Term

/-!
# Experimental Lean mirror backend core

This module contains the core LF-to-Lean mirror translation and declaration-generation helpers.
It stays below `InternalLean.LFElab` in the import graph so the direct-LF checker can optionally
use the mirror as a theory-body fast path without depending on the command frontend.
-/

@[expose] public meta section

open Lean Elab Command Term Meta

namespace InternalLean

/-- User-facing message data extracted from a caught mirror exception. -/
def lfMirrorExceptionMessageData : Exception → MessageData
  | .error _ msg => msg
  | .internal _ _ => m!"internal exception"

/-- Lean binder info corresponding to an LF source-binder visibility in mirror declarations. -/
def lfMirrorBinderInfoOfVisibility : BinderVisibility → BinderInfo
  | .explicit => .default
  | .implicit => .implicit

/-- Erase macro scopes throughout an LF metadata expression for mirror-internal use. -/
partial def lfMirrorEraseObjExprScopes : ObjExpr → ObjExpr
  | .ident n => .ident n.eraseMacroScopes
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (lfMirrorEraseObjExprScopes f) (lfMirrorEraseObjExprScopes a)
  | .arrow x A B => .arrow (x.map Name.eraseMacroScopes) (lfMirrorEraseObjExprScopes A)
      (lfMirrorEraseObjExprScopes B)
  | .funArrow x A B => .funArrow (x.map Name.eraseMacroScopes) (lfMirrorEraseObjExprScopes A)
      (lfMirrorEraseObjExprScopes B)
  | .sigma x A B => .sigma (x.map Name.eraseMacroScopes) (lfMirrorEraseObjExprScopes A)
      (lfMirrorEraseObjExprScopes B)
  | .pair a b => .pair (lfMirrorEraseObjExprScopes a) (lfMirrorEraseObjExprScopes b)
  | .fst e => .fst (lfMirrorEraseObjExprScopes e)
  | .snd e => .snd (lfMirrorEraseObjExprScopes e)
  | .lam xs body => .lam (xs.map Name.eraseMacroScopes) (lfMirrorEraseObjExprScopes body)
  | .jeq lhs rhs => .jeq (lfMirrorEraseObjExprScopes lhs) (lfMirrorEraseObjExprScopes rhs)

/-- Free object-level identifiers in an LF metadata expression, for mirror substitution hygiene. -/
partial def lfMirrorFreeIdentifiers : ObjExpr → NameSet
  | .ident n => ({} : NameSet).insert n.eraseMacroScopes
  | .sort | .univ _ => {}
  | .app f a => lfMirrorFreeIdentifiers f ++ lfMirrorFreeIdentifiers a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let free := lfMirrorFreeIdentifiers A ++ lfMirrorFreeIdentifiers B
      match x with
      | some x => free.erase x.eraseMacroScopes
      | none => free
  | .pair a b => lfMirrorFreeIdentifiers a ++ lfMirrorFreeIdentifiers b
  | .fst e | .snd e => lfMirrorFreeIdentifiers e
  | .lam xs body =>
      let free := lfMirrorFreeIdentifiers body
      xs.foldl (fun free x => free.erase x.eraseMacroScopes) free
  | .jeq lhs rhs => lfMirrorFreeIdentifiers lhs ++ lfMirrorFreeIdentifiers rhs

/-- Names occurring in the range of a mirror substitution. -/
def lfMirrorSubstRangeFreeIdentifiers (subst : NameMap ObjExpr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (_, value) in subst.toList do
    out := out ++ lfMirrorFreeIdentifiers value
  return out

/-- Keys occurring in a mirror substitution. -/
def lfMirrorSubstKeys (subst : NameMap ObjExpr) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (n, _) in subst.toList do
    out := out.insert n.eraseMacroScopes
  return out

/-- Pick a deterministic fresh mirror binder name avoiding a finite set. -/
def lfMirrorFreshNameAvoiding (base : Name) (avoid : NameSet) : Name :=
  let base := base.eraseMacroScopes
  let rec go : Nat → Nat → Name
    | 0, n => .str base s!"_hyg{n}"
    | fuel + 1, n =>
        let candidate := .str base s!"_hyg{n}"
        if avoid.contains candidate then go fuel (n + 1) else candidate
  if avoid.contains base then go (avoid.size + 32) 0 else base

/-- Rename occurrences of a currently-bound identifier in a mirror expression. -/
partial def lfMirrorRenameBoundOccurrences (oldName newName : Name) : ObjExpr → ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      if n == oldName.eraseMacroScopes then .ident newName.eraseMacroScopes else .ident n
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (lfMirrorRenameBoundOccurrences oldName newName f)
      (lfMirrorRenameBoundOccurrences oldName newName a)
  | .arrow x A B =>
      let A := lfMirrorRenameBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            lfMirrorRenameBoundOccurrences oldName newName B
          .arrow (some x) A B
      | none => .arrow none A (lfMirrorRenameBoundOccurrences oldName newName B)
  | .funArrow x A B =>
      let A := lfMirrorRenameBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            lfMirrorRenameBoundOccurrences oldName newName B
          .funArrow (some x) A B
      | none => .funArrow none A (lfMirrorRenameBoundOccurrences oldName newName B)
  | .sigma x A B =>
      let A := lfMirrorRenameBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            lfMirrorRenameBoundOccurrences oldName newName B
          .sigma (some x) A B
      | none => .sigma none A (lfMirrorRenameBoundOccurrences oldName newName B)
  | .pair a b => .pair (lfMirrorRenameBoundOccurrences oldName newName a)
      (lfMirrorRenameBoundOccurrences oldName newName b)
  | .fst e => .fst (lfMirrorRenameBoundOccurrences oldName newName e)
  | .snd e => .snd (lfMirrorRenameBoundOccurrences oldName newName e)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      let body := if clean.contains oldName.eraseMacroScopes then body else
        lfMirrorRenameBoundOccurrences oldName newName body
      .lam clean body
  | .jeq lhs rhs => .jeq (lfMirrorRenameBoundOccurrences oldName newName lhs)
      (lfMirrorRenameBoundOccurrences oldName newName rhs)

/-- Whether a mirror substitution would capture under `binder`. -/
def lfMirrorSubstWouldCaptureUnderBinder (binder : Name) (subst : NameMap ObjExpr)
    (body : ObjExpr) : Bool :=
  let binder := binder.eraseMacroScopes
  let bodyFree := lfMirrorFreeIdentifiers body
  subst.toList.any fun (n, value) =>
    let n := n.eraseMacroScopes
    n != binder && bodyFree.contains n && (lfMirrorFreeIdentifiers value).contains binder

/-- Substitute identifiers in an LF expression for mirror expected-type propagation. -/
partial def lfMirrorSubstParams (subst : NameMap ObjExpr) : ObjExpr → ObjExpr
  | .ident n =>
      let n := n.eraseMacroScopes
      (subst.find? n).getD (.ident n)
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (lfMirrorSubstParams subst f) (lfMirrorSubstParams subst a)
  | .arrow x A B =>
      let A := lfMirrorSubstParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfMirrorSubstWouldCaptureUnderBinder x subst B then
              let avoid := lfMirrorFreeIdentifiers B ++ lfMirrorSubstRangeFreeIdentifiers subst ++
                lfMirrorSubstKeys subst |>.insert x
              let y := lfMirrorFreshNameAvoiding x avoid
              (y, lfMirrorRenameBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .arrow (some x) A (lfMirrorSubstParams subst B)
      | none => .arrow none A (lfMirrorSubstParams subst B)
  | .funArrow x A B =>
      let A := lfMirrorSubstParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfMirrorSubstWouldCaptureUnderBinder x subst B then
              let avoid := lfMirrorFreeIdentifiers B ++ lfMirrorSubstRangeFreeIdentifiers subst ++
                lfMirrorSubstKeys subst |>.insert x
              let y := lfMirrorFreshNameAvoiding x avoid
              (y, lfMirrorRenameBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .funArrow (some x) A (lfMirrorSubstParams subst B)
      | none => .funArrow none A (lfMirrorSubstParams subst B)
  | .sigma x A B =>
      let A := lfMirrorSubstParams subst A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let subst := subst.erase x
          let (x, B, subst) :=
            if lfMirrorSubstWouldCaptureUnderBinder x subst B then
              let avoid := lfMirrorFreeIdentifiers B ++ lfMirrorSubstRangeFreeIdentifiers subst ++
                lfMirrorSubstKeys subst |>.insert x
              let y := lfMirrorFreshNameAvoiding x avoid
              (y, lfMirrorRenameBoundOccurrences x y B, subst.erase y)
            else
              (x, B, subst)
          .sigma (some x) A (lfMirrorSubstParams subst B)
      | none => .sigma none A (lfMirrorSubstParams subst B)
  | .pair a b => .pair (lfMirrorSubstParams subst a) (lfMirrorSubstParams subst b)
  | .fst e => .fst (lfMirrorSubstParams subst e)
  | .snd e => .snd (lfMirrorSubstParams subst e)
  | .lam xs body =>
      let clean := xs.map Name.eraseMacroScopes
      let (clean, body, subst) := Id.run do
        let mut out := #[]
        let mut body := body
        let mut subst := subst
        for x in clean do
          let substBase := subst.erase x
          if lfMirrorSubstWouldCaptureUnderBinder x substBase body then
            let avoid := lfMirrorFreeIdentifiers body ++
              lfMirrorSubstRangeFreeIdentifiers substBase ++ lfMirrorSubstKeys substBase |>.insert x
            let y := lfMirrorFreshNameAvoiding x avoid
            body := lfMirrorRenameBoundOccurrences x y body
            subst := substBase.erase y
            out := out.push y
          else
            subst := substBase
            out := out.push x
        return (out, body, subst)
      .lam clean (lfMirrorSubstParams subst body)
  | .jeq lhs rhs => .jeq (lfMirrorSubstParams subst lhs) (lfMirrorSubstParams subst rhs)

/-- Substitute one LF/object identifier in an expression for mirror expected-type propagation. -/
def lfMirrorSubstSingleParam (x : Name) (value body : ObjExpr) : ObjExpr :=
  let subst : NameMap ObjExpr := {}
  let subst := subst.insert x.eraseMacroScopes value
  lfMirrorSubstParams subst body

register_option internalLean.mirrorBackend.compareWithLF : Bool := {
  defValue := false
  descr := "after a successful experimental Lean mirror check, also run the ordinary LF checker"
}

register_option internalLean.mirrorBackend.checkTheoryBodies : Bool := {
  defValue := false
  descr := "use the experimental Lean mirror backend as an opt-in fast checker for checked \
    theory-block syntax_def and lf_def bodies"
}

register_option internalLean.mirrorBackend.compareTheoryBodiesWithLF : Bool := {
  defValue := false
  descr := "when the experimental Lean mirror theory-body checker is enabled, also run the \
    ordinary LF body checker and report any mismatch"
}

/-- Translate an object-level universe expression to the corresponding Lean universe. -/
def lfMirrorLeanLevelOfLevelExpr (u : LevelExpr) : Level :=
  LevelExpr.toLeanLevel u

/-- Convert an object-level universe to the corresponding Lean sort for the mirror backend. -/
def lfMirrorLeanSortOfLevel (u : LevelExpr) : Expr :=
  mkSort (Level.succ (lfMirrorLeanLevelOfLevelExpr u))

/-- Lean universe parameters used by mirror declarations for one checked theory. -/
def lfMirrorLevelParamNamesForSignature (sig : HLSignature) : List Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  for u in sig.levelParams do
    let u := u.eraseMacroScopes
    unless seen.contains u do
      seen := seen.insert u
      out := out.push u
  return out.toList

/-- Lean universe arguments used when referring to mirror declarations for one signature. -/
def lfMirrorLevelArgsForSignature (sig : HLSignature) : List Level :=
  (lfMirrorLevelParamNamesForSignature sig).map Level.param

/-- Lean universe arguments used when referring to mirror declarations for one registered theory. -/
def lfMirrorLevelArgsForTheory (theoryName : Name) : CoreM (List Level) := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  pure <| lfMirrorLevelArgsForSignature checkedHL

/-- Lean constant reference for a generated mirror declaration with explicit universe arguments. -/
def mkLFMirrorConstWithLevels (theoryName sourceName : Name) (levelArgs : List Level) : Expr :=
  mkConst (lfMirrorDeclName theoryName sourceName) levelArgs

/-- Lean constant reference for a generated mirror declaration in a registered theory. -/
def mkLFMirrorConst (theoryName sourceName : Name) : MetaM Expr := do
  pure <| mkLFMirrorConstWithLevels theoryName sourceName (← lfMirrorLevelArgsForTheory theoryName)

/-- Local LF-to-Lean mirror translation environment. -/
abbrev LFMirrorLocalMap := NameMap Expr

/-- Components of a translated Lean `Sigma` type, including universe levels. -/
structure LFMirrorSigmaLeanParts where
  /-- Universe level of the first component type. -/
  fstLevel : Level
  /-- Universe level of the second component type. -/
  sndLevel : Level
  /-- First component type. -/
  fstType : Expr
  /-- Second component type family. -/
  sndType : Expr

/-- Return the Lean universe level of a translated type expression. -/
def lfMirrorTypeUniverseLevel (typeExpr : Expr) : MetaM Level := do
  match ← whnf (← inferType typeExpr) with
  | .sort (.succ u) => pure u
  | .sort .zero => pure .zero
  | type => throwError "Lean mirror expected a type expression, got type\n  {type}"

/-- Recognize a Lean mirror Sigma type. -/
def lfMirrorSigmaType? (e : Expr) : Option LFMirrorSigmaLeanParts :=
  match e.getAppFn, e.getAppArgs with
  | .const n [u, v], #[AExpr, betaExpr] =>
      if n == ``Sigma then
        some { fstLevel := u, sndLevel := v, fstType := AExpr, sndType := betaExpr }
      else
        none
  | _, _ => none

/-- Translate one LF expression to the experimental Lean mirror expression. -/
partial def lfMirrorExprWithLevels (theoryName : Name) (levelArgs : List Level)
    (locals : LFMirrorLocalMap) : ObjExpr → MetaM Expr
  | .ident n => do
      if let some e := locals.find? n.eraseMacroScopes then
        pure e
      else
        pure <| mkLFMirrorConstWithLevels theoryName n levelArgs
  | .sort => pure (lfMirrorLeanSortOfLevel .zero)
  | .univ u => pure (lfMirrorLeanSortOfLevel u)
  | .app f a => do
      let fExpr ← lfMirrorExprWithLevels theoryName levelArgs locals f
      let fType ← whnf (← inferType fExpr)
      match fType with
      | .forallE _ domain _ _ =>
          pure (mkApp fExpr
            (← lfMirrorExprWithLeanExpected theoryName levelArgs locals domain a))
      | _ =>
          pure (mkApp fExpr (← lfMirrorExprWithLevels theoryName levelArgs locals a))
  | .arrow binder? A B | .funArrow binder? A B => do
      let AExpr ← lfMirrorExprWithLevels theoryName levelArgs locals A
      let binderName := (binder?.getD `_arg).eraseMacroScopes
      withLocalDecl binderName .default AExpr fun x => do
        let locals :=
          match binder? with
          | some n => locals.insert n.eraseMacroScopes x
          | none => locals
        let BExpr ← lfMirrorExprWithLevels theoryName levelArgs locals B
        mkForallFVars #[x] BExpr
  | .sigma binder? A B => do
      let parts ← lfMirrorSigmaParts theoryName levelArgs locals binder? A B
      pure (mkApp2 (mkConst ``Sigma [parts.fstLevel, parts.sndLevel]) parts.fstType
        parts.sndType)
  | .pair a b => do
      -- Without an expected type, infer a nondependent Sigma package from component mirror types.
      -- Dependent pairs should use `lfMirrorTermWithExpectedWithLevels`, which has the LF Sigma
      -- type.
      let aExpr ← lfMirrorExprWithLevels theoryName levelArgs locals a
      let bExpr ← lfMirrorExprWithLevels theoryName levelArgs locals b
      let AExpr ← inferType aExpr
      let BExpr ← inferType bExpr
      let u ← lfMirrorTypeUniverseLevel AExpr
      let v ← lfMirrorTypeUniverseLevel BExpr
      let betaExpr ← withLocalDecl `_fst .default AExpr fun x => mkLambdaFVars #[x] BExpr
      pure (mkApp4 (mkConst ``Sigma.mk [u, v]) AExpr betaExpr aExpr bExpr)
  | .fst e => do
      let eExpr ← lfMirrorExprWithLevels theoryName levelArgs locals e
      let eType ← whnf (← inferType eExpr)
      let some parts := lfMirrorSigmaType? eType
        | throwError "cannot translate LF fst; mirror term does not have Sigma type:\n  {eType}"
      pure (mkApp3 (mkConst ``Sigma.fst [parts.fstLevel, parts.sndLevel]) parts.fstType
        parts.sndType eExpr)
  | .snd e => do
      let eExpr ← lfMirrorExprWithLevels theoryName levelArgs locals e
      let eType ← whnf (← inferType eExpr)
      let some parts := lfMirrorSigmaType? eType
        | throwError "cannot translate LF snd; mirror term does not have Sigma type:\n  {eType}"
      pure (mkApp3 (mkConst ``Sigma.snd [parts.fstLevel, parts.sndLevel]) parts.fstType
        parts.sndType eExpr)
  | .lam xs _body => do
      throwError "cannot translate LF lambda with binders {xs.toList} to the Lean mirror without \
        an expected function type"
  | .jeq lhs rhs => do
      -- Judgmental equality expressions are mirror-encoded as an opaque type family only in later
      -- phases. Current mirror checks should use declared judgment heads instead.
      throwError "Lean mirror backend does not yet support raw judgmental equality expression \
        '{ObjExpr.toString (.jeq lhs rhs)}'"
where
  /-- Translate an LF term using an expected Lean mirror type. -/
  lfMirrorExprWithLeanExpected (theoryName : Name) (levelArgs : List Level)
      (locals : LFMirrorLocalMap) (expected : Expr) : ObjExpr → MetaM Expr
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
            lfMirrorExprWithLeanExpected theoryName levelArgs locals expected body
        go 0 expected locals
    | .pair a b => do
        let expected ← whnf expected
        let some parts := lfMirrorSigmaType? expected
          | throwError "Lean mirror expected a Sigma type while translating pair, got\n  \
              {expected}"
        let aExpr ← lfMirrorExprWithLeanExpected theoryName levelArgs locals parts.fstType a
        let bExpected ← whnf (mkApp parts.sndType aExpr)
        let bExpr ← lfMirrorExprWithLeanExpected theoryName levelArgs locals bExpected b
        pure (mkApp4 (mkConst ``Sigma.mk [parts.fstLevel, parts.sndLevel]) parts.fstType
          parts.sndType aExpr bExpr)
    | e => do
        let eExpr ← lfMirrorExprWithLevels theoryName levelArgs locals e
        let actual ← inferType eExpr
        unless ← withTransparency .all <| isDefEq actual expected do
          throwError "Lean mirror translated LF term with type\n  {actual}\nexpected\n  {expected}"
        pure eExpr

  /-- Translate the components of an LF Sigma type to Lean mirror `Sigma` components. -/
  lfMirrorSigmaParts (theoryName : Name) (levelArgs : List Level)
      (locals : LFMirrorLocalMap) (binder? : Option Name) (A B : ObjExpr) :
      MetaM LFMirrorSigmaLeanParts := do
    let AExpr ← lfMirrorExprWithLevels theoryName levelArgs locals A
    let u ← lfMirrorTypeUniverseLevel AExpr
    let binderName := (binder?.getD `_fst).eraseMacroScopes
    withLocalDecl binderName .default AExpr fun x => do
      let locals :=
        match binder? with
        | some n => locals.insert n.eraseMacroScopes x
        | none => locals
      let BExpr ← lfMirrorExprWithLevels theoryName levelArgs locals B
      let v ← lfMirrorTypeUniverseLevel BExpr
      let beta ← mkLambdaFVars #[x] BExpr
      pure { fstLevel := u, sndLevel := v, fstType := AExpr, sndType := beta }

/-- Translate one LF expression to the mirror for a registered theory. -/
def lfMirrorExpr (theoryName : Name) (locals : LFMirrorLocalMap) (e : ObjExpr) : MetaM Expr := do
  lfMirrorExprWithLevels theoryName (← lfMirrorLevelArgsForTheory theoryName) locals e

/-- Translate an LF term to the Lean mirror while using an expected LF type when needed. -/
partial def lfMirrorTermWithExpectedWithLevels (theoryName : Name) (levelArgs : List Level)
    (locals : LFMirrorLocalMap) (expected : ObjExpr) : ObjExpr → MetaM Expr
  | .lam xs body => do
      let rec go (i : Nat) (expected : ObjExpr) (locals : LFMirrorLocalMap) : MetaM Expr := do
        if _h : i < xs.size then
          match expected with
          | .arrow binder? A B | .funArrow binder? A B => do
              let AExpr ← lfMirrorExprWithLevels theoryName levelArgs locals A
              let sourceName := xs[i]!.eraseMacroScopes
              withLocalDecl sourceName .default AExpr fun x => do
                let binderName := (binder?.getD sourceName).eraseMacroScopes
                let locals := locals.insert sourceName x |>.insert binderName x
                let nextExpected :=
                  match binder? with
                  | some n => lfMirrorSubstSingleParam n (.ident sourceName) B
                  | none => B
                let bodyExpr ← go (i + 1) nextExpected locals
                mkLambdaFVars #[x] bodyExpr
          | _ => throwError "Lean mirror expected a function type while translating lambda, got \
              '{ObjExpr.toString expected}'"
        else
          lfMirrorTermWithExpectedWithLevels theoryName levelArgs locals expected body
      go 0 expected locals
  | .pair a b => do
      match expected with
      | .sigma binder? A B => do
          let parts ← lfMirrorExprWithLevels.lfMirrorSigmaParts theoryName levelArgs locals
            binder? A B
          let aExpr ← lfMirrorTermWithExpectedWithLevels theoryName levelArgs locals A a
          let bExpected :=
            match binder? with
            | some n => lfMirrorSubstSingleParam n (lfMirrorEraseObjExprScopes a) B
            | none => B
          let bExpr ← lfMirrorTermWithExpectedWithLevels theoryName levelArgs locals bExpected b
          pure (mkApp4 (mkConst ``Sigma.mk [parts.fstLevel, parts.sndLevel]) parts.fstType
            parts.sndType aExpr bExpr)
      | _ => throwError "Lean mirror expected a Sigma type while translating pair, got \
          '{ObjExpr.toString expected}'"
  | e => do
      let expectedLean ← lfMirrorExprWithLevels theoryName levelArgs locals expected
      let eExpr ← lfMirrorExprWithLevels theoryName levelArgs locals e
      let actual ← inferType eExpr
      unless ← withTransparency .all <| isDefEq actual expectedLean do
        throwError "Lean mirror translated LF term with type\n  {actual}\nexpected\n  \
          {expectedLean}"
      pure eExpr

/-- Translate an LF term to the mirror for a registered theory, using an expected LF type. -/
def lfMirrorTermWithExpected (theoryName : Name) (locals : LFMirrorLocalMap)
    (expected value : ObjExpr) : MetaM Expr := do
  lfMirrorTermWithExpectedWithLevels theoryName (← lfMirrorLevelArgsForTheory theoryName) locals
    expected value

/-- Build a Lean mirror function type from LF parameters and a result expression. -/
def lfMirrorForallTypeWithLevels (theoryName : Name) (levelArgs : List Level)
    (params : Array HLBinding) (result : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) (fvars : Array Expr) : MetaM Expr := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExprWithLevels theoryName levelArgs locals p.typeExpr
      let binderInfo := lfMirrorBinderInfoOfVisibility p.visibility
      withLocalDecl p.name.eraseMacroScopes binderInfo ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x) (fvars.push x)
    else
      mkForallFVars fvars (← result locals)
  go 0 {} #[]

/-- Build a Lean mirror function type for a registered theory. -/
def lfMirrorForallType (theoryName : Name) (params : Array HLBinding)
    (result : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  lfMirrorForallTypeWithLevels theoryName (← lfMirrorLevelArgsForTheory theoryName) params result

/-- Build a closed Lean mirror lambda from LF parameters and a body expression. -/
def lfMirrorLambdaValueWithLevels (theoryName : Name) (levelArgs : List Level)
    (params : Array HLBinding) (body : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) (fvars : Array Expr) : MetaM Expr := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExprWithLevels theoryName levelArgs locals p.typeExpr
      let binderInfo := lfMirrorBinderInfoOfVisibility p.visibility
      withLocalDecl p.name.eraseMacroScopes binderInfo ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x) (fvars.push x)
    else
      mkLambdaFVars fvars (← body locals)
  go 0 {} #[]

/-- Build a closed Lean mirror lambda for a registered theory. -/
def lfMirrorLambdaValue (theoryName : Name) (params : Array HLBinding)
    (body : LFMirrorLocalMap → MetaM Expr) : MetaM Expr := do
  lfMirrorLambdaValueWithLevels theoryName (← lfMirrorLevelArgsForTheory theoryName) params body

/-- Run a mirror-meta computation under local LF parameters. -/
def withLFMirrorLocalsWithLevels {α : Type} (theoryName : Name) (levelArgs : List Level)
    (params : Array HLBinding) (k : LFMirrorLocalMap → MetaM α) : MetaM α := do
  let rec go (i : Nat) (locals : LFMirrorLocalMap) : MetaM α := do
    if h : i < params.size then
      let p := params[i]
      let ty ← lfMirrorExprWithLevels theoryName levelArgs locals p.typeExpr
      let binderInfo := lfMirrorBinderInfoOfVisibility p.visibility
      withLocalDecl p.name.eraseMacroScopes binderInfo ty fun x =>
        go (i + 1) (locals.insert p.name.eraseMacroScopes x)
    else
      k locals
  go 0 {}

/-- Run a mirror-meta computation under local LF parameters for a registered theory. -/
def withLFMirrorLocals {α : Type} (theoryName : Name) (params : Array HLBinding)
    (k : LFMirrorLocalMap → MetaM α) : MetaM α := do
  withLFMirrorLocalsWithLevels theoryName (← lfMirrorLevelArgsForTheory theoryName) params k

/-- Add one experimental Lean mirror axiom if it is not already present. -/
def addLFMirrorAxiomIfMissing (declName : Name) (levelParams : List Name) (type : Expr) :
    CoreM Unit := do
  unless (← getEnv).contains declName do
    addAndCompile (Declaration.axiomDecl {
      name := declName
      levelParams := levelParams
      type := type
      isUnsafe := false })

/-- Add one experimental Lean mirror definition if it is not already present. -/
def addLFMirrorDefinitionIfMissing (declName : Name) (levelParams : List Name)
    (type value : Expr) : CoreM Unit := do
  unless (← getEnv).contains declName do
    MetaM.run' do
      let actual ← inferType value
      unless ← withTransparency .all <| isDefEq actual type do
        throwError "cannot add Lean mirror definition '{declName}': translated value has \
          type\n  {actual}\nexpected\n  {type}"
    let defVal : DefinitionVal := {
      name := declName
      levelParams := levelParams
      type := type
      value := value
      hints := ReducibilityHints.abbrev
      safety := DefinitionSafety.safe }
    addDecl (Declaration.defnDecl defVal)

/-- One mirror declaration waiting for its dependencies to be available in Lean. -/
inductive LFMirrorPendingDecl where
  | syntaxSort : SyntaxSortDecl → LFMirrorPendingDecl
  | syntaxAbbrev : SyntaxAbbrevDecl → LFMirrorPendingDecl
  | syntaxDef : SyntaxDefDecl → LFMirrorPendingDecl
  | judgment : JudgmentDecl → LFMirrorPendingDecl
  | judgmentAbbrev : JudgmentAbbrevDecl → LFMirrorPendingDecl
  | lfOpaqueConst : LFOpaqueConstDecl → LFMirrorPendingDecl
  | lfObjectDef : LFObjectDefDecl → LFMirrorPendingDecl
  | rule : RuleDecl → LFMirrorPendingDecl
  | lfJudgmentTheorem : LFJudgmentTheoremDecl → LFMirrorPendingDecl

namespace LFMirrorPendingDecl

/-- User-facing kind label for a pending mirror declaration. -/
def kind : LFMirrorPendingDecl → String
  | .syntaxSort _ => "syntax_sort"
  | .syntaxAbbrev _ => "syntax_abbrev"
  | .syntaxDef _ => "syntax_def"
  | .judgment _ => "judgment"
  | .judgmentAbbrev _ => "judgment_abbrev"
  | .lfOpaqueConst _ => "lf_opaque"
  | .lfObjectDef _ => "lf_def"
  | .rule _ => "rule"
  | .lfJudgmentTheorem _ => "judgment_theorem"

/-- User-facing declaration name for a pending mirror declaration. -/
def name : LFMirrorPendingDecl → Name
  | .syntaxSort d => d.name
  | .syntaxAbbrev d => d.name
  | .syntaxDef d => d.name
  | .judgment d => d.name
  | .judgmentAbbrev d => d.name
  | .lfOpaqueConst d => d.name
  | .lfObjectDef d => d.name
  | .rule d => d.name
  | .lfJudgmentTheorem d => d.name

end LFMirrorPendingDecl

/-- Add one mirror declaration, assuming any declarations it references already exist. -/
def addLFMirrorPendingDecl (theoryName : Name) (levelParams : List Name)
    (levelArgs : List Level) (decl : LFMirrorPendingDecl) : CoreM Unit := do
  if (← getEnv).contains (lfMirrorDeclName theoryName decl.name) then
    return
  match decl with
  | .syntaxSort d =>
      let type ← MetaM.run' <| lfMirrorForallTypeWithLevels theoryName levelArgs d.params
        (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
      addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type
  | .syntaxAbbrev d =>
      let (type, value) ← MetaM.run' do
        let type ← lfMirrorForallTypeWithLevels theoryName levelArgs d.params fun locals => do
          inferType (← lfMirrorExprWithLevels theoryName levelArgs locals d.value)
        let value ← lfMirrorLambdaValueWithLevels theoryName levelArgs d.params
          (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals d.value)
        pure (type, value)
      addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) levelParams type value
  | .syntaxDef d =>
      let type ← MetaM.run' <| lfMirrorForallTypeWithLevels theoryName levelArgs d.params
        (fun _ => pure (lfMirrorLeanSortOfLevel d.resultLevel))
      match d.value? with
      | some valueExpr =>
          let value ← MetaM.run' <| lfMirrorLambdaValueWithLevels theoryName levelArgs d.params
            (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals valueExpr)
          addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) levelParams type value
      | none =>
          addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type
  | .judgment d =>
      let type ← MetaM.run' <| lfMirrorForallTypeWithLevels theoryName levelArgs d.params
        (fun _ => pure (mkSort (Level.succ .zero)))
      addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type
  | .judgmentAbbrev d =>
      let (type, value) ← MetaM.run' do
        let type ← lfMirrorForallTypeWithLevels theoryName levelArgs d.params fun locals => do
          inferType (← lfMirrorExprWithLevels theoryName levelArgs locals d.value)
        let value ← lfMirrorLambdaValueWithLevels theoryName levelArgs d.params
          (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals d.value)
        pure (type, value)
      addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) levelParams type value
  | .lfOpaqueConst d =>
      if let some typeExpr := d.typeExpr? then
        let type ← MetaM.run' <| lfMirrorForallTypeWithLevels theoryName levelArgs d.params
          (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals typeExpr)
        addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type
  | .lfObjectDef d =>
      let (type, value) ← MetaM.run' do
        let type ← lfMirrorExprWithLevels theoryName levelArgs {} d.typeExpr
        let value ← lfMirrorTermWithExpectedWithLevels theoryName levelArgs {} d.typeExpr d.value
        pure (type, value)
      addLFMirrorDefinitionIfMissing (lfMirrorDeclName theoryName d.name) levelParams type value
  | .rule d =>
      let type ← MetaM.run' do
        let premiseParams := d.premises.map fun p =>
          ({ name := p.name, typeExpr := p.judgmentExpr, visibility := .explicit } : HLBinding)
        lfMirrorForallTypeWithLevels theoryName levelArgs (d.params ++ premiseParams)
          (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals d.conclusionExpr)
      addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type
  | .lfJudgmentTheorem d =>
      let type ← MetaM.run' <| lfMirrorForallTypeWithLevels theoryName levelArgs d.binders
        (fun locals => lfMirrorExprWithLevels theoryName levelArgs locals d.judgmentExpr)
      addLFMirrorAxiomIfMissing (lfMirrorDeclName theoryName d.name) levelParams type

/-- Add mirror declarations in dependency order by retrying declarations blocked on later heads. -/
partial def addLFMirrorPendingDecls (theoryName : Name) (levelParams : List Name)
    (levelArgs : List Level) (decls : Array LFMirrorPendingDecl) : CoreM Unit := do
  if decls.isEmpty then
    return
  let mut rest : Array LFMirrorPendingDecl := #[]
  let mut blocked : Array (LFMirrorPendingDecl × MessageData) := #[]
  for decl in decls do
    try
      addLFMirrorPendingDecl theoryName levelParams levelArgs decl
    catch ex =>
      rest := rest.push decl
      blocked := blocked.push (decl, lfMirrorExceptionMessageData ex)
  if rest.isEmpty then
    return
  if rest.size == decls.size then
    let details := blocked.toList.take 5 |>.map fun (decl, reason) =>
      m!"  {decl.kind} '{decl.name}': {reason}"
    throwError m!"could not construct Lean mirror declarations for type theory \
      '{theoryName}'. Blocked declaration(s):\n{MessageData.joinSep details Format.line}"
  addLFMirrorPendingDecls theoryName levelParams levelArgs rest

/-- Node count for a source LF expression, used by the best-effort mirror environment. -/
partial def lfMirrorObjExprNodeCount : ObjExpr → Nat
  | .ident _ | .sort | .univ _ => 1
  | .app f a | .pair f a | .jeq f a =>
      1 + lfMirrorObjExprNodeCount f + lfMirrorObjExprNodeCount a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      1 + lfMirrorObjExprNodeCount A + lfMirrorObjExprNodeCount B
  | .fst e | .snd e => 1 + lfMirrorObjExprNodeCount e
  | .lam _ body => 1 + lfMirrorObjExprNodeCount body

/-- Checked `syntax_def` bodies above this size are opaque in best-effort mirror prefixes. -/
def lfMirrorBestEffortSyntaxDefNodeLimit : Nat := 120

/-- Add one mirror declaration in best-effort mode. -/
def addLFMirrorPendingDeclBestEffort (theoryName : Name) (levelParams : List Name)
    (levelArgs : List Level) (decl : LFMirrorPendingDecl) : CoreM Unit := do
  match decl with
  | .syntaxAbbrev d =>
      if lfMirrorObjExprNodeCount d.value > lfMirrorBestEffortSyntaxDefNodeLimit then
        return
      else
        addLFMirrorPendingDecl theoryName levelParams levelArgs decl
  | .syntaxDef d =>
      match d.value? with
      | some value =>
          if lfMirrorObjExprNodeCount value > lfMirrorBestEffortSyntaxDefNodeLimit then
            return
          else
            addLFMirrorPendingDecl theoryName levelParams levelArgs decl
      | none => addLFMirrorPendingDecl theoryName levelParams levelArgs decl
  | _ => addLFMirrorPendingDecl theoryName levelParams levelArgs decl

/-- Add every currently unblocked mirror declaration, leaving blocked declarations for later. -/
partial def addLFMirrorPendingDeclsBestEffort (theoryName : Name) (levelParams : List Name)
    (levelArgs : List Level) (decls : Array LFMirrorPendingDecl) : CoreM Unit := do
  if decls.isEmpty then
    return
  let mut rest : Array LFMirrorPendingDecl := #[]
  for decl in decls do
    try
      addLFMirrorPendingDeclBestEffort theoryName levelParams levelArgs decl
    catch _ =>
      rest := rest.push decl
  if rest.isEmpty || rest.size == decls.size then
    return
  addLFMirrorPendingDeclsBestEffort theoryName levelParams levelArgs rest

/-- Build pending mirror declarations for all mirror-supported declarations in a signature. -/
def lfMirrorPendingDeclsForSignature (sig : HLSignature) : Array LFMirrorPendingDecl := Id.run do
  let mut pending : Array LFMirrorPendingDecl := #[]
  for d in sig.syntaxSorts do
    pending := pending.push (.syntaxSort d)
  for d in sig.syntaxAbbrevs do
    pending := pending.push (.syntaxAbbrev d)
  for d in sig.syntaxDefs do
    pending := pending.push (.syntaxDef d)
  for d in sig.judgments do
    pending := pending.push (.judgment d)
  for d in sig.judgmentAbbrevs do
    pending := pending.push (.judgmentAbbrev d)
  for d in sig.lfOpaqueConsts do
    pending := pending.push (.lfOpaqueConst d)
  for d in sig.lfObjectDefs do
    pending := pending.push (.lfObjectDef d)
  for d in sig.rules do
    pending := pending.push (.rule d)
  for d in sig.lfJudgmentTheorems do
    pending := pending.push (.lfJudgmentTheorem d)
  return pending

/-- Ensure that experimental Lean mirror declarations exist for a checked-HL signature. -/
def ensureLFMirrorForSignature (sig : HLSignature) : CoreM Unit := do
  addLFMirrorPendingDecls sig.name (lfMirrorLevelParamNamesForSignature sig)
    (lfMirrorLevelArgsForSignature sig) (lfMirrorPendingDeclsForSignature sig)

/-- Add all currently unblocked mirror declarations for a signature. -/
def ensureLFMirrorForSignatureBestEffort (sig : HLSignature) : CoreM Unit := do
  addLFMirrorPendingDeclsBestEffort sig.name (lfMirrorLevelParamNamesForSignature sig)
    (lfMirrorLevelArgsForSignature sig) (lfMirrorPendingDeclsForSignature sig)

/-- Ensure that experimental Lean mirror declarations exist for the currently checked signature. -/
def ensureLFMirrorForTheory (theoryName : Name) : CoreM Unit := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  ensureLFMirrorForSignature checkedHL

/-- Check one LF value against an LF type using only the experimental Lean mirror backend. -/
def checkWithLFMirrorOnlyInSignature (sig : HLSignature) (params : Array HLBinding)
    (typeExpr valueExpr : ObjExpr) : CoreM Unit := do
  try
    ensureLFMirrorForSignature sig
    MetaM.run' do
      let levelArgs := lfMirrorLevelArgsForSignature sig
      withLFMirrorLocalsWithLevels sig.name levelArgs params fun locals => do
        let typeLean ← lfMirrorExprWithLevels sig.name (lfMirrorLevelArgsForSignature sig) locals
          typeExpr
        let valueLean ← lfMirrorTermWithExpectedWithLevels sig.name
          (lfMirrorLevelArgsForSignature sig) locals typeExpr valueExpr
        let actual ← inferType valueLean
        unless ← withTransparency .all <| isDefEq actual typeLean do
          let msg :=
            m!"Lean mirror checker inferred\n  {actual}\nfor translated value, expected\n  \
              {typeLean}"
          throwError msg
  catch ex =>
    let typeText := ObjExpr.toString typeExpr
    let valueText := ObjExpr.toString valueExpr
    let reason := lfMirrorExceptionMessageData ex
    throwError "Lean mirror backend rejected term in type theory '{sig.name}'.

Internal type:
  {typeText}

Internal value:
  {valueText}

Reason:
{reason}"

/-- Check one LF value against an LF type using only the mirror for a registered theory. -/
def checkWithLFMirrorOnly (theoryName : Name) (params : Array HLBinding)
    (typeExpr valueExpr : ObjExpr) : CoreM Unit := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  checkWithLFMirrorOnlyInSignature checkedHL params typeExpr valueExpr

/-- Count checked syntax-definition bodies in a high-level signature. -/
def checkedSyntaxDefBodyCount (sig : HLSignature) : Nat :=
  sig.syntaxDefs.foldl (fun n d => if d.value?.isSome then n + 1 else n) 0

/-- Count typed LF opaque constants in a high-level signature. -/
def typedLFOpaqueCount (sig : HLSignature) : Nat :=
  sig.lfOpaqueConsts.foldl (fun n d => if d.typeExpr?.isSome then n + 1 else n) 0

/-- Mirror-check a type-valued abbreviation body under a telescope. -/
def checkLFMirrorTypeLikeBodyInSignature (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (params : Array HLBinding) (value : ObjExpr) : CoreM Unit := do
  try
    MetaM.run' <| withLFMirrorLocalsWithLevels sig.name (lfMirrorLevelArgsForSignature sig)
        params fun locals => do
      let valueLean ← lfMirrorExprWithLevels sig.name (lfMirrorLevelArgsForSignature sig) locals
        value
      discard <| lfMirrorTypeUniverseLevel valueLean
  catch ex =>
    let valueText := ObjExpr.toString value
    let reason := lfMirrorExceptionMessageData ex
    throwError m!"Lean mirror backend rejected {ownerKind} '{ownerName}' in type theory \
      '{sig.name}'.\n\nInternal value:\n  {valueText}\n\nReason:\n{reason}"

/-- Mirror-check a type-valued abbreviation body in a registered theory. -/
def checkLFMirrorTypeLikeBody (theoryName : Name) (ownerKind : String) (ownerName : Name)
    (params : Array HLBinding) (value : ObjExpr) : CoreM Unit := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  checkLFMirrorTypeLikeBodyInSignature checkedHL ownerKind ownerName params value

/-- Mirror-check a checked `syntax_def` body against its declared result universe. -/
def checkLFMirrorSyntaxDefBodyInSignature (sig : HLSignature) (d : SyntaxDefDecl)
    (value : ObjExpr) : CoreM Unit := do
  try
    MetaM.run' <| withLFMirrorLocalsWithLevels sig.name (lfMirrorLevelArgsForSignature sig)
        d.params fun locals => do
      let expected := lfMirrorLeanSortOfLevel d.resultLevel
      let valueLean ← lfMirrorExprWithLevels sig.name (lfMirrorLevelArgsForSignature sig) locals
        value
      let actual ← inferType valueLean
      unless ← withTransparency .all <| isDefEq actual expected do
        throwError "translated value has type\n  {actual}\nexpected\n  {expected}"
  catch ex =>
    let valueText := ObjExpr.toString value
    let reason := lfMirrorExceptionMessageData ex
    throwError m!"Lean mirror backend rejected checked syntax_def '{d.name}' in type theory \
      '{sig.name}'.\n\nInternal value:\n  {valueText}\n\nReason:\n{reason}"

/-- Mirror-check a checked `syntax_def` body in a registered theory. -/
def checkLFMirrorSyntaxDefBody (theoryName : Name) (d : SyntaxDefDecl) (value : ObjExpr) :
    CoreM Unit := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  checkLFMirrorSyntaxDefBodyInSignature checkedHL d value

/-- Mirror-check an `lf_def` body against its declared LF type. -/
def checkLFMirrorLFObjectDefBodyInSignature (sig : HLSignature) (d : LFObjectDefDecl) :
    CoreM Unit := do
  try
    MetaM.run' do
      discard <| lfMirrorTermWithExpectedWithLevels sig.name (lfMirrorLevelArgsForSignature sig) {}
        d.typeExpr d.value
  catch ex =>
    throwError "Lean mirror backend rejected lf_def '{d.name}' in type theory \
      '{sig.name}'.\n\nInternal type:\n  {ObjExpr.toString d.typeExpr}\n\nInternal value:\n  \
      {ObjExpr.toString d.value}\n\nReason:\n{lfMirrorExceptionMessageData ex}"

/-- Mirror-check an `lf_def` body in a registered theory. -/
def checkLFMirrorLFObjectDefBody (theoryName : Name) (d : LFObjectDefDecl) : CoreM Unit := do
  let some checkedHL ← getCheckedHLSignature? theoryName
    | throwError "no checked high-level signature stored for type theory '{theoryName}'"
  checkLFMirrorLFObjectDefBodyInSignature checkedHL d

end InternalLean
