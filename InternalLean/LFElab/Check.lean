/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab.Implicits

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Lazily rendered location text for checker diagnostics. -/
abbrev LFCheckWhere := Unit → String

/-- Lift already available location text into a lazy checker diagnostic thunk. -/
def lfCheckWhere (where_ : String) : LFCheckWhere :=
  fun _ => where_

/-- Map-based variant of `isUntypedLFOpaquePlaceholder`. -/
def isUntypedLFOpaquePlaceholderWithLookup (lookup : LFCheckLookupContext)
    (knownTypes : LFLocalTypes) (expr : ObjExpr) : Bool :=
  match splitObjApp (eraseObjExprScopes expr) with
  | (.ident head, args) =>
      let head := head.eraseMacroScopes
      if (knownTypes.find? head).isSome then
        false
      else
        match lookup.untypedOpaqueArities.find? head with
        | some arities =>
            arities.any fun arity? =>
              match arity? with
              | some arity => args.size == arity
              | none => args.isEmpty
        | none => false
  | _ => false

/-- Check, when possible, that an LF expression has an expected type.

This is a bidirectional checker for the supported LF staging fragment. Lambda expressions are
checked against expected dependent arrows, applications with known typed heads recursively check
their arguments, and non-lambda expressions must infer a type matching the expected type. The only
non-inferable expressions accepted at an expected type are explicitly declared untyped opaque LF
placeholders, which remain a visible trust boundary for staged payloads. -/
partial def checkLFExprHasTypeWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) (expr expected : ObjExpr) : CoreM Unit := do
  let rec checkInferableApps (knownTypes : LFLocalTypes) (expr : ObjExpr) : CoreM Unit := do
    let checkTypedHeadArgs (headLabel : String) (head : Name) (info : LFGlobalTypeInfo)
        (args : Array ObjExpr) := do
      if args.size == info.binders.size then
        let mut subst : NameMap ObjExpr := {}
        for b in info.binders, arg in args do
          let expected := substLFParams subst b.typeExpr
          let whereForArg : LFCheckWhere := fun _ =>
            let whereText := where_ ()
            if whereText.contains " argument '" then
              s!"{whereText} for {headLabel} '{head}' parameter '{b.name.eraseMacroScopes}'"
            else
              s!"{whereText} for {headLabel} '{head}' parameter '{b.name.eraseMacroScopes}' \
                argument '{diagnosticObjExprShortString (eraseObjExprScopes arg)}'"
          checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName whereForArg knownTypes arg
            expected
          subst := subst.insert b.name.eraseMacroScopes (eraseObjExprScopes arg)
      else
        for arg in args do
          checkInferableApps knownTypes arg
    match eraseObjExprScopes expr with
    | .ident _ | .sort | .univ _ => pure ()
    | e@(.app ..) =>
        match splitObjApp e with
        | (.ident head, args) =>
            let head := head.eraseMacroScopes
            if let some info := findLFGlobalTypeInfoIn? lookup head then
              checkTypedHeadArgs "constructor" head info args
            else if let some info := findLFProofTypeInfoIn? lookup head then
              checkTypedHeadArgs "proof constant" head info args
            else
              match knownTypes.find? head with
              | some typeExpr =>
                  let mut current := eraseObjExprScopes typeExpr
                  for arg in args do
                    match current with
                    | .arrow binder? expected result | .funArrow binder? expected result =>
                        checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName
                          (fun _ => s!"{where_ ()} for local function '{head}' argument")
                          knownTypes arg expected
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
    | .arrow x A B | .funArrow x A B | .sigma x A B =>
        checkInferableApps knownTypes A
        let knownTypes := match x with
          | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
          | none => knownTypes
        checkInferableApps knownTypes B
    | .pair a b =>
        checkInferableApps knownTypes a
        checkInferableApps knownTypes b
    | .fst e | .snd e =>
        checkInferableApps knownTypes e
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
            checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName where_ knownTypes bodyExpr
              expectedBody
        | _ =>
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has \
              {where_ ()} as lambda expression '{diagnosticObjExprString expr}', expected \
                non-function type '{diagnosticObjExprString expected}'"
      else
        throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_ ()} as \
          an empty lambda expression"
  | .pair a b =>
      match expected with
      | .sigma expectedBinder? expectedDomain expectedBody =>
          checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName where_ knownTypes a
            expectedDomain
          let expectedBody := match expectedBinder? with
            | some y => substSingleLFParam y (eraseObjExprScopes a) expectedBody
            | none => expectedBody
          checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName where_ knownTypes b
            expectedBody
      | _ =>
          throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_ ()} as \
            pair expression '{diagnosticObjExprString expr}', expected a record/Sigma type but \
              got '{diagnosticObjExprString expected}'"
  | _ =>
      checkInferableApps knownTypes expr
      match inferKnownLFExprTypeWithLookup? lookup knownTypes expr with
      | some actualType =>
          let actualType := normalizeLFExprBetaOnly actualType
          let (normalizedActualType, normalizedExpected) :=
            normalizeLFTypeComparisonPairInLookup lookup actualType expected
          if !lfExprAlphaEq normalizedActualType normalizedExpected then
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has \
              {where_ ()} with type '{diagnosticObjExprString normalizedActualType}', expected \
                '{diagnosticObjExprString normalizedExpected}'"
      | none =>
          unless isUntypedLFOpaquePlaceholderWithLookup lookup knownTypes expr do
            throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has \
              {where_ ()} whose type cannot be inferred: '{diagnosticObjExprString expr}', \
                expected '{diagnosticObjExprString expected}'"

/-- Check, when possible, that an LF expression has an expected type. -/
def checkLFExprHasType (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (where_ : String) (knownTypes : LFLocalTypes) (expr expected : ObjExpr) : CoreM Unit :=
  checkLFExprHasTypeWithLookup (mkLFCheckLookupContext sig) sig ownerKind ownerName
    (lfCheckWhere where_) knownTypes expr expected

/-- Check an LF argument against a known expected type.

Expected argument positions are checked bidirectionally even when the argument has no shallow
inferred type. The only non-inferable arguments accepted by this path are explicitly declared
untyped LF placeholders, which remain visible trust-boundary holes. -/
def checkLFKnownArgumentTypeWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) (arg expected : ObjExpr) : CoreM Unit := do
  checkLFExprHasTypeWithLookup lookup sig ownerKind ownerName
    (fun _ => s!"{where_ ()} argument \
      '{diagnosticObjExprShortString (eraseObjExprScopes arg)}'") knownTypes arg expected

/-- Check an LF argument against a known expected type. -/
def checkLFKnownArgumentType (sig : HLSignature) (ownerKind : String) (ownerName : Name)
    (where_ : String) (knownTypes : LFLocalTypes) (arg expected : ObjExpr) : CoreM Unit := do
  checkLFKnownArgumentTypeWithLookup (mkLFCheckLookupContext sig) sig ownerKind ownerName
    (lfCheckWhere where_) knownTypes arg expected

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
telescope is known, using a reusable lookup context. This catches ill-typed constructor
applications even when an enclosing expression would otherwise be left opaque by shallow
inference. -/
partial def checkLFInferableApplicationArgumentsWithLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) : ObjExpr → CoreM Unit
  | .ident _ | .sort | .univ _ => pure ()
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident head, args) =>
          let head := head.eraseMacroScopes
          if let some info := findLFGlobalTypeInfoIn? lookup head then
            if args.size == info.binders.size then
              let mut subst : NameMap ObjExpr := {}
              for b in info.binders, arg in args do
                let expected := substLFParams subst b.typeExpr
                checkLFKnownArgumentTypeWithLookup lookup sig ownerKind ownerName
                  (fun _ => s!"{where_ ()} for constructor '{head}' parameter \
                    '{b.name.eraseMacroScopes}'") knownTypes arg expected
                subst := subst.insert b.name.eraseMacroScopes (eraseObjExprScopes arg)
            else
              for arg in args do
                checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName
                  where_ knownTypes arg
          else
            for arg in args do
              checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
                knownTypes arg
      | (head, args) =>
          checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
            knownTypes head
          for arg in args do
            checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
              knownTypes arg
  | .arrow x A B | .funArrow x A B | .sigma x A B => do
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes B
  | .pair a b => do
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes a
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes b
  | .fst e | .snd e => do
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes e
  | .lam _ _body =>
      pure ()
  | .jeq lhs rhs => do
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes lhs
      checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName where_
        knownTypes rhs

/-- Recursively validate arguments of global constructor applications whose parameter telescope is
known. -/
def checkLFInferableApplicationArguments (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (expr : ObjExpr) :
    CoreM Unit :=
  checkLFInferableApplicationArgumentsWithLookup (mkLFCheckLookupContext sig) sig ownerKind
    ownerName (lfCheckWhere where_) knownTypes expr

/-- Shallowly check the argument list of a judgment-headed LF expression against the judgment
declaration telescope using a supplied known-type context. -/
def checkLFJudgmentArgumentsWithKnownTypesAndLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) (judgmentName : Name) (args : Array ObjExpr) : CoreM Unit := do
  let some j := findJudgmentDeclIn? lookup judgmentName
    | pure ()
  let mut subst : NameMap ObjExpr := {}
  for h : i in [:j.params.size] do
    let param := j.params[i]
    let arg := args[i]!
    let expected := substLFParams subst param.typeExpr
    checkLFKnownArgumentTypeWithLookup lookup sig ownerKind ownerName
      (fun _ => s!"{where_ ()} for judgment '{judgmentName.eraseMacroScopes}'") knownTypes arg
      expected
    subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)

/-- Shallowly check the argument list of a judgment-headed LF expression against the judgment
    declaration telescope using a supplied known-type context. -/
def checkLFJudgmentArgumentsWithKnownTypes (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (judgmentName : Name)
    (args : Array ObjExpr) : CoreM Unit := do
  checkLFJudgmentArgumentsWithKnownTypesAndLookup (mkLFCheckLookupContext sig) sig ownerKind
    ownerName (lfCheckWhere where_) knownTypes judgmentName args

/-- Shallowly check the argument list of a judgment-headed rule expression against the
judgment declaration telescope. -/
def checkLFJudgmentArguments (sig : HLSignature) (ruleName : Name) (where_ : String)
    (locals : LFLocalTypes) (judgmentName : Name) (args : Array ObjExpr) : CoreM Unit :=
  checkLFJudgmentArgumentsWithKnownTypes sig "rule" ruleName where_ locals judgmentName args

/-- Shallowly check the argument list of a syntax-sort-headed LF expression against the
syntax sort telescope using a supplied known-type context. -/
def checkLFSyntaxSortArgumentsWithKnownTypesAndLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) (sortName : Name) (args : Array ObjExpr) : CoreM Unit := do
  let some s := findSyntaxSortDeclIn? lookup sortName
    | pure ()
  let mut subst : NameMap ObjExpr := {}
  for _h : i in [:min s.params.size args.size] do
    let param := s.params[i]!
    let arg := args[i]!
    let expected := substLFParams subst param.typeExpr
    checkLFKnownArgumentTypeWithLookup lookup sig ownerKind ownerName
      (fun _ => s!"{where_ ()} for syntax_sort '{sortName.eraseMacroScopes}'") knownTypes arg
      expected
    subst := subst.insert param.name.eraseMacroScopes (eraseObjExprScopes arg)

/-- Shallowly check the argument list of a syntax-sort-headed LF expression against the
syntax sort telescope using a supplied known-type context. -/
def checkLFSyntaxSortArgumentsWithKnownTypes (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (sortName : Name)
    (args : Array ObjExpr) : CoreM Unit := do
  checkLFSyntaxSortArgumentsWithKnownTypesAndLookup (mkLFCheckLookupContext sig) sig ownerKind
    ownerName (lfCheckWhere where_) knownTypes sortName args

/-- Recursively check syntax-sort-headed subexpressions against syntax-sort telescopes when
arguments are known local or LF-definition identifiers, using a reusable lookup context. -/
partial def checkLFSyntaxSortArgumentsInExprWithLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (ownerKind : String) (ownerName : Name) (where_ : LFCheckWhere)
    (knownTypes : LFLocalTypes) : ObjExpr → CoreM Unit
  | .ident n => do
      if (findSyntaxSortDeclIn? lookup n).isSome then
        checkLFSyntaxSortArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName where_
          knownTypes n #[]
  | .sort | .univ _ => pure ()
  | e@(.app ..) => do
      match splitObjApp e with
      | (.ident head, args) =>
          if (findSyntaxSortDeclIn? lookup head).isSome then
            checkLFSyntaxSortArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName
              where_ knownTypes head args
          for arg in args do
            checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_
              knownTypes arg
      | (head, args) =>
          checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_
            knownTypes head
          for arg in args do
            checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_
              knownTypes arg
  | .arrow x A B | .funArrow x A B | .sigma x A B => do
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_ knownTypes A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_ knownTypes B
  | .pair a b => do
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_ knownTypes a
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_ knownTypes b
  | .fst e | .snd e => do
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_ knownTypes e
  | .lam _ _body =>
      pure ()
  | .jeq lhs rhs => do
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_
        knownTypes lhs
      checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName where_
        knownTypes rhs

/-- Recursively check syntax-sort-headed subexpressions against syntax-sort telescopes when
arguments are known local or LF-definition identifiers. -/
def checkLFSyntaxSortArgumentsInExpr (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (expr : ObjExpr) :
    CoreM Unit :=
  checkLFSyntaxSortArgumentsInExprWithLookup (mkLFCheckLookupContext sig) sig ownerKind ownerName
    (lfCheckWhere where_) knownTypes expr

/-- Check a metadata telescope sequentially, so later binder types can use earlier binders
as arguments to dependent syntax sorts, using a reusable lookup context. -/
def checkLFSyntaxSortArgumentsInBindingsWithLookup (lookup : LFCheckLookupContext)
    (sig : HLSignature) (ownerKind : String) (ownerName : Name) (bs : Array HLBinding) :
    CoreM Unit := do
  let mut knownTypes : LFLocalTypes := {}
  for b in bs do
    let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
    checkLFSyntaxSortArgumentsInExprWithLookup lookup sig ownerKind ownerName
      (lfCheckWhere where_) knownTypes b.typeExpr
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)

/-- Check a metadata telescope sequentially, so later binder types can use earlier binders
as arguments to dependent syntax sorts. -/
def checkLFSyntaxSortArgumentsInBindings (sig : HLSignature) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) : CoreM Unit :=
  checkLFSyntaxSortArgumentsInBindingsWithLookup (mkLFCheckLookupContext sig) sig ownerKind
    ownerName bs

/-- Whether a shallow inferred LF type certifies that an expression is itself a type. -/
def inferredLFTypeIsUniverseWithLookup (lookup : LFCheckLookupContext)
    (actualType : ObjExpr) : Bool :=
  match normalizeLFExprForTypeComparisonWithDefs {} actualType with
  | .sort | .univ _ => true
  | _ =>
      let defs := lfDefinitionValuesWithSyntaxDefs lookup
      if defs.isEmpty then
        false
      else
        match normalizeLFExprForTypeComparisonWithDefs defs actualType with
        | .sort | .univ _ => true
        | _ => false

/-- Whether a shallow inferred LF type certifies that an expression is itself a type. -/
def inferredLFTypeIsUniverse (sig : HLSignature) (actualType : ObjExpr) : Bool :=
  inferredLFTypeIsUniverseWithLookup (mkLFCheckLookupContext sig) actualType

/-- Extract the universe level from an inferred LF universe type. -/
def inferredLFUniverseLevelWithLookup? (lookup : LFCheckLookupContext)
    (actualType : ObjExpr) : Option LevelExpr :=
  match normalizeLFExprForTypeComparisonWithDefs {} actualType with
  | .sort => some .zero
  | .univ u => some (LevelExpr.normalize u)
  | _ =>
      let defs := lfDefinitionValuesWithSyntaxDefs lookup
      if defs.isEmpty then
        none
      else
        match normalizeLFExprForTypeComparisonWithDefs defs actualType with
        | .sort => some .zero
        | .univ u => some (LevelExpr.normalize u)
        | _ => none

/-- Infer the universe level of a checked LF type expression when the shallow metadata is enough. -/
partial def inferLFTypeExprUniverseLevelWithLookup? (lookup : LFCheckLookupContext)
    (knownTypes : LFLocalTypes) : ObjExpr → Option LevelExpr
  | .sort => some (LevelExpr.succ' .zero)
  | .univ u => some (LevelExpr.succ' u)
  | .arrow x A B | .funArrow x A B | .sigma x A B => do
      let uA ← inferLFTypeExprUniverseLevelWithLookup? lookup knownTypes A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      let uB ← inferLFTypeExprUniverseLevelWithLookup? lookup knownTypes B
      some (LevelExpr.max' uA uB)
  | e => do
      let actualType ← inferKnownLFExprTypeWithLookup? lookup knownTypes e
      inferredLFUniverseLevelWithLookup? lookup actualType

/-- Check that an expression is valid in a metadata telescope binder type position, using a
reusable lookup context.

Binder types are allowed to be universe expressions, syntax-sort-headed type expressions, local or
opaque type-family applications whose inferred kind is a universe, and dependent arrows between
valid binder types. Theorem binders may additionally be judgment-headed local assumptions. -/
partial def checkLFBinderTypeWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (locals : NameSet)
    (allowJudgment : Bool) (typeExpr : ObjExpr) : CoreM Unit := do
  let typeExpr := eraseObjExprScopes typeExpr
  match typeExpr with
  | .sort | .univ _ => pure ()
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      checkLFBinderTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes
        locals false A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      let locals := match x with
        | some x => locals.insert x.eraseMacroScopes
        | none => locals
      checkLFBinderTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes
        locals false B
  | .pair .. | .fst .. | .snd .. =>
      throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} as \
        term-shaped record expression '{diagnosticObjExprString typeExpr}', expected an LF type \
          expression"
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
            checkLFJudgmentArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes head.name args
          else if head.kind == .syntaxSort then
            let (_, args) := splitObjApp typeExpr
            checkLFSyntaxSortArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes head.name args
          else
            checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes typeExpr
            match inferKnownLFExprTypeWithLookup? lookup knownTypes typeExpr with
            | some actualType =>
                unless inferredLFTypeIsUniverseWithLookup lookup actualType do
                  throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                    whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                      universe-valued LF type expression"
            | none =>
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose type cannot be inferred: '{diagnosticObjExprString typeExpr}', expected \
                    an LF type expression"
      | none =>
          checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName
            (lfCheckWhere where_) knownTypes typeExpr
          match inferKnownLFExprTypeWithLookup? lookup knownTypes typeExpr with
          | some actualType =>
              unless inferredLFTypeIsUniverseWithLookup lookup actualType do
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                    universe-valued LF type expression"
          | none =>
              throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                not headed by a known LF type or judgment: {diagnosticObjExprString typeExpr}"

/-- Check that an expression is valid in a metadata telescope binder type position. -/
def checkLFBinderType (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (locals : NameSet)
    (allowJudgment : Bool) (typeExpr : ObjExpr) : CoreM Unit :=
  checkLFBinderTypeWithLookup (mkLFCheckLookupContext sig) sig globalHeads ownerKind ownerName
    where_ knownTypes locals allowJudgment typeExpr

/-- Check a metadata telescope sequentially with the binder-type kind discipline, using a reusable
lookup context. -/
def checkLFBinderTypesInBindingsWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) (allowJudgment : Bool := false)
    (baseKnownTypes : LFLocalTypes := {}) : CoreM Unit := do
  let mut knownTypes := baseKnownTypes
  let mut locals : NameSet := {}
  for b in bs do
    let where_ := s!"parameter '{b.name.eraseMacroScopes}' type"
    checkLFBinderTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes
      locals allowJudgment b.typeExpr
    knownTypes := knownTypes.insert b.name.eraseMacroScopes (eraseObjExprScopes b.typeExpr)
    locals := locals.insert b.name.eraseMacroScopes

/-- Check a metadata telescope sequentially with the binder-type kind discipline. -/
def checkLFBinderTypesInBindings (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (bs : Array HLBinding) (allowJudgment : Bool := false)
    (baseKnownTypes : LFLocalTypes := {}) : CoreM Unit := do
  checkLFBinderTypesInBindingsWithLookup (mkLFCheckLookupContext sig) sig globalHeads ownerKind
    ownerName bs allowJudgment baseKnownTypes

/-- Check that an expression is a type/evidence expression usable as a premise or proof binder,
using a reusable lookup context.

Unlike ordinary object-definition type checking, this discipline allows judgment-headed leaves
under structural arrows and Sigma packages. This supports higher-order premises such as
`(x : Obj) → P x` and `(P x → Q x) × (Q x → P x)`. -/
partial def checkLFEvidenceTypeWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (locals : NameSet)
    (typeExpr : ObjExpr) : CoreM Unit := do
  let typeExpr := eraseObjExprScopes typeExpr
  match typeExpr with
  | .sort | .univ _ => pure ()
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      checkLFEvidenceTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes
        locals A
      let knownTypes := match x with
        | some x => knownTypes.insert x.eraseMacroScopes (eraseObjExprScopes A)
        | none => knownTypes
      let locals := match x with
        | some x => locals.insert x.eraseMacroScopes
        | none => locals
      checkLFEvidenceTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes
        locals B
  | .pair .. | .fst .. | .snd .. | .lam .. =>
      throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} as \
        term-shaped expression '{diagnosticObjExprString typeExpr}', expected an LF \
          type/evidence expression"
  | _ =>
      let head? := checkedLFHead? globalHeads locals typeExpr
      match head? with
      | some head =>
          checkCheckedLFHeadArity sig ownerKind ownerName where_ head
          if head.kind == .judgment then
            let (_, args) := splitObjApp typeExpr
            checkLFJudgmentArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes head.name args
          else if head.kind == .syntaxSort then
            let (_, args) := splitObjApp typeExpr
            checkLFSyntaxSortArgumentsWithKnownTypesAndLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes head.name args
          else
            checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName
              (lfCheckWhere where_) knownTypes typeExpr
            match inferKnownLFExprTypeWithLookup? lookup knownTypes typeExpr with
            | some actualType =>
                unless inferredLFTypeIsUniverseWithLookup lookup actualType do
                  throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                    whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                      universe-valued LF type/evidence expression"
            | none =>
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose type cannot be inferred: '{diagnosticObjExprString typeExpr}', expected \
                    an LF type/evidence expression"
      | none =>
          checkLFInferableApplicationArgumentsWithLookup lookup sig ownerKind ownerName
            (lfCheckWhere where_) knownTypes typeExpr
          match inferKnownLFExprTypeWithLookup? lookup knownTypes typeExpr with
          | some actualType =>
              unless inferredLFTypeIsUniverseWithLookup lookup actualType do
                throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                  whose inferred type is '{diagnosticObjExprString actualType}', expected a \
                    universe-valued LF type/evidence expression"
          | none =>
              throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} \
                not headed by a known LF type/evidence identifier: \
                  {diagnosticObjExprString typeExpr}"

/-- Check that an expression is a type/evidence expression usable as a premise or proof binder. -/
def checkLFEvidenceType (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (knownTypes : LFLocalTypes) (locals : NameSet)
    (typeExpr : ObjExpr) : CoreM Unit :=
  checkLFEvidenceTypeWithLookup (mkLFCheckLookupContext sig) sig globalHeads ownerKind ownerName
    where_ knownTypes locals typeExpr

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
  pure {
    name := s.name.eraseMacroScopes
    params := params
    arity := s.params.size
    resultLevel := LevelExpr.normalize s.resultLevel }

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

/-- Build the checked artifact for one syntax-definition declaration. -/
def checkedLFSyntaxDefDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (d : SyntaxDefDecl) :
    CoreM CheckedLFSyntaxDef := do
  let (params, locals) ← checkedLFBindings sig globalHeads "syntax_def" d.name d.params
  let (checkedValue?, checkedHead?) ← match d.value? with
    | none => pure (none, none)
    | some value => do
        let checkedValue ← resolveLFExpr sig globalHeads locals "syntax_def" d.name "value" value
        let head? := checkedLFHead? globalHeads locals value
        pure (some checkedValue, head?)
  pure {
    name := d.name.eraseMacroScopes
    params := params
    resultLevel := LevelExpr.normalize d.resultLevel
    value? := d.value?.map eraseObjExprScopes
    checkedValue? := checkedValue?
    head? := checkedHead? }

/-- Build the checked artifact for one judgment-abbreviation declaration. -/
def checkedLFJudgmentAbbrevDeclArtifact (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (a : JudgmentAbbrevDecl) :
    CoreM CheckedLFJudgmentAbbrev := do
  let (params, locals) ← checkedLFBindings sig globalHeads "judgment_abbrev" a.name a.params
  let checkedValue ← resolveLFExpr sig globalHeads locals "judgment_abbrev" a.name "value" a.value
  let some head := checkedLFHead? globalHeads locals a.value
    | throwError "internal error: checked judgment_abbrev '{a.name}' has no resolved head"
  pure {
    name := a.name.eraseMacroScopes
    params := params
    value := a.value
    checkedValue := checkedValue
    head := head }

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

/-- Build checked LF declaration artifacts for syntax sorts, abbreviations, syntax definitions,
context zones, binder classes, judgments, and opaque placeholders. -/
def checkedLFDeclarations (sig : HLSignature) :
    CoreM (Array CheckedLFSyntaxSort × Array CheckedLFSyntaxAbbrev ×
      Array CheckedLFSyntaxDef × Array CheckedLFJudgmentAbbrev × Array CheckedLFContextZone ×
      Array CheckedLFBinderClass × Array CheckedLFJudgment × Array CheckedLFOpaqueConst ×
      Array CheckedLFSideConditionSolver × Array CheckedLFConversionPlugin) := do
  let globalHeads := lfGlobalHeadInfo sig
  let syntaxSorts ← sig.syntaxSorts.mapM (checkedLFSyntaxSortDeclArtifact sig globalHeads)
  let syntaxAbbrevs ← sig.syntaxAbbrevs.mapM (checkedLFSyntaxAbbrevDeclArtifact sig globalHeads)
  let syntaxDefs ← sig.syntaxDefs.mapM (checkedLFSyntaxDefDeclArtifact sig globalHeads)
  let judgmentAbbrevs ←
    sig.judgmentAbbrevs.mapM (checkedLFJudgmentAbbrevDeclArtifact sig globalHeads)
  let contextZones := sig.contextZones.map checkedLFContextZoneDeclArtifact
  let binderClasses := sig.binderClasses.map checkedLFBinderClassDeclArtifact
  let judgments ← sig.judgments.mapM (checkedLFJudgmentDeclArtifact sig globalHeads)
  let opaques ← sig.lfOpaqueConsts.mapM (checkedLFOpaqueConstDeclArtifact sig globalHeads)
  let solvers := sig.sideConditionSolvers.map checkedLFSideConditionSolverDeclArtifact
  let plugins := sig.conversionPlugins.map checkedLFConversionPluginDeclArtifact
  pure (syntaxSorts, syntaxAbbrevs, syntaxDefs, judgmentAbbrevs, contextZones, binderClasses,
    judgments, opaques, solvers, plugins)

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
  | .arrow x A B | .funArrow x A B | .sigma x A B => do
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ B
  | .pair a b => do
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ a
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ b
  | .fst e | .snd e => do
      checkKnownNamesInLFExpr sig globals locals opaqueArities ownerKind ownerName where_ e
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
  | .arrow x A B | .sigma x A B =>
      let free := freeCheckedLFLocalIdentifiers A ++ freeCheckedLFLocalIdentifiers B
      match x with
      | some x => free.erase x.eraseMacroScopes
      | none => free
  | .pair a b => freeCheckedLFLocalIdentifiers a ++ freeCheckedLFLocalIdentifiers b
  | .fst e | .snd e => freeCheckedLFLocalIdentifiers e
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
  | .sigma x A B =>
      let A := renameCheckedLFBoundOccurrences oldName newName A
      match x with
      | some x =>
          let x := x.eraseMacroScopes
          let B := if x == oldName.eraseMacroScopes then B else
            renameCheckedLFBoundOccurrences oldName newName B
          .sigma (some x) A B
      | none => .sigma none A (renameCheckedLFBoundOccurrences oldName newName B)
  | .pair a b => .pair (renameCheckedLFBoundOccurrences oldName newName a)
      (renameCheckedLFBoundOccurrences oldName newName b)
  | .fst e => .fst (renameCheckedLFBoundOccurrences oldName newName e)
  | .snd e => .snd (renameCheckedLFBoundOccurrences oldName newName e)
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
  | .sigma y A B =>
      let A := substSingleCheckedLFParam x value A
      match y with
      | some y =>
          let y := y.eraseMacroScopes
          if y == x.eraseMacroScopes then
            .sigma (some y) A B
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
            .sigma (some y) A (substSingleCheckedLFParam x value B)
      | none => .sigma none A (substSingleCheckedLFParam x value B)
  | .pair a b => .pair (substSingleCheckedLFParam x value a)
      (substSingleCheckedLFParam x value b)
  | .fst e => .fst (substSingleCheckedLFParam x value e)
  | .snd e => .snd (substSingleCheckedLFParam x value e)
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
          | .sigma x A B =>
              let A := unfoldLFDefinitionsInCheckedExprCore defs locals fuel A
              match x with
              | some x =>
                  let (x, B) := freshCheckedLFUnfoldBinder defs locals x B
                  let locals := locals.insert x.eraseMacroScopes
                  .sigma (some x) A (unfoldLFDefinitionsInCheckedExprCore defs locals fuel B)
              | none => .sigma none A (unfoldLFDefinitionsInCheckedExprCore defs locals fuel B)
          | .pair a b =>
              .pair (unfoldLFDefinitionsInCheckedExprCore defs locals fuel a)
                (unfoldLFDefinitionsInCheckedExprCore defs locals fuel b)
          | .fst e =>
              match unfoldLFDefinitionsInCheckedExprCore defs locals fuel e with
              | .pair a _ => a
              | e => .fst e
          | .snd e =>
              match unfoldLFDefinitionsInCheckedExprCore defs locals fuel e with
              | .pair _ b => b
              | e => .snd e
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
      | .syntaxSort | .syntaxDef => .tyConst h.name
      | .lfDefinition | .lfTheorem | .lfRule => .tmConst h.name
      | .judgment => .tmConst h.name
      | .primitive | .definition | .theorem | .opaque => .tmConst h.name
  | .sort => .tyConst `Type
  | .univ u => .tyApp `Type [.leanParam (.str .anonymous u.toString)]
  | e@(.app _ _) =>
      let (head, args) := splitCheckedLFApp e
      let rawArgs := args.map checkedLFExprToRaw |>.toList
      match head with
      | .ident h =>
          match h.kind with
          | .syntaxSort | .syntaxDef => .tyApp h.name rawArgs
          | .local => .tmApp h.name rawArgs
          | .lfDefinition | .lfTheorem | .lfRule => .tmApp h.name rawArgs
          | .judgment => .tmApp h.name rawArgs
          | .primitive | .definition | .theorem | .opaque => .tmApp h.name rawArgs
      | other => .tmApp `_app (checkedLFExprToRaw other :: rawArgs)
  | .arrow none A B => .tyApp `arrow [checkedLFExprToRaw A, checkedLFExprToRaw B]
  | .arrow (some x) A B =>
      .tyApp `arrow [checkedLFExprToRaw A, .tmApp `lam [.leanParam x, checkedLFExprToRaw B]]
  | .sigma none A B => .tyApp `sigma [checkedLFExprToRaw A, checkedLFExprToRaw B]
  | .sigma (some x) A B =>
      .tyApp `sigma [checkedLFExprToRaw A, .tmApp `lam [.leanParam x, checkedLFExprToRaw B]]
  | .pair a b => .tmApp `pair [checkedLFExprToRaw a, checkedLFExprToRaw b]
  | .fst e => .tmApp `fst [checkedLFExprToRaw e]
  | .snd e => .tmApp `snd [checkedLFExprToRaw e]
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
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let acc := collectLFDefinitionMentions defs locals acc A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      collectLFDefinitionMentions defs locals acc B
  | .pair a b =>
      collectLFDefinitionMentions defs locals (collectLFDefinitionMentions defs locals acc a) b
  | .fst e | .snd e => collectLFDefinitionMentions defs locals acc e
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
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let acc := collectLFDefinitionUnfoldsCore defs locals fuel acc A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      collectLFDefinitionUnfoldsCore defs locals fuel acc B
  | .pair a b =>
      collectLFDefinitionUnfoldsCore defs locals fuel
        (collectLFDefinitionUnfoldsCore defs locals fuel acc a) b
  | .fst e | .snd e => collectLFDefinitionUnfoldsCore defs locals fuel acc e
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

/-- Equality modulo macro scopes, checked LF-definition unfolding, and structural eta under
local binders. -/
def lfExprEqModuloDefinitionsWithLocals (defs : LFDefinitionValueMap) (locals : NameSet)
    (a b : ObjExpr) : Bool :=
  lfExprAlphaEq (normalizeLFExprForConversionWithLocals defs locals a)
    (normalizeLFExprForConversionWithLocals defs locals b)

/-- Equality modulo macro scopes, checked LF-definition unfolding, and structural eta. -/
def lfExprEqModuloDefinitions (defs : LFDefinitionValueMap) (a b : ObjExpr) : Bool :=
  lfExprEqModuloDefinitionsWithLocals defs {} a b

/-- Stable comma-separated diagnostic rendering of LF definition names. -/
def diagnosticNameListString (xs : Array Name) : String :=
  if xs.isEmpty then "none" else String.intercalate ", " (xs.toList.map toString)

/-- Rich diagnostic for failed LF-definition/beta normalization matching. -/
def lfDefinitionNormalizationMismatchMessage (defs : LFDefinitionValueMap) (locals : NameSet)
    (actual expected : ObjExpr) : MessageData :=
  let actualN := normalizeLFExprForConversionWithLocals defs locals actual
  let expectedN := normalizeLFExprForConversionWithLocals defs locals expected
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
    "explicit LF lambdas, contracts structural eta-redexes, and alpha-renames binders",
    "to avoid local-binder capture."]
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
                local theorem assumption '{localName}' with a statement that does not match after\n\
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
      let mut proofArgIndex := 0
      for b in premiseTheorem.binders do
        let expectedBinderType := eraseObjExprScopes (substLFParams subst b.typeExpr)
        let binderHead? := checkedLFHead? globalHeads localNames expectedBinderType
        match binderHead? with
        | some binderHead =>
            if binderHead.kind == .judgment then
              let some arg := proofArgs[proofArgIndex]?
                | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
                  applies premise theorem '{theoremRefName}' with too few proof arguments"
              proofArgIndex := proofArgIndex + 1
              let some premiseDeriv ←
                checkLFJudgmentDerivation sig rules globalHeads knownTypes defValues localNames
                  availableLocalStatements availableTheoremStatements availableTheoremNames
                  theoremName expectedBinderType arg
                | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
                  applies premise theorem '{theoremRefName}' with unchecked proof argument \
                    '{arg}' for local hypothesis '{b.name.eraseMacroScopes}'"
              premiseDerivations := premiseDerivations.push premiseDeriv
            else
              let some arg := proofArgs[proofArgIndex]?
                | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
                  applies premise theorem '{theoremRefName}' with too few proof arguments"
              proofArgIndex := proofArgIndex + 1
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
        | none =>
            let some arg := proofArgs[proofArgIndex]?
              | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
                premise theorem '{theoremRefName}' with too few proof arguments"
            proofArgIndex := proofArgIndex + 1
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
      if proofArgIndex != proofArgs.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
          premise theorem '{theoremRefName}' with unused proof argument(s)"
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
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' uses \
            premise\ntheorem '{theoremRefName}' with a statement that does not match after \
            LF-definition normalization:\n{mismatch}"
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
      let ruleArgs := proofArgs.extract 0 appliedRule.params.size
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
          throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
            rule\n'{ruleName}' but the statement does not match the rule conclusion after \
            LF-definition normalization:\n{mismatch}"
      let mut premiseDerivations := #[]
      let mut scopedRuleArgs : Array ObjExpr := ruleArgs
      for p in appliedRule.premises, arg in premiseArgs do
        let expectedPremise := eraseObjExprScopes (substLFParams subst p.judgmentExpr)
        if p.isDirectJudgment then
          let some premiseDeriv ←
            checkLFJudgmentDerivation sig rules globalHeads knownTypes defValues localNames
              availableLocalStatements availableTheoremStatements availableTheoremNames theoremName
              expectedPremise arg
            | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' applies \
                rule '{ruleName}' with unchecked premise proof argument \
                '{diagnosticObjExprString arg}' for expected premise \
                '{diagnosticObjExprString expectedPremise}'"
          premiseDerivations := premiseDerivations.push premiseDeriv
        else
          checkLFKnownArgumentType sig "judgment_theorem" theoremName
            s!"proof argument for rule '{ruleName}' evidence premise '{p.name}'" knownTypes arg
            expectedPremise
          checkLFInferableApplicationArguments sig "judgment_theorem" theoremName
            s!"proof argument for rule '{ruleName}' evidence premise '{p.name}'" knownTypes arg
          checkLFSyntaxSortArgumentsInExpr sig "judgment_theorem" theoremName
            s!"proof argument for rule '{ruleName}' evidence premise '{p.name}'" knownTypes arg
          scopedRuleArgs := scopedRuleArgs.push (eraseObjExprScopes arg)
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
      return some (.ruleApp ruleName expectedConclusion scopedRuleArgs premiseDerivations
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
partial def lowerLFDerivationToKernelWithMode (sig : HLSignature) (rules : Array CheckedLFRule)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name)
    (unfoldDefs : Bool) : CheckedLFDerivation → CoreM KernelLFDerivation
  | .localAssumption name stmt => do
      let kernelStmtExpr :=
        if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
        else eraseObjExprScopes stmt
      let kernelStmt ← lfJudgmentObjExprToKernel sig globalHeads "local theorem assumption"
        theoremName kernelStmtExpr localNames
      match kernelStmt.validateBuiltinConstructorDiscipline s!"judgment_theorem '{theoremName}' \
        in type theory '{sig.name}'" s!"kernel-facing local theorem assumption '{name}'" with
      | .ok () => pure ()
      | .error err => throwError err
      pure (.assumption name kernelStmt)
  | .theoremRef name stmt args premises => do
      let kernelStmtExpr :=
        if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
        else eraseObjExprScopes stmt
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
        let mut entries : List ScopedInstantiationEntry := []
        let mut rawSubst : NameMap Raw := {}
        let mut objSubst : NameMap ObjExpr := {}
        let mut argIndex := 0
        for b in appliedTheorem.binders do
          let expectedBinderType := eraseObjExprScopes (substLFParams objSubst b.typeExpr)
          let binderHead? := checkedLFHead? globalHeads localNames expectedBinderType
          let isJudgmentBinder := match binderHead? with
            | some binderHead => binderHead.kind == CheckedLFHeadKind.judgment
            | none => false
          unless isJudgmentBinder do
            let some arg := args[argIndex]?
              | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
                theorem reference '{name}' with too few syntax/evidence arguments"
            let priorInst : Instantiation := fun x =>
              (rawSubst.find? x.eraseMacroScopes).getD (.leanParam x)
            let kernelArg :=
              if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames arg
              else eraseObjExprScopes arg
            let kernelExpectedBinderType :=
              if unfoldDefs then
                unfoldLFDefinitionsInExprWithLocals defValues localNames expectedBinderType
              else
                expectedBinderType
            let checkedArg ← resolveLFExpr sig globalHeads localNames
              "kernel-facing theorem reference" theoremName
              s!"argument for theorem '{name}' binder '{b.name.eraseMacroScopes}'" kernelArg
            let checkedArgRaw := checkedLFExprToRaw checkedArg
            let checkedBinderType ← resolveLFExpr sig globalHeads localNames
              "kernel-facing theorem reference" theoremName
              s!"type of theorem '{name}' binder '{b.name.eraseMacroScopes}'"
              kernelExpectedBinderType
            let sort := match binderHead? with
              | some binderHead =>
                  if binderHead.kind == CheckedLFHeadKind.syntaxSort then
                    RawMetaSort.custom binderHead.name
                  else RawMetaSort.arg
              | none => RawMetaSort.arg
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
            [← lowerLFDerivationToKernelWithMode sig rules globalHeads knownTypes defValues
              localNames theoremName unfoldDefs premiseDeriv]
        pure (.ruleApp (lfJudgmentTheoremKernelRuleName name) kernelStmt { entries := entries }
          loweredPremises [])
  | .ruleApp ruleName stmt ruleArgs premises certs => do
      let some appliedRule := findCheckedLFRule? rules ruleName
        | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers unknown \
          LF rule '{ruleName}'"
      let evidencePremiseCount := appliedRule.premises.foldl (init := 0) fun n p =>
        if p.isDirectJudgment then n else n + 1
      let judgmentPremiseCount := appliedRule.premises.size - evidencePremiseCount
      let expectedRuleArgs := appliedRule.params.size + evidencePremiseCount
      if ruleArgs.size != expectedRuleArgs then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with {ruleArgs.size} scoped instantiation entry/entries, expected \
            {expectedRuleArgs}"
      if premises.size != judgmentPremiseCount then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with {premises.size} premise derivation(s), expected \
            {judgmentPremiseCount}"
      let mut entries : List ScopedInstantiationEntry := []
      let mut rawSubst : NameMap Raw := {}
      let mut objSubst : NameMap ObjExpr := {}
      let paramArgs := ruleArgs[:appliedRule.params.size]
      for param in appliedRule.params, arg in paramArgs do
        let priorInst : Instantiation := fun x =>
          (rawSubst.find? x.eraseMacroScopes).getD (.leanParam x)
        let expectedParamType := substLFParams objSubst param.typeExpr
        let kernelArg :=
          if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames arg
          else eraseObjExprScopes arg
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
      let mut evidenceArgIndex := appliedRule.params.size
      for p in appliedRule.premises do
        unless p.isDirectJudgment do
          let some arg := ruleArgs[evidenceArgIndex]?
            | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
              rule '{ruleName}' with too few evidence arguments"
          evidenceArgIndex := evidenceArgIndex + 1
          let priorInst : Instantiation := fun x =>
            (rawSubst.find? x.eraseMacroScopes).getD (.leanParam x)
          let expectedPremise := eraseObjExprScopes (substLFParams objSubst p.judgmentExpr)
          let kernelArg :=
            if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames arg
            else eraseObjExprScopes arg
          let kernelExpectedPremise :=
            if unfoldDefs then
              unfoldLFDefinitionsInExprWithLocals defValues localNames expectedPremise
            else
              expectedPremise
          checkLFExprHasType sig "judgment_theorem" theoremName
            s!"kernel-facing replay evidence argument for rule '{ruleName}' premise '{p.name}'"
            knownTypes arg expectedPremise
          let checkedArg ← resolveLFExpr sig globalHeads localNames "kernel-facing derivation"
            theoremName s!"evidence argument for premise '{p.name}'" kernelArg
          let checkedArgRaw := checkedLFExprToRaw checkedArg
          let checkedPremiseType ← resolveLFExpr sig globalHeads localNames
            "kernel-facing derivation" theoremName s!"type of evidence premise '{p.name}'"
            kernelExpectedPremise
          let sort := match p.head? with
            | some h => if h.kind == .syntaxSort then RawMetaSort.custom h.name else .arg
            | none => .arg
          entries := entries ++ [{
            name := p.name
            sort := sort
            zone? := none
            type? := some (Raw.instantiate priorInst (checkedLFExprToRaw checkedPremiseType))
            evidence? := none
            value := checkedArgRaw }]
          rawSubst := rawSubst.insert p.name.eraseMacroScopes checkedArgRaw
          objSubst := objSubst.insert p.name.eraseMacroScopes kernelArg
      if evidenceArgIndex != ruleArgs.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with unused evidence argument(s)"
      let inst : ScopedInstantiation := { entries := entries }
      let kernelStmtExpr :=
        if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
        else eraseObjExprScopes stmt
      let kernelStmt ← lfJudgmentObjExprToKernel sig globalHeads "rule application" theoremName
        kernelStmtExpr localNames
      match kernelStmt.validateBuiltinConstructorDiscipline s!"judgment_theorem '{theoremName}' \
        in type theory '{sig.name}'" s!"kernel-facing replay statement for rule '{ruleName}'" with
      | .ok () => pure ()
      | .error err => throwError err
      let ruleLocals : NameSet := appliedRule.params.foldl (init := {}) fun acc p =>
        acc.insert p.name
      let ruleConclusionExpr :=
        if unfoldDefs then
          unfoldLFDefinitionsInExprWithLocals defValues ruleLocals appliedRule.conclusionExpr
        else
          eraseObjExprScopes appliedRule.conclusionExpr
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
          replay of rule '{ruleName}' has conclusion '{judgmentSourceString kernelStmt}', \
            expected instantiated rule conclusion '{judgmentSourceString expectedConclusion}'"
      let mut loweredPremises := []
      let mut premiseIndex := 0
      for p in appliedRule.premises do
        if p.isDirectJudgment then
          let some premiseDeriv := premises[premiseIndex]?
            | throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers \
              rule '{ruleName}' with too few premise derivation(s)"
          premiseIndex := premiseIndex + 1
          let lowered ← lowerLFDerivationToKernelWithMode sig rules globalHeads knownTypes
            defValues localNames theoremName unfoldDefs premiseDeriv
          let rulePremiseExpr :=
            if unfoldDefs then
              unfoldLFDefinitionsInExprWithLocals defValues ruleLocals p.judgmentExpr
            else
              eraseObjExprScopes p.judgmentExpr
          let rulePremise ← lfJudgmentObjExprToKernel sig globalHeads "rule premise"
            appliedRule.name rulePremiseExpr ruleLocals
          let expectedPremise ←
            match rulePremise.instantiateChecked inst.asInstantiation with
            | .ok expectedPremise => pure expectedPremise
            | .error err =>
              throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
                kernel-facing replay of rule '{ruleName}' has capture-unsafe premise \
                  instantiation: {err}"
          match expectedPremise.validateBuiltinConstructorDiscipline s!"judgment_theorem \
            '{theoremName}' in type theory '{sig.name}'" s!"kernel-facing replay premise for \
              rule '{ruleName}'" with
          | .ok () => pure ()
          | .error err => throwError err
          let actualPremise := kernelLFDerivationStatement lowered
          if !judgmentAlphaEq actualPremise expectedPremise then
            throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
              kernel-facing replay of rule '{ruleName}' has premise \
                '{judgmentSourceString actualPremise}', expected instantiated premise \
                  '{judgmentSourceString expectedPremise}'"
          loweredPremises := loweredPremises ++ [lowered]
      if premiseIndex != premises.size then
        throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
          '{ruleName}' with unused premise derivation(s)"
      pure (.ruleApp ruleName kernelStmt inst loweredPremises certs.toList)

/-- Lower a shallow checked LF derivation, preserving checked LF-definition heads when exact replay
works and falling back to the former fully unfolded replay shape when compact replay is too
coarse. -/
def lowerLFDerivationToKernel (sig : HLSignature) (rules : Array CheckedLFRule)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name)
    (derivation : CheckedLFDerivation) : CoreM KernelLFDerivation := do
  try
    lowerLFDerivationToKernelWithMode sig rules globalHeads knownTypes defValues localNames
      theoremName false derivation
  catch _ =>
    lowerLFDerivationToKernelWithMode sig rules globalHeads knownTypes defValues localNames
      theoremName true derivation

/-- Try to lower legacy raw-kernel replay without making that compatibility path authoritative. -/
def tryLowerLFDerivationToKernel? (sig : HLSignature) (rules : Array CheckedLFRule)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name)
    (derivation : CheckedLFDerivation) : CoreM (Option KernelLFDerivation) := do
  try
    let kernelDerivation ← lowerLFDerivationToKernel sig rules globalHeads knownTypes defValues
      localNames theoremName derivation
    pure (some kernelDerivation)
  catch ex =>
    logInfo m!"legacy raw kernel replay lowering failed for judgment_theorem '{theoremName}' \
      in type theory '{sig.name}'; structural replay will decide acceptance.\n{ex.toMessageData}"
    pure none

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
  | .arrow x A B | .funArrow x A B | .sigma x A B => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals B
  | .pair a b => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals a
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals b
  | .fst e | .snd e =>
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals e
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals body
  | .jeq lhs rhs => do
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals lhs
      checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
        locals rhs

/-- Check an LF annotation that is expected to denote an object or structural package type,
using a reusable lookup context.

This shared path validates known identifiers, universe hygiene, LF-definition availability, syntax
sort arities and arguments, inferable-application arguments, and the recursive LF type-expression
discipline. It accepts syntax-sort heads, local type-family heads whose inferred kind is a
universe, and structural function/Sigma package types. Judgment-headed expressions are rejected by
this helper; callers that want theorem-shaped admissions should classify those before calling it. -/
def checkLFObjectOrStructuralTypeWithLookup (lookup : LFCheckLookupContext) (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
    (typeExpr : ObjExpr) : CoreM (Option CheckedLFHead) := do
  let lfGlobals := lfKnownGlobalNames sig
  let opaqueArities := lfOpaqueArities sig
  let syntaxSortArities : NameMap Nat := lfSyntaxFamilyArities sig
  checkKnownNamesInLFExpr sig lfGlobals locals opaqueArities ownerKind ownerName where_ typeExpr
  checkNoLFLocalBinderShadowingInExpr sig ownerKind ownerName where_ typeExpr
    (baseLocals := locals)
  checkDeclaredLevelParamsInLFExpr sig ownerKind ownerName where_ typeExpr
  checkNoCaptureUnsafeBetaInLFExpr sig ownerKind ownerName where_ typeExpr
  checkLFDefinitionReferencesAvailable sig globalHeads knownTypes ownerKind ownerName where_
    (locals := locals) typeExpr
  checkSyntaxSortApplicationsInExpr sig syntaxSortArities ownerKind ownerName where_ typeExpr
  checkLFBinderTypeWithLookup lookup sig globalHeads ownerKind ownerName where_ knownTypes locals
    false typeExpr
  let typeExpr := eraseObjExprScopes typeExpr
  let typeHead? := checkedLFHead? globalHeads locals typeExpr
  match typeHead? with
  | some typeHead =>
      if typeHead.kind != .syntaxSort && typeHead.kind != .syntaxDef &&
          typeHead.kind != .local then
        throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} headed \
          by {typeHead.kind.label} '{typeHead.name}', expected a syntax-family-, \
            local-family-, or structural package type"
  | none =>
      unless lfOpaqueResultIsStructuralType typeExpr do
        throwError "{ownerKind} '{ownerName}' in type theory '{sig.name}' has {where_} not \
          headed by a known LF identifier or structural package type: {typeExpr}"
  pure typeHead?

/-- Check an LF annotation that is expected to denote an object or structural package type. -/
def checkLFObjectOrStructuralType (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownTypes : LFLocalTypes)
    (locals : NameSet) (ownerKind : String) (ownerName : Name) (where_ : String)
    (typeExpr : ObjExpr) : CoreM (Option CheckedLFHead) :=
  checkLFObjectOrStructuralTypeWithLookup (mkLFCheckLookupContext sig) sig globalHeads knownTypes
    locals ownerKind ownerName where_ typeExpr

/-- Check an `lf_def` type annotation and return its final rigid LF head, when it has one,
using a reusable lookup context.

This combines the recursive LF type-expression discipline with the object-definition result-shape
check, so `lf_def` checking does not also need separate syntax-sort and inferable-application
passes over the same annotation. -/
def checkLFObjectDefTypeAndResultHeadWithLookup? (lookup : LFCheckLookupContext)
    (sig : HLSignature) (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
    (knownLFDefTypes : LFLocalTypes) (d : LFObjectDefDecl) :
    CoreM (Option CheckedLFHead) := do
  discard <| checkLFObjectOrStructuralTypeWithLookup lookup sig globalHeads knownLFDefTypes {}
    "lf_def" d.name "type" d.typeExpr
  let resultTypeExpr := eraseObjExprScopes (lfFunctionTypeResult d.typeExpr)
  let typeHead? := checkedLFHead? globalHeads {} resultTypeExpr
  match typeHead? with
  | some typeHead =>
      if typeHead.kind != .syntaxSort && typeHead.kind != .syntaxDef then
        throwError "lf_def '{d.name}' in type theory '{sig.name}' has result type headed by \
          {typeHead.kind.label} '{typeHead.name}', expected a syntax-family-headed or structural \
            record/Sigma type"
  | none =>
      unless lfObjectDefResultIsStructuralRecord resultTypeExpr do
        throwError "lf_def '{d.name}' in type theory '{sig.name}' has type not ending in a known \
          LF identifier or structural record/Sigma type: {d.typeExpr}"
  pure typeHead?

/-- Check an `lf_def` type annotation and return its final rigid LF head, when it has one. -/
def checkLFObjectDefTypeAndResultHead? (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (knownLFDefTypes : LFLocalTypes)
    (d : LFObjectDefDecl) : CoreM (Option CheckedLFHead) :=
  checkLFObjectDefTypeAndResultHeadWithLookup? (mkLFCheckLookupContext sig) sig globalHeads
    knownLFDefTypes d

end InternalLean
