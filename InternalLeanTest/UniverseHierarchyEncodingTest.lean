/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Examples.UniverseHierarchy

/-!
# Object-language universe hierarchy encoding tests

These regressions exercise the hand-written universe-hierarchy prelude from
`Examples.UniverseHierarchy`.  Object levels remain ordinary LF syntax; all acceptance still flows
through checked LF replay and generated model obligations.
-/

@[expose] public section

open Lean Elab Command
open InternalLean

namespace UniverseHierarchyMacroLabelTokenSmoke

-- The shorthand parses its field labels as identifiers where possible; it must not reserve these.
def levels : Nat := 0
def le : Nat := 0
def wf : Nat := 0
def lift : Nat := 0

end UniverseHierarchyMacroLabelTokenSmoke

namespace UniverseHierarchyNotationTokenSmoke

-- The bracketed notation heads must not reserve plausible Lean identifiers.
def 𝒰 : Nat := 0
def El : Nat := 0
def Level : Nat := 0
def lmax : Nat := 0

end UniverseHierarchyNotationTokenSmoke

#check UniverseHierarchy.Model
#check UniverseHierarchy.syntacticModel
#check UniverseHierarchy.natModel
#check UniverseHierarchy.zero_le_succ_zero
#check UniverseHierarchy.liftedZeroUniv
#check UniverseHierarchy.liftedZeroUniv_wf
#check UniverseHierarchy.liftedZeroUnivLmax
#check UniverseHierarchy.liftedZeroUnivLmax_wf
#check UniverseHierarchy.unitToUnitPi
#check UniverseHierarchy.LFQuote.Pi
#check UniverseHierarchy.LFQuote.Sigma
#check UniverseHierarchy.LFQuote.UnitTy

example : UniverseHierarchy.natModel.Le UniverseHierarchy.natModel.zero
    (UniverseHierarchy.natModel.succ UniverseHierarchy.natModel.zero) :=
  UniverseHierarchy.natModel.le_succ UniverseHierarchy.natModel.zero

example : UniverseHierarchy.natModel.IsTy
    (UniverseHierarchy.natModel.Univ UniverseHierarchy.natModel.zero) :=
  UniverseHierarchy.natModel.univ_wf UniverseHierarchy.natModel.zero

run_cmd do
  let some checked ← liftCoreM <| getCheckedTheory? `UniverseHierarchy
    | throwError "missing checked UniverseHierarchy artifact"
  unless checked.lfLevelNormalizerProfiles.size == 1 do
    throwError "expected one level-normalizer profile"
  let some profile := checked.lfLevelNormalizerProfiles[0]?
    | throwError "missing level-normalizer profile"
  unless profile.solverName == `level_norm_solver && profile.pluginName == `level_norm do
    throwError "unexpected level-normalizer generated names"
  let levelCerts := checked.lfSideConditionCertificates.filter fun cert =>
    cert.kind == .levelNormalizer
  unless levelCerts.size == 1 do
    throwError "expected one level-normalizer side-condition certificate"
  let some cert := levelCerts[0]?
    | throwError "missing level-normalizer certificate"
  unless cert.certificateName == `lift_lmax_left_wf.side_condition.le_left do
    throwError "unexpected level-normalizer certificate name '{cert.certificateName}'"
  unless cert.diagnostic.contains "lhs_nf=i" && cert.diagnostic.contains "rhs_nf=max(i, j)" do
    throwError "missing level-normalizer normal-form diagnostic: {cert.diagnostic}"
  let replay ← kernelLFReplayCertificateForTheorem checked `liftedZeroUnivLmax_wf
  let audit := kernelLFReplayCertificateAuditString `UniverseHierarchy `liftedZeroUnivLmax_wf
    replay checked
  unless audit.contains "external certificates used: lift_lmax_left_wf.side_condition.le_left" do
    throwError "replay audit did not mention the level certificate"

#guard
  let lhs := Raw.tmApp `lmax [.tmMeta `i, .tmApp `lmax [.tmMeta `j, .tmMeta `i]]
  let rhs := Raw.tmApp `lmax [.tmMeta `j, .tmMeta `i]
  let stmt : ConversionStatement := { plugin := `level_norm, lhs := lhs, rhs := rhs }
  let profile : LevelNormalizerRawProfile := {
    zeroName := `zero
    succName := `succ
    maxName := `lmax }
  let sig : Signature := {
    name := `T
    conversionPlugins := [{
      name := `level_norm
      trust := .executableChecked
      supportedSteps := [.reindexing]
      levelNormalizer? := some profile }] }
  match KernelLFConversionCertificate.check sig (.pluginStep stmt .reindexing none [] "") stmt with
  | .ok () => true
  | .error _ => false

#guard
  let stmt : ConversionStatement := {
    plugin := `level_norm
    lhs := .tmApp `succ [.tmMeta `i]
    rhs := .tmMeta `i }
  let profile : LevelNormalizerRawProfile := {
    zeroName := `zero
    succName := `succ
    maxName := `lmax }
  let sig : Signature := {
    name := `T
    conversionPlugins := [{
      name := `level_norm
      trust := .executableChecked
      supportedSteps := [.reindexing]
      levelNormalizer? := some profile }] }
  match KernelLFConversionCertificate.checkDetailed sig (.pluginStep stmt .reindexing none [] "")
      stmt with
  | .ok _ => false
  | .error err =>
      err.kind == .malformedCertificate &&
        err.message.contains "level-normalizer conversion failed"

#guard
  let head (n : Name) : Kernel.KTerm := .ident { name := Kernel.KName.ofName n }
  let app2 (n : Name) (lhs rhs : Kernel.KTerm) : Kernel.KTerm :=
    .app (.app (head n) lhs) rhs
  let i : Kernel.KTerm := .mvar (Kernel.KName.ofName `i) .arg
  let j : Kernel.KTerm := .mvar (Kernel.KName.ofName `j) .arg
  let lhs := app2 `lmax i (app2 `lmax j i)
  let rhs := app2 `lmax j i
  let stmt : Kernel.ConversionStatement := {
    plugin := Kernel.KName.ofName `level_norm
    lhs := lhs
    rhs := rhs }
  let profile : Kernel.LevelNormalizerKProfile := {
    zeroName := Kernel.KName.ofName `zero
    succName := Kernel.KName.ofName `succ
    maxName := Kernel.KName.ofName `lmax }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `T
    conversionPlugins := [{
      name := Kernel.KName.ofName `level_norm
      trust := .executableChecked
      supportedSteps := [.reindexing]
      levelNormalizer? := some profile }] }
  match Kernel.CheckedKernelLFConversionCertificate.check sig {}
      stmt (.pluginStep stmt .reindexing none [] "") with
  | .ok _ => true
  | .error _ => false

#guard
  let head (n : Name) : Kernel.KTerm := .ident { name := Kernel.KName.ofName n }
  let app1 (n : Name) (arg : Kernel.KTerm) : Kernel.KTerm := .app (head n) arg
  let i : Kernel.KTerm := .mvar (Kernel.KName.ofName `i) .arg
  let stmt : Kernel.ConversionStatement := {
    plugin := Kernel.KName.ofName `level_norm
    lhs := app1 `succ i
    rhs := i }
  let profile : Kernel.LevelNormalizerKProfile := {
    zeroName := Kernel.KName.ofName `zero
    succName := Kernel.KName.ofName `succ
    maxName := Kernel.KName.ofName `lmax }
  let sig : Kernel.Signature := {
    name := Kernel.KName.ofName `T
    conversionPlugins := [{
      name := Kernel.KName.ofName `level_norm
      trust := .executableChecked
      supportedSteps := [.reindexing]
      levelNormalizer? := some profile }] }
  match Kernel.CheckedKernelLFConversionCertificate.checkDetailed sig {}
      stmt (.pluginStep stmt .reindexing none [] "") with
  | .ok _ => false
  | .error err =>
      err.kind == .malformedCertificate &&
        err.message.contains "level-normalizer conversion failed"

-- Native-tactic goals for the hierarchy render through the mirror display backend.
run_cmd do
  let target : InternalDefTarget := {
    theoryName := `UniverseHierarchy
    localName := `zero_le_succ_zero
    anchorName := `UniverseHierarchy.zero_le_succ_zero }
  let targetExpr : ObjExpr :=
    .app (.app (.ident `Le) (.ident `zero)) (.app (.ident `succ) (.ident `zero))
  let snapshot ← liftTermElabM do
    let displayCtx ← prepareInternalGoalDisplayContext target
    let goal := mkInternalGoalDisplayGoal #[] targetExpr
    mkInternalObjectGoalDisplaySnapshotWithContext target displayCtx #[goal]
  unless snapshot.fallbacks.isEmpty do
    throwError "universe hierarchy goal display unexpectedly used fallback"
  let some mvarId := snapshot.goals.head? | throwError "missing hierarchy display goal"
  let mvarDecl := snapshot.mctx.getDecl mvarId
  match mvarDecl.type.getAppFn with
  | .const n _ =>
      unless n == lfMirrorDeclName `UniverseHierarchy `Le do
        throwError "hierarchy display goal has unexpected head '{n}'"
  | _ => throwError "hierarchy display goal is not headed by a mirror constant"

/--
info: reflected LF term in type theory 'UniverseHierarchy':
  lift (succ zero) (succ (succ zero)) (Univ zero)
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote UniverseHierarchy :
  lift (i := succ zero) (j := succ (succ zero)) (Univ zero)

/--
info: reflected LF term in type theory 'UniverseHierarchy':
  Pi zero zero (UnitTy zero) (fun x => UnitTy zero)
-/
#guard_msgs (whitespace := lax) in
#reflect_lf_quote UniverseHierarchy :
  Pi (i := zero) (j := zero) (UnitTy (i := zero)) fun _ => UnitTy (i := zero)

/--
info: "𝒰[" i "]" => Ty i
"El[" A "]" => Tm A
"Level.max[" i "," j "]" => lmax i j
-/
#guard_msgs in
#print_object_notations UniverseHierarchy

/--
info: Ty (lmax zero (succ zero))
-/
#guard_msgs in
#expand_object UniverseHierarchy 𝒰[ Level.max[ zero, succ zero ] ]

/--
info: Tm (Univ zero)
-/
#guard_msgs in
#expand_object UniverseHierarchy El[ Univ zero ]

run_cmd do
  let uNotation ← elabObjExpr (← `(ttExpr| 𝒰[ Level.max[ zero, succ zero ] ]))
  let uExpanded ← elabObjExpr (← `(ttExpr| Ty (lmax zero (succ zero))))
  unless eraseObjExprScopes uNotation == eraseObjExprScopes uExpanded do
    throwError "universe notation did not expand to the ordinary type-code expression"
  let elNotation ← elabObjExpr (← `(ttExpr| El[ Univ zero ]))
  let elExpanded ← elabObjExpr (← `(ttExpr| Tm (Univ zero)))
  unless eraseObjExprScopes elNotation == eraseObjExprScopes elExpanded do
    throwError "element notation did not expand to the ordinary element expression"
  let maxNotation ← elabObjExpr (← `(ttExpr| Level.max[ zero, succ zero ]))
  let maxExpanded ← elabObjExpr (← `(ttExpr| lmax zero (succ zero)))
  unless eraseObjExprScopes maxNotation == eraseObjExprScopes maxExpanded do
    throwError "level-maximum notation did not expand to the ordinary object expression"

extend_type_theory UniverseHierarchy where
  lf_def notationMaxZeroSucc : Level := Level.max[ zero, succ zero ]
  lf_opaque notationUnit : 𝒰[ zero ]
  lf_opaque notationElem : El[ notationUnit ]

#check UniverseHierarchy.LFQuote.notationMaxZeroSucc
#check UniverseHierarchy.LFQuote.notationUnit
#check UniverseHierarchy.LFQuote.notationElem

/--
error: syntax_def 'Bad' in type theory 'BadUniverseHierarchySyntaxDef' has value in universe
'Type 1', expected 'Type'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadUniverseHierarchySyntaxDef where
  syntax_sort Level : Type
  syntax_sort Ty (i : Level) : Type 1
  lf_opaque zero : Level
  syntax_def Bad : Type := Ty zero

/-- Hand-written baseline for the `universe_hierarchy` DSL shorthand. -/
declare_type_theory HandWrittenUniverseHierarchyMacroBaseline{u} where
  syntax_sort Level : Type u
  syntax_sort Ty (i : Level) : Type (u+1)
  syntax_sort Tm {i : Level} (A : Ty i) : Type u

  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level

  judgment Le (i : Level) (j : Level)
  rule le_refl (i : Level) : Le i i
  rule le_succ (i : Level) : Le i (succ i)

  lf_opaque lift {i : Level} {j : Level} (A : Ty i) : Ty j
  judgment IsTy {i : Level} (A : Ty i)
  rule lift_wf {i : Level} {j : Level} (A : Ty i) where
    premise le : Le i j
    premise wf : IsTy (i := i) A
    conclusion : IsTy (i := j) (lift (i := i) (j := j) A)

  lf_opaque Univ (i : Level) : Ty (succ i)
  rule univ_wf (i : Level) : IsTy (i := succ i) (Univ i)

/-- The same prelude generated by the `universe_hierarchy` shorthand. -/
declare_type_theory MacroUniverseHierarchySmoke{u} where
  universe_hierarchy Level Ty Tm where
    levels zero succ lmax
    le Le
    wf IsTy
    lift lift
    universe Univ

#check_theory MacroUniverseHierarchySmoke

generate_model_interface HandWrittenUniverseHierarchyMacroBaseline as
  HandWrittenUniverseHierarchyMacroBaselineModel
generate_model_interface MacroUniverseHierarchySmoke as MacroUniverseHierarchySmokeModel
generate_syntactic_model_instance MacroUniverseHierarchySmoke as macroSyntacticModel for
  MacroUniverseHierarchySmokeModel

#check MacroUniverseHierarchySmoke.LFQuote.Level
#check MacroUniverseHierarchySmoke.LFQuote.Ty
#check MacroUniverseHierarchySmoke.LFQuote.Tm
#check MacroUniverseHierarchySmoke.LFQuote.lift
#check MacroUniverseHierarchySmoke.LFQuote.Univ
#check MacroUniverseHierarchySmoke.macroSyntacticModel

namespace UniverseHierarchyMacroSmokeTest

open LeanTypeModelGeneration

private def hierarchyDeclNames : Array Name := #[
  `Level, `Ty, `Tm, `zero, `succ, `lmax, `Le, `le_refl, `le_succ,
  `lift, `IsTy, `lift_wf, `Univ, `univ_wf
]

private meta def modelFieldNames (obs : Array LFModelObligation) : Array Name :=
  obs.filterMap fun o =>
    if o.generatedRole == .field && o.renderable then
      some o.name.eraseMacroScopes
    else
      none

run_cmd do
  let some hand ← liftCoreM <| getCheckedHLSignature?
      `HandWrittenUniverseHierarchyMacroBaseline
    | throwError "missing hand-written hierarchy baseline"
  let some macroSig ← liftCoreM <| getCheckedHLSignature? `MacroUniverseHierarchySmoke
    | throwError "missing macro-generated hierarchy"
  unless hand.syntaxSorts == macroSig.syntaxSorts do
    throwError "macro hierarchy syntax sorts differ from the hand-written baseline"
  unless hand.lfOpaqueConsts == macroSig.lfOpaqueConsts do
    throwError "macro hierarchy LF opaque constants differ from the hand-written baseline"
  unless hand.judgments == macroSig.judgments do
    throwError "macro hierarchy judgments differ from the hand-written baseline"
  unless hand.rules == macroSig.rules do
    throwError "macro hierarchy rules differ from the hand-written baseline"
  let macroRoles := macroSig.universeHierarchyRoleProfile
  unless macroRoles.complete do
    throwError "macro hierarchy role profile is incomplete: {macroRoles.summaryString}"
  unless macroRoles.levelSorts == #[`Level] && macroRoles.codeSorts == #[`Ty] &&
      macroRoles.elementSorts == #[`Tm] && macroRoles.leqJudgments == #[`Le] do
    throwError "macro hierarchy role profile has unexpected declarations: \
      {macroRoles.summaryString}"

  let some handChecked ← liftCoreM <| getCheckedTheory?
      `HandWrittenUniverseHierarchyMacroBaseline
    | throwError "missing checked hand-written hierarchy baseline"
  let some macroChecked ← liftCoreM <| getCheckedTheory? `MacroUniverseHierarchySmoke
    | throwError "missing checked macro-generated hierarchy"
  let handObs ← validateLFModelObligations handChecked {}
  let macroObs ← validateLFModelObligations macroChecked {}
  let handFields := modelFieldNames handObs
  let macroFields := modelFieldNames macroObs
  unless handFields == macroFields do
    throwError "macro hierarchy model field names differ: hand-written {handFields}, \
      macro-generated {macroFields}"
  let roleLines := modelUniverseHierarchyRoleLines macroChecked macroObs
  let expectedRoleLines := #[
    "universe hierarchy model fields (complete role profile):",
    "  levels: Level",
    "  codes: Ty",
    "  elements: Tm",
    "  level order: Le",
    "  type-code formers returning recognized codes: lift, Univ",
    "  diagnostics: none"
  ]
  unless roleLines == expectedRoleLines do
    throwError "unexpected macro hierarchy model-role lines: {roleLines}"

  let env ← getEnv
  for n in hierarchyDeclNames do
    unless env.contains (lfQuoteDeclName `MacroUniverseHierarchySmoke n) do
      throwError "missing macro hierarchy quote stub for '{n}'"
    unless env.contains (lfMirrorDeclName `MacroUniverseHierarchySmoke n) do
      throwError "missing macro hierarchy mirror declaration for '{n}'"
    let some _ ← liftCoreM <| internalSourceDeclAnchorName? `MacroUniverseHierarchySmoke n
      | throwError "missing macro hierarchy source anchor for '{n}'"

end UniverseHierarchyMacroSmokeTest

/--
info: logical-framework roles for MacroUniverseHierarchySmoke (4 declarations, parents flattened)
---
info: universe hierarchy roles: complete
  levels: Level
  codes: Ty
  elements: Tm
  level order: Le
  diagnostics: none
---
info: syntax_sort_role Level : universe_level
---
info: syntax_sort_role Ty : universe_code
---
info: syntax_sort_role Tm : universe_element
---
info: judgment_role Le : universe_leq
-/
#guard_msgs (whitespace := lax) in
#print_logical_framework_roles MacroUniverseHierarchySmoke

/-- Partial hierarchy roles are diagnostic metadata; the theory still checks normally. -/
declare_type_theory PartialUniverseHierarchyRoleSmoke where
  syntax_sort Obj
  syntax_sort_role Obj : universe_level

#check_theory PartialUniverseHierarchyRoleSmoke

/--
info: type theory PartialUniverseHierarchyRoleSmoke with 2 logical-framework declarations
---
info: universe hierarchy roles: partial
  levels: Obj
  codes: (none)
  elements: (none)
  level order: (none)
  diagnostics: missing universe_code syntax sort, universe_element syntax sort,
    universe_leq judgment
---
info: syntax_sort Obj
---
info: syntax_sort_role Obj : universe_level
-/
#guard_msgs (whitespace := lax) in
#print_type_theory PartialUniverseHierarchyRoleSmoke

/--
info: model obligations for PartialUniverseHierarchyRoleSmoke (generic LF-model backend)
LF model obligations for PartialUniverseHierarchyRoleSmoke: 1 obligation(s), 1 user field(s),
  0 generated method/declaration(s), 0 theorem-local certificate parameter(s), 0 replay artifact(s),
  0 metadata expansion(s), 0 blocked/omitted obligation(s)
field breakdown: 1 syntax_sort
next action: run `#print_model_interface PartialUniverseHierarchyRoleSmoke as <Name>`, then fill
  the 1 user field(s); checked LF definitions/theorems can be generated afterward with
  `#print_model_transports`.
universe hierarchy model fields (partial role profile):
  levels: Obj
  codes: (none)
  elements: (none)
  level order: (none)
  type-code formers returning recognized codes: (none)
  diagnostics: missing universe_code syntax sort, universe_element syntax sort,
    universe_leq judgment
metatheory accounting:
  primitive user fields: 1
  checked derived declarations: 0
  checked metadata expansions: 0
  generated induction principles: 0 judgment family(ies), 0 rule case(s),
    0 recursive premise(s); not model fields
  generated congruence candidates: 0; not model fields unless declared as primitive rules
  admitted internal declarations: 0
  blocked/omitted items: 0
fields to provide:
  Obj ← syntax_sort Obj: ready
derived declarations generated from replay: none
theorem-local certificate parameters: none
blocked/omitted: none
-/
#guard_msgs (whitespace := lax) in
#print_model_obligations PartialUniverseHierarchyRoleSmoke

/--
error: duplicate judgment declaration 'Level' in type-theory block
-/
#guard_msgs in
declare_type_theory BadUniverseHierarchyMacroDuplicate{u} where
  universe_hierarchy Level Ty Tm where
    levels zero succ lmax
    le Level
    wf IsTy
    lift lift
    universe Univ

/--
error: expected universe_hierarchy field 'levels', got 'levelz'
-/
#guard_msgs in
declare_type_theory BadUniverseHierarchyMacroLabel{u} where
  universe_hierarchy Level Ty Tm where
    levelz zero succ lmax
    le Le
    wf IsTy
    lift lift
    universe Univ

declare_type_theory LevelNormalizerMaxTreeSmoke where
  syntax_sort Level
  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level
  judgment Le (i : Level) (j : Level)
  level_normalizer Level zero succ lmax Le
  rule max_tree (a : Level) (b : Level) (c : Level) (d : Level) where
    side_condition le by level_norm_solver :
      Le (lmax (lmax a b) (lmax c d)) (lmax (lmax d c) (lmax b a))
    conclusion : Le (lmax (lmax a b) (lmax c d)) (lmax (lmax d c) (lmax b a))

#check_theory LevelNormalizerMaxTreeSmoke

/--
error: level-normalizer side-condition 'nope' in rule 'bad' failed: lhs normal form i,
  rhs normal form j
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadLevelNormalizerOrder where
  syntax_sort Level
  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level
  judgment Le (i : Level) (j : Level)
  level_normalizer Level zero succ lmax Le
  rule bad (i : Level) (j : Level) where
    side_condition nope by level_norm_solver : Le i j
    conclusion : Le i j

/--
error: unsupported level-normalizer head 'weird' in 'weird i'
-/
#guard_msgs in
declare_type_theory BadLevelNormalizerHead where
  syntax_sort Level
  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level
  lf_opaque weird (i : Level) : Level
  judgment Le (i : Level) (j : Level)
  level_normalizer Level zero succ lmax Le
  rule bad (i : Level) where
    side_condition nope by level_norm_solver : Le i (weird i)
    conclusion : Le i i

/--
error: judgment_theorem 'use' in type theory 'MissingLevelNormalizerProfile' applies rule 'ok'
  but side-condition 'le' uses opaque solver 'level_norm_solver' with no checked certificate
-/
#guard_msgs (whitespace := lax) in
declare_type_theory MissingLevelNormalizerProfile where
  side_condition_solver level_norm_solver
  syntax_sort Level
  lf_opaque zero : Level
  lf_opaque succ (i : Level) : Level
  lf_opaque lmax (i : Level) (j : Level) : Level
  judgment Le (i : Level) (j : Level)
  rule ok (i : Level) (j : Level) where
    side_condition le by level_norm_solver : Le i (lmax i j)
    conclusion : Le i (lmax i j)
  judgment_theorem use : Le zero (lmax zero zero) := ok zero zero
