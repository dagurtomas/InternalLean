/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.ReplayAudit
public meta import InternalLean.InternalTactic

/-!
# Diagnostics for user-declared type theories

This file contains object-role commands, documentation/admission lints, type-theory
metadata printers, and LF replay-certificate diagnostics.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

elab "object_macro" theory:ident macroName:ident "(" params:ident,* ")" " => " template:ttExpr :
  command => do
  let template ← elabObjExpr template
  liftCoreM <| registerObjectMacro theory.getId {
    name := macroName.getId
    params := params.getElems.map (·.getId)
    template := template }

/-- Attach non-semantic role metadata to an object declaration or macro. -/
elab "object_role" theory:ident objectName:ident " : " kind:ident : command => do
  liftCoreM <| registerObjectRole theory.getId {
    name := objectName.getId
    kind := kind.getId }

/-- Attach non-semantic role metadata with a related object declaration or macro. -/
elab "object_role" theory:ident objectName:ident " : " kind:ident " for " related:ident :
  command => do
  liftCoreM <| registerObjectRole theory.getId {
    name := objectName.getId
    kind := kind.getId
    related := some related.getId }

/-- Print registered theory-local object macros. -/
elab "#print_object_macros" theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let lines := flatSig.macros.toList.map fun mac =>
    let params := String.intercalate " " (mac.params.toList.map (toString ·.eraseMacroScopes))
    s!"{mac.name.eraseMacroScopes} ({params}) => {mac.template}"
  logInfo m!"{String.intercalate "\n" lines}"

/-- Print registered theory-local object roles. -/
elab "#print_object_roles" theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let lines := flatSig.roles.toList.map fun role =>
    let related := match role.related with | some n => s!" for {n.eraseMacroScopes}" | none => ""
    s!"{role.name.eraseMacroScopes} : {role.kind.eraseMacroScopes}{related}"
  logInfo m!"{String.intercalate "\n" lines}"

/-- User-facing side-condition/certificate summary for object tactic and model workflows. -/
def internalLeanSideConditionSummaryString (sig : HLSignature) : String := Id.run do
  let mut lines := #[s!"side-condition summary for {sig.name.eraseMacroScopes}"]
  let mut count := 0
  for r in sig.rules do
    for ev in r.paramEvidences do
      count := count + 1
      lines :=
        lines.push s!"rule {r.name.eraseMacroScopes} evidence {ev.name.eraseMacroScopes} for \
          {ev.paramName.eraseMacroScopes}: {ev.judgmentExpr} (object tactic subgoal/premise)"
    for sc in r.sideConditions do
      count := count + 1
      let status := match classifySideConditionHook sc.solver with
        | .builtinTrivial =>
          s!"checked certificate generated automatically as \
            {lfSideConditionCertificateName r.name sc.name}"
        | .opaque =>
          "opaque solver: core object tactics cannot synthesize this certificate; model backends \
            may expose a theorem-local certificate parameter when renderable"
      lines :=
        lines.push s!"rule {r.name.eraseMacroScopes} side_condition {sc.name.eraseMacroScopes} by \
          {sc.solver.eraseMacroScopes}: {sc.input} -- {status}"
  if count == 0 then
    lines := lines.push "no rule side-condition or parameter-evidence obligations"
  lines :=
    lines.push "layer note: these are LF replay certificate obligations, not Lean goals; internal \
      equality proofs must be applied through declared object rules/theorems."
  String.intercalate "\n" lines.toList

/-- Print side-condition certificate obligations relevant to object tactics and model replay. -/
elab "#print_type_theory_side_conditions" theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  logInfo m!"{internalLeanSideConditionSummaryString flatSig}"

/-- User-facing name rendering for documentation/admission lints. -/
def docLintNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Whether an object expression mentions a named object constant/variable. -/
partial def objExprMentionsName (needle : Name) : ObjExpr → Bool
  | .ident n => n.eraseMacroScopes == needle.eraseMacroScopes
  | .sort | .univ .. => false
  | .app f a => objExprMentionsName needle f || objExprMentionsName needle a
  | .arrow _ A B | .funArrow _ A B => objExprMentionsName needle A || objExprMentionsName needle B
  | .lam _ body => objExprMentionsName needle body
  | .jeq lhs rhs => objExprMentionsName needle lhs || objExprMentionsName needle rhs

/-- Downstream declarations whose source body/proof mentions admitted internal declarations. -/
def internalAdmissionDependencyLines (sig : HLSignature) (admissions : Array InternalAdmission) :
  Array String := Id.run do
  let admittedNames := admissions.map (·.declName)
  let mut out := #[]
  let depsForExpr (e : ObjExpr) := admittedNames.filter (fun n => objExprMentionsName n e)
  for d in sig.lfObjectDefs do
    let deps := depsForExpr d.value
    unless deps.isEmpty do
      out :=
        out.push s!"internal def {docLintNameString d.name} depends on admitted \
          {String.intercalate ", " (deps.toList.map docLintNameString)}"
  for t in sig.lfJudgmentTheorems do
    let deps := depsForExpr t.proof
    unless deps.isEmpty do
      out :=
        out.push s!"internal def {docLintNameString t.name} depends on admitted \
          {String.intercalate ", " (deps.toList.map docLintNameString)}"
  return out

/-- One source item checked by the documentation linter. -/
structure DocLintItem where
  role : SourceDocRole
  sourceName : Name
  generatedName? : Option Name := none
  deriving Inhabited, Repr

/-- Whether an internal declaration anchor exists for a theory-local name. -/
def hasInternalDeclarationAnchor (theoryName localName : Name) : CoreM Bool := do
  return (← getEnv).contains (theoryName ++ localName)

/-- Source items that should carry docs for polished theory/library UX. -/
def docLintItems (sig : HLSignature) : CoreM (Array DocLintItem) := do
  let admissions ← getInternalAdmissionsFor sig.name
  let admittedNames := admissions.foldl (init := ({} : NameSet)) fun acc a => acc.insert a.declName
  let theoryItem : DocLintItem := {
    role := .theory
    sourceName := sig.name
    generatedName? := some (theoryAnchorName sig.name)
  }
  let mut out := #[theoryItem]
  for s in sig.syntaxSorts do out := out.push { role := .syntaxSort, sourceName := s.name }
  for a in sig.syntaxAbbrevs do out := out.push { role := .syntaxAbbrev, sourceName := a.name }
  for z in sig.contextZones do out := out.push { role := .contextZone, sourceName := z.name }
  for b in sig.binderClasses do out := out.push { role := .binderClass, sourceName := b.name }
  for j in sig.judgments do out := out.push { role := .judgment, sourceName := j.name }
  for r in sig.rules do out := out.push { role := .rule, sourceName := r.name }
  for s in sig.sideConditionSolvers do
    out := out.push { role := .sideConditionSolver, sourceName := s.name }
  for p in sig.conversionPlugins do
    out := out.push { role := .conversionPlugin, sourceName := p.name }
  for c in sig.lfOpaqueConsts do
    if admittedNames.contains c.name then
      out := out.push {
        role := .internalDef
        sourceName := c.name
        generatedName? := some (sig.name ++ c.name)
      }
    else
      out := out.push { role := .lfOpaque, sourceName := c.name }
  for d in sig.lfObjectDefs do
    let role ← if (← hasInternalDeclarationAnchor sig.name d.name) then
      pure SourceDocRole.internalDef else pure SourceDocRole.lfObjectDef
    let generatedName? := if role == .internalDef then some (sig.name ++ d.name) else none
    out := out.push { role, sourceName := d.name, generatedName? }
  for t in sig.lfJudgmentTheorems do
    let role ← if (← hasInternalDeclarationAnchor sig.name t.name) then
      pure SourceDocRole.internalDef else pure SourceDocRole.lfJudgmentTheorem
    let generatedName? := if role == .internalDef then some (sig.name ++ t.name) else none
    out := out.push { role, sourceName := t.name, generatedName? }
  return out

/-- Documentation linter output for a type theory. -/
def lintInternalLeanDocsString (sig : HLSignature) : CoreM (Bool × String) := do
  let items ← docLintItems sig
  let mut missing := #[]
  let mut documented := 0
  for item in items do
    if (← findSourceDoc? sig.name item.role item.sourceName).isSome then
      documented := documented + 1
    else
      let generated := match item.generatedName? with
        | some n => s!", generated anchor {docLintNameString n}"
        | none => ""
      missing :=
        missing.push s!"missing doc: {item.role.label} \
          {docLintNameString item.sourceName}{generated}"
  if missing.isEmpty then
    pure (true,
      s!"type theory '{docLintNameString sig.name}' documentation lint passed: {documented} \
        documented public item(s)")
  else
    pure (false, String.intercalate "\n" <|
      s!"type theory '{docLintNameString sig.name}' is missing docs for {missing.size} public \
        item(s):" :: missing.toList)

/-- Source docstring for an internal declaration, if available. -/
def findInternalSourceDoc? (theoryName localName : Name) : CoreM (Option String) := do
  if let some doc ← findSourceDoc? theoryName .internalDef localName then
    return some doc
  findAnySourceDocForName? theoryName localName

/-- Generated docstring for a transported or interpreted declaration. -/
def generatedDeclarationDocString (theoryName localName : Name) (backend roleText : String) (
  sourceDoc? : Option String) : String :=
  let sourceDocLines :=
    match sourceDoc? with
    | some doc => ["", "Source documentation:", trimCapturedDoc doc]
    | none => ["",
      "Source documentation: missing; run `#lint_type_theory_docs` on the source theory."]
  String.intercalate "\n" <|
    [ s!"Generated declaration `{theoryName.eraseMacroScopes}.{localName.eraseMacroScopes}`.",
      s!"Source internal/object declaration: {localName.eraseMacroScopes}.",
      s!"Backend: {backend}.",
      s!"Generated role: {roleText}.",
      "The generated Lean declaration is backed by checked object-theory/LF artifacts for this \
        backend." ] ++ sourceDocLines

/-- Generated docstring for a model-interface method available by dot notation. -/
def generatedModelMethodDocString (theoryName structureName methodName sourceName : Name)
    (backend roleText : String) (sourceDoc? : Option String) : String :=
  let sourceDocLines :=
    match sourceDoc? with
    | some doc => ["", "Source documentation:", trimCapturedDoc doc]
    | none => ["",
      "Source documentation: missing; run `#lint_type_theory_docs` on the source theory."]
  String.intercalate "\n" <|
    [ s!"Generated model-interface method \
      `{theoryName.eraseMacroScopes}.{structureName.eraseMacroScopes}.\
      {methodName.eraseMacroScopes}`.",
      s!"Source internal/LF declaration: {sourceName.eraseMacroScopes}.",
      s!"Dot notation: `M.{methodName.eraseMacroScopes}` for `M : \
        {theoryName.eraseMacroScopes}.{structureName.eraseMacroScopes}`.",
      s!"Backend: {backend}.",
      s!"Generated role: {roleText}.",
      "The generated Lean declaration is backed by checked object-theory/LF artifacts for this \
        backend." ] ++ sourceDocLines

/-- Report missing source docstrings for public theory declarations and internal declarations. -/
elab "#lint_type_theory_docs" theory:ident : command => do
  liftCoreM <| requireTheoryAnchor theory.getId
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let (ok, text) ← liftCoreM <| lintInternalLeanDocsString sig
  if ok then logInfo m!"{text}" else logWarning m!"{text}"

/-- Report internal declarations admitted by `sorry` for a type theory. -/
elab "#lint_type_theory_sorries" theory:ident : command => do
  liftCoreM <| requireTheoryAnchor theory.getId
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theory.getId
  if admissions.isEmpty then
    logInfo m!"type theory '{theory.getId}' has no admitted internal declarations"
  else
    let some sig ← liftCoreM <| getTheory? theory.getId
      | throwError "unknown type theory '{theory.getId}'"
    let docs ← liftCoreM <| getSourceDocsFor theory.getId
    let lines := admissions.map fun a =>
      let hasDoc := docs.any fun d => d.role == .internalDef
        && d.sourceName.eraseMacroScopes == a.declName.eraseMacroScopes
      let docText := if hasDoc then " [documented]" else " [missing doc]"
      let binderText :=
        if a.params.isEmpty then ""
        else " " ++ String.intercalate " " (a.params.toList.map HLBinding.summary)
      s!"admitted internal def {a.anchorName.eraseMacroScopes}{binderText} : {a.typeExpr}{docText}"
    let deps := internalAdmissionDependencyLines sig admissions
    let transports ← liftCoreM <| getInternalAdmissionTransportsFor theory.getId
    let transportLines := transports.map fun t =>
      s!"transported declaration {t.generatedName.eraseMacroScopes} for admitted \
        {t.declName.eraseMacroScopes} over model {t.structureName.eraseMacroScopes} intentionally \
          uses Lean `sorry`/`sorryAx`"
    let allLines := lines ++
      (if deps.isEmpty then #[] else #["downstream declarations mentioning admissions:"] ++ deps) ++
      (if transportLines.isEmpty then #[] else
        #["generated transported declarations with Lean `sorryAx` dependency:"] ++ transportLines)
    logWarning m!"type theory '{theory.getId}' has {admissions.size} admitted internal \
      declaration(s):\n{String.intercalate "\n" allLines.toList}"

/-- Expand one object expression using the currently registered macros for a theory. -/
elab "#expand_object" theory:ident e:ttExpr : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let e ← elabObjExpr e
  let expanded ← liftCoreM <| expandObjectMacrosInExpr flatSig e
  logInfo m!"{expanded}"

/-- Print the names of registered type theories. -/
elab "#print_type_theories" : command => do
  let theories ← liftCoreM getTheories
  let names := theories.toList.map Prod.fst
  logInfo m!"{names}"

/-- Format checked-artifact counts for diagnostics. -/
def CheckedSignature.summary (checked : CheckedSignature) : MessageData :=
  let levels :=
    if checked.levelParams.isEmpty then
      m!"no opt-in LF universe level parameter(s)"
    else
      m!"{checked.levelParams.size} opt-in LF universe level parameter(s)"
  let roleCount :=
    checked.lfSyntaxSortRoles.size + checked.lfJudgmentRoles.size + checked.lfRuleRoles.size
  let rewriteMetadataCount := checked.lfRewriteRelations.size +
    checked.lfRewriteSymmetries.size + checked.lfRewriteCongruences.size +
    checked.lfTransportRules.size + checked.lfTransportPositions.size
  m!"{levels}, {checked.lfSyntaxSorts.size} checked LF syntax sorts, \
    {checked.lfSyntaxAbbrevs.size} checked syntax abbreviation(s), {roleCount} role(s), \
    {rewriteMetadataCount} rewrite/transport metadata item(s), \
    {checked.lfContextZones.size} checked LF context zones, \
    {checked.lfBinderClasses.size} checked LF binder classes, \
    {checked.lfJudgments.size} checked LF judgments, \
    {checked.lfSideConditionSolvers.size} checked LF side-condition solvers, \
    {checked.lfConversionPlugins.size} checked LF conversion plugins, \
    {checked.lfRules.size} checked LF rules, {checked.lfRuleSchemas.size} LF rule schema(s), \
    {checked.lfSideConditionCertificates.size} LF side-condition certificate(s), \
    {checked.lfObjectDefs.size} LF object definition(s), \
    {checked.lfJudgmentTheorems.size} LF judgment theorem(s)"

/-- Check one registered type theory with the direct-LF checker and persist the checked artifact. -/
elab "#check_type_theory " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  let checked ← liftCoreM <| checkSignatureForRegistration sig
  liftCoreM <| registerCheckedTheory checked
  logInfo m!"type theory {checked.name} checks with the direct-LF checker ({checked.summary})"

/-- Print summary information for one registered checked theory artifact. -/
elab "#print_checked_type_theory " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"checked type theory {checked.name}: {checked.summary}"
  for s in checked.lfSyntaxSorts do
    logInfo m!"LF syntax_sort {s.name}: {s.arity} parameter(s)"
  for a in checked.lfSyntaxAbbrevs do
    logInfo m!"LF syntax_abbrev {a.name}: {a.params.size} parameter(s), expands to {a.value}"
  for role in checked.lfSyntaxSortRoles do
    logInfo m!"LF syntax_sort_role {role.sortName} : {role.kind}"
  for j in checked.lfJudgments do
    logInfo m!"LF judgment {j.name}: {j.arity} parameter(s)"
  for role in checked.lfJudgmentRoles do
    logInfo m!"LF judgment_role {role.judgmentName} : {role.kind}"
  for s in checked.lfSideConditionSolvers do
    logInfo m!"LF side_condition_solver {s.name} [{s.hookKind.label}]"
  for p in checked.lfConversionPlugins do
    let supported := if p.supportedSteps.isEmpty then "metadata_only" else
      String.intercalate ", " (p.supportedSteps.toList.map ConversionStepKind.label)
    logInfo m!"LF conversion_plugin {p.name} [{p.trust.label}; {supported}]"
  for r in checked.lfRules do
    logInfo m!"LF rule {r.name}: {r.premises.size} premise(s), \
      {r.sideConditions.size} side-condition(s)"
  for role in checked.lfRuleRoles do
    logInfo m!"LF rule_role {role.ruleName} : {role.kind}"
  for rel in checked.lfRewriteRelations do
    logInfo rel.summary
  for tr in checked.lfTransportRules do
    logInfo tr.summary
  for pos in checked.lfTransportPositions do
    logInfo pos.summary
  for r in checked.lfRuleSchemas do
    logInfo m!"LF rule schema {r.name}: {r.metavariables.size} metavariable(s), \
      {r.premises.size} premise schema(s), {r.sideConditionSlots.size} side-condition slot(s)"
  for c in checked.lfSideConditionCertificates do
    logInfo m!"LF side-condition certificate {c.certificateName}: {c.name} by {c.solver} \
      [{c.kind.label}]"
  for d in checked.lfObjectDefs do
    logInfo m!"LF object definition {d.name}: {d.typeExpr} := {d.value}"
  for t in checked.lfJudgmentTheorems do
    logInfo m!"LF judgment theorem {t.name}: {t.judgmentExpr} := {t.proof}"

/-- Render a checked LF head for diagnostics. -/
def CheckedLFHead.summary (h : CheckedLFHead) : MessageData :=
  let arity := match h.arity? with | some n => m!" / {n}" | none => m!""
  m!"{h.name} [{h.kind.label}] ({h.actualArity} arg(s){arity})"

/-- Diagnostic rendering of a recursively resolved LF expression. -/
partial def CheckedLFExpr.summary : CheckedLFExpr → MessageData
  | .ident h => h.summary
  | .sort => m!"Type"
  | .univ u => m!"Type {u}"
  | .app f a => m!"({CheckedLFExpr.summary f} {CheckedLFExpr.summary a})"
  | .arrow none A B => m!"({CheckedLFExpr.summary A} ⇒ {CheckedLFExpr.summary B})"
  | .arrow (some x) A B => m!"(({x} : {CheckedLFExpr.summary A}) ⇒ {CheckedLFExpr.summary B})"
  | .lam xs body => m!"(fun {xs} => {CheckedLFExpr.summary body})"
  | .jeq lhs rhs => m!"({CheckedLFExpr.summary lhs} ≡ {CheckedLFExpr.summary rhs})"

/-- Increment a `NameMap Nat` counter. -/
def incrementNameCount (m : NameMap Nat) (n : Name) : NameMap Nat :=
  m.insert n ((m.find? n).getD 0 + 1)

/-- Collect resolved LF head occurrences from a checked LF expression. -/
partial def CheckedLFExpr.collectHeads (counts : NameMap Nat) : CheckedLFExpr → NameMap Nat
  | .ident h =>
      if h.kind == .local then counts else incrementNameCount counts h.name
  | .sort | .univ _ => counts
  | .app f a => CheckedLFExpr.collectHeads (CheckedLFExpr.collectHeads counts f) a
  | .arrow _ A B => CheckedLFExpr.collectHeads (CheckedLFExpr.collectHeads counts A) B
  | .lam _ body => CheckedLFExpr.collectHeads counts body
  | .jeq lhs rhs => CheckedLFExpr.collectHeads (CheckedLFExpr.collectHeads counts lhs) rhs

/-- Collect resolved LF head occurrences from one checked LF rule. -/
def CheckedLFRule.collectHeads (counts : NameMap Nat) (r : CheckedLFRule) : NameMap Nat := Id.run do
  let mut counts := counts
  for b in r.params do
    counts := b.checkedTypeExpr.collectHeads counts
  for p in r.premises do
    counts := p.checkedJudgmentExpr.collectHeads counts
  for sc in r.sideConditions do
    counts := sc.checkedInput.collectHeads counts
  counts := r.checkedConclusionExpr.collectHeads counts
  return counts

/-- Print checked Phase-1 LF declaration artifacts stored for a theory. -/
elab "#print_checked_logical_framework_metadata " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"checked LF metadata for {checked.name} ({checked.lfSyntaxSorts.size} syntax sort(s), \
    {checked.lfSyntaxAbbrevs.size} syntax abbreviation(s), {checked.lfContextZones.size} context \
      zone(s), {checked.lfBinderClasses.size} binder class(es), {checked.lfJudgments.size} \
        judgment(s), {checked.lfOpaqueConsts.size} opaque placeholder(s), \
          {checked.lfSideConditionSolvers.size} side-condition solver(s), \
            {checked.lfConversionPlugins.size} conversion plugin(s), {checked.lfRules.size} \
              rule(s), {checked.lfObjectDefs.size} LF object definition(s), \
                {checked.lfJudgmentTheorems.size} LF judgment theorem(s))"
  for s in checked.lfSyntaxSorts do
    logInfo m!"syntax_sort {s.name} / {s.arity}"
  for a in checked.lfSyntaxAbbrevs do
    let params := String.intercalate " " (a.params.toList.map fun b =>
      s!"({b.name} : {b.typeExpr})")
    let head := match a.head? with | some h => m!" headed by {h.summary}" | none => m!""
    logInfo m!"syntax_abbrev {a.name} {params} := {a.value}{head}"
  for z in checked.lfContextZones do
    let deps := if z.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (z.dependsOn.toList.map toString)
    logInfo m!"context_zone {z.name} : {z.sortName}{deps}"
  for b in checked.lfBinderClasses do
    let deps := if b.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (b.dependsOn.toList.map toString)
    logInfo m!"binder_class {b.name} : {b.boundSortName} in {b.zoneName}{deps}"
  for role in checked.lfSyntaxSortRoles do
    logInfo m!"syntax_sort_role {role.sortName} : {role.kind}"
  for j in checked.lfJudgments do
    logInfo m!"judgment {j.name} / {j.arity}"
  for role in checked.lfJudgmentRoles do
    logInfo m!"judgment_role {role.judgmentName} : {role.kind}"
  for o in checked.lfOpaqueConsts do
    match o.typeExpr? with
    | some typeExpr =>
        let params := String.intercalate " " (o.params.toList.map fun b =>
          s!"({b.name} : {b.typeExpr})")
        let head := match o.typeHead? with | some h => m!" headed by {h.summary}" | none => m!""
        logInfo m!"lf_opaque {o.name} {params} : {typeExpr}{head}"
    | none =>
        let arity := match o.arity? with | some n => m!" / {n}" | none => m!""
        logInfo m!"lf_opaque {o.name}{arity}"
  for s in checked.lfSideConditionSolvers do
    logInfo m!"side_condition_solver {s.name} [{s.hookKind.label}]"
  for p in checked.lfConversionPlugins do
    let supported := if p.supportedSteps.isEmpty then "metadata_only" else
      String.intercalate ", " (p.supportedSteps.toList.map ConversionStepKind.label)
    logInfo m!"conversion_plugin {p.name} [{p.trust.label}; {supported}]"
  for role in checked.lfRuleRoles do
    logInfo m!"rule_role {role.ruleName} : {role.kind}"
  for rel in checked.lfRewriteRelations do
    logInfo rel.summary
  for tr in checked.lfTransportRules do
    logInfo tr.summary
  for pos in checked.lfTransportPositions do
    logInfo pos.summary
  for d in checked.lfObjectDefs do
    logInfo m!"lf_def {d.name}: {d.typeExpr} := {d.value}"
  for t in checked.lfJudgmentTheorems do
    logInfo m!"judgment_theorem {t.name}: {t.judgmentExpr} := {t.proof}"

/-- Print the Phase-2 checked LF environment summary for a theory. -/
elab "#print_checked_logical_framework_environment " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  let env := checked.lfEnvironment
  let levels := if env.levelParams.isEmpty then "none" else
    String.intercalate ", " (env.levelParams.toList.map toString)
  logInfo m!"checked LF environment for {env.theoryName}: level parameter(s): {levels}; \
    {env.syntaxSorts.size} syntax sort(s), {env.syntaxAbbrevs.size} syntax abbreviation(s), \
      {env.contextZones.size} context zone(s), {env.binderClasses.size} binder class(es), \
        {env.judgments.size} judgment(s), {env.opaqueConsts.size} opaque placeholder(s), \
          {env.sideConditionSolvers.size} side-condition solver(s), {env.conversionPlugins.size} \
            conversion plugin(s), {env.rules.size} checked rule(s), {env.ruleSchemas.size} \
              rule schema(s), {env.sideConditionCertificates.size} side-condition \
                certificate(s), {checked.lfKernelRuleSchemas.size} kernel rule-schema staging \
                  artifact(s)"
  for z in env.contextZones do
    let deps := if z.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (z.dependsOn.toList.map toString)
    logInfo m!"context-zone {z.name}: sort {z.sortName}{deps}"
  for b in env.binderClasses do
    let deps := if b.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (b.dependsOn.toList.map toString)
    logInfo m!"binder-class {b.name}: sort {b.boundSortName} in zone {b.zoneName}{deps}"
  for r in env.ruleSchemas do
    logInfo m!"rule-schema {r.name}: {r.metavariables.size} metavariable(s), \
      {r.multiContext.locals.size} zoned local(s), {r.premises.size} premise slot(s), \
        {r.sideConditionSlots.size} certificate slot(s)"

/-- Print checked Phase-1 LF rule artifacts stored for a theory. -/
elab "#print_checked_logical_framework_rules " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"checked LF rules for {checked.name} ({checked.lfRules.size} rule(s))"
  for r in checked.lfRules do
    logInfo m!"rule {r.name}: conclusion head {r.conclusionHead.summary}"
    for b in r.params do
      let head := match b.head? with | some h => m!" headed by {h.summary}" | none => m!""
      logInfo m!"  parameter {b.name} : {b.typeExpr}{head}"
      logInfo m!"    resolved type: {b.checkedTypeExpr.summary}"
    let evidencePremiseNames : NameSet := r.paramEvidences.foldl (init := {}) fun acc ev =>
      acc.insert ev.name
    for ev in r.paramEvidences do
      logInfo m!"  evidence {ev.name} for {ev.paramName}: {ev.judgmentExpr} headed by \
        {ev.head.summary}"
      logInfo m!"    resolved evidence: {ev.checkedJudgmentExpr.summary}"
    for p in r.premises do
      if !evidencePremiseNames.contains p.name then
        logInfo m!"  premise {p.name}: {p.judgmentExpr} headed by {p.head.summary}"
        logInfo m!"    resolved premise: {p.checkedJudgmentExpr.summary}"
    for sc in r.sideConditions do
      let head := match sc.head? with | some h => m!" headed by {h.summary}" | none => m!""
      logInfo m!"  side_condition {sc.name} by {sc.solver}: {sc.input}{head}"
      logInfo m!"    resolved side-condition: {sc.checkedInput.summary}"
    logInfo m!"  resolved conclusion: {r.checkedConclusionExpr.summary}"

/-- Print Phase-2 LF rule schemas derived from checked metadata. -/
elab "#print_logical_framework_rule_schemas " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"LF rule schemas for {checked.name} ({checked.lfRuleSchemas.size} rule(s))"
  for r in checked.lfRuleSchemas do
    logInfo m!"rule-schema {r.name}: conclusion {r.conclusionHead.summary}"
    for v in r.metavariables do
      let sort :=
        match v.sortHead? with
        | some h => m!" sort {h.summary}"
        | none => m!" non-sort-shaped"
      let zone := match v.zoneName? with | some z => m!", zone {z}" | none => m!""
      let binder := match v.binderClass? with | some b => m!", binder_class {b}" | none => m!""
      logInfo m!"  metavariable {v.name} : {v.typeExpr}{sort}{zone}{binder}"
      logInfo m!"    resolved type: {v.checkedTypeExpr.summary}"
    for z in r.multiContext.locals do
      let binder := match z.binderClass? with | some b => m!" by {b}" | none => m!""
      logInfo m!"  zone-local {z.name} in {z.zoneName}{binder}: {z.typeExpr}"
    let evidencePremiseNames : NameSet := r.metavariables.foldl (init := {}) fun acc v =>
      match v.evidence? with
      | some ev => acc.insert ev.name
      | none => acc
    for p in r.premises do
      if evidencePremiseNames.contains p.name then
        logInfo m!"  evidence-slot {p.name}: {p.judgmentHead.summary}"
        logInfo m!"    resolved evidence: {p.checkedJudgmentExpr.summary}"
      else
        logInfo m!"  premise-slot {p.name}: {p.judgmentHead.summary}"
        logInfo m!"    resolved premise: {p.checkedJudgmentExpr.summary}"
    for sc in r.sideConditionSlots do
      let head :=
        match sc.inputHead? with
        | some h => m!" input {h.summary}"
        | none => m!" input without resolved head"
      logInfo m!"  certificate-slot {sc.name}: solver {sc.solver},{head}"
      logInfo m!"    resolved input: {sc.checkedInput.summary}"
      if let some cert := sc.certificate? then
        logInfo m!"    checked certificate: {cert.certificateName} [{cert.kind.label}] \
          {cert.diagnostic}"
    logInfo m!"  resolved conclusion: {r.checkedConclusionExpr.summary}"

/-- Print Phase-4 LF context-zone and binder-class staging artifacts. -/
elab "#print_logical_framework_context_zones " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  let env := checked.lfEnvironment
  logInfo m!"LF context zones for {checked.name} ({env.contextZones.size} zone(s), \
    {env.binderClasses.size} binder class(es))"
  for z in env.contextZones do
    let deps := if z.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (z.dependsOn.toList.map toString)
    logInfo m!"zone {z.name}: sort {z.sortName}{deps}"
  for b in env.binderClasses do
    let deps := if b.dependsOn.isEmpty then "" else " depends_on "
      ++ String.intercalate ", " (b.dependsOn.toList.map toString)
    logInfo m!"binder_class {b.name}: {b.boundSortName} in {b.zoneName}{deps}"
  for r in env.ruleSchemas do
    if !r.multiContext.locals.isEmpty then
      logInfo m!"rule-schema {r.name}: {r.multiContext.locals.size} zone-local(s)"
      for zoneLocal in r.multiContext.locals do
        let binder := match zoneLocal.binderClass? with | some cls => m!" by {cls}" | none => m!""
        logInfo m!"  {zoneLocal.name} in {zoneLocal.zoneName}{binder}: {zoneLocal.typeExpr}"

/-- One-line diagnostic rendering for the head of a checked LF derivation. -/
partial def lfDerivationHeadSummary : CheckedLFDerivation → MessageData
  | .localAssumption name stmt => m!"local_assumption {name} : {stmt}"
  | .theoremRef name stmt args premises =>
      let argText := if args.isEmpty then m!"" else m!" args={args.size}"
      let premiseText := if premises.isEmpty then m!"" else m!" premises={premises.size}"
      m!"theorem_ref {name} : {stmt}{argText}{premiseText}"
  | .ruleApp ruleName stmt args premises certs =>
      let argText := String.intercalate ", " (args.toList.map (fun e => toString e))
      m!"rule_app {ruleName} : {stmt} args [{argText}] with {premises.size} premise proof(s) and \
        {certs.size} certificate(s)"

/-- Compact diagnostic rendering for shallow checked LF derivations. -/
partial def lfDerivationSummary : CheckedLFDerivation → MessageData
  | .localAssumption name stmt => m!"local_assumption {name} : {stmt}"
  | .theoremRef name stmt args premises =>
      let argText := if args.isEmpty then m!"" else m!" args={args.size}"
      let premiseText := if premises.isEmpty then m!"" else m!" premises={premises.size}"
      m!"theorem_ref {name} : {stmt}{argText}{premiseText}"
  | .ruleApp ruleName stmt args premises certs =>
      let argText := String.intercalate ", " (args.toList.map (fun e => toString e))
      let certText := String.intercalate ", " (certs.toList.map toString)
      let premiseText := MessageData.joinSep (premises.toList.map lfDerivationSummary) m!"; "
      m!"rule_app {ruleName} : {stmt} args [{argText}] premises [{premiseText}] certificates \
        [{certText}]"

/-- Compact diagnostic rendering for kernel-facing LF derivation replay artifacts. -/
partial def kernelLFDerivationSummary : KernelLFDerivation → MessageData
  | .assumption name stmt => m!"local_assumption {name} : {reprStr stmt}"
  | .theoremRef name stmt => m!"theorem_ref {name} : {reprStr stmt}"
  | .certificate name stmt cert => m!"certificate {name} : {reprStr stmt} certificate {cert}"
  | .ruleApp ruleName concl inst premises certs =>
      let instText := String.intercalate ", " <| inst.entries.map (fun e =>
        let zone := match e.zone? with | some z => s!" in {z}" | none => ""
        let evidenceText :=
          match e.evidence? with
          | some ev => s!" evidence {reprStr ev}"
          | none => ""
        s!"{e.name}{zone} := {reprStr e.value} : {reprStr e.type?}{evidenceText}")
      let certText := String.intercalate ", " (certs.map toString)
      let premiseText := MessageData.joinSep (premises.map kernelLFDerivationSummary) m!"; "
      m!"rule_app {ruleName} : {reprStr concl} inst [{instText}] premises [{premiseText}] \
        certificates [{certText}]"

/-- Check the compact LF replay certificate generated for a checked LF judgment theorem. -/
elab "#check_lf_replay_certificate " theory:ident theoremName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let cert ← kernelLFReplayCertificateForTheorem checked theoremName.getId
  match cert.toChecked with
  | .ok _checkedReplay =>
      let contextCount := cert.context.assumptions.length + cert.context.theorems.length +
        cert.context.certificates.length
      logInfo m!"compact LF replay certificate for {theory.getId}.{theoremName.getId} \
        checks: {cert.signature.rules.length} rule(s), {contextCount} \
        theorem/certificate context entry(ies), {cert.context.localParameters.length} \
        local parameter(s)"
  | .error err =>
      throwError "compact LF replay certificate for {theory.getId}.{theoremName.getId} failed \
        validation: {err}"

/-- Print the compact LF replay certificate generated for a checked LF judgment theorem. -/
elab "#print_lf_replay_certificate " theory:ident theoremName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let cert ← kernelLFReplayCertificateForTheorem checked theoremName.getId
  let audit := kernelLFReplayCertificateAuditString theory.getId theoremName.getId cert checked
  logInfo m!"{audit}"

/-- Print the raw `repr` compact LF replay certificate payload for debugging. -/
elab "#print_lf_replay_certificate_raw " theory:ident theoremName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let cert ← kernelLFReplayCertificateForTheorem checked theoremName.getId
  logInfo m!"raw compact LF replay certificate for {theory.getId}.{theoremName.getId}:\n\
    {reprStr cert}"

/-- Print trust dependencies used by one checked LF judgment theorem replay artifact. -/
elab "#print_lf_replay_trust_dependencies " theory:ident theoremName:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let cert ← kernelLFReplayCertificateForTheorem checked theoremName.getId
  let deps := kernelLFReplayDependencySummary cert.derivation
  let opaqueHeads := replayOpaqueHeadNames checked deps
  logInfo m!"LF replay trust dependencies for {theory.getId}.{theoremName.getId}\n\
    local assumptions: {nameSetSummary deps.localAssumptions}\n\
    theorem references: {nameSetSummary deps.theoremReferences}\n\
    certificate obligations: {nameSetSummary deps.certificateObligations}\n\
    external certificates: {nameSetSummary deps.externalCertificates}\n\
    rule applications: {nameSetSummary deps.ruleApplications}\n\
    opaque LF heads: {nameSetSummary opaqueHeads}\n\
    all global LF heads: {nameSetSummary deps.globalHeads}"

/-- Print aggregate trust dependencies for all checked LF judgment theorem replay artifacts. -/
elab "#print_lf_replay_trust_summary " theory:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? theory.getId
    | throwError "no checked artifact stored for type theory '{theory.getId}'"
  let mut deps : KernelLFReplayDependencySummary := {}
  let mut checkedCount := 0
  let mut missing : Array Name := #[]
  let mut failed : Array String := #[]
  for t in checked.lfJudgmentTheorems do
    match kernelLFReplayCertificateForCheckedTheorem checked t with
    | .error err =>
        missing := missing.push t.name
        failed := failed.push s!"{t.name}: {err}"
    | .ok cert =>
        match cert.toChecked with
        | .error err => failed := failed.push s!"{t.name}: {err}"
        | .ok _ =>
            checkedCount := checkedCount + 1
            deps := deps.merge (kernelLFReplayDependencySummary cert.derivation)
  let opaqueHeads := replayOpaqueHeadNames checked deps
  let missingText := if missing.isEmpty then "none" else nameSetSummary (missing.foldl
    (init := {}) fun names n => names.insert n.eraseMacroScopes)
  let failedText := if failed.isEmpty then "none" else String.intercalate "; " failed.toList
  logInfo m!"LF replay trust summary for {theory.getId}: {checkedCount}/\
    {checked.lfJudgmentTheorems.size} theorem replay artifact(s) checked\n\
    missing replay artifacts: {missingText}\n\
    validation failures: {failedText}\n\
    local assumptions: {nameSetSummary deps.localAssumptions}\n\
    theorem references: {nameSetSummary deps.theoremReferences}\n\
    certificate obligations: {nameSetSummary deps.certificateObligations}\n\
    external certificates: {nameSetSummary deps.externalCertificates}\n\
    rule applications: {nameSetSummary deps.ruleApplications}\n\
    opaque LF heads: {nameSetSummary opaqueHeads}\n\
    all global LF heads: {nameSetSummary deps.globalHeads}"

/-- Print staged sorted LF/object definitions and custom-judgment theorem artifacts. -/
elab "#print_logical_framework_definitions " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"LF internal definition layer for {checked.name} ({checked.lfObjectDefs.size} object \
    definition(s), {checked.lfJudgmentTheorems.size} judgment theorem(s))"
  for d in checked.lfObjectDefs do
    let typeHead := match d.typeHead? with
      | some h => m!" type {h.summary}"
      | none => m!" type without resolved head"
    let valueHead := match d.valueHead? with
      | some h => m!" value {h.summary}"
      | none => m!" value without resolved head"
    logInfo m!"lf_def {d.name}:{typeHead},{valueHead}"
    logInfo m!"  type: {truncateDiagnosticString 600 (toString d.typeExpr)}"
    logInfo m!"  resolved type: {replayAuditCheckedLFExprString d.checkedTypeExpr}"
    logInfo m!"  value: {truncateDiagnosticString 600 (toString d.value)}"
    logInfo m!"  resolved value: {replayAuditCheckedLFExprString d.checkedValue}"
  for t in checked.lfJudgmentTheorems do
    let proofHead := match t.proofHead? with
      | some h => m!" proof {h.summary}"
      | none => m!" proof without resolved head"
    let binderText := if t.binders.isEmpty then m!"" else m!", {t.binders.size} local binder(s)"
    logInfo m!"judgment_theorem {t.name}: statement {t.judgmentHead.summary},\
      {proofHead}{binderText}"
    logInfo m!"  statement: {truncateDiagnosticString 600 (toString t.judgmentExpr)}"
    logInfo m!"  resolved statement: {replayAuditCheckedLFExprString t.checkedJudgmentExpr}"
    logInfo m!"  proof: {truncateDiagnosticString 600 (toString t.proof)}"
    logInfo m!"  resolved proof: {replayAuditCheckedLFExprString t.checkedProof}"
    if let some ruleName := t.proofRule? then
      let args := t.proofRuleArgs.toList.map fun e =>
        truncateDiagnosticString 160 (toString e)
      let args := String.intercalate ", " args
      let certs := String.intercalate ", " (t.sideConditionCertificateNames.toList.map toString)
      let premiseProofs := match t.derivation? with
        | some (.ruleApp _ _ _ premises _) =>
            premises.toList.map (fun p =>
              truncateDiagnosticString 240 (checkedLFDerivationSourceStringWithDepth 2 p))
        | _ => t.premiseTheorems.toList.map toString
      let premiseProofs := String.intercalate ", " premiseProofs
      logInfo m!"  rule application: {ruleName} args [{args}] premise proofs \
        [{premiseProofs}] certificates [{certs}]"
    if let some derivation := t.derivation? then
      logInfo m!"  derivation: {replayAuditCheckedLFDerivationString derivation}"
    if let some derivation := t.kernelDerivation? then
      logInfo m!"  kernel replay: {replayAuditDerivationString derivation}"
      match t.checkedKernelDerivation? with
      | some checkedReplay =>
          match checkedReplay.check with
          | .ok () =>
              logInfo m!"  checked kernel replay wrapper: eligible"
          | .error err =>
              logInfo m!"  checked kernel replay wrapper: ineligible: {err}"
      | none =>
          logInfo m!"  checked kernel replay wrapper: unavailable"

/-- Print Phase-3 LF side-condition hook registry and produced certificates. -/
elab "#print_logical_framework_side_condition_hooks " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"LF side-condition hooks for {checked.name} ({checked.lfSideConditionSolvers.size} \
    solver(s), {checked.lfSideConditionCertificates.size} certificate(s))"
  for s in checked.lfSideConditionSolvers do
    logInfo m!"solver {s.name}: {s.hookKind.label}"
  for c in checked.lfSideConditionCertificates do
    let head :=
      match c.inputHead? with
      | some h => m!" headed by {h.summary}"
      | none => m!" without resolved head"
    logInfo m!"certificate {c.certificateName}: slot {c.name} by {c.solver} [{c.kind.label}]{head}"
    logInfo m!"  input: {c.input}"
    logInfo m!"  resolved input: {c.checkedInput.summary}"
    logInfo m!"  diagnostic: {c.diagnostic}"

/-- Print low-level kernel rule-schema staging artifacts derived from LF rule schemas. -/
elab "#print_logical_framework_kernel_rule_schemas " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"kernel LF rule-schema staging artifacts for {checked.name} \
    ({checked.lfKernelRuleSchemas.size} rule(s))"
  for r in checked.lfKernelRuleSchemas do
    let zoned := r.metavariables.countP (fun v => v.zone?.isSome)
    logInfo m!"kernel rule-schema {r.name}: {r.metavariables.length} metavariable(s), {zoned} \
      zoned metavariable(s), {r.premises.length} premise(s), {r.sideConditions.length} \
        side-condition(s), {r.sideConditionCertificates.length} certificate slot(s), \
          {r.checkedSideConditionCertificates.length} checked certificate(s)"

/-- Print aggregate resolved-head usage in checked LF rule artifacts. -/
elab "#print_checked_logical_framework_head_usage " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  let mut counts : NameMap Nat := {}
  for s in checked.lfSyntaxSorts do
    for b in s.params do
      counts := b.checkedTypeExpr.collectHeads counts
  for j in checked.lfJudgments do
    for b in j.params do
      counts := b.checkedTypeExpr.collectHeads counts
  for r in checked.lfRules do
    counts := r.collectHeads counts
  for d in checked.lfObjectDefs do
    counts := d.checkedTypeExpr.collectHeads counts
    counts := d.checkedValue.collectHeads counts
  for t in checked.lfJudgmentTheorems do
    counts := t.checkedJudgmentExpr.collectHeads counts
    counts := t.checkedProof.collectHeads counts
  logInfo m!"checked LF head usage for {checked.name} ({counts.toList.length} head(s))"
  for (name, count) in counts.toList do
    logInfo m!"{name}: {count} occurrence(s)"



/-- Elaborate generated command syntax inside the Lean namespace named by the object theory.

This is the syntax-based replacement for generated declarations: the declaration itself is
built as `Syntax`, not rendered to source and reparsed. -/
elab "#print_logical_framework_metadata " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  let sig ← liftCoreM <| flattenSignature sig
  let lfCount :=
    sig.syntaxSorts.size + sig.syntaxAbbrevs.size + sig.syntaxSortRoles.size +
      sig.contextZones.size +
    sig.binderClasses.size + sig.judgments.size + sig.judgmentRoles.size + sig.rules.size +
    sig.ruleRoles.size + sig.rewriteRelations.size + sig.rewriteSymmetries.size +
    sig.rewriteCongruences.size + sig.transportRules.size + sig.transportPositions.size +
    sig.sideConditionSolvers.size +
    sig.conversionPlugins.size + sig.lfOpaqueConsts.size + sig.modelVisibilities.size +
    sig.modelSections.size + sig.modelSectionMemberships.size + sig.lfObjectDefs.size +
    sig.lfJudgmentTheorems.size
  logInfo m!"logical-framework metadata for {nm.getId} ({lfCount} declarations, parents flattened)"
  for s in sig.syntaxSorts do
    logInfo s.summary
  for a in sig.syntaxAbbrevs do
    logInfo a.summary
  for role in sig.syntaxSortRoles do
    logInfo role.summary
  for zone in sig.contextZones do
    logInfo zone.summary
  for binderClass in sig.binderClasses do
    logInfo binderClass.summary
  for j in sig.judgments do
    logInfo j.summary
  for role in sig.judgmentRoles do
    logInfo role.summary
  for r in sig.rules do
    logInfo r.summary
  for role in sig.ruleRoles do
    logInfo role.summary
  for rel in sig.rewriteRelations do
    logInfo rel.summary
  for symm in sig.rewriteSymmetries do
    logInfo symm.summary
  for congr in sig.rewriteCongruences do
    logInfo congr.summary
  for tr in sig.transportRules do
    logInfo tr.summary
  for pos in sig.transportPositions do
    logInfo pos.summary
  for solver in sig.sideConditionSolvers do
    logInfo solver.summary
  for plugin in sig.conversionPlugins do
    logInfo plugin.summary
  for opaqueDecl in sig.lfOpaqueConsts do
    logInfo opaqueDecl.summary
  for v in sig.modelVisibilities do
    logInfo v.summary
  for s in sig.modelSections do
    logInfo s.summary
  for m in sig.modelSectionMemberships do
    logInfo m.summary
  for d in sig.lfObjectDefs do
    logInfo d.summary
  for t in sig.lfJudgmentTheorems do
    logInfo t.summary

/-- Print only role metadata available to a type theory, after flattening parents. -/
elab "#print_logical_framework_roles " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  let sig ← liftCoreM <| flattenSignature sig
  let roleCount := sig.syntaxSortRoles.size + sig.judgmentRoles.size + sig.ruleRoles.size
  logInfo m!"logical-framework roles for {nm.getId} ({roleCount} declarations, parents flattened)"
  for role in sig.syntaxSortRoles do
    logInfo role.summary
  for role in sig.judgmentRoles do
    logInfo role.summary
  for role in sig.ruleRoles do
    logInfo role.summary

/-- Print checked rewrite/transport metadata available to a type theory. -/
elab "#print_lf_rewrite_metadata " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  logInfo m!"LF rewrite/transport metadata for {checked.name}"
  if checked.lfRewriteRelations.isEmpty then
    logInfo m!"  rewrite relations: none"
  else
    logInfo m!"  rewrite relations: {checked.lfRewriteRelations.size} declaration(s)"
    for rel in checked.lfRewriteRelations do
      logInfo m!"  {rel.summary}"
  if checked.lfRewriteSymmetries.isEmpty then
    logInfo m!"  rewrite symmetries: none"
  else
    logInfo m!"  rewrite symmetries: {checked.lfRewriteSymmetries.size} declaration(s)"
    for symm in checked.lfRewriteSymmetries do
      logInfo m!"  {symm.summary}"
  if checked.lfRewriteCongruences.isEmpty then
    logInfo m!"  rewrite congruences: none"
  else
    logInfo m!"  rewrite congruences: {checked.lfRewriteCongruences.size} declaration(s)"
    for congr in checked.lfRewriteCongruences do
      logInfo m!"  {congr.summary}"
  if checked.lfTransportRules.isEmpty then
    logInfo m!"  transport rules: none"
  else
    logInfo m!"  transport rules: {checked.lfTransportRules.size} declaration(s)"
    for tr in checked.lfTransportRules do
      logInfo m!"  {tr.summary}"
  if checked.lfTransportPositions.isEmpty then
    logInfo m!"  transport positions: none"
  else
    logInfo m!"  transport positions: {checked.lfTransportPositions.size} declaration(s)"
    for pos in checked.lfTransportPositions do
      logInfo m!"  {pos.summary}"

/-- Format a list of declaration names for role-automation diagnostics. -/
def roleAutomationNameList (names : Array Name) : String :=
  if names.isEmpty then "(none)" else String.intercalate ", " (names.toList.map toString)

/-- Render a role-automation diagnostic. -/
def LFRoleAutomationDiagnostic.summary (d : LFRoleAutomationDiagnostic) : MessageData :=
  let target := match d.declaration? with | some n => m!" {n}" | none => m!""
  m!"[{d.kind.label}]{target}: {d.message}"

/-- Print role-classifier output intended for future tactic search and LF rewriting. -/
elab "#print_lf_role_automation " nm:ident : command => do
  let some checked ← liftCoreM <| getCheckedTheory? nm.getId
    | throwError "no checked artifact stored for type theory '{nm.getId}'"
  let profile := checked.roleAutomationProfile
  logInfo m!"LF role automation profile for {checked.name}"
  logInfo m!"  formation rules: {roleAutomationNameList profile.formationRules}"
  logInfo m!"  introduction rules: {roleAutomationNameList profile.introductionRules}"
  logInfo m!"  elimination rules: {roleAutomationNameList profile.eliminationRules}"
  logInfo m!"  computation rules: {roleAutomationNameList profile.computationRules}"
  logInfo m!"  structural rules: {roleAutomationNameList profile.structuralRules}"
  logInfo m!"  type conversion judgments: \
    {roleAutomationNameList profile.typeConversionJudgments}"
  logInfo m!"  term conversion judgments: \
    {roleAutomationNameList profile.termConversionJudgments}"
  logInfo m!"  direct-LF rewrite candidate rules: \
    {roleAutomationNameList profile.rewriteCandidateRules}"
  logInfo m!"  evidence rewrite relations: \
    {roleAutomationNameList profile.evidenceRewriteRelations}"
  logInfo m!"  evidence rewrite symmetries: \
    {roleAutomationNameList profile.evidenceRewriteSymmetries}"
  logInfo m!"  evidence rewrite congruences: \
    {roleAutomationNameList profile.evidenceRewriteCongruences}"
  logInfo m!"  evidence transport rules: \
    {roleAutomationNameList profile.evidenceTransportRules}"
  logInfo m!"  evidence transport positions: \
    {roleAutomationNameList profile.evidenceTransportPositions}"
  if profile.diagnostics.isEmpty then
    logInfo m!"  diagnostics: none"
  else
    logInfo m!"  diagnostics: {profile.diagnostics.size} issue(s)"
    for d in profile.diagnostics do
      logInfo m!"  {d.summary}"

/-- Check that a type theory has its generated Lean-visible anchor. -/
elab "#check_type_theory_anchor " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  liftCoreM <| requireTheoryAnchor sig.name
  logInfo m!"type theory '{sig.name}' has Lean-visible anchor '{theoryAnchorName sig.name}'"

/-- Print the generated Lean-visible theory anchor declaration and doc summary. -/
elab "#print_type_theory_anchor " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  liftCoreM <| requireTheoryAnchor sig.name
  let anchorName := theoryAnchorName sig.name
  logInfo m!"{anchorName} : InternalLean.TheoryAnchor"
  match ← findDocString? (← getEnv) anchorName with
  | some doc => logInfo m!"{doc}"
  | none => logInfo m!"no docstring found for '{anchorName}'"

/-- Print one registered type theory's high-level declarations. -/
elab "#print_type_theory " nm:ident : command => do
  let some sig ← liftCoreM <| getTheory? nm.getId
    | throwError "unknown type theory '{nm.getId}'"
  let levelText :=
    if sig.levelParams.isEmpty then ""
    else " {" ++ String.intercalate ", " (sig.levelParams.toList.map toString) ++ "}"
  let parentText :=
    if sig.parents.isEmpty then ""
    else s!" extends {String.intercalate ", " (sig.parents.toList.map toString)}"
  let lfCount :=
    sig.syntaxSorts.size + sig.syntaxAbbrevs.size + sig.syntaxSortRoles.size +
      sig.contextZones.size +
    sig.binderClasses.size + sig.judgments.size + sig.judgmentRoles.size + sig.rules.size +
    sig.ruleRoles.size + sig.rewriteRelations.size + sig.rewriteSymmetries.size +
    sig.rewriteCongruences.size + sig.transportRules.size + sig.transportPositions.size +
    sig.sideConditionSolvers.size +
    sig.conversionPlugins.size + sig.lfOpaqueConsts.size + sig.modelVisibilities.size +
    sig.modelSections.size + sig.modelSectionMemberships.size + sig.lfObjectDefs.size +
    sig.lfJudgmentTheorems.size
  logInfo m!"type theory {sig.name}{levelText}{parentText} with {lfCount} \
    logical-framework declarations"
  for s in sig.syntaxSorts do
    logInfo s.summary
  for a in sig.syntaxAbbrevs do
    logInfo a.summary
  for role in sig.syntaxSortRoles do
    logInfo role.summary
  for zone in sig.contextZones do
    logInfo zone.summary
  for binderClass in sig.binderClasses do
    logInfo binderClass.summary
  for j in sig.judgments do
    logInfo j.summary
  for role in sig.judgmentRoles do
    logInfo role.summary
  for r in sig.rules do
    logInfo r.summary
  for role in sig.ruleRoles do
    logInfo role.summary
  for rel in sig.rewriteRelations do
    logInfo rel.summary
  for symm in sig.rewriteSymmetries do
    logInfo symm.summary
  for congr in sig.rewriteCongruences do
    logInfo congr.summary
  for tr in sig.transportRules do
    logInfo tr.summary
  for pos in sig.transportPositions do
    logInfo pos.summary
  for solver in sig.sideConditionSolvers do
    logInfo solver.summary
  for plugin in sig.conversionPlugins do
    logInfo plugin.summary
  for opaqueDecl in sig.lfOpaqueConsts do
    logInfo opaqueDecl.summary
  for v in sig.modelVisibilities do
    logInfo v.summary
  for s in sig.modelSections do
    logInfo s.summary
  for m in sig.modelSectionMemberships do
    logInfo m.summary
  for d in sig.lfObjectDefs do
    logInfo d.summary
  for t in sig.lfJudgmentTheorems do
    logInfo t.summary


end InternalLean
