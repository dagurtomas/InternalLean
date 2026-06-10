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

/-- Syntax category for parse-only object-notation pattern entries. -/
declare_syntax_cat objectNotationPart
syntax str : objectNotationPart
syntax ident : objectNotationPart
syntax (name := objectNotationDeclStx)
  "object_notation" ident objectNotationPart+ " => " ttExpr : command

/-- Parse one `object_notation` pattern token. -/
meta def elabObjectNotationPart : TSyntax `objectNotationPart → CommandElabM ObjectNotationPart
  | `(objectNotationPart| $s:str) => pure (.atom s.getString)
  | `(objectNotationPart| $x:ident) => pure (.hole x.getId)
  | stx => throwError "unsupported object_notation pattern part:{indentD stx}"

/-- String key used to detect duplicate concrete object-notation patterns. -/
meta def objectNotationPatternKey (parts : Array ObjectNotationPart) : String :=
  String.intercalate "\u0001" <| parts.toList.map fun
    | .atom text => "atom:" ++ text
    | .hole _ => "hole"

/-- Render a string as a Lean string literal in a generated `syntax` command. -/
meta def leanStringLiteralSyntax (s : String) : String :=
  toString (repr s)

/-- Generated parser command for one object notation. -/
meta def objectNotationSyntaxCommand (syntaxName : Name) (parts : Array ObjectNotationPart) :
    String :=
  let items := parts.toList.map fun
    | .atom text => leanStringLiteralSyntax text
    | .hole _ => "ttExpr"
  s!"syntax (name := {syntaxName}) {String.intercalate " " items} : ttExpr"

/-- Free object-expression identifiers, respecting object binders. -/
meta partial def freeObjectNotationTemplateIdentifiers (locals : NameSet) : ObjExpr → NameSet
  | .ident n =>
      let n := n.eraseMacroScopes
      if locals.contains n then {} else ({} : NameSet).insert n
  | .sort | .univ _ => {}
  | .app f a =>
      freeObjectNotationTemplateIdentifiers locals f ++
        freeObjectNotationTemplateIdentifiers locals a
  | .arrow x A B | .funArrow x A B | .sigma x A B =>
      let free := freeObjectNotationTemplateIdentifiers locals A
      let locals := match x with | some x => locals.insert x.eraseMacroScopes | none => locals
      free ++ freeObjectNotationTemplateIdentifiers locals B
  | .pair a b =>
      freeObjectNotationTemplateIdentifiers locals a ++
        freeObjectNotationTemplateIdentifiers locals b
  | .fst e | .snd e => freeObjectNotationTemplateIdentifiers locals e
  | .lam xs body =>
      let locals := xs.foldl (fun locals x => locals.insert x.eraseMacroScopes) locals
      freeObjectNotationTemplateIdentifiers locals body
  | .jeq lhs rhs =>
      freeObjectNotationTemplateIdentifiers locals lhs ++
        freeObjectNotationTemplateIdentifiers locals rhs

/-- Register parse-only object notation for later object expressions. -/
elab_rules : command
  | `(command| object_notation $theory:ident $parts:objectNotationPart* =>
      $templateStx:ttExpr) => do
      let some _sig ← liftCoreM <| getTheory? theory.getId
        | throwError "unknown type theory '{theory.getId}'"
      let parts ← parts.mapM elabObjectNotationPart
      if parts.isEmpty then
        throwError "object_notation for type theory '{theory.getId}' must have a nonempty pattern"
      match parts[0]! with
      | .atom _ => pure ()
      | .hole _ =>
          throwError "object_notation for type theory '{theory.getId}' must start with a literal \
            token; notation patterns beginning with an expression hole need precedence support"
      let mut holeNames : Array Name := #[]
      let mut seenHoles : NameSet := {}
      for part in parts do
        match part with
        | .atom text =>
            if text == "⇒" then
              throwError "object_notation for type theory '{theory.getId}' uses reserved token \
                '⇒'; this token is the built-in LF dependent arrow, so use a different notation \
                token such as '⟶' or '⇛'"
        | .hole name =>
            let name := name.eraseMacroScopes
            if seenHoles.contains name then
              throwError "object_notation for type theory '{theory.getId}' has duplicate hole \
                '{name}'"
            seenHoles := seenHoles.insert name
            holeNames := holeNames.push name
      let patternKey := objectNotationPatternKey parts
      for old in getObjectNotationDecls (← getEnv) do
        if objectNotationPatternKey old.parts == patternKey then
          throwError "object_notation pattern {old.patternString} is already registered for type \
            theory '{old.theoryName}'"
      let template ← elabObjExpr templateStx
      let free := freeObjectNotationTemplateIdentifiers {} template
      for holeName in holeNames do
        unless free.contains holeName do
          throwError "object_notation for type theory '{theory.getId}' declares hole \
            '{holeName}', but the expansion template does not use it"
      let syntaxName := Name.str `InternalLean.ObjectNotation
        s!"n{(getObjectNotationDecls (← getEnv)).size + 1}"
      let syntaxCommand := objectNotationSyntaxCommand syntaxName parts
      let commandStx ←
        match Lean.Parser.runParserCategory (← getEnv) `command syntaxCommand with
        | .ok stx => pure stx
        | .error err =>
            throwError "failed to generate parser for object_notation in type theory \
              '{theory.getId}':\n{err}\ngenerated command:\n{syntaxCommand}"
      elabCommand commandStx
      liftCoreM <| registerObjectNotationDecl {
        theoryName := theory.getId.eraseMacroScopes
        syntaxName := syntaxName
        parts := parts
        holeNames := holeNames
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

/-- Print registered parse-only object notations for a theory. -/
elab "#print_object_notations" theory:ident : command => do
  let some _sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let theoryName := theory.getId.eraseMacroScopes
  let notations := (getObjectNotationDecls (← getEnv)).filter fun d =>
    d.theoryName.eraseMacroScopes == theoryName
  let lines := notations.toList.map fun d => s!"{d.patternString} => {d.template}"
  if lines.isEmpty then
    logInfo m!"no object_notation declarations for {theoryName}"
  else
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
          s!"unconditional built-in hook: any validated input is accepted and a certificate is \
            generated automatically as {lfSideConditionCertificateName r.name sc.name}"
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

/-- Render a declaration name for generic structural-metatheory diagnostics. -/
def structuralMetaNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Render a list of declaration names for generic structural-metatheory diagnostics. -/
def structuralMetaNameList (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map structuralMetaNameString)

/-- Render one checked LF binder for generic rule-induction diagnostics. -/
def renderInductionBinder (b : CheckedLFBinding) : String :=
  let rendered := s!"{structuralMetaNameString b.name} : {b.typeExpr}"
  match b.visibility with
  | .explicit => s!"({rendered})"
  | .implicit => "{" ++ rendered ++ "}"

/-- Render a nonempty list of binders, or `none`. -/
def renderInductionBinders (bs : Array CheckedLFBinding) : String :=
  if bs.isEmpty then "none" else String.intercalate " " (bs.toList.map renderInductionBinder)

/-- Render one rule-induction premise line. -/
def renderInductionPremise (p : LFJudgmentInductionPremise) : String :=
  if p.recursive then
    s!"recursive premise {structuralMetaNameString p.name} : {p.judgmentExpr}"
  else
    s!"premise {structuralMetaNameString p.name} : {p.judgmentExpr}"

/-- Render one parameter-evidence entry for a rule-induction case. -/
def renderInductionParamEvidence (ev : CheckedLFRuleParamEvidence) : String :=
  s!"evidence {structuralMetaNameString ev.name} for \
    {structuralMetaNameString ev.paramName} : {ev.judgmentExpr}"

/-- Render one side-condition entry for a rule-induction case. -/
def renderInductionSideCondition (sc : CheckedLFRuleSideCondition) : String :=
  s!"side_condition {structuralMetaNameString sc.name} by \
    {structuralMetaNameString sc.solver} : {sc.input}"

/-- Render generic rule-induction metadata as a user-facing diagnostic. -/
def LFJudgmentInductionPrinciple.render (p : LFJudgmentInductionPrinciple) : String :=
  Id.run do
    let mut lines := #[]
    lines := lines.push s!"rule induction for {structuralMetaNameString p.theoryName} over \
      {structuralMetaNameList p.judgmentNames}"
    lines := lines.push s!"cases: {p.cases.size}"
    lines := lines.push s!"recursive premises: {p.recursivePremiseCount}"
    if !p.diagnostics.isEmpty then
      lines := lines.push "diagnostics:"
      for d in p.diagnostics do
        lines := lines.push s!"- {d.kind.label}: {d.message}"
    for c in p.cases do
      lines := lines.push ""
      lines := lines.push s!"case {structuralMetaNameString c.ruleName}"
      lines := lines.push s!"  parameters: {renderInductionBinders c.params}"
      for ev in c.paramEvidences do
        lines := lines.push s!"  {renderInductionParamEvidence ev}"
      for prem in c.premises do
        lines := lines.push s!"  {renderInductionPremise prem}"
      for sc in c.sideConditions do
        lines := lines.push s!"  {renderInductionSideCondition sc}"
      lines := lines.push s!"  conclusion: {c.conclusionExpr}"
    return String.intercalate "\n" lines.toList

/-- Fetch the checked theory artifact used by generic structural-metatheory diagnostics. -/
def getCheckedStructuralMetatheoryTheory (theory : Name) : CommandElabM CheckedSignature := do
  let some checked ← liftCoreM <| getCheckedTheory? theory
    | throwError "no checked artifact stored for type theory '{theory}'"
  pure checked

/-- Throw if rule-induction metadata has blocking diagnostics. -/
def ensureUsableInductionPrinciple (p : LFJudgmentInductionPrinciple) : CommandElabM Unit := do
  unless p.isUsable do
    throwError "rule-induction metadata for type theory '{p.theoryName}' is not usable:\n\
      {String.intercalate "\n" (p.diagnostics.toList.map (·.message))}"

/-- Print generic rule-induction metadata for one judgment family. -/
elab "#print_judgment_induction " theory:ident judgmentName:ident : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let principle := checked.judgmentInductionPrinciple #[judgmentName.getId]
  logInfo m!"{principle.render}"

/-- Check that generic rule-induction metadata is available for one judgment family. -/
elab "#check_judgment_induction " theory:ident judgmentName:ident : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let principle := checked.judgmentInductionPrinciple #[judgmentName.getId]
  ensureUsableInductionPrinciple principle
  logInfo m!"judgment induction metadata for {structuralMetaNameString checked.name}.\
    {structuralMetaNameString judgmentName.getId}: {principle.cases.size} case(s), \
    {principle.recursivePremiseCount} recursive premise(s)"

/-- Print generic mutual rule-induction metadata for one or more judgment families. -/
elab "#print_rule_induction " theory:ident " for " judgments:ident,* : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let names := judgments.getElems.map (·.getId)
  if names.isEmpty then
    throwError "#print_rule_induction requires at least one judgment after `for`"
  let principle := checked.judgmentInductionPrinciple names
  logInfo m!"{principle.render}"

/-- Check generic mutual rule-induction metadata for one or more judgment families. -/
elab "#check_rule_induction " theory:ident " for " judgments:ident,* : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let names := judgments.getElems.map (·.getId)
  if names.isEmpty then
    throwError "#check_rule_induction requires at least one judgment after `for`"
  let principle := checked.judgmentInductionPrinciple names
  ensureUsableInductionPrinciple principle
  logInfo m!"rule induction metadata for {structuralMetaNameString checked.name} over \
    {structuralMetaNameList principle.judgmentNames}: {principle.cases.size} case(s), \
    {principle.recursivePremiseCount} recursive premise(s)"

/-- Render an InternalLean `Name` literal for generated structural-metatheory declarations. -/
def renderLeanNameLiteral (n : Name) : String :=
  "`" ++ structuralMetaNameString n

/-- Render a Lean `Option Name` term for generated structural-metatheory declarations. -/
def renderLeanOptionName : Option Name → String
  | none => "none"
  | some n => s!"(some {renderLeanNameLiteral n})"

/-- Render an object-universe level as a Lean expression. -/
partial def renderLevelExprTerm : LevelExpr → String
  | .zero => "InternalLean.LevelExpr.zero"
  | .lit n => s!"(InternalLean.LevelExpr.lit {n})"
  | .param n => s!"(InternalLean.LevelExpr.param {renderLeanNameLiteral n})"
  | .succ u => s!"(InternalLean.LevelExpr.succ {renderLevelExprTerm u})"
  | .max u v => s!"(InternalLean.LevelExpr.max {renderLevelExprTerm u} \
      {renderLevelExprTerm v})"

/-- Local variable names available while rendering generated induction constructors. -/
abbrev GeneratedObjLocals := NameMap Unit

/-- Whether a local variable is available while rendering an object expression. -/
def generatedObjLocalContains (locals : GeneratedObjLocals) (n : Name) : Bool :=
  (locals.find? n.eraseMacroScopes).isSome

/-- Add one local variable to a generated-object-expression renderer context. -/
def generatedObjLocalInsert (locals : GeneratedObjLocals) (n : Name) : GeneratedObjLocals :=
  locals.insert n.eraseMacroScopes ()

/-- Remove one shadowed local variable from a generated-object-expression renderer context. -/
def generatedObjLocalErase (locals : GeneratedObjLocals) (n : Name) : GeneratedObjLocals :=
  locals.erase n.eraseMacroScopes

/-- Render an `ObjExpr` as a Lean expression, using Lean variables for rule parameters. -/
partial def renderObjExprTerm (locals : GeneratedObjLocals) : ObjExpr → String
  | .ident n =>
      if generatedObjLocalContains locals n then
        structuralMetaNameString n
      else
        s!"(InternalLean.ObjExpr.ident {renderLeanNameLiteral n})"
  | .sort => "InternalLean.ObjExpr.sort"
  | .univ u => s!"(InternalLean.ObjExpr.univ {renderLevelExprTerm u})"
  | .app f a =>
      s!"(InternalLean.ObjExpr.app {renderObjExprTerm locals f} {renderObjExprTerm locals a})"
  | .arrow x A B =>
      let bodyLocals := match x with
        | some n => generatedObjLocalErase locals n
        | none => locals
      s!"(InternalLean.ObjExpr.arrow {renderLeanOptionName x} {renderObjExprTerm locals A} \
        {renderObjExprTerm bodyLocals B})"
  | .funArrow x A B =>
      let bodyLocals := match x with
        | some n => generatedObjLocalErase locals n
        | none => locals
      s!"(InternalLean.ObjExpr.funArrow {renderLeanOptionName x} {renderObjExprTerm locals A} \
        {renderObjExprTerm bodyLocals B})"
  | .sigma x A B =>
      let bodyLocals := match x with
        | some n => generatedObjLocalErase locals n
        | none => locals
      s!"(InternalLean.ObjExpr.sigma {renderLeanOptionName x} {renderObjExprTerm locals A} \
        {renderObjExprTerm bodyLocals B})"
  | .pair a b =>
      s!"(InternalLean.ObjExpr.pair {renderObjExprTerm locals a} {renderObjExprTerm locals b})"
  | .fst e => s!"(InternalLean.ObjExpr.fst {renderObjExprTerm locals e})"
  | .snd e => s!"(InternalLean.ObjExpr.snd {renderObjExprTerm locals e})"
  | .lam xs body =>
      let bodyLocals := xs.foldl (fun acc n => generatedObjLocalErase acc n) locals
      let xsTerm := "#[" ++ String.intercalate ", "
        (xs.toList.map renderLeanNameLiteral) ++ "]"
      s!"(InternalLean.ObjExpr.lam {xsTerm} {renderObjExprTerm bodyLocals body})"
  | .jeq lhs rhs =>
      s!"(InternalLean.ObjExpr.jeq {renderObjExprTerm locals lhs} \
        {renderObjExprTerm locals rhs})"

/-- Generated Lean family name for a judgment derivation predicate. -/
def judgmentDerivationFamilyName (judgmentName : Name) : String :=
  structuralMetaNameString judgmentName ++ "Derivation"

/-- Render one constructor argument binder for a generated derivation family. -/
def renderGeneratedArg (name : Name) (typeTerm : String) : String :=
  s!"({structuralMetaNameString name} : {typeTerm})"

/-- Render one generated induction constructor. -/
def renderGeneratedInductionConstructor (targets : Array Name) (c : LFJudgmentInductionCase) :
    String :=
  let targetSetContains (n : Name) : Bool :=
    targets.any fun target => target.eraseMacroScopes == n.eraseMacroScopes
  let locals := c.params.foldl (init := ({} : GeneratedObjLocals)) fun locals b =>
    generatedObjLocalInsert locals b.name
  let args : List String := Id.run do
    let mut args := c.params.toList.map fun b =>
      renderGeneratedArg b.name "InternalLean.ObjExpr"
    for ev in c.paramEvidences do
      args := args ++ [renderGeneratedArg ev.name "InternalLean.ObjExpr"]
    for p in c.premises do
      let typeTerm := match p.head? with
        | some h =>
            if h.kind == .judgment && targetSetContains h.name then
              s!"{judgmentDerivationFamilyName h.name} {renderObjExprTerm locals p.judgmentExpr}"
            else
              "InternalLean.ObjExpr"
        | none => "InternalLean.ObjExpr"
      args := args ++ [renderGeneratedArg p.name typeTerm]
    for sc in c.sideConditions do
      args := args ++ [renderGeneratedArg sc.name "InternalLean.ObjExpr"]
    return args
  let argsText := if args.isEmpty then "" else " " ++ String.intercalate " " args
  let family := judgmentDerivationFamilyName c.conclusionHead.name
  s!"  | {structuralMetaNameString c.ruleName}{argsText} : {family} \
    {renderObjExprTerm locals c.conclusionExpr}"

/-- Render a generated derivation-family inductive declaration for one target judgment. -/
def renderGeneratedInductionFamily (p : LFJudgmentInductionPrinciple) (target : Name) : String :=
  let cases := p.cases.filter fun c =>
    c.conclusionHead.name.eraseMacroScopes == target.eraseMacroScopes
  let constructorLines := cases.toList.map (renderGeneratedInductionConstructor p.judgmentNames)
  let constructors := String.intercalate "\n" constructorLines
  s!"inductive {judgmentDerivationFamilyName target} : InternalLean.ObjExpr → Type where\n\
    {constructors}"

/-- Render generated derivation-family declarations for a rule-induction principle. -/
def LFJudgmentInductionPrinciple.renderGeneratedCommands (p : LFJudgmentInductionPrinciple) :
    Array String :=
  let familyDecls := p.judgmentNames.toList.map (renderGeneratedInductionFamily p)
  let body :=
    if p.judgmentNames.size == 1 then
      String.intercalate "\n\n" familyDecls
    else
      "mutual\n" ++ String.intercalate "\n\n" familyDecls ++ "\nend"
  #[s!"namespace {structuralMetaNameString p.theoryName}", body,
    s!"end {structuralMetaNameString p.theoryName}"]

/-- Render generated derivation-family declarations as one diagnostic string. -/
def LFJudgmentInductionPrinciple.renderGeneratedCommand (p : LFJudgmentInductionPrinciple) :
    String :=
  String.intercalate "\n\n" p.renderGeneratedCommands.toList

/-- Elaborate generated derivation-family declarations for a checked induction principle. -/
def elabGeneratedInductionPrinciple (p : LFJudgmentInductionPrinciple) : CommandElabM Unit := do
  ensureUsableInductionPrinciple p
  for commandString in p.renderGeneratedCommands do
    let commandStx ←
      match Lean.Parser.runParserCategory (← getEnv) `command commandString with
      | .ok stx => pure stx
      | .error err =>
          throwError "failed to generate rule-induction declarations for type theory \
            '{p.theoryName}':\n{err}\ngenerated command:\n{p.renderGeneratedCommand}"
    elabCommand commandStx

/-- Generate Lean derivation families for one judgment's generic rule-induction metadata. -/
elab "generate_judgment_induction " theory:ident judgmentName:ident : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  elabGeneratedInductionPrinciple <| checked.judgmentInductionPrinciple #[judgmentName.getId]

/-- Generate Lean derivation families for one or more mutually covered judgments. -/
elab "generate_rule_induction " theory:ident " for " judgments:ident,* : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let names := judgments.getElems.map (·.getId)
  if names.isEmpty then
    throwError "generate_rule_induction requires at least one judgment after `for`"
  elabGeneratedInductionPrinciple <| checked.judgmentInductionPrinciple names

/-- Whether a role tag matches a normalized structural-metatheory role name. -/
def structuralRoleMatches (kind expected : Name) : Bool :=
  kind.eraseMacroScopes == expected.eraseMacroScopes

/-- Names of syntax sorts carrying a given structural-metatheory role. -/
def syntaxSortsWithStructuralRole (checked : CheckedSignature) (role : Name) : Array Name :=
  checked.lfSyntaxSortRoles.foldl (init := #[]) fun out r =>
    if structuralRoleMatches r.kind role then pushIfMissing out r.sortName.eraseMacroScopes
    else out

/-- Theory-local object roles carrying a given structural-metatheory role. -/
def objectRolesWithStructuralRole (sig : HLSignature) (role : Name) : Array ObjectRole :=
  sig.roles.filter fun r => structuralRoleMatches r.kind role

/-- Render one theory-local structural object role. -/
def renderStructuralObjectRole (r : ObjectRole) : String :=
  let related := match r.related with
    | some n => s!" for {structuralMetaNameString n}"
    | none => ""
  s!"{structuralMetaNameString r.name} : {structuralMetaNameString r.kind}{related}"

/-- Build a generic structural-substitution metadata report from existing roles/zones/classes. -/
def structuralMetatheoryReport (sig : HLSignature) (checked : CheckedSignature) :
    String × Array String := Id.run do
  let contextSorts := syntaxSortsWithStructuralRole checked `context
  let typeSorts := syntaxSortsWithStructuralRole checked `type_sort
  let termSorts := syntaxSortsWithStructuralRole checked `term_sort
  let extensions := objectRolesWithStructuralRole sig `context_extension
  let newestVariables := objectRolesWithStructuralRole sig `newest_variable
  let weakenings := objectRolesWithStructuralRole sig `structural_weakening
  let substitutions := objectRolesWithStructuralRole sig `structural_substitution
  let mut lines := #[]
  lines := lines.push s!"generic structural metadata for {structuralMetaNameString checked.name}"
  lines := lines.push s!"context syntax sorts: {structuralMetaNameList contextSorts}"
  lines := lines.push s!"type-like syntax sorts: {structuralMetaNameList typeSorts}"
  lines := lines.push s!"term-like syntax sorts: {structuralMetaNameList termSorts}"
  lines := lines.push s!"context zones: {checked.lfContextZones.size}"
  for z in checked.lfContextZones do
    let deps := if z.dependsOn.isEmpty then "none" else structuralMetaNameList z.dependsOn
    lines := lines.push s!"  zone {structuralMetaNameString z.name} : \
      {structuralMetaNameString z.sortName}, depends_on {deps}"
  lines := lines.push s!"binder classes: {checked.lfBinderClasses.size}"
  for b in checked.lfBinderClasses do
    let deps := if b.dependsOn.isEmpty then "none" else structuralMetaNameList b.dependsOn
    lines := lines.push s!"  binder_class {structuralMetaNameString b.name} : \
      {structuralMetaNameString b.boundSortName} in {structuralMetaNameString b.zoneName}, \
      depends_on {deps}"
  lines := lines.push "structural object roles:"
  for pair in #[(extensions, "context_extension"), (newestVariables, "newest_variable"),
      (weakenings, "structural_weakening"), (substitutions, "structural_substitution")] do
    let roles := pair.1
    let label := pair.2
    if roles.isEmpty then
      lines := lines.push s!"  {label}: none"
    else
      lines := lines.push s!"  {label}:"
      for r in roles do
        lines := lines.push s!"    {renderStructuralObjectRole r}"
  let mut diagnostics := #[]
  if contextSorts.isEmpty then
    diagnostics := diagnostics.push "no syntax_sort_role ... : context metadata is registered"
  if checked.lfContextZones.isEmpty then
    diagnostics := diagnostics.push "no context_zone metadata is registered"
  for z in checked.lfContextZones do
    unless checked.lfBinderClasses.any (fun b =>
        b.zoneName.eraseMacroScopes == z.name.eraseMacroScopes) do
      diagnostics := diagnostics.push s!"context zone '{z.name}' has no binder_class"
  if checked.lfBinderClasses.isEmpty then
    diagnostics := diagnostics.push "no binder_class metadata is registered"
  if extensions.isEmpty then
    diagnostics := diagnostics.push "no object_role ... : context_extension metadata is registered"
  if weakenings.isEmpty && substitutions.isEmpty then
    diagnostics := diagnostics.push "no structural_weakening or structural_substitution object \
      roles are registered"
  if !diagnostics.isEmpty then
    lines := lines.push "diagnostics:"
    for d in diagnostics do
      lines := lines.push s!"- {d}"
  return (String.intercalate "\n" lines.toList, diagnostics)

/-- Print generic structural-substitution metadata and diagnostics. -/
elab "#print_structural_metatheory " theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let (report, _) := structuralMetatheoryReport flatSig checked
  logInfo m!"{report}"

/-- Check that enough generic structural-substitution metadata is present for later generators. -/
elab "#check_structural_metatheory " theory:ident : command => do
  let some sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let flatSig ← liftCoreM <| flattenSignature sig
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let (_, diagnostics) := structuralMetatheoryReport flatSig checked
  unless diagnostics.isEmpty do
    throwError "generic structural metadata for type theory '{checked.name}' is incomplete:\n\
      {String.intercalate "\n" diagnostics.toList}"
  logInfo m!"generic structural metadata for {structuralMetaNameString checked.name}: ready"

/-- Recognized conversion judgments for generic congruence diagnostics. -/
def congruenceConversionJudgments (checked : CheckedSignature) : Array Name :=
  checked.conversionJudgmentNames

/-- Explicit congruence metadata target-head names. -/
def explicitCongruenceTargetHeads (checked : CheckedSignature) : Array Name :=
  checked.lfRewriteCongruences.foldl (init := #[]) fun out c =>
    pushIfMissing out c.targetHead.eraseMacroScopes

/-- Render generic congruence obligations inferred from checked declarations and metadata. -/
def congruenceObligationReport (checked : CheckedSignature) : String × Array String := Id.run do
  let conversionJudgments := congruenceConversionJudgments checked
  let explicitTargets := explicitCongruenceTargetHeads checked
  let mut lines := #[]
  let mut diagnostics := #[]
  lines := lines.push s!"generic congruence obligations for {structuralMetaNameString checked.name}"
  lines := lines.push s!"conversion judgments: {structuralMetaNameList conversionJudgments}"
  if conversionJudgments.isEmpty then
    diagnostics := diagnostics.push "no judgment_role ... : type_conversion or term_conversion \
      metadata is registered"
  lines := lines.push s!"explicit rewrite_congruence metadata: \
    {checked.lfRewriteCongruences.size}"
  for d in checked.lfSyntaxDefs do
    let status := if d.value?.isSome then "automatic candidate from checked syntax_def" else
      "proof required for admitted syntax_def"
    lines := lines.push s!"- {structuralMetaNameString d.name}: {status}"
  for d in checked.lfObjectDefs do
    lines := lines.push s!"- {structuralMetaNameString d.name}: automatic candidate from \
      checked lf_def"
  for o in checked.lfOpaqueConsts do
    if o.typeExpr?.isSome then
      let status :=
        if explicitTargets.contains o.name.eraseMacroScopes then
          "explicit rewrite_congruence metadata present"
        else
          "proof required for opaque head"
      lines := lines.push s!"- {structuralMetaNameString o.name}: {status}"
  if !diagnostics.isEmpty then
    lines := lines.push "diagnostics:"
    for d in diagnostics do
      lines := lines.push s!"- {d}"
  return (String.intercalate "\n" lines.toList, diagnostics)

/-- Print generic congruence theorem obligations inferred from checked declaration metadata. -/
elab "#print_congruence_obligations " theory:ident : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let (report, _) := congruenceObligationReport checked
  logInfo m!"{report}"

/-- Check that generic congruence metadata has at least one declared conversion judgment. -/
elab "#check_congruence_obligations " theory:ident : command => do
  let checked ← getCheckedStructuralMetatheoryTheory theory.getId
  let (_, diagnostics) := congruenceObligationReport checked
  unless diagnostics.isEmpty do
    throwError "generic congruence metadata for type theory '{checked.name}' is incomplete:\n\
      {String.intercalate "\n" diagnostics.toList}"
  logInfo m!"generic congruence obligations for {structuralMetaNameString checked.name}: ready"

/-- Class of a theory-local external Lean parameter declaration. -/
inductive ExternalLeanDeclarationKind where
  /-- External type/parameter family available to the LF metadata layer. -/
  | param
  /-- External Lean constant available in explicitly external metadata. -/
  | const
  /-- External Lean proposition-valued relation or side-condition predicate. -/
  | rel
  deriving Inhabited, Repr, BEq

namespace ExternalLeanDeclarationKind

/-- User-facing external Lean declaration label. -/
def label : ExternalLeanDeclarationKind → String
  | .param => "external_param"
  | .const => "external_const"
  | .rel => "external_rel"

end ExternalLeanDeclarationKind

/-- Stored source for an external Lean parameter/constant declaration.

This is Phase-6 trust-boundary metadata.  The Lean terms are parsed by Lean's parser at the command
site and stored as source strings; future LF telescope integration should elaborate these through
Lean's kernel rather than adding an InternalLean evaluator for external terms. -/
structure ExternalLeanDeclaration where
  /-- Theory that owns this external metadata. -/
  theoryName : Name
  /-- Theory-local external declaration name. -/
  name : Name
  /-- Declaration class. -/
  kind : ExternalLeanDeclarationKind
  /-- Parsed Lean type expression, rendered as source. -/
  typeSource : String
  /-- Parsed Lean value/expression, rendered as source. -/
  valueSource : String
  deriving Inhabited, Repr, BEq

/-- Persistent external Lean metadata declarations, keyed by owning theory in diagnostics. -/
initialize externalLeanDeclExt : SimplePersistentEnvExtension ExternalLeanDeclaration
    (Array ExternalLeanDeclaration) ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.externalLeanDeclExt
    addEntryFn := fun decls d => decls.push d
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[] }

/-- Render a parsed Lean term syntax as a compact source string for metadata reports. -/
def leanTermSourceString (stx : TSyntax `term) : CommandElabM String := do
  let fmt ← liftCoreM <| Lean.PrettyPrinter.ppTerm stx
  pure fmt.pretty

/-- Registered external Lean metadata for a theory. -/
def externalLeanDeclarationsFor (env : Environment) (theoryName : Name) :
    Array ExternalLeanDeclaration :=
  externalLeanDeclExt.getState env |>.filter fun d =>
    d.theoryName.eraseMacroScopes == theoryName.eraseMacroScopes

/-- Register one external Lean declaration after checking the owning theory and duplicates. -/
def registerExternalLeanDeclaration (d : ExternalLeanDeclaration) : CommandElabM Unit := do
  let some _sig ← liftCoreM <| getTheory? d.theoryName
    | throwError "unknown type theory '{d.theoryName}'"
  let old := externalLeanDeclarationsFor (← getEnv) d.theoryName
  if old.any (fun old => old.name.eraseMacroScopes == d.name.eraseMacroScopes) then
    throwError "external Lean metadata '{d.name}' is already registered for type theory \
      '{d.theoryName}'"
  modifyEnv fun env => externalLeanDeclExt.addEntry env d

/-- Register an external Lean type/parameter alias for a checked type theory. -/
elab "external_param " theory:ident name:ident " : " ty:term " := " value:term : command => do
  registerExternalLeanDeclaration {
    theoryName := theory.getId.eraseMacroScopes
    name := name.getId.eraseMacroScopes
    kind := .param
    typeSource := (← leanTermSourceString ty)
    valueSource := (← leanTermSourceString value) }

/-- Register an external Lean constant for a checked type theory. -/
elab "external_const " theory:ident name:ident " : " ty:term " := " value:term : command => do
  registerExternalLeanDeclaration {
    theoryName := theory.getId.eraseMacroScopes
    name := name.getId.eraseMacroScopes
    kind := .const
    typeSource := (← leanTermSourceString ty)
    valueSource := (← leanTermSourceString value) }

/-- Register an external Lean relation or side-condition predicate for a checked type theory. -/
elab "external_rel " theory:ident name:ident " : " ty:term " := " value:term : command => do
  registerExternalLeanDeclaration {
    theoryName := theory.getId.eraseMacroScopes
    name := name.getId.eraseMacroScopes
    kind := .rel
    typeSource := (← leanTermSourceString ty)
    valueSource := (← leanTermSourceString value) }

/-- Render external Lean parameter metadata for diagnostics. -/
def externalLeanMetadataReport (theoryName : Name) (decls : Array ExternalLeanDeclaration) :
    String := Id.run do
  let mut lines := #[s!"external Lean metadata for {structuralMetaNameString theoryName}: \
    {decls.size} declaration(s)",
    "external terms are Lean-side metadata; future LF telescope support must elaborate them \
      through Lean's kernel"]
  if decls.isEmpty then
    lines := lines.push "none"
  else
    for d in decls do
      lines := lines.push s!"{d.kind.label} {structuralMetaNameString d.name} : \
        {d.typeSource} := {d.valueSource}"
  return String.intercalate "\n" lines.toList

/-- Print external Lean metadata registered for a type theory. -/
elab "#print_external_lf_parameters " theory:ident : command => do
  let some _sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let decls := externalLeanDeclarationsFor (← getEnv) theory.getId
  logInfo m!"{externalLeanMetadataReport theory.getId decls}"

/-- Check that at least one external Lean metadata declaration is registered for a theory. -/
elab "#check_external_lf_parameters " theory:ident : command => do
  let some _sig ← liftCoreM <| getTheory? theory.getId
    | throwError "unknown type theory '{theory.getId}'"
  let decls := externalLeanDeclarationsFor (← getEnv) theory.getId
  if decls.isEmpty then
    throwError "no external Lean metadata registered for type theory '{theory.getId}'"
  logInfo m!"external Lean metadata for {structuralMetaNameString theory.getId}: \
    {decls.size} declaration(s)"

/-- User-facing name rendering for documentation/admission lints. -/
def docLintNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Whether an object expression mentions a named object constant/variable. -/
partial def objExprMentionsName (needle : Name) : ObjExpr → Bool
  | .ident n => n.eraseMacroScopes == needle.eraseMacroScopes
  | .sort | .univ .. => false
  | .app f a => objExprMentionsName needle f || objExprMentionsName needle a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B =>
      objExprMentionsName needle A || objExprMentionsName needle B
  | .pair a b => objExprMentionsName needle a || objExprMentionsName needle b
  | .fst e | .snd e => objExprMentionsName needle e
  | .lam _ body => objExprMentionsName needle body
  | .jeq lhs rhs => objExprMentionsName needle lhs || objExprMentionsName needle rhs

/-- Downstream declarations whose source body/proof mentions admitted internal declarations. -/
def internalAdmissionDependencyLines (sig : HLSignature) (admissions : Array InternalAdmission) :
  Array String := Id.run do
  let admittedNames := admissions.map (·.declName)
  let mut out := #[]
  let depsForExprs (exprs : Array ObjExpr) := admittedNames.filter fun n =>
    exprs.any (fun e => objExprMentionsName n e)
  for d in sig.syntaxDefs do
    if let some value := d.value? then
      let paramTypes := d.params.map (·.typeExpr)
      let deps := depsForExprs (paramTypes.push value)
      unless deps.isEmpty do
        out := out.push s!"syntax_def {docLintNameString d.name} depends on admitted \
          {String.intercalate ", " (deps.toList.map docLintNameString)}"
  for d in sig.lfObjectDefs do
    let deps := depsForExprs #[d.typeExpr, d.value]
    unless deps.isEmpty do
      out :=
        out.push s!"internal def {docLintNameString d.name} depends on admitted \
          {String.intercalate ", " (deps.toList.map docLintNameString)}"
  for t in sig.lfJudgmentTheorems do
    let deps := depsForExprs #[t.judgmentExpr, t.proof]
    unless deps.isEmpty do
      out :=
        out.push s!"internal theorem {docLintNameString t.name} depends on admitted \
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
  for d in sig.syntaxDefs do out := out.push { role := .syntaxDef, sourceName := d.name }
  for a in sig.judgmentAbbrevs do
    out := out.push { role := .judgmentAbbrev, sourceName := a.name }
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

/-- Print accumulated theory/internal-declaration registration profile entries. -/
elab "#print_internal_registration_profile " theory:ident : command => do
  liftCoreM <| requireTheoryAnchor theory.getId
  let profiles ← liftCoreM <| getInternalRegistrationProfilesFor theory.getId
  if profiles.isEmpty then
    logInfo m!"type theory '{theory.getId}' has no registration profile entries"
  else
    let totals := profiles.foldl
      (init := (0, 0, 0, 0))
      (fun (objs, thms, opaques, inc) p =>
        (objs + p.recheckedObjectDefs, thms + p.recheckedJudgmentTheorems,
          opaques + p.recheckedOpaqueConsts, inc + p.incrementallyChecked))
    let lines := profiles.map fun p =>
      s!"{p.declName.eraseMacroScopes}: {p.strategy}; prior={p.priorObjectDefs} object def(s), \
        {p.priorJudgmentTheorems} theorem(s){internalRegistrationProfileMetadataSuffix p}; \
        rechecked={p.recheckedObjectDefs} object def(s), {p.recheckedJudgmentTheorems} \
        theorem(s); incremental={p.incrementallyChecked}"
    let opaqueText :=
      if totals.2.2.1 == 0 then ""
      else s!", {totals.2.2.1} opaque(s)"
    logInfo m!"registration profile for {theory.getId}: {profiles.size} event(s); total \
      old-artifact rechecks={totals.1} object def(s), {totals.2.1} theorem(s){opaqueText}; \
      incrementally checked={totals.2.2.2}\n{String.intercalate "\n" lines.toList}"

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
      let docRole := match a.kind with
        | .syntaxDef => SourceDocRole.syntaxDef
        | .lfOpaque | .judgmentTheorem => SourceDocRole.internalDef
      let hasDoc := docs.any fun d => d.role == docRole
        && d.sourceName.eraseMacroScopes == a.declName.eraseMacroScopes
      let docText := if hasDoc then " [documented]" else " [missing doc]"
      let binderText :=
        if a.params.isEmpty then ""
        else " " ++ String.intercalate " " (a.params.toList.map HLBinding.summary)
      s!"admitted {a.kind.sourceNoun} {a.anchorName.eraseMacroScopes}{binderText} : \
        {a.typeExpr}{docText}"
    let deps := internalAdmissionDependencyLines sig admissions
    let transports ← liftCoreM <| getInternalAdmissionTransportsFor theory.getId
    let transportLines := transports.map fun t =>
      s!"transported declaration {t.generatedName.eraseMacroScopes} for admitted \
        {t.declName.eraseMacroScopes} over\nmodel {t.structureName.eraseMacroScopes} intentionally \
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
    {checked.lfSyntaxAbbrevs.size} checked syntax abbreviation(s), \
    {checked.lfSyntaxDefs.size} checked syntax definition(s), \
    {checked.lfJudgmentAbbrevs.size} checked judgment abbreviation(s), {roleCount} role(s), \
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
    let result := if LevelExpr.equal s.resultLevel .zero then "Type" else s!"Type {s.resultLevel}"
    logInfo m!"LF syntax_sort {s.name}: {s.arity} parameter(s), result {result}"
  for a in checked.lfSyntaxAbbrevs do
    logInfo m!"LF syntax_abbrev {a.name}: {a.params.size} parameter(s), expands to {a.value}"
  for d in checked.lfSyntaxDefs do
    let result := if LevelExpr.equal d.resultLevel .zero then "Type" else s!"Type {d.resultLevel}"
    match d.value? with
    | some value =>
        logInfo m!"LF syntax_def {d.name}: {d.params.size} parameter(s), result {result}, := \
          {value}"
    | none =>
        logInfo m!"LF syntax_def {d.name}: {d.params.size} parameter(s), result {result}, := \
          sorry"
  for a in checked.lfJudgmentAbbrevs do
    logInfo m!"LF judgment_abbrev {a.name}: {a.params.size} parameter(s), expands to {a.value}"
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
  | .sigma none A B => m!"({CheckedLFExpr.summary A} × {CheckedLFExpr.summary B})"
  | .sigma (some x) A B => m!"(Σ {x} : {CheckedLFExpr.summary A}, {CheckedLFExpr.summary B})"
  | .pair a b => m!"⟨{CheckedLFExpr.summary a}, {CheckedLFExpr.summary b}⟩"
  | .fst e => m!"({CheckedLFExpr.summary e}.1)"
  | .snd e => m!"({CheckedLFExpr.summary e}.2)"
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
  | .arrow _ A B | .sigma _ A B =>
      CheckedLFExpr.collectHeads (CheckedLFExpr.collectHeads counts A) B
  | .pair a b => CheckedLFExpr.collectHeads (CheckedLFExpr.collectHeads counts a) b
  | .fst e | .snd e => CheckedLFExpr.collectHeads counts e
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
    {checked.lfSyntaxAbbrevs.size} syntax abbreviation(s), \
      {checked.lfSyntaxDefs.size} syntax definition(s), \
      {checked.lfJudgmentAbbrevs.size} judgment abbreviation(s), \
        {checked.lfContextZones.size} context zone(s), {checked.lfBinderClasses.size} binder \
          class(es), {checked.lfJudgments.size} \
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
  for d in checked.lfSyntaxDefs do
    let params := String.intercalate " " (d.params.toList.map fun b =>
      s!"({b.name} : {b.typeExpr})")
    let head := match d.head? with | some h => m!" headed by {h.summary}" | none => m!""
    match d.value? with
    | some value => logInfo m!"syntax_def {d.name} {params} : Type {d.resultLevel} := {value}{head}"
    | none => logInfo m!"syntax_def {d.name} {params} : Type {d.resultLevel} := sorry"
  for a in checked.lfJudgmentAbbrevs do
    let params := String.intercalate " " (a.params.toList.map fun b =>
      s!"({b.name} : {b.typeExpr})")
    logInfo m!"judgment_abbrev {a.name} {params} := {a.value} headed by {a.head.summary}"
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
      {env.syntaxDefs.size} syntax definition(s), \
      {env.judgmentAbbrevs.size} judgment abbreviation(s), {env.contextZones.size} context \
        zone(s), {env.binderClasses.size} binder class(es), \
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
        let head := match p.head? with | some h => m!" headed by {h.summary}" | none => m!""
        logInfo m!"  premise {p.name}: {p.judgmentExpr}{head}"
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
    for p in r.premises do
      let head := match p.head? with | some h => m!"{h.summary}" | none => m!"structural evidence"
      if p.isDirectJudgment then
        logInfo m!"  premise-slot {p.name}: {head}"
        logInfo m!"    resolved premise: {p.checkedJudgmentExpr.summary}"
      else
        logInfo m!"  evidence-parameter slot {p.name}: {head}"
        logInfo m!"    resolved evidence type: {p.checkedJudgmentExpr.summary}"
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
  for d in checked.lfSyntaxDefs do
    for b in d.params do
      counts := b.checkedTypeExpr.collectHeads counts
    if let some value := d.checkedValue? then
      counts := value.collectHeads counts
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
    sig.syntaxSorts.size + sig.syntaxAbbrevs.size + sig.syntaxDefs.size +
      sig.judgmentAbbrevs.size + sig.syntaxSortRoles.size + sig.contextZones.size +
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
  for d in sig.syntaxDefs do
    logInfo d.summary
  for a in sig.judgmentAbbrevs do
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
  let evidenceName := theoryEvidenceName sig.name
  logInfo m!"{anchorName} : InternalLean.TheoryAnchor {evidenceName}"
  match ← findDocString? (← getEnv) anchorName with
  | some doc => logInfo m!"{doc}"
  | none => logInfo m!"no docstring found for '{anchorName}'"

/-- Print one generated internal-declaration anchor and its evidence registry record. -/
elab "#print_internal_declaration_anchor " anchor:ident : command => do
  let anchorName := anchor.getId
  let some record ← liftCoreM <| findInternalDeclarationEvidenceByAnchor? anchorName
    | throwError "unknown InternalLean internal declaration anchor '{anchorName}'"
  let paramsText := String.intercalate " " (record.params.toList.map HLBinding.summary)
  let paramsText := if paramsText.isEmpty then "none" else paramsText
  let valueText :=
    match record.valueExpr? with
    | some valueExpr => toString valueExpr
    | none => "explicit admission; no checked body"
  let env ← getEnv
  let anchorStatus := if env.contains record.anchorName then "present" else "missing"
  let evidenceStatus := if env.contains record.evidenceName then "present" else "missing"
  let checkedHL? ← liftCoreM <| getCheckedHLSignature? record.theoryName
  let checkedStatus :=
    match checkedHL? with
    | some sig => if sig.containsName record.localName then "present" else "missing"
    | none => "missing checked signature"
  let admissionStatus ← liftCoreM do
    if record.kind.isAdmitted then
      let admissions ← getInternalAdmissionsFor record.theoryName
      pure <| if admissions.any (fun a => a.declName.eraseMacroScopes ==
          record.localName.eraseMacroScopes) then "present" else "missing"
    else
      pure "not an admission"
  logInfo m!"internal declaration anchor {record.anchorName}"
  logInfo m!"  theory: {record.theoryName}"
  logInfo m!"  local name: {record.localName}"
  logInfo m!"  kind: {record.kind.label}"
  logInfo m!"  source command: {record.sourceCommand}"
  logInfo m!"  evidence: {record.evidenceName} [{evidenceStatus}]"
  logInfo m!"  anchor declaration: {anchorStatus}"
  logInfo m!"  checked registry entry: {checkedStatus}"
  logInfo m!"  admission registry entry: {admissionStatus}"
  logInfo m!"  source binders: {paramsText}"
  logInfo m!"  checked annotation/type: {record.typeExpr}"
  logInfo m!"  checked body/proof: {valueText}"

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
    sig.syntaxSorts.size + sig.syntaxAbbrevs.size + sig.syntaxDefs.size +
      sig.judgmentAbbrevs.size + sig.syntaxSortRoles.size + sig.contextZones.size +
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
  for d in sig.syntaxDefs do
    logInfo d.summary
  for a in sig.judgmentAbbrevs do
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
