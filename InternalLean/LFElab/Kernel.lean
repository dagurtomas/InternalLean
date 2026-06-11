/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.Kernel
public meta import InternalLean.LFElab.Objects

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Find a de Bruijn index for a source local in a KTerm-lowering binder stack.

Exact hygienic binder names win. If no exact binder exists, erased-name fallback is allowed only
when it is unique; otherwise lowering rejects the ambiguous binder instead of guessing. -/
def findKTermLoweringBinder? (binders : Array (Option Name)) (x : Name) :
    Except String (Option Nat) := do
  let rec exact (i : Nat) : List (Option Name) → Option Nat
    | [] => none
    | none :: rest => exact (i + 1) rest
    | some y :: rest => if y == x then some i else exact (i + 1) rest
  let stack := binders.toList.reverse
  match exact 0 stack with
  | some i => pure (some i)
  | none =>
      let xErased := x.eraseMacroScopes
      let rec erasedMatches (i : Nat) : List (Option Name) → List (Nat × Name)
        | [] => []
        | none :: rest => erasedMatches (i + 1) rest
        | some y :: rest =>
            let restMatches := erasedMatches (i + 1) rest
            if y.eraseMacroScopes == xErased then (i, y) :: restMatches else restMatches
      match erasedMatches 0 stack with
      | [] => pure none
      | [(i, _)] => pure (some i)
      | _ => throw s!"checked LF expression lowers ambiguous local '{xErased}' after erasing \
          macro scopes"

/-- Lower a checked LF expression to a structural kernel term. -/
partial def checkedLFExprToKTermWithContext (metas : NameMap RawMetaSort) (freeLocals : NameSet)
    (binders : Array (Option Name)) : CheckedLFExpr → Except String Kernel.KTerm
  | .ident h => do
      let name := h.name.eraseMacroScopes
      if h.kind == .local then
        match ← findKTermLoweringBinder? binders h.name with
        | some i => pure (.bvar i)
        | none =>
            match metas.find? name with
            | some sort => pure (.mvar (Kernel.KName.ofName name) sort)
            | none =>
                if freeLocals.contains name then
                  pure (.fvar (Kernel.KLocalName.ofName name))
                else
                  throw s!"checked LF expression lowers out-of-scope local '{name}'"
      else
        pure <| .ident { name := Kernel.KName.ofName name }
  | .sort => pure (.univ .zero)
  | .univ u => pure (.univ (LevelExpr.normalize u))
  | .app f a => do
      let f ← checkedLFExprToKTermWithContext metas freeLocals binders f
      let a ← checkedLFExprToKTermWithContext metas freeLocals binders a
      pure (.app f a)
  | .arrow none A B => do
      let A ← checkedLFExprToKTermWithContext metas freeLocals binders A
      let B ← checkedLFExprToKTermWithContext metas freeLocals (binders.push none) B
      pure (.arrow A B)
  | .arrow (some x) A B => do
      let A ← checkedLFExprToKTermWithContext metas freeLocals binders A
      let B ← checkedLFExprToKTermWithContext metas freeLocals (binders.push (some x)) B
      pure (.arrow A B)
  | .sigma none A B => do
      let A ← checkedLFExprToKTermWithContext metas freeLocals binders A
      let B ← checkedLFExprToKTermWithContext metas freeLocals (binders.push none) B
      pure (.sigma A B)
  | .sigma (some x) A B => do
      let A ← checkedLFExprToKTermWithContext metas freeLocals binders A
      let B ← checkedLFExprToKTermWithContext metas freeLocals (binders.push (some x)) B
      pure (.sigma A B)
  | .pair a b => do
      let a ← checkedLFExprToKTermWithContext metas freeLocals binders a
      let b ← checkedLFExprToKTermWithContext metas freeLocals binders b
      pure (.pair a b)
  | .fst e => do
      let e ← checkedLFExprToKTermWithContext metas freeLocals binders e
      pure (.fst e)
  | .snd e => do
      let e ← checkedLFExprToKTermWithContext metas freeLocals binders e
      pure (.snd e)
  | .lam xs body => do
      let binders' := xs.foldl (fun binders x => binders.push (some x)) binders
      let body ← checkedLFExprToKTermWithContext metas freeLocals binders' body
      pure <| xs.toList.foldr (fun _ acc => .lam acc) body
  | .jeq lhs rhs => do
      let lhs ← checkedLFExprToKTermWithContext metas freeLocals binders lhs
      let rhs ← checkedLFExprToKTermWithContext metas freeLocals binders rhs
      pure (.jeq lhs rhs)

/-- Lower a closed checked LF expression to a structural kernel term. -/
def checkedLFExprToKTerm (e : CheckedLFExpr) (metas : NameMap RawMetaSort := {})
    (freeLocals : NameSet := {}) : Except String Kernel.KTerm :=
  checkedLFExprToKTermWithContext metas freeLocals #[] e

/-- Lower a checked LF judgment-headed expression to a structural kernel judgment. -/
def checkedLFJudgmentExprToKJudgment (e : CheckedLFExpr) (head : CheckedLFHead)
    (metas : NameMap RawMetaSort := {}) (freeLocals : NameSet := {}) :
    Except String Kernel.Judgment := do
  let (_, args) := splitCheckedLFApp e
  let args ← args.toList.mapM (fun arg => checkedLFExprToKTerm arg metas freeLocals)
  pure { head := Kernel.KName.ofName head.name, args := args }

/-- Structural kernel sort label inferred for a checked LF binder. -/
def checkedLFBindingKernelSort (b : CheckedLFBinding) : RawMetaSort :=
  match b.head? with
  | some h => if h.kind == .syntaxSort then .custom h.name else .arg
  | none => .arg

/-- Add one checked LF binder to a structural metavariable map. -/
def insertCheckedLFBindingMeta (metas : NameMap RawMetaSort) (b : CheckedLFBinding) :
    NameMap RawMetaSort :=
  metas.insert b.name.eraseMacroScopes (checkedLFBindingKernelSort b)

/-- Lower a checked LF binder to a structural replay metavariable. -/
def checkedLFBindingToKMetaVar (metas : NameMap RawMetaSort) (b : CheckedLFBinding) :
    Except String Kernel.RuleMetaVar := do
  pure {
    name := Kernel.KName.ofName b.name
    sort := checkedLFBindingKernelSort b
    type? := some (← checkedLFExprToKTerm b.checkedTypeExpr metas) }

/-- Lower a checked LF binder telescope to structural replay metavariables. -/
def checkedLFBindingsToKMetaVars (params : Array CheckedLFBinding) :
    Except String (List Kernel.RuleMetaVar × NameMap RawMetaSort) := do
  let mut metas : NameMap RawMetaSort := {}
  let mut out := []
  for p in params do
    out := out ++ [← checkedLFBindingToKMetaVar metas p]
    metas := insertCheckedLFBindingMeta metas p
  pure (out, metas)

/-- Split a checked LF function type into a structural constant telescope and result. -/
partial def checkedLFTypeToKConstantTelescope (metas : NameMap RawMetaSort)
    (e : CheckedLFExpr) (i : Nat := 1) :
    Except String (List Kernel.RuleMetaVar × Kernel.KTerm) := do
  match e with
  | .arrow binder? A B =>
      let name := (binder?.getD (Name.mkSimple s!"_arg{i}")).eraseMacroScopes
      let param : Kernel.RuleMetaVar := {
        name := Kernel.KName.ofName name
        sort := .arg
        type? := some (← checkedLFExprToKTerm A metas) }
      let metas' :=
        match binder? with
        | some x => metas.insert x.eraseMacroScopes .arg
        | none => metas
      let (params, result) ← checkedLFTypeToKConstantTelescope metas' B (i + 1)
      pure (param :: params, result)
  | e => pure ([], ← checkedLFExprToKTerm e metas)

/-- Lower a checked syntax definition to a structural replay constant. -/
def checkedLFSyntaxDefToKConstant (defValues : CheckedLFDefinitionValueMap)
    (d : CheckedLFSyntaxDef) : Except String Kernel.LFConstantSchema := do
  let rawTypeExpr := d.params.foldr (init := checkedLFTypeOfLevel d.resultLevel) fun b acc =>
    .arrow (some b.name) b.checkedTypeExpr acc
  let typeExpr := unfoldLFDefinitionsInCheckedExpr defValues {} rawTypeExpr
  let (params, result) ← checkedLFTypeToKConstantTelescope {} typeExpr
  pure {
    name := Kernel.KName.ofName d.name
    params := params
    kind := .syntaxDef
    resultType := result }

/-- Lower a typed LF opaque placeholder to a structural replay constant, when possible. -/
def checkedLFOpaqueConstToKConstant? (defValues : CheckedLFDefinitionValueMap)
    (c : CheckedLFOpaqueConst) : Except String (Option Kernel.LFConstantSchema) := do
  let some result := c.checkedTypeExpr? | pure none
  let locals := c.params.foldl (init := {}) fun locals p => locals.insert p.name.eraseMacroScopes
  let result := unfoldLFDefinitionsInCheckedExpr defValues locals result
  let (params, metas) ← checkedLFBindingsToKMetaVars c.params
  pure <| some {
    name := Kernel.KName.ofName c.name
    params := params
    kind := .opaque
    resultType := (← checkedLFExprToKTerm result metas) }

/-- Lower a checked LF object definition to a structural replay constant. -/
def checkedLFObjectDefToKConstant (defValues : CheckedLFDefinitionValueMap)
    (d : CheckedLFObjectDef) : Except String Kernel.LFConstantSchema := do
  let typeExpr := unfoldLFDefinitionsInCheckedExpr defValues {} d.checkedTypeExpr
  let (params, result) ← checkedLFTypeToKConstantTelescope {} typeExpr
  pure {
    name := Kernel.KName.ofName d.name
    params := params
    kind := .lfDefinition
    resultType := result }

/-- Lower checked LF constants/definitions to structural replay constants. -/
def checkedLFConstantsToK (defValues : CheckedLFDefinitionValueMap)
    (syntaxDefs : Array CheckedLFSyntaxDef) (opaqueConsts : Array CheckedLFOpaqueConst)
    (objectDefs : Array CheckedLFObjectDef) : Except String (Array Kernel.LFConstantSchema) := do
  let mut out := #[]
  for d in syntaxDefs do
    out := out.push (← checkedLFSyntaxDefToKConstant defValues d)
  for c in opaqueConsts do
    if let some k ← checkedLFOpaqueConstToKConstant? defValues c then
      out := out.push k
  for d in objectDefs do
    out := out.push (← checkedLFObjectDefToKConstant defValues d)
  pure out

/-- Lower a checked context zone to a structural replay zone schema. -/
def checkedLFContextZoneToK (z : CheckedLFContextZone) : Kernel.ContextZoneSchema :=
  { name := Kernel.KName.ofName z.name
    sort := .custom z.sortName
    dependsOn := z.dependsOn.toList.map Kernel.KName.ofName }

/-- Lower a checked binder class to a structural replay binder-class schema. -/
def checkedLFBinderClassToK (b : CheckedLFBinderClass) : Kernel.BinderClassSchema :=
  { name := Kernel.KName.ofName b.name
    zone := Kernel.KName.ofName b.zoneName
    boundSort := .custom b.boundSortName
    dependsOn := b.dependsOn.toList.map Kernel.KName.ofName }

/-- Lower a checked conversion plugin to a structural replay plugin schema. -/
def checkedLFConversionPluginToK (p : CheckedLFConversionPlugin) :
    Kernel.ConversionPluginSchema :=
  { name := Kernel.KName.ofName p.name
    trust := p.trust
    supportedSteps := p.supportedSteps.toList }

/-- Build the structural metavariable map for one checked LF rule schema. -/
def checkedLFRuleSchemaMetaMap (r : CheckedLFRuleSchema) : NameMap RawMetaSort := Id.run do
  let mut metas : NameMap RawMetaSort := {}
  for v in r.metavariables do
    let sort := match v.sortHead? with | some h => .custom h.name | none => .arg
    metas := metas.insert v.name.eraseMacroScopes sort
  return metas

/-- Lower a checked LF rule-side condition to structural replay form. -/
def checkedLFSideConditionToK (metas : NameMap RawMetaSort)
    (sc : CheckedLFSideConditionSlot) : Except String Kernel.SideCondition := do
  pure {
    name := Kernel.KName.ofName sc.solver
    args := [← checkedLFExprToKTerm sc.checkedInput metas] }

/-- Lower a checked LF side-condition certificate to structural replay form. -/
def checkedLFSideConditionCertificateToK (metas : NameMap RawMetaSort)
    (cert : CheckedLFSideConditionCertificate) : Except String Kernel.SideConditionCertificate := do
  pure {
    name := Kernel.KName.ofName cert.certificateName
    condition := {
      name := Kernel.KName.ofName cert.solver
      args := [← checkedLFExprToKTerm cert.checkedInput metas] }
    kind := .builtinTrivial
    payload := cert.diagnostic }

/-- Lower a checked LF rule schema to the structural replay shape. -/
def checkedLFRuleSchemaToK (normalize? : Bool) (defValues : CheckedLFDefinitionValueMap)
    (r : CheckedLFRuleSchema) : Except String Kernel.RuleSchema := do
  let baseMetas := checkedLFRuleSchemaMetaMap r
  let locals := r.metavariables.foldl (init := {}) fun locals v =>
    locals.insert v.name.eraseMacroScopes
  let norm := if normalize? then unfoldLFDefinitionsInCheckedExpr defValues locals else id
  let sideConditions ← r.sideConditionSlots.toList.mapM (fun sc =>
    checkedLFSideConditionToK baseMetas { sc with checkedInput := norm sc.checkedInput })
  let certificateSlots ← r.sideConditionSlots.toList.mapM (fun sc => do
    let checkedInput := norm sc.checkedInput
    let condition ← checkedLFSideConditionToK baseMetas { sc with checkedInput := checkedInput }
    pure ({
      name := Kernel.KName.ofName sc.name
      condition := condition } : Kernel.SideConditionCertificateSlot))
  let mut checkedCertificates := []
  for sc in r.sideConditionSlots do
    match sc.certificate? with
    | none => pure ()
    | some cert =>
        checkedCertificates := checkedCertificates ++
          [← checkedLFSideConditionCertificateToK baseMetas
            { cert with checkedInput := norm cert.checkedInput }]
  let ruleMetas ← r.metavariables.toList.mapM fun v => do
    let sort := match v.sortHead? with | some h => .custom h.name | none => .arg
    pure ({
      name := Kernel.KName.ofName v.name
      sort := sort
      zone? := v.zoneName?.map Kernel.KName.ofName
      type? := some (← checkedLFExprToKTerm (norm v.checkedTypeExpr) baseMetas)
      evidence? := (← v.evidence?.mapM fun ev =>
        checkedLFJudgmentExprToKJudgment (norm ev.checkedJudgmentExpr) ev.head baseMetas) } :
        Kernel.RuleMetaVar)
  let mut evidenceMetas := []
  for p in r.premises do
    if !p.isDirectJudgment then
      let sort := match p.head? with
        | some h => if h.kind == .syntaxSort then .custom h.name else .arg
        | none => .arg
      evidenceMetas := evidenceMetas ++ [({
        name := Kernel.KName.ofName p.name
        sort := sort
        type? := some (← checkedLFExprToKTerm (norm p.checkedJudgmentExpr) baseMetas) } :
        Kernel.RuleMetaVar)]
  let mut kernelPremises := []
  for p in r.premises do
    match p.head? with
    | some h =>
        if h.kind == .judgment then
          kernelPremises := kernelPremises ++
            [← checkedLFJudgmentExprToKJudgment (norm p.checkedJudgmentExpr) h baseMetas]
    | none => pure ()
  pure {
    name := Kernel.KName.ofName r.name
    metavariables := ruleMetas ++ evidenceMetas
    premises := kernelPremises
    sideConditions := sideConditions
    sideConditionCertificates := certificateSlots
    checkedSideConditionCertificates := checkedCertificates
    conclusionStmt :=
      (← checkedLFJudgmentExprToKJudgment (norm r.checkedConclusionExpr) r.conclusionHead
        baseMetas) }

/-- Lower checked LF rule schemas to structural replay schemas. -/
def checkedLFRuleSchemasToK (normalize? : Bool) (defValues : CheckedLFDefinitionValueMap)
    (rules : Array CheckedLFRuleSchema) : Except String (Array Kernel.RuleSchema) := do
  let mut out := #[]
  for r in rules do
    out := out.push (← checkedLFRuleSchemaToK normalize? defValues r)
  pure out

/-- Find the unique checked context zone whose entry sort matches `sortName`, if any. -/
def uniqueZoneForSort? (zones : Array CheckedLFContextZone) (sortName : Name) : Option Name :=
  let candidates := zones.filter (fun z => z.sortName == sortName.eraseMacroScopes)
  if candidates.size == 1 then candidates[0]!.name else none

/-- Find the unique binder class for a sort/zone pair, if any. -/
def uniqueBinderClassFor? (classes : Array CheckedLFBinderClass) (sortName zoneName : Name) :
  Option Name :=
  let sortName := sortName.eraseMacroScopes
  let zoneName := zoneName.eraseMacroScopes
  let candidates := classes.filter (fun b => b.boundSortName == sortName && b.zoneName == zoneName)
  if candidates.size == 1 then candidates[0]!.name else none

/-- Extract a typed LF local schema from a checked metadata binder. -/
def checkedLFTypedLocalOfBinding (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (evidence? : Option CheckedLFRuleParamEvidence) (b : CheckedLFBinding) : CheckedLFTypedLocal :=
  let sortHead? := b.head?.filter (fun h => h.kind == .syntaxSort)
  let zoneName? := sortHead?.bind (fun h => uniqueZoneForSort? zones h.name)
  let binderClass? := match sortHead?, zoneName? with
    | some h, some z => uniqueBinderClassFor? classes h.name z
    | _, _ => none
  { name := b.name
    typeExpr := b.typeExpr
    checkedTypeExpr := b.checkedTypeExpr
    sortHead? := sortHead?
    zoneName? := zoneName?
    binderClass? := binderClass?
    evidence? := evidence? }

/-- Extract multi-zone locals from a rule metavariable telescope. -/
def checkedLFMultiContextOfLocals (locals : Array CheckedLFTypedLocal) : CheckedLFMultiContext :=
  { locals := locals.filterMap fun v =>
      match v.zoneName? with
      | some zoneName => some {
          name := v.name
          zoneName := zoneName
          binderClass? := v.binderClass?
          typeExpr := v.typeExpr
          checkedTypeExpr := v.checkedTypeExpr }
      | none => none }

/-- Run the current built-in executable side-condition hooks for one checked side condition.

The Phase-3 hook API is deliberately tiny: the built-in trivial hook accepts any side
condition that already passed LF metadata validation and records a provenance certificate.
Opaque solver names return no certificate. -/
def checkLFSideCondition? (ruleName : Name) (sc : CheckedLFRuleSideCondition) :
    Option CheckedLFSideConditionCertificate :=
  match classifySideConditionHook sc.solver with
  | .opaque => none
  | .builtinTrivial =>
      some {
        name := sc.name
        solver := sc.solver.eraseMacroScopes
        input := sc.input
        checkedInput := sc.checkedInput
        inputHead? := sc.head?
        kind := .builtinTrivial
        certificateName := .str (.str ruleName.eraseMacroScopes "side_condition") (
          toString sc.name.eraseMacroScopes)
        diagnostic := "accepted unconditionally by built-in trivial side-condition hook" }

/-- Derive a Phase-2/3/4 LF rule schema from a checked LF rule artifact. -/
def checkedLFRuleSchemaOfRule (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (r : CheckedLFRule) : CheckedLFRuleSchema :=
  let evidenceFor (paramName : Name) : Option CheckedLFRuleParamEvidence :=
    r.paramEvidences.find? (fun ev => ev.paramName == paramName.eraseMacroScopes)
  let metavariables := r.params.map (fun p =>
    checkedLFTypedLocalOfBinding zones classes (evidenceFor p.name) p)
  { name := r.name
    metavariables := metavariables
    multiContext := checkedLFMultiContextOfLocals metavariables
    premises := r.premises.map fun p =>
      { name := p.name
        head? := p.head?
        checkedJudgmentExpr := p.checkedJudgmentExpr }
    sideConditionSlots := r.sideConditions.map fun sc =>
      let cert? := checkLFSideCondition? r.name sc
      { name := sc.name
        solver := sc.solver
        checkedInput := sc.checkedInput
        inputHead? := sc.head?
        certificate? := cert? }
    checkedConclusionExpr := r.checkedConclusionExpr
    conclusionHead := r.conclusionHead }

/-- Derive all Phase-2/3/4 LF rule schemas from checked LF rule metadata. -/
def checkedLFRuleSchemasOfRules (zones : Array CheckedLFContextZone) (classes :
  Array CheckedLFBinderClass)
    (rules : Array CheckedLFRule) : Array CheckedLFRuleSchema :=
  rules.map (checkedLFRuleSchemaOfRule zones classes)

/-- Collect checked side-condition certificates from derived rule schemas. -/
def checkedLFSideConditionCertificatesOfSchemas (rules : Array CheckedLFRuleSchema) :
    Array CheckedLFSideConditionCertificate := Id.run do
  let mut out := #[]
  for r in rules do
    for sc in r.sideConditionSlots do
      if let some cert := sc.certificate? then
        out := out.push cert
  return out

/-- Explicit checked LF type of a `syntax_def` family. -/
def checkedLFSyntaxDefTypeExpr (d : CheckedLFSyntaxDef) : CheckedLFExpr :=
  d.params.foldr (init := checkedLFTypeOfLevel d.resultLevel) fun b acc =>
    .arrow (some b.name) b.checkedTypeExpr acc

/-- Checked lambda value of a `syntax_def`, when it has a body. -/
def checkedLFSyntaxDefValue? (d : CheckedLFSyntaxDef) : Option CheckedLFExpr :=
  d.checkedValue?.map fun value =>
    if d.params.isEmpty then value else .lam (d.params.map (·.name)) value

/-- Checked LF object-definition values keyed by definition name. -/
def checkedLFObjectDefinitionValues (defs : Array CheckedLFObjectDef) :
    CheckedLFDefinitionValueMap :=
  defs.foldl (init := {}) fun values d =>
    values.insert d.name.eraseMacroScopes d.checkedValue

/-- Checked LF-definition values keyed by definition name. -/
def checkedLFDefinitionValues (syntaxDefs : Array CheckedLFSyntaxDef)
    (defs : Array CheckedLFObjectDef) : CheckedLFDefinitionValueMap := Id.run do
  let mut values : CheckedLFDefinitionValueMap := {}
  for d in syntaxDefs do
    if let some value := checkedLFSyntaxDefValue? d then
      values := values.insert d.name.eraseMacroScopes value
  for (n, value) in (checkedLFObjectDefinitionValues defs).toList do
    values := values.insert n value
  return values

/-- Structural checked external-certificate entries exposed by checked theorem artifacts. -/
def kernelLFCertificateEntriesOfTheoremsToK (theorems : Array CheckedLFJudgmentTheorem) :
    List Kernel.KernelLFCertificateEntry := Id.run do
  let mut out := []
  for t in theorems do
    match t.structuralKernelDerivation? with
    | some (.certificate name stmt certificateName) =>
        out := out ++ [{ name := name, statement := stmt, certificateName := certificateName }]
    | _ => pure ()
  return out

/-- Free-local set for all binders of a checked LF theorem. -/
def theoremBinderFreeLocals (t : CheckedLFJudgmentTheorem) : NameSet :=
  t.binders.foldl (init := {}) fun locals b => locals.insert b.name.eraseMacroScopes

/-- Lower a checked LF theorem statement using theorem binders as replay-context locals. -/
def checkedLFJudgmentTheoremStatementToK (t : CheckedLFJudgmentTheorem) :
    Except String Kernel.Judgment :=
  checkedLFJudgmentExprToKJudgment t.checkedJudgmentExpr t.judgmentHead {}
    (theoremBinderFreeLocals t)

/-- Extract structural local theorem assumptions from a checked LF theorem. -/
def kernelLFLocalAssumptionEntriesOfTheoremToK (normalize? : Bool)
    (defValues : CheckedLFDefinitionValueMap) (t : CheckedLFJudgmentTheorem) :
    Except String (List Kernel.KernelLFTheoremEntry) := do
  let freeLocals := theoremBinderFreeLocals t
  let locals := freeLocals
  let norm := if normalize? then unfoldLFDefinitionsInCheckedExpr defValues locals else id
  let mut out := []
  for b in t.binders do
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          out := out ++ [{
            name := Kernel.KName.ofName b.name
            statement :=
              (← checkedLFJudgmentExprToKJudgment (norm b.checkedTypeExpr) head {} freeLocals) }]
    | none => pure ()
  pure out

/-- Lower a checked LF theorem to the structural rule schema used by theorem references. -/
def kernelLFRuleSchemaOfTheoremToK (normalize? : Bool)
    (defValues : CheckedLFDefinitionValueMap) (t : CheckedLFJudgmentTheorem) :
    Except String Kernel.RuleSchema := do
  let theoremMetas : NameMap RawMetaSort := Id.run do
    let mut metas : NameMap RawMetaSort := {}
    for b in t.binders do
      match b.head? with
      | some head =>
          if head.kind != .judgment then
            let sort := if head.kind == .syntaxSort then .custom head.name else .arg
            metas := metas.insert b.name.eraseMacroScopes sort
      | none => metas := metas.insert b.name.eraseMacroScopes .arg
    return metas
  let locals := t.binders.foldl (init := {}) fun locals b => locals.insert b.name.eraseMacroScopes
  let norm := if normalize? then unfoldLFDefinitionsInCheckedExpr defValues locals else id
  let mut metavariables := []
  for b in t.binders do
    match b.head? with
    | some head =>
        if head.kind != .judgment then
          let sort := if head.kind == .syntaxSort then .custom head.name else .arg
          metavariables := metavariables ++ [({
            name := Kernel.KName.ofName b.name
            sort := sort
            type? := some (← checkedLFExprToKTerm (norm b.checkedTypeExpr) theoremMetas) } :
            Kernel.RuleMetaVar)]
    | none =>
        metavariables := metavariables ++ [({
          name := Kernel.KName.ofName b.name
          sort := .arg
          type? := some (← checkedLFExprToKTerm (norm b.checkedTypeExpr) theoremMetas) } :
          Kernel.RuleMetaVar)]
  let mut premises := []
  for b in t.binders do
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          premises := premises ++
            [← checkedLFJudgmentExprToKJudgment (norm b.checkedTypeExpr) head theoremMetas]
    | none => pure ()
  pure {
    name := Kernel.KName.ofName (lfJudgmentTheoremKernelRuleName t.name)
    metavariables := metavariables
    premises := premises
    conclusionStmt :=
      (← checkedLFJudgmentExprToKJudgment (norm t.checkedJudgmentExpr) t.judgmentHead
        theoremMetas) }

/-- Lower checked LF theorem schemas to structural replay rule schemas. -/
def kernelLFRuleSchemasOfTheoremsToK (normalize? : Bool)
    (defValues : CheckedLFDefinitionValueMap) (theorems : Array CheckedLFJudgmentTheorem) :
    Except String (Array Kernel.RuleSchema) := do
  let mut out := #[]
  for t in theorems do
    out := out.push (← kernelLFRuleSchemaOfTheoremToK normalize? defValues t)
  pure out

/-- Build a structural replay context from checked theorem artifacts. -/
def kernelLFReplayContextOfTheoremsToK (theorems : Array CheckedLFJudgmentTheorem) :
    Except String Kernel.KernelLFCheckContext := do
  let mut replayCtx : Kernel.KernelLFCheckContext := {
    certificates := kernelLFCertificateEntriesOfTheoremsToK theorems }
  for prior in theorems do
    if prior.binders.isEmpty then
      if prior.checkedStructuralKernelDerivation?.isSome || prior.derivation?.isSome then
        let statement ←
          match prior.checkedStructuralKernelDerivation? with
          | some checkedReplay => pure checkedReplay.statement
          | none => checkedLFJudgmentTheoremStatementToK prior
        replayCtx := { replayCtx with
          theorems := replayCtx.theorems ++ [{
            name := Kernel.KName.ofName prior.name
            statement := statement }] }
  pure replayCtx

/-- Lower checked LF artifacts to a structural compact replay signature. -/
def checkedSignatureToKSignature (theoryName : Name) (lfSyntaxDefs : Array CheckedLFSyntaxDef)
    (lfOpaqueConsts : Array CheckedLFOpaqueConst) (lfContextZones : Array CheckedLFContextZone)
    (lfBinderClasses : Array CheckedLFBinderClass)
    (lfConversionPlugins : Array CheckedLFConversionPlugin)
    (lfRuleSchemas : Array CheckedLFRuleSchema) (lfObjectDefs : Array CheckedLFObjectDef)
    (lfJudgmentTheorems : Array CheckedLFJudgmentTheorem) (normalizeRules? : Bool := false) :
    Except String Kernel.Signature := do
  let lfCheckedDefValues := checkedLFDefinitionValues lfSyntaxDefs lfObjectDefs
  let constants ← checkedLFConstantsToK lfCheckedDefValues lfSyntaxDefs lfOpaqueConsts lfObjectDefs
  let rules ← checkedLFRuleSchemasToK normalizeRules? lfCheckedDefValues lfRuleSchemas
  let theoremRules ←
    kernelLFRuleSchemasOfTheoremsToK normalizeRules? lfCheckedDefValues lfJudgmentTheorems
  pure {
    name := Kernel.KName.ofName theoryName
    constants := constants.toList
    contextZones := lfContextZones.toList.map checkedLFContextZoneToK
    binderClasses := lfBinderClasses.toList.map checkedLFBinderClassToK
    conversionPlugins := lfConversionPlugins.toList.map checkedLFConversionPluginToK
    rules := (rules ++ theoremRules).toList }

/-- Build a structural replay signature from a compiled cache's retained checked artifacts. -/
def compiledLFCheckCacheStructuralSignature (cache : CompiledLFCheckCache)
    (normalizeRules? : Bool := false) : Except String Kernel.Signature :=
  checkedSignatureToKSignature cache.theoryName cache.lfSyntaxDefs cache.lfOpaqueConsts
    cache.lfContextZones cache.lfBinderClasses cache.lfConversionPlugins cache.checkedRuleSchemas
    cache.lfObjectDefs cache.lfJudgmentTheorems normalizeRules?

/-- Lift structural-kernel construction failures into command elaboration errors. -/
def liftStructuralKernelExcept (label : String) : Except String α → CoreM α
  | .ok value => pure value
  | .error err => throwError "structural kernel construction failed for {label}: {err}"

/-- Lower a checked judgment expression to a structural-kernel judgment. -/
def lfJudgmentObjExprToKJudgment (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (e : ObjExpr) (locals : NameSet := {}) : CoreM Kernel.Judgment := do
  let judgmentArities : NameMap Nat := sig.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let head ← checkRuleJudgmentHead sig judgmentArities ownerName ownerKind e
  let checked ← resolveLFExpr sig globalHeads locals ownerKind ownerName
    "structural kernel statement" e
  liftStructuralKernelExcept s!"{ownerKind} '{ownerName}' statement" <|
    checkedLFJudgmentExprToKJudgment checked head {} locals

/-- Lower a checked proof-context term to a structural-kernel term. -/
def lfObjExprToKTerm (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (ownerKind : String)
    (ownerName : Name) (where_ : String) (e : ObjExpr) (locals : NameSet := {}) :
    CoreM Kernel.KTerm := do
  let checked ← resolveLFExpr sig globalHeads locals ownerKind ownerName where_ e
  liftStructuralKernelExcept s!"{ownerKind} '{ownerName}' {where_}" <|
    checkedLFExprToKTerm checked {} locals

/-- Find a structural replay rule by name in a source-order signature. -/
def findStructuralRule? (signature : Kernel.Signature) (name : Kernel.KName) :
    Option Kernel.RuleSchema :=
  signature.rules.find? (fun r => r.name == name)

/-- Build a structural scoped-instantiation entry from a checked proof argument. -/
def structuralScopedEntryOfArg (processed : List Kernel.ScopedInstantiationEntry)
    (v : Kernel.RuleMetaVar) (value : Kernel.KTerm) :
    Except String Kernel.ScopedInstantiationEntry := do
  let prefixInst := Kernel.ScopedInstantiation.entriesAsInstantiation processed
  let type? ← Kernel.ScopedInstantiation.instantiateTermOption prefixInst v.type?
  let entryBase : Kernel.ScopedInstantiationEntry := {
    name := v.name
    sort := v.sort
    zone? := v.zone?
    type? := type?
    value := value }
  let withCurrent :=
    Kernel.ScopedInstantiation.entriesAsInstantiation (processed ++ [entryBase])
  let evidence? ← Kernel.ScopedInstantiation.instantiateJudgmentOption withCurrent v.evidence?
  pure { entryBase with evidence? := evidence? }

mutual
  /-- Lower a rule or theorem-rule application to a structural derivation node. -/
  partial def lowerLFRuleApplicationToStructuralKernel (sig : HLSignature)
      (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
      (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name)
      (unfoldDefs : Bool) (signature : Kernel.Signature) (ruleName : Kernel.KName)
      (stmt : ObjExpr) (ruleArgs : Array ObjExpr) (premises : Array CheckedLFDerivation)
      (sideConditionCertificateNames : Array Name) : CoreM Kernel.KernelLFDerivation := do
    let r ←
      match findStructuralRule? signature ruleName with
      | some r => pure r
      | none => throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' \
          lowers unknown structural LF rule '{ruleName}'"
    if ruleArgs.size != r.metavariables.length then
      throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
        '{ruleName}' with {ruleArgs.size} scoped instantiation entry/entries, expected \
          {r.metavariables.length}"
    if premises.size != r.premises.length then
      throwError "judgment_theorem '{theoremName}' in type theory '{sig.name}' lowers rule \
        '{ruleName}' with {premises.size} premise derivation(s), expected {r.premises.length}"
    let mut entries : List Kernel.ScopedInstantiationEntry := []
    for v in r.metavariables, arg in ruleArgs do
      let kernelArgExpr :=
        if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames arg
        else eraseObjExprScopes arg
      let value ← lfObjExprToKTerm sig globalHeads "kernel-facing structural derivation"
        theoremName s!"argument for '{v.name}'" kernelArgExpr localNames
      let entry ← liftStructuralKernelExcept
        s!"judgment_theorem '{theoremName}' argument for '{v.name}'" <|
          structuralScopedEntryOfArg entries v value
      entries := entries ++ [entry]
    let inst : Kernel.ScopedInstantiation := { entries := entries }
    let stmtExpr :=
      if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
      else eraseObjExprScopes stmt
    let kernelStmt ← lfJudgmentObjExprToKJudgment sig globalHeads "rule application"
      theoremName stmtExpr localNames
    let mut loweredPremises := []
    for premiseDeriv in premises do
      loweredPremises := loweredPremises ++
        [← lowerLFDerivationToStructuralKernelWithMode sig globalHeads defValues localNames
          theoremName unfoldDefs signature premiseDeriv]
    pure (.ruleApp ruleName kernelStmt inst loweredPremises
      (sideConditionCertificateNames.toList.map Kernel.KName.ofName))

  /-- Lower a shallow checked LF derivation directly to the structural kernel. -/
  partial def lowerLFDerivationToStructuralKernelWithMode (sig : HLSignature)
      (globalHeads : NameMap (CheckedLFHeadKind × Option Nat))
      (defValues : LFDefinitionValueMap) (localNames : NameSet) (theoremName : Name)
      (unfoldDefs : Bool) (signature : Kernel.Signature) :
      CheckedLFDerivation → CoreM Kernel.KernelLFDerivation
    | .localAssumption name stmt => do
        let stmtExpr :=
          if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
          else eraseObjExprScopes stmt
        let kernelStmt ← lfJudgmentObjExprToKJudgment sig globalHeads "local theorem assumption"
          theoremName stmtExpr localNames
        pure (.assumption (Kernel.KName.ofName name) kernelStmt)
    | .theoremRef name stmt args premises => do
        if args.isEmpty && premises.isEmpty then
          let stmtExpr :=
            if unfoldDefs then unfoldLFDefinitionsInExprWithLocals defValues localNames stmt
            else eraseObjExprScopes stmt
          let kernelStmt ← lfJudgmentObjExprToKJudgment sig globalHeads "theorem reference"
            theoremName stmtExpr localNames
          pure (.theoremRef (Kernel.KName.ofName name) kernelStmt)
        else
          lowerLFRuleApplicationToStructuralKernel sig globalHeads defValues localNames
            theoremName unfoldDefs signature
            (Kernel.KName.ofName (lfJudgmentTheoremKernelRuleName name)) stmt args premises #[]
    | .ruleApp ruleName stmt ruleArgs premises certs =>
        lowerLFRuleApplicationToStructuralKernel sig globalHeads defValues localNames theoremName
          unfoldDefs signature (Kernel.KName.ofName ruleName) stmt ruleArgs premises certs
end

/-- Lower a shallow checked LF derivation through compact mode, falling back to unfolded mode. -/
def lowerLFDerivationToStructuralKernel (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (defValues : LFDefinitionValueMap)
    (localNames : NameSet) (theoremName : Name) (signature : Kernel.Signature)
    (signatureExpanded : Kernel.Signature) (derivation : CheckedLFDerivation) :
    CoreM (Kernel.KernelLFDerivation × Bool) := do
  try
    let d ← lowerLFDerivationToStructuralKernelWithMode sig globalHeads defValues localNames
      theoremName false signature derivation
    pure (d, false)
  catch _ =>
    let d ← lowerLFDerivationToStructuralKernelWithMode sig globalHeads defValues localNames
      theoremName true signatureExpanded derivation
    pure (d, true)

/-- Check a directly lowered structural-kernel replay artifact. -/
def checkStructuralKernelReplay (label : String) (signature : Kernel.Signature)
    (context : Kernel.KernelLFCheckContext) (statement : Kernel.Judgment)
    (derivation : Kernel.KernelLFDerivation) : CoreM Kernel.CheckedKernelLFDerivation := do
  match Kernel.CheckedKernelLFDerivation.ofReplay signature context statement derivation with
  | .ok checked => pure checked
  | .error err =>
      throwError "Phase-5c structural kernel replay failed for {label}: {err}"

/-- Add checked structural-kernel replay validation to one incrementally checked LF theorem. -/
def validateIncrementalLFTheoremKernelReplay (sig : HLSignature) (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let some shallowDeriv := t.derivation?
    | pure t
  let lfCheckedDefValues := checkedLFDefinitionValues checked.lfSyntaxDefs checked.lfObjectDefs
  let lfKernelDefValues :=
    lfDefinitionValueMapFromCheckedDefs checked.lfSyntaxDefs checked.lfObjectDefs
  let structuralSig ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' compact signature" <|
      checkedSignatureToKSignature sig.name checked.lfSyntaxDefs checked.lfOpaqueConsts
      checked.lfContextZones checked.lfBinderClasses checked.lfConversionPlugins
      checked.lfRuleSchemas checked.lfObjectDefs checked.lfJudgmentTheorems
  let structuralReplayCtx ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' compact replay context" <|
      kernelLFReplayContextOfTheoremsToK checked.lfJudgmentTheorems
  let structuralAssumptions ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' compact local assumptions" <|
      kernelLFLocalAssumptionEntriesOfTheoremToK false lfCheckedDefValues t
  let structuralDeriv ← lowerLFDerivationToStructuralKernelWithMode sig (lfGlobalHeadInfo sig)
    lfKernelDefValues (theoremBinderFreeLocals t) t.name false structuralSig shallowDeriv
  let structuralStmt := Kernel.KernelLFDerivation.statement structuralDeriv
  let structuralLocalReplayCtx := { structuralReplayCtx with
    localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
    assumptions := structuralAssumptions }
  let (structuralDeriv, _structuralStmt, checkedStructuralReplay) ←
    try
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' compact replay" structuralSig structuralLocalReplayCtx
        structuralStmt structuralDeriv
      pure (structuralDeriv, structuralStmt, checkedStructuralReplay)
    catch _ =>
      let structuralSigExpanded ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' expanded signature" <|
          checkedSignatureToKSignature sig.name checked.lfSyntaxDefs checked.lfOpaqueConsts
            checked.lfContextZones checked.lfBinderClasses checked.lfConversionPlugins
            checked.lfRuleSchemas checked.lfObjectDefs checked.lfJudgmentTheorems true
      let structuralExpandedAssumptions ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' expanded local assumptions" <|
          kernelLFLocalAssumptionEntriesOfTheoremToK true lfCheckedDefValues t
      let structuralDerivExpanded ← lowerLFDerivationToStructuralKernelWithMode sig
        (lfGlobalHeadInfo sig) lfKernelDefValues (theoremBinderFreeLocals t) t.name true
        structuralSigExpanded shallowDeriv
      let structuralStmtExpanded := Kernel.KernelLFDerivation.statement structuralDerivExpanded
      let structuralExpandedReplayCtx := { structuralReplayCtx with
        localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
        assumptions := structuralExpandedAssumptions }
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' expanded replay" structuralSigExpanded
        structuralExpandedReplayCtx structuralStmtExpanded structuralDerivExpanded
      pure (structuralDerivExpanded, structuralStmtExpanded, checkedStructuralReplay)
  pure { t with
    structuralKernelDerivation? := some structuralDeriv
    checkedStructuralKernelDerivation? := some checkedStructuralReplay }

/-- Add checked structural-kernel replay validation to one incrementally checked LF theorem,
    reusing a compiled checked-theory replay cache. -/
def validateIncrementalLFTheoremKernelReplayWithCache (cache : CompiledLFCheckCache)
    (t : CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let some shallowDeriv := t.derivation?
    | pure t
  let lfKernelDefValues : LFDefinitionValueMap := Id.run do
    let mut values := cache.knownLFDefValues
    for (n, value) in cache.knownLFSyntaxDefValues.toList do
      values := values.insert n value
    return values
  let structuralSig ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' cached compact signature" <|
      compiledLFCheckCacheStructuralSignature cache
  let structuralReplayCtx := cache.structuralKernelReplayBase
  let structuralAssumptions ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' compact cached local assumptions" <|
      kernelLFLocalAssumptionEntriesOfTheoremToK false cache.checkedLFDefValues t
  let structuralDeriv ← lowerLFDerivationToStructuralKernelWithMode cache.checkedHL
    cache.globalHeads lfKernelDefValues (theoremBinderFreeLocals t) t.name false structuralSig
    shallowDeriv
  let structuralStmt := Kernel.KernelLFDerivation.statement structuralDeriv
  let structuralLocalReplayCtx := { structuralReplayCtx with
    localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
    assumptions := structuralAssumptions }
  let (structuralDeriv, _structuralStmt, checkedStructuralReplay) ←
    try
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' compact cached replay" structuralSig
        structuralLocalReplayCtx structuralStmt structuralDeriv
      pure (structuralDeriv, structuralStmt, checkedStructuralReplay)
    catch _ =>
      let structuralSigExpanded ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' cached expanded signature" <|
          compiledLFCheckCacheStructuralSignature cache true
      let structuralExpandedAssumptions ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' expanded cached local assumptions" <|
          kernelLFLocalAssumptionEntriesOfTheoremToK true cache.checkedLFDefValues t
      let structuralDerivExpanded ← lowerLFDerivationToStructuralKernelWithMode cache.checkedHL
        cache.globalHeads lfKernelDefValues (theoremBinderFreeLocals t) t.name true
        structuralSigExpanded shallowDeriv
      let structuralStmtExpanded := Kernel.KernelLFDerivation.statement structuralDerivExpanded
      let structuralExpandedReplayCtx := { structuralReplayCtx with
        localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
        assumptions := structuralExpandedAssumptions }
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' expanded cached replay" structuralSigExpanded
        structuralExpandedReplayCtx structuralStmtExpanded structuralDerivExpanded
      pure (structuralDerivExpanded, structuralStmtExpanded, checkedStructuralReplay)
  pure { t with
    structuralKernelDerivation? := some structuralDeriv
    checkedStructuralKernelDerivation? := some checkedStructuralReplay }


/-- Convert a checked LF binding back to the high-level declaration shape used for checking
new extension deltas against an already checked baseline. -/
def checkedLFBindingToHLBinding (b : CheckedLFBinding) : HLBinding :=
  { name := b.name, typeExpr := b.typeExpr, visibility := b.visibility }

/-- Convert a checked syntax-sort artifact to a high-level declaration. -/
def checkedLFSyntaxSortToHLDecl (s : CheckedLFSyntaxSort) : SyntaxSortDecl :=
  { name := s.name
    params := s.params.map checkedLFBindingToHLBinding
    resultLevel := s.resultLevel }

/-- Convert a checked syntax-abbreviation artifact to a high-level declaration. -/
def checkedLFSyntaxAbbrevToHLDecl (a : CheckedLFSyntaxAbbrev) : SyntaxAbbrevDecl :=
  { name := a.name, params := a.params.map checkedLFBindingToHLBinding, value := a.value }

/-- Convert a checked syntax-definition artifact to a high-level declaration. -/
def checkedLFSyntaxDefToHLDecl (d : CheckedLFSyntaxDef) : SyntaxDefDecl :=
  { name := d.name
    params := d.params.map checkedLFBindingToHLBinding
    resultLevel := d.resultLevel
    value? := d.value? }

/-- Convert a checked judgment-abbreviation artifact to a high-level declaration. -/
def checkedLFJudgmentAbbrevToHLDecl (a : CheckedLFJudgmentAbbrev) : JudgmentAbbrevDecl :=
  { name := a.name, params := a.params.map checkedLFBindingToHLBinding, value := a.value }

/-- Convert a checked context-zone artifact to a high-level declaration. -/
def checkedLFContextZoneToHLDecl (z : CheckedLFContextZone) : ContextZoneDecl :=
  { name := z.name, sortName := z.sortName, dependsOn := z.dependsOn }

/-- Convert a checked binder-class artifact to a high-level declaration. -/
def checkedLFBinderClassToHLDecl (b : CheckedLFBinderClass) : BinderClassDecl :=
  { name := b.name
    boundSortName := b.boundSortName
    zoneName := b.zoneName
    dependsOn := b.dependsOn }

/-- Convert a checked judgment artifact to a high-level declaration. -/
def checkedLFJudgmentToHLDecl (j : CheckedLFJudgment) : JudgmentDecl :=
  { name := j.name, params := j.params.map checkedLFBindingToHLBinding }

/-- Convert a checked LF opaque artifact to a high-level declaration. -/
def checkedLFOpaqueConstToHLDecl (o : CheckedLFOpaqueConst) : LFOpaqueConstDecl :=
  { name := o.name
    arity? := o.arity?
    params := o.params.map checkedLFBindingToHLBinding
    typeExpr? := o.typeExpr? }

/-- Convert a checked side-condition solver artifact to a high-level declaration. -/
def checkedLFSideConditionSolverToHLDecl (s : CheckedLFSideConditionSolver) :
    SideConditionSolverDecl :=
  { name := s.name }

/-- Convert a checked conversion-plugin artifact to a high-level declaration. -/
def checkedLFConversionPluginToHLDecl (p : CheckedLFConversionPlugin) : ConversionPluginDecl :=
  { name := p.name, trust := p.trust, supportedSteps := p.supportedSteps }

/-- Convert a checked LF rule artifact to a high-level declaration. -/
def checkedLFRuleToHLDecl (r : CheckedLFRule) : RuleDecl :=
  { name := r.name
    params := r.params.map checkedLFBindingToHLBinding
    premises := r.premises.map fun p =>
      ({ name := p.name, judgmentExpr := p.judgmentExpr } : RulePremiseDecl)
    sideConditions := r.sideConditions.map fun sc =>
      ({ name := sc.name, solver := sc.solver, input := sc.input } : RuleSideConditionDecl)
    paramEvidences := r.paramEvidences.map fun ev =>
      ({ name := ev.name, paramName := ev.paramName, judgmentExpr := ev.judgmentExpr } :
        RuleParamEvidenceDecl)
    conclusionExpr := r.conclusionExpr }

/-- Convert a checked LF object definition to a high-level declaration. -/
def checkedLFObjectDefToHLDecl (d : CheckedLFObjectDef) : LFObjectDefDecl :=
  { name := d.name, typeExpr := d.typeExpr, value := d.value }

/-- Convert a checked LF judgment theorem to a high-level declaration. -/
def checkedLFJudgmentTheoremToHLDecl (t : CheckedLFJudgmentTheorem) :
    LFJudgmentTheoremDecl :=
  { name := t.name
    binders := t.binders.map checkedLFBindingToHLBinding
    judgmentExpr := t.judgmentExpr
    proof := t.proof }

/-- Reconstruct a flat high-level signature from checked artifacts for incremental checking.
The source baseline contributes non-checking metadata such as object macros. -/
def checkedSignatureToHLSignature (sourceBase : HLSignature) (checked : CheckedSignature) :
    HLSignature :=
  { name := checked.name
    parents := #[]
    levelParams := checked.levelParams
    syntaxSorts := checked.lfSyntaxSorts.map checkedLFSyntaxSortToHLDecl
    syntaxAbbrevs := checked.lfSyntaxAbbrevs.map checkedLFSyntaxAbbrevToHLDecl
    syntaxDefs := checked.lfSyntaxDefs.map checkedLFSyntaxDefToHLDecl
    judgmentAbbrevs := checked.lfJudgmentAbbrevs.map checkedLFJudgmentAbbrevToHLDecl
    syntaxSortRoles := checked.lfSyntaxSortRoles
    contextZones := checked.lfContextZones.map checkedLFContextZoneToHLDecl
    binderClasses := checked.lfBinderClasses.map checkedLFBinderClassToHLDecl
    judgments := checked.lfJudgments.map checkedLFJudgmentToHLDecl
    judgmentRoles := checked.lfJudgmentRoles
    rules := checked.lfRules.map checkedLFRuleToHLDecl
    ruleRoles := checked.lfRuleRoles
    rewriteRelations := checked.lfRewriteRelations
    rewriteSymmetries := checked.lfRewriteSymmetries
    rewriteCongruences := checked.lfRewriteCongruences
    transportRules := checked.lfTransportRules
    transportPositions := checked.lfTransportPositions
    sideConditionSolvers :=
      checked.lfSideConditionSolvers.map checkedLFSideConditionSolverToHLDecl
    conversionPlugins := checked.lfConversionPlugins.map checkedLFConversionPluginToHLDecl
    lfOpaqueConsts := checked.lfOpaqueConsts.map checkedLFOpaqueConstToHLDecl
    modelVisibilities := checked.modelVisibilities
    modelSections := checked.modelSections
    modelSectionMemberships := checked.modelSectionMemberships
    lfObjectDefs := checked.lfObjectDefs.map checkedLFObjectDefToHLDecl
    lfJudgmentTheorems := checked.lfJudgmentTheorems.map checkedLFJudgmentTheoremToHLDecl
    macros := sourceBase.macros
    roles := sourceBase.roles }

/-- Reconstruct the high-level checking signature for a checked signature.

Callers should prefer `getCheckedHLSignature?` when available; this function is the fallback for
older imports or manually constructed checked artifacts. -/
def checkedSignatureIncrementalHLSignature (sourceBase : HLSignature)
    (checked : CheckedSignature) : HLSignature :=
  checkedSignatureToHLSignature sourceBase checked

/-- Whether a cached/reconstructed checked high-level signature has the same declaration counts as
one checked signature. This is only a sanity guard before using the checked-HL cache; the checked
signature remains authoritative. -/
def checkedHLSignatureMatchesChecked (checkedHL : HLSignature)
    (checked : CheckedSignature) : Bool :=
  checkedHL.name.eraseMacroScopes == checked.name.eraseMacroScopes &&
    checkedHL.levelParams.size == checked.levelParams.size &&
    checkedHL.syntaxSorts.size == checked.lfSyntaxSorts.size &&
    checkedHL.syntaxAbbrevs.size == checked.lfSyntaxAbbrevs.size &&
    checkedHL.syntaxDefs.size == checked.lfSyntaxDefs.size &&
    checkedHL.judgmentAbbrevs.size == checked.lfJudgmentAbbrevs.size &&
    checkedHL.contextZones.size == checked.lfContextZones.size &&
    checkedHL.binderClasses.size == checked.lfBinderClasses.size &&
    checkedHL.judgments.size == checked.lfJudgments.size &&
    checkedHL.rules.size == checked.lfRules.size &&
    checkedHL.lfOpaqueConsts.size == checked.lfOpaqueConsts.size &&
    checkedHL.lfObjectDefs.size == checked.lfObjectDefs.size &&
    checkedHL.lfJudgmentTheorems.size == checked.lfJudgmentTheorems.size

/-- Recover the flattened checked high-level signature to store in a compiled LF cache. -/
def checkedHLSignatureForCompiledCache (theoryName : Name) (checked : CheckedSignature) :
    CoreM HLSignature := do
  match ← getCheckedHLSignature? theoryName with
  | some checkedHL =>
      if checkedHLSignatureMatchesChecked checkedHL checked then
        pure checkedHL
      else
        match ← getTheory? theoryName with
        | some sourceSig =>
            let sourceBase ← flattenSignature sourceSig
            pure (checkedSignatureIncrementalHLSignature sourceBase checked)
        | none => pure (checkedSignatureIncrementalHLSignature { name := checked.name } checked)
  | none =>
      match ← getTheory? theoryName with
      | some sourceSig =>
          let sourceBase ← flattenSignature sourceSig
          pure (checkedSignatureIncrementalHLSignature sourceBase checked)
      | none => pure (checkedSignatureIncrementalHLSignature { name := checked.name } checked)

/-- Build a compiled LF checking cache from a checked high-level signature and checked artifacts. -/
def mkCompiledLFCheckCacheFromHL (checkedHL : HLSignature) (checked : CheckedSignature) :
    CoreM CompiledLFCheckCache := do
  let checkedLFDefValues := checkedLFDefinitionValues checked.lfSyntaxDefs checked.lfObjectDefs
  let structuralKernelReplayBase ← liftStructuralKernelExcept
    s!"compiled cache for '{checked.name}' structural replay context" <|
      kernelLFReplayContextOfTheoremsToK checked.lfJudgmentTheorems
  pure {
    theoryName := checked.name.eraseMacroScopes
    stamp := CompiledLFCheckCacheStamp.ofCheckedSignature checked
    checkedHL := checkedHL
    lfSyntaxDefs := checked.lfSyntaxDefs
    lfOpaqueConsts := checked.lfOpaqueConsts
    lfContextZones := checked.lfContextZones
    lfBinderClasses := checked.lfBinderClasses
    lfConversionPlugins := checked.lfConversionPlugins
    lfObjectDefs := checked.lfObjectDefs
    lfJudgmentTheorems := checked.lfJudgmentTheorems
    lfGlobals := lfKnownGlobalNames checkedHL
    opaqueArities := lfOpaqueArities checkedHL
    globalHeads := lfGlobalHeadInfo checkedHL
    syntaxSortArities := lfSyntaxFamilyArities checkedHL
    judgmentArities := checkedHL.judgments.foldl (init := {}) fun acc j =>
      acc.insert j.name.eraseMacroScopes j.params.size
    solvers := checkedHL.sideConditionSolvers.foldl (init := {}) fun acc s =>
      acc.insert s.name.eraseMacroScopes
    checkedRules := checked.lfRules
    checkedRuleSchemas := checked.lfRuleSchemas
    checkedSideConditionCertificates := checked.lfSideConditionCertificates
    knownLFDefTypes :=
      checkedLFDefinitionTypeMapFromDefs checked.lfSyntaxDefs checked.lfObjectDefs
    knownLFDefValues := lfObjectDefinitionValueMapFromCheckedDefs checked.lfObjectDefs
    knownLFSyntaxDefValues := lfSyntaxDefinitionValueMapFromCheckedDefs checked.lfSyntaxDefs
    checkedLFDefValues := checkedLFDefValues
    availableLFTheoremStatements :=
      availableLFTheoremStatementsFromChecked checked.lfJudgmentTheorems
    availableLFTheoremNames := availableLFTheoremNamesFromChecked checked.lfJudgmentTheorems
    structuralKernelReplayBase := structuralKernelReplayBase }

/-- Build a compiled LF checking cache from the current checked-HL registry when available. -/
def mkCompiledLFCheckCache (theoryName : Name) (checked : CheckedSignature) :
    CoreM CompiledLFCheckCache := do
  let checkedHL ← checkedHLSignatureForCompiledCache theoryName checked
  mkCompiledLFCheckCacheFromHL checkedHL checked

/-- Result of looking up or rebuilding a compiled LF checking cache. -/
structure CompiledLFCheckCacheLookup where
  /-- Cache to use. -/
  cache : CompiledLFCheckCache
  /-- User-facing cache status, such as `hit`, `miss`, or `stale-rebuilt`. -/
  status : String
  /-- Whether the cache had to be rebuilt before use. -/
  rebuilt : Bool := false
  deriving Inhabited

end InternalLean
