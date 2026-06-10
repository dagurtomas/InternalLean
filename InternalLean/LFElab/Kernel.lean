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

/-- Convert checked LF head classes to the Phase-5b structural kernel head classes. -/
def checkedLFHeadKindToKHeadKind : CheckedLFHeadKind → Kernel.KHeadKind
  | .local => .primitive
  | .syntaxSort => .syntaxSort
  | .syntaxDef => .syntaxDef
  | .lfDefinition => .lfDefinition
  | .lfTheorem => .lfTheorem
  | .lfRule => .lfRule
  | .judgment => .judgment
  | .primitive => .primitive
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque

/-- Find a de Bruijn index for a source local in a KTerm-lowering binder stack. -/
def findKTermLoweringBinder? (binders : Array (Option Name)) (x : Name) : Option Nat :=
  let x := x.eraseMacroScopes
  let rec go (i : Nat) : List (Option Name) → Option Nat
    | [] => none
    | none :: rest => go (i + 1) rest
    | some y :: rest => if y.eraseMacroScopes == x then some i else go (i + 1) rest
  go 0 binders.toList.reverse

/-- Lower a checked LF expression to the Phase-5b structural kernel term. -/
partial def checkedLFExprToKTermWithContext (metas : NameMap RawMetaSort) (freeLocals : NameSet)
    (binders : Array (Option Name)) : CheckedLFExpr → Except String Kernel.KTerm
  | .ident h =>
      let name := h.name.eraseMacroScopes
      if h.kind == .local then
        match findKTermLoweringBinder? binders name with
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
        pure <| .ident {
          name := Kernel.KName.ofName name
          kind := checkedLFHeadKindToKHeadKind h.kind
          arity? := h.arity? }
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

/-- Lower a closed checked LF expression to the Phase-5b structural kernel term. -/
def checkedLFExprToKTerm (e : CheckedLFExpr) (metas : NameMap RawMetaSort := {})
    (freeLocals : NameSet := {}) : Except String Kernel.KTerm :=
  checkedLFExprToKTermWithContext metas freeLocals #[] e

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

/-- Convert a checked LF side-condition certificate to the low-level kernel form. -/
def checkedLFSideConditionCertificateToKernel (cert : CheckedLFSideConditionCertificate) :
    SideConditionCertificate :=
  { name := cert.certificateName
    condition := { name := cert.solver, args := [checkedLFExprToRaw cert.checkedInput] }
    kind := .builtinTrivial
    payload := cert.diagnostic }

/-- Convert a checked LF binder to a low-level raw metavariable declaration. -/
def checkedLFBindingToKernelMetaVar (v : CheckedLFBinding) : RuleMetaVar :=
  { name := v.name
    sort := match v.head? with | some h => .custom h.name | none => .arg
    type? := some (checkedLFExprToRaw v.checkedTypeExpr) }

/-- Convert a checked context zone to a low-level kernel replay zone schema. -/
def checkedLFContextZoneToKernel (z : CheckedLFContextZone) : ContextZoneSchema :=
  { name := z.name
    sort := .custom z.sortName
    dependsOn := z.dependsOn.toList }

/-- Convert a checked binder class to a low-level kernel replay binder-class schema. -/
def checkedLFBinderClassToKernel (b : CheckedLFBinderClass) : BinderClassSchema :=
  { name := b.name
    zone := b.zoneName
    boundSort := .custom b.boundSortName
    dependsOn := b.dependsOn.toList }

/-- Explicit checked LF type of a `syntax_def` family. -/
def checkedLFSyntaxDefTypeExpr (d : CheckedLFSyntaxDef) : CheckedLFExpr :=
  d.params.foldr (init := checkedLFTypeOfLevel d.resultLevel) fun b acc =>
    .arrow (some b.name) b.checkedTypeExpr acc

/-- Checked lambda value of a `syntax_def`, when it has a body. -/
def checkedLFSyntaxDefValue? (d : CheckedLFSyntaxDef) : Option CheckedLFExpr :=
  d.checkedValue?.map fun value =>
    if d.params.isEmpty then value else .lam (d.params.map (·.name)) value

/-- Convert a typed LF opaque placeholder to a typed kernel replay constant, when possible. -/
def checkedLFOpaqueConstToKernelConstant? (defValues : CheckedLFDefinitionValueMap)
    (c : CheckedLFOpaqueConst) : Option LFConstantSchema := do
  let result ← c.checkedTypeExpr?
  let locals := c.params.foldl (init := {}) fun locals p => locals.insert p.name.eraseMacroScopes
  let result := unfoldLFDefinitionsInCheckedExpr defValues locals result
  return LFConstantSchema.mk c.name (c.params.toList.map checkedLFBindingToKernelMetaVar)
    (checkedLFExprToRaw result)

/-- Split a checked LF function type into a low-level constant telescope and result type.

The kernel-facing replay checker only needs a finite first-order telescope for typed LF
constant applications.  Function-valued `lf_def`s therefore expose their leading structural
arrows as generated constant parameters; named dependent arrows keep their source name, while
nondependent arrows receive deterministic `_argN` names. -/
partial def checkedLFTypeToKernelConstantTelescope (e : CheckedLFExpr) (i : Nat := 1) :
  List RuleMetaVar × Raw :=
  match e with
  | .arrow binder? A B =>
      let name := (binder?.getD (Name.mkSimple s!"_arg{i}")).eraseMacroScopes
      let param : RuleMetaVar := {
        name := name
        sort := .arg
        type? := some (checkedLFExprToRaw A)
      }
      let (params, result) := checkedLFTypeToKernelConstantTelescope B (i + 1)
      (param :: params, result)
  | e => ([], checkedLFExprToRaw e)

/-- Convert a checked syntax definition to a typed kernel replay constant. -/
def checkedLFSyntaxDefToKernelConstant (defValues : CheckedLFDefinitionValueMap)
    (d : CheckedLFSyntaxDef) : LFConstantSchema :=
  let typeExpr := unfoldLFDefinitionsInCheckedExpr defValues {} (checkedLFSyntaxDefTypeExpr d)
  let (params, result) := checkedLFTypeToKernelConstantTelescope typeExpr
  LFConstantSchema.mk d.name params result

/-- Convert a checked LF definition to a typed kernel replay constant. -/
def checkedLFObjectDefToKernelConstant (defValues : CheckedLFDefinitionValueMap)
    (d : CheckedLFObjectDef) : LFConstantSchema :=
  let typeExpr := unfoldLFDefinitionsInCheckedExpr defValues {} d.checkedTypeExpr
  let (params, result) := checkedLFTypeToKernelConstantTelescope typeExpr
  LFConstantSchema.mk d.name params result

/-- Convert checked LF constants/definitions to typed kernel replay constants. -/
def checkedLFConstantsToKernel (defValues : CheckedLFDefinitionValueMap)
    (syntaxDefs : Array CheckedLFSyntaxDef) (opaqueConsts : Array CheckedLFOpaqueConst)
    (objectDefs : Array CheckedLFObjectDef) : Array LFConstantSchema :=
  (syntaxDefs.map (checkedLFSyntaxDefToKernelConstant defValues)) ++
    (opaqueConsts.filterMap (checkedLFOpaqueConstToKernelConstant? defValues)) ++
      (objectDefs.map (checkedLFObjectDefToKernelConstant defValues))

/-- Convert a checked conversion-plugin handle to the low-level kernel replay schema. -/
def checkedLFConversionPluginToKernel (p : CheckedLFConversionPlugin) : ConversionPluginSchema :=
  { name := p.name
    trust := p.trust
    supportedSteps := p.supportedSteps.toList }

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

/-- Convert a Phase-2/3 LF rule schema to the low-level kernel `RuleSchema` shape. -/
def checkedLFRuleSchemaToKernel (_defValues : CheckedLFDefinitionValueMap)
    (r : CheckedLFRuleSchema) : RuleSchema :=
  let sideConditions := r.sideConditionSlots.toList.map fun sc =>
    ({ name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] } : SideCondition)
  let certificateSlots := r.sideConditionSlots.toList.map fun sc =>
    let condition : SideCondition :=
      { name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] }
    ({ name := sc.name, condition := condition } : SideConditionCertificateSlot)
  let checkedCertificates := r.sideConditionSlots.toList.filterMap fun sc =>
    sc.certificate?.map checkedLFSideConditionCertificateToKernel
  let ruleMetas := r.metavariables.toList.map (fun v =>
    { name := v.name
      sort := match v.sortHead? with | some h => .custom h.name | none => .arg
      zone? := v.zoneName?
      type? := some (checkedLFExprToRaw v.checkedTypeExpr)
      evidence? := v.evidence?.map (fun ev =>
        checkedLFJudgmentExprToKernel ev.checkedJudgmentExpr ev.head) })
  let evidenceMetas := r.premises.toList.filterMap fun p =>
    if p.isDirectJudgment then
      none
    else
      some ({ name := p.name
              sort := match p.head? with
                | some h => if h.kind == .syntaxSort then .custom h.name else .arg
                | none => .arg
              type? := some (checkedLFExprToRaw p.checkedJudgmentExpr) } : RuleMetaVar)
  let kernelPremises := r.premises.toList.filterMap fun p =>
    match p.head? with
    | some h =>
        if h.kind == .judgment then
          some (checkedLFJudgmentExprToKernel p.checkedJudgmentExpr h)
        else
          none
    | none => none
  RuleSchema.mk r.name
    (ruleMetas ++ evidenceMetas)
    kernelPremises
    sideConditions
    certificateSlots
    checkedCertificates
    (checkedLFJudgmentExprToKernel r.checkedConclusionExpr r.conclusionHead)

/-- Convert a checked LF rule schema to the former fully unfolded kernel `RuleSchema` shape. -/
def checkedLFRuleSchemaToKernelExpanded (defValues : CheckedLFDefinitionValueMap)
    (r : CheckedLFRuleSchema) : RuleSchema :=
  let locals := r.metavariables.foldl (init := {}) fun locals v =>
    locals.insert v.name.eraseMacroScopes
  let norm := unfoldLFDefinitionsInCheckedExpr defValues locals
  let sideConditions := r.sideConditionSlots.toList.map fun sc =>
    ({ name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] } : SideCondition)
  let certificateSlots := r.sideConditionSlots.toList.map fun sc =>
    let condition : SideCondition :=
      { name := sc.solver, args := [checkedLFExprToRaw sc.checkedInput] }
    ({ name := sc.name, condition := condition } : SideConditionCertificateSlot)
  let checkedCertificates := r.sideConditionSlots.toList.filterMap fun sc =>
    sc.certificate?.map checkedLFSideConditionCertificateToKernel
  let ruleMetas := r.metavariables.toList.map (fun v =>
    { name := v.name
      sort := match v.sortHead? with | some h => .custom h.name | none => .arg
      zone? := v.zoneName?
      type? := some (checkedLFExprToRaw v.checkedTypeExpr)
      evidence? := v.evidence?.map (fun ev =>
        checkedLFJudgmentExprToKernel ev.checkedJudgmentExpr ev.head) })
  let evidenceMetas := r.premises.toList.filterMap fun p =>
    if p.isDirectJudgment then
      none
    else
      some ({ name := p.name
              sort := match p.head? with
                | some h => if h.kind == .syntaxSort then .custom h.name else .arg
                | none => .arg
              type? := some (checkedLFExprToRaw (norm p.checkedJudgmentExpr)) } : RuleMetaVar)
  let kernelPremises := r.premises.toList.filterMap fun p =>
    match p.head? with
    | some h =>
        if h.kind == .judgment then
          some (checkedLFJudgmentExprToKernel (norm p.checkedJudgmentExpr) h)
        else
          none
    | none => none
  RuleSchema.mk r.name
    (ruleMetas ++ evidenceMetas)
    kernelPremises
    sideConditions
    certificateSlots
    checkedCertificates
    (checkedLFJudgmentExprToKernel (norm r.checkedConclusionExpr) r.conclusionHead)

/-- Convert all Phase-2 LF rule schemas to compact kernel `RuleSchema` staging artifacts. -/
def checkedLFRuleSchemasToKernel (defValues : CheckedLFDefinitionValueMap)
    (rules : Array CheckedLFRuleSchema) : Array RuleSchema :=
  rules.map (checkedLFRuleSchemaToKernel defValues)

/-- Convert all Phase-2 LF rule schemas to fully unfolded kernel replay artifacts. -/
def checkedLFRuleSchemasToKernelExpanded (defValues : CheckedLFDefinitionValueMap)
    (rules : Array CheckedLFRuleSchema) : Array RuleSchema :=
  rules.map (checkedLFRuleSchemaToKernelExpanded defValues)

/-- Extract checked local theorem-assumption entries from a locally quantified LF theorem. -/
def kernelLFLocalAssumptionEntriesOfTheorem (t : CheckedLFJudgmentTheorem) :
    List KernelLFTheoremEntry :=
  t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          some { name := b.name, statement := checkedLFJudgmentExprToKernel b.checkedTypeExpr head }
        else
          none
    | none => none

/-- Extract checked local theorem assumptions without expanding checked LF definitions. -/
def kernelLFLocalAssumptionEntriesOfTheoremCompact (t : CheckedLFJudgmentTheorem) :
    List KernelLFTheoremEntry :=
  kernelLFLocalAssumptionEntriesOfTheorem t

/-- Extract checked local theorem assumptions after LF-definition normalization. -/
def kernelLFLocalAssumptionEntriesOfTheoremExpanded (sig : HLSignature)
    (globalHeads : NameMap (CheckedLFHeadKind × Option Nat)) (defValues : LFDefinitionValueMap)
    (t : CheckedLFJudgmentTheorem) : CoreM (List KernelLFTheoremEntry) := do
  let theoremLocals := t.binders.foldl (init := {}) fun locals b =>
    locals.insert b.name.eraseMacroScopes
  let mut out := []
  for b in t.binders do
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          let expr := unfoldLFDefinitionsInExprWithLocals defValues theoremLocals b.typeExpr
          let statement ← lfJudgmentObjExprToKernel sig globalHeads "local theorem assumption"
            t.name expr theoremLocals
          out := out ++ [{ name := b.name, statement := statement }]
    | none => pure ()
  pure out

/-- Kernel rule schema used when a checked LF theorem with local binders is referenced as a premise.
-/
def kernelLFRuleSchemaOfTheorem (_defValues : CheckedLFDefinitionValueMap)
    (t : CheckedLFJudgmentTheorem) : RuleSchema :=
  let metavariables := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then none
        else
          some ({ name := b.name
                  sort := if head.kind == .syntaxSort then .custom head.name else .arg
                  type? := some (checkedLFExprToRaw b.checkedTypeExpr) } : RuleMetaVar)
    | none =>
        some ({ name := b.name
                sort := .arg
                type? := some (checkedLFExprToRaw b.checkedTypeExpr) } : RuleMetaVar)
  let premises := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          some (checkedLFJudgmentExprToKernel b.checkedTypeExpr head)
        else none
    | none => none
  RuleSchema.mk (lfJudgmentTheoremKernelRuleName t.name) metavariables premises [] [] []
    (checkedLFJudgmentExprToKernel t.checkedJudgmentExpr t.judgmentHead)

/-- Fully unfolded kernel rule schema used for replay fallback of checked LF theorem references. -/
def kernelLFRuleSchemaOfTheoremExpanded (defValues : CheckedLFDefinitionValueMap)
    (t : CheckedLFJudgmentTheorem) : RuleSchema :=
  let locals := t.binders.foldl (init := {}) fun locals b => locals.insert b.name.eraseMacroScopes
  let norm := unfoldLFDefinitionsInCheckedExpr defValues locals
  let metavariables := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then none
        else
          some ({ name := b.name
                  sort := if head.kind == .syntaxSort then .custom head.name else .arg
                  type? := some (checkedLFExprToRaw (norm b.checkedTypeExpr)) } : RuleMetaVar)
    | none =>
        some ({ name := b.name
                sort := .arg
                type? := some (checkedLFExprToRaw (norm b.checkedTypeExpr)) } : RuleMetaVar)
  let premises := t.binders.toList.filterMap fun b =>
    match b.head? with
    | some head =>
        if head.kind == .judgment then
          some (checkedLFJudgmentExprToKernel (norm b.checkedTypeExpr) head)
        else none
    | none => none
  RuleSchema.mk (lfJudgmentTheoremKernelRuleName t.name) metavariables premises [] [] []
    (checkedLFJudgmentExprToKernel (norm t.checkedJudgmentExpr) t.judgmentHead)

/-- Compact kernel rule schemas for checked LF theorems, used by theorem references. -/
def kernelLFRuleSchemasOfTheorems (defValues : CheckedLFDefinitionValueMap)
    (theorems : Array CheckedLFJudgmentTheorem) : Array RuleSchema :=
  theorems.map (kernelLFRuleSchemaOfTheorem defValues)

/-- Fully unfolded kernel rule schemas for checked LF theorem replay fallback. -/
def kernelLFRuleSchemasOfTheoremsExpanded (defValues : CheckedLFDefinitionValueMap)
    (theorems : Array CheckedLFJudgmentTheorem) : Array RuleSchema :=
  theorems.map (kernelLFRuleSchemaOfTheoremExpanded defValues)

/-- Replace replay rules in a kernel signature by fully unfolded compatibility rules. -/
def kernelSignatureWithExpandedReplayRules (kernelSig : Signature)
    (defValues : CheckedLFDefinitionValueMap) (ruleSchemas : Array CheckedLFRuleSchema)
    (theorems : Array CheckedLFJudgmentTheorem) : Signature :=
  { kernelSig with
    rules := (checkedLFRuleSchemasToKernelExpanded defValues ruleSchemas ++
      kernelLFRuleSchemasOfTheoremsExpanded defValues theorems).toList }

/-- Extract checked external-certificate entries exposed by theorem-like bridge artifacts. -/
def kernelLFCertificateEntriesOfTheorems (theorems : Array CheckedLFJudgmentTheorem) :
    List KernelLFCertificateEntry :=
  theorems.toList.filterMap fun t =>
    match t.kernelDerivation? with
    | some (.certificate name stmt certificateName) =>
        some { name := name, statement := stmt, certificateName := certificateName }
    | _ => none

/-- Run opt-in Phase-5b structural kernel dual replay for an already accepted raw replay. -/
def validateStructuralKernelDualReplay (label : String) (signature : Signature)
    (context : KernelLFCheckContext) (statement : Judgment) (derivation : KernelLFDerivation) :
    CoreM Unit := do
  if !(← getBoolOption `internalLean.kernel.dualReplay) then
    return ()
  let structuralSig := Kernel.Signature.ofOld signature
  let structuralCtx := Kernel.KernelLFCheckContext.ofOld context
  let structuralStmt := Kernel.Judgment.ofOld statement
  let structuralDeriv := Kernel.KernelLFDerivation.ofOld derivation
  match Kernel.CheckedKernelLFDerivation.ofReplay structuralSig structuralCtx structuralStmt
      structuralDeriv with
  | .ok _ => pure ()
  | .error err =>
      throwError "Phase-5b structural kernel dual replay failed for {label}: {err}"

/-- Add checked kernel replay validation to one incrementally checked LF theorem. -/
def validateIncrementalLFTheoremKernelReplay (sig : HLSignature) (checked : CheckedSignature)
    (t : CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let some kernelDeriv := t.kernelDerivation?
    | pure t
  let lfCheckedDefValues := checkedLFDefinitionValues checked.lfSyntaxDefs checked.lfObjectDefs
  let kernelSig : Signature := {
    name := sig.name.eraseMacroScopes
    constants := (checkedLFConstantsToKernel lfCheckedDefValues checked.lfSyntaxDefs
      checked.lfOpaqueConsts checked.lfObjectDefs).toList
    contextZones := checked.lfContextZones.toList.map checkedLFContextZoneToKernel
    binderClasses := checked.lfBinderClasses.toList.map checkedLFBinderClassToKernel
    conversionPlugins := checked.lfConversionPlugins.toList.map checkedLFConversionPluginToKernel
    rules := (checkedLFRuleSchemasToKernel lfCheckedDefValues checked.lfRuleSchemas ++
      kernelLFRuleSchemasOfTheorems lfCheckedDefValues checked.lfJudgmentTheorems).toList }
  let mut replayCtx : KernelLFCheckContext := {
    certificates := kernelLFCertificateEntriesOfTheorems checked.lfJudgmentTheorems }
  for prior in checked.lfJudgmentTheorems do
    if prior.binders.isEmpty then
      if let some priorKernel := prior.kernelDerivation? then
        replayCtx := replayCtx.addTheorem prior.name (KernelLFDerivation.statement priorKernel)
  let assumptions := kernelLFLocalAssumptionEntriesOfTheoremCompact t
  let localReplayCtx := { replayCtx with
    localParameters := t.binders.toList.map (fun b => b.name)
    assumptions := assumptions }
  match CheckedKernelLFDerivation.ofReplay kernelSig localReplayCtx
      (KernelLFDerivation.statement kernelDeriv) kernelDeriv with
  | .ok checkedReplay => do
      validateStructuralKernelDualReplay s!"judgment_theorem '{t.name}' compact replay"
        kernelSig localReplayCtx (KernelLFDerivation.statement kernelDeriv) kernelDeriv
      pure { t with checkedKernelDerivation? := some checkedReplay }
  | .error compactErr =>
      let expandedKernelSig :=
        kernelSignatureWithExpandedReplayRules kernelSig lfCheckedDefValues checked.lfRuleSchemas
          checked.lfJudgmentTheorems
      let lfKernelDefValues :=
        lfDefinitionValueMapFromCheckedDefs checked.lfSyntaxDefs checked.lfObjectDefs
      let expandedAssumptions ←
        kernelLFLocalAssumptionEntriesOfTheoremExpanded sig (lfGlobalHeadInfo sig)
          lfKernelDefValues t
      let expandedReplayCtx := { replayCtx with
        localParameters := t.binders.toList.map (fun b => b.name)
        assumptions := expandedAssumptions }
      match CheckedKernelLFDerivation.ofReplay expandedKernelSig expandedReplayCtx
          (KernelLFDerivation.statement kernelDeriv) kernelDeriv with
      | .ok checkedReplay => do
          validateStructuralKernelDualReplay s!"judgment_theorem '{t.name}' expanded replay"
            expandedKernelSig expandedReplayCtx (KernelLFDerivation.statement kernelDeriv)
            kernelDeriv
          pure { t with checkedKernelDerivation? := some checkedReplay }
      | .error expandedErr =>
          throwError "kernel-facing replay check failed for judgment_theorem '{t.name}' in type \
            theory '{sig.name}': {compactErr}\nexpanded fallback also failed: {expandedErr}"

/-- Add checked kernel replay validation to one incrementally checked LF theorem, reusing a
compiled checked-theory replay cache. -/
def validateIncrementalLFTheoremKernelReplayWithCache (cache : CompiledLFCheckCache)
    (t : CheckedLFJudgmentTheorem) : CoreM CheckedLFJudgmentTheorem := do
  let some kernelDeriv := t.kernelDerivation?
    | pure t
  let assumptions := kernelLFLocalAssumptionEntriesOfTheoremCompact t
  let localReplayCtx := { cache.kernelReplayBase with
    localParameters := t.binders.toList.map (fun b => b.name)
    assumptions := assumptions }
  match CheckedKernelLFDerivation.ofReplay cache.kernelSig localReplayCtx
      (KernelLFDerivation.statement kernelDeriv) kernelDeriv with
  | .ok checkedReplay => do
      validateStructuralKernelDualReplay s!"judgment_theorem '{t.name}' compact cached replay"
        cache.kernelSig localReplayCtx (KernelLFDerivation.statement kernelDeriv) kernelDeriv
      pure { t with checkedKernelDerivation? := some checkedReplay }
  | .error compactErr =>
      let primitiveNames : NameSet := cache.checkedRuleSchemas.foldl (init := {}) fun names r =>
        names.insert r.name.eraseMacroScopes
      let expandedPrimitiveRules :=
        checkedLFRuleSchemasToKernelExpanded cache.checkedLFDefValues cache.checkedRuleSchemas
      let oldTheoremRules := cache.kernelSig.rules.toArray.filter fun r =>
        !primitiveNames.contains r.name.eraseMacroScopes
      let expandedKernelSig := { cache.kernelSig with
        rules := (expandedPrimitiveRules ++ oldTheoremRules).toList }
      let lfKernelDefValues : LFDefinitionValueMap := Id.run do
        let mut values := cache.knownLFDefValues
        for (n, value) in cache.knownLFSyntaxDefValues.toList do
          values := values.insert n value
        return values
      let expandedAssumptions ←
        kernelLFLocalAssumptionEntriesOfTheoremExpanded cache.checkedHL cache.globalHeads
          lfKernelDefValues t
      let expandedReplayCtx := { cache.kernelReplayBase with
        localParameters := t.binders.toList.map (fun b => b.name)
        assumptions := expandedAssumptions }
      match CheckedKernelLFDerivation.ofReplay expandedKernelSig expandedReplayCtx
          (KernelLFDerivation.statement kernelDeriv) kernelDeriv with
      | .ok checkedReplay => do
          validateStructuralKernelDualReplay s!"judgment_theorem '{t.name}' expanded cached replay"
            expandedKernelSig expandedReplayCtx (KernelLFDerivation.statement kernelDeriv)
            kernelDeriv
          pure { t with checkedKernelDerivation? := some checkedReplay }
      | .error expandedErr =>
          throwError "kernel-facing replay check failed for judgment_theorem '{t.name}' in type \
            theory '{cache.checkedHL.name}': {compactErr}\nexpanded fallback also failed: \
            {expandedErr}"


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
  let checkedLFObjectDefValues := checkedLFObjectDefinitionValues checked.lfObjectDefs
  let kernelSig : Signature := {
    name := checked.name.eraseMacroScopes
    constants :=
      (checked.lfSyntaxDefs.map (checkedLFSyntaxDefToKernelConstant checkedLFDefValues) ++
        checked.lfOpaqueConsts.filterMap
          (checkedLFOpaqueConstToKernelConstant? checkedLFObjectDefValues) ++
        checked.lfObjectDefs.map (checkedLFObjectDefToKernelConstant checkedLFDefValues)).toList
    contextZones := checked.lfContextZones.toList.map checkedLFContextZoneToKernel
    binderClasses := checked.lfBinderClasses.toList.map checkedLFBinderClassToKernel
    conversionPlugins := checked.lfConversionPlugins.toList.map checkedLFConversionPluginToKernel
    rules := (checkedLFRuleSchemasToKernel checkedLFDefValues checked.lfRuleSchemas ++
      kernelLFRuleSchemasOfTheorems checkedLFDefValues checked.lfJudgmentTheorems).toList }
  let mut replayCtx : KernelLFCheckContext := {
    certificates := kernelLFCertificateEntriesOfTheorems checked.lfJudgmentTheorems }
  for prior in checked.lfJudgmentTheorems do
    if prior.binders.isEmpty then
      if let some priorKernel := prior.kernelDerivation? then
        replayCtx := replayCtx.addTheorem prior.name (KernelLFDerivation.statement priorKernel)
  pure {
    theoryName := checked.name.eraseMacroScopes
    stamp := CompiledLFCheckCacheStamp.ofCheckedSignature checked
    checkedHL := checkedHL
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
    kernelSig := kernelSig
    kernelReplayBase := replayCtx }

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
