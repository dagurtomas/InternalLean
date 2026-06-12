/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.ModelInterface

/-!
# Theory fragment dependency reports

This module implements the report-only first phase of theory-fragment extraction.  The closure is
computed from checked LF replay artifacts for a flattened theory; no generated fragment theory is
registered in this phase.
-/

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

namespace TheoryFragment

/-- Stable membership and reason data for one report-only fragment closure. -/
structure Closure where
  levelParams : NameSet := {}
  syntaxSorts : NameSet := {}
  syntaxAbbrevs : NameSet := {}
  syntaxDefs : NameSet := {}
  judgmentAbbrevs : NameSet := {}
  contextZones : NameSet := {}
  binderClasses : NameSet := {}
  judgments : NameSet := {}
  rules : NameSet := {}
  sideConditionSolvers : NameSet := {}
  conversionPlugins : NameSet := {}
  levelNormalizerProfiles : NameSet := {}
  lfOpaqueConsts : NameSet := {}
  lfObjectDefs : NameSet := {}
  lfJudgmentTheorems : NameSet := {}
  sideConditionCertificates : NameSet := {}
  reasons : NameMap String := {}
  deriving Inhabited

/-- Worklist item kinds for transitive fragment closure. -/
inductive ItemKind where
  | levelParam
  | syntaxSort
  | syntaxAbbrev
  | syntaxDef
  | judgmentAbbrev
  | contextZone
  | binderClass
  | judgment
  | rule
  | sideConditionSolver
  | conversionPlugin
  | levelNormalizerProfile
  | lfOpaqueConst
  | lfObjectDef
  | lfJudgmentTheorem
  | sideConditionCertificate
  deriving Inhabited, BEq, Repr

/-- A pending closure item. -/
structure Item where
  kind : ItemKind
  name : Name
  deriving Inhabited, Repr

/-- Builder state for the pure closure computation. -/
structure Builder where
  closure : Closure := {}
  worklist : Array Item := #[]
  deriving Inhabited

/-- Source and checked lookup tables used by the closure builder. -/
structure Index where
  /-- Flattened high-level signature retained for report callers and later source filtering. -/
  flat : HLSignature
  checked : CheckedSignature
  syntaxSorts : NameMap CheckedLFSyntaxSort := {}
  syntaxAbbrevs : NameMap CheckedLFSyntaxAbbrev := {}
  syntaxDefs : NameMap CheckedLFSyntaxDef := {}
  judgmentAbbrevs : NameMap CheckedLFJudgmentAbbrev := {}
  contextZones : NameMap CheckedLFContextZone := {}
  binderClasses : NameMap CheckedLFBinderClass := {}
  judgments : NameMap CheckedLFJudgment := {}
  rules : NameMap CheckedLFRule := {}
  sideConditionSolvers : NameMap CheckedLFSideConditionSolver := {}
  conversionPlugins : NameMap CheckedLFConversionPlugin := {}
  levelNormalizerProfilesBySolver : NameMap CheckedLFLevelNormalizerProfile := {}
  levelNormalizerProfilesByPlugin : NameMap CheckedLFLevelNormalizerProfile := {}
  lfOpaqueConsts : NameMap CheckedLFOpaqueConst := {}
  lfObjectDefs : NameMap CheckedLFObjectDef := {}
  lfJudgmentTheorems : NameMap CheckedLFJudgmentTheorem := {}
  sideConditionCertificatesByName : NameMap CheckedLFSideConditionCertificate := {}
  sideConditionCertificatesByCertificateName : NameMap CheckedLFSideConditionCertificate := {}

/-- Insert an entry in a name map with erased macro scopes. -/
def insertByName (m : NameMap α) (name : Name) (value : α) : NameMap α :=
  m.insert name.eraseMacroScopes value

/-- Build closure lookup tables from the checked signature. -/
def mkIndex (flat : HLSignature) (checked : CheckedSignature) : Index := Id.run do
  let mut idx : Index := { flat := flat, checked := checked }
  for d in checked.lfSyntaxSorts do
    idx := { idx with syntaxSorts := insertByName idx.syntaxSorts d.name d }
  for d in checked.lfSyntaxAbbrevs do
    idx := { idx with syntaxAbbrevs := insertByName idx.syntaxAbbrevs d.name d }
  for d in checked.lfSyntaxDefs do
    idx := { idx with syntaxDefs := insertByName idx.syntaxDefs d.name d }
  for d in checked.lfJudgmentAbbrevs do
    idx := { idx with judgmentAbbrevs := insertByName idx.judgmentAbbrevs d.name d }
  for d in checked.lfContextZones do
    idx := { idx with contextZones := insertByName idx.contextZones d.name d }
  for d in checked.lfBinderClasses do
    idx := { idx with binderClasses := insertByName idx.binderClasses d.name d }
  for d in checked.lfJudgments do
    idx := { idx with judgments := insertByName idx.judgments d.name d }
  for d in checked.lfRules do
    idx := { idx with rules := insertByName idx.rules d.name d }
  for d in checked.lfSideConditionSolvers do
    idx := { idx with sideConditionSolvers := insertByName idx.sideConditionSolvers d.name d }
  for d in checked.lfConversionPlugins do
    idx := { idx with conversionPlugins := insertByName idx.conversionPlugins d.name d }
  for d in checked.lfLevelNormalizerProfiles do
    idx := {
      idx with
      levelNormalizerProfilesBySolver :=
        insertByName idx.levelNormalizerProfilesBySolver d.solverName d
      levelNormalizerProfilesByPlugin :=
        insertByName idx.levelNormalizerProfilesByPlugin d.pluginName d }
  for d in checked.lfOpaqueConsts do
    idx := { idx with lfOpaqueConsts := insertByName idx.lfOpaqueConsts d.name d }
  for d in checked.lfObjectDefs do
    idx := { idx with lfObjectDefs := insertByName idx.lfObjectDefs d.name d }
  for d in checked.lfJudgmentTheorems do
    idx := { idx with lfJudgmentTheorems := insertByName idx.lfJudgmentTheorems d.name d }
  for d in checked.lfSideConditionCertificates do
    idx := {
      idx with
      sideConditionCertificatesByName := insertByName idx.sideConditionCertificatesByName d.name d
      sideConditionCertificatesByCertificateName :=
        insertByName idx.sideConditionCertificatesByCertificateName d.certificateName d }
  return idx

/-- Membership test for one item kind. -/
def Closure.contains (c : Closure) (kind : ItemKind) (name : Name) : Bool :=
  let name := name.eraseMacroScopes
  match kind with
  | .levelParam => c.levelParams.contains name
  | .syntaxSort => c.syntaxSorts.contains name
  | .syntaxAbbrev => c.syntaxAbbrevs.contains name
  | .syntaxDef => c.syntaxDefs.contains name
  | .judgmentAbbrev => c.judgmentAbbrevs.contains name
  | .contextZone => c.contextZones.contains name
  | .binderClass => c.binderClasses.contains name
  | .judgment => c.judgments.contains name
  | .rule => c.rules.contains name
  | .sideConditionSolver => c.sideConditionSolvers.contains name
  | .conversionPlugin => c.conversionPlugins.contains name
  | .levelNormalizerProfile => c.levelNormalizerProfiles.contains name
  | .lfOpaqueConst => c.lfOpaqueConsts.contains name
  | .lfObjectDef => c.lfObjectDefs.contains name
  | .lfJudgmentTheorem => c.lfJudgmentTheorems.contains name
  | .sideConditionCertificate => c.sideConditionCertificates.contains name

/-- Insert a name into the set for one item kind. -/
def Closure.insert (c : Closure) (kind : ItemKind) (name : Name) (reason : String) : Closure :=
  let name := name.eraseMacroScopes
  let reasons := if c.reasons.contains name then c.reasons else c.reasons.insert name reason
  match kind with
  | .levelParam =>
      { c with
        levelParams := c.levelParams.insert name
        reasons := reasons }
  | .syntaxSort =>
      { c with
        syntaxSorts := c.syntaxSorts.insert name
        reasons := reasons }
  | .syntaxAbbrev =>
      { c with
        syntaxAbbrevs := c.syntaxAbbrevs.insert name
        reasons := reasons }
  | .syntaxDef =>
      { c with
        syntaxDefs := c.syntaxDefs.insert name
        reasons := reasons }
  | .judgmentAbbrev =>
      { c with
        judgmentAbbrevs := c.judgmentAbbrevs.insert name
        reasons := reasons }
  | .contextZone =>
      { c with
        contextZones := c.contextZones.insert name
        reasons := reasons }
  | .binderClass =>
      { c with
        binderClasses := c.binderClasses.insert name
        reasons := reasons }
  | .judgment =>
      { c with
        judgments := c.judgments.insert name
        reasons := reasons }
  | .rule =>
      { c with
        rules := c.rules.insert name
        reasons := reasons }
  | .sideConditionSolver =>
      { c with
        sideConditionSolvers := c.sideConditionSolvers.insert name
        reasons := reasons }
  | .conversionPlugin =>
      { c with
        conversionPlugins := c.conversionPlugins.insert name
        reasons := reasons }
  | .levelNormalizerProfile =>
      { c with
        levelNormalizerProfiles := c.levelNormalizerProfiles.insert name
        reasons := reasons }
  | .lfOpaqueConst =>
      { c with
        lfOpaqueConsts := c.lfOpaqueConsts.insert name
        reasons := reasons }
  | .lfObjectDef =>
      { c with
        lfObjectDefs := c.lfObjectDefs.insert name
        reasons := reasons }
  | .lfJudgmentTheorem =>
      { c with
        lfJudgmentTheorems := c.lfJudgmentTheorems.insert name
        reasons := reasons }
  | .sideConditionCertificate =>
      { c with
        sideConditionCertificates := c.sideConditionCertificates.insert name
        reasons := reasons }

/-- Add one worklist item if it was not already present in the closure. -/
def Builder.add (b : Builder) (kind : ItemKind) (name : Name) (reason : String) : Builder :=
  let name := name.eraseMacroScopes
  if b.closure.contains kind name then b else
    { closure := b.closure.insert kind name reason
      worklist := b.worklist.push { kind := kind, name := name } }

/-- Add all universe parameters mentioned by a level expression. -/
def Builder.addLevelParams (b : Builder) (u : LevelExpr) (reason : String) : Builder :=
  u.params.foldl (fun b n => b.add .levelParam n reason) b

/-- Names of all non-local heads in a resolved LF expression. -/
partial def checkedLFExprHeadNames : CheckedLFExpr → NameSet
  | .ident h => if h.kind == .local then {} else ({h.name.eraseMacroScopes} : NameSet)
  | .sort | .univ _ => {}
  | .app f a | .arrow _ f a | .sigma _ f a | .pair f a | .jeq f a =>
      insertNameSet (checkedLFExprHeadNames f) (checkedLFExprHeadNames a)
  | .fst e | .snd e => checkedLFExprHeadNames e
  | .lam _ body => checkedLFExprHeadNames body

/-- Universe parameters mentioned by explicit universe expressions in a resolved LF expression. -/
partial def checkedLFExprLevelParams : CheckedLFExpr → NameSet
  | .univ u => u.params.foldl (fun s n => s.insert n.eraseMacroScopes) {}
  | .ident _ | .sort => {}
  | .app f a | .arrow _ f a | .sigma _ f a | .pair f a | .jeq f a =>
      insertNameSet (checkedLFExprLevelParams f) (checkedLFExprLevelParams a)
  | .fst e | .snd e => checkedLFExprLevelParams e
  | .lam _ body => checkedLFExprLevelParams body

/-- Add dependencies from a resolved LF expression. -/
def Builder.addCheckedExprHeads (idx : Index) (b : Builder) (expr : CheckedLFExpr)
    (reason : String) : Builder :=
  let b := checkedLFExprHeadNames expr |>.toList.foldl (fun b n => addHead idx b n reason) b
  checkedLFExprLevelParams expr |>.toList.foldl (fun b n => b.add .levelParam n reason) b
where
  addHead (idx : Index) (b : Builder) (name : Name) (reason : String) : Builder :=
    let name := name.eraseMacroScopes
    if idx.syntaxSorts.contains name then b.add .syntaxSort name reason
    else if idx.syntaxAbbrevs.contains name then b.add .syntaxAbbrev name reason
    else if idx.syntaxDefs.contains name then b.add .syntaxDef name reason
    else if idx.judgmentAbbrevs.contains name then b.add .judgmentAbbrev name reason
    else if idx.judgments.contains name then b.add .judgment name reason
    else if idx.rules.contains name then b.add .rule name reason
    else if idx.sideConditionSolvers.contains name then b.add .sideConditionSolver name reason
    else if idx.conversionPlugins.contains name then b.add .conversionPlugin name reason
    else if idx.lfOpaqueConsts.contains name then b.add .lfOpaqueConst name reason
    else if idx.lfObjectDefs.contains name then b.add .lfObjectDef name reason
    else if idx.lfJudgmentTheorems.contains name then b.add .lfJudgmentTheorem name reason
    else b

/-- Add one source/global head dependency by category. -/
def Builder.addHead (idx : Index) (b : Builder) (name : Name) (reason : String) : Builder :=
  let name := name.eraseMacroScopes
  if idx.syntaxSorts.contains name then b.add .syntaxSort name reason
  else if idx.syntaxAbbrevs.contains name then b.add .syntaxAbbrev name reason
  else if idx.syntaxDefs.contains name then b.add .syntaxDef name reason
  else if idx.judgmentAbbrevs.contains name then b.add .judgmentAbbrev name reason
  else if idx.judgments.contains name then b.add .judgment name reason
  else if idx.rules.contains name then b.add .rule name reason
  else if idx.sideConditionSolvers.contains name then b.add .sideConditionSolver name reason
  else if idx.conversionPlugins.contains name then b.add .conversionPlugin name reason
  else if idx.lfOpaqueConsts.contains name then b.add .lfOpaqueConst name reason
  else if idx.lfObjectDefs.contains name then b.add .lfObjectDef name reason
  else if idx.lfJudgmentTheorems.contains name then b.add .lfJudgmentTheorem name reason
  else b

/-- Add dependencies from a checked telescope. -/
def Builder.addBindings (idx : Index) (b : Builder) (bindings : Array CheckedLFBinding)
    (reason : String) : Builder :=
  bindings.foldl (fun b binding =>
    Builder.addCheckedExprHeads idx b binding.checkedTypeExpr reason) b

/-- Add dependencies from a side-condition certificate. -/
def Builder.addSideConditionCertificate (idx : Index) (b : Builder)
    (cert : CheckedLFSideConditionCertificate) (reason : String) : Builder :=
  let b := b.add .sideConditionSolver cert.solver reason
  Builder.addCheckedExprHeads idx b cert.checkedInput reason

/-- Add dependencies from a checked rule declaration. -/
def Builder.addRuleDependencies (idx : Index) (b : Builder) (r : CheckedLFRule) : Builder :=
  Id.run do
  let reason := s!"dependency of rule {r.name.eraseMacroScopes}"
  let mut b := Builder.addBindings idx b r.params reason
  for p in r.paramEvidences do
    b := Builder.addCheckedExprHeads idx b p.checkedJudgmentExpr reason
  for p in r.premises do
    b := Builder.addCheckedExprHeads idx b p.checkedJudgmentExpr reason
  for sc in r.sideConditions do
    b := b.add .sideConditionSolver sc.solver reason
    b := Builder.addCheckedExprHeads idx b sc.checkedInput reason
  b := Builder.addCheckedExprHeads idx b r.checkedConclusionExpr reason
  return b

/-- Add dependencies from a checked theorem declaration and replay summary. -/
def Builder.addTheoremDependencies (idx : Index) (b : Builder)
    (t : CheckedLFJudgmentTheorem) : Except String Builder := do
  let reason := s!"dependency of theorem {t.name.eraseMacroScopes}"
  let mut b := Builder.addBindings idx b t.binders reason
  b := Builder.addCheckedExprHeads idx b t.checkedJudgmentExpr reason
  b := Builder.addCheckedExprHeads idx b t.checkedProof reason
  let cert ← kernelLFReplayCertificateForCheckedTheorem idx.checked t
  let deps := kernelLFReplayDependencySummary cert.derivation
  for n in deps.globalHeads.toList do
    b := b.addHead idx n s!"global LF head used by theorem {t.name.eraseMacroScopes}"
  for n in deps.ruleApplications.toList do
    b := b.add .rule n s!"rule applied by theorem {t.name.eraseMacroScopes}"
  for n in deps.theoremReferences.toList do
    b := b.add .lfJudgmentTheorem n s!"theorem referenced by {t.name.eraseMacroScopes}"
  for n in deps.externalCertificates.toList do
    if let some cert := idx.sideConditionCertificatesByCertificateName.find? n.eraseMacroScopes then
      b := b.add .sideConditionCertificate cert.certificateName
        s!"side-condition certificate used by theorem {t.name.eraseMacroScopes}"
  for n in deps.certificateObligations.toList do
    if let some cert := idx.sideConditionCertificatesByName.find? n.eraseMacroScopes then
      b := b.add .sideConditionCertificate cert.certificateName
        s!"side-condition certificate used by theorem {t.name.eraseMacroScopes}"
  return b

/-- Add dependencies required by a level-normalizer profile. -/
def Builder.addLevelNormalizerProfileDependencies (idx : Index) (b : Builder)
    (profile : CheckedLFLevelNormalizerProfile) : Builder :=
  let reason := s!"constituent of level_normalizer profile {profile.solverName.eraseMacroScopes}"
  let b := b.add .sideConditionSolver profile.solverName reason
  let b := b.add .conversionPlugin profile.pluginName reason
  let b := b.addHead idx profile.levelSortName reason
  let b := b.addHead idx profile.zeroName reason
  let b := b.addHead idx profile.succName reason
  let b := b.addHead idx profile.maxName reason
  b.addHead idx profile.leName reason

/-- Process one worklist item. -/
def processItem (idx : Index) (item : Item) (b : Builder) : Except String Builder := do
  let name := item.name.eraseMacroScopes
  match item.kind with
  | .levelParam => pure b
  | .syntaxSort =>
      match idx.syntaxSorts.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addBindings idx b d.params s!"parameter of syntax_sort {name}"
          pure <| Builder.addLevelParams b d.resultLevel
            s!"universe annotation of syntax_sort {name}"
  | .syntaxAbbrev =>
      match idx.syntaxAbbrevs.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addBindings idx b d.params s!"parameter of syntax_abbrev {name}"
          pure <| Builder.addCheckedExprHeads idx b d.checkedValue s!"body of syntax_abbrev {name}"
  | .syntaxDef =>
      match idx.syntaxDefs.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addBindings idx b d.params s!"parameter of syntax_def {name}"
          let b := Builder.addLevelParams b d.resultLevel
            s!"universe annotation of syntax_def {name}"
          match d.checkedValue? with
          | some value =>
              pure <| Builder.addCheckedExprHeads idx b value s!"body of syntax_def {name}"
          | none => pure b
  | .judgmentAbbrev =>
      match idx.judgmentAbbrevs.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addBindings idx b d.params s!"parameter of judgment_abbrev {name}"
          pure <| Builder.addCheckedExprHeads idx b d.checkedValue
            s!"body of judgment_abbrev {name}"
  | .contextZone =>
      match idx.contextZones.find? name with
      | none => pure b
      | some d =>
          let b := b.add .syntaxSort d.sortName s!"sort of context_zone {name}"
          pure <| d.dependsOn.foldl (fun b z => b.add .contextZone z
            s!"dependency of context_zone {name}") b
  | .binderClass =>
      match idx.binderClasses.find? name with
      | none => pure b
      | some d =>
          let b := b.add .syntaxSort d.boundSortName s!"bound sort of binder_class {name}"
          let b := b.add .contextZone d.zoneName s!"context zone of binder_class {name}"
          pure <| d.dependsOn.foldl (fun b z => b.add .contextZone z
            s!"dependency of binder_class {name}") b
  | .judgment =>
      match idx.judgments.find? name with
      | none => pure b
      | some d => pure <| Builder.addBindings idx b d.params s!"parameter of judgment {name}"
  | .rule =>
      match idx.rules.find? name with
      | none => pure b
      | some d => pure <| Builder.addRuleDependencies idx b d
  | .sideConditionSolver =>
      let b := match idx.levelNormalizerProfilesBySolver.find? name with
        | some profile => b.add .levelNormalizerProfile profile.solverName
            s!"profile for solver {name}"
        | none => b
      pure b
  | .conversionPlugin =>
      let b := match idx.levelNormalizerProfilesByPlugin.find? name with
        | some profile => b.add .levelNormalizerProfile profile.solverName
            s!"profile for conversion plugin {name}"
        | none => b
      pure b
  | .levelNormalizerProfile =>
      match idx.levelNormalizerProfilesBySolver.find? name with
      | none => pure b
      | some profile => pure <| Builder.addLevelNormalizerProfileDependencies idx b profile
  | .lfOpaqueConst =>
      match idx.lfOpaqueConsts.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addBindings idx b d.params s!"parameter of lf_opaque {name}"
          match d.checkedTypeExpr? with
          | some ty =>
              pure <| Builder.addCheckedExprHeads idx b ty s!"result type of lf_opaque {name}"
          | none => pure b
  | .lfObjectDef =>
      match idx.lfObjectDefs.find? name with
      | none => pure b
      | some d =>
          let b := Builder.addCheckedExprHeads idx b d.checkedTypeExpr s!"type of lf_def {name}"
          pure <| Builder.addCheckedExprHeads idx b d.checkedValue s!"body of lf_def {name}"
  | .lfJudgmentTheorem =>
      match idx.lfJudgmentTheorems.find? name with
      | none => pure b
      | some d => b.addTheoremDependencies idx d
  | .sideConditionCertificate =>
      match idx.sideConditionCertificatesByCertificateName.find? name with
      | none => pure b
      | some cert =>
          pure <| Builder.addSideConditionCertificate idx b cert
            s!"payload of side-condition certificate {name}"

/-- Process a worklist to a fixed point. -/
partial def processWorklist (idx : Index) (b : Builder) (pos : Nat := 0) : Except String Builder :=
  if h : pos < b.worklist.size then
    let item := b.worklist[pos]
    match processItem idx item b with
    | .ok b' => processWorklist idx b' (pos + 1)
    | .error err => .error err
  else
    .ok b

/-- Compute the closure for one checked theorem or object definition root. -/
def computeClosure (idx : Index) (rootName : Name) : Except String Closure := do
  let rootName := rootName.eraseMacroScopes
  let start : Builder ←
    if idx.lfJudgmentTheorems.contains rootName then
      pure <| ({} : Builder).add .lfJudgmentTheorem rootName s!"seed theorem {rootName}"
    else if idx.lfObjectDefs.contains rootName then
      pure <| ({} : Builder).add .lfObjectDef rootName s!"seed object definition {rootName}"
    else
      throw s!"unknown checked internal declaration '{rootName}' in type theory \
        '{idx.checked.name.eraseMacroScopes}'"
  return (← processWorklist idx start).closure

/-- Whether a declaration name is included anywhere in the closure. -/
def Closure.includesDeclaration (c : Closure) (name : Name) : Bool :=
  let name := name.eraseMacroScopes
  c.syntaxSorts.contains name || c.syntaxAbbrevs.contains name || c.syntaxDefs.contains name ||
    c.judgmentAbbrevs.contains name || c.contextZones.contains name ||
      c.binderClasses.contains name || c.judgments.contains name || c.rules.contains name ||
        c.sideConditionSolvers.contains name || c.conversionPlugins.contains name ||
          c.lfOpaqueConsts.contains name || c.lfObjectDefs.contains name ||
            c.lfJudgmentTheorems.contains name

/-- Metadata names carried by section memberships. -/
def carriedModelSectionNames (checked : CheckedSignature) (c : Closure) : NameSet := Id.run do
  let mut out : NameSet := {}
  for m in checked.modelSectionMemberships do
    if c.includesDeclaration m.declName then
      out := out.insert m.sectionName.eraseMacroScopes
  return out

/-- Whether a rewrite/transport metadata entry is fully supported by the closure. -/
def Closure.carriesRewriteRelation (c : Closure) (m : LFRewriteRelationDecl) : Bool :=
  c.includesDeclaration m.relationName

/-- Whether a rewrite symmetry metadata entry is fully supported by the closure. -/
def Closure.carriesRewriteSymmetry (c : Closure) (m : LFRewriteSymmetryDecl) : Bool :=
  c.includesDeclaration m.symmetryName && c.includesDeclaration m.relationName

/-- Whether a rewrite congruence metadata entry is fully supported by the closure. -/
def Closure.carriesRewriteCongruence (c : Closure) (m : LFRewriteCongruenceDecl) : Bool :=
  c.includesDeclaration m.congruenceName && c.includesDeclaration m.relationName &&
    c.includesDeclaration m.targetHead

/-- Whether a transport-rule metadata entry is fully supported by the closure. -/
def Closure.carriesTransportRule (c : Closure) (m : LFTransportRuleDecl) : Bool :=
  c.includesDeclaration m.ruleName && c.includesDeclaration m.relationName

/-- Whether a transport-position metadata entry is fully supported by the closure. -/
def Closure.carriesTransportPosition (c : Closure) (m : LFTransportPositionDecl) : Bool :=
  c.includesDeclaration m.ruleName && c.includesDeclaration m.targetHead

/-- Filter checked artifacts to the computed report-only fragment. -/
def filterCheckedSignature (checked : CheckedSignature) (c : Closure) : CheckedSignature :=
  let sectionNames := carriedModelSectionNames checked c
  { checked with
    levelParams := checked.levelParams.filter (fun n => c.levelParams.contains n.eraseMacroScopes)
    lfSyntaxSorts := checked.lfSyntaxSorts.filter (fun d => c.syntaxSorts.contains d.name)
    lfSyntaxAbbrevs := checked.lfSyntaxAbbrevs.filter (fun d => c.syntaxAbbrevs.contains d.name)
    lfSyntaxDefs := checked.lfSyntaxDefs.filter (fun d => c.syntaxDefs.contains d.name)
    lfJudgmentAbbrevs := checked.lfJudgmentAbbrevs.filter (fun d =>
      c.judgmentAbbrevs.contains d.name)
    lfSyntaxSortRoles := checked.lfSyntaxSortRoles.filter (fun d =>
      c.syntaxSorts.contains d.sortName.eraseMacroScopes)
    lfContextZones := checked.lfContextZones.filter (fun d => c.contextZones.contains d.name)
    lfBinderClasses := checked.lfBinderClasses.filter (fun d => c.binderClasses.contains d.name)
    lfJudgments := checked.lfJudgments.filter (fun d => c.judgments.contains d.name)
    lfJudgmentRoles := checked.lfJudgmentRoles.filter (fun d =>
      c.judgments.contains d.judgmentName.eraseMacroScopes)
    lfOpaqueConsts := checked.lfOpaqueConsts.filter (fun d => c.lfOpaqueConsts.contains d.name)
    modelVisibilities := checked.modelVisibilities.filter (fun d =>
      c.includesDeclaration d.declName)
    modelSections := checked.modelSections.filter (fun d =>
      sectionNames.contains d.name.eraseMacroScopes)
    modelSectionMemberships := checked.modelSectionMemberships.filter (fun d =>
      c.includesDeclaration d.declName)
    lfSideConditionSolvers := checked.lfSideConditionSolvers.filter (fun d =>
      c.sideConditionSolvers.contains d.name)
    lfConversionPlugins := checked.lfConversionPlugins.filter (fun d =>
      c.conversionPlugins.contains d.name)
    lfLevelNormalizerProfiles := checked.lfLevelNormalizerProfiles.filter (fun d =>
      c.levelNormalizerProfiles.contains d.solverName.eraseMacroScopes)
    lfRules := checked.lfRules.filter (fun d => c.rules.contains d.name)
    lfRuleRoles := checked.lfRuleRoles.filter (fun d =>
      c.rules.contains d.ruleName.eraseMacroScopes)
    lfRewriteRelations := checked.lfRewriteRelations.filter (c.carriesRewriteRelation ·)
    lfRewriteSymmetries := checked.lfRewriteSymmetries.filter (c.carriesRewriteSymmetry ·)
    lfRewriteCongruences := checked.lfRewriteCongruences.filter (c.carriesRewriteCongruence ·)
    lfTransportRules := checked.lfTransportRules.filter (c.carriesTransportRule ·)
    lfTransportPositions := checked.lfTransportPositions.filter (c.carriesTransportPosition ·)
    lfRuleSchemas := checked.lfRuleSchemas.filter (fun d => c.rules.contains d.name)
    lfEnvironment := default
    lfSideConditionCertificates := checked.lfSideConditionCertificates.filter (fun d =>
      c.sideConditionCertificates.contains d.certificateName.eraseMacroScopes)
    lfObjectDefs := checked.lfObjectDefs.filter (fun d => c.lfObjectDefs.contains d.name)
    lfJudgmentTheorems := checked.lfJudgmentTheorems.filter (fun d =>
      c.lfJudgmentTheorems.contains d.name) }

/-- Renderable model-field count for a checked signature. -/
def renderableModelFieldCount (checked : CheckedSignature) (admittedNames : NameSet) : Nat :=
  let obs := LeanTypeModelGeneration.lfModelObligations checked admittedNames
  LeanTypeModelGeneration.countLFModelObligations obs fun o =>
    o.generatedRole == .field && o.renderable

/-- One reportable fragment closure result. -/
structure Report where
  theoryName : Name
  rootName : Name
  flat : HLSignature
  checked : CheckedSignature
  closure : Closure
  fullModelFieldCount : Nat
  fragmentModelFieldCount : Nat
  carriedAdmissions : Array InternalAdmission := #[]
  deriving Inhabited

/-- Build a report-only fragment closure for one theory and root declaration. -/
def buildReport (theoryName rootName : Name) : CommandElabM Report := do
  let some sig ← liftCoreM <| getTheory? theoryName
    | throwError "unknown type theory '{theoryName}'"
  let some checked ← liftCoreM <| getCheckedTheory? theoryName
    | throwError "type theory '{theoryName}' has no checked LF signature"
  let flat ← liftCoreM <| flattenSignature sig
  let idx := mkIndex flat checked
  let closure ← match computeClosure idx rootName with
    | .ok closure => pure closure
    | .error err => throwError err
  let admissions ← liftCoreM <| getInternalAdmissionsForIncludingParents theoryName
  let admittedNames := LeanTypeModelGeneration.internalAdmissionNameSet admissions
  let fragmentChecked := filterCheckedSignature checked closure
  let fragmentAdmissions := admissions.filter (fun a => closure.includesDeclaration a.declName)
  let fragmentAdmittedNames := LeanTypeModelGeneration.internalAdmissionNameSet fragmentAdmissions
  pure {
    theoryName := theoryName.eraseMacroScopes
    rootName := rootName.eraseMacroScopes
    flat := flat
    checked := checked
    closure := closure
    fullModelFieldCount := renderableModelFieldCount checked admittedNames
    fragmentModelFieldCount := renderableModelFieldCount fragmentChecked fragmentAdmittedNames
    carriedAdmissions := fragmentAdmissions }

/-- Reason for an included declaration, if available. -/
def Closure.reason (c : Closure) (name : Name) : String :=
  (c.reasons.find? name.eraseMacroScopes).getD "included by dependency closure"

/-- Render one included declaration line. -/
def includedLine (c : Closure) (name : Name) : String :=
  s!"  - {name.eraseMacroScopes}: {c.reason name}"

/-- Render a category in source order. -/
def renderCategory (title : String) (names : Array Name) (c : Closure) : Array String :=
  if names.isEmpty then #[s!"{title}: none"] else
    #[s!"{title} ({names.size}):"] ++ names.map (includedLine c)

/-- Render metadata names as one diagnostic line. -/
def renderNameListLine (title : String) (names : Array Name) : String :=
  if names.isEmpty then s!"{title}: none" else
    s!"{title}: {String.intercalate ", " (names.toList.map (toString ·.eraseMacroScopes))}"

/-- Source-order included names from an array. -/
def includedNames (xs : Array α) (nameOf : α → Name) (contains : Name → Bool) : Array Name :=
  xs.foldl (init := #[]) fun out x =>
    let n := (nameOf x).eraseMacroScopes
    if contains n then out.push n else out

/-- Metadata entries carried by a fragment, rendered by their primary declaration names. -/
def carriedMetadataNames (checked : CheckedSignature) (c : Closure) : Array Name := Id.run do
  let sectionNames := carriedModelSectionNames checked c
  let mut out := #[]
  for d in checked.lfSyntaxSortRoles do
    if c.syntaxSorts.contains d.sortName.eraseMacroScopes then out := out.push d.sortName
  for d in checked.lfJudgmentRoles do
    if c.judgments.contains d.judgmentName.eraseMacroScopes then out := out.push d.judgmentName
  for d in checked.lfRuleRoles do
    if c.rules.contains d.ruleName.eraseMacroScopes then out := out.push d.ruleName
  for d in checked.modelVisibilities do
    if c.includesDeclaration d.declName then out := out.push d.declName
  for d in checked.modelSections do
    if sectionNames.contains d.name.eraseMacroScopes then out := out.push d.name
  for d in checked.modelSectionMemberships do
    if c.includesDeclaration d.declName then out := out.push d.declName
  for d in checked.lfRewriteRelations do
    if c.carriesRewriteRelation d then out := out.push d.relationName
  for d in checked.lfRewriteSymmetries do
    if c.carriesRewriteSymmetry d then out := out.push d.symmetryName
  for d in checked.lfRewriteCongruences do
    if c.carriesRewriteCongruence d then out := out.push d.congruenceName
  for d in checked.lfTransportRules do
    if c.carriesTransportRule d then out := out.push d.ruleName
  for d in checked.lfTransportPositions do
    if c.carriesTransportPosition d then out := out.push d.ruleName
  return out

/-- Metadata entries dropped by a fragment, rendered by their primary declaration names. -/
def droppedMetadataNames (checked : CheckedSignature) (c : Closure) : Array Name := Id.run do
  let mut out := #[]
  for d in checked.lfSyntaxSortRoles do
    unless c.syntaxSorts.contains d.sortName.eraseMacroScopes do out := out.push d.sortName
  for d in checked.lfJudgmentRoles do
    unless c.judgments.contains d.judgmentName.eraseMacroScopes do out := out.push d.judgmentName
  for d in checked.lfRuleRoles do
    unless c.rules.contains d.ruleName.eraseMacroScopes do out := out.push d.ruleName
  for d in checked.modelVisibilities do
    unless c.includesDeclaration d.declName do out := out.push d.declName
  for d in checked.modelSectionMemberships do
    unless c.includesDeclaration d.declName do out := out.push d.declName
  for d in checked.lfRewriteRelations do
    unless c.carriesRewriteRelation d do out := out.push d.relationName
  for d in checked.lfRewriteSymmetries do
    unless c.carriesRewriteSymmetry d do out := out.push d.symmetryName
  for d in checked.lfRewriteCongruences do
    unless c.carriesRewriteCongruence d do out := out.push d.congruenceName
  for d in checked.lfTransportRules do
    unless c.carriesTransportRule d do out := out.push d.ruleName
  for d in checked.lfTransportPositions do
    unless c.carriesTransportPosition d do out := out.push d.ruleName
  return out

/-- Report string for a computed fragment closure. -/
def reportString (r : Report) : String :=
  let c := r.closure
  let checked := r.checked
  let levelNames := checked.levelParams.filter (fun n => c.levelParams.contains n.eraseMacroScopes)
  let carriedMetadata := carriedMetadataNames checked c
  let droppedMetadata := droppedMetadataNames checked c
  let lines := #[
    s!"theory fragment report for {r.theoryName}.{r.rootName}",
    "mode: report-only; no fragment theory was registered",
    s!"model fields: full={r.fullModelFieldCount}, fragment={r.fragmentModelFieldCount}"]
  let lines := lines ++ renderCategory "level parameters" levelNames c
  let lines := lines ++ renderCategory "syntax sorts"
    (includedNames checked.lfSyntaxSorts (·.name) c.syntaxSorts.contains) c
  let lines := lines ++ renderCategory "syntax abbreviations"
    (includedNames checked.lfSyntaxAbbrevs (·.name) c.syntaxAbbrevs.contains) c
  let lines := lines ++ renderCategory "syntax definitions"
    (includedNames checked.lfSyntaxDefs (·.name) c.syntaxDefs.contains) c
  let lines := lines ++ renderCategory "judgment abbreviations"
    (includedNames checked.lfJudgmentAbbrevs (·.name) c.judgmentAbbrevs.contains) c
  let lines := lines ++ renderCategory "context zones"
    (includedNames checked.lfContextZones (·.name) c.contextZones.contains) c
  let lines := lines ++ renderCategory "binder classes"
    (includedNames checked.lfBinderClasses (·.name) c.binderClasses.contains) c
  let lines := lines ++ renderCategory "judgments"
    (includedNames checked.lfJudgments (·.name) c.judgments.contains) c
  let lines := lines ++ renderCategory "LF opaque constants"
    (includedNames checked.lfOpaqueConsts (·.name) c.lfOpaqueConsts.contains) c
  let lines := lines ++ renderCategory "side-condition solvers"
    (includedNames checked.lfSideConditionSolvers (·.name) c.sideConditionSolvers.contains) c
  let lines := lines ++ renderCategory "conversion plugins"
    (includedNames checked.lfConversionPlugins (·.name) c.conversionPlugins.contains) c
  let lines := lines ++ renderCategory "level-normalizer profiles"
    (includedNames checked.lfLevelNormalizerProfiles (·.solverName)
      c.levelNormalizerProfiles.contains) c
  let lines := lines ++ renderCategory "rules"
    (includedNames checked.lfRules (·.name) c.rules.contains) c
  let lines := lines ++ renderCategory "LF object definitions"
    (includedNames checked.lfObjectDefs (·.name) c.lfObjectDefs.contains) c
  let lines := lines ++ renderCategory "LF judgment theorems"
    (includedNames checked.lfJudgmentTheorems (·.name) c.lfJudgmentTheorems.contains) c
  let lines := lines ++ renderCategory "side-condition certificates"
    (includedNames checked.lfSideConditionCertificates (·.certificateName)
      c.sideConditionCertificates.contains) c
  let carriedAdmissions := r.carriedAdmissions.map (fun a => a.declName.eraseMacroScopes)
  let lines := lines.push (renderNameListLine "carried admissions" carriedAdmissions)
  let lines := lines.push (renderNameListLine "carried metadata" carriedMetadata)
  let lines := lines.push (renderNameListLine "dropped metadata" droppedMetadata)
  String.intercalate "\n" lines.toList

/-- Build and render a theory-fragment report. -/
def reportStringFor (theoryName rootName : Name) : CommandElabM String := do
  return reportString (← buildReport theoryName rootName)

end TheoryFragment

/-- Print the dependency-closure fragment that would be needed for one checked declaration. -/
elab "#print_theory_fragment " theory:ident root:ident : command => do
  logInfo m!"{← TheoryFragment.reportStringFor theory.getId root.getId}"

end InternalLean
