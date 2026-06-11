/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.LFElab.Kernel

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

/-- Retrieve a matching compiled LF checking cache, rebuilding and storing it on miss/mismatch. -/
def getOrBuildCompiledLFCheckCache (theoryName : Name) (checked : CheckedSignature) :
    CoreM CompiledLFCheckCacheLookup := do
  let expected := CompiledLFCheckCacheStamp.ofCheckedSignature checked
  match ← getCompiledLFCheckCache? theoryName with
  | some cache =>
      if cache.stamp == expected then
        pure { cache := cache, status := "hit", rebuilt := false }
      else
        let cache ← mkCompiledLFCheckCache theoryName checked
        setCompiledLFCheckCache theoryName cache
        pure { cache := cache, status := "stale-rebuilt", rebuilt := true }
  | none =>
      let cache ← mkCompiledLFCheckCache theoryName checked
      setCompiledLFCheckCache theoryName cache
      pure { cache := cache, status := "miss", rebuilt := true }

namespace CompiledLFCheckCache

/-- Append a checked LF object definition to a compiled LF checking cache. -/
def appendObjectDef (cache : CompiledLFCheckCache) (d : CheckedLFObjectDef) :
    CompiledLFCheckCache :=
  let defName := d.name.eraseMacroScopes
  let checkedLFDefValues := cache.checkedLFDefValues.insert defName d.checkedValue
  { cache with
    stamp := { cache.stamp with objectDefCount := cache.stamp.objectDefCount + 1 }
    checkedHL := cache.checkedHL.appendBlock { lfObjectDefs := #[checkedLFObjectDefToHLDecl d] }
    lfGlobals := cache.lfGlobals.insert defName
    globalHeads := cache.globalHeads.insert defName (.lfDefinition,
      some (lfFunctionTypeArity d.typeExpr))
    knownLFDefTypes := cache.knownLFDefTypes.insert defName (eraseObjExprScopes d.typeExpr)
    knownLFDefValues := cache.knownLFDefValues.insert defName (eraseObjExprScopes d.value)
    lfObjectDefs := cache.lfObjectDefs.push d
    checkedLFDefValues := checkedLFDefValues }

/-- Append a checked LF judgment theorem to a compiled LF checking cache. -/
def appendJudgmentTheorem (cache : CompiledLFCheckCache) (t : CheckedLFJudgmentTheorem) :
    CompiledLFCheckCache :=
  let theoremName := t.name.eraseMacroScopes
  let structuralCertificateEntries := kernelLFCertificateEntriesOfTheoremsToK #[t]
  let structuralReplayCtx := { cache.structuralKernelReplayBase with
    certificates := cache.structuralKernelReplayBase.certificates ++ structuralCertificateEntries }
  let structuralReplayCtx :=
    if t.binders.isEmpty then
      let stmt? :=
        match t.checkedStructuralKernelDerivation? with
        | some checkedReplay => some checkedReplay.statement
        | none => checkedLFJudgmentTheoremStatementToK t |>.toOption
      match stmt? with
      | some stmt => { structuralReplayCtx with
          theorems := structuralReplayCtx.theorems ++ [{
            name := Kernel.KName.ofName t.name
            statement := stmt }] }
      | none => structuralReplayCtx
    else
      structuralReplayCtx
  let availableStatements :=
    if t.binders.isEmpty then
      let stmt := match t.derivation? with
        | some derivation => checkedLFDerivationStatement derivation
        | none => t.judgmentExpr
      cache.availableLFTheoremStatements.insert theoremName (eraseObjExprScopes stmt)
    else
      cache.availableLFTheoremStatements
  { cache with
    stamp := { cache.stamp with
      judgmentTheoremCount := cache.stamp.judgmentTheoremCount + 1 }
    checkedHL := cache.checkedHL.appendBlock {
      lfJudgmentTheorems := #[checkedLFJudgmentTheoremToHLDecl t] }
    lfGlobals := cache.lfGlobals.insert theoremName
    globalHeads := cache.globalHeads.insert theoremName (.lfTheorem, some t.binders.size)
    availableLFTheoremStatements := availableStatements
    availableLFTheoremNames := cache.availableLFTheoremNames.insert theoremName
    lfJudgmentTheorems := cache.lfJudgmentTheorems.push t
    structuralKernelReplayBase := structuralReplayCtx }

end CompiledLFCheckCache

/-- Return a fallback reason when a block still needs the full checker. -/
def unsupportedIncrementalTheoryBlockReason? (block : HLTheoryBlock) : Option String :=
  if !block.rewriteRelations.isEmpty then
    some "unsupported incremental declaration kind: rewrite_relation"
  else if !block.rewriteSymmetries.isEmpty then
    some "unsupported incremental declaration kind: rewrite_symmetry"
  else if !block.rewriteCongruences.isEmpty then
    some "unsupported incremental declaration kind: rewrite_congruence"
  else if !block.transportRules.isEmpty then
    some "unsupported incremental declaration kind: transport_rule"
  else if !block.transportPositions.isEmpty then
    some "unsupported incremental declaration kind: transport_position"
  else
    none

/-- Count declarations/metadata entries handled by the incremental extension checker. -/
def theoryBlockIncrementalDeclCount (block : HLTheoryBlock) : Nat :=
  block.syntaxSorts.size + block.syntaxAbbrevs.size + block.syntaxDefs.size +
    block.judgmentAbbrevs.size + block.syntaxSortRoles.size + block.contextZones.size +
    block.binderClasses.size + block.judgments.size +
    block.judgmentRoles.size + block.rules.size + block.ruleRoles.size +
    block.sideConditionSolvers.size + block.conversionPlugins.size + block.lfOpaqueConsts.size +
    block.modelVisibilities.size + block.modelSections.size + block.lfObjectDefs.size +
    block.lfJudgmentTheorems.size

/-- Check that an LF-head declaration name does not collide with reserved surface syntax. -/
def checkLFKernelReservedDeclarationName (kind : String) (rawName : Name) : CoreM Unit := do
  if isLFKernelReservedName rawName then
    throwError (lfKernelReservedNameError kind rawName)

/-- Check all LF-head declarations in a flattened signature against reserved surface names. -/
def checkNoKernelReservedLFHeadNamesInSignature (sig : HLSignature) : CoreM Unit := do
  for d in sig.syntaxSorts do
    checkLFKernelReservedDeclarationName "syntax-sort" d.name
  for d in sig.syntaxAbbrevs do
    checkLFKernelReservedDeclarationName "syntax abbreviation" d.name
  for d in sig.syntaxDefs do
    checkLFKernelReservedDeclarationName "syntax definition" d.name
  for d in sig.judgmentAbbrevs do
    checkLFKernelReservedDeclarationName "judgment abbreviation" d.name
  for d in sig.judgments do
    checkLFKernelReservedDeclarationName "judgment" d.name
  for d in sig.rules do
    checkLFKernelReservedDeclarationName "rule" d.name
  for d in sig.lfOpaqueConsts do
    checkLFKernelReservedDeclarationName "LF opaque constant" d.name
  for d in sig.lfObjectDefs do
    checkLFKernelReservedDeclarationName "LF object definition" d.name
  for d in sig.lfJudgmentTheorems do
    checkLFKernelReservedDeclarationName "LF judgment theorem" d.name

/-- Desugar trailing rule binders whose types are judgment statements into premises. -/
def desugarRuleBinderPremises (sigWithBlock : HLSignature) (r : RuleDecl) :
    CoreM RuleDecl := do
  let mut params := #[]
  let mut binderPremises := #[]
  let mut seenPremiseBinder := false
  for b in r.params do
    let isPremiseBinder :=
      b.visibility == .explicit && lfExprIsJudgmentHeaded sigWithBlock b.typeExpr
    if isPremiseBinder then
      seenPremiseBinder := true
      binderPremises := binderPremises.push { name := b.name, judgmentExpr := b.typeExpr }
    else
      if seenPremiseBinder then
        throwError "rule '{r.name}' has judgment-headed binder premise(s) followed by \
          non-premise binder '{b.name}'. Binder-style premises must be trailing; move \
            interleaved premises to the `where premise` form."
      params := params.push b
  pure { r with params := params, premises := binderPremises ++ r.premises }

/-- Desugar binder-style premises in every rule in an extension block. -/
def desugarRuleBinderPremisesInBlock (flatBase : HLSignature) (block : HLTheoryBlock) :
    CoreM HLTheoryBlock := do
  let sigWithBlock := flatBase.appendBlock block
  let rules ← block.rules.mapM (desugarRuleBinderPremises sigWithBlock)
  pure { block with rules := rules }

/-- Check that new declaration names do not collide with the already flattened baseline. -/
def checkNoExtensionNameCollisions (flatBase : HLSignature) (block : HLTheoryBlock) :
    CoreM Unit := do
  let existing := flatBase.nameSet
  let checkName (reserveKernelName : Bool) (seen : NameSet) (kind : String)
      (rawName : Name) : CoreM NameSet := do
    let n := rawName.eraseMacroScopes
    if reserveKernelName then
      checkLFKernelReservedDeclarationName kind rawName
    if seen.contains n then
      throwError "duplicate {kind} declaration '{rawName}' in type-theory block"
    if existing.contains n then
      throwError "declaration '{rawName}' already exists in type theory '{flatBase.name}' or one \
        of its parents"
    pure (seen.insert n)
  let mut seen : NameSet := {}
  for d in block.syntaxSorts do
    seen ← checkName true seen "syntax-sort" d.name
  for d in block.syntaxAbbrevs do
    seen ← checkName true seen "syntax abbreviation" d.name
  for d in block.syntaxDefs do
    seen ← checkName true seen "syntax definition" d.name
  for d in block.judgmentAbbrevs do
    seen ← checkName true seen "judgment abbreviation" d.name
  for d in block.contextZones do
    seen ← checkName false seen "context zone" d.name
  for d in block.binderClasses do
    seen ← checkName false seen "binder class" d.name
  for d in block.judgments do
    seen ← checkName true seen "judgment" d.name
  for d in block.rules do
    seen ← checkName true seen "rule" d.name
  for d in block.sideConditionSolvers do
    seen ← checkName false seen "side-condition solver" d.name
  for d in block.conversionPlugins do
    seen ← checkName false seen "conversion plugin" d.name
  for d in block.lfOpaqueConsts do
    seen ← checkName true seen "LF opaque constant" d.name
  for d in block.lfObjectDefs do
    seen ← checkName true seen "LF object definition" d.name
  for d in block.lfJudgmentTheorems do
    seen ← checkName true seen "LF judgment theorem" d.name

/-- Elaborate implicit applications in just the new extension block. -/
def elaborateImplicitAppsInTheoryBlockExtension (flatBase : HLSignature)
    (priorKnownTypes : LFLocalTypes) (block : HLTheoryBlock) : CoreM HLTheoryBlock := do
  let headSig := flatBase.appendBlock block
  let headLookup := mkImplicitCallableLookupContext headSig
  let syntaxSorts ←
    block.syntaxSorts.mapM
      (elaborateImplicitAppsInSyntaxSortDeclWithLookup headLookup headSig)
  let syntaxAbbrevs ←
    block.syntaxAbbrevs.mapM
      (elaborateImplicitAppsInSyntaxAbbrevDeclWithLookup headLookup headSig)
  let syntaxDefs ←
    block.syntaxDefs.mapM (elaborateImplicitAppsInSyntaxDefDeclWithLookup headLookup headSig)
  let judgmentAbbrevs ←
    block.judgmentAbbrevs.mapM
      (elaborateImplicitAppsInJudgmentAbbrevDeclWithLookup headLookup headSig)
  let judgments ←
    block.judgments.mapM (elaborateImplicitAppsInJudgmentDeclWithLookup headLookup headSig)
  let lfOpaqueConsts ←
    block.lfOpaqueConsts.mapM
      (elaborateImplicitAppsInLFOpaqueConstDeclWithLookup headLookup headSig)
  let rules ← block.rules.mapM (elaborateImplicitAppsInRuleDeclWithLookup headLookup headSig)
  let metaBlock := {
    block with
    syntaxSorts := syntaxSorts
    syntaxAbbrevs := syntaxAbbrevs
    syntaxDefs := syntaxDefs
    judgmentAbbrevs := judgmentAbbrevs
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    rules := rules }
  let sigForObjects := flatBase.appendBlock metaBlock
  let objectLookup := mkImplicitCallableLookupContext sigForObjects
  let mut knownTypes := priorKnownTypes
  let mut lfObjectDefs := #[]
  for d in block.lfObjectDefs do
    let d ← elaborateImplicitAppsInLFObjectDefWithLookup objectLookup sigForObjects knownTypes d
    lfObjectDefs := lfObjectDefs.push d
    knownTypes := knownTypes.insert d.name.eraseMacroScopes (eraseObjExprScopes d.typeExpr)
  let blockForTheorems := { metaBlock with lfObjectDefs := lfObjectDefs }
  let sigForTheorems := flatBase.appendBlock blockForTheorems
  let theoremLookup := mkImplicitCallableLookupContext sigForTheorems
  let lfJudgmentTheorems ←
    block.lfJudgmentTheorems.mapM
      (elaborateImplicitAppsInLFJudgmentTheoremWithLookup theoremLookup sigForTheorems knownTypes)
  pure { blockForTheorems with lfJudgmentTheorems := lfJudgmentTheorems }

/-- Expand syntax and judgment abbreviations in just the new extension block. -/
def expandSyntaxAbbrevsInTheoryBlockExtension (checkedBase : HLSignature)
    (block : HLTheoryBlock) : CoreM HLTheoryBlock := do
  let sigWithRawBlock := checkedBase.appendBlock block
  let syntaxAbbrevs ← block.syntaxAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sigWithRawBlock "syntax_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sigWithRawBlock "syntax_abbrev" a.name "value" locals
        (lfAbbrevExpansionFuel sigWithRawBlock) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let judgmentAbbrevs ← block.judgmentAbbrevs.mapM fun a => do
    let params ← expandSyntaxAbbrevsInBindings sigWithRawBlock "judgment_abbrev" a.name a.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value ←
      expandSyntaxAbbrevsInExpr sigWithRawBlock "judgment_abbrev" a.name "value" locals
        (lfAbbrevExpansionFuel sigWithRawBlock) a.value
    pure { a with name := a.name.eraseMacroScopes, params, value }
  let blockWithAbbrevs := {
    block with
    syntaxAbbrevs := syntaxAbbrevs
    judgmentAbbrevs := judgmentAbbrevs }
  let sigForRest := checkedBase.appendBlock blockWithAbbrevs
  let syntaxDefs ← block.syntaxDefs.mapM fun d => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "syntax_def" d.name d.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let value? ←
      d.value?.mapM (expandSyntaxAbbrevsInExpr sigForRest "syntax_def" d.name "value" locals
        (lfAbbrevExpansionFuel sigForRest))
    pure { d with name := d.name.eraseMacroScopes, params, value? }
  let syntaxSorts ← block.syntaxSorts.mapM fun s => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "syntax_sort" s.name s.params
    pure { s with name := s.name.eraseMacroScopes, params }
  let judgments ← block.judgments.mapM fun j => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "judgment" j.name j.params
    pure { j with name := j.name.eraseMacroScopes, params }
  let lfOpaqueConsts ← block.lfOpaqueConsts.mapM fun o => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "lf_opaque" o.name o.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let typeExpr? ←
      o.typeExpr?.mapM (expandSyntaxAbbrevsInExpr sigForRest "lf_opaque" o.name
        "result type" locals (lfAbbrevExpansionFuel sigForRest))
    pure { o with name := o.name.eraseMacroScopes, params, typeExpr? }
  let rules ← block.rules.mapM fun r => do
    let params ← expandSyntaxAbbrevsInBindings sigForRest "rule" r.name r.params
    let locals := params.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let premises ← r.premises.mapM fun p => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"premise '{p.name.eraseMacroScopes}'" locals
          (lfAbbrevExpansionFuel sigForRest) p.judgmentExpr
      pure { p with judgmentExpr }
    let sideConditions ← r.sideConditions.mapM fun sc => do
      let input ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"side-condition '{sc.name.eraseMacroScopes}'" locals
          (lfAbbrevExpansionFuel sigForRest) sc.input
      pure { sc with input }
    let paramEvidences ← r.paramEvidences.mapM fun ev => do
      let judgmentExpr ←
        expandSyntaxAbbrevsInExpr sigForRest "rule" r.name
          s!"evidence '{ev.name.eraseMacroScopes}'" locals
          (lfAbbrevExpansionFuel sigForRest) ev.judgmentExpr
      pure { ev with judgmentExpr }
    let conclusionExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "rule" r.name "conclusion" locals
        (lfAbbrevExpansionFuel sigForRest) r.conclusionExpr
    pure {
      r with
      name := r.name.eraseMacroScopes
      params := params
      premises := premises
      sideConditions := sideConditions
      paramEvidences := paramEvidences
      conclusionExpr := conclusionExpr }
  let lfObjectDefs ← block.lfObjectDefs.mapM fun d => do
    let typeExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "type" {}
        (lfAbbrevExpansionFuel sigForRest) d.typeExpr
    let value ←
      expandSyntaxAbbrevsInExpr sigForRest "lf_def" d.name "value" {}
        (lfAbbrevExpansionFuel sigForRest) d.value
    pure { d with name := d.name.eraseMacroScopes, typeExpr, value }
  let lfJudgmentTheorems ← block.lfJudgmentTheorems.mapM fun t => do
    let binders ← expandSyntaxAbbrevsInBindings sigForRest "judgment_theorem" t.name t.binders
    let locals := binders.foldl (fun locals b => locals.insert b.name.eraseMacroScopes) {}
    let judgmentExpr ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "statement" locals
        (lfAbbrevExpansionFuel sigForRest) t.judgmentExpr
    let proof ←
      expandSyntaxAbbrevsInExpr sigForRest "judgment_theorem" t.name "proof" locals
        (lfAbbrevExpansionFuel sigForRest) t.proof
    pure { t with name := t.name.eraseMacroScopes, binders, judgmentExpr, proof }
  pure {
    blockWithAbbrevs with
    syntaxSorts := syntaxSorts
    syntaxDefs := syntaxDefs
    judgmentAbbrevs := judgmentAbbrevs
    judgments := judgments
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := block.modelVisibilities.map fun v =>
      { v with declName := v.declName.eraseMacroScopes }
    modelSections := block.modelSections.map fun s => { s with name := s.name.eraseMacroScopes }
    modelSectionMemberships := block.modelSectionMemberships.map fun m =>
      { m with
        sectionName := m.sectionName.eraseMacroScopes
        declName := m.declName.eraseMacroScopes }
    rules := rules
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

/-- Check model-visibility metadata added by an incremental extension. -/
def checkModelVisibilityMetadataForExtension (baseSig candidateSig : HLSignature)
    (block : HLTheoryBlock) : CoreM Unit := do
  let declNames := candidateSig.nameSet
  let mut seen : NameSet := {}
  for v in baseSig.modelVisibilities do
    seen := seen.insert v.declName.eraseMacroScopes
  for v in block.modelVisibilities do
    let n := v.declName.eraseMacroScopes
    if seen.contains n then
      throwError "duplicate model visibility annotation for '{n}' in type theory \
        '{candidateSig.name}'"
    seen := seen.insert n
    unless declNames.contains n do
      throwError "model visibility annotation refers to unknown declaration '{n}' in type theory \
        '{candidateSig.name}'"

/-- Check model-section metadata affected by an incremental extension. -/
def checkModelSectionMetadataForExtension (candidateSig : HLSignature)
    (block : HLTheoryBlock) : CoreM Unit := do
  let declNames := candidateSig.nameSet
  let mut sections : NameSet := {}
  for s in candidateSig.modelSections do
    sections := sections.insert s.name.eraseMacroScopes
  for m in block.modelSectionMemberships do
    let sectionName := m.sectionName.eraseMacroScopes
    let declName := m.declName.eraseMacroScopes
    unless sections.contains sectionName do
      throwError "model section membership for '{declName}' refers to unknown section \
        '{sectionName}' in type theory '{candidateSig.name}'"
    unless declNames.contains declName do
      throwError "model section membership refers to unknown declaration '{declName}' in type \
        theory '{candidateSig.name}'"

/-- Check binder hygiene for one syntax-sort declaration. -/
def checkLFLocalBinderHygieneInSyntaxSortDecl (sig : HLSignature) (s : SyntaxSortDecl) :
    CoreM Unit := do
  for b in s.params do
    checkNoLFLocalBinderShadowingInBinding sig "syntax_sort" s.name b

/-- Check binder hygiene for one syntax-abbreviation declaration. -/
def checkLFLocalBinderHygieneInSyntaxAbbrevDecl (sig : HLSignature) (a : SyntaxAbbrevDecl) :
    CoreM Unit := do
  for b in a.params do
    checkNoLFLocalBinderShadowingInBinding sig "syntax_abbrev" a.name b
  checkNoLFLocalBinderShadowingInExpr sig "syntax_abbrev" a.name "value" a.value

/-- Check binder hygiene for one syntax-definition declaration. -/
def checkLFLocalBinderHygieneInSyntaxDefDecl (sig : HLSignature) (d : SyntaxDefDecl) :
    CoreM Unit := do
  for b in d.params do
    checkNoLFLocalBinderShadowingInBinding sig "syntax_def" d.name b
  if let some value := d.value? then
    checkNoLFLocalBinderShadowingInExpr sig "syntax_def" d.name "value" value

/-- Check binder hygiene for one judgment-abbreviation declaration. -/
def checkLFLocalBinderHygieneInJudgmentAbbrevDecl (sig : HLSignature)
    (a : JudgmentAbbrevDecl) : CoreM Unit := do
  for b in a.params do
    checkNoLFLocalBinderShadowingInBinding sig "judgment_abbrev" a.name b
  checkNoLFLocalBinderShadowingInExpr sig "judgment_abbrev" a.name "value" a.value

/-- Check binder hygiene for one judgment declaration. -/
def checkLFLocalBinderHygieneInJudgmentDecl (sig : HLSignature) (j : JudgmentDecl) :
    CoreM Unit := do
  for b in j.params do
    checkNoLFLocalBinderShadowingInBinding sig "judgment" j.name b

/-- Check binder hygiene for one LF opaque declaration. -/
def checkLFLocalBinderHygieneInLFOpaqueConstDecl (sig : HLSignature) (o : LFOpaqueConstDecl) :
    CoreM Unit := do
  for b in o.params do
    checkNoLFLocalBinderShadowingInBinding sig "lf_opaque" o.name b
  if let some ty := o.typeExpr? then
    checkNoLFLocalBinderShadowingInExpr sig "lf_opaque" o.name "result type" ty

/-- Check binder hygiene for one rule declaration. -/
def checkLFLocalBinderHygieneInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM Unit := do
  for b in r.params do
    checkNoLFLocalBinderShadowingInBinding sig "rule" r.name b
  for p in r.premises do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"premise '{p.name.eraseMacroScopes}'" p.judgmentExpr
  for e in r.paramEvidences do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"evidence '{e.name.eraseMacroScopes}'" e.judgmentExpr
  for sc in r.sideConditions do
    checkNoLFLocalBinderShadowingInExpr sig "rule" r.name
      s!"side-condition '{sc.name.eraseMacroScopes}'" sc.input
  checkNoLFLocalBinderShadowingInExpr sig "rule" r.name "conclusion" r.conclusionExpr

/-- Check binder hygiene for one LF object definition. -/
def checkLFLocalBinderHygieneInLFObjectDefDecl (sig : HLSignature) (d : LFObjectDefDecl) :
    CoreM Unit := do
  checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "type" d.typeExpr
  checkNoLFLocalBinderShadowingInExpr sig "lf_def" d.name "value" d.value

/-- Check binder hygiene for one LF judgment theorem. -/
def checkLFLocalBinderHygieneInLFJudgmentTheoremDecl (sig : HLSignature)
    (t : LFJudgmentTheoremDecl) : CoreM Unit := do
  for b in t.binders do
    checkNoLFLocalBinderShadowingInBinding sig "judgment_theorem" t.name b
  checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "statement"
    t.judgmentExpr
  checkNoLFLocalBinderShadowingInExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Check universe parameters for one syntax-sort declaration. -/
def checkLFUniverseLevelInSyntaxSortDecl (sig : HLSignature) (s : SyntaxSortDecl) :
    CoreM Unit := do
  for b in s.params do
    checkDeclaredLevelParamsInLFBinding sig "syntax_sort" s.name b
  checkDeclaredLevelParamsInLevelExpr sig "syntax_sort" s.name "result universe" s.resultLevel

/-- Check universe parameters for one syntax-abbreviation declaration. -/
def checkLFUniverseLevelInSyntaxAbbrevDecl (sig : HLSignature) (a : SyntaxAbbrevDecl) :
    CoreM Unit := do
  for b in a.params do
    checkDeclaredLevelParamsInLFBinding sig "syntax_abbrev" a.name b
  checkDeclaredLevelParamsInLFExpr sig "syntax_abbrev" a.name "value" a.value

/-- Check universe parameters for one syntax-definition declaration. -/
def checkLFUniverseLevelInSyntaxDefDecl (sig : HLSignature) (d : SyntaxDefDecl) : CoreM Unit := do
  for b in d.params do
    checkDeclaredLevelParamsInLFBinding sig "syntax_def" d.name b
  checkDeclaredLevelParamsInLevelExpr sig "syntax_def" d.name "result universe" d.resultLevel
  if let some value := d.value? then
    checkDeclaredLevelParamsInLFExpr sig "syntax_def" d.name "value" value

/-- Check universe parameters for one judgment-abbreviation declaration. -/
def checkLFUniverseLevelInJudgmentAbbrevDecl (sig : HLSignature) (a : JudgmentAbbrevDecl) :
    CoreM Unit := do
  for b in a.params do
    checkDeclaredLevelParamsInLFBinding sig "judgment_abbrev" a.name b
  checkDeclaredLevelParamsInLFExpr sig "judgment_abbrev" a.name "value" a.value

/-- Check universe parameters for one judgment declaration. -/
def checkLFUniverseLevelInJudgmentDecl (sig : HLSignature) (j : JudgmentDecl) : CoreM Unit := do
  for b in j.params do
    checkDeclaredLevelParamsInLFBinding sig "judgment" j.name b

/-- Check universe parameters for one LF opaque declaration. -/
def checkLFUniverseLevelInLFOpaqueConstDecl (sig : HLSignature) (o : LFOpaqueConstDecl) :
    CoreM Unit := do
  for b in o.params do
    checkDeclaredLevelParamsInLFBinding sig "lf_opaque" o.name b
  if let some ty := o.typeExpr? then
    checkDeclaredLevelParamsInLFExpr sig "lf_opaque" o.name "result type" ty

/-- Check universe parameters for one rule declaration. -/
def checkLFUniverseLevelInRuleDecl (sig : HLSignature) (r : RuleDecl) : CoreM Unit := do
  for b in r.params do
    checkDeclaredLevelParamsInLFBinding sig "rule" r.name b
  for p in r.premises do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"premise '{p.name.eraseMacroScopes}'" p.judgmentExpr
  for e in r.paramEvidences do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"evidence '{e.name.eraseMacroScopes}'" e.judgmentExpr
  for sc in r.sideConditions do
    checkDeclaredLevelParamsInLFExpr sig "rule" r.name
      s!"side-condition '{sc.name.eraseMacroScopes}'" sc.input
  checkDeclaredLevelParamsInLFExpr sig "rule" r.name "conclusion" r.conclusionExpr

/-- Check universe parameters for one LF object definition. -/
def checkLFUniverseLevelInLFObjectDefDecl (sig : HLSignature) (d : LFObjectDefDecl) :
    CoreM Unit := do
  checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "type" d.typeExpr
  checkDeclaredLevelParamsInLFExpr sig "lf_def" d.name "value" d.value

/-- Check universe parameters for one LF judgment theorem. -/
def checkLFUniverseLevelInLFJudgmentTheoremDecl (sig : HLSignature)
    (t : LFJudgmentTheoremDecl) : CoreM Unit := do
  for b in t.binders do
    checkDeclaredLevelParamsInLFBinding sig "judgment_theorem" t.name b
  checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "statement" t.judgmentExpr
  checkDeclaredLevelParamsInLFExpr sig "judgment_theorem" t.name "proof" t.proof

/-- Checked artifacts produced by an incremental theory-extension pass. -/
structure CheckedTheoryDelta where
  syntaxSorts : Array CheckedLFSyntaxSort := #[]
  syntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  syntaxDefs : Array CheckedLFSyntaxDef := #[]
  judgmentAbbrevs : Array CheckedLFJudgmentAbbrev := #[]
  syntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  contextZones : Array CheckedLFContextZone := #[]
  binderClasses : Array CheckedLFBinderClass := #[]
  judgments : Array CheckedLFJudgment := #[]
  judgmentRoles : Array JudgmentRoleDecl := #[]
  opaqueConsts : Array CheckedLFOpaqueConst := #[]
  sideConditionSolvers : Array CheckedLFSideConditionSolver := #[]
  conversionPlugins : Array CheckedLFConversionPlugin := #[]
  levelNormalizerProfiles : Array CheckedLFLevelNormalizerProfile := #[]
  rules : Array CheckedLFRule := #[]
  ruleRoles : Array RuleRoleDecl := #[]
  rewriteRelations : Array LFRewriteRelationDecl := #[]
  rewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  rewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  transportRules : Array LFTransportRuleDecl := #[]
  transportPositions : Array LFTransportPositionDecl := #[]
  ruleSchemas : Array CheckedLFRuleSchema := #[]
  sideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  objectDefs : Array CheckedLFObjectDef := #[]
  judgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  modelVisibilities : Array ModelVisibilityDecl := #[]
  modelSections : Array ModelSectionDecl := #[]
  modelSectionMemberships : Array ModelSectionMembershipDecl := #[]
  deriving Inhabited, Repr, BEq

/-- Append an incrementally checked delta and refresh derived checked-signature caches. -/
def appendCheckedTheoryDelta (checked : CheckedSignature) (delta : CheckedTheoryDelta) :
    CheckedSignature :=
  let lfSyntaxSorts := checked.lfSyntaxSorts ++ delta.syntaxSorts
  let lfSyntaxAbbrevs := checked.lfSyntaxAbbrevs ++ delta.syntaxAbbrevs
  let lfSyntaxDefs := checked.lfSyntaxDefs ++ delta.syntaxDefs
  let lfJudgmentAbbrevs := checked.lfJudgmentAbbrevs ++ delta.judgmentAbbrevs
  let lfSyntaxSortRoles := checked.lfSyntaxSortRoles ++ delta.syntaxSortRoles
  let lfContextZones := checked.lfContextZones ++ delta.contextZones
  let lfBinderClasses := checked.lfBinderClasses ++ delta.binderClasses
  let lfJudgments := checked.lfJudgments ++ delta.judgments
  let lfJudgmentRoles := checked.lfJudgmentRoles ++ delta.judgmentRoles
  let lfOpaqueConsts := checked.lfOpaqueConsts ++ delta.opaqueConsts
  let lfSideConditionSolvers := checked.lfSideConditionSolvers ++ delta.sideConditionSolvers
  let lfConversionPlugins := checked.lfConversionPlugins ++ delta.conversionPlugins
  let lfLevelNormalizerProfiles :=
    checked.lfLevelNormalizerProfiles ++ delta.levelNormalizerProfiles
  let lfRules := checked.lfRules ++ delta.rules
  let lfRuleRoles := checked.lfRuleRoles ++ delta.ruleRoles
  let lfRewriteRelations := checked.lfRewriteRelations ++ delta.rewriteRelations
  let lfRewriteSymmetries := checked.lfRewriteSymmetries ++ delta.rewriteSymmetries
  let lfRewriteCongruences := checked.lfRewriteCongruences ++ delta.rewriteCongruences
  let lfTransportRules := checked.lfTransportRules ++ delta.transportRules
  let lfTransportPositions := checked.lfTransportPositions ++ delta.transportPositions
  let lfRuleSchemas := checked.lfRuleSchemas ++ delta.ruleSchemas
  let lfSideConditionCertificates :=
    checked.lfSideConditionCertificates ++ delta.sideConditionCertificates
  let lfObjectDefs := checked.lfObjectDefs ++ delta.objectDefs
  let lfJudgmentTheorems := checked.lfJudgmentTheorems ++ delta.judgmentTheorems
  let modelVisibilities := checked.modelVisibilities ++ delta.modelVisibilities
  let modelSections := dedupeModelSections (checked.modelSections ++ delta.modelSections)
  let modelSectionMemberships :=
    checked.modelSectionMemberships ++ delta.modelSectionMemberships
  let lfEnvironment : CheckedLFEnvironment := {
    checked.lfEnvironment with
    syntaxSorts := lfSyntaxSorts
    syntaxAbbrevs := lfSyntaxAbbrevs
    syntaxDefs := lfSyntaxDefs
    judgmentAbbrevs := lfJudgmentAbbrevs
    syntaxSortRoles := lfSyntaxSortRoles
    contextZones := lfContextZones
    binderClasses := lfBinderClasses
    judgments := lfJudgments
    judgmentRoles := lfJudgmentRoles
    opaqueConsts := lfOpaqueConsts
    sideConditionSolvers := lfSideConditionSolvers
    conversionPlugins := lfConversionPlugins
    levelNormalizerProfiles := lfLevelNormalizerProfiles
    rules := lfRules
    ruleRoles := lfRuleRoles
    rewriteRelations := lfRewriteRelations
    rewriteSymmetries := lfRewriteSymmetries
    rewriteCongruences := lfRewriteCongruences
    transportRules := lfTransportRules
    transportPositions := lfTransportPositions
    ruleSchemas := lfRuleSchemas
    sideConditionCertificates := lfSideConditionCertificates
    objectDefs := lfObjectDefs
    judgmentTheorems := lfJudgmentTheorems }
  { checked with
    lfSyntaxSorts := lfSyntaxSorts
    lfSyntaxAbbrevs := lfSyntaxAbbrevs
    lfSyntaxDefs := lfSyntaxDefs
    lfJudgmentAbbrevs := lfJudgmentAbbrevs
    lfSyntaxSortRoles := lfSyntaxSortRoles
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfJudgments := lfJudgments
    lfJudgmentRoles := lfJudgmentRoles
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := modelVisibilities
    modelSections := modelSections
    modelSectionMemberships := modelSectionMemberships
    lfSideConditionSolvers := lfSideConditionSolvers
    lfConversionPlugins := lfConversionPlugins
    lfLevelNormalizerProfiles := lfLevelNormalizerProfiles
    lfRules := lfRules
    lfRuleRoles := lfRuleRoles
    lfRewriteRelations := lfRewriteRelations
    lfRewriteSymmetries := lfRewriteSymmetries
    lfRewriteCongruences := lfRewriteCongruences
    lfTransportRules := lfTransportRules
    lfTransportPositions := lfTransportPositions
    lfRuleSchemas := lfRuleSchemas
    lfEnvironment := lfEnvironment
    lfSideConditionCertificates := lfSideConditionCertificates
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

namespace CompiledLFCheckCache

/-- Extend cached LF global names with all globally visible names from one checked delta. -/
def appendDeltaGlobals (globals : NameSet) (delta : CheckedTheoryDelta) : NameSet := Id.run do
  let mut globals := globals
  for s in delta.syntaxSorts do globals := globals.insert s.name.eraseMacroScopes
  for a in delta.syntaxAbbrevs do globals := globals.insert a.name.eraseMacroScopes
  for d in delta.syntaxDefs do globals := globals.insert d.name.eraseMacroScopes
  for a in delta.judgmentAbbrevs do globals := globals.insert a.name.eraseMacroScopes
  for j in delta.judgments do globals := globals.insert j.name.eraseMacroScopes
  for o in delta.opaqueConsts do globals := globals.insert o.name.eraseMacroScopes
  for r in delta.rules do globals := globals.insert r.name.eraseMacroScopes
  for d in delta.objectDefs do globals := globals.insert d.name.eraseMacroScopes
  for t in delta.judgmentTheorems do globals := globals.insert t.name.eraseMacroScopes
  return globals

/-- Extend cached opaque arities with typed/untyped opaque constants from one checked delta. -/
def appendDeltaOpaqueArities (arities : NameMap (Option Nat))
    (delta : CheckedTheoryDelta) : NameMap (Option Nat) := Id.run do
  let mut arities := arities
  for o in delta.opaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
      | none => o.arity?
    arities := arities.insert o.name.eraseMacroScopes arity?
  return arities

/-- Extend cached global-head metadata with heads from one checked delta. -/
def appendDeltaGlobalHeads (heads : NameMap (CheckedLFHeadKind × Option Nat))
    (delta : CheckedTheoryDelta) : NameMap (CheckedLFHeadKind × Option Nat) := Id.run do
  let mut heads := heads
  for s in delta.syntaxSorts do
    heads := heads.insert s.name.eraseMacroScopes (.syntaxSort, some s.arity)
  for d in delta.syntaxDefs do
    heads := heads.insert d.name.eraseMacroScopes (.syntaxDef, some d.params.size)
  for j in delta.judgments do
    heads := heads.insert j.name.eraseMacroScopes (.judgment, some j.arity)
  for o in delta.opaqueConsts do
    let arity? := match o.typeExpr? with
      | some _ => some o.params.size
      | none => o.arity?
    heads := heads.insert o.name.eraseMacroScopes (.opaque, arity?)
  for r in delta.rules do
    heads := heads.insert r.name.eraseMacroScopes (.lfRule, none)
  for d in delta.objectDefs do
    heads := heads.insert d.name.eraseMacroScopes (.lfDefinition,
      some (lfFunctionTypeArity d.typeExpr))
  for t in delta.judgmentTheorems do
    heads := heads.insert t.name.eraseMacroScopes (.lfTheorem, some t.binders.size)
  return heads

/-- Extend cached syntax-sort arities with checked syntax sorts from one delta. -/
def appendDeltaSyntaxSortArities (arities : NameMap Nat)
    (delta : CheckedTheoryDelta) : NameMap Nat := Id.run do
  let mut arities := arities
  for s in delta.syntaxSorts do
    arities := arities.insert s.name.eraseMacroScopes s.arity
  for d in delta.syntaxDefs do
    arities := arities.insert d.name.eraseMacroScopes d.params.size
  return arities

/-- Extend cached judgment arities with checked judgments from one delta. -/
def appendDeltaJudgmentArities (arities : NameMap Nat)
    (delta : CheckedTheoryDelta) : NameMap Nat :=
  delta.judgments.foldl (init := arities) fun arities j =>
    arities.insert j.name.eraseMacroScopes j.arity

/-- Extend cached side-condition solver names with checked solvers from one delta. -/
def appendDeltaSolvers (solvers : NameSet) (delta : CheckedTheoryDelta) : NameSet :=
  delta.sideConditionSolvers.foldl (init := solvers) fun solvers s =>
    solvers.insert s.name.eraseMacroScopes

/-- Extend cached LF definition type/value maps with checked definitions from one delta. -/
def appendDeltaLFDefMaps (typeMap : LFLocalTypes) (valueMap : LFDefinitionValueMap)
    (syntaxValueMap : LFDefinitionValueMap) (checkedValueMap : CheckedLFDefinitionValueMap)
    (delta : CheckedTheoryDelta) :
    LFLocalTypes × LFDefinitionValueMap × LFDefinitionValueMap ×
      CheckedLFDefinitionValueMap := Id.run do
  let mut typeMap := typeMap
  let mut valueMap := valueMap
  let mut syntaxValueMap := syntaxValueMap
  let mut checkedValueMap := checkedValueMap
  for d in delta.syntaxDefs do
    let defName := d.name.eraseMacroScopes
    typeMap := typeMap.insert defName
      (eraseObjExprScopes (syntaxDefTypeExpr (checkedLFSyntaxDefToHLDecl d)))
    if let some checkedValue := checkedLFSyntaxDefValue? d then
      if let some value := syntaxDefValueExpr? (checkedLFSyntaxDefToHLDecl d) then
        syntaxValueMap := syntaxValueMap.insert defName (eraseObjExprScopes value)
      checkedValueMap := checkedValueMap.insert defName checkedValue
  for d in delta.objectDefs do
    let defName := d.name.eraseMacroScopes
    typeMap := typeMap.insert defName (eraseObjExprScopes d.typeExpr)
    valueMap := valueMap.insert defName (eraseObjExprScopes d.value)
    checkedValueMap := checkedValueMap.insert defName d.checkedValue
  return (typeMap, valueMap, syntaxValueMap, checkedValueMap)

/-- Extend cached theorem availability maps with checked judgment theorems from one delta. -/
def appendDeltaTheoremAvailability (statementMap : NameMap ObjExpr) (nameSet : NameSet)
    (delta : CheckedTheoryDelta) : NameMap ObjExpr × NameSet := Id.run do
  let mut statementMap := statementMap
  let mut nameSet := nameSet
  for t in delta.judgmentTheorems do
    let theoremName := t.name.eraseMacroScopes
    if t.binders.isEmpty then
      let stmt := match t.derivation? with
        | some derivation => checkedLFDerivationStatement derivation
        | none => t.judgmentExpr
      statementMap := statementMap.insert theoremName (eraseObjExprScopes stmt)
    nameSet := nameSet.insert theoremName
  return (statementMap, nameSet)

/-- Append one checked extension delta to a compiled LF checking cache. -/
def appendDelta (cache : CompiledLFCheckCache) (checkedHLAfter : HLSignature)
    (checkedAfter : CheckedSignature) (delta : CheckedTheoryDelta) : CompiledLFCheckCache :=
  let (knownLFDefTypes, knownLFDefValues, knownLFSyntaxDefValues, checkedLFDefValues) :=
    appendDeltaLFDefMaps cache.knownLFDefTypes cache.knownLFDefValues
      cache.knownLFSyntaxDefValues cache.checkedLFDefValues delta
  let (availableStatements, availableNames) :=
    appendDeltaTheoremAvailability cache.availableLFTheoremStatements
      cache.availableLFTheoremNames delta
  let lfSyntaxDefs := cache.lfSyntaxDefs ++ delta.syntaxDefs
  let lfOpaqueConsts := cache.lfOpaqueConsts ++ delta.opaqueConsts
  let lfContextZones := cache.lfContextZones ++ delta.contextZones
  let lfBinderClasses := cache.lfBinderClasses ++ delta.binderClasses
  let lfConversionPlugins := cache.lfConversionPlugins ++ delta.conversionPlugins
  let lfObjectDefs := cache.lfObjectDefs ++ delta.objectDefs
  let lfJudgmentTheorems := cache.lfJudgmentTheorems ++ delta.judgmentTheorems
  let structuralKernelReplayBase :=
    match kernelLFReplayContextOfTheoremsToK checkedAfter.lfJudgmentTheorems with
    | .ok ctx => ctx
    | .error _ => cache.structuralKernelReplayBase
  { cache with
    stamp := CompiledLFCheckCacheStamp.ofCheckedSignature checkedAfter
    checkedHL := checkedHLAfter
    lfSyntaxDefs := lfSyntaxDefs
    lfOpaqueConsts := lfOpaqueConsts
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfConversionPlugins := lfConversionPlugins
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems
    lfGlobals := appendDeltaGlobals cache.lfGlobals delta
    opaqueArities := appendDeltaOpaqueArities cache.opaqueArities delta
    globalHeads := appendDeltaGlobalHeads cache.globalHeads delta
    syntaxSortArities := appendDeltaSyntaxSortArities cache.syntaxSortArities delta
    judgmentArities := appendDeltaJudgmentArities cache.judgmentArities delta
    solvers := appendDeltaSolvers cache.solvers delta
    checkedRules := cache.checkedRules ++ delta.rules
    checkedRuleSchemas := cache.checkedRuleSchemas ++ delta.ruleSchemas
    checkedSideConditionCertificates :=
      cache.checkedSideConditionCertificates ++ delta.sideConditionCertificates
    knownLFDefTypes := knownLFDefTypes
    knownLFDefValues := knownLFDefValues
    knownLFSyntaxDefValues := knownLFSyntaxDefValues
    checkedLFDefValues := checkedLFDefValues
    availableLFTheoremStatements := availableStatements
    availableLFTheoremNames := availableNames
    structuralKernelReplayBase := structuralKernelReplayBase }

end CompiledLFCheckCache

/-- Cached kernel-facing replay state shared by all theorem checks in one block. -/
structure IntraBlockKernelReplayContext where
  /-- Owning object theory. -/
  theoryName : Name := Name.anonymous
  /-- Checked syntax definitions used to build structural replay signatures. -/
  lfSyntaxDefs : Array CheckedLFSyntaxDef := #[]
  /-- Checked LF opaque constants used to build structural replay signatures. -/
  lfOpaqueConsts : Array CheckedLFOpaqueConst := #[]
  /-- Checked context zones used to build structural replay signatures. -/
  lfContextZones : Array CheckedLFContextZone := #[]
  /-- Checked binder classes used to build structural replay signatures. -/
  lfBinderClasses : Array CheckedLFBinderClass := #[]
  /-- Checked conversion plugins used to build structural replay signatures. -/
  lfConversionPlugins : Array CheckedLFConversionPlugin := #[]
  /-- Checked primitive rule schemas used to build structural replay signatures. -/
  lfRuleSchemas : Array CheckedLFRuleSchema := #[]
  /-- Checked LF object definitions used to build structural replay signatures. -/
  lfObjectDefs : Array CheckedLFObjectDef := #[]
  /-- Checked LF judgment theorems used to build structural replay signatures. -/
  lfJudgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  /-- Global LF heads used by structural replay fallback assumptions. -/
  lfKernelGlobalHeads : NameMap (CheckedLFHeadKind × Option Nat)
  /-- LF definition values used by structural replay fallback assumptions. -/
  lfKernelDefValues : LFDefinitionValueMap
  /-- Checked LF definition values used by structural replay. -/
  checkedLFDefValues : CheckedLFDefinitionValueMap := {}
  /-- Structural compact signature built from checked artifacts for replay. -/
  structuralKernelSig : Except String Kernel.Signature := .ok default
  /-- Structural replay context built from checked prior theorem artifacts. -/
  structuralReplayCtx : Except String Kernel.KernelLFCheckContext := .ok default
  deriving Inhabited

/-- Build a structural replay signature from a block replay context's checked artifacts. -/
def intraBlockKernelReplayStructuralSignature (ctx : IntraBlockKernelReplayContext)
    (normalizeRules? : Bool := false) : Except String Kernel.Signature :=
  checkedSignatureToKSignature ctx.theoryName ctx.lfSyntaxDefs ctx.lfOpaqueConsts
    ctx.lfContextZones ctx.lfBinderClasses ctx.lfConversionPlugins ctx.lfRuleSchemas
    ctx.lfObjectDefs ctx.lfJudgmentTheorems normalizeRules?

/-- Build cached replay state for a checked baseline plus one checked block delta. -/
def mkIntraBlockKernelReplayContext (sig : HLSignature) (checked : CheckedSignature)
    (delta : CheckedTheoryDelta := {}) (objectDefs : Array CheckedLFObjectDef := #[])
    (theoremCandidates : Array CheckedLFJudgmentTheorem := #[]) :
    IntraBlockKernelReplayContext :=
  let lfSyntaxDefs := checked.lfSyntaxDefs ++ delta.syntaxDefs
  let lfOpaqueConsts := checked.lfOpaqueConsts ++ delta.opaqueConsts
  let lfContextZones := checked.lfContextZones ++ delta.contextZones
  let lfBinderClasses := checked.lfBinderClasses ++ delta.binderClasses
  let lfConversionPlugins := checked.lfConversionPlugins ++ delta.conversionPlugins
  let lfRuleSchemas := checked.lfRuleSchemas ++ delta.ruleSchemas
  let lfObjectDefs := checked.lfObjectDefs ++ objectDefs
  let lfJudgmentTheorems := checked.lfJudgmentTheorems ++ theoremCandidates
  let lfCheckedDefValues := checkedLFDefinitionValues lfSyntaxDefs lfObjectDefs
  { theoryName := sig.name
    lfSyntaxDefs := lfSyntaxDefs
    lfOpaqueConsts := lfOpaqueConsts
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfConversionPlugins := lfConversionPlugins
    lfRuleSchemas := lfRuleSchemas
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems
    lfKernelGlobalHeads := lfGlobalHeadInfo sig
    lfKernelDefValues := lfDefinitionValueMapFromCheckedDefs lfSyntaxDefs lfObjectDefs
    checkedLFDefValues := lfCheckedDefValues
    structuralKernelSig :=
      checkedSignatureToKSignature sig.name lfSyntaxDefs lfOpaqueConsts lfContextZones
        lfBinderClasses lfConversionPlugins lfRuleSchemas lfObjectDefs lfJudgmentTheorems
    structuralReplayCtx := kernelLFReplayContextOfTheoremsToK checked.lfJudgmentTheorems }

/-- Replay-check one theorem against cached block-level kernel state and update availability. -/
def validateLFTheoremKernelReplayInContext (sig : HLSignature)
    (ctx : IntraBlockKernelReplayContext) (t : CheckedLFJudgmentTheorem) :
    CoreM (CheckedLFJudgmentTheorem × IntraBlockKernelReplayContext) := do
  let some shallowDeriv := t.derivation?
    | pure (t, ctx)
  let structuralSig ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' block compact signature" ctx.structuralKernelSig
  let structuralReplayCtx ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' block compact replay context" ctx.structuralReplayCtx
  let structuralAssumptions ← liftStructuralKernelExcept
    s!"judgment_theorem '{t.name}' block compact local assumptions" <|
      kernelLFLocalAssumptionEntriesOfTheoremToK false ctx.checkedLFDefValues t
  let structuralDeriv ← lowerLFDerivationToStructuralKernelWithMode sig ctx.lfKernelGlobalHeads
    ctx.lfKernelDefValues (theoremBinderFreeLocals t) t.name false structuralSig shallowDeriv
  let structuralStmt := Kernel.KernelLFDerivation.statement structuralDeriv
  let structuralLocalReplayCtx := { structuralReplayCtx with
    localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
    assumptions := structuralAssumptions }
  let (structuralDeriv, structuralStmt, checkedStructuralReplay) ←
    try
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' block compact replay" structuralSig
        structuralLocalReplayCtx structuralStmt structuralDeriv
      pure (structuralDeriv, structuralStmt, checkedStructuralReplay)
    catch _ =>
      let structuralSigExpanded ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' block expanded signature" <|
          intraBlockKernelReplayStructuralSignature ctx true
      let structuralExpandedAssumptions ← liftStructuralKernelExcept
        s!"judgment_theorem '{t.name}' block expanded local assumptions" <|
          kernelLFLocalAssumptionEntriesOfTheoremToK true ctx.checkedLFDefValues t
      let structuralDerivExpanded ← lowerLFDerivationToStructuralKernelWithMode sig
        ctx.lfKernelGlobalHeads ctx.lfKernelDefValues (theoremBinderFreeLocals t) t.name true
        structuralSigExpanded shallowDeriv
      let structuralStmtExpanded := Kernel.KernelLFDerivation.statement structuralDerivExpanded
      let structuralExpandedReplayCtx := { structuralReplayCtx with
        localParameters := t.binders.toList.map (fun b => Kernel.KLocalName.ofName b.name)
        assumptions := structuralExpandedAssumptions }
      let checkedStructuralReplay ← checkStructuralKernelReplay
        s!"judgment_theorem '{t.name}' block expanded replay" structuralSigExpanded
        structuralExpandedReplayCtx structuralStmtExpanded structuralDerivExpanded
      pure (structuralDerivExpanded, structuralStmtExpanded, checkedStructuralReplay)
  let t := { t with
    structuralKernelDerivation? := some structuralDeriv
    checkedStructuralKernelDerivation? := some checkedStructuralReplay }
  let structuralReplayCtx :=
    if t.binders.isEmpty then
      { structuralReplayCtx with theorems := structuralReplayCtx.theorems ++ [{
          name := Kernel.KName.ofName t.name
          statement := structuralStmt }] }
    else
      structuralReplayCtx
  pure (t, { ctx with
    structuralReplayCtx := .ok structuralReplayCtx })

/-- Replay-check all new theorem artifacts in one block using one cached kernel signature. -/
def validateLFTheoremKernelReplayBlock (sig : HLSignature)
    (ctx : IntraBlockKernelReplayContext) (theorems : Array CheckedLFJudgmentTheorem) :
    CoreM (Array CheckedLFJudgmentTheorem × IntraBlockKernelReplayContext) := do
  let mut ctx := ctx
  let mut checkedTheorems := #[]
  for t in theorems do
    let (t, ctx') ← validateLFTheoremKernelReplayInContext sig ctx t
    ctx := ctx'
    checkedTheorems := checkedTheorems.push t
  pure (checkedTheorems, ctx)

/-- Check simple role metadata added by one incremental extension block. -/
def checkIncrementalRoleMetadataDelta (flatForCheck : HLSignature)
    (checkedBase : CheckedSignature) (block : HLTheoryBlock) :
    CoreM (Array SyntaxSortRoleDecl × Array JudgmentRoleDecl × Array RuleRoleDecl) := do
  let syntaxSortNames : NameSet :=
    flatForCheck.syntaxSorts.foldl (init := {}) fun acc s => acc.insert s.name.eraseMacroScopes
  let syntaxFamilyNames : NameSet :=
    flatForCheck.syntaxDefs.foldl (init := syntaxSortNames) fun acc d =>
      acc.insert d.name.eraseMacroScopes
  let judgmentNames : NameSet :=
    flatForCheck.judgments.foldl (init := {}) fun acc j => acc.insert j.name.eraseMacroScopes
  let ruleNames : NameSet :=
    flatForCheck.rules.foldl (init := {}) fun acc r => acc.insert r.name.eraseMacroScopes
  let mut seenSortRoles : NameMap NameSet := {}
  for role in checkedBase.lfSyntaxSortRoles do
    let sortName := role.sortName.eraseMacroScopes
    let kinds := (seenSortRoles.find? sortName).getD {}
    seenSortRoles := seenSortRoles.insert sortName (kinds.insert role.kind.eraseMacroScopes)
  let mut syntaxSortRoles := #[]
  for role in block.syntaxSortRoles do
    let sortName := role.sortName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !syntaxFamilyNames.contains sortName then
      throwError "syntax_sort_role for unknown syntax family '{role.sortName}' in type theory \
        '{flatForCheck.name}'"
    let kinds := (seenSortRoles.find? sortName).getD {}
    if kinds.contains kind then
      throwError "duplicate syntax_sort_role '{role.kind}' for syntax sort '{role.sortName}' in \
        type theory '{flatForCheck.name}'"
    seenSortRoles := seenSortRoles.insert sortName (kinds.insert kind)
    syntaxSortRoles := syntaxSortRoles.push { sortName := sortName, kind := kind }
  let mut seenJudgmentRoles : NameMap NameSet := {}
  for role in checkedBase.lfJudgmentRoles do
    let judgmentName := role.judgmentName.eraseMacroScopes
    let kinds := (seenJudgmentRoles.find? judgmentName).getD {}
    seenJudgmentRoles :=
      seenJudgmentRoles.insert judgmentName (kinds.insert role.kind.eraseMacroScopes)
  let mut judgmentRoles := #[]
  for role in block.judgmentRoles do
    let judgmentName := role.judgmentName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !judgmentNames.contains judgmentName then
      throwError "judgment_role for unknown judgment '{role.judgmentName}' in type theory \
        '{flatForCheck.name}'"
    let kinds := (seenJudgmentRoles.find? judgmentName).getD {}
    if kinds.contains kind then
      throwError "duplicate judgment_role '{role.kind}' for judgment '{role.judgmentName}' in \
        type theory '{flatForCheck.name}'"
    seenJudgmentRoles := seenJudgmentRoles.insert judgmentName (kinds.insert kind)
    judgmentRoles := judgmentRoles.push { judgmentName := judgmentName, kind := kind }
  let mut seenRuleRoles : NameMap NameSet := {}
  for role in checkedBase.lfRuleRoles do
    let ruleName := role.ruleName.eraseMacroScopes
    let kinds := (seenRuleRoles.find? ruleName).getD {}
    seenRuleRoles := seenRuleRoles.insert ruleName (kinds.insert role.kind.eraseMacroScopes)
  let mut ruleRoles := #[]
  for role in block.ruleRoles do
    let ruleName := role.ruleName.eraseMacroScopes
    let kind := role.kind.eraseMacroScopes
    if !ruleNames.contains ruleName then
      throwError "rule_role for unknown rule '{role.ruleName}' in type theory '{flatForCheck.name}'"
    let kinds := (seenRuleRoles.find? ruleName).getD {}
    if kinds.contains kind then
      throwError "duplicate rule_role '{role.kind}' for rule '{role.ruleName}' in type theory \
        '{flatForCheck.name}'"
    seenRuleRoles := seenRuleRoles.insert ruleName (kinds.insert kind)
    ruleRoles := ruleRoles.push { ruleName := ruleName, kind := kind }
  pure (syntaxSortRoles, judgmentRoles, ruleRoles)

/-- Check context-zone and binder-class metadata added by one incremental extension block. -/
def checkIncrementalContextBinderMetadataDelta (flatForCheck : HLSignature)
    (checkedBase : CheckedSignature) (block : HLTheoryBlock) :
    CoreM (Array CheckedLFContextZone × Array CheckedLFBinderClass) := do
  let syntaxSortNames : NameSet :=
    flatForCheck.syntaxSorts.foldl (init := {}) fun acc s => acc.insert s.name.eraseMacroScopes
  let mut seenZones : NameSet :=
    checkedBase.lfContextZones.foldl (init := {}) fun acc z => acc.insert z.name.eraseMacroScopes
  let mut checkedContextZones := #[]
  for zone in block.contextZones do
    let zoneName := zone.name.eraseMacroScopes
    let sortName := zone.sortName.eraseMacroScopes
    if seenZones.contains zoneName then
      throwError "duplicate context_zone '{zoneName}' in type theory '{flatForCheck.name}'"
    if !syntaxSortNames.contains sortName then
      throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' uses unknown \
        syntax sort '{zone.sortName}'"
    let mut seenDeps : NameSet := {}
    for dep in zone.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' has \
          duplicate dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !seenZones.contains dep then
        throwError "context_zone '{zone.name}' in type theory '{flatForCheck.name}' depends on \
          unknown or later zone '{dep}'"
    seenZones := seenZones.insert zoneName
    checkedContextZones := checkedContextZones.push (checkedLFContextZoneDeclArtifact zone)
  let mut seenBinderClasses : NameSet :=
    checkedBase.lfBinderClasses.foldl (init := {}) fun acc b =>
      acc.insert b.name.eraseMacroScopes
  let allZones : NameSet :=
    flatForCheck.contextZones.foldl (init := {}) fun acc z => acc.insert z.name.eraseMacroScopes
  let mut checkedBinderClasses := #[]
  for binderClass in block.binderClasses do
    let binderName := binderClass.name.eraseMacroScopes
    let sortName := binderClass.boundSortName.eraseMacroScopes
    let zoneName := binderClass.zoneName.eraseMacroScopes
    if seenBinderClasses.contains binderName then
      throwError "duplicate binder_class '{binderName}' in type theory '{flatForCheck.name}'"
    seenBinderClasses := seenBinderClasses.insert binderName
    if !syntaxSortNames.contains sortName then
      throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' uses \
        unknown syntax sort '{binderClass.boundSortName}'"
    if !allZones.contains zoneName then
      throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' uses \
        unknown context zone '{binderClass.zoneName}'"
    let mut seenDeps : NameSet := {}
    for dep in binderClass.dependsOn do
      let dep := dep.eraseMacroScopes
      if seenDeps.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' has \
          duplicate dependency '{dep}'"
      seenDeps := seenDeps.insert dep
      if !allZones.contains dep then
        throwError "binder_class '{binderClass.name}' in type theory '{flatForCheck.name}' \
          depends on unknown context zone '{dep}'"
    checkedBinderClasses := checkedBinderClasses.push (checkedLFBinderClassDeclArtifact binderClass)
  pure (checkedContextZones, checkedBinderClasses)

/-- Check metadata declarations in a theory block and collect checked delta artifacts. -/
def checkTheoryBlockMetadataDelta (flatForCheck : HLSignature) (checkedBase : CheckedSignature)
    (block : HLTheoryBlock) : CoreM CheckedTheoryDelta := do
  let lfGlobals := lfKnownGlobalNames flatForCheck
  let opaqueArities := lfOpaqueArities flatForCheck
  let globalHeads := lfGlobalHeadInfo flatForCheck
  let lookup := mkLFCheckLookupContext flatForCheck
  let syntaxSortArities : NameMap Nat := lfSyntaxFamilyArities flatForCheck
  let judgmentArities : NameMap Nat := flatForCheck.judgments.foldl (init := {}) fun acc j =>
    acc.insert j.name.eraseMacroScopes j.params.size
  let solvers : NameSet := flatForCheck.sideConditionSolvers.foldl (init := {}) fun acc s =>
    acc.insert s.name.eraseMacroScopes
  let mut checkedSyntaxSorts : Array CheckedLFSyntaxSort := #[]
  for s in block.syntaxSorts do
    checkLFLocalBinderHygieneInSyntaxSortDecl flatForCheck s
    checkLFUniverseLevelInSyntaxSortDecl flatForCheck s
    checkOneSyntaxSortMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
      syntaxSortArities s
    checkedSyntaxSorts :=
      checkedSyntaxSorts.push (← checkedLFSyntaxSortDeclArtifact flatForCheck globalHeads s)
  let mut checkedSyntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  for a in block.syntaxAbbrevs do
    checkLFLocalBinderHygieneInSyntaxAbbrevDecl flatForCheck a
    checkLFUniverseLevelInSyntaxAbbrevDecl flatForCheck a
    checkOneSyntaxAbbrevMetadataInSignature flatForCheck lfGlobals opaqueArities
      syntaxSortArities globalHeads a
    checkedSyntaxAbbrevs :=
      checkedSyntaxAbbrevs.push (← checkedLFSyntaxAbbrevDeclArtifact flatForCheck globalHeads a)
  let blockSyntaxDefNames := block.syntaxDefs.map (fun d => d.name.eraseMacroScopes)
  let mut checkedSyntaxDefs : Array CheckedLFSyntaxDef := #[]
  for _h : i in [:block.syntaxDefs.size] do
    let d := block.syntaxDefs[i]!
    checkNoUnavailableSyntaxDefRefsFrom flatForCheck d blockSyntaxDefNames i
    checkLFLocalBinderHygieneInSyntaxDefDecl flatForCheck d
    checkLFUniverseLevelInSyntaxDefDecl flatForCheck d
    let mirrorSyntaxDefs :=
      (checkedBase.lfSyntaxDefs.map checkedLFSyntaxDefToHLDecl) ++
        (checkedSyntaxDefs.map checkedLFSyntaxDefToHLDecl)
    let mirrorSig := {
      flatForCheck with
      syntaxDefs := mirrorSyntaxDefs.push d
      lfObjectDefs := checkedBase.lfObjectDefs.map checkedLFObjectDefToHLDecl
      lfJudgmentTheorems := checkedBase.lfJudgmentTheorems.map checkedLFJudgmentTheoremToHLDecl
      rules := checkedBase.lfRules.map checkedLFRuleToHLDecl }
    checkOneSyntaxDefMetadataInSignatureSelected mirrorSig lookup flatForCheck lfGlobals
      opaqueArities syntaxSortArities globalHeads d
    checkedSyntaxDefs :=
      checkedSyntaxDefs.push (← checkedLFSyntaxDefDeclArtifact flatForCheck globalHeads d)
  let mut checkedJudgmentAbbrevs : Array CheckedLFJudgmentAbbrev := #[]
  for a in block.judgmentAbbrevs do
    checkLFLocalBinderHygieneInJudgmentAbbrevDecl flatForCheck a
    checkLFUniverseLevelInJudgmentAbbrevDecl flatForCheck a
    checkOneJudgmentAbbrevMetadataInSignature flatForCheck lfGlobals opaqueArities
      syntaxSortArities globalHeads a
    checkedJudgmentAbbrevs := checkedJudgmentAbbrevs.push
      (← checkedLFJudgmentAbbrevDeclArtifact flatForCheck globalHeads a)
  let (checkedSyntaxSortRoles, checkedJudgmentRoles, checkedRuleRoles) ←
    checkIncrementalRoleMetadataDelta flatForCheck checkedBase block
  let (checkedContextZones, checkedBinderClasses) ←
    checkIncrementalContextBinderMetadataDelta flatForCheck checkedBase block
  let mut checkedJudgments : Array CheckedLFJudgment := #[]
  for j in block.judgments do
    checkLFLocalBinderHygieneInJudgmentDecl flatForCheck j
    checkLFUniverseLevelInJudgmentDecl flatForCheck j
    checkOneJudgmentMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
      syntaxSortArities j
    checkedJudgments :=
      checkedJudgments.push (← checkedLFJudgmentDeclArtifact flatForCheck globalHeads j)
  let knownLFDefTypes := mergeLFLocalTypes
    (checkedLFDefinitionTypeMapFromDefs checkedBase.lfSyntaxDefs checkedBase.lfObjectDefs)
    (lfDefinitionTypeMapFromDecls block.lfObjectDefs)
  let mut checkedOpaques : Array CheckedLFOpaqueConst := #[]
  for o in block.lfOpaqueConsts do
    checkLFLocalBinderHygieneInLFOpaqueConstDecl flatForCheck o
    checkLFUniverseLevelInLFOpaqueConstDecl flatForCheck o
    checkOneLFOpaqueConstMetadataInSignature flatForCheck lfGlobals opaqueArities
      syntaxSortArities globalHeads o knownLFDefTypes
    checkedOpaques :=
      checkedOpaques.push (← checkedLFOpaqueConstDeclArtifact flatForCheck globalHeads o)
  checkLFLevelNormalizerProfilesInSignature flatForCheck
  let checkedProfiles :=
    block.levelNormalizerProfiles.map checkedLFLevelNormalizerProfileDeclArtifact
  let allProfiles := checkedBase.lfLevelNormalizerProfiles ++ checkedProfiles
  let checkedSolvers :=
    block.sideConditionSolvers.map (checkedLFSideConditionSolverDeclArtifact allProfiles)
  let mut checkedPlugins : Array CheckedLFConversionPlugin := #[]
  for p in block.conversionPlugins do
    checkOneConversionPluginMetadataInSignature flatForCheck p
    checkedPlugins := checkedPlugins.push (checkedLFConversionPluginDeclArtifact allProfiles p)
  let mut checkedRules : Array CheckedLFRule := #[]
  for r in block.rules do
    checkLFLocalBinderHygieneInRuleDecl flatForCheck r
    checkLFUniverseLevelInRuleDecl flatForCheck r
    let checkedRule ←
      checkOneRuleMetadataInSignature flatForCheck lfGlobals opaqueArities globalHeads
        syntaxSortArities judgmentArities solvers r
    checkedRules := checkedRules.push checkedRule
  let checkedRuleSchemas ←
    match checkedLFRuleSchemasOfRules (checkedBase.lfContextZones ++ checkedContextZones)
        (checkedBase.lfBinderClasses ++ checkedBinderClasses) allProfiles checkedRules with
    | .ok schemas => pure schemas
    | .error err => throwError err
  let checkedCertificates := checkedLFSideConditionCertificatesOfSchemas checkedRuleSchemas
  pure {
    syntaxSorts := checkedSyntaxSorts
    syntaxAbbrevs := checkedSyntaxAbbrevs
    syntaxDefs := checkedSyntaxDefs
    judgmentAbbrevs := checkedJudgmentAbbrevs
    syntaxSortRoles := checkedSyntaxSortRoles
    contextZones := checkedContextZones
    binderClasses := checkedBinderClasses
    judgments := checkedJudgments
    judgmentRoles := checkedJudgmentRoles
    opaqueConsts := checkedOpaques
    sideConditionSolvers := checkedSolvers
    conversionPlugins := checkedPlugins
    levelNormalizerProfiles := checkedProfiles
    rules := checkedRules
    ruleRoles := checkedRuleRoles
    ruleSchemas := checkedRuleSchemas
    sideConditionCertificates := checkedCertificates
    modelVisibilities := block.modelVisibilities
    modelSections := block.modelSections
    modelSectionMemberships := block.modelSectionMemberships }

/-- Stream-check all artifacts in one theory block and return a single appendable delta. -/
def checkTheoryBlockDeltaStreaming (flatForCheck : HLSignature) (checkedBase : CheckedSignature)
    (block : HLTheoryBlock) : CoreM CheckedTheoryDelta := do
  let metadataDelta ← profileLFCheckPhase m!"{flatForCheck.name}: metadata delta" do
    checkTheoryBlockMetadataDelta flatForCheck checkedBase block
  if block.lfObjectDefs.isEmpty && block.lfJudgmentTheorems.isEmpty then
    return metadataDelta
  let ctx0 := mkIntraBlockLFCheckContext flatForCheck checkedBase metadataDelta.rules
    metadataDelta.ruleSchemas metadataDelta.sideConditionCertificates
  let ctx ← profileLFCheckPhase m!"{flatForCheck.name}: object definitions in block" do
    let mut ctx := ctx0
    for d in block.lfObjectDefs do
      checkLFLocalBinderHygieneInLFObjectDefDecl flatForCheck d
      checkLFUniverseLevelInLFObjectDefDecl flatForCheck d
      let (_, ctx') ← checkLFObjectDefInContextSelected ctx d
      ctx := ctx'
    pure ctx
  let ctx ← profileLFCheckPhase m!"{flatForCheck.name}: judgment theorems in block" do
    let mut ctx := ctx
    for t in block.lfJudgmentTheorems do
      checkLFLocalBinderHygieneInLFJudgmentTheoremDecl flatForCheck t
      checkLFUniverseLevelInLFJudgmentTheoremDecl flatForCheck t
      let (_, ctx') ← checkLFJudgmentTheoremInContext ctx t
      ctx := ctx'
    pure ctx
  let checkedTheorems ←
    if ctx.newJudgmentTheorems.isEmpty then
      pure #[]
    else
      let replayCtx := mkIntraBlockKernelReplayContext flatForCheck checkedBase metadataDelta
        ctx.newObjectDefs ctx.newJudgmentTheorems
      Prod.fst <$> profileLFCheckPhase m!"{flatForCheck.name}: theorem replay block" do
        validateLFTheoremKernelReplayBlock flatForCheck replayCtx ctx.newJudgmentTheorems
  pure { metadataDelta with
    objectDefs := ctx.newObjectDefs
    judgmentTheorems := checkedTheorems }

/-- Result of incrementally checking a supported `extend_type_theory` block. -/
structure CheckedTheoryBlockExtensionResult where
  /-- Block shape to store in the source theory registry. -/
  blockForRegistry : HLTheoryBlock
  /-- Final checked signature after appending the delta. -/
  checked : CheckedSignature
  /-- Final checked high-level signature used by later incremental checks. -/
  checkedHL : HLSignature
  /-- Checked delta produced from the extension block. -/
  delta : CheckedTheoryDelta
  deriving Inhabited

/-- Incrementally check a supported theory block against an already flattened baseline. -/
def checkTheoryBlockExtensionIncrementalWithFlatBase (theoryName : Name)
    (flatSourceBase : HLSignature) (checked : CheckedSignature) (block : HLTheoryBlock)
    (checkBase? : Option HLSignature := none) : CoreM CheckedTheoryBlockExtensionResult := do
  if let some reason := unsupportedIncrementalTheoryBlockReason? block then
    throwError "cannot incrementally register extension for type theory '{theoryName}': {reason}"
  profileLFCheckPhase m!"{theoryName}: extension collision check" do
    checkNoExtensionNameCollisions flatSourceBase block
  let priorKnownTypes :=
    checkedLFDefinitionTypeMapFromDefs checked.lfSyntaxDefs checked.lfObjectDefs
  let blockForRegistry ← profileLFCheckPhase m!"{theoryName}: elaborate implicit apps" do
    elaborateImplicitAppsInTheoryBlockExtension flatSourceBase priorKnownTypes block
  let checkedBase ← profileLFCheckPhase m!"{theoryName}: checked-to-HL baseline" do
    match checkBase? with
    | some checkedBase => pure checkedBase
    | none => pure (checkedSignatureIncrementalHLSignature flatSourceBase checked)
  let blockForCheck ← profileLFCheckPhase m!"{theoryName}: expand syntax abbrevs" do
    expandSyntaxAbbrevsInTheoryBlockExtension checkedBase blockForRegistry
  let flatForCheck ← profileLFCheckPhase m!"{theoryName}: append checked block" do
    pure (checkedBase.appendBlock blockForCheck)
  profileLFCheckPhase m!"{theoryName}: model visibility metadata" do
    checkModelVisibilityMetadataForExtension checkedBase flatForCheck blockForCheck
  profileLFCheckPhase m!"{theoryName}: model section metadata" do
    checkModelSectionMetadataForExtension flatForCheck blockForCheck
  let delta ← profileLFCheckPhase m!"{theoryName}: check theory block delta" do
    checkTheoryBlockDeltaStreaming flatForCheck checked blockForCheck
  let checked ← profileLFCheckPhase m!"{theoryName}: append checked delta" do
    pure (appendCheckedTheoryDelta checked delta)
  pure {
    blockForRegistry := blockForRegistry
    checked := checked
    checkedHL := flatForCheck
    delta := delta }

/-- Incrementally check a supported `extend_type_theory` block against a checked baseline. -/
def checkTheoryBlockExtensionIncremental (theoryName : Name) (sig : HLSignature)
    (checked : CheckedSignature) (block : HLTheoryBlock) (checkBase? : Option HLSignature := none) :
    CoreM CheckedTheoryBlockExtensionResult := do
  let flatSourceBase ← profileLFCheckPhase m!"{theoryName}: flatten source base" do
    flattenSignature sig
  checkTheoryBlockExtensionIncrementalWithFlatBase theoryName flatSourceBase checked block
    checkBase?

/-- Check a candidate signature with the direct-LF checker and report command errors. -/
def checkSignatureForRegistration (sig : HLSignature) : CoreM CheckedSignature := do
  let flat ← flattenSignature sig
  checkNoDuplicateNamesInSignature flat
  checkNoKernelReservedLFHeadNamesInSignature flat
  checkModelVisibilityMetadataInSignature flat
  checkModelSectionMetadataInSignature flat
  let flat ← expandSyntaxAbbrevsInSignature flat
  checkLFLocalBinderHygieneMetadata flat
  checkLFUniverseLevelMetadata flat
  checkLFLevelNormalizerProfilesInSignature flat
  let lfRules ← checkRuleMetadataInSignature flat
  checkLFRewriteTransportMetadata flat
  let (lfObjectDefsFromDecls, lfJudgmentTheoremsFromDecls) ←
    checkLFObjectArtifactsInSignatureStreaming flat lfRules
  let lfObjectDefs := lfObjectDefsFromDecls
  let lfJudgmentTheoremsRaw := lfJudgmentTheoremsFromDecls
  let (lfSyntaxSorts, lfSyntaxAbbrevs, lfSyntaxDefs, lfJudgmentAbbrevs, lfContextZones,
    lfBinderClasses, lfJudgments, lfOpaqueConsts, lfSideConditionSolvers, lfConversionPlugins,
      lfLevelNormalizerProfiles) ←
      checkedLFDeclarations flat
  let lfSyntaxSortRoles := flat.syntaxSortRoles.map fun r =>
    { sortName := r.sortName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfJudgmentRoles := flat.judgmentRoles.map fun r =>
    { judgmentName := r.judgmentName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfRuleRoles := flat.ruleRoles.map fun r =>
    { ruleName := r.ruleName.eraseMacroScopes, kind := r.kind.eraseMacroScopes }
  let lfRewriteRelations := flat.rewriteRelations.map fun r =>
    { relationName := r.relationName.eraseMacroScopes
      lhsParam := r.lhsParam.eraseMacroScopes
      rhsParam := r.rhsParam.eraseMacroScopes }
  let lfRewriteSymmetries := flat.rewriteSymmetries.map fun r =>
    { symmetryName := r.symmetryName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      evidenceParam := r.evidenceParam.eraseMacroScopes }
  let lfRewriteCongruences := flat.rewriteCongruences.map fun r =>
    { congruenceName := r.congruenceName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      targetHead := r.targetHead.eraseMacroScopes
      argumentIndex := r.argumentIndex
      evidenceParam := r.evidenceParam.eraseMacroScopes }
  let lfTransportRules := flat.transportRules.map fun r =>
    { ruleName := r.ruleName.eraseMacroScopes
      relationName := r.relationName.eraseMacroScopes
      evidencePremise := r.evidencePremise.eraseMacroScopes
      sourcePremise := r.sourcePremise.eraseMacroScopes }
  let lfTransportPositions := flat.transportPositions.map fun p =>
    { ruleName := p.ruleName.eraseMacroScopes
      targetHead := p.targetHead.eraseMacroScopes
      argumentIndex := p.argumentIndex }
  let lfRuleSchemas ←
    match checkedLFRuleSchemasOfRules lfContextZones lfBinderClasses lfLevelNormalizerProfiles
        lfRules with
    | .ok schemas => pure schemas
    | .error err => throwError err
  let lfSideConditionCertificates := checkedLFSideConditionCertificatesOfSchemas lfRuleSchemas
  let replayDelta : CheckedTheoryDelta := {
    syntaxSorts := lfSyntaxSorts
    syntaxAbbrevs := lfSyntaxAbbrevs
    syntaxDefs := lfSyntaxDefs
    judgmentAbbrevs := lfJudgmentAbbrevs
    syntaxSortRoles := lfSyntaxSortRoles
    contextZones := lfContextZones
    binderClasses := lfBinderClasses
    judgments := lfJudgments
    judgmentRoles := lfJudgmentRoles
    opaqueConsts := lfOpaqueConsts
    sideConditionSolvers := lfSideConditionSolvers
    conversionPlugins := lfConversionPlugins
    levelNormalizerProfiles := lfLevelNormalizerProfiles
    rules := lfRules
    ruleRoles := lfRuleRoles
    rewriteRelations := lfRewriteRelations
    rewriteSymmetries := lfRewriteSymmetries
    rewriteCongruences := lfRewriteCongruences
    transportRules := lfTransportRules
    transportPositions := lfTransportPositions
    ruleSchemas := lfRuleSchemas
    sideConditionCertificates := lfSideConditionCertificates }
  let replayBase : CheckedSignature := {
    name := flat.name.eraseMacroScopes
    levelParams := flat.levelParams.map Name.eraseMacroScopes }
  let replayCtx := mkIntraBlockKernelReplayContext flat replayBase replayDelta lfObjectDefs
    lfJudgmentTheoremsRaw
  let (lfJudgmentTheorems, _) ←
    validateLFTheoremKernelReplayBlock flat replayCtx lfJudgmentTheoremsRaw
  let flat ← expandSurfaceFunctionsInSignature flat
  let lfEnvironment : CheckedLFEnvironment :=
    { theoryName := flat.name.eraseMacroScopes
      levelParams := flat.levelParams.map Name.eraseMacroScopes
      syntaxSorts := lfSyntaxSorts
      syntaxAbbrevs := lfSyntaxAbbrevs
      syntaxDefs := lfSyntaxDefs
      judgmentAbbrevs := lfJudgmentAbbrevs
      syntaxSortRoles := lfSyntaxSortRoles
      contextZones := lfContextZones
      binderClasses := lfBinderClasses
      judgments := lfJudgments
      judgmentRoles := lfJudgmentRoles
      opaqueConsts := lfOpaqueConsts
      sideConditionSolvers := lfSideConditionSolvers
      conversionPlugins := lfConversionPlugins
      levelNormalizerProfiles := lfLevelNormalizerProfiles
      rules := lfRules
      ruleRoles := lfRuleRoles
      rewriteRelations := lfRewriteRelations
      rewriteSymmetries := lfRewriteSymmetries
      rewriteCongruences := lfRewriteCongruences
      transportRules := lfTransportRules
      transportPositions := lfTransportPositions
      ruleSchemas := lfRuleSchemas
      sideConditionCertificates := lfSideConditionCertificates
      objectDefs := lfObjectDefs
      judgmentTheorems := lfJudgmentTheorems }
  pure {
    name := flat.name
    levelParams := flat.levelParams.map Name.eraseMacroScopes
    lfSyntaxSorts := lfSyntaxSorts
    lfSyntaxAbbrevs := lfSyntaxAbbrevs
    lfSyntaxDefs := lfSyntaxDefs
    lfJudgmentAbbrevs := lfJudgmentAbbrevs
    lfSyntaxSortRoles := lfSyntaxSortRoles
    lfContextZones := lfContextZones
    lfBinderClasses := lfBinderClasses
    lfJudgments := lfJudgments
    lfJudgmentRoles := lfJudgmentRoles
    lfOpaqueConsts := lfOpaqueConsts
    modelVisibilities := flat.modelVisibilities.map (fun v =>
      { v with declName := v.declName.eraseMacroScopes })
    modelSections := dedupeModelSections flat.modelSections
    modelSectionMemberships := flat.modelSectionMemberships.map (fun m =>
      { m with
        sectionName := m.sectionName.eraseMacroScopes
        declName := m.declName.eraseMacroScopes })
    lfSideConditionSolvers := lfSideConditionSolvers
    lfConversionPlugins := lfConversionPlugins
    lfLevelNormalizerProfiles := lfLevelNormalizerProfiles
    lfRules := lfRules
    lfRuleRoles := lfRuleRoles
    lfRewriteRelations := lfRewriteRelations
    lfRewriteSymmetries := lfRewriteSymmetries
    lfRewriteCongruences := lfRewriteCongruences
    lfTransportRules := lfTransportRules
    lfTransportPositions := lfTransportPositions
    lfRuleSchemas := lfRuleSchemas
    lfEnvironment := lfEnvironment
    lfSideConditionCertificates := lfSideConditionCertificates
    lfObjectDefs := lfObjectDefs
    lfJudgmentTheorems := lfJudgmentTheorems }

end InternalLean
