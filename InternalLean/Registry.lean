/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public meta import InternalLean.DSL
public meta import Lean.PrettyPrinter

/-!
# Registries for user-declared type theories

This file contains the Lean-visible anchor types and persistent environment
extensions used by the type-theory frontend, internal declarations, source
documentation, admissions, and semantic-transport metadata.
-/

namespace InternalLean

/-- Lean-visible marker type for a declared object type theory.

A generated declaration such as `TinyNat.theory : InternalLean.TheoryAnchor` is an
editor/navigation anchor and registry handle. The trusted semantics of a theory remain
in the checked artifacts stored by the registry and replay validators. -/
public inductive TheoryAnchor where
  /-- The unique marker value for a theory anchor. -/
  | mk : TheoryAnchor
  deriving Inhabited

/-- Canonical Lean declaration name for the editor/navigation anchor of a theory. -/
public meta def theoryAnchorName (theoryName : Lean.Name) : Lean.Name :=
  theoryName ++ `theory

/-- Lean-visible marker type for a top-level internal object declaration.

Generated declarations such as `TinyNat.double : InternalLean.InternalDeclarationAnchor`
are editor/navigation handles for object-theory declarations. They do not interpret the
object declaration as a Lean definition or theorem. -/
public inductive InternalDeclarationAnchor where
  /-- The unique marker value for an internal declaration anchor. -/
  | mk : InternalDeclarationAnchor
  deriving Inhabited

/-- Lean-visible marker type used for editor navigation to declarations inside a type-theory
block. The generated declarations are hidden implementation anchors; the checked artifacts remain
in the InternalLean registries. -/
public inductive InternalTheoryDeclarationAnchor where
  /-- The unique marker value for an internal type-theory declaration anchor. -/
  | mk : InternalTheoryDeclarationAnchor
  deriving Inhabited

/-- Lean-visible marker type for experimental quoted LF terms.

Generated declarations in `T.LFQuote` have this type, or a function type ending in this type.
They are frontend quotation stubs only; they are reflected back to `ObjExpr` and checked by the LF
checker before any InternalLean declaration is registered. -/
public inductive LFQuoteTerm where
  /-- Dummy inhabitant used by generated quote-stub definitions. -/
  | mk : LFQuoteTerm
  deriving Inhabited

/-- Namespace containing generated quoted-LF frontend stubs for one type theory. -/
public meta def lfQuoteNamespace (theoryName : Lean.Name) : Lean.Name :=
  theoryName ++ `LFQuote

/-- Lean declaration name for a generated quoted-LF frontend stub. -/
public meta def lfQuoteDeclName (theoryName sourceName : Lean.Name) : Lean.Name :=
  lfQuoteNamespace theoryName ++ sourceName.eraseMacroScopes

/-- Canonical hidden Lean declaration name for an object-theory source declaration anchor. -/
public meta def internalTheoryDeclarationAnchorName (theoryName sourceName : Lean.Name) :
    Lean.Name :=
  theoryName ++ `_internalLeanDecl ++ sourceName.eraseMacroScopes

/-- Lean-visible marker proposition used only to populate the editor infoview for
object-theory tactic scripts. The string payloads record the object theory, local
object context, and current object goal; they are not part of the trusted kernel. -/
public inductive InternalObjectGoalView (theory : String) (context : String) (target : String) :
  Prop where
  /-- Marker constructor; generated infoview metavariables are never solved through this value. -/
  | marker : InternalObjectGoalView theory context target

/-- Lean-visible marker proposition used for hover text on names in internal tactic scripts. -/
public inductive InternalHoverView (theory : String) (kind : String) (name : String)
    (typeOrStatement : String) : Prop where
  /-- Marker constructor; generated hover metavariables are never solved through this value. -/
  | marker : InternalHoverView theory kind name typeOrStatement

end InternalLean

@[expose] public meta section

open Lean Elab Command

namespace InternalLean

syntax (name := internalObjectGoalViewPretty) "object_goal" ident " : " ttExpr : «term»
syntax (name := internalObjectGoalViewPrettyWithContext)
  "object_goal_context" ident str " : " ttExpr : «term»
syntax (name := internalObjectGoalViewPrettyRaw) "object_goal_raw" ident " : " str : «term»
syntax (name := internalObjectGoalViewPrettyWithContextRaw)
  "object_goal_context_raw" ident str " : " str : «term»
declare_syntax_cat internalHoverKind
syntax "local_assumption" : internalHoverKind
syntax "internal_definition" : internalHoverKind
syntax "lf_constant" : internalHoverKind
syntax "rule" : internalHoverKind
syntax "theorem" : internalHoverKind
syntax "syntax_sort" : internalHoverKind
syntax "judgment" : internalHoverKind
syntax ident : internalHoverKind

syntax (name := internalHoverViewPretty)
  "internal" internalHoverKind ident " : " ppLine ttExpr : «term»
syntax (name := internalHoverViewPrettyRaw)
  "internal" internalHoverKind ident " : " ppLine str : «term»

macro_rules
  | `(object_goal $_:ident : $_:ttExpr) => `(True)
  | `(object_goal_context $_:ident $_:str : $_:ttExpr) => `(True)
  | `(object_goal_raw $_:ident : $_:str) => `(True)
  | `(object_goal_context_raw $_:ident $_:str : $_:str) => `(True)
  | `(internal $_:internalHoverKind $_:ident : $_:ttExpr) => `(True)
  | `(internal $_:internalHoverKind $_:ident : $_:str) => `(True)

/-- Parse object-theory text back through the object-expression grammar for display when possible.
This is editor metadata only: failed parses fall back to a raw string literal rather than affecting
checking of the object proof. -/
def parseInternalObjectGoalViewTTExprSyntax (s : String) :
  Lean.PrettyPrinter.Delaborator.DelabM (Option (TSyntax `ttExpr)) := do
  match Lean.Parser.runParserCategory (← getEnv) `ttExpr s with
  | .ok stx => pure (some ⟨stx⟩)
  | .error _ => pure none

/-- Delaborate the object-theory infoview marker as object-goal syntax, not as a giant
string literal. -/
@[app_delab InternalObjectGoalView] def delabInternalObjectGoalView :
  Lean.PrettyPrinter.Delaborator.Delab := do
  let args := (← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr).getAppArgs
  let (theory, context, target) ←
    match args with
    | #[Lean.Expr.lit (Lean.Literal.strVal theory),
        Lean.Expr.lit (Lean.Literal.strVal context),
        Lean.Expr.lit (Lean.Literal.strVal target)] => pure (theory, context, target)
    | _ => Lean.PrettyPrinter.Delaborator.failure
  let theoryStx := mkIdent (Name.mkSimple theory)
  let targetStx? ← parseInternalObjectGoalViewTTExprSyntax target
  let contextStx : TSyntax `str := ⟨Syntax.mkStrLit context⟩
  let targetRawStx : TSyntax `str := ⟨Syntax.mkStrLit target⟩
  if context == "  (empty object context)" then
    match targetStx? with
    | some targetStx => `(object_goal $theoryStx:ident : $targetStx:ttExpr)
    | none => `(object_goal_raw $theoryStx:ident : $targetRawStx:str)
  else
    match targetStx? with
    | some targetStx => `(object_goal_context $theoryStx:ident $contextStx:str : $targetStx:ttExpr)
    | none => `(object_goal_context_raw $theoryStx:ident $contextStx:str : $targetRawStx:str)

/-- Fallback identifier used for unknown hover declaration kinds. -/
def internalHoverKindIdentName : String → Name
  | "local assumption" => `local_assumption
  | "internal definition" => `internal_definition
  | "LF constant" => `lf_constant
  | "syntax sort" => `syntax_sort
  | other => other.toName

/-- Syntax token used for a hover declaration kind in compact hover display. -/
def internalHoverKindSyntax (kind : String) :
    Lean.PrettyPrinter.Delaborator.DelabM (TSyntax `internalHoverKind) := do
  match kind with
  | "local assumption" => `(internalHoverKind| local_assumption)
  | "internal definition" => `(internalHoverKind| internal_definition)
  | "LF constant" => `(internalHoverKind| lf_constant)
  | "rule" => `(internalHoverKind| rule)
  | "theorem" => `(internalHoverKind| theorem)
  | "syntax sort" => `(internalHoverKind| syntax_sort)
  | "judgment" => `(internalHoverKind| judgment)
  | other => pure ⟨mkIdent (internalHoverKindIdentName other)⟩

/-- Delaborate an internal hover marker into compact source-like text. -/
@[app_delab InternalHoverView] def delabInternalHoverView :
  Lean.PrettyPrinter.Delaborator.Delab := do
  let args := (← Lean.PrettyPrinter.Delaborator.SubExpr.getExpr).getAppArgs
  let (theory, kind, name, typeOrStatement) ←
    match args with
    | #[Lean.Expr.lit (Lean.Literal.strVal theory),
        Lean.Expr.lit (Lean.Literal.strVal kind),
        Lean.Expr.lit (Lean.Literal.strVal name),
        Lean.Expr.lit (Lean.Literal.strVal typeOrStatement)] =>
        pure (theory, kind, name, typeOrStatement)
    | _ => Lean.PrettyPrinter.Delaborator.failure
  let fullNameStx := mkIdent (theory.toName ++ name.toName)
  let kindStx ← internalHoverKindSyntax kind
  let typeStx? ← parseInternalObjectGoalViewTTExprSyntax typeOrStatement
  let typeRawStx : TSyntax `str := ⟨Syntax.mkStrLit typeOrStatement⟩
  match typeStx? with
  | some typeStx =>
      `(internal $kindStx:internalHoverKind $fullNameStx:ident : $typeStx:ttExpr)
  | none =>
      `(internal $kindStx:internalHoverKind $fullNameStx:ident : $typeRawStx:str)

/-- Append declaration-block metadata to a high-level signature while preserving source order within
all declaration classes. -/
def HLSignature.appendBlock (sig : HLSignature) (block : HLTheoryBlock) : HLSignature :=
  { sig with
    syntaxSorts := sig.syntaxSorts ++ block.syntaxSorts
    syntaxAbbrevs := sig.syntaxAbbrevs ++ block.syntaxAbbrevs
    syntaxDefs := sig.syntaxDefs ++ block.syntaxDefs
    judgmentAbbrevs := sig.judgmentAbbrevs ++ block.judgmentAbbrevs
    syntaxSortRoles := sig.syntaxSortRoles ++ block.syntaxSortRoles
    contextZones := sig.contextZones ++ block.contextZones
    binderClasses := sig.binderClasses ++ block.binderClasses
    judgments := sig.judgments ++ block.judgments
    judgmentRoles := sig.judgmentRoles ++ block.judgmentRoles
    rules := sig.rules ++ block.rules
    ruleRoles := sig.ruleRoles ++ block.ruleRoles
    rewriteRelations := sig.rewriteRelations ++ block.rewriteRelations
    rewriteSymmetries := sig.rewriteSymmetries ++ block.rewriteSymmetries
    rewriteCongruences := sig.rewriteCongruences ++ block.rewriteCongruences
    transportRules := sig.transportRules ++ block.transportRules
    transportPositions := sig.transportPositions ++ block.transportPositions
    sideConditionSolvers := sig.sideConditionSolvers ++ block.sideConditionSolvers
    conversionPlugins := sig.conversionPlugins ++ block.conversionPlugins
    lfOpaqueConsts := sig.lfOpaqueConsts ++ block.lfOpaqueConsts
    modelVisibilities := sig.modelVisibilities ++ block.modelVisibilities
    modelSections := sig.modelSections ++ block.modelSections
    modelSectionMemberships := sig.modelSectionMemberships ++ block.modelSectionMemberships
    lfObjectDefs := sig.lfObjectDefs ++ block.lfObjectDefs
    lfJudgmentTheorems := sig.lfJudgmentTheorems ++ block.lfJudgmentTheorems }

/-- Persistent entries for the high-level theory registry. -/
inductive TheoryEntry where
  /-- Register or replace a high-level signature. -/
  | sig : HLSignature → TheoryEntry
  /-- Add a staged LF opaque constant to an existing signature. -/
  | lfOpaqueConst : Name → LFOpaqueConstDecl → TheoryEntry
  /-- Add a staged LF/object definition to an existing signature. -/
  | lfObjectDef : Name → LFObjectDefDecl → TheoryEntry
  /-- Add a staged LF judgment theorem to an existing signature. -/
  | lfJudgmentTheorem : Name → LFJudgmentTheoremDecl → TheoryEntry
  /-- Add a theory-local ergonomic object macro. -/
  | macro : Name → ObjectMacro → TheoryEntry
  /-- Add non-semantic role metadata for a theory-local object constant or macro. -/
  | role : Name → ObjectRole → TheoryEntry
  deriving Inhabited, Repr

/-- Environment extension storing currently declared high-level signatures by name. -/
initialize theoryExt : SimplePersistentEnvExtension TheoryEntry (NameMap HLSignature) ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.theoryExt
    addEntryFn := fun m e =>
      match e with
      | .sig sig => m.insert sig.name sig
      | .lfOpaqueConst theoryName d =>
          match m.find? theoryName with
          | some sig =>
                  let sig := { sig with lfOpaqueConsts := sig.lfOpaqueConsts.push d }
                  m.insert theoryName sig
          | none => m
      | .lfObjectDef theoryName d =>
          match m.find? theoryName with
          | some sig => m.insert theoryName { sig with lfObjectDefs := sig.lfObjectDefs.push d }
          | none => m
      | .lfJudgmentTheorem theoryName t =>
          match m.find? theoryName with
          | some sig =>
              let sig := { sig with lfJudgmentTheorems := sig.lfJudgmentTheorems.push t }
              m.insert theoryName sig
          | none => m
      | .macro theoryName mac =>
          match m.find? theoryName with
          | some sig => m.insert theoryName { sig with macros := sig.macros.push mac }
          | none => m
      | .role theoryName role =>
          match m.find? theoryName with
          | some sig => m.insert theoryName { sig with roles := sig.roles.push role }
          | none => m
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .sig sig => m.insert sig.name sig
          | .lfOpaqueConst theoryName d =>
              match m.find? theoryName with
              | some sig =>
                  let sig := { sig with lfOpaqueConsts := sig.lfOpaqueConsts.push d }
                  m.insert theoryName sig
              | none => m
          | .lfObjectDef theoryName d =>
              match m.find? theoryName with
              | some sig => m.insert theoryName { sig with lfObjectDefs := sig.lfObjectDefs.push d }
              | none => m
          | .lfJudgmentTheorem theoryName t =>
              match m.find? theoryName with
              | some sig =>
              let sig := { sig with lfJudgmentTheorems := sig.lfJudgmentTheorems.push t }
              m.insert theoryName sig
              | none => m
          | .macro theoryName mac =>
              match m.find? theoryName with
              | some sig => m.insert theoryName { sig with macros := sig.macros.push mac }
              | none => m
          | .role theoryName role =>
              match m.find? theoryName with
              | some sig => m.insert theoryName { sig with roles := sig.roles.push role }
              | none => m
  }

/-- Persistent entries for checked signatures. Each entry replaces the checked artifact
for its theory name. -/
inductive CheckedTheoryEntry where
  /-- Store a checked signature. -/
  | sig : CheckedSignature → CheckedTheoryEntry

/-- Environment extension storing checked signatures by theory name. -/
initialize checkedTheoryExt :
  SimplePersistentEnvExtension CheckedTheoryEntry (NameMap CheckedSignature) ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.checkedTheoryExt
    addEntryFn := fun m e =>
      match e with
      | .sig checked => m.insert checked.name checked
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .sig checked => m.insert checked.name checked
  }

/-- Persistent entries for cached high-level signatures reconstructed from checked artifacts. -/
inductive CheckedHLSignatureEntry where
  /-- Store a flattened checked high-level signature for one theory. -/
  | sig : Name → HLSignature → CheckedHLSignatureEntry

/-- Environment extension storing checked high-level signatures by theory name.

The cache is a performance aid for long files with many small `extend_type_theory` or
`internal def` commands: it avoids reconstructing the whole high-level checking baseline from the
full `CheckedSignature` after every small update. The checked artifact remains authoritative. -/
initialize checkedHLSignatureExt :
  SimplePersistentEnvExtension CheckedHLSignatureEntry (NameMap HLSignature) ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.checkedHLSignatureExt
    addEntryFn := fun m e =>
      match e with
      | .sig theoryName sig => m.insert theoryName sig
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .sig theoryName sig => m.insert theoryName sig
  }

/-- Cheap consistency stamp for a derived compiled LF checking cache. -/
structure CompiledLFCheckCacheStamp where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Number of opt-in LF universe parameters. -/
  levelParamCount : Nat := 0
  /-- Number of checked syntax sorts. -/
  syntaxSortCount : Nat := 0
  /-- Number of checked syntax abbreviations. -/
  syntaxAbbrevCount : Nat := 0
  /-- Number of checked syntax definitions. -/
  syntaxDefCount : Nat := 0
  /-- Number of checked judgment abbreviations. -/
  judgmentAbbrevCount : Nat := 0
  /-- Number of checked context zones. -/
  contextZoneCount : Nat := 0
  /-- Number of checked binder classes. -/
  binderClassCount : Nat := 0
  /-- Number of checked judgments. -/
  judgmentCount : Nat := 0
  /-- Number of checked opaque constants. -/
  opaqueConstCount : Nat := 0
  /-- Number of checked side-condition solvers. -/
  sideConditionSolverCount : Nat := 0
  /-- Number of checked conversion plugins. -/
  conversionPluginCount : Nat := 0
  /-- Number of checked rules. -/
  ruleCount : Nat := 0
  /-- Number of checked rule schemas. -/
  ruleSchemaCount : Nat := 0
  /-- Number of checked LF object definitions. -/
  objectDefCount : Nat := 0
  /-- Number of checked LF judgment theorems. -/
  judgmentTheoremCount : Nat := 0
  /-- Number of checked side-condition certificates. -/
  sideConditionCertificateCount : Nat := 0
  deriving Inhabited, Repr, BEq

namespace CompiledLFCheckCacheStamp

/-- Compute the cache stamp for a checked signature. -/
def ofCheckedSignature (checked : CheckedSignature) : CompiledLFCheckCacheStamp :=
  { theoryName := checked.name.eraseMacroScopes
    levelParamCount := checked.levelParams.size
    syntaxSortCount := checked.lfSyntaxSorts.size
    syntaxAbbrevCount := checked.lfSyntaxAbbrevs.size
    syntaxDefCount := checked.lfSyntaxDefs.size
    judgmentAbbrevCount := checked.lfJudgmentAbbrevs.size
    contextZoneCount := checked.lfContextZones.size
    binderClassCount := checked.lfBinderClasses.size
    judgmentCount := checked.lfJudgments.size
    opaqueConstCount := checked.lfOpaqueConsts.size
    sideConditionSolverCount := checked.lfSideConditionSolvers.size
    conversionPluginCount := checked.lfConversionPlugins.size
    ruleCount := checked.lfRules.size
    ruleSchemaCount := checked.lfRuleSchemas.size
    objectDefCount := checked.lfObjectDefs.size
    judgmentTheoremCount := checked.lfJudgmentTheorems.size
    sideConditionCertificateCount := checked.lfSideConditionCertificates.size }

/-- Whether a stamp still matches the current checked signature. -/
def matchesCheckedSignature (stamp : CompiledLFCheckCacheStamp)
    (checked : CheckedSignature) : Bool :=
  stamp == ofCheckedSignature checked

end CompiledLFCheckCacheStamp

/-- Derived compiled LF checking/replay context for one checked type theory.

The checked signature remains authoritative; this cache stores maps and kernel replay data derived
from checked artifacts so small incremental declarations can avoid rebuilding full-theory staging
structures. -/
structure CompiledLFCheckCache where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Cheap consistency stamp for the checked artifacts used to build this cache. -/
  stamp : CompiledLFCheckCacheStamp
  /-- Flattened checked high-level signature used by incremental checking. -/
  checkedHL : HLSignature
  /-- Known LF global names. -/
  lfGlobals : NameSet
  /-- Declared LF opaque arities. -/
  opaqueArities : NameMap (Option Nat)
  /-- Resolved LF global-head table. -/
  globalHeads : NameMap (CheckedLFHeadKind × Option Nat)
  /-- Syntax-sort arities. -/
  syntaxSortArities : NameMap Nat
  /-- Judgment arities. -/
  judgmentArities : NameMap Nat
  /-- Declared side-condition solvers. -/
  solvers : NameSet
  /-- Checked rules available to theorem checking. -/
  checkedRules : Array CheckedLFRule := #[]
  /-- Checked rule schemas available to kernel replay. -/
  checkedRuleSchemas : Array CheckedLFRuleSchema := #[]
  /-- Checked side-condition certificates available to kernel replay. -/
  checkedSideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  /-- Available LF definition result types. -/
  knownLFDefTypes : NameMap ObjExpr := {}
  /-- Available LF object-definition values. -/
  knownLFDefValues : NameMap ObjExpr := {}
  /-- Available checked syntax-definition values, unfolded lazily by checker lookups. -/
  knownLFSyntaxDefValues : NameMap ObjExpr := {}
  /-- Available checked LF definition values. -/
  checkedLFDefValues : NameMap CheckedLFExpr := {}
  /-- Available binder-free LF theorem statements. -/
  availableLFTheoremStatements : NameMap ObjExpr := {}
  /-- Available LF theorem names. -/
  availableLFTheoremNames : NameSet := {}
  /-- Kernel replay signature for the checked base theory. -/
  kernelSig : Signature
  /-- Kernel replay context containing prior theorem/certificate entries. -/
  kernelReplayBase : KernelLFCheckContext := {}
  deriving Inhabited

/-- State for compiled LF checking caches.

The `dirty` set tracks theory caches updated in the current module. The persistent extension exports
one final full cache per dirty theory instead of serializing every intermediate full-cache snapshot.
-/
structure CompiledLFCheckCacheStore where
  /-- Current compiled caches by theory name, including imported and local updates. -/
  caches : NameMap CompiledLFCheckCache := {}
  /-- Theory names whose caches were updated in this module. -/
  dirty : NameSet := {}
  deriving Inhabited

/-- Persistent entries for compiled LF checking caches. -/
inductive CompiledLFCheckCacheEntry where
  /-- Store a compiled checker cache for one theory in exported `.olean` data. -/
  | cache : Name → CompiledLFCheckCache → CompiledLFCheckCacheEntry
  /-- Mark a theory cache as changed locally; this small marker is not exported. -/
  | touch : Name → CompiledLFCheckCacheEntry
  deriving Inhabited

namespace CompiledLFCheckCacheStore

/-- Add an entry produced in the current module to the in-memory cache store. -/
def addLocalEntry (store : CompiledLFCheckCacheStore)
    (entry : CompiledLFCheckCacheEntry) : CompiledLFCheckCacheStore :=
  match entry with
  | .cache theoryName cache =>
      let theoryName := theoryName.eraseMacroScopes
      { caches := store.caches.insert theoryName cache
        dirty := store.dirty.insert theoryName }
  | .touch theoryName =>
      { store with dirty := store.dirty.insert theoryName.eraseMacroScopes }

/-- Add an entry imported from another module to the cache store. Imported caches are available but
are not dirty in the importing module. -/
def addImportedEntry (store : CompiledLFCheckCacheStore)
    (entry : CompiledLFCheckCacheEntry) : CompiledLFCheckCacheStore :=
  match entry with
  | .cache theoryName cache =>
      { store with caches := store.caches.insert theoryName.eraseMacroScopes cache }
  | .touch _ => store

/-- Export one final cache snapshot for each theory touched in the current module. -/
def exportEntries (store : CompiledLFCheckCacheStore) : Array CompiledLFCheckCacheEntry := Id.run do
  let mut entries := #[]
  for theoryName in store.dirty do
    if let some cache := store.caches.find? theoryName then
      entries := entries.push (.cache theoryName cache)
  return entries

end CompiledLFCheckCacheStore

/-- Environment extension storing derived compiled LF checking caches by theory name. -/
initialize compiledLFCheckCacheExt :
    SimplePersistentEnvExtension CompiledLFCheckCacheEntry CompiledLFCheckCacheStore ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.compiledLFCheckCacheExt
    addEntryFn := CompiledLFCheckCacheStore.addLocalEntry
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun store es =>
        es.foldl (init := store) CompiledLFCheckCacheStore.addImportedEntry
    exportEntriesFnEx? := some fun _env store _localEntries =>
      .uniform (CompiledLFCheckCacheStore.exportEntries store)
  }

/-- Retrieve a compiled LF checking cache, if one is stored for the theory. -/
def getCompiledLFCheckCache? (theoryName : Name) : CoreM (Option CompiledLFCheckCache) := do
  return (compiledLFCheckCacheExt.getState (← getEnv)).caches.find? theoryName.eraseMacroScopes

/-- Store or replace a compiled LF checking cache in an environment. -/
def setCompiledLFCheckCacheInEnv (env : Environment) (theoryName : Name)
    (cache : CompiledLFCheckCache) : Environment :=
  let theoryName := theoryName.eraseMacroScopes
  let env := compiledLFCheckCacheExt.modifyState env fun store =>
    { caches := store.caches.insert theoryName cache
      dirty := store.dirty.insert theoryName }
  compiledLFCheckCacheExt.addEntry env (.touch theoryName)

/-- Store or replace a compiled LF checking cache for one theory. -/
def setCompiledLFCheckCache (theoryName : Name) (cache : CompiledLFCheckCache) : CoreM Unit := do
  modifyEnv fun env => setCompiledLFCheckCacheInEnv env theoryName cache

/-- Persistent profile record for a theory or internal-declaration registration event. -/
structure InternalRegistrationProfile where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Theory-local declaration name or registration event label. -/
  declName : Name
  /-- Registration strategy used for this event. -/
  strategy : String
  /-- Existing checked object definitions before this declaration. -/
  priorObjectDefs : Nat := 0
  /-- Existing checked judgment theorems before this declaration. -/
  priorJudgmentTheorems : Nat := 0
  /-- Existing checked LF opaque constants before this declaration. -/
  priorOpaqueConsts : Nat := 0
  /-- Existing checked rules before this declaration. -/
  priorRules : Nat := 0
  /-- Existing checked LF metadata declarations before this declaration. -/
  priorMetadataDecls : Nat := 0
  /-- Number of LF object definitions rechecked by this registration. -/
  recheckedObjectDefs : Nat := 0
  /-- Number of LF judgment theorems rechecked by this registration. -/
  recheckedJudgmentTheorems : Nat := 0
  /-- Number of LF opaque constants rechecked by this registration. -/
  recheckedOpaqueConsts : Nat := 0
  /-- Number of checked rules rechecked by this registration. -/
  recheckedRules : Nat := 0
  /-- Number of LF metadata declarations rechecked by this registration. -/
  recheckedMetadataDecls : Nat := 0
  /-- Number of new declarations checked incrementally. -/
  incrementallyChecked : Nat := 0
  /-- Cache lookup/update status for this registration event, when applicable. -/
  cacheStatus? : Option String := none
  /-- Whether this event rebuilt the compiled LF checking cache before checking. -/
  cacheRebuilt : Bool := false
  /-- Number of candidate declarations overlaid on the cached checking context. -/
  cacheOverlayDecls : Nat := 0
  /-- Whether kernel replay validation reused the compiled replay cache. -/
  kernelReplayCacheHit : Bool := false
  deriving Inhabited, Repr, BEq

/-- Persistent entries for registration profiles. -/
inductive InternalRegistrationProfileEntry where
  /-- Record one registration event. -/
  | profile : InternalRegistrationProfile → InternalRegistrationProfileEntry
  deriving Inhabited, Repr

/-- Per-theory registration profiles. -/
abbrev InternalRegistrationProfileState := NameMap (Array InternalRegistrationProfile)

initialize internalRegistrationProfileExt : SimplePersistentEnvExtension
    InternalRegistrationProfileEntry InternalRegistrationProfileState ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.internalRegistrationProfileExt
    addEntryFn := fun m e =>
      match e with
      | .profile p =>
          let xs := (m.find? p.theoryName).getD #[]
          m.insert p.theoryName (xs.push p)
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .profile p =>
              let xs := (m.find? p.theoryName).getD #[]
              m.insert p.theoryName (xs.push p)
  }

/-- The checked shape of an internal declaration admitted by `sorry`. -/
inductive InternalAdmissionKind where
  /-- An admitted typed LF opaque constant, generated from an object-sort-shaped annotation. -/
  | lfOpaque
  /-- A theorem-shaped admission, checked as an LF judgment statement but not as a model field. -/
  | judgmentTheorem
  /-- An admitted derived syntax-family definition, not a model field. -/
  | syntaxDef
  deriving Inhabited, Repr, BEq

namespace InternalAdmissionKind

/-- Human-readable label for admitted declaration diagnostics. -/
def label : InternalAdmissionKind → String
  | .lfOpaque => "lf_opaque"
  | .judgmentTheorem => "judgment theorem"
  | .syntaxDef => "syntax_def"

/-- User-facing source command category for admitted declaration diagnostics. -/
def sourceNoun : InternalAdmissionKind → String
  | .lfOpaque => "internal def"
  | .judgmentTheorem => "internal theorem"
  | .syntaxDef => "syntax_def"

end InternalAdmissionKind

/-- Persistent record for an internal declaration whose body was admitted by `sorry`. -/
structure InternalAdmission where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Theory-local object declaration name. -/
  declName : Name
  /-- Lean-visible anchor generated for the admitted declaration. -/
  anchorName : Name
  /-- Source-level binders before `:`. -/
  params : Array HLBinding := #[]
  /-- Source-level annotation after `:`. -/
  typeExpr : ObjExpr
  /-- Checked admission category. -/
  kind : InternalAdmissionKind := .lfOpaque
  deriving Inhabited, Repr, BEq

/-- Persistent entries for internal declaration admissions. -/
inductive InternalAdmissionEntry where
  /-- Record one admitted top-level internal declaration. -/
  | admission : InternalAdmission → InternalAdmissionEntry
  deriving Inhabited, Repr

/-- Per-theory internal `sorry` admissions. -/
abbrev InternalAdmissionState := NameMap (Array InternalAdmission)

/-- Environment extension storing explicit internal declaration admissions. -/
initialize internalAdmissionExt :
  SimplePersistentEnvExtension InternalAdmissionEntry InternalAdmissionState ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.internalAdmissionExt
    addEntryFn := fun m e =>
      match e with
      | .admission a =>
          let as := (m.find? a.theoryName).getD #[]
          m.insert a.theoryName (as.push a)
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .admission a =>
              let as := (m.find? a.theoryName).getD #[]
              m.insert a.theoryName (as.push a)
  }

/-- A generated model-side Lean declaration whose body intentionally uses `sorry` for an
admitted internal declaration. -/
structure InternalAdmissionTransport where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Theory-local admitted declaration. -/
  declName : Name
  /-- Target model/interface structure name used by the generated declaration. -/
  structureName : Name
  /-- Generated Lean declaration name. -/
  generatedName : Name
  deriving Inhabited, Repr, BEq

/-- Persistent entries for generated admitted-declaration transports. -/
inductive InternalAdmissionTransportEntry where
  /-- Record one generated Lean-side admitted transport declaration. -/
  | transport : InternalAdmissionTransport → InternalAdmissionTransportEntry
  deriving Inhabited, Repr

/-- Per-theory admitted transport declarations. -/
abbrev InternalAdmissionTransportState := NameMap (Array InternalAdmissionTransport)

/-- Environment extension storing generated declarations that intentionally depend on Lean
`sorryAx`. -/
initialize internalAdmissionTransportExt :
  SimplePersistentEnvExtension InternalAdmissionTransportEntry InternalAdmissionTransportState ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.internalAdmissionTransportExt
    addEntryFn := fun m e =>
      match e with
      | .transport t =>
          let ts := (m.find? t.theoryName).getD #[]
          m.insert t.theoryName (ts.push t)
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .transport t =>
              let ts := (m.find? t.theoryName).getD #[]
              m.insert t.theoryName (ts.push t)
  }

/-- Source declaration classes that can carry user-written documentation. -/
inductive SourceDocRole where
  | theory
  | primitiveType
  | primitiveTerm
  | primitiveEq
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
  | lfOpaque
  | lfObjectDef
  | lfJudgmentTheorem
  | internalDef
  deriving Inhabited, Repr, BEq

namespace SourceDocRole

/-- User-facing label for documentation diagnostics. -/
def label : SourceDocRole → String
  | .theory => "theory"
  | .primitiveType => "primitive type"
  | .primitiveTerm => "primitive term"
  | .primitiveEq => "primitive equality"
  | .syntaxSort => "syntax sort"
  | .syntaxAbbrev => "syntax abbreviation"
  | .syntaxDef => "syntax definition"
  | .judgmentAbbrev => "judgment abbreviation"
  | .contextZone => "context zone"
  | .binderClass => "binder class"
  | .judgment => "judgment"
  | .rule => "rule"
  | .sideConditionSolver => "side-condition solver"
  | .conversionPlugin => "conversion plugin"
  | .lfOpaque => "LF opaque constant"
  | .lfObjectDef => "LF object definition"
  | .lfJudgmentTheorem => "LF judgment theorem"
  | .internalDef => "internal def"

end SourceDocRole

/-- Persistent source documentation attached to a type-theory declaration or internal declaration.
-/
structure SourceDoc where
  /-- Owning object theory. -/
  theoryName : Name
  /-- Source declaration class. -/
  role : SourceDocRole
  /-- Theory-local declaration name, or the theory name for the theory doc itself. -/
  sourceName : Name
  /-- User-written docstring text with comment delimiters removed. -/
  doc : String
  deriving Inhabited, Repr, BEq

/-- Persistent source-documentation entries. -/
inductive SourceDocEntry where
  /-- Record one source docstring. -/
  | doc : SourceDoc → SourceDocEntry
  deriving Inhabited, Repr

/-- Per-theory source-documentation state. -/
abbrev SourceDocState := NameMap (Array SourceDoc)

/-- Environment extension storing docstrings captured from custom type-theory commands. -/
initialize sourceDocExt : SimplePersistentEnvExtension SourceDocEntry SourceDocState ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.sourceDocExt
    addEntryFn := fun m e =>
      match e with
      | .doc d =>
          let docs := (m.find? d.theoryName).getD #[]
          m.insert d.theoryName (docs.push d)
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .doc d =>
              let docs := (m.find? d.theoryName).getD #[]
              m.insert d.theoryName (docs.push d)
  }

/-- Persistent entries mapping object rewrite rules to generated semantic transport lemmas. -/
inductive SemanticTransportEntry where
  /-- Register that `rewriteName` is semantically replayed by `lemmaName` in `theoryName`. -/
  | map (theoryName rewriteName lemmaName : Name) : SemanticTransportEntry

/-- Per-theory mappings from object rewrite names to semantic transport lemma names. -/
abbrev SemanticTransportState := NameMap (NameMap Name)

/-- Environment extension storing semantic transport mappings for generated theorems. -/
initialize semanticTransportExt :
  SimplePersistentEnvExtension SemanticTransportEntry SemanticTransportState ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.semanticTransportExt
    addEntryFn := fun m e =>
      match e with
      | .map theoryName rewriteName lemmaName =>
          let theoryMap := (m.find? theoryName).getD {}
          m.insert theoryName (theoryMap.insert rewriteName lemmaName)
    addImportedFn := fun entries =>
      entries.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m e =>
          match e with
          | .map theoryName rewriteName lemmaName =>
              let theoryMap := (m.find? theoryName).getD {}
              m.insert theoryName (theoryMap.insert rewriteName lemmaName)
  }

/-- Return the registered high-level signatures. -/
def getTheories : CoreM (NameMap HLSignature) := do
  return theoryExt.getState (← getEnv)

/-- Look up a declared high-level theory. -/
def getTheory? (nm : Name) : CoreM (Option HLSignature) := do
  return (← getTheories).find? nm

/-- Return the registered checked signatures. -/
def getCheckedTheories : CoreM (NameMap CheckedSignature) := do
  return checkedTheoryExt.getState (← getEnv)

/-- Look up a checked theory artifact. -/
def getCheckedTheory? (nm : Name) : CoreM (Option CheckedSignature) := do
  return (← getCheckedTheories).find? nm

/-- Register or replace a checked theory artifact. -/
def registerCheckedTheory (checked : CheckedSignature) : CoreM Unit := do
  modifyEnv fun env => checkedTheoryExt.addEntry env (.sig checked)

/-- Return cached checked high-level signatures. -/
def getCheckedHLSignatures : CoreM (NameMap HLSignature) := do
  return checkedHLSignatureExt.getState (← getEnv)

/-- Look up a cached checked high-level signature. -/
def getCheckedHLSignature? (nm : Name) : CoreM (Option HLSignature) := do
  return (← getCheckedHLSignatures).find? nm

/-- Register or replace a cached checked high-level signature. -/
def registerCheckedHLSignature (theoryName : Name) (sig : HLSignature) : CoreM Unit := do
  modifyEnv fun env => checkedHLSignatureExt.addEntry env (.sig theoryName sig)

/-- Return registration profile entries. -/
def getInternalRegistrationProfiles : CoreM InternalRegistrationProfileState := do
  return internalRegistrationProfileExt.getState (← getEnv)

/-- Return registration profile entries for one theory. -/
def getInternalRegistrationProfilesFor (theoryName : Name) :
    CoreM (Array InternalRegistrationProfile) := do
  return ((← getInternalRegistrationProfiles).find? theoryName).getD #[]

/-- Record one registration profile entry. -/
def registerInternalRegistrationProfile (p : InternalRegistrationProfile) : CoreM Unit := do
  modifyEnv fun env => internalRegistrationProfileExt.addEntry env (.profile p)

/-- Return all recorded internal `sorry` admissions. -/
def getInternalAdmissions : CoreM InternalAdmissionState := do
  return internalAdmissionExt.getState (← getEnv)

/-- Return recorded internal `sorry` admissions for one theory. -/
def getInternalAdmissionsFor (theoryName : Name) : CoreM (Array InternalAdmission) := do
  return ((← getInternalAdmissions).find? theoryName).getD #[]

/-- Deduplicate admissions by source theory/declaration name while preserving order. -/
def dedupeInternalAdmissions (admissions : Array InternalAdmission) : Array InternalAdmission :=
  Id.run do
  let mut seen : NameSet := {}
  let mut out := #[]
  for a in admissions do
    let key := a.theoryName.eraseMacroScopes ++ a.declName.eraseMacroScopes
    unless seen.contains key do
      seen := seen.insert key
      out := out.push a
  return out

/-- Return recorded internal `sorry` admissions inherited by a theory through its parent chain. -/
partial def getInternalAdmissionsForIncludingParents (theoryName : Name) (seen : NameSet := {}) :
  CoreM (Array InternalAdmission) := do
  let theoryName := theoryName.eraseMacroScopes
  if seen.contains theoryName then
    return #[]
  let seen := seen.insert theoryName
  let direct ← getInternalAdmissionsFor theoryName
  match ← getTheory? theoryName with
  | none => return direct
  | some sig =>
      let mut out := #[]
      for parent in sig.parents do
        out := out ++ (← getInternalAdmissionsForIncludingParents parent seen)
      return dedupeInternalAdmissions (out ++ direct)

/-- Return all recorded admitted-declaration model transports. -/
def getInternalAdmissionTransports : CoreM InternalAdmissionTransportState := do
  return internalAdmissionTransportExt.getState (← getEnv)

/-- Return recorded admitted-declaration model transports for one theory. -/
def getInternalAdmissionTransportsFor (theoryName : Name) :
  CoreM (Array InternalAdmissionTransport) := do
  return ((← getInternalAdmissionTransports).find? theoryName).getD #[]

/-- Record a generated admitted-declaration model transport. -/
def registerInternalAdmissionTransport (t : InternalAdmissionTransport) : CoreM Unit := do
  modifyEnv fun env => internalAdmissionTransportExt.addEntry env (.transport t)

/-- Return all captured source docstrings. -/
def getSourceDocs : CoreM SourceDocState := do
  return sourceDocExt.getState (← getEnv)

/-- Return captured source docstrings for one theory. -/
def getSourceDocsFor (theoryName : Name) : CoreM (Array SourceDoc) := do
  return ((← getSourceDocs).find? theoryName).getD #[]

/-- Trim ASCII whitespace from a captured documentation string. -/
def trimCapturedDoc (doc : String) : String :=
  doc.trimAscii.toString

/-- Register a captured source docstring, ignoring empty/whitespace-only comments. -/
def registerSourceDoc (theoryName : Name) (role : SourceDocRole) (sourceName : Name) (doc :
  String) : CoreM Unit := do
  let doc := trimCapturedDoc doc
  unless doc.isEmpty do
    modifyEnv fun env => sourceDocExt.addEntry env (.doc { theoryName, role, sourceName, doc })

/-- Find a captured source docstring in a theory. Later entries win. -/
def findSourceDoc? (theoryName : Name) (role : SourceDocRole) (sourceName : Name) :
  CoreM (Option String) := do
  let docs ← getSourceDocsFor theoryName
  let docs := docs.reverse
  pure <| (docs.find? fun d => d.role == role
    && d.sourceName.eraseMacroScopes == sourceName.eraseMacroScopes).map (·.doc)

/-- Find any captured source docstring for a local source name in a theory. Later entries win. -/
def findAnySourceDocForName? (theoryName sourceName : Name) : CoreM (Option String) := do
  let docs ← getSourceDocsFor theoryName
  let docs := docs.reverse
  pure <| (docs.find? fun d =>
    d.sourceName.eraseMacroScopes == sourceName.eraseMacroScopes).map (·.doc)

/-- Return true when the canonical Lean anchor declaration for a theory is present. -/
def hasTheoryAnchor (theoryName : Name) : CoreM Bool := do
  return (← getEnv).contains (theoryAnchorName theoryName)

/-- Ensure the canonical Lean anchor declaration for a theory is present. -/
def requireTheoryAnchor (theoryName : Name) : CoreM Unit := do
  unless ← hasTheoryAnchor theoryName do
    throwError "type theory '{theoryName}' has no Lean-visible anchor \
      '{theoryAnchorName theoryName}'"

/-- Return registered semantic transport mappings. -/
def getSemanticTransportMappings : CoreM SemanticTransportState := do
  return semanticTransportExt.getState (← getEnv)

/-- Return registered semantic transport mappings for one theory. -/
def getSemanticTransportMap (theoryName : Name) : CoreM (NameMap Name) := do
  return ((← getSemanticTransportMappings).find? theoryName).getD {}

/-- Register a semantic transport mapping. -/
def registerSemanticTransport (theoryName rewriteName lemmaName : Name) : CoreM Unit := do
  modifyEnv fun env => semanticTransportExt.addEntry env (.map theoryName rewriteName lemmaName)

/-- Compare user-facing object names modulo macro scopes. -/
def sameObjectName (a b : Name) : Bool :=
  a.eraseMacroScopes == b.eraseMacroScopes
