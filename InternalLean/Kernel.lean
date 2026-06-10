/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.DSL

/-!
# Parallel structural LF kernel prototype

This module contains the Phase-5b structural kernel that runs beside the existing raw kernel.
It uses first-class constructors for binders, applications, structural products/functions,
universes, and judgmental equality.  The old raw kernel remains authoritative during Phase 5b;
this module is used for opt-in dual replay comparison.
-/

@[expose] public section

open Lean

namespace InternalLean

register_option internalLean.kernel.dualReplay : Bool := {
  defValue := false
  descr := "also replay checked LF kernel certificates through the Phase-5b structural kernel"
}

namespace Kernel

/-- Erased global kernel name. -/
structure KName where
  /-- Underlying Lean name, with macro scopes erased at construction boundaries. -/
  raw : Name
  deriving Inhabited, Repr, BEq, Hashable

namespace KName

/-- Construct an erased kernel name. -/
def ofName (n : Name) : KName := { raw := n.eraseMacroScopes }

instance : ToString KName where
  toString n := toString n.raw

end KName

/-- Erased free local name used by replay contexts. -/
structure KLocalName where
  /-- Underlying Lean name, with macro scopes erased at construction boundaries. -/
  raw : Name
  deriving Inhabited, Repr, BEq, Hashable

namespace KLocalName

/-- Construct an erased free local name. -/
def ofName (n : Name) : KLocalName := { raw := n.eraseMacroScopes }

instance : ToString KLocalName where
  toString n := toString n.raw

end KLocalName

/-- Resolved class of a kernel LF head. -/
inductive KHeadKind where
  | syntaxSort
  | syntaxDef
  | lfDefinition
  | lfTheorem
  | lfRule
  | judgment
  | primitive
  | definition
  | theorem
  | opaque
  deriving Inhabited, Repr, BEq

/-- Resolved global LF head. -/
structure KHead where
  /-- Erased global head name. -/
  name : KName
  /-- Head class. -/
  kind : KHeadKind := .primitive
  /-- Optional declared arity. -/
  arity? : Option Nat := none
  deriving Inhabited, Repr, BEq

/-- First-class structural kernel term.

Bound variables are de Bruijn indices.  Binder names and printer hints are kept out of the
semantic term, so structural equality is alpha-equivalence for locally closed terms. -/
inductive KTerm where
  | ident (head : KHead)
  | fvar (name : KLocalName)
  | bvar (index : Nat)
  | mvar (name : KName) (sort : RawMetaSort)
  | app (fn arg : KTerm)
  | lam (body : KTerm)
  | arrow (domain codomain : KTerm)
  | sigma (domain codomain : KTerm)
  | pair (left right : KTerm)
  | fst (value : KTerm)
  | snd (value : KTerm)
  | univ (level : LevelExpr)
  | jeq (lhs rhs : KTerm)
  deriving Inhabited, Repr, BEq

namespace KTerm

/-- Apply a function term to a list of arguments. -/
def mkApps (fn : KTerm) (args : List KTerm) : KTerm :=
  args.foldl (fun f a => .app f a) fn

/-- Whether all de Bruijn indices are bound by at least `depth` surrounding binders. -/
partial def isLocallyClosedAt (depth : Nat) : KTerm → Bool
  | .ident _ | .fvar _ | .mvar .. | .univ _ => true
  | .bvar i => i < depth
  | .app f a => isLocallyClosedAt depth f && isLocallyClosedAt depth a
  | .lam body => isLocallyClosedAt (depth + 1) body
  | .arrow A B | .sigma A B =>
      isLocallyClosedAt depth A && isLocallyClosedAt (depth + 1) B
  | .pair a b | .jeq a b => isLocallyClosedAt depth a && isLocallyClosedAt depth b
  | .fst e | .snd e => isLocallyClosedAt depth e

/-- Whether a kernel term has no loose de Bruijn indices. -/
def isLocallyClosed (e : KTerm) : Bool :=
  isLocallyClosedAt 0 e

/-- Structural equality, valid as alpha-equivalence for locally closed `KTerm`s. -/
def alphaEq (a b : KTerm) : Bool :=
  a == b

/-- Whether a term mentions the de Bruijn index `target` under `depth` binders. -/
partial def hasBVarAt (target depth : Nat) : KTerm → Bool
  | .ident _ | .fvar _ | .mvar .. | .univ _ => false
  | .bvar i => i == target + depth
  | .app f a => hasBVarAt target depth f || hasBVarAt target depth a
  | .lam body => hasBVarAt target (depth + 1) body
  | .arrow A B | .sigma A B => hasBVarAt target depth A || hasBVarAt target (depth + 1) B
  | .pair a b | .jeq a b => hasBVarAt target depth a || hasBVarAt target depth b
  | .fst e | .snd e => hasBVarAt target depth e

/-- Shift loose de Bruijn indices at or above `cutoff` by `amount`. -/
partial def shiftAbove (cutoff amount : Nat) : KTerm → KTerm
  | .ident h => .ident h
  | .fvar n => .fvar n
  | .bvar i => if i >= cutoff then .bvar (i + amount) else .bvar i
  | .mvar n s => .mvar n s
  | .app f a => .app (shiftAbove cutoff amount f) (shiftAbove cutoff amount a)
  | .lam body => .lam (shiftAbove (cutoff + 1) amount body)
  | .arrow A B => .arrow (shiftAbove cutoff amount A) (shiftAbove (cutoff + 1) amount B)
  | .sigma A B => .sigma (shiftAbove cutoff amount A) (shiftAbove (cutoff + 1) amount B)
  | .pair a b => .pair (shiftAbove cutoff amount a) (shiftAbove cutoff amount b)
  | .fst e => .fst (shiftAbove cutoff amount e)
  | .snd e => .snd (shiftAbove cutoff amount e)
  | .univ u => .univ u
  | .jeq lhs rhs => .jeq (shiftAbove cutoff amount lhs) (shiftAbove cutoff amount rhs)

/-- Remove the top binder while substituting `arg` for de Bruijn index `0`. -/
partial def substTop (arg : KTerm) : KTerm → KTerm :=
  let rec go (depth : Nat) : KTerm → KTerm
    | .ident h => .ident h
    | .fvar n => .fvar n
    | .bvar i =>
        if i == depth then
          shiftAbove 0 depth arg
        else if i > depth then
          .bvar (i - 1)
        else
          .bvar i
    | .mvar n s => .mvar n s
    | .app f a => .app (go depth f) (go depth a)
    | .lam body => .lam (go (depth + 1) body)
    | .arrow A B => .arrow (go depth A) (go (depth + 1) B)
    | .sigma A B => .sigma (go depth A) (go (depth + 1) B)
    | .pair a b => .pair (go depth a) (go depth b)
    | .fst e => .fst (go depth e)
    | .snd e => .snd (go depth e)
    | .univ u => .univ u
    | .jeq lhs rhs => .jeq (go depth lhs) (go depth rhs)
  go 0

/-- Remove the top binder from a term that does not mention index `0`. -/
partial def lowerTop : KTerm → KTerm :=
  let rec go (depth : Nat) : KTerm → KTerm
    | .ident h => .ident h
    | .fvar n => .fvar n
    | .bvar i => if i > depth then .bvar (i - 1) else .bvar i
    | .mvar n s => .mvar n s
    | .app f a => .app (go depth f) (go depth a)
    | .lam body => .lam (go (depth + 1) body)
    | .arrow A B => .arrow (go depth A) (go (depth + 1) B)
    | .sigma A B => .sigma (go depth A) (go (depth + 1) B)
    | .pair a b => .pair (go depth a) (go depth b)
    | .fst e => .fst (go depth e)
    | .snd e => .snd (go depth e)
    | .univ u => .univ u
    | .jeq lhs rhs => .jeq (go depth lhs) (go depth rhs)
  go 0

/-- One structural β step, when the outer term is a lambda application. -/
def betaReduce? : KTerm → Option KTerm
  | .app (.lam body) arg => some (substTop arg body)
  | _ => none

/-- One structural η step for functions and dependent pairs. -/
def etaReduce? : KTerm → Option KTerm
  | .lam (.app f (.bvar 0)) =>
      if hasBVarAt 0 0 f then none else some (lowerTop f)
  | .pair (.fst p) (.snd q) =>
      if p.alphaEq q then some p else none
  | _ => none

/-- Finite metavariable instantiation. -/
abbrev KInstantiation := Std.HashMap KName KTerm

/-- Instantiate schema metavariables in a term. Values are expected to be locally closed. -/
partial def instantiateMetas (σ : KInstantiation) : KTerm → Except String KTerm
  | .ident h => pure (.ident h)
  | .fvar n => pure (.fvar n)
  | .bvar i => pure (.bvar i)
  | .mvar n _ =>
      match σ[n]? with
      | some v =>
          if v.isLocallyClosed then pure v else
            throw s!"kernel metavariable '{n}' instantiates to a term with loose binders"
      | none => throw s!"missing kernel metavariable instantiation for '{n}'"
  | .app f a => return .app (← instantiateMetas σ f) (← instantiateMetas σ a)
  | .lam body => return .lam (← instantiateMetas σ body)
  | .arrow A B => return .arrow (← instantiateMetas σ A) (← instantiateMetas σ B)
  | .sigma A B => return .sigma (← instantiateMetas σ A) (← instantiateMetas σ B)
  | .pair a b => return .pair (← instantiateMetas σ a) (← instantiateMetas σ b)
  | .fst e => return .fst (← instantiateMetas σ e)
  | .snd e => return .snd (← instantiateMetas σ e)
  | .univ u => pure (.univ u)
  | .jeq lhs rhs => return .jeq (← instantiateMetas σ lhs) (← instantiateMetas σ rhs)

end KTerm

abbrev KInstantiation := KTerm.KInstantiation

/-- KTerm judgment: an LF judgment head applied to KTerm arguments. -/
structure Judgment where
  /-- Judgment head. -/
  head : KName
  /-- Judgment arguments. -/
  args : List KTerm := []
  deriving Inhabited, Repr, BEq

namespace Judgment

/-- Instantiate schema metavariables in a judgment. -/
def instantiateMetas (σ : KInstantiation) (j : Judgment) : Except String Judgment := do
  return { j with args := (← j.args.mapM (KTerm.instantiateMetas σ)) }

/-- Structural equality, valid as alpha-equivalence for locally closed KTerm arguments. -/
def alphaEq (a b : Judgment) : Bool :=
  a == b

end Judgment

/-- Context-zone schema for the structural kernel. -/
structure ContextZoneSchema where
  name : KName
  sort : RawMetaSort
  dependsOn : List KName := []
  deriving Inhabited, Repr, BEq

/-- Binder-class schema for the structural kernel. -/
structure BinderClassSchema where
  name : KName
  zone : KName
  boundSort : RawMetaSort
  dependsOn : List KName := []
  deriving Inhabited, Repr, BEq

/-- Rule metavariable schema for structural replay. -/
structure RuleMetaVar where
  name : KName
  sort : RawMetaSort := .arg
  zone? : Option KName := none
  type? : Option KTerm := none
  evidence? : Option Judgment := none
  deriving Inhabited, Repr, BEq

/-- Side-condition payload for structural replay. -/
structure SideCondition where
  name : KName
  args : List KTerm := []
  deriving Inhabited, Repr, BEq

/-- Side-condition certificate slot for structural replay. -/
structure SideConditionCertificateSlot where
  name : KName
  condition : SideCondition
  deriving Inhabited, Repr, BEq

/-- Checked side-condition certificate for structural replay. -/
structure SideConditionCertificate where
  name : KName
  condition : SideCondition
  kind : SideConditionCertificateKind := .builtinTrivial
  payload : String := ""
  deriving Inhabited, Repr, BEq

/-- Conversion-plugin schema for structural conversion checking. -/
structure ConversionPluginSchema where
  name : KName
  trust : ConversionPluginTrustKind := .opaqueAssumption
  supportedSteps : List ConversionStepKind := []
  deriving Inhabited, Repr, BEq

/-- Conversion statement over structural KTerms. -/
structure ConversionStatement where
  plugin : KName
  context? : Option KTerm := none
  lhs : KTerm
  rhs : KTerm
  deriving Inhabited, Repr, BEq

namespace ConversionStatement

/-- Reverse a conversion statement. -/
def symm (stmt : ConversionStatement) : ConversionStatement :=
  { stmt with lhs := stmt.rhs, rhs := stmt.lhs }

/-- Replace the target endpoint. -/
def withRhs (stmt : ConversionStatement) (rhs : KTerm) : ConversionStatement :=
  { stmt with rhs := rhs }

/-- Replace the source endpoint. -/
def withLhs (stmt : ConversionStatement) (lhs : KTerm) : ConversionStatement :=
  { stmt with lhs := lhs }

end ConversionStatement

/-- External conversion certificate entry for structural replay. -/
structure KernelLFConversionCertificateEntry where
  certificateName : KName
  statement : ConversionStatement
  stepKind : ConversionStepKind
  deriving Inhabited, Repr, BEq

/-- Structural conversion certificate tree. -/
inductive KernelLFConversionCertificate where
  | refl (statement : ConversionStatement) : KernelLFConversionCertificate
  | symm (statement : ConversionStatement) (child : KernelLFConversionCertificate) :
      KernelLFConversionCertificate
  | trans (statement : ConversionStatement) (middle : KTerm)
      (left right : KernelLFConversionCertificate) : KernelLFConversionCertificate
  | pluginStep (statement : ConversionStatement) (stepKind : ConversionStepKind)
      (externalCertificateName? : Option KName) (sideConditionCertificateNames : List KName)
      (payload : String) : KernelLFConversionCertificate
  deriving Inhabited, Repr, BEq

/-- Scoped instantiation entry for structural replay. -/
structure ScopedInstantiationEntry where
  name : KName
  sort : RawMetaSort := .arg
  zone? : Option KName := none
  type? : Option KTerm := none
  evidence? : Option Judgment := none
  value : KTerm
  deriving Inhabited, Repr, BEq

/-- Finite scoped instantiation for structural replay. -/
structure ScopedInstantiation where
  entries : List ScopedInstantiationEntry := []
  deriving Inhabited, Repr, BEq

namespace ScopedInstantiation

/-- Convert a scoped instantiation to a finite metavariable map. -/
def asInstantiation (σ : ScopedInstantiation) : KInstantiation := Id.run do
  let mut out : KInstantiation := {}
  for e in σ.entries do
    out := out.insert e.name e.value
  return out

/-- Validate a scoped instantiation against a rule metavariable telescope. -/
def validateAgainst (σ : ScopedInstantiation) (metavariables : List RuleMetaVar) :
    Except String Unit := do
  if σ.entries.length != metavariables.length then
    throw s!"scoped instantiation has {σ.entries.length} entrie(s), expected \
      {metavariables.length}"
  for e in σ.entries, v in metavariables do
    if e.name != v.name then
      throw s!"scoped instantiation entry for '{e.name}' appears where metavariable \
        '{v.name}' was expected"
    if e.sort != v.sort then
      throw s!"scoped instantiation entry '{e.name}' has sort '{reprStr e.sort}', expected \
        '{reprStr v.sort}'"
    if e.zone? != v.zone? then
      throw s!"scoped instantiation entry '{e.name}' has zone '{reprStr e.zone?}', expected \
        '{reprStr v.zone?}'"
    if e.type? != v.type? then
      throw s!"scoped instantiation entry '{e.name}' has a type annotation that differs from \
        the rule telescope"
    if e.evidence? != v.evidence? then
      throw s!"scoped instantiation entry '{e.name}' has evidence that differs from the rule \
        telescope"
    unless e.value.isLocallyClosed do
      throw s!"scoped instantiation entry '{e.name}' has a value with loose binders"

end ScopedInstantiation

/-- Typed LF constant schema for structural replay. -/
structure LFConstantSchema where
  name : KName
  params : List RuleMetaVar := []
  resultType : KTerm
  deriving Inhabited, Repr, BEq

/-- Rule schema for structural replay. -/
structure RuleSchema where
  name : KName
  metavariables : List RuleMetaVar := []
  premises : List Judgment := []
  sideConditions : List SideCondition := []
  sideConditionCertificates : List SideConditionCertificateSlot := []
  checkedSideConditionCertificates : List SideConditionCertificate := []
  conclusionStmt : Judgment
  deriving Inhabited, Repr, BEq

namespace RuleSchema

/-- Instantiate a rule premise with a finite metavariable map. -/
def instantiatePremise (_r : RuleSchema) (σ : KInstantiation) (premiseStmt : Judgment) :
    Except String Judgment :=
  premiseStmt.instantiateMetas σ

/-- Instantiate a rule concl with a finite metavariable map. -/
def instantiateConclusion (r : RuleSchema) (σ : KInstantiation) : Except String Judgment :=
  r.conclusionStmt.instantiateMetas σ

end RuleSchema

/-- Source-order structural kernel signature. -/
structure Signature where
  name : KName
  constants : List LFConstantSchema := []
  contextZones : List ContextZoneSchema := []
  binderClasses : List BinderClassSchema := []
  conversionPlugins : List ConversionPluginSchema := []
  rules : List RuleSchema := []
  deriving Inhabited, Repr, BEq

/-- Validated, indexed structural kernel signature. -/
structure ValidatedSignature where
  name : KName
  source : Signature
  constantsByKey : Std.HashMap (KName × Nat) LFConstantSchema := {}
  constantsByName : Std.HashMap KName (Array LFConstantSchema) := {}
  rulesByName : Std.HashMap KName RuleSchema := {}
  contextZonesByName : Std.HashMap KName ContextZoneSchema := {}
  binderClassesByName : Std.HashMap KName BinderClassSchema := {}
  conversionPluginsByName : Std.HashMap KName ConversionPluginSchema := {}

/-- Previously checked theorem entry for structural replay. -/
structure KernelLFTheoremEntry where
  name : KName
  statement : Judgment
  deriving Inhabited, Repr, BEq

/-- Checked external certificate entry for structural replay. -/
structure KernelLFCertificateEntry where
  name : KName
  statement : Judgment
  certificateName : KName
  deriving Inhabited, Repr, BEq

/-- Source-order structural replay context. -/
structure KernelLFCheckContext where
  localParameters : List KLocalName := []
  assumptions : List KernelLFTheoremEntry := []
  theorems : List KernelLFTheoremEntry := []
  certificates : List KernelLFCertificateEntry := []
  conversionCertificates : List KernelLFConversionCertificateEntry := []
  deriving Inhabited, Repr, BEq

/-- Validated, indexed structural replay context. -/
structure ValidatedReplayContext where
  source : KernelLFCheckContext
  localParameters : Array KLocalName := #[]
  localParameterSet : Std.HashSet KLocalName := {}
  assumptionsByName : Std.HashMap KName KernelLFTheoremEntry := {}
  theoremsByName : Std.HashMap KName KernelLFTheoremEntry := {}
  certificatesByName : Std.HashMap KName KernelLFCertificateEntry := {}
  certificatesByCertificateName : Std.HashMap KName KernelLFCertificateEntry := {}
  conversionCertificatesByCertificateName :
    Std.HashMap KName KernelLFConversionCertificateEntry := {}

/-- First duplicate value in a list. -/
def firstDuplicate? [BEq α] (xs : List α) : Option α :=
  let rec go (seen : List α) : List α → Option α
    | [] => none
    | x :: xs => if seen.contains x then some x else go (x :: seen) xs
  go [] xs

namespace ValidatedSignature

/-- Validate and index a source-order structural signature. -/
def ofSignature (sig : Signature) : Except String ValidatedSignature := do
  let mut constantsByKey : Std.HashMap (KName × Nat) LFConstantSchema := {}
  let mut constantsByName : Std.HashMap KName (Array LFConstantSchema) := {}
  for c in sig.constants do
    let key := (c.name, c.params.length)
    if constantsByKey.contains key then
      throw s!"signature '{sig.name}' has duplicate typed LF constant '{c.name}' with \
        arity {c.params.length}"
    constantsByKey := constantsByKey.insert key c
    let prior := (constantsByName[c.name]?).getD #[]
    constantsByName := constantsByName.insert c.name (prior.push c)
  let mut contextZonesByName : Std.HashMap KName ContextZoneSchema := {}
  let mut seenZones : Std.HashSet KName := {}
  for z in sig.contextZones do
    if seenZones.contains z.name then
      throw s!"signature '{sig.name}' has duplicate context-zone schema '{z.name}'"
    for dep in z.dependsOn do
      unless seenZones.contains dep do
        throw s!"context-zone schema '{z.name}' in signature '{sig.name}' depends on unknown \
          or later zone '{dep}'"
    seenZones := seenZones.insert z.name
    contextZonesByName := contextZonesByName.insert z.name z
  let mut binderClassesByName : Std.HashMap KName BinderClassSchema := {}
  let mut seenClasses : Std.HashSet KName := {}
  for c in sig.binderClasses do
    if seenClasses.contains c.name then
      throw s!"signature '{sig.name}' has duplicate binder-class schema '{c.name}'"
    unless contextZonesByName.contains c.zone do
      throw s!"binder-class schema '{c.name}' in signature '{sig.name}' uses unknown context \
        zone '{c.zone}'"
    for dep in c.dependsOn do
      unless contextZonesByName.contains dep do
        throw s!"binder-class schema '{c.name}' in signature '{sig.name}' depends on unknown \
          context zone '{dep}'"
    seenClasses := seenClasses.insert c.name
    binderClassesByName := binderClassesByName.insert c.name c
  let mut conversionPluginsByName : Std.HashMap KName ConversionPluginSchema := {}
  let mut seenPlugins : Std.HashSet KName := {}
  for p in sig.conversionPlugins do
    if seenPlugins.contains p.name then
      throw s!"signature '{sig.name}' has duplicate conversion-plugin schema '{p.name}'"
    if let some dup := firstDuplicate? p.supportedSteps then
      throw s!"conversion-plugin schema '{p.name}' in signature '{sig.name}' lists duplicate \
        supported step '{dup.label}'"
    seenPlugins := seenPlugins.insert p.name
    conversionPluginsByName := conversionPluginsByName.insert p.name p
  let mut rulesByName : Std.HashMap KName RuleSchema := {}
  let mut seenRules : Std.HashSet KName := {}
  for r in sig.rules do
    if seenRules.contains r.name then
      throw s!"signature '{sig.name}' has duplicate rule schema '{r.name}'"
    let mut seenMetas : Std.HashSet KName := {}
    for v in r.metavariables do
      if seenMetas.contains v.name then
        throw s!"rule '{r.name}' in signature '{sig.name}' has duplicate metavariable \
          '{v.name}'"
      seenMetas := seenMetas.insert v.name
      if let some zoneName := v.zone? then
        let zone ←
          match contextZonesByName[zoneName]? with
          | some zone => pure zone
          | none => throw s!"rule '{r.name}' metavariable '{v.name}' uses unknown context \
              zone '{zoneName}'"
        if v.sort != zone.sort then
          throw s!"rule '{r.name}' metavariable '{v.name}' has sort '{reprStr v.sort}' in \
            context zone '{zoneName}', expected zone sort '{reprStr zone.sort}'"
    seenRules := seenRules.insert r.name
    rulesByName := rulesByName.insert r.name r
  pure {
    name := sig.name
    source := sig
    constantsByKey
    constantsByName
    rulesByName
    contextZonesByName
    binderClassesByName
    conversionPluginsByName }

end ValidatedSignature

namespace ValidatedReplayContext

/-- Validate and index a source-order structural replay context. -/
def ofContext (ctx : KernelLFCheckContext) : Except String ValidatedReplayContext := do
  let mut localParameterSet : Std.HashSet KLocalName := {}
  let mut localParameters := #[]
  for p in ctx.localParameters do
    if localParameterSet.contains p then
      throw s!"checked replay context has duplicate local parameter '{p}'"
    localParameterSet := localParameterSet.insert p
    localParameters := localParameters.push p
  let mut assumptionsByName : Std.HashMap KName KernelLFTheoremEntry := {}
  for e in ctx.assumptions do
    if assumptionsByName.contains e.name then
      throw s!"checked replay context has duplicate assumption entry '{e.name}'"
    assumptionsByName := assumptionsByName.insert e.name e
  let mut theoremsByName : Std.HashMap KName KernelLFTheoremEntry := {}
  for e in ctx.theorems do
    if theoremsByName.contains e.name then
      throw s!"checked replay context has duplicate theorem entry '{e.name}'"
    theoremsByName := theoremsByName.insert e.name e
  let mut certificatesByName : Std.HashMap KName KernelLFCertificateEntry := {}
  let mut certificatesByCertificateName : Std.HashMap KName KernelLFCertificateEntry := {}
  for e in ctx.certificates do
    if certificatesByName.contains e.name then
      throw s!"checked replay context has duplicate certificate entry '{e.name}'"
    if certificatesByCertificateName.contains e.certificateName then
      throw s!"checked replay context has duplicate certificate token '{e.certificateName}'"
    certificatesByName := certificatesByName.insert e.name e
    certificatesByCertificateName := certificatesByCertificateName.insert e.certificateName e
  let mut conversionCertificatesByCertificateName :
      Std.HashMap KName KernelLFConversionCertificateEntry := {}
  for e in ctx.conversionCertificates do
    if conversionCertificatesByCertificateName.contains e.certificateName then
      throw s!"checked replay context has duplicate conversion certificate token \
        '{e.certificateName}'"
    conversionCertificatesByCertificateName :=
      conversionCertificatesByCertificateName.insert e.certificateName e
  pure {
    source := ctx
    localParameters
    localParameterSet
    assumptionsByName
    theoremsByName
    certificatesByName
    certificatesByCertificateName
    conversionCertificatesByCertificateName }

end ValidatedReplayContext

namespace KernelLFConversionCertificate

/-- Statement carried by a structural conversion certificate. -/
def statement : KernelLFConversionCertificate → ConversionStatement
  | .refl stmt => stmt
  | .symm stmt _ => stmt
  | .trans stmt _ _ _ => stmt
  | .pluginStep stmt _ _ _ _ => stmt

/-- Raise a structured conversion failure. -/
def throwFailure (kind : ConversionCheckFailureKind) (message : String) :
    Except ConversionCheckFailure α :=
  throw { kind, message }

/-- Validate the currently implemented structural executable conversion steps. -/
def validateExecutableStep (pluginName : KName) (stmt : ConversionStatement)
    (kind : ConversionStepKind) : Except ConversionCheckFailure Unit := do
  match kind with
  | .beta =>
      match stmt.lhs.betaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{pluginName}' beta step reduces lhs to a \
                different rhs"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{pluginName}' beta step expected a structural redex"
  | .eta =>
      match stmt.lhs.etaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{pluginName}' eta step contracts lhs to a \
                different rhs"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{pluginName}' eta step expected a structural eta-redex"
  | _ =>
      throwFailure .unsupportedConversion <|
        s!"checked conversion plugin '{pluginName}' has no structural executable engine for \
          step '{kind.label}'"

/-- Validate one structural conversion plugin step. -/
def validatePluginStepWithContextDetailed (ctx : ValidatedReplayContext)
    (sig : ValidatedSignature) (stmt : ConversionStatement) (kind : ConversionStepKind)
    (externalCertificateName? : Option KName) (sideConditionCertificateNames : List KName)
    (payload : String) : Except ConversionCheckFailure Unit := do
  let plugin ←
    match sig.conversionPluginsByName[stmt.plugin]? with
    | some plugin => pure plugin
    | none => throwFailure .unsupportedConversion <|
        s!"conversion certificate plugin step uses unknown conversion plugin '{stmt.plugin}'"
  unless plugin.supportedSteps.contains kind do
    throwFailure .unsupportedConversion <|
      s!"conversion plugin '{plugin.name}' does not support step '{kind.label}'"
  if let some dup := firstDuplicate? sideConditionCertificateNames then
    throwFailure .malformedCertificate <|
      s!"conversion plugin step for '{plugin.name}' has duplicate side-condition certificate \
        reference '{dup}'"
  for certName in sideConditionCertificateNames do
    unless ctx.certificatesByCertificateName.contains certName do
      throwFailure .malformedCertificate <|
        s!"conversion plugin step for '{plugin.name}' references unavailable side-condition \
          certificate '{certName}'"
  match plugin.trust with
  | .executableChecked =>
      if externalCertificateName?.isSome then
        throwFailure .malformedCertificate <|
          s!"checked conversion plugin '{plugin.name}' must not use an external certificate token"
      validateExecutableStep plugin.name stmt kind
  | .externalCertificate =>
      let certName ←
        match externalCertificateName? with
        | some certName => pure certName
        | none => throwFailure .externalCertificate <|
            s!"external-certificate conversion plugin '{plugin.name}' requires an external \
              conversion certificate token"
      let entry ←
        match ctx.conversionCertificatesByCertificateName[certName]? with
        | some entry => pure entry
        | none => throwFailure .externalCertificate <|
            s!"external conversion certificate '{certName}' is not available in the checked \
              replay context"
      if entry.statement != stmt then
        throwFailure .externalCertificate <|
          s!"external conversion certificate '{certName}' certifies a different statement"
      if entry.stepKind != kind then
        throwFailure .externalCertificate <|
          s!"external conversion certificate '{certName}' certifies step \
            '{entry.stepKind.label}', expected '{kind.label}'"
  | .opaqueAssumption =>
      if externalCertificateName?.isSome then
        throwFailure .opaquePlugin <|
          s!"opaque conversion plugin '{plugin.name}' must not use an external certificate token"
      if payload == "" then
        throwFailure .opaquePlugin <|
          s!"opaque conversion plugin '{plugin.name}' requires a visible nonempty payload"

/-- Recursive structural conversion certificate checker. -/
partial def checkWithContextDetailedCore (ctx : ValidatedReplayContext)
    (sig : ValidatedSignature) : KernelLFConversionCertificate → ConversionStatement →
    Except ConversionCheckFailure Unit
  | .refl stmt, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate "conversion refl has an unexpected statement"
      unless stmt.lhs == stmt.rhs do
        throwFailure .malformedCertificate s!"conversion refl for plugin '{stmt.plugin}' has \
          non-identical endpoints"
  | .symm stmt child, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate "conversion symm has an unexpected statement"
      checkWithContextDetailedCore ctx sig child stmt.symm
  | .trans stmt middle left right, expected => do
      if stmt != expected then
        throwFailure .malformedCertificate "conversion trans has an unexpected statement"
      checkWithContextDetailedCore ctx sig left (stmt.withRhs middle)
      checkWithContextDetailedCore ctx sig right (stmt.withLhs middle)
  | .pluginStep stmt kind externalCertificateName? sideConditionCertificateNames payload,
      expected => do
      if stmt != expected then
        throwFailure .malformedCertificate "conversion plugin step has an unexpected statement"
      validatePluginStepWithContextDetailed ctx sig stmt kind externalCertificateName?
        sideConditionCertificateNames payload

/-- Validate a structural conversion certificate with validated signature/context. -/
def checkWithValidatedContextDetailed (ctx : ValidatedReplayContext) (sig : ValidatedSignature)
    (cert : KernelLFConversionCertificate) (expected : ConversionStatement) :
    Except ConversionCheckFailure Unit :=
  checkWithContextDetailedCore ctx sig cert expected

end KernelLFConversionCertificate

/-- Checked structural conversion certificate wrapper. -/
structure CheckedKernelLFConversionCertificate where
  signature : Signature
  context : KernelLFCheckContext := {}
  statement : ConversionStatement
  certificate : KernelLFConversionCertificate
  deriving Inhabited, Repr, BEq

namespace CheckedKernelLFConversionCertificate

/-- Check and wrap a structural conversion certificate, preserving structured failures. -/
def checkDetailed (signature : Signature) (context : KernelLFCheckContext)
    (statement : ConversionStatement) (certificate : KernelLFConversionCertificate) :
    Except ConversionCheckFailure CheckedKernelLFConversionCertificate := do
  let sig ←
    match ValidatedSignature.ofSignature signature with
    | .ok sig => pure sig
    | .error err => KernelLFConversionCertificate.throwFailure .malformedCertificate err
  let ctx ←
    match ValidatedReplayContext.ofContext context with
    | .ok ctx => pure ctx
    | .error err => KernelLFConversionCertificate.throwFailure .malformedCertificate err
  KernelLFConversionCertificate.checkWithValidatedContextDetailed ctx sig certificate statement
  pure { signature, context, statement, certificate }

/-- Check and wrap a structural conversion certificate. -/
def check (signature : Signature) (context : KernelLFCheckContext)
    (statement : ConversionStatement) (certificate : KernelLFConversionCertificate) :
    Except String CheckedKernelLFConversionCertificate :=
  match checkDetailed signature context statement certificate with
  | .ok checked => .ok checked
  | .error err => .error err.message

end CheckedKernelLFConversionCertificate

/-- Structural LF derivation tree. -/
inductive KernelLFDerivation where
  | assumption (name : KName) (statement : Judgment) : KernelLFDerivation
  | theoremRef (name : KName) (statement : Judgment) : KernelLFDerivation
  | certificate (name : KName) (statement : Judgment) (certificateName : KName) :
      KernelLFDerivation
  | ruleApp (ruleName : KName) (concl : Judgment) (instantiation : ScopedInstantiation)
      (premises : List KernelLFDerivation) (sideConditionCertificateNames : List KName) :
      KernelLFDerivation
  deriving Inhabited, Repr, BEq

namespace KernelLFDerivation

/-- Statement carried by a structural LF derivation. -/
def statement : KernelLFDerivation → Judgment
  | .assumption _ stmt => stmt
  | .theoremRef _ stmt => stmt
  | .certificate _ stmt _ => stmt
  | .ruleApp _ concl _ _ _ => concl

/-- Expected checked side-condition certificate names for a rule schema. -/
def expectedCertificateNames (r : RuleSchema) : List KName :=
  r.checkedSideConditionCertificates.map (fun c => c.name)

/-- Validate a rule application against a resolved structural rule schema. -/
def validateRuleApplicationAgainstRule (sig : ValidatedSignature) (ruleName : KName)
    (r : RuleSchema) (concl : Judgment) (inst : ScopedInstantiation) (premiseCount : Nat)
    (certificateNames : List KName) : Except String Unit := do
  unless sig.rulesByName.contains ruleName do
    throw s!"rule application uses unknown rule '{ruleName}'"
  inst.validateAgainst r.metavariables
  let expectedConclusion ← r.instantiateConclusion inst.asInstantiation
  if !concl.alphaEq expectedConclusion then
    throw s!"rule application '{ruleName}' has a concl different from the instantiated \
      rule conclusion"
  if premiseCount != r.premises.length then
    throw s!"rule application '{ruleName}' has {premiseCount} premise(s), expected \
      {r.premises.length}"
  let expectedCerts := expectedCertificateNames r
  if certificateNames != expectedCerts then
    throw s!"rule application '{ruleName}' has certificate names '{reprStr certificateNames}', \
      expected '{reprStr expectedCerts}'"

/-- Validate a local assumption leaf. -/
def validateAssumptionWithContext (ctx : ValidatedReplayContext) (name : KName)
    (stmt : Judgment) : Except String Unit := do
  let entry ←
    match ctx.assumptionsByName[name]? with
    | some entry => pure entry
    | none => throw s!"local theorem assumption '{name}' is not available in the checked replay \
        context"
  if !entry.statement.alphaEq stmt then
    throw s!"local theorem assumption '{name}' has a statement different from the replay context"

/-- Validate a theorem-reference leaf. -/
def validateTheoremReferenceWithContext (ctx : ValidatedReplayContext) (name : KName)
    (stmt : Judgment) : Except String Unit := do
  let entry ←
    match ctx.theoremsByName[name]? with
    | some entry => pure entry
    | none => throw s!"theorem reference '{name}' is not available in the checked replay context"
  if !entry.statement.alphaEq stmt then
    throw s!"theorem reference '{name}' has a statement different from the replay context"

/-- Validate a certificate-backed leaf. -/
def validateCertificateWithContext (ctx : ValidatedReplayContext) (name : KName)
    (stmt : Judgment) (certificateName : KName) : Except String Unit := do
  let entry ←
    match ctx.certificatesByName[name]? with
    | some entry => pure entry
    | none => throw s!"certificate-backed derivation '{name}' is not available in the checked \
        certificate context"
  if !entry.statement.alphaEq stmt then
    throw s!"certificate-backed derivation '{name}' has a statement different from the \
      certificate context"
  if entry.certificateName != certificateName then
    throw s!"certificate-backed derivation '{name}' uses certificate '{certificateName}', \
      expected '{entry.certificateName}'"

/-- Recursive structural replay checker over validated signature/context. -/
partial def checkWithValidatedContextCore (ctx : ValidatedReplayContext) (sig :
    ValidatedSignature) : KernelLFDerivation → Judgment → Except String Unit
  | .assumption name stmt, expected => do
      if !stmt.alphaEq expected then
        throw s!"local theorem assumption '{name}' has an unexpected statement"
      validateAssumptionWithContext ctx name stmt
  | .theoremRef name stmt, expected => do
      if !stmt.alphaEq expected then
        throw s!"theorem reference '{name}' has an unexpected statement"
      validateTheoremReferenceWithContext ctx name stmt
  | .certificate name stmt certificateName, expected => do
      if !stmt.alphaEq expected then
        throw s!"certificate-backed derivation '{name}' has an unexpected statement"
      validateCertificateWithContext ctx name stmt certificateName
  | .ruleApp ruleName concl inst premises certificateNames, expected => do
      if !concl.alphaEq expected then
        throw s!"rule application '{ruleName}' has an unexpected conclusion"
      let r ←
        match sig.rulesByName[ruleName]? with
        | some r => pure r
        | none => throw s!"rule application uses unknown rule '{ruleName}'"
      validateRuleApplicationAgainstRule sig ruleName r concl inst premises.length
        certificateNames
      let σ := inst.asInstantiation
      for premiseDeriv in premises, premiseStmt in r.premises do
        let expectedPremise ← r.instantiatePremise σ premiseStmt
        checkWithValidatedContextCore ctx sig premiseDeriv expectedPremise

/-- Validate a structural replay tree with validated signature/context. -/
def checkWithValidatedContext (ctx : ValidatedReplayContext) (sig : ValidatedSignature)
    (d : KernelLFDerivation) (expected : Judgment) : Except String Unit :=
  checkWithValidatedContextCore ctx sig d expected

end KernelLFDerivation

/-- Checked structural LF derivation wrapper. -/
structure CheckedKernelLFDerivation where
  signature : Signature
  context : KernelLFCheckContext := {}
  statement : Judgment
  derivation : KernelLFDerivation
  deriving Inhabited, Repr, BEq

namespace CheckedKernelLFDerivation

/-- Re-run the structural replay check for this checked wrapper. -/
def check (checked : CheckedKernelLFDerivation) : Except String Unit := do
  let sig ← ValidatedSignature.ofSignature checked.signature
  let ctx ← ValidatedReplayContext.ofContext checked.context
  KernelLFDerivation.checkWithValidatedContext ctx sig checked.derivation checked.statement

/-- Build a checked structural replay wrapper from a raw structural payload. -/
def ofReplay (signature : Signature) (context : KernelLFCheckContext) (statement : Judgment)
    (derivation : KernelLFDerivation) : Except String CheckedKernelLFDerivation := do
  let sig ← ValidatedSignature.ofSignature signature
  let ctx ← ValidatedReplayContext.ofContext context
  KernelLFDerivation.checkWithValidatedContext ctx sig derivation statement
  pure { signature, context, statement, derivation }

/-- Build a checked structural replay wrapper using the derivation's carried statement. -/
def ofDerivation (signature : Signature) (context : KernelLFCheckContext)
    (derivation : KernelLFDerivation) : Except String CheckedKernelLFDerivation :=
  ofReplay signature context derivation.statement derivation

end CheckedKernelLFDerivation

/-- Compact structural replay certificate. -/
structure KernelLFReplayCertificate where
  signature : Signature
  context : KernelLFCheckContext := {}
  statement : Judgment
  derivation : KernelLFDerivation
  deriving Inhabited, Repr, BEq

namespace KernelLFReplayCertificate

/-- Validate a compact structural replay certificate. -/
def check (cert : KernelLFReplayCertificate) : Except String Unit := do
  let ctx ← ValidatedReplayContext.ofContext cert.context
  let sig ← ValidatedSignature.ofSignature cert.signature
  KernelLFDerivation.checkWithValidatedContext ctx sig cert.derivation cert.statement

/-- Convert a compact structural certificate to a checked wrapper. -/
def toChecked (cert : KernelLFReplayCertificate) : Except String CheckedKernelLFDerivation :=
  CheckedKernelLFDerivation.ofReplay cert.signature cert.context cert.statement cert.derivation

end KernelLFReplayCertificate

/-- Interpretation data for structural replay premises. -/
def InterpPremises (interpJudgment : Judgment → Type) (σ : KInstantiation) :
    List Judgment → Type
  | [] => PUnit
  | p :: ps =>
      match p.instantiateMetas σ with
      | .ok p' => interpJudgment p' × InterpPremises interpJudgment σ ps
      | .error _ => PUnit

/-- Semantic model interface for a structural kernel signature. -/
structure Model (sig : Signature) where
  interpJudgment : Judgment → Type
  interpRule :
    (r : RuleSchema) →
    (σ : KInstantiation) →
    r ∈ sig.rules →
    InterpPremises interpJudgment σ r.premises →
    interpJudgment
      (match r.instantiateConclusion σ with | .ok j => j | .error _ => r.conclusionStmt)

/-- Semantic model for a structural signature and replay context. -/
structure ContextModel (sig : Signature) (ctx : KernelLFCheckContext) extends Model sig where
  interpAssumption : (e : KernelLFTheoremEntry) → e ∈ ctx.assumptions → interpJudgment e.statement
  interpTheorem : (e : KernelLFTheoremEntry) → e ∈ ctx.theorems → interpJudgment e.statement
  interpCertificate :
    (e : KernelLFCertificateEntry) → e ∈ ctx.certificates → interpJudgment e.statement

namespace RawLowering

/-- Metadata used while decoding old raw terms for Phase-5b dual replay. -/
structure Context where
  binders : List (Option KLocalName) := []
  metas : Std.HashMap KName RawMetaSort := {}

/-- Look up a de Bruijn index in a raw-lowering context. -/
def findBinder? (ctx : Context) (name : KLocalName) : Option Nat :=
  let rec go : Nat → List (Option KLocalName) → Option Nat
    | _, [] => none
    | i, none :: rest => go (i + 1) rest
    | i, some x :: rest => if x == name then some i else go (i + 1) rest
  go 0 ctx.binders

/-- Push a named binder while decoding old raw syntax. -/
def pushBinder (ctx : Context) (name : Name) : Context :=
  { ctx with binders := some (KLocalName.ofName name) :: ctx.binders }

/-- Push an anonymous binder while decoding old raw syntax. -/
def pushAnonymousBinder (ctx : Context) : Context :=
  { ctx with binders := none :: ctx.binders }

/-- Decode a non-structural old raw head kind. -/
def oldHead (name : Name) (kind : KHeadKind := .primitive) : KTerm :=
  .ident { name := KName.ofName name, kind := kind }

/-- Decode an old raw local/metavariable reference. -/
def lowerRef (ctx : Context) (name : Name) (_fallbackSort : RawMetaSort := .arg) : KTerm :=
  let localName := KLocalName.ofName name
  match findBinder? ctx localName with
  | some i => .bvar i
  | none =>
      let k := KName.ofName name
      match ctx.metas[k]? with
      | some sort => .mvar k sort
      | none => .fvar localName

mutual

/-- Decode an old raw LF lambda convention. -/
partial def lowerLam (ctx : Context) (binders : List Raw) (body : Raw) : KTerm :=
  let names? := binders.mapM fun
    | .leanParam x => some x
    | _ => none
  match names? with
  | some names =>
      let ctx' := names.foldl (fun c n => pushBinder c n) ctx
      let body := lowerRaw ctx' body
      names.foldr (fun _ acc => .lam acc) body
  | none => KTerm.mkApps (oldHead `lam) ((binders ++ [body]).map (lowerRaw ctx))

/-- Decode old raw syntax into structural KTerms for dual replay. -/
partial def lowerRaw (ctx : Context) : Raw → KTerm
  | .ctxNil => oldHead `emptyCtx
  | .ctxMeta x => lowerRef { ctx with metas := ctx.metas.insert (KName.ofName x) .ctx } x .ctx
  | .ctxExt Γ A => KTerm.mkApps (oldHead `ctxExt) [lowerRaw ctx Γ, lowerRaw ctx A]
  | .tyMeta x => lowerRef { ctx with metas := ctx.metas.insert (KName.ofName x) .ty } x .ty
  | .tyConst `Type => .univ .zero
  | .tyConst c => oldHead c .syntaxSort
  | .tyApp `Type [.leanParam u] => .univ (.param u.eraseMacroScopes)
  | .tyApp `arrow [A, .tmApp `lam bindersAndBody] =>
      match bindersAndBody.reverse with
      | body :: revBinders =>
          match revBinders.reverse with
          | [.leanParam x] => .arrow (lowerRaw ctx A) (lowerRaw (pushBinder ctx x) body)
          | _ =>
              KTerm.mkApps (oldHead `arrow)
                [lowerRaw ctx A, lowerRaw ctx (.tmApp `lam bindersAndBody)]
      | [] => KTerm.mkApps (oldHead `arrow) [lowerRaw ctx A]
  | .tyApp `arrow [A, B] => .arrow (lowerRaw ctx A) (lowerRaw (pushAnonymousBinder ctx) B)
  | .tyApp `sigma [A, .tmApp `lam bindersAndBody] =>
      match bindersAndBody.reverse with
      | body :: revBinders =>
          match revBinders.reverse with
          | [.leanParam x] => .sigma (lowerRaw ctx A) (lowerRaw (pushBinder ctx x) body)
          | _ =>
              KTerm.mkApps (oldHead `sigma)
                [lowerRaw ctx A, lowerRaw ctx (.tmApp `lam bindersAndBody)]
      | [] => KTerm.mkApps (oldHead `sigma) [lowerRaw ctx A]
  | .tyApp `sigma [A, B] => .sigma (lowerRaw ctx A) (lowerRaw (pushAnonymousBinder ctx) B)
  | .tyApp f args => KTerm.mkApps (oldHead f .syntaxSort) (args.map (lowerRaw ctx))
  | .tySubst A τ => KTerm.mkApps (oldHead `tySubst) [lowerRaw ctx A, lowerRaw ctx τ]
  | .tmVar i => .bvar i
  | .tmMeta x => lowerRef { ctx with metas := ctx.metas.insert (KName.ofName x) .tm } x .tm
  | .tmConst c => oldHead c
  | .tmApp `lam args =>
      match args.reverse with
      | body :: revBinders => lowerLam ctx revBinders.reverse body
      | [] => oldHead `lam
  | .tmApp `_app (fn :: args) => KTerm.mkApps (lowerRaw ctx fn) (args.map (lowerRaw ctx))
  | .tmApp `pair [a, b] => .pair (lowerRaw ctx a) (lowerRaw ctx b)
  | .tmApp `fst [e] => .fst (lowerRaw ctx e)
  | .tmApp `snd [e] => .snd (lowerRaw ctx e)
  | .tmApp `jeq [lhs, rhs] => .jeq (lowerRaw ctx lhs) (lowerRaw ctx rhs)
  | .tmApp f args => KTerm.mkApps (oldHead f) (args.map (lowerRaw ctx))
  | .tmSubst t τ => KTerm.mkApps (oldHead `tmSubst) [lowerRaw ctx t, lowerRaw ctx τ]
  | .substId Γ => KTerm.mkApps (oldHead `substId) [lowerRaw ctx Γ]
  | .substMeta x =>
      lowerRef { ctx with metas := ctx.metas.insert (KName.ofName x) .subst } x .subst
  | .substComp τ υ => KTerm.mkApps (oldHead `substComp) [lowerRaw ctx τ, lowerRaw ctx υ]
  | .substEmpty => oldHead `substEmpty
  | .substExt τ t => KTerm.mkApps (oldHead `substExt) [lowerRaw ctx τ, lowerRaw ctx t]
  | .scopedBind zone cls x ty body =>
      KTerm.mkApps (oldHead `scopedBind)
        [oldHead zone, oldHead cls, lowerRaw ctx ty, lowerRaw (pushBinder ctx x) body]
  | .leanParam x => lowerRef ctx x

end

/-- Build a meta map from old raw rule metavariables. -/
def metaMapOfOldVars (vars : List _root_.InternalLean.RuleMetaVar) :
    Std.HashMap KName RawMetaSort := Id.run do
  let mut out : Std.HashMap KName RawMetaSort := {}
  for v in vars do
    out := out.insert (KName.ofName v.name) v.sort
  return out

/-- Decode old raw syntax without schema metavariable metadata. -/
def lowerRawClosed (raw : Raw) : KTerm :=
  lowerRaw {} raw

/-- Decode old raw syntax with a schema metavariable map. -/
def lowerRawWithMetas (metas : Std.HashMap KName RawMetaSort) (raw : Raw) : KTerm :=
  lowerRaw { metas := metas } raw

end RawLowering

/-- Convert an old raw-kernel judgment to a structural judgment. -/
def Judgment.ofOldWithMetas (metas : Std.HashMap KName RawMetaSort) :
    _root_.InternalLean.Judgment → Judgment
  | .wfCtx Γ => { head := KName.ofName `wfCtx, args := [RawLowering.lowerRawWithMetas metas Γ] }
  | .wfTy Γ A =>
      { head := KName.ofName `wfTy
        args := [RawLowering.lowerRawWithMetas metas Γ, RawLowering.lowerRawWithMetas metas A] }
  | .wfTm Γ t A =>
      { head := KName.ofName `wfTm
        args := [RawLowering.lowerRawWithMetas metas Γ, RawLowering.lowerRawWithMetas metas t,
          RawLowering.lowerRawWithMetas metas A] }
  | .wfSubst Δ τ Γ =>
      { head := KName.ofName `wfSubst
        args := [RawLowering.lowerRawWithMetas metas Δ, RawLowering.lowerRawWithMetas metas τ,
          RawLowering.lowerRawWithMetas metas Γ] }
  | .eqTy Γ A B =>
      { head := KName.ofName `eqTy
        args := [RawLowering.lowerRawWithMetas metas Γ, RawLowering.lowerRawWithMetas metas A,
          RawLowering.lowerRawWithMetas metas B] }
  | .eqTm Γ t u A =>
      { head := KName.ofName `eqTm
        args := [RawLowering.lowerRawWithMetas metas Γ, RawLowering.lowerRawWithMetas metas t,
          RawLowering.lowerRawWithMetas metas u, RawLowering.lowerRawWithMetas metas A] }
  | .custom k args =>
      { head := KName.ofName k, args := args.map (RawLowering.lowerRawWithMetas metas) }

/-- Convert an old raw-kernel judgment with no schema metavariable metadata. -/
def Judgment.ofOld (j : _root_.InternalLean.Judgment) : Judgment :=
  Judgment.ofOldWithMetas {} j

/-- Convert an old rule metavariable schema. -/
def RuleMetaVar.ofOld (metas : Std.HashMap KName RawMetaSort)
    (v : _root_.InternalLean.RuleMetaVar) : RuleMetaVar :=
  { name := KName.ofName v.name
    sort := v.sort
    zone? := v.zone?.map KName.ofName
    type? := v.type?.map (RawLowering.lowerRawWithMetas metas)
    evidence? := v.evidence?.map (Judgment.ofOldWithMetas metas) }

/-- Convert an old side condition. -/
def SideCondition.ofOld (metas : Std.HashMap KName RawMetaSort)
    (sc : _root_.InternalLean.SideCondition) : SideCondition :=
  { name := KName.ofName sc.name, args := sc.args.map (RawLowering.lowerRawWithMetas metas) }

/-- Convert an old side-condition certificate slot. -/
def SideConditionCertificateSlot.ofOld (metas : Std.HashMap KName RawMetaSort)
    (slot : _root_.InternalLean.SideConditionCertificateSlot) : SideConditionCertificateSlot :=
  { name := KName.ofName slot.name, condition := SideCondition.ofOld metas slot.condition }

/-- Convert an old checked side-condition certificate. -/
def SideConditionCertificate.ofOld (metas : Std.HashMap KName RawMetaSort)
    (cert : _root_.InternalLean.SideConditionCertificate) : SideConditionCertificate :=
  { name := KName.ofName cert.name
    condition := SideCondition.ofOld metas cert.condition
    kind := cert.kind
    payload := cert.payload }

/-- Convert an old scoped-instantiation entry. -/
def ScopedInstantiationEntry.ofOld (e : _root_.InternalLean.ScopedInstantiationEntry) :
    ScopedInstantiationEntry :=
  { name := KName.ofName e.name
    sort := e.sort
    zone? := e.zone?.map KName.ofName
    type? := e.type?.map RawLowering.lowerRawClosed
    evidence? := e.evidence?.map Judgment.ofOld
    value := RawLowering.lowerRawClosed e.value }

/-- Convert an old scoped instantiation. -/
def ScopedInstantiation.ofOld (σ : _root_.InternalLean.ScopedInstantiation) :
    ScopedInstantiation :=
  { entries := σ.entries.map ScopedInstantiationEntry.ofOld }

/-- Convert an old typed LF constant schema. -/
def LFConstantSchema.ofOld (c : _root_.InternalLean.LFConstantSchema) : LFConstantSchema :=
  let metas := RawLowering.metaMapOfOldVars c.params
  { name := KName.ofName c.name
    params := c.params.map (RuleMetaVar.ofOld metas)
    resultType := RawLowering.lowerRawWithMetas metas c.resultType }

/-- Convert an old conversion plugin schema. -/
def ConversionPluginSchema.ofOld (p : _root_.InternalLean.ConversionPluginSchema) :
    ConversionPluginSchema :=
  { name := KName.ofName p.name, trust := p.trust, supportedSteps := p.supportedSteps }

/-- Convert an old rule schema. -/
def RuleSchema.ofOld (r : _root_.InternalLean.RuleSchema) : RuleSchema :=
  let metas := RawLowering.metaMapOfOldVars r.metavariables
  { name := KName.ofName r.name
    metavariables := r.metavariables.map (RuleMetaVar.ofOld metas)
    premises := r.premises.map (Judgment.ofOldWithMetas metas)
    sideConditions := r.sideConditions.map (SideCondition.ofOld metas)
    sideConditionCertificates :=
      r.sideConditionCertificates.map (SideConditionCertificateSlot.ofOld metas)
    checkedSideConditionCertificates :=
      r.checkedSideConditionCertificates.map (SideConditionCertificate.ofOld metas)
    conclusionStmt := Judgment.ofOldWithMetas metas r.conclusion }

/-- Convert an old context-zone schema. -/
def ContextZoneSchema.ofOld (z : _root_.InternalLean.ContextZoneSchema) : ContextZoneSchema :=
  { name := KName.ofName z.name, sort := z.sort, dependsOn := z.dependsOn.map KName.ofName }

/-- Convert an old binder-class schema. -/
def BinderClassSchema.ofOld (b : _root_.InternalLean.BinderClassSchema) : BinderClassSchema :=
  { name := KName.ofName b.name
    zone := KName.ofName b.zone
    boundSort := b.boundSort
    dependsOn := b.dependsOn.map KName.ofName }

/-- Convert an old raw-kernel signature to a structural signature. -/
def Signature.ofOld (sig : _root_.InternalLean.Signature) : Signature :=
  { name := KName.ofName sig.name
    constants := sig.constants.map LFConstantSchema.ofOld
    contextZones := sig.contextZones.map ContextZoneSchema.ofOld
    binderClasses := sig.binderClasses.map BinderClassSchema.ofOld
    conversionPlugins := sig.conversionPlugins.map ConversionPluginSchema.ofOld
    rules := sig.rules.map RuleSchema.ofOld }

/-- Convert an old theorem entry. -/
def KernelLFTheoremEntry.ofOld (e : _root_.InternalLean.KernelLFTheoremEntry) :
    KernelLFTheoremEntry :=
  { name := KName.ofName e.name, statement := Judgment.ofOld e.statement }

/-- Convert an old external certificate entry. -/
def KernelLFCertificateEntry.ofOld (e : _root_.InternalLean.KernelLFCertificateEntry) :
    KernelLFCertificateEntry :=
  { name := KName.ofName e.name
    statement := Judgment.ofOld e.statement
    certificateName := KName.ofName e.certificateName }

/-- Convert an old conversion statement. -/
def ConversionStatement.ofOld (stmt : _root_.InternalLean.ConversionStatement) :
    ConversionStatement :=
  { plugin := KName.ofName stmt.plugin
    context? := stmt.context?.map RawLowering.lowerRawClosed
    lhs := RawLowering.lowerRawClosed stmt.lhs
    rhs := RawLowering.lowerRawClosed stmt.rhs }

/-- Convert an old conversion-certificate entry. -/
def KernelLFConversionCertificateEntry.ofOld
    (e : _root_.InternalLean.KernelLFConversionCertificateEntry) :
    KernelLFConversionCertificateEntry :=
  { certificateName := KName.ofName e.certificateName
    statement := ConversionStatement.ofOld e.statement
    stepKind := e.stepKind }

/-- Convert an old replay context. -/
def KernelLFCheckContext.ofOld (ctx : _root_.InternalLean.KernelLFCheckContext) :
    KernelLFCheckContext :=
  { localParameters := ctx.localParameters.map KLocalName.ofName
    assumptions := ctx.assumptions.map KernelLFTheoremEntry.ofOld
    theorems := ctx.theorems.map KernelLFTheoremEntry.ofOld
    certificates := ctx.certificates.map KernelLFCertificateEntry.ofOld
    conversionCertificates :=
      ctx.conversionCertificates.map KernelLFConversionCertificateEntry.ofOld }

namespace KernelLFDerivation

/-- Convert an old raw-kernel derivation to a structural derivation for dual replay. -/
partial def ofOld : _root_.InternalLean.KernelLFDerivation → KernelLFDerivation
  | .assumption name stmt => .assumption (KName.ofName name) (Judgment.ofOld stmt)
  | .theoremRef name stmt => .theoremRef (KName.ofName name) (Judgment.ofOld stmt)
  | .certificate name stmt certificateName =>
      .certificate (KName.ofName name) (Judgment.ofOld stmt) (KName.ofName certificateName)
  | .ruleApp ruleName concl inst premises certificateNames =>
      .ruleApp (KName.ofName ruleName) (Judgment.ofOld concl) (ScopedInstantiation.ofOld inst)
        (premises.map ofOld) (certificateNames.map KName.ofName)

end KernelLFDerivation

namespace KernelLFConversionCertificate

/-- Convert an old raw-kernel conversion certificate to a structural certificate. -/
partial def ofOld : _root_.InternalLean.KernelLFConversionCertificate →
    KernelLFConversionCertificate
  | .refl stmt => .refl (ConversionStatement.ofOld stmt)
  | .symm stmt child => .symm (ConversionStatement.ofOld stmt) (ofOld child)
  | .trans stmt middle left right =>
      .trans (ConversionStatement.ofOld stmt) (RawLowering.lowerRawClosed middle) (ofOld left)
        (ofOld right)
  | .pluginStep stmt kind externalCertificateName? sideConditionCertificateNames payload =>
      .pluginStep (ConversionStatement.ofOld stmt) kind (externalCertificateName?.map KName.ofName)
        (sideConditionCertificateNames.map KName.ofName) payload

end KernelLFConversionCertificate

end Kernel

end InternalLean
