/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Basic

/-!
# Structural LF kernel

This module contains InternalLean's structural LF replay kernel. It uses first-class constructors
for binders, applications, structural products/functions, universes, and judgmental equality.
Replay registration and executable conversion checks use direct checked-LF-to-structural
lowering. Legacy raw replay is no longer part of the registered LF theorem boundary.
-/

@[expose] public section

open Lean

namespace InternalLean

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
  deriving Inhabited, Repr

namespace KHead

/-- Semantic equality for resolved heads. -/
def alphaEq (a b : KHead) : Bool :=
  a.name == b.name

instance : BEq KHead where
  beq := alphaEq

end KHead

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
  deriving Inhabited, Repr

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
partial def alphaEq : KTerm → KTerm → Bool
  | .ident a, .ident b => a.alphaEq b
  | .fvar a, .fvar b => a == b
  | .bvar a, .bvar b => a == b
  | .mvar an as, .mvar bn bs => an == bn && as == bs
  | .app af aa, .app bf ba => alphaEq af bf && alphaEq aa ba
  | .lam a, .lam b => alphaEq a b
  | .arrow aDom aCod, .arrow bDom bCod => alphaEq aDom bDom && alphaEq aCod bCod
  | .sigma aDom aCod, .sigma bDom bCod => alphaEq aDom bDom && alphaEq aCod bCod
  | .pair al ar, .pair bl br => alphaEq al bl && alphaEq ar br
  | .fst a, .fst b => alphaEq a b
  | .snd a, .snd b => alphaEq a b
  | .univ a, .univ b => a == b
  | .jeq al ar, .jeq bl br => alphaEq al bl && alphaEq ar br
  | _, _ => false

instance : BEq KTerm where
  beq := alphaEq

/-- Validate that a structural term has no loose de Bruijn indices. -/
def ensureLocallyClosed (label : String) (e : KTerm) : Except String Unit := do
  unless e.isLocallyClosed do
    throw s!"{label} contains a loose de Bruijn index"

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
  deriving Inhabited, Repr

namespace Judgment

/-- Instantiate schema metavariables in a judgment. -/
def instantiateMetas (σ : KInstantiation) (j : Judgment) : Except String Judgment := do
  return { j with args := (← j.args.mapM (KTerm.instantiateMetas σ)) }

/-- Structural equality, valid as alpha-equivalence for locally closed KTerm arguments. -/
def alphaEq (a b : Judgment) : Bool :=
  a.head == b.head && a.args.length == b.args.length &&
    (a.args.zip b.args).all (fun pair => pair.1.alphaEq pair.2)

instance : BEq Judgment where
  beq := alphaEq

/-- Whether every argument of a structural judgment is locally closed. -/
def isLocallyClosed (j : Judgment) : Bool :=
  j.args.all KTerm.isLocallyClosed

/-- Validate that a structural judgment contains no loose de Bruijn indices. -/
def ensureLocallyClosed (label : String) (j : Judgment) : Except String Unit := do
  unless j.isLocallyClosed do
    throw s!"{label} contains a loose de Bruijn index"

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

namespace SideCondition

/-- Validate that a side condition contains no loose de Bruijn indices. -/
def ensureLocallyClosed (label : String) (sc : SideCondition) : Except String Unit := do
  for arg in sc.args do
    KTerm.ensureLocallyClosed label arg

end SideCondition

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

/-- Structural conversion profile for an object-language level normalizer. -/
structure LevelNormalizerKProfile where
  zeroName : KName
  succName : KName
  maxName : KName
  deriving Inhabited, Repr, BEq

/-- Conversion-plugin schema for structural conversion checking. -/
structure ConversionPluginSchema where
  name : KName
  trust : ConversionPluginTrustKind := .opaqueAssumption
  supportedSteps : List ConversionStepKind := []
  levelNormalizer? : Option LevelNormalizerKProfile := none
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

/-- Semantic equality for structural conversion statements. -/
def alphaEq (a b : ConversionStatement) : Bool :=
  a.plugin == b.plugin && a.context? == b.context? && a.lhs.alphaEq b.lhs &&
    a.rhs.alphaEq b.rhs

/-- Validate that a conversion statement contains no loose de Bruijn indices. -/
def ensureLocallyClosed (label : String) (stmt : ConversionStatement) : Except String Unit := do
  if let some ctx := stmt.context? then
    KTerm.ensureLocallyClosed label ctx
  KTerm.ensureLocallyClosed label stmt.lhs
  KTerm.ensureLocallyClosed label stmt.rhs

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

/-- Convert scoped-instantiation entries to a finite metavariable map. -/
def entriesAsInstantiation (entries : List ScopedInstantiationEntry) : KInstantiation :=
  Id.run do
    let mut out : KInstantiation := {}
    for e in entries do
      out := out.insert e.name e.value
    return out

/-- Convert a scoped instantiation to a finite metavariable map. -/
def asInstantiation (σ : ScopedInstantiation) : KInstantiation :=
  entriesAsInstantiation σ.entries

/-- Instantiate an optional structural term with a prefix metavariable map. -/
def instantiateTermOption (σ : KInstantiation) : Option KTerm → Except String (Option KTerm)
  | none => pure none
  | some e => return some (← KTerm.instantiateMetas σ e)

/-- Instantiate an optional structural judgment with a prefix metavariable map. -/
def instantiateJudgmentOption (σ : KInstantiation) :
    Option Judgment → Except String (Option Judgment)
  | none => pure none
  | some j => return some (← Judgment.instantiateMetas σ j)

/-- Validate a scoped instantiation against a rule metavariable telescope. -/
def validateAgainst (σ : ScopedInstantiation) (metavariables : List RuleMetaVar) :
    Except String Unit := do
  if σ.entries.length != metavariables.length then
    throw s!"scoped instantiation has {σ.entries.length} entrie(s), expected \
      {metavariables.length}"
  let mut processed : List ScopedInstantiationEntry := []
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
    unless e.value.isLocallyClosed do
      throw s!"scoped instantiation entry '{e.name}' has a value with loose binders"
    let expectedType? ← instantiateTermOption (entriesAsInstantiation processed) v.type?
    match e.type?, expectedType? with
    | some actual, some expected =>
        unless actual.alphaEq expected do
          throw s!"scoped instantiation entry '{e.name}' has a type annotation that differs \
            from the rule telescope"
    | none, none => pure ()
    | _, _ =>
        throw s!"scoped instantiation entry '{e.name}' has a type annotation that differs from \
          the rule telescope"
    let expectedEvidence? ←
      instantiateJudgmentOption (entriesAsInstantiation (processed ++ [e])) v.evidence?
    match e.evidence?, expectedEvidence? with
    | some actual, some expected =>
        unless actual.alphaEq expected do
          throw s!"scoped instantiation entry '{e.name}' has evidence that differs from the \
            rule telescope"
    | none, none => pure ()
    | _, _ =>
        throw s!"scoped instantiation entry '{e.name}' has evidence that differs from the rule \
          telescope"
    processed := processed ++ [e]

end ScopedInstantiation

/-- Typed LF constant schema for structural replay. -/
structure LFConstantSchema where
  name : KName
  params : List RuleMetaVar := []
  kind : KHeadKind := .primitive
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
    let mut seenParams : Std.HashSet KName := {}
    for p in c.params do
      if seenParams.contains p.name then
        throw s!"typed LF constant '{c.name}' in signature '{sig.name}' has duplicate \
          parameter '{p.name}'"
      seenParams := seenParams.insert p.name
      if let some ty := p.type? then
        KTerm.ensureLocallyClosed s!"typed LF constant '{c.name}' parameter '{p.name}' type" ty
      if let some ev := p.evidence? then
        Judgment.ensureLocallyClosed
          s!"typed LF constant '{c.name}' parameter '{p.name}' evidence" ev
    KTerm.ensureLocallyClosed s!"typed LF constant '{c.name}' result type" c.resultType
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
      if let some ty := v.type? then
        KTerm.ensureLocallyClosed s!"rule '{r.name}' metavariable '{v.name}' type" ty
      if let some ev := v.evidence? then
        Judgment.ensureLocallyClosed s!"rule '{r.name}' metavariable '{v.name}' evidence" ev
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
    for p in r.premises do
      Judgment.ensureLocallyClosed s!"rule '{r.name}' premise" p
    for sc in r.sideConditions do
      SideCondition.ensureLocallyClosed s!"rule '{r.name}' side condition '{sc.name}'" sc
    for slot in r.sideConditionCertificates do
      SideCondition.ensureLocallyClosed
        s!"rule '{r.name}' certificate slot '{slot.name}'" slot.condition
    for cert in r.checkedSideConditionCertificates do
      SideCondition.ensureLocallyClosed
        s!"rule '{r.name}' checked certificate '{cert.name}'" cert.condition
    Judgment.ensureLocallyClosed s!"rule '{r.name}' conclusion" r.conclusionStmt
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
    Judgment.ensureLocallyClosed s!"checked replay assumption '{e.name}'" e.statement
    assumptionsByName := assumptionsByName.insert e.name e
  let mut theoremsByName : Std.HashMap KName KernelLFTheoremEntry := {}
  for e in ctx.theorems do
    if theoremsByName.contains e.name then
      throw s!"checked replay context has duplicate theorem entry '{e.name}'"
    Judgment.ensureLocallyClosed s!"checked replay theorem '{e.name}'" e.statement
    theoremsByName := theoremsByName.insert e.name e
  let mut certificatesByName : Std.HashMap KName KernelLFCertificateEntry := {}
  let mut certificatesByCertificateName : Std.HashMap KName KernelLFCertificateEntry := {}
  for e in ctx.certificates do
    if certificatesByName.contains e.name then
      throw s!"checked replay context has duplicate certificate entry '{e.name}'"
    if certificatesByCertificateName.contains e.certificateName then
      throw s!"checked replay context has duplicate certificate token '{e.certificateName}'"
    Judgment.ensureLocallyClosed s!"checked replay certificate '{e.name}'" e.statement
    certificatesByName := certificatesByName.insert e.name e
    certificatesByCertificateName := certificatesByCertificateName.insert e.certificateName e
  let mut conversionCertificatesByCertificateName :
      Std.HashMap KName KernelLFConversionCertificateEntry := {}
  for e in ctx.conversionCertificates do
    if conversionCertificatesByCertificateName.contains e.certificateName then
      throw s!"checked replay context has duplicate conversion certificate token \
        '{e.certificateName}'"
    ConversionStatement.ensureLocallyClosed
      s!"checked replay conversion certificate '{e.certificateName}'" e.statement
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

/-- Normalizer budget for structural executable level-conversion leaves. -/
def levelNormalizerKFuelLimit : Nat := 4096

/-- Normal form for the first-order level fragment over structural terms.

This mirrors `InternalLean.LevelNormalizerRawNF` and `LFElab.Kernel.LevelNormalizerObjNF`. The
copies stay separate so the raw compatibility checker and structural checker do not share trusted
syntax. -/
structure LevelNormalizerKNF where
  floor : Nat := 0
  atoms : List (KTerm × Nat) := []
  deriving Inhabited, Repr

namespace LevelNormalizerKNF

/-- Look up an atom offset. -/
def atomOffset? (nf : LevelNormalizerKNF) (atom : KTerm) : Option Nat :=
  (nf.atoms.find? (fun entry => entry.1.alphaEq atom)).map Prod.snd

/-- Set one atom to the maximum of the old and new offsets. -/
def setAtomMax (nf : LevelNormalizerKNF) (atom : KTerm) (offset : Nat) : LevelNormalizerKNF :=
  let rec go : List (KTerm × Nat) → List (KTerm × Nat)
    | [] => [(atom, offset)]
    | (oldAtom, oldOffset) :: rest =>
        if oldAtom.alphaEq atom then
          (oldAtom, Nat.max oldOffset offset) :: rest
        else
          (oldAtom, oldOffset) :: go rest
  { nf with atoms := go nf.atoms }

/-- Successor of a structural level normal form. -/
def succ (nf : LevelNormalizerKNF) : LevelNormalizerKNF :=
  { floor := nf.floor + 1
    atoms := nf.atoms.map (fun entry => (entry.1, entry.2 + 1)) }

/-- Maximum of two structural level normal forms. -/
def max (lhs rhs : LevelNormalizerKNF) : LevelNormalizerKNF := Id.run do
  let mut out := { lhs with floor := Nat.max lhs.floor rhs.floor }
  for (atom, offset) in rhs.atoms do
    out := out.setAtomMax atom offset
  return out

/-- Equality of structural level normal forms, ignoring atom insertion order. -/
def equal (lhs rhs : LevelNormalizerKNF) : Bool :=
  lhs.floor == rhs.floor && lhs.atoms.length == rhs.atoms.length &&
    lhs.atoms.all (fun entry => rhs.atomOffset? entry.1 == some entry.2)

/-- Render a compact normal-form summary. -/
def format (nf : LevelNormalizerKNF) : String :=
  let floorPart := if nf.floor == 0 then [] else [toString nf.floor]
  let atomPart := nf.atoms.map fun (atom, offset) =>
    let atomText := reprStr atom
    if offset == 0 then atomText else s!"{atomText}+{offset}"
  match floorPart ++ atomPart with
  | [] => "0"
  | [part] => part
  | parts => s!"max({String.intercalate ", " parts})"

end LevelNormalizerKNF

/-- Normalize one structural level term for an executable conversion plugin. -/
def normalizeKLevel (profile : LevelNormalizerKProfile) (term : KTerm)
    (fuel : Nat := levelNormalizerKFuelLimit) :
    Except ConversionCheckFailure LevelNormalizerKNF := do
  match fuel with
  | 0 =>
      throwFailure .unsupportedConversion <|
        s!"level normalizer budget exhausted while normalizing structural term '{reprStr term}'"
  | fuel + 1 =>
      match term with
      | .ident h =>
          if h.name == profile.zeroName then
            pure {}
          else
            pure { atoms := [(term, 0)] }
      | .app (.ident h) arg =>
          if h.name == profile.succName then
            return (← normalizeKLevel profile arg fuel).succ
          else
            throwFailure .unsupportedConversion <|
              s!"level normalizer does not support application headed by '{h.name}'"
      | .app (.app (.ident h) lhs) rhs =>
          if h.name == profile.maxName then
            return LevelNormalizerKNF.max (← normalizeKLevel profile lhs fuel)
              (← normalizeKLevel profile rhs fuel)
          else
            throwFailure .unsupportedConversion <|
              s!"level normalizer does not support application headed by '{h.name}'"
      | .fvar _ | .mvar .. =>
          pure { atoms := [(term, 0)] }
      | .app .. =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer does not support structural application '{reprStr term}'"
      | _ =>
          throwFailure .unsupportedConversion <|
            s!"level normalizer does not support structural term '{reprStr term}'"

/-- Validate a structural level-normalization conversion leaf. -/
def validateKLevelNormalization (profile : LevelNormalizerKProfile) (stmt : ConversionStatement) :
    Except ConversionCheckFailure Unit := do
  let lhs ← normalizeKLevel profile stmt.lhs
  let rhs ← normalizeKLevel profile stmt.rhs
  unless lhs.equal rhs do
    throwFailure .malformedCertificate <|
      s!"level-normalizer conversion failed: lhs normal form {lhs.format}, rhs normal form \
        {rhs.format}"

/-- Validate the currently implemented structural executable conversion steps. -/
def validateExecutableStep (plugin : ConversionPluginSchema) (stmt : ConversionStatement)
    (kind : ConversionStepKind) : Except ConversionCheckFailure Unit := do
  match plugin.levelNormalizer?, kind with
  | some profile, .reindexing =>
      validateKLevelNormalization profile stmt
  | _, .beta =>
      match stmt.lhs.betaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{plugin.name}' beta step reduces lhs to a \
                different rhs"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{plugin.name}' beta step expected a structural redex"
  | _, .eta =>
      match stmt.lhs.etaReduce? with
      | some rhs =>
          unless rhs.alphaEq stmt.rhs do
            throwFailure .malformedCertificate <|
              s!"checked conversion plugin '{plugin.name}' eta step contracts lhs to a \
                different rhs"
      | none =>
          throwFailure .malformedCertificate <|
            s!"checked conversion plugin '{plugin.name}' eta step expected a structural eta-redex"
  | _, _ =>
      throwFailure .unsupportedConversion <|
        s!"checked conversion plugin '{plugin.name}' has no structural executable engine for \
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
      validateExecutableStep plugin stmt kind
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
      unless entry.statement.alphaEq stmt do
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
      unless stmt.alphaEq expected do
        throwFailure .malformedCertificate "conversion refl has an unexpected statement"
      unless stmt.lhs.alphaEq stmt.rhs do
        throwFailure .malformedCertificate s!"conversion refl for plugin '{stmt.plugin}' has \
          non-identical endpoints"
  | .symm stmt child, expected => do
      unless stmt.alphaEq expected do
        throwFailure .malformedCertificate "conversion symm has an unexpected statement"
      checkWithContextDetailedCore ctx sig child stmt.symm
  | .trans stmt middle left right, expected => do
      unless stmt.alphaEq expected do
        throwFailure .malformedCertificate "conversion trans has an unexpected statement"
      checkWithContextDetailedCore ctx sig left (stmt.withRhs middle)
      checkWithContextDetailedCore ctx sig right (stmt.withLhs middle)
  | .pluginStep stmt kind externalCertificateName? sideConditionCertificateNames payload,
      expected => do
      unless stmt.alphaEq expected do
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
  match ConversionStatement.ensureLocallyClosed "checked conversion statement" statement with
  | .ok () => pure ()
  | .error err => KernelLFConversionCertificate.throwFailure .malformedCertificate err
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
      rule conclusion: got {repr concl}; expected {repr expectedConclusion}"
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
        throw s!"rule application '{ruleName}' has an unexpected conclusion: got {repr concl}; \
          expected {repr expected}"
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

/-- Build a checked structural replay wrapper from an unchecked structural payload. -/
def ofReplay (signature : Signature) (context : KernelLFCheckContext) (statement : Judgment)
    (derivation : KernelLFDerivation) : Except String CheckedKernelLFDerivation := do
  Judgment.ensureLocallyClosed "checked replay wrapper statement" statement
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
  Judgment.ensureLocallyClosed "kernel replay certificate statement" cert.statement
  let ctx ← ValidatedReplayContext.ofContext cert.context
  let sig ← ValidatedSignature.ofSignature cert.signature
  KernelLFDerivation.checkWithValidatedContext ctx sig cert.derivation cert.statement

/-- Convert a compact structural certificate to a checked wrapper. -/
def toChecked (cert : KernelLFReplayCertificate) : Except String CheckedKernelLFDerivation :=
  CheckedKernelLFDerivation.ofReplay cert.signature cert.context cert.statement cert.derivation

end KernelLFReplayCertificate

/-- Find a structural rule by name together with its source-order membership proof. -/
def findRuleWithProof? (sig : Signature) (name : KName) :
    Option { r : RuleSchema // r ∈ sig.rules } :=
  let rec go : (rules : List RuleSchema) → Option { r : RuleSchema // r ∈ rules }
    | [] => none
    | r :: rs =>
        if r.name == name then
          some ⟨r, List.Mem.head _⟩
        else
          match go rs with
          | some ⟨r', h⟩ => some ⟨r', List.Mem.tail _ h⟩
          | none => none
  go sig.rules

/-- Find a theorem entry by name together with its source-order membership proof. -/
def findTheoremEntryInListWithProof? (name : KName) :
    (entries : List KernelLFTheoremEntry) →
      Option { e : KernelLFTheoremEntry // e ∈ entries }
  | [] => none
  | e :: es =>
      if e.name == name then
        some ⟨e, List.Mem.head _⟩
      else
        match findTheoremEntryInListWithProof? name es with
        | some ⟨e', h⟩ => some ⟨e', List.Mem.tail _ h⟩
        | none => none

/-- Find a certificate entry by name together with its source-order membership proof. -/
def findCertificateEntryInListWithProof? (name : KName) :
    (entries : List KernelLFCertificateEntry) →
      Option { e : KernelLFCertificateEntry // e ∈ entries }
  | [] => none
  | e :: es =>
      if e.name == name then
        some ⟨e, List.Mem.head _⟩
      else
        match findCertificateEntryInListWithProof? name es with
        | some ⟨e', h⟩ => some ⟨e', List.Mem.tail _ h⟩
        | none => none

namespace KernelLFDerivation

mutual
  /-- Context-relative structural replay evidence after executable validation. -/
  inductive ContextDeriv (sig : Signature) (ctx : KernelLFCheckContext) :
      Judgment → Type 1 where
    | assumption (e : KernelLFTheoremEntry) :
        e ∈ ctx.assumptions → ContextDeriv sig ctx e.statement
    | theorem (e : KernelLFTheoremEntry) :
        e ∈ ctx.theorems → ContextDeriv sig ctx e.statement
    | certificate (e : KernelLFCertificateEntry) :
        e ∈ ctx.certificates → ContextDeriv sig ctx e.statement
    | rule (r : RuleSchema) (σ : KInstantiation) (concl : Judgment) :
        r ∈ sig.rules →
        r.instantiateConclusion σ = .ok concl →
        ContextDerivList sig ctx σ r.premises →
        ContextDeriv sig ctx concl

  /-- Context-relative evidence for instantiated structural replay premises. -/
  inductive ContextDerivList (sig : Signature) (ctx : KernelLFCheckContext) :
      KInstantiation → List Judgment → Type 1 where
    | nil {σ : KInstantiation} : ContextDerivList sig ctx σ []
    | cons {σ : KInstantiation} {p : Judgment} {ps : List Judgment} {p' : Judgment} :
        p.instantiateMetas σ = .ok p' →
        ContextDeriv sig ctx p' →
        ContextDerivList sig ctx σ ps →
        ContextDerivList sig ctx σ (p :: ps)
end

noncomputable section ContextDerivProducer

mutual
  /-- Extract context-relative structural evidence from a replay tree.

  Use `CheckedKernelLFDerivation.toContextDeriv?` at trust boundaries; it re-runs the executable
  replay check before calling this producer. -/
  partial def toContextDeriv? (ctx : KernelLFCheckContext) (sig : Signature) :
      (d : KernelLFDerivation) → Except String (ContextDeriv sig ctx d.statement)
    | .assumption name stmt => do
        let some ⟨entry, hmem⟩ := findTheoremEntryInListWithProof? name ctx.assumptions
          | throw s!"local theorem assumption '{name}' is not available in the checked replay \
              context"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.assumption entry hmem)
        else
          throw s!"local theorem assumption '{name}' has a statement different from the replay \
            context"
    | .theoremRef name stmt => do
        let some ⟨entry, hmem⟩ := findTheoremEntryInListWithProof? name ctx.theorems
          | throw s!"theorem reference '{name}' is not available in the checked replay context"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.theorem entry hmem)
        else
          throw s!"theorem reference '{name}' has a statement different from the replay context"
    | .certificate name stmt certificateName => do
        let some ⟨entry, hmem⟩ := findCertificateEntryInListWithProof? name ctx.certificates
          | throw s!"certificate-backed derivation '{name}' is not available in the checked \
              certificate context"
        if entry.certificateName != certificateName then
          throw s!"certificate-backed derivation '{name}' uses certificate '{certificateName}', \
            expected '{entry.certificateName}'"
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        if h : entry.statement = stmt then
          pure (h ▸ ContextDeriv.certificate entry hmem)
        else
          throw s!"certificate-backed derivation '{name}' has a statement different from the \
            certificate context"
    | .ruleApp ruleName concl inst premises certificateNames => do
        let some ⟨r, hr⟩ := findRuleWithProof? sig ruleName
          | throw s!"rule application uses unknown rule '{ruleName}'"
        match ValidatedSignature.ofSignature sig with
        | .error err => throw err
        | .ok validatedSig =>
            match validateRuleApplicationAgainstRule validatedSig ruleName r concl inst
                premises.length certificateNames with
            | .ok () => pure PUnit.unit
            | .error err => throw err
            let σ := inst.asInstantiation
            let premiseDerivs ← toContextDerivList? ctx sig σ premises r.premises
            let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
            match hInst : r.instantiateConclusion σ with
            | .ok expected =>
                if h : expected = concl then
                  pure (h ▸ ContextDeriv.rule r σ expected hr hInst premiseDerivs)
                else
                  throw s!"rule application '{ruleName}' has an unexpected conclusion"
            | .error err => throw err

  /-- Extract context-relative evidence for a list of replay premise trees. -/
  partial def toContextDerivList? (ctx : KernelLFCheckContext) (sig : Signature)
      (σ : KInstantiation) :
      (ds : List KernelLFDerivation) → (ps : List Judgment) →
        Except String (ContextDerivList sig ctx σ ps)
    | [], [] => pure ContextDerivList.nil
    | d :: ds, p :: ps => do
        let rest ← toContextDerivList? ctx sig σ ds ps
        let dDeriv ← toContextDeriv? ctx sig d
        let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
        match hInst : p.instantiateMetas σ with
        | .ok expected =>
            if h : d.statement = expected then
              pure (ContextDerivList.cons hInst (h ▸ dDeriv) rest)
            else
              throw s!"premise replay has an unexpected statement"
        | .error err => throw err
    | ds, ps =>
        throw s!"context derivation producer has {ds.length} premise derivation(s), expected \
          {ps.length}"
end

end ContextDerivProducer

end KernelLFDerivation

namespace CheckedKernelLFDerivation

noncomputable section ContextDerivProducer

/-- Produce context-relative structural evidence after re-running executable replay validation. -/
def toContextDeriv? (checked : CheckedKernelLFDerivation) :
    Except String
      (KernelLFDerivation.ContextDeriv checked.signature checked.context checked.statement) :=
  match checked.check with
  | .error err => throw err
  | .ok () => do
      let derivation ← KernelLFDerivation.toContextDeriv? checked.context checked.signature
        checked.derivation
      let _ : DecidableEq Judgment := Classical.typeDecidableEq Judgment
      if h : checked.derivation.statement = checked.statement then
        pure (h ▸ derivation)
      else
        throw "checked replay wrapper statement differs from its derivation statement"

end ContextDerivProducer

end CheckedKernelLFDerivation

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
    (concl : Judgment) →
    r ∈ sig.rules →
    r.instantiateConclusion σ = .ok concl →
    InterpPremises interpJudgment σ r.premises →
    interpJudgment concl

/-- Semantic model for a structural signature and replay context. -/
structure ContextModel (sig : Signature) (ctx : KernelLFCheckContext) extends Model sig where
  interpAssumption : (e : KernelLFTheoremEntry) → e ∈ ctx.assumptions → interpJudgment e.statement
  interpTheorem : (e : KernelLFTheoremEntry) → e ∈ ctx.theorems → interpJudgment e.statement
  interpCertificate :
    (e : KernelLFCertificateEntry) → e ∈ ctx.certificates → interpJudgment e.statement

namespace KernelLFDerivation

mutual
  /-- Interpret context-relative structural replay evidence in a context model. -/
  def ContextDeriv.interp {sig : Signature} {ctx : KernelLFCheckContext}
      (M : ContextModel sig ctx) :
      {J : Judgment} → ContextDeriv sig ctx J → M.interpJudgment J
    | _, .assumption e h => M.interpAssumption e h
    | _, .theorem e h => M.interpTheorem e h
    | _, .certificate e h => M.interpCertificate e h
    | _, .rule r σ concl hr hInst premises =>
        M.interpRule r σ concl hr hInst (ContextDerivList.interp M premises)

  /-- Interpret context-relative structural replay evidence for a premise list. -/
  def ContextDerivList.interp {sig : Signature} {ctx : KernelLFCheckContext}
      (M : ContextModel sig ctx) :
      {σ : KInstantiation} → {ps : List Judgment} → ContextDerivList sig ctx σ ps →
        InterpPremises M.interpJudgment σ ps
    | _, [], .nil => PUnit.unit
    | _, _ :: _, .cons hInst d ds => by
        dsimp [InterpPremises]
        rw [hInst]
        exact ⟨ContextDeriv.interp M d, ContextDerivList.interp M ds⟩
end

end KernelLFDerivation

end Kernel

end InternalLean
