/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Lean.Exception
public import Lean.Message
public import InternalLean.Basic
public import InternalLean.Kernel
public meta import InternalLean.Basic

/-!
# User-facing syntax for declaring object type theories

This file contains the high-level metadata layer for commands such as

```lean
declare_type_theory TinyNat where
  syntax_sort Nat
  judgment wfNat (n : Nat)
  lf_opaque zero : Nat
  rule zero_wf : wfNat zero
```

Object expressions have their own syntax category with identifiers, numeric universes
and universe parameters (`Type`, `Type 1`, `Type u`, ...), application, arrows,
dependent arrows, equality expressions, and lambdas. They are
**not** elaborated as Lean terms and do not use Lean's typing or equality.
-/

@[expose] public section

open Lean Elab Command

namespace InternalLean

/-- High-level object expressions parsed from the user-facing DSL.

This is still a small core AST for the current middle path: a generic dependent
function fragment with constants, variables, universe expressions, applications, arrows,
lambdas, and judgmental equality expressions. Later extensions such as cube/tope layers should add
new expression/judgment forms or plugin hooks rather than hard-coding a single
dependent-type-theory fragment everywhere. -/
inductive ObjExpr where
  /-- Identifier, used for constants and local variables before name resolution. -/
  | ident : Name → ObjExpr
  /-- The object universe/type of small types, written `Type`. This is `Type 0`. -/
  | sort : ObjExpr
  /-- An explicit object universe level, written `Type u`. -/
  | univ : LevelExpr → ObjExpr
  /-- Function application. -/
  | app : ObjExpr → ObjExpr → ObjExpr
  /-- Structural/meta-level nondependent or dependent arrow. `none` means a nondependent arrow. -/
  | arrow : Option Name → ObjExpr → ObjExpr → ObjExpr
  /-- Surface compatibility spelling of the structural/function-family arrow, written `→`.
  The explicit framework spelling is `⇒`; both currently share this representation. -/
  | funArrow : Option Name → ObjExpr → ObjExpr → ObjExpr
  /-- Structural dependent-pair/record type. `none` means a nondependent product. -/
  | sigma : Option Name → ObjExpr → ObjExpr → ObjExpr
  /-- Structural pair constructor for a dependent-pair/record type. -/
  | pair : ObjExpr → ObjExpr → ObjExpr
  /-- First projection from a structural dependent-pair/record value. -/
  | fst : ObjExpr → ObjExpr
  /-- Second projection from a structural dependent-pair/record value. -/
  | snd : ObjExpr → ObjExpr
  /-- Lambda with one or more untyped binders. Types are supplied by checking against an arrow. -/
  | lam : Array Name → ObjExpr → ObjExpr
  /-- Object-level judgmental equality expression, used in `eq` declarations and, for now,
  as syntax inside motives/types. This is not an internal equality type. -/
  | jeq : ObjExpr → ObjExpr → ObjExpr
  deriving Inhabited, Repr, BEq

namespace ObjExpr

/-- User-facing rendering of names, ignoring macro scopes. -/
def userNameString (n : Name) : String :=
  toString n.eraseMacroScopes

/-- Render a high-level object expression. -/
partial def toString : ObjExpr → String
  | .ident n => userNameString n
  | .sort => "Type"
  | .univ .zero => "Type"
  | .univ u => s!"Type {u}"
  | .app f a => s!"{toString f} {atomString a}"
  | .arrow none a b => s!"{atomString a} ⇒ {toString b}"
  | .arrow (some x) a b => s!"({userNameString x} : {toString a}) ⇒ {toString b}"
  | .funArrow none a b => s!"{atomString a} → {toString b}"
  | .funArrow (some x) a b => s!"({userNameString x} : {toString a}) → {toString b}"
  | .sigma none a b => s!"{atomString a} × {toString b}"
  | .sigma (some x) a b => s!"Σ {userNameString x} : {toString a}, {toString b}"
  | .pair a b => s!"⟨{toString a}, {toString b}⟩"
  | .fst e => s!"Sigma.fst {atomString e}"
  | .snd e => s!"Sigma.snd {atomString e}"
  | .lam xs body =>
      s!"fun {String.intercalate " " (xs.toList.map userNameString)} => {toString body}"
  | .jeq lhs rhs => s!"{toString lhs} ≡ {toString rhs}"
where
  /-- Render an expression atom, adding parentheses around compound expressions. -/
  atomString : ObjExpr → String
    | .ident n => userNameString n
    | .sort => "Type"
    | .univ .zero => "Type"
    | .univ u => s!"Type {u}"
    | e => s!"({toString e})"

instance : ToString ObjExpr := ⟨toString⟩

/-- Collect universe parameter names occurring in an object expression. -/
partial def levelParams : ObjExpr → Array Name
  | .ident _ | .sort => #[]
  | .univ u => u.params
  | .app f a => levelParams f ++ levelParams a
  | .arrow _ A B | .funArrow _ A B | .sigma _ A B => levelParams A ++ levelParams B
  | .pair a b => levelParams a ++ levelParams b
  | .fst e | .snd e => levelParams e
  | .lam _ body => levelParams body
  | .jeq lhs rhs => levelParams lhs ++ levelParams rhs

end ObjExpr

/-- Structural Sigma projection names recognized by the object-expression frontend. -/
inductive StructuralSigmaProjection where
  /-- First projection from a structural Sigma/package value. -/
  | fst
  /-- Second projection from a structural Sigma/package value. -/
  | snd
  deriving Inhabited, Repr, BEq

/-- Qualified name for the first structural Sigma projection in object syntax. -/
meta def structuralSigmaFstName : Name := `Sigma.fst

/-- Qualified name for the second structural Sigma projection in object syntax. -/
meta def structuralSigmaSndName : Name := `Sigma.snd

/-- Legacy identifier spelling for the first structural Sigma projection. -/
meta def legacyStructuralSigmaFstName : Name := `π₁

/-- Legacy identifier spelling for the second structural Sigma projection. -/
meta def legacyStructuralSigmaSndName : Name := `π₂

/-- Recognize structural Sigma projection identifiers. -/
meta def structuralSigmaProjectionName? (n : Name) : Option StructuralSigmaProjection :=
  let n := n.eraseMacroScopes
  if n == structuralSigmaFstName || n == legacyStructuralSigmaFstName then some .fst
  else if n == structuralSigmaSndName || n == legacyStructuralSigmaSndName then some .snd
  else none

/-- Object-expression universe/type expression for a normalized level. -/
def objExprTypeOfLevel (u : LevelExpr) : ObjExpr :=
  if LevelExpr.equal u .zero then .sort else .univ (LevelExpr.normalize u)

/-- Internal marker used only while elaborating named implicit arguments like `{x := t}`. -/
def implicitNamedArgHeadName : Name := `__implicitArg

/-- Return whether an object expression is the internal named-implicit-argument marker. -/
def isImplicitNamedArgHead : ObjExpr → Bool
  | .ident n => n.eraseMacroScopes == implicitNamedArgHeadName
  | _ => false

/-- Encode a source named implicit argument. This marker must be consumed before checking. -/
def mkImplicitNamedArg (name : Name) (value : ObjExpr) : ObjExpr :=
  .app (.app (.ident implicitNamedArgHeadName) (.ident name)) value

/-- Decode a source named implicit argument marker. -/
def implicitNamedArg? (e : ObjExpr) : Option (Name × ObjExpr) :=
  match e with
  | .app (.app h (.ident n)) value =>
      if isImplicitNamedArgHead h then some (n.eraseMacroScopes, value) else none
  | _ => none

/-- Surface visibility for a declaration-local object binder. -/
inductive BinderVisibility where
  /-- Explicit binder, supplied positionally by ordinary applications. -/
  | explicit
  /-- Ordinary implicit binder, normally omitted and reconstructed by elaboration. -/
  | implicit
  deriving Inhabited, Repr, BEq

namespace BinderVisibility

/-- Render a binder visibility for diagnostics. -/
def label : BinderVisibility → String
  | .explicit => "explicit"
  | .implicit => "implicit"

end BinderVisibility

/-- A binder in a user-facing type-theory declaration. -/
structure HLBinding where
  /-- Binder name. -/
  name : Name
  /-- Object type of the binder. -/
  typeExpr : ObjExpr
  /-- Surface visibility of the binder. -/
  visibility : BinderVisibility := .explicit
  deriving Inhabited, Repr, BEq

/-- User-declared role metadata for a primitive or derived object-theory constant.

Roles are intentionally non-semantic: they are ergonomic metadata for theory-local
frontends, pretty-printers, and model-interface diagnostics. The checker does not trust
or interpret them. -/
structure ObjectRole where
  /-- Name of the object constant or macro being described. -/
  name : Name
  /-- Role tag, e.g. `typeFormer`, `intro`, `elim`, `computationRule`. -/
  kind : Name
  /-- Optional related object constant, e.g. an intro rule's type former. -/
  related : Option Name := none
  /-- Optional human-readable note. -/
  doc : String := ""
  deriving Inhabited, Repr, BEq

/-- Theory-local surface macro.

An object macro is a user-space ergonomic abbreviation. It is expanded before checking
and has no trusted semantics of its own. Parameters are object-expression variables in
`template`; applications headed by `name` with the right number of arguments are replaced
by the template with parameters substituted. -/
structure ObjectMacro where
  /-- Macro head name as used in object expressions. -/
  name : Name
  /-- Positional object-expression parameters. -/
  params : Array Name := #[]
  /-- Expansion template. -/
  template : ObjExpr
  /-- Optional human-readable note. -/
  doc : String := ""
  deriving Inhabited, Repr, BEq

/-- One token in a user-declared object notation pattern. -/
inductive ObjectNotationPart where
  /-- A literal parser atom, written as a string in `object_notation`. -/
  | atom (text : String)
  /-- An object-expression hole. -/
  | hole (name : Name)
  deriving Inhabited, Repr, BEq

namespace ObjectNotationPart

/-- User-facing rendering of one object-notation pattern token. -/
meta def sourceString : ObjectNotationPart → String
  | .atom text => s!"\"{text}\""
  | .hole name => toString name.eraseMacroScopes

end ObjectNotationPart

/-- A parse-only notation declaration for object expressions.

The concrete parser rule is global Lean syntax, while this registry entry records the intended
owning theory and expansion template. Elaboration expands the parsed holes into `template` before
LF checking. -/
structure ObjectNotationDecl where
  /-- Theory that owns this notation declaration. -/
  theoryName : Name
  /-- Name of the generated `ttExpr` syntax parser. -/
  syntaxName : Name
  /-- Concrete notation pattern. -/
  parts : Array ObjectNotationPart := #[]
  /-- Hole names, in parser order. -/
  holeNames : Array Name := #[]
  /-- Expansion template, with hole names used as object-expression variables. -/
  template : ObjExpr
  deriving Inhabited, Repr, BEq

namespace ObjectNotationDecl

/-- User-facing rendering of an object-notation pattern. -/
meta def patternString (d : ObjectNotationDecl) : String :=
  String.intercalate " " (d.parts.toList.map ObjectNotationPart.sourceString)

end ObjectNotationDecl

/-- Environment extension storing parse-only object notations by declaration. -/
public meta initialize objectNotationExt : SimplePersistentEnvExtension ObjectNotationDecl
    (Array ObjectNotationDecl) ←
  registerSimplePersistentEnvExtension {
    name := `InternalLean.objectNotationExt
    addEntryFn := fun xs d => xs.push d
    addImportedFn := fun imports => imports.foldl (init := #[]) fun acc xs => acc ++ xs
  }

/-- All currently registered object notations. -/
meta def getObjectNotationDecls (env : Environment) : Array ObjectNotationDecl :=
  objectNotationExt.getState env

/-- Find an object notation by its generated syntax node kind. -/
meta def findObjectNotationDeclBySyntax? (env : Environment) (syntaxName : Name) :
    Option ObjectNotationDecl :=
  (getObjectNotationDecls env).find? fun d => d.syntaxName == syntaxName

/-- Register an object notation expansion entry. The parser rule is installed separately. -/
meta def registerObjectNotationDecl (d : ObjectNotationDecl) : CoreM Unit := do
  modifyEnv fun env => objectNotationExt.addEntry env d

/-- Substitute object-expression notation holes in a template. -/
meta partial def substObjectNotationParams (subst : NameMap ObjExpr) : ObjExpr → ObjExpr
  | .ident n =>
      match subst.find? n.eraseMacroScopes with
      | some e => e
      | none => .ident n
  | .sort => .sort
  | .univ u => .univ u
  | .app f a => .app (substObjectNotationParams subst f) (substObjectNotationParams subst a)
  | .arrow x A B =>
      let A := substObjectNotationParams subst A
      let subst := match x with | some x => subst.erase x.eraseMacroScopes | none => subst
      .arrow x A (substObjectNotationParams subst B)
  | .funArrow x A B =>
      let A := substObjectNotationParams subst A
      let subst := match x with | some x => subst.erase x.eraseMacroScopes | none => subst
      .funArrow x A (substObjectNotationParams subst B)
  | .sigma x A B =>
      let A := substObjectNotationParams subst A
      let subst := match x with | some x => subst.erase x.eraseMacroScopes | none => subst
      .sigma x A (substObjectNotationParams subst B)
  | .pair a b => .pair (substObjectNotationParams subst a) (substObjectNotationParams subst b)
  | .fst e => .fst (substObjectNotationParams subst e)
  | .snd e => .snd (substObjectNotationParams subst e)
  | .lam xs body =>
      let subst := xs.foldl (fun subst x => subst.erase x.eraseMacroScopes) subst
      .lam xs (substObjectNotationParams subst body)
  | .jeq lhs rhs => .jeq (substObjectNotationParams subst lhs) (substObjectNotationParams subst rhs)

/-- Model-interface visibility for a source LF declaration.

Visibility is ergonomic metadata for generated model interfaces/templates. It does not change
LF checking: hidden declarations remain available to the theory and to full/debug interfaces. -/
inductive ModelVisibilityKind where
  /-- Default public model-interface item. -/
  | public_
  /-- Internal helper omitted from public/minimal model interfaces. -/
  | internal
  /-- Compatibility/deprecated item omitted from public/minimal interfaces.
  Retained in full/debug interfaces. -/
  | compat
  deriving Inhabited, Repr, BEq

namespace ModelVisibilityKind

/-- Human-readable visibility label. -/
def label : ModelVisibilityKind → String
  | .public_ => "public"
  | .internal => "internal"
  | .compat => "compatibility"

end ModelVisibilityKind

/-- Visibility metadata for one source LF declaration. -/
structure ModelVisibilityDecl where
  /-- Source declaration being annotated. -/
  declName : Name
  /-- Requested model-interface visibility. -/
  visibility : ModelVisibilityKind := .public_
  deriving Inhabited, Repr, BEq

/-- User-facing grouping marker for generated model interfaces.

A `model_section S` declaration is non-semantic metadata.  It starts a source-order section;
later LF declarations are assigned to that section until another `model_section` marker
appears.  Section metadata is consumed only by generated model-interface templates and
sectioned/bundled interfaces. -/
structure ModelSectionDecl where
  /-- Theory-local section name. -/
  name : Name
  deriving Inhabited, Repr, BEq

/-- Assignment of one LF declaration to a user-facing model section. -/
structure ModelSectionMembershipDecl where
  /-- Section that owns the declaration in generated sectioned interfaces. -/
  sectionName : Name
  /-- Source LF declaration assigned to the section. -/
  declName : Name
  deriving Inhabited, Repr, BEq

/-- Declaration of a user-level syntactic category for future multi-judgment theories.

This is Phase-1 logical-framework metadata: the current dependent-function checker stores
and reports these declarations but does not yet assign them semantics. -/
structure SyntaxSortDecl where
  /-- Syntactic category name. -/
  name : Name
  /-- Optional object-expression parameters indexing the syntactic category. -/
  params : Array HLBinding := #[]
  /-- Result universe for the semantic carrier of this syntax sort in generated models. -/
  resultLevel : LevelExpr := .zero
  deriving Inhabited, Repr, BEq

/-- User-facing abbreviation for a syntax-sort-shaped LF expression.

A `syntax_abbrev` is expanded in later metadata before model obligations are computed, so it
can be used as public notation without becoming an independent model-interface field. -/
structure SyntaxAbbrevDecl where
  /-- Abbreviation name. -/
  name : Name
  /-- Parameters of the abbreviation. -/
  params : Array HLBinding := #[]
  /-- Sort-shaped expansion body. -/
  value : ObjExpr
  deriving Inhabited, Repr, BEq

/-- User-facing derived syntax-family definition.

A checked `syntax_def` is a named type-valued LF definition. An admitted `syntax_def` stores only
its telescope and result universe, so later declarations can mention the family while the package
shape remains explicit `sorry` debt. -/
structure SyntaxDefDecl where
  /-- Definition name. -/
  name : Name
  /-- Parameters of the derived syntax family. -/
  params : Array HLBinding := #[]
  /-- Result universe for the derived family. -/
  resultLevel : LevelExpr := .zero
  /-- Checked source body when present; `none` means `:= sorry`. -/
  value? : Option ObjExpr := none
  deriving Inhabited, Repr, BEq

/-- User-facing abbreviation for a judgment-shaped LF expression.

A `judgment_abbrev` is expanded in later metadata before LF checking and model obligations are
computed, so it can be used as public notation without becoming an independent model-interface
field. -/
structure JudgmentAbbrevDecl where
  /-- Abbreviation name. -/
  name : Name
  /-- Parameters of the abbreviation. -/
  params : Array HLBinding := #[]
  /-- Judgment-shaped expansion body. -/
  value : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Non-semantic role metadata for a user-declared syntactic category. -/
structure SyntaxSortRoleDecl where
  /-- Syntactic category being described. -/
  sortName : Name
  /-- Role tag, e.g. `context`, `type`, `term`, `cube`, `tope`. -/
  kind : Name
  deriving Inhabited, Repr, BEq

/-- A named context zone for future multi-zone judgments such as `Ξ | Φ | Γ`. -/
structure ContextZoneDecl where
  /-- Zone name, e.g. `cube`, `tope`, or `type`. -/
  name : Name
  /-- Syntactic sort whose objects inhabit this zone. -/
  sortName : Name
  /-- Earlier zones this zone may depend on. -/
  dependsOn : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- Declaration of a binder class for scoped multi-zone raw syntax.

A binder class says that binders of this class extend one declared context zone with a
variable whose type/sort is headed by a declared syntax sort. It is still metadata: later
phases should use it to elaborate scoped raw syntax and check substitution. -/
structure BinderClassDecl where
  /-- Binder-class name, e.g. `cube_var` or `type_var`. -/
  name : Name
  /-- Syntax sort of variables introduced by this binder class. -/
  boundSortName : Name
  /-- Context zone extended by this binder class. -/
  zoneName : Name
  /-- Earlier zones this binder may depend on. -/
  dependsOn : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- Declaration of a custom judgment form for future logical-framework rules. -/
structure JudgmentDecl where
  /-- Judgment form name. -/
  name : Name
  /-- Parameters of the judgment form. -/
  params : Array HLBinding := #[]
  deriving Inhabited, Repr, BEq

/-- Non-semantic role metadata for a user-declared judgment form.

Roles let future generic tooling recognize intended judgment classes such as context
wellformedness, type formation, term typing, conversion, or side judgments, without
hard-coding example-specific judgment names. -/
structure JudgmentRoleDecl where
  /-- Judgment form being described. -/
  judgmentName : Name
  /-- Role tag, e.g. `context_wellformedness`, `type_formation`, `term_typing`. -/
  kind : Name
  deriving Inhabited, Repr, BEq

/-- A named derivation premise in a future logical-framework rule. -/
structure RulePremiseDecl where
  /-- Premise name, used for diagnostics and future dependency between premises. -/
  name : Name
  /-- Schematic premise expression, usually headed by a declared judgment form. -/
  judgmentExpr : ObjExpr
  deriving Inhabited, Repr, BEq

/-- A named side condition in a future logical-framework rule. -/
structure RuleSideConditionDecl where
  /-- Side-condition name, used for diagnostics and future certificates. -/
  name : Name
  /-- Declared solver expected to check this side condition. -/
  solver : Name
  /-- Schematic side-condition input/judgment. -/
  input : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Judgmental evidence required for a rule parameter instantiation.

This lets a rule say that a parameter, especially a substitution-shaped one, must carry an
instantiated LF judgment such as `wfSubst Δ Γ σ` in the kernel-facing replay artifact. The
named evidence item is also a rule premise, so high-level rule applications must provide a
checked derivation of the same judgment. -/
structure RuleParamEvidenceDecl where
  /-- Evidence premise name, with the same role as an ordinary premise name. -/
  name : Name
  /-- Rule parameter whose instantiation carries this evidence. -/
  paramName : Name
  /-- Schematic evidence judgment. -/
  judgmentExpr : ObjExpr
  deriving Inhabited, Repr, BEq

/-- A skeletal rule declaration for future custom-judgment checking.

For now, all expressions are represented as object expressions, usually applications
headed by declared judgment forms. Premises and side conditions are stored as metadata;
the current dependent-function checker deliberately does not interpret them. -/
structure RuleDecl where
  /-- Rule name. -/
  name : Name
  /-- Rule metavariable/object-parameter telescope. -/
  params : Array HLBinding := #[]
  /-- Derivation premises. -/
  premises : Array RulePremiseDecl := #[]
  /-- Side conditions with declared solver names. -/
  sideConditions : Array RuleSideConditionDecl := #[]
  /-- Optional parameter evidence obligations. -/
  paramEvidences : Array RuleParamEvidenceDecl := #[]
  /-- Schematic conclusion, usually headed by a custom judgment. -/
  conclusionExpr : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Non-semantic role/class metadata for a user-declared rule.

Rule roles let future tooling distinguish formation, introduction, elimination,
computation, structural, and admissible-theorem rules without hard-coding rule names. -/
structure RuleRoleDecl where
  /-- Rule being described. -/
  ruleName : Name
  /-- Role tag, e.g. `formation`, `introduction`, `elimination`, `computation`. -/
  kind : Name
  deriving Inhabited, Repr, BEq

/-- Metadata identifying a judgment whose evidence may drive proof-producing rewrites.

The declaration is descriptive: it names the relation head and the parameters that should be
read as the oriented rewrite endpoints. A later tactic step must still use a declared
transport principle and checked LF replay before changing a goal non-definitionally. -/
structure LFRewriteRelationDecl where
  /-- Relation or judgment head that carries rewrite evidence. -/
  relationName : Name
  /-- Parameter of the relation representing the left/source endpoint. -/
  lhsParam : Name
  /-- Parameter of the relation representing the right/target endpoint. -/
  rhsParam : Name
  deriving Inhabited, Repr, BEq

/-- Metadata marking a rule or theorem as symmetry for a rewrite relation.

The declaration names an LF declaration that turns evidence for `R lhs rhs` into evidence
for `R rhs lhs`. Tactics use it only when reverse rewriting needs relation evidence in
the opposite orientation. -/
structure LFRewriteSymmetryDecl where
  /-- Rule or theorem implementing symmetry. -/
  symmetryName : Name
  /-- Rewrite relation produced in the opposite orientation. -/
  relationName : Name
  /-- Premise/binder name carrying the forward relation evidence. -/
  evidenceParam : Name
  deriving Inhabited, Repr, BEq

/-- Metadata marking a rule or theorem as congruence for a rewrite relation.

The declaration names an LF declaration that lifts evidence for `R lhs rhs` to evidence
for `R (H ... lhs ...) (H ... rhs ...)` at one argument position of `H`. -/
structure LFRewriteCongruenceDecl where
  /-- Rule or theorem implementing congruence. -/
  congruenceName : Name
  /-- Rewrite relation preserved by the congruence principle. -/
  relationName : Name
  /-- Head whose argument is rewritten by the congruence principle. -/
  targetHead : Name
  /-- Zero-based argument position rewritten under `targetHead`. -/
  argumentIndex : Nat
  /-- Premise/binder name carrying relation evidence. -/
  evidenceParam : Name
  deriving Inhabited, Repr, BEq

/-- Metadata marking a rule as a transport principle for a rewrite relation.

The rule must have a premise carrying evidence for the relation and a premise carrying the
source proof/object to transport. The rule conclusion is treated as the transported target
by future tactic synthesis. This metadata is not trusted as a proof by itself. -/
structure LFTransportRuleDecl where
  /-- Transport rule being described. -/
  ruleName : Name
  /-- Rewrite relation consumed by the transport rule. -/
  relationName : Name
  /-- Premise name carrying relation evidence. -/
  evidencePremise : Name
  /-- Premise name carrying the source proof/object to transport. -/
  sourcePremise : Name
  deriving Inhabited, Repr, BEq

/-- Optional metadata describing which argument position a transport rule rewrites.

This lets tactic search distinguish transport principles for different positions of the same
judgment or type former. The checker validates the referenced rule shape, but the transport
rule itself remains the trusted LF evidence. -/
structure LFTransportPositionDecl where
  /-- Transport rule being described. -/
  ruleName : Name
  /-- Head whose argument is rewritten by the transport rule conclusion/source premise. -/
  targetHead : Name
  /-- Zero-based argument position rewritten under `targetHead`. -/
  argumentIndex : Nat
  deriving Inhabited, Repr, BEq

/-- Metadata naming a theory-local side-condition solver.

The executable hook/certificate API is deliberately not implemented yet; this declaration
reserves the name and records the intended interface point. -/
structure SideConditionSolverDecl where
  /-- Solver name. -/
  name : Name
  deriving Inhabited, Repr, BEq

/-- Metadata naming a theory-local conversion plugin.

The default trust kind is an opaque assumption marker.  A declaration records the boundary;
it does not by itself register executable conversion semantics or supported certificate
steps. -/
structure ConversionPluginDecl where
  /-- Plugin name. -/
  name : Name
  /-- Trust/provenance class for leaves justified by this plugin. -/
  trust : ConversionPluginTrustKind := .opaqueAssumption
  /-- Supported generic certificate step classes. Empty means this is metadata only. -/
  supportedSteps : Array ConversionStepKind := #[]
  deriving Inhabited, Repr, BEq

/-- Metadata naming an opaque logical-framework placeholder symbol.

These symbols are not interpreted by the current checker. They let metadata-only rules
mention schematic constructors, boundary predicates, and other future LF constants while
still allowing unknown-name validation to catch accidental free variables. -/
structure LFOpaqueConstDecl where
  /-- Opaque placeholder name. -/
  name : Name
  /-- Optional expected number of object-expression arguments when used as an application head. -/
  arity? : Option Nat := none
  /-- Optional typed parameter telescope for shallow LF inference/checking. -/
  params : Array HLBinding := #[]
  /-- Optional result type for shallow LF inference/checking. -/
  typeExpr? : Option ObjExpr := none
  deriving Inhabited, Repr, BEq

/-- Staged sorted LF/object definition.

Staged sorted LF/object definition. For now it is checked as a resolved LF artifact,
not as a certified custom-judgment derivation. -/
structure LFObjectDefDecl where
  /-- Definition name. -/
  name : Name
  /-- Declared result sort/type of the definition. -/
  typeExpr : ObjExpr
  /-- Defining LF/object expression. -/
  value : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Staged custom-judgment theorem.

Staged custom-judgment theorem. The current checker validates names, arities, and the
judgment head, and replays a small checked proof shape. -/
structure LFJudgmentTheoremDecl where
  /-- Theorem/proof name. -/
  name : Name
  /-- Local LF parameters and theorem assumptions available in the statement/proof. -/
  binders : Array HLBinding := #[]
  /-- Declared custom-judgment statement. -/
  judgmentExpr : ObjExpr
  /-- Proof/certificate expression. -/
  proof : ObjExpr
  deriving Inhabited, Repr, BEq

/-- Class of a resolved LF metadata expression head. -/
inductive CheckedLFHeadKind where
  /-- A locally bound LF metavariable/parameter. -/
  | local
  /-- A declared syntax-sort head. -/
  | syntaxSort
  /-- A derived type-valued syntax definition head. -/
  | syntaxDef
  /-- A staged sorted LF/object definition head. -/
  | lfDefinition
  /-- A staged custom-judgment theorem/proof head. -/
  | lfTheorem
  /-- A declared LF rule schema, usable as a shallow theorem proof head. -/
  | lfRule
  /-- A declared judgment-form head. -/
  | judgment
  /-- A primitive object-theory constant. -/
  | primitive
  /-- A checked object definition. -/
  | definition
  /-- A checked internal theorem/proof constant. -/
  | theorem
  /-- An opaque LF placeholder declared by `lf_opaque`. -/
  | opaque
  deriving Inhabited, Repr, BEq

/-- Resolved head information for an LF metadata expression. -/
structure CheckedLFHead where
  /-- Head name, with macro scopes erased. -/
  name : Name
  /-- Resolved head class. -/
  kind : CheckedLFHeadKind
  /-- Expected arity when this head has a declared arity. -/
  arity? : Option Nat := none
  /-- Actual number of object-expression arguments at this occurrence. -/
  actualArity : Nat := 0
  deriving Inhabited, Repr, BEq

/-- Recursively resolved LF metadata expression.

This keeps the original `ObjExpr` payload available in surrounding records, but also
records local/global head resolution throughout the expression tree. It is still a
syntactic artifact, not a typed LF derivation. -/
inductive CheckedLFExpr where
  /-- Resolved identifier occurrence. For application heads, `actualArity` records the
  full application spine size at the occurrence. -/
  | ident (head : CheckedLFHead) : CheckedLFExpr
  /-- Object universe/type expression. -/
  | sort : CheckedLFExpr
  /-- Explicit object universe level. -/
  | univ (level : LevelExpr) : CheckedLFExpr
  /-- Application. -/
  | app (fn arg : CheckedLFExpr) : CheckedLFExpr
  /-- Structural/function-family arrow. -/
  | arrow (binderName : Option Name) (domain codomain : CheckedLFExpr) : CheckedLFExpr
  /-- Structural dependent-pair/record type. -/
  | sigma (binderName : Option Name) (domain codomain : CheckedLFExpr) : CheckedLFExpr
  /-- Structural pair constructor. -/
  | pair (fst snd : CheckedLFExpr) : CheckedLFExpr
  /-- First projection from a structural dependent pair. -/
  | fst (value : CheckedLFExpr) : CheckedLFExpr
  /-- Second projection from a structural dependent pair. -/
  | snd (value : CheckedLFExpr) : CheckedLFExpr
  /-- Lambda expression. -/
  | lam (binders : Array Name) (body : CheckedLFExpr) : CheckedLFExpr
  /-- Object-level judgmental equality expression. -/
  | jeq (lhs rhs : CheckedLFExpr) : CheckedLFExpr
  deriving Inhabited, Repr, BEq

/-- A resolved LF metadata telescope binder. -/
structure CheckedLFBinding where
  /-- Binder name, with macro scopes erased. -/
  name : Name
  /-- Source binder type expression. -/
  typeExpr : ObjExpr
  /-- Surface visibility of the binder. -/
  visibility : BinderVisibility := .explicit
  /-- Resolved type expression. -/
  checkedTypeExpr : CheckedLFExpr := default
  /-- Resolved head of `typeExpr`, when it has an identifier head. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- Checked LF universe/type expression for a normalized level. -/
def checkedLFTypeOfLevel (u : LevelExpr) : CheckedLFExpr :=
  if LevelExpr.equal u .zero then .sort else .univ (LevelExpr.normalize u)

/-- A checked LF parameter-evidence artifact. -/
structure CheckedLFRuleParamEvidence where
  /-- Evidence premise name, with macro scopes erased. -/
  name : Name
  /-- Parameter name, with macro scopes erased. -/
  paramName : Name
  /-- Source evidence expression. -/
  judgmentExpr : ObjExpr
  /-- Recursively resolved evidence expression. -/
  checkedJudgmentExpr : CheckedLFExpr := default
  /-- Resolved judgment head of the evidence. -/
  head : CheckedLFHead
  deriving Inhabited, Repr, BEq

/-- A checked LF rule premise artifact. -/
structure CheckedLFRulePremise where
  /-- Premise name, with macro scopes erased. -/
  name : Name
  /-- Source premise evidence-type expression. -/
  judgmentExpr : ObjExpr
  /-- Recursively resolved premise evidence-type expression. -/
  checkedJudgmentExpr : CheckedLFExpr := default
  /-- Resolved head of the premise type, when it has one. Direct judgment heads lower to kernel
  rule premises; other checked evidence types lower as typed scoped-instantiation entries. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

namespace CheckedLFRulePremise

/-- Whether this premise is a direct judgment premise rather than a higher-order evidence value. -/
def isDirectJudgment (p : CheckedLFRulePremise) : Bool :=
  match p.head? with
  | some h => h.kind == .judgment
  | none => false

end CheckedLFRulePremise

/-- A checked LF side-condition artifact. -/
structure CheckedLFRuleSideCondition where
  /-- Side-condition name, with macro scopes erased. -/
  name : Name
  /-- Declared solver name, with macro scopes erased. -/
  solver : Name
  /-- Source side-condition input. -/
  input : ObjExpr
  /-- Recursively resolved side-condition input. -/
  checkedInput : CheckedLFExpr := default
  /-- Resolved head of the side-condition input, when it has an identifier head. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- A checked LF syntax-sort declaration artifact. -/
structure CheckedLFSyntaxSort where
  /-- Sort name, with macro scopes erased. -/
  name : Name
  /-- Checked parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Declared arity. -/
  arity : Nat := 0
  /-- Result universe for the semantic carrier of this syntax sort in generated models. -/
  resultLevel : LevelExpr := .zero
  deriving Inhabited, Repr, BEq

/-- A checked syntax-sort-shaped abbreviation artifact. -/
structure CheckedLFSyntaxAbbrev where
  /-- Abbreviation name, with macro scopes erased. -/
  name : Name
  /-- Checked parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Expanded source body. -/
  value : ObjExpr
  /-- Resolved expanded body. -/
  checkedValue : CheckedLFExpr := default
  /-- Resolved body head, when available. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- A checked derived syntax-family definition artifact. -/
structure CheckedLFSyntaxDef where
  /-- Definition name, with macro scopes erased. -/
  name : Name
  /-- Checked parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Result universe for the derived family. -/
  resultLevel : LevelExpr := .zero
  /-- Expanded source body when the definition is checked; `none` means admitted. -/
  value? : Option ObjExpr := none
  /-- Resolved expanded body when present. -/
  checkedValue? : Option CheckedLFExpr := none
  /-- Resolved body head, when available. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- A checked judgment-shaped abbreviation artifact. -/
structure CheckedLFJudgmentAbbrev where
  /-- Abbreviation name, with macro scopes erased. -/
  name : Name
  /-- Checked parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Expanded source body. -/
  value : ObjExpr
  /-- Resolved expanded body. -/
  checkedValue : CheckedLFExpr := default
  /-- Resolved body head. -/
  head : CheckedLFHead
  deriving Inhabited, Repr, BEq

/-- A checked LF context-zone declaration artifact. -/
structure CheckedLFContextZone where
  /-- Zone name, with macro scopes erased. -/
  name : Name
  /-- Syntax sort whose objects inhabit the zone. -/
  sortName : Name
  /-- Earlier zones this zone may depend on. -/
  dependsOn : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- A checked LF binder-class declaration artifact. -/
structure CheckedLFBinderClass where
  /-- Binder-class name, with macro scopes erased. -/
  name : Name
  /-- Syntax sort of variables introduced by this binder class. -/
  boundSortName : Name
  /-- Context zone extended by this binder class. -/
  zoneName : Name
  /-- Earlier zones this binder may refer to. -/
  dependsOn : Array Name := #[]
  deriving Inhabited, Repr, BEq

/-- A checked LF judgment-form declaration artifact. -/
structure CheckedLFJudgment where
  /-- Judgment name, with macro scopes erased. -/
  name : Name
  /-- Checked parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Declared arity. -/
  arity : Nat := 0
  deriving Inhabited, Repr, BEq

/-- A checked LF opaque-placeholder declaration artifact. -/
structure CheckedLFOpaqueConst where
  /-- Placeholder name, with macro scopes erased. -/
  name : Name
  /-- Declared arity, if specified. -/
  arity? : Option Nat := none
  /-- Checked typed parameter telescope, when the placeholder is typed. -/
  params : Array CheckedLFBinding := #[]
  /-- Source result type, when the placeholder is typed. -/
  typeExpr? : Option ObjExpr := none
  /-- Resolved result type, when the placeholder is typed. -/
  checkedTypeExpr? : Option CheckedLFExpr := none
  /-- Resolved result type head, when available. -/
  typeHead? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- Classification of a checked side-condition solver hook.

Most declared solvers are still opaque handles. Phase 3 adds a tiny built-in executable
hook used for tests and for exercising the certificate pipeline. -/
inductive CheckedLFSideConditionHookKind where
  /-- Declared but not executable by the current direct-LF checker. -/
  | opaque
  /-- Built-in hook that accepts a syntactically well-formed LF side-condition input. -/
  | builtinTrivial
  deriving Inhabited, Repr, BEq

namespace CheckedLFSideConditionHookKind

/-- User-facing label for a side-condition hook kind. -/
def label : CheckedLFSideConditionHookKind → String
  | .opaque => "opaque"
  | .builtinTrivial => "builtin_trivial"

end CheckedLFSideConditionHookKind

/-- A checked side-condition solver declaration artifact.

Phase 3 gives solver handles an explicit hook kind. Opaque solvers are stable names for
future trusted/checkable services; built-in solvers can produce checked certificates now. -/
structure CheckedLFSideConditionSolver where
  /-- Solver name, with macro scopes erased. -/
  name : Name
  /-- Hook implementation kind available to the direct-LF checker. -/
  hookKind : CheckedLFSideConditionHookKind := .opaque
  deriving Inhabited, Repr, BEq

/-- Status/kind of a checked LF side-condition certificate. -/
inductive CheckedLFSideConditionCertificateKind where
  /-- Certificate produced by the Phase-3 built-in trivial hook. -/
  | builtinTrivial
  deriving Inhabited, Repr, BEq

namespace CheckedLFSideConditionCertificateKind

/-- User-facing label for a side-condition certificate kind. -/
def label : CheckedLFSideConditionCertificateKind → String
  | .builtinTrivial => "builtin_trivial"

end CheckedLFSideConditionCertificateKind

/-- A checked certificate produced by an executable side-condition hook.

This records the slot, solver, input, resolved input, and hook kind that accepted the obligation.
Nontrivial solvers should provide proof-carrying LF/Lean certificates. -/
structure CheckedLFSideConditionCertificate where
  /-- Stable side-condition slot name. -/
  name : Name
  /-- Solver that produced the certificate. -/
  solver : Name
  /-- Source side-condition input. -/
  input : ObjExpr
  /-- Resolved side-condition input. -/
  checkedInput : CheckedLFExpr := default
  /-- Resolved input head, when available. -/
  inputHead? : Option CheckedLFHead := none
  /-- Certificate kind. -/
  kind : CheckedLFSideConditionCertificateKind := .builtinTrivial
  /-- Stable diagnostic/provenance name for the certificate artifact. -/
  certificateName : Name := .anonymous
  /-- Human-readable diagnostic emitted by the hook. -/
  diagnostic : String := ""
  deriving Inhabited, Repr, BEq

/-- A checked conversion-plugin declaration artifact.

Checked plugin handles classify the trust boundary used by future conversion-certificate
leaves. They remain inert unless a kernel-facing schema explicitly lists supported generic
step classes. -/
structure CheckedLFConversionPlugin where
  /-- Plugin name, with macro scopes erased. -/
  name : Name
  /-- Trust/provenance class for leaves justified by this plugin. -/
  trust : ConversionPluginTrustKind := .opaqueAssumption
  /-- Supported generic certificate step classes. Empty means this is metadata only. -/
  supportedSteps : Array ConversionStepKind := #[]
  deriving Inhabited, Repr, BEq

/-- Checked Phase-5 tope/cofibration formula artifact. -/
structure CheckedLFTopeFormula where
  /-- Formula name, with macro scopes erased. -/
  name : Name
  /-- Source formula expression. -/
  formula : ObjExpr
  /-- Recursively resolved formula expression. -/
  checkedFormula : CheckedLFExpr := default
  /-- Resolved formula head, when available. -/
  head? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- Checked staged sorted LF/object definition artifact. -/
structure CheckedLFObjectDef where
  /-- Definition name. -/
  name : Name
  /-- Source result sort/type. -/
  typeExpr : ObjExpr
  /-- Resolved result sort/type. -/
  checkedTypeExpr : CheckedLFExpr := default
  /-- Resolved type head, when available. -/
  typeHead? : Option CheckedLFHead := none
  /-- Source definition body. -/
  value : ObjExpr
  /-- Resolved definition body. -/
  checkedValue : CheckedLFExpr := default
  /-- Resolved body head, when available. -/
  valueHead? : Option CheckedLFHead := none
  deriving Inhabited, Repr, BEq

/-- A shallow checked LF derivation replay artifact.

This records the syntactic proof tree accepted for a custom judgment. It is still not a
trusted kernel derivation: rule parameters are substituted syntactically, theorem
references are checked by statement matching, and side-condition certificates are named
staging artifacts. -/
inductive CheckedLFDerivation where
  /-- A reference to a local theorem assumption whose statement matches the expected premise. -/
  | localAssumption (name : Name) (statement : ObjExpr) : CheckedLFDerivation
  /-- A reference to a previously declared `judgment_theorem` whose statement matches the
  expected premise. -/
  | theoremRef (name : Name) (statement : ObjExpr) (args : Array ObjExpr)
      (premises : Array CheckedLFDerivation) : CheckedLFDerivation
  /-- A rule application with explicit parameter arguments, recursively checked premise
  derivations, and matched side-condition certificate names. -/
  | ruleApp (ruleName : Name) (statement : ObjExpr) (ruleArgs : Array ObjExpr)
      (premises : Array CheckedLFDerivation) (sideConditionCertificateNames : Array Name) :
      CheckedLFDerivation
  deriving Inhabited, Repr, BEq

/-- Checked staged custom-judgment theorem artifact. -/
structure CheckedLFJudgmentTheorem where
  /-- Theorem/proof name. -/
  name : Name
  /-- Checked local LF parameters and theorem assumptions available in the statement/proof. -/
  binders : Array CheckedLFBinding := #[]
  /-- Source custom-judgment statement. -/
  judgmentExpr : ObjExpr
  /-- Resolved custom-judgment statement. -/
  checkedJudgmentExpr : CheckedLFExpr := default
  /-- Resolved judgment head. -/
  judgmentHead : CheckedLFHead
  /-- Source proof/certificate expression. -/
  proof : ObjExpr
  /-- Resolved proof/certificate expression. -/
  checkedProof : CheckedLFExpr := default
  /-- Resolved proof head, when available. -/
  proofHead? : Option CheckedLFHead := none
  /-- Rule used as proof head when the proof is a shallow checked rule application. -/
  proofRule? : Option Name := none
  /-- Explicit rule metavariable arguments supplied by the proof expression. -/
  proofRuleArgs : Array ObjExpr := #[]
  /-- Premise theorem names consumed by a shallow checked rule application. -/
  premiseTheorems : Array Name := #[]
  /-- Side-condition certificate names matched from the applied rule schema. -/
  sideConditionCertificateNames : Array Name := #[]
  /-- Shallow checked proof replay tree, when the proof uses checked rule/theorem-reference
  syntax rather than an opaque placeholder. -/
  derivation? : Option CheckedLFDerivation := none
  /-- Structural-kernel replay artifact lowered directly from the checked LF derivation. -/
  structuralKernelDerivation? : Option Kernel.KernelLFDerivation := none
  /-- Checked structural-kernel replay artifact accepted during signature registration. -/
  checkedStructuralKernelDerivation? : Option Kernel.CheckedKernelLFDerivation := none
  deriving Inhabited, Repr, BEq

namespace CheckedLFJudgmentTheorem

/-- Whether this theorem has a checked replay artifact at the current kernel boundary. -/
def hasCheckedKernelReplay (t : CheckedLFJudgmentTheorem) : Bool :=
  t.checkedStructuralKernelDerivation?.isSome

end CheckedLFJudgmentTheorem

/-- A checked LF rule metadata artifact.

This is still not a semantic derivation. It records the result of Phase-1 syntactic
validation: telescope locals, resolved judgment heads and arities, side-condition solver
names, and opaque-placeholder arities. -/
structure CheckedLFRule where
  /-- Rule name, with macro scopes erased. -/
  name : Name
  /-- Checked rule-parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Checked premise metadata. -/
  premises : Array CheckedLFRulePremise := #[]
  /-- Checked parameter-evidence metadata. -/
  paramEvidences : Array CheckedLFRuleParamEvidence := #[]
  /-- Checked side-condition metadata. -/
  sideConditions : Array CheckedLFRuleSideCondition := #[]
  /-- Source conclusion expression. -/
  conclusionExpr : ObjExpr
  /-- Recursively resolved conclusion expression. -/
  checkedConclusionExpr : CheckedLFExpr := default
  /-- Resolved judgment head of the conclusion. -/
  conclusionHead : CheckedLFHead
  deriving Inhabited, Repr, BEq

/-- A Phase-2 typed LF local variable schema.

This records the checked telescope entry together with the syntax-sort head of its type
when the binder is sort-shaped. It is still shallow: dependencies and constructor
applications are preserved syntactically rather than elaborated into LF derivations. -/
structure CheckedLFTypedLocal where
  /-- Local metavariable name, with macro scopes erased. -/
  name : Name
  /-- Source type expression of the local metavariable. -/
  typeExpr : ObjExpr
  /-- Recursively resolved type expression. -/
  checkedTypeExpr : CheckedLFExpr := default
  /-- Syntax-sort head of the local type, when known. -/
  sortHead? : Option CheckedLFHead := none
  /-- Context zone inferred from the local type's syntax sort, when unique. -/
  zoneName? : Option Name := none
  /-- Binder class inferred from the local type's syntax sort and zone, when unique. -/
  binderClass? : Option Name := none
  /-- Optional evidence obligation associated with this local. -/
  evidence? : Option CheckedLFRuleParamEvidence := none
  deriving Inhabited, Repr, BEq

/-- A checked local entry in a multi-zone LF context. -/
structure CheckedLFZoneLocal where
  /-- Local name. -/
  name : Name
  /-- Zone containing the local. -/
  zoneName : Name
  /-- Binder class that introduces this local, when known. -/
  binderClass? : Option Name := none
  /-- Source local type expression. -/
  typeExpr : ObjExpr
  /-- Resolved local type expression. -/
  checkedTypeExpr : CheckedLFExpr := default
  deriving Inhabited, Repr, BEq

/-- A checked multi-zone local context extracted from a rule telescope. -/
structure CheckedLFMultiContext where
  /-- Zone-local entries in source order. -/
  locals : Array CheckedLFZoneLocal := #[]
  deriving Inhabited, Repr, BEq

/-- A Phase-2 LF premise schema extracted from checked rule metadata. -/
structure CheckedLFPremiseSchema where
  /-- Premise name, with macro scopes erased. -/
  name : Name
  /-- Head of this premise type, when it has one. -/
  head? : Option CheckedLFHead := none
  /-- Resolved premise evidence-type expression. -/
  checkedJudgmentExpr : CheckedLFExpr := default
  deriving Inhabited, Repr, BEq

namespace CheckedLFPremiseSchema

/-- Whether this premise schema is a direct judgment premise. -/
def isDirectJudgment (p : CheckedLFPremiseSchema) : Bool :=
  match p.head? with
  | some h => h.kind == .judgment
  | none => false

end CheckedLFPremiseSchema

/-- A Phase-2/3 slot for a side-condition certificate.

Phase 2 gave each side condition a stable checked slot keyed by solver and input head.
Phase 3 optionally attaches a checked certificate when the solver name resolves to an
executable hook. -/
structure CheckedLFSideConditionSlot where
  /-- Side-condition name, with macro scopes erased. -/
  name : Name
  /-- Checked side-condition solver name. -/
  solver : Name
  /-- Resolved side-condition input. -/
  checkedInput : CheckedLFExpr := default
  /-- Resolved input head, when available. -/
  inputHead? : Option CheckedLFHead := none
  /-- Checked certificate produced by an executable hook, if one is available. -/
  certificate? : Option CheckedLFSideConditionCertificate := none
  deriving Inhabited, Repr, BEq

/-- A Phase-2 rule schema derived from checked LF metadata.

This is the first stable low-level LF rule artifact: it has a metavariable context,
premise schemas, certificate slots for side conditions, and a checked conclusion. It is
not itself a certified derivation; replay lowers it through `InternalLean.Basic`. -/
structure CheckedLFRuleSchema where
  /-- Rule name, with macro scopes erased. -/
  name : Name
  /-- Typed metavariable/telescope context. -/
  metavariables : Array CheckedLFTypedLocal := #[]
  /-- Multi-zone context projection extracted from metavariables. -/
  multiContext : CheckedLFMultiContext := {}
  /-- Judgment-premise schemas. -/
  premises : Array CheckedLFPremiseSchema := #[]
  /-- Side-condition certificate slots. -/
  sideConditionSlots : Array CheckedLFSideConditionSlot := #[]
  /-- Resolved conclusion expression. -/
  checkedConclusionExpr : CheckedLFExpr := default
  /-- Judgment head of the conclusion. -/
  conclusionHead : CheckedLFHead
  deriving Inhabited, Repr, BEq

/-- A Phase-2 checked logical-framework environment.

This groups the checked declaration handles and the derived rule schemas into a
single artifact. Later semantic LF checking should consume this environment rather than
re-reading unchecked `HLSignature` metadata. -/
structure CheckedLFEnvironment where
  /-- Type-theory name owning this LF environment. -/
  theoryName : Name
  /-- Opt-in object-level universe parameters declared by the theory. These are LF metadata,
  not an assumption that object theories have one fixed style of universes. -/
  levelParams : Array Name := #[]
  /-- Checked syntax-sort declarations. -/
  syntaxSorts : Array CheckedLFSyntaxSort := #[]
  /-- Checked syntax-sort-shaped abbreviations. -/
  syntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  /-- Checked derived syntax-family definitions. -/
  syntaxDefs : Array CheckedLFSyntaxDef := #[]
  /-- Checked judgment-shaped abbreviations. -/
  judgmentAbbrevs : Array CheckedLFJudgmentAbbrev := #[]
  /-- Checked syntax-sort role metadata, with names scope-normalized. -/
  syntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  /-- Checked context-zone declarations. -/
  contextZones : Array CheckedLFContextZone := #[]
  /-- Checked binder-class declarations. -/
  binderClasses : Array CheckedLFBinderClass := #[]
  /-- Checked judgment-form declarations. -/
  judgments : Array CheckedLFJudgment := #[]
  /-- Checked judgment role metadata, with names scope-normalized. -/
  judgmentRoles : Array JudgmentRoleDecl := #[]
  /-- Checked opaque LF placeholders. -/
  opaqueConsts : Array CheckedLFOpaqueConst := #[]
  /-- Checked side-condition solver handles. -/
  sideConditionSolvers : Array CheckedLFSideConditionSolver := #[]
  /-- Checked conversion-plugin handles. -/
  conversionPlugins : Array CheckedLFConversionPlugin := #[]
  /-- Source-level checked rule metadata. -/
  rules : Array CheckedLFRule := #[]
  /-- Checked rule role metadata, with names scope-normalized. -/
  ruleRoles : Array RuleRoleDecl := #[]
  /-- Checked rewrite-relation metadata, with names scope-normalized. -/
  rewriteRelations : Array LFRewriteRelationDecl := #[]
  /-- Checked rewrite-symmetry metadata, with names scope-normalized. -/
  rewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  /-- Checked rewrite-congruence metadata, with names scope-normalized. -/
  rewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  /-- Checked transport-rule metadata, with names scope-normalized. -/
  transportRules : Array LFTransportRuleDecl := #[]
  /-- Checked transport-position metadata, with names scope-normalized. -/
  transportPositions : Array LFTransportPositionDecl := #[]
  /-- Derived Phase-2 rule schemas. -/
  ruleSchemas : Array CheckedLFRuleSchema := #[]
  /-- Phase-3 side-condition certificates produced by executable hooks. -/
  sideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  /-- Checked staged sorted LF/object definitions. -/
  objectDefs : Array CheckedLFObjectDef := #[]
  /-- Checked staged custom-judgment theorems. -/
  judgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  deriving Inhabited, Repr, BEq

/-- Checked direct-LF signature artifacts stored after declaration registration. -/
structure CheckedSignature where
  /-- Theory name. -/
  name : Name
  /-- Object-level universe parameters declared for this theory. -/
  levelParams : Array Name := #[]
  /-- Checked syntax-sort declarations. -/
  lfSyntaxSorts : Array CheckedLFSyntaxSort := #[]
  /-- Checked syntax-sort-shaped abbreviations, expanded before model obligation generation. -/
  lfSyntaxAbbrevs : Array CheckedLFSyntaxAbbrev := #[]
  /-- Checked derived syntax-family definitions. -/
  lfSyntaxDefs : Array CheckedLFSyntaxDef := #[]
  /-- Checked judgment-shaped abbreviations, expanded before model obligation generation. -/
  lfJudgmentAbbrevs : Array CheckedLFJudgmentAbbrev := #[]
  /-- Checked syntax-sort role metadata, with names scope-normalized. -/
  lfSyntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  /-- Checked context-zone declarations. -/
  lfContextZones : Array CheckedLFContextZone := #[]
  /-- Checked binder-class declarations. -/
  lfBinderClasses : Array CheckedLFBinderClass := #[]
  /-- Checked judgment-form declarations. -/
  lfJudgments : Array CheckedLFJudgment := #[]
  /-- Checked judgment role metadata, with names scope-normalized. -/
  lfJudgmentRoles : Array JudgmentRoleDecl := #[]
  /-- Checked LF opaque-placeholder declarations. -/
  lfOpaqueConsts : Array CheckedLFOpaqueConst := #[]
  /-- Model-interface visibility annotations. -/
  modelVisibilities : Array ModelVisibilityDecl := #[]
  /-- User-facing generated model-interface section order. -/
  modelSections : Array ModelSectionDecl := #[]
  /-- Source LF declarations assigned to generated model-interface sections. -/
  modelSectionMemberships : Array ModelSectionMembershipDecl := #[]
  /-- Checked side-condition solver declarations. -/
  lfSideConditionSolvers : Array CheckedLFSideConditionSolver := #[]
  /-- Checked conversion-plugin declarations. -/
  lfConversionPlugins : Array CheckedLFConversionPlugin := #[]
  /-- Checked logical-framework rule metadata. -/
  lfRules : Array CheckedLFRule := #[]
  /-- Checked rule role metadata, with names scope-normalized. -/
  lfRuleRoles : Array RuleRoleDecl := #[]
  /-- Checked rewrite-relation metadata, with names scope-normalized. -/
  lfRewriteRelations : Array LFRewriteRelationDecl := #[]
  /-- Checked rewrite-symmetry metadata, with names scope-normalized. -/
  lfRewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  /-- Checked rewrite-congruence metadata, with names scope-normalized. -/
  lfRewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  /-- Checked transport-rule metadata, with names scope-normalized. -/
  lfTransportRules : Array LFTransportRuleDecl := #[]
  /-- Checked transport-position metadata, with names scope-normalized. -/
  lfTransportPositions : Array LFTransportPositionDecl := #[]
  /-- Derived rule schemas. -/
  lfRuleSchemas : Array CheckedLFRuleSchema := #[]
  /-- Checked logical-framework environment. -/
  lfEnvironment : CheckedLFEnvironment := default
  /-- Side-condition certificates produced by executable hooks. -/
  lfSideConditionCertificates : Array CheckedLFSideConditionCertificate := #[]
  /-- Checked staged sorted LF/object definitions. -/
  lfObjectDefs : Array CheckedLFObjectDef := #[]
  /-- Checked staged custom-judgment theorems. -/
  lfJudgmentTheorems : Array CheckedLFJudgmentTheorem := #[]
  deriving Inhabited, Repr, BEq

/-- Add a value to an array unless it is already present. -/
def pushIfMissing [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

/-- Diagnostic class for generic rule-induction metadata. -/
inductive LFJudgmentInductionDiagnosticKind where
  /-- A requested judgment is not present in the checked theory. -/
  | unknownJudgment
  /-- No checked rule concludes in one of the requested judgments. -/
  | noRuleCases
  deriving Inhabited, Repr, BEq

namespace LFJudgmentInductionDiagnosticKind

/-- User-facing label for a rule-induction metadata diagnostic. -/
def label : LFJudgmentInductionDiagnosticKind → String
  | .unknownJudgment => "unknown_judgment"
  | .noRuleCases => "no_rule_cases"

end LFJudgmentInductionDiagnosticKind

/-- Diagnostic emitted while assembling generic rule-induction metadata. -/
structure LFJudgmentInductionDiagnostic where
  /-- Diagnostic class. -/
  kind : LFJudgmentInductionDiagnosticKind
  /-- Judgment affected by this diagnostic, when the diagnostic is judgment-specific. -/
  judgment? : Option Name := none
  /-- Human-readable message. -/
  message : String
  deriving Inhabited, Repr, BEq

/-- Premise entry for one generic rule-induction case. -/
structure LFJudgmentInductionPremise where
  /-- Source premise/evidence name. -/
  name : Name
  /-- Source premise type. -/
  judgmentExpr : ObjExpr
  /-- Resolved premise head, when available. -/
  head? : Option CheckedLFHead := none
  /-- Whether this premise becomes a recursive hypothesis for the covered judgment family. -/
  recursive : Bool := false
  deriving Inhabited, Repr, BEq

/-- One rule case in a generic rule-induction principle. -/
structure LFJudgmentInductionCase where
  /-- Rule whose conclusion supplies this induction case. -/
  ruleName : Name
  /-- Rule parameter telescope. -/
  params : Array CheckedLFBinding := #[]
  /-- Evidence obligations attached to rule parameters. -/
  paramEvidences : Array CheckedLFRuleParamEvidence := #[]
  /-- Rule premises, annotated with recursive-hypothesis eligibility. -/
  premises : Array LFJudgmentInductionPremise := #[]
  /-- Rule side conditions. -/
  sideConditions : Array CheckedLFRuleSideCondition := #[]
  /-- Source rule conclusion. -/
  conclusionExpr : ObjExpr
  /-- Resolved conclusion judgment head. -/
  conclusionHead : CheckedLFHead
  deriving Inhabited, Repr, BEq

namespace LFJudgmentInductionCase

/-- Recursive premises exposed as induction hypotheses in this case. -/
def recursivePremises (c : LFJudgmentInductionCase) : Array LFJudgmentInductionPremise :=
  c.premises.filter (·.recursive)

end LFJudgmentInductionCase

/-- Generic rule-induction metadata for one or more mutually covered judgments. -/
structure LFJudgmentInductionPrinciple where
  /-- Checked type theory owning the principle. -/
  theoryName : Name
  /-- Judgment families covered by this induction principle. -/
  judgmentNames : Array Name := #[]
  /-- Rule cases whose conclusions target the covered judgments. -/
  cases : Array LFJudgmentInductionCase := #[]
  /-- Metadata diagnostics. A nonempty list means the principle is not usable yet. -/
  diagnostics : Array LFJudgmentInductionDiagnostic := #[]
  deriving Inhabited, Repr, BEq

namespace LFJudgmentInductionPrinciple

/-- Total number of recursive premises exposed by the principle. -/
def recursivePremiseCount (p : LFJudgmentInductionPrinciple) : Nat :=
  p.cases.foldl (init := 0) fun n c => n + c.recursivePremises.size

/-- Whether the principle has no blocking diagnostics. -/
def isUsable (p : LFJudgmentInductionPrinciple) : Bool :=
  p.diagnostics.isEmpty

end LFJudgmentInductionPrinciple

namespace CheckedSignature

/-- Construct generic rule-induction metadata for one or more checked judgment families. -/
def judgmentInductionPrinciple (checked : CheckedSignature) (judgmentNames : Array Name) :
    LFJudgmentInductionPrinciple := Id.run do
  let mut targets : Array Name := #[]
  for j in judgmentNames do
    targets := pushIfMissing targets j.eraseMacroScopes
  let hasTarget (n : Name) : Bool :=
    targets.any fun target => target.eraseMacroScopes == n.eraseMacroScopes
  let mut diagnostics : Array LFJudgmentInductionDiagnostic := #[]
  for target in targets do
    unless checked.lfJudgments.any (fun j => j.name.eraseMacroScopes == target) do
      diagnostics := diagnostics.push {
        kind := .unknownJudgment
        judgment? := some target
        message := s!"unknown judgment '{target}' in checked type theory '{checked.name}'" }
  let mut cases : Array LFJudgmentInductionCase := #[]
  for r in checked.lfRules do
    if hasTarget r.conclusionHead.name then
      let premises := r.premises.map fun p =>
        let recursive := match p.head? with
          | some h => h.kind == .judgment && hasTarget h.name
          | none => false
        ({ name := p.name
           judgmentExpr := p.judgmentExpr
           head? := p.head?
           recursive := recursive } : LFJudgmentInductionPremise)
      cases := cases.push {
        ruleName := r.name
        params := r.params
        paramEvidences := r.paramEvidences
        premises := premises
        sideConditions := r.sideConditions
        conclusionExpr := r.conclusionExpr
        conclusionHead := r.conclusionHead }
  if diagnostics.isEmpty && cases.isEmpty then
    diagnostics := diagnostics.push {
      kind := .noRuleCases
      message := s!"no checked rule in type theory '{checked.name}' concludes in covered \
        judgment(s) {String.intercalate ", " (targets.toList.map toString)}" }
  return {
    theoryName := checked.name
    judgmentNames := targets
    cases := cases
    diagnostics := diagnostics }

end CheckedSignature

/-- Rule classes consumed by generic role-driven automation. -/
inductive LFRuleAutomationClass where
  /-- A formation rule constructs a type/sort/classification judgment. -/
  | formation
  /-- An introduction rule constructs canonical inhabitants or witnesses. -/
  | introduction
  /-- An elimination rule consumes inhabitants or witnesses. -/
  | elimination
  /-- A computation rule proves a conversion/equality consequence. -/
  | computation
  /-- A structural rule handles reflexivity, transitivity, contexts, variables, or weakening. -/
  | structural
  deriving Inhabited, Repr, BEq

namespace LFRuleAutomationClass

/-- Role tag convention for a rule automation class. -/
def roleName : LFRuleAutomationClass → Name
  | .formation => `formation
  | .introduction => `introduction
  | .elimination => `elimination
  | .computation => `computation
  | .structural => `structural

/-- User-facing label for a rule automation class. -/
def label (c : LFRuleAutomationClass) : String :=
  toString c.roleName

/-- Interpret a theory-local rule-role tag as a generic automation class. -/
def ofRoleName? (kind : Name) : Option LFRuleAutomationClass :=
  match kind.eraseMacroScopes with
  | `formation => some .formation
  | `introduction => some .introduction
  | `elimination => some .elimination
  | `computation => some .computation
  | `structural => some .structural
  | _ => none

end LFRuleAutomationClass

/-- Conversion-judgment classes consumed by future direct-LF rewriting. -/
inductive LFConversionJudgmentClass where
  /-- Type-level judgmental conversion/equality. -/
  | typeConversion
  /-- Term-level judgmental conversion/equality. -/
  | termConversion
  deriving Inhabited, Repr, BEq

namespace LFConversionJudgmentClass

/-- Role tag convention for a conversion judgment class. -/
def roleName : LFConversionJudgmentClass → Name
  | .typeConversion => `type_conversion
  | .termConversion => `term_conversion

/-- User-facing label for a conversion judgment class. -/
def label (c : LFConversionJudgmentClass) : String :=
  toString c.roleName

/-- Interpret a theory-local judgment-role tag as a conversion-judgment class. -/
def ofRoleName? (kind : Name) : Option LFConversionJudgmentClass :=
  match kind.eraseMacroScopes with
  | `type_conversion => some .typeConversion
  | `term_conversion => some .termConversion
  | _ => none

end LFConversionJudgmentClass

/-- Query role tags attached to a syntax sort. -/
def syntaxSortRoleKindsOf (roles : Array SyntaxSortRoleDecl) (sortName : Name) : Array Name :=
  roles.foldl (init := #[]) fun kinds role =>
    if role.sortName.eraseMacroScopes == sortName.eraseMacroScopes then
      pushIfMissing kinds role.kind.eraseMacroScopes
    else
      kinds

/-- Query role tags attached to a judgment form. -/
def judgmentRoleKindsOf (roles : Array JudgmentRoleDecl) (judgmentName : Name) : Array Name :=
  roles.foldl (init := #[]) fun kinds role =>
    if role.judgmentName.eraseMacroScopes == judgmentName.eraseMacroScopes then
      pushIfMissing kinds role.kind.eraseMacroScopes
    else
      kinds

/-- Query role tags attached to a rule. -/
def ruleRoleKindsOf (roles : Array RuleRoleDecl) (ruleName : Name) : Array Name :=
  roles.foldl (init := #[]) fun kinds role =>
    if role.ruleName.eraseMacroScopes == ruleName.eraseMacroScopes then
      pushIfMissing kinds role.kind.eraseMacroScopes
    else
      kinds

/-- Role tag for an object-language universe-level syntax family. -/
def universeLevelRoleName : Name := `universe_level

/-- Role tag for an object-language universe-code syntax family. -/
def universeCodeRoleName : Name := `universe_code

/-- Role tag for an object-language element syntax family indexed by universe codes. -/
def universeElementRoleName : Name := `universe_element

/-- Role tag for an object-language level-order/cumulativity judgment. -/
def universeLeqRoleName : Name := `universe_leq

/-- Role metadata summary for an object-language universe hierarchy. -/
structure LFUniverseHierarchyRoleProfile where
  /-- Syntax sorts tagged as object-language universe levels. -/
  levelSorts : Array Name := #[]
  /-- Syntax sorts tagged as object-language universe codes. -/
  codeSorts : Array Name := #[]
  /-- Syntax sorts tagged as object-language elements. -/
  elementSorts : Array Name := #[]
  /-- Judgments tagged as object-language level order/cumulativity evidence. -/
  leqJudgments : Array Name := #[]
  deriving Inhabited, Repr, BEq

namespace LFUniverseHierarchyRoleProfile

/-- Whether the profile contains any universe-hierarchy role metadata. -/
def hasAny (p : LFUniverseHierarchyRoleProfile) : Bool :=
  !p.levelSorts.isEmpty || !p.codeSorts.isEmpty || !p.elementSorts.isEmpty ||
    !p.leqJudgments.isEmpty

/-- Whether the profile has at least one declaration for every recognized hierarchy role. -/
def complete (p : LFUniverseHierarchyRoleProfile) : Bool :=
  !p.levelSorts.isEmpty && !p.codeSorts.isEmpty && !p.elementSorts.isEmpty &&
    !p.leqJudgments.isEmpty

/-- Render a compact list of names for hierarchy-role diagnostics. -/
def nameList (names : Array Name) : String :=
  if names.isEmpty then "(none)" else
    String.intercalate ", " (names.toList.map fun n => toString n.eraseMacroScopes)

/-- Names of missing recognized hierarchy roles. -/
def missingLabels (p : LFUniverseHierarchyRoleProfile) : Array String := Id.run do
  let mut labels := #[]
  if p.levelSorts.isEmpty then labels := labels.push "universe_level syntax sort"
  if p.codeSorts.isEmpty then labels := labels.push "universe_code syntax sort"
  if p.elementSorts.isEmpty then labels := labels.push "universe_element syntax sort"
  if p.leqJudgments.isEmpty then labels := labels.push "universe_leq judgment"
  return labels

/-- Diagnostic lines for hierarchy-role metadata. -/
def summaryLines (p : LFUniverseHierarchyRoleProfile) : Array String := Id.run do
  if !p.hasAny then
    return #["universe hierarchy roles: none"]
  let status := if p.complete then "complete" else "partial"
  let mut lines := #[s!"universe hierarchy roles: {status}"]
  lines := lines.push s!"  levels: {nameList p.levelSorts}"
  lines := lines.push s!"  codes: {nameList p.codeSorts}"
  lines := lines.push s!"  elements: {nameList p.elementSorts}"
  lines := lines.push s!"  level order: {nameList p.leqJudgments}"
  let missing := p.missingLabels
  if missing.isEmpty then
    lines := lines.push "  diagnostics: none"
  else
    lines := lines.push s!"  diagnostics: missing {String.intercalate ", " missing.toList}"
  return lines

/-- Multiline diagnostic summary for hierarchy-role metadata. -/
def summaryString (p : LFUniverseHierarchyRoleProfile) : String :=
  String.intercalate "\n" p.summaryLines.toList

end LFUniverseHierarchyRoleProfile

/-- Compute a universe-hierarchy role profile from syntax-sort and judgment role declarations. -/
def universeHierarchyRoleProfileOf (syntaxRoles : Array SyntaxSortRoleDecl)
    (judgmentRoles : Array JudgmentRoleDecl) : LFUniverseHierarchyRoleProfile := Id.run do
  let mut profile : LFUniverseHierarchyRoleProfile := {}
  for role in syntaxRoles do
    let kind := role.kind.eraseMacroScopes
    let sortName := role.sortName.eraseMacroScopes
    if kind == universeLevelRoleName then
      profile := { profile with levelSorts := pushIfMissing profile.levelSorts sortName }
    else if kind == universeCodeRoleName then
      profile := { profile with codeSorts := pushIfMissing profile.codeSorts sortName }
    else if kind == universeElementRoleName then
      profile := { profile with elementSorts := pushIfMissing profile.elementSorts sortName }
  for role in judgmentRoles do
    let kind := role.kind.eraseMacroScopes
    let judgmentName := role.judgmentName.eraseMacroScopes
    if kind == universeLeqRoleName then
      profile := { profile with leqJudgments := pushIfMissing profile.leqJudgments judgmentName }
  return profile

/-- Classify role tags for one rule. -/
def ruleAutomationClassesOfKinds (kinds : Array Name) : Array LFRuleAutomationClass :=
  kinds.foldl (init := #[]) fun classes kind =>
    match LFRuleAutomationClass.ofRoleName? kind with
    | some c => pushIfMissing classes c
    | none => classes

/-- Classify role tags for one conversion judgment. -/
def conversionJudgmentClassesOfKinds (kinds : Array Name) : Array LFConversionJudgmentClass :=
  kinds.foldl (init := #[]) fun classes kind =>
    match LFConversionJudgmentClass.ofRoleName? kind with
    | some c => pushIfMissing classes c
    | none => classes

/-- Role-driven automation diagnostic class. -/
inductive LFRoleAutomationDiagnosticKind where
  /-- A declaration has more than one recognized automation role. -/
  | ambiguous
  /-- The theory lacks role metadata needed by a future automation consumer. -/
  | insufficient
  deriving Inhabited, Repr, BEq

namespace LFRoleAutomationDiagnosticKind

/-- User-facing diagnostic label. -/
def label : LFRoleAutomationDiagnosticKind → String
  | .ambiguous => "ambiguous"
  | .insufficient => "insufficient"

end LFRoleAutomationDiagnosticKind

/-- Diagnostic emitted by the role-driven automation classifier. -/
structure LFRoleAutomationDiagnostic where
  /-- Diagnostic class. -/
  kind : LFRoleAutomationDiagnosticKind
  /-- Declaration name, when the diagnostic is about one declaration. -/
  declaration? : Option Name := none
  /-- Human-readable message. -/
  message : String
  deriving Inhabited, Repr, BEq

/-- Checked role-driven automation profile for one type theory. -/
structure LFRoleAutomationProfile where
  /-- Formation rules recognized from `rule_role`. -/
  formationRules : Array Name := #[]
  /-- Introduction rules recognized from `rule_role`. -/
  introductionRules : Array Name := #[]
  /-- Elimination rules recognized from `rule_role`. -/
  eliminationRules : Array Name := #[]
  /-- Computation rules recognized from `rule_role`. -/
  computationRules : Array Name := #[]
  /-- Structural rules recognized from `rule_role`. -/
  structuralRules : Array Name := #[]
  /-- Type-conversion judgments recognized from `judgment_role`. -/
  typeConversionJudgments : Array Name := #[]
  /-- Term-conversion judgments recognized from `judgment_role`. -/
  termConversionJudgments : Array Name := #[]
  /-- Computation rules whose conclusion is a recognized conversion judgment. -/
  rewriteCandidateRules : Array Name := #[]
  /-- Relations declared as proof/evidence-producing rewrite relations. -/
  evidenceRewriteRelations : Array Name := #[]
  /-- Rules/theorems declared as proof/evidence-producing symmetry principles. -/
  evidenceRewriteSymmetries : Array Name := #[]
  /-- Rules/theorems declared as proof/evidence-producing congruence principles. -/
  evidenceRewriteCongruences : Array Name := #[]
  /-- Rules declared as proof/evidence-producing transport rules. -/
  evidenceTransportRules : Array Name := #[]
  /-- Transport rules with declared target-head/argument-position metadata. -/
  evidenceTransportPositions : Array Name := #[]
  /-- Ambiguity or insufficiency diagnostics for automation consumers. -/
  diagnostics : Array LFRoleAutomationDiagnostic := #[]
  deriving Inhabited, Repr, BEq

namespace LFRoleAutomationProfile

/-- Rules classified under a given rule automation class. -/
def rulesForClass (profile : LFRoleAutomationProfile) :
    LFRuleAutomationClass → Array Name
  | .formation => profile.formationRules
  | .introduction => profile.introductionRules
  | .elimination => profile.eliminationRules
  | .computation => profile.computationRules
  | .structural => profile.structuralRules

end LFRoleAutomationProfile

namespace CheckedSignature

/-- Object-language universe-hierarchy role metadata for this checked signature. -/
def universeHierarchyRoleProfile (checked : CheckedSignature) : LFUniverseHierarchyRoleProfile :=
  universeHierarchyRoleProfileOf checked.lfSyntaxSortRoles checked.lfJudgmentRoles

/-- Role tags attached to a checked syntax sort. -/
def syntaxSortRoleKinds (checked : CheckedSignature) (sortName : Name) : Array Name :=
  syntaxSortRoleKindsOf checked.lfSyntaxSortRoles sortName

/-- Role tags attached to a checked judgment form. -/
def judgmentRoleKinds (checked : CheckedSignature) (judgmentName : Name) : Array Name :=
  judgmentRoleKindsOf checked.lfJudgmentRoles judgmentName

/-- Role tags attached to a checked rule. -/
def ruleRoleKinds (checked : CheckedSignature) (ruleName : Name) : Array Name :=
  ruleRoleKindsOf checked.lfRuleRoles ruleName

/-- Whether a checked rule has a specific automation class. -/
def ruleHasAutomationClass (checked : CheckedSignature) (ruleName : Name)
    (klass : LFRuleAutomationClass) : Bool :=
  (ruleAutomationClassesOfKinds (checked.ruleRoleKinds ruleName)).contains klass

/-- Whether a checked judgment is a term/type conversion judgment. -/
def judgmentHasConversionClass (checked : CheckedSignature) (judgmentName : Name)
    (klass : LFConversionJudgmentClass) : Bool :=
  (conversionJudgmentClassesOfKinds (checked.judgmentRoleKinds judgmentName)).contains klass

/-- Checked rules classified under one automation role. -/
def rulesWithAutomationClass (checked : CheckedSignature)
    (klass : LFRuleAutomationClass) : Array CheckedLFRule :=
  checked.lfRules.filter fun r => checked.ruleHasAutomationClass r.name klass

/-- Checked judgments classified under one conversion role. -/
def judgmentsWithConversionClass (checked : CheckedSignature)
    (klass : LFConversionJudgmentClass) : Array CheckedLFJudgment :=
  checked.lfJudgments.filter fun j => checked.judgmentHasConversionClass j.name klass

/-- Names of checked judgments classified as term/type conversion judgments. -/
def conversionJudgmentNames (checked : CheckedSignature) : Array Name := Id.run do
  let mut names := #[]
  for j in checked.lfJudgments do
    if !(conversionJudgmentClassesOfKinds (checked.judgmentRoleKinds j.name)).isEmpty then
      names := names.push j.name
  return names

/-- Whether a checked rule concludes in a recognized conversion judgment. -/
def ruleConcludesConversion (checked : CheckedSignature) (rule : CheckedLFRule) : Bool :=
  (checked.conversionJudgmentNames).contains rule.conclusionHead.name.eraseMacroScopes

/-- Computation rules whose conclusions are recognized conversion judgments. -/
def rewriteCandidateRules (checked : CheckedSignature) : Array CheckedLFRule :=
  checked.lfRules.filter fun r =>
    checked.ruleHasAutomationClass r.name .computation && checked.ruleConcludesConversion r

/-- Build the role-driven automation profile for a checked theory. -/
def roleAutomationProfile (checked : CheckedSignature) : LFRoleAutomationProfile := Id.run do
  let mut profile : LFRoleAutomationProfile := {}
  for r in checked.lfRules do
    let classes := ruleAutomationClassesOfKinds (checked.ruleRoleKinds r.name)
    if classes.size > 1 then
      profile := { profile with diagnostics := profile.diagnostics.push {
        kind := .ambiguous
        declaration? := some r.name
        message := s!"rule '{r.name}' has multiple automation roles: \
          {String.intercalate ", " (classes.toList.map LFRuleAutomationClass.label)}" } }
    for c in classes do
      match c with
      | .formation =>
          profile := { profile with formationRules := profile.formationRules.push r.name }
      | .introduction =>
          profile := { profile with introductionRules := profile.introductionRules.push r.name }
      | .elimination =>
          profile := { profile with eliminationRules := profile.eliminationRules.push r.name }
      | .computation =>
          profile := { profile with computationRules := profile.computationRules.push r.name }
      | .structural =>
          profile := { profile with structuralRules := profile.structuralRules.push r.name }
  for j in checked.lfJudgments do
    let classes := conversionJudgmentClassesOfKinds (checked.judgmentRoleKinds j.name)
    if classes.size > 1 then
      profile := { profile with diagnostics := profile.diagnostics.push {
        kind := .ambiguous
        declaration? := some j.name
        message := s!"judgment '{j.name}' has both type and term conversion roles" } }
    for c in classes do
      match c with
      | .typeConversion =>
          profile := {
            profile with typeConversionJudgments := profile.typeConversionJudgments.push j.name }
      | .termConversion =>
          profile := {
            profile with termConversionJudgments := profile.termConversionJudgments.push j.name }
  let rewriteCandidates := checked.rewriteCandidateRules.map (fun r => r.name)
  profile := { profile with
    rewriteCandidateRules := rewriteCandidates
    evidenceRewriteRelations := checked.lfRewriteRelations.map (·.relationName)
    evidenceRewriteSymmetries := checked.lfRewriteSymmetries.map (·.symmetryName)
    evidenceRewriteCongruences := checked.lfRewriteCongruences.map (·.congruenceName)
    evidenceTransportRules := checked.lfTransportRules.map (·.ruleName)
    evidenceTransportPositions := checked.lfTransportPositions.map (·.ruleName) }
  if checked.lfRuleRoles.isEmpty then
    profile := { profile with diagnostics := profile.diagnostics.push {
      kind := .insufficient
      message := "no rule_role metadata is available for automation" } }
  if profile.typeConversionJudgments.isEmpty && profile.termConversionJudgments.isEmpty then
    profile := { profile with diagnostics := profile.diagnostics.push {
      kind := .insufficient
      message := "no type_conversion or term_conversion judgment_role is available" } }
  if !profile.computationRules.isEmpty && profile.rewriteCandidateRules.isEmpty then
    profile := { profile with diagnostics := profile.diagnostics.push {
      kind := .insufficient
      message := "computation rules are present, but none conclude in a conversion judgment" } }
  return profile

end CheckedSignature

/-- A parsed item from a `declare_type_theory` block. -/
inductive HLTheoryItem where
  /-- Future logical-framework syntactic category declaration. -/
  | syntaxSort : SyntaxSortDecl → HLTheoryItem
  /-- Public syntax-sort-shaped abbreviation; expanded before model obligation generation. -/
  | syntaxAbbrev : SyntaxAbbrevDecl → HLTheoryItem
  /-- Derived type-valued syntax family. -/
  | syntaxDef : SyntaxDefDecl → HLTheoryItem
  /-- Public judgment-shaped abbreviation; expanded before LF checking/model generation. -/
  | judgmentAbbrev : JudgmentAbbrevDecl → HLTheoryItem
  /-- Non-semantic role metadata for a syntactic category. -/
  | syntaxSortRole : SyntaxSortRoleDecl → HLTheoryItem
  /-- Future multi-context-zone metadata. -/
  | contextZone : ContextZoneDecl → HLTheoryItem
  /-- Future binder class for scoped multi-zone syntax. -/
  | binderClass : BinderClassDecl → HLTheoryItem
  /-- Future custom judgment-form declaration. -/
  | judgment : JudgmentDecl → HLTheoryItem
  /-- Non-semantic role metadata for a custom judgment form. -/
  | judgmentRole : JudgmentRoleDecl → HLTheoryItem
  /-- Future rule declaration. -/
  | rule : RuleDecl → HLTheoryItem
  /-- Non-semantic role metadata for a future rule declaration. -/
  | ruleRole : RuleRoleDecl → HLTheoryItem
  /-- Rewrite-relation metadata for future proof/evidence-producing rewriting. -/
  | rewriteRelation : LFRewriteRelationDecl → HLTheoryItem
  /-- Rewrite-symmetry metadata for future proof/evidence-producing rewriting. -/
  | rewriteSymmetry : LFRewriteSymmetryDecl → HLTheoryItem
  /-- Rewrite-congruence metadata for future proof/evidence-producing rewriting. -/
  | rewriteCongruence : LFRewriteCongruenceDecl → HLTheoryItem
  /-- Transport-rule metadata for future proof/evidence-producing rewriting. -/
  | transportRule : LFTransportRuleDecl → HLTheoryItem
  /-- Optional transport-position metadata for proof/evidence-producing rewriting. -/
  | transportPosition : LFTransportPositionDecl → HLTheoryItem
  /-- Future side-condition solver declaration. -/
  | sideConditionSolver : SideConditionSolverDecl → HLTheoryItem
  /-- Future conversion plugin declaration. -/
  | conversionPlugin : ConversionPluginDecl → HLTheoryItem
  /-- Opaque placeholder symbol available to LF metadata expressions. -/
  | lfOpaqueConst : LFOpaqueConstDecl → HLTheoryItem
  /-- Staged sorted LF/object definition. -/
  | lfObjectDef : LFObjectDefDecl → HLTheoryItem
  /-- Model-interface visibility annotation for an LF declaration. -/
  | modelVisibility : ModelVisibilityDecl → HLTheoryItem
  /-- Model-interface section marker. -/
  | modelSection : ModelSectionDecl → HLTheoryItem
  /-- Staged custom-judgment theorem. -/
  | lfJudgmentTheorem : LFJudgmentTheoremDecl → HLTheoryItem
  deriving Inhabited, Repr, BEq

/-- A high-level user-declared type theory. -/
structure HLSignature where
  /-- Theory name. -/
  name : Name
  /-- Parent theories whose declarations are available in this theory. -/
  parents : Array Name := #[]
  /-- Object-level universe parameters declared for this theory. These are not Lean universe
  parameters; the Lean backend may later translate them. -/
  levelParams : Array Name := #[]
  /-- User-declared syntactic categories for future multi-judgment theories. -/
  syntaxSorts : Array SyntaxSortDecl := #[]
  /-- Public syntax-sort-shaped abbreviations expanded before checking/model generation. -/
  syntaxAbbrevs : Array SyntaxAbbrevDecl := #[]
  /-- Derived type-valued syntax families. -/
  syntaxDefs : Array SyntaxDefDecl := #[]
  /-- Public judgment-shaped abbreviations expanded before checking/model generation. -/
  judgmentAbbrevs : Array JudgmentAbbrevDecl := #[]
  /-- Non-semantic role metadata for syntactic categories. -/
  syntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  /-- User-declared context zones for future multi-zone judgments. -/
  contextZones : Array ContextZoneDecl := #[]
  /-- User-declared binder classes for scoped multi-zone syntax. -/
  binderClasses : Array BinderClassDecl := #[]
  /-- User-declared custom judgment forms for future multi-judgment theories. -/
  judgments : Array JudgmentDecl := #[]
  /-- Non-semantic role metadata for custom judgment forms. -/
  judgmentRoles : Array JudgmentRoleDecl := #[]
  /-- User-declared skeletal inference-rule metadata. -/
  rules : Array RuleDecl := #[]
  /-- Non-semantic role/class metadata for rules. -/
  ruleRoles : Array RuleRoleDecl := #[]
  /-- User-declared rewrite-relation metadata. -/
  rewriteRelations : Array LFRewriteRelationDecl := #[]
  /-- User-declared rewrite-symmetry metadata. -/
  rewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  /-- User-declared rewrite-congruence metadata. -/
  rewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  /-- User-declared transport-rule metadata. -/
  transportRules : Array LFTransportRuleDecl := #[]
  /-- User-declared transport-position metadata. -/
  transportPositions : Array LFTransportPositionDecl := #[]
  /-- User-declared side-condition solver metadata. -/
  sideConditionSolvers : Array SideConditionSolverDecl := #[]
  /-- User-declared conversion plugin metadata. -/
  conversionPlugins : Array ConversionPluginDecl := #[]
  /-- User-declared opaque LF placeholder symbols. -/
  lfOpaqueConsts : Array LFOpaqueConstDecl := #[]
  /-- Model-interface visibility annotations. -/
  modelVisibilities : Array ModelVisibilityDecl := #[]
  /-- User-facing generated model-interface section order. -/
  modelSections : Array ModelSectionDecl := #[]
  /-- Source LF declarations assigned to generated model-interface sections. -/
  modelSectionMemberships : Array ModelSectionMembershipDecl := #[]
  /-- Staged sorted LF/object definitions. -/
  lfObjectDefs : Array LFObjectDefDecl := #[]
  /-- Staged custom-judgment theorem declarations. -/
  lfJudgmentTheorems : Array LFJudgmentTheoremDecl := #[]
  /-- Theory-local surface macros used to expand ergonomic syntax before checking. -/
  macros : Array ObjectMacro := #[]
  /-- Non-semantic role metadata for theory-specific frontend and pretty-printer tools. -/
  roles : Array ObjectRole := #[]
  deriving Inhabited, Repr, BEq

namespace HLSignature

/-- Object-language universe-hierarchy role metadata for this high-level signature. -/
def universeHierarchyRoleProfile (sig : HLSignature) : LFUniverseHierarchyRoleProfile :=
  universeHierarchyRoleProfileOf sig.syntaxSortRoles sig.judgmentRoles

/-- Role tags attached to a syntax sort in a high-level signature. -/
def syntaxSortRoleKinds (sig : HLSignature) (sortName : Name) : Array Name :=
  syntaxSortRoleKindsOf sig.syntaxSortRoles sortName

/-- Role tags attached to a judgment form in a high-level signature. -/
def judgmentRoleKinds (sig : HLSignature) (judgmentName : Name) : Array Name :=
  judgmentRoleKindsOf sig.judgmentRoles judgmentName

/-- Role tags attached to a rule in a high-level signature. -/
def ruleRoleKinds (sig : HLSignature) (ruleName : Name) : Array Name :=
  ruleRoleKindsOf sig.ruleRoles ruleName

end HLSignature

/-- Fallback source rendering for diagnostics. -/
meta def syntaxString (stx : Syntax) : String :=
  toString stx

/-- Syntax category for object expressions in a type-theory declaration. -/
declare_syntax_cat ttExpr

/-- Syntax category for object universe expressions. -/
declare_syntax_cat ttLevel

syntax num : ttLevel
syntax ident : ttLevel
syntax "(" ttLevel ")" : ttLevel
syntax:70 ttLevel:70 "+1" : ttLevel
syntax "max" ttLevel ttLevel : ttLevel

/-- Syntax category for lambda binders in object expressions. -/
declare_syntax_cat ttLamBinder

/-- Syntax category for binders in a type-theory declaration. -/
declare_syntax_cat ttBinder

/-- Syntax category for declarations in a type-theory declaration block. -/
declare_syntax_cat ttDecl

/-- Syntax category for items in a multi-premise rule declaration. -/
declare_syntax_cat ttRuleItem

syntax "Type" : ttExpr
syntax:90 "Type" "max" ttLevel ttLevel : ttExpr
syntax:90 "Type" ttLevel : ttExpr
syntax ident : ttExpr
syntax "_" : ttExpr
syntax "(" ttExpr ")" : ttExpr
syntax "{" ident " := " ttExpr "}" : ttExpr
syntax "(" ident " := " ttExpr ")" : ttExpr
syntax:45 ttExpr:46 " ≡ " ttExpr:45 : ttExpr
syntax:50 ttExpr:51 " → " ttExpr:50 : ttExpr
syntax:50 "(" ident " : " ttExpr ")" " → " ttExpr:50 : ttExpr
/-- Explicit spelling for the framework's structural/meta-level function layer. This is
not a user-declared object-theory function type former. It currently elaborates to the
same internal representation as `→`, which remains as compatibility syntax. -/
syntax:50 ttExpr:51 " ⇒ " ttExpr:50 : ttExpr
syntax:50 "(" ident " : " ttExpr ")" " ⇒ " ttExpr:50 : ttExpr
syntax:50 ttExpr:51 " × " ttExpr:50 : ttExpr
syntax:50 "Σ " ident " : " ttExpr ", " ttExpr:50 : ttExpr
syntax "⟨" ttExpr ", " ttExpr "⟩" : ttExpr
syntax ident : ttLamBinder
syntax "_" : ttLamBinder
syntax:60 "fun " ttLamBinder+ " => " ttExpr:50 : ttExpr
syntax:70 ttExpr:70 ppSpace ttExpr:71 : ttExpr

syntax (name := ttBinderStx) "(" ident " : " ttExpr ")" : ttBinder
syntax (name := ttImplicitBinderStx) "{" ident " : " ttExpr "}" : ttBinder
syntax (name := ttSyntaxSortDeclStx)
  atomic((docComment)? "syntax_sort") ident ttBinder* : ttDecl
syntax (name := ttSyntaxSortTypedDeclStx)
  atomic((docComment)? "syntax_sort") ident ttBinder* " : " ttExpr : ttDecl
syntax (name := ttSyntaxAbbrevDeclStx)
  atomic((docComment)? "syntax_abbrev") ident ttBinder* " := " ttExpr : ttDecl
syntax (name := ttSyntaxDefDeclStx)
  atomic((docComment)? "syntax_def") ident ttBinder* " : " ttExpr " := " ttExpr : ttDecl
syntax (name := ttSyntaxDefSorryDeclStx)
  atomic((docComment)? "syntax_def") ident ttBinder* " : " ttExpr " := " "sorry" : ttDecl
syntax (name := ttJudgmentAbbrevDeclStx)
  atomic((docComment)? "judgment_abbrev") ident ttBinder* " := " ttExpr : ttDecl
syntax (name := ttSyntaxSortRoleDeclStx) "syntax_sort_role" ident " : " ident : ttDecl
syntax (name := ttSyntaxSortRoleDocDeclStx)
  atomic(docComment "syntax_sort_role") ident " : " ident : ttDecl
syntax (name := ttContextZoneDeclStx) "context_zone" ident " : " ident : ttDecl
syntax (name := ttContextZoneDocDeclStx)
  atomic(docComment "context_zone") ident " : " ident : ttDecl
syntax (name := ttContextZoneDependsDeclStx)
  "context_zone" ident " : " ident " depends_on " ident,* : ttDecl
syntax (name := ttContextZoneDependsDocDeclStx)
  atomic(docComment "context_zone") ident " : " ident " depends_on " ident,* : ttDecl
syntax (name := ttBinderClassDeclStx) "binder_class" ident " : " ident " in " ident : ttDecl
syntax (name := ttBinderClassDocDeclStx)
  atomic(docComment "binder_class") ident " : " ident " in " ident : ttDecl
syntax (name := ttBinderClassDependsDeclStx)
  "binder_class" ident " : " ident " in " ident " depends_on " ident,* : ttDecl
syntax (name := ttBinderClassDependsDocDeclStx)
  atomic(docComment "binder_class") ident " : " ident " in " ident " depends_on " ident,* : ttDecl
syntax (name := ttJudgmentDeclStx) atomic((docComment)? "judgment") ident ttBinder* : ttDecl
syntax (name := ttJudgmentRoleDeclStx) "judgment_role" ident " : " ident : ttDecl
syntax (name := ttJudgmentRoleDocDeclStx)
  atomic(docComment "judgment_role") ident " : " ident : ttDecl
syntax (name := ttRulePremiseItemStx) "premise" ident " : " ttExpr : ttRuleItem
syntax (name := ttRuleEvidenceItemStx) "evidence" ident " for " ident " : " ttExpr : ttRuleItem
syntax (name := ttRuleSideConditionItemStx)
  "side_condition" ident " by " ident " : " ttExpr : ttRuleItem
syntax (name := ttRuleConclusionItemStx) "conclusion" " : " ttExpr : ttRuleItem
syntax (name := ttRuleDeclStx)
  atomic((docComment)? "rule") ident ttBinder* " : " ttExpr : ttDecl
syntax (name := ttRuleBlockDeclStx)
  atomic((docComment)? "rule") ident ttBinder* " where" ppLine ttRuleItem* : ttDecl
syntax (name := ttRuleRoleDeclStx) "rule_role" ident " : " ident : ttDecl
syntax (name := ttRuleRoleDocDeclStx) atomic(docComment "rule_role") ident " : " ident : ttDecl
syntax (name := ttRewriteRelationDeclStx)
  "rewrite_relation" ident " [" ident ", " ident "]" : ttDecl
syntax (name := ttRewriteRelationDocDeclStx)
  atomic(docComment "rewrite_relation") ident " [" ident ", " ident "]" : ttDecl
syntax (name := ttRewriteSymmetryDeclStx)
  "rewrite_symmetry" ident " for " ident " [" ident "]" : ttDecl
syntax (name := ttRewriteSymmetryDocDeclStx) atomic(docComment "rewrite_symmetry")
  ident " for " ident " [" ident "]" : ttDecl
syntax (name := ttRewriteCongruenceDeclStx)
  "rewrite_congruence" ident " for " ident " under " ident " [" num "]" " [" ident "]" : ttDecl
syntax (name := ttRewriteCongruenceDocDeclStx) atomic(docComment "rewrite_congruence")
  ident " for " ident " under " ident " [" num "]" " [" ident "]" : ttDecl
syntax (name := ttTransportRuleDeclStx)
  "transport_rule" ident " for " ident " [" ident ", " ident "]" : ttDecl
syntax (name := ttTransportRuleDocDeclStx) atomic(docComment "transport_rule")
  ident " for " ident " [" ident ", " ident "]" : ttDecl
syntax (name := ttTransportPositionDeclStx)
  "transport_position" ident " : " ident " [" num "]" : ttDecl
syntax (name := ttTransportPositionDocDeclStx) atomic(docComment "transport_position")
  ident " : " ident " [" num "]" : ttDecl
syntax (name := ttSideConditionSolverDeclStx) "side_condition_solver" ident : ttDecl
syntax (name := ttSideConditionSolverDocDeclStx)
  atomic(docComment "side_condition_solver") ident : ttDecl
syntax (name := ttConversionPluginDeclStx) "conversion_plugin" ident : ttDecl
syntax (name := ttConversionPluginOpaqueDeclStx) "conversion_plugin" ident " opaque" : ttDecl
syntax (name := ttConversionPluginExternalDeclStx)
  "conversion_plugin" ident " external_certificate" : ttDecl
syntax (name := ttConversionPluginExecutableDeclStx)
  "conversion_plugin" ident " executable" : ttDecl
syntax (name := ttConversionPluginOpaqueStepsDeclStx)
  "conversion_plugin" ident " opaque" " [" ident,* "]" : ttDecl
syntax (name := ttConversionPluginExternalStepsDeclStx)
  "conversion_plugin" ident " external_certificate" " [" ident,* "]" : ttDecl
syntax (name := ttConversionPluginExecutableStepsDeclStx)
  "conversion_plugin" ident " executable" " [" ident,* "]" : ttDecl
syntax (name := ttConversionPluginDocDeclStx) atomic(docComment "conversion_plugin") ident : ttDecl
syntax (name := ttConversionPluginOpaqueDocDeclStx)
  atomic(docComment "conversion_plugin") ident " opaque" : ttDecl
syntax (name := ttConversionPluginExternalDocDeclStx)
  atomic(docComment "conversion_plugin") ident " external_certificate" : ttDecl
syntax (name := ttConversionPluginExecutableDocDeclStx)
  atomic(docComment "conversion_plugin") ident " executable" : ttDecl
syntax (name := ttConversionPluginOpaqueStepsDocDeclStx)
  atomic(docComment "conversion_plugin") ident " opaque" " [" ident,* "]" : ttDecl
syntax (name := ttConversionPluginExternalStepsDocDeclStx)
  atomic(docComment "conversion_plugin") ident " external_certificate" " [" ident,* "]" : ttDecl
syntax (name := ttConversionPluginExecutableStepsDocDeclStx)
  atomic(docComment "conversion_plugin") ident " executable" " [" ident,* "]" : ttDecl
syntax (name := ttLFOpaqueConstDeclStx) "lf_opaque" ident : ttDecl
syntax (name := ttLFOpaqueConstDocDeclStx) atomic(docComment "lf_opaque") ident : ttDecl
syntax (name := ttLFOpaqueConstArityDeclStx) "lf_opaque" ident " / " num : ttDecl
syntax (name := ttLFOpaqueConstArityDocDeclStx)
  atomic(docComment "lf_opaque") ident " / " num : ttDecl
syntax (name := ttLFOpaqueConstTypedDeclStx)
  atomic((docComment)? "lf_opaque") ident ttBinder* " : " ttExpr : ttDecl
syntax (name := ttModelPublicDeclStx) "model_public" ident : ttDecl
syntax (name := ttModelPublicDocDeclStx) atomic(docComment "model_public") ident : ttDecl
syntax (name := ttModelInternalDeclStx) "model_internal" ident : ttDecl
syntax (name := ttModelInternalDocDeclStx) atomic(docComment "model_internal") ident : ttDecl
syntax (name := ttModelCompatDeclStx) "model_compat" ident : ttDecl
syntax (name := ttModelCompatDocDeclStx) atomic(docComment "model_compat") ident : ttDecl
syntax (name := ttModelSectionDeclStx) "model_section" ident : ttDecl
syntax (name := ttModelSectionDocDeclStx) atomic(docComment "model_section") ident : ttDecl
syntax (name := ttLFObjectDefDeclStx)
  atomic((docComment)? "lf_def") ident " : " ttExpr " := " ttExpr : ttDecl
syntax (name := ttLFJudgmentTheoremDeclStx)
  atomic((docComment)? "judgment_theorem") ident ttBinder* " : " ttExpr " := " ttExpr : ttDecl
/-- Shorthand for the common extrinsic object-language universe hierarchy prelude.

It expands inside the theory block to ordinary `syntax_sort`, `lf_opaque`, `judgment`, and `rule`
declarations. The generated framework-universe annotations use a theory level parameter named
`u`, matching the reusable hierarchy examples.
-/
syntax (name := ttUniverseHierarchyDeclStx)
  "universe_hierarchy" ident ident ident " where" ppLine
    ident ident ident ident ppLine
    ident ident ppLine
    ident ident ppLine
    ident ident ppLine
    "universe" ident : ttDecl

/-- Parse an object universe expression. -/
meta partial def elabLevelExpr : TSyntax `ttLevel → CommandElabM LevelExpr
  | `(ttLevel| $n:num) =>
      let k := n.getNat
      pure (if k == 0 then .zero else .lit k)
  | `(ttLevel| $x:ident) => pure (.param x.getId)
  | `(ttLevel| ($u:ttLevel)) => elabLevelExpr u
  | `(ttLevel| $u:ttLevel+1) => do
      pure (.succ (← elabLevelExpr u))
  | `(ttLevel| max $u:ttLevel $v:ttLevel) => do
      let u ← elabLevelExpr u
      let v ← elabLevelExpr v
      match u, v with
      | .zero, v => pure v
      | u, .zero => pure u
      | .lit m, .lit n => pure (if Nat.max m n == 0 then .zero else .lit (Nat.max m n))
      | u, v => pure (.max u v)
  | stx => throwError "unsupported universe level syntax:{indentD stx}"

/-- Parse a lambda binder. -/
meta def elabLamBinder : TSyntax `ttLamBinder → CommandElabM Name
  | `(ttLamBinder| $x:ident) => pure x.getId
  | `(ttLamBinder| _) => pure `_
  | stx => throwError "unsupported lambda binder syntax:{indentD stx}"

/-- Child object-expression syntax nodes captured by a generated object notation parser. -/
meta def objectNotationChildExprSyntaxes (notationDecl : ObjectNotationDecl) (stx : Syntax) :
    Option (Array (TSyntax `ttExpr)) := do
  let args := stx.getArgs
  if args.size != notationDecl.parts.size then
    none
  else
    let mut out : Array (TSyntax `ttExpr) := #[]
    for part in notationDecl.parts, arg in args do
      match part with
      | .atom _ => pure ()
      | .hole _ => out := out.push (⟨arg⟩ : TSyntax `ttExpr)
    some out

/-- Parse a high-level object expression into an AST. -/
meta partial def elabObjExpr (stx : TSyntax `ttExpr) : CommandElabM ObjExpr := do
  if let some notationDecl := findObjectNotationDeclBySyntax? (← getEnv) stx.raw.getKind then
    let some holeStxs := objectNotationChildExprSyntaxes notationDecl stx.raw
      | throwError "object notation '{notationDecl.patternString}' in type theory \
          '{notationDecl.theoryName}' parsed with {stx.raw.getArgs.size} syntax part(s), expected \
            {notationDecl.parts.size}"
    if holeStxs.size != notationDecl.holeNames.size then
      throwError "object notation '{notationDecl.patternString}' in type theory \
        '{notationDecl.theoryName}' parsed with {holeStxs.size} hole(s), expected \
          {notationDecl.holeNames.size}"
    let mut subst : NameMap ObjExpr := {}
    for holeName in notationDecl.holeNames, holeStx in holeStxs do
      subst := subst.insert holeName.eraseMacroScopes (← elabObjExpr holeStx)
    pure (substObjectNotationParams subst notationDecl.template)
  else if let some stx' ← liftMacroM <| expandMacro? stx.raw then
    elabObjExpr (⟨stx'⟩ : TSyntax `ttExpr)
  else
    match stx with
      | `(ttExpr| Type) => pure .sort
      | `(ttExpr| Type max $u:ttLevel $v:ttLevel) => do
          let u ← elabLevelExpr u
          let v ← elabLevelExpr v
          match u, v with
          | .zero, v => pure (match v with | .zero => .sort | v => .univ v)
          | u, .zero => pure (match u with | .zero => .sort | u => .univ u)
          | .lit m, .lit n =>
              let out : LevelExpr := if Nat.max m n == 0 then .zero else .lit (Nat.max m n)
              pure (match out with | .zero => .sort | out => .univ out)
          | .param u, .param v =>
              if u.eraseMacroScopes == v.eraseMacroScopes then
                pure (.univ (.param u))
              else
                pure (.univ (.max (.param u) (.param v)))
          | u, v => pure (.univ (.max u v))
      | `(ttExpr| Type $u:ttLevel) => do
          let u ← elabLevelExpr u
          match u with
          | .zero => pure .sort
          | u => pure (.univ u)
      | `(ttExpr| $x:ident) => pure (.ident x.getId)
      | `(ttExpr| _) => pure (.ident `_)
      | `(ttExpr| ($e:ttExpr)) => elabObjExpr e
      | `(ttExpr| {$x:ident := $value:ttExpr}) => do
          return .app (.app (.ident `__implicitArg) (.ident x.getId)) (← elabObjExpr value)
      | `(ttExpr| ($x:ident := $value:ttExpr)) => do
          return .app (.app (.ident `__implicitArg) (.ident x.getId)) (← elabObjExpr value)
      | `(ttExpr| $a:ttExpr ≡ $b:ttExpr) => return .jeq (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| $a:ttExpr → $b:ttExpr) =>
          return .funArrow none (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| ($x:ident : $a:ttExpr) → $b:ttExpr) =>
          return .funArrow (some x.getId) (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| $a:ttExpr ⇒ $b:ttExpr) => return .arrow none (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| ($x:ident : $a:ttExpr) ⇒ $b:ttExpr) =>
          return .arrow (some x.getId) (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| $a:ttExpr × $b:ttExpr) => return .sigma none (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| Σ $x:ident : $a:ttExpr, $b:ttExpr) =>
          return .sigma (some x.getId) (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| ⟨$a:ttExpr, $b:ttExpr⟩) => return .pair (← elabObjExpr a) (← elabObjExpr b)
      | `(ttExpr| fun $xs:ttLamBinder* => $body:ttExpr) => do
          let xs ← xs.mapM elabLamBinder
          return .lam xs (← elabObjExpr body)
      | `(ttExpr| $f:ttExpr $a:ttExpr) => do
          let f ← elabObjExpr f
          let a ← elabObjExpr a
          -- The surface form `Type max u v` is parsed by the generic application grammar as
          -- `((Type max) u) v`; recognize that shape and reinterpret it as a universe level.
          match f, a with
          | .ident n, a =>
              match structuralSigmaProjectionName? n with
              | some .fst => pure (.fst a)
              | some .snd => pure (.snd a)
              | none => pure (.app f a)
          | .app (.univ (.param maxName)) (.ident u), .ident v =>
              if maxName.eraseMacroScopes == `max then
                if u.eraseMacroScopes == v.eraseMacroScopes then
                  pure (.univ (.param u))
                else
                  pure (.univ (.max (.param u) (.param v)))
              else
                pure (.app f a)
          | _, _ => pure (.app f a)
      | stx => throwError "unsupported object expression syntax:{indentD stx}"


/-- Parse a high-level binder. -/
meta def elabHLBinding : TSyntax `ttBinder → CommandElabM HLBinding
  | `(ttBinder| ($x:ident : $ty:ttExpr)) =>
      return { name := x.getId, typeExpr := (← elabObjExpr ty), visibility := .explicit }
  | `(ttBinder| {$x:ident : $ty:ttExpr}) =>
      return { name := x.getId, typeExpr := (← elabObjExpr ty), visibility := .implicit }
  | stx => throwError "unsupported type-theory binder syntax:{indentD stx}"

/-- Parse and validate a syntax-sort result universe annotation. -/
meta def elabSyntaxSortResultLevel (sortName : Name) (tyStx : TSyntax `ttExpr)
    (kind : String := "syntax_sort") : CommandElabM LevelExpr := do
  match ← elabObjExpr tyStx with
  | .sort => pure .zero
  | .univ u => pure u
  | _ =>
      throwErrorAt tyStx "{kind} '{sortName}' result annotation must be an object universe \
        (`Type`, `Type u`, `Type (u+1)`, ...)"

/-- Parsed item in a future multi-premise rule declaration. -/
inductive ParsedRuleItem where
  /-- A derivation premise. -/
  | premise : RulePremiseDecl → ParsedRuleItem
  /-- Parameter evidence. -/
  | evidence : RuleParamEvidenceDecl → ParsedRuleItem
  /-- A side condition. -/
  | sideCondition : RuleSideConditionDecl → ParsedRuleItem
  /-- The rule conclusion. -/
  | concl : ObjExpr → ParsedRuleItem
  deriving Inhabited, Repr, BEq

/-- Parse one item in a multi-premise rule declaration. -/
meta def elabRuleItem : TSyntax `ttRuleItem → CommandElabM ParsedRuleItem
  | `(ttRuleItem| premise $n:ident : $j:ttExpr) => do
      pure <| .premise { name := n.getId, judgmentExpr := (← elabObjExpr j) }
  | `(ttRuleItem| evidence $h:ident for $n:ident : $j:ttExpr) => do
      pure <| .evidence {
        name := h.getId
        paramName := n.getId
        judgmentExpr := (← elabObjExpr j)
      }
  | `(ttRuleItem| side_condition $n:ident by $solver:ident : $input:ttExpr) => do
      pure <| .sideCondition {
        name := n.getId
        solver := solver.getId
        input := (← elabObjExpr input)
      }
  | `(ttRuleItem| conclusion : $j:ttExpr) => do
      pure <| .concl (← elabObjExpr j)
  | stx => throwError "unsupported rule item syntax:{indentD stx}"

/-- Assemble rule-block items into premise, side-condition, and conclusion fields. -/
meta def mkRuleDeclFromItems (name : Name) (params : Array HLBinding)
    (items : Array ParsedRuleItem) : CommandElabM RuleDecl := do
  let mut premises := #[]
  let mut sideConditions := #[]
  let mut evidences := #[]
  let mut conclusion? : Option ObjExpr := none
  for item in items do
    match item with
    | .premise p => premises := premises.push p
    | .evidence ev =>
        evidences := evidences.push ev
        premises := premises.push { name := ev.name, judgmentExpr := ev.judgmentExpr }
    | .sideCondition sc => sideConditions := sideConditions.push sc
    | .concl c =>
        if conclusion?.isSome then
          throwError "rule '{name}' has more than one conclusion"
        conclusion? := some c
  let some conclusionExpr := conclusion?
    | throwError "rule '{name}' is missing a conclusion"
  pure { name, params, premises, sideConditions, paramEvidences := evidences, conclusionExpr }

/-- Parse a conversion-plugin step kind. -/
meta def elabConversionStepKind (stx : TSyntax `ident) : CommandElabM ConversionStepKind :=
  match stx.getId.eraseMacroScopes with
  | `beta => pure .beta
  | `eta => pure .eta
  | `reindexing => pure .reindexing
  | `side_condition => pure .sideCondition
  | `sideCondition => pure .sideCondition
  | `plugin_axiom => pure .pluginAxiom
  | `pluginAxiom => pure .pluginAxiom
  | other => throwError "unknown conversion-plugin step kind '{other}'"

/-- Parse conversion-plugin step kinds. -/
meta def elabConversionStepKinds (steps : TSyntaxArray `ident) :
    CommandElabM (Array ConversionStepKind) :=
  steps.mapM elabConversionStepKind

/-- Check one field label in a `universe_hierarchy` declaration. -/
meta def checkUniverseHierarchyLabel (label : Ident) (expected : Name) : CommandElabM Unit := do
  unless label.getId.eraseMacroScopes == expected do
    throwErrorAt label.raw "expected universe_hierarchy field '{expected}', got '{label.getId}'"

/-- Expand one `universe_hierarchy` shorthand declaration, if present. -/
meta def expandUniverseHierarchyDecl? (decl : TSyntax `ttDecl) :
    CommandElabM (Option (Array (TSyntax `ttDecl))) := do
  match decl with
  | `(ttDecl| universe_hierarchy $level:ident $ty:ident $tm:ident where
        $levelsLabel:ident $zero:ident $succ:ident $lmax:ident
        $leLabel:ident $leName:ident
        $wfLabel:ident $wfName:ident
        $liftLabel:ident $liftName:ident
        universe $univName:ident) => do
      checkUniverseHierarchyLabel levelsLabel `levels
      checkUniverseHierarchyLabel leLabel `le
      checkUniverseHierarchyLabel wfLabel `wf
      checkUniverseHierarchyLabel liftLabel `lift
      let u := mkIdentFrom level.raw `u
      let i := mkIdentFrom level.raw `i
      let j := mkIdentFrom level.raw `j
      let A := mkIdentFrom ty.raw `A
      let lePremise := mkIdentFrom leName.raw `le
      let wfPremise := mkIdentFrom wfName.raw `wf
      let leRefl := mkIdentFrom leName.raw `le_refl
      let leSucc := mkIdentFrom leName.raw `le_succ
      let liftWf := mkIdentFrom liftName.raw `lift_wf
      let univWf := mkIdentFrom univName.raw `univ_wf
      let universeLevelRole := mkIdentFrom level.raw `universe_level
      let universeCodeRole := mkIdentFrom ty.raw `universe_code
      let universeElementRole := mkIdentFrom tm.raw `universe_element
      let universeLeqRole := mkIdentFrom leName.raw `universe_leq
      let uLevel ← `(ttLevel| $u:ident)
      let uSucc ← `(ttLevel| $uLevel:ttLevel+1)
      let levelExpr ← `(ttExpr| $level:ident)
      let tyExpr ← `(ttExpr| $ty:ident)
      let iExpr ← `(ttExpr| $i:ident)
      let jExpr ← `(ttExpr| $j:ident)
      let AExpr ← `(ttExpr| $A:ident)
      let succExpr ← `(ttExpr| $succ:ident)
      let leExpr ← `(ttExpr| $leName:ident)
      let wfExpr ← `(ttExpr| $wfName:ident)
      let liftExpr ← `(ttExpr| $liftName:ident)
      let univExpr ← `(ttExpr| $univName:ident)
      let tyI ← `(ttExpr| $tyExpr:ttExpr $iExpr:ttExpr)
      let tyJ ← `(ttExpr| $tyExpr:ttExpr $jExpr:ttExpr)
      let succI ← `(ttExpr| $succExpr:ttExpr $iExpr:ttExpr)
      let leII ← `(ttExpr| $leExpr:ttExpr $iExpr:ttExpr $iExpr:ttExpr)
      let leISuccI ← `(ttExpr| $leExpr:ttExpr $iExpr:ttExpr $succI:ttExpr)
      let leIJ ← `(ttExpr| $leExpr:ttExpr $iExpr:ttExpr $jExpr:ttExpr)
      let isTyIA ← `(ttExpr| $wfExpr:ttExpr ($i:ident := $iExpr:ttExpr) $AExpr:ttExpr)
      let liftIA ← `(ttExpr|
        $liftExpr:ttExpr ($i:ident := $iExpr:ttExpr) ($j:ident := $jExpr:ttExpr) $AExpr:ttExpr)
      let isTyJLift ← `(ttExpr| $wfExpr:ttExpr ($i:ident := $jExpr:ttExpr) $liftIA:ttExpr)
      let succLevel ← `(ttExpr| $succExpr:ttExpr $iExpr:ttExpr)
      let tySucc ← `(ttExpr| $tyExpr:ttExpr $succLevel:ttExpr)
      let univI ← `(ttExpr| $univExpr:ttExpr $iExpr:ttExpr)
      let isTySuccUniv ← `(ttExpr| $wfExpr:ttExpr ($i:ident := $succLevel:ttExpr) $univI:ttExpr)
      pure <| some #[
        ← `(ttDecl| syntax_sort $level:ident : Type $uLevel:ttLevel),
        ← `(ttDecl| syntax_sort $ty:ident ($i:ident : $levelExpr:ttExpr) :
          Type $uSucc:ttLevel),
        ← `(ttDecl| syntax_sort $tm:ident {$i:ident : $levelExpr:ttExpr}
          ($A:ident : $tyI:ttExpr) : Type $uLevel:ttLevel),
        ← `(ttDecl| syntax_sort_role $level:ident : $universeLevelRole:ident),
        ← `(ttDecl| syntax_sort_role $ty:ident : $universeCodeRole:ident),
        ← `(ttDecl| syntax_sort_role $tm:ident : $universeElementRole:ident),
        ← `(ttDecl| lf_opaque $zero:ident : $levelExpr:ttExpr),
        ← `(ttDecl| lf_opaque $succ:ident ($i:ident : $levelExpr:ttExpr) :
          $levelExpr:ttExpr),
        ← `(ttDecl| lf_opaque $lmax:ident ($i:ident : $levelExpr:ttExpr)
          ($j:ident : $levelExpr:ttExpr) : $levelExpr:ttExpr),
        ← `(ttDecl| judgment $leName:ident ($i:ident : $levelExpr:ttExpr)
          ($j:ident : $levelExpr:ttExpr)),
        ← `(ttDecl| judgment_role $leName:ident : $universeLeqRole:ident),
        ← `(ttDecl| rule $leRefl:ident ($i:ident : $levelExpr:ttExpr) : $leII:ttExpr),
        ← `(ttDecl| rule $leSucc:ident ($i:ident : $levelExpr:ttExpr) : $leISuccI:ttExpr),
        ← `(ttDecl| lf_opaque $liftName:ident {$i:ident : $levelExpr:ttExpr}
          {$j:ident : $levelExpr:ttExpr} ($A:ident : $tyI:ttExpr) : $tyJ:ttExpr),
        ← `(ttDecl| judgment $wfName:ident {$i:ident : $levelExpr:ttExpr}
          ($A:ident : $tyI:ttExpr)),
        ← `(ttDecl| rule $liftWf:ident {$i:ident : $levelExpr:ttExpr}
          {$j:ident : $levelExpr:ttExpr} ($A:ident : $tyI:ttExpr) where
            premise $lePremise:ident : $leIJ:ttExpr
            premise $wfPremise:ident : $isTyIA:ttExpr
            conclusion : $isTyJLift:ttExpr),
        ← `(ttDecl| lf_opaque $univName:ident ($i:ident : $levelExpr:ttExpr) : $tySucc:ttExpr),
        ← `(ttDecl| rule $univWf:ident ($i:ident : $levelExpr:ttExpr) : $isTySuccUniv:ttExpr)
      ]
  | _ => pure none

/-- Expand theory-block shorthands to ordinary declarations in source order. -/
meta def expandUniverseHierarchyDecls (decls : TSyntaxArray `ttDecl) :
    CommandElabM (TSyntaxArray `ttDecl) := do
  let mut out : TSyntaxArray `ttDecl := #[]
  for decl in decls do
    match ← expandUniverseHierarchyDecl? decl with
    | some expanded => out := out ++ expanded
    | none => out := out.push decl
  pure out

/-- Parse a full item in a type-theory declaration block. -/
meta def elabHLTheoryItem : TSyntax `ttDecl → CommandElabM HLTheoryItem
  | `(ttDecl| $[$doc?:docComment]? syntax_sort $n:ident $bs:ttBinder*) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .syntaxSort { name := n.getId, params := bs }
  | `(ttDecl| $[$doc?:docComment]? syntax_sort $n:ident $bs:ttBinder* : $result:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .syntaxSort {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result) }
  | `(ttDecl| $[$doc?:docComment]? syntax_abbrev $n:ident $bs:ttBinder* :=
      $value:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .syntaxAbbrev { name := n.getId, params := bs, value := (← elabObjExpr value) }
  | `(ttDecl| $[$doc?:docComment]? syntax_def $n:ident $bs:ttBinder* : $result:ttExpr :=
      sorry) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .syntaxDef {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result "syntax_def")
        value? := none }
  | `(ttDecl| $[$doc?:docComment]? syntax_def $n:ident $bs:ttBinder* : $result:ttExpr :=
      $value:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .syntaxDef {
        name := n.getId
        params := bs
        resultLevel := (← elabSyntaxSortResultLevel n.getId result "syntax_def")
        value? := some (← elabObjExpr value) }
  | `(ttDecl| $[$doc?:docComment]? judgment_abbrev $n:ident $bs:ttBinder* :=
      $value:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .judgmentAbbrev { name := n.getId, params := bs, value := (← elabObjExpr value) }
  | `(ttDecl| syntax_sort_role $sortName:ident : $kind:ident) =>
      pure <| .syntaxSortRole { sortName := sortName.getId, kind := kind.getId }
  | `(ttDecl| $doc:docComment syntax_sort_role $sortName:ident : $kind:ident) =>
      let _ := doc.raw
      pure <| .syntaxSortRole { sortName := sortName.getId, kind := kind.getId }
  | `(ttDecl| context_zone $n:ident : $sortName:ident) =>
      pure <| .contextZone { name := n.getId, sortName := sortName.getId }
  | `(ttDecl| $doc:docComment context_zone $n:ident : $sortName:ident) =>
      let _ := doc.raw
      pure <| .contextZone { name := n.getId, sortName := sortName.getId }
  | `(ttDecl| context_zone $n:ident : $sortName:ident depends_on $deps:ident,*) =>
      pure <| .contextZone {
        name := n.getId
        sortName := sortName.getId
        dependsOn := deps.getElems.map (·.getId)
      }
  | `(ttDecl| $doc:docComment context_zone $n:ident : $sortName:ident depends_on $deps:ident,*) =>
      let _ := doc.raw
      pure <| .contextZone {
        name := n.getId
        sortName := sortName.getId
        dependsOn := deps.getElems.map (·.getId)
      }
  | `(ttDecl| binder_class $n:ident : $sortName:ident in $zoneName:ident) =>
      pure <| .binderClass {
        name := n.getId
        boundSortName := sortName.getId
        zoneName := zoneName.getId
      }
  | `(ttDecl| $doc:docComment binder_class $n:ident : $sortName:ident in $zoneName:ident) =>
      let _ := doc.raw
      pure <| .binderClass {
        name := n.getId
        boundSortName := sortName.getId
        zoneName := zoneName.getId
      }
  | `(ttDecl| binder_class $n:ident :
      $sortName:ident in $zoneName:ident depends_on $deps:ident,*) =>
      pure <| .binderClass {
        name := n.getId
        boundSortName := sortName.getId
        zoneName := zoneName.getId
        dependsOn := deps.getElems.map (·.getId)
      }
  | `(ttDecl| $doc:docComment binder_class $n:ident :
      $sortName:ident in $zoneName:ident depends_on $deps:ident,*) =>
      let _ := doc.raw
      pure <| .binderClass {
        name := n.getId
        boundSortName := sortName.getId
        zoneName := zoneName.getId
        dependsOn := deps.getElems.map (·.getId)
      }
  | `(ttDecl| $[$doc?:docComment]? judgment $n:ident $bs:ttBinder*) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .judgment { name := n.getId, params := bs }
  | `(ttDecl| judgment_role $judgmentName:ident : $kind:ident) =>
      pure <| .judgmentRole { judgmentName := judgmentName.getId, kind := kind.getId }
  | `(ttDecl| $doc:docComment judgment_role $judgmentName:ident : $kind:ident) =>
      let _ := doc.raw
      pure <| .judgmentRole { judgmentName := judgmentName.getId, kind := kind.getId }
  | `(ttDecl| $[$doc?:docComment]? rule $n:ident $bs:ttBinder* : $conclStx:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .rule { name := n.getId, params := bs, conclusionExpr := (← elabObjExpr conclStx) }
  | `(ttDecl| $[$doc?:docComment]? rule $n:ident $bs:ttBinder* where $items:ttRuleItem*) => do
      let bs ← bs.mapM elabHLBinding
      let items ← items.mapM elabRuleItem
      pure <| .rule (← mkRuleDeclFromItems n.getId bs items)
  | `(ttDecl| rule_role $ruleName:ident : $kind:ident) =>
      pure <| .ruleRole { ruleName := ruleName.getId, kind := kind.getId }
  | `(ttDecl| $doc:docComment rule_role $ruleName:ident : $kind:ident) =>
      let _ := doc.raw
      pure <| .ruleRole { ruleName := ruleName.getId, kind := kind.getId }
  | `(ttDecl| rewrite_relation $r:ident [ $lhs:ident, $rhs:ident ]) =>
      pure <| .rewriteRelation {
        relationName := r.getId, lhsParam := lhs.getId, rhsParam := rhs.getId }
  | `(ttDecl| $doc:docComment rewrite_relation $r:ident [ $lhs:ident, $rhs:ident ]) =>
      let _ := doc.raw
      pure <| .rewriteRelation {
        relationName := r.getId, lhsParam := lhs.getId, rhsParam := rhs.getId }
  | `(ttDecl| rewrite_symmetry $symm:ident for $rel:ident [ $ev:ident ]) =>
      pure <| .rewriteSymmetry {
        symmetryName := symm.getId, relationName := rel.getId, evidenceParam := ev.getId }
  | `(ttDecl| $doc:docComment rewrite_symmetry $symm:ident for $rel:ident [ $ev:ident ]) =>
      let _ := doc.raw
      pure <| .rewriteSymmetry {
        symmetryName := symm.getId, relationName := rel.getId, evidenceParam := ev.getId }
  | `(ttDecl| rewrite_congruence $congr:ident for $rel:ident under $head:ident
      [ $idx:num ] [ $ev:ident ]) =>
      pure <| .rewriteCongruence {
        congruenceName := congr.getId, relationName := rel.getId, targetHead := head.getId,
        argumentIndex := idx.getNat, evidenceParam := ev.getId }
  | `(ttDecl| $doc:docComment rewrite_congruence $congr:ident for $rel:ident
      under $head:ident [ $idx:num ] [ $ev:ident ]) =>
      let _ := doc.raw
      pure <| .rewriteCongruence {
        congruenceName := congr.getId, relationName := rel.getId, targetHead := head.getId,
        argumentIndex := idx.getNat, evidenceParam := ev.getId }
  | `(ttDecl| transport_rule $ruleName:ident for $rel:ident [ $ev:ident, $src:ident ]) =>
      pure <| .transportRule {
        ruleName := ruleName.getId, relationName := rel.getId,
        evidencePremise := ev.getId, sourcePremise := src.getId }
  | `(ttDecl|
      $doc:docComment transport_rule $ruleName:ident for $rel:ident [ $ev:ident, $src:ident ]) =>
      let _ := doc.raw
      pure <| .transportRule {
        ruleName := ruleName.getId, relationName := rel.getId,
        evidencePremise := ev.getId, sourcePremise := src.getId }
  | `(ttDecl| transport_position $ruleName:ident : $head:ident [ $idx:num ]) =>
      pure <| .transportPosition {
        ruleName := ruleName.getId, targetHead := head.getId,
        argumentIndex := idx.getNat }
  | `(ttDecl| $doc:docComment transport_position $ruleName:ident : $head:ident [ $idx:num ]) =>
      let _ := doc.raw
      pure <| .transportPosition {
        ruleName := ruleName.getId, targetHead := head.getId,
        argumentIndex := idx.getNat }
  | `(ttDecl| side_condition_solver $n:ident) =>
      pure <| .sideConditionSolver { name := n.getId }
  | `(ttDecl| $doc:docComment side_condition_solver $n:ident) =>
      let _ := doc.raw
      pure <| .sideConditionSolver { name := n.getId }
  | `(ttDecl| conversion_plugin $n:ident) =>
      pure <| .conversionPlugin { name := n.getId }
  | `(ttDecl| conversion_plugin $n:ident opaque) =>
      pure <| .conversionPlugin { name := n.getId, trust := .opaqueAssumption }
  | `(ttDecl| conversion_plugin $n:ident external_certificate) =>
      pure <| .conversionPlugin { name := n.getId, trust := .externalCertificate }
  | `(ttDecl| conversion_plugin $n:ident executable) =>
      pure <| .conversionPlugin { name := n.getId, trust := .executableChecked }
  | `(ttDecl| conversion_plugin $n:ident opaque [$steps:ident,*]) => do
      pure <| .conversionPlugin {
        name := n.getId, trust := .opaqueAssumption,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl| conversion_plugin $n:ident external_certificate [$steps:ident,*]) => do
      pure <| .conversionPlugin {
        name := n.getId, trust := .externalCertificate,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl| conversion_plugin $n:ident executable [$steps:ident,*]) => do
      pure <| .conversionPlugin {
        name := n.getId, trust := .executableChecked,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident) =>
      let _ := doc.raw
      pure <| .conversionPlugin { name := n.getId }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident opaque) =>
      let _ := doc.raw
      pure <| .conversionPlugin { name := n.getId, trust := .opaqueAssumption }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident external_certificate) =>
      let _ := doc.raw
      pure <| .conversionPlugin { name := n.getId, trust := .externalCertificate }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident executable) =>
      let _ := doc.raw
      pure <| .conversionPlugin { name := n.getId, trust := .executableChecked }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident opaque [$steps:ident,*]) => do
      let _ := doc.raw
      pure <| .conversionPlugin {
        name := n.getId, trust := .opaqueAssumption,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl|
      $doc:docComment conversion_plugin $n:ident external_certificate [$steps:ident,*]) => do
      let _ := doc.raw
      pure <| .conversionPlugin {
        name := n.getId, trust := .externalCertificate,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl| $doc:docComment conversion_plugin $n:ident executable [$steps:ident,*]) => do
      let _ := doc.raw
      pure <| .conversionPlugin {
        name := n.getId, trust := .executableChecked,
        supportedSteps := (← elabConversionStepKinds steps.getElems) }
  | `(ttDecl| lf_opaque $n:ident) =>
      pure <| .lfOpaqueConst { name := n.getId }
  | `(ttDecl| $doc:docComment lf_opaque $n:ident) =>
      let _ := doc.raw
      pure <| .lfOpaqueConst { name := n.getId }
  | `(ttDecl| lf_opaque $n:ident / $arity:num) =>
      pure <| .lfOpaqueConst { name := n.getId, arity? := some arity.getNat }
  | `(ttDecl| $doc:docComment lf_opaque $n:ident / $arity:num) =>
      let _ := doc.raw
      pure <| .lfOpaqueConst { name := n.getId, arity? := some arity.getNat }
  | `(ttDecl| $[$doc?:docComment]? lf_opaque $n:ident $bs:ttBinder* : $ty:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .lfOpaqueConst {
        name := n.getId
        arity? := some bs.size
        params := bs
        typeExpr? := some (← elabObjExpr ty) }
  | `(ttDecl| model_public $n:ident) =>
      pure <| .modelVisibility { declName := n.getId, visibility := .public_ }
  | `(ttDecl| $doc:docComment model_public $n:ident) =>
      let _ := doc.raw
      pure <| .modelVisibility { declName := n.getId, visibility := .public_ }
  | `(ttDecl| model_internal $n:ident) =>
      pure <| .modelVisibility { declName := n.getId, visibility := .internal }
  | `(ttDecl| $doc:docComment model_internal $n:ident) =>
      let _ := doc.raw
      pure <| .modelVisibility { declName := n.getId, visibility := .internal }
  | `(ttDecl| model_compat $n:ident) =>
      pure <| .modelVisibility { declName := n.getId, visibility := .compat }
  | `(ttDecl| $doc:docComment model_compat $n:ident) =>
      let _ := doc.raw
      pure <| .modelVisibility { declName := n.getId, visibility := .compat }
  | `(ttDecl| model_section $n:ident) =>
      pure <| .modelSection { name := n.getId }
  | `(ttDecl| $doc:docComment model_section $n:ident) =>
      let _ := doc.raw
      pure <| .modelSection { name := n.getId }
  | `(ttDecl| $[$doc?:docComment]? lf_def $n:ident : $ty:ttExpr := $value:ttExpr) => do
      pure <| .lfObjectDef {
        name := n.getId
        typeExpr := (← elabObjExpr ty)
        value := (← elabObjExpr value)
      }
  | `(ttDecl| $[$doc?:docComment]? judgment_theorem $n:ident $bs:ttBinder* : $j:ttExpr :=
      $proof:ttExpr) => do
      let bs ← bs.mapM elabHLBinding
      pure <| .lfJudgmentTheorem {
        name := n.getId
        binders := bs
        judgmentExpr := (← elabObjExpr j)
        proof := (← elabObjExpr proof)
      }
  | stx =>
      throwError
        "unsupported type-theory declaration syntax; old `type`/`term`/`eq` declarations \
        have been removed{indentD stx}"

/-- Parsed content of a type-theory declaration block, split by declaration class. -/
structure HLTheoryBlock where
  syntaxSorts : Array SyntaxSortDecl := #[]
  syntaxAbbrevs : Array SyntaxAbbrevDecl := #[]
  syntaxDefs : Array SyntaxDefDecl := #[]
  judgmentAbbrevs : Array JudgmentAbbrevDecl := #[]
  syntaxSortRoles : Array SyntaxSortRoleDecl := #[]
  contextZones : Array ContextZoneDecl := #[]
  binderClasses : Array BinderClassDecl := #[]
  judgments : Array JudgmentDecl := #[]
  judgmentRoles : Array JudgmentRoleDecl := #[]
  rules : Array RuleDecl := #[]
  ruleRoles : Array RuleRoleDecl := #[]
  rewriteRelations : Array LFRewriteRelationDecl := #[]
  rewriteSymmetries : Array LFRewriteSymmetryDecl := #[]
  rewriteCongruences : Array LFRewriteCongruenceDecl := #[]
  transportRules : Array LFTransportRuleDecl := #[]
  transportPositions : Array LFTransportPositionDecl := #[]
  sideConditionSolvers : Array SideConditionSolverDecl := #[]
  conversionPlugins : Array ConversionPluginDecl := #[]
  lfOpaqueConsts : Array LFOpaqueConstDecl := #[]
  modelVisibilities : Array ModelVisibilityDecl := #[]
  modelSections : Array ModelSectionDecl := #[]
  modelSectionMemberships : Array ModelSectionMembershipDecl := #[]
  lfObjectDefs : Array LFObjectDefDecl := #[]
  lfJudgmentTheorems : Array LFJudgmentTheoremDecl := #[]
  deriving Inhabited, Repr, BEq

/-- Split parsed declaration-block items by class. -/
meta def HLTheoryBlock.ofItems (items : Array HLTheoryItem) : HLTheoryBlock := Id.run do
  let mut block : HLTheoryBlock := {}
  let mut currentSection? : Option Name := none
  let assignCurrentSection
      (currentSection? : Option Name) (block : HLTheoryBlock) (declName : Name) :
      HLTheoryBlock :=
    match currentSection? with
    | none => block
    | some sectionName =>
        let membership := { sectionName := sectionName, declName := declName }
        { block with modelSectionMemberships := block.modelSectionMemberships.push membership }
  for item in items do
    match item with
    | .syntaxSort d =>
        block := assignCurrentSection currentSection?
          { block with syntaxSorts := block.syntaxSorts.push d } d.name
    | .syntaxAbbrev d =>
        block := assignCurrentSection currentSection?
          { block with syntaxAbbrevs := block.syntaxAbbrevs.push d } d.name
    | .syntaxDef d =>
        block := assignCurrentSection currentSection?
          { block with syntaxDefs := block.syntaxDefs.push d } d.name
    | .judgmentAbbrev d =>
        block := assignCurrentSection currentSection?
          { block with judgmentAbbrevs := block.judgmentAbbrevs.push d } d.name
    | .syntaxSortRole d => block := { block with syntaxSortRoles := block.syntaxSortRoles.push d }
    | .contextZone d => block := { block with contextZones := block.contextZones.push d }
    | .binderClass d => block := { block with binderClasses := block.binderClasses.push d }
    | .judgment d =>
        block := assignCurrentSection currentSection?
          { block with judgments := block.judgments.push d } d.name
    | .judgmentRole d => block := { block with judgmentRoles := block.judgmentRoles.push d }
    | .rule d =>
        block := assignCurrentSection currentSection?
          { block with rules := block.rules.push d } d.name
    | .ruleRole d => block := { block with ruleRoles := block.ruleRoles.push d }
    | .rewriteRelation d =>
        block := { block with rewriteRelations := block.rewriteRelations.push d }
    | .rewriteSymmetry d =>
        block := { block with rewriteSymmetries := block.rewriteSymmetries.push d }
    | .rewriteCongruence d =>
        block := { block with rewriteCongruences := block.rewriteCongruences.push d }
    | .transportRule d =>
        block := { block with transportRules := block.transportRules.push d }
    | .transportPosition d =>
        block := { block with transportPositions := block.transportPositions.push d }
    | .sideConditionSolver d =>
        block := { block with sideConditionSolvers := block.sideConditionSolvers.push d }
    | .conversionPlugin d =>
        block := { block with conversionPlugins := block.conversionPlugins.push d }
    | .lfOpaqueConst d =>
        block := assignCurrentSection currentSection?
          { block with lfOpaqueConsts := block.lfOpaqueConsts.push d } d.name
    | .modelVisibility d =>
        block := { block with modelVisibilities := block.modelVisibilities.push d }
    | .modelSection d =>
        block := { block with modelSections := block.modelSections.push d }
        currentSection? := some d.name
    | .lfObjectDef d =>
        block := assignCurrentSection currentSection?
          { block with lfObjectDefs := block.lfObjectDefs.push d } d.name
    | .lfJudgmentTheorem d =>
        block := assignCurrentSection currentSection?
          { block with lfJudgmentTheorems := block.lfJudgmentTheorems.push d } d.name
  return block

/-- Parse a type-theory declaration block into class-indexed metadata. -/
meta def elabHLTheoryBlock (decls : TSyntaxArray `ttDecl) : CommandElabM HLTheoryBlock := do
  let decls ← expandUniverseHierarchyDecls decls
  return HLTheoryBlock.ofItems (← decls.mapM elabHLTheoryItem)

namespace HLBinding

/-- Render a high-level binder. -/
def summary (b : HLBinding) : String :=
  match b.visibility with
  | .explicit => s!"({ObjExpr.userNameString b.name} : {b.typeExpr})"
  | .implicit => "{" ++ ObjExpr.userNameString b.name ++ " : " ++ toString b.typeExpr ++ "}"

end HLBinding

namespace SyntaxSortDecl

/-- Render a syntactic-sort declaration. -/
def summary (d : SyntaxSortDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  let paramText := if params.isEmpty then "" else s!" {params}"
  let resultText :=
    if LevelExpr.equal d.resultLevel .zero then "" else s!" : Type {d.resultLevel}"
  m!"syntax_sort {d.name}{paramText}{resultText}"

end SyntaxSortDecl

namespace SyntaxAbbrevDecl

/-- Render a syntax-sort-shaped abbreviation. -/
def summary (d : SyntaxAbbrevDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  m!"syntax_abbrev {d.name} {params} := {d.value}"

end SyntaxAbbrevDecl

namespace SyntaxDefDecl

/-- Render a derived syntax-family definition. -/
def summary (d : SyntaxDefDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  let paramText := if params.isEmpty then "" else s!" {params}"
  let body := match d.value? with
    | some value => m!"{value}"
    | none => m!"sorry"
  m!"syntax_def {d.name}{paramText} : Type {d.resultLevel} := {body}"

end SyntaxDefDecl

namespace JudgmentAbbrevDecl

/-- Render a judgment-shaped abbreviation. -/
def summary (d : JudgmentAbbrevDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  m!"judgment_abbrev {d.name} {params} := {d.value}"

end JudgmentAbbrevDecl

namespace SyntaxSortRoleDecl

/-- Render syntax-sort role metadata. -/
def summary (d : SyntaxSortRoleDecl) : MessageData :=
  m!"syntax_sort_role {d.sortName} : {d.kind}"

end SyntaxSortRoleDecl

namespace ContextZoneDecl

/-- Render context-zone metadata. -/
def summary (d : ContextZoneDecl) : MessageData :=
  let deps :=
    if d.dependsOn.isEmpty then ""
    else " depends_on " ++ String.intercalate ", " (d.dependsOn.toList.map toString)
  m!"context_zone {d.name} : {d.sortName}{deps}"

end ContextZoneDecl

namespace BinderClassDecl

/-- Render binder-class metadata. -/
def summary (d : BinderClassDecl) : MessageData :=
  let deps :=
    if d.dependsOn.isEmpty then ""
    else " depends_on " ++ String.intercalate ", " (d.dependsOn.toList.map toString)
  m!"binder_class {d.name} : {d.boundSortName} in {d.zoneName}{deps}"

end BinderClassDecl

namespace JudgmentDecl

/-- Render a judgment-form declaration. -/
def summary (d : JudgmentDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  m!"judgment {d.name} {params}"

end JudgmentDecl

namespace JudgmentRoleDecl

/-- Render judgment-role metadata. -/
def summary (d : JudgmentRoleDecl) : MessageData :=
  m!"judgment_role {d.judgmentName} : {d.kind}"

end JudgmentRoleDecl

namespace RulePremiseDecl

/-- Render a rule premise. -/
def summary (d : RulePremiseDecl) : String :=
  s!"premise {d.name} : {d.judgmentExpr}"

end RulePremiseDecl

namespace RuleSideConditionDecl

/-- Render a rule side condition. -/
def summary (d : RuleSideConditionDecl) : String :=
  s!"side_condition {d.name} by {d.solver} : {d.input}"

end RuleSideConditionDecl

namespace RuleDecl

/-- Render a skeletal rule declaration. -/
def summary (d : RuleDecl) : MessageData :=
  let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
  if d.premises.isEmpty && d.sideConditions.isEmpty then
    m!"rule {d.name} {params} : {d.conclusionExpr}"
  else
    let evidenceNames : NameSet :=
      d.paramEvidences.foldl (init := {}) fun acc ev => acc.insert ev.name.eraseMacroScopes
    let premiseText := d.premises.toList.filterMap fun p =>
      if evidenceNames.contains p.name.eraseMacroScopes then
        none
      else
        some (RulePremiseDecl.summary p)
    let evidenceText := d.paramEvidences.toList.map fun ev =>
      s!"evidence {ev.name} for {ev.paramName} : {ev.judgmentExpr}"
    let sideConditionText := d.sideConditions.toList.map RuleSideConditionDecl.summary
    let items :=
      premiseText ++ evidenceText ++ sideConditionText ++ [s!"conclusion : {d.conclusionExpr}"]
    m!"rule {d.name} {params} where\n  {String.intercalate "\n  " items}"

end RuleDecl

namespace RuleRoleDecl

/-- Render rule-role metadata. -/
def summary (d : RuleRoleDecl) : MessageData :=
  m!"rule_role {d.ruleName} : {d.kind}"

end RuleRoleDecl

namespace LFRewriteRelationDecl

/-- Render rewrite-relation metadata. -/
def summary (d : LFRewriteRelationDecl) : MessageData :=
  m!"rewrite_relation {d.relationName} [{d.lhsParam}, {d.rhsParam}]"

end LFRewriteRelationDecl

namespace LFRewriteSymmetryDecl

/-- Render rewrite-symmetry metadata. -/
def summary (d : LFRewriteSymmetryDecl) : MessageData :=
  m!"rewrite_symmetry {d.symmetryName} for {d.relationName} [{d.evidenceParam}]"

end LFRewriteSymmetryDecl

namespace LFRewriteCongruenceDecl

/-- Render rewrite-congruence metadata. -/
def summary (d : LFRewriteCongruenceDecl) : MessageData :=
  m!"rewrite_congruence {d.congruenceName} for {d.relationName} " ++
    m!"under {d.targetHead} [{d.argumentIndex}] [{d.evidenceParam}]"

end LFRewriteCongruenceDecl

namespace LFTransportRuleDecl

/-- Render transport-rule metadata. -/
def summary (d : LFTransportRuleDecl) : MessageData :=
  m!"transport_rule {d.ruleName} for {d.relationName} " ++
    m!"[{d.evidencePremise}, {d.sourcePremise}]"

end LFTransportRuleDecl

namespace LFTransportPositionDecl

/-- Render transport-position metadata. -/
def summary (d : LFTransportPositionDecl) : MessageData :=
  m!"transport_position {d.ruleName} : {d.targetHead} [{d.argumentIndex}]"

end LFTransportPositionDecl

namespace SideConditionSolverDecl

/-- Render a side-condition solver metadata declaration. -/
def summary (d : SideConditionSolverDecl) : MessageData :=
  m!"side_condition_solver {d.name}"

end SideConditionSolverDecl

namespace ConversionPluginDecl

/-- Render a conversion plugin metadata declaration. -/
def summary (d : ConversionPluginDecl) : MessageData :=
  let supported :=
    if d.supportedSteps.isEmpty then "metadata_only"
    else String.intercalate "," (d.supportedSteps.toList.map ConversionStepKind.label)
  m!"conversion_plugin {d.name} [{d.trust.label}; {supported}]"

end ConversionPluginDecl

namespace LFOpaqueConstDecl

/-- Render an opaque LF placeholder declaration. -/
def summary (d : LFOpaqueConstDecl) : MessageData :=
  match d.typeExpr? with
  | some typeExpr =>
      let params := String.intercalate " " (d.params.toList.map HLBinding.summary)
      m!"lf_opaque {d.name} {params} : {typeExpr}"
  | none =>
      match d.arity? with
      | none => m!"lf_opaque {d.name}"
      | some arity => m!"lf_opaque {d.name} / {arity}"

end LFOpaqueConstDecl




namespace ModelVisibilityDecl

/-- Render model-interface visibility metadata. -/
def summary (d : ModelVisibilityDecl) : MessageData :=
  m!"model_{d.visibility.label} {d.declName}"

end ModelVisibilityDecl

namespace ModelSectionDecl

/-- Render model-interface section metadata. -/
def summary (d : ModelSectionDecl) : MessageData :=
  m!"model_section {d.name}"

end ModelSectionDecl

namespace ModelSectionMembershipDecl

/-- Render model-interface section membership metadata. -/
def summary (d : ModelSectionMembershipDecl) : MessageData :=
  m!"model_section_member {d.sectionName} : {d.declName}"

end ModelSectionMembershipDecl

namespace LFObjectDefDecl

/-- Render a staged sorted LF/object definition. -/
def summary (d : LFObjectDefDecl) : MessageData :=
  m!"lf_def {d.name} : {d.typeExpr} := {d.value}"

end LFObjectDefDecl

namespace LFJudgmentTheoremDecl

/-- Render a staged custom-judgment theorem. -/
def summary (d : LFJudgmentTheoremDecl) : MessageData :=
  let binders := d.binders.foldl (init := m!"") fun acc b =>
    let openDelim := if b.visibility == .implicit then "{" else "("
    let closeDelim := if b.visibility == .implicit then "}" else ")"
    acc ++ m!" {openDelim}{b.name} : {b.typeExpr}{closeDelim}"
  m!"judgment_theorem {d.name}{binders} : {d.judgmentExpr} := {d.proof}"

end LFJudgmentTheoremDecl

end InternalLean
