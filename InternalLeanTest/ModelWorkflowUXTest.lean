/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# UX-6 model workflow tests

These tests exercise the short model workflow commands, fillable templates, transport
signatures, and admitted-declaration transport diagnostics.
-/

@[expose] public section

open Lean

/-- Generic LF theory for model workflow UX. -/
declare_type_theory ModelWorkflowLF where
  /-- Core model fields. -/
  model_section Core
  /-- Object syntax sort. -/
  syntax_sort Obj
  /-- Relation judgment. -/
  judgment Rel (x : Obj)
  /-- Distinguished object. -/
  lf_opaque a : Obj
  /-- Rule/law fields. -/
  model_section Rules
  /-- Rule proving any object relation. -/
  rule rel_intro (x : Obj) : Rel x

namespace ModelWorkflowLF

/-- Checked LF object definition transported by the UX model workflow. -/
internal def objAlias : Obj := a

/-- Checked LF judgment theorem transported by the UX model workflow. -/
internal def relA : Rel a := by
  apply rel_intro

/-- warning: internal declaration 'ModelWorkflowLF.admittedObj' was admitted by `sorry`; the
annotation was checked in theory 'ModelWorkflowLF', but the body was not checked. Use
`#lint_type_theory_sorries ModelWorkflowLF` to list current admissions. -/
#guard_msgs (whitespace := lax) in
/-- Admitted LF object transported with an explicit Lean sorry dependency. -/
internal def admittedObj : Obj := sorry

/-- warning: internal declaration 'ModelWorkflowLF.admittedUnary' was admitted by `sorry`; the
annotation was checked in theory 'ModelWorkflowLF', but the body was not checked. Use
`#lint_type_theory_sorries ModelWorkflowLF` to list current admissions. -/
#guard_msgs (whitespace := lax) in
/-- Admitted LF unary object constructor transported with an explicit Lean sorry dependency. -/
internal def admittedUnary : (x : Obj) → Obj := sorry

/-- Checked LF theorem depending on the admitted LF object. -/
internal def relAdmitted : Rel admittedObj := by
  apply rel_intro

/-- Checked LF theorem depending on an application of the admitted LF unary constructor. -/
internal def relUnaryAdmitted : Rel (admittedUnary admittedObj) := by
  apply rel_intro

end ModelWorkflowLF

#check_theory ModelWorkflowLF

/-- info: compact LF replay certificate for ModelWorkflowLF.relA checks: 1 rule(s), 0
theorem/certificate context entry(ies), 0 local parameter(s) -/
#guard_msgs (whitespace := lax) in
#check_lf_replay_certificate ModelWorkflowLF relA
#print_lf_replay_certificate ModelWorkflowLF relA

/-- error: unknown checked LF judgment theorem 'missing' in type theory 'ModelWorkflowLF' -/
#guard_msgs (whitespace := lax) in
#check_lf_replay_certificate ModelWorkflowLF missing

#check_model_obligations ModelWorkflowLF

/-- info: model obligations for ModelWorkflowLF (generic LF-model backend)
LF model obligations for ModelWorkflowLF: 10 obligation(s), 4 user field(s), 5 generated
method/declaration(s), 0 theorem-local certificate parameter(s), 0 replay artifact(s), 1 metadata
expansion(s), 0 blocked/omitted obligation(s)
field breakdown: 1 syntax_sort, 1 judgment, 1 typed lf_opaque, 1 rule
next action: run `#print_model_interface ModelWorkflowLF as <Name>`, then fill the 4 user field(s);
checked LF definitions/theorems can be generated afterward with `#print_lf_model_transports`.
fields to provide:
  Obj ← syntax_sort Obj: ready
  a ← typed lf_opaque a: ready
  Rel ← judgment Rel: ready
  rel_intro ← rule rel_intro: ready
derived declarations generated from replay:
  admittedObj ← admitted lf_opaque admittedObj: ready (generated as a Lean declaration whose body
  uses sorry, not as a model field)
  admittedUnary ← admitted lf_opaque admittedUnary: ready (generated as a Lean declaration whose
  body uses sorry, not as a model field)
  relA ← judgment_theorem relA: ready
  relAdmitted ← judgment_theorem relAdmitted: ready
  relUnaryAdmitted ← judgment_theorem relUnaryAdmitted: ready
theorem-local certificate parameters: none
blocked/omitted: none -/
#guard_msgs (whitespace := lax) in
#print_model_obligations ModelWorkflowLF

#print_model_interface ModelWorkflowLF as LFUXModel
#print_model_template ModelWorkflowLF as LFUXModel
#print_model_sections ModelWorkflowLF
#print_model_section_template ModelWorkflowLF Core as BundledLFUXPreview
#print_model_section_template ModelWorkflowLF Rules as BundledLFUXPreview
#print_model_section_bundles ModelWorkflowLF as BundledLFUXPreview adapting LFUXModel

generate_model_interface ModelWorkflowLF as LFUXModel
generate_model_sections ModelWorkflowLF as SectionedLFUXModel adapting LFUXModel
generate_model_section_bundles ModelWorkflowLF as BundledLFUXModel adapting LFUXModel

/-- Concrete tiny LF model used to check generated dot-notation transports. -/
def lfUXModelInstance : ModelWorkflowLF.LFUXModel where
  Obj := Unit
  Rel := fun _ => Unit
  a := ()
  rel_intro := fun _ => ()

#print_model_transport_status ModelWorkflowLF for LFUXModel

/-- info: LF model transports for ModelWorkflowLF as LFUXModel
summary: 6 method(s) would be generated, 0 item(s) skipped
methods are generated in the model-interface namespace and are available by dot notation on model
instances
admitted methods:
  admitted lf_opaque admittedObj → ModelWorkflowLF.LFUXModel.admittedObj; dot: M.admittedObj; Lean
  sorry-backed
  admitted lf_opaque admittedUnary → ModelWorkflowLF.LFUXModel.admittedUnary; dot: M.admittedUnary;
  Lean sorry-backed
checked LF definition methods:
  lf_def objAlias → ModelWorkflowLF.LFUXModel.objAlias; dot: M.objAlias
checked LF theorem methods:
  judgment_theorem relA → ModelWorkflowLF.LFUXModel.relA; dot: M.relA
  judgment_theorem relAdmitted → ModelWorkflowLF.LFUXModel.relAdmitted; dot: M.relAdmitted
  judgment_theorem relUnaryAdmitted → ModelWorkflowLF.LFUXModel.relUnaryAdmitted; dot:
  M.relUnaryAdmitted
skipped items: none
next action: run `generate_lf_model_transports ModelWorkflowLF for LFUXModel` after
`generate_model_interface` and after checking name-collision notes above -/
#guard_msgs (whitespace := lax) in
#print_lf_model_transports ModelWorkflowLF for LFUXModel

#print_model_transport_signature ModelWorkflowLF objAlias for LFUXModel
generate_model_transport ModelWorkflowLF objAlias for LFUXModel
#check ModelWorkflowLF.LFUXModel.objAlias
#check lfUXModelInstance.objAlias

#print_model_transport_signature ModelWorkflowLF relA for LFUXModel
generate_model_transport ModelWorkflowLF relA for LFUXModel
#check ModelWorkflowLF.LFUXModel.relA
#check lfUXModelInstance.relA

#print_model_transport_signature ModelWorkflowLF admittedObj for LFUXModel
/-- warning: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
generate_model_transport ModelWorkflowLF admittedObj for LFUXModel
#check ModelWorkflowLF.LFUXModel.admittedObj
#check lfUXModelInstance.admittedObj

#print_model_transport_signature ModelWorkflowLF admittedUnary for LFUXModel
/-- warning: declaration uses `sorry` -/
#guard_msgs (whitespace := lax) in
generate_model_transport ModelWorkflowLF admittedUnary for LFUXModel
#check ModelWorkflowLF.LFUXModel.admittedUnary
#check lfUXModelInstance.admittedUnary

#print_model_transport_signature ModelWorkflowLF relAdmitted for LFUXModel
generate_model_transport ModelWorkflowLF relAdmitted for LFUXModel
#check ModelWorkflowLF.LFUXModel.relAdmitted

#print_model_transport_signature ModelWorkflowLF relUnaryAdmitted for LFUXModel
generate_model_transport ModelWorkflowLF relUnaryAdmitted for LFUXModel
#check ModelWorkflowLF.LFUXModel.relUnaryAdmitted

/-- warning: type theory 'ModelWorkflowLF' has 2 admitted internal declaration(s):
admitted internal def ModelWorkflowLF.admittedObj : Obj [documented]
admitted internal def ModelWorkflowLF.admittedUnary (x : Obj) : Obj [documented]
downstream declarations mentioning admissions:
internal theorem relAdmitted depends on admitted admittedObj
internal theorem relUnaryAdmitted depends on admitted admittedObj, admittedUnary
generated transported declarations with Lean `sorryAx` dependency:
transported declaration ModelWorkflowLF.LFUXModel.admittedObj for admitted admittedObj over model
LFUXModel intentionally uses Lean `sorry`/`sorryAx`
transported declaration ModelWorkflowLF.LFUXModel.admittedUnary for admitted admittedUnary over
model LFUXModel intentionally uses Lean `sorry`/`sorryAx` -/
#guard_msgs (whitespace := lax) in
#lint_type_theory_sorries ModelWorkflowLF

/-- Tiny fixture for public syntax abbreviations that should not become model fields. -/
declare_type_theory SyntaxAbbrevLF where
  /-- Category sort. -/
  syntax_sort Cat
  /-- Distinguished terminal-like category. -/
  lf_opaque UnitCat : Cat
  /-- Functor sort. -/
  syntax_sort Functor (C : Cat) (D : Cat)
  /-- Public point notation; expands to functors out of `UnitCat` before model obligations. -/
  syntax_abbrev Point (C : Cat) := Functor UnitCat C
  /-- Wellformedness judgment using the public abbreviation. -/
  judgment wfPoint (C : Cat) (x : Point C)
  /-- Rule whose telescope also uses the public abbreviation. -/
  rule wf_point (C : Cat) (x : Point C) : wfPoint C x

#check_model_obligations SyntaxAbbrevLF
#print_checked_logical_framework_metadata SyntaxAbbrevLF
#print_model_obligations SyntaxAbbrevLF
#print_model_template SyntaxAbbrevLF as SyntaxAbbrevModel

generate_model_interface SyntaxAbbrevLF as SyntaxAbbrevModel

/-- The `Point` abbreviation is not a field; its uses were expanded to `Functor UnitCat C`. -/
def syntaxAbbrevModelInstance : SyntaxAbbrevLF.SyntaxAbbrevModel where
  Cat := Unit
  UnitCat := ()
  Functor := fun _ _ => Unit
  wfPoint := fun _ _ => Unit
  wf_point := fun _ _ => ()

#check SyntaxAbbrevLF.SyntaxAbbrevModel.Cat
#check SyntaxAbbrevLF.SyntaxAbbrevModel.Functor
#check SyntaxAbbrevLF.SyntaxAbbrevModel.wfPoint
#check syntaxAbbrevModelInstance.wf_point

/-- The sectioned wrapper adapts to the flat interface. -/
def sectionedLfUXModelInstance : ModelWorkflowLF.SectionedLFUXModel where
  Obj := Unit
  Rel := fun _ => Unit
  a := ()
  rel_intro := fun _ => ()

#check ModelWorkflowLF.SectionedLFUXModel.toLFUXModel
#check sectionedLfUXModelInstance.rel_intro
#check (ModelWorkflowLF.SectionedLFUXModel.toLFUXModel sectionedLfUXModelInstance).rel_intro

/-- The true bundle interface lets users fill smaller section records and assemble them. -/
def bundledLFUXCore : ModelWorkflowLF.BundledLFUXModel_Core where
  Obj := Unit
  a := ()
  Rel := fun _ => Unit

def bundledLFUXRules : ModelWorkflowLF.BundledLFUXModel_Rules where
  toBundledLFUXModel_Core := bundledLFUXCore
  rel_intro := fun _ => ()

def bundledLFUXModelInstance : ModelWorkflowLF.BundledLFUXModel where
  toBundledLFUXModel_Rules := bundledLFUXRules

def bundledLFUXFlatModel : ModelWorkflowLF.LFUXModel :=
  bundledLFUXModelInstance.toLFUXModel

#check ModelWorkflowLF.BundledLFUXModel.toLFUXModel
#check bundledLFUXFlatModel.rel_intro

/-- Tiny fixture for public/minimal model-interface filtering. -/
declare_type_theory VisibilityLF where
  /-- Public object sort. -/
  syntax_sort Pub
  /-- Internal helper sort. -/
  syntax_sort Hidden
  model_internal Hidden
  /-- Public judgment. -/
  judgment Good (x : Pub)
  /-- Internal helper judgment. -/
  judgment HiddenJ (h : Hidden)
  model_internal HiddenJ
  /-- Public point. -/
  lf_opaque pub : Pub
  /-- Internal helper point. -/
  lf_opaque hidden : Hidden
  model_internal hidden
  /-- Compatibility point retained only by the full/debug interface. -/
  lf_opaque compatPub : Pub
  model_compat compatPub
  /-- Public rule. -/
  rule good_intro (x : Pub) : Good x
  /-- Internal helper rule. -/
  rule hidden_intro (h : Hidden) : HiddenJ h
  model_internal hidden_intro
  /-- Compatibility rule retained only by the full/debug interface. -/
  rule compat_intro : Good compatPub
  model_compat compat_intro
  /-- Publicly named rule omitted from public/minimal interfaces because its telescope mentions an
  internal sort. -/
  rule depends_hidden (x : Pub) (h : Hidden) : Good x

#check_model_obligations VisibilityLF
#check_public_model_obligations VisibilityLF
#print_public_model_obligations VisibilityLF
#print_public_model_interface VisibilityLF as PublicVisibilityModel
#print_public_model_template VisibilityLF as PublicVisibilityModel
#print_public_model_section_template VisibilityLF Other as PublicVisibilityBundle

generate_public_model_interface VisibilityLF as PublicVisibilityModel
generate_public_model_sections VisibilityLF as SectionedPublicVisibilityModel adapting
  PublicVisibilityModel

/-- Public/minimal interface omits declarations marked `model_internal`/`model_compat` and public
fields depending on them. -/
def publicVisibilityModelInstance : VisibilityLF.PublicVisibilityModel where
  Pub := Unit
  Good := fun _ => Unit
  pub := ()
  good_intro := fun _ => ()

#check VisibilityLF.PublicVisibilityModel.Pub
#check VisibilityLF.PublicVisibilityModel.Good
#check VisibilityLF.PublicVisibilityModel.pub
#check publicVisibilityModelInstance.good_intro

/-- Public/minimal sectioned interface adapts to the public flat interface. -/
def sectionedPublicVisibilityModelInstance : VisibilityLF.SectionedPublicVisibilityModel where
  Pub := Unit
  Good := fun _ => Unit
  pub := ()
  good_intro := fun _ => ()

#check VisibilityLF.SectionedPublicVisibilityModel.toPublicVisibilityModel
#check sectionedPublicVisibilityModelInstance.good_intro

generate_model_interface VisibilityLF as FullVisibilityModel

/-- Full/debug interface still includes internal helper fields. -/
def fullVisibilityModelInstance : VisibilityLF.FullVisibilityModel where
  Pub := Unit
  Hidden := Unit
  Good := fun _ => Unit
  HiddenJ := fun _ => Unit
  pub := ()
  hidden := ()
  compatPub := ()
  good_intro := fun _ => ()
  hidden_intro := fun _ => ()
  compat_intro := ()
  depends_hidden := fun _ _ => ()

#check VisibilityLF.FullVisibilityModel.Hidden
#check VisibilityLF.FullVisibilityModel.compatPub
#check fullVisibilityModelInstance.compat_intro
#check fullVisibilityModelInstance.depends_hidden

/-- Tiny fixture for reopening a theory in layers while producing one coherent model interface. -/
declare_type_theory LayeredLF where
  /-- Base object sort. -/
  syntax_sort Obj
  /-- Distinguished base object. -/
  lf_opaque base : Obj

extend_type_theory LayeredLF where
  /-- Standard-library alias defined after the primitive layer. -/
  lf_def standardObj : Obj := base
  /-- Judgment layer depending on the standard definition layer. -/
  judgment Good (x : Obj)

extend_type_theory LayeredLF where
  /-- Axiom layer depending on declarations from both earlier layers. -/
  rule good_standard : Good standardObj
  /-- Checked theorem layer replaying the axiom. -/
  judgment_theorem good_standard_checked : Good standardObj := good_standard

#check_model_obligations LayeredLF
#print_model_obligations LayeredLF
#print_model_interface LayeredLF as LayeredModel

generate_model_interface LayeredLF as LayeredModel
generate_model_interface LayeredLF as LayeredSelectedModel
generate_lf_model_transports LayeredLF only good_standard_checked for LayeredSelectedModel
#check LayeredLF.LayeredSelectedModel.good_standard_checked
#print_model_transport_status LayeredLF for LayeredModel

/-- The reopened theory has one public interface; checked definitions/theorems are generated
methods. -/
def layeredModelInstance : LayeredLF.LayeredModel where
  Obj := Unit
  base := ()
  Good := fun _ => Unit
  good_standard := ()

#check LayeredLF.LayeredModel.Obj
#check LayeredLF.LayeredModel.Good
#check layeredModelInstance.good_standard

generate_lf_model_transports LayeredLF for LayeredModel
#check LayeredLF.LayeredModel.standardObj
#check LayeredLF.LayeredModel.good_standard_checked
#check layeredModelInstance.standardObj
#check layeredModelInstance.good_standard_checked
