/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Model-structure dependency-order regressions

The generated model-structure field order must account for dependencies introduced by syntax
abbreviation and `lf_def` expansion during rendering. These tests are generic; the SCT-shaped smoke
test is only a reduced reproducer for the dependency pattern.
-/

@[expose] public section

declare_type_theory ModelRenderedDefDependency where
  syntax_sort A
  syntax_sort F (x : A)
  lf_opaque a : A
  lf_opaque f (x : A) : A
  lf_def b : A := f a
  syntax_abbrev Alias := F b
  syntax_sort P (x : Alias)

generate_lf_model_structure ModelRenderedDefDependency as ModelRenderedDefDependencyModel

/-- info: ModelRenderedDefDependency.ModelRenderedDefDependencyModel.P
  (self : ModelRenderedDefDependency.ModelRenderedDefDependencyModel)
  (x : self.F (self.f self.a)) : Type -/
#guard_msgs (whitespace := lax) in
#check ModelRenderedDefDependency.ModelRenderedDefDependencyModel.P

declare_type_theory ModelChunkRenderedDefDependency where
  syntax_sort A
  syntax_sort F (x : A)
  lf_opaque a : A
  lf_opaque f (x : A) : A
  lf_def b : A := f a
  syntax_abbrev Alias := F b
  lf_opaque filler00 : A
  lf_opaque filler01 : A
  lf_opaque filler02 : A
  lf_opaque filler03 : A
  lf_opaque filler04 : A
  lf_opaque filler05 : A
  lf_opaque filler06 : A
  lf_opaque filler07 : A
  lf_opaque filler08 : A
  lf_opaque filler09 : A
  lf_opaque filler10 : A
  lf_opaque filler11 : A
  lf_opaque filler12 : A
  lf_opaque filler13 : A
  lf_opaque filler14 : A
  lf_opaque filler15 : A
  lf_opaque filler16 : A
  lf_opaque filler17 : A
  lf_opaque filler18 : A
  lf_opaque filler19 : A
  lf_opaque filler20 : A
  lf_opaque filler21 : A
  lf_opaque filler22 : A
  lf_opaque filler23 : A
  lf_opaque filler24 : A
  lf_opaque filler25 : A
  lf_opaque filler26 : A
  lf_opaque filler27 : A
  lf_opaque filler28 : A
  lf_opaque filler29 : A
  lf_opaque filler30 : A
  lf_opaque filler31 : A
  lf_opaque filler32 : A
  lf_opaque filler33 : A
  lf_opaque filler34 : A
  lf_opaque filler35 : A
  lf_opaque filler36 : A
  lf_opaque filler37 : A
  lf_opaque filler38 : A
  lf_opaque filler39 : A
  lf_opaque filler40 : A
  lf_opaque filler41 : A
  lf_opaque filler42 : A
  lf_opaque filler43 : A
  lf_opaque filler44 : A
  lf_opaque filler45 : A
  lf_opaque filler46 : A
  lf_opaque filler47 : A
  lf_opaque filler48 : A
  lf_opaque filler49 : A
  lf_opaque filler50 : A
  lf_opaque filler51 : A
  lf_opaque filler52 : A
  lf_opaque filler53 : A
  lf_opaque filler54 : A
  lf_opaque filler55 : A
  lf_opaque filler56 : A
  lf_opaque filler57 : A
  lf_opaque filler58 : A
  lf_opaque filler59 : A
  lf_opaque filler60 : A
  lf_opaque filler61 : A
  lf_opaque filler62 : A
  lf_opaque filler63 : A
  lf_opaque filler64 : A
  lf_opaque filler65 : A
  lf_opaque filler66 : A
  lf_opaque filler67 : A
  lf_opaque filler68 : A
  lf_opaque filler69 : A
  lf_opaque filler70 : A
  lf_opaque filler71 : A
  lf_opaque filler72 : A
  lf_opaque filler73 : A
  lf_opaque filler74 : A
  lf_opaque filler75 : A
  lf_opaque filler76 : A
  lf_opaque filler77 : A
  lf_opaque filler78 : A
  lf_opaque filler79 : A
  syntax_sort P (x : Alias)

generate_lf_model_structure ModelChunkRenderedDefDependency as ModelChunkDependencyModel

#check ModelChunkRenderedDefDependency.ModelChunkDependencyModel.filler79
#check ModelChunkRenderedDefDependency.ModelChunkDependencyModel.P

declare_type_theory SCTShapeModelOrder where
  syntax_sort Anima
  syntax_sort SCat
  lf_opaque animaCat (A : Anima) : SCat
  lf_opaque terminalAnima : Anima
  lf_def terminalCat : SCat := animaCat terminalAnima
  syntax_sort Functor (C : SCat) (D : SCat)
  syntax_abbrev Obj (C : SCat) := Functor terminalCat C
  syntax_sort InitialObjectWitness (C : SCat) (x : Obj C)

generate_lf_model_structure SCTShapeModelOrder as SCTShapeModel

/-- info: SCTShapeModelOrder.SCTShapeModel.InitialObjectWitness
  (self : SCTShapeModelOrder.SCTShapeModel) (C : self.SCat)
  (x : self.Functor (self.animaCat self.terminalAnima) C) : Type -/
#guard_msgs (whitespace := lax) in
#check SCTShapeModelOrder.SCTShapeModel.InitialObjectWitness
