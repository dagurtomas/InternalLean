/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Model-interface universe-level regressions

Generic tests for syntax-sort result universe annotations and generated model-interface universe
parameters. These tests are not tied to any downstream theory such as SCT.
-/

@[expose] public section

declare_type_theory SmallSortUniverse where
  syntax_sort S

generate_model_interface SmallSortUniverse as SmallSortUniverseModel

/-- info: SmallSortUniverse.SmallSortUniverseModel.S
  (self : SmallSortUniverse.SmallSortUniverseModel) : Type -/
#guard_msgs (whitespace := lax) in
#check SmallSortUniverse.SmallSortUniverseModel.S

def smallSortUniverseUnit : SmallSortUniverse.SmallSortUniverseModel where
  S := Unit

declare_type_theory LargeSortUniverse{u} where
  syntax_sort S : Type u

generate_model_interface LargeSortUniverse as LargeSortUniverseModel

/-- info: LargeSortUniverse.LargeSortUniverseModel.S.{u}
  (self : LargeSortUniverse.LargeSortUniverseModel) : Type u -/
#guard_msgs (whitespace := lax) in
#check LargeSortUniverse.LargeSortUniverseModel.S

/-- info: LargeSortUniverse.LargeSortUniverseModel.StructuralEquiv.{u}
  (M N : LargeSortUniverse.LargeSortUniverseModel) : Type u -/
#guard_msgs (whitespace := lax) in
#check LargeSortUniverse.LargeSortUniverseModel.StructuralEquiv

def largeSortUniverseType : LargeSortUniverse.LargeSortUniverseModel.{1} where
  S := Type

declare_type_theory LargeHomUniverse{u, v} where
  syntax_sort Obj : Type u
  syntax_sort Hom (X : Obj) (Y : Obj) : Type v

generate_model_interface LargeHomUniverse as LargeHomUniverseModel

/-- info: LargeHomUniverse.LargeHomUniverseModel.Hom.{u, v}
  (self : LargeHomUniverse.LargeHomUniverseModel) (X Y : self.Obj) : Type v -/
#guard_msgs (whitespace := lax) in
#check LargeHomUniverse.LargeHomUniverseModel.Hom

def largeHomUniverseModel : LargeHomUniverse.LargeHomUniverseModel.{1, 0} where
  Obj := Type
  Hom := fun X Y => X → Y

declare_type_theory LevelExprUniverse{u, v} where
  syntax_sort Succ : Type (u+1)
  syntax_sort Max : Type max u v

generate_model_interface LevelExprUniverse as LevelExprUniverseModel

/-- info: LevelExprUniverse.LevelExprUniverseModel.Succ.{u, v}
  (self : LevelExprUniverse.LevelExprUniverseModel) : Type (u + 1) -/
#guard_msgs (whitespace := lax) in
#check LevelExprUniverse.LevelExprUniverseModel.Succ

/-- info: LevelExprUniverse.LevelExprUniverseModel.Max.{u, v}
  (self : LevelExprUniverse.LevelExprUniverseModel) : Type (max u v) -/
#guard_msgs (whitespace := lax) in
#check LevelExprUniverse.LevelExprUniverseModel.Max

/-- error: syntax_sort 'BadResultLevelUniverse' in type theory 'BadResultLevelUniverse' uses
undeclared universe level parameter 'u' in result universe; declare it in the theory-level
parameter list containing 'u' or use a numeric level. Currently declared level parameter(s): none -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadResultLevelUniverse where
  syntax_sort BadResultLevelUniverse : Type u

/-- error: syntax_sort 'S' result annotation must be an object universe
(`Type`, `Type u`, `Type (u+1)`, ...) -/
#guard_msgs (whitespace := lax) in
declare_type_theory BadResultAnnotationUniverse where
  syntax_sort S : S

declare_type_theory ExtendUniverse{u} where
  syntax_sort Obj : Type u

extend_type_theory ExtendUniverse where
  syntax_sort Fam (X : Obj) : Type u

generate_model_interface ExtendUniverse as ExtendUniverseModel

/-- info: ExtendUniverse.ExtendUniverseModel.Fam.{u}
  (self : ExtendUniverse.ExtendUniverseModel) (X : self.Obj) : Type u -/
#guard_msgs (whitespace := lax) in
#check ExtendUniverse.ExtendUniverseModel.Fam

declare_type_theory SectionUniverse{u} where
  model_section Core
  syntax_sort Obj : Type u
  model_section Family
  syntax_sort Fam (X : Obj)

generate_model_interface SectionUniverse as SectionUniverseFlat
generate_model_section_interface SectionUniverse as SectionUniverseSectioned
generate_model_sections SectionUniverse as SectionUniverseWrapper adapting SectionUniverseFlat
generate_model_section_bundles SectionUniverse as SectionUniverseBundle adapting SectionUniverseFlat

/-- info: SectionUniverse.SectionUniverseSectioned.Fam.{u}
  (self : SectionUniverse.SectionUniverseSectioned) (X : self.Obj) : Type -/
#guard_msgs (whitespace := lax) in
#check SectionUniverse.SectionUniverseSectioned.Fam

declare_type_theory ChunkLateUniverse{u} where
  syntax_sort S00
  syntax_sort S01
  syntax_sort S02
  syntax_sort S03
  syntax_sort S04
  syntax_sort S05
  syntax_sort S06
  syntax_sort S07
  syntax_sort S08
  syntax_sort S09
  syntax_sort S10
  syntax_sort S11
  syntax_sort S12
  syntax_sort S13
  syntax_sort S14
  syntax_sort S15
  syntax_sort S16
  syntax_sort S17
  syntax_sort S18
  syntax_sort S19
  syntax_sort S20
  syntax_sort S21
  syntax_sort S22
  syntax_sort S23
  syntax_sort S24
  syntax_sort S25
  syntax_sort S26
  syntax_sort S27
  syntax_sort S28
  syntax_sort S29
  syntax_sort S30
  syntax_sort S31
  syntax_sort S32
  syntax_sort S33
  syntax_sort S34
  syntax_sort S35
  syntax_sort S36
  syntax_sort S37
  syntax_sort S38
  syntax_sort S39
  syntax_sort S40
  syntax_sort S41
  syntax_sort S42
  syntax_sort S43
  syntax_sort S44
  syntax_sort S45
  syntax_sort S46
  syntax_sort S47
  syntax_sort S48
  syntax_sort S49
  syntax_sort S50
  syntax_sort S51
  syntax_sort S52
  syntax_sort S53
  syntax_sort S54
  syntax_sort S55
  syntax_sort S56
  syntax_sort S57
  syntax_sort S58
  syntax_sort S59
  syntax_sort S60
  syntax_sort S61
  syntax_sort S62
  syntax_sort S63
  syntax_sort S64
  syntax_sort S65
  syntax_sort S66
  syntax_sort S67
  syntax_sort S68
  syntax_sort S69
  syntax_sort S70
  syntax_sort S71
  syntax_sort S72
  syntax_sort S73
  syntax_sort S74
  syntax_sort Code (A : Type u)

generate_model_interface ChunkLateUniverse as ChunkLateUniverseModel

/-- info: ChunkLateUniverse.ChunkLateUniverseModel.Code.{u}
  (self : ChunkLateUniverse.ChunkLateUniverseModel) (A : Type u) : Type -/
#guard_msgs (whitespace := lax) in
#check ChunkLateUniverse.ChunkLateUniverseModel.Code

declare_type_theory ChunkEarlyUniverse{u} where
  syntax_sort Code (A : Type u)
  syntax_sort S00
  syntax_sort S01
  syntax_sort S02
  syntax_sort S03
  syntax_sort S04
  syntax_sort S05
  syntax_sort S06
  syntax_sort S07
  syntax_sort S08
  syntax_sort S09
  syntax_sort S10
  syntax_sort S11
  syntax_sort S12
  syntax_sort S13
  syntax_sort S14
  syntax_sort S15
  syntax_sort S16
  syntax_sort S17
  syntax_sort S18
  syntax_sort S19
  syntax_sort S20
  syntax_sort S21
  syntax_sort S22
  syntax_sort S23
  syntax_sort S24
  syntax_sort S25
  syntax_sort S26
  syntax_sort S27
  syntax_sort S28
  syntax_sort S29
  syntax_sort S30
  syntax_sort S31
  syntax_sort S32
  syntax_sort S33
  syntax_sort S34
  syntax_sort S35
  syntax_sort S36
  syntax_sort S37
  syntax_sort S38
  syntax_sort S39
  syntax_sort S40
  syntax_sort S41
  syntax_sort S42
  syntax_sort S43
  syntax_sort S44
  syntax_sort S45
  syntax_sort S46
  syntax_sort S47
  syntax_sort S48
  syntax_sort S49
  syntax_sort S50
  syntax_sort S51
  syntax_sort S52
  syntax_sort S53
  syntax_sort S54
  syntax_sort S55
  syntax_sort S56
  syntax_sort S57
  syntax_sort S58
  syntax_sort S59
  syntax_sort S60
  syntax_sort S61
  syntax_sort S62
  syntax_sort S63
  syntax_sort S64
  syntax_sort S65
  syntax_sort S66
  syntax_sort S67
  syntax_sort S68
  syntax_sort S69
  syntax_sort S70
  syntax_sort S71
  syntax_sort S72
  syntax_sort S73
  syntax_sort S74

generate_model_interface ChunkEarlyUniverse as ChunkEarlyUniverseModel

/-- info: ChunkEarlyUniverse.ChunkEarlyUniverseModel.S74.{u}
  (self : ChunkEarlyUniverse.ChunkEarlyUniverseModel) : Type -/
#guard_msgs (whitespace := lax) in
#check ChunkEarlyUniverse.ChunkEarlyUniverseModel.S74
