/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import InternalLean.Command

/-!
# Synthetic LF model-generator stress test

This fixture is intentionally synthetic. It preserves large-interface coverage so
source-facing examples can stay smaller and more user-friendly without losing regression pressure
on chunked generated structures, inherited projections, side-condition certificate plumbing, and
generated LF theorem methods.
-/

@[expose] public section

/-- Synthetic large LF signature used only for model-generator stress coverage. -/
declare_type_theory SyntheticLFModelStress where
  /-- Synthetic stress sort 00. -/
  syntax_sort S00
  /-- Synthetic stress sort 01. -/
  syntax_sort S01
  /-- Synthetic stress sort 02. -/
  syntax_sort S02
  /-- Synthetic stress sort 03. -/
  syntax_sort S03
  /-- Synthetic stress sort 04. -/
  syntax_sort S04
  /-- Synthetic stress sort 05. -/
  syntax_sort S05
  /-- Synthetic stress sort 06. -/
  syntax_sort S06
  /-- Synthetic stress sort 07. -/
  syntax_sort S07
  /-- Synthetic stress sort 08. -/
  syntax_sort S08
  /-- Synthetic stress sort 09. -/
  syntax_sort S09
  /-- Synthetic stress sort 10. -/
  syntax_sort S10
  /-- Synthetic stress sort 11. -/
  syntax_sort S11
  /-- Synthetic stress sort 12. -/
  syntax_sort S12
  /-- Synthetic stress sort 13. -/
  syntax_sort S13
  /-- Synthetic stress sort 14. -/
  syntax_sort S14
  /-- Synthetic stress sort 15. -/
  syntax_sort S15
  /-- Synthetic stress sort 16. -/
  syntax_sort S16
  /-- Synthetic stress sort 17. -/
  syntax_sort S17
  /-- Synthetic stress sort 18. -/
  syntax_sort S18
  /-- Synthetic stress sort 19. -/
  syntax_sort S19
  /-- Synthetic stress sort 20. -/
  syntax_sort S20
  /-- Synthetic stress sort 21. -/
  syntax_sort S21
  /-- Synthetic stress sort 22. -/
  syntax_sort S22
  /-- Synthetic stress sort 23. -/
  syntax_sort S23
  /-- Synthetic stress sort 24. -/
  syntax_sort S24
  /-- Synthetic stress sort 25. -/
  syntax_sort S25
  /-- Synthetic stress sort 26. -/
  syntax_sort S26
  /-- Synthetic stress sort 27. -/
  syntax_sort S27
  /-- Synthetic stress sort 28. -/
  syntax_sort S28
  /-- Synthetic stress sort 29. -/
  syntax_sort S29
  /-- Synthetic stress sort 30. -/
  syntax_sort S30
  /-- Synthetic stress sort 31. -/
  syntax_sort S31
  /-- Synthetic stress sort 32. -/
  syntax_sort S32
  /-- Synthetic stress sort 33. -/
  syntax_sort S33
  /-- Synthetic stress sort 34. -/
  syntax_sort S34
  /-- Synthetic stress sort 35. -/
  syntax_sort S35
  /-- Synthetic stress sort 36. -/
  syntax_sort S36
  /-- Synthetic stress sort 37. -/
  syntax_sort S37
  /-- Synthetic stress sort 38. -/
  syntax_sort S38
  /-- Synthetic stress sort 39. -/
  syntax_sort S39
  /-- Synthetic stress sort 40. -/
  syntax_sort S40
  /-- Synthetic stress sort 41. -/
  syntax_sort S41
  /-- Synthetic stress sort 42. -/
  syntax_sort S42
  /-- Synthetic stress sort 43. -/
  syntax_sort S43
  /-- Synthetic stress sort 44. -/
  syntax_sort S44
  /-- Synthetic stress sort 45. -/
  syntax_sort S45
  /-- Synthetic stress sort 46. -/
  syntax_sort S46
  /-- Synthetic stress sort 47. -/
  syntax_sort S47
  /-- Synthetic stress sort 48. -/
  syntax_sort S48
  /-- Synthetic stress sort 49. -/
  syntax_sort S49
  /-- Synthetic stress sort 50. -/
  syntax_sort S50
  /-- Synthetic stress sort 51. -/
  syntax_sort S51
  /-- Synthetic stress sort 52. -/
  syntax_sort S52
  /-- Synthetic stress sort 53. -/
  syntax_sort S53
  /-- Synthetic stress sort 54. -/
  syntax_sort S54
  /-- Synthetic stress sort 55. -/
  syntax_sort S55
  /-- Synthetic stress sort 56. -/
  syntax_sort S56
  /-- Synthetic stress sort 57. -/
  syntax_sort S57
  /-- Synthetic stress sort 58. -/
  syntax_sort S58
  /-- Synthetic stress sort 59. -/
  syntax_sort S59
  /-- Synthetic stress sort 60. -/
  syntax_sort S60
  /-- Synthetic stress sort 61. -/
  syntax_sort S61
  /-- Synthetic stress sort 62. -/
  syntax_sort S62
  /-- Synthetic stress sort 63. -/
  syntax_sort S63
  /-- Synthetic stress sort 64. -/
  syntax_sort S64
  /-- Synthetic stress sort 65. -/
  syntax_sort S65
  /-- Synthetic stress sort 66. -/
  syntax_sort S66
  /-- Synthetic stress sort 67. -/
  syntax_sort S67
  /-- Synthetic stress sort 68. -/
  syntax_sort S68
  /-- Synthetic stress sort 69. -/
  syntax_sort S69
  /-- Synthetic stress sort 70. -/
  syntax_sort S70
  /-- Synthetic stress sort 71. -/
  syntax_sort S71
  /-- Synthetic stress sort 72. -/
  syntax_sort S72
  /-- Synthetic stress sort 73. -/
  syntax_sort S73
  /-- Synthetic stress sort 74. -/
  syntax_sort S74
  /-- Synthetic stress sort 75. -/
  syntax_sort S75
  /-- Synthetic stress sort 76. -/
  syntax_sort S76
  /-- Synthetic stress sort 77. -/
  syntax_sort S77
  /-- Synthetic stress sort 78. -/
  syntax_sort S78
  /-- Synthetic stress sort 79. -/
  syntax_sort S79
  /-- Synthetic stress sort 80. -/
  syntax_sort S80
  /-- Synthetic stress sort 81. -/
  syntax_sort S81
  /-- Synthetic stress sort 82. -/
  syntax_sort S82
  /-- Synthetic stress sort 83. -/
  syntax_sort S83
  /-- Synthetic stress sort 84. -/
  syntax_sort S84
  /-- Shared synthetic side-condition solver. -/
  side_condition_solver stress_cert
  /-- Synthetic stress judgment 00. -/
  judgment Ok00 (x : S00)
  /-- Synthetic stress judgment 01. -/
  judgment Ok01 (x : S01)
  /-- Synthetic stress judgment 02. -/
  judgment Ok02 (x : S02)
  /-- Synthetic stress judgment 03. -/
  judgment Ok03 (x : S03)
  /-- Synthetic stress judgment 04. -/
  judgment Ok04 (x : S04)
  /-- Synthetic stress judgment 05. -/
  judgment Ok05 (x : S05)
  /-- Synthetic stress judgment 06. -/
  judgment Ok06 (x : S06)
  /-- Synthetic stress judgment 07. -/
  judgment Ok07 (x : S07)
  /-- Synthetic stress judgment 08. -/
  judgment Ok08 (x : S08)
  /-- Synthetic stress judgment 09. -/
  judgment Ok09 (x : S09)
  /-- Synthetic distinguished object 00. -/
  lf_opaque c00 : S00
  /-- Synthetic distinguished object 01. -/
  lf_opaque c01 : S01
  /-- Synthetic distinguished object 02. -/
  lf_opaque c02 : S02
  /-- Synthetic distinguished object 03. -/
  lf_opaque c03 : S03
  /-- Synthetic distinguished object 04. -/
  lf_opaque c04 : S04
  /-- Synthetic distinguished object 05. -/
  lf_opaque c05 : S05
  /-- Synthetic distinguished object 06. -/
  lf_opaque c06 : S06
  /-- Synthetic distinguished object 07. -/
  lf_opaque c07 : S07
  /-- Synthetic distinguished object 08. -/
  lf_opaque c08 : S08
  /-- Synthetic distinguished object 09. -/
  lf_opaque c09 : S09
  /-- Synthetic side-condition predicate head 00. -/
  lf_opaque Needs00 / 1
  /-- Synthetic side-condition predicate head 01. -/
  lf_opaque Needs01 / 1
  /-- Synthetic side-condition predicate head 02. -/
  lf_opaque Needs02 / 1
  /-- Synthetic certified rule 00. -/
  rule ok00_intro (x : S00) where
    side_condition cert by stress_cert : Needs00 x
    conclusion : Ok00 x
  /-- Synthetic certified rule 01. -/
  rule ok01_intro (x : S01) where
    side_condition cert by stress_cert : Needs01 x
    conclusion : Ok01 x
  /-- Synthetic certified rule 02. -/
  rule ok02_intro (x : S02) where
    side_condition cert by stress_cert : Needs02 x
    conclusion : Ok02 x
  /-- Synthetic ordinary rule 03. -/
  rule ok03_intro (x : S03) : Ok03 x
  /-- Synthetic ordinary rule 04. -/
  rule ok04_intro (x : S04) : Ok04 x
  /-- Synthetic ordinary rule 05. -/
  rule ok05_intro (x : S05) : Ok05 x
  /-- Synthetic ordinary rule 06. -/
  rule ok06_intro (x : S06) : Ok06 x
  /-- Synthetic ordinary rule 07. -/
  rule ok07_intro (x : S07) : Ok07 x
  /-- Synthetic ordinary rule 08. -/
  rule ok08_intro (x : S08) : Ok08 x
  /-- Synthetic ordinary rule 09. -/
  rule ok09_intro (x : S09) : Ok09 x
  /-- Synthetic checked LF definition 00. -/
  lf_def alias00 : S00 := c00
  /-- Synthetic checked LF definition 01. -/
  lf_def alias01 : S01 := c01
  /-- Synthetic checked LF definition 02. -/
  lf_def alias02 : S02 := c02
  /-- Synthetic checked LF definition 03. -/
  lf_def alias03 : S03 := c03
  /-- Synthetic checked LF definition 04. -/
  lf_def alias04 : S04 := c04
  /-- Synthetic checked LF definition 05. -/
  lf_def alias05 : S05 := c05
  /-- Synthetic checked LF definition 06. -/
  lf_def alias06 : S06 := c06
  /-- Synthetic checked LF definition 07. -/
  lf_def alias07 : S07 := c07
  /-- Synthetic checked LF definition 08. -/
  lf_def alias08 : S08 := c08
  /-- Synthetic checked LF definition 09. -/
  lf_def alias09 : S09 := c09
  /-- Synthetic checked LF theorem 03. -/
  judgment_theorem ok03_checked : Ok03 alias03 := ok03_intro alias03
  /-- Synthetic checked LF theorem 04. -/
  judgment_theorem ok04_checked : Ok04 alias04 := ok04_intro alias04
  /-- Synthetic checked LF theorem 05. -/
  judgment_theorem ok05_checked : Ok05 alias05 := ok05_intro alias05
  /-- Synthetic checked LF theorem 06. -/
  judgment_theorem ok06_checked : Ok06 alias06 := ok06_intro alias06
  /-- Synthetic checked LF theorem 07. -/
  judgment_theorem ok07_checked : Ok07 alias07 := ok07_intro alias07
  /-- Synthetic checked LF theorem 08. -/
  judgment_theorem ok08_checked : Ok08 alias08 := ok08_intro alias08
  /-- Synthetic checked LF theorem 09. -/
  judgment_theorem ok09_checked : Ok09 alias09 := ok09_intro alias09

#check_model_obligations SyntheticLFModelStress
#print_lf_model_summary SyntheticLFModelStress
#check_lf_model_obligations SyntheticLFModelStress
generate_model_interface SyntheticLFModelStress as SyntheticStressModel

-- The synthetic stress interface is large enough to use chunked generated structures.
#check SyntheticLFModelStress.SyntheticStressModel
#check SyntheticLFModelStress.SyntheticStressModel.S00
#check SyntheticLFModelStress.SyntheticStressModel.S84
#check SyntheticLFModelStress.SyntheticStressModel.Ok09
#check SyntheticLFModelStress.SyntheticStressModel.ok09_intro

-- Inherited projections from chunk parents remain available through dot notation.
#check (fun M : SyntheticLFModelStress.SyntheticStressModel => M.S00)
#check (fun M : SyntheticLFModelStress.SyntheticStressModel => M.S84)
#check (fun M : SyntheticLFModelStress.SyntheticStressModel => M.ok09_intro)

#print_model_transport_status SyntheticLFModelStress for SyntheticStressModel
#print_lf_model_transports SyntheticLFModelStress for SyntheticStressModel
generate_lf_model_transports SyntheticLFModelStress for SyntheticStressModel

#check SyntheticLFModelStress.SyntheticStressModel.alias00
#check SyntheticLFModelStress.SyntheticStressModel.alias09
#check SyntheticLFModelStress.SyntheticStressModel.ok03_checked
#check SyntheticLFModelStress.SyntheticStressModel.ok09_checked
#check (fun M : SyntheticLFModelStress.SyntheticStressModel => M.alias09)
#check (fun M : SyntheticLFModelStress.SyntheticStressModel => M.ok09_checked)

