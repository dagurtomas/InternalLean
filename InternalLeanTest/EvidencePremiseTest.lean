import InternalLean.Command

open InternalLean

declare_type_theory EvidencePremiseForallSmoke where
  syntax_sort Obj
  judgment P (x : Obj)
  judgment Q
  rule allP_to_Q where
    premise h : (x : Obj) → P x
    conclusion : Q
  judgment_theorem use_allP (h : (x : Obj) → P x) : Q := allP_to_Q h
  judgment_theorem use_allP_ref (h : (x : Obj) → P x) : Q := use_allP h

#check_type_theory EvidencePremiseForallSmoke
#print_checked_logical_framework_rules EvidencePremiseForallSmoke
#print_logical_framework_rule_schemas EvidencePremiseForallSmoke
generate_lf_model_structure EvidencePremiseForallSmoke as EvidencePremiseForallModel
#check_lf_model_derived_theorems EvidencePremiseForallSmoke for EvidencePremiseForallModel
generate_lf_model_derived_theorems EvidencePremiseForallSmoke for EvidencePremiseForallModel

namespace EvidencePremiseForallSmoke

#check EvidencePremiseForallModel.use_allP_ref

end EvidencePremiseForallSmoke

declare_type_theory EvidencePremiseIffPackageSmoke where
  syntax_sort Obj
  judgment A (x : Obj)
  judgment B (x : Obj)
  judgment R
  rule iff_to_R where
    premise h : (x : Obj) → ((A x → B x) × (B x → A x))
    conclusion : R
  judgment_theorem use_iff
      (h : (x : Obj) → ((A x → B x) × (B x → A x))) : R :=
    iff_to_R h

#check_type_theory EvidencePremiseIffPackageSmoke
generate_lf_model_structure EvidencePremiseIffPackageSmoke as EvidencePremiseIffModel
#check EvidencePremiseIffPackageSmoke.EvidencePremiseIffModel.iff_to_R

declare_type_theory EvidencePremiseNullaryPackageSmoke where
  judgment B
  judgment C
  rule mkB where
    conclusion : B
  rule pairB_to_C where
    premise h : B × B
    conclusion : C
  judgment_theorem use_pair : C := pairB_to_C ⟨mkB, mkB⟩

#check_type_theory EvidencePremiseNullaryPackageSmoke

declare_type_theory EvidencePremiseLambdaSmoke where
  syntax_sort Obj
  judgment A (x : Obj)
  judgment B (x : Obj)
  judgment R
  rule A_to_B (x : Obj) where
    premise h : A x
    conclusion : B x
  rule allB_to_R where
    premise h : (x : Obj) → B x
    conclusion : R
  judgment_theorem use_lambda (h : (x : Obj) → A x) : R :=
    allB_to_R (fun x => A_to_B x (h x))

#check_type_theory EvidencePremiseLambdaSmoke
generate_lf_model_structure EvidencePremiseLambdaSmoke as EvidencePremiseLambdaModel
#print_lf_model_derived_theorems EvidencePremiseLambdaSmoke for EvidencePremiseLambdaModel
#check_lf_model_derived_theorems EvidencePremiseLambdaSmoke for EvidencePremiseLambdaModel
generate_lf_model_derived_theorems EvidencePremiseLambdaSmoke for EvidencePremiseLambdaModel

namespace EvidencePremiseLambdaSmoke

#check EvidencePremiseLambdaModel.use_lambda

end EvidencePremiseLambdaSmoke

/--
error: rule 'bad' in type theory 'BadEvidencePremiseTermShape' has premise 'h' as term-shaped
expression '⟨base, base⟩', expected an LF type/evidence expression
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadEvidencePremiseTermShape where
  syntax_sort Obj
  lf_opaque base : Obj
  judgment Q
  rule bad where
    premise h : ⟨base, base⟩
    conclusion : Q

/--
error: judgment_theorem 'bad' in type theory 'BadEvidencePremiseNestedProofArgument' has proof
argument for rule 'pairB_to_C' evidence premise 'h' argument
'⟨allA_to_B (fun x => x), allA_to_B (fun x => x)⟩' for proof constant 'allA_to_B'
parameter 'h' with type 'Obj', expected 'A x'
-/
#guard_msgs (whitespace := lax) in
declare_type_theory BadEvidencePremiseNestedProofArgument where
  syntax_sort Obj
  judgment A (x : Obj)
  judgment B
  judgment C
  rule allA_to_B where
    premise h : (x : Obj) → A x
    conclusion : B
  rule pairB_to_C where
    premise h : B × B
    conclusion : C
  judgment_theorem bad : C :=
    pairB_to_C ⟨allA_to_B (fun x => x), allA_to_B (fun x => x)⟩
