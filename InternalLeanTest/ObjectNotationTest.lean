import InternalLean.Command

open InternalLean

declare_type_theory ObjectNotationSmoke where
  syntax_sort Ctx
  syntax_sort Ty
  syntax_sort Tm
  lf_opaque Star : Ty
  lf_opaque Arr (A : Ty) (x : Tm) (y : Tm) : Ty
  lf_opaque Γ0 : Ctx
  lf_opaque x0 : Tm
  lf_opaque y0 : Tm
  lf_opaque f0 : Tm
  judgment HasTy (Γ : Ctx) (t : Tm) (A : Ty)

object_notation ObjectNotationSmoke "[" A "]" x "⇛" y => Arr A x y

#print_object_notations ObjectNotationSmoke
#expand_object ObjectNotationSmoke [ Star ] x0 ⇛ y0

extend_type_theory ObjectNotationSmoke where
  lf_def HomTy : Ty := [ Star ] x0 ⇛ y0
  judgment_abbrev Obj (Γ : Ctx) (x : Tm) := HasTy Γ x Star
  judgment_abbrev Mor (Γ : Ctx) (x : Tm) (y : Tm) (f : Tm) :=
    HasTy Γ f ([ Star ] x ⇛ y)
  rule mk_mor where
    premise hx : Obj Γ0 x0
    conclusion : Mor Γ0 x0 y0 f0

#check_type_theory ObjectNotationSmoke
generate_lf_model_structure ObjectNotationSmoke as ObjectNotationModel

namespace ObjectNotationSmoke

#check ObjectNotationModel.mk_mor

end ObjectNotationSmoke

/--
error: unknown type theory 'MissingNotationTheory'
-/
#guard_msgs in
object_notation MissingNotationTheory "[" A "]" => A

/--
error: object_notation for type theory 'ObjectNotationSmoke' has duplicate hole 'A'
-/
#guard_msgs in
object_notation ObjectNotationSmoke "dupA" A A => A

/--
error: object_notation for type theory 'ObjectNotationSmoke' declares hole 'B', but the expansion
template does not use it
-/
#guard_msgs (whitespace := lax) in
object_notation ObjectNotationSmoke "dropB" A B => A

/--
error: object_notation pattern "[" A "]" x "⇛" y is already registered for type theory
'ObjectNotationSmoke'
-/
#guard_msgs (whitespace := lax) in
object_notation ObjectNotationSmoke "[" B "]" u "⇛" v => Arr B u v

/--
error: object_notation for type theory 'ObjectNotationSmoke' must start with a literal token;
notation patterns beginning with an expression hole need precedence support
-/
#guard_msgs (whitespace := lax) in
object_notation ObjectNotationSmoke A "post" => A
