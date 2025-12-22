import Mathlib.CategoryTheory.MorphismProperty.Comma

namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} (X : T) [Q.IsMultiplicative]

-- this is in mathlib on a later version
-- `also solvable by copilot`
instance (P : MorphismProperty T) [P.RespectsIso] (X : T) :
    (P.underObj (X := X)).IsClosedUnderIsomorphisms := by
  classical
  refine ⟨?_⟩
  intro A B e hA
  -- Postcompose `A.hom` with the isomorphism on the right component of `e.hom`.
  have h' : P (A.hom ≫ e.hom.right) :=
    MorphismProperty.RespectsIso.postcomp (P := P) (e := e.hom.right) (f := A.hom) hA
  -- In `Under X`, commutativity identifies this composite with `B.hom`.
  have hw : A.hom ≫ e.hom.right = B.hom := by
    simp only [Functor.const_obj_obj, Functor.id_obj, CategoryTheory.Under.w]
  -- Rewrite and conclude.
  simpa [hw] using h'

namespace Over

abbrev changeProp {P' Q' : MorphismProperty T} [Q'.IsMultiplicative] (hPP' : P ≤ P') (hQQ' : Q ≤ Q') :
    P.Over Q X ⥤ P'.Over Q' X :=
  Comma.changeProp _ _ hPP' hQQ' le_rfl

end Over

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

protected abbrev CostructuredArrow (P : MorphismProperty D) (Q : MorphismProperty C) (F : C ⥤ D) (X : D) :=
  P.Comma F (Functor.fromPUnit.{0} X) Q ⊤

namespace CostructuredArrow

variable {P F X} in
@[simps left hom]
protected def mk {A : C} (f : F.obj A ⟶ X) (hf : P f) : P.CostructuredArrow Q F X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

variable {P Q F X} in
@[simps left]
def homMk {A B : P.CostructuredArrow Q F X} (f : A.left ⟶ B.left) (hf : Q f)
    (w : F.map f ≫ B.hom = A.hom := by cat_disch) :
    A ⟶ B where
  left := f
  right := eqToHom (Subsingleton.elim _ _)
  prop_hom_left := hf
  prop_hom_right := trivial

variable {P Q F X} in
@[ext]
lemma Hom.ext {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B} (h : f.left = g.left) :
    f = g := by
  ext <;> simp [h]

protected abbrev forget :
    P.CostructuredArrow Q F X ⥤ CategoryTheory.CostructuredArrow F X :=
  Comma.forget _ _ _ _ _

@[simps]
protected def toOver :
    P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  obj Y := Over.mk _ Y.hom Y.prop
  map f := Over.homMk (F.map f.left) _

instance [F.Faithful] : (CostructuredArrow.toOver P F X).Faithful := by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

instance [F.Full] : (CostructuredArrow.toOver P F X).Full := by
  constructor
  intro A B f
  refine ⟨homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

end CostructuredArrow

end CategoryTheory.MorphismProperty
