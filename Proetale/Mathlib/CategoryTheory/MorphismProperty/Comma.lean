import Mathlib.CategoryTheory.MorphismProperty.Comma

namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} (X : T) [Q.IsMultiplicative]

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

section Opposite

variable {A B T : Type*} [Category A] [Category B] [Category T]
  (L : A ⥤ T) (R : B ⥤ T)
  (P : MorphismProperty T) (Q : MorphismProperty A) (W : MorphismProperty B)
  [Q.IsMultiplicative]
  [W.IsMultiplicative]

@[simps]
def Comma.opEquiv : P.Comma L R Q W ≌ (P.op.Comma R.op L.op W.op Q.op)ᵒᵖ where
  functor :=
    .rightOp <| lift (.leftOp <| forget _ _ _ _ _ ⋙ CategoryTheory.Comma.opFunctor L R)
      (fun X ↦ X.unop.prop) (fun f ↦ f.unop.prop_hom_right) (fun f ↦ f.unop.prop_hom_left)
  inverse :=
    lift ((forget _ _ _ _ _).op ⋙ .leftOp (CategoryTheory.Comma.unopFunctor R L))
      (fun X ↦ X.unop.prop) (fun f ↦ f.unop.prop_hom_right) (fun f ↦ f.unop.prop_hom_left)
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

section

variable {P}
variable {Q : MorphismProperty T} [Q.IsMultiplicative]
variable {C : Type*} [Category C]

def Over.lift {X : T} (F : C ⥤ Over X) (obj : ∀ Y, P (F.obj Y).hom)
    (map : ∀ {Y Z : C} (f : Y ⟶ Z), Q (F.map f).left) : C ⥤ P.Over Q X where
  obj Y := ⟨F.obj Y, obj Y⟩
  map f := ⟨F.map f, map f, trivial⟩

def Under.lift {X : T} (F : C ⥤ Under X) (obj : ∀ Y, P (F.obj Y).hom)
    (map : ∀ {Y Z : C} (f : Y ⟶ Z), Q (F.map f).right) : C ⥤ P.Under Q X where
  obj Y := ⟨F.obj Y, obj Y⟩
  map f := ⟨F.map f, trivial, map f⟩

end

@[simps! functor_obj_unop_right functor_map_unop_right inverse_obj_left inverse_map_left]
def Over.equivOpUnderOp (Q : MorphismProperty T) [Q.IsMultiplicative] (X : T) :
    P.Over Q X ≌ (P.op.Under Q.op (Opposite.op X))ᵒᵖ where
  functor := .rightOp <| Under.lift
    (.leftOp <| Over.forget _ _ _ ⋙ (CategoryTheory.Under.opEquivOpOver X).inverse.rightOp)
      (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_left)
  inverse := Over.lift
    (.leftOp <| Under.forget _ _ _ ⋙ (CategoryTheory.Under.opEquivOpOver X).functor)
    (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_right)
  unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _

@[simps! functor_obj_unop_left functor_map_unop_left inverse_obj_right inverse_map_right]
def Under.equivOpOverOp (Q : MorphismProperty T) [Q.IsMultiplicative] (X : T) :
    P.Under Q X ≌ (P.op.Over Q.op (Opposite.op X))ᵒᵖ where
  functor := .rightOp <| Over.lift
    (.leftOp <| Under.forget _ _ _ ⋙ (CategoryTheory.Over.opEquivOpUnder X).inverse.rightOp)
    (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_right)
  inverse := Under.lift
    (.leftOp <| Over.forget _ _ _ ⋙ (CategoryTheory.Over.opEquivOpUnder X).functor)
    (fun Y ↦ Y.unop.prop) (fun f ↦ f.unop.prop_hom_left)
  unitIso := NatIso.ofComponents fun _ ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun _ ↦ Iso.refl _

end Opposite

end CategoryTheory.MorphismProperty
