import Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

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

@[simps]
def Comma.preLeft {A : Type*} [Category* A] {B : Type*}
    [Category* B] {T : Type*} [Category* T] {C : Type*} [Category* C] (F : C ⥤ A) (L : A ⥤ T)
    (R : B ⥤ T) {P P' : MorphismProperty T} {Q : MorphismProperty C} [Q.IsMultiplicative]
    {Q' : MorphismProperty A} [Q'.IsMultiplicative] (W : MorphismProperty B) [W.IsMultiplicative]
    (h : P ⊓ .ofObjectProperty (F ⋙ L).essImage ⊤ ≤ P') (h' : Q ≤ Q'.inverseImage F) :
    P.Comma (F ⋙ L) R Q W ⥤ P'.Comma L R Q' W where
  obj X :=
    { left := F.obj X.left
      right := X.right
      hom := X.hom
      prop := h _ ⟨X.prop, by
        simp only [ofObjectProperty_top_right_iff]; apply Functor.obj_mem_essImage⟩ }
  map f :=
    { left := F.map f.left
      right := f.right
      w := by simpa using f.w
      prop_hom_left := h' _ f.prop_hom_left
      prop_hom_right := f.prop_hom_right }

@[simps!]
def CostructuredArrow.pre
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    (X : E)
    {P P' : MorphismProperty E}
    (h : P ⊓ .ofObjectProperty (F ⋙ G).essImage ⊤ ≤ P')
    {Q : MorphismProperty C} [Q.IsMultiplicative]
    {Q' : MorphismProperty D} [Q'.IsMultiplicative]
    (h' : Q ≤ Q'.inverseImage F) :
    P.CostructuredArrow Q (F ⋙ G) X ⥤ P'.CostructuredArrow Q' G X :=
  MorphismProperty.Comma.preLeft _ _ _ _ h h'

@[simps]
def Comma.equivOfEqTop {A B T : Type*} [Category* A]
    [Category* B] [Category* T] (L : A ⥤ T) (R : B ⥤ T)
    {P : MorphismProperty T} {Q : MorphismProperty A} {W : MorphismProperty B}
    [Q.IsMultiplicative] [W.IsMultiplicative]
    (hP : P = ⊤ := by rfl) (hQ : Q = ⊤ := by rfl) (hW : W = ⊤ := by rfl) :
    P.Comma L R Q W ≌ Comma L R where
  functor := MorphismProperty.Comma.forget _ _ _ _ _
  inverse := MorphismProperty.Comma.lift (𝟭 _) (by simp [hP]) (by simp [hQ]) (by simp [hW])
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def Over.iteratedSliceEquiv {C : Type*} [Category* C]
    {P : MorphismProperty C} [P.IsStableUnderComposition] {X : C} (A : P.Over ⊤ X) :
    MorphismProperty.Over
      (P.inverseImage <| MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _) ⊤ A ≌
      P.Over ⊤ A.left where
  functor.obj U := .mk _ U.hom.left U.prop
  functor.map {U V} f :=
    MorphismProperty.Over.homMk f.left.left (by dsimp; rw [← Over.w f]; rfl) trivial
  inverse.obj U := .mk _
    (MorphismProperty.Over.homMk (A := .mk _ (U.hom ≫ A.hom)
      (P.comp_mem _ _ U.prop A.prop)) U.hom (by simp) trivial) (by simp [U.prop])
  inverse.map f :=
    MorphismProperty.Over.homMk (MorphismProperty.Over.homMk f.left (by simp) trivial)
      (by ext; simp) trivial
  -- We don't use `cat_disch` to improve performance.
  unitIso := NatIso.ofComponents (fun U ↦ Over.isoMk (Over.isoMk (Iso.refl _)) (by ext; simp))
    (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun U ↦ Over.isoMk (Iso.refl _))
    (by intros; ext; simp)
  functor_unitIso_comp U := by ext; simp

end CategoryTheory.MorphismProperty
