import Mathlib.CategoryTheory.MorphismProperty.Comma

namespace CategoryTheory.MorphismProperty

variable {T : Type*} [Category T] {P Q : MorphismProperty T} (X : T) [Q.IsMultiplicative]

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

section

variable {A : Type*} [Category A]
  {B : Type*} [Category B] {T : Type*} [Category T] {L L₁ L₂ L₃ : A ⥤ T} {P : MorphismProperty T}
  {Q : MorphismProperty A} {W : MorphismProperty B} [Q.IsMultiplicative] [W.IsMultiplicative]
  {R R₁ R₂ R₃ : B ⥤ T}

variable (L)

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps!]
def Comma.mapRightId [Q.RespectsIso] [W.RespectsIso] :
    mapRight (P := P) (Q := Q) (W := W) L (𝟙 R) (fun X ↦ by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps!]
def Comma.mapRightComp [Q.RespectsIso] [W.RespectsIso] (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃)
    (hr : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right))
    (hr' : ∀ (X : P.Comma L R₂ Q W), P (X.hom ≫ r'.app X.right))
    (hrr' : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ (r ≫ r').app X.right)) :
    mapRight (P := P) (Q := Q) (W := W) L (r ≫ r') hrr' ≅
      mapRight L r hr ⋙ mapRight L r' hr' :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
    `Comma L R₁ ⥤ Comma L R₂`. -/
@[simps!]
def Comma.mapRightEq [Q.RespectsIso] [W.RespectsIso] (r r' : R₁ ⟶ R₂) (h : r = r')
    (hr : ∀ (X : P.Comma L R₁ Q W), P (X.hom ≫ r.app X.right)) :
    mapRight L r hr ≅ mapRight L r' (h ▸ hr) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (Iso.refl _))

def Comma.mapRightIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : R₁ ≅ R₂) :
    P.Comma L R₁ Q W ≌ P.Comma L R₂ Q W where
  functor := Comma.mapRight L e.hom (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapRight L e.inv (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapRightId _).symm ≪≫
    mapRightEq _ _ _ e.hom_inv_id.symm (fun X ↦ by simpa using X.prop) ≪≫
    mapRightComp _ _ _
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapRightComp _ _ _
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapRightEq _ _ _ e.inv_hom_id
      (fun X ↦ (P.cancel_right_of_respectsIso _ _).mpr X.prop) ≪≫
    mapRightId _

variable {L} (R)

/-- The functor `Comma L R ⥤ Comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simps!]
def Comma.mapLeftId [Q.RespectsIso] [W.RespectsIso] :
    mapLeft (P := P) (Q := Q) (W := W) R (𝟙 L) (fun X ↦ by simpa using X.prop) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _) (Iso.refl _))

/-- The functor `Comma L R₁ ⥤ Comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simps!]
def Comma.mapLeftComp [Q.RespectsIso] [W.RespectsIso] (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃)
    (hl : ∀ (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom))
    (hl' : ∀ (X : P.Comma L₃ R Q W), P (l'.app X.left ≫ X.hom))
    (hll' : ∀ (X : P.Comma L₃ R Q W), P ((l ≫ l').app X.left ≫ X.hom)) :
    mapLeft (P := P) (Q := Q) (W := W) R (l ≫ l') hll' ≅
      mapLeft R l' hl' ⋙ mapLeft R l hl :=
  NatIso.ofComponents (fun _ ↦ isoMk (Iso.refl _) (Iso.refl _))

/-- Two equal natural transformations `R₁ ⟶ R₂` yield naturally isomorphic functors
    `Comma L R₁ ⥤ Comma L R₂`. -/
@[simps!]
def Comma.mapLeftEq [Q.RespectsIso] [W.RespectsIso] (l l' : L₁ ⟶ L₂) (h : l = l')
    (hl : ∀ (X : P.Comma L₂ R Q W), P (l.app X.left ≫ X.hom)) :
    mapLeft R l hl ≅ mapLeft R l' (h ▸ hl) :=
  NatIso.ofComponents fun _ ↦ isoMk (Iso.refl _) (Iso.refl _)

@[simps!]
def Comma.mapLeftIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
      (e : L₁ ≅ L₂) :
    P.Comma L₁ R Q W ≌ P.Comma L₂ R Q W where
  functor := Comma.mapLeft R e.inv (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  inverse := Comma.mapLeft R e.hom (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  unitIso := (mapLeftId _).symm ≪≫
    mapLeftEq _ _ _ e.hom_inv_id.symm (fun X ↦ by simpa using X.prop) ≪≫
    mapLeftComp _ _ _
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
  counitIso :=
    (mapLeftComp _ _ _
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop)).symm ≪≫
    mapLeftEq _ _ _ e.inv_hom_id
      (fun X ↦ (P.cancel_left_of_respectsIso _ _).mpr X.prop) ≪≫
    mapLeftId _

@[simps!]
def Comma.mapIso [P.RespectsIso] [Q.RespectsIso] [W.RespectsIso]
    (eL : L₁ ≅ L₂) (eR : R₁ ≅ R₂) :
    P.Comma L₁ R₁ Q W ≌ P.Comma L₂ R₂ Q W :=
  (Comma.mapLeftIso _ eL).trans (Comma.mapRightIso _ eR)

end

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
