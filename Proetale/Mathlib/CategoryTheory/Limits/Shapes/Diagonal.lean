import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Final

variable {C : Type*} [Category* C] {X Y : C}

namespace CategoryTheory.Limits

namespace pushout

variable {X Y : C} (f : X ⟶ Y) [HasPushout f f]

/-- The codiagonal object of a morphism `f : X ⟶ Y` is `pushout f f`. -/
noncomputable abbrev codiagonalObj : C :=
  pushout f f

/-- The codiagonal morphism `pushout f f ⟶ Y` for a morphism `f : X ⟶ Y`. -/
noncomputable def codiagonal : codiagonalObj f ⟶ Y :=
  pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]
theorem inl_codiagonal : pushout.inl _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_codiagonal : pushout.inr _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inr_desc _ _ _

end pushout

lemma hasColimit_op_iff_hasLimit {C : Type*} [Category* C] {J : Type*} [Category* J] {F : J ⥤ C} :
    HasColimit F.op ↔ HasLimit F :=
  ⟨fun _ ↦ hasLimit_of_hasColimit_op F, fun _ ↦ inferInstance⟩

lemma hasLimit_op_iff_hasColimit {C : Type*} [Category* C] {J : Type*} [Category* J] {F : J ⥤ C} :
    HasLimit F.op ↔ HasColimit F :=
  ⟨fun _ ↦ hasColimit_of_hasLimit_op F, fun _ ↦ inferInstance⟩

section Opposite

@[simp]
lemma hasPullback_op_iff_hasPushout {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    HasPullback f.op g.op ↔ HasPushout f g := by
  rw [HasPullback, hasLimit_iff_of_iso (cospanOp f g), Functor.Initial.hasLimit_comp_iff,
    hasLimit_op_iff_hasColimit]

@[simp]
lemma hasPushout_op_iff_hasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPushout f.op g.op ↔ HasPullback f g := by
  rw [HasPushout, hasColimit_iff_of_iso (spanOp f g), Functor.Final.hasColimit_comp_iff,
    hasColimit_op_iff_hasLimit]

instance {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] : HasPullback f.op g.op := by
  rwa [hasPullback_op_iff_hasPushout]

instance {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : HasPushout f.op g.op := by
  rwa [hasPushout_op_iff_hasPullback]

variable {X Y : C} (f : X ⟶ Y)

lemma op_codiagonal [HasPushout f f] [HasPushout f.op.unop f.op.unop] :
    (pushout.codiagonal f).op = pullback.diagonal f.op ≫
      (pullbackIsoOpPushout _ _).hom := by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

lemma op_pushoutMap {C : Type*} [Category* C]
    {W X Y Z S T : C} (f₁ : S ⟶ W) (f₂ : S ⟶ X)
    [HasPushout f₁ f₂] [HasPushout f₁.op.unop f₂.op.unop]
    (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout g₁ g₂]
    [HasPushout g₁.op.unop g₂.op.unop]
    (i₁ : W ⟶ Y)
    (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (eq₁ : f₁ ≫ i₁ = i₃ ≫ g₁)
    (eq₂ : f₂ ≫ i₂ = i₃ ≫ g₂) :
    (pushout.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂).op =
      (pullbackIsoOpPushout _ _).inv ≫
        pullback.map g₁.op g₂.op f₁.op f₂.op i₁.op i₂.op i₃.op
        (by simp [eq₁, ← op_comp]) (by simp [eq₂, ← op_comp]) ≫
        (pullbackIsoOpPushout _ _).hom := by
  rw [← Category.assoc, ← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

end Opposite

end Limits

open Limits

lemma IsPullback.op_iff {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P} :
    IsPullback inr.op inl.op g.op f.op ↔ IsPushout f g inl inr :=
  ⟨fun h ↦ h.unop, fun h ↦ h.op⟩

variable {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)
variable [HasPushouts C]

theorem isPushout_map_codiagonal :
    IsPushout
      (pushout.map i i (i ≫ f) (i ≫ g) f g (𝟙 _) (by simp) (by simp))
      (pushout.codiagonal i)
      (pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (by simp) (by simp))
      (f ≫ pushout.inl _ _) := by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by simp [← Iso.inv_comp_eq]) (by simp) (by simp) (by simp)

open pushout

open pushout

end CategoryTheory
