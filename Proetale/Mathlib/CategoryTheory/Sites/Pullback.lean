import Mathlib.CategoryTheory.Sites.Pullback

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (A : Type*) [Category* A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]

@[simp]
lemma Functor.sheafPushforwardContinuous_map_hom {G G' : Sheaf K A} (f : G ⟶ G') :
    ((F.sheafPushforwardContinuous A J K).map f).hom = F.op.whiskerLeft f.hom :=
  rfl

variable [HasWeakSheafify K A] [∀ (G : Cᵒᵖ ⥤ A), F.op.HasLeftKanExtension G]

/-- If left Kan extensions along `F : C ⥤ D` exist and `D` has sheafification,
the sheaf pullback can be computed as the sheafification of the left Kan extension. -/
noncomputable
def Functor.sheafPullbackIso :
    F.sheafPullback A J K ≅ sheafToPresheaf J A ⋙ F.op.lan ⋙ presheafToSheaf K A :=
  Functor.sheafPullbackConstruction.sheafPullbackIso _ _ _ _

-- TODO: move
lemma sheafToPresheaf_map {F G : Sheaf J A} (f : F ⟶ G) :
    (sheafToPresheaf _ _).map f = f.hom := by
  simp

@[reassoc (attr := simp)]
lemma Functor.sheafAdjunctionContinuous_unit_app_hom_sheafPullbackIso_hom
    (G : Sheaf J A) :
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom ≫
      F.op.whiskerLeft ((F.sheafPullbackIso A J K).hom.app G).hom =
      (F.op.lanUnit.app G.obj) ≫
      F.op.whiskerLeft (toSheafify K (F.op.leftKanExtension G.obj)) := by
  dsimp [Functor.sheafPullbackIso, Functor.sheafPullbackConstruction.sheafPullbackIso]
  have := congr(($(Adjunction.unit_leftAdjointUniq_hom (F.sheafAdjunctionContinuous A J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)).app G).hom)
  dsimp at this
  rw [this]
  dsimp [sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.lan]

@[reassoc (attr := simp)]
lemma Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom
    (G : Sheaf J A) :
    F.op.lanUnit.app G.obj ≫
      F.op.whiskerLeft (toSheafify K (F.op.leftKanExtension G.obj)) ≫
      F.op.whiskerLeft ((F.sheafPullbackIso A J K).inv.app G).hom =
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom := by
  rw [← cancel_mono (F.op.whiskerLeft ((F.sheafPullbackIso A J K).hom.app G).hom)]
  simp [← Functor.whiskerLeft_comp, ← ObjectProperty.FullSubcategory.comp_hom,
    sheafify, Functor.lan]

@[reassoc (attr := simp)]
lemma Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom_app
    (G : Sheaf J A) (U : Cᵒᵖ) :
    dsimp% (F.op.lanUnit.app G.obj).app U ≫
      (toSheafify K (F.op.leftKanExtension G.obj)).app (Opposite.op (F.obj U.unop)) ≫
        ((F.sheafPullbackIso A J K).inv.app G).hom.app (Opposite.op (F.obj U.unop)) =
    ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app U := by
  rw [← Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom]
  rfl

end CategoryTheory
