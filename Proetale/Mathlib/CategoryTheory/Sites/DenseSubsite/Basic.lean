import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) (A : Type*) [Category* A]

lemma IsCoverDense.restrictHomEquivHom_symm_apply [G.IsCoverDense K]
    [G.IsLocallyFull K] {F : Dᵒᵖ ⥤ A} {F' : Sheaf K A}
    (f : F ⟶ F'.obj) :
    restrictHomEquivHom (G := G).symm f = G.op.whiskerLeft f :=
  rfl

namespace IsDenseSubsite

variable [IsDenseSubsite J K G]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence]
  [HasWeakSheafify J A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafifyOfIsEquivalenceCompIso_inv_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify J (G.op ⋙ F) ≫
      ((sheafifyOfIsEquivalenceCompIso J K G A).inv.app F).hom =
      G.op.whiskerLeft ((sheafifyAdjunctionOfIsEquivalence _ _ _ _).unit.app _) := by
  have := isLocallyFull J K G
  have := isCoverDense J K G
  simp only [sheafifyOfIsEquivalenceCompIso, isoWhiskerLeft_trans, isoWhiskerLeft_twice,
    Iso.trans_assoc, Iso.trans_inv, isoWhiskerLeft_inv, Category.assoc, Iso.symm_inv,
    NatTrans.comp_app, comp_obj, whiskeringLeft_obj_obj, id_obj, whiskerLeft_app,
    rightUnitor_inv_app, associator_inv_app, associator_hom_app, Category.comp_id, Category.id_comp,
    sheafifyAdjunctionOfIsEquivalence, sheafifyHomEquivOfIsEquivalence, Equivalence.symm_functor,
    Equivalence.symm_inverse, asEquivalence_functor, ObjectProperty.ι_obj,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply]
  rw [← IsCoverDense.restrictHomEquivHom_symm_apply]
  erw [Equiv.symm_apply_apply]
  erw [CategoryTheory.Adjunction.homEquiv_id]
  rw [toSheafify]
  simp [Adjunction.homEquiv]

variable [HasWeakSheafify K A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify _ _ ≫ ((sheafEquivSheafificationCompatibility J K G A).hom.app F).hom =
      Functor.whiskerLeft G.op (toSheafify _ _) := by
  have := congr($(Adjunction.unit_leftAdjointUniq_hom (sheafifyAdjunctionOfIsEquivalence J K G A)
    (sheafificationAdjunction K A)).app F)
  simp [sheafPushforwardContinuous, sheafEquivSheafificationCompatibility,
    ← whiskerLeft_comp, dsimp% this]

end Functor.IsDenseSubsite

end CategoryTheory
