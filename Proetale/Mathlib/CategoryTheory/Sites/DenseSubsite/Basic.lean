import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

namespace CategoryTheory

namespace Functor.IsDenseSubsite

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) (A : Type*) [Category* A] [IsDenseSubsite J K G]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify _ _ ≫ ((sheafEquivSheafificationCompatibility J K G A).hom.app F).hom =
      Functor.whiskerLeft G.op (toSheafify _ _) := by
  simp [sheafEquivSheafificationCompatibility]
  sorry

end Functor.IsDenseSubsite

end CategoryTheory
