import Mathlib.CategoryTheory.Sites.Sheafification

namespace CategoryTheory

/-- If `G : I ⥤ (Cᵒᵖ ⥤ A)` takes values in `J`-sheafs, the post-composition with
sheafification and inclusion is isomorphic to `G`. -/
noncomputable
def presheafToSheafSheafToPresheafIso {C I A : Type*} [Category* C]
    [Category* I] [Category* A] (J : GrothendieckTopology C) [HasWeakSheafify J A]
    (G : I ⥤ (Cᵒᵖ ⥤ A)) (H : ∀ (i : I), Presheaf.IsSheaf J (G.obj i)) :
    G ⋙ presheafToSheaf J A ⋙ sheafToPresheaf J A ≅ G :=
  NatIso.ofComponents (fun i ↦ (isoSheafify _ (H _)).symm) <| by
    intro i j u
    apply sheafify_hom_ext _ _ _ (H _)
    simp

end CategoryTheory
