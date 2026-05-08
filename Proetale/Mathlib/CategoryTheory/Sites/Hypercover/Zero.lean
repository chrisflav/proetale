import Mathlib.CategoryTheory.Sites.Hypercover.Zero

universe w

namespace CategoryTheory

@[simps]
def PreZeroHypercover.equivOfIso {C : Type*} [Category* C] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) :
    E.I₀ ≃ F.I₀ where
  toFun := e.hom.s₀
  invFun := e.inv.s₀
  left_inv _ := by simp
  right_inv _ := by simp

lemma PreZeroHypercover.mem_of_iso {C : Type*} [Category* C] {K : Precoverage C}
    [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F)
    (hE : E.presieve₀ ∈ K X) :
    F.presieve₀ ∈ K X := by
  have : F.presieve₀ =
      Presieve.ofArrows (fun (i : Σ (_ : F.I₀), Unit) ↦ _)
        (fun i ↦ e.inv.h₀ i.1 ≫ E.f _) := by
    simp [PreZeroHypercover.presieve₀]
    refine le_antisymm ?_ ?_
    · rw [Presieve.ofArrows_le_iff]
      intro i
      exact .mk (⟨i, ⟨⟩⟩ : Σ (_ : F.I₀), Unit)
    · rw [Presieve.ofArrows_le_iff]
      simp
  rw [this]
  refine K.comp_mem_coverings (fun i ↦ E.f (e.inv.s₀ i)) ?_ (fun i (k : Unit) ↦ e.inv.h₀ i) ?_
  · rwa [← E.presieve₀_reindex (PreZeroHypercover.equivOfIso e.symm)] at hE
  · intro i
    rw [Presieve.ofArrows_pUnit]
    exact K.mem_coverings_of_isIso _

lemma PreZeroHypercover.mem_iff_of_iso {C : Type*} [Category* C]
    {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) :
    E.presieve₀ ∈ K X ↔ F.presieve₀ ∈ K X :=
  ⟨fun h ↦ PreZeroHypercover.mem_of_iso e h, fun h ↦ PreZeroHypercover.mem_of_iso e.symm h⟩

end CategoryTheory
