import Mathlib.CategoryTheory.Filtered.Basic

namespace CategoryTheory.IsCofiltered

variable {C : Type*} [Category* C] [IsCofilteredOrEmpty C]

lemma crown {ι : Type*} [Finite ι] (j : ι → C)
    {k₁ k₂ : C} (f : ∀ i, k₁ ⟶ j i) (g : ∀ i, k₂ ⟶ j i) :
    ∃ (s : C) (α : s ⟶ k₁) (β : s ⟶ k₂), ∀ i, α ≫ f i = β ≫ g i := by
  obtain ⟨s, α, β, h⟩ := IsFiltered.crown _ (fun i ↦ (f i).op) (fun i ↦ (g i).op)
  use s.unop, α.unop, β.unop
  intro i
  simpa using congr($(h i).unop)

lemma crown₃ {j₁ j₂ j₃ k₁ k₂ : C} (f₁ : k₁ ⟶ j₁) (g₁ : k₂ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (g₂ : k₂ ⟶ j₂)
    (f₃ : k₁ ⟶ j₃) (g₃ : k₂ ⟶ j₃) :
    ∃ (s : C) (α : s ⟶ k₁) (β : s ⟶ k₂), α ≫ f₁ = β ≫ g₁ ∧ α ≫ f₂ = β ≫ g₂ ∧ α ≫ f₃ = β ≫ g₃ := by
  obtain ⟨s, α, β, H⟩ := crown ![j₁, j₂, j₃] (Fin.cons f₁ (Fin.cons f₂ (Fin.cons f₃ nofun)))
     (Fin.cons g₁ (Fin.cons g₂ (Fin.cons g₃ nofun)))
  exact ⟨s, α, β, H 0, H 1, H 2⟩

lemma tulip {j₁ j₂ j₃ k₁ k₂ l : C} (f₁ : k₁ ⟶ j₁) (f₂ : k₁ ⟶ j₂) (f₃ : k₂ ⟶ j₂) (f₄ : k₂ ⟶ j₃)
    (g₁ : l ⟶ j₁) (g₂ : l ⟶ j₃) :
    ∃ (s : C) (α : s ⟶ k₁) (β : s ⟶ l) (γ : s ⟶ k₂),
      α ≫ f₁ = β ≫ g₁ ∧ α ≫ f₂ = γ ≫ f₃ ∧ γ ≫ f₄ = β ≫ g₂ := by
  obtain ⟨s, α, β, γ, h1, h2, h3⟩ := IsFiltered.tulip f₁.op f₂.op f₃.op f₄.op g₁.op g₂.op
  use s.unop, α.unop, β.unop, γ.unop, by simpa using congr($(h1).unop),
    by simpa using congr($(h2).unop),
    by simpa using congr($(h3).unop)

end CategoryTheory.IsCofiltered
