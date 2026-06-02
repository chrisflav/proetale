import Mathlib.CategoryTheory.Limits.Types.Filtered

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types.FilteredColimit

/-- Given a finite set `s` of elements in the colimit of a filtered diagram of types, we can
find a single stage `j` of the diagram together with a function lifting all elements of `s`
through `c.ι.app j`. This is the finsetwise generalisation of
`Types.jointly_surjective_of_isColimit₂`. -/
lemma jointly_surjective_finset_of_isColimit
    {J : Type v} [Category.{w} J] [IsFiltered J] {F : J ⥤ Type u}
    {c : Cocone F} (hc : IsColimit c) (s : Finset c.pt) :
    ∃ (j : J) (lift : (↑s : Set c.pt) → F.obj j),
      ∀ x : (↑s : Set c.pt), c.ι.app j (lift x) = x.val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨IsFiltered.nonempty.some, ?_, ?_⟩ <;> rintro ⟨x, hx⟩ <;> simp at hx
  | @insert a s ha ih =>
    obtain ⟨j₀, lift₀, h₀⟩ := ih
    obtain ⟨j₁, y₁, hy₁⟩ := Types.jointly_surjective_of_isColimit hc a
    let j : J := IsFiltered.max j₀ j₁
    let m₀ : j₀ ⟶ j := IsFiltered.leftToMax j₀ j₁
    let m₁ : j₁ ⟶ j := IsFiltered.rightToMax j₀ j₁
    refine ⟨j, fun x ↦ if hxs : x.val ∈ s then F.map m₀ (lift₀ ⟨x.val, hxs⟩)
        else F.map m₁ y₁, ?_⟩
    rintro ⟨x, hx⟩
    by_cases hxs : x ∈ s
    · simp only [hxs, ↓reduceDIte]
      rw [show c.ι.app j (F.map m₀ (lift₀ ⟨x, hxs⟩)) = c.ι.app j₀ (lift₀ ⟨x, hxs⟩) by
        simp [Cocone.w_apply]]
      exact h₀ ⟨x, hxs⟩
    · obtain rfl : x = a := (Finset.mem_insert.mp hx).resolve_right hxs
      simp only [hxs, ↓reduceDIte]
      rw [show c.ι.app j (F.map m₁ y₁) = c.ι.app j₁ y₁ by simp [Cocone.w_apply]]
      exact hy₁

end CategoryTheory.Limits.Types.FilteredColimit
