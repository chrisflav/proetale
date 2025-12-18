import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Functor.OfSequence

namespace CategoryTheory.MorphismProperty

lemma ofSequence_map_of_isMultiplicative {C : Type*} [Category C] {X : ℕ → C}
    (f : (n : ℕ) → X n ⟶ X (n + 1)) {m n : ℕ} (hle : m ≤ n) (P : MorphismProperty C)
    [P.IsMultiplicative] (H : ∀ n, P (f n)) :
    P ((Functor.ofSequence f).map (homOfLE hle)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using P.id_mem _
  | succ n ih =>
    rw [← homOfLE_comp (show m ≤ m + n by cutsat) (show m + n ≤ m + (n + 1) by cutsat),
      Functor.map_comp]
    apply P.comp_mem
    · apply ih
    · simp [H]

lemma ofOpSequence_map_of_isMultiplicative {C : Type*} [Category C] {X : ℕ → C}
    (f : (n : ℕ) → X (n + 1) ⟶ X n) {m n : ℕ} (hle : m ≤ n) (P : MorphismProperty C)
    [P.IsMultiplicative] (H : ∀ n, P (f n)) :
    P ((Functor.ofOpSequence f).map (homOfLE hle).op) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using P.id_mem _
  | succ n ih =>
    rw [← homOfLE_comp (show m ≤ m + n by cutsat) (show m + n ≤ m + (n + 1) by cutsat),
      op_comp, Functor.map_comp]
    apply P.comp_mem
    · simp [H]
    · apply ih

end CategoryTheory.MorphismProperty
