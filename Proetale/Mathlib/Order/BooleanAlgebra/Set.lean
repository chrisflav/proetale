import Mathlib.Order.BooleanAlgebra.Set

lemma Set.codisjoint_iff {α : Type*} {s t : Set α} : Codisjoint s t ↔ s ∪ t = .univ := by
  simp [_root_.codisjoint_iff]
