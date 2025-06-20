import Mathlib.AlgebraicGeometry.Limits

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ ↦ (h.uniqueUpToIso specPunitIsInitial).hom.homeomorph.isEmpty,
    fun _ ↦ ⟨isInitialOfIsEmpty⟩⟩

instance : IsEmpty (⊥_ Scheme) := by
  rw [← isInitial_iff_isEmpty]
  exact ⟨initialIsInitial⟩

end AlgebraicGeometry
