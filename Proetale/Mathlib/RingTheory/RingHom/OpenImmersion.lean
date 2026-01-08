import Mathlib.RingTheory.RingHom.OpenImmersion

-- after `Algebra.IsStandardOpenImmersion`
instance Algebra.IsStandardOpenImmersion.refl (R : Type*) [CommSemiring R] :
    Algebra.IsStandardOpenImmersion R R :=
  ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

lemma Algebra.IsStandardOpenImmersion.of_bijective (h : Function.Bijective (algebraMap R S)) :
    IsStandardOpenImmersion R S := by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h

lemma Algebra.IsStandardOpenImmersion.of_algEquiv (T : Type*) [CommSemiring T] [Algebra R T]
    (e : S ≃ₐ[R] T) [h : IsStandardOpenImmersion R S] :
    IsStandardOpenImmersion R T := by
  rw [Algebra.isStandardOpenImmersion_iff] at *
  obtain ⟨r, hr⟩ := h
  use r
  exact IsLocalization.isLocalization_of_algEquiv _ e

