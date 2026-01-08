import Mathlib.RingTheory.RingHom.OpenImmersion

-- after `Algebra.IsStandardOpenImmersion`
instance Algebra.IsStandardOpenImmersion.refl (R : Type*) [CommSemiring R] :
    Algebra.IsStandardOpenImmersion R R :=
  ⟨1, IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id⟩
