/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization
import Proetale.Algebra.IndEtale

/-!
# w-strict-localization

In this file we show that every ring admits a faithfully flat, ind-étale w-strictly-local algebra.
-/

universe u

def WStrictLocalization (R : Type u) [CommRing R] : Type u := sorry

variable (R : Type u) [CommRing R]

instance : CommRing (WStrictLocalization R) :=
  sorry

instance : Algebra R (WStrictLocalization R) :=
  sorry

instance : Algebra.IndEtale R (WStrictLocalization R) :=
  sorry

instance : Module.FaithfullyFlat R (WStrictLocalization R) :=
  sorry

instance : IsWStrictlyLocalRing (WStrictLocalization R) :=
  sorry

/-- Any ring has an ind-étale, faithfully flat cover that is w-strictly-local. -/
theorem exists_isWStrictlyLocalRing (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IndEtale R S)
      (_ : Module.FaithfullyFlat R S),
      IsWStrictlyLocalRing S := by
  use WStrictLocalization R, inferInstance, inferInstance, inferInstance, inferInstance
  infer_instance
