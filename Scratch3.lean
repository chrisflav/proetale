import Mathlib

universe u

open Algebra IsLocalRing

section

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma test [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    (h : Algebra.IsUnramifiedAt R q) :
    Algebra.IsEtaleAt R q := by
  dsimp [Algebra.IsEtaleAt]
  have : Algebra.FormallyEtale R (Localization.AtPrime q) := by
    infer_instance
  exact this

end
