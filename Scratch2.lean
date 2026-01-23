import Mathlib

universe u

open Algebra IsLocalRing

section

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma test [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    (h : Algebra.IsUnramifiedAt R q) :
    Algebra.IsSmoothAt R q := by
  -- try typeclass search
  --simp [Algebra.IsSmoothAt]
  --fail_if_success infer_instance
  --
  -- Try to see goals
  dsimp [Algebra.IsSmoothAt]
  -- we need FormallySmooth R (Localization.AtPrime q)
  -- try to let it synthesize
  have : Algebra.FormallySmooth R (Localization.AtPrime q) := by
    -- Try with aesop?
    -- exact?
    infer_instance
  exact this

end
