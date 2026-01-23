import Mathlib

open Algebra

namespace FindSmooth

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]

-- Try to locate a Mathlib lemma: finite presentation + local flatness + unramified -> smooth at prime.
set_option maxHeartbeats 400000

#find (_ : Algebra.FinitePresentation R S) →
  (_ : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) →
  (_ : Algebra.IsUnramifiedAt R q) → Algebra.IsSmoothAt R q

end FindSmooth

