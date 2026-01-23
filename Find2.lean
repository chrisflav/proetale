import Mathlib

open scoped TensorProduct

universe u v

namespace Search

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Try to locate: flat + formally unramified + finite presentation -> formally etale/smooth
set_option maxHeartbeats 400000

#find (_ : FinitePresentation R S) → (_ : Module.Flat R S) → (_ : Algebra.FormallyUnramified R S) → Algebra.FormallyEtale R S
#find (_ : FinitePresentation R S) → (_ : Module.Flat R S) → (_ : Algebra.FormallyUnramified R S) → Algebra.FormallySmooth R S

end Search
