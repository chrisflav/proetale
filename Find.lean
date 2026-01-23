import Mathlib

open scoped TensorProduct

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

set_option maxHeartbeats 400000

-- Try to locate a lemma: flat + unramified + fp -> formally etale
#find (_ : FinitePresentation R S) → (_ : Module.Flat R S) → (_ : Algebra.FormallyUnramified R S) → Algebra.FormallyEtale R S

end
