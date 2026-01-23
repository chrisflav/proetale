import Mathlib

#check FinitePresentation
#check Algebra.FinitePresentation

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
#check FinitePresentation R S
end
