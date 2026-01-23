import Mathlib

open Algebra

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

#check Algebra.Presentation
#check Algebra.Presentation.ofFinitePresentation
#check Algebra.Presentation.ofFinitePresentationVars
#check Algebra.Presentation.ofFinitePresentationRels
#check Algebra.Presentation.ofFinitePresentation

end
