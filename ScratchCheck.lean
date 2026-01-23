import Mathlib

open Algebra

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

-- candidates
#check Algebra.FormallyEtale.of_flat
#check Algebra.FormallyEtale.of_flat_of_formallyUnramified
#check Algebra.FormallyEtale.of_formallyUnramified_of_flat
#check Algebra.FormallyEtale.of_unramified_of_flat
#check Algebra.FormallySmooth.of_flat
#check Algebra.FormallySmooth.of_flat_of_formallyUnramified
#check Algebra.FormallySmooth.of_formallyUnramified_of_flat
#check Algebra.FormallySmooth.of_unramified_of_flat
#check Algebra.Etale.of_flat_of_unramified
#check Algebra.Etale.of_unramified_of_flat
#check Algebra.IsEtaleAt.of_flat_of_unramified
#check Algebra.IsEtaleAt.of_unramified_of_flat

end
