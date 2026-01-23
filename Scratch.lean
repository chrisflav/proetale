import Mathlib

universe u

open Algebra

section
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]

-- Try to see if some lemma exists
#check Algebra.IsEtaleAt
#check Algebra.IsSmoothAt
#check Algebra.IsUnramifiedAt

-- Try possible lemmas
#check Algebra.FormallyEtale
#check Algebra.FormallyUnramified
#check Algebra.FormallySmooth

-- try find lemma names
#check Algebra.FormallyUnramified.iff_map_maximalIdeal_eq
#check Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

end
