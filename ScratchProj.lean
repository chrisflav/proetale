import Mathlib

section
variable {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

#check Module.Projective
#check Module.Projective.of_subsingleton
#check Module.projective_of_subsingleton

end
