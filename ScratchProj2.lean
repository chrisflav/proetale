import Mathlib

section
variable {R : Type} [CommRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

#check (inferInstance : (Module.Free R M → Module.Projective R M))
#check Module.Projective
#check Module.Free.of_subsingleton

end
