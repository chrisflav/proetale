import Mathlib

open Algebra

section
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
variable [FinitePresentation R S]

noncomputable def P0 : Algebra.Presentation R S (Fin (Algebra.Presentation.ofFinitePresentationVars R S))
    (Fin (Algebra.Presentation.ofFinitePresentationRels R S)) :=
  Algebra.Presentation.ofFinitePresentation R S

#check (P0 (R:=R) (S:=S)).val
#check (P0 (R:=R) (S:=S)).toExtension
#check (P0 (R:=R) (S:=S)).algebraMap_surjective
#check (P0 (R:=R) (S:=S)).fg_ker

end
