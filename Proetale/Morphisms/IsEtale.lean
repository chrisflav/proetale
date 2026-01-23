import Mathlib

universe u

open CategoryTheory Limits MorphismProperty Algebra IsLocalRing

section ring

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

@[stacks 00TF]
lemma Algebra.isEtaleAt_of_flat_of_unramified [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    (hr : Algebra.IsSeparable p.ResidueField q.ResidueField)
    (hpq : p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _) :
    Algebra.IsEtaleAt R q := by
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) := .of_comp R _ _
  sorry

end ring

namespace AlgebraicGeometry

theorem IsEtale.of_flat_of_locallyOfFinitePresentation_of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] [FormallyUnramified f] : IsEtale f := by
  sorry

end AlgebraicGeometry
