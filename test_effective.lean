import Proetale.Topology.Flat.Sheaf

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

section AmitsurExact

open scoped TensorProduct

-- Approach: transport via Spec^op as limit-preserving functor
-- Spec.rightOp : CommRingCat → Scheme^op is defined as the composition
-- of op and Spec. If Spec preserves limits (as a right adjoint),
-- then Spec.rightOp turns CommRingCat limits into Scheme^op limits.

-- Actually, let's try to directly use the fact that Spec sends pushouts
-- in CommRingCat to pullbacks in Scheme, and then dualize.

-- Test: can we show the fork in Scheme^op is a limit?
set_option maxHeartbeats 1600000 in
noncomputable
example {R S : CommRingCat.{u}} (f : R ⟶ S) (hff : f.hom.FaithfullyFlat) :
    EffectiveEpi (Spec.map f) := by
  have hs : Function.Surjective (Spec.map f).base := by
    rw [← AlgebraicGeometry.Scheme.Hom.surjective]
    exact ((flat_and_surjective_SpecMap_iff (P := @Flat)).mpr
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hff.to_flat, by
        rw [flat_and_surjective_SpecMap_iff]; exact ⟨_, by
          rwa [flat_and_surjective_SpecMap_iff]⟩⟩).2
  sorry

end AmitsurExact
