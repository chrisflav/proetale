/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The inclusion of the small étale site into the pro-étale site

For a scheme `X`, every étale `X`-scheme is in particular weakly étale, so the small
étale site `X.Etale` includes into the pro-étale site `X.ProEt`. We define this
inclusion functor `AlgebraicGeometry.Scheme.ProEt.fromEtale` and record its basic
properties: it is fully faithful, preserves finite limits (hence is representably flat),
and is continuous for the small étale and pro-étale topologies.

These are the analogues, for the inclusion `X.Etale ⥤ X.ProEt`, of the properties of the
forgetful functor `X.ProEt ⥤ Over X` established in
`Mathlib/AlgebraicGeometry/Sites/Proetale.lean`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u})

/-- The inclusion of the small étale site of `X` into its pro-étale site, given by
regarding an étale `X`-scheme as a weakly étale one. -/
def fromEtale : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

instance : (fromEtale X).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance : (fromEtale X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful

instance : HasFiniteLimits X.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ X)

instance : PreservesFiniteLimits (fromEtale X) := by
  have : PreservesFiniteLimits (fromEtale X ⋙ ProEt.forget X) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ X)
  exact preservesFiniteLimits_of_reflects_of_preserves (fromEtale X) (ProEt.forget X)

instance representablyFlat_fromEtale : RepresentablyFlat (fromEtale X) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the small étale site into the pro-étale site is continuous. -/
instance isContinuous_fromEtale :
    (fromEtale X).IsContinuous (smallEtaleTopology X) (ProEt.topology X) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (fromEtale X)) ?_
  refine ⟨fun {Y R} hR ↦ ?_⟩
  rw [ProEt.topology_eq_inducedTopology, Functor.mem_inducedTopology_sieves_iff,
    ← Sieve.functorPushforward_comp]
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ X) ∈ etaleTopology.over X _ := hR
  rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
  exact etaleTopology_le_proetaleTopology _ hR'

end AlgebraicGeometry.Scheme.ProEt
