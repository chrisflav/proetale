/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Topology.Proetale.Sheafification
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Comparison with the étale site

-/

universe u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the étale site into the pro-étale site. -/
@[simps! obj_toComma]
def toProEtale (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

variable (S : Scheme.{u})

instance : (toProEtale S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance : (toProEtale S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful

instance : HasFiniteLimits S.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ S)

instance : PreservesFiniteLimits (toProEtale S) := by
  have : PreservesFiniteLimits (toProEtale S ⋙ ProEt.forget S) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ S)
  exact preservesFiniteLimits_of_reflects_of_preserves (toProEtale S) (ProEt.forget S)

instance representablyFlat_toProEtale : RepresentablyFlat (toProEtale S) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the étale site into the pro-étale site is continuous. -/
instance isContinuous_toProEtale :
    (toProEtale S).IsContinuous (smallEtaleTopology S) (ProEt.topology S) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (toProEtale S)) ?_
  refine ⟨fun {X R} hR ↦ ?_⟩
  rw [ProEt.topology_eq_inducedTopology, Functor.mem_inducedTopology_sieves_iff,
    ← Sieve.functorPushforward_comp]
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ S) ∈ etaleTopology.over S _ := hR
  rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
  exact etaleTopology_le_proetaleTopology _ hR'

namespace ProEt

variable (A : Type*) [Category A]

/-- The direct image functor from pro-étale sheafs to étale sheafs. -/
@[simps! obj_obj]
abbrev sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (smallEtaleTopology S) A :=
  (toProEtale S).sheafPushforwardContinuous _ _ _

instance (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) : (toProEtale S).op.HasPointwiseLeftKanExtension F :=
  inferInstance

/-- The direct image functor from pro-étale sheafs to étale sheafs has a left-adjoint. -/
instance : (ProEt.sheafPushforward S Ab.{u + 1}).IsRightAdjoint := inferInstance

variable [(sheafPushforward S A).IsRightAdjoint]

/-- The inverse image functor from étale sheafs to pro-étale sheafs. -/
noncomputable abbrev sheafPullback :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (ProEt.topology S) A :=
  (toProEtale S).sheafPullback _ _ _

/-- The inverse image - direct image adjunction for the pro-étale site. -/
noncomputable abbrev sheafAdjunction :
    ProEt.sheafPullback S A ⊣ ProEt.sheafPushforward S A :=
  (toProEtale S).sheafAdjunctionContinuous _ _ _

end ProEt

end AlgebraicGeometry.Scheme
