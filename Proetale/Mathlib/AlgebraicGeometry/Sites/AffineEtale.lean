import Mathlib.AlgebraicGeometry.Sites.AffineEtale

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace AffineEtale

variable (S : Scheme.{u})

noncomputable
abbrev toScheme : S.AffineEtale ⥤ Scheme :=
  AffineEtale.Spec _ ⋙ Etale.forget _ ⋙ Over.forget _

variable {S} in
lemma mem_topology_iff {X : S.AffineEtale} (R : Sieve X) :
    R ∈ topology S X ↔
      Sieve.functorPushforward (toScheme S) R ∈ etaleTopology ((toScheme S).obj X) := by
  rw [Sieve.functorPushforward_comp, Sieve.functorPushforward_comp]
  rfl

-- TODO: When the Zariski topology on `CommRingCatᵒᵖ` lands, consider refactoring this.
noncomputable
def zariskiTopology : GrothendieckTopology S.AffineEtale :=
  (Precoverage.comap (toScheme S) zariskiPrecoverage).toGrothendieck

/-- The Zariski topology on the small affine étale site of `S` is coarser than the affine étale
topology, since a Zariski cover consists of open immersions, which are étale. -/
lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S := by
  rw [zariskiTopology, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro X R hR
  rw [Precoverage.mem_comap_iff] at hR
  rw [GrothendieckTopology.mem_toPrecoverage_iff, mem_topology_iff,
    ← Sieve.generate_map_eq_functorPushforward]
  -- Open immersions are étale, so a Zariski cover is an étale cover.
  have hle : @IsOpenImmersion ≤ @Etale := fun _ _ _ _ ↦ inferInstance
  exact Precoverage.generate_mem_toGrothendieck (precoverage_mono hle _ hR)

end AffineEtale

end AlgebraicGeometry.Scheme
