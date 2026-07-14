import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Proetale.Mathlib.CategoryTheory.Sites.Sieves

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

/-- A single surjective (étale) morphism is a cover in the small affine étale site. -/
lemma generate_singleton_mem_topology {X Y : S.AffineEtale} (f : X ⟶ Y)
    (hf : Function.Surjective ((toScheme S).map f).base) :
    Sieve.generate (Presieve.singleton f) ∈ topology S Y := by
  have het : Etale ((toScheme S).map f) := by
    refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) ((toScheme S).map f)
      ((AffineEtale.Spec S).obj Y).hom ((AffineEtale.Spec S).obj Y).prop ?_
    have w := MorphismProperty.Over.w ((AffineEtale.Spec S).map f)
    dsimp at w
    change Etale (Spec.map f.left.unop ≫ Y.hom)
    rw [w]
    exact X.prop
  have : Sieve.generate ((Presieve.singleton f).map (toScheme S)) ∈
      grothendieckTopology @Etale ((toScheme S).obj Y) := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Presieve.map_singleton, singleton_mem_precoverage_iff]
    exact ⟨hf, het⟩
  rw [topology, Functor.mem_inducedTopology_sieves_iff, smallEtaleTopology,
    Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff]
  simpa only [Sieve.overEquiv, Equiv.coe_fn_mk,
    ← Sieve.generate_map_eq_functorPushforward, ← Presieve.map_comp, Functor.assoc] using this

end AffineEtale

end AlgebraicGeometry.Scheme
