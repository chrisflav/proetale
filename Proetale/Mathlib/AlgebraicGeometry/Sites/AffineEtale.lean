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

-- TODO: When the Zariski topology on `CommRingCatᵒᵖ` lands, consider refactoring this.
noncomputable
def zariskiTopology : GrothendieckTopology S.AffineEtale :=
  (Precoverage.comap (toScheme S) zariskiPrecoverage).toGrothendieck

lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S := by
  rw [zariskiTopology, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro X R hR
  rw [Precoverage.mem_comap_iff] at hR
  have hle : @IsOpenImmersion ≤ @Etale := by
    intro X Y f hf
    infer_instance
  have : Sieve.generate (R.map (toScheme S)) ∈ grothendieckTopology @Etale ((toScheme S).obj X) :=
    Precoverage.generate_mem_toGrothendieck (precoverage_mono hle _ hR)
  rw [GrothendieckTopology.mem_toPrecoverage_iff, topology,
    Functor.mem_inducedTopology_sieves_iff, smallEtaleTopology,
    Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff]
  simpa only [Sieve.overEquiv, Equiv.coe_fn_mk,
    ← Sieve.generate_map_eq_functorPushforward, ← Presieve.map_comp, Functor.assoc] using this

/-- A single surjective (étale) morphism is a cover in the small affine étale site. -/
lemma generate_singleton_mem_topology {X Y : S.AffineEtale} (f : X ⟶ Y)
    (hf : Function.Surjective ((toScheme S).map f).base) :
    Sieve.generate (Presieve.singleton f) ∈ topology S Y := by
  have het : Etale ((toScheme S).map f) := by
    refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) ((toScheme S).map f)
      ((AffineEtale.Spec S).obj Y).hom ((AffineEtale.Spec S).obj Y).prop ?_
    have w := MorphismProperty.Over.w ((AffineEtale.Spec S).map f)
    dsimp at w
    show Etale (Spec.map f.left.unop ≫ Y.hom)
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
