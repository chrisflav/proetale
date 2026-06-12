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
  have hle : @IsOpenImmersion ≤ @Etale := fun _ _ _ _ ↦ inferInstance
  have key : Sieve.generate (R.map (toScheme S)) ∈
      grothendieckTopology @Etale ((toScheme S).obj X) :=
    Precoverage.generate_mem_toGrothendieck (precoverage_mono hle _ hR)
  rw [GrothendieckTopology.mem_toPrecoverage_iff]
  -- Membership in `topology S` is definitionally membership of the iterated pushforward
  -- through the two induced topologies (along `AffineEtale.Spec S` and
  -- `MorphismProperty.Over.forget`); since `rw`/`simp` cannot pierce the nested
  -- `inducedTopology`, we expose this form by `rfl` via `show`.
  change Sieve.functorPushforward (MorphismProperty.Over.forget @Etale ⊤ S)
      (Sieve.functorPushforward (AffineEtale.Spec S) (Sieve.generate R)) ∈
      overGrothendieckTopology @Etale (S := S)
        ((MorphismProperty.Over.forget @Etale ⊤ S).obj ((AffineEtale.Spec S).obj X))
  rw [GrothendieckTopology.mem_over_iff]
  convert key using 2
  -- The two sieves agree: `toScheme S = AffineEtale.Spec S ⋙ Etale.forget S ⋙ Over.forget S`.
  simp only [toScheme, Sieve.overEquiv, Equiv.coe_fn_mk]
  rw [Sieve.generate_map_eq_functorPushforward
      (F := AffineEtale.Spec S ⋙ Etale.forget S ⋙ Over.forget S),
    Sieve.functorPushforward_comp, Sieve.functorPushforward_comp]
  rfl

end AffineEtale

end AlgebraicGeometry.Scheme
