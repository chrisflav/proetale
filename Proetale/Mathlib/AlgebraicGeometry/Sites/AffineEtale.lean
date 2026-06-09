import Mathlib.AlgebraicGeometry.Sites.AffineEtale

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

namespace AffineEtale

variable (S : Scheme.{u})

/-- The inclusion functor `AffineEtale.Spec` of the small affine étale site of `S` into the
small étale site of `S` is cover dense: every étale `S`-scheme is covered by affine
étale `S`-schemes. -/
lemma isCoverDense_Spec_smallEtaleTopology :
    (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstance

noncomputable
abbrev toScheme : S.AffineEtale ⥤ Scheme :=
  AffineEtale.Spec _ ⋙ Etale.forget _ ⋙ Over.forget _

-- TODO: When the Zariski topology on `CommRingCatᵒᵖ` lands, consider refactoring this.
noncomputable
def zariskiTopology : GrothendieckTopology S.AffineEtale :=
  (Precoverage.comap (toScheme S) zariskiPrecoverage).toGrothendieck

lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S :=
  sorry

end AffineEtale

end AlgebraicGeometry.Scheme
