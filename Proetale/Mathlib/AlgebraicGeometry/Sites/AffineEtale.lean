import Mathlib.AlgebraicGeometry.Sites.AffineEtale

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

lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S :=
  sorry

end AffineEtale

end AlgebraicGeometry.Scheme
