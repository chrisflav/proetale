import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.CategoryTheory.Sites.Continuous

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

instance (hPQ : P ≤ Q) :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) :=
  sorry

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange]
variable (A : Type*) [Category* A]

instance :
    (Over.pullback P ⊤ f).PreservesOneHypercovers
      (T.smallGrothendieckTopology P)
      (S.smallGrothendieckTopology P) := by
  intro X E
  constructor
  · sorry
  · sorry

noncomputable
abbrev smallPushforward :
    Sheaf (S.smallGrothendieckTopology P) A ⥤ Sheaf (T.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPushforwardContinuous _ _ _

instance :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology P)
      (smallGrothendieckTopology P)).IsRightAdjoint :=
  sorry

noncomputable
abbrev smallPullback :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPullback _ _ _

noncomputable
def smallPullbackPushforwardAdj :
    smallPullback f P A ⊣ smallPushforward f P A :=
  (Over.pullback P ⊤ f).sheafAdjunctionContinuous A _ _

instance (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology P) (smallGrothendieckTopology P) :=
  sorry

def smallSheafRestrict (hf : P f) :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.map ⊤ hf).sheafPushforwardContinuous _ _ _

noncomputable def smallSheafRestrictAdj (hf : P f) :
    smallSheafRestrict f P A hf ⊣ smallPushforward f P A :=
  (Over.mapPullbackAdj P ⊤ f hf trivial).sheaf _ _

/-- If `f : S ⟶ T` satisfies `P` the pullback functor `Shv(T) ⥤ Shv(S)` is
naturally isomorphic to the restriction functor. -/
noncomputable def smallPullbackIsoRestrict (hf : P f) :
    smallPullback f P A ≅ smallSheafRestrict f P A hf :=
  (conjugateIsoEquiv (smallSheafRestrictAdj f P A hf) (smallPullbackPushforwardAdj f P A)).symm
    (Iso.refl _)

end

end AlgebraicGeometry.Scheme
