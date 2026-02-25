import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

private lemma changeProp_coverPreserving (hPQ : P ≤ Q) :
    CoverPreserving (S.smallGrothendieckTopology P) (S.smallGrothendieckTopology Q)
      (Over.changeProp S hPQ le_rfl) where
  cover_preserve {U R} hR := by
    rw [Functor.mem_inducedTopology_sieves_iff] at hR ⊢
    rw [← Sieve.functorPushforward_comp]
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    rw [← Sieve.functorPushforward_comp] at hR
    exact grothendieckTopology_monotone hPQ _ hR

private lemma changeProp_compatiblePreserving (hPQ : P ≤ Q) :
    CompatiblePreserving (S.smallGrothendieckTopology Q)
      (Over.changeProp S hPQ le_rfl) := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  -- Goal: ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  -- Since changeProp is fully faithful, Over.changeProp maps are just Comma.changeProp maps
  -- We use: forget Q ∘ changeProp = forget P, and Over.forget is CompatiblePreserving
  -- for (grothendieckTopology Q).over S.
  -- The key idea: push forward through forget Q to get CompatiblePreserving from Over.forget
  have hcompat := (over_forget_compatiblePreserving
    ((grothendieckTopology Q).over S) S).compatible
  -- Apply the compatibility condition using the forget functor
  have eq' : (Over.forget Q ⊤ S).map f₁ ≫ (Over.forget Q ⊤ S).map ((Over.changeProp S hPQ le_rfl).map g₁) =
    (Over.forget Q ⊤ S).map f₂ ≫ (Over.forget Q ⊤ S).map ((Over.changeProp S hPQ le_rfl).map g₂) := by
    simp only [← Functor.map_comp, eq]
  sorry

instance (hPQ : P ≤ Q) :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) :=
  Functor.isContinuous_of_coverPreserving
    (changeProp_compatiblePreserving S hPQ) (changeProp_coverPreserving S hPQ)

end AlgebraicGeometry.Scheme
