import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma

universe u

open CategoryTheory MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

private lemma changeProp_coverPreserving (hPQ : P ≤ Q) :
    CoverPreserving (S.smallGrothendieckTopology P) (S.smallGrothendieckTopology Q)
      (Over.changeProp S hPQ le_rfl) where
  cover_preserve {U R} hR := by
    simp only [smallGrothendieckTopology, Functor.mem_inducedTopology_sieves_iff] at hR ⊢
    rw [← Sieve.functorPushforward_comp]
    exact grothendieckTopology_monotone hPQ _ hR

instance changeProp_isContinuous (hPQ : P ≤ Q) :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) where
  op_comp_isSheaf_of_types := by
    intro G X R hR xx hxx
    set F : P.Over ⊤ S ⥤ Q.Over ⊤ S := Over.changeProp S hPQ le_rfl
    have hR' : R.functorPushforward F ∈ (S.smallGrothendieckTopology Q) (F.obj X) :=
      (changeProp_coverPreserving S hPQ).cover_preserve hR
    have hGsheaf : Presieve.IsSheaf (S.smallGrothendieckTopology Q) G.val :=
      (isSheaf_iff_isSheaf_of_type _ G.val).1 G.cond
    have hSF : Presieve.IsSheafFor G.val (R.functorPushforward F).arrows :=
      hGsheaf _ hR'
    -- The presieve R.arrows.map F generates R.fp(F) and G is a sheaf for it
    have hSFmap : Presieve.IsSheafFor G.val (R.arrows.map F) := by
      rw [Presieve.isSheafFor_iff_generate]
      show Presieve.IsSheafFor G.val (Sieve.generate (R.arrows.map F)).arrows
      rw [show (Sieve.generate (R.arrows.map F)).arrows =
        R.arrows.functorPushforward F from Sieve.arrows_generate_map_eq_functorPushforward (F := F)]
      exact hSF
    apply existsUnique_of_exists_of_unique
    · -- Existence: construct compatible family on R.arrows.map F
      -- For `Presieve.map.of hf : (R.arrows.map F) (F.map f)`, we set `y (F.map f) := xx f hf`
      -- Compatibility follows from hxx + Full/Faithful of F
      sorry
    · -- Uniqueness: two amalgamations agree on R.fp(F) by functoriality, hence equal by sep.
      intro t₁ t₂ ht₁ ht₂
      apply hSF.isSeparatedFor.ext
      rintro Y _ ⟨Z, g, h, hg, rfl⟩
      simp only [op_comp, Functor.map_comp, types_comp_apply]
      exact (congr_arg (G.val.map h.op) (ht₁ g hg)).trans
        (congr_arg (G.val.map h.op) (ht₂ g hg)).symm

end AlgebraicGeometry.Scheme
