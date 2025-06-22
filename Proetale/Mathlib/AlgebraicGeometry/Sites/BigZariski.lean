import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Proetale.Mathlib.AlgebraicGeometry.Sites.MorphismProperty

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/--
The big Zariski site on the category of all `u`-schemes has sheafification in `Type u`.
This requires a refactor of sheafification in mathlib.
-/
instance : HasSheafify Scheme.zariskiTopology.{u} (Type u) := by
  sorry

lemma preservesFiniteProducts_of_isSheaf_zariskiTopology {F : Scheme.{u}ᵒᵖ ⥤ Type*}
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesFiniteProducts F := by
  apply Limits.preservesFiniteProducts_of_preservesLimitsOfShape
  intro ι _
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  let X' := unop ∘ X
  show PreservesLimit (Discrete.functor fun i ↦ op (X' i)) F
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor X')) i) :=
    inferInstanceAs <| Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sigma.cocone (Discrete.functor X')) (coproductIsCoproduct' _) ?_ ?_
  · apply hF.isSheafFor
    convert (⊥_ Scheme).bot_mem_grothendieckTopology
    rw [eq_bot_iff]
    rintro Y f ⟨g, _, _, ⟨i⟩, _⟩
    exact i.elim
  · intro i j hij
    refine ⟨?_, ⟨?_⟩⟩
    · simp
    · refine PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        exact isInitialOfIsEmpty.to _
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        apply isInitialOfIsEmpty.hom_ext
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        apply isInitialOfIsEmpty.hom_ext
      · intro s m
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        intro x y
        apply isInitialOfIsEmpty.hom_ext
  · exact hF.isSheafFor _ _ (sigmaOpenCover' X').generate_ofArrows_mem_grothendieckTopology

end AlgebraicGeometry
