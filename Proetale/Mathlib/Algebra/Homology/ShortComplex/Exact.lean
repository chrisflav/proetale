import Mathlib.Algebra.Homology.ShortComplex.Exact

namespace CategoryTheory

open Limits

instance {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape WalkingParallelPair C] [HasColimitsOfShape WalkingParallelPair C]  (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

lemma ShortComplex.exact_iff_evaluation {J : Type*} [Category J] {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C] [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C] (S : ShortComplex (J ⥤ C)) [S.HasHomology] :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  rw [exact_iff_isZero_homology, Functor.isZero_iff]
  refine forall_congr' fun j ↦ ?_
  let e : S.homology.obj j ≅ _ := (mapHomologyIso S ((evaluation J C).obj j)).symm
  rw [e.isZero_iff, exact_iff_isZero_homology]

end CategoryTheory
