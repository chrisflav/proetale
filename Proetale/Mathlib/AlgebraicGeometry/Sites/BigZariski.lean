import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Proetale.Mathlib.AlgebraicGeometry.Sites.MorphismProperty

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

@[simp]
lemma GrothendieckTopology.pullback_hom_mem_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X Y : C} {e : X ≅ Y} {S : Sieve Y} :
    S.pullback e.hom ∈ J X ↔ S ∈ J Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ J.pullback_stable e.hom h⟩
  simpa using J.pullback_stable e.inv h

end CategoryTheory

namespace AlgebraicGeometry

/--
The big Zariski site on the category of all `u`-schemes has sheafification in `Type u`.
This requires a refactor of sheafification in mathlib.
-/
proof_wanted hasSheafify_zariskiTopology : HasSheafify Scheme.zariskiTopology.{u} (Type u)

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
  · exact hF.isSheafFor _ _ (sigmaOpenCover X').generate_ofArrows_mem_grothendieckTopology

lemma Scheme.IsLocallyDirected.ofArrows_mem_grothendieckTopology {J : Type*} [Category J]
    (F : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F.comp Scheme.forget).IsLocallyDirected]
    [Quiver.IsThin J] [Small.{u} J] :
    Sieve.ofArrows _ (colimit.ι F) ∈ Scheme.zariskiTopology (colimit F) :=
  (Scheme.IsLocallyDirected.openCover F).generate_ofArrows_mem_grothendieckTopology

lemma ofArrows_ι_mem_zariskiTopology_of_isColimit {ι : Type*} {F : Discrete ι ⥤ Scheme.{u}}
    [Small.{u} ι] (c : Cocone F) (hc : IsColimit c) :
    Sieve.ofArrows _ c.ι.app ∈ Scheme.zariskiTopology c.pt := by
  let iso : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
  rw [← GrothendieckTopology.pullback_hom_mem_iff (e := iso.symm)]
  apply GrothendieckTopology.superset_covering _ ?_ ?_
  · exact Sieve.ofArrows _ (colimit.ι F)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    exact ⟨_, 𝟙 _, c.ι.app i, ⟨i⟩, by simp [iso]⟩
  · exact Scheme.IsLocallyDirected.ofArrows_mem_grothendieckTopology F

end AlgebraicGeometry
