import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Proetale.Mathlib.Topology.Separation.Hausdorff

universe u

open CategoryTheory Limits

-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
@[stacks 08ZH]
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Topology.IsClosedEmbedding (prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  refine ⟨TopCat.isEmbedding_pullback_to_prod f g, ?_⟩
  have hrange : Set.range (ConcreteCategory.hom (prod.lift (pullback.fst f g) (pullback.snd f g))) =
      { x : ↑(X ⨯ Y) | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp only [← ConcreteCategory.comp_apply, Set.mem_setOf_eq]
      simp [pullback.condition]
    · rintro (h : f (_, _).1 = g (_, _).2)
      refine ⟨(TopCat.pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩, ?_⟩
      apply Concrete.limit_ext
      rintro ⟨⟨⟩⟩ <;>
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
        cat_disch
  have hdiag : IsClosed (Set.diagonal Z) := by
    simpa [Set.range_diag] using t2Space_iff_diagonal_closed.1 inferInstance
  have hcont :
      Continuous (fun x : ↑(X ⨯ Y) => ((Limits.prod.fst ≫ f) x, (Limits.prod.snd ≫ g) x)) :=
    (Limits.prod.fst ≫ f).hom.continuous.prodMk (Limits.prod.snd ≫ g).hom.continuous
  simpa [hrange] using (by simpa [Set.diagonal] using hdiag.preimage hcont)
