import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Proetale.Mathlib.Topology.Separation.Hausdorff

universe u

open CategoryTheory Limits TopCat

-- Universe-polymorphic version of range_pullback_to_prod
set_option backward.isDefEq.respectTransparency false in
private theorem range_pullback_to_prod' {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (prod.lift (pullback.fst f g) (pullback.snd f g)) =
      { x | (Limits.prod.fst ≫ f) x = (Limits.prod.snd ≫ g) x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [Set.mem_setOf_eq]
    have : (prod.lift (pullback.fst f g) (pullback.snd f g) ≫ prod.fst ≫ f) y =
           (prod.lift (pullback.fst f g) (pullback.snd f g) ≫ prod.snd ≫ g) y := by
      congr 1
      simp [pullback.condition (f := f) (g := g)]
    simp only [ConcreteCategory.comp_apply] at this
    exact this
  · rintro (h : f (_, _).1 = g (_, _).2)
    use (pullbackIsoProdSubtype f g).inv ⟨⟨_, _⟩, h⟩
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩ <;> simp [← ConcreteCategory.comp_apply] <;> cat_disch

set_option backward.isDefEq.respectTransparency false in
-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
@[stacks 08ZH]
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Topology.IsClosedEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) := by
  refine ⟨isEmbedding_pullback_to_prod f g, ?_⟩
  rw [range_pullback_to_prod']
  exact isClosed_eq (prod.fst ≫ f).hom.continuous (prod.snd ≫ g).hom.continuous
