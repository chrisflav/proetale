import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Proetale.Mathlib.Topology.Separation.Hausdorff

universe u

open CategoryTheory Limits

-- use the following lemma: `t2Space_iff_diagonal_closed`
-- after `TopCat.isEmbedding_pullback_to_prod`
@[stacks 08ZH]
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    Topology.IsClosedEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) := by
    set f1 := ConcreteCategory.hom f
    set g1 := ConcreteCategory.hom g
    constructor
    · exact isEmbedding_pullback_to_prod f g
    · have s1 : Set.range ⇑(ConcreteCategory.hom (prod.lift (pullback.fst f g) (pullback.snd f g))) =  (homeoOfIso (prodIsoProd X Y)) ⁻¹' (Prod.map ⇑f1 ⇑g1 ⁻¹' Set.range fun x ↦ (x, x)) := by
        ext x
        simp
        constructor
        · rintro ⟨a, ha⟩
          rw[← ha]
          have hp := pullbackIsoProdSubtype f g
          have : ((homeoOfIso (X.prodIsoProd Y)) ((ConcreteCategory.hom (prod.lift (pullback.fst f g) (pullback.snd f g))) a)).1 = ((prod.lift (pullback.fst f g) (pullback.snd f g)) ≫ (X.prodIsoProd Y).hom ≫ TopCat.prodFst ) a := rfl
          rw[this]
          simp only [prodIsoProd_hom_fst, limit.lift_π, BinaryFan.mk_pt, BinaryFan.mk_fst]
          have : ((homeoOfIso (X.prodIsoProd Y)) ((ConcreteCategory.hom (prod.lift (pullback.fst f g) (pullback.snd f g))) a)).2 = ((prod.lift (pullback.fst f g) (pullback.snd f g)) ≫ (X.prodIsoProd Y).hom ≫ TopCat.prodSnd ) a := rfl
          rw[this]
          simp [f1, g1]
          rw[← ConcreteCategory.comp_apply]
          simp[pullback.condition]
        · intro ha
          -- For this part, there is a mathlib lemma "range_pullback_to_prod", but if we want to apply that lemma, we see that in this lemma we have 'TopCat: Type 1', but we are in 'TopCat : Type (u + 1)' so Lean shows a mismatch and cannot state 'range_pullback_to_prod f g' for our f and g. But since the proof lines are essentially the same, I just adapted the original proof lines below. I don't know if there is a better way of doing it. -- Haowen
          use (pullbackIsoProdSubtype f g).inv ⟨(X.prodIsoProd Y).hom x , ha⟩
          apply Concrete.limit_ext
          rintro ⟨⟨⟩⟩ <;>
             rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, limit.lift_π] <;>
              -- This used to be `simp` before https://github.com/leanprover/lean4/pull/2644
          cat_disch
      have hfg := Continuous.prodMap (map_continuous f1) (map_continuous g1)
      have hc := IsClosed.preimage hfg (t2Space_iff_diagonal_closed.mp ‹T2Space Z›)
      have hc1 := (TopCat.homeoOfIso (TopCat.prodIsoProd X Y)).isClosed_preimage.mpr hc
      rw[← s1] at hc1
      exact hc1
