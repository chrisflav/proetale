import Mathlib.CategoryTheory.Sites.Grothendieck

namespace CategoryTheory

lemma GrothendieckTopology.transitive_of_presieve {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {X : C} (R : Presieve X) (hR : Sieve.generate R ∈ J X)
    (S : Sieve X) (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → S.pullback g ∈ J Y) :
    S ∈ J X := by
  refine J.transitive hR _ ?_
  rintro Y f ⟨W, g, v, hv, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable _ (h _ hv)

/-- Membership of pushforward sieves in a Grothendieck topology only depends on the
functor up to natural isomorphism. -/
lemma GrothendieckTopology.functorPushforward_mem_of_iso {C : Type*} [Category* C]
    {D : Type*} [Category* D]
    (K : GrothendieckTopology D) {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {U : C} (R : Sieve U)
    (h : R.functorPushforward F₁ ∈ K (F₁.obj U)) :
    R.functorPushforward F₂ ∈ K (F₂.obj U) := by
  refine K.superset_covering ?_ (K.pullback_stable (e.inv.app U) h)
  rintro Z g ⟨V, a, h', ha, hfac⟩
  refine ⟨V, a, h' ≫ e.hom.app V, ha, ?_⟩
  have hg : g = (g ≫ e.inv.app U) ≫ e.hom.app U := by
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hg, hfac, Category.assoc, Category.assoc, NatTrans.naturality]

end CategoryTheory
