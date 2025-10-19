import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

namespace CategoryTheory.Limits

noncomputable
def WidePullback.reindex {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasWidePullback B X f]
    {g : (j : β) → Y j ⟶ B} [HasWidePullback B Y g]
    (e : α ≃ β) (s : ∀ a, X a ≅ Y (e a))
    (w : ∀ i, (s i).hom ≫ g (e i) = f _) :
    widePullback B X f ≅ widePullback B Y g where
  hom := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e.symm i) ≫ (s _).hom ≫ eqToHom (by simp))
    fun i ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i
      simp [w]
  inv := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e i) ≫ (s _).inv)
    fun i ↦ by simp [← w]

noncomputable
def WidePullback.proj {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α ⊕ β → C}
    {f : (j : α ⊕ β) → X j ⟶ B} [HasWidePullback B X f]
    [HasWidePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j))] :
    widePullback B X f ⟶ widePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j)) :=
  WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp)

noncomputable
def WidePullback.mapOfSumEquiv {α β γ : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasLimitsOfShape (WidePullbackShape α) C]
    {g : (j : β) → Y j ⟶ B} [HasLimitsOfShape (WidePullbackShape β) C]
    [HasLimitsOfShape (WidePullbackShape (β ⊕ γ)) C]
    (e : β ⊕ γ ≃ α) (s : ∀ (b : β), X (e (.inl b)) ⟶ Y b)
    (w : ∀ b, s b ≫ g b = f _) :
    widePullback B X f ⟶ widePullback B Y g :=
  (WidePullback.reindex (Y := X ∘ e) (g := fun i ↦ f (e i)) e.symm
    (fun a ↦ eqToIso (by simp)) (fun i ↦ by
      simp only [Function.comp_apply, eqToIso.hom]
      rw [← eqToHom_naturality, eqToHom_refl, Category.comp_id]
      rw [Equiv.apply_symm_apply])).hom ≫
    WidePullback.lift (objs := Sum.elim Y (X ∘ e ∘ .inr))
      (arrows := fun i ↦ match i with
        | .inl b => g b
        | .inr c => f _)
      (WidePullback.base _)
      (fun j ↦ match j with
        | .inl b => WidePullback.π _ _ ≫ s b
        | .inr b => WidePullback.π _ _)
      (by simp [w]) ≫
      WidePullback.proj

end CategoryTheory.Limits
