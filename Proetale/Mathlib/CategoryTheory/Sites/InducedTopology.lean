import Mathlib

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace Fix

/-
COPIED FROM MATHLIB: fix the correct universe generality. upstream!
-/

open Sieve

/-- Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf. -/
@[stacks 00Z9 "This is a special case of the Stacks entry, but following a different
proof (see the Stacks comments)."]
def finestTopologySingle (P : Cᵒᵖ ⥤ Type*) : GrothendieckTopology C where
  sieves X := {S | ∀ (Y) (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f : Presieve Y)}
  top_mem' X Y f := by
    rw [Sieve.pullback_top]
    exact Presieve.isSheafFor_top P
  pullback_stable' X Y S f hS Z g := by
    rw [← pullback_comp]
    apply hS
  transitive' X S hS R hR Z g := by
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine Presieve.isSheafFor_trans P (pullback g S) _ (hS Z g) ?_ ?_
    · intro Y f _
      rw [← pullback_comp]
      apply (hS _ _).isSeparatedFor
    · intro Y f hf
      have := hR hf _ (𝟙 _)
      rw [pullback_id, pullback_comp] at this
      apply this

/-- Construct the finest (largest) Grothendieck topology for which all the given presheaves are
sheaves. -/
@[stacks 00Z9 "Equal to that Stacks construction"]
def finestTopology (Ps : Set (Cᵒᵖ ⥤ Type*)) : GrothendieckTopology C :=
  sInf (finestTopologySingle '' Ps)

variable {P : Cᵒᵖ ⥤ Type*} {X : C} (J : GrothendieckTopology C)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
theorem sheaf_for_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type _)) (h : P ∈ Ps) :
    Presieve.IsSheaf (finestTopology Ps) P := fun X S hS => by
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _)

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finestTopology Ps`.
-/
theorem le_finestTopology (Ps : Set (Cᵒᵖ ⥤ Type*)) (J : GrothendieckTopology C)
    (hJ : ∀ P ∈ Ps, Presieve.IsSheaf J P) : J ≤ finestTopology Ps := by
  rintro X S hS _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
  intro Y f
  -- this can't be combined with the previous because the `subst` is applied at the end
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS)

end Fix

lemma mem_finestTopology_of_forall_isSheafFor (Ps : Set (Cᵒᵖ ⥤ Type*)) {X : C} (S : Sieve X)
    (H : ∀ P ∈ Ps, ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSheafFor P (S.pullback f).arrows) :
    S ∈ Fix.finestTopology Ps X := by
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩
  intro Y f
  exact H P hP _

/-- The induced topology by a topology on `D` along a functor `F : C ⥤ D` is the finest
topology making `F` continuous. -/
def Functor.inducedTopology' (F : C ⥤ D) (J : GrothendieckTopology D) :
    GrothendieckTopology C :=
  Fix.finestTopology
    (Set.range fun G : Sheaf J (Type (max u₁ v₁ u₂ v₂)) ↦ F.op ⋙ G.obj)

variable (F : C ⥤ D) (J : GrothendieckTopology D)

instance : F.IsContinuous (F.inducedTopology' J) J where
  op_comp_isSheaf_of_types G := by
    apply Fix.sheaf_for_finestTopology
    use G

@[simp]
lemma le_inducedTopology'_iff (K : GrothendieckTopology C) :
    K ≤ F.inducedTopology' J ↔ F.IsContinuous K J := by
  refine ⟨?_, ?_⟩
  · intro h
    constructor
    intro G
    apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology' J) J G
  · intro h
    apply Fix.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F K J P

/-- [SGA4, III, Proposition 3.2][sga4] -/
lemma mem_inducedTopology'_iff [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
    (G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) :
    S ∈ F.inducedTopology' J X ↔
      ∀ ⦃Y : C⦄ (f : Y ⟶ X),
        J.W (G.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} (S.pullback f)).ι) := by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology' J) J _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology' J) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology' J) f hS
  · intro H
    apply mem_finestTopology_of_forall_isSheafFor
    rintro - ⟨P, rfl⟩ Y f
    dsimp
    rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact (adj.map_comp_bijective_iff _ _).mp (H f _ P.property)

lemma induced_induced_le (G : D ⥤ E) (J : GrothendieckTopology E) :
    F.inducedTopology' (G.inducedTopology' J) ≤ (F ⋙ G).inducedTopology' J := by
  rw [le_inducedTopology'_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology' J) _

-- This is not true in this generality, possibly with more assumptions?
--def asdfasdfasdf (X : C) :
--    { S : Sieve X // (F.inducedTopology' J).IsClosed S } ≃
--      { S : Sieve (F.obj X) // J.IsClosed S } where
--  toFun S := by
--    refine ⟨Sieve.functorPushforward _ S, ?_⟩
--    intro Y f hf
--    simp
--    simp [GrothendieckTopology.Covers] at hf
--    have := S.2
--    sorry
--  invFun := sorry
--  left_inv := sorry
--  right_inv := sorry

-- TODO: this probably needs more assumptions
lemma induced_comp (G : D ⥤ E) (J : GrothendieckTopology E) :
    (F ⋙ G).inducedTopology' J = F.inducedTopology' (G.inducedTopology' J) := by
  refine le_antisymm ?_ (induced_induced_le _ _ _)
  apply CategoryTheory.le_topology_of_closedSieves_isSheaf
  sorry

lemma Functor.op_comp_isSheaf_of_isSheaf_type (J : GrothendieckTopology C)
    {K : GrothendieckTopology D} [F.IsContinuous J K] {G : Dᵒᵖ ⥤ Type*} (h : Presieve.IsSheaf K G) :
    Presieve.IsSheaf J (F.op ⋙ G) := by
  rw [← isSheaf_iff_isSheaf_of_type] at h ⊢
  exact F.op_comp_isSheaf_of_isSheaf _ _ _ h

/-- Continuous functors send covering sieves to covering sieves.
The converse is false, see [SGA4, III, Exemple 1.9.3][sga4]. -/
lemma CoverPreserving.of_isContinuous (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] :
    CoverPreserving J K F where
  cover_preserve {X S} hS := by
    rw [K.mem_iff_isSheafFor_closedSieves]
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    rw [Sieve.ofArrows, ← Sieve.generate_map_eq_functorPushforward,
      ← Presieve.isSheafFor_iff_generate, Presieve.map_ofArrows]
    have := Functor.op_comp_isSheaf_of_isSheaf_type F J (classifier_isSheaf K) _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate] at this
    rw [Presieve.isSheafFor_arrows_iff] at this ⊢
    intro x hx
    refine this x fun i j Z gi gj hgij ↦ hx _ _ _ _ _ ?_
    simp [← Functor.map_comp, hgij]

-- TODO: is this true?
lemma foo [F.LocallyCoverDense J] [F.IsLocallyFull J] [F.IsLocallyFaithful J] :
    F.IsContinuous (F.inducedTopology J) J where
  op_comp_isSheaf_of_types G := by
    intro X S hS
    obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
    simp only [Functor.mem_inducedTopology_sieves_iff, Sieve.ofArrows,
      ← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows] at hS
    have := G.property
    rw [isSheaf_iff_isSheaf_of_type] at this
    have := this _ hS
    rw [← Presieve.isSheafFor_iff_generate] at this ⊢
    rw [Presieve.isSheafFor_arrows_iff] at this ⊢
    intro x hx
    refine this x ?_
    intro i j Z gi gj hgij
    have := hx i j
    dsimp at this gi gj hgij
    -- apply hx
    simp
    -- apply Functor.IsLocallyFull.ext
    sorry

-- TODO: can this be relaxed to `LocallyCoverDense`?
lemma inducedTopology_eq_inducedTopology' [F.IsCoverDense J] [F.IsLocallyFull J]
    [F.IsLocallyFaithful J] :
    F.inducedTopology J = F.inducedTopology' J := by
  refine le_antisymm ?_ ?_
  · rw [le_inducedTopology'_iff]
    infer_instance
  · intro X S hS
    exact (CoverPreserving.of_isContinuous _ _ _).cover_preserve hS

lemma inducedTopology'_forget (X : D) :
    (Over.forget X).inducedTopology' J = J.over X := by
  let e : (Functor.closedSieves (J.over X)).toFunctor ≅
      (Over.forget X).op ⋙ (Functor.closedSieves J).toFunctor := by
    refine NatIso.ofComponents ?_ ?_
    · intro V
      dsimp
      refine Equiv.toIso ?_
      refine Equiv.subtypeEquiv (Sieve.overEquiv _) ?_
      intro S
      refine ⟨?_, ?_⟩
      · intro h Y f hf
        rw [Sieve.overEquiv_iff]
        simp [GrothendieckTopology.Covers] at hf
        refine h _ ?_
        simp only [GrothendieckTopology.Covers]
        rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_pullback]
        simpa
      · intro h Y f hf
        simp only [GrothendieckTopology.Covers] at hf
        rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_pullback] at hf
        let e : Y ≅ Over.mk (f.left ≫ V.unop.hom) := Over.isoMk (Iso.refl _) (by simp)
        have : f = e.hom ≫ Over.homMk f.left rfl := by ext; simp [e]
        rw [this]
        apply S.downward_closed
        have := h f.left hf
        rw [Sieve.overEquiv_iff] at this
        exact this
    · intros
      ext
      simp [Sieve.overEquiv_pullback]
  refine le_antisymm ?_ ?_
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    apply Presieve.isSheaf_iso _ e.symm
    rw [← isSheaf_iff_isSheaf_of_type]
    apply Functor.op_comp_isSheaf_of_isSheaf _ _ J
    rw [isSheaf_iff_isSheaf_of_type]
    exact classifier_isSheaf J
  · rw [le_inducedTopology'_iff]
    infer_instance

end CategoryTheory
