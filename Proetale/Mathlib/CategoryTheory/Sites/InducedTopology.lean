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

/--
The coinduced topology by a topology on `C` along a functor `F : C ⥤ D` is the finest
topology making `F` cocontinuous.
It is implemented by an explicit description of the covering sieves.
`CategoryTheory.Functor.le_coinducedTopology_iff` shows that these descriptions are equivalent.
-/
def Functor.coinducedTopology (F : C ⥤ D) (J : GrothendieckTopology C) :
    GrothendieckTopology D where
  sieves X :=
    { S | ∀ (U : C) (f : F.obj U ⟶ X), Sieve.functorPullback F (S.pullback f) ∈ J _ }
  top_mem' := by simp
  pullback_stable' X Y S f hS := by
    simp only [Set.mem_setOf_eq]
    intro U f
    rw [← Sieve.pullback_comp]
    apply hS
  transitive' X S hS R hR := by
    simp only [Set.mem_setOf_eq]
    intro U f
    apply J.transitive (hS U f)
    intro Y g hg
    simp only [Set.mem_setOf_eq] at hR
    simp only [Sieve.functorPullback_apply, Presieve.functorPullback_mem,
      Sieve.pullback_apply] at hg
    have := hR hg _ (𝟙 _)
    simp only [Sieve.pullback_id] at this
    rwa [← Sieve.functorPullback_pullback, ← Sieve.pullback_comp]

variable (F : C ⥤ D) (J : GrothendieckTopology D)

variable {F} in
lemma Functor.mem_coinducedTopology_iff {J : GrothendieckTopology C} {X : D} {S : Sieve X} :
    S ∈ F.coinducedTopology J X ↔
      ∀ (U : C) (f : F.obj U ⟶ X), Sieve.functorPullback F (S.pullback f) ∈ J _ :=
  .rfl

instance (J : GrothendieckTopology C) : F.IsCocontinuous J (F.coinducedTopology J) where
  cover_lift {U} S hS := by
    rw [Functor.mem_coinducedTopology_iff] at hS
    simpa using hS _ (𝟙 _)

lemma Functor.le_coinducedTopology_iff (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) :
    K ≤ F.coinducedTopology J ↔ F.IsCocontinuous J K := by
  refine ⟨?_, ?_⟩
  · intro h
    constructor
    intro U S hS
    simpa using h _ hS _ (𝟙 _)
  · intro h X S hS U f
    exact F.cover_lift _ K (K.pullback_stable _ hS)

lemma Functor.coinducedTopology_comp (J : GrothendieckTopology C) (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).coinducedTopology J = G.coinducedTopology (F.coinducedTopology J) := by
  refine le_antisymm ?_ ?_
  · intro X S hS
    simp only [Functor.mem_coinducedTopology_iff] at hS ⊢
    intro V f U g
    rw [← Sieve.functorPullback_pullback, ← Sieve.functorPullback_comp, ← Sieve.pullback_comp]
    apply hS
  · rw [Functor.le_coinducedTopology_iff]
    apply isCocontinuous_comp _ _ _ (F.coinducedTopology J)

lemma Functor.IsCocontinuous.of_iso {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (e : F ≅ G) [F.IsCocontinuous J K] :
    G.IsCocontinuous J K where
  cover_lift {U} S hS := by
    sorry

lemma Functor.IsCocontinuous.iff_of_iso {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} (e : F ≅ G) :
    F.IsCocontinuous J K ↔ G.IsCocontinuous J K :=
  ⟨fun _ ↦ .of_iso e, fun _ ↦ .of_iso e.symm⟩

variable {F} in
lemma Functor.coinducedTopology_eq_of_iso {J : GrothendieckTopology C} {G : C ⥤ D} (e : F ≅ G) :
    F.coinducedTopology J = G.coinducedTopology J := by
  refine le_antisymm ?_ ?_
  · rw [Functor.le_coinducedTopology_iff, Functor.IsCocontinuous.iff_of_iso e.symm]
    infer_instance
  · rw [Functor.le_coinducedTopology_iff, Functor.IsCocontinuous.iff_of_iso e]
    infer_instance

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

-- TODO: this probably needs more assumptions
lemma induced_comp
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₁} [Category.{v₁} D]
    {E : Type u₁} [Category.{v₁} E]
    (F : C ⥤ D) (G : D ⥤ E) (J : GrothendieckTopology E) :
    (F ⋙ G).inducedTopology' J = F.inducedTopology' (G.inducedTopology' J) := by
  refine le_antisymm ?_ (induced_induced_le _ _ _)
  intro U S hS
  rw [mem_inducedTopology'_iff (G := F.op.lan) (adj := F.op.lanAdjunction _)]
  intro Y f
  -- apply CategoryTheory.le_topology_of_closedSieves_isSheaf
  sorry

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

lemma inducedTopology_eq_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.inducedTopology' J = G.inducedTopology' J := by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology'_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

def Functor.weakInducedTopology : GrothendieckTopology C :=
  Precoverage.toGrothendieck (Precoverage.comap F J.toPrecoverage)

variable {F} in
lemma mem_weakInducedTopology_of_functorPushforward_mem {X : C} {S : Sieve X}
    (hS : S.functorPushforward F ∈ J _) :
    S ∈ F.weakInducedTopology J X := by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]

lemma fooo : CoverPreserving (F.weakInducedTopology J) J F where
  cover_preserve {U} S hS := by
    suffices h : ∀ (Y : C) (f : Y ⟶ U),
        Sieve.functorPushforward F (Sieve.pullback f S) ∈ J (F.obj Y) by
      simpa using h _ (𝟙 U)
    induction hS with
    | of X S hS =>
      intro Y f
      simp [GrothendieckTopology.mem_toPrecoverage_iff,
        Sieve.generate_map_eq_functorPushforward] at hS
      sorry
      --simpa [GrothendieckTopology.mem_toPrecoverage_iff,
      --  Sieve.generate_map_eq_functorPushforward] using hS
    | top X => simp
    | pullback X S _ Y f ih =>
      intros
      rw [← Sieve.pullback_comp]
      apply ih
    | transitive X S R _ _ _ _ =>
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

--lemma booasdf {X : C} (S : Sieve (F.obj X)) (hs : S ∈ J (F.obj X)) :
--    Sieve.functorPullback F S ∈ F.inducedTopology' J X := by
--  rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
--  obtain ⟨ι, Y, f, rfl⟩ := S.exists_eq_ofArrows
--  simp
--  -- rw?
--  sorry

-- this is false with only `LocallyCoverDense`.
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

lemma foobarasdfasdf (J : GrothendieckTopology C) :
    F.inducedTopology' (F.coinducedTopology J) ≤ J := by
  intro U S hS
  have : CoverPreserving (F.inducedTopology' (F.coinducedTopology J))
    (F.coinducedTopology J) F :=
    CoverPreserving.of_isContinuous _ _ _
  have := this.cover_preserve hS
  simp only [Functor.mem_coinducedTopology_iff] at this
  have := this U (𝟙 _)
  simp only [Sieve.pullback_id] at this
  refine J.superset_covering ?_ this
  sorry

lemma foobarasdfasdf' (K : GrothendieckTopology D) :
    K ≤ F.coinducedTopology (F.inducedTopology' K) := by
  rw [Functor.le_coinducedTopology_iff]
  sorry

lemma asdfasdf (J : GrothendieckTopology C) (K : GrothendieckTopology D) :
    F.inducedTopology' K ≤ J ↔ K ≤ F.coinducedTopology J := by
  refine ⟨?_, ?_⟩
  · intro h X S hS
    simp only [Functor.mem_coinducedTopology_iff]
    intro U f
    apply h
    sorry
  · sorry

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- If `F` is flat, it is continuous if and only if it preserves covers. -/
lemma Functor.isContinuous_iff_coverPreserving [RepresentablyFlat F] :
    F.IsContinuous J K ↔ CoverPreserving J K F := by
  refine ⟨fun h ↦ .of_isContinuous _ _ _, fun h ↦ ?_⟩
  apply Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _) h

lemma aux [RepresentablyFlat F] {X : C} (S : Sieve X)
    (hS : Sieve.functorPushforward F S ∈ K _) :
    S ∈ F.inducedTopology' K X := by
  rw [mem_inducedTopology'_iff (adj := F.op.lanAdjunction _)]
  intro Y f
  -- rw [GrothendieckTopology.mem_iff_isSheafFor_closedSieves]
  sorry

lemma bla [RepresentablyFlat F] : F.inducedTopology' K = F.weakInducedTopology K := by
  refine le_antisymm ?_ ?_
  · intro X S hS
    apply mem_weakInducedTopology_of_functorPushforward_mem
    apply (CoverPreserving.of_isContinuous F _ K).cover_preserve hS
  · --rw [le_inducedTopology'_iff, Functor.isContinuous_iff_coverPreserving]
    --constructor
    rw [Functor.weakInducedTopology, Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro U S hS
    simp at hS
    sorry

end CategoryTheory
