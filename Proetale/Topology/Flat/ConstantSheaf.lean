import Proetale.Topology.Flat.Sheaf

open CategoryTheory Limits

section

variable {C : Type*} [Category C] (J : GrothendieckTopology C) (U : C)
  {A : Type*} [Category* A]

noncomputable def extensionByZero
    [((Over.forget U).sheafPushforwardContinuous A (J.over U) J).IsRightAdjoint] :
    Sheaf (J.over U) A ⥤ Sheaf J A :=
  (Over.forget U).sheafPullback A (J.over U) J

end

universe w' w v₂ u₂ v u

@[simps]
def ContinuousMap.uliftEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :
    C(ULift.{v} X, ULift.{u} Y) ≃ C(X, Y) where
  toFun f := ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩
  invFun f := ⟨ULift.up ∘ f ∘ ULift.down, by fun_prop⟩

@[simps]
def TopCat.Hom.equivContinuousMap (X Y : TopCat.{u}) : (X ⟶ Y) ≃ C(X, Y) where
  toFun f := f.hom
  invFun f := ofHom f

@[simp]
lemma Topology.IsEmbedding.toHomeomorph_symm_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) (x : X) :
    hf.toHomeomorph.symm ⟨f x, by simp⟩ = x := by
  apply hf.toHomeomorph.injective
  ext
  simp

namespace CategoryTheory

open Limits

lemma Functor.op_comp_isSheaf_of_isSheaf {C D : Type*} [Category* C] [Category* D]
    {A : Type*} [Category.{w} A]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [IsContinuous.{w} F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) :=
  F.op_comp_isSheaf J K ⟨P, h⟩

@[upstreamed mathlib 34272]
lemma Precoverage.comap_morphismProperty {C D : Type*} [Category* C] [Category* D]
    (P : MorphismProperty D) (F : C ⥤ D) :
    P.precoverage.comap F = (P.inverseImage F).precoverage := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

@[upstreamed mathlib 34272]
lemma Precoverage.comap_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (G : D ⥤ E) (J : Precoverage E) :
    J.comap (F ⋙ G) = (J.comap G).comap F := by
  ext X R
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  simp

lemma MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback {C : Type*} [Category* C]
    {P : MorphismProperty C} [P.RespectsIso]
    (H : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] (_ : P g),
      ∃ (T : C) (fst : T ⟶ X) (snd : T ⟶ Y), IsPullback fst snd f g ∧ P fst) :
    P.IsStableUnderBaseChange := by
  refine .mk' fun X Y S f g _ hg ↦ ?_
  obtain ⟨T, fst, snd, h, hfst⟩ := H f g hg
  rwa [← h.isoPullback_inv_fst, P.cancel_left_of_respectsIso]

@[simp, upstreamed mathlib 34272]
lemma Sieve.arrows_top {C : Type*} [Category* C] (X : C) : (⊤ : Sieve X).arrows = ⊤ := rfl

@[upstreamed mathlib 34272]
lemma Presieve.ofArrows_le_iff {C : Type*} [Category* C] {X : C} {ι : Type*} {Y : ι → C}
    {f : ∀ i, Y i ⟶ X} {R : Presieve X} :
    Presieve.ofArrows Y f ≤ R ↔ ∀ i, R (f i) :=
  ⟨fun hle i ↦ hle _ ⟨i⟩, fun h _ g ⟨i⟩ ↦ h i⟩

@[upstreamed mathlib 34272]
lemma Sieve.functorPushforward_le_iff_le_functorPullback {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : C} (S : Sieve X) (R : Sieve (F.obj X)) :
    S.functorPushforward F ≤ R ↔ S ≤ R.functorPullback F :=
  (Sieve.functor_galoisConnection F X).le_iff_le

@[upstreamed mathlib 34272]
lemma Sieve.functorPushforward_pullback_le {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    (S.pullback f).functorPushforward F ≤ (S.functorPushforward F).pullback (F.map f) := by
  rw [Sieve.functorPushforward_le_iff_le_functorPullback, Sieve.functorPullback_pullback]
  apply Sieve.pullback_monotone
  exact Sieve.le_functorPushforward_pullback _ _

@[upstreamed mathlib 34272]
lemma Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition {C : Type*} [Category* C]
    {J : Precoverage C} [IsStableUnderComposition J] [IsStableUnderBaseChange J]
    [J.HasPullbacks] [HasIsos J] {X : C} {S : Sieve X} :
    S ∈ J.toGrothendieck X ↔ ∃ R ∈ J X, R ≤ S := by
  refine ⟨fun hS ↦ ?_, fun ⟨R, hR, hle⟩ ↦ ?_⟩
  · induction hS with
    | of X R hR =>
      use R, hR
      exact Sieve.le_generate R
    | top X =>
      exact ⟨Presieve.singleton (𝟙 X), mem_coverings_of_isIso (𝟙 X), by simp⟩
    | pullback X S hS Y f h =>
      obtain ⟨R, hR, hle⟩ := h
      have : R.HasPullbacks f := J.hasPullbacks_of_mem f hR
      refine ⟨R.pullbackArrows f, pullbackArrows_mem f hR, ?_⟩
      rw [← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]
      apply Sieve.pullback_monotone
      rwa [Sieve.generate_le_iff]
    | transitive X S T hS hT hleS hleT =>
      obtain ⟨R, hR, hle⟩ := hleS
      rw [mem_iff_exists_zeroHypercover] at hR
      obtain ⟨E, rfl⟩ := hR
      replace hleT (i : E.I₀) : ∃ (F : J.ZeroHypercover (E.X i)),
          F.presieve₀ ≤ (Sieve.pullback (E.f i) T).arrows := by
        obtain ⟨R', hR', hle'⟩ := hleT (hle _ ⟨i⟩)
        rw [mem_iff_exists_zeroHypercover] at hR'
        obtain ⟨F, rfl⟩ := hR'
        use F
      choose F hle' using hleT
      refine ⟨(E.bind F).presieve₀, (E.bind F).mem₀, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      exact hle' _ _ ⟨i.snd⟩
  · rw [← Sieve.generate_le_iff] at hle
    apply GrothendieckTopology.superset_covering _ hle
    exact generate_mem_toGrothendieck hR

@[upstreamed mathlib 34272]
lemma Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck {C : Type*} [Category* C]
    {J : Precoverage C} [IsStableUnderComposition J] [IsStableUnderBaseChange J]
    [Limits.HasPullbacks C] [HasIsos J] : J.toPretopology.toGrothendieck = J.toGrothendieck := by
  ext
  exact J.mem_toGrothendieck_iff_of_isStableUnderComposition.symm

lemma Precoverage.functorPushforward_mem_toGrothendieck {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {J : Precoverage C} {K : Precoverage D}
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks] [J.HasIsos]
    [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks] [K.HasIsos]
    (H : J ≤ K.comap F) {X : C} (S : Sieve X) (h : S ∈ J.toGrothendieck X) :
    S.functorPushforward F ∈ K.toGrothendieck (F.obj X) := by
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at h ⊢
  obtain ⟨R, hR, hle⟩ := h
  use R.map F, H _ hR
  rw [← Sieve.generate_le_iff, Sieve.generate_map_eq_functorPushforward]
  apply Sieve.functorPushforward_monotone
  rwa [Sieve.generate_le_iff]

@[simp]
lemma PreOneHypercover.map_toPreZeroHypercover {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : C} (E : PreOneHypercover X) :
    (E.map F).toPreZeroHypercover = E.toPreZeroHypercover.map F :=
  rfl

lemma PreOneHypercover.sieve₀_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : C} (E : PreOneHypercover X) :
    (E.map F).sieve₀ = E.sieve₀.functorPushforward F := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
    PreOneHypercover.map_toPreZeroHypercover, PreZeroHypercover.presieve₀_map,
    Sieve.generate_map_eq_functorPushforward]

class Functor.PreservesPairwisePullbacks {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X : C} (R : Presieve X) : Prop where
  preservesLimit (R) ⦃Y Z : C⦄ ⦃f : Y ⟶ X⦄ ⦃g : Z ⟶ X⦄ : R f → R g →
    PreservesLimit (cospan f g) F := by infer_instance

alias Functor.preservesLimit_cospan_of_mem_presieve := Functor.PreservesPairwisePullbacks.preservesLimit

instance {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F] {X : C} (R : Presieve X) :
    F.PreservesPairwisePullbacks R where

class Precoverage.PullbacksPreservedBy {C D : Type*} [Category* C] [Category* D] (J : Precoverage C)
    (F : C ⥤ D) : Prop where
  preservesPairwisePullbacks_of_mem ⦃X : C⦄ ⦃R : Presieve X⦄ :
    R ∈ J X → F.PreservesPairwisePullbacks R := by infer_instance

alias Precoverage.preservesPairwisePullbacks_of_mem :=
  Precoverage.PullbacksPreservedBy.preservesPairwisePullbacks_of_mem

instance {C D : Type*} [Category* C] [Category* D] (J : Precoverage C) (F : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan F] :
    J.PullbacksPreservedBy F where

lemma Presieve.HasPairwisePullbacks.map_of_preservesPairwisePullbacks
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X : C} (R : Presieve X)
    [F.PreservesPairwisePullbacks R] [R.HasPairwisePullbacks] :
    (R.map F).HasPairwisePullbacks where
  has_pullbacks {Y Z} := fun {f} ⟨hf⟩ g ⟨hg⟩ ↦ by
    have := HasPairwisePullbacks.has_pullbacks hf hg
    have := F.preservesLimit_cospan_of_mem_presieve _ hf hg
    exact hasPullback_of_preservesPullback F _ _

lemma Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type*) {X : C} (R : Presieve X) [R.HasPairwisePullbacks]
    [F.PreservesPairwisePullbacks R] :
    Presieve.IsSheafFor (F.op ⋙ P) R ↔ Presieve.IsSheafFor P (R.map F) := by
  have : (R.map F).HasPairwisePullbacks := .map_of_preservesPairwisePullbacks _ _
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [map_ofArrows] at this ⊢
  simp_rw [Presieve.isSheafFor_arrows_iff_pullbacks]
  dsimp [Arrows.PullbackCompatible]
  congr! 4 with x i j
  have : PreservesLimit (cospan (f i) (f j)) F :=
    F.preservesLimit_cospan_of_mem_presieve (ofArrows _ f) ⟨i⟩ ⟨j⟩
  have : HasPullback (F.map (f i)) (F.map (f j)) := hasPullback_of_preservesPullback _ _ _
  rw [← pullbackComparison_comp_fst, op_comp, Functor.map_comp,
    ← pullbackComparison_comp_snd, op_comp, Functor.map_comp]
  have : Function.Bijective (P.map (pullbackComparison F (f i) (f j)).op) := by
    rw [← isIso_iff_bijective]
    infer_instance
  exact this.1.eq_iff

lemma PreOneHypercover.sieve₁'_eq_pullback_functorPushforward {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) {X : C} (E : PreOneHypercover X) (i j : E.I₀)
    [HasPullback ((E.map F).f i) ((E.map F).f j)] [HasPullback (E.f i) (E.f j)]
    [HasPullback (F.map (E.f i)) (F.map (E.f j))] [PreservesLimit (cospan (E.f i) (E.f j)) F] :
    (E.map F).sieve₁' i j =
      Sieve.pullback (PreservesPullback.iso _ _ _).inv ((E.sieve₁' i j).functorPushforward F) := by
  refine le_antisymm ?_ ?_
  · rintro Z f ⟨W, u, v, ⟨k⟩, rfl⟩
    apply Sieve.downward_closed
    refine ⟨E.Y k, E.toPullback k, 𝟙 _, Sieve.ofArrows_mk _ _ k, ?_⟩
    simp [PreOneHypercover.toPullback, Iso.comp_inv_eq]
  · rintro Z f ⟨W, u, v, ⟨T, a, b, ⟨k⟩, rfl⟩, heq⟩
    rw [Iso.comp_inv_eq, Functor.map_comp, Category.assoc, Category.assoc] at heq
    rw [heq]
    apply Sieve.downward_closed
    apply Sieve.downward_closed
    simp only [PreOneHypercover.map_toPreZeroHypercover, PreZeroHypercover.map_X,
      PreZeroHypercover.map_f, PreOneHypercover.toPullback, PreservesPullback.iso_hom,
      map_lift_pullbackComparison]
    exact Sieve.ofArrows_mk _ _ k

lemma Precoverage.hasPairwisePullbacks_of_mem {C : Type*} [Category* C] (J : Precoverage C)
    [J.HasPullbacks] {X : C} {R : Presieve X} (hR : R ∈ J X) :
    R.HasPairwisePullbacks where
  has_pullbacks h f _ := (J.hasPullbacks_of_mem f hR).hasPullback h

lemma Precoverage.isContinuous_toGrothendieck_of_pullbacksPreservedBy {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) (J : Precoverage C) (K : Precoverage D) [J.IsStableUnderBaseChange]
    [J.HasPullbacks] [K.IsStableUnderBaseChange] [K.HasPullbacks] [J.PullbacksPreservedBy F]
    (h : J ≤ K.comap F) :
    F.IsContinuous J.toGrothendieck K.toGrothendieck where
  op_comp_isSheaf_of_types := fun ⟨G, H⟩ ↦ by
    rw [isSheaf_iff_isSheaf_of_type] at H
    rw [← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage] at H ⊢
    intro X R hR
    have : F.PreservesPairwisePullbacks R := J.preservesPairwisePullbacks_of_mem hR
    have : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact H _ (h _ hR)

end CategoryTheory

lemma Topology.IsOpenEmbedding.uliftMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) : Topology.IsOpenEmbedding (ULift.map f) :=
  .comp Homeomorph.ulift.symm.isOpenEmbedding (.comp hf <| Homeomorph.ulift.isOpenEmbedding)

namespace TopCat

/-- The morphism property on the category of topological spaces given by open embeddings. -/
def isOpenEmbedding : MorphismProperty TopCat :=
  fun _ _ f ↦ Topology.IsOpenEmbedding f

@[simp]
lemma isOpenEmbedding_iff {X Y : TopCat} (f : X ⟶ Y) :
    isOpenEmbedding f ↔ Topology.IsOpenEmbedding f := .rfl

instance : isOpenEmbedding.IsMultiplicative where
  id_mem _ := .id
  comp_mem _ _ hf hg := hg.comp hf

instance : isOpenEmbedding.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    (TopCat.homeoOfIso (asIso f)).isOpenEmbedding

lemma isPullback_restrictPreimage {X Y : TopCat} (f : X ⟶ Y) (U : Set Y) :
    IsPullback (ofHom <| ⟨(Subtype.val : f ⁻¹' U → X), by fun_prop⟩)
      (ofHom <| ⟨Set.restrictPreimage _ f, by fun_prop⟩) f
      (ofHom <| ⟨Subtype.val, by fun_prop⟩) := by
  refine ⟨⟨by ext; simp⟩, ⟨Limits.PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro s
    refine ⟨fun x ↦ ⟨s.fst x, by simp [show _ = _ by simpa using congr($(s.condition) x)]⟩, by fun_prop⟩
  · intro; rfl
  · intro s
    ext
    simpa using congr($(s.condition) _)
  · intro s m hm1 _
    ext x
    simpa using congr($(hm1) x)

instance : isOpenEmbedding.IsStableUnderBaseChange := by
  refine .of_forall_exists_isPullback fun {X Y Z} f g _ hg ↦ ?_
  let e : Y ≃ₜ Set.range g := hg.isEmbedding.toHomeomorph
  refine ⟨of (f ⁻¹' (Set.range g)), ?_, ?_, ?_, ?_⟩
  · exact (ofHom ⟨Subtype.val, by fun_prop⟩)
  · exact ofHom ⟨Set.restrictPreimage _ f, by fun_prop⟩ ≫ (isoOfHomeo e).inv
  · have := isPullback_restrictPreimage f (Set.range g)
    refine this.of_iso (Iso.refl _) (Iso.refl _) (isoOfHomeo e).symm (Iso.refl _)
      (by simp) (by simp) (by simp) ?_
    simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.eq_inv_comp]
    ext
    simp [e]
  · exact IsOpen.isOpenEmbedding_subtypeVal (hg.isOpen_range.preimage f.hom.continuous)

def zariskiPrecoverage : Precoverage TopCat.{u} :=
  Types.jointlySurjectivePrecoverage.comap (forget TopCat) ⊓ isOpenEmbedding.precoverage
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange,
    Precoverage.IsStableUnderComposition

/-- The Zariski topology on the category of topological spaces is the topology given by
jointly surjective open embeddings. -/
def zariskiTopology : GrothendieckTopology TopCat.{u} :=
  zariskiPrecoverage.toGrothendieck

lemma exists_mem_zeroHypercover_range {X : TopCat} (E : zariskiPrecoverage.ZeroHypercover X)
    (x : X) : ∃ (i : E.I₀), x ∈ Set.range (E.f i) := by
  revert x
  simpa using E.mem₀.left

lemma isOpenEmbedding_f_zeroHypercover {X : TopCat} (E : zariskiPrecoverage.ZeroHypercover X)
    (i : E.I₀) : Topology.IsOpenEmbedding (E.f i) := by
  revert i
  simpa using E.mem₀.right

instance : Precoverage.Small.{u} zariskiPrecoverage.{u} where
  zeroHypercoverSmall {X} E := by
    choose i y hy using exists_mem_zeroHypercover_range E
    refine ⟨X, i, ?_⟩
    refine ⟨?_, ?_⟩
    · dsimp
      simp only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
        PreZeroHypercover.restrictIndex_I₀, PreZeroHypercover.restrictIndex_X, Function.comp_apply,
        PreZeroHypercover.restrictIndex_f, ConcreteCategory.forget_map_eq_coe,
        Types.ofArrows_mem_jointlySurjectivePrecoverage_iff, Set.mem_range]
      intro x
      use x, y x, hy x
    · simp only [MorphismProperty.ofArrows_mem_precoverage, PreZeroHypercover.restrictIndex_I₀,
        PreZeroHypercover.restrictIndex_X, Function.comp_apply, PreZeroHypercover.restrictIndex_f,
        isOpenEmbedding_iff]
      intro x
      have := E.mem₀.2
      simp only [MorphismProperty.ofArrows_mem_precoverage, isOpenEmbedding_iff] at this
      exact this _

lemma mem_zariskiTopology_iff {X : TopCat.{u}} {S : Sieve X} :
    S ∈ zariskiTopology X ↔
      ∃ E : Precoverage.ZeroHypercover.{u} zariskiPrecoverage X, E.presieve₀ ≤ S := by
  rw [zariskiTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ ↦ ?_, fun ⟨E, hE⟩ ↦ ?_⟩
  · obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    let E' : zariskiPrecoverage.ZeroHypercover X := ⟨E, hR⟩
    refine ⟨E'.restrictIndexOfSmall, le_trans (fun Y f ⟨i⟩ ↦ ?_) hle⟩
    exact Presieve.ofArrows.mk _
  · use E.presieve₀, E.mem₀

attribute [-simp] Lake.FamilyOut.fam_eq

lemma zariskiPrecoverage_le_comap_uliftFunctor :
    zariskiPrecoverage.{u} ≤ zariskiPrecoverage.comap uliftFunctor.{v} := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  refine ⟨?_, ?_⟩
  · simp only [Presieve.map_ofArrows, Precoverage.mem_comap_iff,
      ConcreteCategory.forget_map_eq_coe, Types.ofArrows_mem_jointlySurjectivePrecoverage_iff,
      Set.mem_range]
    intro ⟨x⟩
    obtain ⟨i, y, rfl⟩ := exists_mem_zeroHypercover_range E x
    use i, ⟨y⟩
    rfl
  · simp only [Presieve.map_ofArrows, MorphismProperty.ofArrows_mem_precoverage,
      isOpenEmbedding_iff]
    intro i
    dsimp [uliftFunctor]
    apply Topology.IsOpenEmbedding.uliftMap
    apply isOpenEmbedding_f_zeroHypercover

instance [UnivLE.{w, u}] : PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} := by
  suffices PreservesLimitsOfSize.{w', u} uliftFunctor.{v, u} from
    preservesLimitsOfSize_of_univLE.{w', u} _
  refine ⟨⟨fun {K} ↦ ?_⟩⟩
  refine preservesLimit_of_preserves_limit_cone (limitConeIsLimit _) ?_
  refine .ofIsoLimit (limitConeIsLimit (K ⋙ uliftFunctor)) (.symm ?_)
  refine Cones.ext ?_ ?_
  · refine isoOfHomeo (Homeomorph.trans Homeomorph.ulift ?_)
    refine (Homeomorph.piCongr (.refl _) fun i ↦ Homeomorph.ulift.symm).subtype ?_
    simp [uliftFunctor, ULift.map, Homeomorph.ulift]
  · cat_disch

instance : uliftFunctor.IsContinuous zariskiTopology zariskiTopology := by
  apply Precoverage.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  apply zariskiPrecoverage_le_comap_uliftFunctor

instance : zariskiTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
  rw [zariskiTopology, ← Precoverage.toGrothendieck_toCoverage, Presieve.isSheaf_coverage]
  intro Y R hR
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · refine TopCat.ofHom <| ContinuousMap.liftCover (fun i ↦ Set.range (𝒰.f i)) ?_ ?_ ?_
    · intro i
      exact ⟨(x i).hom ∘ (isOpenEmbedding_f_zeroHypercover 𝒰 i).toHomeomorph.symm, by fun_prop⟩
    · intro i j y
      simp only [Precoverage.toCoverage_toPrecoverage, Set.mem_range, ContinuousMap.coe_mk,
        Function.comp_apply, forall_exists_index]
      intro xi hi xj hj
      conv_lhs => simp only [← hi]
      conv_rhs => simp only [← hj]
      rw [Topology.IsEmbedding.toHomeomorph_symm_apply]
      have := hx i j _ (TopCat.pullbackCone (𝒰.f i) (𝒰.f j)).fst
        (TopCat.pullbackCone (𝒰.f i) (𝒰.f j)).snd (TopCat.pullbackCone (𝒰.f i) (𝒰.f j)).condition
      dsimp at this
      simpa using congr($(this) ⟨(xi, xj), hi ▸ hj.symm⟩)
    · intro x
      obtain ⟨i, hi⟩ := exists_mem_zeroHypercover_range 𝒰 x
      exact ⟨i, (isOpenEmbedding_f_zeroHypercover 𝒰 i).isOpen_range.mem_nhds hi⟩
  · intro i
    dsimp
    ext x
    simp only [hom_comp, hom_ofHom, ContinuousMap.comp_apply]
    have : 𝒰.f i x = (Subtype.val : Set.range (𝒰.f i) → Y) ⟨𝒰.f i x, by simp⟩ := rfl
    rw [this, ContinuousMap.liftCover_coe]
    simp
  · intro f hf
    dsimp
    ext x
    obtain ⟨i, y, rfl⟩ := exists_mem_zeroHypercover_range 𝒰 x
    have := congr($(hf i).hom y)
    dsimp at this
    rw [this]
    have : 𝒰.f i y = (Subtype.val : Set.range (𝒰.f i) → Y) ⟨𝒰.f i y, by simp⟩ := rfl
    dsimp
    rw [this, ContinuousMap.liftCover_coe]
    simp

end TopCat

namespace AlgebraicGeometry.Scheme

lemma forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = forget := rfl

instance : Scheme.forgetToTop.{u}.IsContinuous zariskiTopology TopCat.zariskiTopology := by
  rw [zariskiTopology, grothendieckTopology, pretopology,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR ↦ ⟨fun _ _ f _ hf _ ↦ ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Precoverage.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [TopCat.zariskiPrecoverage, Precoverage.comap_inf, precoverage]
  gcongr
  · rw [← Precoverage.comap_comp, forgetToTop_comp_forget]
  · rw [Precoverage.comap_morphismProperty]
    exact MorphismProperty.precoverage_monotone fun X Y f hf ↦ f.isOpenEmbedding

variable (S : Scheme.{u}) (T : Type v) [TopologicalSpace T]

/-- The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Scheme`. This
is the presheaf `U ↦ C(U, T)`.
For universe reasons, we implement it by hand. -/
@[simps]
def topYoneda (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ Type (max v u) where
  obj U := C(U.unop, T)
  map {U V} f g := g.comp ⟨f.unop.base, f.unop.continuous⟩

noncomputable
def Zl (ℓ : Nat) [Fact ℓ.Prime] : Scheme.{u}ᵒᵖ ⥤ Type _ :=
  topYoneda (PadicInt ℓ)

def topYonedaIsoUlift :
    topYoneda T ≅ Scheme.forgetToTop.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T) :=
  NatIso.ofComponents fun U ↦ equivEquivIso <|
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

lemma isSheaf_zariskiTopology_topYoneda : Presheaf.IsSheaf zariskiTopology (topYoneda T) := by
  rw [Presheaf.isSheaf_of_iso_iff (topYonedaIsoUlift T)]
  apply forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.zariskiTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.zariskiTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The presheaf `U ↦ C(U, T)` is a sheaf for the fpqc topology. -/
lemma isSheaf_fpqcTopology_topYoneda : Presheaf.IsSheaf fpqcTopology (topYoneda T) := by
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_fpqcTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ ↦ ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_topYoneda T
  · rw [Presieve.isSheafFor_singleton]
    have : Flat (Spec.map f) := by rwa [HasRingHomProperty.Spec_iff (P := @Flat)]
    have : Topology.IsQuotientMap (Spec.map f) := Flat.isQuotientMap_of_surjective _
    intro (x : C(Spec S, T)) h
    refine ⟨?_, ?_, ?_⟩
    · refine Topology.IsQuotientMap.lift this x fun a b hfab ↦ ?_
      obtain ⟨c, rfl, rfl⟩ := Pullback.exists_preimage_pullback a b hfab
      exact congr($(h (pullback.fst (Spec.map f) (Spec.map f))
        (pullback.snd _ _) pullback.condition).1 c)
    · apply Topology.IsQuotientMap.lift_comp
    · intro y hy
      rwa [← ContinuousMap.cancel_right (Spec.map f).surjective, Topology.IsQuotientMap.lift_comp]

/-- The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Scheme`
as a sheaf in the fpqc topology. -/
@[simps]
def topYonedaSheaf : Sheaf fpqcTopology (Type _) where
  val := topYoneda T
  cond := isSheaf_fpqcTopology_topYoneda T

end AlgebraicGeometry.Scheme
