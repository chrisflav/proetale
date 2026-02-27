import Mathlib.Topology.Category.TopCat.GrothendieckTopology
import Proetale.Topology.Flat.Sheaf
import Upstreamer

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

namespace CategoryTheory

open Limits

lemma Functor.op_comp_isSheaf_of_isSheaf {C D : Type*} [Category* C] [Category* D]
    {A : Type*} [Category.{w} A]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [IsContinuous.{w} F J K] (P : Dᵒᵖ ⥤ A) (h : Presheaf.IsSheaf K P) :
    Presheaf.IsSheaf J (F.op ⋙ P) :=
  F.op_comp_isSheaf J K ⟨P, h⟩

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

@[upstreamed mathlib 34977]
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

namespace TopCat

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

lemma mem_grothendieckTopology_iff {X : TopCat.{u}} {S : Sieve X} :
    S ∈ grothendieckTopology X ↔
      ∃ E : Precoverage.ZeroHypercover.{u} precoverage X, E.presieve₀ ≤ S := by
  rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ ↦ ?_, fun ⟨E, hE⟩ ↦ ?_⟩
  · obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    let E' : precoverage.ZeroHypercover X := ⟨E, hR⟩
    refine ⟨E'.restrictIndexOfSmall, le_trans (fun Y f ⟨i⟩ ↦ ?_) hle⟩
    exact Presieve.ofArrows.mk _
  · use E.presieve₀, E.mem₀

lemma precoverage_le_comap_uliftFunctor :
    precoverage.{u} ≤ precoverage.comap uliftFunctor.{v} := by
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

instance : uliftFunctor.IsContinuous grothendieckTopology grothendieckTopology := by
  apply Precoverage.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  apply precoverage_le_comap_uliftFunctor

end TopCat

namespace AlgebraicGeometry.Scheme

lemma forgetToTop_comp_forget : forgetToTop ⋙ CategoryTheory.forget TopCat = forget := rfl

instance : Scheme.forgetToTop.{u}.IsContinuous zariskiTopology TopCat.grothendieckTopology := by
  rw [zariskiTopology, grothendieckTopology]
  have : (precoverage IsOpenImmersion).PullbacksPreservedBy forgetToTop := by
    refine ⟨fun _ _ hR ↦ ⟨fun _ _ f _ hf _ ↦ ?_⟩⟩
    have : IsOpenImmersion f := hR.2 hf
    infer_instance
  apply Precoverage.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  rw [TopCat.precoverage, Precoverage.comap_inf, precoverage]
  gcongr
  · rw [← Precoverage.comap_comp, forgetToTop_comp_forget]
  · rw [MorphismProperty.comap_precoverage]
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

lemma isSheaf_grothendieckTopology_topYoneda : Presheaf.IsSheaf zariskiTopology (topYoneda T) := by
  rw [Presheaf.isSheaf_of_iso_iff (topYonedaIsoUlift T)]
  apply forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- The presheaf `U ↦ C(U, T)` is a sheaf for the fpqc topology. -/
lemma isSheaf_fpqcTopology_topYoneda : Presheaf.IsSheaf fpqcTopology (topYoneda T) := by
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_fpqcTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ ↦ ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_grothendieckTopology_topYoneda T
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
