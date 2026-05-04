import Mathlib.Topology.Category.TopCat.GrothendieckTopology
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

namespace CategoryTheory

open Limits

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

end TopCat
