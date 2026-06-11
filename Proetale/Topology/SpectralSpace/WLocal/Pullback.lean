/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.ClosedPoints
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Pullback of w-local spaces

Stacks Project 096C
-/

open CategoryTheory TopCat Topology

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

section Prod

/-- In a product with a `T1` first factor, a singleton is closed iff the singleton of its
second coordinate is closed. -/
lemma isClosed_singleton_prod_iff {A B : Type*} [TopologicalSpace A] [T1Space A]
    [TopologicalSpace B] {p : A × B} :
    IsClosed ({p} : Set (A × B)) ↔ IsClosed ({p.2} : Set B) := by
  constructor
  · intro h
    have hx : ({p.2} : Set B) = (fun b => (p.1, b)) ⁻¹' {p} := by
      ext b
      simp [Prod.ext_iff]
    rw [hx]
    exact h.preimage (by fun_prop)
  · intro h
    rw [← Prod.mk.eta (p := p), ← Set.singleton_prod_singleton]
    exact isClosed_singleton.prod h

/-- In a product with a `T1` first factor, the closed points are exactly the points whose
second coordinate is a closed point. -/
lemma closedPoints_prod {A B : Type*} [TopologicalSpace A] [T1Space A] [TopologicalSpace B] :
    closedPoints (A × B) = Prod.snd ⁻¹' closedPoints B := by
  ext p
  simp only [mem_closedPoints_iff, Set.mem_preimage]
  exact isClosed_singleton_prod_iff

/-- The product of a profinite space and a w-local space is w-local. -/
instance WLocalSpace.prod : WLocalSpace (T × X) where
  toSpectralSpace := inferInstance
  eq_of_specializes {p c c'} hc hc' hpc hpc' := by
    obtain ⟨h1, h2⟩ := specializes_prod.mp hpc
    obtain ⟨h1', h2'⟩ := specializes_prod.mp hpc'
    refine Prod.ext (h1.eq.symm.trans h1'.eq) ?_
    exact WLocalSpace.eq_of_specializes (isClosed_singleton_prod_iff.mp hc)
      (isClosed_singleton_prod_iff.mp hc') h2 h2'
  isClosed_closedPoints := by
    rw [closedPoints_prod]
    exact WLocalSpace.isClosed_closedPoints.preimage continuous_snd

end Prod

namespace ConnectedComponents

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- The defining equation of the fiber product `T ×_{π₀(X)} X` cuts out a closed subset
of `T × X`, since `π₀(X)` is Hausdorff for spectral `X`. -/
private lemma isClosed_pullbackSet (i : C(T, ConnectedComponents X)) :
    IsClosed {p : T × X | i p.1 = mk p.2} :=
  isClosed_eq (i.continuous.comp continuous_fst) (continuous_coe.comp continuous_snd)

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- A pullback of `i : T → π₀(X)` along `X → π₀(X)` is homeomorphic to the explicit
fiber product inside `T × X`, compatibly with the two projections. -/
private lemma exists_homeomorph_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    ∃ e : Y ≃ₜ {p : T × X | i p.1 = mk p.2}, ∀ y, (e y : T × X) = (g y, f y) := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  let eY : Y ≃ₜ (Limits.pullback (ofHom i) (ofHom mkX) : TopCat) := homeoOfIso pb.isoPullback
  let eS : (Limits.pullback (ofHom i) (ofHom mkX) : TopCat) ≃ₜ
      {p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2} :=
    homeoOfIso (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX))
  refine ⟨eY.trans eS, fun y => ?_⟩
  have h1 : Limits.pullback.fst (ofHom i) (ofHom mkX) (eY y) = g y :=
    ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
  have h2 : Limits.pullback.snd (ofHom i) (ofHom mkX) (eY y) = f y :=
    ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
  have h3 := TopCat.pullbackIsoProdSubtype_hom_apply (f := ofHom i) (g := ofHom mkX) (eY y)
  calc (eS (eY y) : T × X)
      = (Limits.pullback.fst (ofHom i) (ofHom mkX) (eY y),
          Limits.pullback.snd (ofHom i) (ofHom mkX) (eY y)) := congrArg Subtype.val h3
    _ = (g y, f y) := by rw [h1, h2]

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y := by
  obtain ⟨e, -⟩ := exists_homeomorph_of_isPullback pb
  have : WLocalSpace {p : T × X | i p.1 = mk p.2} :=
    (isClosed_pullbackSet i).isClosedEmbedding_subtypeVal.wLocalSpace
  exact e.isClosedEmbedding.wLocalSpace

omit [CompactSpace T] [TotallyDisconnectedSpace T] in
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback {f : C(Y, X)}
    {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_isPullback pb
  have hclosed := isClosed_pullbackSet i
  have h1 : closedPoints {p : T × X | i p.1 = mk p.2} =
      Subtype.val ⁻¹' closedPoints (T × X) :=
    hclosed.isClosedEmbedding_subtypeVal.isEmbedding.closedPoints_eq_preimage
      (Subtype.range_val ▸ hclosed.stableUnderSpecialization)
  have h2 : closedPoints Y = e ⁻¹' closedPoints {p : T × X | i p.1 = mk p.2} :=
    e.isEmbedding.closedPoints_eq_preimage
      (e.surjective.range_eq ▸ fun _ _ _ _ => Set.mem_univ _)
  have hfeq : (f : Y → X) = Prod.snd ∘ Subtype.val ∘ e := by
    funext y
    exact (congrArg Prod.snd (he y)).symm
  rw [h2, h1, closedPoints_prod, ← Set.preimage_comp, ← Set.preimage_comp, ← hfeq]

omit [TotallyDisconnectedSpace T] in
@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_isPullback pb
  have hfeq : (f : Y → X) = Prod.snd ∘ Subtype.val ∘ e := by
    funext y
    exact (congrArg Prod.snd (he y)).symm
  refine ⟨?_, ?_⟩
  · rw [hfeq]
    exact isProperMap_snd_of_compactSpace.isSpectralMap.comp
      (((isClosed_pullbackSet i).isClosedEmbedding_subtypeVal.isProperMap.isSpectralMap).comp
        e.isProperMap.isSpectralMap)
  · exact (preimage_closedPoints_eq_closedPoints_of_isPullback pb).symm.subset

end ConnectedComponents
