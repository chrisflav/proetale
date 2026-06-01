/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.ClosedPoints
import Proetale.Topology.SpectralSpace.WLocal.ConnectedComponents
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Pullback of w-local spaces

For `X` a w-local space, `T` a profinite space and `i : T → π₀(X)`, the pullback
`Y = X ×_{π₀(X)} T` is again w-local. This is the second part of Stacks 096C.

## Main results

* `ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback`:
  the closed points of `Y` are precisely the preimage of the closed points of `X`.
* `ConnectedComponents.wlocalSpace_of_isPullback`: `Y` is w-local.
* `ConnectedComponents.isWLocalMap_of_isPullback`: the projection `Y → X` is w-local.
-/

open CategoryTheory TopCat Topology

namespace ConnectedComponents

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

/-- The homeomorphism of `Y` with the explicit subspace
`{p : T × X // i p.1 = mk p.2}` of `T × X` provided by the pullback. -/
private noncomputable def pullbackHomeo :
    Y ≃ₜ {p : T × X // i p.1 = ConnectedComponents.mk p.2} :=
  haveI := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
@[simp] private lemma pullbackHomeo_val_fst (y : Y) :
    ((pullbackHomeo pb y).val).1 = g y := by
  have := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype (ofHom i)
    (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
@[simp] private lemma pullbackHomeo_val_snd (y : Y) :
    ((pullbackHomeo pb y).val).2 = f y := by
  have := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype (ofHom i)
    (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
include pb in
/-- The map `y ↦ (g y, f y) : Y → T × X` is a closed embedding: the pullback `Y` is
homeomorphic to the closed subspace `{p : T × X // i p.1 = mk p.2}`. -/
private lemma isClosedEmbedding_prodMk_of_isPullback :
    IsClosedEmbedding (fun y => (g y, f y) : Y → T × X) := by
  have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
    isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
  have hval_ce : IsClosedEmbedding ((Subtype.val : _ → T × X) ∘ pullbackHomeo pb) :=
    hclosed.isClosedEmbedding_subtypeVal.comp (pullbackHomeo pb).isClosedEmbedding
  convert hval_ce using 1
  ext y
  · exact (pullbackHomeo_val_fst pb y).symm
  · exact (pullbackHomeo_val_snd pb y).symm

omit [TotallyDisconnectedSpace T] in
include pb in
/-- The closed points of the pullback `Y = X ×_{π₀(X)} T` are precisely the preimage of
the closed points of `X`. -/
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  have hce := isClosedEmbedding_prodMk_of_isPullback pb
  ext y
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  refine ⟨fun hfy => ?_, fun hy => ?_⟩
  · -- `{(g y, f y)} = {g y} ×ˢ {f y}` is closed (T2 gives `{g y}` closed, hypothesis gives
    -- `{f y}` closed); pulling back along the closed embedding `(g, f)` gives `{y}` closed.
    have hprod : IsClosed ({(g y, f y)} : Set (T × X)) := by
      rw [← Set.singleton_prod_singleton]
      exact isClosed_singleton.prod hfy
    rw [hce.isClosed_iff_image_isClosed, Set.image_singleton]
    exact hprod
  · -- `{y}` closed maps to a closed `{(g y, f y)}` under the closed embedding,
    -- and `Prod.snd` is a closed map because `T` is compact, so `{f y}` is closed.
    have himg : IsClosed ((fun y' => (g y', f y')) '' {y} : Set (T × X)) :=
      hce.isClosedMap _ hy
    rw [Set.image_singleton] at himg
    simpa using isClosedMap_snd_of_compactSpace _ himg

include pb in
/-- The pullback `Y = X ×_{π₀(X)} T` of a w-local space `X` along a profinite space `T` is
again w-local. -/
@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback : WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    have hpre := preimage_closedPoints_eq_closedPoints_of_isPullback pb
    have hfc : IsClosed {f c} := by
      have : c ∈ closedPoints Y := mem_closedPoints_iff.mpr hc
      rw [← hpre] at this
      exact mem_closedPoints_iff.mp this
    have hfc' : IsClosed {f c'} := by
      have : c' ∈ closedPoints Y := mem_closedPoints_iff.mpr hc'
      rw [← hpre] at this
      exact mem_closedPoints_iff.mp this
    have hf_eq : f c = f c' :=
      WLocalSpace.eq_of_specializes hfc hfc' (hyc.map f.2) (hyc'.map f.2)
    -- Specializations in a T2 space (here `T`) are equalities.
    have hg_eq : g c = g c' := (hyc.map g.2).eq.symm.trans (hyc'.map g.2).eq
    exact (isClosedEmbedding_prodMk_of_isPullback pb).injective (Prod.ext hg_eq hf_eq)
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.2

omit [TotallyDisconnectedSpace T] in
include pb in
/-- The projection `f : Y → X` from the pullback `Y = X ×_{π₀(X)} T` is a w-local map. -/
@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback : IsWLocalMap (f : Y → X) where
  toIsSpectralMap := by
    -- `f` factors as `Prod.snd ∘ (g, f) : Y → T × X → X`. The first map is a closed embedding
    -- and `Prod.snd` is proper because `T` is compact. Proper maps are spectral.
    change IsSpectralMap (Prod.snd ∘ (fun y => (g y, f y) : Y → T × X))
    exact (isProperMap_snd_of_compactSpace.comp
      (isClosedEmbedding_prodMk_of_isPullback pb).isProperMap).isSpectralMap
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end ConnectedComponents
