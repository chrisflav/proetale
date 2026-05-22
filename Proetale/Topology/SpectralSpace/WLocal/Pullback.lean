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

Stacks Project 096C
-/

open CategoryTheory TopCat

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- The pullback `Y` of `f : Y → X` and `i : T → ConnectedComponents X` along the canonical
projection `mk : X → ConnectedComponents X` is homeomorphic to the closed subspace
`{p : T × X // i p.1 = mk p.2}` of `T × X`. -/
private noncomputable def ConnectedComponents.pullbackHomeo
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Y ≃ₜ {p : T × X // i p.1 = ConnectedComponents.mk p.2} :=
  have := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫ pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma ConnectedComponents.pullbackHomeo_apply_fst
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) (y : Y) :
    (ConnectedComponents.pullbackHomeo pb y).val.1 = g y := by
  have := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma ConnectedComponents.pullbackHomeo_apply_snd
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) (y : Y) :
    (ConnectedComponents.pullbackHomeo pb y).val.2 = f y := by
  have := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma ConnectedComponents.fg_injective_of_isPullback
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) : y₁ = y₂ := by
  refine (ConnectedComponents.pullbackHomeo pb).injective (Subtype.ext (Prod.ext ?_ ?_))
  · rw [pullbackHomeo_apply_fst, pullbackHomeo_apply_fst, hg]
  · rw [pullbackHomeo_apply_snd, pullbackHomeo_apply_snd, hf]

set_option linter.unusedSectionVars false in
@[stacks 096C "second part"]
theorem ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    by_cases hfzy : f z = f y
    · have hgzy : g z ≠ g y := fun h ↦ hz (fg_injective_of_isPullback pb hfzy h)
      obtain ⟨U, V, hU, hV, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      refine ⟨g ⁻¹' U, fun w hw ↦ ?_, hU.preimage g.2, hgzU⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact Set.disjoint_left.mp hUV hw hgyV
    · refine ⟨f ⁻¹' {f y}ᶜ, fun w hw ↦ ?_, hy.isOpen_compl.preimage f.2, ?_⟩
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
        rintro rfl
        exact hw rfl
      · simpa using hfzy
  · have hy_closed : IsClosed ({y} : Set Y) := mem_closedPoints_iff.mp hy
    rw [Set.mem_preimage, mem_closedPoints_iff]
    have : SpectralSpace Y := pb.spectralSpace
    obtain ⟨x_c, hx_c_closed, hfy_xc⟩ := exists_isClosed_specializes (f y)
    have hcc : ConnectedComponents.mk x_c = ConnectedComponents.mk (f y) :=
      ConnectedComponents.coe_eq_coe'.mpr (closure_minimal
        (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hfy_xc.mem_closure)
    have hmk_eq : mk x_c = i (g y) :=
      hcc.trans (ConcreteCategory.congr_hom pb.w y).symm
    let y_c := pb.lift (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
      (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
      (by ext ⟨⟩; exact hmk_eq.symm) PUnit.unit
    have hgy_c : g y_c = g y := ConcreteCategory.congr_hom
      (pb.lift_fst (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
        (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
        (by ext ⟨⟩; exact hmk_eq.symm)) PUnit.unit
    have hfy_c : f y_c = x_c := ConcreteCategory.congr_hom
      (pb.lift_snd (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
        (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
        (by ext ⟨⟩; exact hmk_eq.symm)) PUnit.unit
    have hy_spec_yc : y ⤳ y_c := by
      have hval_spec : (pullbackHomeo pb y).val ⤳ (pullbackHomeo pb y_c).val := by
        rw [specializes_prod]
        refine ⟨?_, ?_⟩
        · rw [pullbackHomeo_apply_fst, pullbackHomeo_apply_fst, hgy_c]
        · rw [pullbackHomeo_apply_snd, pullbackHomeo_apply_snd, hfy_c]
          exact hfy_xc
      exact (pullbackHomeo pb).isInducing.specializes_iff.mp
        (Topology.IsInducing.subtypeVal.specializes_iff.mp hval_spec)
    have heq : y = y_c := by
      have hmem : y_c ∈ closure ({y} : Set Y) := hy_spec_yc.mem_closure
      rw [hy_closed.closure_eq, Set.mem_singleton_iff] at hmem
      exact hmem.symm
    rw [heq, hfy_c]
    exact hx_c_closed

@[stacks 096C "second part"]
theorem ConnectedComponents.wLocalSpace_of_isPullback
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    have hfc : f c ∈ closedPoints X := by
      have : c ∈ closedPoints Y := mem_closedPoints_iff.mpr hc
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at this
    have hfc' : f c' ∈ closedPoints X := by
      have : c' ∈ closedPoints Y := mem_closedPoints_iff.mpr hc'
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at this
    have hf_eq : f c = f c' := WLocalSpace.eq_of_specializes
      (mem_closedPoints_iff.mp hfc) (mem_closedPoints_iff.mp hfc')
      (hyc.map f.2) (hyc'.map f.2)
    have hg_eq : g c = g c' := (hyc.map g.2).eq.symm.trans (hyc'.map g.2).eq
    exact fg_injective_of_isPullback pb hf_eq hg_eq
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.2

@[stacks 096C "second part"]
theorem ConnectedComponents.isWLocalMap_of_isPullback
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f where
  toIsSpectralMap := by
    have := pb.spectralSpace
    have := wLocalSpace_of_isPullback pb
    refine ⟨f.2, ?_⟩
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hf_eq : (f : Y → X) = Prod.snd ∘ Subtype.val ∘ pullbackHomeo pb :=
      funext fun y ↦ (pullbackHomeo_apply_snd pb y).symm
    have hf_proper : IsProperMap (f : Y → X) := by
      rw [hf_eq]
      exact (isProperMap_snd_of_compactSpace.comp
        hclosed.isProperMap_subtypeVal).comp (pullbackHomeo pb).isProperMap
    intro s hs hsc
    exact hf_proper.isSpectralMap.isCompact_preimage_of_isOpen hs hsc
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]
