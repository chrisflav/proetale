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

namespace ConnectedComponents

-- In the pullback `Y` of `i : T → π₀(X)` along `mk : X → π₀(X)`, the pair
-- `(f, g) : Y → X × T` is injective.
omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma fg_injective_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) : y₁ = y₂ := by
  have inst_hp := pb.hasPullback
  let E := homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
  have hE_g : ∀ y, (E y).val.1 = g y := fun y => by
    change ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
  have hE_f : ∀ y, (E y).val.2 = f y := fun y => by
    change ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
  refine E.injective (Subtype.ext (Prod.ext ?_ ?_))
  · simp only [hE_g]; exact hg
  · simp only [hE_f]; exact hf

-- Commutativity of the pullback square: `i ∘ g = mk ∘ f`.
omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma hw_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    (y : Y) : i (g y) = (f y : ConnectedComponents X) :=
  ConcreteCategory.congr_hom pb.w y

set_option linter.unusedSectionVars false in
/-- **Stacks Project 096C (second part).** If `Y` is the pullback of `i : T → π₀(X)` along
`mk : X → π₀(X)`, where `X` is `w`-local and `T` is a compact, Hausdorff, totally
disconnected space, then the preimage of the closed points of `X` along the first projection
`f : Y → X` is precisely the closed points of `Y`. -/
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  have hw := hw_of_isPullback pb
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · -- If `f y` is closed in `X`, every point `z ≠ y` of `Y` can be separated from `y`
    -- by an open: either `f z ≠ f y` (use `f ⁻¹' {f y}ᶜ`) or `g z ≠ g y` (use the
    -- `T₂` separation in `T`).
    rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    by_cases hfzy : f z = f y
    · have hgzy : g z ≠ g y := fun h => hz (fg_injective_of_isPullback pb hfzy h)
      obtain ⟨U, V, hU, _, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      refine ⟨g ⁻¹' U, fun w hw => ?_, hU.preimage g.2, hgzU⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact Set.disjoint_left.mp hUV hw hgyV
    · refine ⟨f ⁻¹' {f y}ᶜ, fun w hw => ?_, hy.isOpen_compl.preimage f.2, by simp [hfzy]⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
      rintro rfl; exact hw rfl
  · -- If `y` is closed in `Y`, then `f y` specialises to its unique closed point `x_c`
    -- in the `w`-local `X`. Lifting `(g y, x_c)` through the pullback yields `y_c ∈ Y`
    -- with `f y_c = x_c`. Componentwise specialization in the subspace
    -- `{(t, x) | i t = mk x} ⊂ T × X` gives `y ⤳ y_c`, so `y = y_c` by closedness.
    rw [Set.mem_preimage, mem_closedPoints_iff]
    rw [mem_closedPoints_iff] at hy
    haveI : SpectralSpace Y := ConnectedComponents.spectralSpace_of_isPullback pb
    obtain ⟨x_c, hx_c_closed, hfy_xc⟩ := exists_isClosed_specializes (f y)
    have hcc : ConnectedComponents.mk x_c = ConnectedComponents.mk (f y) := by
      rw [ConnectedComponents.coe_eq_coe']
      exact closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hfy_xc.mem_closure
    have hmk_eq : mk x_c = i (g y) := hcc.trans (hw y).symm
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
      rw [specializes_iff_mem_closure]
      have inst_hp := pb.hasPullback
      let E := homeoOfIso (pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
      have hE_g : ∀ y', (E y').val.1 = g y' := fun y' => by
        change ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.1 = _
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y'
      have hE_f : ∀ y', (E y').val.2 = f y' := fun y' => by
        change ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.2 = _
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y'
      have hval_spec : (E y).val ⤳ (E y_c).val := by
        rw [specializes_prod]
        refine ⟨?_, ?_⟩
        · change (E y).val.1 ⤳ (E y_c).val.1
          rw [hE_g, hE_g, hgy_c]
        · change (E y).val.2 ⤳ (E y_c).val.2
          rw [hE_f, hE_f, hfy_c]; exact hfy_xc
      have hsub_spec : E y ⤳ E y_c :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hval_spec
      exact (E.isInducing.specializes_iff.mp hsub_spec).mem_closure
    have heq : y = y_c := by
      have hmem : y_c ∈ closure ({y} : Set Y) := hy_spec_yc.mem_closure
      rw [hy.closure_eq, Set.mem_singleton_iff] at hmem
      exact hmem.symm
    rw [show f y = x_c from heq ▸ hfy_c]
    exact hx_c_closed

/-- **Stacks Project 096C (second part).** The pullback of a `w`-local space along a map
out of a compact, Hausdorff, totally disconnected space is again `w`-local. -/
@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
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
    have hf_eq : f c = f c' :=
      WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hfc)
        (mem_closedPoints_iff.mp hfc') (hyc.map f.2) (hyc'.map f.2)
    have hg_eq : g c = g c' := (hyc.map g.2).eq.symm.trans (hyc'.map g.2).eq
    exact fg_injective_of_isPullback pb hf_eq hg_eq
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.2

/-- **Stacks Project 096C (second part).** The first projection `Y → X` from the pullback
along `i : T → π₀(X)` is a `w`-local map: it is spectral (in fact proper) and sends closed
points to closed points. -/
@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f where
  toIsSpectralMap := by
    haveI := pb.spectralSpace
    haveI := wlocalSpace_of_isPullback pb
    refine ⟨f.2, ?_⟩
    -- `f` factors as `Prod.snd ∘ Subtype.val ∘ E` where `E : Y ≃ₜ {p : T × X | i p.1 = mk p.2}`
    -- is the pullback-to-subtype homeo. `Prod.snd` is proper (`T` compact), the subtype
    -- inclusion is proper (the equaliser of `i ∘ Prod.fst` and `mk ∘ Prod.snd` is closed
    -- in `T₂`), and `E` is a homeomorphism. Hence `f` is proper, hence spectral.
    have inst_hp := pb.hasPullback
    let E := homeoOfIso (pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hsnd_proper : IsProperMap (Prod.snd : T × X → X) :=
      isProperMap_snd_of_compactSpace
    have hf_eq : ∀ y, f y = (E y).val.2 := fun y' => by
      change f y' = ((pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.2
      simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
      rw [pullbackIsoProdSubtype_hom_apply]
      exact (ConcreteCategory.congr_hom pb.isoPullback_hom_snd y').symm
    have hf_proper : IsProperMap f := by
      rw [show (f : Y → X) = Prod.snd ∘ Subtype.val ∘ E from funext hf_eq]
      exact (hsnd_proper.comp hclosed.isProperMap_subtypeVal).comp E.isProperMap
    intro s hs hsc
    exact hf_proper.isSpectralMap.isCompact_preimage_of_isOpen hs hsc
  closedPoints_subset_preimage_closedPoints y hy := by
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end ConnectedComponents
