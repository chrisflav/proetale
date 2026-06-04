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

-- In the pullback, `y ↦ (f y, g y)` is injective: `Y` is homeomorphic to a subspace of `X × T`.
omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma fg_injective_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) : y₁ = y₂ := by
  have := pb.hasPullback
  let E := homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
  have hE_g : ∀ y, (E y).val.1 = g y := fun y ↦ by
    change ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
  have hE_f : ∀ y, (E y).val.2 = f y := fun y ↦ by
    change ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
  refine E.injective <| Subtype.ext <| Prod.ext ?_ ?_
  · simp only [hE_g]; exact hg
  · simp only [hE_f]; exact hf

-- The pullback square commutes pointwise: `i (g y) = mk (f y)`.
omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma hw_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    (y : Y) : i (g y) = (f y : ConnectedComponents X) :=
  ConcreteCategory.congr_hom pb.w y

-- In the pullback, `g` restricted to `f ⁻¹' closedPoints X` is injective.
omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma g_injective_on_preimage_closedPoints
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hy₁ : f y₁ ∈ closedPoints X) (hy₂ : f y₂ ∈ closedPoints X)
    (hg : g y₁ = g y₂) : y₁ = y₂ := by
  have hw := hw_of_isPullback pb
  have hmk : (f y₁ : ConnectedComponents X) = f y₂ :=
    (hw y₁).symm.trans (congrArg i hg ▸ hw y₂)
  have hinj := (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).bijective.1
  have hf : f y₁ = f y₂ := by
    have := @hinj ⟨f y₁, hy₁⟩ ⟨f y₂, hy₂⟩
    simp only [Function.comp] at this
    exact congrArg Subtype.val (this hmk)
  exact fg_injective_of_isPullback pb hf hg

@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · -- If `f y` is closed in `X`, then `y` is closed in `Y`: separate `y` from any other
    -- `z ∈ Y` using either the `f`-image (when `f z ≠ f y`) or the `g`-image (otherwise,
    -- using injectivity of `(f, g)` and `T2Space T`).
    rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    by_cases hfzy : f z = f y
    · have hgzy : g z ≠ g y := fun h => hz (fg_injective_of_isPullback pb hfzy h)
      obtain ⟨U, V, hU, _, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      refine ⟨g ⁻¹' U, fun w hw ↦ ?_, hU.preimage g.2, hgzU⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq; subst heq
      exact Set.disjoint_left.mp hUV hw hgyV
    · refine ⟨f ⁻¹' {f y}ᶜ, fun w hw ↦ ?_, hy.isOpen_compl.preimage f.2, by simp [hfzy]⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
      intro heq; subst heq; exact hw rfl
  · -- If `y` is closed in `Y`, find a closed-point specialization `x_c` of `f y` in `X`
    -- (using w-localness of `X` via `exists_isClosed_specializes`), lift it back through
    -- the pullback to a closed-point specialization `y_c` of `y`, and conclude `y = y_c`.
    rw [Set.mem_preimage, mem_closedPoints_iff]
    rw [mem_closedPoints_iff] at hy
    have : SpectralSpace Y := pb.spectralSpace
    obtain ⟨x_c, hx_c_closed, hfy_xc⟩ := exists_isClosed_specializes (f y)
    have hcc : ConnectedComponents.mk x_c = ConnectedComponents.mk (f y) := by
      rw [ConnectedComponents.coe_eq_coe']
      exact closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hfy_xc.mem_closure
    have hmk_eq : mk x_c = i (g y) := hcc.trans (hw_of_isPullback pb y).symm
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
    -- `y ⤳ y_c`: transfer specialization from `X × T` via the closed embedding
    -- `Y ≃ₜ {(t, x) | i t = mk x} ↪ T × X`.
    have hy_spec_yc : y ⤳ y_c := by
      rw [specializes_iff_mem_closure]
      have := pb.hasPullback
      let E := homeoOfIso (pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
      have hE_g : ∀ y', (E y').val.1 = g y' := fun y' ↦ by
        change ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.1 = _
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y'
      have hE_f : ∀ y', (E y').val.2 = f y' := fun y' ↦ by
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
      rw [hy.closure_eq] at hmem
      exact (Set.mem_singleton_iff.mp hmem).symm
    have : f y = x_c := by rw [heq, hfy_c]
    rw [this]; exact hx_c_closed

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    have hpre := preimage_closedPoints_eq_closedPoints_of_isPullback pb
    have hfc : f c ∈ closedPoints X := by
      have : c ∈ closedPoints Y := mem_closedPoints_iff.mpr hc
      rwa [← hpre] at this
    have hfc' : f c' ∈ closedPoints X := by
      have : c' ∈ closedPoints Y := mem_closedPoints_iff.mpr hc'
      rwa [← hpre] at this
    have hfyc : f y ⤳ f c := hyc.map f.2
    have hfyc' : f y ⤳ f c' := hyc'.map f.2
    have hf_eq : f c = f c' :=
      WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hfc)
        (mem_closedPoints_iff.mp hfc') hfyc hfyc'
    have hg_eq : g c = g c' :=
      (hyc.map g.2).eq.symm.trans (hyc'.map g.2).eq
    exact fg_injective_of_isPullback pb hf_eq hg_eq
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.2

@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f where
  toIsSpectralMap := by
    have := pb.spectralSpace
    have := wlocalSpace_of_isPullback pb
    refine ⟨f.2, ?_⟩
    -- `f` is proper: it factors as `Prod.snd ∘ Subtype.val ∘ E`, where
    -- `E : Y ≃ₜ {p : T × X | i p.1 = mk p.2}`, the subtype is closed in `T × X`
    -- (equalizer of two continuous maps to the T2 space `ConnectedComponents X`),
    -- and `Prod.snd : T × X → X` is proper since `T` is compact.
    have := pb.hasPullback
    let E := homeoOfIso (pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hf_eq : ∀ y, f y = (E y).val.2 := fun y' ↦ by
      change f y' = ((pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.2
      simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
      rw [pullbackIsoProdSubtype_hom_apply]
      exact (ConcreteCategory.congr_hom pb.isoPullback_hom_snd y').symm
    have hf_proper : IsProperMap f := by
      have heq : f = Prod.snd ∘ Subtype.val ∘ E := funext hf_eq
      rw [heq]
      exact (isProperMap_snd_of_compactSpace.comp hclosed.isProperMap_subtypeVal).comp
        E.isProperMap
    intro s hs hsc
    exact hf_proper.isSpectralMap.isCompact_preimage_of_isOpen hs hsc
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end ConnectedComponents
