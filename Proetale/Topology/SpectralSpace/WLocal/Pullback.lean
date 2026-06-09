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

This file proves the second part of Stacks Project 096C: if `X` is a w-local space and `T`
is a compact Hausdorff totally disconnected space, then the pullback `Y` of any continuous
map `i : T → π₀(X)` along the quotient map `mk : X → π₀(X)` is again w-local, the projection
`Y → X` is a w-local map, and the closed points of `Y` are exactly the preimage of the
closed points of `X`.

## Main results

* `ConnectedComponents.subtypeHomeoOfIsPullback`: the canonical homeomorphism between the
  pullback `Y` and the subspace `{(t, x) ∈ T × X // i t = mk x}` of the product.
* `ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback`: the closed
  points of `Y` are exactly the preimage of the closed points of `X`.
* `ConnectedComponents.wlocalSpace_of_isPullback`: `Y` is a w-local space.
* `ConnectedComponents.isWLocalMap_of_isPullback`: `Y → X` is a w-local map.

-/

open CategoryTheory TopCat

universe u

namespace ConnectedComponents

variable {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
  {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
  (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

/-- The canonical homeomorphism between the pullback `Y` of `i : T → π₀(X)` along
`mk : X → π₀(X)` and the subspace `{(t, x) ∈ T × X | i t = mk x}` of the product. -/
noncomputable def subtypeHomeoOfIsPullback :
    Y ≃ₜ {p : T × X // i p.1 = ConnectedComponents.mk p.2} :=
  letI := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

@[simp]
lemma subtypeHomeoOfIsPullback_apply_fst (y : Y) :
    (subtypeHomeoOfIsPullback pb y).val.1 = g y := by
  letI := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

@[simp]
lemma subtypeHomeoOfIsPullback_apply_snd (y : Y) :
    (subtypeHomeoOfIsPullback pb y).val.2 = f y := by
  letI := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

include pb in
/-- The pair `(g, f) : Y → T × X` from the pullback `Y` is injective. -/
lemma pair_injective_of_isPullback {y₁ y₂ : Y} (hg : g y₁ = g y₂) (hf : f y₁ = f y₂) :
    y₁ = y₂ :=
  (subtypeHomeoOfIsPullback pb).injective <| Subtype.ext <| Prod.ext
    (by simp [hg]) (by simp [hf])

include pb in
/-- Given `(t, x) ∈ T × X` with `i t = mk x`, there is a point `y` in the pullback `Y`
with `g y = t` and `f y = x`. -/
lemma exists_apply_eq_of_isPullback {t : T} {x : X} (h : i t = mk x) :
    ∃ y : Y, g y = t ∧ f y = x := by
  refine ⟨(subtypeHomeoOfIsPullback pb).symm ⟨(t, x), h⟩, ?_, ?_⟩
  · rw [← subtypeHomeoOfIsPullback_apply_fst pb, Homeomorph.apply_symm_apply]
  · rw [← subtypeHomeoOfIsPullback_apply_snd pb, Homeomorph.apply_symm_apply]

include pb in
/-- Specialization in the pullback `Y` is detected by specialization of both projections. -/
lemma specializes_of_specializes_of_isPullback {y₁ y₂ : Y} (hg : g y₁ ⤳ g y₂)
    (hf : f y₁ ⤳ f y₂) : y₁ ⤳ y₂ := by
  have hval : ((subtypeHomeoOfIsPullback pb y₁) : T × X) ⤳
      ((subtypeHomeoOfIsPullback pb y₂) : T × X) := by
    rw [specializes_prod]
    refine ⟨?_, ?_⟩
    · simpa using hg
    · simpa using hf
  exact (subtypeHomeoOfIsPullback pb).isInducing.specializes_iff.mp
    (Topology.IsInducing.subtypeVal.specializes_iff.mp hval)

include pb in
/-- If the image of `y` under `f` is a closed point of `X`, then `y` is a closed point of
the pullback `Y`. This direction does not need `X` to be w-local. -/
lemma mem_closedPoints_of_mem_closedPoints_of_isPullback [T2Space T] {y : Y}
    (hy : f y ∈ closedPoints X) : y ∈ closedPoints Y := by
  rw [mem_closedPoints_iff] at hy
  rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  by_cases hfzy : f z = f y
  · have hgzy : g z ≠ g y := fun h ↦ hz (pair_injective_of_isPullback pb h hfzy)
    obtain ⟨U, V, hU, _, hgzU, hgyV, hUV⟩ := t2_separation hgzy
    refine ⟨g ⁻¹' U, fun w hw ↦ ?_, hU.preimage g.continuous, hgzU⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact Set.disjoint_left.mp hUV hw hgyV
  · refine ⟨f ⁻¹' {f y}ᶜ, fun w hw ↦ ?_, hy.isOpen_compl.preimage f.continuous,
      by simp [hfzy]⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
    rintro rfl
    exact hw rfl

section Main

variable [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

include pb

/-- **Stacks Project 096C (second part).** If `Y` is the pullback of `i : T → π₀(X)` along
`mk : X → π₀(X)`, where `X` is `w`-local and `T` is a compact, Hausdorff, totally
disconnected space, then the preimage of the closed points of `X` along the first projection
`f : Y → X` is precisely the closed points of `Y`. -/
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  ext y
  refine ⟨mem_closedPoints_of_mem_closedPoints_of_isPullback pb, fun hy ↦ ?_⟩
  -- If `y` is closed in `Y`, then `f y` specialises to its unique closed point `x_c`
  -- in the `w`-local `X`. Lift `(g y, x_c)` through the pullback to get `y_c ∈ Y` with
  -- `f y_c = x_c`. Componentwise specialization gives `y ⤳ y_c`, so `y = y_c` by closedness.
  rw [Set.mem_preimage, mem_closedPoints_iff]
  rw [mem_closedPoints_iff] at hy
  have : SpectralSpace Y := pb.spectralSpace
  obtain ⟨x_c, hx_c_closed, hfy_xc⟩ := exists_isClosed_specializes (f y)
  have hmk_eq : ConnectedComponents.mk x_c = ConnectedComponents.mk (f y) := by
    rw [ConnectedComponents.coe_eq_coe']
    exact closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
      isClosed_connectedComponent hfy_xc.mem_closure
  have hi_eq : i (g y) = mk x_c :=
    (ConcreteCategory.congr_hom pb.w y).trans hmk_eq.symm
  obtain ⟨y_c, hgy_c, hfy_c⟩ := exists_apply_eq_of_isPullback pb hi_eq
  have hy_spec_yc : y ⤳ y_c := specializes_of_specializes_of_isPullback pb
    (by rw [hgy_c]) (by rw [hfy_c]; exact hfy_xc)
  have heq : y = y_c := by
    have hmem : y_c ∈ closure ({y} : Set Y) := hy_spec_yc.mem_closure
    rw [hy.closure_eq, Set.mem_singleton_iff] at hmem
    exact hmem.symm
  rw [heq, hfy_c]
  exact hx_c_closed

/-- **Stacks Project 096C (second part).** The pullback of a `w`-local space along a map
out of a compact, Hausdorff, totally disconnected space is again `w`-local. -/
@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback : WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    have hfc : f c ∈ closedPoints X := by
      have h : c ∈ closedPoints Y := mem_closedPoints_iff.mpr hc
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at h
    have hfc' : f c' ∈ closedPoints X := by
      have h : c' ∈ closedPoints Y := mem_closedPoints_iff.mpr hc'
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at h
    have hf_eq : f c = f c' :=
      WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hfc)
        (mem_closedPoints_iff.mp hfc') (hyc.map f.continuous) (hyc'.map f.continuous)
    have hg_eq : g c = g c' :=
      (hyc.map g.continuous).eq.symm.trans (hyc'.map g.continuous).eq
    exact pair_injective_of_isPullback pb hg_eq hf_eq
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.continuous

/-- **Stacks Project 096C (second part).** The first projection `Y → X` from the pullback
along `i : T → π₀(X)` is a `w`-local map: it is spectral (in fact proper) and sends closed
points to closed points. -/
@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback : IsWLocalMap f where
  toIsSpectralMap := by
    -- `f` factors as `Prod.snd ∘ Subtype.val ∘ subtypeHomeoOfIsPullback pb`. Since `T` is
    -- compact, `Prod.snd : T × X → X` is proper; the subspace
    -- `{(t, x) | i t = mk x}` is closed in `T × X` (Hausdorff equaliser), hence its inclusion
    -- is proper; and a homeomorphism is proper. Therefore `f` is proper, hence spectral.
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.continuous.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hf_eq : (f : Y → X) = Prod.snd ∘ Subtype.val ∘ subtypeHomeoOfIsPullback pb :=
      funext fun y ↦ (subtypeHomeoOfIsPullback_apply_snd pb y).symm
    have hf_proper : IsProperMap f := by
      rw [hf_eq]
      exact (isProperMap_snd_of_compactSpace.comp hclosed.isProperMap_subtypeVal).comp
        (subtypeHomeoOfIsPullback pb).isProperMap
    exact hf_proper.isSpectralMap
  closedPoints_subset_preimage_closedPoints _ hy := by
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end Main

end ConnectedComponents
