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

open CategoryTheory TopCat Limits

universe u

namespace ConnectedComponents

section

variable {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

include pb

/-- The pullback `Y` of `i : T → π₀(X)` along `mk : X → π₀(X)` is homeomorphic to the
subspace `{p ∈ T × X | i p.1 = mk p.2}`. -/
noncomputable def subtypeHomeo : Y ≃ₜ { p : T × X // i p.1 = mk p.2 } :=
  letI : HasPullback (ofHom i) (ofHom ⟨mk, continuous_coe⟩) := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

@[simp]
lemma subtypeHomeo_apply_fst (y : Y) : (subtypeHomeo pb y).val.1 = g y := by
  letI : HasPullback (ofHom i) (ofHom ⟨mk, continuous_coe⟩) := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

@[simp]
lemma subtypeHomeo_apply_snd (y : Y) : (subtypeHomeo pb y).val.2 = f y := by
  letI : HasPullback (ofHom i) (ofHom ⟨mk, continuous_coe⟩) := pb.hasPullback
  change ((pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

/-- In the pullback square defining `Y`, the map `(f, g) : Y → X × T` is injective. -/
lemma fg_injective_of_isPullback {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) :
    y₁ = y₂ :=
  (subtypeHomeo pb).injective <| Subtype.ext <| Prod.ext
    (by rw [subtypeHomeo_apply_fst, subtypeHomeo_apply_fst, hg])
    (by rw [subtypeHomeo_apply_snd, subtypeHomeo_apply_snd, hf])

end

section

variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

include pb

@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  have hw (y : Y) : i (g y) = (f y : ConnectedComponents X) :=
    ConcreteCategory.congr_hom pb.w y
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · -- `(f y, g y)` is T1: separate any `z ≠ y` via either `f`-closedness or T2 of `T`.
    rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    by_cases hfzy : f z = f y
    · have hgzy : g z ≠ g y := fun h ↦ hz (fg_injective_of_isPullback pb hfzy h)
      obtain ⟨U, V, hU, _, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      refine ⟨g ⁻¹' U, fun w hw ↦ ?_, hU.preimage g.continuous, hgzU⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact Set.disjoint_left.mp hUV hw hgyV
    · refine ⟨f ⁻¹' {f y}ᶜ, fun w hw heq ↦ ?_, hy.isOpen_compl.preimage f.continuous,
        by simp [hfzy]⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw
      exact hw (heq ▸ rfl)
  · -- The unique closed generalization `xc` of `f y` lifts back to `yc ∈ Y` with `y ⤳ yc`;
    -- closedness of `y` forces `y = yc`, so `f y = xc`.
    rw [Set.mem_preimage, mem_closedPoints_iff]
    rw [mem_closedPoints_iff] at hy
    have : SpectralSpace Y := pb.spectralSpace
    obtain ⟨xc, hxc, hxcSpec⟩ := exists_isClosed_specializes (f y)
    have hcc : mk xc = mk (f y) := by
      rw [coe_eq_coe']
      exact closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hxcSpec.mem_closure
    have hmk_eq : mk xc = i (g y) := hcc.trans (hw y).symm
    let p₁ : TopCat.of PUnit.{u+1} ⟶ TopCat.of T :=
      TopCat.ofHom (ContinuousMap.const _ (g y))
    let p₂ : TopCat.of PUnit.{u+1} ⟶ TopCat.of X :=
      TopCat.ofHom (ContinuousMap.const _ xc)
    have hcomp : p₁ ≫ ofHom i = p₂ ≫ ofHom ⟨mk, continuous_coe⟩ := by
      ext ⟨⟩; exact hmk_eq.symm
    let yc := pb.lift p₁ p₂ hcomp PUnit.unit
    have hgyc : g yc = g y :=
      ConcreteCategory.congr_hom (pb.lift_fst p₁ p₂ hcomp) PUnit.unit
    have hfyc : f yc = xc :=
      ConcreteCategory.congr_hom (pb.lift_snd p₁ p₂ hcomp) PUnit.unit
    have hyc_spec : y ⤳ yc := by
      rw [specializes_iff_mem_closure]
      have hval_spec : (subtypeHomeo pb y).val ⤳ (subtypeHomeo pb yc).val := by
        rw [specializes_prod]
        refine ⟨?_, ?_⟩
        · rw [subtypeHomeo_apply_fst, subtypeHomeo_apply_fst, hgyc]
        · rw [subtypeHomeo_apply_snd, subtypeHomeo_apply_snd, hfyc]; exact hxcSpec
      exact ((subtypeHomeo pb).isInducing.specializes_iff.mp
        (Topology.IsInducing.subtypeVal.specializes_iff.mp hval_spec)).mem_closure
    have heq : y = yc := by
      have hmem : yc ∈ closure ({y} : Set Y) := hyc_spec.mem_closure
      rw [hy.closure_eq, Set.mem_singleton_iff] at hmem
      exact hmem.symm
    exact heq ▸ hfyc ▸ hxc

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback : WLocalSpace Y where
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
      WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hfc) (mem_closedPoints_iff.mp hfc')
        (hyc.map f.continuous) (hyc'.map f.continuous)
    -- `T` is T2, so specializations are equalities.
    have hg_eq : g c = g c' :=
      (hyc.map g.continuous).eq.symm.trans (hyc'.map g.continuous).eq
    exact fg_injective_of_isPullback pb hf_eq hg_eq
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.continuous

@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback : IsWLocalMap f where
  toIsSpectralMap := by
    have := pb.spectralSpace
    -- `f` factors as the homeomorphism `Y ≃ {p : T × X | i p.1 = mk p.2}`, closed embedding
    -- into `T × X`, then proper projection to `X`; hence `f` is proper, hence spectral.
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.continuous.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hf_eq : f = Prod.snd ∘ Subtype.val ∘ subtypeHomeo pb :=
      funext fun y ↦ (subtypeHomeo_apply_snd pb y).symm
    have hf_proper : IsProperMap f := hf_eq ▸
      (isProperMap_snd_of_compactSpace.comp hclosed.isProperMap_subtypeVal).comp
        (subtypeHomeo pb).isProperMap
    exact hf_proper.isSpectralMap
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end

end ConnectedComponents
