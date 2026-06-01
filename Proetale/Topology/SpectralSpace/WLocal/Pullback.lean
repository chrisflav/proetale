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

We formalise the second part of [Stacks 096C](https://stacks.math.columbia.edu/tag/096C):
given a w-local space `X`, a profinite space `T`, a continuous map `i : T → π₀ X`, and
a pullback square

```
      Y ─g─> T
      │      │
      f      i
      v      v
      X ─π─> π₀ X
```

(with `π : X → π₀ X` the canonical map to connected components), the total space `Y` is
again w-local, the projection `f : Y → X` is a w-local map, and `f⁻¹ (X_max) = Y_max`
where `X_max`/`Y_max` denote the closed points.

## Main results

* `ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback`:
  `f⁻¹ (closedPoints X) = closedPoints Y`.
* `ConnectedComponents.wlocalSpace_of_isPullback`: `Y` is w-local.
* `ConnectedComponents.isWLocalMap_of_isPullback`: `f : Y → X` is a w-local map.
-/

open CategoryTheory TopCat

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

namespace ConnectedComponents

section IsPullback

variable {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
  (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

include pb

/-- The pullback `Y` is homeomorphic to the subspace
`{(t, x) : T × X | i t = π x}` of `T × X` via the categorical pullback isomorphism. -/
private noncomputable def pullbackHomeo :
    Y ≃ₜ {p : T × X // i p.1 = ConnectedComponents.mk p.2} :=
  haveI := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _)

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma pullbackHomeo_fst (y : Y) : (pullbackHomeo pb y).val.1 = g y := by
  haveI := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
private lemma pullbackHomeo_snd (y : Y) : (pullbackHomeo pb y).val.2 = f y := by
  haveI := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- `(g, f)` jointly identifies points of `Y`, because `Y` embeds into `T × X` via the
homeomorphism `pullbackHomeo`. -/
private lemma fg_injective_of_isPullback
    {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) : y₁ = y₂ := by
  apply (pullbackHomeo pb).injective
  apply Subtype.ext
  apply Prod.ext
  · simp only [pullbackHomeo_fst]; exact hg
  · simp only [pullbackHomeo_snd]; exact hf

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- The pointwise form of the commuting square `g ≫ i = f ≫ π`. -/
private lemma hw_of_isPullback (y : Y) : i (g y) = (f y : ConnectedComponents X) :=
  ConcreteCategory.congr_hom pb.w y

set_option linter.unusedSectionVars false in
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  have hw := hw_of_isPullback pb
  ext y; constructor
  · -- Forward: separate `y` from any `z ≠ y` using either `f` (when `f z ≠ f y`, via the
    -- closed point `f y`) or `g` (when `f z = f y`, via `T` being `T2`).
    intro hy
    rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    by_cases hfzy : f z = f y
    · have hgzy : g z ≠ g y := fun h => hz (fg_injective_of_isPullback pb hfzy h)
      obtain ⟨U, V, hU, hV, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      exact ⟨g ⁻¹' U, fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq; subst heq
        exact Set.disjoint_left.mp hUV hw hgyV,
        hU.preimage g.2, hgzU⟩
    · exact ⟨f ⁻¹' {f y}ᶜ, fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
        intro heq; subst heq; exact hw rfl,
        hy.isOpen_compl.preimage f.2,
        by simp [hfzy]⟩
  · -- Backward: `y` closed implies `f y` closed. Pick the closed point `x_c` of `X`
    -- specialized by `f y` (using `WLocalSpace X`), then lift to `y_c ∈ Y` with
    -- `f y_c = x_c` and `g y_c = g y`. Componentwise specialization gives `y ⤳ y_c`,
    -- so `y = y_c` and `f y = x_c`.
    intro hy
    rw [Set.mem_preimage, mem_closedPoints_iff]
    rw [mem_closedPoints_iff] at hy
    haveI : SpectralSpace Y := pb.spectralSpace
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
      have hval_spec : (pullbackHomeo pb y).val ⤳ (pullbackHomeo pb y_c).val := by
        rw [specializes_prod]
        refine ⟨?_, ?_⟩
        · change (pullbackHomeo pb y).val.1 ⤳ (pullbackHomeo pb y_c).val.1
          rw [pullbackHomeo_fst, pullbackHomeo_fst, hgy_c]
        · change (pullbackHomeo pb y).val.2 ⤳ (pullbackHomeo pb y_c).val.2
          rw [pullbackHomeo_snd, pullbackHomeo_snd, hfy_c]; exact hfy_xc
      have hsub_spec : pullbackHomeo pb y ⤳ pullbackHomeo pb y_c :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hval_spec
      exact ((pullbackHomeo pb).isInducing.specializes_iff.mp hsub_spec).mem_closure
    have heq : y = y_c := by
      have hmem : y_c ∈ closure ({y} : Set Y) := hy_spec_yc.mem_closure
      rw [hy.closure_eq, Set.mem_singleton_iff] at hmem
      exact hmem.symm
    have : f y = x_c := by rw [heq, hfy_c]
    rw [this]; exact hx_c_closed

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback : WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    -- `f c, f c'` are closed points of `X`, both specialized by `f y`. By `WLocalSpace X`
    -- they coincide; `g c = g c'` follows from `T` being `T2`. Injectivity of `(g, f)`
    -- on `Y` then forces `c = c'`.
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

@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback : IsWLocalMap f where
  toIsSpectralMap := by
    haveI := pb.spectralSpace
    haveI := wlocalSpace_of_isPullback pb
    refine ⟨f.2, ?_⟩
    -- `f` factors as `Y ≃ₜ {p : T × X // i p.1 = π p.2} ↪ T × X ─snd→ X`. The first map is a
    -- homeomorphism, the second a closed embedding (since `T` is `T2`), and the third is
    -- proper (since `T` is compact). The composition is proper, hence spectral.
    have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
      isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
    have hsnd_proper : IsProperMap (Prod.snd : T × X → X) :=
      isProperMap_snd_of_compactSpace
    have hf_proper : IsProperMap f := by
      have heq : f = Prod.snd ∘ Subtype.val ∘ pullbackHomeo pb :=
        funext fun y => (pullbackHomeo_snd pb y).symm
      rw [heq]
      exact (hsnd_proper.comp hclosed.isProperMap_subtypeVal).comp (pullbackHomeo pb).isProperMap
    intro s hs hsc
    exact hf_proper.isSpectralMap.isCompact_preimage_of_isOpen hs hsc
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end IsPullback

end ConnectedComponents
