/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.ClosedPoints
import Proetale.Topology.SpectralSpace.WLocal.ConnectedComponents
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Proetale.Mathlib.Topology.JacobsonSpace

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

* `ConnectedComponents.pullbackHomeo`: `Y` is homeomorphic to the subspace
  `{(t, x) : T × X | i t = π x}` of `T × X`.
* `ConnectedComponents.isClosedEmbedding_prodMk_of_isPullback`: `(g, f) : Y → T × X` is
  a closed embedding.
* `ConnectedComponents.isProperMap_of_isPullback`: `f : Y → X` is proper.
* `ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback`:
  `f⁻¹ (closedPoints X) = closedPoints Y`.
* `ConnectedComponents.wlocalSpace_of_isPullback`: `Y` is w-local.
* `ConnectedComponents.isWLocalMap_of_isPullback`: `f : Y → X` is a w-local map.
-/

open CategoryTheory TopCat

universe u
variable {X Y T : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]

namespace ConnectedComponents

section IsPullback

variable {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
  (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))

include pb

/-- The pullback `Y` is homeomorphic to the subspace
`{(t, x) : T × X | i t = π x}` of `T × X` via the categorical pullback isomorphism. -/
noncomputable def pullbackHomeo :
    Y ≃ₜ {p : T × X // i p.1 = ConnectedComponents.mk p.2} :=
  haveI := pb.hasPullback
  homeoOfIso (pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _)

@[simp]
lemma pullbackHomeo_fst (y : Y) : (pullbackHomeo pb y).val.1 = g y := by
  haveI := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _).hom y).val.1 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y

@[simp]
lemma pullbackHomeo_snd (y : Y) : (pullbackHomeo pb y).val.2 = f y := by
  haveI := pb.hasPullback
  change ((pb.isoPullback ≪≫ pullbackIsoProdSubtype _ _).hom y).val.2 = _
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  rw [pullbackIsoProdSubtype_hom_apply]
  exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] [WLocalSpace X]

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- The map `(g, f) : Y → T × X` is a closed embedding. -/
lemma isClosedEmbedding_prodMk_of_isPullback :
    Topology.IsClosedEmbedding (fun y ↦ (g y, f y)) := by
  have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
    isClosed_eq (i.continuous.comp continuous_fst) (continuous_coe.comp continuous_snd)
  have h : (fun y ↦ (g y, f y)) = Subtype.val ∘ pullbackHomeo pb := by
    ext y <;> simp
  rw [h]
  exact hclosed.isClosedEmbedding_subtypeVal.comp (pullbackHomeo pb).isClosedEmbedding

omit [T2Space T] [TotallyDisconnectedSpace T] in
/-- `f : Y → X` is proper, as a base change of the proper map `T → π₀ X` along `X → π₀ X`. -/
lemma isProperMap_of_isPullback : IsProperMap f :=
  isProperMap_snd_of_compactSpace.comp
    (isClosedEmbedding_prodMk_of_isPullback pb).isProperMap

omit [CompactSpace T] [TotallyDisconnectedSpace T] in
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  rw [← (isClosedEmbedding_prodMk_of_isPullback pb).preimage_closedPoints,
    closedPoints_prod, closedPoints_eq_univ (X := T)]
  ext y
  simp

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback : WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    -- `f c, f c'` are closed points of `X`, both specialized by `f y`. By `WLocalSpace X`
    -- they coincide; `g c = g c'` follows from `T` being `T2`. Injectivity of `(g, f)`
    -- on `Y` then forces `c = c'`.
    have hfc : f c ∈ closedPoints X := by
      rw [← Set.mem_preimage, preimage_closedPoints_eq_closedPoints_of_isPullback pb]
      exact hc
    have hfc' : f c' ∈ closedPoints X := by
      rw [← Set.mem_preimage, preimage_closedPoints_eq_closedPoints_of_isPullback pb]
      exact hc'
    have hf_eq : f c = f c' :=
      WLocalSpace.eq_of_specializes (mem_closedPoints_iff.mp hfc)
        (mem_closedPoints_iff.mp hfc') (hyc.map f.continuous) (hyc'.map f.continuous)
    have hg_eq : g c = g c' :=
      (hyc.map g.continuous).eq.symm.trans (hyc'.map g.continuous).eq
    exact (isClosedEmbedding_prodMk_of_isPullback pb).injective (Prod.ext hg_eq hf_eq)
  isClosed_closedPoints := by
    rw [← preimage_closedPoints_eq_closedPoints_of_isPullback pb]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.continuous

omit [TotallyDisconnectedSpace T] in
@[stacks 096C "second part"]
theorem isWLocalMap_of_isPullback : IsWLocalMap f where
  toIsSpectralMap := (isProperMap_of_isPullback pb).isSpectralMap
  closedPoints_subset_preimage_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]

end IsPullback

end ConnectedComponents
