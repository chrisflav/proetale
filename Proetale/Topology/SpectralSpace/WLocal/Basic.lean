/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.JacobsonSpace
import Proetale.Mathlib.Topology.Separation.Basic
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.Constructible

/-!
#### w-local spaces

In this file we define w-local spaces. These are spectral spaces in which every point
specializes to a unique closed point and where the set of closed points is closed.
-/

/--
A spectral space is w-local if every point specializes to a unique closed point
and the set of closed points is closed.
Note: In a spectral space, every point specializes to a closed point, so we only require
the uniqueness.
-/
class WLocalSpace (X : Type*) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- Any two closed specializations of a point are equal. -/
  eq_of_specializes {x c c' : X} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hxc : x ⤳ c) (hxc' : x ⤳ c') : c = c'
  /-- The set of closed points is closed. -/
  isClosed_closedPoints : IsClosed (closedPoints X)

attribute [instance] WLocalSpace.isClosed_closedPoints


/-- A w-local map is a spectral map that maps closed points to closed points. -/
@[mk_iff]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop
    extends IsSpectralMap f where
  preimage_closedPoints : f ⁻¹' (closedPoints Y) ⊆ closedPoints X

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
      toIsSpectralMap := IsSpectralMap.comp hg.toIsSpectralMap hf.toIsSpectralMap
      preimage_closedPoints := fun _ hx => hf.preimage_closedPoints <|
        hg.preimage_closedPoints <| Set.mem_preimage.2 <| hx

theorem Topology.Test
  {f : X → Y} (hf : IsEmbedding f)
  (h : StableUnderSpecialization (Set.range f)) {x : X}
  (hx : IsClosed {x}) : IsClosed {f x} := by
  rw [← closure_eq_iff_isClosed]
  have : closure {x} = f ⁻¹' closure (f '' {x}) := hf.closure_eq_preimage_closure_image {x}
  rw [Set.image_singleton] at this
  have hx_closed : closure {x} = {x} := closure_eq_iff_isClosed.mpr hx
  rw [hx_closed] at this
  have key : closure {f x} ∩ Set.range f = {f x} := by
    ext y
    constructor
    · intro ⟨hy_closure, y_in_range⟩
      obtain ⟨z, rfl⟩ := y_in_range
      have hz : z ∈ f ⁻¹' closure {f x} := hy_closure
      rw [← this] at hz
      simp at hz
      rw [hz]
      rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      constructor
      · exact subset_closure rfl
      · exact Set.mem_range_self x
  have closure_sub_range : closure {f x} ⊆ Set.range f := by
    intro y hy
    have : f x ⤳ y := by
      rw [specializes_iff_mem_closure]
      exact hy
    exact h this (Set.mem_range_self x)
  rw [← key]
  ext y
  constructor
  · intro hy
    have fx_in_range : f x ∈ Set.range f := ⟨x, rfl⟩
    have singleton_inter : {f x} ∩ Set.range f = {f x} :=
      Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr fx_in_range)
    have closure_fx_eq : closure {f x} = {f x} := by
      have : closure {f x} = closure {f x} ∩ Set.range f :=
        (Set.inter_eq_self_of_subset_left closure_sub_range).symm
      rw [this, key]
    rw [closure_fx_eq, singleton_inter] at hy ⊢
    simpa [closure_fx_eq] using hy
  · apply subset_closure

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X := by
  have closedPoint_maps {x : X} (hx : IsClosed ({x} : Set X)) :
      IsClosed ({f x} : Set Y) := Test hf h hx
  refine {
  eq_of_specializes := by
    intro x c c' hc hc' hxc hxc'
    -- Map specializations into `Y` using inducing.
    have hfxc : f x ⤳ f c := (hf.1.specializes_iff (x := x) (y := c)).2 hxc
    have hfxc' : f x ⤳ f c' := (hf.1.specializes_iff (x := x) (y := c')).2 hxc'
    -- Closedness of the images of closed points.
    have hfc_closed : IsClosed ({f c} : Set Y) := closedPoint_maps (x := c) hc
    have hfc'_closed : IsClosed ({f c'} : Set Y) := closedPoint_maps (x := c') hc'
    have : f c = f c' :=
      WLocalSpace.eq_of_specializes hfc_closed hfc'_closed hfxc hfxc'
    exact hf.2 this
  isClosed_closedPoints := by
    have hpre1 : f ⁻¹' closedPoints Y ⊆ closedPoints X :=
      preimage_closedPoints_subset hf.2 hf.continuous
    have hpre2 : closedPoints X ⊆ f ⁻¹' closedPoints Y := by
      intro x hx
      -- `x` is closed in `X`, so `{f x}` is closed in `Y`.
      have hx_closed : IsClosed ({x} : Set X) := (mem_closedPoints_iff (X := X) (x := x)).1 hx
      have : IsClosed ({f x} : Set Y) := closedPoint_maps (x := x) hx_closed
      -- Hence `f x` is a closed point in `Y`.
      exact (mem_closedPoints_iff (X := Y) (x := f x)).2 this
    have hEq : f ⁻¹' closedPoints Y = closedPoints X :=
      Set.Subset.antisymm hpre1 (by
        intro x hx
        exact hpre2 hx)
    -- Closedness follows from closedness of `closedPoints Y` and continuity.
    -- Use `hEq` to rewrite.
    simpa [hEq] using (WLocalSpace.isClosed_closedPoints).preimage hf.continuous
    }

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  intro x y hxy hx
  rw [mem_generalizationHull_iff] at hx ⊢
  obtain ⟨z, hzs, hxz⟩ := hx
  obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
  obtain ⟨c', hc'_closed, hyc'⟩ := exists_isClosed_specializes y
  have hxc : x ⤳ c := hxz.trans hzc
  have hxc' : x ⤳ c' := hxy.trans hyc'
  have heq : c = c' := WLocalSpace.eq_of_specializes hc_closed hc'_closed hxc hxc'
  exact ⟨c, hs hzc hzs, heq ▸ hyc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X := by
  have : SpectralSpace X := hf.spectralSpace
  exact Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    hf.isEmbedding hf.isClosed_range.stableUnderSpecialization

lemma generalizationHull.eq_sUnion_of_isCompact' (X : Type*) [TopologicalSpace X] [SpectralSpace X]
    {s : Set X} (hs : IsCompact s) :
    ∃ S ⊆ {U | IsOpen U ∧ IsCompact U}, generalizationHull s = ⋂₀ S := by

  sorry

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) := by
  -- 闭集在紧空间中是紧的
  have hs_compact : IsCompact s := hs.isCompact
  -- generalizationHull s 是紧开集的交集
  obtain ⟨S, hS_sub, hS_eq⟩ := generalizationHull.eq_sUnion_of_isCompact' X hs_compact
  -- 应用 IsClosed.of_isClosed_constructibleTopology
  apply IsClosed.of_isClosed_constructibleTopology
  · -- 证明 generalizationHull s 在 constructible topology 中是闭的
    rw [hS_eq]
    apply @isClosed_sInter _ (constructibleTopology X) S
    intro U hU
    obtain ⟨hU_open, hU_compact⟩ := hS_sub hU
    -- 紧开集 U 在 constructible topology 中是闭的
    -- 因为 Uᶜ 是闭的且 (Uᶜ)ᶜ = U 是紧的，所以 Uᶜ 在 constructible topology 中是开的
    rw [← @isOpen_compl_iff]
    have : IsClosed Uᶜ := isClosed_compl_iff.mpr hU_open
    have : IsCompact Uᶜᶜ := by simp [hU_compact]
    exact IsCompact.isOpen_constructibleTopology_of_isClosed this ‹IsClosed Uᶜ›
  · -- 证明 generalizationHull s 是 StableUnderSpecialization
    exact hs.stableUnderSpecialization.generalizationHull_of_wLocalSpace


variable {X : Type*} [TopologicalSpace X]

namespace WLocalSpace

instance spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  SpectralSpace.of_isClosed X

instance t2Space_closedPoints [WLocalSpace X] :
    T2Space (closedPoints X) :=
  SpectralSpace.t2Space_of_isClosed_singleton  closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

instance totallyDisconnected_closedPoints [WLocalSpace X] :
    TotallyDisconnectedSpace (closedPoints X) :=
  SpectralSpace.totallyDisconnectedSpace_of_isClosed_singleton closedPoints.isClosed_singleton

end WLocalSpace

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) := by
  have : CompactSpace (closedPoints X) :=
    (IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints).compactSpace
  have : T2Space (ConnectedComponents X) := t2Space_connectedComponent
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, ?_, ?_⟩
  · -- 单射性：不同闭点在不同连通分量
    intro ⟨x, hx⟩ ⟨y, hy⟩ heq
    simp only [Function.comp_apply] at heq
    -- rw [ConnectedComponents.coe_eq_coe'] at heq
    -- heq : x ∈ connectedComponent y
    -- 需要证明 x = y
    by_contra hxy
    -- 由于 closedPoints X 是 profinite (紧 Hausdorff 完全不连通)，可以用 clopen 分离 x 和 y
    have hxy' : (⟨x, hx⟩ : closedPoints X) ≠ ⟨y, hy⟩ := by
      intro h
      apply hxy
      exact h
    -- 使用 TotallySeparatedSpace 得到分离 x 和 y 的 clopen 集
    obtain ⟨U₀, hU₀_clopen, hxU₀, hyU₀⟩ := exists_isClopen_of_totally_separated hxy'
    -- U₀ 是 closedPoints X 的 clopen 子集，x ∈ U₀，y ∈ U₀ᶜ
    -- 需要将 U₀ 转换为 X 的子集
    let U₀' : Set X := Subtype.val '' U₀
    let V₀' : Set X := Subtype.val '' U₀ᶜ
    -- U₀' 和 V₀' 是 closedPoints X 在 X 中的像，它们是闭的
    have hce : Topology.IsClosedEmbedding ((↑) : closedPoints X → X) :=
      IsClosed.isClosedEmbedding_subtypeVal WLocalSpace.isClosed_closedPoints
    have hU₀'_closed : IsClosed U₀' := hce.isClosedMap U₀ hU₀_clopen.1
    have hV₀'_closed : IsClosed V₀' := hce.isClosedMap U₀ᶜ hU₀_clopen.compl.1
    -- 令 U = U₀'^g 和 V = V₀'^g 为泛化壳
    let U := generalizationHull U₀'
    let V := generalizationHull V₀'
    -- 由于 w-local 空间，闭集的泛化壳是闭的
    have hU_closed : IsClosed U := isClosed_generalizationHull_of_wLocalSpace hU₀'_closed
    have hV_closed : IsClosed V := isClosed_generalizationHull_of_wLocalSpace hV₀'_closed
    -- 证明 X = U ∪ V
    have hX_eq : (Set.univ : Set X) = U ∪ V := by
      ext z
      simp only [Set.mem_univ, true_iff]
      -- 每个点 z 特化到某个闭点
      obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
      have hc_closedPoint : c ∈ closedPoints X := mem_closedPoints_iff.mpr hc_closed
      -- c ∈ U₀' 或 c ∈ V₀'
      by_cases hcU₀ : ⟨c, hc_closedPoint⟩ ∈ U₀
      · -- c ∈ U₀'，所以 z ∈ U
        left
        rw [mem_generalizationHull_iff]
        exact ⟨c, ⟨⟨c, hc_closedPoint⟩, hcU₀, rfl⟩, hzc⟩
      · -- c ∈ V₀'
        right
        rw [mem_generalizationHull_iff]
        exact ⟨c, ⟨⟨c, hc_closedPoint⟩, hcU₀, rfl⟩, hzc⟩
    -- U 和 V 是 disjoint 的
    have hUV_disjoint : Disjoint U V := by
      rw [Set.disjoint_iff]
      intro z ⟨hzU, hzV⟩
      rw [mem_generalizationHull_iff] at hzU hzV
      obtain ⟨c, ⟨⟨c', hc'⟩, hc'U₀, hc_eq⟩, hzc⟩ := hzU
      obtain ⟨d, ⟨⟨d', hd'⟩, hd'V₀, hd_eq⟩, hzd⟩ := hzV
      simp only at hc_eq hd_eq
      subst hc_eq hd_eq
      -- c' 和 d' 都是 z 特化到的闭点
      have hc'_closed : IsClosed {c'} := mem_closedPoints_iff.mp hc'
      have hd'_closed : IsClosed {d'} := mem_closedPoints_iff.mp hd'
      -- 由于 w-local 空间中闭点唯一
      have heq : c' = d' := WLocalSpace.eq_of_specializes hc'_closed hd'_closed hzc hzd
      -- 但 c' ∈ U₀ 且 d' ∈ U₀ᶜ 矛盾
      simp_rw [heq] at hc'U₀
      exact hd'V₀ hc'U₀
    -- Uᶜ = V
    have hU_compl : Uᶜ = V := by
      ext z
      constructor
      · intro hz
        have : z ∈ U ∪ V := hX_eq ▸ Set.mem_univ z
        rcases this with hzU | hzV
        · exact (hz hzU).elim
        · exact hzV
      · intro hzV hzU
        exact Set.disjoint_iff.mp hUV_disjoint ⟨hzU, hzV⟩
    -- 由于 X = U ∪ V 且 U, V 闭且不交，U 是 clopen
    have hU_clopen : IsClopen U := by
      refine ⟨hU_closed, ?_⟩
      rw [← isClosed_compl_iff, hU_compl]
      exact hV_closed
    -- x ∈ U 且 y ∈ V
    have hxU : x ∈ U := by
      rw [mem_generalizationHull_iff]
      exact ⟨x, ⟨⟨x, hx⟩, hxU₀, rfl⟩, by rfl⟩
    have hyV : y ∈ V := by
      rw [mem_generalizationHull_iff]
      exact ⟨y, ⟨⟨y, hy⟩, hyU₀, rfl⟩, by rfl⟩
    -- 由于 x ∈ U (clopen)，connectedComponent x ⊆ U
    have hconn_sub : connectedComponent x ⊆ U :=
      hU_clopen.connectedComponent_subset hxU
    -- 但 y ∈ connectedComponent x（由 heq）且 y ∈ V
    have hy_in_conn : y ∈ connectedComponent x :=
      ConnectedComponents.coe_eq_coe'.mp heq.symm
    have hy_in_U : y ∈ U := hconn_sub hy_in_conn
    -- 这与 U ∩ V = ∅ 矛盾
    exact Set.disjoint_iff.mp hUV_disjoint ⟨hy_in_U, hyV⟩
  · -- 满射性：每个连通分量包含闭点
    intro c
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨p, hp, hxp⟩ := exists_isClosed_specializes x
    have hp_conn : p ∈ connectedComponent x := by
      have : closure {x} ⊆ connectedComponent x :=
        isConnected_singleton.closure.subset_connectedComponent (subset_closure rfl)
      exact this (specializes_iff_mem_closure.mp hxp)
    exact ⟨⟨p, mem_closedPoints_iff.mpr hp⟩,
      ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq_iff_mem.mpr hp_conn)⟩

/-- The closed points of a w-local space are homeomorphic to the connected components. -/
noncomputable
def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
