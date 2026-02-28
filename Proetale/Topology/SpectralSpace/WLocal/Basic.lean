/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.Inseparable
import Proetale.Mathlib.Topology.Separation.Basic
import Proetale.Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.JacobsonSpace
import Proetale.Topology.SpectralSpace.Constructible
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Mathlib.Topology.JacobsonSpace

/-!
# w-local spaces

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
  image_closedPoints : closedPoints X ⊆ f ⁻¹' (closedPoints Y)

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
  toIsSpectralMap := hg.toIsSpectralMap.comp hf.toIsSpectralMap
  image_closedPoints := by
    intro x hx
    exact hg.image_closedPoints (hf.image_closedPoints hx)

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' := by
    -- closed points in X map to closed points in Y under an embedding with stable range
    have closed_map_points : ∀ z : X, IsClosed ({z} : Set X) → IsClosed ({f z} : Set Y) := by
      intro z hz
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
      have hfy : y ∈ Set.range f := h hspec (Set.mem_range_self z)
      obtain ⟨z', rfl⟩ := hfy
      have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
      have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
      rw [Set.mem_singleton_iff.mp this]
      exact Set.mem_singleton _
    have hfc : IsClosed ({f c} : Set Y) := closed_map_points c hc
    have hfc' : IsClosed ({f c'} : Set Y) := closed_map_points c' hc'
    exact hf.injective (WLocalSpace.eq_of_specializes hfc hfc' (hxc.map hf.continuous)
      (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    have closed_map_points : ∀ z : X, IsClosed ({z} : Set X) → IsClosed ({f z} : Set Y) := by
      intro z hz
      rw [← closure_eq_iff_isClosed]
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
      have hfy : y ∈ Set.range f := h hspec (Set.mem_range_self z)
      obtain ⟨z', rfl⟩ := hfy
      have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
      have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
      rw [Set.mem_singleton_iff.mp this]
      exact Set.mem_singleton _
    have : closedPoints X = f ⁻¹' closedPoints Y := by
      ext x
      simp only [Set.mem_preimage, mem_closedPoints_iff]
      constructor
      · exact closed_map_points x
      · intro hfx
        rw [← closure_eq_iff_isClosed]
        apply Set.Subset.antisymm _ subset_closure
        intro x' hx'
        have hspec : x ⤳ x' := specializes_iff_mem_closure.mpr hx'
        have hfspec : f x ⤳ f x' := hspec.map hf.continuous
        have hmem : f x' ∈ ({f x} : Set Y) := hfx.closure_eq ▸ hfspec.mem_closure
        exact Set.mem_singleton_iff.mpr (hf.injective (Set.mem_singleton_iff.mp hmem))
    rw [this]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  rw [generalizationHull_eq]
  intro a b hab ha
  -- hab : a ⤳ b, ha : a ∈ {x | ∃ y ∈ s, x ⤳ y}
  -- Need: b ∈ {x | ∃ y ∈ s, x ⤳ y}, i.e., ∃ w ∈ s, b ⤳ w
  obtain ⟨y, hys, hay⟩ := ha
  -- Get closed point that y specializes to
  obtain ⟨c, hc_closed, hyc⟩ := exists_isClosed_specializes y
  -- c ∈ s since y ∈ s and y ⤳ c
  have hcs : c ∈ s := hs hyc hys
  -- a ⤳ c (transitivity: a ⤳ y ⤳ c)
  have hac : a ⤳ c := hay.trans hyc
  -- Get closed point that b specializes to
  obtain ⟨c', hc'_closed, hbc'⟩ := exists_isClosed_specializes b
  -- a ⤳ b ⤳ c', so a ⤳ c'
  have hac' : a ⤳ c' := hab.trans hbc'
  -- By uniqueness of closed specializations: c = c'
  have : c = c' := WLocalSpace.eq_of_specializes hc_closed hc'_closed hac hac'
  subst this
  exact ⟨c, hcs, hbc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X where
  toSpectralSpace := hf.spectralSpace
  eq_of_specializes {x c c'} hc hc' hxc hxc' := by
    have hfc : IsClosed ({f c} : Set Y) := by
      rw [← Set.image_singleton]; exact hf.isClosedMap _ hc
    have hfc' : IsClosed ({f c'} : Set Y) := by
      rw [← Set.image_singleton]; exact hf.isClosedMap _ hc'
    have hfxc : f x ⤳ f c := hxc.map hf.continuous
    have hfxc' : f x ⤳ f c' := hxc'.map hf.continuous
    exact hf.injective (WLocalSpace.eq_of_specializes hfc hfc' hfxc hfxc')
  isClosed_closedPoints := by
    have : closedPoints X = f ⁻¹' closedPoints Y := by
      ext x
      simp only [Set.mem_preimage, mem_closedPoints_iff]
      constructor
      · intro hx
        rw [← Set.image_singleton]
        exact hf.isClosedMap _ hx
      · intro hfx
        rwa [hf.isClosed_iff_image_isClosed, Set.image_singleton]
    rw [this]
    exact (WLocalSpace.isClosed_closedPoints).preimage hf.continuous

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) := by
  -- Strategy: show (1) stable under specialization and (2) closed in constructible topology,
  -- then apply IsClosed.of_isClosed_constructibleTopology.
  have hspec : StableUnderSpecialization (generalizationHull s) :=
    hs.stableUnderSpecialization.generalizationHull_of_wLocalSpace
  -- Show generalizationHull s is closed in the constructible topology.
  -- For each x ∉ generalizationHull s, find a compact open W with s ⊆ W and x ∉ W.
  -- Then Wᶜ is constructibly open and disjoint from generalizationHull s.
  have h_key : ∀ x ∉ generalizationHull s, ∃ W : Set X, IsOpen W ∧ IsCompact W ∧
      s ⊆ W ∧ x ∉ W := by
    intro x hx
    rw [mem_generalizationHull_iff] at hx
    push_neg at hx
    -- For each y ∈ s, get a compact open set separating x from y
    -- Use subtype indexing to avoid dependent choose issues
    have h_sep : ∀ (y : s), ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ (y : X) ∈ V ∧ x ∉ V := by
      intro ⟨y, hy⟩
      obtain ⟨U, hUo, hyU, hxU⟩ := not_specializes_iff_exists_open.mp (hx y hy)
      obtain ⟨V, ⟨hVo, hVc⟩, hyV, hVU⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hyU hUo
      exact ⟨V, hVo, hVc, hyV, fun hxV => hxU (hVU hxV)⟩
    choose V hVo hVc hyV hxV using h_sep
    -- s ⊆ ⋃ (y : s), V y
    have hs_cover : s ⊆ ⋃ (y : s), V y := by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
    -- s is compact
    have hs_compact : IsCompact s := hs.isCompact
    obtain ⟨t, ht_cover⟩ := hs_compact.elim_finite_subcover (fun y => V y)
      (fun y => hVo y) hs_cover
    -- W = ⋃ i ∈ t, V i is compact and open
    set W := ⋃ i ∈ t, V i with hW_def
    refine ⟨W,
      isOpen_biUnion fun y _ => hVo y,
      t.isCompact_biUnion fun y _ => hVc y,
      ht_cover, ?_⟩
    simp only [hW_def, Set.mem_iUnion]
    push_neg
    intro y _
    exact hxV y
  -- Now prove the generalization hull is closed using the constructible topology approach.
  apply IsClosed.of_isClosed_constructibleTopology _ hspec
  -- Show generalizationHull s is closed in the constructible topology.
  refine @IsClosed.mk X (constructibleTopology X) _ ?_
  -- Show (generalizationHull s)ᶜ is open in constructible topology
  rw [@isOpen_iff_forall_mem_open X (constructibleTopology X)]
  intro x hx
  obtain ⟨W, hWo, hWc, hsW, hxW⟩ := h_key x hx
  refine ⟨Wᶜ, ?_, ?_, hxW⟩
  · -- Wᶜ ⊆ (generalizationHull s)ᶜ
    intro z hz
    simp only [Set.mem_compl_iff, mem_generalizationHull_iff, not_exists, not_and]
    intro y hy hzy
    exact hz (hzy.mem_open hWo (hsW hy))
  · -- Wᶜ is open in the constructible topology
    exact IsCompact.isOpen_constructibleTopology_of_isClosed
      (by rwa [compl_compl] : IsCompact Wᶜᶜ) hWo.isClosed_compl

/-- In a w-local space, every point is in the generalization hull of the closed points. -/
private lemma WLocalSpace.mem_generalizationHull_closedPoints [WLocalSpace X]
    (x : X) : x ∈ generalizationHull (Subtype.val '' (Set.univ : Set (closedPoints X))) := by
  rw [mem_generalizationHull_iff]
  obtain ⟨c, hc_closed, hxc⟩ := exists_isClosed_specializes x
  exact ⟨c, ⟨⟨c, mem_closedPoints_iff.mpr hc_closed⟩, Set.mem_univ _, rfl⟩, hxc⟩

/-- In a w-local space, if S is a set of closed points and x specializes to some point of S,
    then the unique closed specialization of x is in S. -/
private lemma WLocalSpace.unique_closed_specialization_mem [WLocalSpace X]
    {S : Set X} (hS : S ⊆ Subtype.val '' (Set.univ : Set (closedPoints X)))
    {x : X} (hx : x ∈ generalizationHull S) :
    ∃! c : X, IsClosed ({c} : Set X) ∧ x ⤳ c ∧ c ∈ S := by
  rw [mem_generalizationHull_iff] at hx
  obtain ⟨y, hyS, hxy⟩ := hx
  obtain ⟨⟨y', hy'⟩, _, rfl⟩ := hS hyS
  have hy_closed : IsClosed ({y'} : Set X) := mem_closedPoints_iff.mp hy'
  -- y' is a closed point that x specializes to via y' (since y' = y' and x ⤳ y')
  refine ⟨y', ⟨hy_closed, hxy, hyS⟩, ?_⟩
  intro c ⟨hc_closed, hxc, _⟩
  exact WLocalSpace.eq_of_specializes hc_closed hy_closed hxc hxy

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
@[stacks 0968]
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) := by
  -- closedPoints X is profinite: T2, compact, totally disconnected
  haveI : SpectralSpace (closedPoints X) := SpectralSpace.of_isClosed X
  haveI : T2Space (closedPoints X) :=
    SpectralSpace.t2Space_of_isClosed_singleton closedPoints.isClosed_singleton
  haveI : CompactSpace (closedPoints X) :=
    (IsClosed.isClosedEmbedding_subtypeVal
      (WLocalSpace.isClosed_closedPoints (X := X))).compactSpace
  haveI : TotallyDisconnectedSpace (closedPoints X) :=
    SpectralSpace.totallyDisconnectedSpace_of_isClosed_singleton closedPoints.isClosed_singleton
  -- ConnectedComponents X is T2
  haveI : T2Space (ConnectedComponents X) := t2Space_connectedComponent
  -- Use compact -> T2 criterion: continuous + bijective suffices
  rw [isHomeomorph_iff_continuous_bijective]
  constructor
  · exact ConnectedComponents.continuous_coe.comp continuous_subtype_val
  constructor
  · -- Injectivity: distinct closed points are in distinct connected components
    intro ⟨x, hx⟩ ⟨y, hy⟩ hfxy
    -- Extract: mk x = mk y from composition
    have hfxy_mk : ConnectedComponents.mk (α := X) x = ConnectedComponents.mk y := hfxy
    -- Suffices to show x = y as subtypes
    ext
    by_contra hxney
    have hne_sub : (⟨x, hx⟩ : closedPoints X) ≠ ⟨y, hy⟩ :=
      fun h => hxney (congrArg Subtype.val h)
    -- Get closed embedding of closedPoints X into X
    have hcl_emb : Topology.IsClosedEmbedding (Subtype.val : closedPoints X → X) :=
      IsClosed.isClosedEmbedding_subtypeVal (WLocalSpace.isClosed_closedPoints)
    -- In closedPoints X (totally disconnected), connectedComponent = {pt}
    -- So y ∉ connectedComponent x in closedPoints X
    have hne_cc : (⟨y, hy⟩ : closedPoints X) ∉
        connectedComponent (⟨x, hx⟩ : closedPoints X) := by
      rw [connectedComponent_eq_singleton]
      exact fun h => hne_sub (Set.mem_singleton_iff.mp h).symm
    -- connectedComponent = ⋂ clopen sets containing x
    rw [connectedComponent_eq_iInter_isClopen] at hne_cc
    -- So there exists a clopen set containing x but not y
    simp only [Set.mem_iInter, not_forall] at hne_cc
    obtain ⟨⟨U₀, hU₀clopen, hxU₀⟩, hyU₀⟩ := hne_cc
    -- S_U and S_V are closed images in X
    have hSU_closed : IsClosed (Subtype.val '' U₀ : Set X) :=
      hcl_emb.isClosedMap _ hU₀clopen.1
    have hSV_closed : IsClosed (Subtype.val '' U₀ᶜ : Set X) :=
      hcl_emb.isClosedMap _ hU₀clopen.compl.1
    -- generalizationHull of both are closed
    have hgU_closed : IsClosed (generalizationHull (Subtype.val '' U₀ : Set X)) :=
      isClosed_generalizationHull_of_wLocalSpace hSU_closed
    have hgV_closed : IsClosed (generalizationHull (Subtype.val '' U₀ᶜ : Set X)) :=
      isClosed_generalizationHull_of_wLocalSpace hSV_closed
    -- Cover: every point specializes to a unique closed point
    have hcover : generalizationHull (Subtype.val '' U₀ : Set X) ∪
        generalizationHull (Subtype.val '' U₀ᶜ : Set X) = Set.univ := by
      ext z; simp only [Set.mem_union, Set.mem_univ, iff_true]
      obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
      by_cases hc_mem : (⟨c, mem_closedPoints_iff.mpr hc_closed⟩ : closedPoints X) ∈ U₀
      · left; exact mem_generalizationHull_iff.mpr
          ⟨c, Set.mem_image_of_mem Subtype.val hc_mem, hzc⟩
      · right; exact mem_generalizationHull_iff.mpr
          ⟨c, ⟨⟨c, mem_closedPoints_iff.mpr hc_closed⟩, hc_mem, rfl⟩, hzc⟩
    -- Disjoint: by uniqueness of closed specialization
    have hdisjoint : generalizationHull (Subtype.val '' U₀ : Set X) ∩
        generalizationHull (Subtype.val '' U₀ᶜ : Set X) = ∅ := by
      ext z; simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hzU hzV
      rw [mem_generalizationHull_iff] at hzU hzV
      obtain ⟨cu, hcuU, hzcu⟩ := hzU
      obtain ⟨cv, hcvV, hzcv⟩ := hzV
      obtain ⟨⟨_, hcu'⟩, hcu_mem, rfl⟩ := hcuU
      obtain ⟨⟨_, hcv'⟩, hcv_nmem, rfl⟩ := hcvV
      have heq := WLocalSpace.eq_of_specializes
        (mem_closedPoints_iff.mp hcu') (mem_closedPoints_iff.mp hcv') hzcu hzcv
      have : (⟨_, hcu'⟩ : closedPoints X) = ⟨_, hcv'⟩ := Subtype.ext heq
      rw [this] at hcu_mem
      exact hcv_nmem hcu_mem
    -- generalizationHull S_U is clopen
    have hgU_clopen : IsClopen (generalizationHull (Subtype.val '' U₀ : Set X)) := by
      constructor
      · exact hgU_closed
      · -- A = Bᶜ because A ∪ B = univ and A ∩ B = ∅
        suffices h : generalizationHull (Subtype.val '' U₀ : Set X) =
            (generalizationHull (Subtype.val '' U₀ᶜ : Set X))ᶜ by
          rw [h]; exact hgV_closed.isOpen_compl
        ext z; constructor
        · intro hz hzV
          have : z ∈ generalizationHull (Subtype.val '' U₀ : Set X) ∩
              generalizationHull (Subtype.val '' U₀ᶜ : Set X) := ⟨hz, hzV⟩
          rw [hdisjoint] at this; exact this
        · intro hz
          have huniv : z ∈ generalizationHull (Subtype.val '' U₀ : Set X) ∪
              generalizationHull (Subtype.val '' U₀ᶜ : Set X) := hcover ▸ Set.mem_univ z
          exact huniv.elim id (fun h => absurd h hz)
    -- x ∈ generalizationHull S_U (x ⤳ x and x ∈ image U₀)
    have hx_in_gU : x ∈ generalizationHull (Subtype.val '' U₀ : Set X) :=
      mem_generalizationHull_iff.mpr ⟨x, Set.mem_image_of_mem Subtype.val hxU₀, specializes_refl _⟩
    -- y ∈ generalizationHull S_V
    have hy_in_gV : y ∈ generalizationHull (Subtype.val '' U₀ᶜ : Set X) :=
      mem_generalizationHull_iff.mpr ⟨y, ⟨⟨y, hy⟩, hyU₀, rfl⟩, specializes_refl _⟩
    -- y ∉ generalizationHull S_U (since gU ∩ gV = ∅)
    have hy_not_gU : y ∉ generalizationHull (Subtype.val '' U₀ : Set X) := by
      intro h
      have : y ∈ generalizationHull (Subtype.val '' U₀ : Set X) ∩
          generalizationHull (Subtype.val '' U₀ᶜ : Set X) := ⟨h, hy_in_gV⟩
      rw [hdisjoint] at this; exact this
    -- x and y are in the same connected component of X
    have hfxy' : y ∈ connectedComponent x :=
      connectedComponent_eq_iff_mem.mp
        (connectedComponent_eq (ConnectedComponents.coe_eq_coe'.mp hfxy_mk))
    -- Since gU is clopen and x ∈ gU, connectedComponent x ⊆ gU
    exact hy_not_gU (hgU_clopen.connectedComponent_subset hx_in_gU hfxy')
  · -- Surjectivity: every connected component contains a closed point
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨cp, hcp_closed, hxcp⟩ := exists_isClosed_specializes x
    have hcp_cc : cp ∈ connectedComponent x :=
      closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hxcp.mem_closure
    exact ⟨⟨cp, mem_closedPoints_iff.mpr hcp_closed⟩,
      show ConnectedComponents.mk cp = ConnectedComponents.mk x from
        ConnectedComponents.coe_eq_coe'.mpr hcp_cc⟩

/-- The closed points of a w-local space are homeomorphic to the connected components. -/
noncomputable
def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
