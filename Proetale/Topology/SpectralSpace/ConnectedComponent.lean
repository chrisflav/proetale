/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.Preliminaries.Profinite
import Proetale.Topology.Preliminaries.Pullback
import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Connected Component in Spectral Space

Profiniteness is expressed as [TopologicalSpace X] [CompactSpace X] [T2Space X]
[TotallyDisconnectedSpace X]

-/

universe u

variable {X : Type u} [TopologicalSpace X]

section

open TopologicalSpace

variable [PrespectralSpace X]

lemma exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace
    (S : Set X) (B : Set X) (hB : IsOpen B) (h2 : IsCompact (S ∩ B)) :
    ∃ U ⊆ B, IsOpen U ∧ IsCompact U ∧ S ∩ U = S ∩ B := by
  obtain ⟨Us, hUs, hUsC⟩ := Opens.isBasis_iff_cover.mp (PrespectralSpace.isBasis_opens X) ⟨B, hB⟩
  have heq := congr($(hUsC).carrier)
  simp only [Opens.carrier_eq_coe, Opens.coe_sSup] at heq
  obtain ⟨t, ht⟩ := h2.elim_finite_subcover (U := fun i : Us ↦ i.1) (fun i ↦ i.1.2) (by simp [heq])
  use ⋃ i ∈ t, i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    intro i hi
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
      exists_and_right] at hi
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    grind
  · exact isOpen_biUnion (fun i hi ↦ i.1.2)
  · exact t.finite_toSet.isCompact_biUnion fun i hi ↦ hUs i.2
  · refine subset_antisymm ?_ (by simpa using ht)
    rw [heq]
    gcongr
    intro i hi
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
      exists_and_right] at hi
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    grind

variable [CompactSpace X] [QuasiSeparatedSpace X]

@[simp, stacks 005F]
theorem sInter_isClopen_and_mem_eq_connectedComponent {x : X} :
    ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U = connectedComponent x := by
  set S : Set X := ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U
  have hx : x ∈ S := by simp [S]
  refine subset_antisymm ?_ connectedComponent_subset_iInter_isClopen
  refine IsConnected.subset_connectedComponent ?_ hx
  by_contra h
  simp only [IsConnected, not_and] at h
  have := h ⟨x, by simp [S]⟩
  simp only [IsPreconnected, not_forall] at this
  have : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ IsCompact U ∧
      IsCompact V ∧ (U ∩ V) ∩ S = ∅ ∧ S ⊆ U ∪ V ∧ (U ∩ S).Nonempty ∧ (V ∩ S).Nonempty := by
    obtain ⟨B, C, hB, hC, hBC, hBn, hCn, h⟩ := this
    push_neg at h
    have hS : IsClosed S := isClosed_iInter fun U ↦ U.2.1.1
    obtain ⟨U, hUB, hU, hUc, hUSB⟩ :=
        exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace S B hB <| by
      apply IsClosed.isCompact
      convert IsClosed.sdiff hS hC using 1
      tauto_set
    obtain ⟨V, hVB, hV, hVc, hVSC⟩ :=
        exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace S C hC <| by
      apply IsClosed.isCompact
      convert IsClosed.sdiff hS hB using 1
      tauto_set
    use U, V, hU, hV, hUc, hVc
    refine ⟨?_, ?_, ?_⟩
    · grind
    · trans (S ∩ U) ∪ (S ∩ V)
      · rw [hUSB, hVSC, ← Set.inter_union_distrib_left]
        simp [hBC]
      · rw [← Set.inter_union_distrib_left]
        exact Set.inter_subset_right
    · rw [U.inter_comm, V.inter_comm, hUSB, hVSC]
      exact ⟨hBn, hCn⟩
  obtain ⟨U, V, hU, hV, hUc, hVc, hUVS, hSUV, hUSn, hVSn⟩ := this
  have : Nonempty {U // IsClopen U ∧ x ∈ U} := ⟨⟨⊤, by simp [isClopen_univ]⟩⟩
  obtain ⟨W, hxW, hW, hUVW⟩ : ∃ W : Set X, x ∈ W ∧ IsClopen W ∧ U ∩ V ∩ W = ∅ := by
    obtain ⟨W, hW⟩ := IsCompact.elim_directed_family_closed
      (IsCompact.inter_of_isOpen hUc hVc hU hV) _ (·.2.1.1) hUVS
      fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
    use W, W.2.2, W.2.1
  obtain ⟨W', hxW', hW', hW'UV⟩ : ∃ W' : Set X, x ∈ W' ∧ IsClopen W' ∧ W' ⊆ U ∪ V := by
    have : (U ∪ V)ᶜ ∩ S = ∅ := by
      rwa [← Set.diff_eq_compl_inter, Set.diff_eq_empty]
    obtain ⟨W', hW'⟩ := IsCompact.elim_directed_family_closed
      ((hU.union hV).isClosed_compl.isCompact) _ (·.2.1.1) this
      fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
    use W', W'.2.2, W'.2.1
    rwa [← Set.diff_eq_empty, Set.diff_eq_compl_inter]
  set WW := W ∩ W'
  have hUWW : IsClopen (U ∩ WW) := by
    refine ⟨?_, hU.inter (hW.2.inter hW'.2)⟩
    convert IsClosed.sdiff (hW.1.inter hW'.1) hV using 1
    unfold WW
    clear * - hUVW hW'UV
    tauto_set
  have hVWW : IsClopen (V ∩ WW) := by
    refine ⟨?_, hV.inter (hW.2.inter hW'.2)⟩
    convert IsClosed.sdiff (hW.1.inter hW'.1) hU using 1
    unfold WW
    clear * - hUVW hW'UV
    tauto_set
  obtain (hxU | hxV) := hSUV hx
  · refine hVSn.elim fun y hy ↦ ?_
    have hS : S ⊆ U ∩ WW := by
      fapply Set.iInter_subset_of_subset
      exact ⟨_, hUWW, ⟨hxU, ⟨hxW, hxW'⟩⟩⟩
      rfl
    have : y ∈ U ∩ V ∩ S := by grind
    grind
  · refine hUSn.elim fun y hy ↦ ?_
    have hS : S ⊆ V ∩ WW := by
      fapply Set.iInter_subset_of_subset
      exact ⟨_, hVWW, ⟨hxV, ⟨hxW, hxW'⟩⟩⟩
      rfl
    have : y ∈ U ∩ V ∩ S := by grind
    grind

@[stacks 04PL]
theorem isClosed_and_iUnion_connectedComponent_eq_iff {T : Set X} :
    (IsClosed T ∧ ∃ I : Set X, ⋃ x ∈ I, connectedComponent x = T) ↔
    ∃ J : Set ({U : Set X // IsClopen U}), ⋂ (U : J), U = T := by
  classical
  constructor
  · rintro ⟨hT, ⟨I, hI⟩⟩
    let J : Set ({U : Set X // IsClopen U}) := {U | T ⊆ U}
    refine ⟨J, ?_⟩
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      by_contra hxT
      have hTcomp : IsCompact T := hT.isCompact
      have hSat : ∀ z, z ∈ T → connectedComponent z ⊆ T := by
        intro z hz
        have hz' : z ∈ ⋃ x ∈ I, connectedComponent x := by simpa [hI] using hz
        rcases Set.mem_iUnion₂.mp hz' with ⟨w, hwI, hzw⟩
        have hEq : connectedComponent z = connectedComponent w := (connectedComponent_eq hzw).symm
        have : connectedComponent w ⊆ T := by
          intro u hu
          have : u ∈ ⋃ x ∈ I, connectedComponent x := Set.mem_iUnion₂.mpr ⟨w, hwI, hu⟩
          simpa [hI] using this
        simpa [hEq] using this
      have hdis : Disjoint (connectedComponent x) T := by
        refine Set.disjoint_left.2 ?_
        intro z hz hxz
        have hxmem : x ∈ connectedComponent z := by
          have hEq : connectedComponent z = connectedComponent x := (connectedComponent_eq hz).symm
          simpa [hEq] using (mem_connectedComponent (x := x))
        have : x ∈ T := (hSat z hxz) hxmem
        exact hxT this
      let K : Type u := {U : Set X // IsClopen U ∧ x ∈ U}
      have hInter : (⋂ U : K, (U : Set X)) = connectedComponent x :=
        sInter_isClopen_and_mem_eq_connectedComponent (X := X) (x := x)
      have hcover : T ⊆ ⋃ U : K, (U : Set X)ᶜ := by
        intro z hz
        have hznot : z ∉ connectedComponent x := by
          intro hz'
          exact (Set.disjoint_left.mp hdis) hz' hz
        have : z ∉ ⋂ U : K, (U : Set X) := by rwa [hInter]
        simp only [Set.mem_iInter, not_forall] at this
        exact Set.mem_iUnion.mpr this
      obtain ⟨s, hs⟩ :=
        hTcomp.elim_finite_subcover
          (U := fun U : K => (U : Set X)ᶜ)
          (fun U => U.2.1.1.isOpen_compl) hcover
      let V : Set X := ⋃ U ∈ s, (U : Set X)ᶜ
      have hVcl : IsClopen V := by
        refine Set.Finite.isClopen_biUnion s.finite_toSet ?_
        intro U hU
        exact U.2.1.compl
      have hVT : T ⊆ V := hs
      have hxV : x ∈ V := by
        have hxmem : (⟨V, hVcl⟩ : {U : Set X // IsClopen U}) ∈ J := hVT
        have : x ∈ ((⟨⟨V, hVcl⟩, hxmem⟩ : J) : Set X) :=
          Set.mem_iInter.1 hx ⟨⟨V, hVcl⟩, hxmem⟩
        simpa using this
      have hxnotV : x ∉ V := by
        intro hxV'
        rcases (by simpa [V] using hxV') with ⟨U, hUs, hxU⟩
        exact hxU U.2.2
      exact hxnotV hxV
    · intro x hx
      simp [J]
      intro U hU hTU
      exact hTU hx
  · rintro ⟨J, hJ⟩
    refine ⟨?_, ?_⟩
    · have : IsClosed (⋂ U : J, (U : Set X)) := isClosed_iInter fun U => (U.1.2).1
      simpa [hJ] using this
    · refine ⟨T, ?_⟩
      refine Set.Subset.antisymm ?_ ?_
      · intro z hz
        rcases Set.mem_iUnion₂.mp hz with ⟨x, hxT, hzx⟩
        have hxInter : x ∈ ⋂ U : J, (U : Set X) := by simpa [hJ] using hxT
        have hzInter : z ∈ ⋂ U : J, (U : Set X) := by
          refine Set.mem_iInter.2 ?_
          intro U
          have hxU : x ∈ (U : Set X) := Set.mem_iInter.1 hxInter U
          exact (IsClopen.connectedComponent_subset U.1.2 hxU) hzx
        simpa [hJ] using hzInter
      · intro z hz
        exact Set.mem_iUnion₂.mpr ⟨z, hz, mem_connectedComponent⟩

  -- uses `ConnectedComponents.injective_lift`

instance compactSpace_connectedComponent {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    CompactSpace (ConnectedComponents X) where
  isCompact_univ := by
    let f : X → ConnectedComponents X := ConnectedComponents.mk
    have h1 : Continuous f := ConnectedComponents.continuous_coe
    have h2 : Function.Surjective f := ConnectedComponents.surjective_coe
    have h3 : IsCompact (Set.range f) := isCompact_range h1
    simpa [f, ConnectedComponents.range_coe] using h3


@[stacks 0906]
instance t2Space_connectedComponent {X : Type u} [TopologicalSpace X]  [CompactSpace X]
    [QuasiSeparatedSpace X] [PrespectralSpace X] : T2Space (ConnectedComponents X) :=
  by
    classical
    refine ⟨?_⟩
    intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have hxy : connectedComponent x ≠ connectedComponent y :=
      (ConnectedComponents.coe_ne_coe (x := x) (y := y)).1 hab
    have hdis : Disjoint (connectedComponent x) (connectedComponent y) :=
      connectedComponent_disjoint hxy
    -- Express `connectedComponent x` as an intersection of clopens.
    have hxdata :
        IsClosed (connectedComponent x : Set X) ∧
          ∃ I : Set X, ⋃ z ∈ I, connectedComponent z = connectedComponent x :=
      ⟨isClosed_connectedComponent, {x}, by ext z; simp⟩
    obtain ⟨J, hJ⟩ :=
      (isClosed_and_iUnion_connectedComponent_eq_iff (X := X) (T := connectedComponent x)).1 hxdata
    -- Use compactness of `connectedComponent y` to find a clopen neighborhood of `x` disjoint from it.
    have hcover : connectedComponent y ⊆ ⋃ U : J, (↑↑U : Set X)ᶜ := by
      intro z hz
      have hznot : z ∉ ⋂ U : J, (↑↑U : Set X) := by
        intro hz'
        have : z ∈ connectedComponent x := by simpa [hJ] using hz'
        exact (Set.disjoint_left.mp hdis) this hz
      have hznot' : ¬ ∀ U : J, z ∈ (↑↑U : Set X) := by
        simpa [Set.mem_iInter] using hznot
      rcases not_forall.mp hznot' with ⟨U, hzU⟩
      exact Set.mem_iUnion.mpr ⟨U, by simpa using hzU⟩
    have hyCpt : IsCompact (connectedComponent y : Set X) :=
      (isClosed_connectedComponent (x := y)).isCompact
    obtain ⟨s, hs⟩ :=
      hyCpt.elim_finite_subcover
        (U := fun U : J => (↑↑U : Set X)ᶜ)
        (fun U => (U.1.2).1.isOpen_compl) hcover
    let U0 : Set X := ⋂ U ∈ s, (↑↑U : Set X)
    have hU0 : IsClopen U0 := by
      simpa [U0] using
        (isClopen_biInter_finset (s := s) (f := fun U : J => (↑↑U : Set X)) fun U _ => U.1.2)
    have hxInter : x ∈ ⋂ U : J, (↑↑U : Set X) := by
      simpa [hJ] using (mem_connectedComponent (x := x))
    have hxU0 : x ∈ U0 := Set.mem_iInter₂.mpr fun U _ => Set.mem_iInter.1 hxInter U
    have hyU0 : y ∉ U0 := by
      obtain ⟨U, hUs, hyU⟩ := Set.mem_iUnion₂.mp (hs mem_connectedComponent)
      exact fun h => hyU (Set.mem_iInter₂.mp h U hUs)
    -- Descend the clopen set `U0` to a clopen set in `ConnectedComponents X`.
    let V : Set (ConnectedComponents X) := ((↑) : X → ConnectedComponents X) '' U0
    have hUnion : (⋃ z ∈ U0, connectedComponent z) = U0 := by
      ext z
      constructor
      · intro hz
        rcases Set.mem_iUnion₂.mp hz with ⟨w, hwU0, hzw⟩
        exact (IsClopen.connectedComponent_subset hU0 hwU0) hzw
      · intro hz
        exact Set.mem_iUnion₂.mpr ⟨z, hz, mem_connectedComponent⟩
    have hpreV : (((↑) : X → ConnectedComponents X) ⁻¹' V) = U0 := by
      simpa [V, hUnion] using (connectedComponents_preimage_image (α := X) U0)
    have hVopen : IsOpen V := by
      have : IsOpen (((↑) : X → ConnectedComponents X) ⁻¹' V) := by
        simpa [hpreV] using hU0.2
      exact (ConnectedComponents.isQuotientMap_coe.isOpen_preimage).1 this
    have hVclosed : IsClosed V := by
      have : IsClosed (((↑) : X → ConnectedComponents X) ⁻¹' V) := by
        simpa [hpreV] using hU0.1
      exact (ConnectedComponents.isQuotientMap_coe.isClosed_preimage).1 this
    refine ⟨V, Vᶜ, hVopen, hVclosed.isOpen_compl, ?_, ?_, disjoint_compl_right⟩
    · exact ⟨x, hxU0, rfl⟩
    · have : (y : ConnectedComponents X) ∉ V := by
        intro hyV
        have : y ∈ (((↑) : X → ConnectedComponents X) ⁻¹' V) := by
          simpa using hyV
        have : y ∈ U0 := by simpa [hpreV] using this
        exact hyU0 this
      simpa [Set.mem_compl_iff] using this

end

section Spectral

variable [SpectralSpace X]

open CategoryTheory TopCat Continuous Limits

theorem ConnectedComponents.spectralSpace_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    SpectralSpace Y := pb.spectralSpace

omit [SpectralSpace X] in
/-- The first projection of a pullback along the connected components map is surjective. -/
theorem ConnectedComponents.surjective_fst_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Function.Surjective g := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  intro t
  rcases ConnectedComponents.surjective_coe (i t) with ⟨x, hx⟩
  let p : { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    ⟨⟨t, x⟩, hx.symm⟩
  let q : (pullback (ofHom i) (ofHom mkX) : TopCat) :=
    (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX)).inv p
  refine ⟨pb.isoPullback.inv q, ?_⟩
  have hq : g (pb.isoPullback.inv q) = pullback.fst (ofHom i) (ofHom mkX) q :=
    ConcreteCategory.congr_hom pb.isoPullback_inv_fst q
  have hfst : pullback.fst (ofHom i) (ofHom mkX) q = t := by
    simpa [q] using TopCat.pullbackIsoProdSubtype_inv_fst_apply (ofHom i) (ofHom mkX) p
  simp [hq, hfst]

omit [SpectralSpace X] in
/-- The fibers of the first projection of a pullback along the connected components map are
preconnected. -/
theorem ConnectedComponents.isPreconnected_fiber_of_isPullback {Y T : Type u}
    [TopologicalSpace Y] [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    (t : T) : IsPreconnected ((g : Y → T) ⁻¹' ({t} : Set T)) := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  -- Transport to the (concrete) pullback.
  let eY : Y ≃ₜ (pullback (ofHom i) (ofHom mkX) : TopCat) := homeoOfIso pb.isoPullback
  let fiberP : Set (pullback (ofHom i) (ofHom mkX) : TopCat) :=
    (pullback.fst (ofHom i) (ofHom mkX)) ⁻¹' ({t} : Set T)
  have hsetY : ((g : Y → T) ⁻¹' ({t} : Set T)) = eY.symm '' fiberP := by
    ext y
    constructor
    · intro hy
      refine ⟨eY y, ?_, by simp⟩
      have hy' : g y = t := by simpa using hy
      have hfst : pullback.fst (ofHom i) (ofHom mkX) (eY y) = t := by
        rw [show pullback.fst (ofHom i) (ofHom mkX) (eY y) = g y from
          ConcreteCategory.congr_hom pb.isoPullback_hom_fst y, hy']
      simp [fiberP, hfst]
    · rintro ⟨q, hq, rfl⟩
      have hgq : g (eY.symm q) = pullback.fst (ofHom i) (ofHom mkX) q :=
        ConcreteCategory.congr_hom pb.isoPullback_inv_fst q
      simpa [hgq] using hq
  -- Work in the explicit subtype pullback `S ⊆ T × X`.
  let eS :
      (pullback (ofHom i) (ofHom mkX) : TopCat) ≃ₜ
        { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    homeoOfIso (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX))
  let FSt : Set { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    { p | (p : T × X).fst = t }
  -- Show `FSt` is preconnected: it is the continuous image of a connected component in `X`.
  have hFSt : IsPreconnected FSt := by
    rcases ConnectedComponents.surjective_coe (i t) with ⟨x0, hx0⟩
    let A : Set X := ((↑) : X → ConnectedComponents X) ⁻¹' ({i t} : Set (ConnectedComponents X))
    have hA : IsPreconnected A := by
      have hA' : A = connectedComponent x0 := by
        simpa [A, hx0] using (connectedComponents_preimage_singleton (α := X) (x := x0))
      simpa [hA'] using (isPreconnected_connectedComponent (x := x0))
    letI : PreconnectedSpace A := (isPreconnected_iff_preconnectedSpace (s := A)).1 hA
    let φ : A → { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
      fun ⟨x, hxA⟩ => ⟨⟨t, x⟩, by simpa [mkX, Set.mem_singleton_iff, A] using hxA.symm⟩
    have hφcont : Continuous φ :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk fun ⟨x, hxA⟩ => by
        simpa [mkX, Set.mem_singleton_iff, A] using hxA.symm
    have hRange : Set.range φ = FSt := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        simp [FSt, φ]
      · intro hp
        have hxmem : p.1.2 ∈ A := by
          have h : i p.1.1 = (p.1.2 : ConnectedComponents X) := by simpa [mkX] using p.2
          have hip : i t = i p.1.1 := by simpa using (congrArg i hp).symm
          simp [A, (hip.trans h).symm]
        exact ⟨⟨p.1.2, hxmem⟩, Subtype.ext (Prod.ext hp.symm rfl)⟩
    simpa [hRange, Set.image_univ] using
      isPreconnected_univ.image (f := φ) (hf := hφcont.continuousOn)
  have hfiberP : IsPreconnected fiberP := by
    have hEq : fiberP = eS.symm '' FSt := by
      ext q
      constructor
      · intro hq
        refine ⟨eS q, ?_, by simp⟩
        have hqt : pullback.fst (ofHom i) (ofHom mkX) q = t := by simpa using hq
        have : (eS q : T × X).fst = pullback.fst (ofHom i) (ofHom mkX) q := by
          simpa using congrArg Prod.fst <| congrArg Subtype.val <|
            TopCat.pullbackIsoProdSubtype_hom_apply (f := ofHom i) (g := ofHom mkX) (x := q)
        simp [FSt, this, hqt]
      · rintro ⟨p, hp, rfl⟩
        have : pullback.fst (ofHom i) (ofHom mkX) (eS.symm p) = (p : T × X).fst := by
          simpa [eS] using TopCat.pullbackIsoProdSubtype_inv_fst_apply (ofHom i) (ofHom mkX) p
        simp [fiberP, this, show (p : T × X).fst = t by simpa [FSt] using hp]
    simpa [hEq] using hFSt.image (f := eS.symm) (hf := eS.symm.continuous.continuousOn)
  simpa [hsetY] using hfiberP.image (f := eY.symm) (hf := eY.symm.continuous.continuousOn)

omit [SpectralSpace X] in
theorem ConnectedComponents.lift_bijective_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Function.Bijective (connectedComponentsLift g.2) := by
  refine ⟨?_, ?_⟩
  · exact Continuous.connectedComponentsLift_injective g.2
      (ConnectedComponents.isPreconnected_fiber_of_isPullback pb)
  · intro t
    rcases ConnectedComponents.surjective_fst_of_isPullback pb t with ⟨y, rfl⟩
    exact ⟨(y : ConnectedComponents Y), by simp⟩

@[stacks 096C "first part"]
theorem ConnectedComponents.isHomeomorph_lift_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsHomeomorph (connectedComponentsLift g.2) :=
  let _ := IsPullback.compactSpace pb
  (isHomeomorph_iff_continuous_bijective (X := ConnectedComponents Y) (Y := T)).mpr ⟨connectedComponentsLift_continuous g.2, lift_bijective_of_isPullback pb⟩

end Spectral
