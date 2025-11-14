/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.Preliminaries.Profinite
import Proetale.Topology.Preliminaries.Pullback
import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.Profinite.Basic

/-!
# Connected Component in Spectral Space

Profiniteness is expressed as [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

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
  constructor
  · intro h
    have h1 := h.1
    have h2 := h.2
    obtain ⟨J, hJ⟩ := h2
    let S : Set ({U : Set X // IsClopen U}) := {U | T ⊆ U}
    use S
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hcontra
      let CCx := connectedComponent x
      have hC {p : X} : (p ∈ CCx) ∧ (p ∈ T) → False := by
        intro htx
        let CCp := connectedComponent p
        have heq : CCp = CCx := by
          apply connectedComponent_eq_iff_mem.mpr
          exact Set.mem_of_mem_inter_right (id (And.symm htx))
        have hsub : CCp ⊆ T := by
          have hp : p ∈ T := htx.2
          rw [hJ.symm] at hp
          simp at hp
          obtain ⟨j, hj⟩ := hp
          let CCj := connectedComponent j
          have heq2 : CCp = CCj := by
            apply connectedComponent_eq_iff_mem.mpr
            exact hj.2
          rw [heq2, hJ.symm]
          simp [CCj]
          apply Set.subset_biUnion_of_mem hj.1
        have hx2 : x ∈ T := by
          apply hsub
          rw [heq]
          simp [CCx]
          exact mem_connectedComponent
        exact hcontra hx2
      have lem1 : ⋃ (U : {U : Set X // IsClopen U ∧ x ∈ U}), Uᶜ = (connectedComponent x)ᶜ := by
        rw [← Set.compl_iInter, sInter_isClopen_and_mem_eq_connectedComponent]
      have lem2 : T ⊆ (connectedComponent x)ᶜ := by
        intro t ht
        intro htx
        exact hC ⟨htx, ht⟩
      rw [lem1.symm] at lem2
      have lem3 : IsCompact T := by
        exact IsClosed.isCompact h1
      have lem4 : ∃ (K: Finset ({U : Set X // IsClopen U ∧ x ∈ U})), T ⊆ ⋃ U ∈ K, Uᶜ := by
        apply isCompact_iff_finite_subcover.mp
        · exact lem3
        · simp
          exact fun a a_1 a_2 ↦ IsClopen.isClosed a_1
        · exact lem2
      obtain ⟨K, hK⟩ := lem4
      let V := ⋃ U ∈ K, (Uᶜ : Set X)
      have hV1 : IsClopen V := by
        apply Set.Finite.isClopen_biUnion
        · exact K.finite_toSet
        · simp
          intro U hU _ _
          exact hU
      have hV2 : T ⊆ V := hK
      have hV3 : x ∉ V := by
        intro hVx
        simp [V] at hVx
        obtain ⟨U, hU1, hU2⟩ := hVx
        obtain ⟨hU3, _⟩ := hU1
        exact hU2 hU3.2
      have hV4 : x ∈ V := by
        apply hx
        simp
        use hV1
        exact hV2
      exact hV3 hV4
    · simp
      intro U hU1 hU2
      exact hU2
  · intro h
    obtain ⟨J, hJ⟩ := h
    constructor
    · rw [hJ.symm]
      apply isClosed_iInter
      simp
      intro a ha
      exact fun b ↦ IsClopen.isClosed ha
    · use T
      apply Set.Subset.antisymm
      · simp
        intro t ht1
        rw [hJ.symm]
        simp only [Set.iInter_coe_set, Set.subset_iInter_iff, Subtype.forall]
        intro V hV1 hV2
        have ht2 : t ∈ ⋂ (U : J), U := by
          rw [hJ]
          exact ht1
        have ht3 : t ∈ V := by
          simp only [Set.iInter_coe_set, Set.mem_iInter, Subtype.forall] at ht2
          exact ht2 V hV1 hV2
        exact IsClopen.connectedComponent_subset hV1 ht3
      · intro x hx
        simp only [Set.mem_iUnion, exists_prop]
        use x
        constructor
        · exact hx
        · exact mem_connectedComponent

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
  sorry
  -- use `isClosed_and_iUnion_connectedComponent_eq_iff`

end

section Spectral

variable [SpectralSpace X]

open CategoryTheory TopCat Continuous

theorem ConnectedComponents.spectralSpace_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    SpectralSpace Y := pb.spectralSpace

theorem ConnectedComponents.lift_bijective_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Function.Bijective (connectedComponentsLift g.2) := sorry

@[stacks 096C "first part"]
theorem ConnectedComponents.isHomeomorph_lift_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsHomeomorph (connectedComponentsLift g.2) :=
  let _ := IsPullback.compactSpace pb
  (isHomeomorph_iff_continuous_bijective (X := ConnectedComponents Y) (Y := T)).mpr ⟨connectedComponentsLift_continuous g.2, lift_bijective_of_isPullback pb⟩

end Spectral
