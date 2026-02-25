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
  have : Nonempty {U // IsClopen U ∧ x ∈ U} := ⟨⟨⊤, isClopen_univ, Set.mem_univ x⟩⟩
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
  · intro ⟨h1, h2⟩
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
        intro t ht htx
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
    [QuasiSeparatedSpace X] [PrespectralSpace X] : T2Space (ConnectedComponents X) := by
  rw [(t2Space_iff _)]
  intro a b hab
  -- Pick representatives
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  rw [ConnectedComponents.coe_ne_coe] at hab
  -- y ∉ connectedComponent x
  have hy : y ∉ connectedComponent x := fun h => hab (connectedComponent_eq h)
  -- connectedComponent x = ⋂ {U | IsClopen U ∧ x ∈ U}, so ∃ clopen U with x ∈ U and y ∉ U
  have hy' : ∃ U, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
    by_contra! habs
    apply hy
    rw [← sInter_isClopen_and_mem_eq_connectedComponent]
    exact Set.mem_iInter.mpr fun ⟨U, hU1, hU2⟩ => habs U hU1 hU2
  obtain ⟨U, hU, hxU, hyU⟩ := hy'
  -- Project U to ConnectedComponents X via mk
  -- mk ⁻¹' (mk '' U) = U since U is clopen (hence saturated)
  have hsat : (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents X)) = U := by
    rw [connectedComponents_preimage_image]
    exact hU.biUnion_connectedComponent_eq
  -- mk '' U is clopen in ConnectedComponents X
  have hU' : IsClopen ((↑) '' U : Set (ConnectedComponents X)) := by
    rwa [← ConnectedComponents.isQuotientMap_coe.isClopen_preimage, hsat]
  -- Use clopen set to separate: mk '' U and (mk '' U)ᶜ are disjoint open neighborhoods
  refine ⟨(↑) '' U, ((↑) '' U)ᶜ, hU'.2, hU'.1.isOpen_compl, Set.mem_image_of_mem _ hxU, ?_, disjoint_compl_right⟩
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  intro z hzU hzy
  apply hyU
  rw [ConnectedComponents.coe_eq_coe'] at hzy
  exact hU.connectedComponent_subset hzU (connectedComponent_eq_iff_mem.mp (connectedComponent_eq hzy))

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
    Function.Bijective (connectedComponentsLift g.2) := by
  -- The commutativity: i ∘ g = mk ∘ f (from fst ≫ f = snd ≫ g, i.e., g ≫ i = f ≫ mk)
  have hw : ∀ y : Y, i (g y) = (f y : ConnectedComponents X) :=
    fun y => ConcreteCategory.congr_hom pb.w y
  constructor
  · -- Injectivity: use connectedComponentsLift_injective by showing fibers of g are preconnected.
    -- The fiber g⁻¹'{t} is homeomorphic (via the pullback) to a connected component of X.
    apply g.2.connectedComponentsLift_injective
    intro t
    -- Construct the homeomorphism E : Y ≃ₜ {p : T × X | i p.1 = mk p.2}
    have inst_hp := pb.hasPullback
    let E := homeoOfIso (pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    -- Key property: g = fst ∘ E
    have hE_g : ∀ y, (E y).val.1 = g y := by
      intro y
      show ((pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
      simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
      rw [pullbackIsoProdSubtype_hom_apply]
      exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
    -- Key property: f = snd ∘ E
    have hE_f : ∀ y, (E y).val.2 = f y := by
      intro y
      show ((pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
      simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
      rw [pullbackIsoProdSubtype_hom_apply]
      exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
    -- The fiber g⁻¹'{t} is preconnected because it is the continuous image
    -- of a connected component of X under the inverse of the pullback homeomorphism.
    -- First handle the empty case.
    by_cases hne : (g ⁻¹' {t}).Nonempty
    swap
    · exact (Set.not_nonempty_iff_eq_empty.mp hne) ▸ isPreconnected_empty
    obtain ⟨y₀, hy₀⟩ := hne
    have hy₀t : g y₀ = t := Set.mem_singleton_iff.mp hy₀
    -- Define φ : {x : X | mk x = i t} → Y by φ(x) = E⁻¹(⟨(t, x), proof⟩)
    let φ : {x : X | (x : ConnectedComponents X) = i t} → Y :=
      fun x => E.symm ⟨(t, x.val), x.prop.symm⟩
    -- φ is continuous
    have hφ_cont : Continuous φ := by
      show Continuous (E.symm ∘ (fun x : {x : X | (x : ConnectedComponents X) = i t} =>
        (⟨(t, x.val), x.prop.symm⟩ : { p : T × X | i p.1 = (p.2 : ConnectedComponents X)})))
      apply E.symm.continuous.comp
      exact Continuous.subtype_mk (by fun_prop) _
    -- φ maps into g⁻¹'{t}
    have hφ_img : ∀ x, g (φ x) = t := by
      intro ⟨x, hx⟩
      show g (E.symm ⟨(t, x), hx.symm⟩) = t
      conv_lhs => rw [← hE_g (E.symm ⟨(t, x), hx.symm⟩), E.apply_symm_apply]
    -- φ is surjective onto g⁻¹'{t}
    have hφ_surj : ∀ y, y ∈ g ⁻¹' {t} → y ∈ Set.range φ := by
      intro y hy
      have hyt : g y = t := Set.mem_singleton_iff.mp hy
      have hmk : (f y : ConnectedComponents X) = i t := by
        rw [← hw y, hyt]
      refine ⟨⟨f y, hmk⟩, ?_⟩
      show E.symm ⟨(t, f y), hmk.symm⟩ = y
      apply E.injective
      simp only [Homeomorph.apply_symm_apply]
      apply Subtype.ext
      apply Prod.ext
      · simp only [hE_g]; exact hyt.symm
      · exact (hE_f y).symm
    -- {x : X | mk x = i t} = connectedComponent (f y₀), which is preconnected.
    have hit : i t = (f y₀ : ConnectedComponents X) := by rw [← hw y₀, hy₀t]
    have hconn : IsPreconnected {x : X | (x : ConnectedComponents X) = i t} := by
      suffices h : {x : X | (x : ConnectedComponents X) = i t} = connectedComponent (f y₀) by
        rw [h]; exact isConnected_connectedComponent.isPreconnected
      ext x
      simp only [Set.mem_setOf_eq, hit]
      exact ConnectedComponents.coe_eq_coe'
    -- The fiber g⁻¹'{t} is the image of a preconnected set under φ, hence preconnected.
    have heq : g ⁻¹' {t} = Set.range φ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
      exact ⟨fun hy => hφ_surj y hy, fun ⟨x, hx⟩ => hx ▸ hφ_img x⟩
    -- The domain of φ has preconnected space.
    have : PreconnectedSpace {x : X | (x : ConnectedComponents X) = i t} :=
      Subtype.preconnectedSpace hconn
    show IsPreconnected (g.toFun ⁻¹' {t})
    rw [show g.toFun ⁻¹' {t} = Set.range φ from heq]
    exact isPreconnected_range hφ_cont
  · -- Surjectivity: for each t : T, find y : Y with g y = t, giving lift(mk y) = g y = t.
    intro t
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (i t)
    let y := pb.lift (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} t))
      (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x))
      (by ext ⟨⟩; exact hx.symm) PUnit.unit
    have hgy : g y = t := ConcreteCategory.congr_hom
      (pb.lift_fst (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} t))
        (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x))
        (by ext ⟨⟩; exact hx.symm)) PUnit.unit
    exact ⟨mk y, g.2.connectedComponentsLift_apply_coe y ▸ hgy⟩

@[stacks 096C "first part"]
theorem ConnectedComponents.isHomeomorph_lift_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsHomeomorph (connectedComponentsLift g.2) :=
  let _ := IsPullback.compactSpace pb
  (isHomeomorph_iff_continuous_bijective (X := ConnectedComponents Y) (Y := T)).mpr ⟨connectedComponentsLift_continuous g.2, lift_bijective_of_isPullback pb⟩

end Spectral
