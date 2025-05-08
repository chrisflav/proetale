/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Sets.Opens

/-!
# Compact open covered sets

-/

universe w u v

section

variable {ι S : Type*} {X : ι → Type*}

lemma Set.sigma_eq_biUnion (s : Set ι) (t : ∀ i, Set (X i)) :
    s.sigma t = ⋃ i ∈ s, Sigma.mk i '' t i := by
  aesop

lemma Set.image_sigma_eq_iUnion (f : ∀ i, X i → S) (s : Set ι) (t : ∀ i, Set (X i)) :
    (fun p ↦ f p.1 p.2) '' (s.sigma t) = ⋃ i ∈ s, f i '' t i := by
  simp_rw [Set.sigma_eq_biUnion, Set.image_iUnion]
  simp [← Set.image_comp]

lemma Set.forall_mem_iUnion_iff {X ι : Type*} {p : X → Prop}
    {s : ι → Set X} :
    (∀ t ∈ (⋃ i, s i), p t) ↔ ∀ (i : ι), ∀ x ∈ s i, p x := by
  simp
  tauto

open TopologicalSpace Opens

lemma isBasis_sigma [∀ i, TopologicalSpace (X i)] {B : ∀ i, Set (Opens (X i))}
    (hB : ∀ i, IsBasis (B i)) :
    IsBasis (⋃ i : ι, (fun U ↦ ⟨Sigma.mk i '' U.1, isOpenMap_sigmaMk _ U.2⟩) '' B i) := by
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  convert TopologicalSpace.IsTopologicalBasis.sigma hB
  aesop

/-- If `X` has a basis of compact opens and `f : X → S` is open, every
compact open of `S` is the image of a compact open of `X`. -/
lemma IsOpenMap.exists_opens_image_eq_of_isBasis
    {X : Type*} [TopologicalSpace X] [TopologicalSpace S] (f : X → S)
    {B : Set (Opens X)} (hB : IsBasis B) (hBc : ∀ U ∈ B, IsCompact U.1)
    (hfc : Continuous f) (h : IsOpenMap f)
    {U : Set S} (hs : U ⊆ Set.range f) (hU : IsOpen U) (hc : IsCompact U) :
    ∃ (V : Opens X), IsCompact V.1 ∧ f '' V = U := by
  obtain ⟨Us, hUs, heq⟩ := isBasis_iff_cover.mp hB ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us ↦ f '' s.1) (fun s ↦ h _ s.1.2) (fun x hx ↦ ?_)
    obtain ⟨x, rfl⟩ := hs hx
    obtain ⟨i, hi, hx⟩ := mem_sSup.mp <| by rwa [← heq]
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, x, hx, rfl⟩
  refine ⟨⨆ s ∈ t, s.1, ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    exact t.finite_toSet.isCompact_biUnion fun i _ ↦ hBc _ (hUs i.2)
  · simp only [iSup_mk, carrier_eq_coe, Set.iUnion_coe_set, coe_mk, Set.image_iUnion]
    convert_to ⋃ i ∈ t, f '' i.1 = U
    · aesop
    · refine subset_antisymm (fun x ↦ ?_) ht
      simp_rw [Set.mem_iUnion]
      rintro ⟨i, hi, x, hx, rfl⟩
      have := heq ▸ mem_sSup.mpr ⟨i.1, i.2, hx⟩
      exact this

end

lemma TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact
    {X : Type*} [TopologicalSpace X] {B : Set (Opens X)}
    (hB : IsBasis B) {U : Opens X} (hU : IsCompact U.1) :
    ∃ Us ⊆ B, Us.Finite ∧ U = sSup Us := by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' ↦ s.1) (fun s ↦ s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans ht (by simp)) (le_trans (sSup_le_sSup (by simp)) hsup.ge)

open TopologicalSpace Opens

/-- A set `U` is compact-open covered by the family `fᵢ : X i → S`, if
`U` is the finite union of images of compact open sets in the `X i`. -/
def IsCompactOpenCovered {S ι : Type*} {X : ι → Type*} (f : ∀ i, X i → S)
    [∀ i, TopologicalSpace (X i)] (U : Set S) : Prop :=
  ∃ (s : Set ι) (_ : s.Finite) (V : ∀ i ∈ s, Opens (X i)),
    (∀ (i : ι) (h : i ∈ s), IsCompact (V i h).1) ∧
    ⋃ (i : ι) (h : i ∈ s), (f i) '' (V i h) = U

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι → Type v} {f : ∀ i, X i → S} [∀ i, TopologicalSpace (X i)]

lemma of_iUnion_eq_of_finite {U : Set S} (s : Set (Set S)) (hs : ⋃ t ∈ s, t = U) (hf : s.Finite)
    (H : ∀ t ∈ s, IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  choose a af V hVc hVeq using fun t : s ↦ H t t.2
  have : Finite s := hf
  refine ⟨⋃ s, a s, Set.finite_iUnion af, fun i hi ↦ ⨆ (j : s) (h : i ∈ a j), V j _ h, ?_, ?_⟩
  · intro i h
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_iSup, Opens.coe_mk]
    exact isCompact_iUnion (fun _ ↦ isCompact_iUnion (fun _ ↦ hVc _ _ _))
  · rw [← hs]
    simp only [iSup_mk, carrier_eq_coe, coe_iSup, coe_mk, Set.image_iUnion, Set.biUnion_iUnion]
    ext x
    simp_rw [Set.mem_iUnion]
    refine ⟨fun ⟨i, hi, hmem, o, ho, ho₂⟩ ↦ ?_, fun ⟨O, hOs, h⟩ ↦ ?_⟩
    · use o, o.2
      simp_rw [← hVeq, Set.mem_iUnion]
      use hi, ho
    · have : x ∈ ((⟨O, hOs⟩ : s) : Set _) := h
      rw [← hVeq] at this
      simp_rw [Set.mem_iUnion] at this
      obtain ⟨j, hj, hmem⟩ := this
      use ⟨O, hOs⟩, j, hj, ⟨O, hOs⟩, hj

lemma id_iff_isOpen_and_isCompact [TopologicalSpace S] {U : Set S} :
    IsCompactOpenCovered (fun _ : Unit ↦ id) U ↔ IsOpen U ∧ IsCompact U := by
  refine ⟨fun ⟨s, hsf, V, hc, hunion⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp only [← hunion, id_eq, Set.image_id']
    refine ⟨isOpen_iUnion fun _ ↦ (isOpen_iUnion fun _ ↦ (V _ _).2),
      isCompact_iUnion fun _ ↦ (isCompact_iUnion fun _ ↦ hc _ _)⟩
  · use Set.univ, Set.finite_univ, fun _ _ ↦ ⟨U, h.1⟩, fun _ _ ↦ h.2
    simp [Set.iUnion_const]

lemma exists_mem_of_isBasis {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1) {U : Set S} (hU : IsCompactOpenCovered f U) :
    ∃ (n : ℕ) (a : Fin n → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧
      ⋃ i, f (a i) '' V i = U := by
  suffices h : ∃ (κ : Type _) (_ : Finite κ) (a : κ → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧
      ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i ↦ V _, fun i ↦ hB _, fun i ↦ hc _,
      ?_⟩
    rw [← hU, ← Function.Surjective.iUnion_comp (Fintype.equivFin κ).symm.surjective]
    rfl
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  choose Us UsB hUsf hUs using fun i : s ↦ (hB i.1).exists_finite_of_isCompact (hc i i.2)
  let σ := Σ i : s, Us i
  have : Finite s := hs
  have (i) : Finite (Us i) := hUsf i
  refine ⟨σ, inferInstance, fun i ↦ i.1.1, fun i ↦ i.2.1, fun i ↦ UsB _ (by simp),
      fun _ ↦ hBc _ _ (UsB _ (by simp)), ?_⟩
  rw [← hunion]
  ext x
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨i, hi, o, ho⟩ ↦ ?_, fun ⟨i, hi, h, hmem, heq⟩ ↦ ?_⟩
  · use i.1, i.1.2
    refine ⟨hi, ?_, ho⟩
    simp only [hUs, coe_sSup, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    use i.2
    simpa
  · rw [hUs ⟨i, hi⟩, coe_sSup, Set.mem_iUnion] at hmem
    obtain ⟨a, ha⟩ := hmem
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
    use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

lemma iff_of_unique [Unique ι] {U : Set S} :
    IsCompactOpenCovered f U ↔ ∃ (V : Opens (X default)), IsCompact V.1 ∧ f default '' V.1 = U := by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ ↦ ?_, fun ⟨V, hc, h⟩ ↦ ?_⟩
  · by_cases h : s = ∅
    · simp only [h, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hcov
      exact ⟨⊥, isCompact_empty, by simpa⟩
    obtain rfl : s = {default} := by
      rw [← Set.univ_unique, Subsingleton.eq_univ_of_nonempty (Set.nonempty_iff_ne_empty.mpr h)]
    use V default (by simp), hc _ _
    simpa using hcov
  · refine ⟨{default}, Set.finite_singleton _, fun i h ↦ h ▸ V, fun i ↦ ?_, by simpa⟩
    rintro rfl
    simpa

lemma Set.isCompact_sigma {s : Set ι} {t : ∀ i, Set (X i)} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsCompact (t i)) : IsCompact (s.sigma t) := by
  rw [Set.sigma_eq_biUnion]
  apply hs.isCompact_biUnion fun i hi ↦ (ht i hi).image continuous_sigmaMk

lemma _root_.IsCompact.sigma_exists_finite_sigma_eq (u : Set (Σ i, X i)) (hu : IsCompact u) :
    ∃ (s : Set ι) (t : ∀ i, Set (X i)), s.Finite ∧ (∀ i, IsCompact (t i)) ∧ s.sigma t = u := by
  obtain ⟨s, hs⟩ := by
    refine hu.elim_finite_subcover (fun i : ι ↦ Sigma.mk i '' (Sigma.mk i ⁻¹' Set.univ))
        (fun i ↦ ?_) ?_
    · exact isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk
    · intro x hx
      rw [Set.mem_iUnion]
      exact ⟨x.1, by simp⟩
  use s, fun i ↦ Sigma.mk i ⁻¹' u, s.finite_toSet, fun i ↦ ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, Sigma.eta,
      and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    rw [Set.mem_iUnion] at hi
    obtain ⟨his, hj⟩ := hi
    convert his
    simpa using hj

lemma iff_isCompactOpenCovered_sigmaMk {U : Set S} :
    IsCompactOpenCovered f U ↔
      IsCompactOpenCovered (fun (_ : PUnit.{w + 1}) (p : Σ i : ι, X i) ↦ f p.1 p.2) U := by
  classical
  rw [iff_of_unique (ι := PUnit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ ↦ ?_, fun ⟨V, hc, heq⟩ ↦ ?_⟩
  · refine ⟨⟨s.sigma fun i ↦ if h : i ∈ s then V i h else ∅, ?_⟩, ?_, ?_⟩
    · rw [isOpen_sigma_iff]
      intro i
      by_cases h : i ∈ s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      refine Set.isCompact_sigma hs fun i ↦ ?_
      by_cases h : i ∈ s
      · simpa [h] using hc _ _
      · simp [h]
    · rw [← hU]
      ext x
      dsimp
      simp only [Set.mem_image, Set.mem_sigma_iff, Sigma.exists, Set.mem_iUnion, SetLike.mem_coe]
      refine ⟨fun ⟨i, b, ⟨hi, hb⟩, heq⟩ ↦ ?_, fun ⟨i, hi, b, hb, hx⟩ ↦ ?_⟩
      · simp only [hi, ↓reduceDIte, SetLike.mem_coe] at hb
        exact ⟨i, hi, b, hb, heq⟩
      · exact ⟨i, b, ⟨hi, by simpa [hi] using hb⟩, hx⟩
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i ∈ s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (s := s) (t := t) hi]
      apply isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi ↦ ⟨t i, this i hi⟩, fun i _ ↦ hc i, ?_⟩
    simp only [coe_mk, ← Set.image_sigma_eq_iUnion, heq', heq]

lemma of_isOpenMap {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1)
    [TopologicalSpace S] (hfc : ∀ i, Continuous (f i))
    (h : ∀ i, IsOpenMap (f i))
    {U : Set S} (hs : ∀ x ∈ U, ∃ i y, f i y = x) (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk.{0}, iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_isBasis
      (fun p : Σ i, X i ↦ f p.1 p.2) (isBasis_sigma hB) ?_ (continuous_sigma_iff.mpr hfc)
      (fun x hx ↦ ?_) hU hc
  · simp only [Set.mem_iUnion, carrier_eq_coe, Set.mem_image, forall_exists_index, and_imp]
    rintro U x hx hBx rfl
    exact (hBc _ _ hBx).image continuous_sigmaMk
  · simpa using hs x hx

end IsCompactOpenCovered
