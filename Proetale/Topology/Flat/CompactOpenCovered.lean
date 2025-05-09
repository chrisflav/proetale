/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Basic

/-!
# Compact open covered sets

-/

universe w u v

lemma PrespectralSpace.exists_isCompact_and_isOpen_between {X : Type*} [TopologicalSpace X]
    [PrespectralSpace X] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hUV : K ⊆ U) :
    ∃ (W : Set X), IsCompact W ∧ IsOpen W ∧ W ⊆ U ∧ K ⊆ W := by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hWU, hKW⟩ ↦ ?_) ?_ ?_
  · use W, Wc, Wo, hWU, subset_trans hst hKW
  · intro s t ⟨W₁, Wc₁, Wo₁, hWU₁, hKW₁⟩ ⟨W₂, Wc₂, Wo₂, hWU₂, hKW₂⟩
    use W₁ ∪ W₂
    exact ⟨Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset hWU₁ hWU₂,
      Set.union_subset_union hKW₁ hKW₂⟩
  · intro x hx
    obtain ⟨V, h, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hUV hx) hU
    exact ⟨V, mem_nhdsWithin.mpr ⟨V, h.1, hxV, Set.inter_subset_left⟩, V, h.2, h.1, hVU, subset_rfl⟩

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

instance PrespectralSpace.sigma {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    [∀ i, PrespectralSpace (X i)] : PrespectralSpace (Σ i, X i) :=
  .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i ↦ isTopologicalBasis) fun U hU ↦ by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

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

variable [∀ i, TopologicalSpace (X i)]

lemma Set.isCompact_sigma {s : Set ι} {t : ∀ i, Set (X i)} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsCompact (t i)) : IsCompact (s.sigma t) := by
  rw [Set.sigma_eq_biUnion]
  apply hs.isCompact_biUnion fun i hi ↦ (ht i hi).image continuous_sigmaMk

lemma IsCompact.sigma_exists_finite_sigma_eq (u : Set (Σ i, X i)) (hu : IsCompact u) :
    ∃ (s : Set ι) (t : ∀ i, Set (X i)), s.Finite ∧ (∀ i, IsCompact (t i)) ∧ s.sigma t = u := by
  obtain ⟨s, hs⟩ := hu.elim_finite_subcover (fun i : ι ↦ Sigma.mk i '' (Sigma.mk i ⁻¹' Set.univ))
    (fun i ↦ isOpenMap_sigmaMk _ <| isOpen_univ.preimage continuous_sigmaMk)
    fun x hx ↦ (by aesop)
  use s, fun i ↦ Sigma.mk i ⁻¹' u, s.finite_toSet, fun i ↦ ?_, ?_
  · exact Topology.IsClosedEmbedding.sigmaMk.isCompact_preimage hu
  · ext x
    simp only [Set.mem_sigma_iff, Finset.mem_coe, Set.mem_preimage, and_iff_right_iff_imp]
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    aesop

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

lemma empty : IsCompactOpenCovered f ∅ :=
  ⟨∅, Set.finite_empty, fun _ _ ↦ ⟨∅, isOpen_empty⟩, fun _ _ ↦ isCompact_empty, by simp⟩

lemma iff_of_unique [Unique ι] {U : Set S} :
    IsCompactOpenCovered f U ↔ ∃ (V : Opens (X default)), IsCompact V.1 ∧ f default '' V.1 = U := by
  refine ⟨fun ⟨s, hs, V, hc, hcov⟩ ↦ ?_, fun ⟨V, hc, h⟩ ↦ ?_⟩
  · by_cases h : s = ∅
    · aesop
    · obtain rfl : s = {default} := by
        rw [← Set.univ_unique, Subsingleton.eq_univ_of_nonempty (Set.nonempty_iff_ne_empty.mpr h)]
      aesop
  · refine ⟨{default}, Set.finite_singleton _, fun i h ↦ h ▸ V, fun i ↦ ?_, by simpa⟩
    rintro rfl
    simpa

lemma id_iff_isOpen_and_isCompact [TopologicalSpace S] {U : Set S} :
    IsCompactOpenCovered (fun _ : Unit ↦ id) U ↔ IsOpen U ∧ IsCompact U := by
  rw [iff_of_unique]
  refine ⟨fun ⟨V, hV, heq⟩ ↦ ?_, fun ⟨ho, hc⟩ ↦ ⟨⟨U, ho⟩, hc, by simp⟩⟩
  simp only [id_eq, Set.image_id', carrier_eq_coe, ← heq] at heq ⊢
  exact ⟨V.2, hV⟩

lemma iff_isCompactOpenCovered_sigmaMk {U : Set S} :
    IsCompactOpenCovered f U ↔
      IsCompactOpenCovered (fun (_ : Unit) (p : Σ i : ι, X i) ↦ f p.1 p.2) U := by
  classical
  rw [iff_of_unique (ι := Unit)]
  refine ⟨fun ⟨s, hs, V, hc, hU⟩ ↦ ?_, fun ⟨V, hc, heq⟩ ↦ ?_⟩
  · refine ⟨⟨s.sigma fun i ↦ if h : i ∈ s then V i h else ∅, isOpen_sigma_iff.mpr ?_⟩, ?_, ?_⟩
    · intro i
      by_cases h : i ∈ s
      · simpa [h] using (V _ _).2
      · simp [h]
    · dsimp only
      exact Set.isCompact_sigma hs fun i ↦ (by aesop)
    · aesop
  · obtain ⟨s, t, hs, hc, heq'⟩ := hc.sigma_exists_finite_sigma_eq
    have (i : ι) (hi : i ∈ s) : IsOpen (t i) := by
      rw [← Set.mk_preimage_sigma (t := t) hi]
      exact isOpen_sigma_iff.mp (heq' ▸ V.2) i
    refine ⟨s, hs, fun i hi ↦ ⟨t i, this i hi⟩, fun i _ ↦ hc i, ?_⟩
    simp only [coe_mk, ← Set.image_sigma_eq_iUnion, heq', heq]

lemma of_iUnion_eq_of_finite {U : Set S} (s : Set (Set S)) (hs : ⋃ t ∈ s, t = U) (hf : s.Finite)
    (H : ∀ t ∈ s, IsCompactOpenCovered f t) : IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  have (t) (h : t ∈ s) : ∃ (V : Opens (Σ i, X i)),
      IsCompact V.1 ∧ (fun p ↦ f p.fst p.snd) '' V.carrier = t := by
    have := H t h
    rwa [iff_isCompactOpenCovered_sigmaMk, iff_of_unique] at this
  choose V hVeq hVc using this
  refine ⟨⨆ (t : s), V t t.2, ?_, ?_⟩
  · simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_iSup, Opens.coe_mk]
    have : Finite s := hf
    exact isCompact_iUnion (fun _ ↦ hVeq _ _)
  · simp [Set.image_iUnion, ← hs]
    aesop

lemma of_iUnion_eq_of_isCompact [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (s : Set (Opens S)) (hs : ⋃ t ∈ s, t = U) (H : ∀ t ∈ s, IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun V : s ↦ V.1) (fun V ↦ V.1.2) (by simp [← hs])
  refine of_iUnion_eq_of_finite (SetLike.coe '' (t.image Subtype.val : Set (Opens S))) ?_ ?_ ?_
  · exact subset_antisymm (fun x ↦ by aesop) (subset_trans ht <| by simp)
  · exact Set.toFinite _
  · aesop

lemma of_isCompact_of_forall_exists [TopologicalSpace S] {U : Set S} (hU : IsCompact U)
    (H : ∀ x ∈ U, ∃ t ⊆ U, x ∈ t ∧ IsOpen t ∧ IsCompactOpenCovered f t) :
    IsCompactOpenCovered f U := by
  choose Us hU' hUx hUo hU'' using H
  refine of_iUnion_eq_of_isCompact hU { Us x h | (x : S) (h : x ∈ U) } ?_ ?_
  · refine subset_antisymm (fun x ↦ ?_) fun x hx ↦ ?_
    · simp only [Set.mem_setOf_eq, Set.iUnion_exists, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
        exists_and_right, forall_exists_index, and_imp]
      intro V y hy heq hyV
      apply hU' y hy
      rwa [heq]
    · simpa using ⟨⟨Us x hx, hUo _ _⟩, ⟨x, by simpa⟩, hUx _ _⟩
  · simp only [Set.mem_setOf_eq, forall_exists_index]
    intro t x hx heq
    rw [← heq]
    exact hU'' _ _

lemma exists_mem_of_isBasis {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1) {U : Set S} (hU : IsCompactOpenCovered f U) :
    ∃ (n : ℕ) (a : Fin n → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧
      ⋃ i, f (a i) '' V i = U := by
  suffices h : ∃ (κ : Type _) (_ : Finite κ) (a : κ → ι) (V : ∀ i, Opens (X (a i))),
      (∀ i, V i ∈ B (a i)) ∧ (∀ i, IsCompact (V i).1) ∧ ⋃ i, f (a i) '' V i = U by
    obtain ⟨κ, _, a, V, hB, hc, hU⟩ := h
    cases nonempty_fintype κ
    refine ⟨Fintype.card κ, a ∘ (Fintype.equivFin κ).symm, fun i ↦ V _, fun i ↦ hB _, fun i ↦ hc _,
      ?_⟩
    simp [← hU, ← (Fintype.equivFin κ).symm.surjective.iUnion_comp, Function.comp_apply]
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
  refine ⟨fun ⟨i, hi, o, ho⟩ ↦ by aesop, fun ⟨i, hi, h, hmem, heq⟩ ↦ ?_⟩
  rw [hUs ⟨i, hi⟩, coe_sSup, Set.mem_iUnion] at hmem
  obtain ⟨a, ha⟩ := hmem
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ha
  use ⟨⟨i, hi⟩, ⟨a, ha.1⟩⟩, h, ha.2, heq

lemma of_isOpenMap {B : ∀ i, Set (Opens (X i))} (hB : ∀ i, IsBasis (B i))
    (hBc : ∀ (i : ι), ∀ U ∈ B i, IsCompact U.1)
    [TopologicalSpace S] (hfc : ∀ i, Continuous (f i))
    (h : ∀ i, IsOpenMap (f i))
    {U : Set S} (hs : ∀ x ∈ U, ∃ i y, f i y = x) (hU : IsOpen U) (hc : IsCompact U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique]
  refine (isOpenMap_sigma.mpr h).exists_opens_image_eq_of_isBasis
      (fun p : Σ i, X i ↦ f p.1 p.2) (isBasis_sigma hB) ?_ (continuous_sigma_iff.mpr hfc)
      (fun x hx ↦ ?_) hU hc
  · simp only [Set.mem_iUnion, carrier_eq_coe, Set.mem_image, forall_exists_index, and_imp]
    rintro U x hx hBx rfl
    exact (hBc _ _ hBx).image continuous_sigmaMk
  · simpa using hs x hx

lemma of_finite {U : Set S} {κ : Type*} [Finite κ] (a : κ → ι) (V : ∀ k, Opens (X (a k)))
    (hV : ∀ k, IsCompact (V k).1) (hU : ⋃ k, f (a k) '' V k = U) :
    IsCompactOpenCovered f U := by
  refine ⟨Set.range a, Set.finite_range a, fun i hi ↦ ⨆ (k : κ) (h : i = a k), h ▸ V k,
      fun i hi ↦ ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    refine isCompact_iUnion fun i ↦ isCompact_iUnion ?_
    rintro rfl
    exact hV _
  · simp only [Set.mem_range, iSup_mk, carrier_eq_coe, coe_mk, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', ← hU]
    ext x
    simp_rw [Set.image_iUnion, Set.mem_iUnion]
    refine ⟨fun ⟨i, j, h, y, hy, hyx⟩ ↦ ⟨j, h ▸ y, ?_, ?_⟩, fun ⟨m, y, h, e⟩ ↦ ⟨m, m, rfl, y, h, e⟩⟩
    · simp only [SetLike.mem_coe] at hy ⊢
      convert hy using 1 <;> try rw [h]
      repeat simp
    · rw [← hyx]
      congr 1 <;> simp [h]

/-- Being compact open covered descends along refinements if the spaces are prespectral. -/
lemma of_comp [∀ i, PrespectralSpace (X i)] [TopologicalSpace S]
    {σ : Type*} {Y : σ → Type*} [∀ i, TopologicalSpace (Y i)]
    (g : ∀ i, Y i → S) {a : σ → ι} (t : ∀ i, Y i → X (a i)) (ht : ∀ i, Continuous (t i))
    (hge : ∀ i, g i = f (a i) ∘ t i)
    (hf : ∀ i, Continuous (f i)) {U : Set S} (ho : IsOpen U) (hU : IsCompactOpenCovered g U) :
    IsCompactOpenCovered f U := by
  rw [iff_isCompactOpenCovered_sigmaMk, iff_of_unique] at hU ⊢
  let p : (Σ i, Y i) → (Σ i, X i) := Sigma.map a t
  have hcomp : (fun x ↦ f x.1 x.2) ∘ p = fun x ↦ g x.1 x.2 := by
    ext
    simp [hge, p, Sigma.map]
  have hp : Continuous p := Continuous.sigma_map ht
  have hf : Continuous (fun p : Σ i, X i ↦ f p.1 p.2) := by simp [hf]
  obtain ⟨V, hV, heq⟩ := hU
  obtain ⟨K, hK, ho, hKU, hVK⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
      (hV.image hp) (ho.preimage hf) <| by
    simp [← heq, ← Set.preimage_comp, hcomp, Set.subset_preimage_image]
  refine ⟨⟨K, ho⟩, hK, subset_antisymm (by simpa) ?_⟩
  rw [← heq, ← hcomp, Set.image_comp]
  exact subset_trans (Set.image_mono hVK) (by simp)

end IsCompactOpenCovered
