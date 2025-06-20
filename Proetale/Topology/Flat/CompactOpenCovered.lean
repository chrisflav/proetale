/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Sets.CompactOpenCovered

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

lemma Set.forall_mem_iUnion_iff {X ι : Type*} {p : X → Prop}
    {s : ι → Set X} :
    (∀ t ∈ (⋃ i, s i), p t) ↔ ∀ (i : ι), ∀ x ∈ s i, p x := by
  simp
  tauto

end

open TopologicalSpace Opens

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι → Type v} {f : ∀ i, X i → S} [∀ i, TopologicalSpace (X i)]

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

lemma comp {σ : ι → Type*} {Y : ∀ (i : ι) (k : σ i), Type*}
    (g : ∀ (i : ι) (k : σ i), Y i k → X i)
    [∀ i k, TopologicalSpace (Y i k)]
    {U : Set S} (hU : IsCompactOpenCovered f U) :
    IsCompactOpenCovered (fun (p : Σ (i : ι), σ i) ↦ f p.1 ∘ g p.1 p.2) U :=
  sorry

end IsCompactOpenCovered
