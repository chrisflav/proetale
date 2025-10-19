import Mathlib.Topology.Inseparable

/-- The generalization hull of `s` is the smallest set containing `s` that is stable
under generalization.
It is equal to the set of points specializing to a point in `s`, see `generalizationHull_eq`. -/
def generalizationHull {X : Type*} [TopologicalSpace X] (s : Set X) : Set X :=
  ⋂₀ {t : Set X | StableUnderGeneralization t ∧ s ⊆ t }

variable {X : Type*} [TopologicalSpace X]

lemma stableUnderGeneralization_generalizationHull (s : Set X) :
    StableUnderGeneralization (generalizationHull s) :=
  stableUnderGeneralization_sInter _ fun _ ht ↦ ht.1

lemma generalizationHull_eq (s : Set X) :
    generalizationHull s = { x | ∃ y ∈ s, x ⤳ y } := by
  rw [generalizationHull]
  refine subset_antisymm ?_ ?_
  · apply Set.sInter_subset_of_mem
    refine ⟨?_, ?_⟩
    · intro x y hyx ⟨z, hzs, hxz⟩
      use z, hzs, hyx.trans hxz
    · intro x hx
      use x
  · rw [Set.subset_sInter_iff]
    intro t ⟨ht, hs⟩ x ⟨y, hy, h⟩
    exact ht h (hs hy)

lemma mem_generalizationHull_iff {s : Set X} {x : X} :
    x ∈ generalizationHull s ↔ ∃ y ∈ s, x ⤳ y := by
  rw [generalizationHull_eq]
  rfl

lemma Topology.IsEmbedding.specializes_iff {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {x y : X} :
    f x ⤳ f y ↔ x ⤳ y := by
  rw [specializes_iff_mem_closure, ← Set.mem_preimage, ← Set.image_singleton,
    ← hf.closure_eq_preimage_closure_image, specializes_iff_mem_closure]
