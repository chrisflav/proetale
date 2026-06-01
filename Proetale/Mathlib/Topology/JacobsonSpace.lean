import Mathlib.Topology.JacobsonSpace

variable {X : Type*} [TopologicalSpace X]

-- before `closedPoints_eq_univ`
theorem closedPoints.isClosed_singleton (x : closedPoints X) :
    IsClosed ({x} : Set (closedPoints X)) := by
  simpa [Set.preimage, Subtype.val_inj] using
      x.2.preimage (f := fun (x : closedPoints X) ↦ (x : X)) continuous_subtype_val

lemma closedPoints_prod (Y : Type*) [TopologicalSpace Y] :
    closedPoints (X × Y) = closedPoints X ×ˢ closedPoints Y := by
  ext ⟨x, y⟩
  simp only [mem_closedPoints_iff, Set.mem_prod, ← closure_eq_iff_isClosed,
    ← Set.singleton_prod_singleton, closure_prod_eq]
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ ↦ by rw [hx, hy]⟩
  refine ⟨Set.Subset.antisymm (fun z hz ↦ ?_) subset_closure,
    Set.Subset.antisymm (fun z hz ↦ ?_) subset_closure⟩
  · have : (z, y) ∈ closure ({x} : Set X) ×ˢ closure ({y} : Set Y) := ⟨hz, subset_closure rfl⟩
    rw [h] at this
    exact this.1
  · have : (x, z) ∈ closure ({x} : Set X) ×ˢ closure ({y} : Set Y) := ⟨subset_closure rfl, hz⟩
    rw [h] at this
    exact this.2
