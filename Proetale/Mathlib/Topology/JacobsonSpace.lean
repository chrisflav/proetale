import Mathlib.Topology.JacobsonSpace

variable {X : Type*} [TopologicalSpace X]

-- before `closedPoints_eq_univ`
theorem closedPoints.isClosed_singleton (x : closedPoints X) : IsClosed ({x} : Set (closedPoints X)) := by
  simpa [Set.preimage, Subtype.val_inj] using
      x.2.preimage (f := fun (x : closedPoints X) ↦ (x : X)) continuous_subtype_val
