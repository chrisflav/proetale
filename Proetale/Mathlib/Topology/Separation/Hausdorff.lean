import Mathlib.Topology.Separation.Hausdorff

-- after `t2Space_iff_disjoint_nhds`
-- `by copilot`, this theorem exists in mathlib already.
@[stacks 08ZE]
theorem t2Space_iff_diagonal_closed {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ IsClosed (Set.range (fun x : X ↦ (x, x))) := by
  simpa [Set.range_diag] using (t2_iff_isClosed_diagonal (X := X))
