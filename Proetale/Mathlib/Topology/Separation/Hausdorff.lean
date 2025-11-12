import Mathlib.Topology.Separation.Hausdorff

-- after `t2Space_iff_disjoint_nhds`
@[stacks 08ZE]
theorem t2Space_iff_diagonal_closed {X : Type*} [TopologicalSpace X] :
    T2Space X ↔ IsClosed (Set.range (fun x : X ↦ (x, x))) := by
  sorry
