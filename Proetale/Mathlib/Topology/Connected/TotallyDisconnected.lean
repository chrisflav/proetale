import Mathlib.Topology.Connected.TotallyDisconnected

variable {X : Type*} [TopologicalSpace X]

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form IsPreconnected.foo
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X] (x : X)
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) : Function.Injective (hf.connectedComponentsLift) := by
  sorry
