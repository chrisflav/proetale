import Mathlib.Topology.Maps.Basic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed map sends closed singletons to closed singletons. -/
lemma IsClosedMap.isClosed_singleton {f : X → Y} (hf : IsClosedMap f)
    {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} := by
  rw [← Set.image_singleton]
  exact hf _ hx
