import Mathlib.Topology.Connected.TotallyDisconnected

variable {X : Type*} [TopologicalSpace X]

@[stacks 0906]
instance totallyDisconnectedSpace_connectedComponent : TotallyDisconnectedSpace (ConnectedComponents X) := sorry
