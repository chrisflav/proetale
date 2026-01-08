import Mathlib.Topology.Constructions

-- after `Topology.isOpenEmbedding_sigmaMap`
variable {α β : Type*} [TopologicalSpace α] [b : TopologicalSpace β]
theorem Prod.continuous_toSigma [DiscreteTopology α] : Continuous (Prod.toSigma : α × β → _) := by
  refine ⟨fun U hU ↦ ?_⟩
  rw [isOpen_prod_iff]
  rw [isOpen_sigma_iff] at hU
  intro a b hab
  use {a}, ((Sigma.mk (β := fun _ ↦ β) a) ⁻¹' U)
  refine ⟨by simp, hU a, by simp, hab, fun t hT ↦ ?_⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_preimage] at hT
  simpa [← hT.1] using hT.2
