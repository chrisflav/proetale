import Mathlib.Topology.QuasiSeparated

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- Quasi-separatedness transfers along homeomorphisms. -/
-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) :
    QuasiSeparatedSpace β where
  inter_isCompact U V hUo hUc hVo hVc := by
    have hc := QuasiSeparatedSpace.inter_isCompact _ _
      (hUo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hUc)
      (hVo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hVc)
    rw [← f.image_preimage (U ∩ V), Set.preimage_inter]
    exact hc.image f.continuous

/-- Quasi-separatedness is invariant under homeomorphisms. -/
theorem Homeomorph.quasiSeparatedSpace_iff (f : α ≃ₜ β) :
    QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β :=
  ⟨fun _ => f.quasiSeparatedSpace, fun _ => f.symm.quasiSeparatedSpace⟩

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) := by
  sorry
