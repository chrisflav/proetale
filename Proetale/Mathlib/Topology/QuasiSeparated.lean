import Mathlib.Topology.QuasiSeparated

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- Quasi-separatedness transfers along homeomorphisms. -/
-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) :
    QuasiSeparatedSpace β where
  inter_isCompact U V hUo hUc hVo hVc := by
    have key : ∀ W : Set β, IsCompact W → IsCompact (f ⁻¹' W) := fun W hW =>
      f.image_symm ▸ hW.image f.symm.continuous
    have hc := QuasiSeparatedSpace.inter_isCompact _ _
      (hUo.preimage f.continuous) (key U hUc) (hVo.preimage f.continuous) (key V hVc)
    rw [← f.image_preimage (U ∩ V), Set.preimage_inter]
    exact hc.image f.continuous

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) := by
  sorry
