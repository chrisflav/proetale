import Mathlib.Topology.QuasiSeparated

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) :
    QuasiSeparatedSpace β where
  inter_isCompact U V hUo hUc hVo hVc := by
    have key : ∀ W : Set β, IsCompact W → IsCompact (f ⁻¹' W) := fun W hW => by
      have h : f.symm '' W = f ⁻¹' W := by
        ext x; simp [Set.mem_preimage, Set.mem_image, Homeomorph.symm_apply_eq]
      rw [← h]; exact hW.image f.symm.continuous
    have hc := QuasiSeparatedSpace.inter_isCompact _ _
      (hUo.preimage f.continuous) (key U hUc) (hVo.preimage f.continuous) (key V hVc)
    have heq : U ∩ V = f '' (f ⁻¹' U ∩ f ⁻¹' V) := by
      rw [← Set.preimage_inter]; ext y
      simp only [Set.mem_image, Set.mem_preimage]
      exact ⟨fun hy => ⟨f.symm y, by rwa [f.apply_symm_apply], f.apply_symm_apply y⟩,
        fun ⟨x, hx, hxy⟩ => hxy ▸ hx⟩
    rw [heq]; exact hc.image f.continuous

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) := by
  sorry
