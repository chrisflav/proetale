import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

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
  ⟨fun _ ↦ f.quasiSeparatedSpace, fun _ ↦ f.symm.quasiSeparatedSpace⟩

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [PrespectralSpace α]
    [QuasiSeparatedSpace β] [PrespectralSpace β] : QuasiSeparatedSpace (α × β) := by
  let b : ({ U : Set α // IsOpen U ∧ IsCompact U } × { V : Set β // IsOpen V ∧ IsCompact V }) →
      Set (α × β) := fun i ↦ (i.1.1 : Set α) ×ˢ (i.2.1 : Set β)
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := b) ?_ ?_
  · have hbα : IsTopologicalBasis ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α)) :=
      PrespectralSpace.isTopologicalBasis (X := α)
    have hbβ : IsTopologicalBasis ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) :=
      PrespectralSpace.isTopologicalBasis (X := β)
    have hrange : Set.range b =
        Set.image2 (· ×ˢ ·) ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α))
          ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) := by
      ext s
      refine ⟨?_, ?_⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.1.1, i.1.2, i.2.1, i.2.2, rfl⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    simpa [hrange] using hbα.prod hbβ
  · intro i j
    have hA : IsCompact ((i.1.1 : Set α) ∩ (j.1.1 : Set α)) :=
      i.1.2.2.inter_of_isOpen j.1.2.2 i.1.2.1 j.1.2.1
    have hB : IsCompact ((i.2.1 : Set β) ∩ (j.2.1 : Set β)) :=
      i.2.2.2.inter_of_isOpen j.2.2.2 i.2.2.1 j.2.2.1
    simpa [b, Set.prod_inter_prod] using hA.prod hB
