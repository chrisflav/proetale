import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) : QuasiSeparatedSpace β :=
  (quasiSeparatedSpace_congr f).1 inferInstance

/-- A function between topological spaces is quasi-compact if the preimages of compact open sets
are compact. -/
def QuasiCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

variable {X : Type*} [TopologicalSpace X]

theorem quasiSeparatedSpace_of_quasiCompact_diagonal (h : QuasiCompact (fun x : X ↦ (x, x))) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff]
  intro U V hUopen hUcomp hVopen hVcomp
  have hpre :
      (fun x : X ↦ (x, x)) ⁻¹' (U ×ˢ V) = U ∩ V := by
    ext x
    simp
  have : IsCompact ((fun x : X ↦ (x, x)) ⁻¹' (U ×ˢ V)) :=
    h (U ×ˢ V) (hUopen.prod hVopen) (hUcomp.prod hVcomp)
  simpa [hpre] using this

theorem quasiCompact_diagonal_of_quasiSeparatedSpace [QuasiSeparatedSpace X] [PrespectralSpace X] :
    QuasiCompact (fun x : X ↦ (x, x)) := by
  sorry

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [PrespectralSpace α]
    [QuasiSeparatedSpace β] [PrespectralSpace β] : QuasiSeparatedSpace (α × β) := by
  sorry
