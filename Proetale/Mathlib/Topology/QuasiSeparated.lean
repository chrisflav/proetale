import Mathlib.Topology.QuasiSeparated

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) : QuasiSeparatedSpace β :=
  (quasiSeparatedSpace_congr f).1 inferInstance

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) := by
  sorry

namespace Topology

/-- A function between topological spaces is quasi-compact if the preimages of compact open sets
are compact. -/
@[mk_iff]
class QuasiCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop where
  /-- The preimage of a compact open set under a quasi-compact map is compact. -/
  isCompact_preimage : ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

variable {X : Type*} [TopologicalSpace X]

theorem quasiSeparatedSpace_iff_quasiCompact_diagonal :
    QuasiSeparatedSpace X ↔ QuasiCompact (fun x : X ↦ (x, x)) := by
  constructor
  · intro h
    classical
    -- TODO: prove this direction (likely needs additional infrastructure about compact opens in `X × X`).
    sorry
  · intro h
    classical
    rw [quasiSeparatedSpace_iff]
    intro U V hUopen hUcomp hVopen hVcomp
    have hpre :
        (fun x : X ↦ (x, x)) ⁻¹' (U ×ˢ V) = U ∩ V := by
      ext x
      simp
    have :
        IsCompact ((fun x : X ↦ (x, x)) ⁻¹' (U ×ˢ V)) :=
      h.isCompact_preimage (U ×ˢ V) (hUopen.prod hVopen) (hUcomp.prod hVcomp)
    simpa [hpre] using this

instance (priority := 100) quasiCompact_diagonal_of_quasiSeparatedSpace [QuasiSeparatedSpace X] :
    QuasiCompact (fun x : X ↦ (x, x)) := by
  classical
  exact (quasiSeparatedSpace_iff_quasiCompact_diagonal (X := X)).1 inferInstance

end Topology
