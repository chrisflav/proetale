import Mathlib.Topology.Sober

-- after `quasiSober_iff`
theorem Homeomorph.quasiSober {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] (f : X ≃ₜ Y) : QuasiSober Y := sorry

-- put this at end of the file
instance QuasiSober.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] : QuasiSober (X × Y) :=
  sorry
