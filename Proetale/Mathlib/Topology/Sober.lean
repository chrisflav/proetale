import Mathlib.Topology.Sober

-- put this at end of the file
instance QuasiSober.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] : QuasiSober (X × Y) :=
  sorry
