import Mathlib.Topology.Spectral.Prespectral

-- after `PrespectralSpace.sigma`
instance PrespectralSpace.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y] : PrespectralSpace (X × Y) :=
  sorry
