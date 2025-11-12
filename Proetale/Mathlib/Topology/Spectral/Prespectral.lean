import Mathlib.Topology.Spectral.Prespectral

-- after `PrespectralSpace.of_isTopologicalBasis'`
theorem Homeomorph.prespectralSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace X] (f : X ≃ₜ Y) : PrespectralSpace Y := sorry

-- after `PrespectralSpace.sigma`
instance PrespectralSpace.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y] : PrespectralSpace (X × Y) :=
  sorry
