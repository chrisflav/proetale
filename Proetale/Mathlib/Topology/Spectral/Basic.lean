import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.QuasiSeparated
import Proetale.Mathlib.Topology.Sober
import Proetale.Mathlib.Topology.Spectral.Prespectral


open Topology

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

-- after `SpectralSpace`
variable {X Y} in
theorem Homeomorph.spectralSpace [SpectralSpace X] (f : X ≃ₜ Y) : SpectralSpace Y :=
  {f.t0Space, f.compactSpace, f.quasiSober, f.quasiSeparatedSpace, f.prespectralSpace with}

variable {X Y} in
theorem Topology.IsClosedEmbedding.spectralSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [SpectralSpace Y] : SpectralSpace X where
  toT0Space := hf.isEmbedding.t0Space
  toQuasiSober := hf.quasiSober
  toQuasiSeparatedSpace := hf.quasiSeparatedSpace
  toCompactSpace := hf.compactSpace
  toPrespectralSpace := PrespectralSpace.of_isClosedEmbedding f hf

instance SpectralSpace.of_isClosed [SpectralSpace X] {C : Set X} [IsClosed C] : SpectralSpace C := (IsClosed.isClosedEmbedding_subtypeVal ‹_›).spectralSpace

@[stacks 0907]
instance SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) where
  toCompactSpace := inferInstance
  toT0Space := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance
