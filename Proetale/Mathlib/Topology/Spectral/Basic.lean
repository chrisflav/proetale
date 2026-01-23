import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.Inseparable
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
  toQuasiSeparatedSpace := by
    constructor
    intro V1 V2 open1 cpt1 open2 cpt2
    obtain ⟨U1, open1, cpt1, h1⟩ := hf.isOpen_and_isCompact_and_preimage_eq open1 cpt1
    obtain ⟨U2, open2, cpt2, h2⟩ := hf.isOpen_and_isCompact_and_preimage_eq open2 cpt2
    simp [← h1, ← h2, ← Set.preimage_inter]
    apply IsCompact.preimage_of_isOpen hf.isProperMap.isSpectralMap
    · exact QuasiSeparatedSpace.inter_isCompact U1 U2 open1 cpt1 open2 cpt2
    · exact open1.inter open2
  toCompactSpace := hf.compactSpace
  toPrespectralSpace := PrespectralSpace.of_isClosedEmbedding f hf

instance SpectralSpace.of_isClosed [SpectralSpace X] {C : Set X} [IsClosed C] : SpectralSpace C :=
  (IsClosed.isClosedEmbedding_subtypeVal ‹_›).spectralSpace

@[stacks 0907]
instance SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) where
  toCompactSpace := inferInstance
  toT0Space := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance

theorem generalizationHull.eq_sUnion_of_isCompact [SpectralSpace X] {s : Set X} (hs : IsCompact s) :
    ∃ S ⊆ {U : Set X | IsOpen U ∧ IsCompact U}, (generalizationHull s) = ⋃₀ S :=
  sorry
