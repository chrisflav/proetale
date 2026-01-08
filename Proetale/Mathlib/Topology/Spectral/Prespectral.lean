import Mathlib.Topology.Spectral.Prespectral

-- after `PrespectralSpace.of_isTopologicalBasis'`
theorem Homeomorph.prespectralSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace X] (f : X ≃ₜ Y) : PrespectralSpace Y := sorry

-- after `PrespectralSpace.sigma`
instance PrespectralSpace.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PrespectralSpace X] [PrespectralSpace Y] : PrespectralSpace (X × Y) :=
  sorry

-- end of file
theorem Topology.IsClosedEmbedding.isOpen_and_isCompact_and_preimage_eq {X Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Z] [PrespectralSpace X] [CompactSpace X]
    {f : Z → X} (hf : Topology.IsClosedEmbedding f) {V : Set Z} (h₁ : IsOpen V) (h₂ : IsCompact V) :
    ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ f ⁻¹' U = V := by
  obtain ⟨U', open', hV⟩ := hf.isInducing.isOpen_iff.mp h₁
  obtain ⟨S, Ui, hU', hUi⟩ := PrespectralSpace.isTopologicalBasis.open_eq_iUnion open'
  obtain ⟨T, hT⟩ := IsCompact.elim_finite_subcover h₂ (fun i ↦ f ⁻¹' Ui i)
    (fun i ↦ (hUi i).1.preimage hf.continuous)
    (by simpa [← hV, ← Set.preimage_iUnion] using Set.preimage_mono hU'.subset)
  have := fun i ↦ (hUi i).2.preimage_of_isOpen hf.isProperMap.isSpectralMap (hUi i).1
  have : V = ⋃ i ∈ T, f ⁻¹' Ui i := by
    refine subset_antisymm hT (Set.iUnion₂_subset ?_)
    rw [← hV, hU']
    exact fun _ _ ↦ Set.preimage_mono (Set.subset_iUnion _ _)
  use ⋃ i ∈ T, Ui i, isOpen_biUnion (fun i _ ↦ (hUi i).1),
    T.finite_toSet.isCompact_biUnion (fun i hi ↦ (hUi i).2)
  simp [this]
