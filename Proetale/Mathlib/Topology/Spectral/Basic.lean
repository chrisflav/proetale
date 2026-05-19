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
    simp only [← h1, ← h2, ← Set.preimage_inter]
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

variable {X} in
theorem generalizationHull.eq_sInter_of_isCompact [SpectralSpace X] {s : Set X} (hs : IsCompact s) :
    ∃ S ⊆ {U : Set X | IsOpen U ∧ IsCompact U}, (generalizationHull s) = ⋂₀ S := by
  refine ⟨{U : Set X | IsOpen U ∧ IsCompact U ∧ generalizationHull s ⊆ U},
    fun _ h ↦ ⟨h.1, h.2.1⟩, subset_antisymm (fun _ hx _ hU ↦ hU.2.2 hx) ?_⟩
  intro x hx
  by_contra hxW
  have hbasis := PrespectralSpace.isTopologicalBasis (X := X)
  have hcov : ∀ y ∈ s, ∃ U, (IsOpen U ∧ IsCompact U) ∧ y ∈ U ∧ x ∉ U := by
    intro y hy
    have hxy : ¬ x ⤳ y := fun h ↦ hxW (mem_generalizationHull_iff.mpr ⟨y, hy, h⟩)
    rw [specializes_iff_mem_closure] at hxy
    obtain ⟨U, hU, hyU, hUsub⟩ :=
      hbasis.exists_subset_of_mem_open hxy (isOpen_compl_iff.mpr isClosed_closure)
    exact ⟨U, hU, hyU, fun hxU ↦ hUsub hxU (subset_closure rfl)⟩
  choose U hU hyU hxnU using hcov
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun y : s ↦ U y y.2)
    (fun y ↦ (hU y y.2).1) (fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hyU y hy⟩)
  set V := ⋃ y ∈ t, U y.1 y.2 with hV_def
  have hVopen : IsOpen V := isOpen_biUnion fun y _ ↦ (hU y.1 y.2).1
  have hVcompact : IsCompact V :=
    t.finite_toSet.isCompact_biUnion fun y _ ↦ (hU y.1 y.2).2
  have hWsub : generalizationHull s ⊆ V := fun z hz ↦ by
    obtain ⟨y, hy, hzy⟩ := mem_generalizationHull_iff.mp hz
    exact hzy.mem_open hVopen (ht hy)
  have hxV : x ∈ V := hx V ⟨hVopen, hVcompact, hWsub⟩
  obtain ⟨y, hyt, hxUy⟩ : ∃ y ∈ t, x ∈ U y.1 y.2 := by
    simpa [hV_def] using hxV
  exact hxnU y.1 y.2 hxUy
