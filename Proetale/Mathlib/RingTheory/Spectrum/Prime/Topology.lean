import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Spectral.Hom

-- end of file
theorem PrimeSpectrum.continuous_sigmaToPi {ι : Type*} (R : ι → Type*)
    [(i : ι) → CommSemiring (R i)] :
    Continuous (PrimeSpectrum.sigmaToPi R) :=
  continuous_sigma fun _ ↦ continuous_comap (Pi.evalRingHom R _)

/-- The factors of `Spec (∀ i, R i)` are pairwise incomparable under specialization: if the
images under `PrimeSpectrum.sigmaToPi` of two points are comparable, they lie over the same
factor. -/
theorem PrimeSpectrum.sigmaToPi_fst_eq_of_le {ι : Type*} {R : ι → Type*}
    [∀ i, CommSemiring (R i)] {x y : Σ i, PrimeSpectrum (R i)}
    (h : PrimeSpectrum.sigmaToPi R x ≤ PrimeSpectrum.sigmaToPi R y) :
    x.1 = y.1 := by
  classical
  obtain ⟨i, p⟩ := x
  obtain ⟨j, q⟩ := y
  simp only [PrimeSpectrum.sigmaToPi_apply] at h
  by_contra hne
  have hmem : (Pi.single j 1 : ∀ k, R k) ∈
      (PrimeSpectrum.comap (Pi.evalRingHom R i) p).asIdeal := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    simp [Pi.single_eq_of_ne hne]
  have h1 : (1 : R j) ∈ q.asIdeal := by
    have h2 := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h hmem
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h2
    simpa using h2
  exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem PrimeSpectrum.isSpectralMap_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : IsSpectralMap (PrimeSpectrum.comap f) where
  toContinuous := PrimeSpectrum.continuous_comap f
  isCompact_preimage_of_isOpen s hs hc := by
    obtain ⟨I, hI_fg, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hc, hs⟩
    rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    refine (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hI_fg.map f, ?_⟩).1
    rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_eq, ← Ideal.span_eq I, Ideal.map_span,
      PrimeSpectrum.zeroLocus_span, Ideal.span_eq]
