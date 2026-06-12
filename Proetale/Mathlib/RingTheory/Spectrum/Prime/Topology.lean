import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Spectral.Hom

-- end of file
theorem PrimeSpectrum.continuous_sigmaToPi {ι : Type*} (R : ι → Type*)
    [(i : ι) → CommSemiring (R i)] :
    Continuous (PrimeSpectrum.sigmaToPi R) :=
  continuous_sigma fun _ ↦ continuous_comap (Pi.evalRingHom R _)

theorem PrimeSpectrum.isSpectralMap_comap {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) : IsSpectralMap (PrimeSpectrum.comap f) where
  toContinuous := PrimeSpectrum.continuous_comap f
  isCompact_preimage_of_isOpen s hs hc := by
    obtain ⟨I, hI_fg, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hc, hs⟩
    rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
    refine (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hI_fg.map f, ?_⟩).1
    rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_eq, ← Ideal.span_eq I, Ideal.map_span,
      PrimeSpectrum.zeroLocus_span, Ideal.span_eq]
