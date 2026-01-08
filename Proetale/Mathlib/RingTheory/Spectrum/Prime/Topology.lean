import Mathlib.RingTheory.Spectrum.Prime.Topology

-- end of file
theorem PrimeSpectrum.continuous_sigmaToPi {ι : Type*} (R : ι → Type*)
    [(i : ι) → CommSemiring (R i)] : Continuous (PrimeSpectrum.sigmaToPi R) := continuous_sigma fun _ ↦ (comap (Pi.evalRingHom R _)).2
