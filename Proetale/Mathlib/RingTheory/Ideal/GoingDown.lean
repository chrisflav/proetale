import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Topology.JacobsonSpace

-- after `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
theorem Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (h : closedPoints (PrimeSpectrum R) ⊆ Set.range (algebraMap R S).specComap) :
    Function.Surjective (algebraMap R S).specComap := by
  rintro ⟨p, hp⟩
  obtain ⟨m, hm, hle⟩  := Ideal.exists_le_maximal _ hp.ne_top
  have : ⟨m, hm.isPrime⟩ ∈ closedPoints (PrimeSpectrum R) := by
    rwa [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  obtain ⟨⟨n, _⟩, hn⟩ := h this
  have : n.LiesOver m := ⟨PrimeSpectrum.ext_iff.mp hn.symm⟩
  obtain ⟨q, _, hq, hpq⟩ := Ideal.exists_ideal_le_liesOver_of_le n hle
  use ⟨q, hq⟩, PrimeSpectrum.ext hpq.over.symm
