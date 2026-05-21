/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Topology.SpectralSpace.WLocal.Basic
import Proetale.Algebra.StalkIso

/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

variable {R S : Type*} [CommRing R] [CommRing S]

instance (R : Type*) [CommSemiring R] [IsWLocalRing R] : WLocalSpace (PrimeSpectrum R) :=
  IsWLocalRing.wLocalSpace_primeSepectrum

lemma IsWLocalRing.of_surjective {f : R →+* S} (hf : Function.Surjective f) [IsWLocalRing R] :
    IsWLocalRing S :=
  ⟨(PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hf).wLocalSpace⟩

/-- A ring homomorphism is w-local if the induced map on spectra is w-local. -/
def RingHom.IsWLocal {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

lemma RingHom.isWLocal_iff_isMaximal_of_isMaximal (f : R →+* S) :
    IsWLocal f ↔ ∀ (m : Ideal S) [m.IsMaximal], (m.comap f).IsMaximal := by
  rw [IsWLocal, isWLocalMap_iff]
  refine ⟨fun ⟨_, h⟩ m hm ↦ ?_, fun hmax ↦ ?_⟩
  · have hm_cp : (⟨m, hm.isPrime⟩ : PrimeSpectrum S) ∈ closedPoints (PrimeSpectrum S) := by
      rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      exact hm
    have hcl : PrimeSpectrum.comap f ⟨m, hm.isPrime⟩ ∈ closedPoints (PrimeSpectrum R) := h hm_cp
    rwa [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hcl
  · refine ⟨⟨PrimeSpectrum.continuous_comap f, fun s hs hc ↦ ?_⟩, fun x hx ↦ ?_⟩
    · obtain ⟨I, hI_fg, rfl⟩ := PrimeSpectrum.isCompact_isOpen_iff_ideal.mp ⟨hc, hs⟩
      rw [Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
      refine (PrimeSpectrum.isCompact_isOpen_iff_ideal.mpr ⟨_, hI_fg.map f, ?_⟩).1
      rw [← PrimeSpectrum.zeroLocus_span, Ideal.span_eq, ← Ideal.span_eq I, Ideal.map_span,
        PrimeSpectrum.zeroLocus_span, Ideal.span_eq]
    · rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at hx
      rw [Set.mem_preimage, mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
      exact hmax x.asIdeal

namespace RingHom.IsWLocal

/-- A w-local ring map between w-local rings that is bijective on stalks and
bijective on connected components is bijective. -/
lemma bijective_of_bijective [IsWLocalRing R] [IsWLocalRing S] {f : R →+* S} (hw : f.IsWLocal)
    (hs : f.BijectiveOnStalks)
    (hb : (PrimeSpectrum.continuous_comap f).connectedComponentsMap.Bijective) :
    Function.Bijective f :=
  sorry

end RingHom.IsWLocal

/-- A w-strictly-local ring is a w-local ring whose stalks at maximal ideals are strictly Henselian
local rings. -/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where
  isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m)
