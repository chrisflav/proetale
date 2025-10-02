/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Topology.SpectralSpace.WLocal

universe u

class WLocalRing (R : Type*) [CommRing R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

structure RingHom.IsWLocal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  isWLocalMap_comap : IsWLocalMap (PrimeSpectrum.comap f)

/--
-- To avoid universe issues, we use [BS15, Lemma 2.2.9] as the definition of a `WStrictlyLocalRing`.
The definition of `Algebra.Etale R A` requires `R` and `A` to be in the same universe.
-/
class WStrictlyLocalRing (R : Type u) [CommRing R] : Prop extends WLocalRing R where
  section_exists :∀ (S : Type u) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Algebra.Etale R S] , ∃ f : S →+* R, f.comp (algebraMap R S) = RingHom.id R


/--

-/
theorem WStrictlyLocalRing.isStrictlyHenselianLocalRing_of_isMaximal {R : Type u} [CommRing R]
    [WStrictlyLocalRing R] (m : Ideal R) [m.IsMaximal] : IsStrictlyHenselianLocalRing
    (Localization.AtPrime m) := sorry

theorem wStrictlyLocalRing_of_isStrictlyHenselianLocalRing_atPrime {R : Type u} [CommRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], IsStrictlyHenselianLocalRing (Localization.AtPrime m)) : WStrictlyLocalRing R := sorry
