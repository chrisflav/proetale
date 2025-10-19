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

/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

structure RingHom.IsWLocal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  isWLocalMap_comap : IsWLocalMap (PrimeSpectrum.comap f)

-- refactor this, using the definition of strict henselian.
/--
-- To avoid universe issues, we use [BS15, Lemma 2.2.9] as the definition of a `WStrictlyLocalRing`.
The definition of `Algebra.Etale R A` requires `R` and `A` to be in the same universe.
-/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where

theorem WStrictlyLocalRing.isStrictlyHenselianLocalRing_of_isMaximal {R : Type*} [CommRing R]
    [IsWStrictlyLocalRing R] (m : Ideal R) [m.IsMaximal] : IsStrictlyHenselianLocalRing
    (Localization.AtPrime m) :=
  sorry

theorem wStrictlyLocalRing_of_isStrictlyHenselianLocalRing_atPrime {R : Type*} [CommRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal], IsStrictlyHenselianLocalRing (Localization.AtPrime m)) :
    IsWStrictlyLocalRing R :=
  sorry
