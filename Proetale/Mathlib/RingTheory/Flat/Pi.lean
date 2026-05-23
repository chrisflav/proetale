/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of finite products

We show that a finite product of flat modules is flat, and that a projection
from a finite product of commutative rings is flat as a ring map.

## Main results

- `Module.Flat.pi`: a finite product of flat modules is flat.
- `Pi.flat_evalRingHom`: a projection from a finite product of commutative rings is flat.
-/

universe u v

/-- A finite product of flat modules is flat. -/
instance Module.Flat.pi {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  exact .of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- A projection from a finite product of commutative rings is flat as a ring map.

The projection identifies `B i` with the localization of `∀ j, B j` away from the
idempotent `Pi.single i 1`. -/
lemma Pi.flat_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] (i : ι) :
    (Pi.evalRingHom B i).Flat := by
  classical
  algebraize [Pi.evalRingHom B i]
  have he : IsIdempotentElem (Pi.single i 1 : ∀ j, B j) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  haveI : IsLocalization.Away (Pi.single i 1 : ∀ j, B j) (B i) :=
    IsLocalization.away_of_isIdempotentElem he (RingHom.ker_evalRingHom B i)
      (Function.surjective_eval i)
  exact IsLocalization.flat (B i) (Submonoid.powers (Pi.single i 1 : ∀ j, B j))
