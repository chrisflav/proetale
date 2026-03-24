/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Fin

/-!
# Algebra equivalences for Pi types

In this file we provide the algebra version of `RingEquiv.piFinTwo`.
-/

/-- The product over `Fin 2` of some algebras is the Cartesian product of these algebras. -/
def AlgEquiv.piFinTwo (A : Type*) [CommSemiring A] (R : Fin 2 → Type*)
    [∀ i, Semiring (R i)] [∀ i, Algebra A (R i)] :
    (∀ i : Fin 2, R i) ≃ₐ[A] R 0 × R 1 :=
  { RingEquiv.piFinTwo R with
    commutes' := fun _ => rfl }
