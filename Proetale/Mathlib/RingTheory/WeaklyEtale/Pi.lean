/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Pi
import Proetale.Mathlib.RingTheory.WeaklyEtale.Local

/-!
# Finite product of weakly étale algebras

If `B i` is a weakly étale `A`-algebra for each `i` in a finite indexing type,
then `∀ i, B i` is a weakly étale `A`-algebra.

## Main results

- `Algebra.WeaklyEtale.pi`: a finite product of weakly étale algebras is weakly étale.
-/

universe u v

namespace Algebra

/-- A finite product of weakly étale algebras over `A` is weakly étale. -/
instance WeaklyEtale.pi {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Algebra.WeaklyEtale A (B i)] :
    Algebra.WeaklyEtale A (∀ i, B i) := by
  classical
  letI (i : ι) : Algebra (∀ j, B j) (B i) := (Pi.evalAlgHom A B i).toAlgebra
  have (i : ι) : IsLocalization.Away (Pi.single i 1 : ∀ j, B j) (B i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom B i).surjective)
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  exact Algebra.WeaklyEtale.of_span_eq_top_target_of_isLocalizationAway
    _ (Ideal.span_single_eq_top B) (fun i ↦ B i)

end Algebra
