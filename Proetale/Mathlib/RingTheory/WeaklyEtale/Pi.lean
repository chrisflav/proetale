/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Proetale.Algebra.WeaklyEtale

/-!
# Finite product of weakly étale algebras

If `B i` is a weakly étale `A`-algebra for each `i` in a finite indexing type,
then `∀ i, B i` is a weakly étale `A`-algebra.

## Main results

- `Algebra.WeaklyEtale.pi`: a finite product of weakly étale algebras is weakly étale.
-/

universe u v

open scoped TensorProduct

/-- A finite product of flat modules is flat. -/
private lemma Module.Flat.finitePi
    {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  exact .of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- A projection from a finite product of commutative rings is flat as a ring map.

The projection identifies `B i` with the localization of `∀ j, B j` away from the
idempotent `Pi.single i 1`. -/
private lemma _root_.Pi.evalRingHom_flat
    {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] (i : ι) :
    (Pi.evalRingHom B i).Flat := by
  classical
  letI : Algebra (∀ j, B j) (B i) := (Pi.evalRingHom B i).toAlgebra
  have he : IsIdempotentElem (Pi.single i 1 : ∀ j, B j) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have hker : RingHom.ker (algebraMap (∀ j, B j) (B i)) =
      Ideal.span {1 - Pi.single i 1} := RingHom.ker_evalRingHom B i
  have hsurj : Function.Surjective (algebraMap (∀ j, B j) (B i)) :=
    Function.surjective_eval i
  haveI : IsLocalization.Away (Pi.single i 1 : ∀ j, B j) (B i) :=
    IsLocalization.away_of_isIdempotentElem he hker hsurj
  change Module.Flat (∀ j, B j) (B i)
  exact IsLocalization.flat (B i) (Submonoid.powers (Pi.single i 1 : ∀ j, B j))

namespace Algebra

/-- A finite product of weakly étale algebras over `A` is weakly étale. -/
instance WeaklyEtale.pi {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Algebra.WeaklyEtale A (B i)] :
    Algebra.WeaklyEtale A (∀ i, B i) := by
  classical
  cases nonempty_fintype ι
  refine ⟨Module.Flat.finitePi, ?_⟩
  let S := ∀ i, B i
  -- For each `k`, install the `(S ⊗[A] S)`-algebra structure on `B k` given by
  -- `proj_k ∘ lmul'`. By naturality of `lmul'`, this map factors as
  -- `lmul' A (B k) ∘ TensorProduct.map proj_k proj_k`, so flatness reduces to
  -- `proj_k`-flatness and `Algebra.WeaklyEtale.flat_lmul'` for each `B k`.
  letI : ∀ k, Algebra (S ⊗[A] S) (B k) := fun k =>
    ((Pi.evalAlgHom A B k).toRingHom.comp
      (Algebra.TensorProduct.lmul' A (S := S)).toRingHom).toAlgebra
  haveI : ∀ k, Module.Flat (S ⊗[A] S) (B k) := fun k => by
    have hf : (Pi.evalAlgHom A B k).toRingHom.Flat := Pi.evalRingHom_flat B k
    have h1 : (Algebra.TensorProduct.map (Pi.evalAlgHom A B k)
        (Pi.evalAlgHom A B k)).toRingHom.Flat :=
      Algebra.TensorProduct.flat_map hf hf
    have h2 : (Algebra.TensorProduct.lmul' A (S := B k)).toRingHom.Flat :=
      Algebra.WeaklyEtale.flat_lmul' A (B k)
    have hnat : (Pi.evalAlgHom A B k).comp (Algebra.TensorProduct.lmul' A (S := S)) =
        (Algebra.TensorProduct.lmul' A (S := B k)).comp
          (Algebra.TensorProduct.map (Pi.evalAlgHom A B k) (Pi.evalAlgHom A B k)) := by
      apply Algebra.TensorProduct.ext
      · ext x
        change (Pi.evalAlgHom A B k) (Algebra.TensorProduct.lmul' A (x ⊗ₜ[A] 1)) =
            Algebra.TensorProduct.lmul' A (S := B k)
              (Algebra.TensorProduct.map (Pi.evalAlgHom A B k)
                (Pi.evalAlgHom A B k) (x ⊗ₜ[A] 1))
        rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one, mul_one]
      · ext x
        change (Pi.evalAlgHom A B k) (Algebra.TensorProduct.lmul' A (1 ⊗ₜ[A] x)) =
            Algebra.TensorProduct.lmul' A (S := B k)
              (Algebra.TensorProduct.map (Pi.evalAlgHom A B k)
                (Pi.evalAlgHom A B k) (1 ⊗ₜ[A] x))
        rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.map_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul, one_mul]
    have heq : ((Pi.evalAlgHom A B k).toRingHom.comp
          (Algebra.TensorProduct.lmul' A (S := S)).toRingHom) =
        ((Algebra.TensorProduct.lmul' A (S := B k)).toRingHom.comp
          (Algebra.TensorProduct.map (Pi.evalAlgHom A B k)
            (Pi.evalAlgHom A B k)).toRingHom) := by
      simpa using congr_arg AlgHom.toRingHom hnat
    change RingHom.Flat ((Pi.evalAlgHom A B k).toRingHom.comp
      (Algebra.TensorProduct.lmul' A (S := S)).toRingHom)
    rw [heq]
    exact RingHom.Flat.comp h1 h2
  change Module.Flat (S ⊗[A] S) S
  exact Module.Flat.finitePi

end Algebra
