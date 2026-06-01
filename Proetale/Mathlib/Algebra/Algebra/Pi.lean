/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Ring.Fin
import Proetale.Mathlib.RingTheory.Idempotents

/-!
# Algebra equivalences for Pi types

In this file we provide the algebra version of `RingEquiv.piFinTwo`, and lemmas about algebra
homomorphisms out of a finite product of algebras to a local algebra.
-/

/-- The product over `Fin 2` of some algebras is the Cartesian product of these algebras. -/
def AlgEquiv.piFinTwo (A : Type*) [CommSemiring A] (R : Fin 2 → Type*)
    [∀ i, Semiring (R i)] [∀ i, Algebra A (R i)] :
    (∀ i : Fin 2, R i) ≃ₐ[A] R 0 × R 1 :=
  { RingEquiv.piFinTwo R with
    commutes' := fun _ => rfl }

namespace AlgHom

variable {k : Type*} [CommSemiring k] {I : Type*} [DecidableEq I]
  {A : I → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra k (A i)]
  {B : Type*} [CommRing B] [Algebra k B]

/-- An algebra homomorphism from a finite product of commutative rings to a nontrivial local
algebra factors through one of the factors: there exists `j : I` with `ψ (Pi.single j 1) = 1`
and `ψ (Pi.single i 1) = 0` for every `i ≠ j`. -/
lemma exists_pi_single_eq_one_of_isLocalRing [Finite I] [IsLocalRing B]
    (ψ : (∀ i, A i) →ₐ[k] B) :
    ∃ j : I, ψ (Pi.single j 1) = 1 ∧ ∀ i, i ≠ j → ψ (Pi.single i 1) = 0 := by
  have : Fintype I := Fintype.ofFinite I
  have hcoi : CompleteOrthogonalIdempotents
      (fun i : I ↦ Pi.single (M := fun i ↦ A i) i (1 : A i)) :=
    CompleteOrthogonalIdempotents.single _
  have hidem (i : I) : IsIdempotentElem (ψ (Pi.single i 1)) :=
    (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.idem i
  have h01 (i : I) : ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 :=
    (hidem i).eq_zero_or_one_of_isLocalRing
  have hsum : ∑ i : I, ψ (Pi.single i 1) = 1 := by
    rw [← map_sum]
    simp [hcoi.complete]
  have hortho (i j : I) (hij : i ≠ j) :
      ψ (Pi.single i 1) * ψ (Pi.single j 1) = 0 := by
    simpa [Function.comp_def] using
      (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.ortho hij
  have hex : ∃ j, ψ (Pi.single j 1) = 1 := by
    by_contra hall
    push Not at hall
    have hzero : ∀ i, ψ (Pi.single i 1) = 0 := fun i ↦ (h01 i).resolve_right (hall i)
    simp [hzero] at hsum
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, fun i hi ↦ ?_⟩
  have := hortho i j hi
  rwa [hj, mul_one] at this

/-- The algebra homomorphism `A j →ₐ[k] B` factoring `ψ : (∀ i, A i) →ₐ[k] B` through the
`j`-th factor, given that `ψ (Pi.single j 1) = 1` and `ψ (Pi.single i 1) = 0` for every
`i ≠ j`. Note that `B` is not required to be local; the hypotheses subsume that. -/
def piFactor (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (_hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) :
    A j →ₐ[k] B where
  toFun y := ψ (Pi.single j y)
  map_one' := hj
  map_mul' y₁ y₂ := by simp [Pi.single_mul]
  map_zero' := by simp
  map_add' y₁ y₂ := by simp [Pi.single_add]
  commutes' c := by
    have heq : Pi.single j (algebraMap k (A j) c) =
        (algebraMap k (∀ i, A i) c) * Pi.single j 1 := by
      ext i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    rw [heq, map_mul, AlgHom.commutes, hj, mul_one]

@[simp]
lemma piFactor_apply (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) (y : A j) :
    piFactor ψ j hj hothers y = ψ (Pi.single j y) := rfl

/-- An algebra homomorphism `ψ : (∀ i, A i) →ₐ[k] B` to a local algebra is recovered from its
factor through the unique component `A j` selected by the unit idempotents. -/
lemma eq_piFactor_apply [Finite I] (ψ : (∀ i, A i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1) (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0)
    (x : ∀ i, A i) : ψ x = piFactor ψ j hj hothers (x j) := by
  have : Fintype I := Fintype.ofFinite I
  rw [piFactor_apply]
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_eq_single_of_mem j (Finset.mem_univ _) fun i _ hi ↦ ?_
  have : Pi.single (M := fun i ↦ A i) i (x i) = Pi.single i 1 * x := by
    rw [← Pi.single_mul_left]
    simp
  rw [this, map_mul, hothers i hi, zero_mul]

end AlgHom
