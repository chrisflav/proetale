/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Proetale.Mathlib.RingTheory.Idempotents

/-!
# Sections of algebra homomorphisms out of a product

Let `σ : C × E →ₐ[R] A` be an algebra homomorphism. The elements `σ (1, 0)` and `σ (0, 1)` are
orthogonal idempotents of `A` summing to `1`. When `σ (1, 0) = 1` (equivalently `σ (0, 1) = 0`),
the function `c ↦ σ (c, 0)` is a unital algebra homomorphism `C →ₐ[R] A`; symmetrically for `E`.

There is no unital `AlgHom.inl : C →ₐ[R] C × E`: the natural inclusion `c ↦ (c, 0)` fails to send
`1` to `1`. The section constructions below capture the situation in which the post-composition
with such an inclusion is nevertheless unital. In a local target ring, the idempotent `σ (1, 0)`
is forced to be `0` or `1`, so one of the two sections is always available.

## Main definitions

- `AlgHom.compFstSection`: from `σ : C × E →ₐ[R] A` with `σ (1, 0) = 1`, the algebra hom
  `C →ₐ[R] A`, `c ↦ σ (c, 0)`.
- `AlgHom.compSndSection`: dual, requiring `σ (0, 1) = 1`.

## Main lemmas

- `AlgHom.isIdempotentElem_apply_inl` / `_inr`: idempotency of `σ (1, 0)` and `σ (0, 1)`.
- `AlgHom.apply_inl_add_apply_inr`: `σ (1, 0) + σ (0, 1) = 1`.
- `AlgHom.apply_inl_eq_zero_or_one` (over a local ring): the idempotent `σ (1, 0)` is `0` or `1`.
- `AlgHom.exists_section_of_isLocalRing`: over a local target ring, every algebra hom out of a
  binary product factors through one of the two projections.
-/

universe u v w₁ w₂

namespace AlgHom

section Semiring

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Semiring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A)

/-- For `σ : C × E →ₐ[R] A`, the image `σ (1, 0)` is an idempotent of `A`. -/
theorem isIdempotentElem_apply_inl : IsIdempotentElem (σ (1, 0)) := by
  change σ (1, 0) * σ (1, 0) = σ (1, 0)
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- For `σ : C × E →ₐ[R] A`, the image `σ (0, 1)` is an idempotent of `A`. -/
theorem isIdempotentElem_apply_inr : IsIdempotentElem (σ (0, 1)) := by
  change σ (0, 1) * σ (0, 1) = σ (0, 1)
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- The idempotents `σ (1, 0)` and `σ (0, 1)` sum to `1` in `A`. -/
theorem apply_inl_add_apply_inr : σ (1, 0) + σ (0, 1) = 1 := by
  rw [← map_add]
  have h : ((1, 0) + (0, 1) : C × E) = 1 := by ext <;> simp
  rw [h, map_one]

/-- The idempotents `σ (1, 0)` and `σ (0, 1)` are orthogonal. -/
theorem apply_inl_mul_apply_inr : σ (1, 0) * σ (0, 1) = 0 := by
  rw [← map_mul]
  have h : ((1, 0) * (0, 1) : C × E) = 0 := by ext <;> simp
  rw [h, map_zero]

/-- The idempotents `σ (0, 1)` and `σ (1, 0)` are orthogonal. -/
theorem apply_inr_mul_apply_inl : σ (0, 1) * σ (1, 0) = 0 := by
  rw [← map_mul]
  have h : ((0, 1) * (1, 0) : C × E) = 0 := by ext <;> simp
  rw [h, map_zero]

end Semiring

section Ring

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A)

/-- If `σ (1, 0) = 1`, then `σ (0, 1) = 0`. -/
theorem apply_inr_eq_zero_of_apply_inl_eq_one (h : σ (1, 0) = 1) : σ (0, 1) = 0 := by
  have heq := apply_inl_add_apply_inr σ
  rw [h] at heq
  exact add_left_cancel (heq.trans (add_zero 1).symm)

/-- If `σ (0, 1) = 1`, then `σ (1, 0) = 0`. -/
theorem apply_inl_eq_zero_of_apply_inr_eq_one (h : σ (0, 1) = 1) : σ (1, 0) = 0 := by
  have heq := apply_inl_add_apply_inr σ
  rw [h] at heq
  exact add_right_cancel (heq.trans (zero_add 1).symm)

/-- If `σ (1, 0) = 0`, then `σ (0, 1) = 1`. -/
theorem apply_inr_eq_one_of_apply_inl_eq_zero (h : σ (1, 0) = 0) : σ (0, 1) = 1 := by
  have := apply_inl_add_apply_inr σ
  rwa [h, zero_add] at this

/-- If `σ (0, 1) = 0`, then `σ (1, 0) = 1`. -/
theorem apply_inl_eq_one_of_apply_inr_eq_zero (h : σ (0, 1) = 0) : σ (1, 0) = 1 := by
  have := apply_inl_add_apply_inr σ
  rwa [h, add_zero] at this

end Ring

section CompFst

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A) (h : σ (1, 0) = 1)

/-- The algebra homomorphism `C →ₐ[R] A`, `c ↦ σ (c, 0)`, available when `σ (1, 0) = 1`. -/
def compFstSection : C →ₐ[R] A where
  toFun c := σ (c, 0)
  map_one' := h
  map_mul' x y := by
    change σ (x * y, 0) = σ (x, 0) * σ (y, 0)
    rw [← map_mul]
    congr 1
    ext <;> simp
  map_zero' := map_zero σ
  map_add' x y := by
    change σ (x + y, 0) = σ (x, 0) + σ (y, 0)
    rw [← map_add]
    congr 1
    ext <;> simp
  commutes' r := by
    have key : ((algebraMap R C r, (0 : E)) : C × E) = algebraMap R (C × E) r * (1, 0) := by
      ext <;> simp
    change σ _ = _
    rw [key, map_mul, σ.commutes, h, mul_one]

@[simp]
theorem compFstSection_apply (c : C) : compFstSection σ h c = σ (c, 0) := rfl

end CompFst

section CompSnd

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A) (h : σ (0, 1) = 1)

/-- The algebra homomorphism `E →ₐ[R] A`, `e ↦ σ (0, e)`, available when `σ (0, 1) = 1`. -/
def compSndSection : E →ₐ[R] A where
  toFun e := σ (0, e)
  map_one' := h
  map_mul' x y := by
    change σ (0, x * y) = σ (0, x) * σ (0, y)
    rw [← map_mul]
    congr 1
    ext <;> simp
  map_zero' := map_zero σ
  map_add' x y := by
    change σ (0, x + y) = σ (0, x) + σ (0, y)
    rw [← map_add]
    congr 1
    ext <;> simp
  commutes' r := by
    have key : (((0 : C), algebraMap R E r) : C × E) = algebraMap R (C × E) r * (0, 1) := by
      ext <;> simp
    change σ _ = _
    rw [key, map_mul, σ.commutes, h, mul_one]

@[simp]
theorem compSndSection_apply (e : E) : compSndSection σ h e = σ (0, e) := rfl

end CompSnd

section LocalRing

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommRing R] [CommRing A] [IsLocalRing A] [Ring C] [Ring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]

/-- In a local ring target, the idempotent `σ (1, 0)` is forced to be `0` or `1`. -/
theorem apply_inl_eq_zero_or_one (σ : C × E →ₐ[R] A) :
    σ (1, 0) = 0 ∨ σ (1, 0) = 1 :=
  (isIdempotentElem_apply_inl σ).eq_zero_or_one_of_isLocalRing

/-- In a local ring target, the idempotent `σ (0, 1)` is forced to be `0` or `1`. -/
theorem apply_inr_eq_zero_or_one (σ : C × E →ₐ[R] A) :
    σ (0, 1) = 0 ∨ σ (0, 1) = 1 :=
  (isIdempotentElem_apply_inr σ).eq_zero_or_one_of_isLocalRing

/-- Over a local ring target, every algebra homomorphism out of a binary product factors
through one of the two projections. -/
theorem exists_section_of_isLocalRing (σ : C × E →ₐ[R] A) :
    (∃ h : σ (1, 0) = 1, ∀ c e, σ (c, e) = compFstSection σ h c) ∨
    (∃ h : σ (0, 1) = 1, ∀ c e, σ (c, e) = compSndSection σ h e) := by
  have hdecomp (c : C) (e : E) : ((c, e) : C × E) = (c, 0) + (0, e) := by ext <;> simp
  rcases apply_inl_eq_zero_or_one σ with h0 | h1
  · refine .inr ⟨apply_inr_eq_one_of_apply_inl_eq_zero σ h0, fun c e ↦ ?_⟩
    have hc0 : σ (c, 0) = 0 := by
      have : ((c, (0 : E)) : C × E) = (c, 1) * (1, 0) := by ext <;> simp
      rw [this, map_mul, h0, mul_zero]
    change σ (c, e) = σ (0, e)
    rw [hdecomp, map_add, hc0, zero_add]
  · refine .inl ⟨h1, fun c e ↦ ?_⟩
    have he0 : σ (0, e) = 0 := by
      have : (((0 : C), e) : C × E) = (1, e) * (0, 1) := by ext <;> simp
      rw [this, map_mul, apply_inr_eq_zero_of_apply_inl_eq_one σ h1, mul_zero]
    change σ (c, e) = σ (c, 0)
    rw [hdecomp, map_add, he0, add_zero]

end LocalRing

end AlgHom
