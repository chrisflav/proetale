/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.EulerProductAux

/-!
# Analytic evaluation of products of geometric series

This file proves the analytic counterpart of the formal Euler product computations of
`Proetale.WeilConjectures.EulerProductAux`: for a family of exponents `d : ι → ℕ` with
`d i ≠ 0` such that `{i | d i ≤ n}` is finite for every `n`, and a complex number `z`
with `‖z‖ < 1` such that `∑ ‖z‖ ^ d i` converges, the infinite product
`∏ (1 - z ^ d i)⁻¹` converges in `ℂ` and equals the evaluation at `z` of the formal
infinite product `∏ (1 - X ^ d i)⁻¹ ∈ ℚ⟦X⟧`, i.e. the convergent power series
`∑ cₙ zⁿ` where `cₙ` are the coefficients of the formal product.

The proof proceeds by exact finite-level identities (finite products of geometric series
evaluate via Cauchy products, matching `PowerSeries.coeff_mul` termwise), together with
nonnegativity and monotonicity of the coefficients in the index set, an exponential
bound for the dominating series, and dominated convergence along the net of finite
subsets.
-/

namespace PowerSeries

variable {ι : Type*} {d : ι → ℕ} {z : ℂ}

/-- The geometric series `(1 - X ^ k)⁻¹` evaluates at `z` with `‖z‖ < 1` to
`(1 - z ^ k)⁻¹`. -/
private theorem hasSum_coeff_inv_one_sub_X_pow (hz : ‖z‖ < 1) {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n ↦ ((coeff n ((1 - X ^ k)⁻¹ : ℚ⟦X⟧) : ℚ) : ℂ) * z ^ n)
      (1 - z ^ k)⁻¹ := by
  classical
  have hfun : (fun n : ℕ ↦ ((coeff n ((1 - X ^ k)⁻¹ : ℚ⟦X⟧) : ℚ) : ℂ) * z ^ n) =
      fun n : ℕ ↦ if k ∣ n then z ^ n else 0 := by
    funext n
    rw [inv_one_sub_X_pow_eq_mk hk, coeff_mk]
    split
    · rw [Rat.cast_one, one_mul]
    · rw [Rat.cast_zero, zero_mul]
  rw [hfun]
  have hza : ‖z ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) hz hk
  have hinj : Function.Injective (fun m : ℕ ↦ k * m) := fun m₁ m₂ h ↦
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h
  have h0 : ∀ n, n ∉ Set.range (fun m : ℕ ↦ k * m) →
      (if k ∣ n then z ^ n else 0) = 0 := by
    intro n hn
    refine if_neg ?_
    rintro ⟨m, hm⟩
    exact hn ⟨m, hm.symm⟩
  have hcomp : ((fun n : ℕ ↦ if k ∣ n then z ^ n else 0) ∘ fun m : ℕ ↦ k * m) =
      fun m : ℕ ↦ (z ^ k) ^ m := by
    funext m
    rw [Function.comp_apply, if_pos (dvd_mul_right k m), ← pow_mul]
  refine (hinj.hasSum_iff h0).mp ?_
  rw [hcomp]
  exact hasSum_geometric_of_norm_lt_one hza

/-- The evaluation of the geometric series `(1 - X ^ k)⁻¹` at `z` with `‖z‖ < 1` is
absolutely convergent. -/
private theorem summable_norm_coeff_inv_one_sub_X_pow (hz : ‖z‖ < 1) {k : ℕ}
    (hk : k ≠ 0) :
    Summable fun n ↦ ‖((coeff n ((1 - X ^ k)⁻¹ : ℚ⟦X⟧) : ℚ) : ℂ) * z ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
    (summable_geometric_of_lt_one (norm_nonneg z) hz)
  rw [inv_one_sub_X_pow_eq_mk hk, coeff_mk]
  split
  · rw [Rat.cast_one, one_mul, norm_pow]
  · rw [Rat.cast_zero, zero_mul, norm_zero]
    exact pow_nonneg (norm_nonneg z) n

private theorem summable_norm_and_hasSum_coeff_prod (hz : ‖z‖ < 1) (S : Finset ι)
    (hd : ∀ i ∈ S, d i ≠ 0) :
    (Summable fun n ↦
      ‖((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n‖) ∧
    HasSum (fun n ↦ ((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)
      (∏ i ∈ S, (1 - z ^ d i)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    constructor
    · refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) fun n hn ↦ ?_
      rw [if_neg (by simpa using hn), Rat.cast_zero, zero_mul, norm_zero]
    · have hfun : (fun n : ℕ ↦ ((if n = 0 then (1 : ℚ) else 0 : ℚ) : ℂ) * z ^ n) =
          fun n : ℕ ↦ if n = 0 then (1 : ℂ) else 0 := by
        funext n
        split
        · rename_i h
          rw [h, Rat.cast_one, one_mul, pow_zero]
        · rw [Rat.cast_zero, zero_mul]
      rw [hfun]
      exact hasSum_ite_eq 0 1
  | insert a S ha ih =>
    have hda : d a ≠ 0 := hd a (Finset.mem_insert_self a S)
    obtain ⟨ihn, ihs⟩ := ih fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)
    have hfa := hasSum_coeff_inv_one_sub_X_pow hz hda
    have hna := summable_norm_coeff_inv_one_sub_X_pow hz hda
    have hcoeff : ∀ n : ℕ,
        ((coeff n (∏ i ∈ insert a S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n =
        ∑ p ∈ Finset.antidiagonal n,
          ((coeff p.1 ((1 - X ^ d a)⁻¹ : ℚ⟦X⟧) : ℚ) : ℂ) * z ^ p.1 *
            (((coeff p.2 (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ p.2) := by
      intro n
      rw [Finset.prod_insert ha, coeff_mul, Rat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [Rat.cast_mul, ← hp, pow_add]
      ring
    have hnorm := summable_norm_sum_mul_antidiagonal_of_summable_norm hna ihn
    constructor
    · exact hnorm.congr fun n ↦ by rw [hcoeff n]
    · have hhs := (Summable.of_norm hnorm).hasSum
      have hval : ∑' n, ∑ p ∈ Finset.antidiagonal n,
            ((coeff p.1 ((1 - X ^ d a)⁻¹ : ℚ⟦X⟧) : ℚ) : ℂ) * z ^ p.1 *
              (((coeff p.2 (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ p.2) =
          (1 - z ^ d a)⁻¹ * ∏ i ∈ S, (1 - z ^ d i)⁻¹ := by
        rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna ihn,
          hfa.tsum_eq, ihs.tsum_eq]
      rw [hval] at hhs
      rw [Finset.prod_insert (f := fun i ↦ (1 - z ^ d i)⁻¹) ha]
      exact hhs.congr_fun hcoeff

/-- Finite products of geometric series evaluate absolutely convergently: the value of
the evaluation of `∏ i ∈ S, (1 - X ^ d i)⁻¹` at `z` with `‖z‖ < 1` is
`∏ i ∈ S, (1 - z ^ d i)⁻¹`. -/
theorem hasSum_coeff_prod_inv_one_sub_X_pow (hz : ‖z‖ < 1) (S : Finset ι)
    (hd : ∀ i ∈ S, d i ≠ 0) :
    HasSum (fun n ↦ ((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)
      (∏ i ∈ S, (1 - z ^ d i)⁻¹) :=
  (summable_norm_and_hasSum_coeff_prod hz S hd).2

/-- The coefficients of a finite product of geometric series are nonnegative. -/
theorem coeff_prod_inv_one_sub_X_pow_nonneg (S : Finset ι) (hd : ∀ i ∈ S, d i ≠ 0)
    (n : ℕ) :
    0 ≤ coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
  classical
  induction S using Finset.induction_on generalizing n with
  | empty =>
    rw [Finset.prod_empty, coeff_one]
    split
    · exact zero_le_one
    · exact le_refl 0
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, coeff_mul]
    refine Finset.sum_nonneg fun p _ ↦ mul_nonneg ?_
      (ih (fun i hi ↦ hd i (Finset.mem_insert_of_mem hi)) p.2)
    rw [inv_one_sub_X_pow_eq_mk (hd a (Finset.mem_insert_self a S)), coeff_mk]
    split
    · exact zero_le_one
    · exact le_refl 0

/-- The coefficients of a finite product of geometric series are monotone in the index
set. -/
theorem coeff_prod_inv_one_sub_X_pow_mono {T S : Finset ι} (hTS : T ⊆ S)
    (hd : ∀ i ∈ S, d i ≠ 0) (n : ℕ) :
    coeff n (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) ≤
      coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
  classical
  have hdT : ∀ i ∈ T, d i ≠ 0 := fun i hi ↦ hd i (hTS hi)
  have hdST : ∀ i ∈ S \ T, d i ≠ 0 := fun i hi ↦ hd i (Finset.sdiff_subset hi)
  have h0 : coeff 0 (∏ i ∈ S \ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_prod]
    exact Finset.prod_eq_one fun i hi ↦ constantCoeff_inv_one_sub_X_pow (hdST i hi)
  have hmem : ((0 : ℕ), n) ∈ Finset.antidiagonal n := by
    rw [Finset.mem_antidiagonal, zero_add]
  calc coeff n (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧))
      = coeff 0 (∏ i ∈ S \ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) *
        coeff n (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by rw [h0, one_mul]
    _ ≤ ∑ p ∈ Finset.antidiagonal n,
          coeff p.1 (∏ i ∈ S \ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) *
            coeff p.2 (∏ i ∈ T, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) :=
        Finset.single_le_sum (fun p _ ↦ mul_nonneg
          (coeff_prod_inv_one_sub_X_pow_nonneg _ hdST p.1)
          (coeff_prod_inv_one_sub_X_pow_nonneg _ hdT p.2)) hmem
    _ = coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
        rw [← coeff_mul, Finset.prod_sdiff hTS]

/-- Real version of `hasSum_coeff_prod_inv_one_sub_X_pow`, obtained by evaluating at the
real point `(r : ℂ)` and descending along `Complex.ofReal`. -/
private theorem hasSum_coeff_prod_inv_one_sub_X_pow_real {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (S : Finset ι) (hd : ∀ i ∈ S, d i ≠ 0) :
    HasSum (fun n ↦ ((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) * r ^ n)
      (∏ i ∈ S, (1 - r ^ d i)⁻¹) := by
  have hz : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_of_nonneg hr0]
  have h := hasSum_coeff_prod_inv_one_sub_X_pow hz S hd
  have hfun : (fun n : ℕ ↦
      ((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * (r : ℂ) ^ n) =
      fun n : ℕ ↦
        ((((coeff n (∏ i ∈ S, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) * r ^ n : ℝ) : ℂ) := by
    funext n
    norm_cast
  have hval : (∏ i ∈ S, (1 - (r : ℂ) ^ d i)⁻¹) =
      ((∏ i ∈ S, (1 - r ^ d i)⁻¹ : ℝ) : ℂ) := by
    norm_cast
  rw [hfun, hval] at h
  exact Complex.hasSum_ofReal.mp h

/-- Elementary exponential bound for a single geometric factor. -/
private theorem inv_one_sub_pow_le_exp {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {k : ℕ}
    (hk : k ≠ 0) : (1 - r ^ k)⁻¹ ≤ Real.exp (r ^ k / (1 - r)) := by
  have htr : r ^ k ≤ r := pow_le_of_le_one hr0 hr.le hk
  have h1t : 0 < 1 - r ^ k := by
    have : r ^ k < 1 := pow_lt_one₀ hr0 hr hk
    linarith
  have heq : (1 - r ^ k)⁻¹ = 1 + r ^ k / (1 - r ^ k) := by
    field_simp
    ring
  have hle : r ^ k / (1 - r ^ k) ≤ r ^ k / (1 - r) :=
    div_le_div_of_nonneg_left (pow_nonneg hr0 k) (by linarith) (by linarith)
  have hexp := Real.add_one_le_exp (r ^ k / (1 - r))
  rw [heq]
  linarith

/-- The `n`-th coefficient of any finite subproduct is at most the `n`-th coefficient of
the subproduct over all indices `i` with `d i ≤ n`. -/
private theorem coeff_prod_le_coeff_prod_toFinset (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) (s : Finset ι) (n : ℕ) :
    coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) ≤
      coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
  classical
  have h1 : coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      coeff n (∏ i ∈ s ∩ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
    refine coeff_prod_inv_one_sub_X_pow_congr Finset.inter_subset_left fun i hi hni ↦ ?_
    by_contra hle
    exact hni (Finset.mem_inter.mpr ⟨hi, (hfin n).mem_toFinset.mpr (not_lt.mp hle)⟩)
  rw [h1]
  exact coeff_prod_inv_one_sub_X_pow_mono Finset.inter_subset_right (fun i _ ↦ hd i) n

open WithPiTopology in
/-- **Analytic evaluation of the Euler product**: for a family of exponents `d i ≥ 1`
with only finitely many indices below any bound and `z` with `‖z‖ < 1` such that
`∑ ‖z‖ ^ d i < ∞`, the product `∏ (1 - z ^ d i)⁻¹` converges in `ℂ` to the value at
`z` of the formal power series `∏ (1 - X ^ d i)⁻¹ ∈ ℚ⟦X⟧`. -/
theorem hasProd_inv_one_sub_pow (hd : ∀ i, d i ≠ 0) (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hz : ‖z‖ < 1) (hsum : Summable fun i ↦ ‖z‖ ^ d i) :
    HasProd (fun i ↦ (1 - z ^ d i)⁻¹)
      (∑' n : ℕ, ((coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n) := by
  classical
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1r : 0 < 1 - ‖z‖ := by linarith
  -- uniform exponential bound for the real subproducts
  have hprod_le : ∀ T : Finset ι, ∏ i ∈ T, (1 - ‖z‖ ^ d i)⁻¹ ≤
      Real.exp ((∑' i, ‖z‖ ^ d i) / (1 - ‖z‖)) := by
    intro T
    calc ∏ i ∈ T, (1 - ‖z‖ ^ d i)⁻¹
        ≤ ∏ i ∈ T, Real.exp (‖z‖ ^ d i / (1 - ‖z‖)) :=
          Finset.prod_le_prod
            (fun i _ ↦ inv_nonneg.mpr (by
              have := pow_lt_one₀ hz0 hz (hd i)
              linarith))
            (fun i _ ↦ inv_one_sub_pow_le_exp hz0 hz (hd i))
      _ = Real.exp (∑ i ∈ T, ‖z‖ ^ d i / (1 - ‖z‖)) := (Real.exp_sum T _).symm
      _ ≤ Real.exp ((∑' i, ‖z‖ ^ d i) / (1 - ‖z‖)) := by
          rw [Real.exp_le_exp, ← Finset.sum_div]
          exact div_le_div_of_nonneg_right
            (hsum.sum_le_tsum T fun i _ ↦ pow_nonneg hz0 _) h1r.le
  -- summability of the dominating series
  have hbound_nonneg : ∀ n : ℕ, 0 ≤
      ((coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
        ‖z‖ ^ n := by
    intro n
    refine mul_nonneg ?_ (pow_nonneg hz0 n)
    exact_mod_cast coeff_prod_inv_one_sub_X_pow_nonneg _ (fun i _ ↦ hd i) n
  have hbound_summable : Summable fun n : ℕ ↦
      ((coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
        ‖z‖ ^ n := by
    refine summable_of_sum_range_le
      (c := Real.exp ((∑' i, ‖z‖ ^ d i) / (1 - ‖z‖))) hbound_nonneg fun m ↦ ?_
    have hreal := hasSum_coeff_prod_inv_one_sub_X_pow_real hz0 hz
      (hfin m).toFinset (fun i _ ↦ hd i)
    have hle1 : ∀ n ∈ Finset.range m,
        ((coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
          ‖z‖ ^ n ≤
        ((coeff n (∏ i ∈ (hfin m).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
          ‖z‖ ^ n := by
      intro n hn
      rw [Finset.mem_range] at hn
      have hsub : (hfin n).toFinset ⊆ (hfin m).toFinset := by
        intro i hi
        rw [Set.Finite.mem_toFinset] at hi ⊢
        exact le_trans hi hn.le
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hz0 n)
      exact_mod_cast coeff_prod_inv_one_sub_X_pow_mono hsub (fun i _ ↦ hd i) n
    calc ∑ n ∈ Finset.range m,
          ((coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
            ‖z‖ ^ n
        ≤ ∑ n ∈ Finset.range m,
            ((coeff n (∏ i ∈ (hfin m).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
              ‖z‖ ^ n := Finset.sum_le_sum hle1
      _ ≤ ∑' n : ℕ,
            ((coeff n (∏ i ∈ (hfin m).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
              ‖z‖ ^ n :=
          hreal.summable.sum_le_tsum _ fun n _ ↦ mul_nonneg
            (by exact_mod_cast coeff_prod_inv_one_sub_X_pow_nonneg _ (fun i _ ↦ hd i) n)
            (pow_nonneg hz0 n)
      _ = ∏ i ∈ (hfin m).toFinset, (1 - ‖z‖ ^ d i)⁻¹ := hreal.tsum_eq
      _ ≤ Real.exp ((∑' i, ‖z‖ ^ d i) / (1 - ‖z‖)) := hprod_le _
  -- pointwise convergence of the coefficients along the net of finite sets
  have hcoeff_tprod : ∀ n : ℕ, coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
      coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := fun n ↦
    coeff_tprod_inv_one_sub_X_pow hd hfin n fun i hi ↦ (hfin n).mem_toFinset.mpr hi
  have hcongr : ∀ (n : ℕ) (s : Finset ι), (hfin n).toFinset ⊆ s →
      coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) =
        coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) := by
    intro n s hs
    refine coeff_prod_inv_one_sub_X_pow_congr hs fun i _ hni ↦ ?_
    by_contra hle
    exact hni ((hfin n).mem_toFinset.mpr (not_lt.mp hle))
  have hab : ∀ n : ℕ, Filter.Tendsto
      (fun s : Finset ι ↦
        ((coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)
      Filter.atTop
      (nhds (((coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)) := by
    intro n
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (hfin n).toFinset] with s hs
    rw [hcoeff_tprod n, hcongr n s hs]
  -- domination
  have h_bound : ∀ (s : Finset ι) (n : ℕ),
      ‖((coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n‖ ≤
        ((coeff n (∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℝ) *
          ‖z‖ ^ n := by
    intro s n
    rw [norm_mul, norm_pow, Complex.norm_ratCast, abs_of_nonneg (by
      exact_mod_cast coeff_prod_inv_one_sub_X_pow_nonneg s (fun i _ ↦ hd i) n)]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hz0 n)
    exact_mod_cast coeff_prod_le_coeff_prod_toFinset hd hfin s n
  -- Tannery's theorem and conclusion
  have htan := tendsto_tsum_of_dominated_convergence
    (f := fun (s : Finset ι) (n : ℕ) ↦
      ((coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)
    (g := fun n : ℕ ↦ ((coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n)
    hbound_summable hab (Filter.Eventually.of_forall h_bound)
  have hfin_eq : ∀ s : Finset ι,
      ∑' n : ℕ, ((coeff n (∏ i ∈ s, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) : ℚ) : ℂ) * z ^ n =
        ∏ i ∈ s, (1 - z ^ d i)⁻¹ := fun s ↦
    (hasSum_coeff_prod_inv_one_sub_X_pow hz s fun i _ ↦ hd i).tsum_eq
  exact htan.congr hfin_eq

end PowerSeries
