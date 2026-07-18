/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.EulerProductAux
import Proetale.WeilConjectures.PointCount

/-!
# The Euler product expansion of the zeta function

For a scheme `X` of finite type over a finite field `k`, given by a structure morphism
`f : X ⟶ Spec k`, we prove the Euler product expansion of its zeta function:

`Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`,

the product running over the closed points of `X` and converging coefficientwise (there
are only finitely many closed points of each degree by
`AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`).

The proof compares logarithmic derivatives: by
`AlgebraicGeometry.Scheme.Hom.X_mul_derivative_zetaSeries` and the point counting formula
`AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum`, both sides satisfy differential
equations `X * F' = A * F` whose right hand sides agree up to any given order, and both
sides have constant coefficient `1`; the coefficient recursion determined by such an
equation then forces the coefficients to agree.

Substituting `t = q ^ (-s)` and comparing factors with `#κ(x) = q ^ deg x` shows that
this is the Euler product defining the zeta function `AlgebraicGeometry.Scheme.zeta` of
`X` as an abstract scheme.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

open scoped PowerSeries.WithPiTopology in
/-- **The Euler product expansion** of the zeta function of a scheme of finite type over
a finite field: `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`, the product running over the closed
points of `X` and converging coefficientwise. -/
theorem Hom.zetaSeries_eq_tprod [Finite k] (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] :
    f.zetaSeries =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ := by
  classical
  have hd : ∀ x : X.finitePoints, f.degreeOver x.1 ≠ 0 := fun x ↦ f.degreeOver_ne_zero x.2
  have hfin : ∀ n, {x : X.finitePoints | f.degreeOver x.1 ≤ n}.Finite :=
    f.finite_setOf_degreeOver_le
  ext n
  set T : Finset X.finitePoints := (hfin n).toFinset with hT_def
  have hT : ∀ x : X.finitePoints, f.degreeOver x.1 ≤ n → x ∈ T := fun x hx ↦ by
    simpa [hT_def] using hx
  rw [PowerSeries.coeff_tprod_inv_one_sub_X_pow hd hfin n hT]
  refine PowerSeries.coeff_eq_of_X_mul_derivative_eq f.X_mul_derivative_zetaSeries
    (PowerSeries.X_mul_derivative_prod_inv_one_sub_X_pow _ T fun i _ ↦ hd i)
    ?_ (by simp) ?_ n le_rfl
  · rw [f.constantCoeff_zetaSeries, map_prod]
    exact (Finset.prod_eq_one fun x _ ↦
      PowerSeries.constantCoeff_inv_one_sub_X_pow (hd x)).symm
  · intro i hi
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    · rw [PowerSeries.coeff_mk, if_neg hi0, map_sum]
      simp only [PowerSeries.coeff_mk]
      rw [f.pointCount_eq_sum hi0 (T := T)
        fun x hx ↦ hT x ((Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hx).trans hi)]
      rw [Finset.sum_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by simp [hi0]

end AlgebraicGeometry.Scheme
