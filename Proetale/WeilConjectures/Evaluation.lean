/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.AnalyticAux
import Proetale.WeilConjectures.EulerProduct

/-!
# The zeta function is the evaluation of the zeta series

For a scheme `X` of finite type over a finite field `k` with `q` elements, given by a
structure morphism `f : X ⟶ Spec k`, we prove Serre's identity

`ζ_X(s) = Z(X, q ^ (-s))`,

where `ζ_X` is the zeta function of `X` as an abstract scheme
(`AlgebraicGeometry.Scheme.zeta`, an Euler product over the points with finite residue
field) and `Z(X, t)` is the zeta series of `X` over `k`
(`AlgebraicGeometry.Scheme.Hom.zetaSeries`), evaluated at `t = q ^ (-s)` as a convergent
power series.

The identity holds under the correct convergence assumptions: `‖q ^ (-s)‖ < 1` and
summability of `∑ ‖q ^ (-s)‖ ^ deg x` over the closed points of `X` (which is precisely
absolute convergence of the Euler product; by a theorem of Serre both hold whenever
`re s > dim X`, but we take them as hypotheses). Both assumptions are necessary: for `X`
finite and nonempty the power series diverges at `‖q ^ (-s)‖ ≥ 1` while the Euler
product is a finite product.

The proof combines the formal Euler product `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`
(`Proetale.WeilConjectures.EulerProduct`) with its analytic counterpart
(`Proetale.WeilConjectures.AnalyticAux`), and the identity `#κ(x) = q ^ deg x` for the
norms of closed points.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.pointNorm_eq_pow_degreeOver`: `#κ(x) = q ^ deg x`.
- `AlgebraicGeometry.Scheme.Hom.zeta_eq_tsum_coeff_zetaSeries`: `ζ_X(s) = Z(X, q^(-s))`.
- `AlgebraicGeometry.Scheme.Hom.multipliable_eulerFactor`: the Euler product defining
  `ζ_X` converges under the same assumptions.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The norm of a point of a scheme over a finite field `k` with `q` elements is
`q ^ deg x`. -/
theorem Hom.pointNorm_eq_pow_degreeOver [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) :
    X.pointNorm x = Nat.card k ^ f.degreeOver x := by
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  haveI : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  haveI : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  unfold Scheme.pointNorm Hom.degreeOver
  exact Module.natCard_eq_pow_finrank

/-- The Euler factor of the zeta function at a point of degree `d` over `k` is the
geometric factor `(1 - (q ^ (-s)) ^ d)⁻¹`. -/
theorem Hom.eulerFactor_eq [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) (s : ℂ) :
    X.eulerFactor x s = (1 - ((Nat.card k : ℂ) ^ (-s)) ^ f.degreeOver x)⁻¹ := by
  unfold Scheme.eulerFactor
  rw [f.pointNorm_eq_pow_degreeOver hx, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- **The zeta function of a variety over a finite field is the evaluation of its zeta
series**: `ζ_X(s) = Z(X, q ^ (-s))`, for `X` of finite type over a finite field `k` with
`q` elements, whenever `‖q ^ (-s)‖ < 1` and the Euler product converges absolutely.
The right hand side is the evaluation of the power series `Z(X, t)` at `t = q ^ (-s)`. -/
theorem Hom.zeta_eq_tsum_coeff_zetaSeries [Finite k] (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] {s : ℂ}
    (hz : ‖(Nat.card k : ℂ) ^ (-s)‖ < 1)
    (hsum : Summable fun x : X.finitePoints ↦ ‖(Nat.card k : ℂ) ^ (-s)‖ ^ f.degreeOver x.1) :
    X.zeta s =
      ∑' n : ℕ, ((PowerSeries.coeff n f.zetaSeries : ℚ) : ℂ) * ((Nat.card k : ℂ) ^ (-s)) ^ n := by
  have hd : ∀ x : X.finitePoints, f.degreeOver x.1 ≠ 0 := fun x ↦ f.degreeOver_ne_zero x.2
  have hP := PowerSeries.hasProd_inv_one_sub_pow
    (d := fun x : X.finitePoints ↦ f.degreeOver x.1) hd f.finite_setOf_degreeOver_le hz hsum
  rw [← f.zetaSeries_eq_tprod] at hP
  have h1 : X.zeta s =
      ∏' x : X.finitePoints, (1 - ((Nat.card k : ℂ) ^ (-s)) ^ f.degreeOver x.1)⁻¹ :=
    tprod_congr fun x ↦ f.eulerFactor_eq x.2 s
  rw [h1]
  exact hP.tprod_eq

/-- Under the assumptions of `zeta_eq_tsum_coeff_zetaSeries`, the Euler product defining
the zeta function of `X` converges. -/
theorem Hom.multipliable_eulerFactor [Finite k] (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] {s : ℂ}
    (hz : ‖(Nat.card k : ℂ) ^ (-s)‖ < 1)
    (hsum : Summable fun x : X.finitePoints ↦ ‖(Nat.card k : ℂ) ^ (-s)‖ ^ f.degreeOver x.1) :
    Multipliable fun x : X.finitePoints ↦ X.eulerFactor x.1 s := by
  have hd : ∀ x : X.finitePoints, f.degreeOver x.1 ≠ 0 := fun x ↦ f.degreeOver_ne_zero x.2
  have hP := PowerSeries.hasProd_inv_one_sub_pow
    (d := fun x : X.finitePoints ↦ f.degreeOver x.1) hd f.finite_setOf_degreeOver_le hz hsum
  exact hP.multipliable.congr fun x ↦ (f.eulerFactor_eq x.2 s).symm

end AlgebraicGeometry.Scheme
