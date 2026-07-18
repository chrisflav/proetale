/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaFunction

/-!
# The zeta function of a scheme over a finite field

For a scheme `X` over a finite field `k` with `q` elements, the zeta function of `X` is
traditionally packaged as the formal power series

`Z(X, t) = exp (∑ N_n * t ^ n / n)`,

where `N_n` is the number of points of `X` with values in the degree `n` extension of `k`.
It is related to the zeta function `ζ_X` of `Proetale.WeilConjectures.ZetaFunction` by the
formal substitution `ζ_X(s) = Z(X, q ^ (-s))`.

## Main definitions

- `FiniteField.galoisExtension k n`: a model of the degree `n` extension of the finite
  field `k`, as the splitting field of `X ^ (#k ^ n) - X`.
- `AlgebraicGeometry.Scheme.fieldPoints`: the `K`-rational points of a scheme over `k`.
- `AlgebraicGeometry.Scheme.pointCount`: the number `N_n` of points of `X` rational over
  the degree `n` extension of `k`.
- `AlgebraicGeometry.Scheme.zetaSeries`: the power series `Z(X, t) ∈ ℚ⟦t⟧`.
- `AlgebraicGeometry.Scheme.degreeOver`: the degree `[κ(x) : k]` of a point.

## Main statements

- `AlgebraicGeometry.Scheme.X_mul_derivative_zetaSeries`: the logarithmic derivative of
  `Z(X, t)` is the generating series of the point counts, i.e.
  `t * Z'(X, t) = (∑ N_n t ^ n) * Z(X, t)`. Together with `constantCoeff_zetaSeries` this
  characterizes `Z(X, t)` uniquely.
- `AlgebraicGeometry.Scheme.zetaSeries_eq_tprod`: the Euler product expansion
  `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹` over the closed points of `X`, converging in the
  `t`-adic sense.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial

namespace FiniteField

/-- A model for the degree `n` extension of a finite field `k` with `q` elements:
the splitting field of `X ^ (q ^ n) - X` over `k`. For infinite `k` this is junk
(the polynomial degenerates), as is the value for `n = 0`. -/
def galoisExtension (k : Type u) [Field k] (n : ℕ) : Type u :=
  (Polynomial.X ^ Nat.card k ^ n - Polynomial.X : Polynomial k).SplittingField

variable (k : Type u) [Field k] (n : ℕ)

noncomputable instance : Field (galoisExtension k n) :=
  inferInstanceAs (Field (Polynomial.SplittingField _))

noncomputable instance : Algebra k (galoisExtension k n) :=
  inferInstanceAs (Algebra k (Polynomial.SplittingField _))

/-- The degree `n` extension of a finite field `k` has `#k ^ n` elements. -/
theorem nat_card_galoisExtension [Finite k] (hn : n ≠ 0) :
    Nat.card (galoisExtension k n) = Nat.card k ^ n :=
  sorry

/-- The degree `n` extension of a finite field `k` has degree `n` over `k`. -/
theorem finrank_galoisExtension [Finite k] (hn : n ≠ 0) :
    Module.finrank k (galoisExtension k n) = n :=
  sorry

end FiniteField

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (K : Type u) [Field K] [Algebra k K]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The `K`-rational points `X(K)` of a scheme `X` over a field `k`, for a field extension
`K` of `k`: morphisms `Spec K ⟶ X` commuting with the structure morphisms to `Spec k`. -/
def fieldPoints : Type u :=
  {f : Spec (.of K) ⟶ X // f ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k K))}

/-- The number of rational points is invariant under isomorphisms of the coefficient
field extension. In particular, over a finite field the point counts `N_n` do not depend
on the chosen model of the degree `n` extension. -/
theorem nat_card_fieldPoints_congr {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] (e : K ≃ₐ[k] L) :
    Nat.card (X.fieldPoints k K) = Nat.card (X.fieldPoints k L) :=
  sorry

/-- `X.pointCount k n` is the number `N_n` of points of `X` which are rational over the
degree `n` extension of `k`, with junk value `0` if this number is infinite. -/
noncomputable def pointCount (n : ℕ) : ℕ :=
  Nat.card (X.fieldPoints k (FiniteField.galoisExtension k n))

/-- The zeta function of a scheme `X` over a finite field `k` with `q` elements, as a
formal power series: `Z(X, t) = exp (∑ N_n * t ^ n / n)` where `N_n = #X(𝔽_(q ^ n))`.

It is related to the zeta function `ζ_X` of `X` as an abstract scheme by the formal
identity `ζ_X(s) = Z(X, q ^ (-s))`, see `zetaSeries_eq_tprod`. -/
noncomputable def zetaSeries : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    (PowerSeries.mk fun n ↦ if n = 0 then 0 else (X.pointCount k n : ℚ) / n)

theorem constantCoeff_zetaSeries : PowerSeries.constantCoeff (X.zetaSeries k) = 1 :=
  sorry

/-- The logarithmic derivative of the zeta function of `X` over `k` is the generating
function of the point counts of `X`: `t * Z'(X, t) = (∑ N_n * t ^ n) * Z(X, t)`. -/
theorem X_mul_derivative_zetaSeries :
    PowerSeries.X * PowerSeries.derivative ℚ (X.zetaSeries k) =
      PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else X.pointCount k n) *
        X.zetaSeries k :=
  sorry

/-- The canonical embedding of the base field of `X` into the residue field of a point,
obtained by evaluating global sections. -/
noncomputable def residueFieldAlgebraMap (x : X) : k →+* X.residueField x :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
    X.evaluation ⊤ x trivial).hom

/-- The degree `[κ(x) : k]` of a point `x` of a scheme `X` over a field `k`, with junk
value `0` if the residue field extension is infinite. -/
noncomputable def degreeOver (x : X) : ℕ :=
  letI := (X.residueFieldAlgebraMap k x).toAlgebra
  Module.finrank k (X.residueField x)

open scoped PowerSeries.WithPiTopology in
/-- The Euler product expansion of the zeta function of a variety over a finite field:
`Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`, the product running over the closed points of `X` and
converging coefficientwise (there are only finitely many closed points of each degree).

Substituting `t = q ^ (-s)` and comparing factors with `#κ(x) = q ^ deg x` shows that
this is the Euler product defining `Scheme.zeta`. -/
theorem zetaSeries_eq_tprod [Finite k] [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    X.zetaSeries k =
      ∏' x : X.finitePoints, (1 - PowerSeries.X ^ X.degreeOver k x.1 : PowerSeries ℚ)⁻¹ :=
  sorry

end AlgebraicGeometry.Scheme
