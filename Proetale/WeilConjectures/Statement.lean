/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaSeries

/-!
# The Weil conjectures

Let `X` be a smooth, proper, geometrically integral scheme of dimension `d` over a finite
field `k` with `q` elements and let `Z(X, t) ∈ ℚ⟦t⟧` be its zeta function
(`AlgebraicGeometry.Scheme.zetaSeries`). The Weil conjectures [weil1949] assert:

1. *Rationality* (Dwork, 1960): `Z(X, t)` is a rational function. More precisely
   `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` for polynomials `Pᵢ ∈ ℤ[t]` with
   `Pᵢ(0) = 1`, `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`, the odd-indexed ones in the
   numerator and the even-indexed ones in the denominator. Rationality alone holds for
   arbitrary schemes of finite type over `k`, see `zetaSeries_rational`.
2. *Functional equation* (Grothendieck, 1965): `Z(X, 1 / (qᵈ t)) = ± q^{dχ/2} tᵡ Z(X, t)`
   where `χ = ∑ (-1)ⁱ deg Pᵢ`. Equivalently — and this is how we state it — the map
   `α ↦ qᵈ / α` sends the inverse roots of `Pᵢ` bijectively (with multiplicity) to the
   inverse roots of `P_{2d - i}`.
3. *Riemann hypothesis* (Deligne, 1974): the inverse roots of `Pᵢ` are algebraic numbers
   of absolute value `q^{i/2}` under every complex embedding. Since each `Pᵢ` has integer
   coefficients and constant coefficient `1`, its inverse roots are automatically
   algebraic integers, so we only need to constrain the norms of its complex roots.

We state the three conjectures in terms of the complex roots of the `Pᵢ`: a root `z` of
`Pᵢ` is the inverse of an inverse root `α`, so the Riemann hypothesis reads
`‖z‖ = q^{-i/2}` and the functional equation says that `z ↦ 1 / (qᵈ z)` maps the root
multiset of `Pᵢ` to that of `P_{2d - i}`.

Weil's fourth conjecture — if `X` lifts to a smooth proper scheme over a number ring, then
`deg Pᵢ` is the `i`-th Betti number of the associated complex manifold — needs singular
cohomology of the analytification and is not stated here. In the Grothendieck-Deligne
proof `deg Pᵢ` is the `ℚ_ℓ`-dimension of the `i`-th étale cohomology of the base change of
`X` to an algebraic closure of `k`; compare `Scheme.EllAdicCohomology` and
the `Comparator` library of this repository.

## Main statements

- `AlgebraicGeometry.IsWeilFactorization`: the factorization of `Z(X, t)` predicted by
  the rationality conjecture.
- `AlgebraicGeometry.WeilFunctionalEquation`: the functional equation, as a
  correspondence of root multisets.
- `AlgebraicGeometry.WeilRiemannHypothesis`: the Riemann hypothesis for the roots.
- `AlgebraicGeometry.Scheme.zetaSeries_rational`: rationality of `Z(X, t)` for arbitrary
  `X` of finite type over `k` (Dwork's theorem).
- `AlgebraicGeometry.Scheme.weil_conjectures`: the Weil conjectures for a smooth, proper,
  geometrically integral scheme over a finite field.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
-/

universe u

open Polynomial

namespace AlgebraicGeometry

/-- `IsWeilFactorization q d Z P` says that the polynomials `P₀, …, P_{2d} ∈ ℤ[t]`
factor the power series `Z` as `Z = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})`, normalized by
`Pᵢ(0) = 1`, with `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`. This is the shape of the zeta
function of a smooth, proper, geometrically integral scheme of dimension `d` over a field
with `q` elements predicted by the Weil conjectures. -/
structure IsWeilFactorization (q d : ℕ) (Z : PowerSeries ℚ)
    (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop where
  coeff_zero_eq_one : ∀ i, (P i).coeff 0 = 1
  apply_zero : P 0 = 1 - Polynomial.X
  apply_last : P (Fin.last (2 * d)) = 1 - Polynomial.C ((q : ℤ) ^ d) * Polynomial.X
  factorization : Z * ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) =
    ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
      ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)

/-- The functional equation part of the Weil conjectures: `α ↦ qᵈ / α` maps the inverse
roots of `Pᵢ` bijectively (with multiplicity) to the inverse roots of `P_{2d - i}`.
In terms of the complex roots `z = 1 / α` this says that `z ↦ 1 / (qᵈ z)` identifies the
root multisets of `Pᵢ` and `P_{2d - i}`. It implies the classical functional equation
`Z(X, 1 / (qᵈ t)) = ± q^{dχ/2} tᵡ Z(X, t)` for the associated rational function. -/
def WeilFunctionalEquation (q d : ℕ) (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop :=
  ∀ i, ((P i.rev).map (Int.castRingHom ℂ)).roots =
    (((P i).map (Int.castRingHom ℂ)).roots.map fun z ↦ ((q : ℂ) ^ d * z)⁻¹)

/-- The Riemann hypothesis part of the Weil conjectures: every inverse root of `Pᵢ` has
absolute value `q^{i/2}`, i.e. every complex root `z` of `Pᵢ` satisfies `‖z‖ = q^{-i/2}`. -/
def WeilRiemannHypothesis (q d : ℕ) (P : Fin (2 * d + 1) → Polynomial ℤ) : Prop :=
  ∀ i : Fin (2 * d + 1), ∀ z ∈ ((P i).map (Int.castRingHom ℂ)).roots,
    ‖z‖ = (q : ℝ) ^ (-(i.1 : ℝ) / 2)

namespace Scheme

variable {k : Type u} [Field k] [Finite k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Dwork's theorem**: the zeta function of a scheme of finite type over a finite field
is a rational function with integer coefficients. This is the first Weil conjecture, which
holds without any smoothness or properness hypotheses. -/
theorem zetaSeries_rational [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  sorry

/-- **The Weil conjectures** (Dwork, Grothendieck, Deligne): the zeta function of a
smooth, proper, geometrically integral scheme `X` of dimension `d` over a finite field
`k` with `q` elements factors as `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` with
`Pᵢ ∈ ℤ[t]`, `Pᵢ(0) = 1`, `P₀ = 1 - t`, `P_{2d} = 1 - qᵈ t`, satisfying the functional
equation and the Riemann hypothesis: all inverse roots of `Pᵢ` have absolute value
`q^{i/2}`, and `α ↦ qᵈ / α` matches the inverse roots of `Pᵢ` with those of `P_{2d-i}`. -/
theorem weil_conjectures (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [GeometricallyIntegral f] :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k) d P ∧
      WeilRiemannHypothesis (Nat.card k) d P :=
  sorry

end Scheme

end AlgebraicGeometry
