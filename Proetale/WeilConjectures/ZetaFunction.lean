/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The zeta function of a scheme

In this file we define the (Hasse-Weil) zeta function of an arbitrary scheme `X` in
maximal generality: it is the Euler product

`ζ_X(s) = ∏ (1 - #κ(x) ^ (-s))⁻¹`

taken over all points `x : X` whose residue field `κ(x)` is finite. The product is
interpreted as an unconditional infinite product (`tprod`), which takes the junk value `1`
whenever the family is not multipliable, so no convergence or finiteness hypotheses on `X`
are needed for the definition.

Every point with finite residue field is a closed point of every affine open containing it
(a finite integral domain is a field), hence a closed point of `X`. Conversely, if `X` is
locally of finite type over `Spec ℤ`, every closed point of `X` has finite residue field by
the general Nullstellensatz. Hence for such `X` (e.g. any variety over a finite field, or
any arithmetic scheme) the product ranges exactly over the closed points of `X` and recovers
the classical arithmetic zeta function; in this case it converges for `re s` large.

## Main definitions

- `AlgebraicGeometry.Scheme.finitePoints`: the points of `X` with finite residue field.
- `AlgebraicGeometry.Scheme.pointNorm`: the norm `N(x) = #κ(x)` of a point.
- `AlgebraicGeometry.Scheme.eulerFactor`: the local factor `(1 - N(x) ^ (-s))⁻¹`.
- `AlgebraicGeometry.Scheme.zeta`: the zeta function `ζ_X(s)` of a scheme `X`.

## Main statements

- `AlgebraicGeometry.Scheme.multipliable_eulerFactor_of_finiteType`: for a scheme of finite
  type over `ℤ`, the Euler product converges on a right half-plane.
- `AlgebraicGeometry.Scheme.zeta_specInt_eq_riemannZeta`: the zeta function of `Spec ℤ`
  is the Riemann zeta function.

## References

- [J.-P. Serre, *Zeta and L functions*][serre1965]
-/

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The points of a scheme with finite residue field. Any such point is closed in every
affine open containing it, hence closed in `X`. If `X` is locally of finite type over `ℤ`,
these are exactly the closed points of `X` (see `finitePoints_eq_closedPoints`). -/
def finitePoints : Set X :=
  {x | Finite (X.residueField x)}

lemma mem_finitePoints {x : X} : x ∈ X.finitePoints ↔ Finite (X.residueField x) :=
  Iff.rfl

/-- A point with finite residue field is a closed point. -/
lemma isClosed_singleton_of_mem_finitePoints {x : X} (hx : x ∈ X.finitePoints) :
    IsClosed ({x} : Set X) :=
  sorry

/-- If `X` is locally of finite type over `ℤ`, the points with finite residue field are
exactly the closed points. This is a consequence of the general Nullstellensatz. -/
theorem finitePoints_eq_closedPoints (f : X ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType f] :
    X.finitePoints = {x | IsClosed ({x} : Set X)} :=
  sorry

/-- The norm of a point `x` of a scheme is the cardinality of its residue field,
with junk value `0` if the residue field is infinite. -/
noncomputable def pointNorm (x : X) : ℕ :=
  Nat.card (X.residueField x)

lemma pointNorm_pos {x : X} (hx : x ∈ X.finitePoints) : 0 < X.pointNorm x :=
  have : Finite (X.residueField x) := hx
  Nat.card_pos

lemma one_lt_pointNorm {x : X} (hx : x ∈ X.finitePoints) : 1 < X.pointNorm x :=
  have : Finite (X.residueField x) := hx
  Finite.one_lt_card

/-- The Euler factor `(1 - N(x) ^ (-s))⁻¹` of the zeta function of `X` at a point `x`. -/
noncomputable def eulerFactor (x : X) (s : ℂ) : ℂ :=
  (1 - (X.pointNorm x : ℂ) ^ (-s))⁻¹

/-- The (Hasse-Weil) zeta function of an arbitrary scheme `X`: the Euler product
`ζ_X(s) = ∏ (1 - #κ(x) ^ (-s))⁻¹` over all points `x` of `X` with finite residue field.

The product is an unconditional infinite product (`tprod`) and takes the junk value `1`
if the family of Euler factors is not multipliable. For `X` of finite type over `ℤ` it
converges for `re s` sufficiently large (see `multipliable_eulerFactor_of_finiteType`),
and this definition recovers the classical arithmetic zeta function of `X`. -/
noncomputable def zeta (s : ℂ) : ℂ :=
  ∏' x : X.finitePoints, X.eulerFactor x.1 s

@[simp]
lemma zeta_of_isEmpty [IsEmpty X] (s : ℂ) : X.zeta s = 1 := by
  have : IsEmpty X.finitePoints := ⟨fun x ↦ IsEmpty.false x.1⟩
  rw [zeta, tprod_empty]

/-- For a scheme of finite type over `ℤ`, the Euler product defining the zeta function
converges on a right half-plane. (For `X` of dimension `d` one can take `a = d`, but we
do not state this.) -/
theorem multipliable_eulerFactor_of_finiteType (f : X ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Multipliable fun x : X.finitePoints ↦ X.eulerFactor x.1 s :=
  sorry

/-- The zeta function of the spectrum of a finite field `k` is `(1 - #k ^ (-s))⁻¹`. -/
theorem zeta_spec_eq_of_finite (k : Type u) [Field k] [Finite k] (s : ℂ) :
    (Spec (.of k)).zeta s = (1 - (Nat.card k : ℂ) ^ (-s))⁻¹ :=
  sorry

/-- The zeta function of `Spec ℤ` is the Riemann zeta function (on the half-plane of
absolute convergence, hence everywhere by analytic continuation of the right hand side). -/
theorem zeta_specInt_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (Spec (.of ℤ)).zeta s = riemannZeta s :=
  sorry

end AlgebraicGeometry.Scheme
