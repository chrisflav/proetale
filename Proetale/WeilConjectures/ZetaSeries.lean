/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaFunction

/-!
# The zeta function of a scheme over a finite field

For a scheme `X` over a finite field `k` with `q` elements, given by a structure morphism
`f : X ⟶ Spec k`, the zeta function of `X` is traditionally packaged as the formal power
series

`Z(X, t) = exp (∑ N_n * t ^ n / n)`,

where `N_n` is the number of points of `X` with values in the degree `n` extension of `k`.
It is related to the zeta function `ζ_X` of `Proetale.WeilConjectures.ZetaFunction` by the
formal substitution `ζ_X(s) = Z(X, q ^ (-s))`.

## Main definitions

- `FiniteField.galoisExtension k n`: a model of the degree `n` extension of the finite
  field `k`, as the splitting field of `X ^ (#k ^ n) - X`.
- `AlgebraicGeometry.Scheme.Hom.fieldPoints`: the `K`-rational points of `X` relative to a
  structure morphism `f : X ⟶ Spec k`.
- `AlgebraicGeometry.Scheme.Hom.pointCount`: the number `N_n` of points of `X` rational
  over the degree `n` extension of `k`.
- `AlgebraicGeometry.Scheme.Hom.zetaSeries`: the power series `Z(X, t) ∈ ℚ⟦t⟧`.
- `AlgebraicGeometry.Scheme.Hom.degreeOver`: the degree `[κ(x) : k]` of a point.

## Main statements

- `FiniteField.nat_card_galoisExtension`: the degree `n` extension of `k` has `#k ^ n`
  elements.
- `AlgebraicGeometry.Scheme.Hom.nat_card_fieldPoints_congr`: the point counts do not
  depend on the chosen model of the coefficient field extension.
- `AlgebraicGeometry.Scheme.Hom.X_mul_derivative_zetaSeries`: the logarithmic derivative
  of `Z(X, t)` is the generating series of the point counts, i.e.
  `t * Z'(X, t) = (∑ N_n t ^ n) * Z(X, t)`. Together with
  `constantCoeff_zetaSeries` this characterizes `Z(X, t)` uniquely.

The Euler product expansion `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹` over the closed points of
`X` is proved in `Proetale.WeilConjectures.EulerProduct`.
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace FiniteField

/-- A model for the degree `n` extension of a finite field `k` with `q` elements:
the splitting field of `X ^ (q ^ n) - X` over `k`. For infinite `k` this is junk
(the polynomial degenerates), as is the value for `n = 0`. -/
def galoisExtension (k : Type u) [Field k] (n : ℕ) : Type u :=
  (X ^ Nat.card k ^ n - X : k[X]).SplittingField
deriving Field, Algebra k, FiniteDimensional k,
  IsSplittingField k _ (X ^ Nat.card k ^ n - X)

variable (k : Type u) [Field k] (n : ℕ)

/-- The degree `n` extension of a finite field `k` has `#k ^ n` elements. -/
theorem nat_card_galoisExtension [Finite k] (hn : n ≠ 0) :
    Nat.card (galoisExtension k n) = Nat.card k ^ n := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  set L := galoisExtension k n with hL
  set g : k[X] := X ^ Nat.card k ^ n - X with hgdef
  obtain ⟨p, hcharp, s, hp, hcard⟩ := FiniteField.card' (K := k)
  haveI := hcharp
  have hq1 : 1 < Nat.card k := Finite.one_lt_card
  have hqs : Nat.card k = p ^ (s : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hpq : p ∣ Nat.card k ^ n :=
    dvd_trans (hqs ▸ dvd_pow_self p s.2.ne') (dvd_pow_self _ hn)
  have hg0 : g ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero (K' := k) hn hq1
  have hsep : g.Separable := galois_poly_separable p (Nat.card k ^ n) hpq
  -- every element of `L` is fixed by the `q ^ n`-power Frobenius
  haveI : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  haveI : ExpChar L p := .prime hp
  have hpsn : p ^ ((s : ℕ) * n) = Nat.card k ^ n := by rw [pow_mul, ← hqs]
  have hak : ∀ a : k, a ^ Nat.card k ^ n = a := fun a ↦ by
    rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card_pow n a
  let ψ : L →ₐ[k] L :=
    { iterateFrobenius L p ((s : ℕ) * n) with
      commutes' := fun a ↦ by
        change algebraMap k L a ^ p ^ ((s : ℕ) * n) = algebraMap k L a
        rw [hpsn, ← map_pow, hak] }
  have key : ∀ x : L, x ^ Nat.card k ^ n = x := by
    have hle : Algebra.adjoin k (g.rootSet L) ≤ AlgHom.equalizer ψ (AlgHom.id k L) := by
      refine Algebra.adjoin_le fun x hx ↦ ?_
      rw [Polynomial.mem_rootSet_of_ne hg0] at hx
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      change x ^ p ^ ((s : ℕ) * n) = x
      rw [hpsn]
      simpa [hgdef, sub_eq_zero] using hx
    intro x
    have hx : x ∈ AlgHom.equalizer ψ (AlgHom.id k L) :=
      hle (Polynomial.IsSplittingField.adjoin_rootSet L g ▸ Algebra.mem_top)
    rw [AlgHom.mem_equalizer] at hx
    calc x ^ Nat.card k ^ n = ψ x := by change _ = x ^ p ^ ((s : ℕ) * n); rw [hpsn]
      _ = x := hx
  -- hence `L` consists exactly of the roots of `g`, of which there are `q ^ n`
  have huniv : g.rootSet L = Set.univ := Set.eq_univ_of_forall fun x ↦ by
    rw [Polynomial.mem_rootSet_of_ne hg0, hgdef, map_sub, map_pow, aeval_X, sub_eq_zero]
    exact key x
  have hcardroots : Fintype.card (g.rootSet L) = Nat.card k ^ n := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep
        (Polynomial.IsSplittingField.splits L g),
      FiniteField.X_pow_card_pow_sub_X_natDegree_eq (K' := k) hn hq1]
  calc Nat.card L = Nat.card (g.rootSet L) := by
        rw [huniv]; exact (Nat.card_congr (Equiv.Set.univ L)).symm
    _ = Nat.card k ^ n := by rw [Nat.card_eq_fintype_card, hcardroots]

/-- The degree `n` extension of a finite field `k` has degree `n` over `k`. -/
theorem finrank_galoisExtension [Finite k] (hn : n ≠ 0) :
    Module.finrank k (galoisExtension k n) = n := by
  haveI : Fintype k := Fintype.ofFinite k
  have hcard := nat_card_galoisExtension k n hn
  haveI : Finite (galoisExtension k n) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (pow_pos Nat.card_pos n).ne')
  haveI : Fintype (galoisExtension k n) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank
    (K := k) (V := galoisExtension k n)] at hcard
  exact Nat.pow_right_injective Fintype.one_lt_card hcard

end FiniteField

end

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The `K`-rational points `X(K)` of a scheme `X` with structure morphism
`f : X ⟶ Spec k`, for a field extension `K` of `k`: morphisms `Spec K ⟶ X` commuting
with the structure morphisms. -/
def Hom.fieldPoints (f : X.Hom (Spec (.of k))) (K : Type u) [Field K] [Algebra k K] :
    Type u :=
  {g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))}

/-- An isomorphism of coefficient field extensions induces an equivalence of rational
point sets. -/
noncomputable def Hom.fieldPointsCongr (f : X.Hom (Spec (.of k))) {K L : Type u}
    [Field K] [Field L] [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L) :
    f.fieldPoints K ≃ f.fieldPoints L where
  toFun g := ⟨Spec.map (CommRingCat.ofHom (e : K →+* L)) ≫ g.1, by
    rw [Category.assoc, g.2, ← Spec.map_comp]
    congr 1
    ext a
    simp⟩
  invFun h := ⟨Spec.map (CommRingCat.ofHom (e.symm : L →+* K)) ≫ h.1, by
    rw [Category.assoc, h.2, ← Spec.map_comp]
    congr 1
    ext a
    simp⟩
  left_inv g := Subtype.ext <| by
    have h : CommRingCat.ofHom (e : K →+* L) ≫ CommRingCat.ofHom (e.symm : L →+* K) =
        𝟙 (CommRingCat.of K) := by
      ext a
      simp
    change Spec.map _ ≫ Spec.map _ ≫ g.1 = g.1
    rw [← Category.assoc, ← Spec.map_comp, h, Spec.map_id, Category.id_comp]
  right_inv h := Subtype.ext <| by
    have hy : CommRingCat.ofHom (e.symm : L →+* K) ≫ CommRingCat.ofHom (e : K →+* L) =
        𝟙 (CommRingCat.of L) := by
      ext a
      simp
    change Spec.map _ ≫ Spec.map _ ≫ h.1 = h.1
    rw [← Category.assoc, ← Spec.map_comp, hy, Spec.map_id, Category.id_comp]

/-- The number of rational points is invariant under isomorphisms of the coefficient
field extension. In particular, over a finite field the point counts `N_n` do not depend
on the chosen model of the degree `n` extension. -/
theorem Hom.nat_card_fieldPoints_congr (f : X.Hom (Spec (.of k))) {K L : Type u}
    [Field K] [Field L] [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L) :
    Nat.card (f.fieldPoints K) = Nat.card (f.fieldPoints L) :=
  Nat.card_congr (f.fieldPointsCongr e)

/-- `f.pointCount n` is the number `N_n` of points of `X` which are rational over the
degree `n` extension of `k`, with junk value `0` if this number is infinite. -/
noncomputable def Hom.pointCount (f : X.Hom (Spec (.of k))) (n : ℕ) : ℕ :=
  Nat.card (f.fieldPoints (FiniteField.galoisExtension k n))

/-- The zeta function of a scheme `X` over a finite field `k` with `q` elements, given by
a structure morphism `f : X ⟶ Spec k`, as a formal power series:
`Z(X, t) = exp (∑ N_n * t ^ n / n)` where `N_n = #X(𝔽_(q ^ n))`.

It is related to the zeta function `ζ_X` of `X` as an abstract scheme by the formal
identity `ζ_X(s) = Z(X, q ^ (-s))`, see `Hom.zetaSeries_eq_tprod`. -/
noncomputable def Hom.zetaSeries (f : X.Hom (Spec (.of k))) : PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ) / n)

variable (f : X ⟶ Spec (.of k))

private lemma hasSubst_pointCount :
    PowerSeries.HasSubst
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (Hom.pointCount f n : ℚ) / n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

/-- The zeta function of a scheme over a finite field has constant coefficient `1`. -/
theorem Hom.constantCoeff_zetaSeries :
    PowerSeries.constantCoeff f.zetaSeries = 1 := by
  have h0 : PowerSeries.coeff 0 f.zetaSeries = 1 := by
    unfold Hom.zetaSeries
    rw [PowerSeries.coeff_subst' (hb := hasSubst_pointCount f), finsum_eq_single _ 0
      fun d hd ↦ by simp [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, zero_pow hd]]
    simp [PowerSeries.coeff_exp]
  simpa using h0

/-- The logarithmic derivative of the zeta function of `X` over `k` is the generating
function of the point counts of `X`: `t * Z'(X, t) = (∑ N_n * t ^ n) * Z(X, t)`. -/
theorem Hom.X_mul_derivative_zetaSeries :
    PowerSeries.X * PowerSeries.derivative ℚ f.zetaSeries =
      PowerSeries.mk (fun n ↦ if n = 0 then (0 : ℚ) else f.pointCount n) *
        f.zetaSeries := by
  have hXF : PowerSeries.X * PowerSeries.derivative ℚ
      (PowerSeries.mk fun n ↦ if n = 0 then 0 else (f.pointCount n : ℚ) / n) =
      PowerSeries.mk fun n ↦ if n = 0 then (0 : ℚ) else f.pointCount n := by
    ext n
    match n with
    | 0 => simp
    | m + 1 =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg m.succ_ne_zero,
        if_neg m.succ_ne_zero]
      have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      rw [div_mul_cancel₀ _ hm]
  unfold Hom.zetaSeries
  rw [PowerSeries.derivative_subst (hg := hasSubst_pointCount f), PowerSeries.derivative_exp,
    mul_comm (PowerSeries.subst _ (PowerSeries.exp ℚ)), ← mul_assoc, hXF]

/-- The canonical embedding of the base field of `X` into the residue field of a point,
induced by the structure morphism via functoriality of residue fields. See
`AlgebraicGeometry.Scheme.Hom.specMap_residueFieldAlgebraMap` for its geometric
characterization. -/
noncomputable def Hom.residueFieldAlgebraMap (f : X.Hom (Spec (.of k))) (x : X) :
    k →+* X.residueField x :=
  (CommRingCat.ofHom (algebraMap (CommRingCat.of k) (f.base x).asIdeal.ResidueField) ≫
    (Spec.residueFieldIso (.of k) (f.base x)).inv ≫ f.residueFieldMap x).hom

/-- The degree `[κ(x) : k]` of a point `x` of a scheme `X` over a field `k`, with junk
value `0` if the residue field extension is infinite. -/
noncomputable def Hom.degreeOver (f : X.Hom (Spec (.of k))) (x : X) : ℕ :=
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  Module.finrank k (X.residueField x)

end AlgebraicGeometry.Scheme
