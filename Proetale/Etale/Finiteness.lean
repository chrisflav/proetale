/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.IsSepClosed
import Proetale.Etale.ProperBaseChange
import Proetale.Topology.Comparison.EllAdicCanonical

/-!
# Finiteness of étale cohomology of proper schemes

For a scheme `X` proper over a separably closed field, the étale cohomology groups
`Hᵠ(X_ét, M)` with coefficients in a finite abelian group `M` are finite
(SGA 4, Exp. XIV; Stacks 0A4B ff.). This is a consequence of the proper base change
theorem (`Proetale/Etale/ProperBaseChange.lean`): by proper base change the stalks of
the higher direct images along a fibration in curves are the cohomologies of the
fibers, so the dévissage of the proper base change theorem reduces finiteness to the
case of curves over separably closed fields.

- `AlgebraicGeometry.Scheme.finite_H_of_isProper`: the finiteness theorem (statement;
  the deduction shares the missing inputs of the proper base change theorem and is
  decomposed in the blueprint chapter "Proper base change").

As a corollary, the finiteness hypothesis in the `ℓ`-adic comparison theorem
(`Proetale/Topology/Comparison/EllAdicCanonical.lean` and the comparator pair) is
automatically satisfied:

- `AlgebraicGeometry.Scheme.bijective_ellAdicCohomologyToLimit_of_isProper` and
  `AlgebraicGeometry.Scheme.existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper`:
  **for `X` proper over a separably closed field, `ℓ`-adic cohomology is
  unconditionally the inverse limit of the étale cohomology groups `ℤ/ℓⁿℤ`**, via the
  canonical comparison maps. These deductions are complete Lean proofs; only the
  finiteness input itself remains to be proved.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

include f in
/-- **Finiteness of étale cohomology** (SGA 4, Exp. XIV): the étale cohomology groups
of a scheme proper over a separably closed field with coefficients in a finite abelian
group are finite. -/
theorem finite_H_of_isProper (M : Type) [AddCommGroup M] [Finite M] (q : ℕ) :
    Finite (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} M))) q) := by
  -- **Deduction from proper base change** (see the blueprint chapter "Proper base
  -- change", section "Finiteness of étale cohomology"):
  -- 1. Induct on the dimension of `X`. Locally on a stratification, `X` admits (after
  --    the standard reductions: Chow's lemma to reduce to projective `X`, and finite
  --    morphisms, which preserve finiteness since `R^q = 0` for `q > 0` and stalks
  --    are finite products) a fibration `π : X → Y` in curves over a base of smaller
  --    dimension.
  -- 2. By the proper base change theorem
  --    (`isIso_derivedBaseChangeNatTrans_app`, applied to the square over each
  --    geometric point of `Y`), the stalks of `R^q π_* (ℤ/n)` are the cohomology
  --    groups `H^q` of the geometric fibers, which are proper curves over separably
  --    closed fields: these are finite by the curve computations
  --    (blueprint `thm:pbc-curves`) — in particular `R^q π_*(ℤ/n)` is constructible.
  -- 3. The Leray spectral sequence for `π` (or the exact couples of the associated
  --    filtration in the derived category `DerivedCategoryPlus`) expresses
  --    `H^q(X, ℤ/n)` by extensions of `H^p(Y, R^{q-p} π_* (ℤ/n))`, which are finite
  --    by the induction hypothesis applied to the constructible sheaves
  --    `R^{q-p} π_* (ℤ/n)` (dévissage from constant to constructible coefficients:
  --    finite filtrations with subquotients pushed forward from constant sheaves on
  --    finite étale covers of locally closed strata).
  -- Prerequisite gaps beyond the proper base change theorem itself: constructible
  -- sheaves, the Leray spectral sequence, and the étale cohomology of curves.
  sorry

include f in
/-- **`ℓ`-adic cohomology of a proper scheme over a separably closed field is
unconditionally the inverse limit of the étale cohomology groups of `ℤ/ℓⁿℤ`**: the
canonical map to the inverse limit of the pro-étale cohomology groups is bijective,
the finiteness hypothesis of the general comparison theorem being satisfied by
`finite_H_of_isProper`. -/
theorem bijective_ellAdicCohomologyToLimit_of_isProper (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    Function.Bijective (ConcreteCategory.hom
      (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1))) :=
  ProEt.bijective_ellAdicCohomologyToLimit_of_finite X ℓ i fun n ↦ by
    haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out (p := ℓ.Prime)).ne_zero⟩
    exact finite_H_of_isProper f (ZMod (ℓ ^ n)) i

include f in
/-- **The `ℓ`-adic comparison for proper schemes over separably closed fields**: for
`X` proper over a separably closed field there is a unique additive equivalence
between the `ℓ`-adic cohomology `Hⁱ⁺¹(X_proét, ℤ_ℓ)` and the inverse limit of the
étale cohomology groups `Hⁱ⁺¹(X_ét, ℤ/ℓⁿℤ)` compatible with the canonical comparison
maps — no finiteness hypothesis is needed, by `finite_H_of_isProper`. -/
theorem existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ) :
    ∃! e : X.EllAdicCohomology ℓ (i + 1) ≃+
        ↥(limit (EllAdicEtaleComparison.etaleCohomologySystem X ℓ (i + 1))),
      ∀ x, ConcreteCategory.hom (limMap
          (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))
          (e x) =
        ConcreteCategory.hom
          (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1)) x :=
  ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite X ℓ i fun n ↦ by
    haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out (p := ℓ.Prime)).ne_zero⟩
    exact finite_H_of_isProper f (ZMod (ℓ ^ n)) i

end AlgebraicGeometry.Scheme
