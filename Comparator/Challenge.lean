/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions

/-!
# Challenge: `ℓ`-adic cohomology is the limit of étale cohomology with `ℤ/ℓⁿℤ`-coefficients

This is a `leanprover/comparator` challenge file. It is stated using only mathlib and the
shared definitions file `Definitions.lean` (which itself only imports mathlib).

Mathlib defines the `ℓ`-adic cohomology of a scheme `X` as the cohomology of the
pro-étale site of `X` with coefficients in the sheaf of continuous `ℤ_[ℓ]`-valued
functions (`AlgebraicGeometry.Scheme.EllAdicCohomology`). `Definitions.lean` constructs,
from mathlib primitives, the canonical comparison zig-zag

`X.EllAdicCohomology ℓ m ──ρ──▸ lim_n Hᵐ(X_proét, ℤ/ℓⁿℤ) ◂──lim c── lim_n Hᵐ(X_ét, ℤ/ℓⁿℤ)`

where `ρ = ellAdicCohomologyToLimit` is induced by the reduction maps `ℤ_[ℓ] → ℤ/ℓⁿℤ` on
coefficient sheaves and `c = etaleToProetaleCohomologySystemHom` is the levelwise
comparison map from étale to pro-étale cohomology. The challenge is to show:

- `bijective_etaleToProetaleCohomology`: **étale and pro-étale cohomology with
  `ℤ/ℓⁿℤ`-coefficients agree** — the canonical comparison map `c` is levelwise bijective
  (in every degree, unconditionally; BS, Corollary 5.1.6).
- `bijective_ellAdicCohomologyToLimit_of_finite`: **`ℓ`-adic cohomology is the inverse
  limit of the pro-étale cohomology groups of `ℤ/ℓⁿℤ`** in positive degrees — the
  canonical map `ρ` in degree `i + 1` is bijective whenever the étale cohomology groups
  `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite.
- `existsUnique_ellAdicCohomology_addEquiv_limit_of_finite`: consequently, **there is a
  unique additive equivalence `X.EllAdicCohomology ℓ (i+1) ≃+ lim_n Hⁱ⁺¹(X_ét, ℤ/ℓⁿℤ)`
  compatible with the two canonical maps**.

Some finiteness-type hypothesis is necessary for the last two statements: in general the
two sides differ by a `lim¹`-term (Jannsen, *Continuous étale cohomology*).
-/

universe u

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry

namespace EllAdicEtaleComparison

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- **Étale and pro-étale cohomology with `ℤ/ℓⁿℤ`-coefficients agree**: the canonical
comparison map from the étale cohomology of the constant sheaf `ℤ/ℓⁿℤ` to the pro-étale
cohomology of the sheaf of continuous `ℤ/ℓⁿℤ`-valued functions is bijective in every
degree. -/
theorem bijective_etaleToProetaleCohomology (m n : ℕ) :
    Function.Bijective (ConcreteCategory.hom
      ((etaleToProetaleCohomologySystemHom X ℓ m).app (op n))) :=
  sorry

variable [Fact ℓ.Prime]

/-- **`ℓ`-adic cohomology is the inverse limit of the pro-étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees: the canonical map induced by the reductions
`ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves is bijective in degree `i + 1`, whenever the
étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` one degree lower are finite. -/
theorem bijective_ellAdicCohomologyToLimit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType ((etaleCohomologySystem X ℓ i).obj (op n)))) :
    Function.Bijective (ConcreteCategory.hom (ellAdicCohomologyToLimit X ℓ (i + 1))) :=
  sorry

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, whenever the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)`
one degree lower are finite: there is a unique additive equivalence
`X.EllAdicCohomology ℓ (i+1) ≃+ lim_n Hⁱ⁺¹(X_ét, ℤ/ℓⁿℤ)` compatible with the canonical
comparison maps into the inverse limit of the pro-étale cohomology groups of `ℤ/ℓⁿℤ`. -/
theorem existsUnique_ellAdicCohomology_addEquiv_limit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType ((etaleCohomologySystem X ℓ i).obj (op n)))) :
    ∃! e : X.EllAdicCohomology ℓ (i + 1) ≃+
        ↥(limit (etaleCohomologySystem X ℓ (i + 1))),
      ∀ x, ConcreteCategory.hom (limMap (etaleToProetaleCohomologySystemHom X ℓ (i + 1)))
          (e x) =
        ConcreteCategory.hom (ellAdicCohomologyToLimit X ℓ (i + 1)) x :=
  sorry

end EllAdicEtaleComparison
