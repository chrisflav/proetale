/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions
import Proetale.Topology.Comparison.EllAdicCanonical

/-!
# Solution: `ℓ`-adic cohomology is the limit of étale cohomology with `ℤ/ℓⁿℤ`-coefficients

This is the solution to the `leanprover/comparator` challenge in `Challenge.lean`. The
challenge statements are about the canonical comparison maps constructed in the shared
mathlib-only definitions file `Definitions.lean`; they are proved in
`Proetale/Topology/Comparison/EllAdicCanonical.lean` using this repository.
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
  Scheme.ProEt.bijective_etaleToProetaleCohomology X ℓ m n

variable [Fact ℓ.Prime]

/-- **`ℓ`-adic cohomology is the inverse limit of the pro-étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees: the canonical map induced by the reductions
`ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves is bijective in degree `i + 1`, whenever the
étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` one degree lower are finite. -/
theorem bijective_ellAdicCohomologyToLimit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType ((etaleCohomologySystem X ℓ i).obj (op n)))) :
    Function.Bijective (ConcreteCategory.hom (ellAdicCohomologyToLimit X ℓ (i + 1))) :=
  Scheme.ProEt.bijective_ellAdicCohomologyToLimit_of_finite X ℓ i hfin

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
  Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite X ℓ i hfin

end EllAdicEtaleComparison
