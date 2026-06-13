/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Challenge: `ℓ`-adic cohomology is the limit of étale cohomology with `ℤ/ℓⁿℤ`-coefficients

This is a `leanprover/comparator` challenge file. It is stated using only mathlib.

Mathlib defines the `ℓ`-adic cohomology of a scheme `X` as the cohomology of the
pro-étale site of `X` with coefficients in the sheaf of continuous `ℤ_[ℓ]`-valued
functions (`AlgebraicGeometry.Scheme.EllAdicCohomology`). The challenge is to show
that, **whenever the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite, `ℓ`-adic
cohomology in degree `i + 1` is the inverse limit over `n` of the étale cohomology
groups of the constant sheaves `ℤ/ℓⁿℤ`** (with transition maps induced by the
reduction maps `ℤ/ℓⁿ⁺¹ℤ → ℤ/ℓⁿℤ`).

Some finiteness-type hypothesis is necessary: in general the two sides differ by a
`lim¹`-term (Jannsen, *Continuous étale cohomology*).

The étale cohomology system is spelled out below from mathlib primitives: the degree-`i`
étale cohomology of the constant sheaf on `M` is
`Ext ((constantSheaf X.smallEtaleTopology Ab).obj (.of (ULift ℤ)))
  ((constantSheaf X.smallEtaleTopology Ab).obj (.of M)) i`,
which is mathlib's `CategoryTheory.Sheaf.H` of the constant sheaf, and the
functoriality in the system direction is `extFunctorObj`, which agrees with mathlib's
`CategoryTheory.Sheaf.H.map`.
-/

universe u

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry

instance Ab.hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance Ab.ab5OfSize : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

namespace EllAdicEtaleComparison

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

/-- The inverse system `n ↦ Hⁱ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ` on the small étale site of `X`, with transition maps induced by the
reduction maps. Its value at `n` is
`AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab).obj
  (AddCommGrpCat.of (ULift (ZMod (ℓ ^ n))))) i)`. -/
noncomputable def etaleCohomologySystem (X : Scheme.{u}) (ℓ : ℕ) (i : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙
    extFunctorObj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))) i

/-- The value of `etaleCohomologySystem` at level `n` is the étale cohomology
`Hⁱ(X_ét, ℤ/ℓⁿℤ)` in the sense of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem etaleCohomologySystem_obj (X : Scheme.{u}) (ℓ : ℕ) (i n : ℕ) :
    (etaleCohomologySystem X ℓ i).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) i) :=
  rfl

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, whenever the étale cohomology groups
`Hⁱ(X_ét, ℤ/ℓⁿℤ)` one degree lower are finite. -/
theorem nonempty_ellAdicCohomology_addEquiv_limit_of_finite
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType ((etaleCohomologySystem X ℓ i).obj (op n)))) :
    Nonempty (X.EllAdicCohomology ℓ (i + 1) ≃+
      ↥(limit (etaleCohomologySystem X ℓ (i + 1)))) :=
  sorry

end EllAdicEtaleComparison
