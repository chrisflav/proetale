/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The étale cohomology system of the constant sheaves `ℤ/ℓⁿℤ`

For a scheme `X`, a prime `ℓ` and a cohomological degree `m`, we spell out the inverse
system

`n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)`

of étale cohomology groups of the constant sheaves `ℤ/ℓⁿℤ` on the small étale site of
`X`, with transition maps induced by the reduction maps `ℤ/ℓⁿ⁺¹ℤ → ℤ/ℓⁿℤ`. This is the
étale side of the `ℓ`-adic comparison: `ℓ`-adic cohomology
(`AlgebraicGeometry.Scheme.EllAdicCohomology`) is, under a finiteness hypothesis, the
inverse limit of this system.

The degree-`m` étale cohomology of the constant sheaf on `M` is
`Ext ((constantSheaf X.smallEtaleTopology Ab).obj (.of (ULift ℤ)))
  ((constantSheaf X.smallEtaleTopology Ab).obj (.of M)) m`,
which is mathlib's `CategoryTheory.Sheaf.H` of the constant sheaf, and the functoriality
in the system direction is `extFunctorObj`, which agrees with mathlib's
`CategoryTheory.Sheaf.H.map`.

## Main definitions

* `AlgebraicGeometry.zmodAbSystem`: the inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian
  groups, with the reduction maps as transition maps.
* `AlgebraicGeometry.Scheme.etaleCohomologySystem`: the inverse system
  `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups.
-/

universe u

open CategoryTheory Limits Opposite Abelian

instance : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

namespace AlgebraicGeometry

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

/-- The transition maps of `zmodAbSystem` are the (`ULift`ed) reduction maps. -/
lemma zmodAbSystem_map_succ (ℓ n : ℕ) :
    (zmodAbSystem.{u} ℓ).map (homOfLE (Nat.le_succ n)).op =
      AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom) :=
  congrArg Quiver.Hom.unop
    (Functor.ofSequence_map_homOfLE_succ
      (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (f := fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)
      n)

namespace Scheme

variable (X : Scheme.{u})

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantUnit : Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The inverse system `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ` on the small étale site of `X`, with transition maps induced by the
reduction maps. Its value at `n` is
`AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab).obj
  (AddCommGrpCat.of (ULift (ZMod (ℓ ^ n))))) m)`. -/
noncomputable def etaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙
    extFunctorObj (etaleConstantUnit X) m

/-- The value of `etaleCohomologySystem` at level `n` is the étale cohomology
`Hᵐ(X_ét, ℤ/ℓⁿℤ)` in the sense of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem etaleCohomologySystem_obj (ℓ m n : ℕ) :
    (etaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) m) :=
  rfl

end Scheme

end AlgebraicGeometry
