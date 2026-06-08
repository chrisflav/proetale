/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.Localization

/-!
# Localization maps are weakly étale

This file records the fact that any localization map `R → S⁻¹R` is weakly étale,
which is item (1) of Stacks
[092J](https://stacks.math.columbia.edu/tag/092J).

## Main results

* `Algebra.WeaklyEtale.of_isLocalization` — if `T` is the localization of `R` at a
  submonoid `S`, then `T` is a weakly étale `R`-algebra.
* `Algebra.WeaklyEtale.localization` — the canonical instance for `Localization S`.
-/

namespace Algebra.WeaklyEtale

/-- **Stacks [092J], localization clause.**

If `T` is the localization of `R` at a submonoid `S`, then `T` is weakly étale over `R`. -/
@[stacks 092J "(1)"]
theorem of_isLocalization (R : Type*) [CommRing R] (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T] :
    Algebra.WeaklyEtale R T where
  flat := IsLocalization.flat T S
  flat_lmul' :=
    RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.lmul' R (S := T)).toRingHom)
      (IsLocalization.bijective_linearMap_mul' (R := R) (A := T) S)

/-- The canonical localization `R → Localization S` is weakly étale. -/
instance localization (R : Type*) [CommRing R] (S : Submonoid R) :
    Algebra.WeaklyEtale R (Localization S) :=
  of_isLocalization R S _

end Algebra.WeaklyEtale
