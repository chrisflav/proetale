/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.Localization

/-!
# Localization maps are weakly étale

This file records the fact that any localization map `R → S⁻¹R` is weakly étale,
which is item (1) of Stacks
[092J](https://stacks.math.columbia.edu/tag/092J).

## Main results

* `Algebra.WeaklyEtale.of_isLocalization` — for any commutative ring `R`,
  multiplicative submonoid `S ⊆ R`, and ring `T` that is the localization of `R`
  at `S`, the structure map `R → T` is weakly étale. Stated as a theorem because
  the submonoid `S` cannot be inferred from `WeaklyEtale R T` alone.
* `Algebra.WeaklyEtale.localization` — the canonical instance for the explicit
  `Localization S` construction, derived from the theorem above.

## Proof strategy

We unwind Mathlib's definition of weakly étale, which packages two flatness
conditions:

* (F1) `T` is flat as an `R`-module;
* (F2) `T ⊗[R] T` is flat as a `T`-module via the multiplication map
  `Algebra.TensorProduct.lmul' R : T ⊗[R] T →ₐ[R] T`.

Condition (F1) is `IsLocalization.flat`. Condition (F2) follows from the
sharper fact that when `R → T` is a localization, the multiplication map
`T ⊗[R] T → T` is itself bijective (the diagonal ideal vanishes because every
element of `S` is already a unit in `T`), so flatness is immediate from
`RingHom.Flat.of_bijective`. Bijectivity is exactly
`IsLocalization.bijective_linearMap_mul'` from
`Mathlib/RingTheory/Localization/BaseChange.lean`.
-/

namespace Algebra.WeaklyEtale

/-- **Stacks [092J], localization clause.**

For any commutative ring `R`, multiplicative submonoid `S ⊆ R`, and ring `T`
that is the localization of `R` at `S`, the structure map `R → T` is weakly
étale.

This is stated as a theorem (rather than an instance) because the submonoid `S`
cannot be inferred from the head `Algebra.WeaklyEtale R T`. The canonical
instance for `Localization S` is `Algebra.WeaklyEtale.localization` below. -/
theorem of_isLocalization (R : Type*) [CommRing R] (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T] :
    Algebra.WeaklyEtale R T where
  flat := IsLocalization.flat T S
  flat_lmul' :=
    -- Stacks 092J Step 2: `lmul' : T ⊗[R] T → T` is bijective when `R → T` is
    -- a localization (the elements of `S` are already units in `T`, so the
    -- diagonal ideal vanishes). Bijective ring maps are flat.
    RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.lmul' R (S := T)).toRingHom)
      (IsLocalization.bijective_linearMap_mul' (R := R) (A := T) S)

/-- The canonical localization `R → Localization S` is weakly étale. -/
instance localization (R : Type*) [CommRing R] (S : Submonoid R) :
    Algebra.WeaklyEtale R (Localization S) :=
  of_isLocalization R S _

end Algebra.WeaklyEtale
