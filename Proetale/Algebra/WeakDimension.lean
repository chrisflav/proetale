/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtale

/-!
# Weak dimension of a commutative ring

Since mathlib does not have `Tor`, we only define some special cases in low dimensions.
-/

/-- A ring `R` is absolutely flat if every ideal of `R` is pure, i.e. `R ⧸ I` is flat. -/
class Ring.AbsolutelyFlat (R : Type*) [CommRing R] where
  flat (I : Ideal R) : Module.Flat R (R ⧸ I)

/-- A ring `R` is of weak dimension `≤ 1` if any finitely generated ideal is flat. -/
class Ring.WeakDimensionLEOne (R : Type*) [CommRing R] where
  flat_of_fg (I : Ideal R) : I.FG → Module.Flat R I

namespace Ring.WeakDimensionLEOne

variable (R : Type*) [CommRing R]

/-- If `R` is of weak dimension `≤ 1` if any submodule of a flat module is flat. -/
lemma flat_submodule [Ring.WeakDimensionLEOne R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N :=
  sorry

end Ring.WeakDimensionLEOne

namespace Ring.AbsolutelyFlat

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

instance [AbsolutelyFlat R] : Module.Flat R M := by
  sorry

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat)

include h in
@[stacks 092C]
theorem _root_.Module.Flat.of_flat_lmul'_of_flat [Module.Flat R M] : Module.Flat S M := by
  constructor
  rintro P _ _ _ N h

  sorry

include h in
@[stacks 092I "(2)"]
theorem of_flat_lmul' [AbsolutelyFlat R] : AbsolutelyFlat S :=
  ⟨fun _ ↦ Module.Flat.of_flat_lmul'_of_flat R S _ h⟩

end Ring.AbsolutelyFlat
