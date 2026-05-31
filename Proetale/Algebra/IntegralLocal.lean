/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.RingTheory.Henselian

/-!
# Local rings and integral algebras

This file collects miscellaneous lemmas relating local rings, integral ring
homomorphisms, and Henselian local rings.  These are used in the proof of
[Stacks 097Z](https://stacks.math.columbia.edu/tag/097Z) (over a strictly
Henselian local ring, a weakly étale local algebra is the ring itself).

## Main statements

* `HenselianLocalRing.exists_pi_of_finite` ([Stacks 04GH (1)]
  (https://stacks.math.columbia.edu/tag/04GH)):
  A finite algebra over a Henselian local ring decomposes as a finite product
  of Henselian local rings, each finite over the base.
* `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain`:
  An integral algebra over a Henselian local ring that is an integral domain is local.
* `Algebra.IsAlgebraic.residueField_of_isIntegral`:
  The residue field extension induced by a local integral homomorphism of local rings
  is algebraic.
* `Algebra.IsLocalRing.tensorProduct_of_isPurelyInseparable_residueField`
  ([Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y)):
  If `R → S` is local and integral and either `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely
  inseparable, the tensor product `S ⊗[R] T` is a local ring.
-/

universe u

open TensorProduct

namespace HenselianLocalRing

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]

/-- A finite algebra over a Henselian local ring is, as a ring, a finite product of
Henselian local rings, each finite over the base.

[Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH).

This is destined to go directly to Mathlib, so it should not be worked on here. -/
theorem exists_pi_of_finite :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, HenselianLocalRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i)),
        Nonempty (S ≃ₐ[R] (Π i, B i)) :=
  sorry

end HenselianLocalRing

namespace IsLocalRing

/-- An integral algebra over a Henselian local ring that is an integral domain is local. -/
theorem of_henselianLocalRing_of_isIntegral_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] :
    IsLocalRing S :=
  sorry

end IsLocalRing

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The residue field extension induced by a local integral homomorphism of local rings is
algebraic. -/
theorem IsAlgebraic.residueField_of_isIntegral [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  sorry

variable (R S) in
/-- Let `R → S` and `R → T` be local ring homomorphisms of local rings, with `R → S`
integral.  If `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely inseparable, the tensor product
`S ⊗[R] T` is a local ring.

[Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y). -/
theorem isLocalRing_tensorProduct_of_isPurelyInseparable_residueField
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (S ⊗[R] T) :=
  sorry

end Algebra
