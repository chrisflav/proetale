/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.OpenImmersion

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/
/-- An `R`-algebra `S` is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
class Algebra.IsLocalIso (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] : Prop where
  exists_notMem_isStandardOpenImmersion (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, IsStandardOpenImmersion R (Localization.Away g)

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra.IsLocalIso

instance [IsStandardOpenImmersion R S] : IsLocalIso R S where
  exists_notMem_isStandardOpenImmersion q hq := by
    use 1, hq.one_notMem
    exact IsStandardOpenImmersion.trans _ S _

end Algebra.IsLocalIso

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)"]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso :=
  sorry

lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso :=
  sorry

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
