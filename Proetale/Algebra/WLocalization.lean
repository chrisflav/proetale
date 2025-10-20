/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocal
import Proetale.Algebra.IndZariski

/-!
# w-localization

In this file we show that every ring admits a faithfully flat, ind-Zariski w-local algebra.
-/

namespace WLocalization

variable {A : Type*} [CommRing A]

/-- The submonoid of `A` consisting of elements that become invertible in `(A / I)_f`. -/
def Generalization.submonoid (f : A) (I : Ideal A) : Submonoid A :=
  Submonoid.comap (algebraMap A (Localization.Away <| Ideal.Quotient.mk I f))
    (IsUnit.submonoid _)

/-- The localization of `A` at all elements invertible in `(A / I)_f`. -/
def Generalization (f : A) (I : Ideal A) : Type _ :=
  Localization (Generalization.submonoid f I)

namespace Generalization

variable (f : A) (I : Ideal A)

instance : CommRing (Generalization f I) := fast_instance%
  inferInstanceAs <| CommRing <| Localization (Generalization.submonoid f I)

instance : Algebra A (Generalization f I) := fast_instance%
  inferInstanceAs <| Algebra A <| Localization (Generalization.submonoid f I)

instance : IsLocalization (Generalization.submonoid f I) (Generalization f I) :=
  inferInstanceAs <| IsLocalization _ <| Localization (Generalization.submonoid f I)

/-- The canonical map from the generalization at `(f, I)` to `(A ⧸ I)_f`. -/
noncomputable
def toLocQuotient (f : A) (I : Ideal A) :
    Generalization f I →ₐ[A] Localization.Away (Ideal.Quotient.mk I f) :=
  IsLocalization.liftAlgHom (f := Algebra.ofId _ _) (M := submonoid f I) fun y ↦ y.2

/--
The kernel of the canonical map from the generalization at `(f, I)` to `(A ⧸ I)_f`.
This ideal defines a closed subset of the prime spectrum of the generalization at `(f, I)` that
maps homeomorphically to `D(f) ∩ V(I)`.
-/
noncomputable
def ideal (f : A) (I : Ideal A) : Ideal (Generalization f I) :=
  RingHom.ker (toLocQuotient f I)

instance indZariski : Algebra.IndZariski A (Generalization f I) :=
  sorry

end Generalization

/-- The single stratum `Z(E, F)` in `Spec A`. -/
def stratum (E F : Finset A) : Set (PrimeSpectrum A) :=
  (⋂ f ∈ E, PrimeSpectrum.basicOpen f) ∩ PrimeSpectrum.zeroLocus (Ideal.span (F : Set A))

lemma stratum_eq_basicOpen_inter_zeroLocus (E F : Finset A) :
    stratum E F =
      (PrimeSpectrum.basicOpen (∏ f ∈ E, f) : Set _) ∩
        PrimeSpectrum.zeroLocus (Ideal.span (F : Set A)) :=
  sorry

lemma stratum_anti {E F E' F' : Finset A} (hEE' : E ⊆ E') (hFF' : F ⊆ F') :
    stratum E' F' ⊆ stratum E F :=
  sorry

/-- The type of disjoint union decompositions of `E` into two finite sets. -/
structure Stratification.Index (E : Finset A) where
  left : Finset A
  right : Finset A
  disjoint : Disjoint left right
  union_eq : (left : Set A) ∪ (right : Set A) = E

/-- Given a disjoint union decomposition `E = E' ⨿ E''`, this is product of the `f ∈ E'. -/
def Stratification.Index.function {E : Finset A} (i : Stratification.Index E) : A :=
  ∏ f ∈ i.left, f

/-- Given a disjoint union decomposition `E = E' ⨿ E''`, this is the ideal spanned by `E''`. -/
def Stratification.Index.ideal {E : Finset A} (i : Stratification.Index E) : Ideal A :=
  Ideal.span i.right

/-- The product of the generalizations of `Z(E', E'')` indexed by all disjoint union decompositions
`E = E' ⨿ E''`. -/
def prodStrata (E : Finset A) : Type _ :=
  ∀ (i : Stratification.Index E), Generalization i.function i.ideal

instance (E : Finset A) : CommRing (prodStrata E) := fast_instance%
  inferInstanceAs <| CommRing <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

instance (E : Finset A) : Algebra A (prodStrata E) := fast_instance%
  inferInstanceAs <| Algebra A <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

/-- The ideal of the stratification product, given by the product of the ideals defining
`Z(E', E'')` in its generalization. -/
noncomputable def prodStrataIdeal (E : Finset A) : Ideal (prodStrata E) :=
  Ideal.pi fun _ ↦ Generalization.ideal _ _

lemma exists_specializes_zeroLocus_prodStrataIdeal {E : Finset A}
    (x : PrimeSpectrum (prodStrata E)) :
    ∃ y ∈ PrimeSpectrum.zeroLocus (prodStrataIdeal E), x ⤳ y :=
  sorry

lemma mem_zeroLocus_prodStrataIdeal_of_isClosed {E : Finset A}
    {x : PrimeSpectrum (prodStrata E)} (hx : IsClosed {x}) :
    x ∈ PrimeSpectrum.zeroLocus (prodStrataIdeal E) := by
  obtain ⟨y, hmem, hy⟩ := exists_specializes_zeroLocus_prodStrataIdeal x
  have := hy.mem_closed hx (by simp)
  grind only [= Set.mem_singleton_iff]

end WLocalization
