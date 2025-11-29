/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.RingHomProperties
import Proetale.Mathlib.CategoryTheory.ObjectProperty.Ind

open CategoryTheory

variable {R : Type*} [CommRing R]

universe u v w w'

open CategoryTheory Limits Algebra

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- The induced object property in the category of commutative `R`-algebras by
a property of ring homomorphisms. -/
def RingHom.toObjectProperty
    (P : ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (R : Type u) [CommRing R] :
    ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ P (algebraMap R S)

@[simp]
lemma RingHom.toObjectProperty_iff
    (P : ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (S : CommAlgCat.{v} R) :
    RingHom.toObjectProperty P R S ↔ P (algebraMap R S) :=
  .rfl

lemma RingHom.RespectsIso.isClosedUnderIsomorphisms_toObjectProperty
    {P : ∀ {R : Type u} {S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.RespectsIso P) (R : Type u) [CommRing R] :
    (RingHom.toObjectProperty P R).IsClosedUnderIsomorphisms := by
  refine ⟨fun {A B} e hA ↦ ?_⟩
  rw [toObjectProperty_iff, ← (CommAlgCat.algEquivOfIso e).toAlgHom.comp_algebraMap]
  exact hP.1 (algebraMap R A) (CommAlgCat.algEquivOfIso e).toRingEquiv hA

lemma RingHom.RespectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty
    (P : ∀ {R : Type u} {S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.RespectsIso P) :
    MorphismProperty.ind.{w} (RingHom.toMorphismProperty P) (CommRingCat.ofHom <| algebraMap R S) ↔
      ObjectProperty.ind.{w} (RingHom.toObjectProperty P R) (CommAlgCat.of R S) := by
  have := hP.isClosedUnderIsomorphisms_toObjectProperty R
  rw [MorphismProperty.ind_iff_ind_underMk, ObjectProperty.ind_iff_of_equivalence
    (commAlgCatEquivUnder (.of R)).symm]
  rfl

end
