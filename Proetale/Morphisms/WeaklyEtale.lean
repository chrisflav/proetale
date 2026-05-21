/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Limits
import Proetale.FromPi1.Etale
import Proetale.Algebra.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Weakly étale morphisms

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace WeaklyEtale

instance : HasRingHomProperty @WeaklyEtale.{u} RingHom.WeaklyEtale := by
  haveI := HasRingHomProperty.of_isZariskiLocalAtSource_of_isZariskiLocalAtTarget @WeaklyEtale.{u}
  refine HasRingHomProperty.copy (P := @WeaklyEtale.{u}) rfl ?_
  intro R S _ _ f
  letI : Algebra R S := f.toAlgebra
  have hf : f = algebraMap R S := rfl
  rw [hf, weaklyEtale_iff, diagonal_SpecMap R S,
    MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
    HasRingHomProperty.Spec_iff (P := @Flat), HasRingHomProperty.Spec_iff (P := @Flat)]
  simp only [CommRingCat.hom_ofHom, autoParam, RingHom.flat_algebraMap_iff,
    RingHom.weaklyEtale_algebraMap_iff, Algebra.weaklyEtale_iff]

/-- A weakly étale ring map is formally unramified. -/
private lemma _root_.RingHom.WeaklyEtale.formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.WeaklyEtale) :
    f.FormallyUnramified := by
  letI := f.toAlgebra
  have : Algebra.WeaklyEtale R S := hf
  exact (inferInstance : Algebra.FormallyUnramified R S)

instance (priority := 900) etale [WeaklyEtale f] [LocallyOfFinitePresentation f] : Etale f := by
  have : FormallyUnramified f := by
    rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
    intro U V e
    exact (HasRingHomProperty.appLE @WeaklyEtale.{u} f ‹_› U V e).formallyUnramified
  exact Etale.of_formallyUnramified_of_flat f

@[simp]
lemma Spec_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    WeaklyEtale (Spec.map f) ↔ f.hom.WeaklyEtale :=
  HasRingHomProperty.Spec_iff (P := @WeaklyEtale.{u})

end WeaklyEtale

end AlgebraicGeometry
