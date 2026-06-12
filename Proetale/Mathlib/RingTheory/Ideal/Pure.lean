/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Ideal.Pure
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat surjective ring maps and pure kernels

For a surjective ring map `f : A →+* B`, flatness of `f` is equivalent to the kernel of `f`
being a pure ideal in `A`.
-/

/-- The kernel of a flat surjective ring map is a pure ideal. -/
lemma RingHom.pure_ker_of_flat_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (hsurj : Function.Surjective f) :
    (RingHom.ker f).Pure := by
  algebraize [f]
  exact .of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId A B) hsurj).toLinearEquiv

/-- A surjective ring map whose kernel is a pure ideal is flat. This is the converse of
`RingHom.pure_ker_of_flat_of_surjective`. -/
lemma RingHom.Flat.of_pure_ker_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} (hsurj : Function.Surjective f) (h : (RingHom.ker f).Pure) :
    f.Flat := by
  algebraize [f]
  haveI : Module.Flat A (A ⧸ RingHom.ker (Algebra.ofId A B)) := h
  exact .of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId A B) hsurj).symm.toLinearEquiv

/-- For a surjective ring map, flatness is equivalent to the kernel being a pure ideal. -/
lemma RingHom.flat_iff_pure_ker_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} (hsurj : Function.Surjective f) :
    f.Flat ↔ (RingHom.ker f).Pure :=
  ⟨fun hf ↦ RingHom.pure_ker_of_flat_of_surjective f hf hsurj,
    RingHom.Flat.of_pure_ker_of_surjective hsurj⟩
