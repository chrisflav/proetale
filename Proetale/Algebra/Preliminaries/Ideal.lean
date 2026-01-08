/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!

# Colimit of Ideals

-/

open CategoryTheory Limits PrimeSpectrum

theorem zeroLocus_eq_iInter_specComap_preimage {ι : Type*} [Category ι] [IsFiltered ι]
    {F : Functor ι CommRingCat} {C : Cocone F} (hC : IsColimit C) {Iι : (i : ι) → Ideal (F.obj i)}
    (I : Ideal C.pt) (h : I = ⨆ (i : ι), ((Iι i).map (C.ι.app i).hom : Ideal C.pt)) :
    (zeroLocus I : Set (PrimeSpectrum C.pt)) =
      ⋂ (i : ι), (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i : Set (F.obj i))) :=
  sorry

theorem specComap_preimage_zeroLocus_subset {ι : Type*} [Category ι]
    {F : Functor ι CommRingCat} (C : Cocone F) {i j : ι} (f : i ⟶ j)
    {Iι : (i : ι) → Ideal (F.obj i)} (h : (Iι i).map (F.map f).hom ≤ Iι j) :
    (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i)) ⊆
      (PrimeSpectrum.comap (C.ι.app j).hom) ⁻¹' (zeroLocus (Iι j)):=
  sorry
