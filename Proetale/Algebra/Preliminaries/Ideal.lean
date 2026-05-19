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
    {F : Functor ι CommRingCat} {C : Cocone F} (_hC : IsColimit C) {Iι : (i : ι) → Ideal (F.obj i)}
    (I : Ideal C.pt) (h : I = ⨆ (i : ι), ((Iι i).map (C.ι.app i).hom : Ideal C.pt)) :
    (zeroLocus I : Set (PrimeSpectrum C.pt)) =
      ⋂ (i : ι), (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i : Set (F.obj i))) := by
  ext p
  simp only [Set.mem_iInter, Set.mem_preimage]
  refine ⟨fun hIp i ↦ ?_, fun hall ↦ ?_⟩
  · rw [PrimeSpectrum.mem_zeroLocus] at hIp ⊢
    calc (Iι i : Set (F.obj i))
        ⊆ (Ideal.comap (C.ι.app i).hom ((Iι i).map (C.ι.app i).hom) : Set (F.obj i)) :=
          Ideal.le_comap_map
      _ ⊆ (Ideal.comap (C.ι.app i).hom I : Set (F.obj i)) := by
          refine Ideal.comap_mono ?_
          rw [h]
          exact le_iSup (ι := ι) (fun i ↦ ((Iι i).map (C.ι.app i).hom : Ideal C.pt)) i
      _ ⊆ (Ideal.comap (C.ι.app i).hom p.asIdeal : Set (F.obj i)) :=
          Ideal.comap_mono hIp
  · rw [PrimeSpectrum.mem_zeroLocus, h, SetLike.coe_subset_coe]
    refine iSup_le fun i ↦ ?_
    rw [Ideal.map_le_iff_le_comap]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp (hall i)

theorem specComap_preimage_zeroLocus_subset {ι : Type*} [Category ι]
    {F : Functor ι CommRingCat} (C : Cocone F) {i j : ι} (f : i ⟶ j)
    {Iι : (i : ι) → Ideal (F.obj i)} (h : Iι j ≤ (Iι i).map (F.map f).hom) :
    (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i)) ⊆
      (PrimeSpectrum.comap (C.ι.app j).hom) ⁻¹' (zeroLocus (Iι j)) := by
  intro p hp
  rw [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus] at hp ⊢
  have nat : (C.ι.app i).hom = (C.ι.app j).hom.comp (F.map f).hom := by
    have hnat := C.ι.naturality f
    simp only [Functor.const_obj_map] at hnat
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom hnat.symm
  calc (Iι j : Set (F.obj j))
      ⊆ ((Iι i).map (F.map f).hom : Set (F.obj j)) := h
    _ ⊆ (Ideal.comap (C.ι.app j).hom p.asIdeal : Set (F.obj j)) := by
        rw [SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← nat,
          ← SetLike.coe_subset_coe]
        exact hp
