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
      ⋂ (i : ι), (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i : Set (F.obj i))) := by
  ext p
  simp only [Set.mem_iInter, Set.mem_preimage]
  constructor
  · -- ⊆ direction: if p ∈ V(I), then for each i, comap(ι_i) p ∈ V(Iι i)
    intro hIp i
    rw [PrimeSpectrum.mem_zeroLocus] at hIp ⊢
    -- Goal: (Iι i : Set (F.obj i)) ⊆ (comap (C.ι.app i).hom p).asIdeal
    -- This means: ∀ a ∈ Iι i, a ∈ Ideal.comap (C.ι.app i).hom p.asIdeal
    -- i.e., ∀ a ∈ Iι i, (C.ι.app i).hom a ∈ p.asIdeal
    -- Since (Iι i).map (C.ι.app i).hom ≤ I ≤ p, this follows.
    calc (Iι i : Set (F.obj i))
        ⊆ (Ideal.comap (C.ι.app i).hom ((Iι i).map (C.ι.app i).hom) : Set (F.obj i)) :=
          Ideal.le_comap_map
      _ ⊆ (Ideal.comap (C.ι.app i).hom I : Set (F.obj i)) := by
          apply Ideal.comap_mono
          rw [h]
          exact @le_iSup (Ideal C.pt) _ _ (fun i => (Iι i).map (C.ι.app i).hom) i
      _ ⊆ (Ideal.comap (C.ι.app i).hom p.asIdeal : Set (F.obj i)) :=
          Ideal.comap_mono hIp
  · -- ⊇ direction: if for all i, comap(ι_i) p ∈ V(Iι i), then p ∈ V(I)
    intro hall
    rw [PrimeSpectrum.mem_zeroLocus, h, SetLike.coe_subset_coe]
    apply iSup_le
    intro i
    rw [Ideal.map_le_iff_le_comap]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp (hall i)

theorem specComap_preimage_zeroLocus_subset {ι : Type*} [Category ι]
    {F : Functor ι CommRingCat} (C : Cocone F) {i j : ι} (f : i ⟶ j)
    {Iι : (i : ι) → Ideal (F.obj i)} (h : Iι j ≤ (Iι i).map (F.map f).hom) :
    (PrimeSpectrum.comap (C.ι.app i).hom) ⁻¹' (zeroLocus (Iι i)) ⊆
      (PrimeSpectrum.comap (C.ι.app j).hom) ⁻¹' (zeroLocus (Iι j)):=
  -- Blueprint: thm:colim-ideal-lim-zero-locus. Monotonicity of preimage under transition maps.
  sorry
