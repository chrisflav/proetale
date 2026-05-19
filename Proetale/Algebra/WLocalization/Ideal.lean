/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Separable
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.StalkAlgebraic
import Proetale.Algebra.IndEtale
import Proetale.Mathlib.RingTheory.Ideal.GoingDown

/-!
# w-localization w.r.t an ideal

In this file, we define the w-localization w.r.t an ideal and prove [Tag 097A, Stacks Project].

Let `A` be a w-local ring. Let `I ⊆ A` be an ideal cutting out the set `X^c` of closed points
in `X = Spec(A)`. Let `A → B` be a ring map inducing algebraic extensions on residue fields at
primes. Then there exists an ind-Zariski ring map `B → C` such that

- `B/IB → C/IC` is an isomorphism,
- `C` is w-local
- the map `p : Y = Spec C → X` induced by the ring map `A → B → C` is w-local, and
- `p⁻¹(X^c)` is the set of closed points of `Y`.

In particular, the composition `A → B → C` is faithfully flat if `A → B` is faithfully flat.
-/

universe u

open WLocalization PrimeSpectrum

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A)

instance isWLocalRing_generalization_one [IsWLocalRing A] : IsWLocalRing (Generalization 1 I) := by
  haveI : WLocalSpace (PrimeSpectrum A) := IsWLocalRing.wLocalSpace_primeSepectrum
  rw [isWLocalRing_iff]
  apply Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range
      (f := PrimeSpectrum.comap (algebraMap A (Generalization 1 I)))
  · exact PrimeSpectrum.localization_comap_isEmbedding (Generalization 1 I)
      (Generalization.submonoid 1 I)
  · rw [Generalization.range_algebraMap_generalization]
    apply StableUnderSpecialization.generalizationHull_of_wLocalSpace
    have hlocClosed : Generalization.locClosedSubset 1 I = zeroLocus I := by
      simp [Generalization.locClosedSubset, PrimeSpectrum.basicOpen_one]
    rw [hlocClosed]
    exact (PrimeSpectrum.isClosed_zeroLocus (↑I : Set A)).stableUnderSpecialization

variable {I}

theorem IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq [IsWLocalRing A]
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A (Generalization 1 I))) =
    closedPoints (PrimeSpectrum (Generalization 1 I)) := by
  haveI : WLocalSpace (PrimeSpectrum A) := IsWLocalRing.wLocalSpace_primeSepectrum
  have hEmb : Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) :=
    PrimeSpectrum.localization_comap_isEmbedding _ (Generalization.submonoid 1 I)
  have hlocClosed : Generalization.locClosedSubset 1 I = zeroLocus I := by
    simp [Generalization.locClosedSubset, PrimeSpectrum.basicOpen_one]
  have hRange : Set.range (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) =
                generalizationHull (zeroLocus I) := by
    rw [← hlocClosed]; exact Generalization.range_algebraMap_generalization 1 I
  have hStable : StableUnderSpecialization (Set.range
      (PrimeSpectrum.comap (algebraMap A (Generalization 1 I)))) := by
    rw [hRange]
    exact StableUnderSpecialization.generalizationHull_of_wLocalSpace
      (PrimeSpectrum.isClosed_zeroLocus (↑I : Set A)).stableUnderSpecialization
  rw [hEmb.closedPoints_eq_preimage hStable]
  ext q
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  refine ⟨fun hmem ↦ ?_, fun hclosed ↦ ?_⟩
  · have h1 : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈ zeroLocus I := by
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.mp ((mem_zeroLocus _ _).mp hmem)
    exact mem_closedPoints_iff.mp (hI h1)
  · have hq_in_range : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈
        generalizationHull (zeroLocus I) := hRange ▸ Set.mem_range_self q
    rw [mem_generalizationHull_iff] at hq_in_range
    obtain ⟨y, hy, hspec⟩ := hq_in_range
    have heq : y = PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q :=
      Set.mem_singleton_iff.mp (hspec.mem_closed hclosed (Set.mem_singleton _))
    simp only [mem_zeroLocus, SetLike.coe_subset_coe]
    rw [Ideal.map_le_iff_le_comap]
    have hy' := (mem_zeroLocus _ _).mp hy
    rwa [heq, comap_asIdeal, SetLike.coe_subset_coe] at hy'

theorem zeroLocus_map_algebraMap_subset_closedPoints [Algebra A B]
    (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime],
    Algebra.IsAlgebraic m.ResidueField q.ResidueField)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) := by
  intro q hq
  simp only [mem_zeroLocus, SetLike.coe_subset_coe, mem_closedPoints_iff,
    isClosed_singleton_iff_isMaximal] at ⊢ hq
  set m := comap (algebraMap A B) q with hm_def
  have hm : m.asIdeal.IsMaximal := by
    simpa [isClosed_singleton_iff_isMaximal] using hI (Ideal.le_comap_of_map_le hq)
  have : q.asIdeal.LiesOver m.asIdeal := ⟨PrimeSpectrum.ext_iff.mp hm_def⟩
  have := h m.asIdeal q.asIdeal
  exact Ideal.IsMaximal.of_isAlgebraic m.asIdeal q.asIdeal

variable (I) in
/--
The w-localization with respect to an ideal `I`.
-/
protected def Ideal.WLocalization : Type u :=
  Generalization 1 (I.map (algebraMap A (WLocalization A)))

namespace Ideal.WLocalization

noncomputable instance commRing : CommRing I.WLocalization := fast_instance%
  inferInstanceAs <| CommRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isWLocalRing : IsWLocalRing I.WLocalization :=
  inferInstanceAs <| IsWLocalRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebraWLocalization : Algebra (WLocalization A) I.WLocalization :=
  fast_instance% inferInstanceAs <| Algebra (WLocalization A) <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isLocalization :
    IsLocalization (Generalization.submonoid 1 (I.map (algebraMap A (WLocalization A))))
      I.WLocalization :=
  inferInstanceAs <| IsLocalization _ <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebra : Algebra A I.WLocalization :=
  Algebra.compHom _ (algebraMap A (WLocalization A))

instance isScalarTower : IsScalarTower A (WLocalization A) I.WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

instance indZariski : Algebra.IndZariski A I.WLocalization :=
  have : Algebra.IndZariski (WLocalization A) I.WLocalization :=
    inferInstanceAs (Algebra.IndZariski (WLocalization A)
      (Generalization 1 (I.map (algebraMap A (WLocalization A)))))
  Algebra.IndZariski.trans (R := A) (S := WLocalization A) (T := I.WLocalization)

theorem zeroLocus_map_algebraMap_eq_closedPoints
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A I.WLocalization)) =
    closedPoints (PrimeSpectrum I.WLocalization) := by
  have hJ : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
      closedPoints (PrimeSpectrum (WLocalization A)) :=
    zeroLocus_map_algebraMap_subset_closedPoints (fun m q _ _ _ ↦ by
      haveI : Algebra.IsSeparable m.ResidueField q.ResidueField :=
        Algebra.IndEtale.isSeparable_residueField (R := A) (S := WLocalization A) m q
      infer_instance) hI
  rw [show I.map (algebraMap A I.WLocalization) = (I.map (algebraMap A (WLocalization A))).map
      (algebraMap (WLocalization A) I.WLocalization) by
    rw [IsScalarTower.algebraMap_eq A (WLocalization A) I.WLocalization, Ideal.map_map]]
  exact IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq hJ

variable (I) in
@[stacks 097A "(2)(a)"]
theorem quotientMap_algebraMap_bijective
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  set J := I.map (algebraMap A (WLocalization A)) with hJ_def
  have hKJ : I.map (algebraMap A I.WLocalization) =
      J.map (algebraMap (WLocalization A) I.WLocalization) := by
    rw [hJ_def, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hα := WLocalization.quotientMap_algebraMap_bijective_of_ideal (A := A) I hI
  -- Since `Ideal.Quotient.mk J 1 = 1`, `WLocalization A ⧸ J → Localization.Away (mk J 1)` is an
  -- isomorphism by `IsLocalization.atUnits`, so elements of `Generalization.submonoid 1 J`,
  -- which are units in the target, are already units in `WLocalization A ⧸ J`.
  have h1 : Ideal.Quotient.mk J (1 : WLocalization A) = (1 : WLocalization A ⧸ J) := map_one _
  have hpow : Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)) ≤
      IsUnit.submonoid (WLocalization A ⧸ J) := by
    rintro x ⟨n, rfl⟩
    simp [h1]
  let e : (WLocalization A ⧸ J) ≃+*
      Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)) :=
    (IsLocalization.atUnits (WLocalization A ⧸ J)
      (Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)))
      (S := Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) hpow).toRingEquiv
  have hsub_unit : ∀ m ∈ Generalization.submonoid 1 J,
      IsUnit (Ideal.Quotient.mk J m) := by
    intro m hm
    have hu : IsUnit (algebraMap (WLocalization A) (Localization.Away
        (Ideal.Quotient.mk J (1 : WLocalization A))) m) := Submonoid.mem_comap.mp hm
    have heq : algebraMap (WLocalization A) (Localization.Away
        (Ideal.Quotient.mk J (1 : WLocalization A))) m = e (Ideal.Quotient.mk J m) :=
      IsScalarTower.algebraMap_apply (WLocalization A) (WLocalization A ⧸ J) _ m
    rw [heq] at hu
    simpa using hu.map e.symm.toRingHom
  have hβ : Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap (WLocalization A) I.WLocalization))
      (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem,
        ← map_sub (algebraMap (WLocalization A) I.WLocalization),
        IsLocalization.algebraMap_mem_map_algebraMap_iff (Generalization.submonoid 1 J)] at hxy
      obtain ⟨m, hm, hmem⟩ := hxy
      obtain ⟨u, hu⟩ := hsub_unit m hm
      have hprod : Ideal.Quotient.mk J m * Ideal.Quotient.mk J (x - y) = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hmem
      rw [← hu] at hprod
      have hsub : Ideal.Quotient.mk J (x - y) = 0 := (Units.mul_right_eq_zero u).mp hprod
      rw [map_sub, sub_eq_zero] at hsub
      exact hsub
    · intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hrs⟩ := IsLocalization.surj (Generalization.submonoid 1 J) y
      set r := x.1
      set s := x.2.1
      have hs : s ∈ Generalization.submonoid 1 J := x.2.2
      obtain ⟨u, hueq⟩ := hsub_unit s hs
      obtain ⟨t, ht⟩ : ∃ t : WLocalization A, s * t - 1 ∈ J := by
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : WLocalization A ⧸ J)
        refine ⟨t, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ht, ← hueq, map_one,
          Units.mul_inv, sub_self]
      refine ⟨Ideal.Quotient.mk J (r * t), ?_⟩
      rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      have hu_s : IsUnit (algebraMap (WLocalization A) I.WLocalization s) :=
        IsLocalization.map_units I.WLocalization (⟨s, hs⟩ : Generalization.submonoid 1 J)
      rw [← Ideal.unit_mul_mem_iff_mem _ hu_s]
      have key : algebraMap (WLocalization A) I.WLocalization s *
          (algebraMap (WLocalization A) I.WLocalization (r * t) - y) =
          algebraMap (WLocalization A) I.WLocalization (r * (s * t - 1)) := by
        rw [mul_sub, mul_comm _ y, hrs, ← map_mul, ← map_sub]
        ring_nf
      rw [key]
      exact Ideal.mem_map_of_mem _ (J.mul_mem_left _ ht)
  have hcomp_eq : Ideal.quotientMap (I.map (algebraMap A I.WLocalization))
      (algebraMap A I.WLocalization) I.le_comap_map =
      (Ideal.quotEquivOfEq hKJ.symm).toRingHom.comp ((Ideal.quotientMap _
        (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map).comp
        (Ideal.quotientMap J (algebraMap A (WLocalization A)) I.le_comap_map)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    change Ideal.Quotient.mk (I.map (algebraMap A I.WLocalization))
        (algebraMap A I.WLocalization a) =
      (Ideal.quotEquivOfEq hKJ.symm) (Ideal.Quotient.mk _
        (algebraMap (WLocalization A) I.WLocalization (algebraMap A (WLocalization A) a)))
    rw [Ideal.quotEquivOfEq_mk,
      IsScalarTower.algebraMap_apply A (WLocalization A) I.WLocalization]
  rw [hcomp_eq]
  exact (Ideal.quotEquivOfEq hKJ.symm).bijective.comp (hβ.comp hα)

variable (I) in
theorem bijOn_zeroLocus_map (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
      (zeroLocus (I.map (algebraMap A I.WLocalization))) (zeroLocus I) := by
  rw [← mk_ker (I := I.map _)]
  conv =>
    enter [3, 1, 1]
    rw [← mk_ker (I := I)]
  rw [← range_comap_of_surjective _ _ Quotient.mk_surjective,
    ← range_comap_of_surjective _ _ Quotient.mk_surjective,
    ← Set.image_univ, ← Set.image_univ]
  apply Set.bijOn_image_image (f := PrimeSpectrum.comap
      (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map))
  · intro
    ext1
    simp only [comap_asIdeal, comap_comap, Quotient.mk_comp_algebraMap]
    congr 1
  · rw [Set.bijOn_univ]
    exact (PrimeSpectrum.comapEquiv
      (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective I hI))).symm.bijective
  · apply Set.InjOn.image_of_comp
    rw [Set.injOn_univ, ← PrimeSpectrum.comap_comp]
    apply PrimeSpectrum.comap_injective_of_surjective
    rw [← Ideal.quotientMap_comp_mk I.le_comap_map]
    simp only [RingHom.coe_comp]
    apply Function.Surjective.comp
    · exact (quotientMap_algebraMap_bijective I hI).surjective
    · exact Ideal.Quotient.mk_surjective

noncomputable instance [Algebra A B] : Algebra A (I.map (algebraMap A B)).WLocalization :=
  Algebra.compHom _ (algebraMap A B)

instance [Algebra A B] : IsScalarTower A B (I.map (algebraMap A B)).WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

@[stacks 097A "(2)(d)"]
theorem algebraMap_specComap_preimage_closedPoints_eq [IsWLocalRing A] [Algebra A B]
    (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) (h : ∀ (m : Ideal A) (q : Ideal B)
    [q.LiesOver m] [m.IsMaximal] [q.IsPrime], Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
    zeroLocus (I.map (algebraMap A (I.map (algebraMap A B)).WLocalization)) =
    closedPoints (PrimeSpectrum (I.map (algebraMap A B)).WLocalization) := by
  set J := I.map (algebraMap A B)
  have hJ_sub : zeroLocus J ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h (hI ▸ le_refl _)
  rw [show I.map (algebraMap A J.WLocalization) = J.map (algebraMap B J.WLocalization) by
    rw [IsScalarTower.algebraMap_eq A B J.WLocalization, Ideal.map_map]]
  exact zeroLocus_map_algebraMap_eq_closedPoints hJ_sub

theorem faithfullyFlat_map_algebraMap [IsWLocalRing A] [Algebra A B] [Module.FaithfullyFlat A B]
  (hI : zeroLocus I = closedPoints (PrimeSpectrum A))
  (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime],
    Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
  Module.FaithfullyFlat A (I.map (algebraMap A B)).WLocalization := by
  have : Module.Flat A (I.map (algebraMap A B)).WLocalization :=
    Module.Flat.trans A B (I.map (algebraMap A B)).WLocalization
  have hJ_sub : zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h (hI ▸ le_refl _)
  apply Module.FaithfullyFlat.of_comap_surjective
  apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
  rw [← hI]
  calc
    zeroLocus I ⊆ PrimeSpectrum.comap (algebraMap A B) '' zeroLocus (I.map (algebraMap A B)) := by
      -- This should be separated as a lemma
      intro p hp
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_image] at hp ⊢
      obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat p (B := B)
      refine ⟨q, ?_, hq⟩
      simp only [← hq, comap_asIdeal] at hp
      exact Ideal.map_le_of_le_comap hp
    _ ⊆ PrimeSpectrum.comap (algebraMap A B) ''
        (PrimeSpectrum.comap (algebraMap B (I.map (algebraMap A B)).WLocalization) ''
        zeroLocus (I.map ((algebraMap B (I.map (algebraMap A B)).WLocalization).comp
        (algebraMap A B)))) := by
      apply Set.image_mono
      rw [← Ideal.map_map]
      intro p hp
      rw [(bijOn_zeroLocus_map (map (algebraMap A B) I) hJ_sub).image_eq]
      exact hp
    _ ⊆ _ := by
      rw [← Set.image_comp, ← comap_comp]
      exact Set.image_subset_range _ _

end Ideal.WLocalization
