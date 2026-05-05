/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.StalkAlgebraic
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

variable {A B : Type u} [CommRing A] [CommRing B] (I :Ideal A)

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
  constructor
  · -- If q ∈ zeroLocus (I.map f), then comap f q ∈ zeroLocus I, hence closed by hI
    intro hmem
    have h1 : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈ zeroLocus I := by
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.mp ((mem_zeroLocus _ _).mp hmem)
    exact mem_closedPoints_iff.mp (hI h1)
  · -- If comap f q is closed, use generalizationHull to find it in zeroLocus I
    intro hclosed
    have hq_in_range : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈
        generalizationHull (zeroLocus I) := hRange ▸ Set.mem_range_self q
    rw [mem_generalizationHull_iff] at hq_in_range
    obtain ⟨y, hy, hspec⟩ := hq_in_range
    -- Since {comap f q} is closed and comap f q ⤳ y, we get y = comap f q
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

noncomputable instance algebraWLocalization: Algebra (WLocalization A) I.WLocalization :=
  fast_instance% inferInstanceAs <| Algebra (WLocalization A) <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebra : Algebra A I.WLocalization :=
  Algebra.compHom _ (algebraMap A (WLocalization A))

instance isScalarTower : IsScalarTower A (WLocalization A) I.WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

instance indZariski : Algebra.IndZariski A I.WLocalization := by
  haveI h1 : Algebra.IndZariski A (WLocalization A) := inferInstance
  haveI h2 : Algebra.IndZariski (WLocalization A) I.WLocalization :=
    inferInstanceAs (Algebra.IndZariski (WLocalization A)
      (Generalization 1 (I.map (algebraMap A (WLocalization A)))))
  exact Algebra.IndZariski.trans (R := A) (S := WLocalization A) (T := I.WLocalization)

theorem zeroLocus_map_algebraMap_eq_closedPoints
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A I.WLocalization)) =
    closedPoints (PrimeSpectrum I.WLocalization) := by
  -- I.WLocalization = Generalization 1 (I.map (algebraMap A (WLocalization A)))
  -- Step 1: zeroLocus(I.map(A→WLocalization A)) ⊆ closedPoints(Spec(WLocalization A))
  -- This follows from IndZariski (hence algebraic residue fields) and hI
  -- V(I.map(A→WLocA)) ⊆ closedPoints(Spec(WLocA)) follows from IndZariski ⟹ bijectiveOnStalks
  -- ⟹ residue field extensions are algebraic. Depends on sorry'd upstream lemmas.
  have hJ : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
            closedPoints (PrimeSpectrum (WLocalization A)) :=
    zeroLocus_map_algebraMap_subset_closedPoints (fun m q _ _ _ => sorry) hI
  -- Step 2: Rewrite I.map(A→I.WLocalization) = (I.map(A→WLocalization A)).map(WLocalization A→I.WLocalization)
  have hrw : I.map (algebraMap A I.WLocalization) =
      (I.map (algebraMap A (WLocalization A))).map (algebraMap (WLocalization A) I.WLocalization) := by
    rw [IsScalarTower.algebraMap_eq A (WLocalization A) I.WLocalization, Ideal.map_map]
  rw [hrw]
  -- Step 3: Apply IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq
  haveI : IsWLocalRing (WLocalization A) := inferInstance
  exact IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq hJ

-- Helper: the image of J = I.map(A→WLocA) in Generalization 1 J equals the ideal Generalization.ideal 1 J.
-- Proof: ker(toLocQuotient 1 J) = J.map(algebraMap WLocA (Gen 1 J)) using mk'_mem_map_algebraMap_iff.
-- The key: ker(algebraMap WLocA (Localization.Away(1))) = J (since Away(1) ≅ WLocA/J by atUnits).
private lemma Generalization.ideal_eq_map_of_submonoid (J : Ideal (WLocalization A)) :
    Generalization.ideal 1 J =
    J.map (algebraMap (WLocalization A) (Generalization 1 J)) := by
  -- The target of toLocQuotient is Localization.Away(Ideal.Quotient.mk J 1) where Quotient.mk J 1 = 1.
  -- So WLocA/J → Localization.Away(1) is an isomorphism (atUnits), hence
  -- ker(WLocA → Localization.Away(1)) = ker(WLocA → WLocA/J) = J.
  have hker_away : RingHom.ker (algebraMap (WLocalization A)
      (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))) = J := by
    have h1 : Ideal.Quotient.mk J (1 : WLocalization A) = (1 : WLocalization A ⧸ J) := map_one _
    have hinj : Function.Injective (algebraMap (WLocalization A ⧸ J)
        (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))) := by
      apply (IsLocalization.atUnits (WLocalization A ⧸ J)
        (Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)))
        (S := Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) _).injective
      rintro x ⟨n, rfl⟩
      simp [h1]
    rw [show algebraMap (WLocalization A)
        (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) =
        (algebraMap (WLocalization A ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))).comp
        (Ideal.Quotient.mk J) from IsScalarTower.algebraMap_eq
          (WLocalization A) (WLocalization A ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))]
    rw [RingHom.ker_comp_of_injective _ hinj]
    exact Ideal.mk_ker
  ext x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (Generalization.submonoid 1 J) x
  rw [Generalization.ideal, RingHom.mem_ker, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Generalization.toLocQuotient, IsLocalization.coe_liftAlgHom,
    IsLocalization.lift_mk'_spec, mul_zero]
  -- Goal: algebraMap WLocA (Localization.Away (Quotient.mk J 1)) r = 0
  --       ↔ ∃ m ∈ Generalization.submonoid 1 J, m * r ∈ J
  constructor
  · intro hr
    -- f(r) = 0 → r ∈ ker(f) = J → take m = 1
    have hrJ : r ∈ J := hker_away ▸ hr
    exact ⟨1, Submonoid.one_mem _, by simpa⟩
  · intro ⟨m, hm, hmr⟩
    -- f(m) is a unit (m ∈ submonoid 1 J), f(m*r) = 0 (m*r ∈ J = ker f) → f(r) = 0
    have hfm : IsUnit (algebraMap (WLocalization A)
        (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) m) :=
      Submonoid.mem_comap.mp hm
    have hfmr : algebraMap (WLocalization A)
        (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) (m * r) = 0 := by
      have : m * r ∈ RingHom.ker (algebraMap (WLocalization A)
          (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))) := hker_away.symm ▸ hmr
      exact this
    rw [map_mul] at hfmr
    exact hfm.mul_left_cancel (by simp [hfmr])

variable (I) in
@[stacks 097A "(2)(a)"]
theorem quotientMap_algebraMap_bijective :
    Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  -- The key: A/I ≅ I.WLocalization / I.map(A→I.WLocalization)
  -- This follows from:
  -- (a) I.map(A→I.WLocalization) = J.map(WLocA→I.WLocalization) = ideal 1 J
  --     (where J = I.map(A→WLocA))
  -- (b) I.WLocalization / ideal 1 J ≅ WLocA/J
  --     (IsLocalization.atUnits applied to submonoid 1 J becoming units in WLocA/J)
  -- (c) A/I ≅ WLocA/J (from faithfully flat A→WLocA, sorry)
  sorry

variable (I) in
theorem bijOn_zeroLocus_map : Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
    (zeroLocus (I.map (algebraMap A I.WLocalization))) (zeroLocus I) := by
    rw [← mk_ker (I := I.map _)]
    conv =>
      enter [3, 1, 1]
      rw [← mk_ker (I := I)]
    rw [← range_comap_of_surjective _ _ Quotient.mk_surjective,
      ← range_comap_of_surjective _ _ Quotient.mk_surjective,
      ← Set.image_univ, ← Set.image_univ]
    apply Set.bijOn_image_image
        (f := PrimeSpectrum.comap (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map))
    · intro
      ext1
      simp only [comap_asIdeal, comap_comap, Quotient.mk_comp_algebraMap]
      congr 1
    · rw [Set.bijOn_univ]
      exact (PrimeSpectrum.comapEquiv (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective I))).symm.bijective
    · apply Set.InjOn.image_of_comp
      rw [Set.injOn_univ, ← PrimeSpectrum.comap_comp]
      apply PrimeSpectrum.comap_injective_of_surjective
      rw [← Ideal.quotientMap_comp_mk I.le_comap_map]
      simp
      apply Function.Surjective.comp
      · exact (quotientMap_algebraMap_bijective I).surjective
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
  set J := I.map (algebraMap A B) with hJ_def
  have hJ_sub : zeroLocus J ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h (hI ▸ le_refl _)
  have hrw : I.map (algebraMap A J.WLocalization) = J.map (algebraMap B J.WLocalization) := by
    rw [IsScalarTower.algebraMap_eq A B J.WLocalization, Ideal.map_map]
  rw [hrw]
  exact zeroLocus_map_algebraMap_eq_closedPoints hJ_sub

theorem faithfullyFlat_map_algebraMap [IsWLocalRing A] [Algebra A B] [Module.FaithfullyFlat A B]
  (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) :
  Module.FaithfullyFlat A (I.map (algebraMap A B)).WLocalization := by
  have : Module.Flat A (I.map (algebraMap A B)).WLocalization :=
    Module.Flat.trans A B (I.map (algebraMap A B)).WLocalization
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
      rw [(bijOn_zeroLocus_map (map (algebraMap A B) I)).image_eq]
      exact hp
    _ ⊆ _ := by
      rw [← Set.image_comp, ← comap_comp]
      exact Set.image_subset_range _ _

end Ideal.WLocalization
