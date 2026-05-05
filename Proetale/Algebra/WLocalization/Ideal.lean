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

instance isLocalization :
    IsLocalization (Generalization.submonoid 1 (I.map (algebraMap A (WLocalization A))))
      I.WLocalization :=
  inferInstanceAs <| IsLocalization _ <|
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
  -- IndZariski → IndEtale → residue field extensions are separable, hence algebraic.
  have hJ : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
            closedPoints (PrimeSpectrum (WLocalization A)) :=
    zeroLocus_map_algebraMap_subset_closedPoints (fun m q _ _ _ => by
      haveI : Algebra.IsSeparable m.ResidueField q.ResidueField :=
        Algebra.IndEtale.isSeparable_residueField (R := A) (S := WLocalization A) m q
      infer_instance) hI
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
theorem quotientMap_algebraMap_bijective
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  set J := I.map (algebraMap A (WLocalization A)) with hJ_def
  -- Step (a): I.map(A→I.WLocalization) = J.map(WLocA→I.WLocalization)
  have hKJ : I.map (algebraMap A I.WLocalization) =
      J.map (algebraMap (WLocalization A) I.WLocalization) := by
    rw [hJ_def, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- Step (c): α : A/I → WLocA/J bijective (sorry'd helper)
  have hα := WLocalization.quotientMap_algebraMap_bijective_of_ideal (A := A) I hI
  -- The submonoid (Generalization.submonoid 1 J) maps to units in WLocA/J:
  -- m ∈ submonoid 1 J means image of m in Localization.Away (mk J 1) is a unit.
  -- Since mk J 1 = 1, Loc.Away (1 : WLocA/J) ≃ WLocA/J via atUnits, so mk J m is a unit.
  have h1 : Ideal.Quotient.mk J (1 : WLocalization A) = (1 : WLocalization A ⧸ J) := map_one _
  haveI hpow : Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)) ≤
      IsUnit.submonoid (WLocalization A ⧸ J) := by
    rintro x ⟨n, rfl⟩; simp [h1]
  have hLocAway_bij : Function.Bijective
      (algebraMap (WLocalization A ⧸ J)
        (Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A)))) :=
    (IsLocalization.atUnits (WLocalization A ⧸ J)
      (Submonoid.powers (Ideal.Quotient.mk J (1 : WLocalization A)))
      (S := Localization.Away (Ideal.Quotient.mk J (1 : WLocalization A))) hpow).bijective
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
        (Ideal.Quotient.mk J (1 : WLocalization A))) m = e (Ideal.Quotient.mk J m) := by
      show algebraMap (WLocalization A) _ m =
        algebraMap (WLocalization A ⧸ J) _ (Ideal.Quotient.mk J m)
      rw [show (Ideal.Quotient.mk J m : WLocalization A ⧸ J) =
        algebraMap (WLocalization A) (WLocalization A ⧸ J) m from rfl,
        ← IsScalarTower.algebraMap_apply]
    rw [heq] at hu
    have := hu.map e.symm.toRingHom
    rwa [show e.symm.toRingHom (e (Ideal.Quotient.mk J m)) = Ideal.Quotient.mk J m from
      e.symm_apply_apply _] at this
  -- Step (b): β : WLocA/J → I.WLocalization/(J.map(WLocA→I.WLocalization)) bijective
  have hβ : Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap (WLocalization A) I.WLocalization))
      (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map) := by
    refine ⟨?_, ?_⟩
    · -- Injective
      intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem,
        ← map_sub (algebraMap (WLocalization A) I.WLocalization),
        IsLocalization.algebraMap_mem_map_algebraMap_iff (Generalization.submonoid 1 J)] at hxy
      obtain ⟨m, hm, hmem⟩ := hxy
      have hu := hsub_unit m hm
      have : Ideal.Quotient.mk J m * Ideal.Quotient.mk J (x - y) = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
      have : Ideal.Quotient.mk J (x - y) = 0 := by
        rcases hu with ⟨u, hu⟩
        rw [← hu] at this
        exact (Units.mul_right_eq_zero u).mp this
      rw [map_sub, sub_eq_zero] at this
      exact this
    · -- Surjective
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hrs⟩ := IsLocalization.surj (Generalization.submonoid 1 J) y
      set r := x.1
      set s := x.2.1 with hs_def
      have hs : s ∈ Generalization.submonoid 1 J := x.2.2
      -- y * algebraMap s = algebraMap r, with s ∈ submonoid 1 J
      -- mk J s is a unit; let v be its inverse in WLocA/J
      obtain ⟨u, hueq⟩ := hsub_unit s hs
      -- We claim [algebraMap WLocA I.WLocalization r] / [algebraMap WLocA I.WLocalization s] = [y]
      -- and that quotient is in the image of WLocA/J via algebraMap (mk J r * (mk J s)⁻¹)
      obtain ⟨t, ht⟩ : ∃ t : WLocalization A, Ideal.Quotient.mk J (s * t - 1) = 0 := by
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : WLocalization A ⧸ J)
        refine ⟨t, ?_⟩
        rw [map_sub, map_mul, ht, ← hueq, map_one, Units.mul_inv, sub_self]
      rw [Ideal.Quotient.eq_zero_iff_mem] at ht
      refine ⟨Ideal.Quotient.mk J (r * t), ?_⟩
      rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      -- Goal: algebraMap (r*t) - y ∈ J.map(WLocA → I.WLocalization)
      have hu_s : IsUnit (algebraMap (WLocalization A) I.WLocalization s) :=
        IsLocalization.map_units I.WLocalization (⟨s, hs⟩ : Generalization.submonoid 1 J)
      rw [← Ideal.unit_mul_mem_iff_mem _ hu_s]
      have key : algebraMap (WLocalization A) I.WLocalization s *
          (algebraMap (WLocalization A) I.WLocalization (r * t) - y) =
          algebraMap (WLocalization A) I.WLocalization (r * (s * t - 1)) := by
        have hy : y * algebraMap (WLocalization A) I.WLocalization s =
            algebraMap (WLocalization A) I.WLocalization r := hrs
        rw [mul_sub, mul_comm _ y, hy, ← map_mul, ← map_sub]
        congr 1
        ring
      rw [key]
      exact Ideal.mem_map_of_mem _ (J.mul_mem_left _ ht)
  -- Compose α and β. Need to identify the codomain via hKJ.
  have hφbij : Function.Bijective (Ideal.quotEquivOfEq hKJ.symm :
      I.WLocalization ⧸ J.map (algebraMap (WLocalization A) I.WLocalization) ≃+*
      I.WLocalization ⧸ I.map (algebraMap A I.WLocalization)) :=
    (Ideal.quotEquivOfEq hKJ.symm).bijective
  have hcomp_eq : (Ideal.quotientMap (I.map (algebraMap A I.WLocalization))
      (algebraMap A I.WLocalization) I.le_comap_map) =
      (Ideal.quotEquivOfEq hKJ.symm).toRingHom.comp ((Ideal.quotientMap _
        (algebraMap (WLocalization A) I.WLocalization) Ideal.le_comap_map).comp
        (Ideal.quotientMap J (algebraMap A (WLocalization A)) I.le_comap_map)) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    show Ideal.Quotient.mk (I.map (algebraMap A I.WLocalization))
        (algebraMap A I.WLocalization a) =
      (Ideal.quotEquivOfEq hKJ.symm) (Ideal.Quotient.mk _
        (algebraMap (WLocalization A) I.WLocalization
          (algebraMap A (WLocalization A) a)))
    rw [Ideal.quotEquivOfEq_mk,
      IsScalarTower.algebraMap_apply A (WLocalization A) I.WLocalization]
  rw [hcomp_eq]
  exact hφbij.comp (hβ.comp hα)

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
    apply Set.bijOn_image_image
        (f := PrimeSpectrum.comap (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map))
    · intro
      ext1
      simp only [comap_asIdeal, comap_comap, Quotient.mk_comp_algebraMap]
      congr 1
    · rw [Set.bijOn_univ]
      exact (PrimeSpectrum.comapEquiv (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective I hI))).symm.bijective
    · apply Set.InjOn.image_of_comp
      rw [Set.injOn_univ, ← PrimeSpectrum.comap_comp]
      apply PrimeSpectrum.comap_injective_of_surjective
      rw [← Ideal.quotientMap_comp_mk I.le_comap_map]
      simp
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
  set J := I.map (algebraMap A B) with hJ_def
  have hJ_sub : zeroLocus J ⊆ closedPoints (PrimeSpectrum B) :=
    zeroLocus_map_algebraMap_subset_closedPoints h (hI ▸ le_refl _)
  have hrw : I.map (algebraMap A J.WLocalization) = J.map (algebraMap B J.WLocalization) := by
    rw [IsScalarTower.algebraMap_eq A B J.WLocalization, Ideal.map_map]
  rw [hrw]
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
