/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocal
import Proetale.Algebra.IndZariski
import Proetale.Algebra.Preliminaries.Ideal
import Proetale.Algebra.FaithfullyFlat

/-!
# w-localization

In this file we show that every ring admits a faithfully flat, ind-Zariski w-local algebra.
-/

universe u

open CategoryTheory Limits PrimeSpectrum Classical

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

instance indZariski : Algebra.IndZariski A (Generalization f I) := by
  dsimp [Generalization]
  infer_instance

def locClosedSubset (f : A) (I : Ideal A) : Set (PrimeSpectrum A) :=
  basicOpen f ∩ zeroLocus I

-- Helper: if `a ∈ submonoid f I` and `q ∈ locClosedSubset f I`, then `a ∉ q.asIdeal`.
-- This is the forward direction of `mem_submonoid_iff_not_mem_locClosedSubset`, extracted
-- here so it can be used in `range_algebraMap_generalization`.
private lemma submonoid_disjoint_locClosedSubset_primes (f : A) (I : Ideal A) (a : A)
    (ha : a ∈ submonoid f I) (q : PrimeSpectrum A) (hq : q ∈ locClosedSubset f I) :
    a ∉ q.asIdeal := by
  simp only [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff] at ha
  simp only [locClosedSubset, Set.mem_inter_iff] at hq
  obtain ⟨hqf, hqI⟩ := hq
  simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hqf
  rw [PrimeSpectrum.mem_zeroLocus] at hqI
  intro haq
  -- Build the prime q_bar = image of q in A/I, then lift to (A/I)_f
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q.asIdeal := by
    rw [Ideal.mk_ker]; exact hqI
  set q_bar := Ideal.map (Ideal.Quotient.mk I) q.asIdeal
  have hq_prime : q_bar.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hmkf : Ideal.Quotient.mk I f ∉ q_bar := by
    intro hfq
    have hcomap := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q.asIdeal
    rw [show Ideal.comap (Ideal.Quotient.mk I) ⊥ = I from
      RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I) ▸ Ideal.mk_ker] at hcomap
    have hIq : I ≤ q.asIdeal := hqI
    exact hqf (sup_eq_left.mpr hIq ▸ (hcomap ▸ Ideal.mem_comap.mpr hfq))
  have hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk I f) : Set (A ⧸ I))
      (q_bar : Set (A ⧸ I)) :=
    Set.disjoint_left.mpr fun y hy1 hy2 => by
      simp only [SetLike.mem_coe, Submonoid.mem_powers_iff] at hy1
      obtain ⟨n, hn⟩ := hy1
      rw [← hn] at hy2
      exact hmkf (hq_prime.mem_of_pow_mem n hy2)
  have hq_loc : (Ideal.map (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f)))
      q_bar).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ q_bar hq_prime hdisj
  apply hq_loc.ne_top
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ haq))
    (by rw [IsScalarTower.algebraMap_apply A (A ⧸ I)] at ha; exact ha)

/-- The image of `Spec (Generalization f I)` in `Spec A` is equal to
the generalization hull of `D(f) ∩ V(I)`. -/
lemma range_algebraMap_generalization (f : A) (I : Ideal A) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) =
    generalizationHull (locClosedSubset f I) := by
  rw [PrimeSpectrum.localization_comap_range (Generalization f I) (submonoid f I)]
  ext p
  simp only [Set.mem_setOf_eq]
  rw [mem_generalizationHull_iff]
  constructor
  · -- If Disjoint (submonoid f I) p.asIdeal, find q ∈ locClosedSubset f I with p ⤳ q
    intro hdisj
    -- Key claim: f ∉ radical (p.asIdeal ⊔ I)
    have hf_not_rad : f ∉ Ideal.radical (p.asIdeal ⊔ I) := by
      rw [Ideal.mem_radical_iff]
      push_neg
      intro n
      intro hfn
      -- f^n ∈ p.asIdeal ⊔ I means f^n = a + b with a ∈ p, b ∈ I
      rw [Submodule.mem_sup] at hfn
      obtain ⟨a, ha, b, hb, hab⟩ := hfn
      -- In (A/I)_f, image of a equals image of f^n (a unit), so a ∈ submonoid f I
      have ha_sub : a ∈ submonoid f I := by
        rw [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        rw [IsScalarTower.algebraMap_apply A (A ⧸ I)]
        have h_eq : (algebraMap A (A ⧸ I)) a = (algebraMap A (A ⧸ I)) (f ^ n) := by
          have hmem : a - f ^ n ∈ I := by
            have : a - f ^ n = -b := by linear_combination hab
            rw [this]; exact I.neg_mem hb
          rwa [← Ideal.Quotient.eq] at hmem
        rw [h_eq]
        -- Goal: IsUnit (algebraMap (A ⧸ I) (Localization.Away (mk I f)) (mk I f ^ n))
        -- mk I f ^ n is in Submonoid.powers (mk I f), so its image is a unit
        have hmem : (Ideal.Quotient.mk I f) ^ n ∈ Submonoid.powers (Ideal.Quotient.mk I f) :=
          ⟨n, rfl⟩
        exact IsLocalization.map_units (Localization.Away (Ideal.Quotient.mk I f)) ⟨_, hmem⟩
      -- But a ∈ p.asIdeal ∩ submonoid f I, contradicting disjointness
      exact Set.disjoint_left.mp hdisj ha_sub ha
    -- Since f ∉ radical(p ⊔ I), there exists a prime q ⊇ p ⊔ I with f ∉ q
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf] at hf_not_rad
    push_neg at hf_not_rad
    obtain ⟨q, ⟨hle, hq_prime⟩, hfq⟩ := hf_not_rad
    refine ⟨⟨q, hq_prime⟩, ?_, ?_⟩
    · -- q ∈ locClosedSubset f I
      constructor
      · simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]; exact hfq
      · rw [PrimeSpectrum.mem_zeroLocus]
        intro x hx
        exact hle (Ideal.mem_sup_right hx)
    · -- p ⤳ q, i.e., p.asIdeal ≤ q
      rw [← PrimeSpectrum.le_iff_specializes]
      show p.asIdeal ≤ q
      intro x hx
      exact hle (Ideal.mem_sup_left hx)
  · -- If ∃ q ∈ locClosedSubset, p ⤳ q, then Disjoint
    rintro ⟨q, hq, hpq⟩
    rw [← PrimeSpectrum.le_iff_specializes] at hpq
    refine Set.disjoint_left.mpr fun a ha_sub ha_p => ?_
    exact submonoid_disjoint_locClosedSubset_primes f I a ha_sub q hq (hpq ha_p)

lemma bijOn_algebraMap_generalization_specComap_zeroLocus_ideal (f : A) (I : Ideal A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) (zeroLocus (ideal f I))
    (locClosedSubset f I) := by
  refine ⟨?mapsTo, ?injOn, ?surjOn⟩
  case mapsTo =>
    intro y hy
    set q := PrimeSpectrum.comap (algebraMap A (Generalization f I)) y
    rw [PrimeSpectrum.mem_zeroLocus] at hy
    constructor
    · -- f ∉ q.asIdeal
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      intro hfq
      have hf_sub : f ∈ submonoid f I := by
        rw [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        rw [IsScalarTower.algebraMap_apply A (A ⧸ I)]
        have hmem : Ideal.Quotient.mk I f ∈ Submonoid.powers (Ideal.Quotient.mk I f) :=
          ⟨1, pow_one _⟩
        exact IsLocalization.map_units _ ⟨_, hmem⟩
      have hdisj : Disjoint (submonoid f I : Set A) (q.asIdeal : Set A) := by
        have hq_range : q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Generalization f I))) :=
          ⟨y, rfl⟩
        rwa [PrimeSpectrum.localization_comap_range (Generalization f I) (submonoid f I)] at hq_range
      exact Set.disjoint_left.mp hdisj hf_sub hfq
    · -- I ⊆ q.asIdeal
      rw [PrimeSpectrum.mem_zeroLocus]
      intro a ha
      show algebraMap A (Generalization f I) a ∈ y.asIdeal
      apply hy
      simp only [ideal, SetLike.mem_coe, RingHom.mem_ker]
      show (toLocQuotient f I) (algebraMap A (Generalization f I) a) = 0
      rw [(toLocQuotient f I).commutes]
      rw [IsScalarTower.algebraMap_apply A (A ⧸ I)]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  case injOn =>
    exact (PrimeSpectrum.localization_comap_isEmbedding (Generalization f I)
      (submonoid f I)).injective.injOn
  case surjOn =>
    intro q hq
    have hq_disj : Disjoint (submonoid f I : Set A) (q.asIdeal : Set A) :=
      Set.disjoint_left.mpr fun a ha ha_q =>
        submonoid_disjoint_locClosedSubset_primes f I a ha q hq ha_q
    set q_map := Ideal.map (algebraMap A (Generalization f I)) q.asIdeal
    have hq_map_prime : q_map.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (submonoid f I) (Generalization f I)
        q.asIdeal q.isPrime hq_disj
    set y : PrimeSpectrum (Generalization f I) := ⟨q_map, hq_map_prime⟩
    have hy_comap : PrimeSpectrum.comap (algebraMap A (Generalization f I)) y = q :=
      PrimeSpectrum.ext (IsLocalization.comap_map_of_isPrime_disjoint (submonoid f I)
        (Generalization f I) q.isPrime hq_disj)
    refine ⟨y, ?_, hy_comap⟩
    -- y ∈ V(ideal f I): same argument as in exists_specializes_zeroLocus_ideal
    rw [PrimeSpectrum.mem_zeroLocus]
    intro z hz_mem
    simp only [ideal, SetLike.mem_coe, RingHom.mem_ker] at hz_mem
    obtain ⟨a, s, hzas⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
    rw [← hzas] at hz_mem ⊢
    have hz' : algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a = 0 := by
      have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
      have h4 : (toLocQuotient f I) (IsLocalization.mk' (Generalization f I) a s *
          algebraMap A (Generalization f I) (s : A)) =
        (toLocQuotient f I) (algebraMap A (Generalization f I) a) := congr_arg _ h3
      rw [map_mul, hz_mem, zero_mul, (toLocQuotient f I).commutes] at h4
      exact h4.symm
    have ha_q : a ∈ q.asIdeal := by
      have hqI : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hq.2
      have hfq : f ∉ q.asIdeal := by
        simp only [locClosedSubset, Set.mem_inter_iff] at hq; exact hq.1
      set a_bar := Ideal.Quotient.mk I a
      set f_bar := Ideal.Quotient.mk I f
      have hz_factor : algebraMap (A ⧸ I) (Localization.Away f_bar) a_bar = 0 := by
        have := IsScalarTower.algebraMap_apply A (A ⧸ I) (Localization.Away f_bar) a
        rw [this] at hz'; exact hz'
      have ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f_bar)
        (Localization.Away f_bar) a_bar).mp hz_factor
      obtain ⟨c_val, n, hn⟩ := c; subst hn
      have hfna : f ^ n * a ∈ I := by
        have : Ideal.Quotient.mk I (f ^ n * a) = 0 := by rw [map_mul, map_pow]; exact hc
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have hfnq : f ^ n ∉ q.asIdeal := mt (q.isPrime.mem_of_pow_mem n) hfq
      exact (q.isPrime.mem_or_mem (hqI hfna)).resolve_left hfnq
    show IsLocalization.mk' (Generalization f I) a s ∈ q_map
    rw [IsLocalization.mk'_mem_map_algebraMap_iff (submonoid f I)]
    exact ⟨1, (submonoid f I).one_mem, by simpa using ha_q⟩

/-- `a ∈ submonoid f I` iff `a` is not in any prime in `locClosedSubset f I`. -/
private lemma mem_submonoid_iff_not_mem_locClosedSubset (f : A) (I : Ideal A) (a : A) :
    a ∈ submonoid f I ↔ ∀ p ∈ locClosedSubset f I, a ∉ p.asIdeal := by
  simp only [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff, locClosedSubset]
  constructor
  · -- If IsUnit (algebraMap A ((A/I)_f) a), then a ∉ p for all p ∈ D(f) ∩ V(I)
    intro ha p ⟨hpf, hpI⟩ hap
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hpf
    simp only [PrimeSpectrum.mem_zeroLocus] at hpI
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p.asIdeal := by
      have hk : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
      rw [hk]; exact hpI
    set q := Ideal.map (Ideal.Quotient.mk I) p.asIdeal with hq_def
    have hq_prime : q.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hmkf : Ideal.Quotient.mk I f ∉ q := by
      rw [hq_def]
      intro hfq
      have hcomap := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective p.asIdeal
      rw [show Ideal.comap (Ideal.Quotient.mk I) ⊥ = I from
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I) ▸ Ideal.mk_ker] at hcomap
      have hfmem : f ∈ p.asIdeal ⊔ I := hcomap ▸ Ideal.mem_comap.mpr hfq
      have : p.asIdeal ⊔ I = p.asIdeal := sup_eq_left.mpr (by
        intro x hx; exact hpI hx)
      exact hpf (this ▸ hfmem)
    have hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk I f) : Set (A ⧸ I)) (q : Set (A ⧸ I)) :=
      Set.disjoint_left.mpr fun y hy1 hy2 => by
        simp only [SetLike.mem_coe, Submonoid.mem_powers_iff] at hy1
        obtain ⟨n, hn⟩ := hy1
        rw [← hn] at hy2
        exact hmkf (hq_prime.mem_of_pow_mem n hy2)
    have hq_loc : (Ideal.map (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ q hq_prime hdisj
    have hmka : Ideal.Quotient.mk I a ∈ q :=
      Ideal.mem_map_of_mem _ hap
    apply hq_loc.ne_top
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmka) (by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ I)] at ha; exact ha)
  · -- If a ∉ p for all p ∈ D(f) ∩ V(I), then IsUnit (algebraMap A ((A/I)_f) a)
    intro ha
    rw [IsScalarTower.algebraMap_apply A (A ⧸ I)]
    have key : basicOpen (Ideal.Quotient.mk I f) ≤ basicOpen (Ideal.Quotient.mk I a) := by
      intro p_bar hp_bar
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp_bar ⊢
      intro hmka
      set p := PrimeSpectrum.comap (Ideal.Quotient.mk I) p_bar
      have hpI : p ∈ zeroLocus (I : Set A) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        intro b hb
        show Ideal.Quotient.mk I b ∈ p_bar.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb]
        exact p_bar.asIdeal.zero_mem
      have hpf : p ∈ (basicOpen f : Set _) := by
        simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
        intro hfp
        exact hp_bar (show Ideal.Quotient.mk I f ∈ p_bar.asIdeal from hfp)
      exact ha p ⟨hpf, hpI⟩ hmka
    rwa [PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit (S :=
      Localization.Away (Ideal.Quotient.mk I f))] at key

theorem submonoid_le {f f' : A} {I I' : Ideal A} (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    submonoid f I ≤ submonoid f' I' := by
  intro a ha
  rw [mem_submonoid_iff_not_mem_locClosedSubset] at ha ⊢
  exact fun p hp => ha p (h hp)

noncomputable def map {f f' : A} {I I' : Ideal A} (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    Generalization f I →ₐ[A] Generalization f' I' where
  toRingHom := IsLocalization.map (T := Generalization.submonoid f' I')
    (Generalization f' I') (RingHom.id A) (submonoid_le h)
  commutes' := fun r => by simp

lemma exists_specializes_zeroLocus_ideal {f : A} (I : Ideal A)
    (x : PrimeSpectrum (Generalization f I)) : ∃ y ∈ zeroLocus (ideal f I), x ⤳ y := by
  -- Map x to its image in Spec A
  set p := PrimeSpectrum.comap (algebraMap A (Generalization f I)) x with hp_def
  -- p is in generalizationHull(locClosedSubset f I)
  have hp_range : p ∈ generalizationHull (locClosedSubset f I) := by
    rw [← range_algebraMap_generalization]; exact ⟨x, rfl⟩
  rw [mem_generalizationHull_iff] at hp_range
  obtain ⟨q, hq_loc, hpq⟩ := hp_range
  rw [← PrimeSpectrum.le_iff_specializes] at hpq
  -- q is disjoint from submonoid f I
  have hq_disj : Disjoint (submonoid f I : Set A) (q.asIdeal : Set A) :=
    Set.disjoint_left.mpr fun a ha ha_q =>
      submonoid_disjoint_locClosedSubset_primes f I a ha q hq_loc ha_q
  -- Lift q to a prime y of Generalization f I
  set q_map := Ideal.map (algebraMap A (Generalization f I)) q.asIdeal
  have hq_map_prime : q_map.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (submonoid f I) (Generalization f I)
      q.asIdeal q.isPrime hq_disj
  set y : PrimeSpectrum (Generalization f I) := ⟨q_map, hq_map_prime⟩
  have hy_comap : (PrimeSpectrum.comap (algebraMap A (Generalization f I)) y).asIdeal =
      q.asIdeal :=
    IsLocalization.comap_map_of_isPrime_disjoint (submonoid f I) (Generalization f I)
      q.isPrime hq_disj
  refine ⟨y, ?_, ?_⟩
  · -- y ∈ V(ideal f I): show ideal f I ⊆ y.asIdeal
    rw [PrimeSpectrum.mem_zeroLocus]
    intro z hz
    simp only [ideal, SetLike.mem_coe, RingHom.mem_ker] at hz
    -- z ∈ ker(toLocQuotient f I), and y.asIdeal = q.asIdeal.map(algebraMap)
    -- Since toLocQuotient factors through the quotient by ideal and q contains I,
    -- we need: toLocQuotient z = 0 implies z ∈ y.asIdeal
    -- toLocQuotient maps z to 0 in (A/I)_f
    -- y.asIdeal = q.asIdeal.map(algebraMap), and its comap is q.asIdeal
    -- Since I ⊆ q (from hq_loc), and algebraMap A (Gen f I) is flat...
    -- Actually, let's use: z ∈ y.asIdeal iff comap z ∈ q, i.e., algebraMap(z) ∈ q_map
    -- But z is already in Gen f I, not in A.
    -- Use: y.asIdeal = q_map = IsLocalization.map_comap gives us y = map(comap y)
    -- and comap y = q. So for z ∈ Gen f I, z ∈ y.asIdeal iff the image of z in
    -- Gen f I / y.asIdeal is 0.
    -- Alternative: use IsLocalization.map_comap to show ideal f I ≤ y.asIdeal
    -- ideal f I = ker(Gen f I → (A/I)_f)
    -- y.asIdeal corresponds to q = some prime containing I with f ∉ q
    -- The map Gen f I → (A/I)_f factors as Gen f I → Gen f I / (I·Gen f I) → (A/I)_f
    -- So ker ⊇ I · Gen f I
    -- And y.asIdeal ⊇ q.asIdeal.map ⊇ I.map
    -- So it suffices to show ideal f I ⊆ I.map ... no, that's wrong direction
    -- Actually: ideal f I = ker(toLocQuotient), and y.asIdeal ⊇ I.map(algebraMap)
    -- We need: ker(toLocQuotient) ⊆ y.asIdeal
    -- Use: toLocQuotient z = 0 and z ∈ Gen f I.
    -- Gen f I = (submonoid f I)⁻¹ A
    -- write z = a/s with a ∈ A and s ∈ submonoid f I
    -- toLocQuotient(a/s) = (image of a in (A/I)_f) / (image of s in (A/I)_f) = 0
    -- So image of a in (A/I)_f = 0
    -- i.e., algebraMap A ((A/I)_f) a = 0
    -- i.e., a ∈ ker(A → (A/I)_f)
    -- ker(A → (A/I)_f) = {a ∈ A | ∃ t ∈ powers(f̄), t · (a mod I) = 0 in A/I}
    --                   = {a ∈ A | ∃ n, f^n · a ∈ I}
    -- Since I ⊆ q.asIdeal and f ∉ q.asIdeal, we get f^n ∉ q.asIdeal
    -- And f^n · a ∈ I ⊆ q.asIdeal, so a ∈ q.asIdeal (since q is prime)
    -- Then z = a/s ∈ y.asIdeal = q.map(algebraMap) since a ∈ q.asIdeal
    -- Write z = mk' a s using surjectivity of mk'
    obtain ⟨a, s, hzas⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
    rw [← hzas] at hz ⊢
    -- toLocQuotient(mk' a s) = 0 means algebraMap A ((A/I)_f) a = 0
    have hz' : algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a = 0 := by
      -- mk' a s * algebraMap s = algebraMap a
      have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
      -- Apply toLocQuotient to both sides
      have h4 : (toLocQuotient f I) (IsLocalization.mk' (Generalization f I) a s *
          algebraMap A (Generalization f I) (s : A)) =
        (toLocQuotient f I) (algebraMap A (Generalization f I) a) := congr_arg _ h3
      rw [map_mul, hz, zero_mul, (toLocQuotient f I).commutes] at h4
      exact h4.symm
    -- hz' : algebraMap A ((A/I)_f) a = 0
    -- Use IsLocalization.eq_iff_exists to extract multiplier
    -- algebraMap A ((A/I)_f) factors as A → A/I → (A/I)_f
    -- So algebraMap A ((A/I)_f) a = 0 means ∃ c ∈ powers(mk I f), c * mk I a = 0
    -- First, get that a maps to zero in A/I localized at f
    -- By IsLocalization.surj of (A/I) → (A/I)_f, the algebra map is
    -- algebraMap R S where R = A/I, S = Localization.Away (mk I f), M = powers(mk I f)
    -- and algebraMap A S = algebraMap (A/I) S ∘ algebraMap A (A/I)
    -- Use exists_of_eq to get: algebraMap A ((A/I)_f) a = algebraMap A ((A/I)_f) 0
    -- implies ∃ c ∈ submonoid f I, c * a = c * 0 = 0 in (some sense)
    -- Actually: use the fact that the composed map A → (A/I)_f has a specific kernel
    -- Let's work directly: a ∈ q.asIdeal
    -- Since f ∉ q and I ⊆ q, the image of a in (A/I)_f is zero
    -- implies ∃ n, f^n * a ∈ I
    -- Actually let me directly use the characterization:
    -- algebraMap A ((A/I)_f) a = 0 iff ∃ n, (mk I f)^n * (mk I a) = 0 in A/I
    -- iff ∃ n, f^n * a ∈ I
    have ha_q : a ∈ q.asIdeal := by
      -- q ∈ locClosedSubset f I, so I ⊆ q.asIdeal and f ∉ q.asIdeal
      have hqI : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hq_loc.2
      have hfq : f ∉ q.asIdeal := by
        simp only [locClosedSubset, Set.mem_inter_iff] at hq_loc
        exact hq_loc.1
      -- From hz': algebraMap A ((A/I)_f) a = 0
      -- Factor: algebraMap A ((A/I)_f) = algebraMap (A/I) ((A/I)_f) ∘ (mk I)
      -- So (mk I a) maps to 0 in (A/I)_f
      -- By localization kernel: ∃ c ∈ powers(mk I f), c * (mk I a) = 0 in A/I
      set a_bar := Ideal.Quotient.mk I a
      set f_bar := Ideal.Quotient.mk I f
      have hz_factor : algebraMap (A ⧸ I) (Localization.Away f_bar) a_bar = 0 := by
        have := IsScalarTower.algebraMap_apply A (A ⧸ I) (Localization.Away f_bar) a
        rw [this] at hz'; exact hz'
      have ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f_bar)
        (Localization.Away f_bar) a_bar).mp hz_factor
      obtain ⟨c_val, n, hn⟩ := c
      subst hn
      -- hc : f_bar ^ n * a_bar = 0 in A/I
      -- i.e., f^n * a ∈ I
      have hfna : f ^ n * a ∈ I := by
        have : Ideal.Quotient.mk I (f ^ n * a) = 0 := by
          rw [map_mul, map_pow]; exact hc
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      -- f^n ∉ q (since q is prime and f ∉ q)
      have hfnq : f ^ n ∉ q.asIdeal := mt (q.isPrime.mem_of_pow_mem n) hfq
      exact (q.isPrime.mem_or_mem (hqI hfna)).resolve_left hfnq
    -- mk' a s ∈ y.asIdeal = Ideal.map (algebraMap A (Gen f I)) q.asIdeal
    show IsLocalization.mk' (Generalization f I) a s ∈ q_map
    rw [IsLocalization.mk'_mem_map_algebraMap_iff (submonoid f I)]
    exact ⟨1, (submonoid f I).one_mem, by simpa using ha_q⟩
  · -- x ⤳ y using the localization embedding
    -- For a localization, comap reflects specialization (it's an embedding)
    have hemb := PrimeSpectrum.localization_comap_isEmbedding (Generalization f I) (submonoid f I)
    rw [← hemb.specializes_iff (x := x) (y := y), ← PrimeSpectrum.le_iff_specializes]
    -- comap y has asIdeal = q.asIdeal (by hy_comap), comap x = p, and p ≤ q
    show p.asIdeal ≤ (PrimeSpectrum.comap (algebraMap A (Generalization f I)) y).asIdeal
    rw [hy_comap]
    exact hpq

end Generalization

/-- The single stratum `Z(E, F)` in `Spec A`. -/
def stratum (E F : Finset A) : Set (PrimeSpectrum A) :=
  (⋂ f ∈ E, basicOpen f) ∩ zeroLocus (Ideal.span (F : Set A))

lemma stratum_eq_basicOpen_inter_zeroLocus (E F : Finset A) :
    stratum E F = (basicOpen (∏ f ∈ E, f) : Set _) ∩ zeroLocus (Ideal.span (F : Set A)) := by
  classical
  rw [stratum]
  congr
  induction E using Finset.induction_on with
  | empty =>
    simp
  | insert a s h1 h2 =>
    simp [h2, Finset.prod_insert h1, -basicOpen_eq_zeroLocus_compl, basicOpen_mul]

lemma stratum_anti {E F E' F' : Finset A} (hEE' : E ⊆ E') (hFF' : F ⊆ F') :
    stratum E' F' ⊆ stratum E F := by
  rw [stratum, stratum]
  apply Set.inter_subset_inter
  · exact Set.biInter_mono hEE' fun x a ⦃a⦄ a ↦ a
  · apply zeroLocus_anti_mono
    exact Ideal.span_mono (Finset.coe_subset.mpr hFF')

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

lemma locClosedSubset_function_ideal {E : Finset A} (i : Stratification.Index E) :
    Generalization.locClosedSubset i.function i.ideal = stratum i.left i.right := by
  rw [Generalization.locClosedSubset, stratum_eq_basicOpen_inter_zeroLocus]
  rfl

/-- Restrict a disjoint union decomposition of `F` to `E`. -/
@[simps]
noncomputable
def Stratification.Index.restrict {E F : Finset A} (i : Stratification.Index F)
    (h : E ⊆ F) : Stratification.Index E where
  left := open Classical in E ∩ i.left
  right := open Classical in E ∩ i.right
  disjoint := open Classical in i.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  union_eq := by
    simp only [Finset.coe_inter]
    rw [← Set.inter_union_distrib_left, i.union_eq,
      Set.inter_eq_left.mpr (Finset.coe_subset.mpr h)]

lemma Stratification.Index.iUnion_stratum (E : Finset A) :
    ⋃ (i : Stratification.Index E), stratum i.left i.right = .univ := by
  classical
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨⟨E.filter (· ∉ p.asIdeal), E.filter (· ∈ p.asIdeal), ?_, ?_⟩, ?_⟩
  · rw [Finset.disjoint_filter]
    exact fun _ _ h1 h2 => h1 h2
  · ext x
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hx : x ∈ p.asIdeal
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl ⟨h, hx⟩
  · rw [stratum]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_iInter, Finset.mem_filter]
      intro f ⟨_, hf⟩
      exact hf
    · rw [PrimeSpectrum.mem_zeroLocus]
      apply Ideal.span_le.mpr
      intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2

/-- The product of the generalizations of `Z(E', E'')` indexed by all disjoint union decompositions
`E = E' ⨿ E''`. -/
def ProdStrata (E : Finset A) : Type _ :=
  ∀ (i : Stratification.Index E), Generalization i.function i.ideal

@[ext]
lemma ProdStrata.ext {E : Finset A} (x y : ProdStrata E) (h : ∀ i, x i = y i) : x = y := by
  dsimp [ProdStrata] at *
  ext i
  exact h i

instance (E : Finset A) : CommRing (ProdStrata E) := fast_instance%
  inferInstanceAs <| CommRing <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

instance (E : Finset A) : Algebra A (ProdStrata E) := fast_instance%
  inferInstanceAs <| Algebra A <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

/-- The ideal of the stratification product, given by the product of the ideals defining
`Z(E', E'')` in its generalization. -/
noncomputable def ProdStrata.ideal (E : Finset A) : Ideal (ProdStrata E) :=
  Ideal.pi fun _ ↦ Generalization.ideal _ _

set_option maxHeartbeats 1600000 in
lemma ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal (E : Finset A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (ProdStrata E))
    (zeroLocus (ProdStrata.ideal E)) .univ := by
  -- Local helper: right is determined by left
  have right_eq_sdiff : ∀ (i : Stratification.Index E), i.right = E \ i.left := by
    intro i; ext a; simp only [Finset.mem_sdiff]; constructor
    · intro ha
      exact ⟨Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_right _ (Finset.mem_coe.mpr ha)),
             fun h => Finset.disjoint_left.mp i.disjoint h ha⟩
    · intro ⟨haE, hal⟩
      have hmem : (a : A) ∈ (i.left : Set A) ∪ (i.right : Set A) :=
        i.union_eq ▸ Finset.mem_coe.mpr haE
      exact hmem.resolve_left (Finset.mem_coe.mp · |> hal)
  -- Local helper: same left implies equal indices
  have index_eq_of_left_eq : ∀ {i j : Stratification.Index E}, i.left = j.left → i = j := by
    intro i j h
    have hr : i.right = j.right := by rw [right_eq_sdiff, right_eq_sdiff, h]
    cases i; cases j; simp only [Stratification.Index.mk.injEq]; exact ⟨h, hr⟩
  -- Finiteness of Stratification.Index
  haveI : Finite (Stratification.Index E) := by
    classical
    apply Finite.of_injective
      (fun i : Stratification.Index E => (⟨i.left, Finset.mem_powerset.mpr fun a ha =>
        Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha))⟩ :
        {s // s ∈ E.powerset}))
    intro i j hij
    simp only [Subtype.mk.injEq] at hij
    exact index_eq_of_left_eq hij
  refine ⟨fun _ _ => Set.mem_univ _, ?injOn, ?surjOn⟩
  case injOn =>
    intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨i₁, q₁, hq₁⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
      (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
      (y₁ : PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
    obtain ⟨i₂, q₂, hq₂⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
      (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
      (y₂ : PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
    -- q_k ∈ V(ideal_ik): from V(I_E) membership, extract factor membership
    have hq₁_mem : q₁ ∈ zeroLocus (Generalization.ideal i₁.function i₁.ideal : Set _) := by
      intro a ha
      have hmem : (Pi.single i₁ a : ProdStrata E) ∈ ProdStrata.ideal E := by
        show _ ∈ Ideal.pi _; rw [Ideal.mem_pi]; intro j
        by_cases h : j = i₁
        · subst h; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h]; exact Ideal.zero_mem _
      have hz_q := (PrimeSpectrum.mem_zeroLocus _ _).mp (hq₁ ▸ hy₁) hmem
      have hz_q' : (Pi.evalRingHom (fun j : Stratification.Index E =>
          Generalization j.function j.ideal) i₁) (Pi.single i₁ a) ∈ (q₁.asIdeal : Set _) :=
        Ideal.mem_comap.mp hz_q
      simp only [Pi.evalRingHom_apply, Pi.single_eq_same] at hz_q'
      exact hz_q'
    have hq₂_mem : q₂ ∈ zeroLocus (Generalization.ideal i₂.function i₂.ideal : Set _) := by
      intro a ha
      have hmem : (Pi.single i₂ a : ProdStrata E) ∈ ProdStrata.ideal E := by
        show _ ∈ Ideal.pi _; rw [Ideal.mem_pi]; intro j
        by_cases h : j = i₂
        · subst h; rwa [Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h]; exact Ideal.zero_mem _
      have hz_q := (PrimeSpectrum.mem_zeroLocus _ _).mp (hq₂ ▸ hy₂) hmem
      have hz_q' : (Pi.evalRingHom (fun j : Stratification.Index E =>
          Generalization j.function j.ideal) i₂) (Pi.single i₂ a) ∈ (q₂.asIdeal : Set _) :=
        Ideal.mem_comap.mp hz_q
      simp only [Pi.evalRingHom_apply, Pi.single_eq_same] at hz_q'
      exact hz_q'
    -- Images land in respective locClosedSubsets = strata
    have h_img₁ := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
      i₁.function i₁.ideal).mapsTo hq₁_mem
    have h_img₂ := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
      i₂.function i₂.ideal).mapsTo hq₂_mem
    -- Build key equality: comap(alg_Gen₁) q₁ = comap(alg_Gen₂) q₂
    have heq' : PrimeSpectrum.comap (algebraMap A (Generalization i₁.function i₁.ideal)) q₁ =
        PrimeSpectrum.comap (algebraMap A (Generalization i₂.function i₂.ideal)) q₂ := by
      have h1 : PrimeSpectrum.comap (algebraMap A (Generalization i₁.function i₁.ideal)) q₁ =
          PrimeSpectrum.comap (algebraMap A (ProdStrata E)) y₁ := by rw [← hq₁]; rfl
      have h2 : PrimeSpectrum.comap (algebraMap A (Generalization i₂.function i₂.ideal)) q₂ =
          PrimeSpectrum.comap (algebraMap A (ProdStrata E)) y₂ := by rw [← hq₂]; rfl
      rw [h1, h2]; exact heq
    -- Must have i₁ = i₂ (strata are disjoint)
    have h_same : i₁ = i₂ := by
      by_contra hne
      rw [locClosedSubset_function_ideal] at h_img₁ h_img₂
      have hlne : i₁.left ≠ i₂.left := fun h => hne (index_eq_of_left_eq h)
      have hex : ∃ a, (a ∈ i₁.left ∧ a ∉ i₂.left) ∨ (a ∉ i₁.left ∧ a ∈ i₂.left) := by
        by_contra hall; push_neg at hall
        exact hlne (Finset.ext fun a =>
          ⟨(hall a).1, fun h => by_contra fun hn => absurd h ((hall a).2 hn)⟩)
      obtain ⟨a, (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)⟩ := hex
      · have ha_jr : a ∈ i₂.right := by
          rw [right_eq_sdiff]
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_coe.mp (i₁.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha1)), ha2⟩
        have hp1' := h_img₁; have hp2' := heq' ▸ h_img₂
        simp only [stratum, Set.mem_inter_iff, Set.mem_iInter] at hp1' hp2'
        exact (hp1'.1 a ha1) (hp2'.2 (Ideal.subset_span (Finset.mem_coe.mpr ha_jr)))
      · have ha_ir : a ∈ i₁.right := by
          rw [right_eq_sdiff]
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_coe.mp (i₂.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha2)), ha1⟩
        have hp1' := h_img₁; have hp2' := heq' ▸ h_img₂
        simp only [stratum, Set.mem_inter_iff, Set.mem_iInter] at hp1' hp2'
        exact (hp2'.1 a ha2) (hp1'.2 (Ideal.subset_span (Finset.mem_coe.mpr ha_ir)))
    subst h_same
    have hq_eq : q₁ = q₂ :=
      (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
        i₁.function i₁.ideal).injOn hq₁_mem hq₂_mem heq'
    rw [← hq₁, ← hq₂, hq_eq]
  case surjOn =>
    intro p _
    have hcover := Stratification.Index.iUnion_stratum E
    rw [Set.eq_univ_iff_forall] at hcover
    simp only [Set.mem_iUnion] at hcover
    obtain ⟨i, hi⟩ := hcover p
    have hp_loc : p ∈ Generalization.locClosedSubset i.function i.ideal :=
      locClosedSubset_function_ideal i ▸ hi
    obtain ⟨q, hq_mem, hq_eq⟩ :=
      (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
        i.function i.ideal).surjOn hp_loc
    set y : PrimeSpectrum (ProdStrata E) :=
      PrimeSpectrum.comap (Pi.evalRingHom (fun j : Stratification.Index E =>
        Generalization j.function j.ideal) i) q
    refine ⟨y, ?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus]
      intro z hz
      show z ∈ (PrimeSpectrum.comap (Pi.evalRingHom _ i) q).asIdeal
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hq_mem ((Ideal.mem_pi _ z).mp hz i)
    · -- comap(alg_PS) y = comap(alg_PS)(comap(eval_i) q) = comap(alg_Gen_i) q = p
      have : PrimeSpectrum.comap (algebraMap A (ProdStrata E)) y =
          PrimeSpectrum.comap (algebraMap A (Generalization i.function i.ideal)) q := by rfl
      rw [this]; exact hq_eq

-- Helper: right in a Stratification.Index is determined by left as E \ left.
private lemma Stratification.Index.right_eq_sdiff {E : Finset A}
    (i : Stratification.Index E) : i.right = E \ i.left := by
  classical
  ext a
  simp only [Finset.mem_sdiff]
  constructor
  · intro ha
    exact ⟨Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_right _ (Finset.mem_coe.mpr ha)),
           fun h => Finset.disjoint_left.mp i.disjoint h ha⟩
  · intro ⟨haE, hal⟩
    have hmem : (a : A) ∈ (i.left : Set A) ∪ (i.right : Set A) :=
      i.union_eq ▸ Finset.mem_coe.mpr haE
    exact hmem.resolve_left (Finset.mem_coe.mp · |> hal)

-- The Stratification.Index type is finite: each index is determined by its left ⊆ E.
set_option maxHeartbeats 400000 in
private instance finite_stratification_index (E : Finset A) :
    Finite (Stratification.Index E) := by
  classical
  -- Inject into E.powerset via left
  have left_mem : ∀ i : Stratification.Index E, i.left ∈ E.powerset := fun i =>
    Finset.mem_powerset.mpr fun a ha =>
      Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha))
  apply Finite.of_injective
    (fun i => (⟨i.left, left_mem i⟩ : {s // s ∈ E.powerset}))
  intro i j hij
  simp only [Subtype.mk.injEq] at hij
  have hr : i.right = j.right := by
    rw [i.right_eq_sdiff, j.right_eq_sdiff, hij]
  cases i; cases j; simp only [Stratification.Index.mk.injEq]; exact ⟨hij, hr⟩

set_option maxHeartbeats 800000 in
lemma ProdStrata.exists_specializes_zeroLocus_ideal {E : Finset A}
    (x : PrimeSpectrum (ProdStrata E)) :
    ∃ y ∈ zeroLocus (ProdStrata.ideal E), x ⤳ y := by
  -- Every prime of ProdStrata E = ∏_i Generalization ... comes from a factor
  -- ProdStrata E is definitionally ∀ (i : Stratification.Index E), Generalization ...
  -- which is a Pi type with finite index.
  -- Use exists_comap_evalRingHom_eq to find a factor i and prime q such that x = comap(eval i)(q)
  have ⟨i, q, hq⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (x : PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  -- By Generalization.exists_specializes_zeroLocus_ideal, q specializes to some y_i ∈ V(ideal)
  obtain ⟨y_i, hy_mem, hy_spec⟩ := Generalization.exists_specializes_zeroLocus_ideal i.ideal q
  -- Lift y_i back to ProdStrata E via sigmaToPi
  set y : PrimeSpectrum (ProdStrata E) :=
    PrimeSpectrum.comap (Pi.evalRingHom (fun j : Stratification.Index E =>
      Generalization j.function j.ideal) i) y_i
  refine ⟨y, ?_, ?_⟩
  · -- y ∈ zeroLocus (ProdStrata.ideal E)
    rw [PrimeSpectrum.mem_zeroLocus]
    intro z hz
    -- ProdStrata.ideal E = Ideal.pi (fun _ => Generalization.ideal _ _)
    have hz' : ∀ j, z j ∈ Generalization.ideal j.function j.ideal := by
      intro j; exact (Ideal.mem_pi _ z).mp hz j
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hy_mem (hz' i)
  · -- x ⤳ y: since x = comap (eval i) q and y = comap (eval i) y_i, and q ⤳ y_i
    show x ⤳ y
    rw [show x = PrimeSpectrum.comap (Pi.evalRingHom _ i) q from hq.symm]
    exact Specializes.map hy_spec (PrimeSpectrum.continuous_comap _)

lemma ProdStrata.mem_zeroLocus_ideal_of_isClosed {E : Finset A} {x : PrimeSpectrum (ProdStrata E)}
    (hx : IsClosed {x}) : x ∈ zeroLocus (ProdStrata.ideal E) := by
  obtain ⟨y, hmem, hy⟩ := exists_specializes_zeroLocus_ideal x
  have := hy.mem_closed hx (by simp)
  grind only [= Set.mem_singleton_iff]

/-- If `E ⊆ F`, this is the canonical map `A_E → A_F`. -/
noncomputable def ProdStrata.map {E F : Finset A} (h : E ⊆ F) :
    ProdStrata E →ₐ[A] ProdStrata F :=
  open Classical in
  Pi.algHom _ _ fun i ↦
    AlgHom.comp
      (Generalization.map <| by
        rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
        exact stratum_anti Finset.inter_subset_right Finset.inter_subset_right)
      (Pi.evalAlgHom _ _ (i.restrict h))

-- Helper: if two Stratification.Index values have the same left and right fields,
-- then Generalization.map acts as the identity between corresponding evaluations.
private lemma map_transport_eq {E : Finset A}
    {i j : Stratification.Index E}
    (hl : j.left = i.left) (hr : j.right = i.right)
    (h : Generalization.locClosedSubset i.function i.ideal ⊆
         Generalization.locClosedSubset j.function j.ideal)
    (x : ProdStrata E) :
    (Generalization.map h) (x j) = x i := by
  have hij : j = i := by
    cases i; cases j; simp only [Stratification.Index.mk.injEq]; exact ⟨hl, hr⟩
  subst hij
  simp only [Generalization.map, AlgHom.coe_mk]
  exact IsLocalization.map_id _

-- Helper for map_comp: if two indices in the same Stratification.Index E have the same
-- left and right fields, then maps from them to a common target produce the same result.
private lemma map_transport_comp_eq {E : Finset A} {f' : A} {I' : Ideal A}
    {j₁ j₂ : Stratification.Index E}
    (hl : j₁.left = j₂.left) (hr : j₁.right = j₂.right)
    (h₁ : Generalization.locClosedSubset f' I' ⊆
           Generalization.locClosedSubset j₁.function j₁.ideal)
    (h₂ : Generalization.locClosedSubset f' I' ⊆
           Generalization.locClosedSubset j₂.function j₂.ideal)
    (x : ProdStrata E) :
    (Generalization.map h₁) (x j₁) = (Generalization.map h₂) (x j₂) := by
  have hij : j₁ = j₂ := by
    cases j₁; cases j₂; simp only [Stratification.Index.mk.injEq]; exact ⟨hl, hr⟩
  subst hij
  rfl

lemma ProdStrata.map_apply {E F : Finset A} (h : E ⊆ F) (x : ProdStrata E)
    (i : Stratification.Index F) :
    ProdStrata.map h x i = (Generalization.map (by
      rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
      exact stratum_anti Finset.inter_subset_right Finset.inter_subset_right))
      (x (i.restrict h)) := by
  classical
  rfl

-- Helper: Generalization.map sends ideal elements to ideal elements when I ≤ I' and f | f'.
-- More precisely: the map Gen f I → Gen f' I' (for locClosedSubset f' I' ⊆ locClosedSubset f I)
-- sends ker(toLocQuotient f I) into ker(toLocQuotient f' I') when I ≤ I' and f | f'.
private lemma Generalization.map_mem_ideal_of_strata {f f' : A} {I I' : Ideal A}
    (h_sub : locClosedSubset f' I' ⊆ locClosedSubset f I) (hI : I ≤ I')
    (hf : f ∣ f') (z : Generalization f I) (hz : z ∈ ideal f I) :
    (map h_sub) z ∈ ideal f' I' := by
  simp only [ideal, SetLike.mem_coe, RingHom.mem_ker] at hz ⊢
  -- Write z = mk' a s
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
  -- From hz: toLocQuotient(mk' a s) = 0
  -- So algebraMap A ((A/I)_f) a = 0
  have hz' : algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a = 0 := by
    have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
    have h4 := congr_arg (toLocQuotient f I) h3
    rw [map_mul, hz, zero_mul, (toLocQuotient f I).commutes] at h4
    exact h4.symm
  -- Factor: algebraMap A ((A/I)_f) a = 0 means ∃ n, f^n * a ∈ I
  set f_bar := Ideal.Quotient.mk I f
  set a_bar := Ideal.Quotient.mk I a
  have hz_factor : algebraMap (A ⧸ I) (Localization.Away f_bar) a_bar = 0 := by
    rwa [IsScalarTower.algebraMap_apply A (A ⧸ I)] at hz'
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f_bar)
    (Localization.Away f_bar) a_bar).mp hz_factor
  have hfna : f ^ n * a ∈ I := by
    have : Ideal.Quotient.mk I (f ^ n * a) = 0 := by rw [map_mul, map_pow]; exact hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  -- Since I ≤ I': f^n * a ∈ I'
  have hfna' : f ^ n * a ∈ I' := hI hfna
  -- Since f | f': f' = f * g for some g
  obtain ⟨g, hfg⟩ := hf
  -- f'^n * a = (f*g)^n * a = g^n * (f^n * a) ∈ I'
  have hf'na : f' ^ n * a ∈ I' := by
    rw [hfg, mul_pow]
    have : f ^ n * g ^ n * a = g ^ n * (f ^ n * a) := by ring
    rw [this]
    exact I'.mul_mem_left _ hfna'
  -- Now show: toLocQuotient f' I' (map h_sub (mk' a s)) = 0
  -- map h_sub (mk' a s) is mk' a (s viewed in submonoid f' I')
  -- Actually, the map is IsLocalization.map induced by id, so it maps mk' a s to mk' (id a) s'
  -- where s' is s coerced into the target submonoid via submonoid_le h_sub.
  -- Then toLocQuotient f' I' of this is algebraMap A ((A/I')_{f'}) a / (unit from s')
  -- Since algebraMap A ((A/I')_{f'}) a = 0 (because f'^n * a ∈ I'), the result is 0.
  -- Let's show algebraMap A ((A/I')_{f'}) a = 0
  have ha_zero : algebraMap A (Localization.Away (Ideal.Quotient.mk I' f')) a = 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ I')]
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk I' f'))
      (Localization.Away (Ideal.Quotient.mk I' f')) (Ideal.Quotient.mk I' a)).mpr
    exact ⟨⟨_, n, rfl⟩, by
      have : Ideal.Quotient.mk I' (f' ^ n * a) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hf'na
      rwa [map_mul, map_pow] at this⟩
  -- Now: map h_sub (mk' a s) = mk' a s' in Gen f' I'
  -- And toLocQuotient f' I' is an algebra hom, so it sends mk' a s' to
  -- (algebraMap A ((A/I')_{f'}) a) / (image of s')
  -- = 0 / (image of s') = 0
  -- We use: toLocQuotient f' I' ∘ map h_sub ∘ algebraMap A = algebraMap A → (A/I')_{f'}
  -- This is because all maps are algebra maps over A.
  -- toLocQuotient f' I' (map h_sub (mk' a s))
  -- = toLocQuotient f' I' (map h_sub (mk' a s))
  -- mk' a s * algebraMap s = algebraMap a
  -- Apply map h_sub: (map h_sub (mk' a s)) * (map h_sub (algebraMap s)) = map h_sub (algebraMap a)
  -- = algebraMap a (since map h_sub is an A-algebra map)
  -- So (map h_sub (mk' a s)) * (algebraMap s) = algebraMap a (in Gen f' I')
  -- Apply toLocQuotient f' I':
  -- (toLocQuotient f' I' (map h_sub (mk' a s))) * (algebraMap A ((A/I')_{f'}) s) = algebraMap A ((A/I')_{f'}) a = 0
  -- Since algebraMap s is a unit (s ∈ submonoid f I ≤ submonoid f' I'), we get the desired = 0.
  have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
  have h4 : (map h_sub) (IsLocalization.mk' (Generalization f I) a s *
      algebraMap A (Generalization f I) (s : A)) =
    (map h_sub) (algebraMap A (Generalization f I) a) := congr_arg _ h3
  rw [map_mul, (map h_sub).commutes, (map h_sub).commutes] at h4
  -- h4 : (map h_sub)(mk' a s) * algebraMap s = algebraMap a in Gen f' I'
  have h5 := congr_arg (toLocQuotient f' I') h4
  rw [map_mul, (toLocQuotient f' I').commutes, (toLocQuotient f' I').commutes] at h5
  -- h5 : toLocQuotient f' I' (map h_sub (mk' a s)) * algebraMap s = algebraMap a in (A/I')_{f'}
  -- Since algebraMap A ((A/I')_{f'}) a = 0:
  rw [ha_zero] at h5
  -- h5 : toLocQuotient f' I' (map h_sub (mk' a s)) * _ = 0
  -- Since s is a unit in the target:
  have hs_unit : IsUnit (algebraMap A (Localization.Away (Ideal.Quotient.mk I' f')) (s : A)) :=
    submonoid_le h_sub s.2
  -- h5 : x * u = 0 where u is a unit, so x = 0
  exact hs_unit.mul_left_eq_zero.mp h5

set_option maxHeartbeats 400000 in
lemma ProdStrata.mapsTo_map_specComap {E F : Finset A} (h : E ⊆ F) :
    Set.MapsTo (PrimeSpectrum.comap (map h).toRingHom)
      (zeroLocus (ideal F)) (zeroLocus (ideal E)) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
  intro z hz
  -- z ∈ ideal E = Ideal.pi (fun _ => Generalization.ideal _ _)
  -- Need: (map h).toRingHom z ∈ p.asIdeal
  -- Since ideal F ⊆ p.asIdeal, suffices to show (map h).toRingHom z ∈ ideal F
  -- i.e., for all i : Strat.Index F, ((map h) z) i ∈ Generalization.ideal i.func i.ideal
  apply hp
  show (map h).toRingHom z ∈ ideal F
  -- ideal F = Ideal.pi (fun _ => Generalization.ideal _ _)
  -- Membership in Ideal.pi means: for all i, the i-th component is in the i-th ideal
  change ∀ i, ((map h) z) i ∈ Generalization.ideal i.function i.ideal
  intro i
  -- ((map h) z) i = Generalization.map ... (z (i.restrict h)) by map_apply
  have hmz : ((map h) z) i = (Generalization.map (by
      rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
      exact stratum_anti Finset.inter_subset_right Finset.inter_subset_right))
      (z (i.restrict h)) := by
    classical
    rfl
  rw [hmz]
  -- z (i.restrict h) ∈ Generalization.ideal (i.restrict h).func (i.restrict h).ideal
  have hz_comp : z (i.restrict h) ∈ Generalization.ideal (i.restrict h).function (i.restrict h).ideal := by
    exact (Ideal.mem_pi _ z).mp hz (i.restrict h)
  -- Use map_mem_ideal_of_strata with the specific strata properties
  exact Generalization.map_mem_ideal_of_strata _ (by
    -- I ≤ I': Ideal.span (E ∩ i.right) ≤ Ideal.span i.right
    exact Ideal.span_mono (Finset.coe_subset.mpr Finset.inter_subset_right))
    (by
    -- f | f': ∏_{f ∈ E ∩ i.left} f divides ∏_{f ∈ i.left} f
    classical
    exact Finset.prod_dvd_prod_of_subset _ _ id Finset.inter_subset_right)
    _ hz_comp

variable (A) in
/-- The diagram whose colimit is the w-localization of `A`. -/
noncomputable def diag : Finset A ⥤ CommAlgCat A where
  obj E := .of A (ProdStrata E)
  map {E F} f := CommAlgCat.ofHom (ProdStrata.map <| leOfHom f)
  map_id E := by
    apply CommAlgCat.hom_ext
    show ProdStrata.map _ = AlgHom.id A (ProdStrata E)
    refine AlgHom.ext fun x => ProdStrata.ext _ _ fun i => ?_
    show (ProdStrata.map (leOfHom (𝟙 E)) x) i = x i
    rw [ProdStrata.map_apply]
    exact map_transport_eq
      (by simp only [Stratification.Index.restrict]
          exact Finset.inter_eq_right.mpr (by
            rw [← Finset.coe_subset]; exact Set.subset_union_left.trans i.union_eq.le))
      (by simp only [Stratification.Index.restrict]
          exact Finset.inter_eq_right.mpr (by
            rw [← Finset.coe_subset]; exact Set.subset_union_right.trans i.union_eq.le))
      _ x
  map_comp {E F G} f g := by
    apply CommAlgCat.hom_ext
    show ProdStrata.map _ = (ProdStrata.map _).comp (ProdStrata.map _)
    refine AlgHom.ext fun x => ProdStrata.ext _ _ fun i => ?_
    show (ProdStrata.map (leOfHom (f ≫ g)) x) i =
      ((ProdStrata.map (leOfHom g)).comp (ProdStrata.map (leOfHom f)) x) i
    rw [ProdStrata.map_apply, AlgHom.comp_apply, ProdStrata.map_apply, ProdStrata.map_apply]
    simp only [Generalization.map, AlgHom.coe_mk]
    -- Use map_map to combine the RHS into a single map
    rw [IsLocalization.map_map
        (Q := Generalization (i.restrict (leOfHom g)).function (i.restrict (leOfHom g)).ideal)]
    simp only [RingHom.id_comp]
    -- Goal: map proof₁ (x (i.restrict (f ≫ g))) = map proof₂ (x ((i.restrict g).restrict f))
    -- Both sides map to Generalization i.function i.ideal.
    -- The indices have the same left/right (E ∩ (F ∩ l) = E ∩ l since E ⊆ F).
    exact map_transport_comp_eq
      (by -- left fields equal: (i.restrict(f≫g)).left = ((i.restrict g).restrict f).left
          simp only [Stratification.Index.restrict]; ext a; simp only [Finset.mem_inter]
          exact ⟨fun ⟨h1, h3⟩ => ⟨h1, leOfHom f h1, h3⟩, fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩⟩)
      (by -- right fields equal
          simp only [Stratification.Index.restrict]; ext a; simp only [Finset.mem_inter]
          exact ⟨fun ⟨h1, h3⟩ => ⟨h1, leOfHom f h1, h3⟩, fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩⟩)
      (by rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
          exact stratum_anti Finset.inter_subset_right Finset.inter_subset_right)
      (by rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
          exact stratum_anti
            (Finset.inter_subset_right.trans Finset.inter_subset_right)
            (Finset.inter_subset_right.trans Finset.inter_subset_right))
      x
variable (A) in
/-- The w-localization of a ring as an object of `CommAlgCat A` is the colimit over
the rings `A_E`. -/
noncomputable def commAlgCat : CommAlgCat A :=
  colimit (WLocalization.diag A)

noncomputable def colimitPresentation : ColimitPresentation (Finset A) (commAlgCat A) where
  diag := WLocalization.diag A
  ι := (colimit.cocone _).ι
  isColimit := colimit.isColimit _

end WLocalization

/-- The w-localization of a ring. -/
def WLocalization (A : Type u) [CommRing A] : Type _ :=
  WLocalization.commAlgCat A

namespace WLocalization

variable (A : Type u) [CommRing A]

noncomputable instance commRing : CommRing (WLocalization A) := fast_instance%
  inferInstanceAs <| CommRing (WLocalization.commAlgCat A)

noncomputable instance algebra : Algebra A (WLocalization A) := fast_instance%
  inferInstanceAs <| Algebra A (WLocalization.commAlgCat A)

noncomputable def ideal : Ideal (WLocalization A) :=
  ⨆ E : Finset A, Ideal.map (colimitPresentation.ι.app E).hom.toRingHom (ProdStrata.ideal E)

-- Helper: the underlying ring hom of the colimit coprojection
private noncomputable abbrev ιRingHom (E : Finset A) : ProdStrata E →+* WLocalization A :=
  (colimitPresentation (A := A)).ι.app E |>.hom.toRingHom

-- Helper: algebraMap A (WLocalization A) factors through each ι_E
private lemma algebraMap_eq_comp_ι (E : Finset A) :
    algebraMap A (WLocalization A) =
    (ιRingHom A E).comp (algebraMap A (ProdStrata E)) := by
  ext a; exact ((colimitPresentation (A := A)).ι.app E).hom.commutes a |>.symm

-- Helper: V(ideal A) iff comap(ι_E) p ∈ V(I_E) for all E
private lemma mem_zeroLocus_ideal_iff (p : PrimeSpectrum (WLocalization A)) :
    p ∈ zeroLocus (ideal A) ↔
    ∀ E : Finset A, PrimeSpectrum.comap (ιRingHom A E) p ∈
      zeroLocus (ProdStrata.ideal E) := by
  simp only [PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro hI E a ha
    apply hI
    show (ιRingHom A E) a ∈ (ideal A : Set (WLocalization A))
    rw [ideal, SetLike.mem_coe]
    exact Ideal.mem_iSup_of_mem E (Ideal.mem_map_of_mem _ ha)
  · intro hall
    rw [ideal, SetLike.coe_subset_coe]
    apply iSup_le
    intro E
    rw [Ideal.map_le_iff_le_comap]
    exact hall E

-- Helper: the CommRingCat cocone and colimit for element representation
private noncomputable def commRingCatCocone :
    Cocone (diag A ⋙ forget₂ (CommAlgCat A) CommRingCat) :=
  (forget₂ (CommAlgCat A) CommRingCat).mapCocone (colimit.cocone (diag A))

private noncomputable def commRingCatIsColimit : IsColimit (commRingCatCocone A) :=
  isColimitOfPreserves (forget₂ (CommAlgCat A) CommRingCat) (colimit.isColimit _)

-- Helper: every element of WLocalization A is in the image of some ι_E
private lemma exists_rep (x : WLocalization A) :
    ∃ (E : Finset A) (y : ProdStrata E), (ιRingHom A E) y = x := by
  have := Concrete.isColimit_exists_rep
    (diag A ⋙ forget₂ (CommAlgCat A) CommRingCat) (commRingCatIsColimit A) x
  obtain ⟨E, y, hy⟩ := this
  exact ⟨E, y, hy⟩

-- Helper: cocone condition ι_E c = ι_G (map c) for E ⊆ G
private lemma ι_comp_map (E G : Finset A) (h : E ⊆ G) (c : ProdStrata E) :
    (ιRingHom A E) c = (ιRingHom A G) (ProdStrata.map h c) := by
  -- colimit.w gives: (diag A).map (homOfLE h) ≫ colimit.ι G = colimit.ι E
  -- At element level: ι_G (ProdStrata.map h c) = ι_E c
  show (colimit.ι (diag A) E).hom c = (colimit.ι (diag A) G).hom ((ProdStrata.map h) c)
  have hw := colimit.w (diag A) (homOfLE h)
  -- hw : (diag A).map (homOfLE h) ≫ colimit.ι (diag A) G = colimit.ι (diag A) E
  rw [← hw]
  rfl

-- Helper: transition maps send I_E into I_G
private lemma map_mem_ideal {E G : Finset A} (h : E ⊆ G) {c : ProdStrata E}
    (hc : c ∈ ProdStrata.ideal E) :
    ProdStrata.map h c ∈ ProdStrata.ideal G := by
  change ∀ i, (ProdStrata.map h c) i ∈ Generalization.ideal i.function i.ideal
  intro i
  have hmz : (ProdStrata.map h c) i = (Generalization.map (by
      rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
      exact stratum_anti Finset.inter_subset_right Finset.inter_subset_right))
      (c (i.restrict h)) := by
    classical
    rfl
  rw [hmz]
  exact Generalization.map_mem_ideal_of_strata _ (by
    exact Ideal.span_mono (Finset.coe_subset.mpr Finset.inter_subset_right))
    (by classical
        exact Finset.prod_dvd_prod_of_subset _ _ id Finset.inter_subset_right)
    _ ((Ideal.mem_pi _ c).mp hc (i.restrict h))

-- Helper: every element of Ideal.map ι_E I_E has a single-stage representative
private lemma ideal_map_mem_exists (E : Finset A) (b : WLocalization A)
    (hb : b ∈ Ideal.map (ιRingHom A E) (ProdStrata.ideal E)) :
    ∃ (G : Finset A) (d : ProdStrata G), d ∈ ProdStrata.ideal G ∧ (ιRingHom A G) d = b := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    exact ⟨E, c, hc, rfl⟩
  | zero => exact ⟨∅, 0, Ideal.zero_mem _, map_zero _⟩
  | add b₁ b₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, d₁, hd₁, hι₁⟩ := ih₁
    obtain ⟨G₂, d₂, hd₂, hι₂⟩ := ih₂
    exact ⟨G₁ ∪ G₂,
      ProdStrata.map Finset.subset_union_left d₁ +
        ProdStrata.map Finset.subset_union_right d₂,
      Ideal.add_mem _ (map_mem_ideal A Finset.subset_union_left hd₁)
        (map_mem_ideal A Finset.subset_union_right hd₂),
      by rw [map_add, ← ι_comp_map A G₁ _ Finset.subset_union_left,
          ← ι_comp_map A G₂ _ Finset.subset_union_right, hι₁, hι₂]⟩
  | smul r b₁ _ ih₁ =>
    obtain ⟨G₁, d₁, hd₁, hι₁⟩ := ih₁
    obtain ⟨F, s, hs⟩ := exists_rep A r
    refine ⟨G₁ ∪ F,
      ProdStrata.map Finset.subset_union_right s *
        ProdStrata.map Finset.subset_union_left d₁,
      Ideal.mul_mem_left _ _ (map_mem_ideal A Finset.subset_union_left hd₁), ?_⟩
    rw [smul_eq_mul, map_mul, ← ι_comp_map A F _ Finset.subset_union_right,
        ← ι_comp_map A G₁ _ Finset.subset_union_left, hs, hι₁]

-- Helper: transition maps preserve Ideal.map algebraMap q
private lemma map_mem_algebraMap_ideal {E G : Finset A} (h : E ⊆ G) {t : ProdStrata E}
    {q : Ideal A} (ht : t ∈ Ideal.map (algebraMap A (ProdStrata E)) q) :
    ProdStrata.map h t ∈ Ideal.map (algebraMap A (ProdStrata G)) q := by
  have hle : Ideal.map (ProdStrata.map h).toRingHom
      (Ideal.map (algebraMap A (ProdStrata E)) q) ≤
      Ideal.map (algebraMap A (ProdStrata G)) q := by
    rw [Ideal.map_map, show (ProdStrata.map h).toRingHom.comp (algebraMap A (ProdStrata E)) =
      algebraMap A (ProdStrata G) from AlgHom.comp_algebraMap (ProdStrata.map h)]
  exact hle (Ideal.mem_map_of_mem (ProdStrata.map h).toRingHom ht)

-- Helper: every element of Ideal.map (algebraMap A W) q has a single-stage representative
-- in Ideal.map (algebraMap A (ProdStrata G)) q
private lemma algebraMap_ideal_map_mem_exists (q : Ideal A) (b : WLocalization A)
    (hb : b ∈ Ideal.map (algebraMap A (WLocalization A)) q) :
    ∃ (G : Finset A) (t : ProdStrata G),
      t ∈ Ideal.map (algebraMap A (ProdStrata G)) q ∧ (ιRingHom A G) t = b := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨a, ha, rfl⟩ := hb
    refine ⟨∅, (algebraMap A (ProdStrata ∅)) a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [algebraMap_eq_comp_ι A ∅]; rfl
  | zero => exact ⟨∅, 0, Ideal.zero_mem _, map_zero _⟩
  | add b₁ b₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, t₁, ht₁, hι₁⟩ := ih₁
    obtain ⟨G₂, t₂, ht₂, hι₂⟩ := ih₂
    exact ⟨G₁ ∪ G₂,
      ProdStrata.map Finset.subset_union_left t₁ +
        ProdStrata.map Finset.subset_union_right t₂,
      Ideal.add_mem _ (map_mem_algebraMap_ideal A Finset.subset_union_left ht₁)
        (map_mem_algebraMap_ideal A Finset.subset_union_right ht₂),
      by rw [map_add, ← ι_comp_map A G₁ _ Finset.subset_union_left,
          ← ι_comp_map A G₂ _ Finset.subset_union_right, hι₁, hι₂]⟩
  | smul r b₁ _ ih₁ =>
    obtain ⟨G₁, t₁, ht₁, hι₁⟩ := ih₁
    obtain ⟨F, s, hs⟩ := exists_rep A r
    refine ⟨G₁ ∪ F,
      ProdStrata.map Finset.subset_union_right s *
        ProdStrata.map Finset.subset_union_left t₁,
      Ideal.mul_mem_left _ _ (map_mem_algebraMap_ideal A Finset.subset_union_left ht₁), ?_⟩
    rw [smul_eq_mul, map_mul, ← ι_comp_map A F _ Finset.subset_union_right,
        ← ι_comp_map A G₁ _ Finset.subset_union_left, hs, hι₁]

-- Helper: monotonicity of the ideal system
private lemma ideal_map_le (E G : Finset A) (h : E ⊆ G) :
    Ideal.map (ιRingHom A E) (ProdStrata.ideal E) ≤
    Ideal.map (ιRingHom A G) (ProdStrata.ideal G) := by
  rw [Ideal.map_le_iff_le_comap]; intro c hc; rw [Ideal.mem_comap, ι_comp_map A E G h c]
  exact Ideal.mem_map_of_mem _ (map_mem_ideal A h hc)

-- Helper: the ideal system is directed
private lemma ideal_map_directed :
    Directed (· ≤ ·) (fun E : Finset A =>
      Ideal.map (ιRingHom A E) (ProdStrata.ideal E)) :=
  fun E F => ⟨E ∪ F, ideal_map_le A E _ Finset.subset_union_left,
    ideal_map_le A F _ Finset.subset_union_right⟩

-- Helper: Type-level isColimit for element equality in the filtered colimit
private noncomputable def typeCocone :
    Cocone ((diag A ⋙ forget₂ (CommAlgCat A) CommRingCat) ⋙ forget CommRingCat) :=
  (forget CommRingCat).mapCocone (commRingCatCocone A)

private noncomputable def typeIsColimit : IsColimit (typeCocone A) :=
  isColimitOfPreserves (forget CommRingCat) (commRingCatIsColimit A)

-- Helper: if two elements of ProdStrata G map to the same element of WLocalization A,
-- then they become equal after applying a transition map.
private lemma exists_map_eq_of_ι_eq (G : Finset A) (x y : ProdStrata G)
    (h : (ιRingHom A G) x = (ιRingHom A G) y) :
    ∃ (H : Finset A) (hGH : G ≤ H), ProdStrata.map hGH x = ProdStrata.map hGH y := by
  have htypeq := (Types.FilteredColimit.isColimit_eq_iff' (typeIsColimit A) x y).mp h
  obtain ⟨H, f, hf⟩ := htypeq
  exact ⟨H, leOfHom f, hf⟩

-- Helper: at each stage, comap(ι_E)(x) ⊔ I_E ≠ ⊤
private lemma comap_sup_ideal_ne_top (E : Finset A)
    (x : PrimeSpectrum (WLocalization A)) :
    (PrimeSpectrum.comap (ιRingHom A E) x).asIdeal ⊔ ProdStrata.ideal E ≠ ⊤ := by
  obtain ⟨t, ht_mem, ht_spec⟩ := ProdStrata.exists_specializes_zeroLocus_ideal
    (PrimeSpectrum.comap (ιRingHom A E) x)
  intro htop
  have hle1 : (PrimeSpectrum.comap (ιRingHom A E) x).asIdeal ≤ t.asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr ht_spec
  have hle2 : (ProdStrata.ideal E : Set (ProdStrata E)) ⊆ t.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp ht_mem
  have h1 : (1 : ProdStrata E) ∈ t.asIdeal := by
    have : (1 : ProdStrata E) ∈
        (PrimeSpectrum.comap (ιRingHom A E) x).asIdeal ⊔ ProdStrata.ideal E :=
      htop ▸ Submodule.mem_top
    exact (sup_le hle1 (SetLike.coe_subset_coe.mp hle2)) this
  exact t.isPrime.ne_top (t.asIdeal.eq_top_iff_one.mpr h1)

set_option maxHeartbeats 800000 in
lemma bijOn_algebraMap_specComap_zeroLocus_ideal :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (WLocalization A))
      (zeroLocus (ideal A)) .univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?injOn, ?surjOn⟩
  case injOn =>
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := (mem_zeroLocus_ideal_iff A p₁).mp hp₁
    have h2 := (mem_zeroLocus_ideal_iff A p₂).mp hp₂
    -- For each E, comap(ι_E) p₁ = comap(ι_E) p₂
    have heq_factor : ∀ E : Finset A,
        PrimeSpectrum.comap (ιRingHom A E) p₁ =
        PrimeSpectrum.comap (ιRingHom A E) p₂ := by
      intro E
      -- comap(algebraMap A (ProdStrata E))(comap(ι_E) p_k) = comap(algebraMap A (WLoc A)) p_k
      have h_eq_E : PrimeSpectrum.comap (algebraMap A (ProdStrata E))
          (PrimeSpectrum.comap (ιRingHom A E) p₁) =
        PrimeSpectrum.comap (algebraMap A (ProdStrata E))
          (PrimeSpectrum.comap (ιRingHom A E) p₂) := by
        have : ∀ (p : PrimeSpectrum (WLocalization A)),
            PrimeSpectrum.comap (algebraMap A (WLocalization A)) p =
            PrimeSpectrum.comap (algebraMap A (ProdStrata E))
              (PrimeSpectrum.comap (ιRingHom A E) p) := by
          intro p; ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
          rw [algebraMap_eq_comp_ι A E]; rfl
        rw [← this, ← this]; exact heq
      exact (ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal E).injOn
        (h1 E) (h2 E) h_eq_E
    -- Since every element comes from some ι_E, p₁ = p₂
    apply PrimeSpectrum.ext; apply Ideal.ext; intro x
    obtain ⟨E, y, hy⟩ := exists_rep A x
    rw [← hy]
    exact (PrimeSpectrum.ext_iff.mp (heq_factor E)) |> Ideal.ext_iff.mp |> (· y)
  case surjOn =>
    -- For each q ∈ Spec(A), find p ∈ V(ideal A) with comap(algebraMap) p = q.
    -- Strategy: show the ideal q.map(algebraMap) + ideal A is disjoint from the
    -- image of q.primeCompl, then use Ideal.exists_le_prime_disjoint.
    intro q _
    -- Helper: comap_algebraMap factors through ι_E
    have hfactor : ∀ (E : Finset A) (p : PrimeSpectrum (WLocalization A)),
        PrimeSpectrum.comap (algebraMap A (WLocalization A)) p =
        PrimeSpectrum.comap (algebraMap A (ProdStrata E))
          (PrimeSpectrum.comap (ιRingHom A E) p) := by
      intro E p; ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      rw [algebraMap_eq_comp_ι A E]; rfl
    -- Helper: at each ProdStrata E, there is y_E ∈ V(I_E) with comap(algebraMap_E) y_E = q
    have hstage : ∀ (E : Finset A),
        ∃ y ∈ zeroLocus (ProdStrata.ideal E),
          PrimeSpectrum.comap (algebraMap A (ProdStrata E)) y = q :=
      fun E => (ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal E).surjOn (Set.mem_univ q)
    -- Key: q.map(algebraMap) + ideal A is disjoint from q.primeCompl.map(algebraMap)
    set I_q := Ideal.map (algebraMap A (WLocalization A)) q.asIdeal ⊔ ideal A with hI_q_def
    set S := q.asIdeal.primeCompl.map (algebraMap A (WLocalization A)).toMonoidHom with hS_def
    have hDisj : Disjoint (I_q : Set (WLocalization A)) S := by
      refine Set.disjoint_left.mpr fun x hxI hxS => ?_
      -- x = algebraMap(a) for some a ∉ q
      obtain ⟨a, ha_not_q, rfl⟩ := hxS
      -- algebraMap(a) ∈ I_q = q.map(algebraMap) ⊔ ideal A
      rw [SetLike.mem_coe, Submodule.mem_sup] at hxI
      obtain ⟨b, hb_map, c, hc_ideal, hbc⟩ := hxI
      -- c ∈ ideal A = ⨆_E Ideal.map ι_E I_E. By directedness, c ∈ some stage.
      change c ∈ ideal A at hc_ideal
      have hideal : ideal A = ⨆ E : Finset A,
          Ideal.map (ιRingHom A E) (ProdStrata.ideal E) := rfl
      rw [hideal, Submodule.mem_iSup_of_directed _ (ideal_map_directed A)] at hc_ideal
      obtain ⟨E₁, hcE⟩ := hc_ideal
      -- b ∈ q.map(algebraMap): use algebraMap_ideal_map_mem_exists to get a stage-level
      -- representative in Ideal.map (algebraMap A (ProdStrata E₂)) q.asIdeal
      obtain ⟨E₂, b', hb'_mem, hb'⟩ := algebraMap_ideal_map_mem_exists A q.asIdeal b hb_map
      obtain ⟨E₃, c', hc', hc'eq⟩ := ideal_map_mem_exists A E₁ c hcE
      -- Go to a common stage G ⊇ E₂ ∪ E₃
      set G := E₂ ∪ E₃ with hG_def
      -- At stage G: algebraMap_G(a) = map(b') + map(c') modulo filtered colimit equality
      have hsum_eq : (ιRingHom A G) (ProdStrata.map Finset.subset_union_left b' +
          ProdStrata.map Finset.subset_union_right c') =
          (algebraMap A (WLocalization A)) a := by
        rw [map_add, ← ι_comp_map A E₂ G Finset.subset_union_left b',
          ← ι_comp_map A E₃ G Finset.subset_union_right c',
          hb', hc'eq, hbc]; rfl
      -- By filtered colimit equality, go to some H where these are equal as ring elements
      have htype_eq : (ιRingHom A G) (ProdStrata.map Finset.subset_union_left b' +
          ProdStrata.map Finset.subset_union_right c') =
          (ιRingHom A G) ((algebraMap A (ProdStrata G)) a) := by
        rw [hsum_eq, algebraMap_eq_comp_ι A G]; rfl
      obtain ⟨H, hGH, hH_eq⟩ := exists_map_eq_of_ι_eq A G _ _ htype_eq
      -- Get y_H ∈ V(I_H) with comap(algebraMap_H) y_H = q
      obtain ⟨y_H, hy_mem, hy_comap⟩ := hstage H
      -- algebraMap_H(a) ∈ y_H would contradict a ∉ q (since comap y_H = q)
      have ha_not_mem : (algebraMap A (ProdStrata H)) a ∉ y_H.asIdeal := by
        intro hmem
        have : a ∈ q.asIdeal := by
          rw [← hy_comap]; exact Ideal.mem_comap.mpr hmem
        exact ha_not_q this
      apply ha_not_mem
      -- Show algebraMap_H(a) ∈ y_H by computing from the stage equality
      have hH_eq' : ProdStrata.map hGH ((algebraMap A (ProdStrata G)) a) =
          ProdStrata.map hGH (ProdStrata.map Finset.subset_union_left b' +
            ProdStrata.map Finset.subset_union_right c') := hH_eq.symm
      -- Since algebraMap commutes with transition maps:
      have halg_comm : ProdStrata.map hGH ((algebraMap A (ProdStrata G)) a) =
          (algebraMap A (ProdStrata H)) a := by
        exact congr_fun (congr_arg DFunLike.coe
          (AlgHom.comp_algebraMap (ProdStrata.map hGH))) a
      rw [halg_comm] at hH_eq'
      rw [hH_eq', map_add]
      apply y_H.asIdeal.add_mem
      · -- map(b') ∈ y_H.asIdeal: b' ∈ Ideal.map algebraMap_{E₂} q, so after transition
        -- to G then H, it's in Ideal.map algebraMap_H q ⊆ y_H.asIdeal
        have hb'G : ProdStrata.map Finset.subset_union_left b' ∈
            Ideal.map (algebraMap A (ProdStrata G)) q.asIdeal :=
          map_mem_algebraMap_ideal A Finset.subset_union_left hb'_mem
        have hb'H : ProdStrata.map hGH (ProdStrata.map Finset.subset_union_left b') ∈
            Ideal.map (algebraMap A (ProdStrata H)) q.asIdeal :=
          map_mem_algebraMap_ideal A hGH hb'G
        -- Ideal.map algebraMap_H q ⊆ y_H since comap(algebraMap_H) y_H = q
        exact Ideal.map_le_iff_le_comap.mpr
          (ge_of_eq (congr_arg PrimeSpectrum.asIdeal hy_comap)) hb'H
      · -- map(c') ∈ y_H.asIdeal: c' ∈ I_{E₃} and y_H ∈ V(I_H), so map(c') ∈ I_H ⊆ y_H
        have hc'G : ProdStrata.map Finset.subset_union_right c' ∈ ProdStrata.ideal G :=
          map_mem_ideal A Finset.subset_union_right hc'
        have hc'H : ProdStrata.map hGH (ProdStrata.map Finset.subset_union_right c') ∈
            ProdStrata.ideal H :=
          map_mem_ideal A hGH hc'G
        exact ((PrimeSpectrum.mem_zeroLocus _ _).mp hy_mem) hc'H
    -- Now use exists_le_prime_disjoint
    obtain ⟨p, hp_prime, hp_le, hp_disj⟩ := Ideal.exists_le_prime_disjoint I_q S hDisj
    refine ⟨⟨p, hp_prime⟩, ?_, ?_⟩
    · -- p ∈ V(ideal A): ideal A ≤ I_q ≤ p
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr
        (SetLike.coe_subset_coe.mpr (le_sup_right.trans hp_le))
    · -- comap(algebraMap) ⟨p, _⟩ = q
      apply PrimeSpectrum.ext; apply Ideal.ext; intro a
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      constructor
      · -- algebraMap(a) ∈ p → a ∈ q (by disjointness with primeCompl)
        intro ha
        by_contra ha_not
        exact Set.disjoint_left.mp hp_disj (SetLike.mem_coe.mpr ha)
          (Submonoid.mem_map.mpr ⟨a, ha_not, rfl⟩)
      · -- a ∈ q → algebraMap(a) ∈ p
        intro ha
        exact hp_le (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

set_option maxHeartbeats 800000 in
lemma exists_mem_zeroLocus_ideal_specializes (x : PrimeSpectrum (WLocalization A)) :
    ∃ y ∈ zeroLocus (ideal A), x ⤳ y := by
  -- Suffices: x.asIdeal ⊔ ideal A ≠ ⊤
  suffices h : x.asIdeal ⊔ ideal A ≠ ⊤ by
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    exact ⟨⟨m, hm.isPrime⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr (sup_le_iff.mp hle).2,
      (PrimeSpectrum.le_iff_specializes _ _).mp (sup_le_iff.mp hle).1⟩
  intro htop
  -- 1 ∈ x.asIdeal + ideal A. Write 1 = a + b.
  have h1 : (1 : WLocalization A) ∈ x.asIdeal ⊔ ideal A := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  -- b ∈ ideal A = ⨆_E Ideal.map ι_E I_E. By directedness, b ∈ some stage.
  change b ∈ ideal A at hb
  have hideal : ideal A = ⨆ E : Finset A,
      Ideal.map (ιRingHom A E) (ProdStrata.ideal E) := rfl
  rw [hideal, Submodule.mem_iSup_of_directed _ (ideal_map_directed A)] at hb
  obtain ⟨E₀, hbE⟩ := hb
  -- b = ι_G(d₀) for some d₀ ∈ I_G (by ideal_map_mem_exists)
  obtain ⟨G₀, d₀, hd₀, hιd₀⟩ := ideal_map_mem_exists A E₀ b hbE
  -- a = 1 - b = ι_G₀(1 - d₀)
  have ha_eq : a = (ιRingHom A G₀) (1 - d₀) := by
    have h_sub : (ιRingHom A G₀) (1 - d₀) = 1 - b := by
      rw [map_sub, map_one, hιd₀]
    -- a + b = 1 implies a = 1 - b
    rw [h_sub]; linear_combination hab
  -- 1 - d₀ ∈ (comap ι_G₀ x).asIdeal
  have h1md : 1 - d₀ ∈ (PrimeSpectrum.comap (ιRingHom A G₀) x).asIdeal := by
    show (ιRingHom A G₀) (1 - d₀) ∈ x.asIdeal; rw [← ha_eq]; exact ha
  -- 1 = (1 - d₀) + d₀ ∈ (comap ι_G₀ x).asIdeal + I_G₀
  have h_one_mem : (1 : ProdStrata G₀) ∈
      (PrimeSpectrum.comap (ιRingHom A G₀) x).asIdeal ⊔ ProdStrata.ideal G₀ :=
    Submodule.mem_sup.mpr ⟨1 - d₀, h1md, d₀, hd₀, sub_add_cancel 1 d₀⟩
  -- Contradiction with comap_sup_ideal_ne_top
  exact comap_sup_ideal_ne_top A G₀ x
    (((PrimeSpectrum.comap (ιRingHom A G₀) x).asIdeal ⊔
      ProdStrata.ideal G₀).eq_top_iff_one.mpr h_one_mem)

-- Helper: in a Pi type, specialization implies same factor.
private lemma pi_specializes_same_factor {ι : Type*} {R : ι → Type*}
    [∀ i, CommRing (R i)] [Finite ι]
    {p p' : PrimeSpectrum (∀ i, R i)}
    {i j : ι} {q : PrimeSpectrum (R i)} {q' : PrimeSpectrum (R j)}
    (hp : p = PrimeSpectrum.comap (Pi.evalRingHom R i) q)
    (hp' : p' = PrimeSpectrum.comap (Pi.evalRingHom R j) q')
    (hspec : p ⤳ p') : i = j := by
  classical
  by_contra hne
  have h1 : Pi.single j (1 : R j) ∈ p.asIdeal := by
    rw [hp]; show (Pi.evalRingHom R i) (Pi.single j 1) ∈ q.asIdeal
    have : (Pi.evalRingHom R i) (Pi.single j (1 : R j)) = 0 := by
      simp only [Pi.evalRingHom_apply]; exact Pi.single_eq_of_ne hne 1
    rw [this]; exact q.asIdeal.zero_mem
  have h2 : Pi.single j (1 : R j) ∉ p'.asIdeal := by
    rw [hp']; show ¬ ((Pi.evalRingHom R j) (Pi.single j 1) ∈ q'.asIdeal)
    have : (Pi.evalRingHom R j) (Pi.single j (1 : R j)) = 1 := by
      rw [Pi.evalRingHom_apply, Pi.single_eq_same]
    rw [this]
    exact q'.isPrime.ne_top ∘ q'.asIdeal.eq_top_iff_one.mpr
  exact h2 ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec h1)

-- Helper: extract a prime of a factor from V(I_E) membership
private lemma factor_mem_zeroLocus_of_prodStrata {E : Finset A}
    {y : PrimeSpectrum (ProdStrata E)}
    (hy : y ∈ zeroLocus (ProdStrata.ideal E))
    {i : Stratification.Index E} {q : PrimeSpectrum (Generalization i.function i.ideal)}
    (hq : y = PrimeSpectrum.comap (Pi.evalRingHom _ i) q) :
    q ∈ zeroLocus (Generalization.ideal i.function i.ideal : Set _) := by
  classical
  let S : Stratification.Index E → Type _ := fun j => Generalization j.function j.ideal
  intro a ha
  have hmem : (Pi.single (M := S) i a : ProdStrata E) ∈ ProdStrata.ideal E := by
    show _ ∈ Ideal.pi _; rw [Ideal.mem_pi]; intro j
    by_cases h : j = i
    · subst h; rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h]; exact Ideal.zero_mem _
  have hz := (PrimeSpectrum.mem_zeroLocus _ _).mp (hq ▸ hy) hmem
  show a ∈ q.asIdeal
  have hmem2 : (Pi.evalRingHom S i) (Pi.single (M := S) i a) ∈ q.asIdeal :=
    Ideal.mem_comap.mp hz
  rwa [Pi.evalRingHom_apply, Pi.single_eq_same] at hmem2

-- Helper: the comap through eval ∘ algebraMap factors as comap(algebraMap W)
private lemma comap_eval_factor {E : Finset A}
    {y : PrimeSpectrum (ProdStrata E)}
    {i : Stratification.Index E} {q : PrimeSpectrum (Generalization i.function i.ideal)}
    (hq : y = PrimeSpectrum.comap (Pi.evalRingHom _ i) q) :
    PrimeSpectrum.comap (algebraMap A (Generalization i.function i.ideal)) q =
    PrimeSpectrum.comap (algebraMap A (ProdStrata E)) y := by
  rw [hq]; ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]; rfl

-- Helper: strata separation at a singleton stage.
-- If p, q ∈ V(I_E) with E = {f} and comap(alg) p, comap(alg) q are in the same
-- locClosedSubset, then f ∈ comap(alg) p ↔ f ∈ comap(alg) q.
private lemma strata_singleton_iff {f : A}
    {p q : PrimeSpectrum (WLocalization A)}
    (hp : p ∈ zeroLocus (ideal A))
    (hq : q ∈ zeroLocus (ideal A))
    (i : Stratification.Index ({f} : Finset A))
    (q_p : PrimeSpectrum (Generalization i.function i.ideal))
    (q_q : PrimeSpectrum (Generalization i.function i.ideal))
    (hp_eq : PrimeSpectrum.comap (ιRingHom A ({f} : Finset A)) p =
      PrimeSpectrum.comap (Pi.evalRingHom _ i) q_p)
    (hq_eq : PrimeSpectrum.comap (ιRingHom A ({f} : Finset A)) q =
      PrimeSpectrum.comap (Pi.evalRingHom _ i) q_q)
    (hq_p_V : q_p ∈ zeroLocus (Generalization.ideal i.function i.ideal : Set _))
    (hq_q_V : q_q ∈ zeroLocus (Generalization.ideal i.function i.ideal : Set _)) :
    (f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal ↔
     f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal) := by
  let E : Finset A := {f}
  have h_comap_p := comap_eval_factor A hp_eq
  have h_comap_q := comap_eval_factor A hq_eq
  have h_img_p := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
    i.function i.ideal).mapsTo hq_p_V
  have h_img_q := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
    i.function i.ideal).mapsTo hq_q_V
  rw [h_comap_p, show PrimeSpectrum.comap (algebraMap A (ProdStrata E))
    (PrimeSpectrum.comap (ιRingHom A E) p) =
    PrimeSpectrum.comap (algebraMap A (WLocalization A)) p from by
    ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    rw [algebraMap_eq_comp_ι A E]; rfl] at h_img_p
  rw [h_comap_q, show PrimeSpectrum.comap (algebraMap A (ProdStrata E))
    (PrimeSpectrum.comap (ιRingHom A E) q) =
    PrimeSpectrum.comap (algebraMap A (WLocalization A)) q from by
    ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    rw [algebraMap_eq_comp_ι A E]; rfl] at h_img_q
  rw [locClosedSubset_function_ideal] at h_img_p h_img_q
  -- Both comap p and comap q are in stratum i.left i.right
  -- = (⋂ g ∈ i.left, D(g)) ∩ V(Ideal.span i.right)
  -- f ∈ E = {f}, so f ∈ i.left ∪ i.right
  have hf_E : f ∈ ({f} : Finset A) := Finset.mem_singleton_self f
  have hf_union : f ∈ (i.left : Set A) ∪ (i.right : Set A) :=
    i.union_eq ▸ (Finset.mem_coe.mpr hf_E)
  rcases hf_union with hfl | hfr
  · -- f ∈ left: both comap p and comap q are in D(f), so f ∉ both
    have hfp_not : f ∉ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal := by
      have hmem := Set.mem_iInter₂.mp h_img_p.1 f (Finset.mem_coe.mp hfl)
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hmem
      exact hmem
    have hfq_not : f ∉ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal := by
      have hmem := Set.mem_iInter₂.mp h_img_q.1 f (Finset.mem_coe.mp hfl)
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hmem
      exact hmem
    exact ⟨fun hfp => absurd hfp hfp_not, fun hfq => absurd hfq hfq_not⟩
  · -- f ∈ right: f ∈ Ideal.span right ⊆ comap p and comap q
    have hfp_in : f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp h_img_p.2
        (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_coe.mp hfr)))
    have hfq_in : f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal :=
      (PrimeSpectrum.mem_zeroLocus _ _).mp h_img_q.2
        (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_coe.mp hfr)))
    exact ⟨fun _ => hfq_in, fun _ => hfp_in⟩

-- Helper: strata separation gives contradiction for distinct comap images.
-- If p, q ∈ V(I_w) with comap p ≠ comap q, and p ⤳ q, then contradiction.
private lemma strata_separation_contradiction
    {p q : PrimeSpectrum (WLocalization A)}
    (hp : p ∈ zeroLocus (ideal A))
    (hq : q ∈ zeroLocus (ideal A))
    (hcomap_ne : PrimeSpectrum.comap (algebraMap A (WLocalization A)) p ≠
      PrimeSpectrum.comap (algebraMap A (WLocalization A)) q)
    (hspec : p ⤳ q) : False := by
  -- Choose f that separates comap p and comap q
  have hcomap_ideals_ne :
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal ≠
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal :=
    fun h => hcomap_ne (PrimeSpectrum.ext h)
  -- p.asIdeal ≤ q.asIdeal, so (comap p).asIdeal ≤ (comap q).asIdeal
  -- Since they're not equal, (comap p) ⊊ (comap q), so ∃ f ∈ comap q \ comap p
  have hcomap_le : (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal ≤
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal :=
    Ideal.comap_mono ((PrimeSpectrum.le_iff_specializes _ _).mpr hspec)
  have hcomap_lt : (PrimeSpectrum.comap (algebraMap A (WLocalization A)) p).asIdeal <
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) q).asIdeal :=
    lt_of_le_of_ne hcomap_le (fun h => hcomap_ne (PrimeSpectrum.ext h))
  obtain ⟨f, hfq, hfp⟩ := Set.exists_of_ssubset hcomap_lt
  set E := ({f} : Finset A)
  haveI : Finite (Stratification.Index E) := finite_stratification_index E
  have hspec_E : PrimeSpectrum.comap (ιRingHom A E) p ⤳
      PrimeSpectrum.comap (ιRingHom A E) q :=
    Specializes.map hspec (PrimeSpectrum.continuous_comap _)
  obtain ⟨i_p, q_p, hq_p⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (PrimeSpectrum.comap (ιRingHom A E) p :
      PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  obtain ⟨i_q, q_q, hq_q⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (PrimeSpectrum.comap (ιRingHom A E) q :
      PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  have h_same_factor := pi_specializes_same_factor hq_p.symm hq_q.symm hspec_E
  subst h_same_factor
  have hp_V_E := ((mem_zeroLocus_ideal_iff A p).mp hp) E
  have hq_V_E := ((mem_zeroLocus_ideal_iff A q).mp hq) E
  have hq_p_V := factor_mem_zeroLocus_of_prodStrata A hp_V_E hq_p.symm
  have hq_q_V := factor_mem_zeroLocus_of_prodStrata A hq_V_E hq_q.symm
  exact absurd ((strata_singleton_iff A hp hq i_p q_p q_q hq_p.symm hq_q.symm
    hq_p_V hq_q_V).mpr hfq) hfp

-- Helper: for distinct primes in V(I_w) in the same factor, no specialization.
-- More general: if x ⤳ both c and c', and c, c' ∈ V(I_w) with comap c ≠ comap c',
-- then contradiction.
private lemma strata_separation_contradiction'
    {c c' : PrimeSpectrum (WLocalization A)}
    {x : PrimeSpectrum (WLocalization A)}
    (hc : c ∈ zeroLocus (ideal A))
    (hc' : c' ∈ zeroLocus (ideal A))
    (hcomap_ne : PrimeSpectrum.comap (algebraMap A (WLocalization A)) c ≠
      PrimeSpectrum.comap (algebraMap A (WLocalization A)) c')
    (hxc : x ⤳ c) (hxc' : x ⤳ c') : False := by
  -- Choose f that separates comap c and comap c'
  have hcomap_ideals_ne :
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) c).asIdeal ≠
      (PrimeSpectrum.comap (algebraMap A (WLocalization A)) c').asIdeal :=
    fun h => hcomap_ne (PrimeSpectrum.ext h)
  -- Get f in the symmetric difference
  have ⟨f, hf⟩ : ∃ f, ¬(f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) c).asIdeal ↔
      f ∈ (PrimeSpectrum.comap (algebraMap A (WLocalization A)) c').asIdeal) := by
    by_contra h; push_neg at h; exact hcomap_ideals_ne (SetLike.ext h)
  set E := ({f} : Finset A)
  haveI : Finite (Stratification.Index E) := finite_stratification_index E
  have hx_c := Specializes.map hxc (PrimeSpectrum.continuous_comap (ιRingHom A E))
  have hx_c' := Specializes.map hxc' (PrimeSpectrum.continuous_comap (ιRingHom A E))
  obtain ⟨i_x, q_x, hq_x⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (PrimeSpectrum.comap (ιRingHom A E) x :
      PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  obtain ⟨i_c, q_c, hq_c⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (PrimeSpectrum.comap (ιRingHom A E) c :
      PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  obtain ⟨i_c', q_c', hq_c'⟩ := @PrimeSpectrum.exists_comap_evalRingHom_eq
    (Stratification.Index E) (fun i => Generalization i.function i.ideal) _ _
    (PrimeSpectrum.comap (ιRingHom A E) c' :
      PrimeSpectrum (∀ i : Stratification.Index E, Generalization i.function i.ideal))
  have h_eq_c := pi_specializes_same_factor hq_x.symm hq_c.symm hx_c
  have h_eq_c' := pi_specializes_same_factor hq_x.symm hq_c'.symm hx_c'
  have h_same : i_c = i_c' := h_eq_c.symm.trans h_eq_c'
  subst h_same
  have hc_V_E := ((mem_zeroLocus_ideal_iff A c).mp hc) E
  have hc'_V_E := ((mem_zeroLocus_ideal_iff A c').mp hc') E
  have hq_c_V := factor_mem_zeroLocus_of_prodStrata A hc_V_E hq_c.symm
  have hq_c'_V := factor_mem_zeroLocus_of_prodStrata A hc'_V_E hq_c'.symm
  exact hf (strata_singleton_iff A hc hc' i_c q_c q_c' hq_c.symm hq_c'.symm hq_c_V hq_c'_V)

set_option maxHeartbeats 1600000 in
lemma zeroLocus_ideal_eq : zeroLocus (ideal A) = closedPoints (PrimeSpectrum (WLocalization A)) := by
  ext p
  constructor
  · -- V(ideal A) ⊆ closedPoints: every p ∈ V(I_w) is closed
    intro hp
    rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    -- If p.asIdeal is not maximal, there exists q with p ⊊ q prime
    by_contra h_not_max
    -- p.asIdeal is not maximal, so it's not coatom
    -- ∃ q : Ideal W, p.asIdeal < q and q ≠ ⊤
    rw [Ideal.isMaximal_def, IsCoatom] at h_not_max
    push_neg at h_not_max
    obtain ⟨q_ideal, hpq_lt, hq_ne_top⟩ := h_not_max p.isPrime.ne_top
    -- q_ideal contains a prime ideal properly above p
    obtain ⟨q_max_ideal, hq_max, hq_le⟩ := Ideal.exists_le_maximal q_ideal hq_ne_top
    set q' : PrimeSpectrum (WLocalization A) := ⟨q_max_ideal, hq_max.isPrime⟩
    have hpq : p.asIdeal < q'.asIdeal := lt_of_lt_of_le hpq_lt hq_le
    have hne : p ≠ q' := fun h => absurd hpq (h ▸ lt_irrefl _)
    have hspec : p ⤳ q' := (PrimeSpectrum.le_iff_specializes _ _).mp hpq.le
    have hq'_mem : q' ∈ zeroLocus (ideal A) :=
      (isClosed_zeroLocus _).closure_subset (closure_mono (Set.singleton_subset_iff.mpr hp)
        (hspec.mem_closed isClosed_closure (subset_closure rfl)))
    have hcomap_ne : PrimeSpectrum.comap (algebraMap A (WLocalization A)) p ≠
        PrimeSpectrum.comap (algebraMap A (WLocalization A)) q' :=
      fun heq => hne ((bijOn_algebraMap_specComap_zeroLocus_ideal A).injOn hp hq'_mem heq)
    exact strata_separation_contradiction A hp hq'_mem hcomap_ne hspec
  · -- closedPoints ⊆ V(ideal A): a closed point specializes to itself
    intro hp
    have ⟨y, hy_mem, hspec⟩ := exists_mem_zeroLocus_ideal_specializes A p
    rw [mem_closedPoints_iff] at hp
    have hpy : p = y := by
      have : y ∈ ({p} : Set _) := hspec.mem_closed hp (Set.mem_singleton p)
      exact (Set.mem_singleton_iff.mp this).symm
    rw [hpy]; exact hy_mem

set_option maxHeartbeats 800000 in
instance isWLocalRing : IsWLocalRing (WLocalization A) := by
  constructor
  refine {
    eq_of_specializes := ?_
    isClosed_closedPoints := (zeroLocus_ideal_eq A).symm ▸ isClosed_zeroLocus _
  }
  intro x c c' hc hc' hxc hxc'
  have hc_V : c ∈ zeroLocus (ideal A) :=
    (zeroLocus_ideal_eq A).symm ▸ mem_closedPoints_iff.mpr hc
  have hc'_V : c' ∈ zeroLocus (ideal A) :=
    (zeroLocus_ideal_eq A).symm ▸ mem_closedPoints_iff.mpr hc'
  by_contra hne
  exact strata_separation_contradiction' A hc_V hc'_V
    (fun heq => hne ((bijOn_algebraMap_specComap_zeroLocus_ideal A).injOn hc_V hc'_V heq))
    hxc hxc'

-- Each ProdStrata E is ind-Zariski over A (finite product of ind-Zariski localizations).
-- We reduce to ULift (Fin n) index via AlgEquiv.piCongrLeft, avoiding the expensive
-- elaboration of Algebra.IndZariski.pi directly on Stratification.Index E.
set_option maxHeartbeats 12000000 in
private lemma prodStrata_indZariski (E : Finset A) :
    Algebra.IndZariski A (ProdStrata E) := by
  change Algebra.IndZariski A
    (∀ (i : Stratification.Index E), Generalization i.function i.ideal)
  obtain ⟨n, ⟨e_fin⟩⟩ := Finite.exists_equiv_fin (Stratification.Index E)
  let e : ULift.{u} (Fin n) ≃ Stratification.Index E :=
    Equiv.ulift.trans e_fin.symm
  let S : Stratification.Index E → Type u := fun i => Generalization i.function i.ideal
  have h1 : Algebra.IndZariski A (∀ k : ULift.{u} (Fin n), S (e k)) :=
    Algebra.IndZariski.pi A (fun k => S (e k))
  exact Algebra.IndZariski.of_equiv
    (R := A) (S := ∀ k : ULift.{u} (Fin n), S (e k)) (T := ∀ i, S i)
    (AlgEquiv.piCongrLeft A S e)

-- WLocalization A is ind-Zariski: filtered colimit of ind-Zariski ProdStrata algebras.
-- Explicit @ is essential here to resolve the instance diamond.
set_option maxHeartbeats 10000000 in
noncomputable instance indZariski : Algebra.IndZariski A (WLocalization A) := by
  letI cr := WLocalization.commRing A
  letI al := WLocalization.algebra A
  have h := fun (E : Finset A) => prodStrata_indZariski (A := A) E
  exact @Algebra.IndZariski.of_colimitPresentation A (WLocalization A) _ cr al
    (Finset A) _ _ colimitPresentation h

-- For any E and maximal m, the ideal m does not generate the unit ideal in ProdStrata E.
-- Proof: by iUnion_stratum, m lies in some locClosedSubset, so the submonoid is disjoint from m,
-- hence the localization at that submonoid preserves properness of m. By the projection from
-- ProdStrata to a single factor, properness is inherited.
private lemma map_algebraMap_prodStrata_ne_top (E : Finset A) (m : PrimeSpectrum A)
    (hm : m.asIdeal.IsMaximal) :
    Ideal.map (algebraMap A (ProdStrata E)) m.asIdeal ≠ ⊤ := by
  -- Find an index i such that m is in stratum i.left i.right
  have huniv := Stratification.Index.iUnion_stratum E
  have hm_mem : m ∈ (Set.univ : Set (PrimeSpectrum A)) := Set.mem_univ _
  rw [← huniv] at hm_mem
  simp only [Set.mem_iUnion] at hm_mem
  obtain ⟨i, hi⟩ := hm_mem
  -- m is in locClosedSubset i.function i.ideal
  rw [← locClosedSubset_function_ideal] at hi
  -- The submonoid is disjoint from m: if a ∈ submonoid and a ∈ m.asIdeal, then
  -- algebraMap a is a unit in (A/I)_f. Since I ≤ m and f ∉ m, there's a ring hom
  -- (A/I)_f → A/m sending units to units. But a ∈ m means its image is 0, not a unit.
  set I := i.ideal
  set f := i.function
  have hdisj : Disjoint (Generalization.submonoid f I : Set A) (m.asIdeal : Set A) :=
    Set.disjoint_left.mpr fun a ha ha_m => by
    -- ha : a ∈ Generalization.submonoid f I, meaning algebraMap a is a unit in (A/I)_f
    have ha_unit : IsUnit (algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a) := by
      change a ∈ Submonoid.comap _ _ at ha
      exact ha
    -- hi gives: f ∉ m.asIdeal and I ≤ m.asIdeal
    have hfm : f ∉ m.asIdeal := by
      have := hi.1
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at this
      exact this
    have hIm : I ≤ m.asIdeal := by
      have := hi.2
      rw [PrimeSpectrum.mem_zeroLocus] at this
      exact this
    -- Build the quotient ideal q = map (mk I) m in A/I. It is prime since I ≤ m.
    have hker : (RingHom.ker (Ideal.Quotient.mk I) : Ideal A) ≤ m.asIdeal := by
      rw [Ideal.mk_ker]; exact hIm
    set q : Ideal (A ⧸ I) := Ideal.map (Ideal.Quotient.mk I) m.asIdeal
    have hq_prime : q.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    -- mk I f ∉ q, since f ∉ m and I ≤ m
    have hmkf : Ideal.Quotient.mk I f ∉ q := by
      intro hfq
      apply hfm
      -- hfq : mk I f ∈ q = Ideal.map (mk I) m.
      -- f ∈ comap (mk I) (map (mk I) m) = m ⊔ ker(mk I) = m ⊔ I = m.
      have h1 : f ∈ Ideal.comap (Ideal.Quotient.mk I) q := Ideal.mem_comap.mpr hfq
      have h2 := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective m.asIdeal
      -- h2 : comap (mk I) (map (mk I) m) = m ⊔ comap (mk I) ⊥
      -- comap (mk I) ⊥ = I (by Ideal.mk_ker, after unfolding ker)
      have h3 : Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (A ⧸ I)) = I := by
        ext x
        simp only [Ideal.mem_comap, Ideal.mem_bot]
        exact Ideal.Quotient.eq_zero_iff_mem
      rw [h2, h3, sup_eq_left.mpr hIm] at h1
      exact h1
    -- powers of mk I f are disjoint from q
    have hdisj_powers : Disjoint (Submonoid.powers (Ideal.Quotient.mk I f) : Set (A ⧸ I))
        (q : Set (A ⧸ I)) :=
      Set.disjoint_left.mpr fun y hy1 hy2 => by
        simp only [SetLike.mem_coe, Submonoid.mem_powers_iff] at hy1
        obtain ⟨n, hn⟩ := hy1
        rw [← hn] at hy2
        exact hmkf (hq_prime.mem_of_pow_mem n hy2)
    -- The localized ideal is prime
    have hq_loc : (Ideal.map (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))) q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ q hq_prime hdisj_powers
    -- Derive contradiction: algebraMap a is a unit, but mk I a ∈ q, so its image
    -- generates the localized ideal to ⊤
    apply hq_loc.ne_top
    have hmka : Ideal.Quotient.mk I a ∈ q := Ideal.mem_map_of_mem _ ha_m
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hmka)
    rwa [IsScalarTower.algebraMap_apply A (A ⧸ I)] at ha_unit
  -- So m generates a proper ideal in Generalization i.function i.ideal
  have hne_top : Ideal.map (algebraMap A (Generalization f I)) m.asIdeal ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      (Generalization.submonoid f I) (Generalization f I) m.asIdeal).mpr hdisj
  -- The projection ProdStrata E -> Generalization i is surjective and an A-algebra map
  -- If m generated ⊤ in ProdStrata E, then applying Pi.evalRingHom gives ⊤ in Generalization
  intro htop
  apply hne_top
  let eval_i := Pi.evalRingHom (fun j : Stratification.Index E =>
    Generalization j.function j.ideal) i
  -- algebraMap A (Gen f I) = eval_i ∘ algebraMap A (ProdStrata E)
  -- Goal: Ideal.map (algebraMap A (Generalization f I)) m.asIdeal = ⊤
  -- algebraMap A (Gen f I) = eval_i ∘ algebraMap A (ProdStrata E) definitionally
  -- So map (algebraMap A (Gen f I)) m = (map (algebraMap A (ProdStrata E)) m).map eval_i = ⊤.map eval_i = ⊤
  -- map (algebraMap A (Gen)) m = map (eval_i.comp (algebraMap A (ProdStrata E))) m
  -- = (map (algebraMap A (ProdStrata E)) m).map eval_i = ⊤.map eval_i = ⊤
  have h1 := Ideal.map_map (algebraMap A (ProdStrata E)) eval_i (I := m.asIdeal)
  -- h1 : (m.asIdeal.map _).map eval_i = m.asIdeal.map (eval_i.comp _)
  rw [htop, Ideal.map_top] at h1
  -- h1 : ⊤ = m.asIdeal.map (eval_i.comp (algebraMap A (ProdStrata E)))
  -- Goal : m.asIdeal.map (algebraMap A (Generalization f I)) = ⊤
  rw [show algebraMap A (Generalization f I) = eval_i.comp (algebraMap A (ProdStrata E)) from
    RingHom.ext fun _ => rfl]
  exact h1.symm

-- WLocalization A is faithfully flat: flat (from indZariski) + nontrivial tensor products.
-- Uses the colimit presentation and CommRingCat.FilteredColimits.nontrivial to show that
-- (A/m) ⊗ WLocalization(A) is nontrivial for each maximal m, since each stage
-- (A/m) ⊗ ProdStrata(E) is nontrivial by map_algebraMap_prodStrata_ne_top.
set_option maxHeartbeats 800000 in
instance faithfullyFlat : Module.FaithfullyFlat A (WLocalization A) := by
  apply Module.FaithfullyFlat.of_nontrivial_tensor_quotient
  intro m hm
  -- Need: Nontrivial ((A ⧸ m) ⊗[A] WLocalization A)
  -- WLocalization A = colim ProdStrata E in CommAlgCat A
  -- (A/m) ⊗ - preserves colimits, so (A/m) ⊗ WLocalization A = colim ((A/m) ⊗ ProdStrata E)
  letI cr := WLocalization.commRing A
  letI al := WLocalization.algebra A
  let pres := @colimitPresentation A _
  let qpres := pres.map (MonoidalCategory.tensorLeft (CommAlgCat.of A (A ⧸ m)))
  -- Each stage is nontrivial: (A/m) ⊗ ProdStrata(E) is nontrivial because
  -- Ideal.map (algebraMap A (ProdStrata E)) m ≠ ⊤
  suffices ∀ E, Nontrivial ((qpres.diag ⋙
      CategoryTheory.forget₂ (CommAlgCat A) CommRingCat).obj E) from by
    change Nontrivial ((CategoryTheory.forget₂ _ CommRingCat).mapCocone qpres.cocone).pt
    exact CommRingCat.FilteredColimits.nontrivial
      (Limits.isColimitOfPreserves _ qpres.isColimit)
  intro E
  -- After unfolding, the goal should be about Nontrivial of some tensor product ring
  -- We know Ideal.map (algebraMap A (ProdStrata E)) m ≠ ⊤
  have hne := map_algebraMap_prodStrata_ne_top A E ⟨m, hm.isPrime⟩ hm
  -- This means the quotient ProdStrata E / (m * ProdStrata E) is nontrivial
  -- which is isomorphic to (A/m) ⊗ ProdStrata E
  -- The goal after simp should reduce to Nontrivial ((A ⧸ m) ⊗[A] ProdStrata E)
  -- The goal involves category-theoretic tensor product; reduce to Nontrivial ((A ⧸ m) ⊗[A] ProdStrata E)
  -- pres.diag.obj E = CommAlgCat.of A (ProdStrata E), and the forget functor extracts the type
  change Nontrivial (TensorProduct A (A ⧸ m) (ProdStrata E))
  -- Use quotTensorEquivQuotSMul to transfer nontriviality
  -- (A/m) ⊗ ProdStrata E ≃ ProdStrata E / (m • ⊤), and m • ⊤ ≠ ⊤ since Ideal.map ... m ≠ ⊤
  rw [(TensorProduct.quotTensorEquivQuotSMul (ProdStrata E) m).nontrivial_congr]
  rw [Submodule.Quotient.nontrivial_iff]
  rw [show m • (⊤ : Submodule A (ProdStrata E)) =
    (Ideal.map (algebraMap A (ProdStrata E)) m).restrictScalars A from
    Ideal.smul_top_eq_map m]
  intro h
  apply hne
  -- h : restrictScalars A (Ideal.map ...) = ⊤
  -- Need : Ideal.map (algebraMap A (ProdStrata E)) m = ⊤
  have : (Ideal.map (algebraMap A (ProdStrata E)) m : Submodule (ProdStrata E) (ProdStrata E)) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff (S := A)]
    exact h
  exact_mod_cast this

open PrimeSpectrum
