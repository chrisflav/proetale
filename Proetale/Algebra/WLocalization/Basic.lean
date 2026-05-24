/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocal
import Proetale.Algebra.IndZariski
import Proetale.Algebra.IndEtale
import Proetale.Algebra.StalkAlgebraic
import Proetale.Algebra.Preliminaries.Ideal

/-!
# w-localization

In this file we show that every ring admits a faithfully flat, ind-Zariski w-local algebra.
-/

universe u

open CategoryTheory Limits PrimeSpectrum

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
      push Not
      intro n hfn
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
    push Not at hf_not_rad
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
        have hq_range :
            q ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Generalization f I))) :=
          ⟨y, rfl⟩
        rwa [PrimeSpectrum.localization_comap_range (Generalization f I) (submonoid f I)]
          at hq_range
      exact Set.disjoint_left.mp hdisj hf_sub hfq
    · -- I ⊆ q.asIdeal
      rw [PrimeSpectrum.mem_zeroLocus]
      intro a ha
      change algebraMap A (Generalization f I) a ∈ y.asIdeal
      apply hy
      simp only [ideal, SetLike.mem_coe, RingHom.mem_ker]
      change (toLocQuotient f I) (algebraMap A (Generalization f I) a) = 0
      rw [(toLocQuotient f I).commutes, IsScalarTower.algebraMap_apply A (A ⧸ I)]
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
      PrimeSpectrum.ext (IsLocalization.under_map_of_isPrime_disjoint (submonoid f I)
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
    change IsLocalization.mk' (Generalization f I) a s ∈ q_map
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
    have hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk I f) : Set (A ⧸ I))
        (q : Set (A ⧸ I)) :=
      Set.disjoint_left.mpr fun y hy1 hy2 => by
        simp only [SetLike.mem_coe, Submonoid.mem_powers_iff] at hy1
        obtain ⟨n, hn⟩ := hy1
        rw [← hn] at hy2
        exact hmkf (hq_prime.mem_of_pow_mem n hy2)
    have hq_loc : (Ideal.map (algebraMap (A ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I f))) q).IsPrime :=
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
      simp only [PrimeSpectrum.mem_basicOpen] at hp_bar ⊢
      intro hmka
      set p := PrimeSpectrum.comap (Ideal.Quotient.mk I) p_bar
      have hpI : p ∈ zeroLocus (I : Set A) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        intro b hb
        change Ideal.Quotient.mk I b ∈ p_bar.asIdeal
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

noncomputable def map {f f' : A} {I I' : Ideal A}
    (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
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
    IsLocalization.under_map_of_isPrime_disjoint (submonoid f I) (Generalization f I)
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
    change IsLocalization.mk' (Generalization f I) a s ∈ q_map
    rw [IsLocalization.mk'_mem_map_algebraMap_iff (submonoid f I)]
    exact ⟨1, (submonoid f I).one_mem, by simpa using ha_q⟩
  · -- x ⤳ y using the localization embedding
    -- For a localization, comap reflects specialization (it's an embedding)
    have hemb :=
      PrimeSpectrum.localization_comap_isEmbedding (Generalization f I) (submonoid f I)
    rw [← hemb.specializes_iff (x := x) (y := y), ← PrimeSpectrum.le_iff_specializes]
    -- comap y has asIdeal = q.asIdeal (by hy_comap), comap x = p, and p ≤ q
    change p.asIdeal ≤ (PrimeSpectrum.comap (algebraMap A (Generalization f I)) y).asIdeal
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
  disjoint := sorry
  union_eq := sorry

lemma Stratification.Index.iUnion_stratum (E : Finset A) :
    ⋃ (i : Stratification.Index E), stratum i.left i.right = .univ :=
  sorry

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

-- wrong
lemma ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal (E : Finset A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (ProdStrata E))
    (zeroLocus (ProdStrata.ideal E)) .univ :=
  sorry

lemma ProdStrata.exists_specializes_zeroLocus_ideal {E : Finset A}
    (x : PrimeSpectrum (ProdStrata E)) :
    ∃ y ∈ zeroLocus (ProdStrata.ideal E), x ⤳ y :=
  sorry

lemma ProdStrata.mem_zeroLocus_ideal_of_isClosed {E : Finset A} {x : PrimeSpectrum (ProdStrata E)}
    (hx : IsClosed {x}) : x ∈ zeroLocus (ProdStrata.ideal E) := by
  obtain ⟨y, hmem, hy⟩ := exists_specializes_zeroLocus_ideal x
  have := hy.mem_closed hx (by simp)
  grind only [= Set.mem_singleton_iff]

/-- If `E ⊆ F`, this is the canonical map `A_E → A_F`. -/
noncomputable def ProdStrata.map {E F : Finset A} (h : E ⊆ F) :
    ProdStrata E →ₐ[A] ProdStrata F :=
  Pi.algHom _ _ fun i ↦
    AlgHom.comp
      (Generalization.map <| by
        rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
        apply stratum_anti <;> simp)
      (Pi.evalAlgHom _ _ (i.restrict h))

lemma ProdStrata.mapsTo_map_specComap {E F : Finset A} (h : E ⊆ F) :
    Set.MapsTo (PrimeSpectrum.comap (map h).toRingHom)
      (zeroLocus (ideal F)) (zeroLocus (ideal E)) := by
  sorry

variable (A) in
/-- The diagram whose colimit is the w-localization of `A`. -/
noncomputable def diag : Finset A ⥤ CommAlgCat A where
  obj E := .of A (ProdStrata E)
  map {E F} f := CommAlgCat.ofHom (ProdStrata.map <| leOfHom f)
  map_id E := sorry
  map_comp := sorry

variable (A) in
/-- The w-localization of a ring as an object of `CommAlgCat A` is the colimit over
the rings `A_E`. -/
noncomputable def commAlgCat : CommAlgCat A :=
  colimit (diag A)

noncomputable def colimitPresentation : ColimitPresentation (Finset A) (commAlgCat A) where
  diag := diag A
  ι := (colimit.cocone _).ι
  isColimit := colimit.isColimit _

end WLocalization

/-- The w-localization of a ring. -/
def WLocalization (A : Type u) [CommRing A] : Type _ :=
  WLocalization.commAlgCat A

namespace WLocalization

variable (A : Type u) [CommRing A]

noncomputable instance commRing : CommRing (WLocalization A) :=
  inferInstanceAs <| CommRing (WLocalization.commAlgCat A)

noncomputable instance algebra : Algebra A (WLocalization A) :=
  inferInstanceAs <| Algebra A (WLocalization.commAlgCat A)

noncomputable def ideal : Ideal (WLocalization A) :=
  ⨆ E : Finset A, Ideal.map (colimitPresentation.ι.app E).hom (ProdStrata.ideal E)

lemma bijOn_algebraMap_specComap_zeroLocus_ideal :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (WLocalization A))
      (zeroLocus (ideal A)) .univ :=
  sorry

lemma exists_mem_zeroLocus_ideal_specializes (x : PrimeSpectrum (WLocalization A)) :
    ∃ y ∈ zeroLocus (ideal A), x ⤳ y :=
  sorry

lemma zeroLocus_ideal_eq : zeroLocus (ideal A) = closedPoints (PrimeSpectrum (WLocalization A)) :=
  sorry

instance isWLocalRing : IsWLocalRing (WLocalization A) :=
  sorry

instance (E : Finset A) : Finite (Stratification.Index E) := by
  classical
  refine Finite.of_injective (β := Set ↥E × Set ↥E)
    (fun i ↦ ((↑) ⁻¹' (i.left : Set A), (↑) ⁻¹' (i.right : Set A))) ?_
  rintro ⟨l₁, r₁, _, u₁⟩ ⟨l₂, r₂, _, u₂⟩ heq
  obtain ⟨hL, hR⟩ := Prod.mk.inj heq
  have aux : ∀ {s₁ s₂ : Finset A}, (s₁ : Set A) ⊆ E → (s₂ : Set A) ⊆ E →
      ((↑) : ↥E → A) ⁻¹' (s₁ : Set A) = ((↑) : ↥E → A) ⁻¹' (s₂ : Set A) → s₁ = s₂ := by
    intro s₁ s₂ h₁ h₂ hst
    ext a
    refine ⟨fun ha ↦ (Set.ext_iff.mp hst ⟨a, h₁ ha⟩).mp ha,
            fun ha ↦ (Set.ext_iff.mp hst ⟨a, h₂ ha⟩).mpr ha⟩
  have sub : ∀ {l r : Finset A}, (l : Set A) ∪ r = E →
      (l : Set A) ⊆ E ∧ (r : Set A) ⊆ E :=
    fun h ↦ ⟨fun a ha ↦ h ▸ Set.mem_union_left _ ha,
            fun a ha ↦ h ▸ Set.mem_union_right _ ha⟩
  obtain ⟨hl₁, hr₁⟩ := sub u₁
  obtain ⟨hl₂, hr₂⟩ := sub u₂
  exact (Stratification.Index.mk.injEq ..).mpr ⟨aux hl₁ hl₂ hL, aux hr₁ hr₂ hR⟩

lemma indZariski_prodStrata (E : Finset A) :
    Algebra.IndZariski A (ProdStrata E) := by
  change Algebra.IndZariski A
    (∀ i : Stratification.Index E, Generalization i.function i.ideal)
  exact Algebra.IndZariski.pi A _

instance indZariski : Algebra.IndZariski A (WLocalization A) := by
  have h := fun E => indZariski_prodStrata (A := A) E
  exact @Algebra.IndZariski.of_colimitPresentation A (WLocalization A) _ _ _
    (Finset A) _ _ colimitPresentation h

instance faithfullyFlat : Module.FaithfullyFlat A (WLocalization A) :=
  sorry

/-- If `V(I) ⊆ Spec A` consists only of closed points, then `V(I·WLocA) → V(I)` is a bijection.
This restricts the bijection `V(WLocalization.ideal A) ≃ Spec A` to `V(I·WLocA) ⊆ closedPoints`. -/
lemma bijOn_specComap_zeroLocus_map (I : Ideal A)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Set.BijOn (PrimeSpectrum.comap (algebraMap A (WLocalization A)))
      (zeroLocus (I.map (algebraMap A (WLocalization A)))) (zeroLocus I) := by
  have hsub : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
      zeroLocus (WLocalization.ideal A : Set (WLocalization A)) := by
    rw [zeroLocus_ideal_eq]
    intro q hq
    simp only [mem_zeroLocus, SetLike.coe_subset_coe, mem_closedPoints_iff,
      isClosed_singleton_iff_isMaximal] at hq ⊢
    set m := PrimeSpectrum.comap (algebraMap A (WLocalization A)) q with hm_def
    have hm : m.asIdeal.IsMaximal := by
      simpa [isClosed_singleton_iff_isMaximal] using hI (Ideal.le_comap_of_map_le hq)
    have : q.asIdeal.LiesOver m.asIdeal := ⟨PrimeSpectrum.ext_iff.mp hm_def⟩
    letI := Localization.AtPrime.algebraOfLiesOver m.asIdeal q.asIdeal
    have : Algebra.IsSeparable m.asIdeal.ResidueField q.asIdeal.ResidueField :=
      Algebra.IndEtale.isSeparable_residueField (R := A) (S := WLocalization A) m.asIdeal
        q.asIdeal
    exact Ideal.IsMaximal.of_isAlgebraic m.asIdeal q.asIdeal
  have hbij := bijOn_algebraMap_specComap_zeroLocus_ideal A
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [mem_zeroLocus, SetLike.coe_subset_coe] at hp ⊢
    rwa [comap_asIdeal, ← Ideal.map_le_iff_le_comap]
  · exact hbij.injOn.mono hsub
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := hbij.surjOn (Set.mem_univ q)
    refine ⟨p, ?_, hpq⟩
    simp only [mem_zeroLocus, SetLike.coe_subset_coe] at hq ⊢
    have hpq' : p.asIdeal.comap (algebraMap A (WLocalization A)) = q.asIdeal := by
      rw [← comap_asIdeal, hpq]
    rw [Ideal.map_le_iff_le_comap, hpq']
    exact hq

/-- If `V(I) ⊆ Spec A` consists only of closed points, then the quotient map
`A/I → WLocA/(I·WLocA)` is bijective. -/
lemma quotientMap_algebraMap_bijective_of_ideal (I : Ideal A)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A (WLocalization A)))
        (algebraMap A (WLocalization A)) I.le_comap_map) := by
  set f := algebraMap A (WLocalization A)
  set J := I.map f
  set φ := Ideal.quotientMap J f I.le_comap_map
  refine RingHom.BijectiveOnStalks.bijective_of_bijective ?_ ?_
  · exact (Algebra.IndZariski.bijectiveOnStalks_algebraMap A (WLocalization A)).quotientMap I
  · have hbij : Set.BijOn (PrimeSpectrum.comap f) (zeroLocus J) (zeroLocus I) :=
      bijOn_specComap_zeroLocus_map A I hI
    have hI_inj : Function.Injective (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
      PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hJ_inj : Function.Injective (PrimeSpectrum.comap (Ideal.Quotient.mk J)) :=
      PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hI_range : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = zeroLocus I := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have hJ_range : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = zeroLocus J := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have hcomm : ∀ y : PrimeSpectrum (WLocalization A ⧸ J),
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap φ y) =
          PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) y) := fun y ↦ by
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
        Ideal.quotientMap_comp_mk]
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
    · have hx : PrimeSpectrum.comap (Ideal.Quotient.mk J) x ∈ zeroLocus J :=
        hJ_range ▸ Set.mem_range_self x
      have hy : PrimeSpectrum.comap (Ideal.Quotient.mk J) y ∈ zeroLocus J :=
        hJ_range ▸ Set.mem_range_self y
      have heq : PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) x) =
          PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) y) := by
        rw [← hcomm, ← hcomm, hxy]
      exact hJ_inj (hbij.injOn hx hy heq)
    · obtain ⟨y', hy'mem, hy'⟩ := hbij.surjOn (hI_range ▸ Set.mem_range_self x)
      obtain ⟨y, rfl⟩ : ∃ y, PrimeSpectrum.comap (Ideal.Quotient.mk J) y = y' := by
        rwa [← Set.mem_range, hJ_range]
      exact ⟨y, hI_inj <| (hcomm y).trans hy'⟩

open PrimeSpectrum

end WLocalization
