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

/-- The locally closed subset `D(f) ∩ V(I)` of `Spec A`. -/
def locClosedSubset (f : A) (I : Ideal A) : Set (PrimeSpectrum A) :=
  basicOpen f ∩ zeroLocus I

/-- Characterization of `submonoid f I`: an element `a : A` lies in `submonoid f I` if and only
if `a` lies outside every prime in `locClosedSubset f I = D(f) ∩ V(I)`. -/
lemma mem_submonoid_iff (f : A) (I : Ideal A) (a : A) :
    a ∈ submonoid f I ↔ ∀ p ∈ locClosedSubset f I, a ∉ p.asIdeal := by
  rw [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
    IsScalarTower.algebraMap_apply A (A ⧸ I),
    ← PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (f := Ideal.Quotient.mk I f) (S := Localization.Away (Ideal.Quotient.mk I f))]
  refine ⟨fun hle p ⟨hpf, hpI⟩ hap ↦ ?_, fun h p_bar hp_bar hmka ↦ ?_⟩
  · simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hpf
    rw [PrimeSpectrum.mem_zeroLocus] at hpI
    obtain ⟨p_bar, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
      exact hpI
    have hpb_f : p_bar ∈ basicOpen (Ideal.Quotient.mk I f) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr fun h ↦ hpf (Ideal.mem_comap.mpr h)
    exact (PrimeSpectrum.mem_basicOpen _ _).mp (hle hpb_f) (Ideal.mem_comap.mp hap)
  · simp only [PrimeSpectrum.mem_basicOpen] at hp_bar ⊢
    refine h (PrimeSpectrum.comap (Ideal.Quotient.mk I) p_bar) ⟨?_, ?_⟩ hmka
    · simpa [PrimeSpectrum.mem_basicOpen] using hp_bar
    · rw [PrimeSpectrum.mem_zeroLocus]
      intro b hb
      rw [comap_asIdeal, SetLike.mem_coe, Ideal.mem_comap,
        Ideal.Quotient.eq_zero_iff_mem.mpr hb]
      exact p_bar.asIdeal.zero_mem

theorem submonoid_le {f f' : A} {I I' : Ideal A} (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    submonoid f I ≤ submonoid f' I' := by
  intro a ha
  rw [mem_submonoid_iff] at ha ⊢
  exact fun p hp ↦ ha p (h hp)

noncomputable def map {f f' : A} {I I' : Ideal A}
    (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    Generalization f I →ₐ[A] Generalization f' I' where
  toRingHom := IsLocalization.map (T := Generalization.submonoid f' I')
    (Generalization f' I') (RingHom.id A) (submonoid_le h)
  commutes' r := by simp

@[simp]
lemma map_id {f : A} {I : Ideal A} (h : locClosedSubset f I ⊆ locClosedSubset f I)
    (x : Generalization f I) : map h x = x := by
  simp [map]

/-- Composition of `Generalization.map`s is again a `Generalization.map`. -/
lemma map_map {f₁ f₂ f₃ : A} {I₁ I₂ I₃ : Ideal A}
    (h₁₂ : locClosedSubset f₂ I₂ ⊆ locClosedSubset f₁ I₁)
    (h₂₃ : locClosedSubset f₃ I₃ ⊆ locClosedSubset f₂ I₂)
    (x : Generalization f₁ I₁) :
    map h₂₃ (map h₁₂ x) = map (h₂₃.trans h₁₂) x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (submonoid f₁ I₁) x
  simp [map, IsLocalization.map_mk']

/-- The image of `Spec (Generalization f I)` in `Spec A` is equal to
the generalization hull of `D(f) ∩ V(I)`. -/
lemma range_algebraMap_generalization (f : A) (I : Ideal A) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) =
    generalizationHull (locClosedSubset f I) := by
  rw [PrimeSpectrum.localization_comap_range (Generalization f I) (submonoid f I)]
  ext p
  simp only [Set.mem_setOf_eq, mem_generalizationHull_iff]
  refine ⟨fun hdisj ↦ ?_, ?_⟩
  · have hf_not_rad : f ∉ Ideal.radical (p.asIdeal ⊔ I) := by
      rw [Ideal.mem_radical_iff]
      push Not
      intro n hfn
      rw [Submodule.mem_sup] at hfn
      obtain ⟨a, ha, b, hb, hab⟩ := hfn
      have ha_sub : a ∈ submonoid f I := by
        rw [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
          IsScalarTower.algebraMap_apply A (A ⧸ I)]
        have h_eq : (algebraMap A (A ⧸ I)) a = (algebraMap A (A ⧸ I)) (f ^ n) := by
          simp only [Ideal.Quotient.algebraMap_eq, ← hab, map_add,
            Ideal.Quotient.eq_zero_iff_mem.mpr hb, add_zero]
        rw [h_eq]
        have hmem : (Ideal.Quotient.mk I f) ^ n ∈ Submonoid.powers (Ideal.Quotient.mk I f) :=
          ⟨n, rfl⟩
        exact IsLocalization.map_units (Localization.Away (Ideal.Quotient.mk I f)) ⟨_, hmem⟩
      exact Set.disjoint_left.mp hdisj ha_sub ha
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf] at hf_not_rad
    push Not at hf_not_rad
    obtain ⟨q, ⟨hle, hq_prime⟩, hfq⟩ := hf_not_rad
    refine ⟨⟨q, hq_prime⟩, ⟨?_, ?_⟩, ?_⟩
    · simpa [PrimeSpectrum.mem_basicOpen] using hfq
    · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr fun x hx ↦ hle (Ideal.mem_sup_right hx)
    · rw [← PrimeSpectrum.le_iff_specializes]
      exact fun x hx ↦ hle (Ideal.mem_sup_left hx)
  · rintro ⟨q, hq, hpq⟩
    rw [← PrimeSpectrum.le_iff_specializes] at hpq
    exact Set.disjoint_left.mpr fun a ha_sub ha_p ↦
      (mem_submonoid_iff f I a).mp ha_sub q hq (hpq ha_p)

/-- Given `q ∈ locClosedSubset f I`, the prime ideal `q · Generalization f I` of
`Generalization f I` lies in `zeroLocus (ideal f I)` and contracts to `q`. -/
private lemma exists_mem_zeroLocus_ideal_specComap_eq {f : A} {I : Ideal A}
    {q : PrimeSpectrum A} (hq : q ∈ locClosedSubset f I) :
    ∃ y ∈ zeroLocus (ideal f I),
      PrimeSpectrum.comap (algebraMap A (Generalization f I)) y = q := by
  have hq_disj : Disjoint (submonoid f I : Set A) (q.asIdeal : Set A) :=
    Set.disjoint_left.mpr fun a ha ha_q ↦ (mem_submonoid_iff f I a).mp ha q hq ha_q
  refine ⟨⟨Ideal.map (algebraMap A (Generalization f I)) q.asIdeal,
    IsLocalization.isPrime_of_isPrime_disjoint (submonoid f I) (Generalization f I)
      q.asIdeal q.isPrime hq_disj⟩, ?_, ?_⟩
  · rw [PrimeSpectrum.mem_zeroLocus]
    intro z hz
    simp only [ideal, SetLike.mem_coe, RingHom.mem_ker] at hz
    obtain ⟨a, s, hzas⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
    rw [← hzas] at hz ⊢
    have hz' : algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a = 0 := by
      have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
      have h4 : toLocQuotient f I (IsLocalization.mk' (Generalization f I) a s *
          algebraMap A (Generalization f I) (s : A)) =
        toLocQuotient f I (algebraMap A (Generalization f I) a) := congr_arg _ h3
      rw [map_mul, hz, zero_mul, (toLocQuotient f I).commutes] at h4
      exact h4.symm
    have ha_q : a ∈ q.asIdeal := by
      have hqI : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hq.2
      have hfq : f ∉ q.asIdeal := hq.1
      rw [IsScalarTower.algebraMap_apply A (A ⧸ I)] at hz'
      obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
        (Submonoid.powers (Ideal.Quotient.mk I f))
        (Localization.Away (Ideal.Quotient.mk I f)) _).mp hz'
      have hfna : f ^ n * a ∈ I :=
        Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul, map_pow]; exact hc)
      exact (q.isPrime.mem_or_mem (hqI hfna)).resolve_left
        (mt (q.isPrime.mem_of_pow_mem n) hfq)
    rw [SetLike.mem_coe, IsLocalization.mk'_mem_map_algebraMap_iff (submonoid f I)]
    exact ⟨1, (submonoid f I).one_mem, by simpa using ha_q⟩
  · exact PrimeSpectrum.ext (IsLocalization.under_map_of_isPrime_disjoint (submonoid f I)
      (Generalization f I) q.isPrime hq_disj)

lemma bijOn_algebraMap_generalization_specComap_zeroLocus_ideal (f : A) (I : Ideal A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) (zeroLocus (ideal f I))
      (locClosedSubset f I) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [PrimeSpectrum.mem_zeroLocus] at hy
    have hdisj := ((IsLocalization.isPrime_iff_isPrime_disjoint (submonoid f I)
      (Generalization f I) y.asIdeal).mp y.isPrime).2
    have hf_sub : f ∈ submonoid f I := by
      rw [submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
        IsScalarTower.algebraMap_apply A (A ⧸ I)]
      have hmem : Ideal.Quotient.mk I f ∈ Submonoid.powers (Ideal.Quotient.mk I f) :=
        ⟨1, pow_one _⟩
      exact IsLocalization.map_units (Localization.Away (Ideal.Quotient.mk I f)) ⟨_, hmem⟩
    refine ⟨fun hfq ↦ Set.disjoint_left.mp hdisj hf_sub hfq, ?_⟩
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine hy ?_
    simp only [ideal, SetLike.mem_coe, RingHom.mem_ker]
    rw [(toLocQuotient f I).commutes, IsScalarTower.algebraMap_apply A (A ⧸ I)]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  · exact (PrimeSpectrum.localization_comap_isEmbedding (Generalization f I)
      (submonoid f I)).injective.injOn
  · intro q hq
    exact exists_mem_zeroLocus_ideal_specComap_eq hq

lemma exists_specializes_zeroLocus_ideal {f : A} (I : Ideal A)
    (x : PrimeSpectrum (Generalization f I)) : ∃ y ∈ zeroLocus (ideal f I), x ⤳ y := by
  have hp_range : PrimeSpectrum.comap (algebraMap A (Generalization f I)) x ∈
      generalizationHull (locClosedSubset f I) :=
    range_algebraMap_generalization f I ▸ ⟨x, rfl⟩
  rw [mem_generalizationHull_iff] at hp_range
  obtain ⟨q, hq_loc, hpq⟩ := hp_range
  obtain ⟨y, hy_mem, hy_eq⟩ := exists_mem_zeroLocus_ideal_specComap_eq hq_loc
  refine ⟨y, hy_mem, ?_⟩
  rw [← (PrimeSpectrum.localization_comap_isEmbedding (Generalization f I)
    (submonoid f I)).specializes_iff, hy_eq]
  exact hpq

/-- An element of the form `algebraMap A _ a` in `Generalization f I` is killed by
`toLocQuotient f I` iff some power of `f` times `a` lies in `I`. -/
lemma toLocQuotient_algebraMap_eq_zero_iff (a : A) :
    toLocQuotient f I (algebraMap A _ a) = 0 ↔ ∃ n : ℕ, f ^ n * a ∈ I := by
  rw [(toLocQuotient f I).commutes,
    IsScalarTower.algebraMap_apply A (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))]
  simp only [IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk I f)),
    Subtype.exists, Submonoid.mem_powers_iff, exists_prop, exists_exists_eq_and]
  refine exists_congr fun n ↦ ?_
  rw [Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

/-- If `I ≤ I'` and `f ∣ f'`, the canonical map `Generalization f I → Generalization f' I'`
sends the kernel ideal `ideal f I` into the kernel ideal `ideal f' I'`. -/
lemma map_ideal_le {f f' : A} {I I' : Ideal A}
    (h_sub : locClosedSubset f' I' ⊆ locClosedSubset f I) (hI : I ≤ I') (hf : f ∣ f') :
    (ideal f I).map (map h_sub).toRingHom ≤ ideal f' I' := by
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  simp only [Ideal.mem_comap, ideal, RingHom.mem_ker] at hz ⊢
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
  have h_alg_zero : toLocQuotient f I (algebraMap A _ a) = 0 := by
    have := congr_arg (toLocQuotient f I) (IsLocalization.mk'_spec _ a s)
    rw [map_mul, hz, zero_mul] at this
    exact this.symm
  obtain ⟨n, hfna⟩ := (toLocQuotient_algebraMap_eq_zero_iff f I a).mp h_alg_zero
  obtain ⟨g, hfg⟩ := hf
  have hf'na : f' ^ n * a ∈ I' := by
    rw [hfg, mul_pow, show f ^ n * g ^ n * a = g ^ n * (f ^ n * a) by ring]
    exact I'.mul_mem_left _ (hI hfna)
  have h_alg_zero' : algebraMap A (Localization.Away (Ideal.Quotient.mk I' f')) a = 0 := by
    rw [← (toLocQuotient f' I').commutes]
    exact (toLocQuotient_algebraMap_eq_zero_iff f' I' a).mpr ⟨n, hf'na⟩
  have hmk' := congr_arg (toLocQuotient f' I' ∘ map h_sub)
    (IsLocalization.mk'_spec (Generalization f I) a s)
  simp only [Function.comp_apply, map_mul, AlgHom.commutes, h_alg_zero'] at hmk'
  exact (submonoid_le h_sub s.2).mul_left_eq_zero.mp hmk'

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
@[ext]
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

omit [CommRing A] in
/-- An element `a : A` lies in the right part `i.right` of a stratification index iff it lies
in `E` but not in the left part `i.left`. -/
lemma Stratification.Index.mem_right_iff {E : Finset A}
    (i : Stratification.Index E) (a : A) : a ∈ i.right ↔ a ∈ E ∧ a ∉ i.left := by
  refine ⟨fun ha ↦ ⟨?_, ?_⟩, fun ⟨haE, hal⟩ ↦ ?_⟩
  · exact Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_right _ (Finset.mem_coe.mpr ha))
  · exact fun h ↦ Finset.disjoint_left.mp i.disjoint h ha
  · have hmem : (a : A) ∈ (i.left : Set A) ∪ (i.right : Set A) :=
      i.union_eq ▸ Finset.mem_coe.mpr haE
    exact hmem.resolve_left (fun hl ↦ hal (Finset.mem_coe.mp hl))

omit [CommRing A] in
/-- A `Stratification.Index E` is determined by its `left` part. -/
lemma Stratification.Index.ext_of_left {E : Finset A} {i j : Stratification.Index E}
    (h : i.left = j.left) : i = j := by
  refine Stratification.Index.ext h ?_
  ext a
  simp_rw [mem_right_iff, h]

omit [CommRing A] in
/-- In a disjoint union decomposition `E = E' ⨿ E''`, the right part is determined by the
left part as `E \ E'`. -/
lemma Stratification.Index.right_eq_sdiff {E : Finset A} [DecidableEq A]
    (i : Stratification.Index E) : i.right = E \ i.left := by
  ext a
  rw [Finset.mem_sdiff, mem_right_iff]

omit [CommRing A] in
instance (E : Finset A) : Finite (Stratification.Index E) :=
  Finite.of_injective (β := ↥E.powerset)
    (fun i ↦ ⟨i.left, Finset.mem_powerset.mpr fun _ ha ↦
      Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha))⟩)
    fun _ _ h ↦ Stratification.Index.ext_of_left (Subtype.ext_iff.mp h)

lemma locClosedSubset_function_ideal {E : Finset A} (i : Stratification.Index E) :
    Generalization.locClosedSubset i.function i.ideal = stratum i.left i.right := by
  rw [Generalization.locClosedSubset, stratum_eq_basicOpen_inter_zeroLocus]
  rfl

/-- Restrict a disjoint union decomposition of `F` to `E`. -/
@[simps]
noncomputable
def Stratification.Index.restrict {E F : Finset A} (i : Stratification.Index F)
    (h : E ⊆ F) : Stratification.Index E :=
  open Classical in
  { left := E ∩ i.left
    right := E ∩ i.right
    disjoint := i.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
    union_eq := by
      simp only [Finset.coe_inter]
      rw [← Set.inter_union_distrib_left, i.union_eq,
        Set.inter_eq_left.mpr (Finset.coe_subset.mpr h)] }

lemma Stratification.Index.function_restrict_dvd_function {E F : Finset A}
    (i : Stratification.Index F) (h : E ⊆ F) :
    (i.restrict h).function ∣ i.function := by
  classical
  simpa only [function, restrict_left] using
    Finset.prod_dvd_prod_of_subset _ _ id Finset.inter_subset_right

lemma Stratification.Index.ideal_restrict_le {E F : Finset A}
    (i : Stratification.Index F) (h : E ⊆ F) :
    (i.restrict h).ideal ≤ i.ideal := by
  classical
  simpa only [ideal, restrict_right] using
    Ideal.span_mono (Finset.coe_subset.mpr Finset.inter_subset_right)

lemma Stratification.Index.iUnion_stratum (E : Finset A) :
    ⋃ (i : Stratification.Index E), stratum i.left i.right = .univ := by
  classical
  refine Set.eq_univ_of_forall fun p ↦ Set.mem_iUnion.mpr ?_
  refine ⟨⟨E.filter (· ∉ p.asIdeal), E.filter (· ∈ p.asIdeal),
    (Finset.disjoint_filter_filter_not E E _).symm, ?_⟩, ?_, ?_⟩
  · rw [← Finset.coe_union, Finset.union_comm, Finset.filter_union_filter_not_eq]
  · simp +contextual [Set.mem_iInter, Finset.mem_filter]
  · simp +contextual [mem_zeroLocus, Set.subset_def]

/-- Given `a ∈ i.left` and `a ∉ j.left`, the strata of `i` and `j` are disjoint. -/
lemma stratum_disjoint_of_mem_left_not_mem_left {E : Finset A}
    {i j : Stratification.Index E} {a : A} (ha_i : a ∈ i.left) (ha_j : a ∉ j.left) :
    Disjoint (stratum i.left i.right) (stratum j.left j.right) := by
  have ha_in_E : a ∈ E := Finset.mem_coe.mp
    (i.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha_i))
  have ha_in_jr : a ∈ j.right :=
    (Stratification.Index.mem_right_iff j a).mpr ⟨ha_in_E, ha_j⟩
  rw [Set.disjoint_left]
  intro p hp_i hp_j
  simp only [stratum, Set.mem_inter_iff, Set.mem_iInter] at hp_i hp_j
  exact hp_i.1 a ha_i (hp_j.2 (Ideal.subset_span (Finset.mem_coe.mpr ha_in_jr)))

/-- The strata of distinct `Stratification.Index E` are disjoint subsets of `Spec A`. -/
lemma stratum_disjoint_of_ne {E : Finset A} {i j : Stratification.Index E} (h : i ≠ j) :
    Disjoint (stratum i.left i.right) (stratum j.left j.right) := by
  have hlne : i.left ≠ j.left := fun heq ↦ h (Stratification.Index.ext_of_left heq)
  rcases not_and_or.mp (mt Finset.Subset.antisymm_iff.mpr hlne) with hsub | hsub
  · obtain ⟨a, ha_i, ha_j⟩ := Finset.not_subset.mp hsub
    exact stratum_disjoint_of_mem_left_not_mem_left ha_i ha_j
  · obtain ⟨a, ha_j, ha_i⟩ := Finset.not_subset.mp hsub
    exact (stratum_disjoint_of_mem_left_not_mem_left ha_j ha_i).symm

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

/-- Membership in `ProdStrata.ideal E` is pointwise membership in each `Generalization.ideal`. -/
lemma ProdStrata.mem_ideal_iff {E : Finset A} (x : ProdStrata E) :
    x ∈ ProdStrata.ideal E ↔
      ∀ i : Stratification.Index E, x i ∈ Generalization.ideal i.function i.ideal :=
  Iff.rfl

/-- Contracting `q : PrimeSpectrum (Generalization i.function i.ideal)` along `Pi.evalRingHom`
and then along the algebra map equals contracting `q` directly along
`algebraMap A (Generalization i.function i.ideal)`. -/
lemma ProdStrata.comap_algebraMap_comap_evalRingHom {E : Finset A}
    (i : Stratification.Index E) (q : PrimeSpectrum (Generalization i.function i.ideal)) :
    PrimeSpectrum.comap (algebraMap A (ProdStrata E))
        (PrimeSpectrum.comap
          (Pi.evalRingHom (fun j : Stratification.Index E ↦
            Generalization j.function j.ideal) i) q) =
      PrimeSpectrum.comap (algebraMap A (Generalization i.function i.ideal)) q :=
  rfl

/-- The contraction `PrimeSpectrum.comap (Pi.evalRingHom _ i) q` lies in
`zeroLocus (ProdStrata.ideal E)` iff `q` lies in `zeroLocus (Generalization.ideal i.function
i.ideal)`. -/
lemma ProdStrata.comap_evalRingHom_mem_zeroLocus_ideal_iff {E : Finset A}
    (i : Stratification.Index E) (q : PrimeSpectrum (Generalization i.function i.ideal)) :
    ((PrimeSpectrum.comap
        (Pi.evalRingHom (fun j : Stratification.Index E ↦
          Generalization j.function j.ideal) i) q) : PrimeSpectrum (ProdStrata E)) ∈
      zeroLocus (ProdStrata.ideal E) ↔
    q ∈ zeroLocus (Generalization.ideal i.function i.ideal : Set _) := by
  classical
  refine ⟨fun hq a ha ↦ ?_, fun hq z hz ↦ ?_⟩
  · have hmem : (Pi.single i a : ProdStrata E) ∈ ProdStrata.ideal E := by
      rw [ProdStrata.mem_ideal_iff]
      intro j
      by_cases h : j = i
      · subst h
        rwa [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne h]
        exact Ideal.zero_mem _
    have hz_q := (PrimeSpectrum.mem_zeroLocus _ _).mp hq hmem
    rw [comap_asIdeal, SetLike.mem_coe, Ideal.mem_comap] at hz_q
    have hz' : ((Pi.single i a : ProdStrata E)) i ∈ q.asIdeal := hz_q
    rwa [Pi.single_eq_same] at hz'
  · rw [comap_asIdeal, SetLike.mem_coe, Ideal.mem_comap]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mp hq ((ProdStrata.mem_ideal_iff z).mp hz i)

lemma ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal (E : Finset A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (ProdStrata E))
    (zeroLocus (ProdStrata.ideal E)) .univ := by
  let R : Stratification.Index E → Type _ := fun i ↦ Generalization i.function i.ideal
  refine ⟨fun _ _ ↦ Set.mem_univ _, ?_, ?_⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨i₁, q₁, hq₁⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := R) (y₁ : PrimeSpectrum (∀ i, R i))
    obtain ⟨i₂, q₂, hq₂⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := R) (y₂ : PrimeSpectrum (∀ i, R i))
    have hq₁_mem : q₁ ∈ zeroLocus (Generalization.ideal i₁.function i₁.ideal : Set _) :=
      (ProdStrata.comap_evalRingHom_mem_zeroLocus_ideal_iff i₁ q₁).mp (hq₁ ▸ hy₁)
    have hq₂_mem : q₂ ∈ zeroLocus (Generalization.ideal i₂.function i₂.ideal : Set _) :=
      (ProdStrata.comap_evalRingHom_mem_zeroLocus_ideal_iff i₂ q₂).mp (hq₂ ▸ hy₂)
    have h_img₁ := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
      i₁.function i₁.ideal).mapsTo hq₁_mem
    have h_img₂ := (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
      i₂.function i₂.ideal).mapsTo hq₂_mem
    have heq' : PrimeSpectrum.comap (algebraMap A (Generalization i₁.function i₁.ideal)) q₁ =
        PrimeSpectrum.comap (algebraMap A (Generalization i₂.function i₂.ideal)) q₂ := by
      rw [← ProdStrata.comap_algebraMap_comap_evalRingHom i₁ q₁,
        ← ProdStrata.comap_algebraMap_comap_evalRingHom i₂ q₂, hq₁, hq₂, heq]
    obtain rfl : i₁ = i₂ := by
      by_contra hne
      rw [locClosedSubset_function_ideal] at h_img₁ h_img₂
      exact Set.disjoint_left.mp (stratum_disjoint_of_ne hne) h_img₁ (heq' ▸ h_img₂)
    have hq_eq : q₁ = q₂ :=
      (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
        i₁.function i₁.ideal).injOn hq₁_mem hq₂_mem heq'
    rw [← hq₁, ← hq₂, hq_eq]
  · intro p _
    obtain ⟨i, hi⟩ : ∃ i : Stratification.Index E, p ∈ stratum i.left i.right := by
      simpa using Set.eq_univ_iff_forall.mp (Stratification.Index.iUnion_stratum E) p
    rw [← locClosedSubset_function_ideal] at hi
    obtain ⟨q, hq_mem, hq_eq⟩ :=
      (Generalization.bijOn_algebraMap_generalization_specComap_zeroLocus_ideal
        i.function i.ideal).surjOn hi
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q,
      (ProdStrata.comap_evalRingHom_mem_zeroLocus_ideal_iff i q).mpr hq_mem, ?_⟩
    rw [ProdStrata.comap_algebraMap_comap_evalRingHom, hq_eq]

/-- `Spec (ProdStrata E) → Spec A` is surjective. -/
lemma ProdStrata.specComap_surjective (E : Finset A) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (ProdStrata E))) := fun p ↦
  let ⟨q, _, hq⟩ :=
    (ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal E).surjOn (Set.mem_univ p)
  ⟨q, hq⟩

lemma ProdStrata.exists_specializes_zeroLocus_ideal {E : Finset A}
    (x : PrimeSpectrum (ProdStrata E)) :
    ∃ y ∈ zeroLocus (ProdStrata.ideal E), x ⤳ y := by
  let R : Stratification.Index E → Type _ := fun i ↦ Generalization i.function i.ideal
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (R := R) (x : PrimeSpectrum (∀ i, R i))
  obtain ⟨y_i, hy_mem, hy_spec⟩ := Generalization.exists_specializes_zeroLocus_ideal i.ideal q
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) y_i,
    (ProdStrata.comap_evalRingHom_mem_zeroLocus_ideal_iff i y_i).mpr hy_mem, ?_⟩
  rw [← hq]
  exact Specializes.map hy_spec (PrimeSpectrum.continuous_comap _)

lemma ProdStrata.mem_zeroLocus_ideal_of_isClosed {E : Finset A} {x : PrimeSpectrum (ProdStrata E)}
    (hx : IsClosed {x}) : x ∈ zeroLocus (ProdStrata.ideal E) := by
  obtain ⟨y, hmem, hy⟩ := exists_specializes_zeroLocus_ideal x
  have := hy.mem_closed hx (by simp)
  grind only [= Set.mem_singleton_iff]

lemma ProdStrata.locClosedSubset_subset_restrict {E F : Finset A} (h : E ⊆ F)
    (i : Stratification.Index F) :
    Generalization.locClosedSubset i.function i.ideal ⊆
      Generalization.locClosedSubset (i.restrict h).function (i.restrict h).ideal := by
  rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
  exact stratum_anti (by simp) (by simp)

/-- If `E ⊆ F`, this is the canonical map `A_E → A_F`. -/
noncomputable def ProdStrata.map {E F : Finset A} (h : E ⊆ F) :
    ProdStrata E →ₐ[A] ProdStrata F :=
  Pi.algHom _ _ fun i ↦
    AlgHom.comp (Generalization.map (locClosedSubset_subset_restrict h i))
      (Pi.evalAlgHom _ _ (i.restrict h))

@[simp]
lemma ProdStrata.map_apply {E F : Finset A} (h : E ⊆ F) (x : ProdStrata E)
    (i : Stratification.Index F) :
    ProdStrata.map h x i =
      Generalization.map (locClosedSubset_subset_restrict h i) (x (i.restrict h)) := rfl

lemma ProdStrata.map_ideal_le {E F : Finset A} (h : E ⊆ F) :
    (ProdStrata.ideal E).map (map h).toRingHom ≤ ProdStrata.ideal F := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  refine (Ideal.mem_pi _ _).mpr fun i ↦ ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_apply]
  exact Generalization.map_ideal_le _ (i.ideal_restrict_le h) (i.function_restrict_dvd_function h)
    (Ideal.mem_map_of_mem _ ((Ideal.mem_pi _ _).mp hx _))

lemma ProdStrata.mapsTo_map_specComap {E F : Finset A} (h : E ⊆ F) :
    Set.MapsTo (PrimeSpectrum.comap (map h).toRingHom)
      (zeroLocus (ideal F)) (zeroLocus (ideal E)) := by
  intro p hp
  simp only [mem_zeroLocus, SetLike.coe_subset_coe, comap_asIdeal,
    ← Ideal.map_le_iff_le_comap] at hp ⊢
  exact (map_ideal_le h).trans hp

variable (A) in
/-- The diagram whose colimit is the w-localization of `A`. -/
noncomputable def diag : Finset A ⥤ CommAlgCat A where
  obj E := .of A (ProdStrata E)
  map {E F} f := CommAlgCat.ofHom (ProdStrata.map <| leOfHom f)
  map_id E := by
    classical
    ext x i
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_id, AlgHom.coe_id, id_eq,
      ProdStrata.map_apply]
    generalize_proofs h pf
    have hi : i.restrict h = i := Stratification.Index.ext
      (Finset.inter_eq_right.mpr <| Finset.coe_subset.mp <|
        Set.subset_union_left.trans i.union_eq.le)
      (Finset.inter_eq_right.mpr <| Finset.coe_subset.mp <|
        Set.subset_union_right.trans i.union_eq.le)
    revert pf
    rw [hi]
    intro pf
    exact Generalization.map_id pf (x i)
  map_comp {E F G} f g := by
    classical
    ext x i
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply,
      ProdStrata.map_apply, Generalization.map_map]
    generalize_proofs hfg pf pfg pff pf'
    have hi : (i.restrict pfg).restrict pff = i.restrict hfg :=
      Stratification.Index.ext
        (by simp only [Stratification.Index.restrict_left,
            ← Finset.inter_assoc, Finset.inter_eq_left.mpr pff])
        (by simp only [Stratification.Index.restrict_right,
            ← Finset.inter_assoc, Finset.inter_eq_left.mpr pff])
    revert pf'
    rw [hi]
    intro pf'
    rfl

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

/-! ### Colimit-presentation helpers

These declarations expose the colimit presentation of `WLocalization A` at the level of
elements: `ιRingHom A E` is the structural ring hom from a finite stage, `exists_rep` says
every element comes from some stage, and the various `ideal_map_*` lemmas package the
directed system used to describe `ideal A`. -/

/-- The ring hom `ProdStrata E → WLocalization A` induced by the colimit presentation. -/
noncomputable def ιRingHom (E : Finset A) : ProdStrata E →+* WLocalization A :=
  ((colimitPresentation (A := A)).ι.app E).hom.toRingHom

/-- The `CommRingCat`-level cocone for the colimit presentation. -/
noncomputable def commRingCatCocone :
    Cocone (diag A ⋙ forget₂ (CommAlgCat A) CommRingCat) :=
  (forget₂ (CommAlgCat A) CommRingCat).mapCocone (colimit.cocone (diag A))

/-- The `CommRingCat`-level cocone is a colimit cocone. -/
noncomputable def commRingCatIsColimit : IsColimit (commRingCatCocone A) :=
  isColimitOfPreserves (forget₂ (CommAlgCat A) CommRingCat) (colimit.isColimit _)

/-- Every element of `WLocalization A` is in the image of `ιRingHom` from some stage. -/
lemma exists_rep (x : WLocalization A) :
    ∃ (E : Finset A) (y : ProdStrata E), ιRingHom A E y = x := by
  obtain ⟨E, y, hy⟩ := Concrete.isColimit_exists_rep _ (commRingCatIsColimit A) x
  exact ⟨E, y, hy⟩

/-- The cocone relation: `ιRingHom` commutes with `ProdStrata.map` for `E ⊆ G`. -/
lemma ιRingHom_map_apply {E G : Finset A} (h : E ⊆ G) (c : ProdStrata E) :
    ιRingHom A G (ProdStrata.map h c) = ιRingHom A E c := by
  have hw : (diag A).map (homOfLE h) ≫ colimit.ι (diag A) G = colimit.ι (diag A) E :=
    colimit.w (diag A) (homOfLE h)
  have key : ((diag A).map (homOfLE h) ≫ colimit.ι (diag A) G).hom c =
      (colimit.ι (diag A) E).hom c :=
    congrArg (fun f ↦ f.hom c) hw
  simpa [diag] using key

noncomputable def ideal : Ideal (WLocalization A) :=
  ⨆ E : Finset A, Ideal.map (ιRingHom A E) (ProdStrata.ideal E)

/-- The defining presentation of `ideal A` as a supremum over finite stages. -/
lemma ideal_eq_iSup :
    ideal A = ⨆ E : Finset A, Ideal.map (ιRingHom A E) (ProdStrata.ideal E) :=
  rfl

/-- Every element of `Ideal.map (ιRingHom E) (ProdStrata.ideal E)` is the image of an
element of `ProdStrata.ideal G` for some stage `G` (which may differ from `E`). -/
lemma exists_rep_of_mem_ideal_map (E : Finset A) (b : WLocalization A)
    (hb : b ∈ Ideal.map (ιRingHom A E) (ProdStrata.ideal E)) :
    ∃ (G : Finset A) (d : ProdStrata G), d ∈ ProdStrata.ideal G ∧ ιRingHom A G d = b := by
  classical
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    exact ⟨E, c, hc, rfl⟩
  | zero => exact ⟨∅, 0, Ideal.zero_mem _, map_zero _⟩
  | add b₁ b₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, d₁, hd₁, hι₁⟩ := ih₁
    obtain ⟨G₂, d₂, hd₂, hι₂⟩ := ih₂
    refine ⟨G₁ ∪ G₂,
      ProdStrata.map Finset.subset_union_left d₁ +
        ProdStrata.map Finset.subset_union_right d₂,
      Ideal.add_mem _
        (ProdStrata.map_ideal_le Finset.subset_union_left
          (Ideal.mem_map_of_mem (ProdStrata.map Finset.subset_union_left).toRingHom hd₁))
        (ProdStrata.map_ideal_le Finset.subset_union_right
          (Ideal.mem_map_of_mem (ProdStrata.map Finset.subset_union_right).toRingHom hd₂)), ?_⟩
    rw [map_add, ιRingHom_map_apply A Finset.subset_union_left,
      ιRingHom_map_apply A Finset.subset_union_right, hι₁, hι₂]
  | smul r b₁ _ ih₁ =>
    obtain ⟨G₁, d₁, hd₁, hι₁⟩ := ih₁
    obtain ⟨F, s, hs⟩ := exists_rep A r
    refine ⟨G₁ ∪ F,
      ProdStrata.map Finset.subset_union_right s *
        ProdStrata.map Finset.subset_union_left d₁,
      Ideal.mul_mem_left _ _
        (ProdStrata.map_ideal_le Finset.subset_union_left
          (Ideal.mem_map_of_mem (ProdStrata.map Finset.subset_union_left).toRingHom hd₁)), ?_⟩
    rw [smul_eq_mul, map_mul, ιRingHom_map_apply A Finset.subset_union_right,
      ιRingHom_map_apply A Finset.subset_union_left, hs, hι₁]

/-- The family `E ↦ Ideal.map (ιRingHom E) (ProdStrata.ideal E)` is monotone. -/
lemma ideal_map_mono {E G : Finset A} (h : E ⊆ G) :
    Ideal.map (ιRingHom A E) (ProdStrata.ideal E) ≤
      Ideal.map (ιRingHom A G) (ProdStrata.ideal G) := by
  have hcomp : (ιRingHom A G).comp (ProdStrata.map h).toRingHom = ιRingHom A E := by
    ext c; exact ιRingHom_map_apply A h c
  rw [← hcomp, ← Ideal.map_map]
  exact Ideal.map_mono (ProdStrata.map_ideal_le h)

/-- The family `E ↦ Ideal.map (ιRingHom E) (ProdStrata.ideal E)` is directed. -/
lemma ideal_map_directed :
    Directed (· ≤ ·) (fun E : Finset A ↦
      Ideal.map (ιRingHom A E) (ProdStrata.ideal E)) := by
  classical
  exact fun E F ↦ ⟨E ∪ F, ideal_map_mono A Finset.subset_union_left,
    ideal_map_mono A Finset.subset_union_right⟩

/-- At each finite stage, the comap of a prime sup the stage ideal is not the whole ring. -/
lemma comap_ιRingHom_sup_ideal_ne_top (E : Finset A)
    (x : PrimeSpectrum (WLocalization A)) :
    (PrimeSpectrum.comap (ιRingHom A E) x).asIdeal ⊔ ProdStrata.ideal E ≠ ⊤ := by
  intro htop
  obtain ⟨t, ht_mem, ht_spec⟩ := ProdStrata.exists_specializes_zeroLocus_ideal
    (PrimeSpectrum.comap (ιRingHom A E) x)
  have hle : (PrimeSpectrum.comap (ιRingHom A E) x).asIdeal ⊔ ProdStrata.ideal E ≤ t.asIdeal :=
    sup_le ((PrimeSpectrum.le_iff_specializes _ _).mpr ht_spec)
      ((PrimeSpectrum.mem_zeroLocus _ _).mp ht_mem)
  exact t.isPrime.ne_top (top_le_iff.mp (htop ▸ hle))

/-- The algebra map `A → WLocalization A` factors through each stage `ιRingHom A E`. -/
lemma algebraMap_eq_comp_ι (E : Finset A) :
    algebraMap A (WLocalization A) =
      (ιRingHom A E).comp (algebraMap A (ProdStrata E)) := by
  ext a
  exact (((colimitPresentation (A := A)).ι.app E).hom.commutes a).symm

/-- A prime lies in `V(ideal A)` if and only if its comap to each finite stage lies in
the corresponding stage ideal. -/
lemma mem_zeroLocus_ideal_iff (p : PrimeSpectrum (WLocalization A)) :
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
    refine iSup_le fun E ↦ ?_
    rw [Ideal.map_le_iff_le_comap]
    exact hall E

/-- Transition maps preserve `Ideal.map (algebraMap A _) q`. -/
lemma map_mem_algebraMap_ideal {E G : Finset A} (h : E ⊆ G) {t : ProdStrata E}
    {q : Ideal A} (ht : t ∈ Ideal.map (algebraMap A (ProdStrata E)) q) :
    ProdStrata.map h t ∈ Ideal.map (algebraMap A (ProdStrata G)) q := by
  have hle : Ideal.map (ProdStrata.map h).toRingHom
        (Ideal.map (algebraMap A (ProdStrata E)) q) ≤
      Ideal.map (algebraMap A (ProdStrata G)) q := by
    rw [Ideal.map_map,
      show (ProdStrata.map h).toRingHom.comp (algebraMap A (ProdStrata E)) =
        algebraMap A (ProdStrata G) from AlgHom.comp_algebraMap (ProdStrata.map h)]
  exact hle (Ideal.mem_map_of_mem (ProdStrata.map h).toRingHom ht)

/-- Every element of `Ideal.map (algebraMap A (WLocalization A)) q` is represented at some
finite stage by an element of `Ideal.map (algebraMap A (ProdStrata G)) q`. -/
lemma algebraMap_ideal_map_mem_exists (q : Ideal A) (b : WLocalization A)
    (hb : b ∈ Ideal.map (algebraMap A (WLocalization A)) q) :
    ∃ (G : Finset A) (t : ProdStrata G),
      t ∈ Ideal.map (algebraMap A (ProdStrata G)) q ∧ ιRingHom A G t = b := by
  classical
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨a, ha, rfl⟩ := hb
    refine ⟨∅, algebraMap A (ProdStrata ∅) a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [algebraMap_eq_comp_ι A ∅]; rfl
  | zero => exact ⟨∅, 0, Ideal.zero_mem _, map_zero _⟩
  | add b₁ b₂ _ _ ih₁ ih₂ =>
    obtain ⟨G₁, t₁, ht₁, hι₁⟩ := ih₁
    obtain ⟨G₂, t₂, ht₂, hι₂⟩ := ih₂
    refine ⟨G₁ ∪ G₂,
      ProdStrata.map Finset.subset_union_left t₁ +
        ProdStrata.map Finset.subset_union_right t₂,
      Ideal.add_mem _
        (map_mem_algebraMap_ideal A Finset.subset_union_left ht₁)
        (map_mem_algebraMap_ideal A Finset.subset_union_right ht₂), ?_⟩
    rw [map_add, ιRingHom_map_apply A Finset.subset_union_left,
      ιRingHom_map_apply A Finset.subset_union_right, hι₁, hι₂]
  | smul r b₁ _ ih₁ =>
    obtain ⟨G₁, t₁, ht₁, hι₁⟩ := ih₁
    obtain ⟨F, s, hs⟩ := exists_rep A r
    refine ⟨G₁ ∪ F,
      ProdStrata.map Finset.subset_union_right s *
        ProdStrata.map Finset.subset_union_left t₁,
      Ideal.mul_mem_left _ _
        (map_mem_algebraMap_ideal A Finset.subset_union_left ht₁), ?_⟩
    rw [smul_eq_mul, map_mul, ιRingHom_map_apply A Finset.subset_union_right,
      ιRingHom_map_apply A Finset.subset_union_left, hs, hι₁]

/-- If two elements at stage `G` become equal in `WLocalization A`, they already become
equal after passing to some later stage `H ⊇ G`. -/
lemma exists_map_eq_of_ι_eq (G : Finset A) (x y : ProdStrata G)
    (h : ιRingHom A G x = ιRingHom A G y) :
    ∃ (H : Finset A) (hGH : G ⊆ H), ProdStrata.map hGH x = ProdStrata.map hGH y := by
  -- Lift `ιRingHom` to the type level via `forget CommRingCat` and use the filtered-colimit
  -- equality criterion.
  let F : Finset A ⥤ Type u :=
    (diag A ⋙ forget₂ (CommAlgCat A) CommRingCat) ⋙ forget CommRingCat
  let c : Cocone F := (forget CommRingCat).mapCocone (commRingCatCocone A)
  have hc : IsColimit c := isColimitOfPreserves (forget CommRingCat) (commRingCatIsColimit A)
  obtain ⟨H, f, hf⟩ := (Limits.IsColimit.eq_iff' hc x y).mp h
  exact ⟨H, leOfHom f, hf⟩

set_option maxHeartbeats 800000 in
lemma bijOn_algebraMap_specComap_zeroLocus_ideal :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (WLocalization A))
      (zeroLocus (ideal A)) .univ := by
  classical
  refine ⟨fun _ _ ↦ Set.mem_univ _, ?injOn, ?surjOn⟩
  case injOn =>
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := (mem_zeroLocus_ideal_iff A p₁).mp hp₁
    have h2 := (mem_zeroLocus_ideal_iff A p₂).mp hp₂
    -- For each stage `E`, the comaps of `p₁` and `p₂` agree.
    have heq_factor : ∀ E : Finset A,
        PrimeSpectrum.comap (ιRingHom A E) p₁ =
          PrimeSpectrum.comap (ιRingHom A E) p₂ := by
      intro E
      have h_eq_E : PrimeSpectrum.comap (algebraMap A (ProdStrata E))
          (PrimeSpectrum.comap (ιRingHom A E) p₁) =
            PrimeSpectrum.comap (algebraMap A (ProdStrata E))
              (PrimeSpectrum.comap (ιRingHom A E) p₂) := by
        have hfact : ∀ p : PrimeSpectrum (WLocalization A),
            PrimeSpectrum.comap (algebraMap A (WLocalization A)) p =
              PrimeSpectrum.comap (algebraMap A (ProdStrata E))
                (PrimeSpectrum.comap (ιRingHom A E) p) := by
          intro p
          ext a
          simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
          rw [algebraMap_eq_comp_ι A E]
          rfl
        rw [← hfact, ← hfact]; exact heq
      exact (ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal E).injOn
        (h1 E) (h2 E) h_eq_E
    -- Every element of `WLocalization A` factors through some `ιRingHom A E`.
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    obtain ⟨E, y, rfl⟩ := exists_rep A x
    have := (PrimeSpectrum.ext_iff.mp (heq_factor E))
    exact Iff.intro
      (fun hy ↦ Ideal.ext_iff.mp this y |>.mp hy)
      (fun hy ↦ Ideal.ext_iff.mp this y |>.mpr hy)
  case surjOn =>
    intro q _
    -- Build the ideal `q.map(algebraMap) + ideal A` and the submonoid image of `q.primeCompl`.
    set I_q := Ideal.map (algebraMap A (WLocalization A)) q.asIdeal ⊔ ideal A with hI_q
    set S := q.asIdeal.primeCompl.map (algebraMap A (WLocalization A)).toMonoidHom with hS
    have hDisj : Disjoint (I_q : Set (WLocalization A)) S := by
      refine Set.disjoint_left.mpr fun x hxI hxS ↦ ?_
      obtain ⟨a, ha_not_q, rfl⟩ := hxS
      rw [SetLike.mem_coe, Submodule.mem_sup] at hxI
      obtain ⟨b, hb_map, c, hc_ideal, hbc⟩ := hxI
      -- Decompose membership in `ideal A` via directedness.
      change c ∈ ideal A at hc_ideal
      rw [ideal_eq_iSup, Submodule.mem_iSup_of_directed _ (ideal_map_directed A)] at hc_ideal
      obtain ⟨E₁, hcE⟩ := hc_ideal
      obtain ⟨E₂, b', hb'_mem, hb'⟩ :=
        algebraMap_ideal_map_mem_exists A q.asIdeal b hb_map
      obtain ⟨E₃, c', hc', hc'eq⟩ := exists_rep_of_mem_ideal_map A E₁ c hcE
      set G := E₂ ∪ E₃ with hG
      -- At stage `G`, the sum of representatives maps to `algebraMap a`.
      have hsum_eq :
          ιRingHom A G
              (ProdStrata.map Finset.subset_union_left b' +
                ProdStrata.map Finset.subset_union_right c') =
            algebraMap A (WLocalization A) a := by
        rw [map_add, ιRingHom_map_apply A Finset.subset_union_left,
          ιRingHom_map_apply A Finset.subset_union_right, hb', hc'eq, hbc]
        rfl
      have htype_eq :
          ιRingHom A G
              (ProdStrata.map Finset.subset_union_left b' +
                ProdStrata.map Finset.subset_union_right c') =
            ιRingHom A G ((algebraMap A (ProdStrata G)) a) := by
        rw [hsum_eq, algebraMap_eq_comp_ι A G]; rfl
      obtain ⟨H, hGH, hH_eq⟩ := exists_map_eq_of_ι_eq A G _ _ htype_eq
      obtain ⟨y_H, hy_mem, hy_comap⟩ :=
        (ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal H).surjOn (Set.mem_univ q)
      have ha_not_mem : (algebraMap A (ProdStrata H)) a ∉ y_H.asIdeal := by
        intro hmem
        have : a ∈ q.asIdeal := by
          rw [← hy_comap]; exact Ideal.mem_comap.mpr hmem
        exact ha_not_q this
      apply ha_not_mem
      -- Combine the stage equality with naturality of `algebraMap`.
      have halg_comm :
          ProdStrata.map hGH ((algebraMap A (ProdStrata G)) a) =
            algebraMap A (ProdStrata H) a :=
        congr_fun (congr_arg DFunLike.coe (AlgHom.comp_algebraMap (ProdStrata.map hGH))) a
      have hH_eq' :
          algebraMap A (ProdStrata H) a =
            ProdStrata.map hGH
              (ProdStrata.map Finset.subset_union_left b' +
                ProdStrata.map Finset.subset_union_right c') := by
        rw [← halg_comm, hH_eq]
      rw [hH_eq', map_add]
      refine y_H.asIdeal.add_mem ?_ ?_
      · have hb'G : ProdStrata.map Finset.subset_union_left b' ∈
            Ideal.map (algebraMap A (ProdStrata G)) q.asIdeal :=
          map_mem_algebraMap_ideal A Finset.subset_union_left hb'_mem
        have hb'H : ProdStrata.map hGH (ProdStrata.map Finset.subset_union_left b') ∈
            Ideal.map (algebraMap A (ProdStrata H)) q.asIdeal :=
          map_mem_algebraMap_ideal A hGH hb'G
        exact Ideal.map_le_iff_le_comap.mpr
          (ge_of_eq (congr_arg PrimeSpectrum.asIdeal hy_comap)) hb'H
      · have hc'G : ProdStrata.map Finset.subset_union_right c' ∈ ProdStrata.ideal G :=
          ProdStrata.map_ideal_le _
            (Ideal.mem_map_of_mem (ProdStrata.map Finset.subset_union_right).toRingHom hc')
        have hc'H : ProdStrata.map hGH (ProdStrata.map Finset.subset_union_right c') ∈
            ProdStrata.ideal H :=
          ProdStrata.map_ideal_le _
            (Ideal.mem_map_of_mem (ProdStrata.map hGH).toRingHom hc'G)
        exact ((PrimeSpectrum.mem_zeroLocus _ _).mp hy_mem) hc'H
    obtain ⟨p, hp_prime, hp_le, hp_disj⟩ :=
      Ideal.exists_le_prime_disjoint I_q S hDisj
    refine ⟨⟨p, hp_prime⟩, ?_, ?_⟩
    · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr
        (SetLike.coe_subset_coe.mpr (le_sup_right.trans hp_le))
    · apply PrimeSpectrum.ext
      apply Ideal.ext
      intro a
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
      · by_contra ha_not
        exact Set.disjoint_left.mp hp_disj (SetLike.mem_coe.mpr ha)
          (Submonoid.mem_map.mpr ⟨a, ha_not, rfl⟩)
      · exact hp_le (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

lemma exists_mem_zeroLocus_ideal_specializes (x : PrimeSpectrum (WLocalization A)) :
    ∃ y ∈ zeroLocus (ideal A), x ⤳ y := by
  suffices h : x.asIdeal ⊔ ideal A ≠ ⊤ by
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨hle₁, hle₂⟩ := sup_le_iff.mp hle
    exact ⟨⟨m, hm.isPrime⟩,
      (PrimeSpectrum.mem_zeroLocus _ _).mpr hle₂,
      (PrimeSpectrum.le_iff_specializes _ _).mp hle₁⟩
  intro htop
  have h1 : (1 : WLocalization A) ∈ x.asIdeal ⊔ ideal A := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  rw [ideal_eq_iSup, Submodule.mem_iSup_of_directed _ (ideal_map_directed A)] at hb
  obtain ⟨E₀, hbE⟩ := hb
  obtain ⟨G, d, hd, hιd⟩ := exists_rep_of_mem_ideal_map A E₀ b hbE
  have hab' : (1 : WLocalization A) - b = a := (eq_sub_of_add_eq hab).symm
  have h_one_mem : (1 : ProdStrata G) ∈
      (PrimeSpectrum.comap (ιRingHom A G) x).asIdeal ⊔ ProdStrata.ideal G := by
    refine Submodule.mem_sup.mpr ⟨1 - d, ?_, d, hd, sub_add_cancel 1 d⟩
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_sub, map_one, hιd, hab']
      using ha
  exact comap_ιRingHom_sup_ideal_ne_top A G x
    (((PrimeSpectrum.comap (ιRingHom A G) x).asIdeal ⊔
      ProdStrata.ideal G).eq_top_iff_one.mpr h_one_mem)

lemma zeroLocus_ideal_eq : zeroLocus (ideal A) = closedPoints (PrimeSpectrum (WLocalization A)) :=
  sorry

instance isWLocalRing : IsWLocalRing (WLocalization A) :=
  sorry

lemma indZariski_prodStrata {A : Type u} [CommRing A] (E : Finset A) :
    Algebra.IndZariski A (ProdStrata E) :=
  inferInstanceAs <| Algebra.IndZariski A
    (∀ i : Stratification.Index E, Generalization i.function i.ideal)

instance ProdStrata.faithfullyFlat (E : Finset A) :
    Module.FaithfullyFlat A (ProdStrata E) := by
  have : Algebra.IndZariski A (ProdStrata E) := indZariski_prodStrata E
  exact Module.FaithfullyFlat.of_comap_surjective (ProdStrata.specComap_surjective E)

instance indZariski : Algebra.IndZariski A (WLocalization A) := by
  have h := fun E => indZariski_prodStrata (A := A) E
  exact @Algebra.IndZariski.of_colimitPresentation A (WLocalization A) _ _ _
    (Finset A) _ _ colimitPresentation h

instance faithfullyFlat : Module.FaithfullyFlat A (WLocalization A) :=
  CommAlgCat.faithfullyFlat_of_colimitPresentation colimitPresentation fun E ↦
    inferInstanceAs (Module.FaithfullyFlat A (ProdStrata E))

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
