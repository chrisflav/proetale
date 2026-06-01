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

/-- If two indices share `left` and `right`, then transporting a `ProdStrata`-component along
`Generalization.map` recovers the other component. -/
private lemma ProdStrata.map_transport_eq {E : Finset A}
    {i j : Stratification.Index E}
    (hl : j.left = i.left) (hr : j.right = i.right)
    (h : Generalization.locClosedSubset i.function i.ideal ⊆
         Generalization.locClosedSubset j.function j.ideal)
    (x : ProdStrata E) :
    Generalization.map h (x j) = x i := by
  obtain rfl : j = i := Stratification.Index.ext hl hr
  simp

/-- Two `Generalization.map` calls into the same target, starting from `ProdStrata`-components
of indices that share `left` and `right`, give equal results. -/
private lemma ProdStrata.map_transport_comp_eq {E : Finset A} {f' : A} {I' : Ideal A}
    {j₁ j₂ : Stratification.Index E}
    (hl : j₁.left = j₂.left) (hr : j₁.right = j₂.right)
    (h₁ : Generalization.locClosedSubset f' I' ⊆
            Generalization.locClosedSubset j₁.function j₁.ideal)
    (h₂ : Generalization.locClosedSubset f' I' ⊆
            Generalization.locClosedSubset j₂.function j₂.ideal)
    (x : ProdStrata E) :
    Generalization.map h₁ (x j₁) = Generalization.map h₂ (x j₂) := by
  obtain rfl : j₁ = j₂ := Stratification.Index.ext hl hr
  rfl

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
    refine ProdStrata.map_transport_eq ?_ ?_ _ x
    · exact Finset.inter_eq_right.mpr <| Finset.coe_subset.mp <|
        Set.subset_union_left.trans i.union_eq.le
    · exact Finset.inter_eq_right.mpr <| Finset.coe_subset.mp <|
        Set.subset_union_right.trans i.union_eq.le
  map_comp {E F G} f g := by
    classical
    ext x i
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply,
      ProdStrata.map_apply, Generalization.map_map]
    refine ProdStrata.map_transport_comp_eq ?_ ?_ _ _ x
    · simp only [Stratification.Index.restrict_left,
        ← Finset.inter_assoc, Finset.inter_eq_left.mpr (leOfHom f)]
    · simp only [Stratification.Index.restrict_right,
        ← Finset.inter_assoc, Finset.inter_eq_left.mpr (leOfHom f)]

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
    Algebra.IndZariski A (ProdStrata E) :=
  inferInstanceAs <| Algebra.IndZariski A
    (∀ i : Stratification.Index E, Generalization i.function i.ideal)

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
