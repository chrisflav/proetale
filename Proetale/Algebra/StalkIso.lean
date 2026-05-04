/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.LocalIso
import Proetale.Mathlib.RingTheory.Spectrum.Prime.RingHom
import Proetale.Mathlib.Topology.Inseparable

/-!
# Algebras and ring homomorphisms bijective on stalks

In this file we define the property of algebras and ring homomorphisms of being bijective
on stalks.

An `R`-algebra `S` is bijective on stalks if `R_q →+* S_p` is bijective for every pair of
primes `q = (algebraMap R S)⁻¹(p)`. In the literature, also the term "`R → S` identifies
local rings" is used.
-/

universe u v

/-- An `R`-algebra `S` is bijective on stalks if `R_q →+* S_p` is bijective for every pair of
primes `q = (algebraMap R S)⁻¹(p)`. -/
@[stacks 096E "(2)"]
class Algebra.BijectiveOnStalks (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  bijective_localRingHom (p : Ideal S) [p.IsPrime] :
    Function.Bijective
      (Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism `R →+* S` is bijective on stalks if `R_q →+* S_p` is bijective
for every pair of primes `q = f⁻¹(p)`. -/
@[algebraize Algebra.BijectiveOnStalks]
def RingHom.BijectiveOnStalks (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.BijectiveOnStalks R S

lemma RingHom.bijectiveOnStalks_algebraMap [Algebra R S] :
    (algebraMap R S).BijectiveOnStalks ↔ Algebra.BijectiveOnStalks R S :=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

namespace RingHom.BijectiveOnStalks

lemma localRingHom {f : R →+* S} (hf : f.BijectiveOnStalks) (p : Ideal S) [p.IsPrime] :
    Function.Bijective (Localization.localRingHom (p.comap f) p f rfl) := by
  letI := f.toAlgebra
  exact hf.bijective_localRingHom p

lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) : (g.comp f).BijectiveOnStalks := by
  letI := (g.comp f).toAlgebra
  refine ⟨fun p hp ↦ ?_⟩
  show Function.Bijective (Localization.localRingHom (p.comap (g.comp f)) p (g.comp f) rfl)
  have hq : (p.comap g).IsPrime := Ideal.IsPrime.comap g
  rw [Localization.localRingHom_comp
    (I := p.comap (g.comp f)) (p.comap g) p f (Ideal.comap_comap f g) g rfl]
  exact (hg.localRingHom p).comp (hf.localRingHom (p.comap g))

/-- A ring homomorphism `f : R →+* S` is bijective on stalks if there exists a set of elements
of `S` spanning the unit ideal such that for every such element, the composition of `f` with
the localization map is bijective on stalks. -/
lemma of_span_unit_ideal {f : R →+* S} (s : Set S)
    (hs : Ideal.span s = ⊤)
    (h : ∀ g ∈ s, ∀ (Sg : Type v) [CommRing Sg] [Algebra S Sg] [IsLocalization.Away g Sg],
      ((algebraMap S Sg).comp f).BijectiveOnStalks) :
    f.BijectiveOnStalks := by
  letI := f.toAlgebra
  refine ⟨fun p hp ↦ ?_⟩
  show Function.Bijective (Localization.localRingHom (p.comap f) p f rfl)
  obtain ⟨g, hgs, hgp⟩ : ∃ g ∈ s, g ∉ p := by
    by_contra! h_contra
    exact hp.ne_top <| le_antisymm le_top <|
      hs ▸ Ideal.span_le.mpr h_contra
  set Sg := Localization.Away g
  set p_g := Ideal.map (algebraMap S Sg) p
  have hpM : Disjoint (Submonoid.powers g : Set S) (↑p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem g hp.isRadical).mpr hgp
  haveI : p_g.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Sg p hp hpM
  have hcomap_pg : p_g.comap (algebraMap S Sg) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) Sg hp hpM
  have h_alg_bij : Function.Bijective
      (Localization.localRingHom p p_g (algebraMap S Sg) hcomap_pg.symm) := by
    letI : IsLocalization.AtPrime (Localization.AtPrime p_g) p := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g) (Localization.AtPrime p_g) p_g
      simp_rw [hcomap_pg] at this
      exact this
    exact IsLocalization.bijective p.primeCompl _ (by
      ext x
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      exact (IsScalarTower.algebraMap_apply S Sg (Localization.AtPrime p_g) x).symm)
  have hfactor := Localization.localRingHom_comp (p.comap f) p p_g f rfl
    (algebraMap S Sg) hcomap_pg.symm
  have hcomap_eq : p_g.comap ((algebraMap S Sg).comp f) = p.comap f := by
    rw [← Ideal.comap_comap, hcomap_pg]
  have h_inner : Function.Bijective (Localization.localRingHom (p.comap f) p_g
      ((algebraMap S Sg).comp f) hcomap_eq.symm) := by
    have aux : ∀ {J : Ideal R} [J.IsPrime] (heq : J = p.comap f)
        (hb : Function.Bijective (Localization.localRingHom J p_g
          ((algebraMap S Sg).comp f) (heq.trans hcomap_eq.symm))),
        Function.Bijective (Localization.localRingHom (p.comap f) p_g
          ((algebraMap S Sg).comp f) hcomap_eq.symm) := by
      rintro J _ rfl hb
      exact hb
    haveI : (p_g.comap ((algebraMap S Sg).comp f)).IsPrime :=
      hcomap_eq ▸ inferInstanceAs (p.comap f).IsPrime
    exact aux hcomap_eq ((h g hgs Sg).localRingHom p_g)
  refine (h_alg_bij.of_comp_iff' _).mp ?_
  rw [← RingHom.coe_comp, ← hfactor]
  exact h_inner

/-- The algebra map of a standard open immersion is bijective on stalks. -/
lemma of_isStandardOpenImmersion (R T : Type*) [CommRing R] [CommRing T] [Algebra R T]
    [Algebra.IsStandardOpenImmersion R T] : (algebraMap R T).BijectiveOnStalks := by
  obtain ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R T
  refine RingHom.bijectiveOnStalks_algebraMap.mpr ⟨fun q hq ↦ ?_⟩
  show Function.Bijective (Localization.localRingHom
    (q.comap (algebraMap R T)) q (algebraMap R T) rfl)
  letI : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap R T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers r) (Localization.AtPrime q) q
  exact IsLocalization.bijective (q.comap (algebraMap R T)).primeCompl _ (by
    ext x
    rw [RingHom.comp_apply, Localization.localRingHom_to_map]
    exact (IsScalarTower.algebraMap_apply R T (Localization.AtPrime q) x).symm)

end RingHom.BijectiveOnStalks

/-- Local isomorphisms are bijective on stalks. -/
lemma RingHom.IsLocalIso.bijectiveOnStalks {f : R →+* S} (hf : f.IsLocalIso) :
    f.BijectiveOnStalks := by
  algebraize [f]
  exact RingHom.BijectiveOnStalks.of_span_unit_ideal
    {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S)
    (fun g hg Sg _ _ _ ↦ by
      letI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
      algebraize [(algebraMap S Sg).comp f]
      haveI : IsScalarTower R S Sg := .of_algebraMap_eq fun _ ↦ rfl
      haveI : Algebra.IsStandardOpenImmersion R Sg :=
        .of_algEquiv R (Localization.Away g) Sg
          ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Sg).restrictScalars R)
      exact RingHom.BijectiveOnStalks.of_isStandardOpenImmersion R Sg)

namespace RingHom.BijectiveOnStalks

/-- A ring homomorphism that is bijective on stalks and induces a bijection on prime spectra
is itself bijective. -/
lemma bijective_of_bijective {f : R →+* S} (hf : f.BijectiveOnStalks)
    (hb : Function.Bijective <| PrimeSpectrum.comap f) : Function.Bijective f := by
  have hinj : Function.Injective f :=
    RingHom.injective_of_localRingHom_injective (fun p [_] ↦ (hf.localRingHom p).1) hb.2
  have hsurj : Function.Surjective f := by
    have hflat : f.Flat :=
      RingHom.flat_of_flat_localRingHom fun P [_] ↦ .of_bijective (hf.localRingHom P)
    have hgen : GeneralizingMap (PrimeSpectrum.comap f) := hflat.generalizingMap_comap
    have going_down_key : ∀ (p : Ideal S) [p.IsPrime] (c : S), c ∉ p →
        ∀ (q : Ideal S) [q.IsPrime], c ∈ q → ¬(q.comap f ≤ p.comap f) := by
      intro p hp c hcp q hq hcq hle
      exact hcp ((PrimeSpectrum.le_iff_specializes ⟨q, hq⟩ ⟨p, hp⟩).mpr
        (hgen.specializes_of_map_specializes hb.1
          ((PrimeSpectrum.le_iff_specializes _ _).mp hle)) hcq)
    apply RingHom.surjective_of_forall_isMaximal_exists
    intro s m hm
    have hm_prime := hm.isPrime
    obtain ⟨⟨q, hq⟩, hqm : PrimeSpectrum.comap f ⟨q, hq⟩ = ⟨m, hm_prime⟩⟩ := hb.2 ⟨m, hm_prime⟩
    have hqm' : q.comap f = m := congr_arg PrimeSpectrum.asIdeal hqm
    algebraize [f]
    obtain ⟨x, hx⟩ := (hf.localRingHom q).2 (algebraMap S (Localization.AtPrime q) s)
    obtain ⟨⟨r₀, ⟨b, hb⟩⟩, hxeq⟩ := IsLocalization.surj (q.comap f).primeCompl x
    have hfb_s : algebraMap S (Localization.AtPrime q) (f b * s) =
        algebraMap S (Localization.AtPrime q) (f r₀) := by
      rw [map_mul, ← hx,
        ← Localization.localRingHom_to_map (hIJ := rfl) (f := f),
        ← Localization.localRingHom_to_map (hIJ := rfl) (f := f) (x := r₀),
        ← map_mul, mul_comm, hxeq]
    have hfb_s' : algebraMap S (Localization.AtPrime q) (f b * s - f r₀) =
        algebraMap S (Localization.AtPrime q) 0 := by
      rw [map_zero, map_sub, hfb_s, sub_self]
    obtain ⟨⟨c, hcq⟩, hc_eq⟩ := (IsLocalization.eq_iff_exists q.primeCompl
      (Localization.AtPrime q)).mp hfb_s'
    simp only [mul_zero] at hc_eq
    set T := Algebra.algebraMapSubmonoid S m.primeCompl
    have hc_unit : IsUnit (algebraMap S (Localization T) c) := by
      by_contra hnu
      obtain ⟨I, hI, hcI⟩ := exists_max_ideal_of_mem_nonunits hnu
      have hI_prime := hI.isPrime
      have ⟨hcomap_prime, hcomap_disj⟩ :=
        (IsLocalization.isPrime_iff_isPrime_disjoint T (Localization T) I).mp hI_prime
      have hcomap_le : (I.comap (algebraMap S (Localization T))).comap f ≤ m := by
        intro r hr
        by_contra hrm
        have hfr_T : f r ∈ T := ⟨r, hrm, rfl⟩
        exact Set.disjoint_left.mp hcomap_disj hfr_T hr
      exact going_down_key q c hcq (I.comap (algebraMap S (Localization T))) hcI
        (hqm' ▸ hcomap_le)
    rw [IsLocalization.algebraMap_isUnit_iff (M := T)] at hc_unit
    obtain ⟨t, ht_mem, hc_dvd⟩ := hc_unit
    obtain ⟨r₁, hr₁m, rfl⟩ := ht_mem
    obtain ⟨d', hd'⟩ := hc_dvd
    have hd'' : f r₁ = c * d' := hd'
    have hkey2 : f r₁ * (f b * s - f r₀) = 0 := by
      rw [hd'']
      linear_combination d' * hc_eq
    have hkey3 : f (r₁ * b) * s = f (r₁ * r₀) := by
      rw [mul_sub, sub_eq_zero] at hkey2
      rw [map_mul, map_mul, mul_assoc, hkey2]
    refine ⟨r₁ * b, ?_, r₁ * r₀, hkey3.symm⟩
    exact mt hm_prime.mul_mem_iff_mem_or_mem.mp (by
      push_neg
      exact ⟨hr₁m, hqm' ▸ hb⟩)
  exact ⟨hinj, hsurj⟩

lemma prod {T : Type*} [CommRing T] {f : R →+* S} {g : R →+* T} :
    RingHom.BijectiveOnStalks (f.prod g) :=
  sorry

end RingHom.BijectiveOnStalks

namespace Algebra.BijectiveOnStalks

lemma comp (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.BijectiveOnStalks R S] [Algebra.BijectiveOnStalks S T] :
    Algebra.BijectiveOnStalks R T := by
  refine RingHom.bijectiveOnStalks_algebraMap.mp ?_
  rw [IsScalarTower.algebraMap_eq R S T]
  exact (RingHom.bijectiveOnStalks_algebraMap.mpr ‹_›).comp
    (RingHom.bijectiveOnStalks_algebraMap.mpr ‹_›)

instance (priority := 100) of_isStandardOpenImmersion (R T : Type*) [CommRing R] [CommRing T]
    [Algebra R T] [Algebra.IsStandardOpenImmersion R T] : Algebra.BijectiveOnStalks R T :=
  RingHom.bijectiveOnStalks_algebraMap.mp <|
    RingHom.BijectiveOnStalks.of_isStandardOpenImmersion R T

/-- An algebra `R → S` that is bijective on stalks and induces a bijection on prime spectra
has a bijective algebra map. -/
lemma bijective_of_bijective [Algebra R S] [Algebra.BijectiveOnStalks R S]
    (hb : Function.Bijective <| PrimeSpectrum.comap (algebraMap R S)) :
    Function.Bijective (algebraMap R S) :=
  (RingHom.bijectiveOnStalks_algebraMap.mpr ‹_›).bijective_of_bijective hb

end Algebra.BijectiveOnStalks
