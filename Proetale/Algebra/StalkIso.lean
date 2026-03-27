/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.LocalIso
import Proetale.Mathlib.RingTheory.Spectrum.Prime.RingHom
import Proetale.Mathlib.Topology.Inseparable

/-!
# Ring homomorphisms bijective on stalks

In this file we define the property of ring homomorphisms of being bijective on stalks.

A ring homomorphism `R →+* S` is bijective on stalks if `R_q →+* S_p` is bijective
for every pair of primes `q = f⁻¹(p)`. In the literature, also the term "`R →+* S` identifies
local rings" is used.
-/

/-- A ring homomorphism `R →+* S` is bijective on stalks if `R_q →+* S_p` is bijective
for every pair of primes `q = f⁻¹(p)`. -/
@[stacks 096E "(2)"]
def RingHom.BijectiveOnStalks {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  ∀ (p : Ideal S) [p.IsPrime],
    Function.Bijective (Localization.localRingHom (p.comap f) p f rfl)

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom.BijectiveOnStalks

lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) : (g.comp f).BijectiveOnStalks := by
  intro p hp
  have hq : (p.comap g).IsPrime := Ideal.IsPrime.comap g
  rw [Localization.localRingHom_comp
    (I := p.comap (g.comp f)) (p.comap g) p f (Ideal.comap_comap f g) g rfl]
  exact (hg p).comp (hf (p.comap g))

/-- If `f : R →+* S` is bijective on stalks, then checking bijectivity at a prime `p` of `S`
can be done after localizing at any element not in `p`. This is the key locality property. -/
lemma of_localization {f : R →+* S} (g : S) (p : Ideal S) [hp : p.IsPrime] (hgp : g ∉ p)
    (Sg : Type*) [CommRing Sg] [Algebra S Sg] [IsLocalization.Away g Sg] :
    let hpM : Disjoint (Submonoid.powers g : Set S) (↑p : Set S) :=
      (Ideal.disjoint_powers_iff_notMem g hp.isRadical).mpr hgp
    let p_g := Ideal.map (algebraMap S Sg) p
    let hp_g : p_g.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Sg p hp hpM
    let hcomap_pg : p_g.comap (algebraMap S Sg) = p :=
      IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) Sg hp hpM
    Function.Bijective (Localization.localRingHom (p.comap f) p_g ((algebraMap S Sg).comp f)
      (by rw [← Ideal.comap_comap, hcomap_pg])) →
    Function.Bijective (Localization.localRingHom (p.comap f) p f rfl) := fun h => by
  set p_g := Ideal.map (algebraMap S Sg) p
  have hpM : Disjoint (Submonoid.powers g : Set S) (↑p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem g hp.isRadical).mpr hgp
  have hp_g : p_g.IsPrime :=
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
  have hfactor' : Function.Bijective
      ((Localization.localRingHom p p_g (algebraMap S Sg) hcomap_pg.symm).comp
       (Localization.localRingHom (p.comap f) p f rfl)) :=
    hfactor ▸ h
  exact (h_alg_bij.of_comp_iff' _).mp hfactor'

end RingHom.BijectiveOnStalks

/-- Local isomorphisms are bijective on stalks. -/
lemma RingHom.IsLocalIso.bijectiveOnStalks {f : R →+* S} (hf : f.IsLocalIso) :
    f.BijectiveOnStalks := by
  intro p hp
  algebraize [f]
  obtain ⟨g, hgp, hstd⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) p
  obtain ⟨r, hr⟩ := Algebra.IsStandardOpenImmersion.exists_away R (Localization.Away g)
  set Sg := Localization.Away g
  set p_g := Ideal.map (algebraMap S Sg) p
  have hpM : Disjoint (Submonoid.powers g : Set S) (↑p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem g hp.isRadical).mpr hgp
  have hp_g : p_g.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Sg p hp hpM
  have hcomap_pg : p_g.comap (algebraMap S Sg) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) Sg hp hpM
  letI : IsScalarTower R S Sg := .of_algebraMap_eq fun _ ↦ rfl
  have halg_eq : (algebraMap S Sg).comp f = algebraMap R Sg := by
    ext x
    exact (IsScalarTower.algebraMap_apply R S Sg x).symm
  have hcomap_comp : p.comap f = p_g.comap ((algebraMap S Sg).comp f) := by
    rw [← Ideal.comap_comap, hcomap_pg]
  refine RingHom.BijectiveOnStalks.of_localization g p hgp Sg ?_
  have hcomap_R : p_g.comap (algebraMap R Sg) = p.comap f := by
    rw [← halg_eq, ← Ideal.comap_comap, hcomap_pg]
  letI : IsLocalization.AtPrime (Localization.AtPrime p_g) (p.comap f) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers r) (Localization.AtPrime p_g) p_g
    simp_rw [hcomap_R] at this
    exact this
  exact IsLocalization.bijective (p.comap f).primeCompl _ (by
    ext x
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    have : (algebraMap S Sg) (f x) = (algebraMap R Sg) x :=
      (IsScalarTower.algebraMap_apply R S Sg x).symm
    rw [this, IsScalarTower.algebraMap_apply R Sg (Localization.AtPrime p_g)])

namespace RingHom.BijectiveOnStalks

/-- A ring homomorphism that is bijective on stalks and induces a bijection on prime spectra
is itself bijective. -/
lemma bijective_of_bijective {f : R →+* S} (hf : f.BijectiveOnStalks)
    (hb : Function.Bijective <| PrimeSpectrum.comap f) : Function.Bijective f := by
  have hinj : Function.Injective f :=
    RingHom.injective_of_injectiveOnStalks (fun p [_] ↦ (hf p).1) hb.2
  have hsurj : Function.Surjective f := by
    have hflat : f.Flat :=
      RingHom.flat_of_localizations_flat fun P [_] ↦ .of_bijective (hf P)
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
    obtain ⟨x, hx⟩ := (hf q).2 (algebraMap S (Localization.AtPrime q) s)
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
