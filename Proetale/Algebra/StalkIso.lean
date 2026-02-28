/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.LocalIso
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.Ideal

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

/-- Local isomorphisms are bijective on stalks. -/
lemma RingHom.IsLocalIso.bijectiveOnStalks {f : R →+* S} (hf : f.IsLocalIso) :
    f.BijectiveOnStalks := by
  intro p hp
  letI := f.toAlgebra
  haveI : Algebra.IsLocalIso R S := hf
  obtain ⟨g, hgp, hstd⟩ := Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) p
  obtain ⟨r, hr⟩ := Algebra.IsStandardOpenImmersion.exists_away R (Localization.Away g)
  set Sg := Localization.Away g
  -- p is disjoint from powers of g (since g ∉ p)
  have hpM : Disjoint (Submonoid.powers g : Set S) (↑p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem g hp.isRadical).mpr hgp
  -- The prime p_g of Sg corresponding to p
  set p_g := Ideal.map (algebraMap S Sg) p
  have hp_g : p_g.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Sg p hp hpM
  have hcomap_pg : p_g.comap (algebraMap S Sg) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) Sg hp hpM
  -- Step 1: stalk map for algebraMap S Sg at p_g is bijective
  -- (Sg)_{p_g} is a localization of S at p (since p_g.comap = p)
  -- S_p and (Sg)_{p_g} are both localizations of S at p.primeCompl
  have h_alg_bij : Function.Bijective
      (Localization.localRingHom p p_g (algebraMap S Sg) hcomap_pg.symm) := by
    -- (Sg)_{p_g} is a localization of S at p by isLocalization_isLocalization_atPrime_isLocalization
    haveI : IsLocalization.AtPrime (Localization.AtPrime p_g) p := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g) (Localization.AtPrime p_g) p_g
      simp_rw [hcomap_pg] at this
      exact this
    -- localRingHom is IsLocalization.map, between two AtPrime localizations of S at p
    exact IsLocalization.bijective p.primeCompl
      (Localization.localRingHom p p_g (algebraMap S Sg) hcomap_pg.symm) (by
      ext x
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      exact (IsScalarTower.algebraMap_apply S Sg (Localization.AtPrime p_g) x).symm)
  -- Step 2: composed stalk map for (algebraMap S Sg) ∘ f is bijective
  haveI : IsScalarTower R S Sg := .of_algebraMap_eq fun _ ↦ rfl
  have halg_eq : (algebraMap S Sg).comp f = algebraMap R Sg := by
    ext x; exact (IsScalarTower.algebraMap_apply R S Sg x).symm
  -- The comap of p_g along (algebraMap S Sg) ∘ f equals p.comap f
  have hcomap_comp : p.comap f = p_g.comap ((algebraMap S Sg).comp f) := by
    rw [show p_g.comap ((algebraMap S Sg).comp f) = (p_g.comap (algebraMap S Sg)).comap f
      from (Ideal.comap_comap f (algebraMap S Sg)).symm, hcomap_pg]
  have h_comp_bij : Function.Bijective
      (Localization.localRingHom (p.comap f) p_g ((algebraMap S Sg).comp f) hcomap_comp) := by
    -- Sg is a localization of R at Submonoid.powers r
    -- (Sg)_{p_g} is a localization of R at p_g.comap (algebraMap R Sg) = p.comap f
    have hcomap_R : p_g.comap (algebraMap R Sg) = p.comap f := by
      conv_lhs => rw [show (algebraMap R Sg) = (algebraMap S Sg).comp f from halg_eq.symm]
      rw [← Ideal.comap_comap, hcomap_pg]
    haveI : IsLocalization.AtPrime (Localization.AtPrime p_g) (p.comap f) := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers r) (Localization.AtPrime p_g) p_g
      simp_rw [hcomap_R] at this
      exact this
    exact IsLocalization.bijective (p.comap f).primeCompl
      (Localization.localRingHom (p.comap f) p_g ((algebraMap S Sg).comp f) hcomap_comp) (by
      ext x
      simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
      -- Goal: (algebraMap Sg _) ((algebraMap S Sg) (f x)) = (algebraMap R _) x
      -- Use the scalar tower R → S → Sg → Localization.AtPrime p_g
      have : (algebraMap S Sg) (f x) = (algebraMap R Sg) x := by
        change (algebraMap S Sg) ((algebraMap R S) x) = (algebraMap R Sg) x
        exact IsScalarTower.algebraMap_apply R S Sg x
      rw [this, IsScalarTower.algebraMap_apply R Sg (Localization.AtPrime p_g)])
  -- Step 3: Factor and conclude
  -- By localRingHom_comp: localRingHom(fg) = localRingHom(alg) ∘ localRingHom(f)
  have hfactor := Localization.localRingHom_comp (p.comap f) p p_g f rfl
    (algebraMap S Sg) hcomap_pg.symm
  -- hfactor says the composed localRingHom equals the composition of individual localRingHoms
  -- We transport bijectivity from h_comp_bij through hfactor
  have hfactor' : Function.Bijective
      ((Localization.localRingHom p p_g (algebraMap S Sg) hcomap_pg.symm).comp
       (Localization.localRingHom (p.comap f) p f rfl)) :=
    hfactor ▸ h_comp_bij
  exact (h_alg_bij.of_comp_iff' _).mp hfactor'

namespace RingHom.BijectiveOnStalks

lemma comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) : (g.comp f).BijectiveOnStalks := by
  intro p hp
  have hq : (p.comap g).IsPrime := Ideal.IsPrime.comap g
  have key := Localization.localRingHom_comp
    (I := p.comap (g.comp f)) (p.comap g) p f (Ideal.comap_comap f g) g rfl
  rw [key]
  exact (hg p).comp (hf (p.comap g))

lemma bijective_of_bijective {f : R →+* S} (hf : f.BijectiveOnStalks)
    (hb : Function.Bijective <| PrimeSpectrum.comap f) : Function.Bijective f := by
  have hinj : Function.Injective f := by
    -- For any prime q of R, by surjectivity of Spec(f), q = (p.comap f) for some prime p of S.
    -- The stalk map at p is injective, so algebraMap to R_q is injective on the image of f.
    -- By PrimeSpectrum.toPiLocalization_injective, f is injective.
    intro r₁ r₂ hr
    apply PrimeSpectrum.toPiLocalization_injective R
    funext ⟨q, hq⟩
    -- q = p.comap f for some prime p
    obtain ⟨⟨p, hp⟩, hpq : PrimeSpectrum.comap f ⟨p, hp⟩ = ⟨q, hq⟩⟩ := hb.2 ⟨q, hq⟩
    have hpq' : p.comap f = q := congr_arg PrimeSpectrum.asIdeal hpq
    -- The stalk map localRingHom at p is injective
    have hstalk_inj := (hf p).1
    -- The toPiLocalization evaluates to algebraMap R (Localization.AtPrime q) rᵢ
    -- We need to show these agree. Transport along hpq'.
    subst hpq'
    apply hstalk_inj
    -- Goal: localRingHom (toPiLocalization R r₁ ⟨..⟩) = localRingHom (toPiLocalization R r₂ ⟨..⟩)
    -- toPiLocalization R rᵢ ⟨q, hq⟩ = algebraMap R (Localization.AtPrime q) rᵢ
    change Localization.localRingHom _ p f rfl (algebraMap R _ r₁) =
           Localization.localRingHom _ p f rfl (algebraMap R _ r₂)
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map, hr]
  -- Surjectivity: use flatness → going-down → conductor ideal argument
  have hsurj : Function.Surjective f := by
    -- Step 1: f is flat.
    have hflat : f.Flat := by
      letI := f.toAlgebra
      rw [RingHom.Flat]
      apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
        (fun P ↦ Algebra.linearMap S _)
      intro P _
      letI := (Localization.localRingHom (Ideal.comap f P) P f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
        .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := by
        exact Module.Flat.of_linearEquiv
          (LinearEquiv.ofBijective (Algebra.linearMap _ _) (hf P)).symm
      exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)
    -- Step 2: f has generalizing Spec (going-down).
    have hgen : GeneralizingMap (PrimeSpectrum.comap f) := hflat.generalizingMap_comap
    -- Step 3: Use going-down to prove surjectivity.
    -- Key going-down lemma: for any prime p of S and c ∉ p, there is no prime q of S
    -- with c ∈ q and q.comap f ⊆ p.comap f (because going-down + Spec injectivity
    -- would force q ⊆ p, contradicting c ∉ p).
    -- Key going-down lemma: for any prime p of S and c ∉ p, there is no prime q of S
    -- with c ∈ q and q.comap f ⊆ p.comap f.
    have going_down_key : ∀ (p : Ideal S) [p.IsPrime] (c : S), c ∉ p →
        ∀ (q : Ideal S) [q.IsPrime], c ∈ q → ¬(q.comap f ≤ p.comap f) := by
      intro p hp c hcp q hq hcq hle
      -- q.comap f ≤ p.comap f means ⟨q.comap f, _⟩ ⤳ ⟨p.comap f, _⟩ in Spec R
      set sp := (⟨p, hp⟩ : PrimeSpectrum S)
      set sq := (⟨q, hq⟩ : PrimeSpectrum S)
      have hspec : PrimeSpectrum.comap f sq ⤳ PrimeSpectrum.comap f sp :=
        (PrimeSpectrum.le_iff_specializes
          (PrimeSpectrum.comap f sq) (PrimeSpectrum.comap f sp)).mp hle
      -- By GeneralizingMap: ∃ q' ⤳ p with comap f q' = comap f q
      obtain ⟨q', hq'spec, hq'eq⟩ := hgen hspec
      -- q' ⤳ sp means q'.asIdeal ≤ p
      have hq'le : q'.asIdeal ≤ p :=
        (PrimeSpectrum.le_iff_specializes q' sp).mpr hq'spec
      -- q'.comap f = q.comap f, so sq = q' by injectivity of Spec(f)
      have hqeq : sq = q' :=
        hb.1 (PrimeSpectrum.ext (congr_arg PrimeSpectrum.asIdeal hq'eq).symm)
      -- So q ≤ p, but c ∈ q and c ∉ p, contradiction.
      have : sq.asIdeal ≤ p := hqeq ▸ hq'le
      exact hcp (this hcq)
    -- For each s, show s ∈ f.range using the conductor ideal argument
    intro s
    -- The conductor ideal J_s = {r : R | f(r) * s ∈ f.range} is not in any maximal ideal.
    -- We show this by using stalk surjectivity + going-down to find, for each maximal m,
    -- an element r₁ * b ∈ J_s \ m, contradicting J_s ⊆ m.
    -- Instead of defining J_s explicitly, we use by_contra + Ideal.exists_le_maximal
    -- on the ideal {r : R | f(r) * s ∈ f.range}.
    letI := f.toAlgebra
    -- Construct J_s as an ideal
    have hJ_zero : f 0 * s ∈ f.range := ⟨0, by simp⟩
    have hJ_add : ∀ {a b : R}, f a * s ∈ f.range → f b * s ∈ f.range →
        f (a + b) * s ∈ f.range := by
      intro a b ⟨x, hx⟩ ⟨y, hy⟩
      exact ⟨x + y, by rw [map_add, map_add, add_mul]; congr 1⟩
    have hJ_smul : ∀ (c : R) {r : R}, f r * s ∈ f.range → f (c * r) * s ∈ f.range := by
      intro c r ⟨x, hx⟩
      exact ⟨c * x, by rw [map_mul, map_mul, mul_assoc]; congr 1⟩
    -- It suffices to show: ∃ r with f(r) * s ∈ f.range and r is a unit (i.e., r = 1 works)
    -- Equivalently, show ∀ m maximal, ∃ r ∉ m, f(r) * s ∈ f.range
    -- and then use Ideal.eq_top_iff to conclude J_s = ⊤
    suffices key : ∀ (m : Ideal R), m.IsMaximal →
        ∃ r : R, r ∉ m ∧ f r * s ∈ f.range by
      -- The set {r : R | f(r) * s ∈ f.range} is not contained in any maximal ideal,
      -- so it must contain a unit, giving s ∈ f.range.
      by_contra hs
      -- s ∉ f.range means 1 ∉ J_s (since f(1)*s = s)
      have h1 : ¬(f 1 * s ∈ f.range) := by
        simp only [map_one, one_mul]
        exact hs
      -- J_s ≠ ⊤
      have hJ_ne_top : ¬(∀ r : R, f r * s ∈ f.range) := by
        intro hall; exact h1 (hall 1)
      push_neg at hJ_ne_top
      -- So ∃ r₀ with f(r₀) * s ∉ f.range, meaning J_s ≠ ⊤
      -- By Zorn, J_s ⊆ some maximal m
      -- Actually, let's just use the key directly: pick any maximal m
      -- For J_s = {r | f(r)*s ∈ f.range}, if J_s ≠ R, there's a maximal m ⊇ J_s
      -- and key gives r ∉ m with r ∈ J_s ⊆ m, contradiction.
      -- Let me formalize: J_s = R ↔ 1 ∈ J_s ↔ s ∈ f.range
      -- Since s ∉ f.range, J_s ≠ R, so J_s ⊆ m for some maximal m
      -- Then key gives r ∉ m with f(r)*s ∈ f.range, but this r ∈ J_s ⊆ m, contradiction
      -- To make this work, I need to actually form J_s as an ideal and use exists_le_maximal
      -- Let me do this via the Submodule approach
      set J_s : Ideal R := {
        carrier := {r : R | f r * s ∈ f.range}
        add_mem' := fun ha hb => hJ_add ha hb
        zero_mem' := hJ_zero
        smul_mem' := fun c _ hr => hJ_smul c hr
      }
      have hJ_ne_top' : J_s ≠ ⊤ := by
        intro heq
        have : (1 : R) ∈ J_s := heq ▸ Submodule.mem_top
        exact h1 this
      obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J_s hJ_ne_top'
      obtain ⟨r, hrm, hr_range⟩ := key m hm
      exact hrm (hJm hr_range)
    -- Now prove the key: for each maximal m, ∃ r ∉ m with f(r)*s ∈ f.range
    intro m hm
    have hm_prime := hm.isPrime
    -- Get unique prime q of S with q.comap f = m
    obtain ⟨⟨q, hq⟩, hqm : PrimeSpectrum.comap f ⟨q, hq⟩ = ⟨m, hm_prime⟩⟩ := hb.2 ⟨m, hm_prime⟩
    have hqm' : q.comap f = m := congr_arg PrimeSpectrum.asIdeal hqm
    -- Stalk surjectivity at q: localRingHom is surjective
    obtain ⟨x, hx⟩ := (hf q).2 (algebraMap S (Localization.AtPrime q) s)
    -- x ∈ R_m; write x = r₀ / b via IsLocalization.surj
    obtain ⟨⟨r₀, ⟨b, hb⟩⟩, hxeq⟩ := IsLocalization.surj (q.comap f).primeCompl x
    -- hxeq : ↑⟨b, hb⟩ • x = algebraMap R _ r₀, i.e., (algebraMap R _) b * x = (algebraMap R _) r₀
    -- Apply localRingHom: f(b) * s = f(r₀) in S_q (up to torsion)
    have hfb_s : algebraMap S (Localization.AtPrime q) (f b * s) =
        algebraMap S (Localization.AtPrime q) (f r₀) := by
      rw [map_mul]
      have step1 := congr_arg (Localization.localRingHom (q.comap f) q f rfl) hxeq
      rw [map_mul, Localization.localRingHom_to_map, Localization.localRingHom_to_map] at step1
      rw [← step1, ← hx, mul_comm]
    -- Extract c ∉ q with c * (f(b) * s - f(r₀)) = 0
    have hfb_s' : algebraMap S (Localization.AtPrime q) (f b * s - f r₀) =
        algebraMap S (Localization.AtPrime q) 0 := by
      rw [map_zero, map_sub, hfb_s, sub_self]
    obtain ⟨⟨c, hcq⟩, hc_eq⟩ := (IsLocalization.eq_iff_exists q.primeCompl
      (Localization.AtPrime q)).mp hfb_s'
    -- hc_eq : c * (f b * s - f r₀) = c * 0 = 0, c ∉ q
    simp only [mul_zero] at hc_eq
    -- Use going_down_key to show c is a unit in the localization at T = f(R \ m)
    have hT_inst : IsLocalization (Algebra.algebraMapSubmonoid S m.primeCompl)
        (Localization (Algebra.algebraMapSubmonoid S m.primeCompl)) := Localization.isLocalization
    set T := Algebra.algebraMapSubmonoid S m.primeCompl
    have hc_unit : IsUnit (algebraMap S (Localization T) c) := by
      by_contra hnu
      obtain ⟨I, hI, hcI⟩ := exists_max_ideal_of_mem_nonunits hnu
      have hI_prime := hI.isPrime
      have ⟨hcomap_prime, hcomap_disj⟩ :=
        (IsLocalization.isPrime_iff_isPrime_disjoint T (Localization T) I).mp hI_prime
      have hcq' : c ∈ I.comap (algebraMap S (Localization T)) := hcI
      have hcomap_le : (I.comap (algebraMap S (Localization T))).comap f ≤ m := by
        intro r hr
        by_contra hrm
        have hfr_T : f r ∈ T := ⟨r, hrm, rfl⟩
        have hfr_comap : f r ∈ I.comap (algebraMap S (Localization T)) := hr
        exact Set.disjoint_left.mp hcomap_disj hfr_T hfr_comap
      exact going_down_key q c hcq (I.comap (algebraMap S (Localization T))) hcq'
        (hqm' ▸ hcomap_le)
    -- From hc_unit: ∃ t ∈ T, c ∣ t
    rw [IsLocalization.algebraMap_isUnit_iff (M := T)] at hc_unit
    obtain ⟨t, ht_mem, hc_dvd⟩ := hc_unit
    -- t ∈ T means t = f(r₁) for some r₁ ∉ m
    obtain ⟨r₁, hr₁m, rfl⟩ := ht_mem
    -- hc_dvd : c ∣ f(r₁)
    obtain ⟨d', hd'⟩ := hc_dvd
    -- From hc_eq: c * (f(b) * s - f(r₀)) = 0
    -- Multiply by d': f(r₁) * (f(b) * s - f(r₀)) = 0
    -- hd' : algebraMap R S r₁ = c * d', but f = algebraMap R S here
    have hd'' : f r₁ = c * d' := by
      change (algebraMap R S) r₁ = c * d' at hd'; exact hd'
    have hkey2 : f r₁ * (f b * s - f r₀) = 0 := by
      calc f r₁ * (f b * s - f r₀)
        _ = (c * d') * (f b * s - f r₀) := by rw [← hd'']
        _ = d' * (c * (f b * s - f r₀)) := by ring
        _ = d' * 0 := by rw [hc_eq]
        _ = 0 := mul_zero _
    -- So f(r₁ * b) * s = f(r₁ * r₀)
    have hkey3 : f (r₁ * b) * s = f (r₁ * r₀) := by
      have := hkey2
      rw [mul_sub, sub_eq_zero] at this
      rw [map_mul, mul_assoc, this, ← map_mul]
    -- r₁ * b ∉ m (since r₁ ∉ m, b ∉ m, and m is prime)
    have hb_nmem : b ∉ m := hqm' ▸ hb
    have hr1b_nmem : r₁ * b ∉ m :=
      mt hm_prime.mul_mem_iff_mem_or_mem.mp (by push_neg; exact ⟨hr₁m, hb_nmem⟩)
    -- f(r₁ * b) * s = f(r₁ * r₀) ∈ f.range
    exact ⟨r₁ * b, hr1b_nmem, r₁ * r₀, hkey3.symm⟩
  exact ⟨hinj, hsurj⟩

lemma prod {T : Type*} [CommRing T] {f : R →+* S} {g : R →+* T}
    (hf : f.BijectiveOnStalks) (hg : g.BijectiveOnStalks) :
    RingHom.BijectiveOnStalks (f.prod g) :=
  -- Blueprint: thm:finite-product-identifies-local-rings. A→∏Aᵢ identifies local rings if each A→Aᵢ does.
  sorry

end RingHom.BijectiveOnStalks
