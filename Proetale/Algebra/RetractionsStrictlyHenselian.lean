/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Mathlib.RingTheory.Etale.Prod
import Proetale.Algebra.ProEtaleContraction

/-!
# Retractions and strictly henselian local rings

This file proves blueprint `lemma:retractions-strictly-henselian`: if every faithfully flat
étale ring map out of `A` admits a retraction, then the local rings of `A` at maximal ideals
are strictly henselian. As a corollary (blueprint `cor:strictly-henselian-etale-contraction`),
the local rings of `IndEtaleContraction R` at maximal ideals are strictly henselian.

## Outline

The key technical statement is
`Algebra.Etale.exists_algHom_localization_atPrime_comap_eq`: for every étale `A`-algebra `C`
and every prime `q` of `C` lying over a maximal ideal `m` of `A`, there is an `A`-algebra map
`ρ : C →ₐ[A] Aₘ` with `ρ⁻¹(m Aₘ) = q`. It is proven following the blueprint:

1. By quasi-finiteness of `C` over `A` there are only finitely many primes of `C` over `m`;
   choose `g ∈ C` contained in all of them except `q` (prime avoidance,
   `Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver`). Then `q` induces the unique prime of
   `C_g` over `m`.
2. The image `U` of `Spec C_g → Spec A` is open (flat + finite presentation) and contains `m`.
   By quasi-compactness there are `a₁, …, aᵣ ∈ m` with `Spec A = U ∪ ⋃ D(aᵢ)`.
3. `C' := C_g × ∏ᵢ A_{aᵢ}` is étale over `A` with surjective `Spec C' → Spec A`, so the
   hypothesis provides a retraction `σ : C' →+* A`. Since `aᵢ ∈ m`, the prime `σ⁻¹(m)` lies in
   the `C_g`-factor and is therefore the unique prime over `m` there, i.e. the one induced
   by `q`. Localizing `σ` at this prime and precomposing with `C → C_g → (C')_{σ⁻¹ m}`
   yields the desired `ρ`.

Both consequences are then derived without any descent machinery, by constructing standard
étale algebras (`StandardEtalePair`) directly over `A` from monic polynomial data lifted from
`Aₘ` (using `Polynomial.scaleRoots` to clear denominators while preserving monicity):

* `IsSepClosed`: an irreducible separable monic polynomial `p` over the residue field `κ(m)`
  lifts to a monic `F` over `A`; applying the key statement to the standard étale algebra
  `A[X][1/F']/(F)` at the prime given by `κ(m)[X]/(p)` produces a root of `p` in `κ(m)`.
* `HenselianLocalRing`: a Hensel datum `(f, a₀)` over `Aₘ` is scaled to a monic polynomial
  over `A` and treated by the same method; the prime tracking in the key statement pins down
  the residue of the produced root.
-/

universe u

open Polynomial IsLocalRing

section KeyLemma

variable {A : Type u} [CommRing A]

/-- Multiplying a function with `Pi.single i x` yields `Pi.single i 1` provided `g i * x = 1`. -/
private lemma pi_mul_single_eq_single {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, MulZeroOneClass (M i)] (g : Π i, M i) (i : ι) (x : M i) (h : g i * x = 1) :
    g * Pi.single i x = Pi.single i 1 := by
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simpa using h
  · simp [Pi.single_eq_of_ne hj]

/-- Blueprint `lemma:retractions-strictly-henselian`, main step: assume that every étale
`A`-algebra `B` with surjective `Spec B → Spec A` admits a retraction. Then for every étale
`A`-algebra `C` and every prime `q` of `C` lying over a maximal ideal `m`, there is an
`A`-algebra map `ρ : C →ₐ[A] Aₘ` such that the preimage of the maximal ideal is `q`. -/
theorem Algebra.Etale.exists_algHom_localization_atPrime_comap_eq
    (H : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.Etale A B →
      Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) →
      ∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A)
    (m : Ideal A) [m.IsMaximal]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (q : Ideal C) [q.IsPrime] (hq : q.comap (algebraMap A C) = m) :
    ∃ ρ : C →ₐ[A] Localization.AtPrime m,
      (maximalIdeal (Localization.AtPrime m)).comap ρ.toRingHom = q := by
  classical
  haveI : q.LiesOver m := ⟨hq.symm⟩
  -- Step 1: choose `g` isolating `q` among the (finitely many) primes over `m`.
  obtain ⟨g, hgq, hg⟩ := Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver m q
  set Cg := Localization.Away g with hCgdef
  have hdisj : Disjoint (Submonoid.powers g : Set C) (q : Set C) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hgq (‹q.IsPrime›.mem_of_pow_mem n hx)
  have hqg_prime : (q.map (algebraMap C Cg)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Cg q ‹_› hdisj
  have hqg_under : (q.map (algebraMap C Cg)).comap (algebraMap C Cg) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Cg ‹_› hdisj
  have halg : algebraMap A Cg = (algebraMap C Cg).comp (algebraMap A C) :=
    IsScalarTower.algebraMap_eq A C Cg
  have hqg_over : (q.map (algebraMap C Cg)).comap (algebraMap A Cg) = m := by
    rw [halg, ← Ideal.comap_comap, hqg_under, hq]
  -- `q.map (algebraMap C Cg)` is the unique prime of `Cg` over `m`.
  have huniq : ∀ Q : Ideal Cg, Q.IsPrime → Q.comap (algebraMap A Cg) = m →
      Q = q.map (algebraMap C Cg) := by
    intro Q hQ hQm
    have hp_prime : (Q.comap (algebraMap C Cg)).IsPrime := hQ.comap _
    have hp_over : (Q.comap (algebraMap C Cg)).comap (algebraMap A C) = m := by
      rw [Ideal.comap_comap, ← halg, hQm]
    have hgp : g ∉ Q.comap (algebraMap C Cg) := by
      intro hmem
      rw [Ideal.mem_comap] at hmem
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
        (IsLocalization.Away.algebraMap_isUnit g))
    have hpq : Q.comap (algebraMap C Cg) = q := by
      by_contra hne
      exact hgp (hg _ hp_prime hne ⟨hp_over.symm⟩)
    conv_lhs => rw [← IsLocalization.map_under (Submonoid.powers g) Cg Q]
    rw [show Q.under C = q from hpq]
  -- Étale instances for `Cg`.
  haveI : Algebra.Etale C Cg := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale A Cg := Algebra.Etale.comp A C Cg
  -- Step 2: the image `U` of `Spec Cg → Spec A` is open and contains `m`.
  set U : Set (PrimeSpectrum A) := Set.range (PrimeSpectrum.comap (algebraMap A Cg)) with hUdef
  have hU_open : IsOpen U :=
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := A)
      (S := Cg)).isOpen_range
  have hmU : (⟨m, Ideal.IsMaximal.isPrime ‹_›⟩ : PrimeSpectrum A) ∈ U :=
    ⟨⟨q.map (algebraMap C Cg), hqg_prime⟩, PrimeSpectrum.ext hqg_over⟩
  -- The complement of `U` is compact and covered by `D(a)`, `a ∈ m`.
  have hZ_sub : Uᶜ ⊆ ⋃ a : m, (PrimeSpectrum.basicOpen (a : A) : Set (PrimeSpectrum A)) := by
    intro p hp
    have hpm : p.asIdeal ≠ m := by
      rintro rfl
      exact hp hmU
    have : ¬m ≤ p.asIdeal := by
      intro hle
      exact hpm (((Ideal.IsMaximal.eq_of_le ‹_› p.isPrime.ne_top hle)).symm)
    obtain ⟨a, ham, hap⟩ := SetLike.not_le_iff_exists.mp this
    refine Set.mem_iUnion.mpr ⟨⟨a, ham⟩, ?_⟩
    simpa [PrimeSpectrum.basicOpen] using hap
  obtain ⟨t, ht⟩ := (hU_open.isClosed_compl.isCompact).elim_finite_subcover
    (fun a : m => (PrimeSpectrum.basicOpen (a : A) : Set (PrimeSpectrum A)))
    (fun a => (PrimeSpectrum.basicOpen _).isOpen) hZ_sub
  -- Step 3: the étale `A`-algebra `C' = Cg × ∏ A_a` with surjective spectrum map.
  set D : Type u := Π a : t, Localization.Away ((a : m) : A) with hDdef
  haveI : ∀ a : t, Algebra.Etale A (Localization.Away ((a : m) : A)) :=
    fun a => Algebra.Etale.of_isLocalizationAway ((a : m) : A)
  set C' : Type u := Cg × D with hC'def
  have hfst_alg : algebraMap A Cg = (RingHom.fst Cg D).comp (algebraMap A C') :=
    RingHom.ext fun r => rfl
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A C')) := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨y, rfl⟩ := hx
      refine ⟨PrimeSpectrum.comap (RingHom.fst Cg D) y, ?_⟩
      rw [hfst_alg, PrimeSpectrum.comap_comp_apply]
    · obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
      have : x ∈ Set.range
          (PrimeSpectrum.comap (algebraMap A (Localization.Away ((a : A))))) := by
        rw [PrimeSpectrum.localization_away_comap_range _ ((a : A))]
        exact hxa
      obtain ⟨y, rfl⟩ := this
      refine ⟨PrimeSpectrum.comap
        ((Pi.evalRingHom _ (⟨a, hat⟩ : t)).comp (RingHom.snd Cg D)) y, ?_⟩
      rw [show algebraMap A (Localization.Away ((a : A))) =
        ((Pi.evalRingHom _ (⟨a, hat⟩ : t)).comp (RingHom.snd Cg D)).comp (algebraMap A C')
        from RingHom.ext fun r => rfl]
      simp only [PrimeSpectrum.comap_comp_apply]
  obtain ⟨σ, hσ⟩ := H C' inferInstance hsurj
  -- Step 4: `σ⁻¹(m)` avoids the idempotent `(1, 0)`.
  set e : t → C' := fun a => (0, Pi.single a 1) with hedef
  have he_mem : ∀ a : t, σ (e a) ∈ m := by
    intro a
    have hu : IsUnit (algebraMap A (Localization.Away ((a : m) : A)) ((a : m) : A)) :=
      IsLocalization.Away.algebraMap_isUnit _
    have hmul : algebraMap A C' ((a : m) : A) * (0, Pi.single a ↑hu.unit⁻¹) = e a := by
      refine Prod.ext ?_ ?_
      · change algebraMap A Cg ((a : m) : A) * 0 = 0
        exact mul_zero _
      · change algebraMap A D ((a : m) : A) * Pi.single a (↑hu.unit⁻¹ :
          Localization.Away ((a : m) : A)) = Pi.single a 1
        exact pi_mul_single_eq_single (algebraMap A D ((a : m) : A)) a _ hu.mul_val_inv
    have hσa : σ (algebraMap A C' ((a : m) : A)) = ((a : m) : A) :=
      RingHom.congr_fun hσ _
    have : σ (e a) = ((a : m) : A) * σ (0, Pi.single a ↑hu.unit⁻¹) := by
      rw [← hmul, map_mul, hσa]
    rw [this]
    exact m.mul_mem_right _ (a : m).2
  have h10 : ((1, 0) : C') ∉ Ideal.comap σ m := by
    intro h
    rw [Ideal.mem_comap] at h
    have hsum : ((1, 0) : C') + ∑ a, e a = 1 := by
      change ((1, 0) : Cg × (Π c : t, Localization.Away ((c : m) : A))) +
          ∑ a : t, ((0 : Cg), Pi.single a (1 : Localization.Away ((a : m) : A))) = 1
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simpa [Prod.snd_sum] using
          Finset.univ_sum_single (1 : Π c : t, Localization.Away ((c : m) : A))
    have hone : σ (1, 0) + ∑ a, σ (e a) = 1 := by
      rw [← map_sum, ← map_add, hsum, map_one]
    have : (1 : A) ∈ m := by
      rw [← hone]
      exact Ideal.add_mem m h (Ideal.sum_mem m fun a _ => he_mem a)
    exact (Ideal.IsMaximal.ne_top ‹_›) ((Ideal.eq_top_iff_one m).mpr this)
  set P : Ideal C' := Ideal.comap σ m with hPdef
  haveI hP_prime : P.IsPrime := Ideal.IsPrime.comap σ
  have hP_over : P.comap (algebraMap A C') = m := by
    rw [hPdef, Ideal.comap_comap, hσ, Ideal.comap_id]
  -- the kernel of the first projection is contained in `P`
  have hker_fst : RingHom.ker (RingHom.fst Cg D) ≤ P := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hmul : x * ((1, 0) : C') = 0 := by
      refine Prod.ext ?_ (by simp)
      change x.1 * 1 = 0
      rw [show x.1 = (0 : Cg) from hx, zero_mul]
    have : x * ((1, 0) : C') ∈ P := hmul ▸ P.zero_mem
    exact (hP_prime.mem_or_mem this).resolve_right h10
  have hfst_surj : Function.Surjective (RingHom.fst Cg D) := Prod.fst_surjective
  haveI hpg_prime : (P.map (RingHom.fst Cg D)).IsPrime :=
    Ideal.map_isPrime_of_surjective hfst_surj hker_fst
  have hP_eq : (P.map (RingHom.fst Cg D)).comap (RingHom.fst Cg D) = P := by
    rw [Ideal.comap_map_of_surjective _ hfst_surj]
    rw [← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hker_fst
  have hpg : P.map (RingHom.fst Cg D) = q.map (algebraMap C Cg) := by
    refine huniq _ hpg_prime ?_
    rw [hfst_alg, ← Ideal.comap_comap, hP_eq, hP_over]
  -- Step 5: localize the retraction at `P` and pull back to `C`.
  set L := Localization.AtPrime P with hLdef
  have hℓ_ker : RingHom.ker (RingHom.fst Cg D) ≤ RingHom.ker (algebraMap C' L) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hmul : x * ((1, 0) : C') = 0 := by
      refine Prod.ext ?_ (by simp)
      change x.1 * 1 = 0
      rw [show x.1 = (0 : Cg) from hx, zero_mul]
    have h0 : algebraMap C' L x * algebraMap C' L (1, 0) = 0 := by
      rw [← map_mul, hmul, map_zero]
    have hunit : IsUnit (algebraMap C' L ((1, 0) : C')) :=
      IsLocalization.map_units L (⟨(1, 0), h10⟩ : P.primeCompl)
    exact (hunit.mul_left_eq_zero).mp h0
  set ψ : Cg →+* L := RingHom.liftOfRightInverse (RingHom.fst Cg D) (fun x => (x, 0))
    (fun x => rfl) ⟨algebraMap C' L, hℓ_ker⟩ with hψdef
  have hψ : ∀ x : C', ψ x.1 = algebraMap C' L x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hψ_comp : ψ.comp (RingHom.fst Cg D) = algebraMap C' L :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  set σL : L →+* Localization.AtPrime m := Localization.localRingHom P m σ rfl with hσLdef
  haveI : IsLocalHom σL := Localization.isLocalHom_localRingHom P m σ rfl
  have hσL : (maximalIdeal (Localization.AtPrime m)).comap σL = maximalIdeal L := by
    ext x
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff σL]
  have hcomap_ψ : (maximalIdeal L).comap ψ = q.map (algebraMap C Cg) := by
    apply Ideal.comap_injective_of_surjective (RingHom.fst Cg D) hfst_surj
    rw [Ideal.comap_comap, hψ_comp, ← hpg, hP_eq]
    exact Localization.AtPrime.under_maximalIdeal
  -- Assemble the algebra map.
  set ρ₀ : C →+* Localization.AtPrime m := (σL.comp ψ).comp (algebraMap C Cg) with hρ₀def
  have hcomm : ∀ r : A, ρ₀ (algebraMap A C r) = algebraMap A (Localization.AtPrime m) r := by
    intro r
    have hσr : σ (algebraMap A C' r) = r := RingHom.congr_fun hσ r
    change σL (ψ (algebraMap C Cg (algebraMap A C r))) = _
    rw [← IsScalarTower.algebraMap_apply A C Cg,
      show algebraMap A Cg r = (algebraMap A C' r).1 from rfl, hψ,
      Localization.localRingHom_to_map, hσr]
  refine ⟨{ toRingHom := ρ₀, commutes' := hcomm }, ?_⟩
  change (maximalIdeal (Localization.AtPrime m)).comap ρ₀ = q
  rw [hρ₀def, ← Ideal.comap_comap, ← Ideal.comap_comap, hσL, hcomap_ψ, hqg_under]

end KeyLemma

section Consumers

variable {A : Type u} [CommRing A]

/-- Helper: the standard étale pair `(F, F')` attached to a monic polynomial. -/
@[simps f g]
noncomputable def Polynomial.Monic.standardEtalePair {F : A[X]} (hF : F.Monic) :
    StandardEtalePair A where
  f := F
  monic_f := hF
  g := derivative F
  cond := ⟨1, 0, 1, by ring⟩

/-- Identity used to control the derivative of `scaleRoots`:
`(p.scaleRoots t) ∘ (tX) = tᵈ • p` as polynomials. -/
lemma Polynomial.scaleRoots_comp_C_mul_X {B : Type*} [CommRing B] (p : B[X]) (t : B) :
    (p.scaleRoots t).comp (C t * X) = C (t ^ p.natDegree) * p := by
  have h1 := Polynomial.scaleRoots_eval₂_mul (C : B →+* B[X]) X t (p := p)
  rw [Polynomial.eval₂_C_X] at h1
  rw [show (p.scaleRoots t).comp (C t * X) = eval₂ C (C t * X) (p.scaleRoots t) from rfl, h1,
    ← Polynomial.C_pow]

/-- Evaluation of the derivative of `scaleRoots`: `t * (p.scaleRoots t)'(t y) = tᵈ * p'(y)`. -/
lemma Polynomial.derivative_scaleRoots_eval {B : Type*} [CommRing B] (p : B[X]) (t y : B) :
    t * (derivative (p.scaleRoots t)).eval (t * y) =
      t ^ p.natDegree * (derivative p).eval y := by
  have h2 := congrArg derivative (p.scaleRoots_comp_C_mul_X t)
  rw [Polynomial.derivative_comp] at h2
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_C_mul] at h2
  have h3 := congrArg (Polynomial.eval y) h2
  simpa [Polynomial.eval_comp, mul_assoc] using h3

variable (H : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.Etale A B →
      Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) →
      ∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A)
  (m : Ideal A) [m.IsMaximal]

include H

/-- Under the retraction hypothesis, the residue field of `Aₘ` is separably closed. -/
theorem IsSepClosed.residueField_localization_atPrime_of_forall_retraction :
    IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m)) := by
  classical
  apply IsSepClosed.of_exists_root
  intro p hpm hpirr hpsep
  -- lift `p` to a monic polynomial over `A`
  have hlift : p ∈ Polynomial.lifts (algebraMap A m.ResidueField) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n =>
      Ideal.algebraMap_residueField_surjective m _
  obtain ⟨F, hF_map, -, hF_monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  set Q : StandardEtalePair A := hF_monic.standardEtalePair with hQdef
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  -- the root of `p` is an `AdjoinRoot p`-point of the standard étale algebra
  have haevalp : Polynomial.aeval (AdjoinRoot.root p) p = 0 := by
    rw [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root p
  have hroot0 : Polynomial.aeval (AdjoinRoot.root p) F = 0 := by
    rw [← Polynomial.aeval_map_algebraMap m.ResidueField, hF_map]
    exact haevalp
  have hroot1 : IsUnit (Polynomial.aeval (AdjoinRoot.root p) (derivative F)) := by
    rw [← Polynomial.aeval_map_algebraMap m.ResidueField, ← Polynomial.derivative_map, hF_map]
    obtain ⟨u', v', huv⟩ := hpsep
    have h1 := congrArg (Polynomial.aeval (AdjoinRoot.root p)) huv
    rw [map_add, map_mul, map_mul, map_one, haevalp, mul_zero, zero_add] at h1
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h1)
  set φK : Q.Ring →ₐ[A] AdjoinRoot p := Q.lift (AdjoinRoot.root p) ⟨hroot0, hroot1⟩ with hφKdef
  haveI : (RingHom.ker φK.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hover : (RingHom.ker φK.toRingHom).comap (algebraMap A Q.Ring) = m := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change φK (algebraMap A Q.Ring x) = 0 ↔ x ∈ m
    rw [φK.commutes, IsScalarTower.algebraMap_apply A m.ResidueField (AdjoinRoot p) x,
      map_eq_zero_iff _ (algebraMap m.ResidueField (AdjoinRoot p)).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  obtain ⟨ρ, -⟩ := Algebra.Etale.exists_algHom_localization_atPrime_comap_eq H m Q.Ring
    (RingHom.ker φK.toRingHom) hover
  -- the image of `X` under `ρ` reduces to a root of `p` in the residue field
  refine ⟨algebraMap (Localization.AtPrime m) m.ResidueField (ρ Q.X), ?_⟩
  have h0 : Polynomial.aeval Q.X Q.f = 0 := Q.hasMap_X.1
  have h1 : Polynomial.aeval
      (algebraMap (Localization.AtPrime m) m.ResidueField (ρ Q.X)) F = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algHom_apply,
      show Polynomial.aeval Q.X F = 0 from h0, map_zero, map_zero]
  rwa [Polynomial.aeval_def, ← Polynomial.eval_map, hF_map] at h1

/-- Under the retraction hypothesis, `Aₘ` is henselian. -/
theorem HenselianLocalRing.localization_atPrime_of_forall_retraction :
    HenselianLocalRing (Localization.AtPrime m) := by
  classical
  constructor
  intro f hf a₀ h₁ h₂
  have hres0 : ∀ z : Localization.AtPrime m,
      algebraMap (Localization.AtPrime m) m.ResidueField z = 0 ↔
        z ∈ maximalIdeal (Localization.AtPrime m) := fun z => by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  -- clear denominators using `scaleRoots`
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples m.primeCompl
    (Finset.range (f.natDegree + 1)) f.coeff
  set t : Localization.AtPrime m := algebraMap A (Localization.AtPrime m) (s : A) with htdef
  have ht : IsUnit t := IsLocalization.map_units (Localization.AtPrime m) s
  have hG_lifts : f.scaleRoots t ∈ Polynomial.lifts (algebraMap A (Localization.AtPrime m)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rcases lt_trichotomy n f.natDegree with hn | hn | hn
    · obtain ⟨b, hb⟩ := hs n (Finset.mem_range.mpr (by omega))
      have hb' : algebraMap A (Localization.AtPrime m) b = t * f.coeff n := by
        rw [hb, Algebra.smul_def, htdef]
      refine ⟨b * (s : A) ^ (f.natDegree - n - 1), ?_⟩
      have hd : f.natDegree - n = (f.natDegree - n - 1) + 1 := by omega
      conv_rhs => rw [Polynomial.coeff_scaleRoots, hd, pow_succ]
      rw [map_mul, map_pow, hb', ← htdef]
      ring
    · refine ⟨1, ?_⟩
      rw [map_one, hn, Polynomial.coeff_scaleRoots_natDegree]
      exact hf.leadingCoeff.symm
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.coeff_scaleRoots, Polynomial.coeff_eq_zero_of_natDegree_lt hn,
        zero_mul]
  obtain ⟨F, hF_map, -, hF_monic⟩ := Polynomial.lifts_and_degree_eq_and_monic hG_lifts
    ((Polynomial.monic_scaleRoots_iff t).mpr hf)
  set Q : StandardEtalePair A := hF_monic.standardEtalePair with hQdef
  -- the residue of `t * a₀` is a `κ(m)`-point of the standard étale algebra
  set x₀ : m.ResidueField :=
    algebraMap (Localization.AtPrime m) m.ResidueField (t * a₀) with hx₀def
  have haeval_ta₀ : Polynomial.aeval (t * a₀) F = t ^ f.natDegree * f.eval a₀ := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hF_map, Polynomial.scaleRoots_eval_mul]
  have hres_eval : algebraMap (Localization.AtPrime m) m.ResidueField (f.eval a₀) = 0 :=
    (hres0 _).mpr h₁
  have hx1 : Polynomial.aeval x₀ F = 0 := by
    rw [hx₀def, Polynomial.aeval_algebraMap_apply, haeval_ta₀, map_mul, hres_eval, mul_zero]
  have hx2 : IsUnit (Polynomial.aeval x₀ (derivative F)) := by
    have hGd : Polynomial.aeval (t * a₀) (derivative F) =
        (derivative (f.scaleRoots t)).eval (t * a₀) := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF_map]
    have hu2 : IsUnit ((derivative (f.scaleRoots t)).eval (t * a₀)) := by
      have hid := Polynomial.derivative_scaleRoots_eval f t a₀
      have hRHS : IsUnit (t ^ f.natDegree * (derivative f).eval a₀) := (ht.pow _).mul h₂
      rw [← hid] at hRHS
      exact isUnit_of_mul_isUnit_right hRHS
    rw [hx₀def, Polynomial.aeval_algebraMap_apply, hGd]
    exact hu2.map _
  set φ : Q.Ring →ₐ[A] m.ResidueField := Q.lift x₀ ⟨hx1, hx2⟩ with hφdef
  haveI : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hover : (RingHom.ker φ.toRingHom).comap (algebraMap A Q.Ring) = m := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change φ (algebraMap A Q.Ring x) = 0 ↔ x ∈ m
    rw [φ.commutes]
    exact Ideal.algebraMap_residueField_eq_zero
  obtain ⟨ρ, hρ⟩ := Algebra.Etale.exists_algHom_localization_atPrime_comap_eq H m Q.Ring
    (RingHom.ker φ.toRingHom) hover
  -- the reduction of `ρ` coincides with `φ` (both have the same kernel and `A → κ(m)` is onto)
  have hres : ∀ c : Q.Ring,
      algebraMap (Localization.AtPrime m) m.ResidueField (ρ c) = φ c := by
    intro c
    obtain ⟨a, ha⟩ := Ideal.algebraMap_residueField_surjective m (φ c)
    have hkc : c - algebraMap A Q.Ring a ∈ RingHom.ker φ.toRingHom := by
      rw [RingHom.mem_ker]
      change φ (c - algebraMap A Q.Ring a) = 0
      rw [map_sub, φ.commutes, ha, sub_self]
    have hkc' : ρ (c - algebraMap A Q.Ring a) ∈
        maximalIdeal (Localization.AtPrime m) := by
      rw [← hρ] at hkc
      exact hkc
    have h0 : algebraMap (Localization.AtPrime m) m.ResidueField
        (ρ (c - algebraMap A Q.Ring a)) = 0 := (hres0 _).mpr hkc'
    have h0' : algebraMap (Localization.AtPrime m) m.ResidueField (ρ c) -
        algebraMap A m.ResidueField a = 0 := by
      rw [map_sub, map_sub, ρ.commutes, ← IsScalarTower.algebraMap_apply] at h0
      exact h0
    rw [sub_eq_zero] at h0'
    rw [h0', ha]
  -- extract the root
  set a' : Localization.AtPrime m := ρ Q.X with ha'def
  have haF : Polynomial.aeval a' F = 0 := by
    rw [ha'def, Polynomial.aeval_algHom_apply, show Polynomial.aeval Q.X F = 0 from
      Q.hasMap_X.1, map_zero]
  have hGa' : (f.scaleRoots t).eval a' = 0 := by
    rw [← hF_map, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact haF
  set a : Localization.AtPrime m := (↑ht.unit⁻¹ : Localization.AtPrime m) * a' with hadef
  have hta : t * a = a' := by
    rw [hadef, ← mul_assoc, ht.mul_val_inv, one_mul]
  have hroot : f.eval a = 0 := by
    have h3 : t ^ f.natDegree * f.eval a = 0 := by
      rw [← Polynomial.scaleRoots_eval_mul, hta, hGa']
    exact ((ht.pow f.natDegree).mul_right_eq_zero).mp h3
  refine ⟨a, hroot, ?_⟩
  -- the root reduces to the residue of `a₀`
  have h1 : algebraMap (Localization.AtPrime m) m.ResidueField a' = x₀ := by
    rw [ha'def, hres Q.X, hφdef, StandardEtalePair.lift_X]
  have h2 : algebraMap (Localization.AtPrime m) m.ResidueField a =
      algebraMap (Localization.AtPrime m) m.ResidueField a₀ := by
    have h3 : algebraMap (Localization.AtPrime m) m.ResidueField (t * a) =
        algebraMap (Localization.AtPrime m) m.ResidueField (t * a₀) := by
      rw [hta, h1, hx₀def]
    rw [map_mul, map_mul] at h3
    exact (ht.map (algebraMap (Localization.AtPrime m) m.ResidueField)).mul_left_cancel h3
  have h4 : algebraMap (Localization.AtPrime m) m.ResidueField (a - a₀) = 0 := by
    rw [map_sub, h2, sub_self]
  exact (hres0 _).mp h4

end Consumers

/-- Blueprint `lemma:retractions-strictly-henselian`: if every faithfully flat étale ring map
out of `A` has a retraction, then the local rings of `A` at maximal ideals are strictly
henselian. -/
theorem IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
    {A : Type u} [CommRing A]
    (H : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.Etale A B →
      Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) →
      ∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A)
    (m : Ideal A) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) :=
  (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed _).mpr
    ⟨HenselianLocalRing.localization_atPrime_of_forall_retraction H m,
      IsSepClosed.residueField_localization_atPrime_of_forall_retraction H m⟩

/-- Blueprint `cor:strictly-henselian-etale-contraction`: the local rings of the ind-étale
contraction of a ring at maximal ideals are strictly henselian. -/
theorem IsStrictlyHenselianLocalRing.localization_atPrime_indEtaleContraction
    (R : Type u) [CommRing R] (m : Ideal (IndEtaleContraction R)) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) :=
  IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
    (fun B _ _ hB hsurj =>
      RingHom.Etale.exists_comp_eq_id_indContraction (algebraMap _ B)
        (RingHom.etale_algebraMap.mpr hB) hsurj) m
