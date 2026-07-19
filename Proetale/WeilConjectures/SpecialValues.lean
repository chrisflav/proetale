/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaFunction

/-!
# The zeta functions of `Spec 𝔽_q` and `Spec ℤ`

We compute the zeta function of the spectrum of a finite field (a single Euler factor)
and identify the zeta function of `Spec ℤ` with the Riemann zeta function on the
half-plane of absolute convergence, via the classification of the primes of `ℤ`, the
computation of the residue fields `κ((p)) ≅ ℤ/p` and `κ((0)) ≅ ℚ`, and the Euler
product for the Riemann zeta function.

## Main statements

- `AlgebraicGeometry.Scheme.zeta_spec_eq_of_finite`
- `AlgebraicGeometry.Scheme.zeta_specInt_eq_riemannZeta`
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The residue field of `Spec R` at a point `x` is the residue field of the prime `x`. -/
private noncomputable def specResidueFieldEquiv (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).residueField x ≃+* x.asIdeal.ResidueField :=
  (Spec.residueFieldIso R x).commRingCatIsoToRingEquiv

private lemma finite_residueField_iff (R : CommRingCat.{u}) (x : Spec R) :
    Finite ((Spec R).residueField x) ↔ Finite x.asIdeal.ResidueField :=
  ⟨fun _ ↦ .of_equiv _ (specResidueFieldEquiv R x).toEquiv,
    fun _ ↦ .of_equiv _ (specResidueFieldEquiv R x).symm.toEquiv⟩

private lemma pointNorm_spec (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).pointNorm x = Nat.card x.asIdeal.ResidueField :=
  Nat.card_congr (specResidueFieldEquiv R x).toEquiv

/-- The residue field of `Spec k` at any point is `k`, for a field `k`. -/
private noncomputable def residueFieldEquivOfField {k : Type u} [Field k]
    (x : Spec (CommRingCat.of k)) : ((Spec (CommRingCat.of k)).residueField x) ≃ k :=
  ((specResidueFieldEquiv (CommRingCat.of k) x).trans
    (Ideal.algEquivResidueFieldOfField x.asIdeal).symm.toRingEquiv).toEquiv

/-- The zeta function of the spectrum of a finite field `k` is `(1 - #k ^ (-s))⁻¹`. -/
theorem zeta_spec_eq_of_finite (k : Type u) [Field k] [Finite k] (s : ℂ) :
    (Spec (.of k)).zeta s = (1 - (Nat.card k : ℂ) ^ (-s))⁻¹ := by
  haveI : Unique ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Unique (PrimeSpectrum k))
  have hmem : (default : ↥(Spec (CommRingCat.of k))) ∈ (Spec (CommRingCat.of k)).finitePoints :=
    Finite.of_equiv k (residueFieldEquivOfField default).symm
  have hnorm : (Spec (CommRingCat.of k)).pointNorm default = Nat.card k :=
    Nat.card_congr (residueFieldEquivOfField default)
  calc (Spec (.of k)).zeta s
      = (Spec (CommRingCat.of k)).eulerFactor default s :=
        tprod_eq_mulSingle (f := fun x : ↥(Spec (CommRingCat.of k)).finitePoints ↦
            (Spec (CommRingCat.of k)).eulerFactor x.1 s)
          ⟨default, hmem⟩ fun c hc ↦ absurd (Subtype.ext (Subsingleton.elim _ _)) hc
    _ = (1 - ((Spec (CommRingCat.of k)).pointNorm default : ℂ) ^ (-s))⁻¹ := rfl
    _ = (1 - (Nat.card k : ℂ) ^ (-s))⁻¹ := by rw [hnorm]

/-- The residue field of `ℤ` at `(0)` is infinite (it is `ℚ`). -/
private lemma not_finite_residueField_of_eq_bot {I : Ideal ℤ} [I.IsPrime] (hI : I = ⊥) :
    ¬Finite I.ResidueField := by
  subst hI
  haveI : Infinite (ℤ ⧸ (⊥ : Ideal ℤ)) :=
    Infinite.of_injective (Ideal.Quotient.mk ⊥)
      ((RingHom.injective_iff_ker_eq_bot _).mpr Ideal.mk_ker)
  haveI : Infinite ((⊥ : Ideal ℤ).ResidueField) :=
    Infinite.of_injective (algebraMap (ℤ ⧸ (⊥ : Ideal ℤ)) ((⊥ : Ideal ℤ).ResidueField))
      (⊥ : Ideal ℤ).injective_algebraMap_quotient_residueField
  exact fun h ↦ @not_finite ((⊥ : Ideal ℤ).ResidueField) _ h

/-- The residue field of `ℤ` at `(p)` is finite of cardinality `p` (it is `ℤ/p`). -/
private lemma finite_residueField_of_span {I : Ideal ℤ} [I.IsPrime] {p : ℕ} (hp : p.Prime)
    (hI : I = Ideal.span {(p : ℤ)}) :
    Finite I.ResidueField ∧ Nat.card I.ResidueField = p := by
  subst hI
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    IsPrime.to_maximal_ideal (by simpa using hp.ne_zero)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have e : ZMod p ≃ (Ideal.span {(p : ℤ)} : Ideal ℤ).ResidueField :=
    ((Int.quotientSpanNatEquivZMod p).symm.trans
      (RingEquiv.ofBijective (algebraMap (ℤ ⧸ Ideal.span {(p : ℤ)}) _)
        (Ideal.bijective_algebraMap_quotient_residueField _))).toEquiv
  exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm.trans (Nat.card_zmod p)⟩

/-- The point of `Spec ℤ` associated to a prime number. -/
private def primesToSpecInt (p : Nat.Primes) : ↥(Spec (CommRingCat.of ℤ)) :=
  (⟨Ideal.span {((p : ℕ) : ℤ)}, (Ideal.span_singleton_prime
    (Int.natCast_ne_zero.mpr p.2.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp p.2)⟩ : PrimeSpectrum ℤ)

private lemma primesToSpecInt_mem (p : Nat.Primes) :
    primesToSpecInt p ∈ (Spec (CommRingCat.of ℤ)).finitePoints :=
  (finite_residueField_iff (CommRingCat.of ℤ) (primesToSpecInt p)).mpr
    (finite_residueField_of_span (I := (primesToSpecInt p).asIdeal) p.2 rfl).1

private lemma pointNorm_primesToSpecInt (p : Nat.Primes) :
    (Spec (CommRingCat.of ℤ)).pointNorm (primesToSpecInt p) = p :=
  (pointNorm_spec _ _).trans
    (finite_residueField_of_span (I := (primesToSpecInt p).asIdeal) p.2 rfl).2

private lemma primesToSpecInt_injective : Function.Injective primesToSpecInt := by
  intro p q h
  have hspan : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} :=
    congrArg PrimeSpectrum.asIdeal h
  have h1 : ((q : ℕ) : ℤ) ∣ ((p : ℕ) : ℤ) := Ideal.span_singleton_le_span_singleton.mp hspan.le
  have h2 : ((p : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := Ideal.span_singleton_le_span_singleton.mp hspan.ge
  exact Subtype.ext (Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp h2)
    (Int.natCast_dvd_natCast.mp h1))

private lemma exists_primesToSpecInt_eq (x : ↥(Spec (CommRingCat.of ℤ)))
    (hx : x ∈ (Spec (CommRingCat.of ℤ)).finitePoints) :
    ∃ p : Nat.Primes, primesToSpecInt p = x := by
  have hfin : Finite x.asIdeal.ResidueField := (finite_residueField_iff _ x).mp hx
  obtain hbot | ⟨p, hp, hspan⟩ := Ideal.isPrime_int_iff.mp x.isPrime
  · exact absurd hfin (not_finite_residueField_of_eq_bot hbot)
  · exact ⟨⟨p, hp⟩, PrimeSpectrum.ext hspan.symm⟩

/-- The primes of `ℤ` are the finite-residue-field points of `Spec ℤ`. -/
private noncomputable def primesEquivFinitePoints :
    Nat.Primes ≃ ↥((Spec (CommRingCat.of ℤ)).finitePoints) :=
  Equiv.ofBijective (fun p ↦ ⟨primesToSpecInt p, primesToSpecInt_mem p⟩)
    ⟨fun _ _ h ↦ primesToSpecInt_injective (congrArg Subtype.val h),
      fun x ↦ (exists_primesToSpecInt_eq x.1 x.2).imp fun _ hp ↦ Subtype.ext hp⟩

/-- The zeta function of `Spec ℤ` is the Riemann zeta function (on the half-plane of
absolute convergence, hence everywhere by analytic continuation of the right hand side). -/
theorem zeta_specInt_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    (Spec (.of ℤ)).zeta s = riemannZeta s := by
  have h1 (p : Nat.Primes) :
      (Spec (CommRingCat.of ℤ)).eulerFactor (primesEquivFinitePoints p).1 s =
        (1 - (p : ℂ) ^ (-s))⁻¹ := by
    calc (Spec (CommRingCat.of ℤ)).eulerFactor (primesEquivFinitePoints p).1 s
        = (1 - ((Spec (CommRingCat.of ℤ)).pointNorm (primesToSpecInt p) : ℂ) ^ (-s))⁻¹ := rfl
      _ = (1 - (p : ℂ) ^ (-s))⁻¹ := by rw [pointNorm_primesToSpecInt]
  calc (Spec (.of ℤ)).zeta s
      = ∏' p : Nat.Primes,
          (Spec (CommRingCat.of ℤ)).eulerFactor (primesEquivFinitePoints p).1 s :=
        (primesEquivFinitePoints.tprod_eq
          fun x ↦ (Spec (CommRingCat.of ℤ)).eulerFactor x.1 s).symm
    _ = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := tprod_congr h1
    _ = riemannZeta s := riemannZeta_eulerProduct_tprod hs

end AlgebraicGeometry.Scheme
