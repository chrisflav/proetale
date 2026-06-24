/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.RingTheory.Henselian

/-!
# Local rings and integral algebras

This file collects miscellaneous lemmas relating local rings, integral ring
homomorphisms, and Henselian local rings.  These are used in the proof of
[Stacks 097Z](https://stacks.math.columbia.edu/tag/097Z) (over a strictly
Henselian local ring, a weakly étale local algebra is the ring itself).

## Main statements

* `HenselianLocalRing.exists_pi_of_finite` ([Stacks 04GH (1)]
  (https://stacks.math.columbia.edu/tag/04GH)):
  A finite algebra over a Henselian local ring decomposes as a finite product
  of Henselian local rings, each finite over the base.
* `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain`:
  An integral algebra over a Henselian local ring that is an integral domain is local.
* `Algebra.IsAlgebraic.residueField_of_isIntegral`:
  The residue field extension induced by a local integral homomorphism of local rings
  is algebraic.
* `Algebra.isLocalRing_tensorProduct_of_isPurelyInseparable_residueField`
  ([Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y)):
  If `R → S` is local and integral and either `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely
  inseparable, the tensor product `S ⊗[R] T` is a local ring.
-/

universe u

open TensorProduct

namespace HenselianLocalRing

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S]

/-- A finite algebra over a Henselian local ring is, as a ring, a finite product of
Henselian local rings, each finite over the base.

[Stacks 04GH (1)](https://stacks.math.columbia.edu/tag/04GH).

This is destined to go directly to Mathlib, so it should not be worked on here. -/
theorem exists_pi_of_finite :
    ∃ (ι : Type u) (_ : Fintype ι) (B : ι → Type u) (_ : ∀ i, CommRing (B i))
      (_ : ∀ i, IsLocalRing (B i)) (_ : ∀ i, HenselianLocalRing (B i))
      (_ : ∀ i, Algebra R (B i)) (_ : ∀ i, Module.Finite R (B i)),
        Nonempty (S ≃ₐ[R] (Π i, B i)) :=
  sorry

end HenselianLocalRing

namespace IsLocalRing

/-- An integral algebra over a Henselian local ring that is an integral domain is local. -/
theorem of_henselianLocalRing_of_isIntegral_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] :
    IsLocalRing S :=
  sorry

/-- A commutative ring with nonempty and subsingleton prime spectrum is local. -/
theorem of_nonempty_subsingleton_primeSpectrum {A : Type*} [CommRing A]
    (h₁ : Nonempty (PrimeSpectrum A)) (h₂ : Subsingleton (PrimeSpectrum A)) :
    IsLocalRing A := by
  obtain ⟨p⟩ := h₁
  have : Nontrivial A :=
    ⟨0, 1, fun e ↦ p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (e ▸ p.asIdeal.zero_mem))⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun J hJ ↦ ?_⟩
  exact congrArg PrimeSpectrum.asIdeal (h₂.elim ⟨J, hJ.isPrime⟩ ⟨m, hm.isPrime⟩)

/-- If the quotient `A ⧸ I` is local and `I` is contained in the Jacobson radical of `A`
(equivalently, `I` is contained in every maximal ideal of `A`), then `A` is local. -/
theorem of_isLocalRing_quotient_of_le_jacobson {A : Type*} [CommRing A] (I : Ideal A)
    [IsLocalRing (A ⧸ I)] (hI : I ≤ (⊥ : Ideal A).jacobson) : IsLocalRing A := by
  classical
  have : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  -- every maximal ideal of `A` contains `I`, hence is the contraction of `𝔪_{A ⧸ I}`
  have key : ∀ Q : Ideal A, Q.IsMaximal →
      Q = (maximalIdeal (A ⧸ I)).comap (Ideal.Quotient.mk I) := by
    intro Q hQ
    have hIQ : I ≤ Q := hI.trans (sInf_le ⟨bot_le, hQ⟩)
    have hmapne : Q.map (Ideal.Quotient.mk I) ≠ ⊤ := by
      intro htop
      have hcm := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective Q
      rw [htop, Ideal.comap_top] at hcm
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := Ideal.mk_ker
      rw [hker] at hcm
      exact hQ.ne_top (by rw [← sup_eq_left.mpr hIQ, ← hcm])
    have hQle : Q ≤ (maximalIdeal (A ⧸ I)).comap (Ideal.Quotient.mk I) :=
      Ideal.le_comap_map.trans (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hmapne))
    exact hQ.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hQle
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact of_unique_max_ideal ⟨M, hM, fun J hJ ↦ by rw [key J hJ, key M hM]⟩

/-- For a local ring `W` with a local homomorphism `R → W` from a local ring `R`, the
composite `R → κ(W)` kills the maximal ideal of `R`. -/
theorem algebraMap_residueField_eq_zero_of_mem_maximalIdeal {R W : Type*} [CommRing R]
    [CommRing W] [IsLocalRing R] [Algebra R W] [IsLocalRing W] [IsLocalHom (algebraMap R W)]
    {x : R} (hx : x ∈ maximalIdeal R) : algebraMap R (ResidueField W) x = 0 := by
  rw [IsScalarTower.algebraMap_apply R W (ResidueField W), ResidueField.algebraMap_eq,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsLocalHom.map_nonunit x hu)

end IsLocalRing

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The residue field extension induced by a local integral homomorphism of local rings is
algebraic. -/
theorem IsAlgebraic.residueField_of_isIntegral [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- It suffices to show that `κ(S)` is integral over `R`: since `S` is integral over `R`
  -- and `κ(S)` is integral over `S` (the map `S → κ(S)` is surjective), the composition
  -- `R → S → κ(S)` is integral.  Integrality then descends along the surjection `R → κ(R)`,
  -- so `κ(S)` is integral, hence algebraic, over `κ(R)`.
  have : Algebra.IsIntegral S (IsLocalRing.ResidueField S) :=
    Algebra.isIntegral_of_surjective IsLocalRing.residue_surjective
  have : Algebra.IsIntegral R (IsLocalRing.ResidueField S) := Algebra.IsIntegral.trans S
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.IsIntegral.tower_top R
  infer_instance

section TensorProduct

open IsLocalRing

/-- If `L` is a purely inseparable extension of the residue field of a local ring `R` and
`K` is an `R`-field killed by the maximal ideal, then `L ⊗[R] K` is a local ring. -/
private theorem isLocalRing_tensorProduct_of_isPurelyInseparable_left
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L K : Type u) [Field L] [Field K] [Algebra R L] [Algebra R K]
    [Algebra (ResidueField R) L] [IsScalarTower R (ResidueField R) L]
    [IsPurelyInseparable (ResidueField R) L]
    (hK : ∀ x ∈ maximalIdeal R, algebraMap R K x = 0) :
    IsLocalRing (L ⊗[R] K) := by
  -- `κ(R) ⊗[R] K ≃ K` since `K` is killed by the maximal ideal.
  let u : ResidueField R →ₐ[R] K :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R K) hK
  let Φ : (ResidueField R) ⊗[R] K →ₐ[R] K := Algebra.TensorProduct.productMap u (AlgHom.id R K)
  have htmul : ∀ z : (ResidueField R) ⊗[R] K, ∃ x : K, z = 1 ⊗ₜ[R] x := by
    intro z
    induction z with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul r x =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      refine ⟨algebraMap R K r * x, ?_⟩
      rw [← ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.smul_def]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, (TensorProduct.tmul_add _ _ _).symm⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro z w hzw
      obtain ⟨x, rfl⟩ := htmul z
      obtain ⟨y, rfl⟩ := htmul w
      obtain rfl : x = y := by simpa [Φ] using hzw
      rfl
    · intro x
      exact ⟨1 ⊗ₜ x, by simp [Φ]⟩
  let e : (ResidueField R) ⊗[R] K ≃ₐ[R] K := AlgEquiv.ofBijective Φ hΦ
  have h1 : IsHomeomorph (PrimeSpectrum.comap (Algebra.TensorProduct.map
      (Algebra.ofId (ResidueField R) L) (AlgHom.id R K)).toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (K := ResidueField R) (R := R) (S := K) L
  -- `Spec (κ(R) ⊗[R] K)` is a single point: it is homeomorphic to `Spec K`, which is one
  have hsub : Subsingleton (PrimeSpectrum ((ResidueField R) ⊗[R] K)) :=
    ((PrimeSpectrum.isHomeomorph_comap_of_bijective
      e.toRingEquiv.bijective).bijective.surjective).subsingleton
  have hne : Nonempty (PrimeSpectrum ((ResidueField R) ⊗[R] K)) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    exact ⟨PrimeSpectrum.comap (e.toRingEquiv : _ ≃+* K).toRingHom q⟩
  -- `Spec (L ⊗[R] K) ≅ Spec (κ(R) ⊗[R] K)` since `κ(R) → L` is purely inseparable
  refine IsLocalRing.of_nonempty_subsingleton_primeSpectrum ?_
    (h1.bijective.injective.subsingleton)
  obtain ⟨q⟩ := hne
  obtain ⟨p, -⟩ := h1.bijective.surjective q
  exact ⟨p⟩

variable (R S) in
private theorem isLocalRing_tensorProduct_aux
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (T ⊗[R] S) := by
  classical
  -- the tensor product of the residue fields is local
  have hcase : IsLocalRing ((ResidueField T) ⊗[R] (ResidueField S)) := by
    rcases h with h | h
    · have := h
      have hloc : IsLocalRing ((ResidueField S) ⊗[R] (ResidueField T)) :=
        isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField S)
          (ResidueField T) fun _ hx ↦
            IsLocalRing.algebraMap_residueField_eq_zero_of_mem_maximalIdeal (W := T) hx
      exact (Algebra.TensorProduct.comm R (ResidueField S)
        (ResidueField T)).toRingEquiv.isLocalRing
    · have := h
      exact isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField T)
        (ResidueField S) fun _ hx ↦
          IsLocalRing.algebraMap_residueField_eq_zero_of_mem_maximalIdeal (W := S) hx
  -- the two distinguished ideals of the tensor product
  set A := T ⊗[R] S
  let inclS : S →ₐ[R] A := Algebra.TensorProduct.includeRight
  let J₂ : Ideal A := (maximalIdeal S).map inclS
  let J₁ : Ideal A := (maximalIdeal T).map (algebraMap T A)
  -- identify `A ⧸ (J₂ ⊔ J₁)` with `κ(T) ⊗[R] κ(S)`
  let e₁ : T ⊗[R] (ResidueField S) ≃ₐ[R] A ⧸ J₂ :=
    Algebra.TensorProduct.tensorQuotientEquiv R S T (maximalIdeal S)
  let I₁ : Ideal (T ⊗[R] (ResidueField S)) :=
    (maximalIdeal T).map (algebraMap T (T ⊗[R] (ResidueField S)))
  have hcomm : (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂).comp
      (algebraMap T (T ⊗[R] (ResidueField S)))
      = (Ideal.Quotient.mk J₂).comp (algebraMap T A) := by
    ext t
    exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul (R := R) R S T
      (maximalIdeal S) t 1
  have hIJ : J₁.map (Ideal.Quotient.mk J₂)
      = I₁.map (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂) := by
    rw [Ideal.map_map, Ideal.map_map, hcomm]
  let E₂ : (T ⊗[R] (ResidueField S)) ⧸ I₁ ≃+* (A ⧸ J₂) ⧸ J₁.map (Ideal.Quotient.mk J₂) :=
    Ideal.quotientEquiv I₁ (J₁.map (Ideal.Quotient.mk J₂)) e₁.toRingEquiv hIJ
  let E₃ : (ResidueField T) ⊗[R] (ResidueField S) ≃ₐ[R] (T ⊗[R] (ResidueField S)) ⧸ I₁ :=
    Algebra.TensorProduct.quotientTensorEquiv R (ResidueField S) T (maximalIdeal T)
  let E : (ResidueField T) ⊗[R] (ResidueField S) ≃+* A ⧸ (J₂ ⊔ J₁) :=
    (E₃.toRingEquiv.trans E₂).trans (DoubleQuot.quotQuotEquivQuotSup J₂ J₁)
  have hQuot : IsLocalRing (A ⧸ (J₂ ⊔ J₁)) := E.isLocalRing
  -- every maximal ideal of `A` contains `J₂ ⊔ J₁`
  have hle : ∀ Q : Ideal A, Q.IsMaximal → J₂ ⊔ J₁ ≤ Q := by
    intro Q hQ
    have := hQ.isPrime
    have hT : Q.comap (algebraMap T A) = maximalIdeal T :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
    have hR : Q.comap (algebraMap R A) = maximalIdeal R := by
      rw [IsScalarTower.algebraMap_eq R T A, ← Ideal.comap_comap, hT,
        IsLocalRing.maximalIdeal_comap]
    have hScomap : (Q.comap inclS.toRingHom).comap (algebraMap R S) = maximalIdeal R := by
      have hcompS : inclS.toRingHom.comp (algebraMap R S) = algebraMap R A := by
        ext r
        exact inclS.commutes r
      rw [Ideal.comap_comap, hcompS, hR]
    have hSmax : (Q.comap inclS.toRingHom).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
        (Q.comap inclS.toRingHom) ?_
      rw [hScomap]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have hS : Q.comap inclS.toRingHom = maximalIdeal S := IsLocalRing.eq_maximalIdeal hSmax
    exact sup_le (Ideal.map_le_iff_le_comap.mpr hS.ge) (Ideal.map_le_iff_le_comap.mpr hT.ge)
  -- conclude: `J₂ ⊔ J₁` is below every maximal ideal, and the quotient by it is local
  have := hQuot
  exact IsLocalRing.of_isLocalRing_quotient_of_le_jacobson (J₂ ⊔ J₁)
    (le_sInf fun Q hQ ↦ hle Q hQ.2)

variable (R S) in
/-- Let `R → S` and `R → T` be local ring homomorphisms of local rings, with `R → S`
integral.  If `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely inseparable, the tensor product
`S ⊗[R] T` is a local ring.

[Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y). -/
theorem isLocalRing_tensorProduct_of_isPurelyInseparable_residueField
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (S ⊗[R] T) := by
  have := isLocalRing_tensorProduct_aux R S T h
  exact (Algebra.TensorProduct.comm R T S).toRingEquiv.isLocalRing

end TensorProduct

end Algebra
