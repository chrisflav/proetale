/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.DepRewrite

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/
/-- An `R`-algebra `S` is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
class Algebra.IsLocalIso (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] : Prop where
  exists_notMem_isStandardOpenImmersion (q : Ideal S) [q.IsPrime] :
    ∃ g ∉ q, IsStandardOpenImmersion R (Localization.Away g)

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

lemma Algebra.IsStandardOpenImmersion.of_bijective (h : Function.Bijective (algebraMap R S)) :
    IsStandardOpenImmersion R S := by
  rw [Algebra.isStandardOpenImmersion_iff]
  use 1
  apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one h

namespace Algebra.IsLocalIso

instance [IsStandardOpenImmersion R S] : IsLocalIso R S where
  exists_notMem_isStandardOpenImmersion q hq := by
    use 1, hq.one_notMem
    exact IsStandardOpenImmersion.trans _ S _


lemma of_span_eq_top {ι : Type*} (f : ι → S) (h : Ideal.span (Set.range f) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra S (T i)]
    [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (f i) (T i)]
    [∀ i, IsLocalIso R (T i)] : IsLocalIso R S := by
  constructor
  intro q  hq
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff] at h

  have : ⟨q, hq⟩ ∈ ⨆ i, PrimeSpectrum.basicOpen (f i)  := by simp [h]
  simp at this
  obtain ⟨i, hi⟩ := this
  have : ⟨q, hq⟩ ∈ PrimeSpectrum.basicOpen (f i) := hi
  rw [← SetLike.mem_coe, ← PrimeSpectrum.localization_away_comap_range (T i)] at this
  obtain ⟨q', hq'⟩ := this
  obtain ⟨g', hg', h⟩ := exists_notMem_isStandardOpenImmersion (R := R) q'.1
  obtain ⟨n, g, hg⟩ := IsLocalization.Away.surj (f i) g'
  use g * (f i)

  constructor
  · apply Ideal.IsPrime.mul_notMem hq _ hi
    simp [PrimeSpectrum.ext_iff] at hq'
    rw [← hq']
    simp
    rw [← hg]
    rwa [Ideal.mul_unit_mem_iff_mem]
    apply IsUnit.pow
    apply IsLocalization.Away.algebraMap_isUnit
  · have : IsLocalization.Away (g * (f i)) (Localization.Away (algebraMap S (T i) g)) := .mul (T i) _ _ _
    let e : Localization.Away (g * (f i)) ≃ₐ[S] (Localization.Away (algebraMap S (T i) g)) :=
      Localization.algEquiv _ _
    let : Algebra (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) :=
      RingHom.toAlgebra e.symm.toAlgHom

    have : IsScalarTower R (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) := by
      refine .of_algebraMap_eq' ?_
      rw [RingHom.algebraMap_toAlgebra]
      rw [← RingHom.cancel_left (g := e.toRingHom) e.injective]
      ext
      simp
      simp [e]
      rw [IsScalarTower.algebraMap_apply R S]
      simp
      rw [← IsScalarTower.algebraMap_apply R S]

    have : IsStandardOpenImmersion (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) :=
      .of_bijective _ _ e.symm.bijective
    have : IsStandardOpenImmersion R (Localization.Away ((algebraMap S (T i)) g)) := sorry
    apply IsStandardOpenImmersion.trans _ (Localization.Away (algebraMap S (T i) g)) _

lemma pi_of_finite {ι : Type*} (R : Type*) (S : ι → Type*)
    [CommRing R] [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [Finite ι] [∀ i, IsLocalIso R (S i)] :
    IsLocalIso R (∀ i, S i)  := by

  sorry

end Algebra.IsLocalIso

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)"]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso :=
  sorry

lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso :=
  sorry

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
