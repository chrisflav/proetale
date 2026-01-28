/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.DepRewrite
import Proetale.Mathlib.RingTheory.RingHom.OpenImmersion

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

namespace Algebra.IsLocalIso

instance (priority := 100) [IsStandardOpenImmersion R S] : IsLocalIso R S where
  exists_notMem_isStandardOpenImmersion q hq := by
    use 1, hq.one_notMem
    exact IsStandardOpenImmersion.trans _ S _

-- TODO: cleanup proof after bumping
lemma of_span_eq_top {ι : Type*} (f : ι → S) (h : Ideal.span (Set.range f) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra S (T i)]
    [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (f i) (T i)]
    [∀ i, IsLocalIso R (T i)] : IsLocalIso R S := by
  constructor
  intro q hq
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
  · have : IsLocalization.Away (g * f i) (Localization.Away (algebraMap S (T i) g)) :=
      .mul (T i) _ _ _
    let e : Localization.Away (g * (f i)) ≃ₐ[S] (Localization.Away (algebraMap S (T i) g)) :=
      Localization.algEquiv _ _
    let : Algebra (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) :=
      RingHom.toAlgebra e.symm.toAlgHom
    have : IsScalarTower R (Localization.Away (algebraMap S (T i) g))
        (Localization.Away (g * f i)) := by
      refine .of_algebraMap_eq' ?_
      rw [RingHom.algebraMap_toAlgebra, ← RingHom.cancel_left (g := e.toRingHom) e.injective]
      ext
      simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        AlgEquiv.toAlgHom_eq_coe, AlgHomClass.toRingHom_toAlgHom, AlgEquiv.apply_symm_apply]
      simp [e]
      rw [IsScalarTower.algebraMap_apply R S, IsLocalization.map_eq, RingHomCompTriple.comp_apply,
        ← IsScalarTower.algebraMap_apply R S]
    have : IsStandardOpenImmersion
        (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) :=
      .of_bijective _ _ e.symm.bijective
    have : IsStandardOpenImmersion R (Localization.Away ((algebraMap S (T i)) g)) := by
      rw [← hg]
      have : IsLocalization.Away (g' * (algebraMap S (T i)) (f i) ^ n) (Localization.Away g') := by
        apply (config := { allowSynthFailures := true })
          IsLocalization.Away.mul' (Localization.Away g')
        apply IsLocalization.away_of_isUnit_of_bijective
        · exact IsUnit.map _ (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _))
        · exact Function.bijective_id
      let e' : Localization.Away (g' * (algebraMap S (T i) (f i)) ^ n) ≃ₐ[T i]
          Localization.Away g' := by
        exact Localization.algEquiv _ _
      apply IsStandardOpenImmersion.of_algEquiv _ _ _ (e'.symm.restrictScalars R)
    apply IsStandardOpenImmersion.trans _ (Localization.Away (algebraMap S (T i) g)) _

lemma pi_of_finite {ι : Type*} (R : Type*) (S : ι → Type*)
    [CommRing R] [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)] [Finite ι] [∀ i, IsLocalIso R (S i)] :
    IsLocalIso R (∀ i, S i)  := by
  classical
  let (i : ι) : Algebra (∀ i, S i) (S i) := (Pi.evalAlgHom R S i).toAlgebra
  have (i : ι) : IsLocalization.Away ((fun i ↦ Pi.single i (1 : S i)) i) ((fun i ↦ S i) i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [IsIdempotentElem, ← Pi.single_mul_left]
    · apply RingHom.ker_evalRingHom
    · apply (Pi.evalRingHom S i).surjective
  apply of_span_eq_top _ _ (fun i ↦ Pi.single i (1 : S i)) _ fun i ↦ S i
  apply Ideal.span_single_eq_top

instance refl : IsLocalIso R R :=
  instOfIsStandardOpenImmersion R R

end Algebra.IsLocalIso

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)"]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  let := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  dsimp [RingHom.IsLocalIso]
  let := f.toAlgebra
  have h : Function.Bijective (algebraMap R S) := by simpa [RingHom.algebraMap_toAlgebra] using hf
  have : Algebra.IsStandardOpenImmersion R S := Algebra.IsStandardOpenImmersion.of_bijective R S h
  infer_instance

lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  dsimp [RingHom.IsLocalIso] at hg hf ⊢
  algebraize [f, g, g.comp f]
  constructor
  intro q hq
  have hg' : Algebra.IsLocalIso S T := by simpa [RingHom.IsLocalIso] using hg
  have hf' : Algebra.IsLocalIso R S := by simpa [RingHom.IsLocalIso] using hf
  obtain ⟨t, htq, ht⟩ := hg'.exists_notMem_isStandardOpenImmersion q
  obtain ⟨s, hsq, hs⟩ := hf'.exists_notMem_isStandardOpenImmersion (Ideal.comap g q)
  have hgsq : g s ∉ q := by simpa [Ideal.mem_comap] using hsq
  refine ⟨t * g s, ?_, ?_⟩
  · exact Ideal.IsPrime.mul_notMem hq htq hgsq
  · -- Reduce to localizations of `S` using the `IsStandardOpenImmersion` data for `f` and `g`.
    rw [Algebra.isStandardOpenImmersion_iff] at ht
    obtain ⟨s₀, hs₀⟩ := ht
    -- First show `R → S_{s₀*s}` is a standard open immersion.
    have hRs₀ : Algebra.IsStandardOpenImmersion R
        (Localization.Away (algebraMap S (Localization.Away s) s₀)) :=
      Algebra.IsStandardOpenImmersion.trans R (Localization.Away s) _
    let e₁ : Localization.Away (s₀ * s) ≃ₐ[S] Localization.Away
        (algebraMap S (Localization.Away s) s₀) :=
      Localization.algEquiv _ _
    have hRss₀ : Algebra.IsStandardOpenImmersion R (Localization.Away (s₀ * s)) :=
       Algebra.IsStandardOpenImmersion.of_algEquiv R
        (Localization.Away (algebraMap S (Localization.Away s) s₀))
          (Localization.Away (s₀ * s)) (e₁.symm.restrictScalars R)
    let e₂ : Localization.Away (s₀ * s) ≃ₐ[S] Localization.Away
        (algebraMap S (Localization.Away t) s) :=
      Localization.algEquiv _ _
    have hR_Tt_s : Algebra.IsStandardOpenImmersion R
        (Localization.Away (algebraMap S (Localization.Away t) s)) :=
      Algebra.IsStandardOpenImmersion.of_algEquiv R (Localization.Away (s₀ * s))
        (Localization.Away (algebraMap S (Localization.Away t) s)) (e₂.restrictScalars R)
    have hsmap :
        algebraMap S (Localization.Away t) s = algebraMap T (Localization.Away t) (g s) := by
      simpa [RingHom.algebraMap_toAlgebra] using
        (IsScalarTower.algebraMap_apply S T (Localization.Away t) s)
    have hR_Tt_gs : Algebra.IsStandardOpenImmersion R
        (Localization.Away (algebraMap T (Localization.Away t) (g s))) := by
      simpa [hsmap] using hR_Tt_s
    let e₃ : Localization.Away (t * g s) ≃ₐ[T] Localization.Away
        (algebraMap T (Localization.Away t) (g s)) :=
      Localization.algEquiv _ _
    exact Algebra.IsStandardOpenImmersion.of_algEquiv R
      (Localization.Away (algebraMap T (Localization.Away t) (g s))) (Localization.Away (t * g s))
        (e₃.symm.restrictScalars R)

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
