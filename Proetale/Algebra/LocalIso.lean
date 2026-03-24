/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
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
  · have : IsLocalization.Away (g * (f i)) (Localization.Away (algebraMap S (T i) g)) := .mul (T i) _ _ _
    let e : Localization.Away (g * (f i)) ≃ₐ[S] (Localization.Away (algebraMap S (T i) g)) :=
      Localization.algEquiv _ _
    let : Algebra (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) :=
      RingHom.toAlgebra e.symm.toAlgHom
    have : IsScalarTower R (Localization.Away (algebraMap S (T i) g)) (Localization.Away (g * (f i))) := by
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
        apply +allowSynthFailures IsLocalization.Away.mul' (Localization.Away g')
        apply IsLocalization.away_of_isUnit_of_bijective
        · exact IsUnit.map _ (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _))
        · exact Function.bijective_id
      let e' : Localization.Away (g' * (algebraMap S (T i) (f i))^n) ≃ₐ[T i] Localization.Away g' := by
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

lemma trans {T : Type*} [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T := by
  constructor
  intro q hq
  obtain ⟨g₁, hg₁q, hstd_g⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := S) q
  let Tg := Localization.Away g₁
  obtain ⟨s₁, hs₁⟩ := Algebra.IsStandardOpenImmersion.exists_away S Tg
  set q_g := Ideal.map (algebraMap T Tg) q
  have : q_g.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g₁) Tg q hq
      ((Ideal.disjoint_powers_iff_notMem g₁ hq.isRadical).mpr hg₁q)
  set p := q_g.comap (algebraMap S Tg)
  have : p.IsPrime := Ideal.IsPrime.comap (algebraMap S Tg)
  obtain ⟨r₁, hr₁p, hstd_f⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) p
  obtain ⟨n, t, ht⟩ := IsLocalization.Away.surj g₁ (algebraMap S Tg r₁)
  refine ⟨t * g₁, ?_, ?_⟩
  · apply Ideal.IsPrime.mul_notMem hq
    · intro htq
      apply hr₁p
      rw [Ideal.mem_comap]
      have ht_mem : algebraMap T Tg t ∈ q_g := Ideal.mem_map_of_mem _ htq
      rw [← ht] at ht_mem
      rwa [Ideal.mul_unit_mem_iff_mem] at ht_mem
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    · exact hg₁q
  · have hmul : IsLocalization.Away (t * g₁) (Localization.Away (algebraMap T Tg t)) :=
      .mul Tg _ _ _
    have : Algebra.IsStandardOpenImmersion R (Localization.Away (algebraMap T Tg t)) := by
      rw [← ht]
      have hunit : IsUnit ((algebraMap T Tg g₁) ^ n) :=
        IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
      have : IsLocalization.Away
          ((algebraMap S Tg r₁) * (algebraMap T Tg g₁) ^ n)
          (Localization.Away (algebraMap S Tg r₁)) := by
        apply +allowSynthFailures IsLocalization.Away.mul'
          (Localization.Away (algebraMap S Tg r₁))
        apply IsLocalization.away_of_isUnit_of_bijective
        · exact IsUnit.map _ hunit
        · exact Function.bijective_id
      let Sr := Localization.Away r₁
      let Tgr := Localization.Away (algebraMap S Tg r₁)
      letI : Algebra Sr Tgr := (IsLocalization.Away.map Sr Tgr (algebraMap S Tg) r₁).toAlgebra
      have : IsScalarTower R Sr Tgr :=
        IsScalarTower.of_algebraMap_eq' (R := R) (S := Sr) (A := Tgr) (by
        ext x
        rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R S Sr,
            RingHom.algebraMap_toAlgebra, IsLocalization.Away.map, IsLocalization.map_eq,
            ← IsScalarTower.algebraMap_apply R S Tg, ← IsScalarTower.algebraMap_apply R Tg Tgr])
      have : IsScalarTower S Sr Tgr :=
        IsScalarTower.of_algebraMap_eq' (R := S) (S := Sr) (A := Tgr) (by
        ext a
        rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra, IsLocalization.Away.map,
            IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply S Tg Tgr])
      have : IsLocalization.Away (algebraMap S Sr s₁) Tgr :=
        IsLocalization.Away.commutes Sr Tg Tgr r₁ s₁
      have : Algebra.IsStandardOpenImmersion Sr Tgr := ⟨algebraMap S Sr s₁, inferInstance⟩
      have : Algebra.IsStandardOpenImmersion R Tgr :=
        Algebra.IsStandardOpenImmersion.trans R Sr Tgr
      exact .of_algEquiv _ _ _
        ((IsLocalization.algEquiv
          (Submonoid.powers ((algebraMap S Tg r₁) * (algebraMap T Tg g₁) ^ n)) _
          (Localization.Away (algebraMap S Tg r₁))).symm.restrictScalars R)
    exact .of_algEquiv _ _ _
      ((IsLocalization.algEquiv (Submonoid.powers (t * g₁)) _
        (Localization.Away (algebraMap T Tg t))).symm.restrictScalars R)

end Algebra.IsLocalIso

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)", algebraize]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective R S hf
  show Algebra.IsLocalIso R S
  infer_instance

lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
