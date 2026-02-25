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
        apply (config := { allowSynthFailures := true }) IsLocalization.Away.mul' (Localization.Away g')
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

lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  letI : Algebra R S := f.toAlgebra
  have hbij : Function.Bijective (algebraMap R S) := hf
  have : Algebra.IsStandardOpenImmersion R S := by
    rw [Algebra.isStandardOpenImmersion_iff]
    exact ⟨1, IsLocalization.away_of_isUnit_of_bijective _ isUnit_one hbij⟩
  exact Algebra.IsLocalIso.instOfIsStandardOpenImmersion R S

lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := .of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.IsLocalIso R S := hf
  haveI : Algebra.IsLocalIso S T := hg
  show Algebra.IsLocalIso R T
  constructor
  intro q hq
  -- Step 1: By IsLocalIso S T, get g₁ ∉ q with IsStandardOpenImmersion S (Localization.Away g₁)
  obtain ⟨g₁, hg₁q, hstd_g⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := S) q
  obtain ⟨s₁, hs₁⟩ := Algebra.IsStandardOpenImmersion.exists_away S (Localization.Away g₁)
  set Tg := Localization.Away g₁
  have hq_disj : Disjoint (Submonoid.powers g₁ : Set T) (↑q : Set T) :=
    (Ideal.disjoint_powers_iff_notMem g₁ hq.isRadical).mpr hg₁q
  set q_g := Ideal.map (algebraMap T Tg) q
  haveI : q_g.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g₁) Tg q hq hq_disj
  have hcomap_qg : q_g.comap (algebraMap T Tg) = q :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g₁) Tg hq hq_disj
  -- p is the prime of S corresponding to q_g via S → Tg
  set p := q_g.comap (algebraMap S Tg)
  haveI : p.IsPrime := Ideal.IsPrime.comap (algebraMap S Tg)
  -- Step 2: By IsLocalIso R S, get r₁ ∉ p with IsStandardOpenImmersion R (Localization.Away r₁)
  obtain ⟨r₁, hr₁p, hstd_f⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) p
  -- Step 3: Use surj for T → Tg to lift algebraMap S Tg r₁ to T
  obtain ⟨n, t, ht⟩ := IsLocalization.Away.surj g₁ (algebraMap S Tg r₁)
  -- ht : (algebraMap S Tg r₁) * (algebraMap T Tg g₁)^n = algebraMap T Tg t
  -- Step 4: The element t * g₁ : T is not in q
  use t * g₁
  constructor
  · -- Need t * g₁ ∉ q. Since q is prime, suffices t ∉ q and g₁ ∉ q.
    -- g₁ ∉ q is given. For t ∉ q: if t ∈ q then algebraMap T Tg t ∈ q_g,
    -- so (algebraMap S Tg r₁) * (algebraMap T Tg g₁)^n ∈ q_g, but g₁^n maps to a unit
    -- in Tg (so its image is not in any prime), contradiction unless algebraMap S Tg r₁ ∈ q_g,
    -- which would mean r₁ ∈ p, contradicting hr₁p.
    apply Ideal.IsPrime.mul_notMem hq
    · -- t ∉ q
      intro htq
      apply hr₁p
      show r₁ ∈ q_g.comap (algebraMap S Tg)
      rw [Ideal.mem_comap]
      -- algebraMap S Tg r₁ ∈ q_g
      -- From ht: (algebraMap S Tg r₁) * (algebraMap T Tg g₁)^n = algebraMap T Tg t
      -- algebraMap T Tg t ∈ q_g since t ∈ q
      have ht_mem : algebraMap T Tg t ∈ q_g := Ideal.mem_map_of_mem _ htq
      rw [← ht] at ht_mem
      -- (algebraMap S Tg r₁) * (algebraMap T Tg g₁)^n ∈ q_g
      -- (algebraMap T Tg g₁)^n is a unit in Tg
      rwa [Ideal.mul_unit_mem_iff_mem] at ht_mem
      exact IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
    · exact hg₁q
  · -- Step 5: Algebra.IsStandardOpenImmersion R (Localization.Away (t * g₁))
    -- Following of_span_eq_top pattern lines 59-87
    -- Localization.Away (t * g₁) ≅ Localization.Away (algebraMap T Tg t) as T-algebras
    -- via IsLocalization.Away.mul
    have hmul : IsLocalization.Away (t * g₁) (Localization.Away (algebraMap T Tg t)) :=
      .mul Tg _ _ _
    let e : Localization.Away (t * g₁) ≃ₐ[T] (Localization.Away (algebraMap T Tg t)) :=
      Localization.algEquiv _ _
    letI instAlg : Algebra (Localization.Away (algebraMap T Tg t)) (Localization.Away (t * g₁)) :=
      RingHom.toAlgebra (e.symm : Localization.Away (algebraMap T Tg t) →+* Localization.Away (t * g₁))
    haveI : IsScalarTower R (Localization.Away (algebraMap T Tg t)) (Localization.Away (t * g₁)) :=
      IsScalarTower.of_algebraMap_eq' (A := Localization.Away (t * g₁))
        (S := Localization.Away (algebraMap T Tg t)) (R := R) (by
      rw [show (algebraMap (Localization.Away (algebraMap T Tg t)) (Localization.Away (t * g₁)))
        = (e.symm : Localization.Away (algebraMap T Tg t) →+* Localization.Away (t * g₁))
        from RingHom.algebraMap_toAlgebra _]
      ext (x : R)
      -- target: algebraMap R (Loc(t*g₁)) x = e.symm (algebraMap R (Loc(algMap T Tg t)) x)
      change algebraMap R (Localization.Away (t * g₁)) x =
        e.symm (algebraMap R (Localization.Away (algebraMap T Tg t)) x)
      rw [IsScalarTower.algebraMap_apply R T (Localization.Away (algebraMap T Tg t)),
        AlgEquiv.commutes, IsScalarTower.algebraMap_apply R T (Localization.Away (t * g₁))])
    have : Algebra.IsStandardOpenImmersion
        (Localization.Away (algebraMap T Tg t)) (Localization.Away (t * g₁)) :=
      .of_bijective _ _ e.symm.bijective
    -- Now show Algebra.IsStandardOpenImmersion R (Localization.Away (algebraMap T Tg t))
    have : Algebra.IsStandardOpenImmersion R (Localization.Away (algebraMap T Tg t)) := by
      rw [← ht]
      have hunit : IsUnit ((algebraMap T Tg g₁) ^ n) :=
        IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit _)
      have : IsLocalization.Away
          ((algebraMap S Tg r₁) * (algebraMap T Tg g₁) ^ n)
          (Localization.Away (algebraMap S Tg r₁)) := by
        apply (config := { allowSynthFailures := true }) IsLocalization.Away.mul'
          (Localization.Away (algebraMap S Tg r₁))
        apply IsLocalization.away_of_isUnit_of_bijective
        · exact IsUnit.map _ hunit
        · exact Function.bijective_id
      let e' : Localization.Away ((algebraMap S Tg r₁) * (algebraMap T Tg g₁) ^ n) ≃ₐ[Tg]
          Localization.Away (algebraMap S Tg r₁) :=
        Localization.algEquiv _ _
      -- First establish IsStdOpenImm R (Loc.Away(algebraMap S Tg r₁))
      -- via trans: R → Loc.Away r₁ → Loc.Away(algebraMap S Tg r₁)
      -- Step A: Build Algebra (Loc.Away r₁) (Loc.Away(algebraMap S Tg r₁))
      -- using IsLocalization.Away.map
      set Sr := Localization.Away r₁  -- S-localization at r₁
      set Tgr := Localization.Away (algebraMap S Tg r₁)  -- Tg-localization
      let φ : Sr →+* Tgr := IsLocalization.Away.map Sr Tgr (algebraMap S Tg) r₁
      letI : Algebra Sr Tgr := φ.toAlgebra
      -- Step B: Build IsScalarTower R Sr Tgr
      have hST_R : IsScalarTower R Sr Tgr :=
        IsScalarTower.of_algebraMap_eq' (R := R) (S := Sr) (A := Tgr) (by
        ext x
        simp only [RingHom.comp_apply]
        -- Need: algebraMap R Tgr x = φ (algebraMap R Sr x)
        -- algebraMap R Sr x = algebraMap S Sr (algebraMap R S x) by IsScalarTower
        -- φ (algebraMap S Sr (algebraMap R S x)) = algebraMap S Tgr (algebraMap R S x)
        --   by definition of φ = IsLocalization.map
        -- algebraMap S Tgr (algebraMap R S x) = algebraMap R Tgr x
        --   by IsScalarTower R S Tg → Tgr
        change algebraMap R Tgr x = φ (algebraMap R Sr x)
        rw [IsScalarTower.algebraMap_apply R S Sr]
        show algebraMap R Tgr x =
          IsLocalization.Away.map Sr Tgr (algebraMap S Tg) r₁
            (algebraMap S Sr (algebraMap R S x))
        rw [IsLocalization.Away.map, IsLocalization.map_eq]
        -- Goal: algebraMap R Tgr x = algebraMap Tg Tgr (algebraMap S Tg (algebraMap R S x))
        rw [← IsScalarTower.algebraMap_apply R S Tg]
        -- Goal: algebraMap R Tgr x = algebraMap Tg Tgr (algebraMap R Tg x)
        rw [← IsScalarTower.algebraMap_apply R Tg Tgr])
      -- Step C: IsStdOpenImm (Loc.Away r₁) (Loc.Away(algebraMap S Tg r₁))
      -- Use IsLocalization.Away.commutes:
      -- S₁ = Sr, S₂ = Tg, T = Tgr, x = r₁, y = s₁
      -- Need IsScalarTower S Sr Tgr
      haveI : IsScalarTower S Sr Tgr :=
        IsScalarTower.of_algebraMap_eq' (R := S) (S := Sr) (A := Tgr) (by
        ext a
        simp only [RingHom.comp_apply]
        change algebraMap S Tgr a = φ (algebraMap S Sr a)
        show algebraMap S Tgr a =
          IsLocalization.Away.map Sr Tgr (algebraMap S Tg) r₁ (algebraMap S Sr a)
        rw [IsLocalization.Away.map, IsLocalization.map_eq,
          IsScalarTower.algebraMap_apply S Tg Tgr])
      haveI : IsLocalization.Away (algebraMap S Sr s₁) Tgr :=
        IsLocalization.Away.commutes Sr Tg Tgr r₁ s₁
      haveI : Algebra.IsStandardOpenImmersion Sr Tgr := ⟨algebraMap S Sr s₁, inferInstance⟩
      haveI : Algebra.IsStandardOpenImmersion R Tgr :=
        Algebra.IsStandardOpenImmersion.trans R Sr Tgr
      apply Algebra.IsStandardOpenImmersion.of_algEquiv _ _ _ (e'.symm.restrictScalars R)
    exact Algebra.IsStandardOpenImmersion.trans _ (Localization.Away (algebraMap T Tg t)) _

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
