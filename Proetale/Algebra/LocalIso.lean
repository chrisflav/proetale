/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
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

instance isScalarTower_localizationAlgebra {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*)
    [CommSemiring S] [Algebra R S] {Rₘ : Type*} {Sₘ : Type*} [CommSemiring Rₘ] [CommSemiring Sₘ]
    [Algebra R Rₘ] [IsLocalization M Rₘ] [Algebra S Sₘ]
    [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] :
    letI : Algebra Rₘ Sₘ := localizationAlgebra M S
    IsScalarTower R Rₘ Sₘ :=
  letI : Algebra Rₘ Sₘ := localizationAlgebra M S
  .of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R S Sₘ]

open TensorProduct

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

variable {R S} in
-- TODO: cleanup proof after bumping
lemma of_span_range_eq_top {ι : Type*} (f : ι → S) (h : Ideal.span (Set.range f) = ⊤)
    (T : ι → Type*) [∀ i, CommSemiring (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra S (T i)]
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
      simp only [RingEquiv.toRingHom_eq_coe,
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

lemma of_span_eq_top {s : Set S} (h : Ideal.span s = ⊤)
    (h : ∀ x ∈ s, IsLocalIso R (Localization.Away x)) : IsLocalIso R S := by
  have heq : Ideal.span (Set.range fun i : s ↦ i.1) = ⊤ := by simpa
  have (i : s) : IsLocalIso R (Localization.Away i.1) := h _ i.property
  refine .of_span_range_eq_top _ heq fun i ↦ Localization.Away i.1

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
  apply of_span_range_eq_top (fun i ↦ Pi.single i (1 : S i)) _ fun i ↦ S i
  apply Ideal.span_single_eq_top

instance refl : IsLocalIso R R := inferInstance

lemma span_isStandardOpenImmersion_eq_top [Algebra.IsLocalIso R S] :
    Ideal.span {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hgm, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) m
  exact hgm (hms (Ideal.subset_span hstd))

lemma iff_span_isStandardOpenImmersion_eq_top :
    IsLocalIso R S ↔
      Ideal.span {g : S | IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  refine ⟨fun _ ↦ span_isStandardOpenImmersion_eq_top R S, fun h ↦ ⟨fun q hq ↦ ?_⟩⟩
  by_contra!
  apply hq.ne_top
  rw [_root_.eq_top_iff, ← h, Ideal.span_le]
  grind [SetLike.mem_coe]

/-- Local isomorphisms are stable under composition. -/
lemma trans (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T := by
  -- The proof is purely formal given that open immersions are stable under composition.
  let s : Set S := {g : S | IsStandardOpenImmersion R (Localization.Away g)}
  let T' (g : S) := Localization.Away (algebraMap S T g)
  let (g : S) : Algebra (Localization.Away g) (T' g) := localizationAlgebra (.powers g) T
  let T'' (g : S) (x : T) := Localization.Away (algebraMap _ (T' g) x)
  let t (g : S) : Set T := {x : T | IsStandardOpenImmersion (Localization.Away g) (T'' g x)}
  let ι : Type _ := Σ i : s, t i.1
  have (i : ι) : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1 i.2) := i.2.2
  suffices h : Ideal.span (Set.range fun i : ι ↦ algebraMap S T i.1 * i.2) = ⊤ by
    have (i : ι) : IsStandardOpenImmersion R (T'' i.1 i.2) :=
      have : IsScalarTower R (Localization.Away i.1.1) (T' i.1.1) :=
        IsScalarTower.to₁₃₄ _ S _ _
      have : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1.1 i.2.1) := i.2.2
      have : IsStandardOpenImmersion R (Localization.Away i.1.1) := i.1.2
      .trans _ (Localization.Away i.1.1) _
    exact .of_span_range_eq_top _ h fun i : ι ↦ T'' i.1 i.2
  have h1 := congr(Ideal.map (algebraMap S T) $(span_isStandardOpenImmersion_eq_top R S))
  rw [Ideal.map_top, Ideal.map_span] at h1
  nth_rw 1 [_root_.eq_top_iff, ← Ideal.top_mul ⊤, ← h1, ← span_isStandardOpenImmersion_eq_top S T,
    Ideal.span_mul_span, Ideal.span_le, Set.mul_subset_iff]
  simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro g hg x hx
  refine Ideal.subset_span ⟨⟨⟨g, hg⟩, ⟨x, ?_⟩⟩, rfl⟩
  simp only [Set.mem_setOf_eq, t]
  let : Algebra (Localization.Away x) (T'' g x) :=
    localizationAlgebra (.powers x) (T' g)
  have : IsScalarTower S (Localization.Away x) (T'' g x) :=
    IsScalarTower.to₁₃₄ _ T _ _
  have : IsLocalization (algebraMapSubmonoid (Localization.Away x) (.powers g)) (T'' g x) := by
    have : algebraMapSubmonoid (Localization.Away x) (.powers g) =
      algebraMapSubmonoid (Localization.Away x) (.powers (algebraMap S T g)) := by
        simp [IsScalarTower.algebraMap_apply S T (Localization.Away x)]
    rw [this]
    exact .commutes _ (T' g) _ (.powers x) (.powers (algebraMap S T g))
  have : IsPushout S (Localization.Away x) (Localization.Away g) (T'' g x) :=
    Algebra.isPushout_of_isLocalization (.powers g) _ _ _
  exact .of_isPushout S (Localization.Away x) _ _

end Algebra.IsLocalIso

section Flat

universe v w

/-- A standard open immersion is flat, since it is a localization. -/
lemma Module.Flat.of_isStandardOpenImmersion
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardOpenImmersion R S] : Module.Flat R S := by
  obtain ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R S
  exact IsLocalization.flat S (Submonoid.powers r)

/-- A local isomorphism is flat, since it is locally a localization. -/
lemma Algebra.IsLocalIso.flat
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] : Module.Flat R S := by
  refine Module.flat_of_isLocalized_span S S
    {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top _ _)
    (fun g ↦ Localization.Away g.1)
    (fun g ↦ Algebra.linearMap S (Localization.Away g.1)) fun ⟨g, hg⟩ ↦ by
      letI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
      exact Module.Flat.of_isStandardOpenImmersion R (Localization.Away g)

end Flat

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

/-- A bijective ring homomorphism is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective R S hf
  show Algebra.IsLocalIso R S
  infer_instance

/-- The composition of local isomorphisms is a local isomorphism. -/
lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso
