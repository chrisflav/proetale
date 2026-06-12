/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Proetale.Algebra.IndZariski
import Proetale.Algebra.Etale
import Proetale.Mathlib.RingTheory.Etale.Field
import Proetale.Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Ind-étale algebras

In this file we define ind-étale algebras and ring homomorphisms.
-/

universe u

open CategoryTheory Limits TensorProduct

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The object property on commutative `R`-algebras of being étale. -/
def CommAlgCat.etale : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.Etale R S

lemma CommAlgCat.etale_eq : etale R = RingHom.toObjectProperty RingHom.Etale R := by
  ext S
  exact RingHom.etale_algebraMap.symm

instance : (MorphismProperty.ind.{u} CommRingCat.etale.{u}).IsStableUnderComposition :=
  .ind_of_le_isFinitelyPresentable CommRingCat.etale_le_isFinitelyPresentable.{u}

/-- An algebra is ind-étale if it can be written as the filtered colimit of étale
algebras. -/
@[mk_iff]
class Algebra.IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.Etale R (P.diag.obj i)

namespace Algebra.IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma iff_ind_etale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u} (CommAlgCat.etale R) (.of R S) :=
  Algebra.indEtale_iff R S

/-- Étale `R`-algebras are finitely presented. -/
lemma etale_le_finitePresentation :
    CommAlgCat.etale R ≤ CommAlgCat.finitePresentation R := by
  intro S hS
  exact (RingHom.etale_algebraMap.mpr hS).2

/-- If every stage of a filtered colimit presentation of `S` over `R` is ind-étale,
then `S` is ind-étale over `R`. -/
theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndEtale R (P.diag.obj i)) : Algebra.IndEtale R S := by
  rw [iff_ind_etale, ← ObjectProperty.ind_ind (etale_le_finitePresentation R |>.trans
    (CommAlgCat.finitePresentation_le_isFinitelyPresentable R))]
  exact ⟨ι, ‹_›, ‹_›, P, fun i => (iff_ind_etale R _).mp (h i)⟩

lemma isLocalIso_le_etale (R : Type u) [CommRing R] :
    CommAlgCat.isLocalIso R ≤ CommAlgCat.etale R := fun X hX ↦
  have : Algebra.IsLocalIso R X := hX
  Algebra.IsLocalIso.etale R X

/-- An ind-Zariski algebra is ind-étale, since localizations are étale. -/
instance (priority := 100) of_indZariski [IndZariski R S] : IndEtale R S := by
  rw [iff_ind_etale]
  refine ObjectProperty.ind_mono (isLocalIso_le_etale R) _ ?_
  rwa [← Algebra.IndZariski.iff_ind_isLocalIso]

/-- Let `A → B` be an ind-étale algebra and let `L` be a local ring that is also an algebra
over a field `k`, in a way compatible with the `A`-algebra structures. Then for every
`A`-algebra homomorphism `φ : B →ₐ[A] L` and every `b : B`, the image `φ b` is separable
over `k`. -/
lemma isSeparable_of_algHom_to_isLocalRing {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [IndEtale A B] (k L : Type u) [Field k] [CommRing L] [IsLocalRing L]
    [Algebra A k] [Algebra A L] [Algebra k L] [IsScalarTower A k L]
    (φ : B →ₐ[A] L) (b : B) : IsSeparable k (φ b) := by
  obtain ⟨ι, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := A) (S := B)
  letI : SmallCategory ι := hcat
  letI : IsFiltered ι := hfilt
  have hcolim : IsColimit ((forget (CommAlgCat.{u} A)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} A)) P.isColimit
  obtain ⟨i, bᵢ, hbᵢ⟩ := Types.jointly_surjective_of_isColimit hcolim b
  have : Algebra.Etale A (P.diag.obj i) := hP i
  let ψ : (k ⊗[A] P.diag.obj i) →ₐ[k] L :=
    Algebra.TensorProduct.lift (Algebra.ofId k L) (φ.comp (P.ι.app i).hom)
      (fun _ _ ↦ Commute.all _ _)
  have hψ : ψ ((1 : k) ⊗ₜ[A] bᵢ) = φ b := by
    simpa [ψ] using congrArg φ hbᵢ
  rw [← hψ]
  exact IsSeparable.of_algHom_etale_to_isLocalRing k _ L ψ _

instance isSeparable (k : Type u) [Field k] [Algebra k R] [IndEtale k R] [IsLocalRing R] :
    Algebra.IsSeparable k R :=
  ⟨fun x ↦ isSeparable_of_algHom_to_isLocalRing k R (AlgHom.id k R) x⟩

/-- If every element of `S` has separable image in `κ(q)` over a field `F`, then the residue
field `κ(q)` is separable over `F`. A general element of `κ(q)` is a ratio of images of two
elements of `S`, so the conclusion follows from `separableClosure` being closed under
division. -/
private lemma isSeparable_residueField_of_forall_isSeparable {F : Type u} [Field F]
    {T : Type u} [CommRing T] (q : Ideal T) [q.IsPrime] [Algebra F q.ResidueField]
    (key : ∀ s : T, IsSeparable F (algebraMap T q.ResidueField s)) :
    Algebra.IsSeparable F q.ResidueField := by
  refine ⟨fun y ↦ ?_⟩
  rw [← mem_separableClosure_iff (F := F) (E := q.ResidueField)]
  obtain ⟨x', m', -, hxm⟩ := IsFractionRing.div_surjective (A := T ⧸ q) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m'
  rw [← hxm, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  exact div_mem (mem_separableClosure_iff.mpr (key x))
    (mem_separableClosure_iff.mpr (key m))

/-- An ind-étale ring extension `R → S` induces a separable extension `κ(p) → κ(q)` on
residue fields, for any pair of primes `q ∈ Spec S` lying over `p ∈ Spec R`. -/
instance isSeparable_residueField [IndEtale R S] (p : Ideal R) (q : Ideal S)
    [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField :=
  -- Every image in `q.ResidueField` of an element of `S` factors through a finite étale
  -- `p.ResidueField`-subalgebra, hence is separable over `p.ResidueField`.
  isSeparable_residueField_of_forall_isSeparable q fun s ↦
    isSeparable_of_algHom_to_isLocalRing p.ResidueField q.ResidueField
      (IsScalarTower.toAlgHom R S q.ResidueField) s

/-- If `B` is an ind-étale algebra over a field `K`, then the residue field of any prime of
`B` is separable over `K`. -/
theorem isSeparable_residueField_of_field {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [IndEtale K B] (q : Ideal B) [q.IsPrime] :
    Algebra.IsSeparable K q.ResidueField :=
  isSeparable_residueField_of_forall_isSeparable q fun s ↦
    isSeparable_of_algHom_to_isLocalRing K q.ResidueField
      (IsScalarTower.toAlgHom K B q.ResidueField) s

/-- An étale algebra over a field with two distinct primes `p₁ ≠ p₂` contains an idempotent
separating `p₁` from `p₂`. -/
private lemma exists_isIdempotentElem_mem_of_ne {K C : Type u} [Field K] [CommRing C]
    [Algebra K C] [Algebra.Etale K C] {p₁ p₂ : Ideal C} [p₁.IsPrime] [p₂.IsPrime]
    (h : p₁ ≠ p₂) :
    ∃ e : C, IsIdempotentElem e ∧ e ∈ p₁ ∧ 1 - e ∈ p₂ := by
  classical
  obtain ⟨I, hfin, Ai, hfield, halg, eqv, -⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := C)).mp inferInstance
  have : Finite I := hfin
  let _ : ∀ i, Field (Ai i) := hfield
  let _ : ∀ i, Algebra K (Ai i) := halg
  let f : (∀ i, Ai i) →ₐ[K] C := eqv.symm.toAlgHom
  have hfx : ∀ x : C, f (eqv x) = x := fun x ↦ eqv.symm_apply_apply x
  obtain ⟨j₁, hj₁⟩ := Ideal.exists_eq_ker_evalRingHom (p₁.comap f)
  obtain ⟨j₂, hj₂⟩ := Ideal.exists_eq_ker_evalRingHom (p₂.comap f)
  have hj : j₁ ≠ j₂ := by
    rintro rfl
    refine h (SetLike.ext fun x ↦ ?_)
    have h₁ : x ∈ p₁ ↔ eqv x ∈ p₁.comap f := by rw [Ideal.mem_comap, hfx]
    have h₂ : x ∈ p₂ ↔ eqv x ∈ p₂.comap f := by rw [Ideal.mem_comap, hfx]
    rw [h₁, h₂, hj₁, hj₂]
  have hidem : IsIdempotentElem (Pi.single j₁ (1 : Ai j₁)) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  refine ⟨f ((1 : ∀ i, Ai i) - Pi.single j₁ 1), hidem.one_sub.map f, ?_, ?_⟩
  · have hz : ((1 : ∀ i, Ai i) - Pi.single j₁ 1) ∈ p₁.comap f := by
      rw [hj₁, RingHom.mem_ker]
      simp
    exact Ideal.mem_comap.mp hz
  · have h1f : (1 : C) - f ((1 : ∀ i, Ai i) - Pi.single j₁ 1) = f (Pi.single j₁ 1) := by
      rw [map_sub, map_one, sub_sub_cancel]
    rw [h1f]
    have hz : (Pi.single j₁ (1 : Ai j₁) : ∀ i, Ai i) ∈ p₂.comap f := by
      rw [hj₂, RingHom.mem_ker, Pi.evalRingHom_apply]
      exact Pi.single_eq_of_ne (Ne.symm hj) 1
    exact Ideal.mem_comap.mp hz

/-- If `B` is an ind-étale algebra over a field `K` and `B` has at least two distinct prime
ideals, then `B` has a nontrivial idempotent element. -/
theorem exists_isIdempotentElem_of_two_primes {K B : Type u} [Field K] [CommRing B]
    [Algebra K B] [Algebra.IndEtale K B] {q₁ q₂ : Ideal B} [q₁.IsPrime] [q₂.IsPrime]
    (h : q₁ ≠ q₂) :
    ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  -- Pick an element distinguishing `q₁` from `q₂`.
  obtain ⟨x, hx⟩ : ∃ x : B, ¬ (x ∈ q₁ ↔ x ∈ q₂) :=
    not_forall.mp fun hc ↦ h (SetLike.ext hc)
  -- Lift `x` to a stage of a filtered colimit presentation by étale algebras.
  obtain ⟨ι, _, _, P, hP⟩ := exists_colimitPresentation (R := K) (S := B)
  have hc' := isColimitOfPreserves (forget (CommAlgCat K)) P.isColimit
  obtain ⟨i, x₀, hx'⟩ := Types.jointly_surjective_of_isColimit hc' x
  let φ : P.diag.obj i →ₐ[K] B := (P.ι.app i).hom
  replace hx' : φ x₀ = x := by simpa using hx'
  have : Algebra.Etale K (P.diag.obj i) := hP i
  -- The contractions of `q₁` and `q₂` to the étale stage are distinct primes.
  have hne : q₁.comap φ ≠ q₂.comap φ := fun he ↦
    hx (by rw [← hx', ← Ideal.mem_comap, ← Ideal.mem_comap, he])
  obtain ⟨e', he', hm₁, hm₂⟩ := exists_isIdempotentElem_mem_of_ne (K := K) hne
  refine ⟨φ e', he'.map φ, ?_, ?_⟩
  · intro h0
    have h1 : (1 : B) - φ e' ∈ q₂ := by
      have hm : φ (1 - e') ∈ q₂ := Ideal.mem_comap.mp hm₂
      rwa [map_sub, map_one] at hm
    rw [h0, sub_zero] at h1
    exact (Ideal.ne_top_iff_one q₂).mp ‹q₂.IsPrime›.ne_top h1
  · intro h1
    have h2 : φ e' ∈ q₁ := Ideal.mem_comap.mp hm₁
    rw [h1] at h2
    exact (Ideal.ne_top_iff_one q₁).mp ‹q₁.IsPrime›.ne_top h2

end Algebra.IndEtale

/-- A ring hom is ind-étale if and only if it is an ind-étale algebra. -/
@[algebraize Algebra.IndEtale]
def RingHom.IndEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndEtale R S

namespace RingHom.IndEtale

variable (S) in
lemma algebraMap_iff : (algebraMap R S).IndEtale ↔ Algebra.IndEtale R S :=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

lemma iff_ind_etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u} CommRingCat.etale (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndEtale, Algebra.IndEtale.iff_ind_etale, ← f.algebraMap_toAlgebra,
    CommRingCat.etale, RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.etale_eq]

/-- A ring hom is ind-étale if and only if it can be written as a colimit of étale ring homs. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndEtale ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S) (_ : IsColimit (.mk _ c)),
      ∀ i, (t.app i).hom.Etale ∧ t.app i ≫ c.app i = f :=
  RingHom.IndEtale.iff_ind_etale _

variable {R S : Type u} [CommRing R] [CommRing S]

lemma comp {T : Type u} [CommRing T] {g : S →+* T} {f : R →+* S} (hg : g.IndEtale)
    (hf : f.IndEtale) : (g.comp f).IndEtale := by
  rw [iff_ind_etale] at hf hg ⊢
  rw [CommRingCat.ofHom_comp]
  exact (MorphismProperty.ind.{u} CommRingCat.etale).comp_mem _ _ hf hg

/-- Ind-étale ring homomorphisms are stable under base change. -/
lemma isStableUnderBaseChange : IsStableUnderBaseChange IndEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush hRS
  rw [iff_ind_etale] at hRS ⊢
  rw [← CommRingCat.isPushout_iff_isPushout] at hpush
  exact (inferInstance : (MorphismProperty.ind CommRingCat.etale).IsStableUnderCobaseChange).1
    hpush.flip hRS

/-- Ind-étale is equivalent to ind-ind-étale. -/
lemma iff_ind_indEtale (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndEtale) (CommRingCat.ofHom f) := by
  rw [iff_ind_etale]
  have heq : RingHom.toMorphismProperty RingHom.IndEtale =
      MorphismProperty.ind.{u} CommRingCat.etale := by
    ext X Y g
    exact iff_ind_etale g.hom
  rw [heq, MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable.{u}]

/-- A ring hom is ind-étale if it can be written as a filtered colimit of ind-étale maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndEtale ∧ t.app i ≫ c.app i = f) : f.hom.IndEtale :=
  (iff_ind_indEtale _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

/-- Ind-étale algebras are equivalent to ind-ind-étale algebras. -/
theorem _root_.Algebra.IndEtale.iff_ind_indEtale [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndEtale R) (.of R S) :=
  have h := isStableUnderBaseChange.localizationPreserves.away.respectsIso
  (algebraMap_iff (R := R) S).symm.trans
    ((RingHom.IndEtale.iff_ind_indEtale _).trans
      h.ind_toMorphismProperty_iff_ind_toObjectProperty)

lemma _root_.RingHom.IndZariski.indEtale {f : R →+* S}
    (hf : f.IndZariski) : f.IndEtale := by
  algebraize [f]
  exact .of_indZariski R S

end RingHom.IndEtale

namespace Algebra.IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T := by
  rw [← RingHom.IndEtale.algebraMap_iff R T, IsScalarTower.algebraMap_eq R S T]
  exact RingHom.IndEtale.comp
    ((RingHom.IndEtale.algebraMap_iff S T).mpr ‹_›)
    ((RingHom.IndEtale.algebraMap_iff R S).mpr ‹_›)

/-- If `B` is an ind-étale algebra over a field `K` and `q` is a prime ideal of `B` whose
residue field is strictly larger than `K`, then the tensor product
`κ(q) ⊗[K] B` has a nontrivial idempotent element. -/
theorem exists_isIdempotentElem_tensorProduct_of_residueField_ne {K B : Type u}
    [Field K] [CommRing B] [Algebra K B] [Algebra.IndEtale K B]
    (q : Ideal B) [q.IsPrime]
    (h : ¬ Function.Bijective (algebraMap K q.ResidueField)) :
    ∃ e : q.ResidueField ⊗[K] B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  have : Algebra.IsSeparable K q.ResidueField := isSeparable_residueField_of_field q
  -- `κ(q) ⊗[K] B` is ind-étale over `κ(q)` by base change.
  have : Algebra.IndEtale q.ResidueField (q.ResidueField ⊗[K] B) := by
    have hbc := RingHom.IsStableUnderBaseChange.tensorProduct
      RingHom.IndEtale.isStableUnderBaseChange (R := K) (S := B) q.ResidueField
      ((RingHom.IndEtale.algebraMap_iff (R := K) (S := B)).mpr inferInstance)
    exact (RingHom.IndEtale.algebraMap_iff (R := q.ResidueField)
      (S := q.ResidueField ⊗[K] B)).mp hbc
  -- By `exists_isIdempotentElem_of_two_primes` it suffices to exhibit two distinct primes.
  suffices hp : ∃ P₁ P₂ : Ideal (q.ResidueField ⊗[K] B),
      P₁.IsPrime ∧ P₂.IsPrime ∧ P₁ ≠ P₂ by
    obtain ⟨P₁, P₂, hP₁, hP₂, hPne⟩ := hp
    have := hP₁
    have := hP₂
    exact exists_isIdempotentElem_of_two_primes (K := q.ResidueField) hPne
  -- An element `y` of the residue field not in the image of `K`.
  obtain ⟨y, hy⟩ : ∃ y : q.ResidueField, y ∉ (algebraMap K q.ResidueField).range :=
    not_forall.mp fun hc ↦ h ⟨(algebraMap K q.ResidueField).injective,
      fun y ↦ RingHom.mem_range.mp (hc y)⟩
  have hyint : IsIntegral K y := (Algebra.IsSeparable.isSeparable K y).isIntegral
  -- The minimal polynomial of `y` has a second root `y'` in the algebraic closure.
  have hcard : 1 < Fintype.card
      ((minpoly K y).rootSet (AlgebraicClosure q.ResidueField)) := by
    rw [Polynomial.card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable K y)
      (IsAlgClosed.splits _)]
    exact lt_of_lt_of_le one_lt_two ((minpoly.two_le_natDegree_iff hyint).mpr hy)
  have hy₀mem : algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y ∈
      (minpoly K y).rootSet (AlgebraicClosure q.ResidueField) := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hyint,
      by rw [Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]⟩
  obtain ⟨⟨y', hy'mem⟩, hne'⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨_, hy₀mem⟩
  have hyne : y' ≠ algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y :=
    fun hh ↦ hne' (Subtype.ext hh)
  -- A second embedding `σ : κ(q) →ₐ[K] Ω` with `σ y = y'`.
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun s : q.ResidueField ↦
      ⟨(Algebra.IsSeparable.isSeparable K s).isIntegral, IsAlgClosed.splits _⟩)
    ((Polynomial.mem_rootSet.mp hy'mem).2)
  -- Write `y` as a fraction of images of elements of `B`.
  obtain ⟨x', m', hm', hxm⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective x'
  obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective m'
  have hb₂ : algebraMap B q.ResidueField b₂ ≠ 0 := by
    have hb := map_ne_zero_of_mem_nonZeroDivisors (algebraMap (B ⧸ q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField hm'
    rwa [Ideal.algebraMap_quotient_residueField_mk] at hb
  rw [Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk] at hxm
  have hyb : algebraMap B q.ResidueField b₁ = y * algebraMap B q.ResidueField b₂ :=
    (div_eq_iff hb₂).mp hxm
  -- The two maps to the algebraic closure, differing only on the left tensor factor.
  let ψ : B →ₐ[K] AlgebraicClosure q.ResidueField :=
    (IsScalarTower.toAlgHom K q.ResidueField (AlgebraicClosure q.ResidueField)).comp
      (IsScalarTower.toAlgHom K B q.ResidueField)
  let Φ₁ : q.ResidueField ⊗[K] B →ₐ[K] AlgebraicClosure q.ResidueField :=
    Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom K q.ResidueField (AlgebraicClosure q.ResidueField)) ψ
  let Φ₂ : q.ResidueField ⊗[K] B →ₐ[K] AlgebraicClosure q.ResidueField :=
    Algebra.TensorProduct.productMap σ ψ
  have hΦ₁tmul (l : q.ResidueField) (b : B) : Φ₁ (l ⊗ₜ[K] b) =
      algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) l *
      algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
        (algebraMap B q.ResidueField b) := by
    simp only [Φ₁, ψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
  have hΦ₂tmul (l : q.ResidueField) (b : B) : Φ₂ (l ⊗ₜ[K] b) =
      σ l * algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
        (algebraMap B q.ResidueField b) := by
    simp only [Φ₂, ψ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']
  -- The element `y ⊗ b₂ - 1 ⊗ b₁` lies in `ker Φ₁` but not in `ker Φ₂`.
  have hw₁ : Φ₁ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) = 0 := by
    rw [map_sub, hΦ₁tmul y b₂, hΦ₁tmul 1 b₁, map_one, one_mul, ← map_mul, ← hyb,
      sub_self]
  have hβ₂Ω : algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
      (algebraMap B q.ResidueField b₂) ≠ 0 := fun h0 ↦
    hb₂ (RingHom.injective (algebraMap q.ResidueField (AlgebraicClosure q.ResidueField))
      (by rw [h0, map_zero]))
  have hw₂ : Φ₂ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) ≠ 0 := by
    have hcalc : Φ₂ (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁) =
        (σ y - algebraMap q.ResidueField (AlgebraicClosure q.ResidueField) y) *
        algebraMap q.ResidueField (AlgebraicClosure q.ResidueField)
          (algebraMap B q.ResidueField b₂) := by
      rw [map_sub, hΦ₂tmul y b₂, hΦ₂tmul 1 b₁, map_one, one_mul, hyb, map_mul, sub_mul]
    rw [hcalc]
    exact mul_ne_zero (sub_ne_zero_of_ne (by rwa [hσ])) hβ₂Ω
  refine ⟨RingHom.ker Φ₁, RingHom.ker Φ₂, RingHom.ker_isPrime _, RingHom.ker_isPrime _, ?_⟩
  intro hk
  apply hw₂
  have hmem : (y ⊗ₜ[K] b₂ - 1 ⊗ₜ[K] b₁ : q.ResidueField ⊗[K] B) ∈ RingHom.ker Φ₁ :=
    RingHom.mem_ker.mpr hw₁
  rw [hk] at hmem
  exact RingHom.mem_ker.mp hmem

end Algebra.IndEtale
