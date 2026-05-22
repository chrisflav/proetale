/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Proetale.Algebra.IndZariski
import Proetale.Algebra.Etale

/-!
# Ind-étale algebras

In this file we define ind-étale algebras and ring homomorphisms.
-/

universe u

open CategoryTheory Limits

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The object property on commutative `R`-algebras of being étale. -/
def CommAlgCat.etale : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.Etale R S

lemma CommAlgCat.etale_eq : etale R = RingHom.toObjectProperty RingHom.Etale R := by
  ext S
  exact RingHom.etale_algebraMap.symm

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

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T :=
  sorry

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

/-- In a local ring, every idempotent element is `0` or `1`. -/
private lemma _root_.IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hsum : e + (1 - e) = 1 := by ring
  have hmul : e * (1 - e) = 0 := by
    have : e * (1 - e) = e - e * e := by ring
    rw [this, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with hu | hu
  · exact .inr (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hmul)).symm
  · exact .inl (hu.mul_right_eq_zero.mp (by rw [mul_comm]; exact hmul))

/-- An algebra homomorphism from a finite product of fields to a nontrivial local ring
factors through one of the factors. -/
private lemma exists_unique_index_of_algHom_pi_to_local
    {k : Type u} [Field k] {I : Type*} [Finite I] [DecidableEq I]
    {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra k (Ai i)]
    {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B] [Nontrivial B]
    (ψ : (∀ i, Ai i) →ₐ[k] B) :
    ∃ j : I, ψ (Pi.single j 1) = 1 ∧ ∀ i, i ≠ j → ψ (Pi.single i 1) = 0 := by
  haveI : Fintype I := Fintype.ofFinite I
  have hcoi : CompleteOrthogonalIdempotents
      (fun i : I => Pi.single (M := fun i => Ai i) i (1 : Ai i)) :=
    CompleteOrthogonalIdempotents.single _
  have hidem (i : I) : IsIdempotentElem (ψ (Pi.single i 1)) :=
    (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.idem i
  have h01 (i : I) : ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 :=
    (hidem i).eq_zero_or_one_of_isLocalRing
  have hsum : ∑ i : I, ψ (Pi.single i 1) = 1 := by
    rw [← map_sum]; simp [hcoi.complete]
  have hortho (i j : I) (hij : i ≠ j) :
      ψ (Pi.single i 1) * ψ (Pi.single j 1) = 0 := by
    simpa [Function.comp_def] using
      (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.ortho hij
  have hex : ∃ j, ψ (Pi.single j 1) = 1 := by
    by_contra hall
    push Not at hall
    have hzero : ∀ i, ψ (Pi.single i 1) = 0 := fun i => (h01 i).resolve_right (hall i)
    simp [hzero] at hsum
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, fun i hi => ?_⟩
  have := hortho i j hi
  rwa [hj, mul_one] at this

/-- The algebra homomorphism from the `j`-th factor obtained by composing with `Pi.single j`. -/
private noncomputable def algHomSingleComponent
    {k : Type u} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra k (Ai i)]
    {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B]
    (ψ : (∀ i, Ai i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1)
    (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) : Ai j →ₐ[k] B where
  toFun y := ψ (Pi.single j y)
  map_one' := hj
  map_mul' y₁ y₂ := show ψ _ = ψ _ * ψ _ by rw [Pi.single_mul, map_mul]
  map_zero' := by simp
  map_add' y₁ y₂ := by
    change ψ (Pi.single j (y₁ + y₂)) = ψ (Pi.single j y₁) + ψ (Pi.single j y₂)
    rw [← map_add]
    congr 1
    ext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  commutes' c := by
    have heq : Pi.single j (algebraMap k (Ai j) c) =
        (algebraMap k (∀ i, Ai i) c) * Pi.single j 1 := by
      ext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_eq_of_ne hij]
    rw [heq, map_mul, AlgHom.commutes, hj, mul_one]

/-- If `A` is an étale algebra over a field `k` and `φ : A →ₐ[k] B` is an algebra homomorphism
to a local ring `B`, then every element of the image of `φ` is separable over `k`. -/
private lemma isSeparable_of_etale_to_local (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] [Algebra.Etale k A] (B : Type u) [CommRing B] [Algebra k B] [IsLocalRing B]
    (φ : A →ₐ[k] B) (a : A) : IsSeparable k (φ a) := by
  by_cases hB : Nontrivial B
  · haveI : Module.Finite k A := FormallyUnramified.finite_of_free k A
    obtain ⟨I, _, Ai, hfield, halg, e, hprop⟩ :=
      (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := A)).mp inferInstance
    haveI : Fintype I := Fintype.ofFinite I
    letI (i : I) : Field (Ai i) := hfield i
    letI (i : I) : Algebra k (Ai i) := halg i
    classical
    let ψ : (∀ i, Ai i) →ₐ[k] B := φ.comp e.symm.toAlgHom
    obtain ⟨j, hj, hothers⟩ := exists_unique_index_of_algHom_pi_to_local ψ
    let τ := algHomSingleComponent ψ j hj hothers
    have hfactor (x : ∀ i, Ai i) : ψ x = τ (x j) := by
      change ψ x = ψ (Pi.single j (x j))
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      refine Finset.sum_eq_single_of_mem j (Finset.mem_univ _) fun i _ hi => ?_
      have : Pi.single (M := fun i => Ai i) i (x i) = Pi.single i 1 * x := by
        rw [← Pi.single_mul_left]; simp
      rw [this, map_mul, hothers i hi, zero_mul]
    have hφa : φ a = τ ((e a) j) := by
      rw [← hfactor (e a)]
      simp [ψ]
    rw [hφa]
    have hsep_j : Algebra.IsSeparable k (Ai j) := (hprop j).2
    have hb_sep : IsSeparable k ((e a) j) := Algebra.IsSeparable.isSeparable k _
    exact hb_sep.of_dvd <| minpoly.dvd k _ <| by
      rw [Polynomial.aeval_algHom_apply]; simp [minpoly.aeval]
  · haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
    have hint : IsIntegral k (φ a) :=
      ⟨Polynomial.X, Polynomial.monic_X, by simp [Subsingleton.elim (φ a) 0]⟩
    have hdvd1 : minpoly k (φ a) ∣ 1 :=
      minpoly.dvd k (φ a) (by simp [Subsingleton.elim (Polynomial.aeval (φ a) 1) 0])
    have heq1 : minpoly k (φ a) = 1 :=
      (minpoly.monic hint).eq_one_of_isUnit (isUnit_of_dvd_one hdvd1)
    rw [IsSeparable, heq1]
    exact Polynomial.separable_one

instance isSeparable (k : Type u) [Field k] [Algebra k R] [IndEtale k R] [IsLocalRing R] :
    Algebra.IsSeparable k R := by
  obtain ⟨ι, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := k) (S := R)
  letI := hcat; letI := hfilt
  refine ⟨fun x => ?_⟩
  have hcolim : IsColimit ((forget (CommAlgCat.{u} k)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} k)) P.isColimit
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hcolim x
  rw [← ha]
  haveI : Algebra.Etale k (P.diag.obj i) := hP i
  exact isSeparable_of_etale_to_local k (P.diag.obj i) R (P.ι.app i).hom a

instance isSeparable_residueField [Algebra.IndEtale R S] (p : Ideal R) (q : Ideal S)
    [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField :=
  sorry

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
  algebraize [f, g, (g.comp f)]
  exact Algebra.IndEtale.trans R S T

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
