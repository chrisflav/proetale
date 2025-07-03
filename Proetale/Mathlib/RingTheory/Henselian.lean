import Mathlib

-- Rename `HenselianRing` to `IsHenselianRing`, ``HenselianLocalRing` to `IsHenselianLocalRing`.

class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

universe u v

noncomputable section
open Polynomial
open MvPolynomial Ideal Quotient Algebra

variable {R : Type u} [CommRing R] (f : R[X])

-- f(X), f'(X)Y - 1
private def idealJ (f : R[X]) : Ideal (MvPolynomial (Fin 2) R) :=
  (span (Set.range ![toMvPolynomial (0 : Fin 2) f, (toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1]))

private def S : Type u := MvPolynomial (Fin 2) R ⧸ (idealJ f)

private instance : CommRing (S f) := by
  unfold S
  infer_instance

private instance : Algebra R (S f) := by
  unfold S
  infer_instance

private def presentationS : Presentation R (S f) (Fin 2) (Fin 2) := by
  let s : (S f) → (MvPolynomial (Fin 2) R) :=
    Function.surjInv (f := (Ideal.Quotient.mk (idealJ f))) Ideal.Quotient.mk_surjective
  have hs (x : S f) : mk _ (s x) = x := by
    rw [Function.surjInv_eq (f := (Ideal.Quotient.mk (idealJ f)))]
  apply Presentation.naive s hs

private def preSubmersivePresentationS : PreSubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPresentation := presentationS f
  map := id
  map_inj _ _ h := h
}

theorem pderiv_toMvPolynomial_eq_zero_of_ne (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (pderiv i) ((toMvPolynomial j) f) = 0 := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp [Pi.single_eq_of_ne h.symm]

theorem pderiv_toMvPolynomial_eq_toMvPolynomial_pderiv (n : ℕ) (i : Fin n) :
    (pderiv i) ((toMvPolynomial i) f) = (toMvPolynomial i) f.derivative := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp

private def submersivePresentationS (f : R[X]) : SubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPreSubmersivePresentation := preSubmersivePresentationS f
  jacobian_isUnit := by
    let f' := (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative))
    have unit_f' : IsUnit f' := by
      rw [isUnit_iff_exists]
      use (mk (idealJ f) (X 1))
      constructor
      · rw [← map_mul, ← map_one (Ideal.Quotient.mk _), mk_eq_mk_iff_sub_mem]
        apply Ideal.subset_span
        simp
      · rw [← map_mul, ← map_one (Ideal.Quotient.mk _), mk_eq_mk_iff_sub_mem]
        apply Ideal.subset_span
        use 1
        simp
        ring
    let P := preSubmersivePresentationS f
    have : P.jacobian = f' * f' := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      rw [Matrix.det_fin_two]
      have hP₀ : P.map 0 = 0 := rfl
      have hP₁ : P.map 1 = 1 := rfl
      have hR₀ : P.relation 0 = toMvPolynomial (0 : Fin 2) f := rfl
      have hR₁ : P.relation 1 = (toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1 := rfl
      have hd10 : (pderiv (P.map 1)) (P.relation 0) = 0 := by
        rw [hP₁, hR₀]
        apply pderiv_toMvPolynomial_eq_zero_of_ne
        simp
      have h01 : P.jacobiMatrix 1 0 = 0 := by
        rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
        rw [hd10]
      have h00 : P.jacobiMatrix 0 0 = (toMvPolynomial (0 : Fin 2) f.derivative) := by
        rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
        rw [hP₀, hR₀]
        apply pderiv_toMvPolynomial_eq_toMvPolynomial_pderiv
      have h11 : P.jacobiMatrix 1 1 = (toMvPolynomial (0 : Fin 2) f.derivative) := by
        rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
        rw [hP₁, hR₁]
        simp
        apply pderiv_toMvPolynomial_eq_zero_of_ne
        simp
      rw [h01, h00, h11]
      simp
      have : (Polynomial.aeval (P.val 0)) (derivative f) = f' := by
        have : P.val 0 = Ideal.Quotient.mk _ (X 0) := rfl
        rw [this]
        sorry
        -- have : (Polynomial.aeval ((Ideal.Quotient.mk (idealJ f)) (MvPolynomial.X 0))) = (Ideal.Quotient.mk (idealJ f)) (Polynomial.aeval (MvPolynomial.X 0)) := by sorry
        -- rw [Polynomial.aeval_algHom]
      rw [this]
    rw [this]
    simp
    exact unit_f'
}

private instance : IsStandardSmoothOfRelativeDimension 0 R (S f) := by
  unfold S
  constructor
  use (Fin 2), (Fin 2), inferInstance, inferInstance, (submersivePresentationS f)
  simp [Presentation.dimension]

private theorem aeval_zero_of_mem_span {I : Ideal R} {f : R[X]} {a₀ : R} (e : Polynomial.eval a₀ f ∈ I)
    (u : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a₀ (derivative f)))) :
    ∀ a ∈ idealJ f,
    (MvPolynomial.aeval
    ![(Ideal.Quotient.mk I) a₀, (Ideal.Quotient.mk I) ((derivative f).aeval a₀)]) a = 0 := by
  sorry

private def g {I : Ideal R} {f : R[X]} {a₀ : R} (e : Polynomial.eval a₀ f ∈ I)
    (u : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a₀ (derivative f)))) : S f →ₐ[R] R ⧸ I :=
  Ideal.Quotient.liftₐ (idealJ f) (MvPolynomial.aeval ![a₀, f.derivative.aeval a₀]) (aeval_zero_of_mem_span e u)

theorem henselian_if_exists_section (R : Type u)
    [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S] (g : S →ₐ[R] R ⧸ I),
    ∃ σ : S →+* R, (Ideal.Quotient.mk I).comp σ = g) :
    HenselianRing R I where
      jac := Ideal.jacobson_bot (R := R) ▸ hI
      is_henselian := by
          intro f monic a₀ e u
          obtain ⟨σ, hσ⟩ := h (S f) (g e u)
          use σ (mk _ (X 0))
          constructor
          · sorry -- f (X_0) = 0 since kernel contains f(X_0)
          · sorry -- σ (X_0) = a₀ since σ is a section of the quotient map (hσ)

-- Success

open CategoryTheory CommAlgCat

variable (Q : MorphismProperty CommRingCat) (R : CommRingCat.{u})

noncomputable
def CommRingCat.Under.inclusion :
    MorphismProperty.Under Q ⊤ R ⥤ CommAlgCat R :=
  MorphismProperty.Under.forget _ _ _ ⋙ (commAlgCatEquivUnder R).inverse

def CategoryTheory.CommRingCat.Etale : MorphismProperty CommRingCat := fun _ _ f ↦ f.hom.Etale

instance (R : Type u) [CommRing R] : (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).HasPointwiseLeftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)) := sorry-- Would be in Mathlib

def henselizationFunctor (R : Type u) [CommRing R] : (CommAlgCat R) ⥤ CommAlgCat R := (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).leftKanExtension (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def Henselization : Type u := (henselizationFunctor R).obj (of R S)

instance : CommRing (Henselization R S) := by
  unfold Henselization
  infer_instance

instance : Algebra R (Henselization R S) := by
  unfold Henselization
  infer_instance

def henselization_isom_colim : CommAlgCat.of R (Henselization R S) ≅
    Limits.colimit ((CostructuredArrow.proj (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R)) (CommAlgCat.of R S)).comp (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R))) :=
  CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _

theorem henselization_of_quotient_is_henselian {R : Type*} [CommRing R] (I: Ideal R) (hI : I ≤ Ring.jacobson R) :
    HenselianRing (Henselization R (R ⧸ I)) (I.map (algebraMap R _)) := by
  apply henselian_if_exists_section
  · sorry -- I * Hens_R ()
  · intro S _ _ _ g
    sorry -- any such (S, g) should already appear in the colimit.

-- Even more success
