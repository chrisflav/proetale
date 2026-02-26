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

private instance : CommRing (S f) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin 2) R ⧸ idealJ f))

private instance : Algebra R (S f) :=
  inferInstanceAs (Algebra R (MvPolynomial (Fin 2) R ⧸ idealJ f))

-- Helper: pderiv i (toMvPolynomial i p) = toMvPolynomial i p.derivative
private lemma pderiv_toMvPolynomial_self {σ : Type*} [DecidableEq σ] (i : σ) (p : R[X]) :
    pderiv i (toMvPolynomial i p) = toMvPolynomial i p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.toMvPolynomial, Polynomial.aeval_monomial,
      Polynomial.derivative_monomial]
    change pderiv i (MvPolynomial.C a * MvPolynomial.X i ^ n) =
      MvPolynomial.C (a * (n : R)) * MvPolynomial.X i ^ (n - 1)
    rw [pderiv_mul, pderiv_C, zero_mul, zero_add, pderiv_pow, pderiv_X,
      Pi.single_eq_same, map_mul, map_natCast]
    ring

-- Helper: pderiv j (toMvPolynomial i p) = 0 when j ≠ i
private lemma pderiv_toMvPolynomial_ne {σ : Type*} (i j : σ) (hne : j ≠ i) (p : R[X]) :
    pderiv j (toMvPolynomial i p) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  rw [Polynomial.toMvPolynomial_eq_rename_comp, AlgHom.comp_apply]
  intro hmem
  obtain ⟨_, _, hk⟩ := MvPolynomial.mem_vars_rename _ _ hmem
  exact absurd hk.symm hne

-- Helper: toMvPolynomial 0 f.derivative is a unit in S f
private lemma isUnit_toMvPolynomial_derivative :
    IsUnit (Ideal.Quotient.mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative)) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨Ideal.Quotient.mk (idealJ f) (X 1), ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (idealJ f)), Ideal.Quotient.eq]
  apply Ideal.subset_span
  simp only [idealJ, Set.mem_range]
  exact ⟨1, by simp [Matrix.cons_val_one, Matrix.cons_val_fin_one]⟩

private instance : IsStandardSmoothOfRelativeDimension 0 R (S f) := by
  let v : Fin 2 → MvPolynomial (Fin 2) R :=
    ![toMvPolynomial (0 : Fin 2) f,
      (toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1]
  let P := PreSubmersivePresentation.naive (R := R) (σ := Fin 2) (ι := Fin 2)
    (v := v) (_root_.id) (Function.injective_id)
  suffices h : IsUnit P.jacobian by
    exact (SubmersivePresentation.mk P h).isStandardSmoothOfRelativeDimension
      (by simp [Presentation.dimension])
  -- Compute Jacobian matrix entries using jacobiMatrix_apply
  -- P.jacobiMatrix i j = pderiv (P.map i) (P.relation j) = pderiv (id i) (v j) = pderiv i (v j)
  have hm00 : P.jacobiMatrix 0 0 = pderiv (0 : Fin 2) (v 0) :=
    PreSubmersivePresentation.jacobiMatrix_apply P 0 0
  have hm01 : P.jacobiMatrix 0 1 = pderiv (0 : Fin 2) (v 1) :=
    PreSubmersivePresentation.jacobiMatrix_apply P 0 1
  have hm10 : P.jacobiMatrix 1 0 = pderiv (1 : Fin 2) (v 0) :=
    PreSubmersivePresentation.jacobiMatrix_apply P 1 0
  have hm11 : P.jacobiMatrix 1 1 = pderiv (1 : Fin 2) (v 1) :=
    PreSubmersivePresentation.jacobiMatrix_apply P 1 1
  -- Compute each pderiv entry
  have h10 : pderiv (1 : Fin 2) (v 0) = 0 := by
    simp only [v, Matrix.cons_val_zero]
    exact pderiv_toMvPolynomial_ne (0 : Fin 2) (1 : Fin 2) (by decide) f
  have h00 : pderiv (0 : Fin 2) (v 0) = toMvPolynomial (0 : Fin 2) f.derivative := by
    simp only [v, Matrix.cons_val_zero]
    exact pderiv_toMvPolynomial_self (0 : Fin 2) f
  have h11 : pderiv (1 : Fin 2) (v 1) = toMvPolynomial (0 : Fin 2) f.derivative := by
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [map_sub, pderiv_one, sub_zero, pderiv_mul,
      pderiv_toMvPolynomial_ne (0 : Fin 2) (1 : Fin 2) (by decide) f.derivative,
      zero_mul, zero_add, pderiv_X, Pi.single_eq_same, mul_one]
  -- Assemble: det = h00 * h11 - h01 * h10 = f'^2 (since h10 = 0)
  rw [P.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two,
    hm00, hm01, hm10, hm11, h10, h00, h11, mul_zero, sub_zero, map_mul]
  exact (isUnit_toMvPolynomial_derivative f).mul (isUnit_toMvPolynomial_derivative f)

private def g {I : Ideal R} {f : R[X]} {a₀ : R} (e : Polynomial.eval a₀ f ∈ I)
    (u : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a₀ (derivative f)))) : S f →ₐ[R] R ⧸ I := by
  let φ : Fin 2 → R ⧸ I := ![Ideal.Quotient.mk I a₀, ↑u.unit⁻¹]
  let ψ : MvPolynomial (Fin 2) R →ₐ[R] R ⧸ I := MvPolynomial.aeval φ
  have hle : idealJ f ≤ RingHom.ker (ψ : MvPolynomial (Fin 2) R →+* R ⧸ I) := by
    rw [show idealJ f = Ideal.span (Set.range _) from rfl, Ideal.span_le]
    intro y hy
    simp only [SetLike.mem_coe, RingHom.mem_ker, Set.mem_range] at hy ⊢
    obtain ⟨i, rfl⟩ := hy
    fin_cases i
    · show ψ (toMvPolynomial (0 : Fin 2) f) = 0
      simp only [ψ, MvPolynomial.aeval_toMvPolynomial, φ, Matrix.cons_val_zero]
      rw [show (Ideal.Quotient.mk I : R → R ⧸ I) = algebraMap R (R ⧸ I) from rfl,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr e)
    · show ψ ((toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1) = 0
      simp only [ψ, map_sub, map_one, map_mul, MvPolynomial.aeval_toMvPolynomial,
        MvPolynomial.aeval_X, φ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      have haeval : Polynomial.aeval (Ideal.Quotient.mk I a₀) f.derivative =
          Ideal.Quotient.mk I (Polynomial.eval a₀ f.derivative) :=
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval a₀ f.derivative
      rw [haeval, IsUnit.mul_val_inv u]; exact sub_self 1
  have hψ : ∀ x ∈ idealJ f, ψ x = 0 := fun x hx => RingHom.mem_ker.mp (hle hx)
  exact (Ideal.Quotient.liftₐ (idealJ f) ψ hψ : S f →ₐ[R] R ⧸ I)

theorem henselian_if_exists_section (R : Type u)
    [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S] (g : S →ₐ[R] R ⧸ I),
    ∃ σ : S →ₐ[R] R, (Ideal.Quotient.mk I).comp (σ : S →+* R) = g) :
    HenselianRing R I where
  jac := Ideal.jacobson_bot (R := R) ▸ hI
  is_henselian := by
    intro f hf a₀ hfa hdf
    obtain ⟨σ, hσ⟩ := h (S f) (g hfa hdf)
    refine ⟨σ (Ideal.Quotient.mk (idealJ f) (MvPolynomial.X 0)), ?_, ?_⟩
    · rw [Polynomial.IsRoot, ← Polynomial.coe_aeval_eq_eval]
      have key : σ (Ideal.Quotient.mk (idealJ f) (Polynomial.toMvPolynomial (0 : Fin 2) f))
          = Polynomial.aeval (σ (Ideal.Quotient.mk (idealJ f) (MvPolynomial.X 0))) f := by
        have h1 := MvPolynomial.aeval_unique (σ.comp (Ideal.Quotient.mkₐ R (idealJ f)))
        have h2 := AlgHom.congr_fun h1 (Polynomial.toMvPolynomial (0 : Fin 2) f)
        simp only [AlgHom.comp_apply, MvPolynomial.aeval_toMvPolynomial] at h2
        exact h2
      have hmem : (Ideal.Quotient.mk (idealJ f)) (Polynomial.toMvPolynomial (0 : Fin 2) f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, by simp [Matrix.cons_val_zero]⟩)
      simp only [hmem] at key
      -- key : σ 0 = aeval a f; we need aeval a f = 0
      -- Since σ is an AlgHom, σ 0 = 0
      exact key.symm.trans (map_zero σ)
    · have hσ' : ∀ x : S f, Ideal.Quotient.mk I (σ x) = g hfa hdf x := by
        intro x; exact RingHom.congr_fun hσ x
      rw [← Ideal.Quotient.eq, hσ']
      show g hfa hdf (Ideal.Quotient.mk (idealJ f) (MvPolynomial.X 0)) = Ideal.Quotient.mk I a₀
      change (Ideal.Quotient.liftₐ (idealJ f) (MvPolynomial.aeval (![Ideal.Quotient.mk I a₀, ↑hdf.unit⁻¹])) _) (Ideal.Quotient.mk (idealJ f) (MvPolynomial.X 0)) = _
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      simp [MvPolynomial.aeval_X, Matrix.cons_val_zero]

-- Success

open CategoryTheory CommAlgCat Limits

universe u₁ v₁ u₂ v₂ w

variable (Q : MorphismProperty CommRingCat) (R : CommRingCat.{u})

noncomputable
def CommRingCat.Under.inclusion :
    MorphismProperty.Under Q ⊤ R ⥤ CommAlgCat R :=
  MorphismProperty.Under.forget _ _ _ ⋙ (commAlgCatEquivUnder R).inverse

abbrev CategoryTheory.CommRingCat.Etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty RingHom.Etale

instance {C : Type*} [Category C] [HasColimits C] (X : C) : HasColimits (Under X) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  constructor
  refine ⟨?_, ?_⟩
  · exact WithInitial.coconeEquiv.inverse.obj (colimit.cocone _)
  · apply WithInitial.isColimitEquiv.toFun
    apply IsColimit.ofIsoColimit _ (WithInitial.coconeEquiv.counitIso.app _).symm
    exact colimit.isColimit (WithInitial.liftFromUnder.obj K)

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (S : C ⥤ D) (T : D)

instance foo [EssentiallySmall.{w} C] [∀ (X : C), Small.{w} (S.obj X ⟶ T)] :
    EssentiallySmall.{w} (CostructuredArrow S T) := by
  rw [← essentiallySmall_congr
    (CostructuredArrow.pre (equivSmallModel.{w} C).inverse S T).asEquivalence]
  letI (X : SmallModel.{w} C) : Small.{w}
      (((equivSmallModel.{w} C).inverse ⋙ S).obj X ⟶ T) :=
    inferInstanceAs (Small.{w} (S.obj ((equivSmallModel C).inverse.obj X) ⟶ T))
  haveI : Small.{w} (CostructuredArrow ((equivSmallModel.{w} C).inverse ⋙ S) T) := by
    apply small_of_surjective
      (f := fun (p : Σ (X : SmallModel.{w} C),
        Shrink.{w} (((equivSmallModel.{w} C).inverse ⋙ S).obj X ⟶ T)) ↦
      CostructuredArrow.mk ((equivShrink _).symm p.2))
    intro f
    obtain ⟨X, f, rfl⟩ := f.mk_surjective
    refine ⟨⟨X, (equivShrink _) f⟩, ?_⟩
    dsimp only
    congr 1
    exact Equiv.symm_apply_apply _ _
  exact essentiallySmall_of_small_of_locallySmall _

instance : EssentiallySmall.{u, u, u + 1} (CommRingCat.Etale.Under ⊤ R) := by
  apply essentiallySmall_of_le (Q := CommRingCat.Etale)
  intro X Y f (hf : RingHom.Etale f.hom)
  show RingHom.FiniteType f.hom
  exact RingHom.FiniteType.of_finitePresentation (by
    algebraize [f.hom]
    exact (hf : Algebra.Etale _ _).finitePresentation)

instance (R : Type u) [CommRing R] :
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).HasPointwiseLeftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)) := by
  intro Y
  let L := CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)
  show HasColimit (CostructuredArrow.proj L Y ⋙ L)
  set_option synthInstance.maxHeartbeats 80000 in
  exact hasColimit_of_equivalence_comp
    (equivSmallModel.{u} (CostructuredArrow L Y)).symm

def henselizationFunctor (R : Type u) [CommRing R] :
    (CommAlgCat R) ⥤ CommAlgCat R :=
  (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).leftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def Henselization : Type u := (henselizationFunctor R).obj (of R S)

instance : CommRing (Henselization R S) := by
  unfold Henselization
  infer_instance

instance : Algebra R (Henselization R S) := by
  delta Henselization henselizationFunctor
  exact (inferInstance : Algebra R ((Functor.leftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))).obj (of R S)))

def henselization_isom_colim : CommAlgCat.of R (Henselization R S) ≅
    Limits.colimit ((CostructuredArrow.proj (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R)) (CommAlgCat.of R S)).comp (CommRingCat.Under.inclusion
    CommRingCat.Etale (CommRingCat.of R))) := by
  let L := CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)
  let Y := CommAlgCat.of R S
  have hpw : Functor.LeftExtension.IsPointwiseLeftKanExtensionAt
      (Functor.LeftExtension.mk _ (Functor.leftKanExtensionUnit L L)) Y :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      (L.leftKanExtension L) (Functor.leftKanExtensionUnit L L) Y
  exact hpw.isoColimit

-- Abbreviation for the colimit diagram functor used in the Henselization.
private noncomputable abbrev hensDiagram (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] :=
  (CostructuredArrow.proj (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
    (CommAlgCat.of R S)) ⋙
  (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))

-- The canonical cocone from the Henselization diagram to R/I.
-- Each stage has a section (the CostructuredArrow hom), and these are compatible.
private noncomputable def sectionCocone (R : Type u) [CommRing R] (I : Ideal R) :
    Cocone (hensDiagram R (R ⧸ I)) where
  pt := CommAlgCat.of R (R ⧸ I)
  ι := {
    app := fun j => j.hom
    naturality := fun j₁ j₂ f => by
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map]
      rw [Category.comp_id]
      exact CostructuredArrow.w f
  }

-- The canonical section: Henselization R (R/I) → R/I.
-- Constructed using the colimit universal property.
private noncomputable def henselizationSection (R : Type u) [CommRing R] (I : Ideal R) :
    CommAlgCat.of R (Henselization R (R ⧸ I)) ⟶ CommAlgCat.of R (R ⧸ I) :=
  (henselization_isom_colim R (R ⧸ I)).hom ≫ Limits.colimit.desc _ (sectionCocone R I)

-- The colimit injection at stage j, composed with the inverse of the Henselization isomorphism.
-- This gives an R-algebra map from the j-th étale R-algebra to the Henselization.
private noncomputable def stageToHenselization (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S]
    (j : CostructuredArrow (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
      (CommAlgCat.of R S)) :
    (hensDiagram R S).obj j ⟶ CommAlgCat.of R (Henselization R S) :=
  Limits.colimit.ι (hensDiagram R S) j ≫ (henselization_isom_colim R S).inv

-- Joint surjectivity for the Henselization: every element of the Henselization
-- comes from some stage of the colimit diagram.
-- This follows from the chain: colimits in CommAlgCat R are computed via Under (CommRingCat.of R),
-- underlying CommRingCat objects use liftFromUnder, and forget CommRingCat preserves filtered colimits.
-- The filteredness of CostructuredArrow L Y follows from tensor products of étale R-algebras.
private lemma henselization_jointly_surjective (R : Type u) [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] (y : Henselization R S) :
    ∃ (j : CostructuredArrow (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
        (CommAlgCat.of R S))
      (y_j : (hensDiagram R S).obj j),
      (stageToHenselization R S j).hom y_j = y := by
  -- Needed: PreservesColimit (hensDiagram R S) (forget (CommAlgCat R))
  -- Proof chain: forget = forget₂ CommRingCat ⋙ forget CommRingCat (by HasForget₂.forget_comp)
  -- forget₂ preserves filtered colimits (via commAlgCatEquivUnder + Under.forget preserves filtered)
  -- forget CommRingCat preserves filtered colimits (CommRingCat.FilteredColimits)
  -- Also needs: IsFiltered (CostructuredArrow L Y) (from étale R-algebras: tensor products, etc.)
  -- Universe issue: CostructuredArrow is Category.{u} on Type (u+1), but
  -- PreservesFilteredColimits (forget CommRingCat.{u}) is PreservesFilteredColimitsOfSize.{u, u},
  -- so need equivSmallModel or PreservesFilteredColimitsOfSize.{u+1, u}.
  haveI : PreservesColimit (hensDiagram R S) (forget (CommAlgCat (CommRingCat.of R))) := sorry
  -- Push y through the isomorphism to the colimit
  let iso := henselization_isom_colim R S
  -- Use Concrete.colimit_exists_rep to find a representative in the colimit
  obtain ⟨j, y_j, hj⟩ := Concrete.colimit_exists_rep (hensDiagram R S) (iso.hom y)
  exact ⟨j, y_j, by
    show (colimit.ι (hensDiagram R S) j ≫ iso.inv).hom y_j = y
    change iso.inv.hom ((colimit.ι (hensDiagram R S) j).hom y_j) = _
    rw [hj]
    change (iso.hom ≫ iso.inv).hom y = y
    simp [iso]⟩

-- For a filtered colimit of R-algebras with sections to R/I,
-- elements of I map to the Jacobson radical of the colimit.
-- Proof: for r ∈ I and y : Hens, y comes from some stage A_j via joint surjectivity.
-- At stage j, b_j = algebraMap(r) * y_j + 1 maps to 1 under g_j (since r ∈ I).
-- Localize A_j at b_j: this is still étale, section extends, b_j becomes a unit.
-- The unit maps forward to the colimit, giving IsUnit in Hens.
-- Given a CostructuredArrow j and an element s of the j-th stage algebra such that
-- j.hom sends s to a unit in the target (i.e., s maps to a unit under the section),
-- construct a new CostructuredArrow where s maps to a unit, using localization.
-- The new stage is Localization.Away s, which is still étale over R.
-- The section extends because j.hom(s) is a unit.
-- Returns the new CostructuredArrow and a morphism from j to it.
-- This is the core categorical construction needed for the Jacobson radical argument.
-- Helper: the underlying type of (hensDiagram R S).obj j is definitionally the type of j.left.right
-- (the CommRingCat object at stage j), via commAlgCatEquivUnder.inverse
set_option maxHeartbeats 3200000 in
private lemma exists_costructuredArrow_localization
    {R : Type u} [CommRing R] {I : Ideal R}
    (j : CostructuredArrow (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
      (CommAlgCat.of R (R ⧸ I)))
    (s : (hensDiagram R (R ⧸ I)).obj j)
    (hs : IsUnit (j.hom.hom s)) :
    ∃ (j' : CostructuredArrow (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))
        (CommAlgCat.of R (R ⧸ I)))
      (f : j ⟶ j'),
      IsUnit ((hensDiagram R (R ⧸ I)).map f s) := by
  haveI : Algebra.Etale R ↑((hensDiagram R (R ⧸ I)).obj j) := j.left.prop
  have hs' : IsUnit (j.hom.hom.toRingHom s) := hs
  let L := CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)
  -- New Under object: the localization Localization.Away s, which is etale over R
  let j'_under : CommRingCat.Etale.Under ⊤ (CommRingCat.of R) :=
    MorphismProperty.Under.mk (Q := ⊤)
      (CommRingCat.ofHom (algebraMap R (Localization.Away s)))
      ((RingHom.etale_algebraMap).mpr inferInstance)
  -- The lift: ring hom from Localization.Away s to R/I extending j.hom
  let f_ring : Localization.Away s →+* (R ⧸ I) :=
    IsLocalization.Away.lift s (g := j.hom.hom.toRingHom) hs'
  -- Under morphism from the localization to the target (R/I), for the section
  let under_target := (commAlgCatEquivUnder (CommRingCat.of R)).functor.obj (CommAlgCat.of R (R ⧸ I))
  let under_source := (MorphismProperty.Under.forget CommRingCat.Etale ⊤ (CommRingCat.of R)).obj j'_under
  let f_crm : CommRingCat.of (Localization.Away s) ⟶ CommRingCat.of (R ⧸ I) :=
    CommRingCat.ofHom f_ring
  let section_under : under_source ⟶ under_target :=
    Under.homMk f_crm (by
      ext r
      simp [under_source, under_target, j'_under, MorphismProperty.Under.mk, f_crm, f_ring,
        CommRingCat.ofHom]
      show f_ring (algebraMap R (Localization.Away s) r) = algebraMap R (R ⧸ I) r
      rw [IsScalarTower.algebraMap_apply R ↑((hensDiagram R (R ⧸ I)).obj j) (Localization.Away s)]
      rw [show f_ring (algebraMap ↑((hensDiagram R (R ⧸ I)).obj j) (Localization.Away s)
        (algebraMap R _ r)) = j.hom.hom.toRingHom (algebraMap R _ r) from
        IsLocalization.Away.lift_eq s hs' _]
      exact j.hom.hom.commutes r)
  -- CommAlgCat morphism: L.obj j'_under -> of R (R/I), via inverse.map and unitIso
  let j'_hom_raw := (commAlgCatEquivUnder (CommRingCat.of R)).inverse.map section_under
  let j'_hom : L.obj j'_under ⟶ CommAlgCat.of R (R ⧸ I) :=
    j'_hom_raw ≫ (commAlgCatEquivUnder (CommRingCat.of R)).unitIso.inv.app (CommAlgCat.of R (R ⧸ I))
  -- New CostructuredArrow
  let j' : CostructuredArrow L (CommAlgCat.of R (R ⧸ I)) := CostructuredArrow.mk j'_hom
  -- Localization map as CommRingCat morphism
  let loc_map : j.left.right ⟶ CommRingCat.of (Localization.Away s) :=
    CommRingCat.ofHom (algebraMap ↑((hensDiagram R (R ⧸ I)).obj j) (Localization.Away s))
  -- Under morphism j.left -> j'_under (the localization map)
  let under_morph : j.left ⟶ j'_under := MorphismProperty.Under.homMk loc_map
    (by
      ext r
      simp [j'_under, MorphismProperty.Under.mk, loc_map]
      exact (IsScalarTower.algebraMap_apply R ↑((hensDiagram R (R ⧸ I)).obj j)
        (Localization.Away s) r).symm)
    trivial
  refine ⟨j', CostructuredArrow.homMk under_morph ?_, ?_⟩
  · -- Commutativity: L.map under_morph ≫ j'_hom = j.hom
    -- At element level: f_ring (algebraMap A_j (Loc.Away s) x) = j.hom.hom x, by lift_eq
    apply CommAlgCat.hom_ext
    ext x
    change j'_hom.hom ((L.map under_morph).hom x) = j.hom.hom x
    show (f_ring : Localization.Away s →+* (R ⧸ I))
      ((L.map under_morph).hom x) = j.hom.hom.toRingHom x
    exact IsLocalization.Away.lift_eq s hs' x
  · -- IsUnit: (L.map under_morph).hom s = algebraMap A_j (Loc.Away s) s, a unit by localization
    show IsUnit ((L.map under_morph).hom s)
    have h1 : IsUnit (algebraMap ↑((hensDiagram R (R ⧸ I)).obj j) (Localization.Away s) s) :=
      IsLocalization.map_units (Localization.Away s) ⟨s, Submonoid.mem_powers s⟩
    exact (show (L.map under_morph).hom s =
      algebraMap ↑((hensDiagram R (R ⧸ I)).obj j) (Localization.Away s) s from rfl) ▸ h1

private lemma isUnit_algebraMap_mul_add_one_of_mem_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (r : R) (hr : r ∈ I) (y : Henselization R (R ⧸ I)) :
    IsUnit (algebraMap R (Henselization R (R ⧸ I)) r * y + 1) := by
  -- Step 1: Lift y to a stage of the colimit diagram
  obtain ⟨j, y_j, hy⟩ := henselization_jointly_surjective R (R ⧸ I) y
  -- Abbreviations
  let F := hensDiagram R (R ⧸ I)
  let ι_j := stageToHenselization R (R ⧸ I) j
  -- Step 2: Form b_j at stage j
  -- y_j has type ↑(F.obj j), which is the underlying type of a CommAlgCat R object.
  -- We use the same type for b_j.
  let b_j := algebraMap R _ r * y_j + (1 : (F.obj j : Type u))
  -- Step 3: Show b_j maps to algebraMap R Hens r * y + 1 via ι_j
  have hb : ι_j.hom b_j = algebraMap R (Henselization R (R ⧸ I)) r * y + 1 := by
    show ι_j.hom (algebraMap R _ r * y_j + 1) = algebraMap R _ r * y + 1
    rw [map_add, map_mul, map_one, hy]
    congr 1; congr 1
    exact ι_j.hom.commutes r
  -- Step 4: Show b_j maps to a unit under the section g_j = j.hom
  -- j.hom.hom is an R-algebra map F.obj j → R/I. We need j.hom.hom(b_j) to be a unit.
  -- Since r ∈ I, algebraMap R (R/I) r = 0, so j.hom.hom(b_j) = 0 * _ + 1 = 1.
  have hunit_section : IsUnit (j.hom.hom b_j) := by
    suffices h : j.hom.hom b_j = 1 from h ▸ isUnit_one
    -- Define g as j.hom.hom with explicit types to avoid F.obj j vs L.obj j.left issues
    have hg : ∃ (g : (F.obj j) →ₐ[R] (R ⧸ I)), (g : (F.obj j) → (R ⧸ I)) = j.hom.hom := ⟨j.hom.hom, rfl⟩
    obtain ⟨g, hge⟩ := hg
    -- Now g has the right domain type F.obj j, so map_add/map_mul/map_one work
    suffices hg1 : g b_j = 1 by
      change (j.hom.hom : _ → _) b_j = 1
      rw [← hge]; exact hg1
    show g (algebraMap R _ r * y_j + 1) = 1
    have hrz : algebraMap R (R ⧸ I) r = (0 : R ⧸ I) := by
      have := Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [Ideal.Quotient.algebraMap_eq]; exact this
    -- Use rw for structural steps; avoid simp due to instance diamond on R ⧸ I
    rw [map_add, map_mul, map_one]
    -- Goal: g (algebraMap R _ r) * g y_j + 1 = 1
    -- g.commutes gives g (algebraMap R _ r) = algebraMap R (R ⧸ I) r
    -- hrz gives algebraMap R (R ⧸ I) r = 0
    -- But rw [g.commutes, hrz] introduces Submodule.Quotient zero, not CommRing zero
    -- so zero_mul fails. Instead, prove the product is zero directly.
    -- Compute g(algebraMap r * y_j) = 0 using mul_eq_zero
    have key : g (algebraMap R _ r * y_j) = 0 := by
      rw [map_mul (f := g), g.commutes, hrz]
      exact mul_eq_zero_of_left rfl _
    -- Goal after rw [map_add, map_mul, map_one]: g (algebraMap R _ r) * g y_j + 1 = 1
    -- After g.commutes and hrz: algebraMap R (R ⧸ I) r * g y_j + 1 = 1
    -- But rw [g.commutes, hrz] introduces module zero. Instead use key + congrArg:
    -- key says g (algebraMap R _ r * y_j) = 0
    -- We need: g (algebraMap R _ r) * g y_j + 1 = 1
    -- Using map_mul directly: g (algebraMap R _ r * y_j) = g (algebraMap R _ r) * g y_j
    -- So g (algebraMap R _ r) * g y_j = 0 (from key and map_mul)
    have hmul : g (algebraMap R _ r * y_j) = g (algebraMap R _ r) * g y_j := map_mul g _ _
    have hprod_zero : g (algebraMap R _ r) * g y_j = 0 := hmul ▸ key
    -- Now rw [hprod_zero] introduces the same problematic zero.
    -- Use calc instead:
    calc g (algebraMap R _ r) * g y_j + 1
        = (0 : R ⧸ I) + 1 := by rw [hprod_zero]
      _ = 1 := zero_add 1
  -- Step 5: Get a new stage where b_j is a unit
  obtain ⟨j', f, hunit⟩ := exists_costructuredArrow_localization j b_j hunit_section
  -- Step 6: Transport the unit to the Henselization
  let ι_j' := stageToHenselization R (R ⧸ I) j'
  -- The colimit compatibility: F.map f ≫ ι_j' = ι_j
  have hcompat : F.map f ≫ ι_j' = ι_j := by
    simp only [F, ι_j, ι_j', stageToHenselization, ← Category.assoc, colimit.w F f]
  have hmap : ι_j'.hom (F.map f b_j) = algebraMap R (Henselization R (R ⧸ I)) r * y + 1 := by
    rw [← hb]
    change (F.map f ≫ ι_j').hom b_j = ι_j.hom b_j
    rw [hcompat]
  rw [← hmap]
  exact IsUnit.map ι_j'.hom hunit

theorem henselization_of_quotient_is_henselian {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R) :
    HenselianRing (Henselization R (R ⧸ I)) (I.map (algebraMap R _)) := by
  apply henselian_if_exists_section
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← Ideal.jacobson_bot]
    rw [Ideal.mem_jacobson_bot]
    intro y
    exact isUnit_algebraMap_mul_add_one_of_mem_jacobson I hI r hr y
  · intro S _ _ _ g
    -- Goal: ∃ σ : S →ₐ[Hens] Hens, (Ideal.Quotient.mk (I.map _)).comp σ = g.
    -- Strategy: S is étale (hence finitely presented) over Hens = colim A_i.
    -- By finite presentation, S descends to some stage A_j: there exists an étale
    -- A_j-algebra T_j with S ≅ T_j ⊗_{A_j} Hens. The section g : S → Hens/(I.map)
    -- restricts to T_j → R/I, making (T_j, g|_{T_j}) an object in the colimit diagram.
    -- The colimit map T_j → Hens provides the desired section S → Hens.
    -- This proof requires: descent of finitely presented algebras from filtered colimits,
    -- descent of sections, and the universal property of the colimit.
    sorry
