/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits

/-!
# Etale ind-spreads
-/

universe w u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

@[simps]
def ShortComplex.forget (C : Type*) [Category C] [HasZeroMorphisms C] :
    ShortComplex C ⥤ ComposableArrows C 2 where
  obj S := S.toComposableArrows
  map f := ShortComplex.mapToComposableArrows f

def ComposableArrows.whiskeringRight (C D : Type*) [Category C] [Category D]
    (n : ℕ) :
    (C ⥤ D) ⥤ ComposableArrows C n ⥤ ComposableArrows D n :=
  Functor.whiskeringRight _ _ _

end CategoryTheory

open TensorProduct CategoryTheory Limits

def Subalgebra.FG.finiteType {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {A : Subalgebra R S} (h : A.FG) :
    Algebra.FiniteType R A :=
  A.fg_iff_finiteType.mp h

lemma RingHom.FinitePresentation.of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.FinitePresentation :=
  .of_surjective f hf.2 <| by
    have : ker f = ⊥ := by
      rw [← RingHom.injective_iff_ker_eq_bot]
      exact hf.1
    rw [this]
    exact Submodule.fg_bot

lemma RingHom.FormallyUnramified.of_bijective {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.FormallyUnramified := by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

lemma RingHom.FormallySmooth.of_bijective {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.FormallySmooth := by
  algebraize [f]
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

lemma RingHom.Smooth.of_bijective {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.Smooth := by
  rw [RingHom.smooth_def]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

lemma RingHom.Etale.of_bijective {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) :
    f.Etale := by
  rw [RingHom.etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

lemma RingHom.Etale.smooth {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Etale) :
    f.Smooth := by
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.2

namespace Algebra

variable (R : Type*) (A : Type u) (B : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra A B]

-- In mathlib PR #32837 by Andrew
lemma Etale.exists_subalgebra_fg [Etale A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) :=
  sorry

end Algebra

instance {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C]
    [HasLimitsOfShape WalkingParallelPair C] [HasColimitsOfShape WalkingParallelPair C]  (j : J) :
    ((evaluation J C).obj j).PreservesHomology where

lemma CategoryTheory.ShortComplex.exact_iff_evaluation {J : Type*} [Category J] {C : Type*}
    [Category C] [Preadditive C] [HasZeroObject C] [HasLimitsOfShape WalkingParallelPair C]
    [HasColimitsOfShape WalkingParallelPair C] (S : ShortComplex (J ⥤ C)) [S.HasHomology] :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  rw [exact_iff_isZero_homology, Functor.isZero_iff]
  refine forall_congr' fun j ↦ ?_
  let e : S.homology.obj j ≅ _ := (mapHomologyIso S ((evaluation J C).obj j)).symm
  rw [e.isZero_iff, exact_iff_isZero_homology]

@[simp]
lemma CategoryTheory.Functor.whiskerLeft_zero
    {C D E : Type*} [Category C] [Category D] [Category E] [HasZeroMorphisms E]
    (F : C ⥤ D) (G H : D ⥤ E) :
    Functor.whiskerLeft F (0 : G ⟶ H) = 0 :=
  rfl

instance CategoryTheory.MonoidalCategory.Limits.preservesLimitsOfShape_tensorRight_of_braided
    {J : Type*} [Category J] {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] (c : C)
    [PreservesLimitsOfShape J (tensorLeft c)] :
    PreservesLimitsOfShape J (MonoidalCategory.tensorRight c) where

instance CategoryTheory.MonoidalCategory.Limits.preservesColimitsOfShape_tensorRight_of_braided
    {J : Type*} [Category J] {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] (c : C)
    [PreservesColimitsOfShape J (tensorLeft c)] :
    PreservesColimitsOfShape J (MonoidalCategory.tensorRight c) where

lemma CategoryTheory.ObjectProperty.ind_inverseImage_le
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D)
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

lemma CategoryTheory.ObjectProperty.ind_inverseImage_eq_of_isEquivalence
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [F.IsEquivalence] :
    ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F := by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ ↦ ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j ↦ ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

lemma CategoryTheory.MorphismProperty.ind_inverseImage_le
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : MorphismProperty D) [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X Y f hf
  rw [ind_iff_ind_underMk] at hf
  simp only [inverseImage_iff, ind_iff_ind_underMk]
  -- TODO: make separate instance
  have : PreservesFilteredColimitsOfSize.{w, w} (Under.post (X := X) F) := by
    constructor
    intro
    infer_instance
  exact P.underObj.ind_inverseImage_le (Under.post F) _ hf

namespace ModuleCat

def flat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Flat R M

variable (R : Type u) [CommRing R]

@[simp]
lemma flat_iff (M : ModuleCat R) : flat R M ↔ Module.Flat R M :=
  .rfl

def faithfullyFlat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FaithfullyFlat R M

@[simp]
lemma faithfullyFlat_iff (M : ModuleCat R) : faithfullyFlat R M ↔ Module.FaithfullyFlat R M :=
  .rfl

open MonoidalCategory in
@[simp]
lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm (fun M ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  simp_rw [flat_iff] at h ⊢
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  intro C hC
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    { X₁ := pres.diag ⋙ tensorRight C.X₁
      X₂ := pres.diag ⋙ tensorRight C.X₂
      X₃ := pres.diag ⋙ tensorRight C.X₃
      f := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.f
      g := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.g
      zero := by simp [← CategoryTheory.Functor.whiskerLeft_comp, ← Functor.map_comp, C.zero] }
  apply colim.exact_mapShortComplex (S := S)
      (hc₁ := isColimitOfPreserves _ pres.isColimit)
      (hc₂ := isColimitOfPreserves _ pres.isColimit)
      (hc₃ := isColimitOfPreserves _ pres.isColimit)
  · rw [CategoryTheory.ShortComplex.exact_iff_evaluation]
    intro j
    exact Module.Flat.lTensor_shortComplex_exact (pres.diag.obj j) C hC
  · simp [S, whisker_exchange]
  · simp [S, whisker_exchange]

end ModuleCat

namespace CommRingCat

def surjectiveSpec : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ Function.Surjective (PrimeSpectrum.comap f)

@[simp]
lemma surjectiveSpec_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    surjectiveSpec f ↔ Function.Surjective (PrimeSpectrum.comap f.hom) := .rfl

def faithfullyFlat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.FaithfullyFlat

@[simp]
lemma faithfullyFlat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    faithfullyFlat f ↔ f.hom.FaithfullyFlat := .rfl

def flat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.Flat

@[simp]
lemma flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    flat f ↔ f.hom.Flat := .rfl

lemma faithfullyFlat_eq : faithfullyFlat = flat ⊓ surjectiveSpec := by
  ext X Y f
  simp only [faithfullyFlat_iff, RingHom.FaithfullyFlat.eq_and]
  rfl

def etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ f.Etale

@[simp]
lemma etale_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    etale f ↔ f.hom.Etale := .rfl

lemma etale_le_isFinitelyPresentable :
    etale.{u} ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} :=
  fun _ _ _ hf ↦ isFinitelyPresentable _ _ hf.2

instance : etale.IsStableUnderCobaseChange := by
  rw [etale, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Etale.isStableUnderBaseChange

instance : faithfullyFlat.IsStableUnderCobaseChange := by
  rw [faithfullyFlat, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.FaithfullyFlat.isStableUnderBaseChange

instance : etale.IsMultiplicative where
  id_mem R := .of_bijective Function.bijective_id
  comp_mem {R S T} f g hf hg := by
    apply RingHom.Etale.stableUnderComposition
    exact hf
    exact hg

instance : surjectiveSpec.IsMultiplicative where
  id_mem R := by simp [Function.surjective_id]
  comp_mem _ _ h1 h2 := by simpa using h1.comp h2

instance : faithfullyFlat.IsMultiplicative where
  id_mem _ := .of_bijective Function.bijective_id
  comp_mem _ _ := RingHom.FaithfullyFlat.stableUnderComposition _ _

lemma ind_flat_eq_flat : MorphismProperty.ind.{u} flat.{u} = flat := by
  refine le_antisymm (fun {R S} f hf ↦ ?_) (MorphismProperty.le_ind _)
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  algebraize [f.hom]
  suffices h : ObjectProperty.ind.{u} (ModuleCat.flat.{u} R) (ModuleCat.of R S) by
    rwa [ModuleCat.ind_flat] at h
  let F : Under R ⥤ ModuleCat R := (commAlgCatEquivUnder R).inverse ⋙
    forget₂ (CommAlgCat R) (AlgCat R) ⋙
    forget₂ (AlgCat R) (ModuleCat R)
  apply ObjectProperty.ind_inverseImage_le (F := F) (P := ModuleCat.flat.{u} R)
    (Under.mk f)
  exact hf

variable {J : Type*} [Category J] (D : J ⥤ CommRingCat.{u})

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance : MorphismProperty.PreIndSpreads.{u} etale.{u} := by
  refine .of_isInitial CommRingCat.isInitial fun R S f hf ↦ ?_
  algebraize [f.hom]
  have hf_eq : f = ofHom (algebraMap R S) := rfl
  have : Algebra.Etale R S := hf
  obtain ⟨R₀, S₀, _, _, hfg, h, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R S
  let g : S₀ →+* S := e.symm.toRingHom.comp <| Algebra.TensorProduct.includeRight.toRingHom
  algebraize [g]
  have : IsScalarTower R₀ S₀ ↑S := .of_algebraMap_eq fun x ↦ by
    simpa [RingHom.algebraMap_toAlgebra, g] using (e.symm.toAlgHom.commutes x.val).symm
  refine ⟨.of R₀, .of S₀, CommRingCat.ofHom (algebraMap R₀ R),
      CommRingCat.ofHom g, CommRingCat.ofHom (algebraMap R₀ S₀), ?_, ?_, ?_⟩
  · apply isFinitelyPresentable
    dsimp
    have : isInitial.to (of R₀) = ofHom ((algebraMap ℤ R₀).comp ULift.ringEquiv.toRingHom) :=
      isInitial.hom_ext _ _
    rw [this]
    apply RingHom.FinitePresentation.comp
    · rw [RingHom.finitePresentation_algebraMap, ← Algebra.FinitePresentation.of_finiteType]
      exact hfg.finiteType
    · exact .of_bijective ULift.ringEquiv.bijective
  · simpa [RingHom.etale_algebraMap]
  · rw [hf_eq, ← RingHom.algebraMap_toAlgebra g, isPushout_iff_isPushout]
    exact Algebra.IsPushout.of_equiv (S' := ↑R ⊗[↥R₀] S₀) e.symm rfl

instance (R : CommRingCat.{u}) : EssentiallySmall.{u} (MorphismProperty.Under etale ⊤ R) :=
  essentiallySmall_of_le (fun _ _ _ hf ↦ .of_finitePresentation hf.2) _

instance (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under (etale ⊓ faithfullyFlat) ⊤ R) :=
  essentiallySmall_of_le (fun _ _ _ hf ↦ .of_finitePresentation hf.1.2) _

instance (R : CommRingCat.{u}ᵒᵖ) :
    EssentiallySmall.{u} ((etale.op ⊓ faithfullyFlat.op).Over ⊤ R) := by
  let e : ((etale.op ⊓ faithfullyFlat.op).Over ⊤ R) ≌
      (MorphismProperty.Under (etale ⊓ faithfullyFlat) ⊤ R.unop)ᵒᵖ :=
    .rightOp <| .symm <| MorphismProperty.Under.equivOpOverOp _ _ _
  rw [essentiallySmall_congr e]
  infer_instance

end CommRingCat

open TensorProduct

lemma Module.FaithfullyFlat.of_nontrivial_tensor_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (H : ∀ (m : Ideal R), m.IsMaximal → Nontrivial ((R ⧸ m) ⊗[R] M)) :
    Module.FaithfullyFlat R M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.subsingleton_quotient_iff_eq_top, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.nontrivial_congr]
    exact H m hm

namespace CommAlgCat

variable {R : Type u} [CommRing R]

def flat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.flat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma flat_iff {S : CommAlgCat R} : flat R S ↔ Module.Flat R S := .rfl

def faithfullyFlat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.faithfullyFlat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma faithfullyFlat_iff {S : CommAlgCat R} :
    faithfullyFlat R S ↔ Module.FaithfullyFlat R S := .rfl

attribute [local ext high] Ideal.Quotient.algHom_ext in
/-- The functor of `R`-algebras sending `S` to `S ⧸ I S`. -/
def idealQuotient (I : Ideal R) :
    CommAlgCat R ⥤ CommAlgCat R where
  obj S := of R (S ⧸ I.map (algebraMap R S))
  map f := ofHom <| Ideal.quotientMapₐ _ f.hom <| by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.hom, Ideal.comap_comap]
    simpa using Ideal.le_comap_map

lemma ind_faithfullyFlat :
    ObjectProperty.ind.{u} (faithfullyFlat.{u} R) = faithfullyFlat.{u} R := by
  refine le_antisymm (fun S ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  simp only [faithfullyFlat_iff] at h
  rw [faithfullyFlat_iff]
  have : Module.Flat R S := by
    rw [← flat_iff, flat, ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
      ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨J, ‹_›, ‹_›, pres, fun j ↦ ?_⟩
    exact (h j).1
  refine Module.FaithfullyFlat.of_nontrivial_tensor_quotient fun m hm ↦ ?_
  let qpres : ColimitPresentation J (CommAlgCat.of R <| (R ⧸ m) ⊗[R] S) :=
    pres.map <| MonoidalCategory.tensorLeft (CommAlgCat.of R (R ⧸ m))
  have (j : J) : Nontrivial ((qpres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat).obj j) := by
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      MonoidalCategory.curriedTensor_obj_obj, forget₂_commRingCat_obj, coe_tensorObj,
      Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left, qpres]
    infer_instance
  change Nontrivial ((forget₂ _ CommRingCat).mapCocone qpres.cocone).pt
  exact CommRingCat.FilteredColimits.nontrivial (isColimitOfPreserves _ qpres.isColimit)

end CommAlgCat

namespace CommRingCat

lemma ind_faithfullyFlat_eq_faithfullyFlat :
    MorphismProperty.ind.{u} faithfullyFlat.{u} = faithfullyFlat.{u} := by
  refine le_antisymm (fun {R S} f hf ↦ ?_) (MorphismProperty.le_ind _)
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  algebraize [f.hom]
  suffices h : ObjectProperty.ind.{u} (CommAlgCat.faithfullyFlat.{u} R) (.of R S) by
    rwa [CommAlgCat.ind_faithfullyFlat] at h
  exact ObjectProperty.ind_inverseImage_le (F := (commAlgCatEquivUnder R).inverse)
    (P := CommAlgCat.faithfullyFlat.{u} R) (Under.mk f) hf

end CommRingCat
