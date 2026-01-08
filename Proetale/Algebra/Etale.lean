/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Proetale.Algebra.FaithfullyFlat
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads

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

namespace CommRingCat

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
