/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.FromPi1.Etale
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty
import Proetale.Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Proetale.Mathlib.CategoryTheory.Limits.Comma
import Proetale.Topology.Flat.Sheaf
import Proetale.Topology.Coherent.Etale

/-!
# Affine étale site
-/

universe u

open CategoryTheory Opposite Limits

namespace CategoryTheory

section

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : D)

instance (J : Type*) [Category J] [IsConnected J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F]
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J (CostructuredArrow.toOver F X) where
  preservesLimit {K} := by
    have : PreservesLimitsOfShape J (CostructuredArrow.proj F X) := by
      infer_instance
    have : PreservesLimit K (CostructuredArrow.toOver F X ⋙ Over.forget X) := by
      show PreservesLimit K (CostructuredArrow.proj F X ⋙ F)
      infer_instance
    have : HasLimit (K ⋙ CostructuredArrow.toOver F X) := by
      infer_instance
    have : PreservesLimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) := by
      infer_instance
    have : ReflectsLimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    apply Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget X)

end

namespace MorphismProperty

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

protected abbrev CostructuredArrow (P : MorphismProperty D) (Q : MorphismProperty C) (F : C ⥤ D) (X : D) :=
  P.Comma F (Functor.fromPUnit.{0} X) Q ⊤

namespace CostructuredArrow

variable {P F X} in
@[simps left hom]
protected def mk {A : C} (f : F.obj A ⟶ X) (hf : P f) : P.CostructuredArrow Q F X where
  left := A
  right := ⟨⟨⟩⟩
  hom := f
  prop := hf

variable {P Q F X} in
@[simps left]
def homMk {A B : P.CostructuredArrow Q F X} (f : A.left ⟶ B.left) (hf : Q f)
    (w : F.map f ≫ B.hom = A.hom := by cat_disch) :
    A ⟶ B where
  left := f
  right := eqToHom (Subsingleton.elim _ _)
  prop_hom_left := hf
  prop_hom_right := trivial

variable {P Q F X} in
@[ext]
lemma Hom.ext {A B : P.CostructuredArrow Q F X} {f g : A ⟶ B} (h : f.left = g.left) :
    f = g := by
  ext <;> simp [h]

protected abbrev forget :
    P.CostructuredArrow Q F X ⥤ CategoryTheory.CostructuredArrow F X :=
  Comma.forget _ _ _ _ _

@[simps]
protected def toOver :
    P.CostructuredArrow ⊤ F X ⥤ P.Over ⊤ X where
  obj Y := Over.mk _ Y.hom Y.prop
  map f := Over.homMk (F.map f.left) _

instance [F.Faithful] : (CostructuredArrow.toOver P F X).Faithful := by
  constructor
  intro A B f g hfg
  ext
  exact F.map_injective congr($(hfg).left)

instance [F.Full] : (CostructuredArrow.toOver P F X).Full := by
  constructor
  intro A B f
  refine ⟨homMk (F.preimage f.left) trivial ?_, ?_⟩
  · simpa using f.w
  · ext; simp

variable [P.IsStableUnderBaseChange]
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  [PreservesLimitsOfShape WalkingCospan F] [HasPullbacks C] [HasPullbacks D]

lemma closedUnderLimitsOfShape_walkingCospan :
    ClosedUnderLimitsOfShape WalkingCospan (fun f : CostructuredArrow F X ↦ P f.hom) := by
  intro K c hc hf
  have h : IsPullback (F.map (c.π.app .left).left) (F.map (c.π.app .right).left)
      (F.map (K.map WalkingCospan.Hom.inl).left) (F.map (K.map WalkingCospan.Hom.inr).left) :=
    IsPullback.of_isLimit_cone <| isLimitOfPreserves
      (CategoryTheory.CostructuredArrow.toOver F X ⋙ CategoryTheory.Over.forget X) hc
  rw [show c.pt.hom = F.map (c.π.app .left).left ≫ (K.obj .left).hom by simp]
  apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hf _)
  exact P.of_postcomp _ (K.obj WalkingCospan.one).hom (hf .one) (by simpa using hf .right)

noncomputable
instance createsLimitsOfShape_walkingCospan [HasPullbacks C] [HasPullbacks D] :
    CreatesLimitsOfShape WalkingCospan (CostructuredArrow.forget P ⊤ F X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma F (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (CostructuredArrow F X)
  Comma.forgetCreatesLimitsOfShapeOfClosed P
    (closedUnderLimitsOfShape_walkingCospan P F X)

instance hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ F X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma F (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (CostructuredArrow F X)
  Comma.hasLimitsOfShape_of_closedUnderLimitsOfShape P
    (closedUnderLimitsOfShape_walkingCospan P F X)

instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P F X) := by
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    show PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end CostructuredArrow

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

section

@[simps! hom left]
def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

instance isCoverDense_toOver_Spec (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense
      (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} P U.left := U.left.affineCover.changeProp _
      (fun _ ↦ IsLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.J) : (𝒰.obj i).Over S := ⟨𝒰.map i ≫ U.hom⟩
    refine ⟨𝒰, ?_, ?_, ?_⟩
    · exact ⟨fun i ↦ inferInstance, fun i ↦ ⟨rfl⟩⟩
    · intro i
      apply P.comp_mem
      exact 𝒰.map_prop i
      exact U.prop
    · rintro X f ⟨i⟩
      simp only [Sieve.coverByImage]
      refine ⟨⟨affineOverMk (𝒰.map i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop), ?_, ?_, ?_⟩⟩
      · exact MorphismProperty.CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl
      · dsimp
        exact MorphismProperty.Over.homMk (𝒰.map i) (by simp) trivial
      · ext
        simp

variable {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative]
  [IsLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) :=
  sorry

instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S) :=
  sorry

instance : FinitaryExtensive (P.CostructuredArrow ⊤ Scheme.Spec S) :=
  CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S)

instance : Preregular (P.CostructuredArrow ⊤ Scheme.Spec S) := by
  apply Preregular.of_hasPullbacks_of_effectiveEpi_fst
  sorry

end

noncomputable
def Cover.etaleAffineRefinement (𝒰 : S.Cover @IsEtale) : S.AffineCover @IsEtale where
  J := (𝒰.bind fun j ↦ (𝒰.obj j).affineCover.changeProp _ (fun _ ↦ inferInstance)).J
  obj _ := _
  map := (𝒰.bind fun j => (𝒰.obj j).affineCover.changeProp _ fun _ ↦ inferInstance).map
  f := (𝒰.bind fun j => (𝒰.obj j).affineCover.changeProp _ fun _ ↦ inferInstance).f
  covers := (𝒰.bind fun j => (𝒰.obj j).affineCover.changeProp _ fun _ ↦ inferInstance).covers
  map_prop j := by
    simp [Cover.changeProp]
    have : IsEtale (𝒰.map j.fst) := 𝒰.map_prop _
    infer_instance

def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @IsEtale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

@[simps!]
protected def mk {R : CommRingCat} (f : Spec R ⟶ S) [IsEtale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

instance : Category S.AffineEtale :=
  inferInstanceAs <| Category (MorphismProperty.CostructuredArrow _ _ _ _)

@[simps! obj_left obj_hom map_left]
protected noncomputable def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance : (AffineEtale.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

instance : (AffineEtale.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (smallGrothendieckTopology _)

variable (S) in
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology (smallEtaleTopology S)

/-- The category of sheafs on the small, affine étale site is equivalent to the category of
sheafs on the small étale site. -/
noncomputable def sheafEquiv (A : Type*) [Category A]
    [∀ (X : S.Etaleᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow X (AffineEtale.Spec S).op) A] :
    Sheaf (AffineEtale.topology S) A ≌ Sheaf (smallEtaleTopology S) A :=
  (AffineEtale.Spec S).sheafInducedTopologyEquivOfIsCoverDense _ _

instance : (AffineEtale.Spec S).ReflectsEffectiveEpis :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).ReflectsEffectiveEpis

instance effectiveEpi_of_surjective {S : Scheme} {X Y : S.AffineEtale} (f : X ⟶ Y)
    [Surjective (Spec.map f.left.unop)] : EffectiveEpi f := by
  apply (AffineEtale.Spec S).effectiveEpi_of_map
  have : Surjective ((AffineEtale.Spec S).map f).left := ‹_›
  infer_instance

instance : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

-- Question: What are the effective epimorphisms of `AffineEtale S`?

instance preregular : Preregular (AffineEtale S) := by
  sorry

instance precoherent : Precoherent (AffineEtale S) :=
  sorry

end AffineEtale

end Scheme

end AlgebraicGeometry
