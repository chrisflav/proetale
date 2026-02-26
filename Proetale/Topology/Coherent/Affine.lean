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

namespace CostructuredArrow

variable [P.IsStableUnderBaseChange]
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  [PreservesLimitsOfShape WalkingCospan F] [HasPullbacks C] [HasPullbacks D]

lemma closedUnderLimitsOfShape_walkingCospan :
    (P.costructuredArrowObj F (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (F.map (pres.π.app .left).left) (F.map (pres.π.app .right).left)
        (F.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (F.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <| isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver F X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [costructuredArrowObj_iff]
    have hw1 : Y.hom = F.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom := by
      have := (pres.π.app WalkingCospan.left).w
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this.symm
    rw [hw1]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    have hw2 : F.map (pres.diag.map WalkingCospan.Hom.inr).left ≫
        (pres.diag.obj WalkingCospan.one).hom = (pres.diag.obj WalkingCospan.right).hom := by
      have := (pres.diag.map WalkingCospan.Hom.inr).w
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
      exact this
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (hw2 ▸ hpres .right)

noncomputable
instance createsLimitsOfShape_walkingCospan [HasPullbacks C] [HasPullbacks D] :
    CreatesLimitsOfShape WalkingCospan (CostructuredArrow.forget P ⊤ F X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma F (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (CostructuredArrow F X)
  have : (commaObj F (Functor.fromPUnit X) P).IsClosedUnderLimitsOfShape WalkingCospan := by
    apply closedUnderLimitsOfShape_walkingCospan
  Comma.forgetCreatesLimitsOfShapeOfClosed P

instance hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ F X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma F (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (CostructuredArrow F X)
  have : (commaObj F (Functor.fromPUnit X) P).IsClosedUnderLimitsOfShape WalkingCospan := by
    apply closedUnderLimitsOfShape_walkingCospan
  Comma.hasLimitsOfShape_of_closedUnderLimitsOfShape P

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
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense
      (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    refine ⟨𝒰, ?_, ?_, ?_⟩
    · exact ⟨fun i ↦ inferInstance, fun i ↦ ⟨rfl⟩⟩
    · intro i
      apply P.comp_mem
      exact 𝒰.map_prop i
      exact U.prop
    · rintro X f ⟨i⟩
      simp only [Sieve.coverByImage]
      refine ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop), ?_, ?_, ?_⟩⟩
      · exact MorphismProperty.CostructuredArrow.homMk (𝟙 _) ⟨⟩ (Category.id_comp _)
      · dsimp
        exact MorphismProperty.Over.homMk (𝒰.f i) (by simp) trivial
      · ext; dsimp; exact Category.id_comp _

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape ?_ ?_ ?_ _
  · intro D _
    exact Sigma.cocone _
  · intro D
    exact coproductIsCoproduct' _
  · intro D _ X s h
    exact IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) := by
      apply IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

/-- `CostructuredArrow.toOver Scheme.Spec S` preserves binary coproducts.
This follows because `proj ⋙ Spec` preserves coproducts (as `proj` creates and `Spec`
preserves), `Over.forget S` reflects colimits (since it creates them), and
`toOver ⋙ Over.forget = proj ⋙ Spec`. -/
noncomputable instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S) := by
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S ⋙
        CategoryTheory.Over.forget S) := by
    show PreservesColimitsOfShape (Discrete WalkingPair) <|
      CategoryTheory.CostructuredArrow.proj Scheme.Spec S ⋙ Scheme.Spec
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (CategoryTheory.Over.forget S)

instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S) := by
  haveI : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) := by
    apply IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
  haveI : HasColimitsOfShape (Discrete WalkingPair)
      (P.CostructuredArrow ⊤ Scheme.Spec S) := inferInstance
  haveI : HasColimitsOfShape (Discrete WalkingPair)
      (Comma Scheme.Spec (Functor.fromPUnit S)) :=
    inferInstanceAs <| HasColimitsOfShape _ (CostructuredArrow Scheme.Spec S)
  haveI : CreatesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec S) :=
    MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
      (L := Scheme.Spec) (R := Functor.fromPUnit S) P (Discrete WalkingPair)
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S ⋙
        MorphismProperty.Over.forget P ⊤ S) := by
    show PreservesColimitsOfShape (Discrete WalkingPair) <|
      MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec S ⋙
        CategoryTheory.CostructuredArrow.toOver Scheme.Spec S
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (MorphismProperty.Over.forget P ⊤ S)

instance : FinitaryExtensive (P.CostructuredArrow ⊤ Scheme.Spec S) :=
  CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S)

instance : Preregular (P.CostructuredArrow ⊤ Scheme.Spec S) := by
  apply Preregular.of_hasPullbacks_of_effectiveEpi_fst
  intro X Y Z f g hg
  let F := MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S
  -- The key step: show the underlying scheme map of g is surjective.
  -- This requires: EffectiveEpi g in P.CostructuredArrow → Surjective (F.map g).left
  -- which is non-trivial in general.
  haveI hsur_g : Surjective (F.map g).left := by
    sorry
  -- Show the underlying scheme morphism of pullback.fst in the Over category is surjective.
  haveI : Surjective (pullback.fst (F.map f) (F.map g)).left := by
    show Surjective ((MorphismProperty.Over.forget P ⊤ S ⋙ CategoryTheory.Over.forget S).map
      (pullback.fst (F.map f) (F.map g)))
    rw [← pullbackComparison_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Surjective) _ _).mpr (by
      dsimp
      haveI : Surjective ((CategoryTheory.Over.forget S).map
        ((MorphismProperty.Over.forget P ⊤ S).map (F.map g))) := hsur_g
      infer_instance)
  -- pullback.fst in Over category is EffectiveEpi (from Surjective → EffectiveEpi)
  -- NOTE: This step needs EffectiveEpi from Surjective for general P, which may not hold.
  -- For P = @Etale, this is Scheme.Etale.effectiveEpi_of_surjective.
  haveI : EffectiveEpi (pullback.fst (F.map f) (F.map g)) := by
    sorry
  -- F preserves pullbacks and reflects effective epis, so transfer back
  apply F.effectiveEpi_of_map
  rw [show F.map (pullback.fst f g) =
    (PreservesPullback.iso F f g).hom ≫ pullback.fst (F.map f) (F.map g)
    from (PreservesPullback.iso_hom_fst F f g).symm]
  infer_instance

end

noncomputable
def Cover.etaleAffineRefinement (𝒰 : S.Cover (precoverage @Etale)) :
    S.AffineCover @Etale where
  I₀ := (𝒰.bind fun j ↦ (𝒰.X j).affineCover.changeProp (fun _ ↦ inferInstance)).I₀
  X _ := _
  f := (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance).f
  idx := Cover.idx (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  covers := Cover.covers (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  map_prop j := by
    simp [Cover.changeProp]
    have : IsOpenImmersion ((𝒰.X j.fst).affineCover.f j.snd) := inferInstance
    have : Etale (𝒰.f j.fst) := 𝒰.map_prop _
    exact MorphismProperty.comp_mem _ _ _ (IsZariskiLocalAtSource.of_isOpenImmersion _) ‹_›

def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

@[simps!]
protected def mk {R : CommRingCat} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
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
noncomputable def topology : GrothendieckTopology S.AffineEtale :=
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
-- See blueprint remark:et-not-precoherent-topology for discussion.
-- The `Preregular` instance for the general `P.CostructuredArrow ⊤ Scheme.Spec S`
-- (defined above, with sorry for the key surjectivity step) provides this.

instance preregular : Preregular (AffineEtale S) :=
  inferInstanceAs <| Preregular (MorphismProperty.CostructuredArrow _ _ _ _)

instance precoherent : Precoherent (AffineEtale S) :=
  inferInstanceAs <| Precoherent (MorphismProperty.CostructuredArrow _ _ _ _)

end AffineEtale

end Scheme

end AlgebraicGeometry
