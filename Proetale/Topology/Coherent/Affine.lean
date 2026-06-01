/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.FromPi1.Etale
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
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
      change PreservesLimit K (CostructuredArrow.proj F X ⋙ F)
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

instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P F X) := by
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    change PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end CostructuredArrow

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

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

/-- `CostructuredArrow.toOver Scheme.Spec S` preserves binary coproducts. This follows because
`proj ⋙ Spec` preserves coproducts and `Over.forget S` reflects them. -/
noncomputable instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S) := by
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S ⋙
        CategoryTheory.Over.forget S) := by
    change PreservesColimitsOfShape (Discrete WalkingPair) <|
      CategoryTheory.CostructuredArrow.proj Scheme.Spec S ⋙ Scheme.Spec
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (CategoryTheory.Over.forget S)

instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S) := by
  haveI : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) := by
    apply IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
  haveI : CreatesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec S) :=
    MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
      (L := Scheme.Spec) (R := Functor.fromPUnit S) P (Discrete WalkingPair)
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S ⋙
        MorphismProperty.Over.forget P ⊤ S) := by
    change PreservesColimitsOfShape (Discrete WalkingPair) <|
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
  sorry

noncomputable
def Cover.etaleAffineRefinement (𝒰 : S.Cover (precoverage @Etale)) :
    S.AffineCover @Etale where
  I₀ := (𝒰.bind fun j ↦ (𝒰.X j).affineCover.changeProp (fun _ ↦ inferInstance)).I₀
  X _ := _
  f := (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance).f
  idx := Cover.idx (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  covers := Cover.covers (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  map_prop j := by
    simp only [Cover.changeProp]
    have : Etale (𝒰.f j.fst) := 𝒰.map_prop _
    infer_instance

namespace AffineEtale

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
