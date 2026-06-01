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

instance (J : Type*) [Category J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [HasColimitsOfShape J (Over X)] [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J (CostructuredArrow.toOver F X) where
  preservesColimit {K} := by
    have : PreservesColimitsOfShape J (CostructuredArrow.proj F X) := by
      infer_instance
    have : PreservesColimit K (CostructuredArrow.toOver F X ⋙ Over.forget X) := by
      change PreservesColimit K (CostructuredArrow.proj F X ⋙ F)
      infer_instance
    have : HasColimit (K ⋙ CostructuredArrow.toOver F X) := by
      infer_instance
    have : PreservesColimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) := by
      infer_instance
    have : ReflectsColimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    apply Limits.preservesColimit_of_reflects_of_preserves _ (Over.forget X)

end

namespace MorphismProperty

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

namespace CostructuredArrow

section Limits

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

end Limits

section Colimits

variable (J : Type*) [Category J] [HasColimitsOfShape J C] [HasColimitsOfShape J D]
  [HasColimitsOfShape J (P.Over ⊤ X)] [PreservesColimitsOfShape J F]
  [(MorphismProperty.commaObj F (Functor.fromPUnit X) P).IsClosedUnderColimitsOfShape J]

instance : PreservesColimitsOfShape J (CostructuredArrow.toOver P F X) := by
  have : CreatesColimitsOfShape J (CostructuredArrow.forget P ⊤ F X) :=
    MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
      (L := F) (R := .fromPUnit X) (P := P) (J := J)
  have : PreservesColimitsOfShape J
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    change PreservesColimitsOfShape J <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end Colimits

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

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete_commaObj
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (MorphismProperty.commaObj L (Functor.fromPUnit.{0} X) P).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete L X

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out _ := inferInstance

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
