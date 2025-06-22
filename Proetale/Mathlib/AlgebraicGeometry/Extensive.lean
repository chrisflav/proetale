/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Proetale.Mathlib.AlgebraicGeometry.Sites.BigZariski
import Proetale.Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] {A B : Type*} [Category A] [Category B]
  (J : GrothendieckTopology C) (F : A ⥤ B) [J.HasSheafCompose F]

-- this does not help unfortunately
instance (K : Type*) [Category K] [PreservesLimitsOfShape K F] [HasLimitsOfShape K A]
    [HasSheafify J A] :
    PreservesLimitsOfShape K (sheafCompose J F) :=
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs <| PreservesLimitsOfShape K
      (sheafToPresheaf J A ⋙ (whiskeringRight Cᵒᵖ A B).obj F)
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J B)

end CategoryTheory

namespace AlgebraicGeometry

noncomputable
instance : CoproductsDisjoint Scheme.{u} where
  CoproductDisjoint X Y := sorry

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
instance : HasSheafify Scheme.zariskiTopology.{u} (Type (u + 1)) := inferInstance

/-- One possible proof is to embed into the category of Zariski sheaves. -/
instance : FinitaryExtensive Scheme.{u} := by
  let J := Scheme.zariskiTopology.{u}
  let G : Type u ⥤ Type (u + 1) := uliftFunctor.{u + 1}
  let F : Scheme.{u} ⥤ Sheaf J (Type (u + 1)) :=
    J.yoneda ⋙ sheafCompose _ G
  have : PreservesColimitsOfShape (Discrete WalkingPair) J.yoneda :=
    sorry
  have : PreservesPullbacksOfInclusions F :=
    sorry
  have : PreservesColimitsOfShape (Discrete WalkingPair) F :=
    sorry
  apply finitaryExtensive_of_preserves_and_reflects F

instance : FinitaryExtensive AffineScheme.{u} := by
  let F : AffineScheme.{u} ⥤ Scheme.{u} := AffineScheme.forgetToScheme
  have : PreservesColimitsOfShape (Discrete WalkingPair) F := sorry
  apply finitaryExtensive_of_preserves_and_reflects F

end AlgebraicGeometry
