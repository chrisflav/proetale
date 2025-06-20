/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Proetale.Mathlib.AlgebraicGeometry.Sites.BigZariski
import Proetale.Mathlib.CategoryTheory.Sites.Canonical

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

noncomputable
instance : CoproductsDisjoint Scheme.{u} where
  CoproductDisjoint X Y := sorry

/-- One possible proof is to embed into the category of Zariski sheaves. -/
instance : FinitaryExtensive Scheme.{u} := by
  let J := Scheme.zariskiTopology.{u}
  have : PreservesColimitsOfShape (Discrete WalkingPair) J.yoneda := sorry
  apply finitaryExtensive_of_preserves_and_reflects J.yoneda

instance : FinitaryExtensive AffineScheme.{u} := by
  let F : AffineScheme.{u} ⥤ Scheme.{u} := AffineScheme.forgetToScheme
  have : PreservesColimitsOfShape (Discrete WalkingPair) F := sorry
  apply finitaryExtensive_of_preserves_and_reflects F

end AlgebraicGeometry
