/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- This is the property of morphisms of schemes that are of the form `lim Xᵢ ⟶ S`
where each `Xᵢ` is absolutely affine and étale over `X`. -/
def proAffineEtale : MorphismProperty Scheme.{u} :=
  MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)

lemma proAffineEtale.of_isAffine {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [Etale f] :
    proAffineEtale f :=
  MorphismProperty.le_pro _ _ ⟨‹_›, ⟨‹_›, trivial⟩⟩

/-- Every pro-affine étale morphism is weakly-étale. -/
lemma proAffineEtale_le_weaklyEtale : proAffineEtale ≤ @WeaklyEtale :=
  sorry

instance : proAffineEtale.RespectsIso :=
  sorry

instance : proAffineEtale.HasOfPostcompProperty proAffineEtale :=
  sorry

instance : proAffineEtale.IsStableUnderComposition :=
  sorry

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    proAffineEtale.IsStableUnderBaseChangeAlong f := by
  rw [proAffineEtale]
  have : (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}).IsStableUnderBaseChangeAlong f := by
    constructor
    intro Z W f' g' g h ⟨h₁, h₂⟩
    refine ⟨MorphismProperty.of_isPullback h h₁, ?_⟩
    have : IsAffine Z := h₂.left
    have : IsAffineHom f' := MorphismProperty.of_isPullback h.flip ‹_›
    rw [ofObjectProperty_top_right_iff]
    exact isAffine_of_isAffineHom f'
  infer_instance

end AlgebraicGeometry
