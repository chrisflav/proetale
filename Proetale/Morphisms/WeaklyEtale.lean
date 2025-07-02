/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Weakly étale morphisms

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes is said to be weakly étale if it is flat and the diagonal is flat. -/
@[mk_iff]
class WeaklyEtale {X Y : Scheme.{u}} (f : X ⟶ Y) extends Flat f where
  flat_diagonal : Flat (pullback.diagonal f)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace WeaklyEtale

lemma eq_inf :
    @WeaklyEtale = ((@Flat ⊓ MorphismProperty.diagonal @Flat) : MorphismProperty Scheme.{u}) := by
  ext X Y f
  rw [weaklyEtale_iff]
  rfl

instance : RespectsIso @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance isStableUnderComposition : IsStableUnderComposition @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance isStableUnderBaseChange : IsStableUnderBaseChange @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : IsLocalAtTarget @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : ContainsIdentities @WeaklyEtale := by
  rw [eq_inf]
  infer_instance

instance : IsMultiplicative @WeaklyEtale where

-- this is done in `Pi1`, but needs to be upstreamed to `mathlib`
instance (priority := 900) of_isEtale [IsEtale f] : WeaklyEtale f :=
  sorry

instance (priority := 900) etale [WeaklyEtale f] [LocallyOfFinitePresentation f] : IsEtale f :=
  sorry

end WeaklyEtale

end AlgebraicGeometry
