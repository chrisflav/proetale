/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# The small étale site is (pre)coherent
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Limits.ClosedUnderColimitsOfShape.discrete {ι : Type*} {P : ObjectProperty C}
    [P.IsClosedUnderIsomorphisms]
    (h : ∀ {f : ι → C} [HasColimit (Discrete.functor f)], (∀ j, P (f j)) → P (∐ f)) :
    ClosedUnderColimitsOfShape (Discrete ι) P := by
  refine closedUnderColimitsOfShape_of_colimit fun {F} _ hF ↦ ?_
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    hasColimit_of_iso Discrete.natIsoFunctor.symm
  rw [P.prop_iff_of_iso <| HasColimit.isoOfNatIso Discrete.natIsoFunctor]
  exact h fun j ↦ hF ⟨j⟩

instance (X : C) (P : MorphismProperty C) [P.RespectsIso] :
    ObjectProperty.IsClosedUnderIsomorphisms fun Y : Over X ↦ P Y.hom := by
  constructor
  intro Y Z e hY
  simpa [← P.cancel_left_of_respectsIso e.hom.left]

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (P : MorphismProperty Scheme.{u})

lemma IsLocalAtSource.closedUnderColimitsOfShape_discrete (J : Type*) [Small.{u} J]
    [IsLocalAtSource P] :
    ClosedUnderColimitsOfShape (Discrete J) (fun Y : Over X ↦ P Y.hom) := by
  refine Limits.ClosedUnderColimitsOfShape.discrete fun {f} _ hf ↦ ?_
  have : (PreservesCoproduct.iso (Over.forget X) _).inv ≫ (∐ f).hom =
      Sigma.desc fun j ↦ (f j).hom := by
    refine Limits.Sigma.hom_ext _ _ fun j ↦ ?_
    rw [PreservesCoproduct.inv_hom, Limits.ι_comp_sigmaComparison_assoc]
    simp
  rw [← P.cancel_left_of_respectsIso (PreservesCoproduct.iso (Over.forget X) _).inv, this]
  exact IsLocalAtSource.sigmaDesc hf

noncomputable instance IsLocalAtSource.createsColimitsOfShape_forget (J : Type*) [Small.{u} J]
    [IsLocalAtSource P] :
    CreatesColimitsOfShape (Discrete J) (MorphismProperty.Over.forget P ⊤ X) :=
  MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed _
    (IsLocalAtSource.closedUnderColimitsOfShape_discrete _ _ _)

noncomputable instance (J : Type*) [Small.{u} J] [IsLocalAtSource P] :
    HasCoproductsOfShape J (MorphismProperty.Over P ⊤ X) :=
  MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape _
    (IsLocalAtSource.closedUnderColimitsOfShape_discrete _ _ _)

noncomputable instance [IsLocalAtSource P] : HasFiniteCoproducts (MorphismProperty.Over P ⊤ X) where
  out := inferInstance

instance : FinitaryExtensive (Over X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget X)

instance [IsLocalAtSource P] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] :
    FinitaryExtensive (MorphismProperty.Over P ⊤ X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (MorphismProperty.Over.forget P ⊤ X)

instance (J : Type*) [Small.{u} J] : HasCoproductsOfShape J X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

noncomputable instance (J : Type*) [Small.{u} J] :
    CreatesColimitsOfShape (Discrete J) (Scheme.Etale.forget X) := by
  dsimp [Scheme.Etale.forget, Scheme.Etale]
  infer_instance

noncomputable instance : CreatesLimitsOfShape WalkingCospan (Scheme.Etale.forget.{u} X) :=
  CategoryTheory.MorphismProperty.Over.createsLimitsOfShape_walkingCospan _ _

instance : FinitaryExtensive X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

instance (X : Scheme) [Nonempty X] : Nontrivial Γ(X, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some ‹_›, trivial⟩⟩
  apply Scheme.component_nontrivial

lemma Scheme.exists_nontrivial_hom_of_nonempty (X : Scheme) [Nonempty X] :
    ∃ (Y : Scheme), Nontrivial (X ⟶ Y) := by
  refine ⟨𝔸(Unit; X), AffineSpace.homOfVector (𝟙 X) 0, AffineSpace.homOfVector (𝟙 X) 1, ?_⟩
  rw [ne_eq, AffineSpace.hom_ext_iff]
  simp

instance {X Y : Scheme} (f : X ⟶ Y) [Epi f] [Nonempty Y] [Subsingleton Y] : Surjective f := by
  by_contra h
  have : IsEmpty X := ⟨fun x ↦ h ⟨fun y ↦ ⟨x, Subsingleton.elim _ _⟩⟩⟩
  obtain ⟨Z, ⟨g₁, g₂, hne⟩⟩ := Y.exists_nontrivial_hom_of_nonempty
  apply hne
  rw [← cancel_epi f]
  apply isInitialOfIsEmpty.hom_ext _ _

@[simp]
lemma Scheme.Hom.apply_fiberι {X Y : Scheme} (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f.base ((f.fiberι y).base x) = y := by
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Scheme.Hom.range_fiberι]
  use x

/-- Universal effective epimorphisms in the category of schemes are surjective. -/
instance {X Y : Scheme} (f : X ⟶ Y)
    [∀ {Z} (g : Z ⟶ Y), EffectiveEpi (pullback.snd f g)] : Surjective f := by
  constructor
  intro y
  let g := Y.fromSpecResidueField y
  have h : Surjective (pullback.snd f g) := inferInstance
  obtain ⟨x, hx⟩ := h.1 default
  use (f.fiberι y).base x
  simp

instance : Preregular X.Etale :=
  sorry

end AlgebraicGeometry
