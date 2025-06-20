/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Proetale.Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Proetale.Topology.Flat.QuasiCompactTopology

/-!
# The fpqc topology is subcanonical

In this file we show that the fqpc topology of a scheme is subcanonical. This implies that
all coarser topologies, e.g., the (pro)étale topology, are subcanonical.
-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}}

open Scheme

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

open Opposite

variable {P}

abbrev fpqcPretopology : Pretopology Scheme.{u} := qcPretopology @Flat

/-- The fpqc-topology on the category of schemes is the Grothendieck topology associated
to the pretopology given by fpqc-covers. -/
abbrev fpqcTopology : GrothendieckTopology Scheme.{u} := fpqcPretopology.toGrothendieck

lemma isSheaf_fpqcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf fpqcTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (_ : f.hom.Flat) (_ : Surjective (Spec.map f)),
          Presieve.IsSheafFor F (Presieve.singleton (Spec.map f)) := by
  rw [isSheaf_qcTopology_iff]
  congr!
  exact HasRingHomProperty.Spec_iff

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) := by
  constructor
  constructor
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry

/-- The fpqc topology is subcanonical. -/
instance : fpqcTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
  rw [isSheaf_fpqcTopology_iff (yoneda.obj X)]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)
  · intro R S f hf hs
    revert X
    rw [← Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda,
      Sieve.effectiveEpimorphic_singleton]
    exact effectiveEpi_of_flat _ hf hs

/-- A quasi-compact flat cover is an effective epimorphism family. -/
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}} (𝒰 : X.Cover @Flat)
    [𝒰.QuasiCompact] : EffectiveEpiFamily 𝒰.obj 𝒰.map :=
  -- immediate consequence of fqpc subcanonical
  sorry

end AlgebraicGeometry
