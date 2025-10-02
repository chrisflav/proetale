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

@[simp]
lemma Scheme.Hom.generate_singleton_mem_fpqcTopology_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ fpqcTopology Y := by
  refine ⟨Presieve.singleton f, ?_, ?_⟩
  · refine ⟨f.cover ‹_›, ⟨fun {U} hU ↦ .of_isOpenMap ?_ ?_ ?_ ?_ ?_⟩, ?_⟩
    · intro
      exact f.continuous
    · intro
      exact f.isOpenMap
    · intro x hx
      use ⟨⟩
      exact f.surjective x
    · exact U.2
    · exact hU.isCompact
    · exact (ofArrows_homCover f _).symm
  · exact Sieve.le_generate _

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
instance subcanonical_fpqcTopology : fpqcTopology.Subcanonical := by
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
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}} (𝒰 : Cover.{u} @Flat X)
    [𝒰.QuasiCompact] : EffectiveEpiFamily 𝒰.X 𝒰.f := by
  rw [← Sieve.effectiveEpimorphic_family]
  refine .of_subcanonical fpqcTopology _ ?_
  exact 𝒰.generate_ofArrows_mem_qcTopology

/-- Any surjective, quasi-compact and flat morphism is an effective epimorphism. -/
instance {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [Surjective f] [Flat f] : EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]
  refine .of_subcanonical fpqcTopology _ ?_
  exact f.generate_singleton_mem_qcTopology ‹_›

/-- Any surjective, flat morphism locally of finite presentation is an effective epimorphism.
In particular, étale surjections satisfy this.-/
instance {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Surjective f] [Flat f] :
    EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]
  refine .of_subcanonical fpqcTopology _ ?_
  exact f.generate_singleton_mem_fpqcTopology_of_locallyOfFinitePresentation

end AlgebraicGeometry
