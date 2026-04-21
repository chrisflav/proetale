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

@[simp]
lemma Scheme.Hom.generate_singleton_mem_fpqcTopology_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ fpqcTopology Y := by
  have : QuasiCompactCover (cover f ‹Flat f›).toPreZeroHypercover := by
    refine ⟨fun {U} hU ↦ .of_isOpenMap ?_ ?_ ?_ ?_ ?_⟩
    · intro
      exact f.continuous
    · intro
      exact f.isOpenMap
    · intro x hx
      use ⟨⟩
      exact f.surjective x
    · exact U.2
    · exact hU.isCompact
  rw [← Presieve.ofArrows_pUnit.{u}]
  exact (f.cover _).mem_propQCTopology

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) := by
  have : Flat (Spec.map f) := by
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)]
  infer_instance

/-- A quasi-compact flat cover is an effective epimorphism family. -/
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}}
    (𝒰 : Cover.{u} (precoverage @Flat) X)
    [QuasiCompactCover 𝒰.1] : EffectiveEpiFamily 𝒰.X 𝒰.f := by
  rw [← Sieve.effectiveEpimorphic_family]
  refine .of_subcanonical fpqcTopology _ ?_
  exact 𝒰.mem_propQCTopology

end AlgebraicGeometry
