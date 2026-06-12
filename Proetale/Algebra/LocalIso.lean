/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Proetale.Mathlib.RingTheory.RingHom.OpenImmersion

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra.IsLocalIso

instance refl : IsLocalIso R R := inferInstance

end Algebra.IsLocalIso

section Flat

universe v w

/-- A standard open immersion is flat, since it is a localization. -/
lemma Module.Flat.of_isStandardOpenImmersion
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardOpenImmersion R S] : Module.Flat R S := by
  obtain ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R S
  exact IsLocalization.flat S (Submonoid.powers r)

/-- A local isomorphism is flat, since it is locally a localization. -/
lemma Algebra.IsLocalIso.flat
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] : Module.Flat R S := by
  refine Module.flat_of_isLocalized_span S S
    {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top _ _)
    (fun g ↦ Localization.Away g.1)
    (fun g ↦ Algebra.linearMap S (Localization.Away g.1)) fun ⟨g, hg⟩ ↦ by
      letI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
      exact Module.Flat.of_isStandardOpenImmersion R (Localization.Away g)

end Flat

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)", algebraize]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

/-- A bijective ring homomorphism is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective hf
  change Algebra.IsLocalIso R S
  infer_instance

/-- The composition of local isomorphisms is a local isomorphism. -/
lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso

/-- `RingHom.IsLocalIso` is stable under base change. -/
lemma RingHom.IsLocalIso.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsLocalIso := by
  refine RingHom.IsStableUnderBaseChange.mk RingHom.IsLocalIso.respectsIso ?_
  intro R S T _ _ _ _ _ hRT
  rw [RingHom.isLocalIso_algebraMap] at hRT ⊢
  infer_instance

namespace CategoryTheory.MorphismProperty

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under cobase change. -/
instance isLocalIso_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange := by
  rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.IsLocalIso.isStableUnderBaseChange

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under composition. -/
instance isLocalIso_isStableUnderComposition :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition where
  comp_mem _ _ hf hg := hg.comp hf

end CategoryTheory.MorphismProperty
