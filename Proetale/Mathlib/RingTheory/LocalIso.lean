/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.RingHomProperties
import Proetale.Algebra.LocalIso

/-!
# Stability properties of `RingHom.IsLocalIso`

This file records that `RingHom.IsLocalIso` is stable under base change and that the
associated `MorphismProperty` on `CommRingCat` is stable under cobase change and
composition.
-/

universe u

open CategoryTheory Limits

/-- `RingHom.IsLocalIso` is stable under base change. -/
lemma RingHom.IsLocalIso.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (fun {_ _} _ _ f => f.IsLocalIso) := by
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
