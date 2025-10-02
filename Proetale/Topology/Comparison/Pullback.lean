/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Pullbacks ...
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D]
  (F : C ⥤ D) (A : Type*) [Category A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]

variable [HasWeakSheafify K A] [∀ (G : Cᵒᵖ ⥤ A), F.op.HasPointwiseLeftKanExtension G]

instance [F.Faithful] [F.Full] :
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).unit := by
  dsimp [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  rw [NatTrans.isIso_iff_isIso_app]
  intro G
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J A)]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp
  apply IsIso.comp_isIso'
  infer_instance
  let x := F.op.whiskerLeft (toSheafify K (F.op.lan.obj G.val))
  have : Presheaf.IsSheaf K (F.op.lan.obj G.val) :=
    sorry
  have : IsIso (toSheafify K (F.op.lan.obj G.val)) := isIso_toSheafify K this
  infer_instance

lemma foo [F.Full] [F.Faithful] : IsIso (F.sheafAdjunctionContinuous A J K).unit :=
  --inferInstance
  sorry

end CategoryTheory
