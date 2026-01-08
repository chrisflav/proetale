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

end CategoryTheory
