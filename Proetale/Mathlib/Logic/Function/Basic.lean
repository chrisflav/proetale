/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Logic.Function.Basic

/-!
# A left inverse of a bijection is bijective
-/

/-- A left inverse `f` of a bijection `g` is itself bijective. -/
theorem Function.bijective_of_leftInverse_of_bijective {α β : Type*} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (hg : Function.Bijective g) : Function.Bijective f :=
  ⟨h.injective, fun x ↦ ⟨g x, hg.injective (h (g x))⟩⟩
