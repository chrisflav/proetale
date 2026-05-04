/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Additional constructors for `IsClosedUnderFiniteProducts`

We provide a constructor for `IsClosedUnderFiniteProducts`
from `IsClosedUnderLimitsOfShape (Discrete J)` for `(J : Type w) [Finite J]`
in an arbitrary universe `w`.
-/

universe w

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] {P : ObjectProperty C}

/-- To show `P.IsClosedUnderFiniteProducts`, it suffices to show
`P.IsClosedUnderLimitsOfShape (Discrete J)` for all finite `J` in a single universe. -/
lemma IsClosedUnderFiniteProducts.of_isClosedUnderLimitsOfShape_discrete
    (h : ∀ (J : Type w) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J)) :
    P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
    have := h (ULift.{w} (Fin n))
    exact .of_equivalence (Discrete.equivalence (Equiv.ulift.trans e.symm))

end CategoryTheory.ObjectProperty
