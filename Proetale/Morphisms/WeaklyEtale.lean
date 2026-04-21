/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Limits
import Proetale.FromPi1.Etale
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Weakly étale morphisms

-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace WeaklyEtale

instance (priority := 900) etale [WeaklyEtale f] [LocallyOfFinitePresentation f] : Etale f :=
  sorry

end WeaklyEtale

end AlgebraicGeometry
