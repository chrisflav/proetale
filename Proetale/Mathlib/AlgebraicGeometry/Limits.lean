/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Limits

/-!
# `FinitaryExtensive` for the category of schemes
-/

universe u

namespace AlgebraicGeometry

/-- The category of schemes is finitary extensive. -/
lemma finitaryExtensive_scheme : CategoryTheory.FinitaryExtensive Scheme.{u} := inferInstance

end AlgebraicGeometry
