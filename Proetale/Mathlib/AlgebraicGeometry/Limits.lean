/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Limits

/-!
# Named alias: the category of schemes is finitary extensive

This file provides a `theorem`-shaped, stably-named alias for the anonymous Mathlib
instance `FinitaryExtensive Scheme` in `Mathlib/AlgebraicGeometry/Limits.lean`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The category of schemes is finitary extensive. -/
theorem finitaryExtensive : FinitaryExtensive Scheme.{u} := inferInstance

end AlgebraicGeometry.Scheme
