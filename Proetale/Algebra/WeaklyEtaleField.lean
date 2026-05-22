/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.IndEtale

/-!
# Weakly étale algebras over a field
-/

universe u

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

namespace Algebra.WeaklyEtale

/-- Any weakly étale extension of fields is algebraic separable -/
lemma isAlgebraic {L : Type*} [Field L] [Algebra k L] [WeaklyEtale k L] : Algebra.IsSeparable k L :=
  sorry

/-- Any finitely-generated subalgebra of a weakly étale algebra is étale. -/
lemma etale_of_fg [WeaklyEtale k R] (A : Subalgebra k R) (hA : A.FG) : Etale k A :=
  sorry

variable (k R) in
/-- Any weakly étale algebra over a field is ind-étale. -/
theorem indEtale_field [WeaklyEtale k R] : IndEtale k R :=
  sorry

end Algebra.WeaklyEtale
