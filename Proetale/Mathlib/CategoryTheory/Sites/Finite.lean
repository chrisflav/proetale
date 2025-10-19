import Mathlib.CategoryTheory.Sites.Finite

namespace CategoryTheory

variable {C : Type*} [Category C]

instance : (Precoverage.finite C).IsStableUnderSup where
  sup_mem_coverings hR hS := hR.union hS

end CategoryTheory
