import Mathlib.AlgebraicGeometry.Sites.BigZariski

universe u

open CategoryTheory

namespace AlgebraicGeometry

/--
The big Zariski site on the category of all `u`-schemes has sheafification in `Type u`.
This requires a refactor of sheafification in mathlib.
-/
instance : HasSheafify Scheme.zariskiTopology.{u} (Type u) := by
  sorry

end AlgebraicGeometry
