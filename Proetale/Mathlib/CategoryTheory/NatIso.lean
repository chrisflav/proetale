import Mathlib.CategoryTheory.NatIso

namespace CategoryTheory

/-- Naturality of pointwise inverses: if components of a natural transformation are isos,
the inverses satisfy a naturality condition. -/
lemma NatTrans.naturality_inv {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (α : F ⟶ G)
    {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)] [IsIso (α.app Y)] :
    inv (α.app X) ≫ F.map f = G.map f ≫ inv (α.app Y) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact α.naturality f

end CategoryTheory
