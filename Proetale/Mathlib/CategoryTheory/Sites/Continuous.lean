import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Whiskering

namespace CategoryTheory

open Opposite

variable {C D : Type*} [Category* C] [Category D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : C ⥤ D) (R : D ⥤ C)
  {A : Type*} [Category A]

@[simps]
def Adjunction.sheaf [L.IsContinuous J K] [R.IsContinuous K J] (adj : L ⊣ R) :
    L.sheafPushforwardContinuous A J K ⊣ R.sheafPushforwardContinuous A K J where
  unit.app F := ⟨(adj.op.whiskerLeft A).unit.app F.val⟩
  counit.app F := ⟨(adj.op.whiskerLeft A).counit.app F.val⟩
  right_triangle_components F := by
    ext1
    exact (adj.op.whiskerLeft A).right_triangle_components F.val
  left_triangle_components F := by
    ext1
    exact (adj.op.whiskerLeft A).left_triangle_components F.val

end CategoryTheory
