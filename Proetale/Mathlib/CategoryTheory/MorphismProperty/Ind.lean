/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## TODOs:

- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

universe s t w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

instance (X : C) [HasFilteredColimits C] : ReflectsFilteredColimits (Under.forget X) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms

open Opposite

namespace MorphismProperty

variable {P}

/--
Let `P` be a property of morphisms. `P.Pro` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : Xᵢ ⟶ Y` and `sᵢ : X ⟶ Xᵢ` indexed by `J`
such that
- `J` is cofiltered
- `X = lim Xᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = sᵢ ≫ tᵢ` for all `i`.
-/
def pro (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCofiltered J)
    (D : J ⥤ C) (t : D ⟶ (Functor.const J).obj Y) (s : (Functor.const J).obj X ⟶ D)
    (_ : IsLimit (Cone.mk _ s)), ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

lemma pro_eq_unop_ind_op : pro.{w} P = (ind.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, isColimitOfUnop hs, fun j ↦ ⟨(hst j.1).1, by simp [← (hst j.1).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isLimitOfCoconeRightOpOfCone D.leftOp hs, fun j ↦ ⟨(hst _).1,
      op_injective (hst _).2⟩⟩

end CategoryTheory.MorphismProperty
