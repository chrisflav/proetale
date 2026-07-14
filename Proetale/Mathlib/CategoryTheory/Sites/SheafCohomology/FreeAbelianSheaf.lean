/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Free abelian sheaves on objects of a site

For a site `(C, J)` we define the free abelian sheaf functor sending `U : C` to the
sheafification of the free abelian group presheaf on the (universe-lifted) presheaf
represented by `U`. This is the composite appearing in mathlib's
`Sheaf.cohomologyPresheafFunctor`, in a universe setting where the coefficients live
one universe above the morphisms of `C`.

We provide the basic "sections" adjunction: morphisms from the free abelian sheaf on `U`
to a sheaf `F` are in bijection with the sections of `F` over `U`.
-/

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C]
variable (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{u + 1}]

/-- The free abelian sheaf functor, sending `U : C` to the sheafification of the
free abelian group presheaf on the (universe-lifted) presheaf represented by `U`.
This is the composite appearing in `Sheaf.cohomologyPresheafFunctor`. -/
noncomputable def freeAbelianSheafFunctor : C ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf J _

variable {J}

/-- Morphisms from the free abelian sheaf on `U` to a sheaf `F` are sections of `F`
over `U`. -/
noncomputable def freeAbelianSheafHomEquiv {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}} :
    ((freeAbelianSheafFunctor J).obj U ⟶ F) ≃
      ((sheafToPresheaf J _).obj F ⋙ forget AddCommGrpCat.{u + 1}).obj (op U) :=
  ((sheafificationAdjunction J _).homEquiv _ _).trans <|
    (((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj.{u + 1}).homEquiv _ _).trans
      uliftYonedaEquiv)

end CategoryTheory
