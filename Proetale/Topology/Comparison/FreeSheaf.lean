/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.FreeAbelianSheaf
import Definitions

/-!
# Pullback of free abelian sheaves along the inclusion of the étale site

We show that the sheaf pullback along `toProEtale S : S.Etale ⥤ S.ProEt` is compatible
with forming free abelian sheaves on representable presheaves, and that it sends
constant sheaves to constant sheaves.

The main results are:

- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackCompFreeIso`: pulling back the free abelian
  sheaf on `U : S.Etale` yields the free abelian sheaf on `(toProEtale S).obj U`,
  functorially in `U`.
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackConstantIso`: pulling back the constant
  sheaf with values `M` yields the constant sheaf with values `M`.

All isomorphisms are obtained from uniqueness of left adjoints, via
`CategoryTheory.conjugateIsoEquiv`.
-/

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D]

variable (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K]

section Presheaf

variable (A : Type*) [Category A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ F : Cᵒᵖ ⥤ A, G.op.HasLeftKanExtension F]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The underlying presheaf of the pushforward of a sheaf is the restriction of its
underlying presheaf, functorially. -/
def sheafPushforwardContinuousCompSheafToPresheafIso :
    G.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- Sheafification commutes with pullback of (pre)sheaves: sheafifying and then pulling
back is the same as left Kan extending and then sheafifying. -/
noncomputable def presheafToSheafCompSheafPullbackIso :
    presheafToSheaf J A ⋙ G.sheafPullback A J K ≅ G.op.lan ⋙ presheafToSheaf K A :=
  ((conjugateIsoEquiv
      ((sheafificationAdjunction J A).comp (G.sheafAdjunctionContinuous A J K))
      ((G.op.lanAdjunction A).comp (sheafificationAdjunction K A))).symm
    (sheafPushforwardContinuousCompSheafToPresheafIso G J K A)).symm

end Presheaf

section Free

variable [∀ F : Cᵒᵖ ⥤ Type (u + 1), G.op.HasLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}, G.op.HasLeftKanExtension F]

/-- Forming free abelian group presheaves commutes with left Kan extension. -/
noncomputable def whiskeringFreeCompLanIso :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free.{u + 1} ⋙ G.op.lan ≅
      G.op.lan ⋙ (Functor.whiskeringRight Dᵒᵖ _ _).obj AddCommGrpCat.free.{u + 1} :=
  ((conjugateIsoEquiv
      ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).comp (G.op.lanAdjunction _))
      ((G.op.lanAdjunction _).comp (Adjunction.whiskerRight Dᵒᵖ AddCommGrpCat.adj))).symm
    (NatIso.ofComponents fun _ ↦ Iso.refl _)).symm

variable [HasWeakSheafify J AddCommGrpCat.{u + 1}] [HasWeakSheafify K AddCommGrpCat.{u + 1}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).IsRightAdjoint]

/-- The free abelian sheaf functor commutes with sheaf pullback. -/
noncomputable def freeAbelianSheafFunctorCompSheafPullbackIso :
    freeAbelianSheafFunctor J ⋙ G.sheafPullback AddCommGrpCat.{u + 1} J K ≅
      G ⋙ freeAbelianSheafFunctor K :=
  Functor.isoWhiskerLeft
      (uliftYoneda.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
      (presheafToSheafCompSheafPullbackIso G J K _) ≪≫
    Functor.isoWhiskerLeft uliftYoneda.{u + 1}
      (Functor.isoWhiskerRight (whiskeringFreeCompLanIso G) (presheafToSheaf K _)) ≪≫
    Functor.isoWhiskerRight (Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1} G).symm
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf K _)

end Free

section Constant

variable (A : Type*) [Category A] [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))

/-- If `G` preserves the terminal object, the constant sheaf functor commutes with
sheaf pullback along `G`. -/
noncomputable def constantSheafCompSheafPullbackIso :
    constantSheaf J A ⋙ G.sheafPullback A J K ≅ constantSheaf K A :=
  ((conjugateIsoEquiv
      ((constantSheafAdj J A hT).comp (G.sheafAdjunctionContinuous A J K))
      (constantSheafAdj K A hT')).symm
    (NatIso.ofComponents fun _ ↦ Iso.refl _)).symm

end Constant

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace ProEt

/-- Pulling back free abelian sheaves on the small étale site of `S` to the pro-étale
site of `S` yields free abelian sheaves, functorially. -/
noncomputable def sheafPullbackCompFreeIso :
    freeAbelianSheafFunctor (smallEtaleTopology S) ⋙
        ProEt.sheafPullback S AddCommGrpCat.{u + 1} ≅
      toProEtale S ⋙ freeAbelianSheafFunctor (ProEt.topology S) :=
  freeAbelianSheafFunctorCompSheafPullbackIso (toProEtale S) _ _

/-- The pullback of the free abelian sheaf on `U : S.Etale` to the pro-étale site of `S`
is the free abelian sheaf on `(toProEtale S).obj U`. -/
noncomputable def sheafPullbackFreeIso (U : S.Etale) :
    (ProEt.sheafPullback S AddCommGrpCat.{u + 1}).obj
        ((freeAbelianSheafFunctor (smallEtaleTopology S)).obj U) ≅
      (freeAbelianSheafFunctor (ProEt.topology S)).obj ((toProEtale S).obj U) :=
  (sheafPullbackCompFreeIso S).app U

/-- `S` with the identity is a terminal object of the small étale site of `S`. -/
noncomputable def isTerminalMkId :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 S) (MorphismProperty.id_mem _ S) : S.Etale) :=
  MorphismProperty.Over.mkIdTerminal _ _

/-- The image of the terminal object of the small étale site of `S` in the pro-étale
site of `S` is terminal. -/
noncomputable def isTerminalMkIdProEt :
    IsTerminal ((toProEtale S).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 S) (MorphismProperty.id_mem _ S))) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale S

/-- Pulling back constant sheaves on the small étale site of `S` to the pro-étale site
of `S` yields constant sheaves, functorially. -/
noncomputable def sheafPullbackCompConstantIso :
    constantSheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1} ⋙
        ProEt.sheafPullback S AddCommGrpCat.{u + 1} ≅
      constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  constantSheafCompSheafPullbackIso (toProEtale S) _ _ _
    (isTerminalMkId S) (isTerminalMkIdProEt S)

/-- The pullback of the constant sheaf with values `M` on the small étale site of `S`
to the pro-étale site of `S` is the constant sheaf with values `M`. -/
noncomputable def sheafPullbackConstantIso (M : AddCommGrpCat.{u + 1}) :
    (ProEt.sheafPullback S AddCommGrpCat.{u + 1}).obj
        ((constantSheaf (smallEtaleTopology S) _).obj M) ≅
      (constantSheaf (ProEt.topology S) _).obj M :=
  (sheafPullbackCompConstantIso S).app M

end ProEt

end AlgebraicGeometry.Scheme
