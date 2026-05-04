/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Sheafs in the pro category

In this file we develop conditions for when a presheaf on the pro-category
is a sheaf.
-/

universe s t w v₁ v₂ u₁ u₂

namespace CategoryTheory
open Limits

noncomputable
def Limits.IsLimit.ofPreservesLimitColim {J K C : Type*} [Category J] [Category K] [Category C]
    [HasColimitsOfShape J C]
    {D : J ⥤ K ⥤ C} [PreservesLimit D.flip colim]
    (c : Cone D.flip) (hc : IsLimit c)
    (d : Cocone D) (hd : IsColimit d)
    (f : Cocone c.pt) (hf : IsColimit f)
    (e : Cone d.pt)
    (iso : f.pt ≅ e.pt)
    (w : ∀ j k, (c.π.app k).app j ≫ (d.ι.app j).app k = f.ι.app j ≫ iso.hom ≫ e.π.app k) :
    IsLimit e :=
  let natiso : D.flip ⋙ colim ≅ d.pt :=
    (Limits.colimitIsoFlipCompColim _).symm ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso hd
  let hc' : IsLimit (colim.mapCone c) := isLimitOfPreserves _ hc
  let t : (Cone.postcompose natiso.hom).obj (colim.mapCone c) ≅ e := by
    refine Cone.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hf ≪≫ iso) ?_
    intro k
    apply colimit.hom_ext
    intro j
    simp only [Iso.trans_hom, Iso.symm_hom, Cone.postcompose_obj_pt, Functor.mapCone_pt,
      colim_obj, Cone.postcompose_obj_π, NatTrans.comp_app, Functor.const_obj_obj,
      Functor.comp_obj, Functor.mapCone_π_app, colim_map, colimitIsoFlipCompColim_inv_app,
      ι_colimMap_assoc, Functor.flip_obj_obj, Category.assoc,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc, natiso]
    erw [colimitObjIsoColimitCompEvaluation_ι_inv_assoc]
    simp [← NatTrans.comp_app, w]
  IsLimit.equivOfNatIsoOfIso natiso _ e t hc'

end CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

namespace Limits

structure RelativeColimitPresentation (J : Type w) [Category.{t} J] (F : C ⥤ D) (X : D) where
  diag : J ⥤ C
  ι : diag ⋙ F ⟶ (Functor.const J).obj X
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {F : C ⥤ D} {X : D}

namespace RelativeColimitPresentation

initialize_simps_projections RelativeColimitPresentation (-isColimit)

abbrev cocone (pres : RelativeColimitPresentation J F X) : Cocone (pres.diag ⋙ F) :=
  Cocone.mk _ pres.ι

/-- Forget the fact that the diagram factors through `F`. -/
def colimitPresentation (pres : RelativeColimitPresentation J F X) : ColimitPresentation J X where
  diag := pres.diag ⋙ F
  ι := pres.ι
  isColimit := pres.isColimit

noncomputable def self (X : C) : RelativeColimitPresentation PUnit.{s + 1} F (F.obj X) where
  diag := (Functor.const _).obj X
  ι := (F.constComp _ X).hom
  isColimit := .equivOfNatIsoOfIso (F.constComp _ X).symm _
    (Cocone.mk _ (F.constComp _ X).hom) (Cocone.ext (Iso.refl _))
    (isColimitConstCocone PUnit.{s + 1} (F.obj X))

/-- A morphism between relative colimit presentations is a natural transformation between
the diagrams. -/
@[ext]
structure Hom {X Y : D} (pres₁ : RelativeColimitPresentation J F X)
    (pres₂ : RelativeColimitPresentation J F Y) where
  natTrans : pres₁.diag ⟶ pres₂.diag

namespace Hom

variable {X Y Z : D} {pres₁ : RelativeColimitPresentation J F X}
    {pres₂ : RelativeColimitPresentation J F Y} {pres₃ : RelativeColimitPresentation J F Z}

@[simps]
def id (pres : RelativeColimitPresentation J F X) : pres.Hom pres where
  natTrans := 𝟙 _

@[simps]
def comp (f : pres₁.Hom pres₂) (g : pres₂.Hom pres₃) : pres₁.Hom pres₃ where
  natTrans := f.natTrans ≫ g.natTrans

def map (f : pres₁.Hom pres₂) : X ⟶ Y :=
  pres₁.isColimit.map pres₂.cocone (Functor.whiskerRight f.natTrans F)

variable (f : pres₁.Hom pres₂)

@[reassoc (attr := simp)]
lemma ι_map (j : J) : pres₁.ι.app j ≫ f.map = F.map (f.natTrans.app j) ≫ pres₂.ι.app j :=
  pres₁.isColimit.ι_map _ _ j

end Hom

end RelativeColimitPresentation

structure RelativeLimitPresentation (J : Type w) [Category.{t} J] (F : C ⥤ D) (X : D) where
  diag : J ⥤ C
  π : (Functor.const J).obj X ⟶ diag ⋙ F
  isLimit : IsLimit (Cone.mk _ π)

variable {J : Type w} [Category.{t} J] {F : C ⥤ D} {X : D}

namespace RelativeLimitPresentation

initialize_simps_projections RelativeLimitPresentation (-isLimit)

abbrev cone (pres : RelativeLimitPresentation J F X) : Cone (pres.diag ⋙ F) :=
  Cone.mk _ pres.π

/-- Forget the fact that the diagram factors through `F`. -/
def limitPresentation (pres : RelativeLimitPresentation J F X) : LimitPresentation J X where
  diag := pres.diag ⋙ F
  π := pres.π
  isLimit := pres.isLimit

noncomputable def self (X : C) : RelativeLimitPresentation PUnit.{s + 1} F (F.obj X) where
  diag := (Functor.const _).obj X
  π := (F.constComp _ X).inv
  isLimit := .equivOfNatIsoOfIso (F.constComp _ X).symm _
    (Cone.mk _ (F.constComp _ X).inv) (Cone.ext (Iso.refl _))
    (isLimitConstCone PUnit.{s + 1} (F.obj X))

/-- A morphism between relative colimit presentations is a natural transformation between
the diagrams. -/
@[ext]
structure Hom {X Y : D} (pres₁ : RelativeLimitPresentation J F X)
    (pres₂ : RelativeLimitPresentation J F Y) where
  natTrans : pres₁.diag ⟶ pres₂.diag

namespace Hom

variable {X Y Z : D} {pres₁ : RelativeLimitPresentation J F X}
    {pres₂ : RelativeLimitPresentation J F Y} {pres₃ : RelativeLimitPresentation J F Z}

@[simps]
def id (pres : RelativeLimitPresentation J F X) : pres.Hom pres where
  natTrans := 𝟙 _

@[simps]
def comp (f : pres₁.Hom pres₂) (g : pres₂.Hom pres₃) : pres₁.Hom pres₃ where
  natTrans := f.natTrans ≫ g.natTrans

def map (f : pres₁.Hom pres₂) : X ⟶ Y :=
  pres₂.isLimit.map pres₁.cone (Functor.whiskerRight f.natTrans F)

variable (f : pres₁.Hom pres₂)

@[reassoc (attr := simp)]
lemma map_π (j : J) : f.map ≫ pres₂.π.app j = pres₁.π.app j ≫ F.map (f.natTrans.app j) :=
  pres₂.isLimit.map_π _ _ j

end Hom

end RelativeLimitPresentation

end Limits

open Limits Opposite

class Functor.IsInd (F : C ⥤ D) : Prop where
  hom_exists {X Y : D} (f : X ⟶ Y) : ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres₁ : RelativeColimitPresentation J F X) (pres₂ : RelativeColimitPresentation J F Y)
    (t : pres₁.Hom pres₂), f = t.map

lemma Functor.IsInd.obj_exists [IsInd.{w} F] (X : D) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsFiltered J),
      Nonempty (RelativeColimitPresentation J F X) := by
  obtain ⟨J, _, _, pres, _, _, _⟩ := hom_exists (F := F) (𝟙 X)
  use J, inferInstance, inferInstance
  exact ⟨pres⟩

instance : Functor.IsInd.{v₁} (Ind.yoneda (C := C)) where
  hom_exists {X Y} f := by
    obtain ⟨J, _, _, D₁, D₂, φ, ⟨e⟩⟩ := Ind.exists_nonempty_arrow_mk_iso_ind_lim (f := f)
    use J, inferInstance, inferInstance
    let pres₁ : RelativeColimitPresentation J Ind.yoneda X :=
    { diag := D₁
      ι := (colimit.cocone (D₁ ⋙ Ind.yoneda)).ι ≫
        (Functor.const J).map (Arrow.leftFunc.mapIso e).inv
      isColimit := (colimit.isColimit _).extendIso _ }
    let pres₂ : RelativeColimitPresentation J Ind.yoneda Y :=
    { diag := D₂
      ι := (colimit.cocone (D₂ ⋙ Ind.yoneda)).ι ≫
        (Functor.const J).map (Arrow.rightFunc.mapIso e).inv
      isColimit := (colimit.isColimit _).extendIso _ }
    refine ⟨pres₁, pres₂, ⟨φ⟩, ?_⟩
    apply pres₁.isColimit.hom_ext
    intro j
    simp only [Functor.comp_obj, Functor.const_obj_obj, RelativeColimitPresentation.Hom.ι_map]
    simp [pres₁, pres₂, Ind.lim]

class Functor.IsPro (F : C ⥤ D) : Prop where
  hom_exists {X Y : D} (f : X ⟶ Y) : ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCofiltered J)
    (pres₁ : RelativeLimitPresentation J F X) (pres₂ : RelativeLimitPresentation J F Y)
    (t : pres₁.Hom pres₂), f = t.map

/-- The pro-category of `C` is `(Ind Cᵒᵖ)ᵒᵖ`. -/
def Pro (C : Type*) [Category C] := (Ind Cᵒᵖ)ᵒᵖ

noncomputable instance : Category (Pro C) :=
  inferInstanceAs <| Category (Ind Cᵒᵖ)ᵒᵖ

def PreOneHypercover.functor (F : C ⥤ D) (X : C) : PreOneHypercover.{w} X ⥤ PreOneHypercover.{w} (F.obj X) where
  obj E := E.map F
  map {E G} f :=
    { s₀ := f.s₀
      h₀ i := F.map (f.h₀ i)
      s₁ k := f.s₁ k
      h₁ k := F.map (f.h₁ k)
      w₀ i := by simp [← Functor.map_comp]
      w₁₁ := by simp [← Functor.map_comp, Hom.w₁₁]
      w₁₂ := by simp [← Functor.map_comp, Hom.w₁₂] }
  -- TODO: improve these proofs by adding some `simp` lemmas
  map_id E := by apply Hom.ext <;> simp <;> rfl
  map_comp {E₁ E₂ E₃} f g := by apply Hom.ext <;> simp <;> rfl

structure PreOneHypercover.RelativeLimitPresentation (J : Type*) [Category J]
    {X : D} (F : C ⥤ D) (E : PreOneHypercover.{w} X) where
  pres : Limits.RelativeLimitPresentation J F X
  pres₀ : ∀ i : E.I₀, Limits.RelativeLimitPresentation J F (E.X i)
  pres₁ : ∀ {i j} (k : E.I₁ i j), Limits.RelativeLimitPresentation J F (E.Y k)
  f : ∀ i, (pres₀ i).Hom pres
  p₁ : ∀ {i j} (k : E.I₁ i j), (pres₁ k).Hom (pres₀ i)
  p₂ : ∀ {i j} (k : E.I₁ i j), (pres₁ k).Hom (pres₀ j)
  hf : ∀ i, (f i).map = E.f i
  hp₁ : ∀ {i j} (k : E.I₁ i j), (p₁ k).map = E.p₁ k
  hp₂ : ∀ {i j} (k : E.I₁ i j), (p₂ k).map = E.p₂ k
  w : ∀ {i j} (k : E.I₁ i j), (p₁ k).comp (f i) = (p₂ k).comp (f j)

@[simps]
def PreOneHypercover.RelativeLimitPresentation.preOneHypercover {J : Type*} [Category J]
    {X : D} {F : C ⥤ D} {E : PreOneHypercover.{w} X}
    (pres : E.RelativeLimitPresentation J F) (j : J) :
    PreOneHypercover (pres.pres.diag.obj j) where
  I₀ := E.I₀
  X i := (pres.pres₀ i).diag.obj j
  f i := (pres.f i).natTrans.app j
  I₁ := E.I₁
  Y _ _ k := (pres.pres₁ k).diag.obj j
  p₁ _ _ k := (pres.p₁ k).natTrans.app j
  p₂ _ _ k := (pres.p₂ k).natTrans.app j
  w _ _ k := by simpa using congr($(pres.w k).natTrans.app j)

variable {J : Type*} [Category J] {X : D} {F : C ⥤ D} {E : PreOneHypercover.{w} X}
  {K : GrothendieckTopology C}

def PreOneHypercover.RelativeLimitPresentation.oneHypercover
    (pres : E.RelativeLimitPresentation J F) (j : J)
    (mem₀ : (pres.preOneHypercover j).sieve₀ ∈ K _)
    (mem₁ : ∀ {a b : E.I₀} {W : C} (p₁ : W ⟶ (pres.preOneHypercover j).X a)
        (p₂ : W ⟶ (pres.preOneHypercover j).X b),
        p₁ ≫ (pres.preOneHypercover j).f a = p₂ ≫ (pres.preOneHypercover j).f b →
        (pres.preOneHypercover j).sieve₁ p₁ p₂ ∈ K W) :
    K.OneHypercover (pres.pres.diag.obj j) where
  __ := pres.preOneHypercover j
  mem₀ := mem₀
  mem₁ _ _ _ := mem₁

variable {A : Type*} [Category A]

@[simps]
def PreOneHypercover.RelativeLimitPresentation.multicospan (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Jᵒᵖ ⥤ (WalkingMulticospan E.multicospanShape ⥤ A) where
  obj j := ((pres.preOneHypercover j.unop).multicospanIndex (F.op ⋙ P)).multicospan
  map {i j} f :=
    { app
        | .left k => P.map (F.map <| (pres.pres₀ k).diag.map f.unop).op
        | .right k => P.map (F.map <| (pres.pres₁ k.2).diag.map f.unop).op
      naturality k l f := by
        rcases f
        · simp
        · simp [← Functor.map_comp, ← op_comp]
        · simp [← Functor.map_comp, ← op_comp] }

@[simps]
def PreOneHypercover.RelativeLimitPresentation.cocone (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Cocone (pres.multicospan P) where
  pt := (E.multicospanIndex P).multicospan
  ι.app j :=
    { app
        | .left k => P.map ((pres.pres₀ k).π.app j.unop).op
        | .right k => P.map ((pres.pres₁ k.2).π.app j.unop).op
      naturality k l f := by
        match f with
        | .id _ => simp
        | .fst k =>
          suffices h : P.map (F.map ((pres.p₁ k.snd).natTrans.app (unop j))).op ≫
              P.map ((pres.pres₁ k.snd).π.app (unop j)).op =
                P.map ((pres.pres₀ k.fst.1).π.app (unop j)).op ≫ P.map (E.p₁ k.snd).op by
            simpa
          simp_rw [← Functor.map_comp, ← op_comp]
          rw [← pres.hp₁ k.2]
          simp
        | .snd k =>
          suffices h : P.map (F.map ((pres.p₂ k.snd).natTrans.app (unop j))).op ≫
              P.map ((pres.pres₁ k.snd).π.app (unop j)).op =
                P.map ((pres.pres₀ k.fst.2).π.app (unop j)).op ≫ P.map (E.p₂ k.snd).op by
            simpa
          simp_rw [← Functor.map_comp, ← op_comp]
          rw [← pres.hp₂ k.2]
          simp
    }
  ι.naturality i j f := by
    ext k
    match k with
    | .left k =>
        simp only [multicospan_obj, MulticospanIndex.multicospan_obj, multicospanShape_L,
          preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
          Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
          preOneHypercover_Y, Functor.const_obj_obj, NatTrans.comp_app, multicospan_map_app,
          ← Functor.map_comp, ← op_comp, Functor.const_obj_map, Category.comp_id]
        congr 2
        simpa using ((pres.pres₀ k).π.naturality f.unop).symm
    | .right k =>
        simp only [multicospan_obj, MulticospanIndex.multicospan_obj, multicospanShape_L,
          preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
          Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
          preOneHypercover_Y, Functor.const_obj_obj, NatTrans.comp_app, multicospan_map_app,
          ← Functor.map_comp, ← op_comp, Functor.const_obj_map, Category.comp_id]
        congr 2
        simpa using ((pres.pres₁ k.2).π.naturality f.unop).symm

noncomputable
def PreOneHypercover.RelativeLimitPresentation.isColimit (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) [PreservesColimitsOfShape Jᵒᵖ P] :
    IsColimit (pres.cocone P) :=
  evaluationJointlyReflectsColimits _ fun k ↦ match k with
    | .left k => isColimitOfPreserves P (pres.pres₀ k).isLimit.op
    | .right k => isColimitOfPreserves P (pres.pres₁ k.2).isLimit.op

@[simps]
def PreOneHypercover.RelativeLimitPresentation.multifork (pres : E.RelativeLimitPresentation J F)
    (P : Dᵒᵖ ⥤ A) :
    Cone (pres.multicospan P).flip where
  pt := pres.pres.diag.op ⋙ F.op ⋙ P
  π.app
    | .left k =>
      Functor.whiskerRight (NatTrans.op (pres.f k).natTrans) _
    | .right k =>
      Functor.whiskerRight (NatTrans.op <| (pres.p₁ k.2).natTrans ≫ (pres.f k.1.1).natTrans) _
  π.naturality k l f := by
    rcases f
    · simp
    · ext; simp
    · ext
      simp only [multicospanShape_snd, Functor.const_obj_obj, Functor.comp_obj, Functor.op_obj,
        Functor.flip_obj_obj, multicospan_obj, MulticospanIndex.multicospan_obj, multicospanShape_L,
        preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, multicospanShape_R,
        multicospanIndex_right, preOneHypercover_I₁, preOneHypercover_Y, Functor.const_obj_map,
        NatTrans.op_comp, Functor.whiskerRight_comp, Category.id_comp, NatTrans.comp_app,
        Functor.whiskerRight_app, NatTrans.op_app, Functor.comp_map, Functor.op_map,
        Quiver.Hom.unop_op, Functor.flip_map_app, MulticospanIndex.multicospan_map,
        multicospanIndex_snd, preOneHypercover_p₂, ← Functor.map_comp, ← op_comp]
      congr 3
      simpa using congr($(pres.w _).natTrans.app _)

noncomputable
def PreOneHypercover.RelativeLimitPresentation.isLimit (P : Dᵒᵖ ⥤ A)
    [PreservesColimitsOfShape Jᵒᵖ P]
    [HasColimitsOfShape Jᵒᵖ A]
    [PreservesLimitsOfShape (WalkingMulticospan E.multicospanShape) (colim : (Jᵒᵖ ⥤ A) ⥤ _)]
    (pres : E.RelativeLimitPresentation J F)
    (h : ∀ j, IsLimit <| (pres.preOneHypercover j).multifork (F.op ⋙ P)) :
    IsLimit (E.multifork P) := by
  refine IsLimit.ofPreservesLimitColim (pres.multifork P) ?_ (pres.cocone P) (pres.isColimit P)
      (P.mapCocone pres.pres.cone.op) (isColimitOfPreserves _ pres.pres.isLimit.op) _ (.refl _) ?_
  · refine evaluationJointlyReflectsLimits _ fun j ↦ ?_
    refine IsLimit.ofIsoLimit (h j.1) (Cone.ext (Iso.refl _) ?_)
    intro l
    simp only [Functor.const_obj_obj, MulticospanIndex.multicospan_obj, multicospanShape_L,
      preOneHypercover_I₀, multicospanIndex_left, preOneHypercover_X, Functor.comp_obj,
      Functor.op_obj, multicospanShape_R, multicospanIndex_right, preOneHypercover_I₁,
      preOneHypercover_Y, Functor.mapCone_pt, multifork_pt, evaluation_obj_obj, Iso.refl_hom,
      Functor.mapCone_π_app, multifork_π_app, NatTrans.op_comp, Functor.whiskerRight_comp,
      evaluation_obj_map, Category.id_comp]
    cases l <;> rfl
  · intro j k
    match k with
    | .left k =>
      suffices h : (pres.pres₀ k).π.app (unop j) ≫ F.map ((pres.f k).natTrans.app (unop j)) =
          E.f k ≫ pres.pres.π.app (unop j) by
        simp [h, ← Functor.map_comp, ← op_comp, PreOneHypercover.multifork]
      rw [← pres.hf]
      simp
    | .right k =>
      suffices h : (pres.pres₁ k.snd).π.app (unop j) ≫
          F.map ((pres.p₁ k.snd).natTrans.app (unop j) ≫ (pres.f k.fst.1).natTrans.app (unop j)) =
          E.p₁ k.snd ≫ E.f k.fst.1 ≫ pres.pres.π.app (unop j) by
        simp [h, ← Functor.map_comp, ← op_comp, PreOneHypercover.multifork]
      rw [← pres.hf, ← pres.hp₁]
      simp

section

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable (F A) in
/--
The family of `1`-hypercovers of `D` (think: `= Pro C`) that is a limit
of `1`-hypercovers in `C`.

We shall show that if `D = Pro C`, the finite `1`-hypercovers for a suitable topology
on `D` satisfy this.
-/
def GrothendieckTopology.oneHypercoverRelativelyRepresentable [HasFilteredColimitsOfSize.{w, w} A] :
    K.OneHypercoverFamily :=
  fun _ E ↦ ∃ (I : Type w) (_ : SmallCategory I) (_ : IsCofiltered I)
    (pres : E.toPreOneHypercover.RelativeLimitPresentation I F),
    PreservesLimitsOfShape (WalkingMulticospan E.multicospanShape)
      (colim : (Iᵒᵖ ⥤ A) ⥤ _) ∧
    ∀ j, (pres.preOneHypercover j).sieve₀ ∈ J _ ∧
      ∀ {a b : E.I₀} {W : C} (p₁ : W ⟶ (pres.preOneHypercover j).X a)
        (p₂ : W ⟶ (pres.preOneHypercover j).X b),
        p₁ ≫ (pres.preOneHypercover j).f a = p₂ ≫ (pres.preOneHypercover j).f b →
        (pres.preOneHypercover j).sieve₁ p₁ p₂ ∈ J W

/--
Let `K` be a topology generated by limits of `1`-hypercovers in `C`. Then if `P` is a
presheaf on `D` (think: `= Pro C`) such that

1. `P` restricted to `C` is a sheaf, and
2. `P` preserves filtered colimits, then

`P` is a sheaf.
-/
lemma Presheaf.IsSheaf.of_preservesFilteredColimitsOfSize (P : Dᵒᵖ ⥤ A) (h : IsSheaf J (F.op ⋙ P))
    [PreservesFilteredColimitsOfSize.{w, w} P] [HasFilteredColimitsOfSize.{w, w} A]
    [(GrothendieckTopology.oneHypercoverRelativelyRepresentable.{w} F A J K).IsGenerating] :
    IsSheaf K P := by
  rw [(GrothendieckTopology.oneHypercoverRelativelyRepresentable F A J K).isSheaf_iff]
  intro X E ⟨I, _, _, pres, hinst, mem⟩
  constructor
  apply pres.isLimit (P := P)
  intro j
  let E' : J.OneHypercover (pres.pres.diag.obj j) := pres.oneHypercover j (mem j).1 (mem j).2
  exact E'.isLimitMultifork ⟨_, h⟩

end

end CategoryTheory
