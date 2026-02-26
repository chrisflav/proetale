/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Local properties of sheafs
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (K : GrothendieckTopology C)
variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable {J : Type*} [Category J]

namespace Sheaf

--structure IsLocal (P : ObjectProperty (Sheaf K A)) : Prop where
--  iff_of_coversTop (F : Sheaf K A) {ι : Type*} (X : ι → C) (h : K.CoversTop X) :
--    P F ↔ ∀ i, P (F.over (X i))

variable {ι : Type*} (X : ι → C) (hX : K.CoversTop X)
include hX

lemma isIso_iff_of_coversTop {F G : Sheaf K A} {f : F ⟶ G}
    (h : ∀ i, IsIso ((K.overPullback A (X i)).map f)) :
    IsIso f := by
  -- f.val.app (op Z) is iso for any Z with a map to some X i
  have hiso : ∀ (Z : C) (i : ι) (_ : Z ⟶ X i), IsIso (f.val.app (op Z)) := by
    intro Z i g
    have h1 : IsIso ((sheafToPresheaf (K.over (X i)) A).map ((K.overPullback A (X i)).map f)) :=
      inferInstance
    rw [sheafToPresheaf_map, NatTrans.isIso_iff_isIso_app] at h1
    exact h1 (op (Over.mk g))
  -- Show IsIso f.val, then sheafToPresheaf reflects isos
  haveI : IsIso f.val := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    -- Define cover S for W.unop
    set S : K.Cover W.unop := hX.cover W.unop
    -- For each arrow in S, f.val.app is iso
    have harrow : ∀ (I : S.Arrow), IsIso (f.val.app (op I.Y)) := by
      intro I; obtain ⟨i, ⟨g⟩⟩ := I.hf; exact hiso I.Y i g
    -- Construct inverse via sheaf amalgamation
    -- Key naturality lemma: inv(f_Y) ≫ F.map g = G.map g ≫ inv(f_Z)
    have nat_inv : ∀ {Y Z : C} (g : Z ⟶ Y) [IsIso (f.val.app (op Y))]
        [IsIso (f.val.app (op Z))],
        inv (f.val.app (op Y)) ≫ F.val.map g.op = G.val.map g.op ≫ inv (f.val.app (op Z)) := by
      intro Y Z g _ _
      rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
      exact f.val.naturality g.op
    let invMap : G.val.obj (op W.unop) ⟶ F.val.obj (op W.unop) :=
      F.2.amalgamate S (fun I => G.val.map I.f.op ≫ inv (f.val.app (op I.Y))) (by
        intro I₁ I₂ r
        have hZ : IsIso (f.val.app (op r.Z)) := by
          obtain ⟨i, ⟨g⟩⟩ := I₁.hf; exact hiso r.Z i (r.g₁ ≫ g)
        simp only [Category.assoc, nat_inv]
        rw [← Category.assoc, ← Category.assoc, ← G.val.map_comp, ← G.val.map_comp,
          ← op_comp, ← op_comp, r.w])
    -- f.val.app W is iso with inverse invMap
    change IsIso (f.val.app (op W.unop))
    exact ⟨⟨invMap, by
      apply F.2.hom_ext S; intro I
      simp only [Category.assoc, Category.id_comp]
      rw [Presheaf.IsSheaf.amalgamate_map, ← Category.assoc, ← f.val.naturality,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id], by
      apply G.2.hom_ext S; intro I
      simp only [Category.assoc, Category.id_comp]
      rw [← f.val.naturality, Presheaf.IsSheaf.amalgamate_map_assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩
  haveI : IsIso ((sheafToPresheaf K A).map f) := by show IsIso f.val; infer_instance
  exact isIso_of_reflects_iso f (sheafToPresheaf K A)

lemma foo (F : Sheaf K A) [HasColimitsOfShape J A] [(forget A).ReflectsIsomorphisms]
    (hF : ∀ i : ι, PreservesColimitsOfShape J (F.over (X i)).val) :
    PreservesColimitsOfShape J F.val := by
  constructor
  intro D
  constructor
  intro c hc
  constructor
  have : IsIso ((colimit.isColimit (D ⋙ F.val)).desc (F.val.mapCocone c)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    simp only [colimit.cocone_x, Functor.mapCocone_pt, colimit.isColimit_desc]
    refine ⟨?_, ?_⟩
    · sorry
    · intro y
      sorry
  exact .ofPointIso (colimit.isColimit _)

end Sheaf

end CategoryTheory
