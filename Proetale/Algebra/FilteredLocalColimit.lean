/-
Copyright (c) 2026 Jingting Wang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Christian Merten
-/

import Mathlib

#check IsLocalRing

universe u v

open CategoryTheory Limits

section

variable {J : Type*} [Category* J] [IsFiltered J] (F : J ⥤ CommRingCat.{v}) {c : Cocone F} (hc : IsColimit c)

#check CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq

instance [IsFiltered J] : PreservesColimit F (forget CommRingCat) := by sorry

include hc in
lemma CommRingCat.FilteredColimits.nonunits_colimits_le :
    (nonunits c.pt : Set _) ≤ ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  intro x hx
  obtain ⟨j, y, rfl⟩ := CategoryTheory.Limits.Concrete.isColimit_exists_rep F hc x
  exact Set.mem_iUnion.mpr ⟨j, ⟨y, fun h ↦ hx (h.map _), rfl⟩⟩

include hc in
lemma CommRingCat.FilteredColimits.ι_isLocalHom
    (h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom) (j : J) :
    IsLocalHom (c.ι.app j).hom := by
  refine IsLocalHom.mk fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := hx
  obtain ⟨j', z, hz⟩ := CategoryTheory.Limits.Concrete.isColimit_exists_rep F hc y.inv
  obtain ⟨j'', f', g', _⟩ := IsFilteredOrEmpty.cocone_objs j j'

  sorry

include hc in
lemma CommRingCat.FilteredColimits.nonunits_colimits_eq_of_isLocalHom
    (h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom) :
    (nonunits c.pt : Set _) = ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  apply le_antisymm (nonunits_colimits_le F hc) (fun x hx ↦ ?_)
  obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  have := ι_isLocalHom F hc h_hom
  exact (map_mem_nonunits_iff _ _).mpr hy

end
#check NatTrans
/- [TODO]: generalize the upstream lemma `CommRingCat.FilteredColimits.nontrivial` to remove the
  requirement of `SmallCategory J`. -/

theorem CommRingCat.FilteredColimits.colimit_isLocalRing {J : Type v} [SmallCategory J]
    [IsFiltered J] (F : J ⥤ CommRingCat.{v}) {c : Cocone F} (hc : IsColimit c)
    (h_obj : ∀ (j : J), IsLocalRing (F.obj j)) (h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom) :
    IsLocalRing c.pt := by
  have : Nontrivial c.pt := CommRingCat.FilteredColimits.nontrivial (c := c) hc
  have h_nonunits_eq := nonunits_colimits_eq_of_isLocalHom F hc h_hom
  have h_isLocalHom := ι_isLocalHom F hc h_hom
  refine IsLocalRing.of_nonunits_add (fun a b ha hb ↦ h_nonunits_eq ▸ (Set.mem_iUnion.mpr ?_))
  simp only [h_nonunits_eq, Functor.const_obj_obj, Set.mem_iUnion, Set.mem_image] at ha hb
  obtain ⟨j, a, ha, rfl⟩ := ha
  obtain ⟨j', b, hb, rfl⟩ := hb
  obtain ⟨j'', f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  refine ⟨j'', ⟨F.map f a + F.map g b, (h_obj j'').nonunits_add
    ((map_mem_nonunits_iff _ _).mpr ha) ((map_mem_nonunits_iff _ _).mpr hb), ?_⟩⟩
  rw [map_add, ← comp_apply .., ← comp_apply .., Cocone.w c f, Cocone.w c g]
  rfl
