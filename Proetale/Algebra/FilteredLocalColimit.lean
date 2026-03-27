/-
Copyright (c) 2026 Jingting Wang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Christian Merten
-/

import Mathlib

/-!
# Filtered colimit of local rings
-/
universe u

open CategoryTheory Limits

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F}

/- [TODO]: generalize the upstream instance `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`
  to remove the universe constraint on `J`. -/

namespace CommRingCat.FilteredColimits

lemma nonunits_colimits_le (hc : IsColimit c) :
    (nonunits c.pt : Set _) ≤ ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  intro x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  exact Set.mem_iUnion.mpr ⟨j, ⟨y, fun h ↦ hx (h.map _), rfl⟩⟩

lemma ι_isLocalHom (hc : IsColimit c)
    (h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom) (j : J) :
    IsLocalHom (c.ι.app j).hom := by
  apply IsLocalHom.mk
  rintro x ⟨y, hy⟩
  obtain ⟨j1, z, hz⟩ := Concrete.isColimit_exists_rep F hc (y⁻¹).1
  obtain ⟨j2, f', g', _⟩ := IsFilteredOrEmpty.cocone_objs j j1
  have : (c.ι.app j2).hom ((F.map f' x) * (F.map g' z)) = (c.ι.app j2).hom 1 := by
    simp only [map_mul, map_one, ← comp_apply .., Cocone.w, ← y.mul_inv, hy, ← hz]
    rfl
  obtain ⟨j3, f3, g3, hfg3⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ this
  obtain ⟨j4, i4, h4⟩ := IsFilteredOrEmpty.cocone_maps f3 g3
  refine isUnit_of_map_unit (F.map (f' ≫ f3 ≫ i4)).hom x <| isUnit_iff_exists_inv.mpr <|
    ⟨(F.map (g' ≫ g3 ≫ i4)).hom z, h4 ▸ ?_⟩
  simpa using congr((F.map i4).hom $hfg3)

lemma nonunits_colimits_eq_of_isLocalHom (hc : IsColimit c)
    (h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom) :
    (nonunits c.pt : Set _) = ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  apply le_antisymm (nonunits_colimits_le F hc) (fun x hx ↦ ?_)
  obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  have := ι_isLocalHom F hc h_hom
  exact (map_mem_nonunits_iff _ _).mpr hy

/- [TODO]: generalize the upstream lemma `CommRingCat.FilteredColimits.nontrivial` to remove the
  requirement of `SmallCategory J`. -/
theorem CommRingCat.FilteredColimits.colimit_isLocalRing (hc : IsColimit c)
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
  simp only [map_add, ← comp_apply .., Cocone.w c _]
  rfl

end CommRingCat.FilteredColimits
