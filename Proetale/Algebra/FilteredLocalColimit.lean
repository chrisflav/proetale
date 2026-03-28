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

open CategoryTheory Limits IsLocalRing

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F}
  [h_obj : ∀ (j : J), IsLocalRing (F.obj j)] [h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom]

/- [TODO]: generalize the upstream instance `CommRingCat.FilteredColimits.forget_preservesFilteredColimits`
  to remove the universe constraint on `J`. -/

namespace CommRingCat.FilteredColimits

omit h_obj h_hom in
lemma nonunits_le_of_isColimit (hc : IsColimit c):
    (nonunits c.pt : Set _) ≤ ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  intro x hx
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc x
  exact Set.mem_iUnion.mpr ⟨j, ⟨y, fun h ↦ hx (h.map _), rfl⟩⟩

omit h_obj in
lemma isLocalHom_ι (hc : IsColimit c) (j : J) :
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

omit h_obj in
lemma nonunits_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (nonunits c.pt : Set _) = ⋃ (j : J), (c.ι.app j) '' (nonunits (F.obj j)) := by
  apply le_antisymm (nonunits_le_of_isColimit F hc) (fun x hx ↦ ?_)
  obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
  have := isLocalHom_ι F hc
  exact (map_mem_nonunits_iff _ _).mpr hy

/- [TODO]: generalize the upstream lemma `CommRingCat.FilteredColimits.nontrivial` to remove the
  requirement of `SmallCategory J`. -/
theorem isLocalRing_of_isColimit (hc : IsColimit c) : IsLocalRing c.pt := by
  have : Nontrivial c.pt := FilteredColimits.nontrivial (c := c) hc
  have h_nonunits_eq := nonunits_eq_iUnion_of_isColimit F hc
  have h_isLocalHom := isLocalHom_ι F hc
  refine IsLocalRing.of_nonunits_add (fun a b ha hb ↦ h_nonunits_eq ▸ (Set.mem_iUnion.mpr ?_))
  simp only [h_nonunits_eq, Functor.const_obj_obj, Set.mem_iUnion, Set.mem_image] at ha hb
  obtain ⟨j, a, ha, rfl⟩ := ha
  obtain ⟨j', b, hb, rfl⟩ := hb
  obtain ⟨j'', f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j j'
  refine ⟨j'', ⟨F.map f a + F.map g b, (h_obj j'').nonunits_add
    ((map_mem_nonunits_iff _ _).mpr ha) ((map_mem_nonunits_iff _ _).mpr hb), ?_⟩⟩
  simp only [map_add, ← comp_apply .., Cocone.w c _]
  rfl

lemma colimit_isLocalRing_maximalIdeal (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal.carrier =
    ⋃ (j : J), (c.ι.app j) '' (maximalIdeal (F.obj j)).carrier :=
  nonunits_eq_iUnion_of_isColimit F hc

-- Is it possible to make `Functor.const.obj` reducible somehow? Is it possible to remove `let`?
set_option linter.unusedVariables false in
lemma colimit_residueField (hc : IsColimit c) :
    let inst_isLocalRing := isLocalRing_of_isColimit F hc
    let inst_isLocalHom := isLocalHom_ι F hc
    let (j : J) : IsLocalRing (((Functor.const J).obj c.pt).obj j) := inst_isLocalRing
    ⋃ (j : J), (ResidueField.map (c.ι.app j).hom).fieldRange.carrier = (⊤ : Set (ResidueField c.pt)):= by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨j, z, rfl⟩ := Concrete.isColimit_exists_rep F hc y
  simp only [Functor.const_obj_obj, Subsemiring.coe_carrier_toSubmonoid, Subring.coe_toSubsemiring,
    Subfield.coe_toSubring, RingHom.coe_fieldRange, Set.mem_iUnion, Set.mem_range, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  exact ⟨j, residue _ z, rfl⟩

end CommRingCat.FilteredColimits
