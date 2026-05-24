import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered

universe v u

open CategoryTheory Limits

instance : ReflectsFilteredColimitsOfSize.{u, u} (forget CommRingCat.{u}) where
  reflects_filtered_colimits _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance : IsIPC.{u} CommRingCat.{u} :=
  .of_preservesFilteredColimitsOfSize (forget CommRingCat.{u})

namespace CommRingCat

/-- Given a finite set `s` of elements in the colimit of a filtered diagram of commutative
rings, we can find a single stage `j` of the diagram together with a function lifting all
elements of `s` through `c.ι.app j`. -/
lemma exists_lift_finset_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c)
    (s : Finset c.pt) :
    ∃ (j : J) (lift : c.pt → F.obj j),
      ∀ x ∈ s, (c.ι.app j).hom (lift x) = x := by
  classical
  have hForget : IsColimit ((forget CommRingCat.{u}).mapCocone c) :=
    isColimitOfPreserves (forget CommRingCat.{u}) hc
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact ⟨j, fun _ => 0, by simp⟩
  | @insert a t ha ih =>
    obtain ⟨j₀, lift₀, h₀⟩ := ih
    obtain ⟨j₁, y₁, hy₁⟩ := Types.jointly_surjective_of_isColimit hForget a
    let j : J := IsFiltered.max j₀ j₁
    let m₀ : j₀ ⟶ j := IsFiltered.leftToMax j₀ j₁
    let m₁ : j₁ ⟶ j := IsFiltered.rightToMax j₀ j₁
    refine ⟨j, Function.update (fun x => (F.map m₀).hom (lift₀ x)) a
      ((F.map m₁).hom y₁), ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxt
    · rw [Function.update_self]
      have hw : F.map m₁ ≫ c.ι.app j = c.ι.app j₁ := c.w m₁
      have := congr($(hw).hom y₁)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [this]
      exact hy₁
    · have hne : x ≠ a := fun heq => ha (heq ▸ hxt)
      rw [Function.update_of_ne hne]
      have hw : F.map m₀ ≫ c.ι.app j = c.ι.app j₀ := c.w m₀
      have := congr($(hw).hom (lift₀ x))
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      rw [this]
      exact h₀ x hxt

end CommRingCat
