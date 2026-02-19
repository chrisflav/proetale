import Mathlib.RingTheory.RingHom.Flat

universe u

open CategoryTheory

namespace CommRingCat

/-- The morphism property of flat ring maps. -/
def flat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.Flat

@[simp]
lemma flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    flat f ↔ f.hom.Flat := .rfl

lemma flat_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    flat (ofHom f) ↔ f.Flat := .rfl

instance : flat.IsStableUnderCobaseChange := by
  rw [flat, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Flat.isStableUnderBaseChange

end CommRingCat
