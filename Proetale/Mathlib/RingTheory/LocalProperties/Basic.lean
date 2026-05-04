import Mathlib.RingTheory.LocalProperties.Basic

universe u

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- A property of ring homs that is stable under base change is preserved by localization away. -/
lemma RingHom.IsStableUnderBaseChange.localizationAwayPreserves
    (hP : RingHom.IsStableUnderBaseChange @P) :
    RingHom.LocalizationAwayPreserves P := by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by
    rw [Submonoid.map_powers]; assumption
  exact hP.isLocalization_map (.powers r) f hf

/-- A property of ring homs that is stable under base change respects isomorphisms. -/
lemma RingHom.IsStableUnderBaseChange.respectsIso
    (hP : RingHom.IsStableUnderBaseChange @P) :
    RingHom.RespectsIso P :=
  hP.localizationAwayPreserves.respectsIso
