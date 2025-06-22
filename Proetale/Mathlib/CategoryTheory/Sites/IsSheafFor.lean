import Mathlib.CategoryTheory.Sites.IsSheafFor

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

-- TODO: this is almost in mathlib, with slightly less general universe assumptions on `F`
-- and with a wrong name
lemma Presieve.IsSheafFor.of_isSheafFor_pullback'' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Sieve X)
    (hF : Presieve.IsSheafFor F S.arrows)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F (S.pullback f).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    refine (H (g ≫ f) (by simp [hf])).isSeparatedFor.ext fun U o ho ↦ ?_
    simp only [Sieve.pullback_apply] at ho
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hs _ _ _ ho, hs _ _ _ (by simpa)]
    congr 1
    simp
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp, ht' (g ≫ f) hg, ← t.comp_of_compatible _ ht]
    have := hs (g ≫ f) hg (𝟙 _)
    dsimp only [Presieve.FamilyOfElements.IsAmalgamation,
      Presieve.FamilyOfElements.pullback] at this
    simp only [Sieve.pullback_apply, Category.id_comp, op_id, FunctorToTypes.map_id_apply] at this
    rw [this]
    · congr 1
      simp
    · simp [hf]
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback
    (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S : Presieve X) (T : Sieve X) [S.hasPullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := hasPullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F (T.pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [pullbackCompatible_iff]
    intro Y Z f g hf hg
    haveI := hasPullbacks.has_pullbacks hf hg
    obtain ⟨R, hR, h⟩ := H' f g hf hg
    refine hR.ext fun W w hw ↦ (h w hw).ext fun U u hu ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, Category.assoc]
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [hs f hf (u ≫ w ≫ pullback.fst f g) (by simpa),
      hs g hg (u ≫ w ≫ pullback.snd f g) (by simpa [← pullback.condition])]
    congr 1
    simp [pullback.condition]
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [Sieve.pullback_apply, Sieve.generate_apply] at hg
    obtain ⟨W, w, u, hu, heq⟩ := hg
    simp only [← heq, op_comp, FunctorToTypes.map_comp_apply, ht' u hu]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ u) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    rw [← t.comp_of_compatible _ ht, this]
    apply hs
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Presieve X) [S.hasPullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := hasPullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F ((Sieve.generate T).pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F ((Sieve.generate T).pullback f).arrows) :
    Presieve.IsSheafFor F T := by
  rw [isSheafFor_iff_generate]
  apply Presieve.IsSheafFor.of_isSheafFor_pullback F S _ _ hF'
  · assumption
  · assumption
  · assumption

end CategoryTheory
