/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind

/-!
# Ind spreads
-/


universe s t w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

namespace MorphismProperty

lemma PreIndSpreads.inf (Q : MorphismProperty C) [PreIndSpreads.{w} P]
    [PreIndSpreads.{w} Q] :
    PreIndSpreads.{w} (P ⊓ Q) where
  exists_isPushout {J} _ _ D c hc T f hf := by
    obtain ⟨j₁, T'₁, f'₁, g₁, hg₁⟩ := P.exists_isPushout_of_isFiltered hc f hf.1
    obtain ⟨j₂, T'₂, f'₂, g₂, hg₂⟩ := Q.exists_isPushout_of_isFiltered hc f hf.2
    sorry

variable {P} in
/-- If `C` has an initial object `S` such that every `P`-morphism `X ⟶ Y` descends to
a P-morphism `X' ⟶ Y'` with `X'` finitely presented over `S`, then `P` pre-ind-spreads. -/
lemma PreIndSpreads.of_isInitial [HasPushouts C] [P.IsStableUnderCobaseChange]
    {S : C} (h : IsInitial S)
    (H : ∀ ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄, P f →
      ∃ (X' Y' : C) (u : X' ⟶ X) (v : Y' ⟶ Y) (f' : X' ⟶ Y'),
        isFinitelyPresentable.{w} C (h.to X') ∧ P f' ∧ IsPushout u f' f v) :
    PreIndSpreads.{w} P where
  exists_isPushout {J _ _ D} c hc Z f hf := by
    obtain ⟨X', Y', u, v, f', hX', hf', H⟩ := H hf
    let s : (Functor.const J).obj S ⟶ D :=
      { app j := h.to _
        naturality _ _ _ := h.hom_ext _ _ }
    obtain ⟨j, q, hgq, rfl⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hc hX' s u
      fun j ↦ h.hom_ext _ _
    exact ⟨j, pushout f' q, pushout.inr _ _, pushout.desc v (c.ι.app j ≫ f) (by simp [← H.w]),
      .of_left (by simpa) (by simp) (IsPushout.of_hasPushout f' q).flip, P.pushout_inr _ _ hf'⟩

lemma PreIndSpreads.of_univLE [UnivLE.{w, w'}] [PreIndSpreads.{w'} P] :
    PreIndSpreads.{w} P where
  exists_isPushout {J} _ _ D c hc T f hf := by
    have : Small.{w'} J := UnivLE.small J
    have : EssentiallySmall.{w'} J := essentiallySmall_of_small_of_locallySmall J
    let e := equivSmallModel.{w'} J
    let D' := e.inverse ⋙ D
    let c' : Cocone D' := c.whisker e.inverse
    have hc' : IsColimit c' :=
      (Functor.Final.isColimitWhiskerEquiv e.inverse c).symm hc
    have : IsFiltered (SmallModel.{w'} J) := IsFiltered.of_equivalence e
    obtain ⟨j', T', f', g, hpb, hf'⟩ := P.exists_isPushout_of_isFiltered hc' f hf
    exact ⟨e.inverse.obj j', T', f', g, hpb, hf'⟩

/--
- Given a `colim Dᵢ`-morphism `f : A = colim Dᵢ ⨿_[Dᵢ] A' ⟶ colim Dᵢ ⨿_[Dⱼ] B' = B`
  where `A' ⟶ Dᵢ` and `B' ⟶ Dⱼ` satisfiy `P`, there exists
  `k ≥ i` and `k ≥ j` and a diagram
  ```
  A <--------------- Dₖ ⨿_[Dᵢ] A'
  |                      |
  f                      f'
  |                      |
  v                      v
  B <--------------- Dₖ ⨿_[Dⱼ] B'
  ```.
-/
class IndSpreads (P : MorphismProperty C) : Prop extends PreIndSpreads.{w} P where
  exists_isPushout_of_hom {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C}
    (c : Cocone D) (_ : IsColimit c)
    {A B A' B' : C} (f : A ⟶ B) (pA : c.pt ⟶ A) (pB : c.pt ⟶ B) (_hf : pA ≫ f = pB)
    {jA jB : J} (qA : A' ⟶ A) (qB : B' ⟶ B) (gA : D.obj jA ⟶ A') (gB : D.obj jB ⟶ B')
    (hA : IsPushout (c.ι.app jA) gA pA qA) (hB : IsPushout (c.ι.app jB) gB pB qB) :
    P gA → P gB →
    ∃ (j : J) (tA : jA ⟶ j) (tB : jB ⟶ j) (PA PB : C) (PA₁ : D.obj j ⟶ PA) (PA₂ : A' ⟶ PA)
      (PB₁ : D.obj j ⟶ PB) (PB₂ : B' ⟶ PB) (hPA : IsPushout (D.map tA) gA PA₁ PA₂)
      (hPB : IsPushout (D.map tB) gB PB₁ PB₂) (f' : PA ⟶ PB),
      PA₁ ≫ f' = PB₁ ∧
      hPA.desc (c.ι.app j ≫ pA) qA (by simp [hA.w]) ≫ f =
        f' ≫ hPB.desc (c.ι.app j ≫ pB) qB (by simp [hB.w])

alias exists_isPushout_of_isFiltered_of_hom := IndSpreads.exists_isPushout_of_hom

variable (Q : MorphismProperty C)

/-- If `f : X ⟶ Y` is `ind P` and `g : Y ⟶ Z` satisfies `P`, then `f ≫ g : X ⟶ Z` is `ind P`.

This is the key step in showing that `ind P` is stable under composition: it descends `g` to a
finite stage of the filtered colimit presentation of `Y` via `PreIndSpreads`, forms pushouts to
build a presentation of `Z`, and checks that each stage is in `P`. -/
lemma ind_comp_mem {P : MorphismProperty C} [P.IsStableUnderComposition]
    [P.IsStableUnderCobaseChange] [HasPushouts C] [PreIndSpreads.{w} P]
    {X Y Z : C} {f : X ⟶ Y} (hf : ind.{w} P f) {g : Y ⟶ Z} (hg : P g) :
    ind.{w} P (f ≫ g) := by
  obtain ⟨J, _, _, D, sX, tY, htY, hData⟩ := hf
  obtain ⟨j₀, T', g', q, hpush, hg'⟩ := P.exists_isPushout_of_isFiltered htY g hg
  let D' : CategoryTheory.Under j₀ ⥤ C :=
    (CategoryTheory.Under.post D ⋙ CategoryTheory.Under.pushout g') ⋙
      CategoryTheory.Under.forget _
  let c'₀ : Cocone D' :=
    (CategoryTheory.Under.pushout g' ⋙ CategoryTheory.Under.forget _).mapCocone
      ((Cocone.mk _ tY).underPost j₀)
  let c' : Cocone D' := c'₀.extend hpush.isoPushout.inv
  let hc' : IsColimit c' :=
    IsColimit.extendIso _ (isColimitOfPreserves _ (htY.underPost j₀))
  let s' : (Functor.const (CategoryTheory.Under j₀)).obj X ⟶ D' :=
    { app k := sX.app k.right ≫ pushout.inl (D.map k.hom) g'
      naturality k l a := by
        have hnat := sX.naturality a.right
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hnat
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        dsimp [D', CategoryTheory.Under.post, CategoryTheory.Under.pushout]
        rw [Category.assoc, pushout.inl_desc, ← Category.assoc, ← hnat] }
  refine ⟨CategoryTheory.Under j₀, inferInstance, inferInstance,
      D', s', c'.ι, hc', fun k ↦ ⟨?_, ?_⟩⟩
  · exact P.comp_mem _ _ (hData k.right).1 (P.pushout_inl _ _ hg')
  · have hkey : pushout.inl (D.map k.hom) g' ≫ c'₀.ι.app k =
        tY.app k.right ≫ pushout.inl ((Cocone.mk _ tY).ι.app j₀) g' := by
      dsimp [c'₀]
      exact pushout.inl_desc _ _ _
    have hcomp : pushout.inl (D.map k.hom) g' ≫ c'.ι.app k = tY.app k.right ≫ g := by
      simp only [c', Cocone.extend_ι, NatTrans.comp_app, Functor.const_map_app]
      rw [← Category.assoc, hkey, Category.assoc, hpush.inl_isoPushout_inv]
    dsimp only [s']
    rw [Category.assoc, hcomp, ← Category.assoc, (hData k.right).2]

/-- If `P` ind-spreads, then `ind P` is stable under composition, provided the assumptions of
`MorphismProperty.ind_ind` are satisfied: `LocallySmall.{w} C` and
`P ≤ isFinitelyPresentable.{w} C`. -/
lemma IsStableUnderComposition.ind_of_le_isFinitelyPresentable {P : MorphismProperty C}
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [HasPushouts C]
    [PreIndSpreads.{w} P] [LocallySmall.{w} C] (H : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).IsStableUnderComposition where
  comp_mem f g hf hg := by
    rw [← ind_ind H]
    obtain ⟨J, _, _, D, sY, tZ, htZ, hData⟩ := hg
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map f ≫ sY, tZ, htZ, fun k ↦ ⟨?_, ?_⟩⟩
    · simpa using ind_comp_mem hf (hData k).1
    · simpa using f ≫= (hData k).2

/--
A property of morphisms `P` is said to pro-spread if `P`-morphisms into cofiltered limits
descend to a finite level. More precisely, let `Dᵢ` be a cofiltered family of objects.
Then:

- if `f : T ⟶ lim Dᵢ` satisfies `P`, there exists an index `j` and a pullback square
  ```
    T ----f---> lim Dᵢ
    |             |
    |             |
    v             v
    T' ----f'---> Dⱼ
  ```
  such that `f'` satisfies `P`.
-/
class PreProSpreads (P : MorphismProperty C) : Prop where
  exists_isPullback {J : Type w} [SmallCategory J] [IsCofiltered J] {D : J ⥤ C}
    (c : Cone D) (_ : IsLimit c) {T : C} (f : T ⟶ c.pt) :
    P f →
    ∃ (j : J) (T' : C) (f' : T' ⟶ D.obj j) (g : T ⟶ T'),
      IsPullback f g (c.π.app j) f' ∧ P f'

alias exists_isPullback_of_isCofiltered := PreProSpreads.exists_isPullback

lemma PreProSpreads.op_iff (P : MorphismProperty C) :
    PreProSpreads.{w} P.op ↔ PreIndSpreads.{w} P := by
  refine ⟨fun h ↦ ⟨fun {J} _ _ D c hc T f hf ↦ ?_⟩, fun h ↦ ⟨fun {J} _ _ D c hc T f hf ↦ ?_⟩⟩
  · obtain ⟨j, T', f', g, h, hf'⟩ := P.op.exists_isPullback_of_isCofiltered c.op hc.op f.op hf
    exact ⟨j.unop, T'.unop, f'.unop, g.unop, h.unop.flip, hf'⟩
  · obtain ⟨j, T', f', g, h, hf'⟩ := P.exists_isPushout_of_isFiltered
      (isColimitCoconeLeftOpOfCone _ hc) f.unop hf
    exact ⟨j.unop, Opposite.op T', f'.op, g.op, h.op.flip, hf'⟩

instance PreProSpreads.op [PreIndSpreads.{w} P] : PreProSpreads.{w} P.op := by
  rwa [PreProSpreads.op_iff]

/--
- Given a `lim Dᵢ`-morphism `f : A = lim Dᵢ ×_[Dᵢ] A' ⟶ lim Dᵢ ×_[Dⱼ] B' = B` where `Dᵢ ⟶ A'` and
  `Dⱼ ⟶ B'` satisfiy `P`, there exists
  `k ≥ i` and `k ≥ j` and a diagram
  ```
  A ---------------> Dₖ ×_[Dᵢ] A'
  |                      |
  f                      f'
  |                      |
  v                      v
  B ---------------> Dₖ ×_[Dⱼ] B'
  ```.
-/
class ProSpreads (P : MorphismProperty C) : Prop extends PreProSpreads.{w} P where
  exists_isPullback_of_hom {J : Type w} [SmallCategory J] [IsCofiltered J] {D : J ⥤ C}
    (c : Cone D) (_ : IsLimit c)
    {A B A' B' : C} (f : A ⟶ B) (pA : A ⟶ c.pt) (pB : B ⟶ c.pt) (_hf : f ≫ pB = pA)
    {jA jB : J}
    (qA : A ⟶ A') (qB : B ⟶ B') (gA : A' ⟶ D.obj jA) (gB : B' ⟶ D.obj jB)
    (hA : IsPullback pA qA (c.π.app jA) gA)
    (hB : IsPullback pB qB (c.π.app jB) gB) :
    P gA → P gB →
    ∃ (j : J) (tA : j ⟶ jA) (tB : j ⟶ jB) (PA PB : C)
      (PA₁ : PA ⟶ D.obj j) (PA₂ : PA ⟶ A') (PB₁ : PB ⟶ D.obj j) (PB₂ : PB ⟶ B')
      (hPA : IsPullback PA₁ PA₂ (D.map tA) gA) (hPB : IsPullback PB₁ PB₂ (D.map tB) gB)
      (f' : PA ⟶ PB),
      f' ≫ PB₁ = PA₁ ∧
      f ≫ hPB.lift (pB ≫ c.π.app j) qB (by simp [hB.w]) =
        hPA.lift (pA ≫ c.π.app j) qA (by simp [hA.w]) ≫ f'

alias exists_isPullback_of_isCofiltered_of_hom := ProSpreads.exists_isPullback_of_hom

-- TODO: this is in mathlib with the correct assumptions, fix this one
instance [P.IsStableUnderComposition] [PreProSpreads.{w} P] :
    IsStableUnderComposition (pro.{w} P) :=
    sorry

-- TODO: this is in mathlib with the correct assumptions, fix this one
instance [P.IsMultiplicative] [PreProSpreads.{w} P] : (pro.{w} P).IsMultiplicative where

end MorphismProperty

end CategoryTheory
