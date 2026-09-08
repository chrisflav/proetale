/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## TODOs:

- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

universe s t w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

instance (X : C) [HasFilteredColimits C] : ReflectsFilteredColimits (Under.forget X) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms

open Opposite

namespace ObjectProperty

lemma ind_of_univLE (P : ObjectProperty C) [UnivLE.{w', w}] :
    ind.{w'} P ≤ ind.{w} P := by
  intro X ⟨J, _, _, pres, H⟩
  exact of_essentiallySmall_index pres H

@[gcongr]
lemma ind_mono {P Q : ObjectProperty C} (h : P ≤ Q) :
    ind.{w} P ≤ ind.{w} Q := by
  intro X ⟨J, _, _, pres, H⟩
  exact ⟨J, inferInstance, inferInstance, pres, fun i ↦ h _ (H i)⟩

end ObjectProperty

namespace MorphismProperty

instance [P.ContainsIdentities] : (ind.{w} P).ContainsIdentities where
  id_mem X := le_ind _ _ (P.id_mem X)

lemma ind_of_univLE [UnivLE.{w', w}] : ind.{w'} P ≤ ind.{w} P := by
  intro X Y f hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hf ⊢
  exact ObjectProperty.ind_of_univLE P.underObj _ hf

@[gcongr]
lemma underObj_mono {P Q : MorphismProperty C} (h : P ≤ Q) (X : C) :
    P.underObj (X := X) ≤ Q.underObj (X := X) :=
  fun _ ↦ h _

@[gcongr]
lemma ind_mono {P Q : MorphismProperty C} (h : P ≤ Q) : ind.{w} P ≤ ind.{w} Q := by
  intro X Y f hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hf ⊢
  apply ObjectProperty.ind_mono _ _ hf
  gcongr

lemma ind_coconeι {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    (j : J) (H : ∀ {i : J} (f : j ⟶ i), P (D.map f)) :
    ind.{w} P (c.ι.app j) := by
  refine ⟨Under j, inferInstance, inferInstance, Under.post D ⋙ CategoryTheory.Under.forget _,
      ?_, ?_, ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · exact
      { app i := D.map i.hom
        naturality := by simp [← Functor.map_comp] }
  · exact ((CategoryTheory.Under.forget _).mapCocone (c.underPost j)).ι
  · exact isColimitOfPreserves (CategoryTheory.Under.forget _) (hc.underPost j)
  · apply H
  · simp

variable {P}

/-- If `P`-morphisms are finitely presentable and `P` cancels from the left, then `ind P`
cancels `P`-morphisms from the left: if `f` satisfies `P` and `f ≫ g` satisfies `ind P`,
then `g` satisfies `ind P`. -/
lemma ind_hasOfPrecompProperty [P.HasOfPrecompProperty P]
    (hP : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).HasOfPrecompProperty P where
  of_precomp {X Y Z} f g hf hfg := by
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hfg
    obtain ⟨j₀, q, hq1, hq2⟩ := exists_hom_of_isFinitelyPresentable hs (hP _ hf) t g
      fun j ↦ (hts j).2
    refine ⟨CategoryTheory.Under j₀, inferInstance, inferInstance,
      CategoryTheory.Under.post D ⋙ CategoryTheory.Under.forget _,
      { app k := q ≫ D.map k.hom
        naturality {k l} a := by
          dsimp
          rw [Category.id_comp, Category.assoc, ← Functor.map_comp, CategoryTheory.Under.w a] },
      ((CategoryTheory.Under.forget _).mapCocone ((Cocone.mk _ s).underPost j₀)).ι,
      isColimitOfPreserves (CategoryTheory.Under.forget _) (hs.underPost j₀),
      fun k ↦ ⟨?_, ?_⟩⟩
    · have ht : f ≫ q ≫ D.map k.hom = t.app k.right := by
        rw [← Category.assoc, hq1]
        simpa using (t.naturality k.hom).symm
      exact MorphismProperty.of_precomp (W := P) (W' := P) f _ hf
        (by rw [ht]; exact (hts k.right).1)
    · change (q ≫ D.map k.hom) ≫ s.app k.right = g
      rw [Category.assoc, show D.map k.hom ≫ s.app k.right = s.app j₀ from by simp]
      exact hq2

/-- Cancellation for ind-`P`-morphisms: if `f` and `f ≫ g` satisfy `ind P`, then so does `g`,
provided `P`-morphisms are finitely presentable, `P` is stable under cobase change and `P`
cancels from the left. -/
lemma ind_hasOfPrecompProperty_ind [HasPushouts C] [P.IsStableUnderCobaseChange]
    [P.HasOfPrecompProperty P] [LocallySmall.{w} C]
    (hP : P ≤ isFinitelyPresentable.{w} C) :
    (ind.{w} P).HasOfPrecompProperty (ind.{w} P) where
  of_precomp {X Y Z} f g hf hfg := by
    haveI : (ind.{w} P).HasOfPrecompProperty P := ind_hasOfPrecompProperty hP
    rw [← ind_ind hP]
    obtain ⟨I, _, _, B, t, c, hc, htc⟩ := hf
    -- Each composite `Bᵢ ⟶ Y ⟶ Z` is ind-`P`.
    have hind (i : I) : ind.{w} P (c.app i ≫ g) := by
      refine MorphismProperty.of_precomp (W := ind.{w} P) (W' := P) (t.app i) _ (htc i).1 ?_
      rw [← Category.assoc, (htc i).2]
      exact hfg
    -- The filtered diagram of pushouts `Y ⨿_{Bᵢ} Z`.
    let E : I ⥤ C :=
      { obj i := pushout (c.app i) (c.app i ≫ g)
        map {i i'} a := pushout.desc (pushout.inl _ _) (pushout.inr _ _) (by
          have hnat : c.app i = B.map a ≫ c.app i' := by simp
          rw [hnat]
          simp only [Category.assoc, pushout.condition])
        map_id i := by apply pushout.hom_ext <;> simp
        map_comp {i i' i''} a b := by apply pushout.hom_ext <;> simp }
    have hinl {i i' : I} (a : i ⟶ i') :
        pushout.inl (c.app i) (c.app i ≫ g) ≫ E.map a =
          pushout.inl (c.app i') (c.app i' ≫ g) := by
      simp [E]
    have hinr {i i' : I} (a : i ⟶ i') :
        pushout.inr (c.app i) (c.app i ≫ g) ≫ E.map a =
          pushout.inr (c.app i') (c.app i' ≫ g) := by
      simp [E]
    have hinlw : ∀ (w : Cocone E) {i i' : I} (a : i ⟶ i'),
        pushout.inl (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
          pushout.inl (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := fun w i i' a ↦ by
      rw [← w.w a, ← Category.assoc, hinl a]
    have hinrw : ∀ (w : Cocone E) (i i' : I),
        pushout.inr (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
          pushout.inr (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := by
      have h1 : ∀ (w : Cocone E) {i i' : I} (a : i ⟶ i'),
          pushout.inr (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
            pushout.inr (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := fun w i i' a ↦ by
        rw [← w.w a, ← Category.assoc, hinr a]
      intro w i i'
      exact (h1 w (IsFiltered.leftToMax i i')).trans (h1 w (IsFiltered.rightToMax i i')).symm
    obtain ⟨i₀⟩ : Nonempty I := IsFiltered.nonempty
    refine ⟨I, ‹_›, ‹_›, E,
      { app i := pushout.inl _ _
        naturality {i i'} a := by
          dsimp
          rw [Category.id_comp, hinl a] },
      { app i := pushout.desc (f := c.app i) (g := c.app i ≫ g) g (𝟙 Z) (by simp)
        naturality {i i'} a := by
          apply pushout.hom_ext <;> simp [E] },
      ?_, fun i ↦ ⟨(ind.{w} P).pushout_inl _ _ (hind i), by simp⟩⟩
    -- `Z` is the colimit of the pushout diagram.
    refine
      { desc := fun w ↦ pushout.inr (c.app i₀) (c.app i₀ ≫ g) ≫ w.ι.app i₀
        fac := fun w i ↦ ?_
        uniq := fun w m hm ↦ ?_ }
    · dsimp only
      rw [hinrw w i₀ i]
      apply pushout.hom_ext
      · -- check on `Y` using that `Y = colim Bᵢ`
        rw [pushout.inl_desc_assoc]
        refine hc.hom_ext fun j ↦ ?_
        have hwk := hinrw w i (IsFiltered.max i j)
        have hil := hinlw w (IsFiltered.leftToMax i j)
        have hcb : B.map (IsFiltered.rightToMax i j) ≫ c.app (IsFiltered.max i j) =
            c.app j := by simp
        dsimp only
        rw [hwk, hil, ← hcb]
        simp only [Category.assoc, pushout.condition_assoc]
      · rw [pushout.inr_desc_assoc, Category.id_comp]
    · rw [← hm i₀]
      dsimp only
      rw [← Category.assoc, pushout.inr_desc, Category.id_comp]

/--
Let `P` be a property of morphisms. `P.Pro` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : Xᵢ ⟶ Y` and `sᵢ : X ⟶ Xᵢ` indexed by `J`
such that
- `J` is cofiltered
- `X = lim Xᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = sᵢ ≫ tᵢ` for all `i`.
-/
def pro (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCofiltered J)
    (D : J ⥤ C) (t : D ⟶ (Functor.const J).obj Y) (s : (Functor.const J).obj X ⟶ D)
    (_ : IsLimit (Cone.mk _ s)), ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

lemma pro_eq_unop_ind_op : pro.{w} P = (ind.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, isColimitOfUnop hs, fun j ↦ ⟨(hst j.1).1, by simp [← (hst j.1).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isLimitOfCoconeRightOpOfCone D.leftOp hs, fun j ↦ ⟨(hst _).1,
      op_injective (hst _).2⟩⟩

lemma ind_eq_unop_pro_op : ind.{w} P = (pro.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, hs.op, fun j ↦ ⟨(hst j.unop).1, by simp [← (hst j.unop).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isColimitCoconeLeftOpOfCone D hs, fun j ↦ ⟨(hst j.unop).1,
      Quiver.Hom.op_inj (hst j.unop).2⟩⟩

@[gcongr]
lemma unop_mono {P Q : MorphismProperty Cᵒᵖ} (h : P ≤ Q) : P.unop ≤ Q.unop :=
  fun _ _ _ hf ↦ h _ hf

@[gcongr]
lemma op_mono {P Q : MorphismProperty C} (h : P ≤ Q) : P.op ≤ Q.op :=
  fun _ _ _ hf ↦ h _ hf

variable (P) in
lemma le_pro : P ≤ pro.{w} P := by
  rw [pro_eq_unop_ind_op]
  conv_lhs => rw [← unop_op P]
  exact unop_mono P.op.le_ind

instance [P.ContainsIdentities] : (pro.{w} P).ContainsIdentities where
  id_mem X := le_pro _ _ (P.id_mem X)

lemma op_isFinitelyPresentable :
    (isFinitelyPresentable.{w} C).op = isFinitelyPresentable.{w} Cᵒᵖ :=
  sorry

lemma pro_pro [LocallySmall.{w} C] (H : P ≤ isFinitelyPresentable.{w} C) :
    pro.{w} (pro.{w} P) = pro.{w} P := by
  rw [pro_eq_unop_ind_op, pro_eq_unop_ind_op, op_unop, ind_ind]
  rw [← op_isFinitelyPresentable]
  exact P.op_mono H

lemma pro_of_univLE [UnivLE.{w', w}] :
    pro.{w'} P ≤ pro.{w} P := by
  grw [pro_eq_unop_ind_op, pro_eq_unop_ind_op]
  exact unop_mono (ind_of_univLE P.op)

@[gcongr]
lemma pro_mono {P Q : MorphismProperty C} (h : P ≤ Q) : pro.{w} P ≤ pro.{w} Q := by
  grw [pro_eq_unop_ind_op, pro_eq_unop_ind_op]
  gcongr

lemma pro_coneπ {J : Type w} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c)
    (j : J) (H : ∀ {i : J} (f : i ⟶ j), P (D.map f)) :
    pro.{w} P (c.π.app j) := by
  rw [pro_eq_unop_ind_op]
  exact ind_coconeι P.op hc.op _ (fun _ ↦ H _)

instance {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] :
    (pro.{w} P).IsStableUnderBaseChangeAlong f where
  of_isPullback {Z W f' g' g} pb hg := by
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hg
    -- `J` is connected, so `Over.forget` reflects `J`-indexed limits
    have : IsConnected J := IsCofiltered.isConnected J
    -- the diagram `D` as a diagram in `Over Y` via the structure maps `t`
    let DY : J ⥤ CategoryTheory.Over Y := CategoryTheory.Over.lift D t
    -- the limit cone `(Z, s)` lifted to a limit cone in `Over Y` with apex `Over.mk g`
    let cY : Cone DY := CategoryTheory.Over.liftCone D t (Cone.mk _ s) g (fun j ↦ (hts j).2)
    have hcY : IsLimit cY :=
      CategoryTheory.Over.isLimitLiftCone D t (Cone.mk _ s) g (fun j ↦ (hts j).2) hs
    -- `Over.pullback f` preserves all limits, being a right adjoint
    have : PreservesLimitsOfSize.{w, w} (CategoryTheory.Over.pullback f) :=
      (CategoryTheory.Over.mapPullbackAdj f).rightAdjoint_preservesLimits
    -- push the limit cone to `Over X` along `Over.pullback f` and forget back to `C`
    let cX : Cone ((DY ⋙ CategoryTheory.Over.pullback f) ⋙ CategoryTheory.Over.forget X) :=
      (CategoryTheory.Over.forget X).mapCone ((CategoryTheory.Over.pullback f).mapCone cY)
    have hcX : IsLimit cX :=
      isLimitOfPreserves (CategoryTheory.Over.forget X)
        (isLimitOfPreserves (CategoryTheory.Over.pullback f) hcY)
    refine ⟨J, inferInstance, inferInstance,
      DY ⋙ CategoryTheory.Over.pullback f ⋙ CategoryTheory.Over.forget X,
      { app j := ((DY ⋙ CategoryTheory.Over.pullback f).obj j).hom
        naturality i j u :=
          (CategoryTheory.Over.w ((DY ⋙ CategoryTheory.Over.pullback f).map u)).trans
            (by simp) },
      (Functor.const J).map pb.isoPullback.hom ≫ cX.π, ?_, fun j ↦ ⟨?_, ?_⟩⟩
    · refine hcX.ofIsoLimit (Cone.ext pb.isoPullback.symm (fun j ↦ ?_))
      simp only [NatTrans.comp_app, Functor.const_map_app, Iso.symm_hom]
      exact (Iso.inv_hom_id_assoc _ _).symm
    · exact P.pullback_snd _ f (hts j).1
    · have hsnd : cX.π.app j ≫ ((DY ⋙ CategoryTheory.Over.pullback f).obj j).hom =
          pullback.snd g f :=
        CategoryTheory.Over.w (((CategoryTheory.Over.pullback f).mapCone cY).π.app j)
      simp only [NatTrans.comp_app, Functor.const_map_app, Category.assoc]
      exact (congrArg (pb.isoPullback.hom ≫ ·) hsnd).trans pb.isoPullback_hom_snd

end CategoryTheory.MorphismProperty
