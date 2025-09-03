/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten, Andrew Yang
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Ind contraction
-/

universe v u

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/-- Let `P` be a property of morphisms. `P.Ind` is satisfied for `f : X ⟶ Y`
if `f = colim fᵢ` where `fᵢ : X ⟶ Yᵢ` satisfies `P`. -/
def Ind : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
    -- `Dᵢ`
    (D : J ⥤ C)
    -- `tᵢ : X ⟶ Dᵢ`
    (t : (Functor.const J).obj X ⟶ D)
    -- `sᵢ : Dᵢ ⟶ Y = colim Dᵢ`
    (s : D ⟶ (Functor.const J).obj Y)
    -- `Y = colim Dᵢ`
    (_ : IsColimit (Cocone.mk _ s)),
    ∀ j, P (t.app j) ∧ t.app j ≫ s.app j = f

class IndSpreads : Prop where
  exists_isPushout : ∀ {J : Type (max u v)} [Category.{v} J] [IsFiltered J] {D : J ⥤ C}
    (c : Cocone D) (_ : IsColimit c)
    (T : C) (f : c.pt ⟶ T) (_ : P f),
    ∃ (j : J) (T' : C) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ P f'
  -- should be modified to "given a presentation as here, there exists a larger index such that
  -- map comes from components"
  exists_isPushout_of_hom : ∀ {J : Type (max u v)} [Category.{v} J] [IsFiltered J] {D : J ⥤ C}
    (c : Cocone D) (_ : IsColimit c)
    {S T : Under c.pt} (_ : P S.hom) (_ : P T.hom) (f : S ⟶ T),
    ∃ (j : J) (S' T' : Under (D.obj j)) (_ : P S'.hom) (_ : P T'.hom)
      (iS : S'.right ⟶ S.right) (iT : T'.right ⟶ T.right)
      (f' : S' ⟶ T'),
        IsPushout (c.ι.app j) S'.hom S.hom iS ∧
        IsPushout (c.ι.app j) T'.hom T.hom iT ∧
        iS ≫ f.right = f'.right ≫ iT

alias exists_isPushout := IndSpreads.exists_isPushout

abbrev under (X : C) : MorphismProperty (Under X) := fun _ _ f ↦ P f.right

namespace IndContraction

variable {C : Type u} [Category.{v} C] (P Q : MorphismProperty C) (X : C)

lemma isFiltered_costructuredArrow_forget' [HasPushouts C]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [HasCoequalizers (P.Under ⊤ X)]
    [PreservesColimitsOfShape WalkingParallelPair (Under.forget P ⊤ X)]
    {S : Under X} :
    IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S) := by
  have : Nonempty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    constructor
    fapply CostructuredArrow.mk
    · exact (Under.mk ⊤ (𝟙 X) (P.id_mem X))
    · fapply CategoryTheory.Under.homMk
      exact S.hom
      simp
  have : IsFilteredOrEmpty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    refine ⟨fun u v ↦ ⟨?_, ?_, ?_, trivial⟩, fun u v f g ↦ ?_⟩
    · fapply CostructuredArrow.mk
      · apply Under.mk ⊤ (u.left.hom ≫ pushout.inl u.left.hom v.left.hom)
          (P.comp_mem _ _ u.left.2 (P.pushout_inl _ _ v.left.2))
      · fapply CategoryTheory.Under.homMk
        · fapply pushout.desc
          · exact u.hom.right
          · exact v.hom.right
          · simp
        · simp
    · fapply CostructuredArrow.homMk
      fapply Under.homMk
      · exact pushout.inl _ _
      · simp
      · simp
      · ext
        simp
    · fapply CostructuredArrow.homMk
      fapply Under.homMk
      · exact pushout.inr _ _
      · simp [pushout.condition]
      · simp
      · ext
        simp
    · refine ⟨?_, ?_, ?_⟩
      · fapply CostructuredArrow.mk
        · exact coequalizer f.left g.left
        · let hc : IsColimit ((Under.forget P ⊤ X).mapCocone (coequalizer.cofork f.left g.left)) :=
            isColimitOfPreserves _ <| colimit.isColimit (parallelPair f.left g.left)
          let s : Cocone (parallelPair f.left g.left ⋙ Under.forget P ⊤ X) := {
            pt := S
            ι.app x := match x with
              | .zero => u.hom
              | .one => v.hom
            ι.naturality i j t := by
              rcases t
              · simpa using u.w _
              · simpa using u.w _
              · simp
          }
          exact hc.desc s
      · fapply CostructuredArrow.homMk
        · apply coequalizer.π
        · show (Under.forget P ⊤ X).map _ ≫ _ = _
          apply
            (isColimitOfPreserves (Under.forget P ⊤ X)
            (colimit.isColimit (parallelPair f.left g.left))).fac
      · ext : 1
        exact coequalizer.condition _ _
  constructor

lemma isFiltered_costructuredArrow_forget [HasPushouts C] [P.IsMultiplicative]
    [P.IsStableUnderCobaseChange] [HasCoequalizers (P.Under ⊤ X)]
    {S : Under X} (hS : IsTerminal S) :
    IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S) := by
  have : Nonempty (CostructuredArrow (Under.forget P ⊤ X) S) :=
    ⟨CostructuredArrow.mk (hS.from ((Under.forget P ⊤ X).obj (Under.mk ⊤ (𝟙 X) (P.id_mem X))))⟩
  have : IsFilteredOrEmpty (CostructuredArrow (Under.forget P ⊤ X) S) := by
    refine ⟨fun u v ↦ ⟨?_, ?_, ?_, trivial⟩, fun u v f g ↦ ?_⟩
    · exact CostructuredArrow.mk <| hS.from
        ((Under.forget P ⊤ X).obj <| Under.mk ⊤ (u.left.hom ≫ pushout.inl u.left.hom v.left.hom)
          (P.comp_mem _ _ u.left.2 (P.pushout_inl _ _ v.left.2)))
    · apply CostructuredArrow.homMk
      · apply hS.hom_ext
      · exact Under.homMk (pushout.inl _ _)
    · apply CostructuredArrow.homMk
      · apply hS.hom_ext
      · exact Under.homMk (pushout.inr _ _) (by simp [pushout.condition])
    · refine ⟨?_, ?_, ?_⟩
      · apply CostructuredArrow.mk
        · exact hS.from _
        · exact coequalizer f.left g.left
      · apply CostructuredArrow.homMk
        · apply hS.hom_ext
        · exact coequalizer.π f.left g.left
      · simpa using coequalizer.condition f.left g.left
  constructor

variable [(Under.forget P ⊤ X).HasLeftKanExtension (Under.forget P ⊤ X)]

variable (R) in
noncomputable
def indContraction :
    Under X ⥤ Under X :=
  (Under.forget P ⊤ X).leftKanExtension (Under.forget P ⊤ X)

variable [(Under.forget P ⊤ X).HasPointwiseLeftKanExtension (Under.forget P ⊤ X)]

variable {X} in
noncomputable
def indContractionCocone (S : Under X) :
    Cocone (CostructuredArrow.proj (Under.forget P ⊤ X) S ⋙
      (Under.forget P ⊤ X)) where
  pt := (indContraction P X).obj S
  ι := (colimit.cocone _).ι ≫ (Functor.const _).map
    (CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _).inv

variable {X} in
noncomputable
def isColimitIndContractionCocone (S : Under X) :
    IsColimit (indContractionCocone P S) :=
  .ofIsoColimit (colimit.isColimit _)
    (Cocones.ext (CategoryTheory.Functor.leftKanExtensionObjIsoColimit _ _ _).symm)

variable {X} in
noncomputable
def fromIndContraction (S : Under X) : (indContraction P X).obj S ⟶ S :=
  letI c : Cocone (CostructuredArrow.proj (Under.forget P ⊤ X) S ⋙
      (Under.forget P ⊤ X)) :=
    { pt := S
      ι.app Y := Y.hom
      ι.naturality i j f := by simpa using f.w }
  (isColimitIndContractionCocone P S).desc c

@[simp]
lemma ι_fromIndContraction (S : Under X)
    (Y : CostructuredArrow (Under.forget P ⊤ X) S) :
    (indContractionCocone P S).ι.app Y ≫ fromIndContraction P S = Y.hom :=
  (isColimitIndContractionCocone P S).fac _ _

/-- The `P`-ind contraction of `X ⟶ S` is ind-`P` over `X`. -/
lemma property_indContraction_hom (S : Under X) : P.Ind ((indContraction P X).obj S).hom :=
  sorry

lemma exists_costructuredArrow_aux [HasPushouts C] [IndSpreads P]
    {S : Under X} (hS : ∀ {T : Under X} (g : S ⟶ T), P g.right → Q g.right →
      ∃ (s : T ⟶ S), g ≫ s = 𝟙 S)
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]
    {T : Under X}
    (f : (indContraction P X).obj S ⟶ T)
    (hPf : P f.right)
    (hQf : Q f.right)
    (j : CostructuredArrow (Under.forget P ⊤ X) S)
    (T' : C)
    (f' : ((CostructuredArrow.proj _ _ ⋙ Under.forget P ⊤ X) ⋙ CategoryTheory.Under.forget X).obj j ⟶ T')
    (g : T' ⟶ T.right)
    (h : IsPushout ((indContractionCocone P S).ι.app j).right f' f.right g)
    (hf' : P f') :
    ∃ (T'' : CostructuredArrow (Under.forget P ⊤ X) S), T''.left.right = T' := by
  let c := ((CategoryTheory.Under.forget X).mapCocone (indContractionCocone P S))
  let Pt : Under X :=
    CategoryTheory.Under.mk (T.hom ≫ pushout.inl f.right (fromIndContraction P S).right)
  let gu : S ⟶ Pt := CategoryTheory.Under.homMk (pushout.inr _ _)
    (by
      rw [← CategoryTheory.Under.w (fromIndContraction P S), Category.assoc]
      simp [← pushout.condition, Pt])
  obtain ⟨su, hsu⟩ := hS gu (P.pushout_inr _ _ hPf) (Q.pushout_inr _ _ hQf)
  let T'' : CostructuredArrow (Under.forget P ⊤ X) S :=
      ⟨MorphismProperty.Under.mk ⊤ (j.1.hom ≫ f') (P.comp_mem _ _ j.1.2 hf'), ⟨⟨⟩⟩,
      CategoryTheory.Under.homMk g (by simp [← h.w]) ≫
        CategoryTheory.Under.homMk (pushout.inl _ _) rfl ≫ su⟩
  use T''
  rfl

/--
Think: `P = étale` and `Q = surjective on Spec`. Assume that for every `X : C`
there exists `S : C` and `X ⟶ S` satisfying `Q` that is contractible
wrt. `P ⊓ Q`-covers (i.e. étale, faithfully flat).

Then also the ind-contraction is contractible wrt. `P ⊓ Q`-covers.
-/
lemma exists_comp_eq_id [HasPushouts C]
    [IndSpreads P]
    {S : Under X}
    (hS : ∀ {T : Under X} (g : S ⟶ T), P g.right → Q g.right →
      ∃ (s : T ⟶ S), g ≫ s = 𝟙 S)
    [IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S)]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]
    {T : Under X} (f : (indContraction P X).obj S ⟶ T) (hPf : P f.right) (hQf : Q f.right) :
    ∃ (g : T ⟶ (indContraction P X).obj S),
      f ≫ g = 𝟙 ((indContraction P X).obj S) := by
  let c := ((CategoryTheory.Under.forget X).mapCocone (indContractionCocone P S))
  obtain ⟨j, T', f', g, h, hf'⟩ :=
    IndSpreads.exists_isPushout (P := P) (J := (CostructuredArrow (Under.forget P ⊤ X) S))
    (D := (CostructuredArrow.proj ((Under.forget P ⊤ X)) S ⋙
      ((Under.forget P ⊤ X))) ⋙ CategoryTheory.Under.forget X) c
    (isColimitOfPreserves _ <| isColimitIndContractionCocone P S) T.right f.right hPf
  let Pt : Under X :=
    CategoryTheory.Under.mk (T.hom ≫ pushout.inl f.right (fromIndContraction P S).right)
  let gu : S ⟶ Pt := CategoryTheory.Under.homMk (pushout.inr _ _)
    (by
      rw [← CategoryTheory.Under.w (fromIndContraction P S), Category.assoc]
      simp [← pushout.condition, Pt])
  obtain ⟨su, hsu⟩ := hS gu (P.pushout_inr _ _ hPf) (Q.pushout_inr _ _ hQf)
  let T'' : CostructuredArrow (Under.forget P ⊤ X) S :=
      ⟨MorphismProperty.Under.mk ⊤ (j.1.hom ≫ f') (P.comp_mem _ _ j.1.2 hf'), ⟨⟨⟩⟩,
      CategoryTheory.Under.homMk g (by simp [← h.w, c]) ≫
        CategoryTheory.Under.homMk (pushout.inl _ _) rfl ≫ su⟩
  refine ⟨CategoryTheory.Under.homMk (h.desc (𝟙 _) (c.ι.app T'') ?_) ?_, ?_⟩
  · let f'' : j ⟶ T'' := CostructuredArrow.homMk (Under.homMk f' rfl) ?_
    · simpa using (c.w f'').symm
    · ext
      simp only [Comma.forget_obj, Functor.id_obj, Functor.const_obj_obj, Comma.forget_map,
        Under.homMk_hom, Under.comp_right, Under.homMk_right, T'']
      rw [← h.w_assoc, pushout.condition_assoc]
      have : pushout.inr f.right (fromIndContraction P S).right ≫ su.right = 𝟙 _ :=
        congr($(hsu).right)
      simp only [Functor.comp_obj, CostructuredArrow.proj_obj, Comma.forget_obj, Under.forget_obj,
        Functor.mapCocone_pt, Functor.const_obj_obj, Functor.mapCocone_ι_app, Under.forget_map,
        this, Category.comp_id, c]
      apply congr($(ι_fromIndContraction P X S j).right)
  · have : T.hom = j.1.hom ≫ f' ≫ g := by
      have : c.ι.app j = ((indContractionCocone P S).ι.app j).right := rfl
      simp [← h.w, this]
    rw [this]
    simp only [Functor.const_obj_obj, Functor.id_obj, Category.assoc, IsPushout.inr_desc]
    rw [← Category.assoc]
    exact CategoryTheory.Under.w ((indContractionCocone P S).ι.app T'')
  · apply (CategoryTheory.Under.forget _).map_injective
    exact h.inl_desc _ _ _

lemma exists_comp_eq_id' [HasPushouts C]
    [IndSpreads P] {S : Under X}
    (hS : ∀ {T : Under X} (g : S ⟶ T), P g.right → Q g.right →
      ∃ (s : T ⟶ S), g ≫ s = 𝟙 S)
    [IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S)]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]
    {T : C} (f : ((indContraction P X).obj S).right ⟶ T) (hPf : P f) (hQf : Q f) :
    ∃ (g : T ⟶ ((indContraction P X).obj S).right),
      f ≫ g = 𝟙 (((indContraction P X).obj S)).right := by
  let T' : Under X := CategoryTheory.Under.mk (((indContraction P X).obj S).hom ≫ f)
  let f' : ((indContraction P X).obj S) ⟶ T' := CategoryTheory.Under.homMk f rfl
  obtain ⟨g, hg⟩ := exists_comp_eq_id P Q X hS f' hPf hQf
  use g.right, congr($(hg).right)

/--
Think: `P = étale` and `Q = surjective on Spec`. Assume that

- for every `X : C`
  there exists `S : C` and `X ⟶ S` satisfying `Q` that is contractible
  wrt. `P ⊓ Q`-covers (i.e. étale, faithfully flat).
- `Q` has a cancellation property (satisfied for e.g. `Q = surjective on Spec`).

Then the ind-contraction is contractible wrt. ind-`P`-covers that also satisfy `Q`.
-/
lemma exists_comp_eq_id_of_ind
    [Q.HasOfPostcompProperty ⊤]
    [HasPushouts C]
    [IndSpreads P] {S : Under X}
    (hS : ∀ {T : Under X} (g : S ⟶ T), P g.right → Q g.right →
      ∃ (s : T ⟶ S), g ≫ s = 𝟙 S)
    [IsFiltered (CostructuredArrow (Under.forget P ⊤ X) S)]
    [P.IsMultiplicative] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]
    {T : Under X} (f : (indContraction P X).obj S ⟶ T) (hPf : P.Ind f.right) (hQf : Q f.right) :
    ∃ (g : T ⟶ (indContraction P X).obj S),
      f ≫ g = 𝟙 ((indContraction P X).obj S) := by
  obtain ⟨J, _, _, D, t, s, hc, h⟩ := hPf
  choose g hg using fun j : J ↦ exists_comp_eq_id' P Q X hS (t.app j) (h j).1
    (Q.of_postcomp (W' := ⊤) _ (s.app j) trivial (by rwa [(h j).2]))
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  let st : Cocone D :=
  { pt := ((indContraction P X).obj S).right,
    ι.app := g
    ι.naturality {i j} u := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      let c := ((CategoryTheory.Under.forget X).mapCocone (indContractionCocone P S))
      obtain ⟨k, S', T', hPS', hPT', iS, iT, f', hSpush, hTpush, heq⟩ :=
        IndSpreads.exists_isPushout_of_hom (P := P) (J := (CostructuredArrow (Under.forget P ⊤ X) S))
        (D := (CostructuredArrow.proj ((Under.forget P ⊤ X)) S ⋙
          ((Under.forget P ⊤ X))) ⋙ CategoryTheory.Under.forget X) c
        (isColimitOfPreserves _ <| isColimitIndContractionCocone P S)
        (S := CategoryTheory.Under.mk (t.app i))
        (T := CategoryTheory.Under.mk (t.app j)) (h i).1 (h j).1
        (CategoryTheory.Under.homMk (D.map u) (by simp [← t.naturality]))
      simp at heq
      apply hSpush.hom_ext
      · simp [← t.naturality_assoc, hg]
      · simp [reassoc_of% heq]
        -- this is probably wrong
        sorry
    }
  have hsection : f.right ≫ hc.desc st = 𝟙 ((indContraction P X).obj S).right := by
    dsimp only [Under.comp_right, Under.homMk_right, Under.id_right]
    rw [← (h j).2]
    rw [← hg j]
    simp only [Functor.const_obj_obj, Category.assoc]
    congr 1
    apply hc.fac
  refine ⟨?_, ?_⟩
  · fapply CategoryTheory.Under.homMk
    · exact hc.desc st
    · rw [← CategoryTheory.Under.w f, Category.assoc, hsection]
      simp
  · ext
    exact hsection

end IndContraction

end MorphismProperty

end CategoryTheory
