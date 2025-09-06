/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## TODOs:

- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

universe s t w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/-- The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`. -/
@[simps]
def Under.lift {J : Type*} [Category J] (D : J ⥤ C) {X : C} (s : (Functor.const J).obj X ⟶ D) :
    J ⥤ Under X where
  obj j := Under.mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)

/-- The induced cocone on `Under X` from on the lifted functor. -/
@[simps]
def Under.liftCocone {J : Type*} [Category J] (D : J ⥤ C) {X : C} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p) :
    Cocone (Under.lift D s) where
  pt := Under.mk p
  ι.app j := Under.homMk (c.ι.app j)

/-- The lifted cocone on `Under X` is a colimit cocone if the original cocone was colimiting
and `J` is nonempty. -/
def Under.isColimitLiftCocone {J : Type*} [Category J] [Nonempty J]
    (D : J ⥤ C) {X : C} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p) :
    IsColimit c → IsColimit (Under.liftCocone D s c p hp) := by
  refine fun hc ↦ ⟨fun s ↦ ?_, fun _ _ ↦ ?_, ?_⟩
  · refine CategoryTheory.Under.homMk ?_ ?_
    · exact hc.desc ((CategoryTheory.Under.forget _).mapCocone s)
    · obtain ⟨j⟩ : Nonempty J := ‹_›
      simp only [liftCocone_pt, Functor.const_obj_obj, mk_right, Functor.id_obj, mk_hom, ← hp j,
        Category.assoc, IsColimit.fac, Functor.mapCocone_pt, forget_obj, Functor.mapCocone_ι_app,
        lift_obj, forget_map]
      apply CategoryTheory.Under.w (s.ι.app j)
  · ext; simp [hc.fac]
  · intro c m hm
    ext
    refine hc.hom_ext fun j ↦ ?_
    simpa [hc.fac] using congr($(hm j).right)

open IsFiltered in
instance {J : Type*} [Category J] [IsFilteredOrEmpty J] : IsFiltered (WithInitial J) where
  cocone_objs x y :=
    match x, y with
    | .star, y => ⟨y, ⟨⟩, 𝟙 y, trivial⟩
    | x, .star => ⟨x, 𝟙 x, ⟨⟩, trivial⟩
    | .of x, .of y => ⟨.of <| max x y, leftToMax _ _, rightToMax _ _, trivial⟩
  cocone_maps x y f g :=
    match x, y with
    | .star, y => ⟨y, 𝟙 _, rfl⟩
    | _, .star => ⟨.star, 𝟙 _, (IsIso.eq_inv_comp f).mp rfl⟩
    | .of _, .of _ => ⟨.of <| coeq f g, coeqHom _ _, coeq_condition _ _⟩

instance (X : C) [HasFilteredColimits C] : ReflectsFilteredColimits (Under.forget X) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms

open Opposite

lemma IsFinitelyPresentable.exists_hom_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f := by
  have : PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) := by
    rw [← isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
    infer_instance
  exact Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

lemma IsFinitelyPresentable.exists_eq_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v := by
  have : PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) := by
    rw [← isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
    infer_instance
  exact
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h

lemma IsFinitelyPresentable.exists_hom_of_isColimit_under
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    {X A : C} (p : X ⟶ A) (s : (Functor.const J).obj X ⟶ D)
    [IsFinitelyPresentable.{w} (Under.mk p)]
    (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f := by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)

namespace Limits

/-- A colimit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`. -/
structure ColimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : Dᵢ ⟶ X`. -/
  natTrans : diag ⟶ (Functor.const J).obj X
  /-- `X` is the colimit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsColimit (Cocone.mk _ natTrans)

variable {J : Type w} [Category.{t} J] {X : C}

namespace ColimitPresentation

/-- The cocone associated to a colimit presentation. -/
abbrev cocone (pres : ColimitPresentation J X) : Cocone pres.diag :=
  Cocone.mk _ pres.natTrans

/-- The canonical colimit presentation of any object over a point. -/
@[simps]
noncomputable
def self (X : C) : ColimitPresentation PUnit.{s + 1} X where
  diag := (Functor.const _).obj X
  natTrans := 𝟙 _
  isColimit := isColimitConstCocone _ _

/-- If `F` preserves colimits of shape `J`, it maps colimit presentations of `X` to
colimit presentations of `F(X)`. -/
noncomputable
def map (P : ColimitPresentation J X) {D : Type*} [Category D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : ColimitPresentation J (F.obj X) where
  diag := P.diag ⋙ F
  natTrans := Functor.whiskerRight P.natTrans F ≫ (F.constComp _ _).hom
  isColimit := by
    convert isColimitOfPreserves F P.isColimit
    ext j
    simp

section

variable {J : Type*} {I : J → Type*} [Category J] [∀ j, Category (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

set_option linter.unusedVariables false in
/-- The type underlying the category used in the construction of the composition
of colimit presentations. This is simply `Σ j, I j` but with a different category structure. -/
@[nolint unusedArguments]
def Total (P : ∀ j, ColimitPresentation (I j) (D.obj j)) : Type _ :=
  Σ j, I j

variable (P) in
/-- Constructor for `Total` to guide type checking. -/
abbrev Total.mk (i : J) (k : I i) : Total P := ⟨i, k⟩

/-- Morphisms in the `Total` category. -/
@[ext]
structure Total.Hom (k l : Total P) where
  /-- The underlying morphism in the first component. -/
  base : k.1 ⟶ l.1
  /-- A morphism in `C`. -/
  hom : (P k.1).diag.obj k.2 ⟶ (P l.1).diag.obj l.2
  w : (P k.1).natTrans.app k.2 ≫ D.map base = hom ≫ (P l.1).natTrans.app l.2 := by aesop_cat

attribute [reassoc] Total.Hom.w

/-- Composition of morphisms in the `Total` category. -/
@[simps]
def Total.Hom.comp {k l m : Total P} (f : k.Hom l) (g : l.Hom m) : k.Hom m where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  w := by
    simp only [Functor.const_obj_obj, Functor.map_comp, Category.assoc]
    rw [f.w_assoc, g.w]

@[simps! id_base id_hom comp_base comp_hom]
instance : Category (Total P) where
  Hom := Total.Hom
  id _ := { base := 𝟙 _, hom := 𝟙 _ }
  comp := Total.Hom.comp

section Small

variable {J : Type w} {I : J → Type w} [SmallCategory J] [∀ j, SmallCategory (I j)]
  {D : J ⥤ C} {P : ∀ j, ColimitPresentation (I j) (D.obj j)}

lemma Total.exists_hom_of_hom {j j' : J} (i : I j) (u : j ⟶ j')
    [IsFiltered (I j')] [IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    ∃ (i' : I j') (f : Total.mk P j i ⟶ Total.mk P j' i'), f.base = u := by
  obtain ⟨i', q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit (P j').isColimit
    ((P j).natTrans.app i ≫ D.map u)
  use i', { base := u, hom := q, w := by simp [← hq] }

instance [IsFiltered J] [∀ j, IsFiltered (I j)] : Nonempty (Total P) := by
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨i⟩ : Nonempty (I j) := IsFiltered.nonempty
  exact ⟨⟨j, i⟩⟩

instance [IsFiltered J] [∀ j, IsFiltered (I j)]
    [∀ j i, IsFinitelyPresentable.{w} ((P j).diag.obj i)] :
    IsFiltered (Total P) where
  cocone_objs k l := by
    let a := IsFiltered.max k.1 l.1
    obtain ⟨a', f, hf⟩ := Total.exists_hom_of_hom (P := P) k.2 (IsFiltered.leftToMax k.1 l.1)
    obtain ⟨b', g, hg⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.rightToMax k.1 l.1)
    refine ⟨⟨a, IsFiltered.max a' b'⟩, ?_, ?_, trivial⟩
    · exact f ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.leftToMax _ _) }
    · exact g ≫ { base := 𝟙 _, hom := (P _).diag.map (IsFiltered.rightToMax _ _) }
  cocone_maps {k l} f g := by
    let a := IsFiltered.coeq f.base g.base
    obtain ⟨a', u, hu⟩ := Total.exists_hom_of_hom (P := P) l.2 (IsFiltered.coeqHom f.base g.base)
    have : (f.hom ≫ u.hom) ≫ (P _).natTrans.app _ = (g.hom ≫ u.hom) ≫ (P _).natTrans.app _ := by
      simp only [Category.assoc, Functor.const_obj_obj, ← u.w, ← f.w_assoc, ← g.w_assoc]
      rw [← Functor.map_comp, hu, IsFiltered.coeq_condition f.base g.base]
      simp
    obtain ⟨j, p, q, hpq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit (P _).isColimit _ _ this
    dsimp at p q
    refine ⟨⟨a, IsFiltered.coeq p q⟩,
      u ≫ { base := 𝟙 _, hom := (P _).diag.map (p ≫ IsFiltered.coeqHom p q) }, ?_⟩
    apply Total.Hom.ext
    · simp [hu, IsFiltered.coeq_condition f.base g.base]
    · rw [Category.assoc] at hpq
      simp only [Functor.map_comp, comp_hom, reassoc_of% hpq]
      simp [← Functor.map_comp, ← IsFiltered.coeq_condition]

/-- If `P` is a colimit presentation over `J` of `X` and for every `j` we are given a colimit
presentation `Qⱼ` over `I j` of the `P.diag.obj j`, this is the refined colimit presentation of `X`
over `Total Q`. -/
@[simps]
def bind {X : C} (P : ColimitPresentation J X) (Q : ∀ j, ColimitPresentation (I j) (P.diag.obj j))
    [∀ j, IsFiltered (I j)] [∀ j i, IsFinitelyPresentable.{w} ((Q j).diag.obj i)] :
    ColimitPresentation (Total Q) X where
  diag.obj k := (Q k.1).diag.obj k.2
  diag.map {k l} f := f.hom
  natTrans.app k := (Q k.1).natTrans.app k.2 ≫ P.natTrans.app k.1
  natTrans.naturality {k l} u := by simp [← u.w_assoc]
  isColimit.desc c := P.isColimit.desc
    { pt := c.pt
      ι.app j := (Q j).isColimit.desc
        { pt := c.pt
          ι.app i := c.ι.app ⟨j, i⟩
          ι.naturality {i i'} u := by
            let v : Total.mk Q j i ⟶ .mk _ j i' := { base := 𝟙 _, hom := (Q _).diag.map u }
            simpa using c.ι.naturality v }
      ι.naturality {j j'} u := by
        refine (Q j).isColimit.hom_ext fun i ↦ ?_
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          (Q j).isColimit.fac]
        obtain ⟨i', hom, rfl⟩ := Total.exists_hom_of_hom (P := Q) i u
        rw [reassoc_of% hom.w, (Q j').isColimit.fac]
        simpa using c.ι.naturality hom }
  isColimit.fac := fun c ⟨j, i⟩ ↦ by simp [P.isColimit.fac, (Q j).isColimit.fac]
  isColimit.uniq c m hm := by
    refine P.isColimit.hom_ext fun j ↦ ?_
    simp only [Functor.const_obj_obj, P.isColimit.fac]
    refine (Q j).isColimit.hom_ext fun i ↦ ?_
    simpa [(Q j).isColimit.fac] using hm (.mk _ j i)

end Small

end

end ColimitPresentation

/-- A limit presentation of `X` over `J` is a diagram `{Dᵢ}` in `C` and natural maps
`sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`. -/
structure LimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : X ⟶ Dᵢ`. -/
  natTrans : (Functor.const J).obj X ⟶ diag
  /-- `X` is the limit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsLimit (Cone.mk _ natTrans)

end Limits

namespace ObjectProperty

variable {P : ObjectProperty C}

/-- `X` satisfies `ind P` if `X` is a filtered colimit of `Xᵢ` for `Xᵢ` in `P`. -/
def ind (P : ObjectProperty C) : ObjectProperty C :=
  fun X ↦ ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J)
    (pres : ColimitPresentation J X), ∀ i, P (pres.diag.obj i)

variable (P) in
lemma le_ind : P ≤ P.ind := by
  intro X hX
  exact ⟨PUnit, inferInstance, inferInstance, .self X, by simpa⟩

variable (C) in
/-- The compact objects of `C` are the finitely presentable ones. -/
def compact : ObjectProperty C := fun X ↦ IsFinitelyPresentable.{v} X

@[simp]
lemma ind_ind (h : P ≤ compact C) : P.ind.ind = P.ind := by
  refine le_antisymm (fun X h ↦ ?_) (le_ind P.ind)
  choose J Jc Jf pres K Kc Kf pres' hp using h
  have (j : J) (i : K j) : IsFinitelyPresentable ((pres' j).diag.obj i) := h _ (hp _ _)
  exact ⟨_, inferInstance, inferInstance, pres.bind pres', fun k ↦ by simp [hp]⟩

end ObjectProperty

namespace MorphismProperty

/-- The object property on `Under X` induced by a morphism property. -/
abbrev under {X : C} : ObjectProperty (Under X) := fun f ↦ P f.hom

/--
Let `P` be a property of morphisms. `P.Ind` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : X ⟶ Yᵢ` and `sᵢ : Yᵢ ⟶ Y` indexed by `J`
such that
- `J` is filtered
- `Y = colim Yᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = tᵢ ≫ sᵢ` for all `i`.

See `CategoryTheory.MorphismProperty.ind_iff_ind_under_mk` for an equivalent characterization
in terms of `Y` as an object of `Under X`.
-/
def ind (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type v) (_ : SmallCategory J) (_ : IsFiltered J)
    (D : J ⥤ C) (t : (Functor.const J).obj X ⟶ D) (s : D ⟶ (Functor.const J).obj Y)
    (_ : IsColimit (Cocone.mk _ s)), ∀ j, P (t.app j) ∧ t.app j ≫ s.app j = f

variable (C) in
/-- A morphism `f : X ⟶ Y` is compact if `Y` is compact viewed as an object of `Under X`. -/
def compact : MorphismProperty C :=
  fun _ _ f ↦ IsFinitelyPresentable.{v} (CategoryTheory.Under.mk f)

lemma exists_hom_of_compact {J : Type v} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D}
    (hc : IsColimit c) {X A : C} {p : X ⟶ A} (hp : compact C p) (s : (Functor.const J).obj X ⟶ D)
    (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f :=
  hp.exists_hom_of_isColimit_under hc _ s _ h

lemma le_ind : P ≤ P.ind := by
  intro X Y f hf
  refine ⟨PUnit, inferInstance, inferInstance, (Functor.const PUnit).obj Y, ?_, 𝟙 _, ?_, ?_⟩
  · exact { app _ := f }
  · exact isColimitConstCocone _ _
  · simpa

variable {P}

lemma ind_iff_ind_under_mk {X Y : C} (f : X ⟶ Y) :
    P.ind f ↔ P.under.ind (CategoryTheory.Under.mk f) := by
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, pres, hpres⟩ ↦ ?_⟩
  · refine ⟨J, ‹_›, ‹_›, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Under.lift D t
    · exact { app j := CategoryTheory.Under.homMk (s.app j) (by simp [hst]) }
    · have : Nonempty J := IsFiltered.nonempty
      refine Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs
    · simp [under, hst]
  · refine ⟨J, ‹_›, ‹_›, pres.diag ⋙ CategoryTheory.Under.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
    · exact { app j := (pres.diag.obj j).hom }
    · exact Functor.whiskerRight pres.natTrans (CategoryTheory.Under.forget X)
    · exact isColimitOfPreserves (CategoryTheory.Under.forget _) pres.isColimit
    · exact hpres j
    · simp

lemma ind_under_eq_under_ind (X : C) : P.ind.under (X := X) = P.under.ind := by
  ext f
  simp [under, show f = CategoryTheory.Under.mk f.hom from rfl, ind_iff_ind_under_mk]

variable (Q : MorphismProperty C)

instance [P.RespectsLeft Q] : P.ind.RespectsLeft Q where
  precomp {X Y Z} i hi f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, (Functor.const J).map i ≫ t, s, hs, fun j ↦ ⟨?_, by simp [hst]⟩⟩
    exact RespectsLeft.precomp _ hi _ (hst j).1

instance [P.RespectsIso] : P.ind.RespectsIso where
  postcomp {X Y Z} i (hi : IsIso i) f := fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ by
    refine ⟨J, ‹_›, ‹_›, D, t, s ≫ (Functor.const J).map i, ?_, fun j ↦ ⟨(hst j).1, ?_⟩⟩
    · exact (IsColimit.equivIsoColimit (Cocones.ext (asIso i))) hs
    · simp [reassoc_of% (hst j).2]

lemma ind_under_pushout {X Y : C} (g : X ⟶ Y) [HasPushouts C] [P.IsStableUnderCobaseChange]
    {f : Under X} (hf : P.under.ind f) : P.under.ind ((Under.pushout g).obj f) := by
  obtain ⟨J, _, _, pres, hpres⟩ := hf
  use J, inferInstance, inferInstance, pres.map (Under.pushout g)
  intro i
  exact P.pushout_inr _ _ (hpres i)

instance [P.IsStableUnderCobaseChange] [HasPushouts C] : P.ind.IsStableUnderCobaseChange := by
  refine .mk' fun A B A' f g _ hf ↦ ?_
  rw [ind_iff_ind_under_mk] at hf ⊢
  exact ind_under_pushout g hf

/-- `ind` is idempotent if `P` implies compact. -/
lemma ind_ind (hp : P ≤ compact C) : P.ind.ind = P.ind := by
  refine le_antisymm (fun X Y f hf ↦ ?_) P.ind.le_ind
  have : P.under ≤ ObjectProperty.compact (Under X) := fun f hf ↦ hp _ hf
  simpa [ind_iff_ind_under_mk, ind_under_eq_under_ind, ObjectProperty.ind_ind this] using hf

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
  fun X Y f ↦ ∃ (J : Type v) (_ : SmallCategory J) (_ : IsCofiltered J)
    (D : J ⥤ C) (t : D ⟶ (Functor.const J).obj Y) (s : (Functor.const J).obj X ⟶ D)
    (_ : IsLimit (Cone.mk _ s)), ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

lemma pro_eq_unop_ind_op : pro P = (ind P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, isColimitOfUnop hs, fun j ↦ ⟨(hst j.1).1, by simp [← (hst j.1).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isLimitOfCoconeRightOpOfCone D.leftOp hs, fun j ↦ ⟨(hst _).1,
      op_injective (hst _).2⟩⟩

end CategoryTheory.MorphismProperty
