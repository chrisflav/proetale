import Mathlib
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Composition
import Proetale.Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Proetale.Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Proetale.Mathlib.CategoryTheory.Sites.MorphismProperty
import Proetale.Mathlib.CategoryTheory.Sites.Sieves
import Proetale.Mathlib.CategoryTheory.Sites.Finite

/-!
# Another attempt at pro-contractions.

In this file we work in `CommRingCatᵒᵖ`, to be able to use the `0`-hypercover API.
The construction is very similar to the stacks project construction, but
has some subtle differences.
-/

universe s t w' w v u

namespace CategoryTheory

open Limits

namespace MorphismProperty

instance {C : Type*} [Category C] (P Q : MorphismProperty C) [P.ContainsIdentities] (X : C) :
    Nonempty (P.Over Q X) :=
  ⟨Over.mk _ _ (P.id_mem X)⟩

lemma of_isLimit_widePullbackCone {C : Type*} [Category C]
    [HasFiniteWidePullbacks C] {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (P : MorphismProperty C)
    (s : WidePullbackCone f) (hs : IsLimit s) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] (hf : ∀ i, P (f i)) :
    P s.base := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h =>
    let s' := s.reindex e
    have hs' : IsLimit s' := (WidePullbackCone.reindexIsLimitEquiv _ _).symm hs
    change P s'.base
    apply h _ hs'
    intro
    apply hf
  | h_empty =>
    have : IsIso s.base := by
      use WidePullbackCone.IsLimit.lift hs (𝟙 X) (fun i ↦ i.elim) (by simp)
      simp only [WidePullbackCone.IsLimit.lift_base, and_true]
      apply WidePullbackCone.IsLimit.hom_ext hs <;> simp
    exact P.of_isIso _
  | h_option ih =>
    let s' : WidePullbackCone (fun i ↦ f (some i)) :=
      limit.cone _
    let hs' : IsLimit s' := limit.isLimit _
    have H : P s'.base := by
      apply ih _ hs'
      intro
      apply hf
    have H' : P (s.π none) := by
      apply P.of_isPullback _ H
      · exact f none
      · exact WidePullbackCone.IsLimit.lift hs' s.base (fun i ↦ s.π (some i)) (by simp)
      · apply IsPullback.flip
        apply CategoryTheory.Limits.WidePullbackCone.isPullback_of_isCompl'
        · exact Option.some_injective _
        · rw [← Set.compl_range_some]
          exact IsCompl.symm isCompl_compl
        · exact hs
    rw [← s.condition none]
    exact P.comp_mem _ _ H' (hf none)

lemma widePullbackBase {C : Type*} [Category C] [HasFiniteWidePullbacks C]
    {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) := by
  apply of_isLimit_widePullbackCone
  · exact limit.isLimit _
  · exact hf

end MorphismProperty

variable {C : Type u} [Category.{v} C] (K : Precoverage C)

instance [EssentiallySmall.{w} C] [Nonempty C] : Nonempty (SmallModel C) :=
  Nonempty.map (equivSmallModel C).functor.obj ‹_›

@[ext]
structure FiniteFamilies (C : Type*) [Category C] where
  set : Set C
  finite : set.Finite

instance : Preorder (FiniteFamilies C) where
  le U V := U.set ⊆ V.set
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

instance [Nonempty C] : Nonempty (FiniteFamilies C) :=
  ⟨⟨{Nonempty.some ‹_›}, by simp⟩⟩

instance : IsDirected (FiniteFamilies C) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.set ∪ V.set, U.finite.union V.finite⟩, Set.subset_union_left, Set.subset_union_right⟩

/-- If `F` is an equivalence, this functor is NOT necessarily an equivalence, because
`FiniteFamilies` is a preorder, so every equivalence would be an isomorphism. -/
@[simps]
def FiniteFamilies.map {D : Type*} [Category D] (F : C ⥤ D) :
    FiniteFamilies C ⥤ FiniteFamilies D where
  obj s :=
    { set := F.obj '' s.set
      finite := s.finite.image _ }
  map f := homOfLE (Set.image_mono (leOfHom f))

namespace FiniteFamilies

variable {P : MorphismProperty C} {X : C} [EssentiallySmall.{w, v, max u v} (P.Over ⊤ X)]

def Index (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))) : Type w := A.set

instance (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))) : Finite A.Index :=
  A.finite

@[simps]
def indexHom {A B : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X))}
    (h : A ≤ B) (i : A.Index) : B.Index :=
  ⟨i.1, h i.2⟩

noncomputable def family (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : C :=
  ((equivSmallModel _).inverse.obj i.1).left

noncomputable def hom (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : A.family i ⟶ X :=
  ((equivSmallModel _).inverse.obj i.1).hom

lemma property_hom (A : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))
    (i : A.Index) : P (A.hom i) :=
  ((equivSmallModel _).inverse.obj i.1).prop

variable (P) in
noncomputable
def diag (X : C) [EssentiallySmall.{w} (P.Over ⊤ X)]
    [HasFiniteWidePullbacks C] :
    (FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))ᵒᵖ ⥤ Over X where
  obj U :=
    Over.mk (WidePullback.base <| U.unop.hom)
  map {U V} f :=
    Over.homMk <| WidePullback.lift (WidePullback.base _)
    (fun j ↦ WidePullback.π _ (indexHom (leOfHom f.unop) j))
    (by intro; exact WidePullback.π_arrow _ _)

end FiniteFamilies

structure SCov (K : Precoverage C) (X : C) where
  presieve : Presieve X
  mem : presieve ∈ K X

structure Cov (K : Precoverage C) (X : C) where
  toZeroHypercover : Precoverage.ZeroHypercover.{w} K X

variable {K : Precoverage C} {X : C}

instance : Preorder (SCov K X) where
  le U V := U.presieve ≤ V.presieve
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

def SCov.zeroHypercover (U : SCov K X) : K.ZeroHypercover X where
  I₀ := U.presieve.uncurry
  X i := i.1.1
  f i := i.1.2
  mem₀ := by
    simp only [PreZeroHypercover.presieve₀]
    convert U.2
    refine le_antisymm ?_ ?_
    · intro Z g ⟨i⟩
      exact i.2
    · intro Z g hg
      exact .mk (⟨⟨Z, g⟩, hg⟩ : U.presieve.uncurry)

namespace Cov

@[ext]
structure Hom (U V : Cov K X) where
  σ : V.1.I₀ → U.1.I₀
  iso (i : V.1.I₀) : U.1.X (σ i) ⟶ V.1.X i
  [isIso (i : V.1.I₀) : IsIso (iso i)]
  w (i : V.1.I₀) : iso i ≫ V.1.f _ = U.1.f _ := by cat_disch

attribute [reassoc (attr := simp)] Hom.w
attribute [instance] Hom.isIso

@[simps]
def Hom.id (U : Cov K X) : U.Hom U where
  σ := _root_.id
  iso _ := 𝟙 _

@[simps]
def Hom.comp {U V W : Cov K X} (f : U.Hom V) (g : V.Hom W) : U.Hom W where
  σ i := f.σ (g.σ i)
  iso _ := f.iso _ ≫ g.iso _

open Limits

variable [∀ (X : C), ∀ (U : Cov K X), HasWidePullback _ U.1.X U.1.f]

variable (X P) in
@[simps! id_σ id_iso comp_σ comp_iso]
instance : Category (Cov K X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext <;> simp; ext; simp
  comp_id := by intros; ext <;> simp; ext; simp
  assoc := by intros; ext <;> simp; ext; simp

instance [K.HasIsos] : Nonempty (Cov K X) :=
  ⟨⟨Precoverage.ZeroHypercover.singleton (𝟙 X) (K.mem_coverings_of_isIso _)⟩⟩

variable (K) in
@[simps -isSimp, simps! obj_hom]
noncomputable
def diag (X : C) : Cov.{w} K X ⥤ Over X where
  obj U := Over.mk (WidePullback.base U.1.f)
  map {U V} f := Over.homMk <| WidePullback.lift (WidePullback.base _)
    (fun j ↦ WidePullback.π _ (f.σ j) ≫ (f.iso j)) (by simp)

end Cov

namespace SCov

variable (K) in
@[simps]
def toCov (X : C) : (SCov K X)ᵒᵖ ⥤ Cov.{max u v} K X where
  obj U := ⟨U.1.zeroHypercover⟩
  map {U V} f :=
    { σ i := ⟨i.1, leOfHom f.1 _ i.2⟩
      iso i := 𝟙 _
      w i := by simp only [Category.id_comp]; rfl }
  map_id _ := rfl
  map_comp _ _ := by apply Cov.Hom.ext <;> cat_disch

variable [∀ (X : C) (U : SCov K X), HasWidePullback _ _ U.zeroHypercover.f]

variable (K) in
@[simps! -isSimp obj_hom]
noncomputable
def diag (X : C) : (SCov K X)ᵒᵖ ⥤ Over X where
  obj U := Over.mk (WidePullback.base U.1.zeroHypercover.f)
  map {U V} f := Over.homMk <| WidePullback.lift (WidePullback.base _)
    (fun j ↦ WidePullback.π _ (⟨j.1, leOfHom f.1 _ j.2⟩ : U.1.zeroHypercover.I₀))
    (by intro; exact WidePullback.π_arrow _ _)

instance [K.HasIsos] : Nonempty (SCov K X) :=
  ⟨⟨.singleton (𝟙 X), K.mem_coverings_of_isIso _⟩⟩

instance [K.IsStableUnderSup] : IsDirected (SCov K X) (· ≤ ·) where
  directed U V :=
    ⟨⟨U.presieve ⊔ V.presieve, K.sup_mem_coverings U.2 V.2⟩,
      le_sup_left (a := U.1), le_sup_right (a := U.1)⟩

example [K.HasIsos] [K.IsStableUnderSup] : IsCofiltered (SCov K X)ᵒᵖ :=
  inferInstance

end SCov

variable [∀ (X : C) (U : SCov K X), HasWidePullback _ _ U.zeroHypercover.f]

namespace MorphismProperty

variable (P : MorphismProperty C)

variable (X : C)

section

variable [EssentiallySmall.{w} (P.Over ⊤ X)]

noncomputable
def precontraction (X : C) [EssentiallySmall.{w} (P.Over ⊤ X)]
    [HasFiniteWidePullbacks C] [HasLimit (FiniteFamilies.diag.{w} P X)] : Over X :=
  limit (FiniteFamilies.diag.{w} P X)

variable [HasFiniteWidePullbacks C] [HasLimit (FiniteFamilies.diag.{w} P X)]

noncomputable
def Precontraction.π {Y : C} (f : Y ⟶ X) (hf : P f) :
    P.precontraction X ⟶ CategoryTheory.Over.mk f :=
  letI U : FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)) :=
    { set := { (equivSmallModel _).functor.obj (.mk _ _ hf) }
      finite := by simp }
  limit.π (FiniteFamilies.diag.{w} P X) ⟨U⟩ ≫
    CategoryTheory.Over.homMk (WidePullback.π U.hom ⟨_, rfl⟩)
      (WidePullback.π_arrow _ _) ≫
    (Functor.mapIso (Over.forget P ⊤ _)
      ((equivSmallModel <| P.Over ⊤ X).unitIso.app _)).inv

@[reassoc (attr := simp)]
lemma Precontraction.π_arrow {Y : C} (f : Y ⟶ X) (hf : P f) :
    (Precontraction.π P X f hf).left ≫ f = (P.precontraction X).hom := by
  simpa using (Precontraction.π P X f hf).w

lemma pro_precontraction_hom [P.IsMultiplicative] [P.IsStableUnderBaseChange] :
    pro.{w} P (precontraction.{w} P X).hom := by
  refine ⟨(FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))ᵒᵖ, inferInstance, inferInstance,
    FiniteFamilies.diag _ _ ⋙ CategoryTheory.Over.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
  · exact { app _ := ((FiniteFamilies.diag _ _).obj _).hom }
  · exact Functor.whiskerRight
      (limit.cone <| FiniteFamilies.diag P X).π
      (CategoryTheory.Over.forget X)
  · exact isLimitOfPreserves (CategoryTheory.Over.forget X) (limit.isLimit _)
  · simp only [Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj]
    apply widePullbackBase
    intro i
    apply FiniteFamilies.property_hom
  · simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Over.forget_obj,
      limit.cone_x, Functor.whiskerRight_app, limit.cone_π, Over.forget_map, CategoryTheory.Over.w]
    rfl

end

variable [HasFiniteWidePullbacks C]
  [∀ X, EssentiallySmall.{w} (P.Over ⊤ X)]
  [∀ X : C, HasLimitsOfShape (FiniteFamilies (SmallModel.{w} (P.Over ⊤ X)))ᵒᵖ (Over X)]

namespace Contraction.Construction

noncomputable
def obj : ℕ → C
  | 0 => X
  | n + 1 => (precontraction.{w} P (obj n)).left

variable (K) in
noncomputable
def diag : ℕᵒᵖ ⥤ C := Functor.ofOpSequence (X := obj P X)
  fun _ ↦ (P.precontraction _).hom

variable (K) in
noncomputable
def objBase (n : ℕ) : obj P X n ⟶ X :=
  (diag P X).map (homOfLE <| n.zero_le).op

lemma diag_map_le_succ (n : ℕ) (hn : n ≤ n + 1) :
    (diag P X).map (homOfLE hn).op = (P.precontraction _).hom := by
  simp [diag]

@[simps]
noncomputable
def diagHomBase : diag P X ⟶ (Functor.const _).obj X where
  app n := objBase P X n.1
  naturality n m f := by
    simp only [Functor.const_obj_obj, objBase, Opposite.op_unop, homOfLE_leOfHom,
      Functor.const_obj_map, Category.comp_id, homOfLE_leOfHom, ← Functor.map_comp]
    rfl

end Contraction.Construction

open Contraction

variable [HasLimitsOfShape ℕᵒᵖ C]

variable (K) in
noncomputable
def contraction : C :=
  limit (Contraction.Construction.diag P X)

variable (K) in
noncomputable
abbrev contraction.π (n : ℕ) : contraction P X ⟶ Construction.obj P X n :=
  limit.π _ _

variable (K) in
noncomputable def Contraction.base : contraction P X ⟶ X :=
  contraction.π _ _ 0

lemma contraction.w (n m : ℕ) (hmn : n ≤ m) :
    contraction.π P X m ≫ (Construction.diag P X).map ⟨homOfLE hmn⟩ = contraction.π P X n :=
  limit.w _ _

lemma exists_comp_eq_id_contraction [PreProSpreads.{0} P] [Limits.HasPullbacks C]
    {Y : C} (f : Y ⟶ contraction.{w} P X) (hf : P f) :
    ∃ (g : contraction.{w} P X ⟶ Y), g ≫ f = 𝟙 (contraction.{w} P X) := by
  obtain ⟨n, D', u, v, hv, hu⟩ :
      ∃ (n : ℕ) (D' : C) (u : D' ⟶ Construction.obj P X n) (v : Y ⟶ D'),
        IsPullback f v (contraction.π P X n) u ∧ P u := by
    obtain ⟨⟨n⟩, D', f', g, h, hf'⟩ := P.exists_isPullback_of_isCofiltered
      (J := ℕᵒᵖ) (D := Construction.diag P X)
      (limit.cone _) (limit.isLimit _) f hf
    use n, D', f', g, h
  let l : P.contraction X ⟶ Y := by
    refine hv.lift (𝟙 _) (contraction.π P X (n + 1) ≫ (Precontraction.π _ _ u hu).left) ?_
    have := limit.w (Construction.diag P X) ⟨homOfLE (Nat.le_succ n)⟩
    dsimp only [Nat.succ_eq_add_one, homOfLE_leOfHom] at this
    simp only [contraction.π, Category.id_comp, Category.assoc, Precontraction.π_arrow, ← this]
    simp [Construction.diag, Functor.ofOpSequence]
  use l
  simp [l]

lemma pro_pro_contractionBase [PreProSpreads.{w} P]
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (X : C) :
    pro.{0} (pro.{w} P) (Contraction.base P X) := by
  refine ⟨ℕᵒᵖ, inferInstance, inferInstance,
      Contraction.Construction.diag P X,
      ?_, (limit.cone _).π, limit.isLimit _, ?_⟩
  · apply Contraction.Construction.diagHomBase
  · intro n
    refine ⟨?_, ?_⟩
    · dsimp [Contraction.Construction.objBase, Contraction.Construction.diag]
      apply ofOpSequence_map_of_isMultiplicative
      intro n
      apply pro_precontraction_hom
    · apply limit.w

lemma pro_contractionBase [LocallySmall.{w} C]
    (H : P ≤ isFinitelyPresentable.{w} C)
    [PreProSpreads.{w} P]
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (X : C) :
    pro.{w} P (Contraction.base P X) := by
  rw [← pro_pro H]
  apply pro_of_univLE.{0, w}
  exact P.pro_pro_contractionBase _

lemma exists_pro_forall_exists_section {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
    (P : MorphismProperty C)
    [HasFiniteWidePullbacks C] [HasLimitsOfShape ℕᵒᵖ C]
    [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    [∀ (X : C), EssentiallySmall.{w} (P.Over ⊤ X)]
    [∀ (X : C), HasLimitsOfShape (FiniteFamilies (SmallModel.{w} <| P.Over ⊤ X))ᵒᵖ (Over X)]
    [PreProSpreads.{0} P] [PreProSpreads.{w} P]
    (H : P ≤ isFinitelyPresentable.{w} C) (X : C) :
    ∃ (Y : C) (f : Y ⟶ X),
      pro.{w} P f ∧ ∀ {Z : C} (g : Z ⟶ Y), P g → ∃ (s : Y ⟶ Z), s ≫ g = 𝟙 Y := by
  refine ⟨P.contraction X, Contraction.base P X, ?_, ?_⟩
  · exact pro_contractionBase _ H _
  · intro Z g hg
    obtain ⟨s, hs⟩ := exists_comp_eq_id_contraction P _ g hg
    use s

end MorphismProperty

end CategoryTheory
