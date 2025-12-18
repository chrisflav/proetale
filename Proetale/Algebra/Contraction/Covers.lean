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

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] (K : Precoverage C)

@[ext]
structure FiniteFamilies (C : Type*) [Category C] where
  set : Set C
  finite : set.Finite

instance : Preorder (FiniteFamilies C) where
  le U V := U.set ⊆ V.set
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

@[simps]
def FiniteFamilies.map {D : Type*} [Category D] (F : C ⥤ D) :
    FiniteFamilies C ⥤ FiniteFamilies D where
  obj s :=
    { set := F.obj '' s.set
      finite := s.finite.image _ }
  map f := homOfLE (Set.image_mono (leOfHom f))

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

namespace Precoverage

variable (X : C)

section

variable (K) in
noncomputable
def precontraction (X : C) [HasLimitsOfShape (SCov K X)ᵒᵖ (Over X)] : Over X :=
  limit (SCov.diag K X)

variable [HasLimitsOfShape (SCov K X)ᵒᵖ (Over X)]

variable (K) in
noncomputable
def Precontraction.π {Y : C} (f : Y ⟶ X) (h : Presieve.singleton f ∈ K X) :
    K.precontraction X ⟶ Over.mk f :=
  letI U : SCov K X := ⟨_, h⟩
  limit.π (SCov.diag K X) ⟨U⟩ ≫
    Over.homMk (WidePullback.π (U.zeroHypercover.f) ⟨⟨_, f⟩, ⟨⟩⟩)
      (WidePullback.π_arrow _ _)

@[reassoc (attr := simp)]
lemma Precontraction.π_arrow {Y : C} (f : Y ⟶ X)
    (h : Presieve.singleton f ∈ K X) :
    (Precontraction.π K X f h).left ≫ f = (K.precontraction X).hom := by
  simpa using (Precontraction.π K X f h).w

end

variable [∀ X, HasLimitsOfShape (SCov K X)ᵒᵖ (Over X)]

namespace Contraction.Construction

variable (K) in
noncomputable
def obj : ℕ → C
  | 0 => X
  | n + 1 => (K.precontraction (obj n)).left

variable (K) in
noncomputable
def diag : ℕᵒᵖ ⥤ C := Functor.ofOpSequence (X := obj K X)
  fun _ ↦ (K.precontraction _).hom

variable (K) in
noncomputable
def objBase (n : ℕ) : obj K X n ⟶ X :=
  (diag K X).map (homOfLE <| n.zero_le).op

lemma diag_map_le_succ (n : ℕ) (hn : n ≤ n + 1) :
    (diag K X).map (homOfLE hn).op = (K.precontraction _).hom := by
  simp [diag]

@[simps]
noncomputable
def diagHomBase : diag K X ⟶ (Functor.const _).obj X where
  app n := objBase K X n.1
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
  limit (Contraction.Construction.diag K X)

variable (K) in
noncomputable
abbrev contraction.π (n : ℕ) : contraction K X ⟶ Construction.obj K X n :=
  limit.π _ _

variable (K) in
noncomputable def Contraction.base : contraction K X ⟶ X :=
  contraction.π _ _ 0

lemma contraction.w (n m : ℕ) (hmn : n ≤ m) :
    contraction.π K X m ≫ (Construction.diag K X).map ⟨homOfLE hmn⟩ = contraction.π K X n :=
  limit.w _ _

variable (P : MorphismProperty C)
variable [MorphismProperty.ProSpreads.{0, 0} P]

lemma exists_comp_eq_id_contraction [Limits.HasPullbacks C]
    (HK : ∀ {A B : C} (f : A ⟶ B), P f → Presieve.singleton f ∈ K B)
    {Y : C} (f : Y ⟶ K.contraction X) (hf : P f) :
    ∃ (g : K.contraction X ⟶ Y), g ≫ f = 𝟙 (K.contraction X) := by
  obtain ⟨n, D', u, v, hv, hu⟩ :
      ∃ (n : ℕ) (D' : C) (u : D' ⟶ Construction.obj K X n) (v : Y ⟶ D'),
        IsPullback f v (contraction.π K X n) u ∧ P u := by
    obtain ⟨⟨n⟩, D', f', g, h, hf'⟩ := P.exists_isPullback_of_isCofiltered
      (J := ℕᵒᵖ) (D := Construction.diag K X)
      (limit.cone _) (limit.isLimit _) f hf
    use n, D', f', g, h
  let l : K.contraction X ⟶ Y := by
    refine hv.lift (𝟙 _) (contraction.π K X (n + 1) ≫ (Precontraction.π _ _ u (HK _ hu)).left) ?_
    have := limit.w (Construction.diag K X) ⟨homOfLE (Nat.le_succ n)⟩
    dsimp only [Nat.succ_eq_add_one, homOfLE_leOfHom] at this
    simp only [contraction.π, Category.id_comp, Category.assoc, Precontraction.π_arrow, ← this]
    simp [Construction.diag, Functor.ofOpSequence]
  use l
  simp [l]

end Precoverage

namespace MorphismProperty

variable (P : MorphismProperty C)

lemma of_isLimit_widePullbackCone [HasFiniteWidePullbacks C] {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
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

lemma widePullbackBase [HasFiniteWidePullbacks C] {ι : Type*} [Finite ι] {X : C}
    {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] [P.ContainsIdentities] (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) := by
  apply of_isLimit_widePullbackCone
  · exact limit.isLimit _
  · exact hf

abbrev finitePrecoverage : Precoverage C := P.precoverage ⊓ Precoverage.finite _

instance (X : C) (U : SCov P.finitePrecoverage X) : Finite U.zeroHypercover.I₀ :=
  U.2.2

variable [HasFiniteWidePullbacks C]

noncomputable def contraction
    [∀ X, HasLimitsOfShape (SCov P.finitePrecoverage X)ᵒᵖ (Over X)]
    [HasLimitsOfShape ℕᵒᵖ C] (X : C) : C :=
  P.finitePrecoverage.contraction X

variable [∀ X, HasLimitsOfShape (SCov P.finitePrecoverage X)ᵒᵖ (Over X)]

lemma pro_precontraction_hom [P.IsMultiplicative] [P.IsStableUnderBaseChange] (X : C) :
    pro.{max u v} P (P.finitePrecoverage.precontraction X).hom := by
  refine ⟨(SCov P.finitePrecoverage X)ᵒᵖ, inferInstance, inferInstance,
    SCov.diag _ _ ⋙ CategoryTheory.Over.forget _, ?_, ?_, ?_, fun j ↦ ⟨?_, ?_⟩⟩
  · exact { app _ := ((SCov.diag _ _).obj _).hom }
  · exact Functor.whiskerRight
      (limit.cone <| SCov.diag P.finitePrecoverage X).π
      (CategoryTheory.Over.forget X)
  · exact isLimitOfPreserves (CategoryTheory.Over.forget X) (limit.isLimit _)
  · simp [SCov.diag_obj_hom]
    apply widePullbackBase
    intro i
    exact j.1.mem.1 i.2
  · simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Over.forget_obj,
      limit.cone_x, Functor.whiskerRight_app, limit.cone_π, Over.forget_map, CategoryTheory.Over.w]
    rfl

variable [HasLimitsOfShape ℕᵒᵖ C]

noncomputable def Contraction.base (X : C) : P.contraction X ⟶ X :=
  Precoverage.Contraction.base _ X

lemma pro_pro_contractionBase [ProSpreads.{max u v, max u v} P]
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (X : C) :
    pro.{0} (pro.{max u v} P) (Contraction.base P X) := by
  refine ⟨ℕᵒᵖ, inferInstance, inferInstance,
      Precoverage.Contraction.Construction.diag P.finitePrecoverage X,
      ?_, (limit.cone _).π, limit.isLimit _, ?_⟩
  · apply Precoverage.Contraction.Construction.diagHomBase
  · intro n
    refine ⟨?_, ?_⟩
    · dsimp [Precoverage.Contraction.Construction.objBase, Precoverage.Contraction.Construction.diag]
      apply ofOpSequence_map_of_isMultiplicative
      intro n
      apply pro_precontraction_hom
    · apply limit.w

lemma exists_comp_eq_id_contraction [ProSpreads.{0, 0} P]
    {Y : C} (f : Y ⟶ P.contraction X) (hf : P f) :
    ∃ (g : P.contraction X ⟶ Y), g ≫ f = 𝟙 (P.contraction X) := by
  refine Precoverage.exists_comp_eq_id_contraction X P ?_ f hf
  intro A B g hg
  exact ⟨by simp [hg], by simp⟩

end MorphismProperty

end CategoryTheory
