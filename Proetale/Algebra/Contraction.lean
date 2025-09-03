import Mathlib
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind

/-!
# Another attempt at pro-contractions.

In this file we work in `CommRingCatᵒᵖ`, to be able to use the `0`-hypercover API.
The construction is very similar to the stacks project construction, but
has some subtle differences.
-/

universe s t w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (K : Precoverage C)

structure Cov (K : Precoverage C) (X : C) where
  toZeroHypercover : Precoverage.ZeroHypercover.{w} K X

variable {K : Precoverage C} {X : C}

namespace Cov

@[ext]
structure Hom (U V : Cov K X) where
  σ : V.1.I₀ → U.1.I₀
  iso (i : V.1.I₀) : U.1.X (σ i) ⟶ V.1.X i
  w (i : V.1.I₀) : iso i ≫ V.1.f _ = U.1.f _

attribute [reassoc (attr := simp)] Hom.w

@[simps]
def Hom.id (U : Cov K X) : U.Hom U where
  σ := _root_.id
  iso _ := 𝟙 _
  w := by simp

@[simps]
def Hom.comp {U V W : Cov K X} (f : U.Hom V) (g : V.Hom W) : U.Hom W where
  σ i := f.σ (g.σ i)
  iso _ := f.iso _ ≫ g.iso _
  w := by simp

variable (X P) in
@[simps! id_σ id_iso comp_σ comp_iso]
instance : Category (Cov K X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by intros; ext <;> simp; ext; simp
  comp_id := by intros; ext <;> simp; ext; simp
  assoc := by intros; ext <;> simp; ext; simp

open Limits

variable (K) in
@[simps -isSimp]
noncomputable
def diag (X : C) [∀ (U : Cov K X), HasWidePullback _ U.1.X U.1.f] : Cov.{w} K X ⥤ C where
  obj U := widePullback X U.1.X U.1.f
  map {U V} f := WidePullback.lift (WidePullback.base _)
    (fun j ↦ WidePullback.π _ (f.σ j) ≫ (f.iso j)) (by simp)
  map_id _ := by
    apply WidePullback.hom_ext
    simp only [id_σ, id_iso, Category.comp_id, limit.lift_π,
      WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app, Category.id_comp, implies_true]
    simp_rw [id_σ]
    simp_rw [id_iso]
    simp
  map_comp _ _ := by
    apply WidePullback.hom_ext
    simp only [comp_σ, comp_iso, limit.lift_π, WidePullbackShape.mkCone_pt,
      WidePullbackShape.mkCone_π_app, Category.assoc, limit.lift_π_assoc,
      WidePullbackShape.wideCospan_obj, implies_true]
    simp_rw [comp_σ]
    simp_rw [comp_iso]
    simp

end Cov

open CategoryTheory Limits

variable [∀ (X : C) (U : Cov K X), HasWidePullback _ U.1.X U.1.f]
  [∀ (X : C), HasColimitsOfShape (Cov K X) C]

namespace Precoverage

variable (K) in
noncomputable
def precontraction (X : C) [HasLimitsOfShape (Cov.{w} K X) C] : C :=
  limit (Cov.diag.{w} K X)

variable (X : C) [HasLimitsOfShape (Cov.{w} K X) C] [HasIsos K]
  [HasLimitsOfShape (WidePullbackShape PUnit) C]

variable (K) in
noncomputable
def Precontraction.π {Y : C} (f : Y ⟶ X) (h : Presieve.singleton f ∈ K X) : K.precontraction X ⟶ Y :=
  limit.π (Cov.diag.{w} K X) ⟨ZeroHypercover.singleton K f h⟩ ≫ WidePullback.π _ ⟨⟩

variable (K) in
noncomputable
def Precontraction.base : K.precontraction X ⟶ X :=
  limit.π (Cov.diag.{w} K X) ⟨ZeroHypercover.singleton K (𝟙 X) <| mem_coverings_of_isIso (𝟙 X)⟩ ≫
    (WidePullback.base _)

omit [∀ (X : C),
  HasColimitsOfShape (Cov K X) C] [K.HasIsos] [HasLimitsOfShape (WidePullbackShape PUnit) C] in
lemma Precontraction.naturality {Y Z : C} (f : Z ⟶ Y) (g : Y ⟶ X)
    (hfg : (Presieve.singleton (f ≫ g) ∈ K X)) (hg : Presieve.singleton g ∈ K X) :
    Precontraction.π K X (f ≫ g) hfg ≫ f = Precontraction.π K X g hg := by
  simp [Precontraction.π]
  let U : Cov.{w} K X := ⟨ZeroHypercover.singleton K _ hfg⟩
  let V : Cov.{w} K X := ⟨ZeroHypercover.singleton K _ hg⟩
  let f : U ⟶ V := {
    σ i := i
    iso i := f
    w := by simp [U, V]
  }
  have := limit.w (Cov.diag.{w} K X) f
  show limit.π (Cov.diag.{w} K X) U ≫ _ = limit.π (Cov.diag.{w} K X) V ≫ _
  rw [← this]
  rw [Category.assoc]
  congr 1
  dsimp [Cov.diag_map]
  erw [WidePullback.lift_π]
  rfl

@[reassoc (attr := simp)]
lemma Precontraction.π_arrow {Y : C} (f : Y ⟶ X) (h : Presieve.singleton f ∈ K X) :
    Precontraction.π K X f h ≫ f = Precontraction.base K X := by
  have := Precontraction.naturality (K := K) X f (𝟙 X) (by simpa) (mem_coverings_of_isIso _)
  simp at this
  rw [this]
  simp only [π, base]
  congr 1
  rw [← Category.comp_id (WidePullback.π (ZeroHypercover.singleton K (𝟙 X) _).f PUnit.unit)]
  apply WidePullback.π_arrow

variable [∀ X, HasLimitsOfShape (Cov K X) C]

namespace Contraction.Construction

variable (K) in
noncomputable
def obj : ℕ → C
  | 0 => X
  | n + 1 => K.precontraction (obj n)

variable (K) in
noncomputable
def diag : ℕᵒᵖ ⥤ C := Functor.ofOpSequence (X := obj K X)
  (fun _ ↦ Precontraction.base K _)

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

lemma contraction.w (n m : ℕ) (hmn : n ≤ m) :
    contraction.π K X m ≫ (Construction.diag K X).map ⟨homOfLE hmn⟩ = contraction.π K X n :=
  limit.w _ _

variable (P : MorphismProperty C)

def _root_.CategoryTheory.MorphismProperty.Pro : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J)
    -- `Dᵢ`
    (D : J ⥤ C)
    -- `tᵢ : Dᵢ ⟶ X`
    (t : D ⟶ (Functor.const J).obj Y)
    -- `sᵢ : Y = lim Dᵢ ⟶ Dᵢ`
    (s : (Functor.const J).obj X ⟶ D)
    -- `Y = colim Dᵢ`
    (_ : IsLimit (Cone.mk _ s)),
    ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

class _root_.CategoryTheory.MorphismProperty.ProSpreads : Prop where
  exists_isPullback : ∀ {J : Type t} [Category.{s} J] [IsCofiltered J] {D : J ⥤ C}
    (c : Cone D) (_ : IsLimit c)
    (T : C) (f : T ⟶ c.pt) (_ : P f),
    ∃ (j : J) (T' : C) (f' : T' ⟶ D.obj j) (g : T ⟶ T'),
      IsPullback f g (c.π.app j) f' ∧ P f'
  exists_isPullback_of_hom : ∀ {J : Type t} [Category.{s} J] [IsCofiltered J] {D : J ⥤ C}
    (c : Cone D) (_ : IsLimit c)
    {A B A' B' : C} (f : A ⟶ B) (pA : A ⟶ c.pt) (pB : B ⟶ c.pt) (_hf : f ≫ pB = pA)
    {jA jB : J}
    (qA : A ⟶ A') (qB : B ⟶ B') (gA : A' ⟶ D.obj jA) (gB : B' ⟶ D.obj jB)
    (hA : IsPullback pA qA (c.π.app jA) gA)
    (hB : IsPullback pB qB (c.π.app jB) gB),
    P gA → P gB →
    ∃ (j : J) (tA : j ⟶ jA) (tB : j ⟶ jB) (PA PB : C)
      (PA₁ : PA ⟶ D.obj j) (PA₂ : PA ⟶ A')
      (PB₁ : PB ⟶ D.obj j) (PB₂ : PB ⟶ B')
      (hPA : IsPullback PA₁ PA₂ (D.map tA) gA)
      (hPB : IsPullback PB₁ PB₂ (D.map tB) gB)
      (f' : PA ⟶ PB),
      f ≫ hPB.lift (pB ≫ c.π.app j) qB (by simp [hB.w]) =
        hPA.lift (pA ≫ c.π.app j) qA (by simp [hA.w]) ≫ f'

alias _root_.CategoryTheory.MorphismProperty.exists_isPullback :=
  MorphismProperty.ProSpreads.exists_isPullback

alias _root_.CategoryTheory.MorphismProperty.exists_isPullback_of_hom :=
  MorphismProperty.ProSpreads.exists_isPullback_of_hom


variable [MorphismProperty.ProSpreads.{0, 0} P]

lemma foo
    (HK : ∀ {A B : C} (f : A ⟶ B), P f → Presieve.singleton f ∈ K B)
    {Y : C} (f : Y ⟶ K.contraction X) (hf : P.Pro f) :
    ∃ (g : K.contraction X ⟶ Y), g ≫ f = 𝟙 (K.contraction X) := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hf
  have (j : J) : ∃ (n : ℕ) (D' : C) (u : D' ⟶ Construction.obj K X n) (v : D.obj j ⟶ D'),
      IsPullback (t.app j) v (contraction.π K X n) u ∧ P u := by
    obtain ⟨⟨n⟩, D', f', g, h, hf'⟩ := P.exists_isPullback (J := ℕᵒᵖ) (D := Construction.diag K X)
      (limit.cone _) (limit.isLimit _) _ (t.app j) (hst j).1
    use n, D', f', g, h
  choose n D' u v hv hu using this
  let l (j : J) : K.contraction X ⟶ D.obj j := by
    refine (hv j).lift (𝟙 _) (contraction.π K X ((n j) + 1) ≫ Precontraction.π _ _ (u j) (HK _ (hu j))) ?_
    have := limit.w (Construction.diag K X) ⟨homOfLE (Nat.le_succ (n j))⟩
    dsimp only [Nat.succ_eq_add_one, homOfLE_leOfHom] at this
    simp only [Functor.const_obj_obj, contraction.π, Category.id_comp, Category.assoc,
      Precontraction.π_arrow]
    rw [← this]
    simp [Construction.diag, Functor.ofOpSequence]
  let c : Cone D := {
    pt := K.contraction X
    π.app := l
    π.naturality {i j} a := by
      apply (hv j).hom_ext
      · simp [l]
      · simp
        obtain ⟨⟨m⟩, hmi, hmj, PA, PB, PA₁, PA₂, PB₁, PB₂, hPA, hPB, f', hff'⟩ :=
          P.exists_isPullback_of_hom (D := Construction.diag K X)
            (limit.cone _) (limit.isLimit _) (D.map a) (t.app i) (t.app j) sorry
            (v i) (v j) (u i) (u j) (hv i) (hv j) (hu i) (hu j)
        have := congr($(hff') ≫ PB₂)
        simp at this
        rw [this]
        conv_lhs => simp [l]
        -- should be part of ProSpreads
        have hstr : f' ≫ PB₁ = PA₁ := sorry
        have comp := Precontraction.naturality (K := K) (Construction.obj K X m)
          f' PB₁ sorry sorry
        simp_rw [hstr] at comp
        -- is this true?
        have key :
            l i ≫ hPA.lift (t.app i ≫ limit.π (Construction.diag K X) ⟨m⟩) (v i) sorry =
              contraction.π K X (m + 1) ≫ Precontraction.π K (Construction.obj K X m) PA₁ sorry :=
          sorry
        rw [reassoc_of% key]
        rw [reassoc_of% comp]
        have : n j ≤ m := hmj.unop.1.1
        have hmjadd : n j + 1 ≤ m + 1 := by omega
        rw [← contraction.w X _ _ hmjadd]
        rw [Category.assoc]
        congr 1
        simp
        -- is this true?
        sorry
  }
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := J)
  refine ⟨hs.lift c, ?_⟩
  simp [← (hst j).2, hs.fac_assoc, c, l]

end Precoverage

/-
we can also do zerohypercover instead?
-/

section

noncomputable
def WidePullback.reindex {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasWidePullback B X f]
    {g : (j : β) → Y j ⟶ B} [HasWidePullback B Y g]
    (e : α ≃ β) (s : ∀ a, X a ≅ Y (e a))
    (w : ∀ i, (s i).hom ≫ g (e i) = f _) :
    widePullback B X f ≅ widePullback B Y g where
  hom := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e.symm i) ≫ (s _).hom ≫ eqToHom (by simp))
    fun i ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i
      simp [w]
  inv := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e i) ≫ (s _).inv)
    fun i ↦ by simp [← w]

noncomputable
def WidePullback.proj {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α ⊕ β → C}
    {f : (j : α ⊕ β) → X j ⟶ B} [HasWidePullback B X f]
    [HasWidePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j))] :
    widePullback B X f ⟶ widePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j)) :=
  WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp)

noncomputable
def WidePullback.mapOfSumEquiv {α β γ : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasLimitsOfShape (WidePullbackShape α) C]
    {g : (j : β) → Y j ⟶ B} [HasLimitsOfShape (WidePullbackShape β) C]
    [HasLimitsOfShape (WidePullbackShape (β ⊕ γ)) C]
    (e : β ⊕ γ ≃ α) (s : ∀ (b : β), X (e (.inl b)) ⟶ Y b)
    (w : ∀ b, s b ≫ g b = f _) :
    widePullback B X f ⟶ widePullback B Y g :=
  (WidePullback.reindex (Y := X ∘ e) (g := fun i ↦ f (e i)) e.symm
    (fun a ↦ eqToIso (by simp)) (fun i ↦ by
      simp only [Function.comp_apply, eqToIso.hom]
      rw [← eqToHom_naturality, eqToHom_refl, Category.comp_id]
      rw [Equiv.apply_symm_apply])).hom ≫
    WidePullback.lift (objs := Sum.elim Y (X ∘ e ∘ .inr))
      (arrows := fun i ↦ match i with
        | .inl b => g b
        | .inr c => f _)
      (WidePullback.base _)
      (fun j ↦ match j with
        | .inl b => WidePullback.π _ _ ≫ s b
        | .inr b => WidePullback.π _ _)
      (by simp [w]) ≫
      WidePullback.proj

end

end CategoryTheory
