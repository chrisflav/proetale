/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.Logic.Small.Set

/-!
# Generators of a Grothendieck topology

Let `K` be a precoverage and `J` a Grothendieck topology on a category `C`. We
say `K` generates `J` if for every presheaf `F` on `C`, it is a sheaf for `J` if and only
if it is a sheaf for every covering in `K`.

If `K` generates `J`, then `J` is the smallest Grothendieck topology containing `K`. The converse
only holds if `K` is a coverage or a pretopology.

## Implementation details

For `C : Type u` and `Category.{v} C`, the definition of `Precoverage.Generates` quantifies over
presheafs `Cᵒᵖ ⥤ Type max u v`. We then show that this implies that the condition holds
for all presheafs `Cᵒᵖ ⥤ Type w`.
-/

universe t t' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
  {K : Precoverage C} {J : GrothendieckTopology C}

lemma Presieve.IsSeparatedFor.of_mono {C : Type*} [Category* C] {X : C} {R : Presieve X}
    {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [Mono f] (h : R.IsSeparatedFor G) :
    R.IsSeparatedFor F := by
  intro x t₁ t₂ ht₁ ht₂
  exact injective_of_mono _ <|  h (x.map f) _ _ (ht₁.map f) (ht₂.map f)

lemma Presieve.FamilyOfElements.Compatible.of_mono {C : Type*} [Category* C] {X : C}
    {R : Presieve X} {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [Mono f] {x : R.FamilyOfElements F}
    (hx : (x.map f).Compatible) :
    x.Compatible := by
  intro Y Z W g₁ g₂ f₁ f₂ hf₁ hf₂ heq
  refine injective_of_mono (f.app _) ?_
  simpa using hx _ _ hf₁ hf₂ heq

lemma Presieve.FamilyOfElements.IsAmalgamation.of_mono {C : Type*} [Category* C] {X : C}
    {R : Presieve X} {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) [Mono f] {x : R.FamilyOfElements F}
    {t : F.obj (.op X)} (ht : (x.map f).IsAmalgamation (f.app _ t)) :
    x.IsAmalgamation t := by
  intro Y u hu
  refine injective_of_mono (f.app _) ?_
  simpa [NatTrans.naturality_apply] using ht _ hu

namespace Precoverage

section

variable {F : Cᵒᵖ ⥤ Type w}

/-- Closure of a family of elements of a presheaf under the gluing of
sections over coverings in `K`. -/
inductive SubsheafClosure (K : Precoverage C) {F : Cᵒᵖ ⥤ Type w}
    (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) :
    ∀ Z : C, F.obj (.op Z) → Prop where
  /-- Element of the initial family. -/
  | base {Z : C} {a : F.obj (.op Z)} : a ∈ 𝒮 Z → K.SubsheafClosure 𝒮 Z a
  /-- Restriction of an element in the closure along a morphism. -/
  | restrict {Z W : C} (h : Z ⟶ W) {a : F.obj (.op W)} :
      K.SubsheafClosure 𝒮 W a → K.SubsheafClosure 𝒮 Z (F.map h.op a)
  /-- Gluing of sections in the closure. -/
  | amalgamate {Z : C} {R : Presieve Z} (hR : R ∈ K Z)
      {y : Presieve.FamilyOfElements F R} (hy : y.Compatible)
      (hmem : ∀ ⦃W : C⦄ (r : W ⟶ Z) (hr : R r), K.SubsheafClosure 𝒮 W (y r hr))
      {t : F.obj (.op Z)} (ht : y.IsAmalgamation t) : K.SubsheafClosure 𝒮 Z t

variable (K) in
/-- The `K`-sheafification of family of sets `𝒮` in `F`: If `F` is
a sheaf for `K`, this is the smallest subsheaf of `F` containing `𝒮`. -/
@[simps]
def subsheafify (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) : Subfunctor F where
  obj U := { x | K.SubsheafClosure 𝒮 U.unop x }
  map _ _ ht := .restrict _ ht

variable (𝒮 : ∀ Z : C, Set (F.obj (.op Z)))

/-- If `F` is a sheaf for `R` and `R ∈ K X`, then the `K`-sheafification of `𝒮` is a
sheaf for `R`. -/
lemma isSheafFor_subsheafify (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) {X : C} {R : Presieve X}
    (h : R ∈ K X) (h' : R.IsSheafFor F) :
    R.IsSheafFor (K.subsheafify 𝒮).toFunctor := by
  let G := K.subsheafify 𝒮
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono G.ι h'.isSeparatedFor, fun x hx ↦ ?_⟩
  obtain ⟨t, ht, uniq⟩ := h' (x.map G.ι) (hx.map G.ι)
  exact ⟨⟨t, .amalgamate h (hx.map G.ι) (fun _ _ hr ↦ (x _ hr).property) ht⟩, .of_mono _ ht⟩

namespace SmallConstruction

variable (K) in
/-- Upper bound for the sections of `Precoverage.subsheafify`: If for every `X : C`,
the underlying type of `𝒮 X` embeds into `ι X`, the sections of `K.subsheafify 𝒮`
on `X` embed into `Witness K ι X`. -/
private inductive Witness (ι : C → Type w) : C → Type max w u v where
  | base (X : C) : ι X → Witness ι X
  | restrict {X Y : C} (f : X ⟶ Y) : Witness ι Y → Witness ι X
  /-- Family of elements over a covering in `K`. Note that it is not necessarily compatible. -/
  | amalgamate {X : C} {R : Presieve X} (hR : R ∈ K X)
      (h : ∀ ⦃W⦄ (r : W ⟶ X), R r → Witness ι W) : Witness ι X

/-- Realization of a term of `Witness K ι X` as a section of `F` over `X`. By
construction, the sections will lie in the subsheaf `K.subsheafify 𝒮`.
This takes values in `Option`, because not every term constructed from
the `Witness.amalgamate` constructor corresponds to a compatible family. -/
private noncomputable
def Witness.eval (hF : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor F R)
    (ι : C → Type max u v) (t : ∀ X, ι X → F.obj (.op X)) :
    {X : C} → Witness K ι X → Option (F.obj (.op X))
  | _, .base X i => t _ i
  | _, .restrict f i => do F.map f.op (← eval hF _ t i)
  | _, .amalgamate (R := R) hR h =>
    open Classical in
    let vals := fun W (r : W ⟶ _) (hr : R r) ↦ eval hF _ t (h r hr)
    /- If all elements of the family are evaluatable and the resulting family is compatible, take
    the glued section. Otherwise, return `none`. -/
    if hall : ∀ (W : C) (r : W ⟶ _) (hr : R r), (vals W r hr).isSome then
      let y : R.FamilyOfElements F := fun _ _ hr ↦ (vals _ _ _).get (hall _ _ hr)
      if hy : y.Compatible then some (hF _ hR _ hy).choose else none
    else none

end SmallConstruction

open SmallConstruction in
/-- If `𝒮 Z` is `max u v`-small for every `Z`, then the subsheaf generated by `𝒮 Z` has
`max u v`-small sections. -/
lemma small_subsheafify_of_small
    (hF : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor F R)
    (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) (h : ∀ Z, _root_.Small.{max u v} (𝒮 Z)) :
    FunctorToTypes.Small.{max u v} (K.subsheafify 𝒮).toFunctor := by
  rintro ⟨X⟩
  let ι (X : C) := Shrink.{max u v} (𝒮 X)
  let t (X : C) (i : ι X) : F.obj (Opposite.op X) := ((equivShrink _).symm i).val
  have (x : F.obj (.op X)) (hx : K.SubsheafClosure 𝒮 X x) :
      ∃ (i : Witness K ι X), Witness.eval hF _ t i = x := by
    induction hx with
    | base ha => exact ⟨.base _ (equivShrink _ ⟨_, ha⟩), by grind [Witness.eval]⟩
    | restrict f ha ih =>
      obtain ⟨i, hi⟩ := ih
      use .restrict f i
      grind [Witness.eval]
    | amalgamate hR hy hmem ht ih =>
      choose x hx using ih
      exact ⟨.amalgamate hR x, by simp [Witness.eval, hx]; grind⟩
  choose i hi using this
  have : Function.Injective (fun x : { x // K.SubsheafClosure 𝒮 X x } ↦ i x x.prop) := by
    intro x y hxy
    ext
    apply Option.some_injective
    simp [← hi _ x.prop, ← hi _ y.prop, hxy]
  exact small_of_injective this

end

/-- A precoverage `K` generates the topology `J` if a presheaf on `C` is a sheaf
for `K` if and only if it is a sheaf for `J`. -/
structure Generates (K : Precoverage C) (J : GrothendieckTopology C) : Prop where
  le_toPrecoverage : K ≤ J.toPrecoverage
  isSheaf_of_forall_max (F : Cᵒᵖ ⥤ Type (max u v)) (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, R.IsSheafFor F) :
    Presieve.IsSheaf J F

variable {K : Precoverage C} {J : GrothendieckTopology C}

lemma Generates.generate_mem (H : K.Generates J) {X : C} {R : Presieve X} (h : R ∈ K X) :
    .generate R ∈ J X :=
  H.le_toPrecoverage _ h

private lemma Generates.isSheaf_of_forall_aux (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R)
    [∀ (Z : C), _root_.Small.{max u v} (F.obj (.op Z))] :
    Presieve.IsSheaf J F := by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR ↦ ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR

lemma Generates.isSheaf_of_forall (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R) :
    Presieve.IsSheaf J F := by
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, fun x hx ↦ ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2) ∪
      .range (fun (g : Z ⟶ X) ↦ F.map g.op t₁) ∪ .range (fun (g : Z ⟶ X) ↦ F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
      fun Z g hg ↦ ⟨x g hg, .base <| .inl <| .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ ∈ Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ ∈ Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    exact congr($((hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩
      (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)).val)
  · let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg ↦ ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    refine ⟨t.val, ht.map Q.ι⟩

/-- If `K` generates `J`, then any presheaf is a sheaf if and only if it is a sheaf
for all `K`-covers. -/
lemma Generates.isSheaf_type_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ Type w} :
    Presieve.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R := by
  refine ⟨fun h X R hR ↦ ?_, fun h ↦ H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

/--
If `K` generates `J`, then `J` is equal to the smallest Grothendieck topology containing `K`.
The converse is false, but holds if `K` is a coverage, see `CategoryTheory.Coverage.generates_iff`.
-/
lemma Generates.toGrothendieck_eq (H : K.Generates J) : K.toGrothendieck = J := by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)

lemma Generates.isSheaf_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ A} :
    Presheaf.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, ∀ (M : A),
      Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) R := by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

end Precoverage

/-- If `K` is a coverage, it generates the smallest Grothendieck topology containing `K`. -/
lemma Coverage.generates_toGrothendieck (K : Coverage C) : K.Generates K.toGrothendieck where
  le_toPrecoverage := by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage, ← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]

lemma Coverage.generates_iff {K : Coverage C} : K.Generates J ↔ K.toGrothendieck = J := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

end CategoryTheory
