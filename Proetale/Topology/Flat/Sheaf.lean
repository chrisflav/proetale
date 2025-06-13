/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Flat.QuasiCompactCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Preserves
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!
# The fpqc topology is subcanonical

In this file we show that the fqpc topology of a scheme is subcanonical. This implies that
all coarser topologies, e.g., the (pro)étale topology, are subcanonical.
-/

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

instance {C : Type*} [Category C] : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

variable {C : Type*} [Category C] {X : C}

def Limits.Fork.isLimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Fork f g)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by aesop_cat)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by aesop_cat)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by aesop_cat) :
    IsLimit c ≃ IsLimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

@[reassoc (attr := simp)]
lemma Limits.opCoproductIsoProduct'_hom_comp_π {α : Type*} {Z : α → C} {c : Cofan Z}
    {f : Fan fun i ↦ op (Z i)} (hc : IsColimit c) (hf : IsLimit f) (i : α) :
    (opCoproductIsoProduct' hc hf).hom ≫ f.proj i = (c.inj i).op := by
  simp [opCoproductIsoProduct', Fan.proj]

@[reassoc (attr := simp)]
lemma Limits.opCoproductIsoProduct_hom_comp_π {α : Type*} (Z : α → C) [HasCoproduct Z] (i : α) :
    (opCoproductIsoProduct Z).hom ≫ Pi.π _ i = (Sigma.ι _ i).op :=
  Limits.opCoproductIsoProduct'_hom_comp_π ..

@[reassoc (attr := simp)]
lemma Limits.ConeMorphism.hom_inv_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F}
    (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[reassoc (attr := simp)]
lemma Limits.ConeMorphism.inv_hom_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F}
    (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F} (f : c ≅ d) :
    IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cone F} (f : c ≅ d) :
    IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[reassoc (attr := simp)]
lemma Limits.CoconeMorphism.hom_inv_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F}
    (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

@[reassoc (attr := simp)]
lemma Limits.CoconeMorphism.inv_hom_id {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F}
    (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F} (f : c ≅ d) :
    IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {J : Type*} [Category J] {F : J ⥤ C} {c d : Cocone F} (f : c ≅ d) :
    IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

def CoproductDisjoint.of_binaryCofan_of_pullbackCone {X Y : C}
    (c : BinaryCofan X Y) (hc : IsColimit c)
    (d : PullbackCone c.inl c.inr) (hd : IsLimit d)
    (H : IsInitial d.pt) [Mono c.inl] [Mono c.inr] :
    CoproductDisjoint X Y where
  isInitialOfIsPullbackOfIsCoproduct {A B} p q f g h hsq hl := by
    let e := h.uniqueUpToIso hc
    have hp : p ≫ e.hom.hom = c.inl := e.hom.w ⟨.left⟩
    have hq : q ≫ e.hom.hom = c.inr := e.hom.w ⟨.right⟩
    let u : B ⟶ d.pt := by
      refine PullbackCone.IsLimit.lift hd f g ?_
      · rw [← hp, reassoc_of% hsq, reassoc_of% show q = c.inr ≫ e.inv.hom by simp]
        rw [CoconeMorphism.w_assoc, CoconeMorphism.w]
    have hu1 : u ≫ d.fst = f := by simp [u]
    have hu2 : u ≫ d.snd = g := by simp [u]
    refine H.ofIso ⟨H.to B, u, H.hom_ext _ _, PullbackCone.IsLimit.hom_ext hl ?_ ?_⟩
    · simp [← hu1, show H.to X = d.fst from H.hom_ext _ _]
    · simp [← hu2, show H.to Y = d.snd from H.hom_ext _ _]
  mono_inl B p q h := by
    rw [show p = c.inl ≫ (h.uniqueUpToIso hc).inv.hom by simp]
    infer_instance
  mono_inr B p q h := by
    rw [show q = c.inr ≫ (h.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

instance GrothendieckTopology.preservesLimitsOfShape_yoneda (J : GrothendieckTopology C)
    [J.Subcanonical] {I : Type*} [Category I] :
    PreservesLimitsOfShape I J.yoneda :=
  have : PreservesLimitsOfShape I (J.yoneda ⋙ sheafToPresheaf J _) :=
    inferInstanceAs <| PreservesLimitsOfShape I CategoryTheory.yoneda
  CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf J _)

lemma Limits.preservesFiniteProducts_of_preservesLimitsOfShape {D : Type*} [Category D] (F : C ⥤ D)
    (H : ∀ (ι : Type v) [Finite ι], PreservesLimitsOfShape (Discrete ι) F) :
    PreservesFiniteProducts F := by
  constructor
  intro n
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F

lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Sieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.arrows.IsSheafFor (yoneda.obj Y) :=
  S.forallYonedaIsSheaf_iff_colimit.symm

lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Presieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.IsSheafFor (yoneda.obj Y) := by
  simp_rw [Presieve.isSheafFor_iff_generate S]
  rw [Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

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

@[simp]
lemma Sieve.generate_bot {X : C} : Sieve.generate (⊥ : Presieve X) = ⊥ := by
  rw [eq_bot_iff]
  rintro Y f ⟨Z, g, u, hg, rfl⟩
  exact hg

-- this needs more assumptions, but the proof will show which the correct ones are
lemma Presieve.isSheafFor_ofArrows_comp {F : Cᵒᵖ ⥤ Type*} {ι : Type*} {Y Z : ι → C}
    (f : ∀ i, Y i ⟶ X) (g : ∀ i, Z i ⟶ X)
    (e : ∀ i, Y i ≅ Z i) (H : Presieve.IsSheafFor F (.ofArrows _ g)) :
    Presieve.IsSheafFor F (.ofArrows _ (fun i ↦ (e i).hom ≫ g i)) := by
  let B (W : C) (w : W ⟶ X) (hw : Presieve.ofArrows _ g w) : Sieve W :=
    sorry
  have : .ofArrows _ (fun i ↦ (e i).hom ≫ g i) = Sieve.bind (.ofArrows _ g) B :=
    sorry
  rw [Presieve.isSheafFor_iff_generate, ← Sieve.ofArrows, this]
  sorry

@[ext]
lemma Presieve.FamilyOfElements.ext {F : Cᵒᵖ ⥤ Type*} {X : C} {R : Presieve X}
    (x y : R.FamilyOfElements F) (H : ∀ {Y : C} (f : Y ⟶ X) (hf : R f), x f hf = y f hf) :
    x = y := by
  funext Z f hf
  exact H f hf

/-- A family of elements on `{ f : X ⟶ Y }` is an element of `F(X)`. -/
@[simps apply, simps -isSimp symm_apply]
def Presieve.FamilyOfElements.singletonEquiv (F : Cᵒᵖ ⥤ Type*) {X Y : C} (f : X ⟶ Y) :
    (singleton f).FamilyOfElements F ≃ F.obj (op X) where
  toFun x := x f (by simp)
  invFun x Z g hg := F.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]
lemma Presieve.FamilyOfElements.singletonEquiv_symm_apply_self (F : Cᵒᵖ ⥤ Type*) {X Y : C}
    (f : X ⟶ Y) (x : F.obj (op X)) :
    (singletonEquiv F f).symm x f ⟨⟩ = x := by
  simp [singletonEquiv_symm_apply]

lemma Presieve.FamilyOfElements.Compatible.singleton_iff
    (F : Cᵒᵖ ⥤ Type*) {X Y : C} (f : X ⟶ Y) (x : (singleton f).FamilyOfElements F) :
    x.Compatible ↔ ∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f →
      F.map p₁.op (x f (by simp)) = F.map p₂.op (x f (by simp)) := by
  rw [Compatible]
  refine ⟨fun H Z p₁ p₂ h ↦ H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ ↦ ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h

lemma Presieve.FamilyOfElements.IsAmalgamation.singleton_iff
    (F : Cᵒᵖ ⥤ Type*) {X Y : C} (f : X ⟶ Y) (x : (singleton f).FamilyOfElements F) (y : F.obj (op Y)) :
    x.IsAmalgamation y ↔ F.map f.op y = x f ⟨⟩ := by
  rw [IsAmalgamation]
  refine ⟨fun H ↦ H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H

lemma Presieve.isSheafFor_singleton {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSheafFor F (.singleton f) ↔
      ∀ (x : F.obj (op X)),
        (∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f → F.map p₁.op x = F.map p₂.op x) →
        ∃! y, F.map f.op y = x := by
  rw [IsSheafFor, Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv F f)]
  simp_rw [FamilyOfElements.Compatible.singleton_iff,
    FamilyOfElements.IsAmalgamation.singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

/-- The sheaf condition for a single morphism is the same as the canonical fork diagram being limiting. -/
lemma Equalizer.Presieve.isSheafFor_singleton_iff {F : Cᵒᵖ ⥤ Type*} {X Y : C} {f : X ⟶ Y}
    (c : PullbackCone f f) (hc : IsLimit c) :
    Presieve.IsSheafFor F (.singleton f) ↔
      Nonempty
        (IsLimit (Fork.ofι (F.map f.op) (f := F.map c.fst.op) (g := F.map c.snd.op)
          (by simp [← Functor.map_comp, ← op_comp, c.condition]))) := by
  have h (x : F.obj (op X)) :(∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f → F.map p₁.op x = F.map p₂.op x) ↔
      F.map c.fst.op x = F.map c.snd.op x := by
    refine ⟨fun H ↦ H _ _ c.condition, fun H Z p₁ p₂ h ↦ ?_⟩
    rw [← PullbackCone.IsLimit.lift_fst hc _ _ h, op_comp, FunctorToTypes.map_comp_apply, H]
    simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [Types.type_equalizer_iff_unique, Presieve.isSheafFor_singleton]
  simp_rw [h]

/--
If

- `F` contravariantly maps (suitable) coproducts to products,
- (suitable) coproducts exist in `C`, and
- (suitable) coproducts distribute over pullbacks, then:

`F` is a sheaf for the single object covering `{ ∐ᵢ Yᵢ ⟶ X }`
if and only if it is a presieve for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {F : Cᵒᵖ ⥤ Type*} {X : C} {ι : Type} {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [(ofArrows Y f).hasPullbacks]
    [HasCoproduct Y] [HasCoproduct fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)]
    [HasPullback (Sigma.desc f) (Sigma.desc f)]
    [PreservesLimit (Discrete.functor <| fun i ↦ op (Y i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F]
    [IsIso (Sigma.desc fun (ij : ι × ι) ↦ pullback.map (f ij.fst) (f ij.snd)
      (Sigma.desc f) (Sigma.desc f) (Sigma.ι _ _) (Sigma.ι _ _) (𝟙 X) (by simp) (by simp))] :
    Presieve.IsSheafFor F (.singleton <| Sigma.desc f) ↔
      Presieve.IsSheafFor F (.ofArrows Y f) := by
  let e : (∐ fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)) ⟶
      pullback (Sigma.desc f) (Sigma.desc f) :=
    Sigma.desc fun ij ↦ pullback.map _ _ _ _ (Sigma.ι _ _) (Sigma.ι _ _) (𝟙 X) (by simp) (by simp)
  rw [Equalizer.Presieve.isSheafFor_singleton_iff (pullback.cone _ _) (pullback.isLimit _ _),
    Equalizer.Presieve.Arrows.sheaf_condition]
  refine (Fork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).nonempty_congr
  · exact F.mapIso (opCoproductIsoProduct Y) ≪≫ PreservesProduct.iso F _
  · exact F.mapIso (.op <| asIso e) ≪≫ F.mapIso (opCoproductIsoProduct _) ≪≫
      PreservesProduct.iso F _
  · exact Iso.refl _
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.fst_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.firstMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_fst, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.snd_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.secondMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_snd, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    simp only [Fork.ofι_pt, Fork.ι_ofι, Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
      Category.assoc, piComparison_comp_π]
    rw [← F.map_comp, ← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← op_comp, Sigma.ι_desc]
    simp [Equalizer.Presieve.Arrows.forkMap]

end CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}}

@[simp]
lemma Scheme.Cover.pullbackArrows_ofArrows [P.IsStableUnderBaseChange] {X S : Scheme.{u}}
    (𝒰 : S.Cover P) (f : X ⟶ S) :
    (Presieve.ofArrows 𝒰.obj 𝒰.map).pullbackArrows f =
      .ofArrows (𝒰.pullbackCover' f).obj (𝒰.pullbackCover' f).map := by
  rw [← Presieve.ofArrows_pullback]
  rfl

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_grothendieckTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} P S) :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ Scheme.grothendieckTopology P S := by
  rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, rfl⟩, Sieve.le_generate _⟩

open Scheme

def qcPretopology (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : Pretopology Scheme.{u} where
  coverings Y S := ∃ (𝒰 : Cover.{u} P Y) (h : 𝒰.QuasiCompact), S = Presieve.ofArrows 𝒰.obj 𝒰.map
  has_isos _ _ f _ := ⟨coverOfIsIso f, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h𝒰, rfl⟩
    exact ⟨𝒰.pullbackCover' f, inferInstance, (Presieve.ofArrows_pullback _ _ _).symm⟩
  transitive := by
    rintro X _ T ⟨𝒰, h𝒰, rfl⟩ H
    choose 𝒱 hc𝒱 h𝒱 using H
    refine ⟨𝒰.bind (fun j ↦ 𝒱 (𝒰.map j) ⟨j⟩), inferInstance, ?_⟩
    simpa only [Cover.bind, ← h𝒱] using Presieve.ofArrows_bind 𝒰.obj 𝒰.map _
      (fun _ f H => (𝒱 f H).obj) (fun _ f H => (𝒱 f H).map)

abbrev fpqcPretopology : Pretopology Scheme.{u} := qcPretopology @Flat

abbrev qcTopology (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : GrothendieckTopology Scheme.{u} := (qcPretopology P).toGrothendieck

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_qcTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} P S) [𝒰.QuasiCompact] :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ qcTopology P S := by
  rw [qcTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, ‹_›, rfl⟩, Sieve.le_generate _⟩

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

/-- The fqpc-topology on the category of schemes is the Grothendieck topology associated
to the pretopology given by fqpc-covers. -/
abbrev fpqcTopology : GrothendieckTopology Scheme.{u} := fpqcPretopology.toGrothendieck

lemma zariskiTopology_le_qcTopology [IsLocalAtSource P] :
    zariskiTopology ≤ qcTopology P := by
  rw [qcTopology, zariskiTopology, (Pretopology.gi _).gc.le_iff_le]
  rintro S R ⟨𝒰, rfl⟩
  rw [Pretopology.mem_ofGrothendieck]
  let 𝒰' : Cover P S := 𝒰.changeProp P (fun j ↦ IsLocalAtSource.of_isOpenImmersion _)
  have : 𝒰'.QuasiCompact := ⟨(inferInstanceAs <| 𝒰.QuasiCompact).1⟩
  exact 𝒰'.generate_ofArrows_mem_qcTopology

variable {P} in
@[simps!]
noncomputable
def Scheme.Hom.cover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] : Cover.{v} P S :=
  .mkOfCovers PUnit.{v + 1} (fun _ ↦ X) (fun _ ↦ f) (fun x ↦ ⟨⟨⟩, f.surjective x⟩) (fun _ ↦ hf)

instance {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] [QuasiCompact f] :
    (f.cover hf).QuasiCompact :=
  sorry

lemma ofArrows_homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] :
    Presieve.ofArrows (f.cover hf).obj (f.cover hf).map = Presieve.singleton f :=
  sorry

open Opposite

@[simps!]
noncomputable
def Scheme.affineCover' (X : Scheme.{u}) : X.OpenCover :=
  .mkOfCovers X.affineOpens (fun i ↦ i.1) (fun i ↦ i.1.ι) fun x ↦ by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)
      (show x ∈ ⊤ from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

variable {P}

lemma Cover.QuasiCompact.exists_hom {S : Scheme.{u}} (𝒰 : S.Cover P)
    [CompactSpace S] [𝒰.QuasiCompact] :
    ∃ (𝒱 : S.AffineCover P) (f : 𝒱.cover ⟶ 𝒰), Finite 𝒱.J ∧ ∀ j, IsOpenImmersion (f.app j) :=
  sorry

lemma Scheme.Cover.Hom.isSheafFor {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S : Scheme.{u}} {𝒰 𝒱 : S.Cover P}
    (f : 𝒰 ⟶ 𝒱)
    (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.map))
    (H₂ : ∀ {X : Scheme.{u}} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullbackCover' f).obj (𝒰.pullbackCover' f).map)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.obj 𝒱.map) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.obj 𝒰.map))
  · show Sieve.generate _ ≤ Sieve.generate _
    rw [Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    rw [← f.w]
    exact ⟨_, f.app i, 𝒱.map _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
    rw [← Presieve.ofArrows_pullback]
    apply H₂

lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ ↦ (h.uniqueUpToIso specPunitIsInitial).hom.homeomorph.isEmpty,
    fun _ ↦ ⟨isInitialOfIsEmpty⟩⟩

lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] :
    ⊥ ∈ Scheme.grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  let 𝒰 : Cover.{u} P X :=
    { J := PEmpty
      obj := PEmpty.elim
      map i := i.elim
      f x := (IsEmpty.false x).elim
      covers x := (IsEmpty.false x).elim
      map_prop x := x.elim }
  have : Presieve.ofArrows 𝒰.obj 𝒰.map = ⊥ := by
    rw [eq_bot_iff]
    rintro - - ⟨i⟩
    exact i.elim
  rw [← this]
  exact 𝒰.generate_ofArrows_mem_grothendieckTopology

instance : IsEmpty (⊥_ Scheme) := by
  rw [← isInitial_iff_isEmpty]
  exact ⟨initialIsInitial⟩

instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

instance : FinitaryExtensive Scheme.{u} := by
  let c : BinaryCofan (Spec (.of <| ULift.{u} ℤ)) (Spec (.of <| ULift.{u} ℤ)) :=
    .mk (P := Spec (.of <| ULift.{u} ℤ × ULift.{u} ℤ))
      (Spec.map <| CommRingCat.ofHom <| RingHom.fst _ _)
      (Spec.map <| CommRingCat.ofHom <| RingHom.snd _ _)
  have hc : IsColimit c := sorry
  rw [finitaryExtensive_iff_of_isTerminal _ _ specULiftZIsTerminal c hc]
  refine BinaryCofan.isVanKampen_mk c (fun X Y ↦ Sigma.cocone _) ?_ ?_ ?_ ?_ ?_
  · exact fun X Y ↦ coproductIsCoproduct' (pair X Y)
  · exact fun {X Y Z} f g ↦ pullback.cone f g
  · exact fun {X Y Z} f g ↦ pullback.isLimit f g
  · intro X Y f g h hf hg
    refine ⟨?_, ?_⟩
    · dsimp at h
      dsimp
      sorry
    · sorry
  · intro Z f
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · intro s
      dsimp
      sorry
    · sorry
    · sorry

instance : FinitaryExtensive AffineScheme.{u} := by
  let F : AffineScheme.{u} ⥤ Scheme.{u} := AffineScheme.forgetToScheme
  have : PreservesColimitsOfShape (Discrete WalkingPair) F := sorry
  apply finitaryExtensive_of_preserves_and_reflects F

lemma isEmpty_of_commSq_sigmaι_of_ne {ι : Type u} {X : ι → Scheme.{u}}
    {i j : ι} {Z : Scheme.{u}} {f : Z ⟶ X i} {g : Z ⟶ X j}
    (h : CommSq f g (Sigma.ι X i) (Sigma.ι X j)) (hij : i ≠ j) :
    IsEmpty Z := by
  refine ⟨fun z ↦ ?_⟩
  fapply eq_bot_iff.mp <| disjoint_iff.mp <| disjoint_opensRange_sigmaι X i j hij
  · exact (f ≫ Sigma.ι X i).base z
  · refine ⟨⟨f.base z, rfl⟩, ⟨g.base z, ?_⟩⟩
    rw [← Scheme.comp_base_apply, h.w]

lemma isEmpty_pullback_sigmaι_of_ne {ι : Type u} (X : ι → Scheme.{u})
    {i j : ι} (hij : i ≠ j) :
    IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

noncomputable
instance : CoproductsDisjoint Scheme.{u} where
  CoproductDisjoint X Y := by
    let c : BinaryCofan X Y := Sigma.cocone (pair X Y)
    have : Mono (BinaryCofan.inr (Sigma.cocone (pair X Y))) := sorry
    have : Mono (BinaryCofan.inl (Sigma.cocone (pair X Y))) := sorry
    fapply CoproductDisjoint.of_binaryCofan_of_pullbackCone (Sigma.cocone (pair X Y))
      (coproductIsCoproduct' (pair X Y)) (pullback.cone _ _)
      (pullback.isLimit _ _)
    sorry

-- universe restrictions can be removed again, after #25764 is merged
lemma preservesFiniteProducts_of_isSheaf_zariskiTopology {F : Scheme.{0}ᵒᵖ ⥤ Type*}
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesFiniteProducts F := by
  apply Limits.preservesFiniteProducts_of_preservesLimitsOfShape.{0}
  intro ι _
  apply (config := { allowSynthFailures := true }) preservesLimitsOfShape_of_discrete
  intro X
  let X' := unop ∘ X
  show PreservesLimit (Discrete.functor fun i ↦ op (X' i)) F
  have (i : ι) : Mono (Cofan.inj (Sigma.cocone (Discrete.functor X')) i) :=
    inferInstanceAs <| Mono (Sigma.ι _ _)
  refine Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial
      (Sigma.cocone (Discrete.functor X')) (coproductIsCoproduct' _) ?_ ?_
  · apply hF.isSheafFor
    convert bot_mem_grothendieckTopology (⊥_ Scheme)
    rw [eq_bot_iff]
    rintro Y f ⟨g, _, _, ⟨i⟩, _⟩
    exact i.elim
  · intro i j hij
    refine ⟨?_, ⟨?_⟩⟩
    · simp
    · refine PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        exact isInitialOfIsEmpty.to _
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        apply isInitialOfIsEmpty.hom_ext
      · intro s
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        apply isInitialOfIsEmpty.hom_ext
      · intro s m
        have : IsEmpty s.pt := isEmpty_of_commSq_sigmaι_of_ne ⟨s.condition⟩ hij
        intro x y
        apply isInitialOfIsEmpty.hom_ext
  · exact hF.isSheafFor _ _ (sigmaOpenCover X').generate_ofArrows_mem_grothendieckTopology

lemma Scheme.Cover.isSheafFor_sigma_iff' {F : Scheme.{u}ᵒᵖ ⥤ Type (max u (u + 1))} [IsLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover P) :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.obj 𝒰.sigma.map) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.obj 𝒰.map) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Equalizer.Presieve.sheaf_condition]
    sorry
  · sorry

lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type*} [IsLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover P) :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.obj 𝒰.sigma.map) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.obj 𝒰.map) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro x hx
    let 𝒱 : OpenCover (∐ 𝒰.obj) := sigmaOpenCover _
    let P : Presieve (∐ 𝒰.obj) := Presieve.ofArrows _ 𝒱.map
    let fam : P.FamilyOfElements F := sorry
    let z : F.obj (op <| ∐ 𝒰.obj) :=
      (hF.isSheafFor _ _ (generate_ofArrows_mem_grothendieckTopology _)).amalgamate fam
        sorry
    let y : Presieve.FamilyOfElements F (Presieve.ofArrows 𝒰.sigma.obj 𝒰.sigma.map) :=
      sorry
    sorry
  · sorry

lemma Scheme.Cover.ofArrows_of_unique {S : Scheme.{u}} (𝒰 : S.Cover P) [Unique 𝒰.J] :
    Presieve.ofArrows 𝒰.obj 𝒰.map = Presieve.singleton (𝒰.map default) :=
  sorry

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.J] :
    𝒰.cover.QuasiCompact :=
  sorry

lemma isSheafFor_iff_of_iso {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (e : X ≅ Y) (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    (he : e.hom ≫ g = f) :
    Presieve.IsSheafFor F (.singleton f) ↔ Presieve.IsSheafFor F (.singleton g) := by
  subst he
  refine ⟨fun hf ↦ ?_, ?_⟩
  · sorry
  · sorry

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`.-/
@[stacks 022H]
nonrec lemma isSheaf_qcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) [IsLocalAtSource P] :
    Presieve.IsSheaf (qcTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_qcTopology P) hF
  · apply hF.isSheafFor
    rw [← ofArrows_homCover P _ hf]
    exact Cover.generate_ofArrows_mem_qcTopology _
  · rw [Presieve.isSheaf_pretopology]
    rintro T - ⟨𝒰, _, rfl⟩
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · let 𝒱 : T.OpenCover := T.affineCover
      have h (j : T.affineCover.J) : Presieve.IsSheafFor F
          (.ofArrows (𝒰.pullbackCover' (𝒱.map j)).obj (𝒰.pullbackCover' (𝒱.map j)).map) :=
        this _ inferInstance ⟨_, rfl⟩
      refine .of_isSheafFor_pullback' F (.ofArrows 𝒱.obj 𝒱.map) _ ?_ ?_ ?_ ?_
      · exact hzar.isSheafFor _ _ 𝒱.generate_ofArrows_mem_grothendieckTopology
      · intro Y f
        refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
        rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm, Cover.pullbackArrows_ofArrows]
        exact (Cover.pullbackCover' 𝒱 f).generate_ofArrows_mem_grothendieckTopology
      · rintro - - - - ⟨i⟩ ⟨j⟩
        use .ofArrows (pullback (𝒱.map i) (𝒱.map j)).affineCover.obj
          (pullback (𝒱.map i) (𝒱.map j)).affineCover.map
        refine ⟨(hzar.isSheafFor _ _ <|
            Cover.generate_ofArrows_mem_grothendieckTopology _).isSeparatedFor, ?_⟩
        · rintro - - ⟨k⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
          apply Presieve.IsSheafFor.isSeparatedFor
          rw [← Presieve.ofArrows_pullback]
          exact this (𝒰.pullbackCover' _) inferInstance ⟨_, rfl⟩
      · rintro - - ⟨i⟩
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullbackCover' (𝒱.map i)) inferInstance ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.obj i)) ∧ Finite 𝒰.J generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := Cover.QuasiCompact.exists_hom 𝒰
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullbackCover' f).obj (𝒱.cover.pullbackCover' f).map) := by
        let 𝒰V := V.affineCover
        refine .of_isSheafFor_pullback' F (.ofArrows 𝒰V.obj 𝒰V.map) _ ?_ ?_ ?_ ?_
        · exact hzar.isSheafFor _ _ 𝒰V.generate_ofArrows_mem_grothendieckTopology
        · intro Y f
          refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
          rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm, Cover.pullbackArrows_ofArrows]
          exact (Cover.pullbackCover' 𝒰V f).generate_ofArrows_mem_grothendieckTopology
        · rintro - - - - ⟨i⟩ ⟨j⟩
          refine ⟨.ofArrows _ (pullback (𝒰V.map i) (𝒰V.map j)).affineCover.map, ?_, ?_⟩
          · exact hzar.isSheafFor _ _
              (Cover.generate_ofArrows_mem_grothendieckTopology _) |>.isSeparatedFor
          · rintro - - ⟨k⟩
            rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
              ← Presieve.isSeparatedFor_iff_generate]
            refine (this _ ((𝒱.cover.pullbackCover' f).pullbackCover' _) inferInstance
              ⟨fun l ↦ ?_, hfin⟩).isSeparatedFor
            exact .of_isIso (pullbackLeftPullbackSndIso (𝒱.map l) f _).hom
        · rintro - - ⟨i⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullbackCover' f).pullbackCover' (𝒰V.map i)
          refine this _ 𝒰' inferInstance
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.map j) f (𝒰V.map i)).hom, hfin⟩
      refine f.isSheafFor ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ _ inferInstance ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.sigma
    rw [← Scheme.Cover.isSheafFor_sigma_iff hzar, Scheme.Cover.ofArrows_of_unique]
    have : IsAffine (𝒰.sigma.obj default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.sigma.obj default).isoSpec.inv ≫ 𝒰.sigma.map default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [isSheafFor_iff_of_iso _ (Spec.map φ) (𝒰.sigma.obj default).isoSpec hzar (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsLocalAtSource.comp (𝒰.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_J, PUnit.default_eq_unit, Cover.sigma_obj, Cover.sigma_map, f]
      infer_instance

lemma isSheaf_fpqcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf fpqcTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (_ : f.hom.Flat) (_ : Surjective (Spec.map f)),
          Presieve.IsSheafFor F (Presieve.singleton (Spec.map f)) := by
  rw [isSheaf_qcTopology_iff]
  congr!
  exact HasRingHomProperty.Spec_iff

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) := by
  constructor
  constructor
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry

/-- The fpqc topology is subcanonical. -/
instance : fpqcTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
  rw [isSheaf_fpqcTopology_iff (yoneda.obj X)]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)
  · intro R S f hf hs
    revert X
    rw [← Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda,
      Sieve.effectiveEpimorphic_singleton]
    exact effectiveEpi_of_flat _ hf hs

/-- A quasi-compact flat cover is an effective epimorphism family. -/
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}} (𝒰 : X.Cover @Flat)
    [𝒰.QuasiCompact] : EffectiveEpiFamily 𝒰.obj 𝒰.map :=
  -- immediate consequence of fqpc subcanonical
  sorry

end AlgebraicGeometry
