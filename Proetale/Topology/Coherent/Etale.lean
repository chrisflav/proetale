/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty
import Proetale.Topology.Flat.Sheaf

/-!
# The small étale site is (pre)coherent
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C]

lemma Limits.ClosedUnderColimitsOfShape.discrete {ι : Type*} {P : ObjectProperty C}
    [P.IsClosedUnderIsomorphisms]
    (h : ∀ {f : ι → C} [HasColimit (Discrete.functor f)], (∀ j, P (f j)) → P (∐ f)) :
    P.IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine .mk' fun X ↦ ?_
  rintro ⟨F, hF⟩
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    hasColimit_of_iso Discrete.natIsoFunctor.symm
  rw [P.prop_iff_of_iso <| HasColimit.isoOfNatIso Discrete.natIsoFunctor]
  exact h fun j ↦ hF ⟨j⟩

instance (X : C) (P : MorphismProperty C) [P.RespectsIso] :
    ObjectProperty.IsClosedUnderIsomorphisms fun Y : Over X ↦ P Y.hom := by
  constructor
  intro Y Z e hY
  simpa [← P.cancel_left_of_respectsIso e.hom.left]

instance {C D E : Type*} [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [F.ReflectsEffectiveEpis] [G.ReflectsEffectiveEpis] :
    (F ⋙ G).ReflectsEffectiveEpis where
  reflects _ hf := F.effectiveEpi_of_map _ (G.effectiveEpi_of_map _ hf)

instance Functor.ReflectsEffectiveEpis.of_preservesLimitsOfShape {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) [HasPullbacks C] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan F] [ReflectsColimitsOfShape WalkingParallelPair F] :
    F.ReflectsEffectiveEpis where
  reflects {X Y} f hf := by
    apply effectiveEpi_of_kernelPair
    apply isColimitOfReflects F
    let n : parallelPair (pullback.fst f f) (pullback.snd f f) ⋙ F ≅
        parallelPair ((pullback.fst (F.map f) (F.map f))) (pullback.snd (F.map f) (F.map f)) := by
      refine diagramIsoParallelPair _ ≪≫ NatIso.ofComponents (fun i ↦ ?_) fun f ↦ ?_
      · match i with
        | .one => exact Iso.refl (F.obj X)
        | .zero => exact PreservesPullback.iso _ _ _
      · rcases f <;> simp
    refine IsColimit.precomposeInvEquiv n (F.mapCocone (Cofork.ofπ f pullback.condition)) ?_
    let e : (Cocone.precompose n.inv).obj (F.mapCocone (Cofork.ofπ f pullback.condition)) ≅
        Cofork.ofπ (F.map f) pullback.condition := by
      refine Cocone.ext (Iso.refl _) fun j ↦ ?_
      cases j <;> simp [n]
    refine .ofIsoColimit ?_ e.symm
    exact (regularEpiOfEffectiveEpi (F.map f)).isColimit

lemma Preregular.of_hasPullbacks_of_effectiveEpi_fst {C : Type*} [Category C] [HasPullbacks C]
    (h : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S), EffectiveEpi g → EffectiveEpi (pullback.fst f g)) :
    Preregular C where
  exists_fac f g :=
    ⟨pullback f g, pullback.fst _ _, h _ _ ‹_›, pullback.snd _ _, pullback.condition.symm⟩

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u})

variable (P : MorphismProperty Scheme.{u})

instance IsZariskiLocalAtSource.closedUnderColimitsOfShape_discrete (J : Type*) [Small.{u} J]
    [IsZariskiLocalAtSource P] :
    (P.overObj (X := X)).IsClosedUnderColimitsOfShape (Discrete J) := by
  refine Limits.ClosedUnderColimitsOfShape.discrete fun {f} _ hf ↦ ?_
  have : (PreservesCoproduct.iso (Over.forget X) _).inv ≫ (∐ f).hom =
      Sigma.desc fun j ↦ (f j).hom := by
    refine Limits.Sigma.hom_ext _ _ fun j ↦ ?_
    rw [PreservesCoproduct.inv_hom, Limits.ι_comp_sigmaComparison_assoc]
    simp
  rw [MorphismProperty.overObj]
  rw [← P.cancel_left_of_respectsIso (PreservesCoproduct.iso (Over.forget X) _).inv, this]
  exact IsZariskiLocalAtSource.sigmaDesc hf

instance : FinitaryExtensive (Over X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (Over.forget X)

instance [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    [P.HasOfPostcompProperty P] :
    FinitaryExtensive (MorphismProperty.Over P ⊤ X) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (MorphismProperty.Over.forget P ⊤ X)

instance (J : Type*) [Small.{u} J] : HasCoproductsOfShape J X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

noncomputable instance (J : Type*) [Small.{u} J] :
    CreatesColimitsOfShape (Discrete J) (Scheme.Etale.forget X) := by
  dsimp [Scheme.Etale.forget, Scheme.Etale]
  infer_instance

noncomputable instance : CreatesLimitsOfShape WalkingCospan (Scheme.Etale.forget.{u} X) :=
  CategoryTheory.MorphismProperty.Over.createsLimitsOfShape_walkingCospan _ _

instance Scheme.Etale.finitaryExtensive : FinitaryExtensive X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

instance (X : Scheme) [Nonempty X] : Nontrivial Γ(X, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some ‹_›, trivial⟩⟩
  apply Scheme.component_nontrivial

lemma Scheme.exists_nontrivial_hom_of_nonempty (X : Scheme) [Nonempty X] :
    ∃ (Y : Scheme), Nontrivial (X ⟶ Y) := by
  refine ⟨𝔸(Unit; X), AffineSpace.homOfVector (𝟙 X) 0, AffineSpace.homOfVector (𝟙 X) 1, ?_⟩
  rw [ne_eq, AffineSpace.hom_ext_iff]
  simp

instance {X Y : Scheme} (f : X ⟶ Y) [Epi f] [Nonempty Y] [Subsingleton Y] : Surjective f := by
  by_contra h
  have : IsEmpty X := ⟨fun x ↦ h ⟨fun y ↦ ⟨x, Subsingleton.elim _ _⟩⟩⟩
  obtain ⟨Z, ⟨g₁, g₂, hne⟩⟩ := Y.exists_nontrivial_hom_of_nonempty
  apply hne
  rw [← cancel_epi f]
  apply isInitialOfIsEmpty.hom_ext _ _

@[simp]
lemma Scheme.Hom.apply_fiberι {X Y : Scheme} (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f.base ((f.fiberι y).base x) = y := by
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage, ← Scheme.Hom.range_fiberι]
  use x

/-- Universal epimorphisms in the category of schemes are surjective. -/
instance {X Y : Scheme} (f : X ⟶ Y) [Epi f]
    [∀ {Z} (g : Z ⟶ Y), Epi (pullback.snd f g)] : Surjective f := by
  constructor
  intro y
  let g := Y.fromSpecResidueField y
  have h : Surjective (pullback.snd f g) := inferInstance
  obtain ⟨x, hx⟩ := h.1 default
  use (f.fiberι y).base x
  simp

lemma isIso_pushoutDesc_iff_epi {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [HasPushout f f] :
    IsIso (pushout.desc (f := f) (g := f) (𝟙 _) (𝟙 _)) ↔ Epi f := by
  refine ⟨fun h ↦ ⟨fun g₁ g₂ h ↦ ?_⟩, fun hf ↦ ?_⟩
  · rw [← pushout.inl_desc _ _ h, (cancel_mono (g := pushout.inl f f) (h := pushout.inr f f)
      (pushout.desc (𝟙 _) (𝟙 _))).mp (by simp), pushout.inr_desc]
  · rw [(IsIso.inv_eq_of_hom_inv_id <| pushout.inl_desc (𝟙 _) (𝟙 _) (by simp)).symm]
    infer_instance

lemma inl_eq_inr_iff_epi {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) [HasPushout f f] :
    pushout.inl f f = pushout.inr f f ↔ Epi f := by
  refine ⟨?_, ?_⟩
  · intro h
    suffices h : IsIso (pushout.inl f f) by
      rw [← isIso_pushoutDesc_iff_epi,
        (IsIso.inv_eq_of_hom_inv_id <| pushout.inl_desc (𝟙 _) (𝟙 _) (by simp)).symm]
      infer_instance
    use pushout.desc (𝟙 _) (𝟙 _) (by simp)
    simp only [colimit.ι_desc, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app, true_and]
    apply pushout.hom_ext
    · simp
    · simpa
  · intro hf
    exact inl_eq_inr_of_epi_eq f

lemma _root_.CategoryTheory.Limits.Types.inl_ne_inr_of_isPushout_of_not_surjective
    {U X Y : Type u} (f : U ⟶ X) {inl inr : X ⟶ Y} (h : IsPushout f f inl inr)
    (hf : ¬ Function.Surjective f) :
    inl ≠ inr := by
  suffices heq : pushout.inl f f ≠ pushout.inr f f by
    rwa [ne_eq, ← cancel_mono h.isoPushout.inv,
      IsPushout.inl_isoPushout_inv, IsPushout.inr_isoPushout_inv] at heq
  rwa [ne_eq, inl_eq_inr_iff_epi, epi_iff_surjective]

lemma inl_ne_inr_of_isOpenImmersion_of_not_surjective {U X Y : Scheme} (f : U ⟶ X)
    {inl inr : X ⟶ Y} (h : IsPushout f f inl inr)
    [IsOpenImmersion f] (hf : ¬ Function.Surjective f.base) :
    inl ≠ inr := by
  intro heq
  have _ : PreservesColimit (span f f) Scheme.forget := by
    rw [Scheme.forget, Scheme.forgetToTop, LocallyRingedSpace.forgetToTop]
    infer_instance
  apply Types.inl_ne_inr_of_isPushout_of_not_surjective (Scheme.forget.map f) _ _
      (congrArg Scheme.forget.map heq)
  · exact Scheme.forget.map_isPushout h
  · simpa

lemma exists_hom_ne_of_not_surjective
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    {S : Scheme} {X : P.Over ⊤ S}
    {U : P.Over ⊤ S} (i : U ⟶ X) [IsOpenImmersion i.left]
    (hi : ¬ Function.Surjective i.left.base) :
    ∃ (Y : P.Over ⊤ S) (g₁ g₂ : X ⟶ Y),
      IsOpenImmersion g₁.left ∧ IsOpenImmersion g₂.left ∧
        g₁ ≠ g₂ ∧ i ≫ g₁ = i ≫ g₂ := by
  refine ⟨pushout i i, pushout.inl _ _, pushout.inr _ _, inferInstance, inferInstance,
      fun heq ↦ ?_, pushout.condition⟩
  refine inl_ne_inr_of_isOpenImmersion_of_not_surjective i.left ?_ hi congr($(heq).left)
  exact (MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S).map_isPushout (.of_hasPushout i i)

lemma Scheme.Opens.exists_hom_ne_of_ne_top {X : Scheme} {U : X.Opens} (hU : U ≠ ⊤) :
    ∃ (Y : Scheme) (g₁ g₂ : X ⟶ Y),
      IsOpenImmersion g₁ ∧ IsOpenImmersion g₂ ∧ g₁ ≠ g₂ ∧ U.ι ≫ g₁ = U.ι ≫ g₂ := by
  refine ⟨pushout U.ι U.ι, pushout.inl _ _, pushout.inr _ _,
    inferInstance, inferInstance, ?_, pushout.condition⟩
  apply inl_ne_inr_of_isOpenImmersion_of_not_surjective U.ι (.of_hasPushout _ _)
  simpa [← Set.range_eq_univ]

noncomputable def IsOpenImmersion.liftOver {P : MorphismProperty Scheme.{u}}
    {S : Scheme.{u}} {X Y U : P.Over ⊤ S}
    (i : U ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i.left]
    (H : Set.range f.left.base ⊆ Set.range i.left.base) :
    X ⟶ U :=
  MorphismProperty.Over.homMk (IsOpenImmersion.lift i.left f.left H) <| by
    rw [← MorphismProperty.Over.w i, lift_fac_assoc, MorphismProperty.Over.w f]

@[reassoc (attr := simp)]
lemma IsOpenImmersion.liftOver_fac {P : MorphismProperty Scheme.{u}}
    {S : Scheme.{u}} {X Y U : P.Over ⊤ S}
    (i : U ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion i.left]
    (H : Set.range f.left.base ⊆ Set.range i.left.base) :
    liftOver i f H ≫ i = f := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- Any open epimorphism is surjective. -/
lemma Over.surjective_of_epi_of_isOpenMap {P : MorphismProperty Scheme} [IsZariskiLocalAtSource P]
    {S : Scheme} {X Y : P.Over ⊤ S}
    {f : X ⟶ Y} [Epi f] (hf : IsOpenMap f.left.base) :
    Surjective f.left := by
  let U : Y.left.Opens := ⟨Set.range f.left.base, hf.isOpen_range⟩
  let i : MorphismProperty.Over.mk _ (U.ι ≫ Y.hom) (IsZariskiLocalAtSource.comp Y.prop _) ⟶ Y :=
    MorphismProperty.Over.homMk U.ι rfl trivial
  have : IsOpenImmersion i.left := inferInstanceAs <| IsOpenImmersion U.ι
  suffices h : Function.Surjective i.left.base by
    rw [surjective_iff, ← Set.range_eq_univ, ← h.range_eq]
    simp [i, U]
  by_contra! hc
  obtain ⟨Z, g₁, g₂, _, _, h₁₂, heq⟩ := exists_hom_ne_of_not_surjective i hc
  apply h₁₂
  rw [← cancel_epi f]
  have : f = IsOpenImmersion.liftOver i f (by simp [i, U]) ≫ i := by simp
  rw [this, Category.assoc, heq, Category.assoc]

/-- Any open epimorphism is surjective. -/
lemma surjective_of_epi_of_isOpenMap {X Y : Scheme} (f : X ⟶ Y) [Epi f] (hf : IsOpenMap f.base) :
    Surjective f := by
  let U : Y.Opens := ⟨Set.range f.base, hf.isOpen_range⟩
  suffices h : U = ⊤ by
    rw [surjective_iff, ← Set.range_eq_univ]
    exact congr($(h).1)
  by_contra! hc
  obtain ⟨Z, g₁, g₂, _, _, h₁₂, heq⟩ := Scheme.Opens.exists_hom_ne_of_ne_top hc
  apply h₁₂
  rw [← cancel_epi f]
  have : f = IsOpenImmersion.lift U.ι f (by simp [U]) ≫ U.ι := by simp
  rw [this, Category.assoc, heq, Category.assoc]

instance {X Y : Scheme} (f : X ⟶ Y) [UniversallyOpen f] [Epi f] : Surjective f := by
  apply surjective_of_epi_of_isOpenMap
  exact f.isOpenMap

@[simp]
lemma Scheme.Etale.forget_map {S : Scheme} {X Y : S.Etale} (f : X ⟶ Y) :
    (Scheme.Etale.forget S).map f = f.hom :=
  rfl

instance {S : Scheme} {X Y : S.Etale} (f : X ⟶ Y) : Etale f.left :=
  MorphismProperty.of_postcomp @Etale f.left Y.hom Y.prop (by simp [X.prop])

-- These are regressions in mathlib
instance (S : Scheme) : (Scheme.Etale.forget S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.forget _ _ _).Full
instance (S : Scheme) : (Scheme.Etale.forget S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.forget _ _ _).Faithful

/-- A morphism in the small étale site is an epimorphism if and only if it is surjective. -/
instance Scheme.Etale.effectiveEpi_of_surjective {S : Scheme} {X Y : S.Etale} (f : X ⟶ Y)
    [Surjective f.left] : EffectiveEpi f := by
  apply (Scheme.Etale.forget S ⋙ Over.forget S).effectiveEpi_of_map
  dsimp
  infer_instance

/-- A morphism in the small étale site is an epimorphism if and only if it is surjective. -/
instance Scheme.Etale.surjective_of_epi {S : Scheme} {X Y : S.Etale} (f : X ⟶ Y)
    [Epi f] : Surjective f.left :=
  Over.surjective_of_epi_of_isOpenMap f.left.isOpenMap

/-- A morphism in the small étale site is an epimorphism if and only if it is surjective. -/
lemma Scheme.Etale.epi_iff_surjective {S : Scheme} {X Y : S.Etale} (f : X ⟶ Y) :
    Epi f ↔ Surjective f.left :=
  ⟨fun _ ↦ Over.surjective_of_epi_of_isOpenMap f.left.isOpenMap, fun _ ↦ inferInstance⟩

/-- The small étale site of a scheme is preregular. -/
instance Scheme.Etale.preregular (S : Scheme.{u}) : Preregular S.Etale := by
  apply Preregular.of_hasPullbacks_of_effectiveEpi_fst
  intro X Y Z f g hg
  have : Surjective (pullback.fst f g).left := by
    rw [← MorphismProperty.Over.forget_comp_forget_map, ← pullbackComparison_comp_fst]
    rw [MorphismProperty.cancel_left_of_respectsIso (P := @Surjective)]
    dsimp
    infer_instance
  infer_instance

/-- The small étale site of a scheme is precoherent. -/
lemma Scheme.Etale.precoherent (S : Scheme.{u}) : Precoherent S.Etale :=
  inferInstance

end AlgebraicGeometry
