/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Proetale.Morphisms.WeaklyEtale

/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.MorphismProperty

universe w' v' u'

variable {C : Type u'} [Category.{v'} C] {P : MorphismProperty C}

/-- If `P` is stable under composition, then `pro P` morphisms compose with `P`-morphisms. -/
lemma pro_comp_mem_of_mem [P.IsStableUnderComposition] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : pro.{w'} P f) (hg : P g) : pro.{w'} P (f ≫ g) := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  refine ⟨J, ‹_›, ‹_›, D, t ≫ (Functor.const J).map g, s, hs, fun j ↦ ⟨?_, ?_⟩⟩
  · exact P.comp_mem _ _ (hts j).1 hg
  · dsimp
    rw [← Category.assoc, (hts j).2]

/-- If `P`-morphisms are finitely presentable and `P` cancels from the left, then `ind P`
cancels `P`-morphisms from the left: if `f` satisfies `P` and `f ≫ g` satisfies `ind P`,
then `g` satisfies `ind P`. -/
lemma ind_hasOfPrecompProperty [P.HasOfPrecompProperty P]
    (hP : P ≤ isFinitelyPresentable.{w'} C) :
    (ind.{w'} P).HasOfPrecompProperty P where
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
    [P.HasOfPrecompProperty P] [LocallySmall.{w'} C]
    (hP : P ≤ isFinitelyPresentable.{w'} C) :
    (ind.{w'} P).HasOfPrecompProperty (ind.{w'} P) where
  of_precomp {X Y Z} f g hf hfg := by
    haveI : (ind.{w'} P).HasOfPrecompProperty P := ind_hasOfPrecompProperty hP
    rw [← ind_ind hP]
    obtain ⟨I, _, _, B, t, c, hc, htc⟩ := hf
    -- Each composite `Bᵢ ⟶ Y ⟶ Z` is ind-`P`.
    have hind (i : I) : ind.{w'} P (c.app i ≫ g) := by
      refine MorphismProperty.of_precomp (W := ind.{w'} P) (W' := P) (t.app i) _ (htc i).1 ?_
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
    have hinr {i i' : I} (a : i ⟶ i') :
        pushout.inr (c.app i) (c.app i ≫ g) ≫ E.map a =
          pushout.inr (c.app i') (c.app i' ≫ g) := by
      simp [E]
    have hinl {i i' : I} (a : i ⟶ i') :
        pushout.inl (c.app i) (c.app i ≫ g) ≫ E.map a =
          pushout.inl (c.app i') (c.app i' ≫ g) := by
      simp [E]
    have hinrw : ∀ (w : Cocone E) (i i' : I),
        pushout.inr (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
          pushout.inr (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := by
      have h1 : ∀ (w : Cocone E) {i i' : I} (a : i ⟶ i'),
          pushout.inr (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
            pushout.inr (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := fun w i i' a ↦ by
        rw [← w.w a, ← Category.assoc, hinr a]
      intro w i i'
      exact (h1 w (IsFiltered.leftToMax i i')).trans (h1 w (IsFiltered.rightToMax i i')).symm
    have hinlw : ∀ (w : Cocone E) {i i' : I} (a : i ⟶ i'),
        pushout.inl (c.app i) (c.app i ≫ g) ≫ w.ι.app i =
          pushout.inl (c.app i') (c.app i' ≫ g) ≫ w.ι.app i' := fun w i i' a ↦ by
      rw [← w.w a, ← Category.assoc, hinl a]
    obtain ⟨i₀⟩ : Nonempty I := IsFiltered.nonempty
    refine ⟨I, ‹_›, ‹_›, E,
      { app i := pushout.inl _ _
        naturality {i i'} a := by
          dsimp
          rw [Category.id_comp, hinl a] },
      { app i := pushout.desc (f := c.app i) (g := c.app i ≫ g) g (𝟙 Z) (by simp)
        naturality {i i'} a := by
          apply pushout.hom_ext <;> simp [E] },
      ?_, fun i ↦ ⟨(ind.{w'} P).pushout_inl _ _ (hind i), by simp⟩⟩
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

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

/-- This is the property of morphisms of schemes that are of the form `lim Xᵢ ⟶ S`
where each `Xᵢ` is absolutely affine and étale over `X`. -/
def proAffineEtale : MorphismProperty Scheme.{u} :=
  MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)

lemma proAffineEtale.of_isAffine {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [Etale f] :
    proAffineEtale f :=
  MorphismProperty.le_pro _ _ ⟨‹_›, ⟨‹_›, trivial⟩⟩

/-- The domain of a pro-affine étale morphism is affine. -/
lemma proAffineEtale.isAffine {X S : Scheme.{u}} {f : X ⟶ S} (hf : proAffineEtale f) :
    IsAffine X := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  have hAff (j : J) : IsAffine (D.obj j) := ofObjectProperty_top_right_iff.mp (hts j).1.2
  exact Scheme.isAffine_of_isLimit (Cone.mk _ s) hs

/-- `IsAffine` is preserved under isomorphisms. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsAffine ·) where
  of_iso e h := (IsAffine.iff_of_isIso e.hom).mp h

instance : proAffineEtale.RespectsIso := by
  rw [proAffineEtale, pro_eq_unop_ind_op]
  infer_instance

/-- For any `MorphismProperty Scheme` `P` coming from a ring-hom property `Q` via
`HasRingHomProperty`, a morphism `Spec.map f` between affine schemes lies in
`pro (P ⊓ isAffine)` if and only if `f` lies in `ind (RingHom.toMorphismProperty Q)`.

The forward direction reflects a pro-affine cone of `Spec.map f` along the `Γ ⊣ Spec`
adjunction (an equivalence on affine objects) to a colimit cocone of ring maps; the
backward direction applies `Scheme.Spec` to such a colimit and packages the result
as a pro-cone. -/
lemma pro_inf_isAffine_Spec_iff (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (MorphismProperty.pro.{u} (P ⊓ ofObjectProperty (IsAffine ·) ⊤)) (Spec.map f) ↔
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty @Q) f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
    have hAff (j : J) : IsAffine (D.obj j) :=
      ofObjectProperty_top_right_iff.mp (hts j).1.2
    let Φ : Jᵒᵖ ⥤ CommRingCat.{u} := D.op ⋙ Scheme.Γ
    let σ (j' : Jᵒᵖ) : Φ.obj j' ⟶ S :=
      Spec.preimage (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom)
    let τ (j' : Jᵒᵖ) : R ⟶ Φ.obj j' :=
      Spec.preimage ((D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop)
    have hSpec_σ (j' : Jᵒᵖ) :
        Spec.map (σ j') = s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom :=
      Spec.map_preimage _
    have hSpec_τ (j' : Jᵒᵖ) :
        Spec.map (τ j') = (D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop :=
      Spec.map_preimage _
    let τNat : (Functor.const Jᵒᵖ).obj R ⟶ Φ :=
      { app := τ
        naturality := fun j' k' α ↦ by
          have : IsAffine (D.obj j'.unop) := hAff j'.unop
          have : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.id_comp]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_τ k', hSpec_τ j']
          have htn : t.app k'.unop = D.map α.unop ≫ t.app j'.unop := by
            have := t.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
            exact this.symm
          have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
          rw [htn, hΦmap]
          exact (Scheme.isoSpec_inv_naturality_assoc (D.map α.unop) (t.app j'.unop)).symm }
    let σNat : Φ ⟶ (Functor.const Jᵒᵖ).obj S :=
      { app := σ
        naturality := fun j' k' α ↦ by
          have : IsAffine (D.obj j'.unop) := hAff j'.unop
          have : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.comp_id]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_σ k', hSpec_σ j']
          have hsn : s.app j'.unop = s.app k'.unop ≫ D.map α.unop := by
            have := s.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
            exact this
          have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
          rw [hsn, hΦmap, Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc] }
    let legSpec (c' : Cocone Φ) (i : J) : Spec c'.pt ⟶ D.obj i :=
      Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv
    let mkScheme (c' : Cocone Φ) : Cone D :=
      { pt := Spec c'.pt
        π :=
          { app := legSpec c'
            naturality := fun i i' α ↦ by
              have : IsAffine (D.obj i) := hAff i
              have : IsAffine (D.obj i') := hAff i'
              dsimp only [legSpec, Functor.const_obj_obj, Functor.const_obj_map]
              rw [Category.id_comp]
              have hcnat : Φ.map α.op ≫ c'.ι.app (Opposite.op i) =
                  c'.ι.app (Opposite.op i') := by
                have := c'.ι.naturality α.op
                simp only [Functor.const_obj_obj, Functor.const_obj_map,
                  Category.comp_id] at this
                exact this
              have hΦmap : Φ.map α.op = (D.map α).appTop := Scheme.Γ_map_op (D.map α)
              rw [hΦmap] at hcnat
              rw [← hcnat, Spec.map_comp, Category.assoc,
                Scheme.isoSpec_inv_naturality, ← Category.assoc] } }
    refine ⟨Jᵒᵖ, inferInstance, inferInstance, Φ, τNat, σNat, ?_, fun j' ↦ ⟨?_, ?_⟩⟩
    · refine
        { desc := fun c' ↦ Spec.preimage (hs.lift (mkScheme c'))
          fac := fun c' j' ↦ ?_
          uniq := fun c' m hm ↦ ?_ }
      · apply Spec.map_injective
        have : IsAffine (D.obj j'.unop) := hAff j'.unop
        have hliftFac : hs.lift (mkScheme c') ≫ s.app j'.unop =
            Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
              (D.obj j'.unop).isoSpec.inv := hs.fac (mkScheme c') j'.unop
        rw [Spec.map_comp, Spec.map_preimage, hSpec_σ, ← Category.assoc, hliftFac,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · apply Spec.map_injective
        refine (hs.uniq (mkScheme c') (Spec.map m) ?_).trans
          (Spec.map_preimage (hs.lift (mkScheme c'))).symm
        intro i
        have : IsAffine (D.obj i) := hAff i
        have hmi : σNat.app (Opposite.op i) ≫ m = c'.ι.app (Opposite.op i) :=
          hm (Opposite.op i)
        have hcπ : Spec.map (c'.ι.app (Opposite.op i)) =
            Spec.map m ≫ s.app i ≫ (D.obj i).isoSpec.hom := by
          rw [← hSpec_σ (Opposite.op i), ← Spec.map_comp, hmi]
        have hmkπ : (mkScheme c').π.app i =
            Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv := rfl
        rw [hmkπ, hcπ, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · exact (HasRingHomProperty.Spec_iff (P := P)).mp <| by
        rw [hSpec_τ]
        exact MorphismProperty.RespectsIso.precomp _ _ _ (hts j'.unop).1.1
    · apply Spec.map_injective
      rw [Spec.map_comp, hSpec_σ, hSpec_τ, Category.assoc, ← Category.assoc _ _ (t.app _),
        Iso.hom_inv_id, Category.id_comp]
      exact (hts j'.unop).2
  · obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
    refine ⟨Jᵒᵖ, inferInstance, inferInstance, D.op ⋙ Scheme.Spec,
      { app j' := Spec.map (t.app j'.unop)
        naturality := fun j' k' α ↦ by
          dsimp
          have := t.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
          rw [Category.comp_id, ← Spec.map_comp, ← this] },
      { app j' := Spec.map (s.app j'.unop)
        naturality := fun j' k' α ↦ by
          dsimp
          have := s.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          rw [Category.id_comp, ← Spec.map_comp, this] },
      ?_, fun j' ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
    · let c : Cocone D := Cocone.mk _ s
      have hSpecLimit : IsLimit (Scheme.Spec.mapCone c.op) :=
        isLimitOfPreserves Scheme.Spec hs.op
      refine IsLimit.ofIsoLimit hSpecLimit (Cone.ext (Iso.refl _) ?_)
      intro j'
      dsimp [c]
      simp
    · exact (HasRingHomProperty.Spec_iff (P := P)).mpr (hts j'.unop).1
    · exact ofObjectProperty_top_right_iff.mpr (AlgebraicGeometry.isAffine_Spec _)
    · rw [← Spec.map_comp]
      exact congrArg Spec.map (hts j'.unop).2

/-- A morphism `Spec.map f` between affine schemes is pro-affine étale if and only
if `f` is ind-étale. -/
lemma proAffineEtale_Spec_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    proAffineEtale (Spec.map f) ↔ f.hom.IndEtale := by
  rw [proAffineEtale, pro_inf_isAffine_Spec_iff (P := @Etale) f, RingHom.IndEtale.iff_ind_etale]
  rfl

/-- A morphism between affine schemes is pro-affine étale if and only if the induced map
on global sections is ind-étale. -/
lemma proAffineEtale_iff_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] {f : X ⟶ Y} :
    proAffineEtale f ↔ f.appTop.hom.IndEtale := by
  have h : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  rw [← proAffineEtale_Spec_iff, h,
    MorphismProperty.cancel_left_of_respectsIso (P := proAffineEtale.{u}),
    MorphismProperty.cancel_right_of_respectsIso (P := proAffineEtale.{u})]

/-- Étale ring maps cancel from the left. -/
instance : CommRingCat.etale.{u}.HasOfPrecompProperty CommRingCat.etale.{u} where
  of_precomp {R S T} f g hf hfg := by
    rw [CommRingCat.etale_iff] at hf hfg ⊢
    rw [← HasRingHomProperty.Spec_iff (P := @Etale)] at hf hfg ⊢
    rw [Spec.map_comp] at hfg
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ _ hf hfg

/-- Cancellation for ind-étale ring maps: if `f : R →+* S` and `g ∘ f : R →+* T` are
ind-étale, then so is `g : S →+* T`. -/
lemma _root_.RingHom.IndEtale.of_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.IndEtale) (hgf : (g.comp f).IndEtale) :
    g.IndEtale := by
  haveI : (MorphismProperty.ind.{u} CommRingCat.etale.{u}).HasOfPrecompProperty
      (MorphismProperty.ind.{u} CommRingCat.etale.{u}) :=
    MorphismProperty.ind_hasOfPrecompProperty_ind CommRingCat.etale_le_isFinitelyPresentable.{u}
  rw [RingHom.IndEtale.iff_ind_etale] at hf hgf ⊢
  rw [CommRingCat.ofHom_comp] at hgf
  exact MorphismProperty.of_precomp (W := MorphismProperty.ind.{u} CommRingCat.etale.{u})
    (W' := MorphismProperty.ind.{u} CommRingCat.etale.{u})
    (CommRingCat.ofHom f) (CommRingCat.ofHom g) hf hgf

/-- The projection from a pro-affine-étale presentation to any of its stages is
pro-affine-étale. -/
lemma proAffineEtale.app_mem {J : Type u} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} {S X : Scheme.{u}} {t : D ⟶ (Functor.const J).obj S}
    {s : (Functor.const J).obj X ⟶ D} (hs : IsLimit (Cone.mk X s))
    (ht : ∀ j, (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}) (t.app j)) (j₀ : J) :
    proAffineEtale (s.app j₀) := by
  refine MorphismProperty.pro_coneπ hs j₀ fun {i} u ↦ ⟨?_, ?_⟩
  · have h1 : D.map u ≫ t.app j₀ = t.app i := by simp
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (t.app j₀)
      (ht j₀).1 (by rw [h1]; exact (ht i).1)
  · exact ofObjectProperty_top_right_iff.mpr (ofObjectProperty_top_right_iff.mp (ht i).2)

/-- A pro-affine-étale morphism into an affine scheme is weakly étale. -/
lemma proAffineEtale.weaklyEtale {X Y : Scheme.{u}} [IsAffine Y] {f : X ⟶ Y}
    (hf : proAffineEtale f) : WeaklyEtale f := by
  haveI : IsAffine X := hf.isAffine
  rw [proAffineEtale_iff_appTop] at hf
  rw [HasRingHomProperty.iff_of_isAffine (P := @WeaklyEtale) (Q := RingHom.WeaklyEtale)]
  exact hf.weaklyEtale

/-- Every pro-affine étale morphism is weakly-étale. -/
lemma proAffineEtale_le_weaklyEtale : proAffineEtale ≤ @WeaklyEtale := by
  intro X S f hf
  haveI hX : IsAffine X := hf.isAffine
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hf
  obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
  haveI : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
  haveI : Etale (t.app j₀) := (hts j₀).1.1
  haveI : WeaklyEtale (s.app j₀) :=
    (proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀).weaklyEtale
  rw [← (hts j₀).2]
  infer_instance

instance : proAffineEtale.HasOfPostcompProperty proAffineEtale where
  of_postcomp {X Y Z} f g hg hfg := by
    haveI hX : IsAffine X := hfg.isAffine
    haveI hY : IsAffine Y := hg.isAffine
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hg
    obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
    haveI : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
    have hπ : proAffineEtale (s.app j₀) :=
      proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀
    -- The composite `X ⟶ Y ⟶ D.obj j₀` is pro-affine-étale: it descends to a finite
    -- stage of the presentation of `f ≫ g` since `D.obj j₀` is locally of finite
    -- presentation over `Z`.
    have hfπ : proAffineEtale (f ≫ s.app j₀) := by
      obtain ⟨K, _, _, E, u, r, hr, hur⟩ := hfg
      have hAffE (k : K) : IsAffine (E.obj k) := ofObjectProperty_top_right_iff.mp (hur k).1.2
      haveI : ∀ {i j : K} (a : i ⟶ j), IsAffineHom (E.map a) := fun {i j} a ↦ by
        haveI := hAffE i; haveI := hAffE j; infer_instance
      haveI : ∀ k : K, CompactSpace (E.obj k) := fun k ↦ by
        haveI := hAffE k; infer_instance
      haveI : ∀ k : K, QuasiSeparatedSpace (E.obj k) := fun k ↦ by
        haveI := hAffE k; infer_instance
      haveI : Etale (t.app j₀) := (hts j₀).1.1
      have hcomm : (Cone.mk X r).π ≫ u =
          (Functor.const K).map ((f ≫ s.app j₀) ≫ t.app j₀) := by
        ext k
        dsimp
        rw [(hur k).2, Category.assoc, (hts j₀).2]
      obtain ⟨k₀, q, hq1, hq2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        E u (t.app j₀) (Cone.mk X r) hr (f ≫ s.app j₀) hcomm
      refine ⟨Over k₀, inferInstance, inferInstance, CategoryTheory.Over.forget k₀ ⋙ E,
        { app l := E.map l.hom ≫ q
          naturality {l l'} a := by
            dsimp
            rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp,
              CategoryTheory.Over.w a] },
        ((Cone.mk X r).whisker (CategoryTheory.Over.forget k₀)).π,
        (Functor.Initial.isLimitWhiskerEquiv (CategoryTheory.Over.forget k₀)
          (Cone.mk X r)).symm hr,
        fun l ↦ ⟨⟨?_, ?_⟩, ?_⟩⟩
      · -- `E.map l.hom ≫ q` is étale by cancellation along the étale map `t.app j₀`
        have h1 : (E.map l.hom ≫ q) ≫ t.app j₀ = u.app l.left := by
          rw [Category.assoc, hq2]
          simp
        exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ (t.app j₀)
          (hts j₀).1.1 (by rw [h1]; exact (hur l.left).1.1)
      · exact ofObjectProperty_top_right_iff.mpr (hAffE l.left)
      · change r.app l.left ≫ E.map l.hom ≫ q = f ≫ s.app j₀
        rw [← Category.assoc, show r.app l.left ≫ E.map l.hom = r.app k₀ from by
          simpa using (r.naturality l.hom).symm]
        exact hq1
    haveI : IsAffine (((Functor.const J).obj Y).obj j₀) := hY
    rw [proAffineEtale_iff_appTop] at hπ hfπ ⊢
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfπ
    exact RingHom.IndEtale.of_comp hπ hfπ

/-- The property `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤` pre-pro-spreads.
This is needed to show that `proAffineEtale` is stable under composition. -/
instance : MorphismProperty.PreProSpreads.{u}
    (@Etale ⊓ .ofObjectProperty (IsAffine ·) (⊤ : ObjectProperty Scheme.{u})) :=
  sorry

/- TODO: this previously followed from a (sorried, mathematically unjustified) global
instance `IsStableUnderComposition (pro P)`. The corrected statement
`MorphismProperty.IsStableUnderComposition.pro_of_le_isFinitelyPresentable` additionally
requires `P.IsStableUnderBaseChange` and `P.op ≤ isFinitelyPresentable Schemeᵒᵖ`,
which are not available for `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤`. -/
instance : proAffineEtale.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    haveI hX : IsAffine X := hf.isAffine
    haveI hY : IsAffine Y := hg.isAffine
    obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hg
    obtain ⟨j₀⟩ : Nonempty J := IsCofiltered.nonempty
    haveI : IsAffine (D.obj j₀) := ofObjectProperty_top_right_iff.mp (hts j₀).1.2
    have hπ : proAffineEtale (s.app j₀) :=
      proAffineEtale.app_mem hs (fun j ↦ (hts j).1) j₀
    have hfπ : proAffineEtale (f ≫ s.app j₀) := by
      haveI : IsAffine (((Functor.const J).obj Y).obj j₀) := hY
      rw [proAffineEtale_iff_appTop] at hπ hf ⊢
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
      exact RingHom.IndEtale.comp hf hπ
    have hcomp := MorphismProperty.pro_comp_mem_of_mem hfπ (hts j₀).1
    rwa [Category.assoc, (hts j₀).2] at hcomp

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    proAffineEtale.IsStableUnderBaseChangeAlong f := by
  rw [proAffineEtale]
  have : (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}).IsStableUnderBaseChangeAlong f := by
    constructor
    intro Z W f' g' g h ⟨h₁, h₂⟩
    refine ⟨MorphismProperty.of_isPullback h h₁, ?_⟩
    have : IsAffine Z := h₂.left
    have : IsAffineHom f' := MorphismProperty.of_isPullback h.flip ‹_›
    rw [ofObjectProperty_top_right_iff]
    exact isAffine_of_isAffineHom f'
  infer_instance

/-- `proAffineEtale.overObj S` is closed under cospan limits in `Over S`: a pullback of a
cospan whose three legs have `proAffineEtale` structural maps again has
`proAffineEtale` structural map. -/
instance {S : Scheme.{u}} :
    (proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape WalkingCospan :=
  Over.closedUnderLimitsOfShape_walkingCospan_of_baseChangeAlong (P := proAffineEtale)
    fun h₁ h₂ _ ↦ by
      have : IsAffine _ := h₁.isAffine
      have : IsAffine _ := h₂.isAffine
      infer_instance

end AlgebraicGeometry
