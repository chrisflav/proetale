/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- This is the property of morphisms of schemes that are of the form `lim Xᵢ ⟶ S`
where each `Xᵢ` is absolutely affine and étale over `X`. -/
def proAffineEtale : MorphismProperty Scheme.{u} :=
  MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)

lemma proAffineEtale.of_isAffine {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [Etale f] :
    proAffineEtale f :=
  MorphismProperty.le_pro _ _ ⟨‹_›, ⟨‹_›, trivial⟩⟩

/-- `IsAffine` is preserved under isomorphisms. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsAffine ·) where
  of_iso e h := (IsAffine.iff_of_isIso e.hom).mp h

/-- Every pro-affine étale morphism is weakly-étale. -/
lemma proAffineEtale_le_weaklyEtale : proAffineEtale ≤ @WeaklyEtale :=
  sorry

instance : proAffineEtale.RespectsIso := by
  rw [proAffineEtale, pro_eq_unop_ind_op]
  infer_instance

instance : proAffineEtale.HasOfPostcompProperty proAffineEtale :=
  sorry

/-- The property `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤` pre-pro-spreads.
This is needed to show that `proAffineEtale` is stable under composition. -/
instance : MorphismProperty.PreProSpreads.{u}
    (@Etale ⊓ .ofObjectProperty (IsAffine ·) (⊤ : ObjectProperty Scheme.{u})) :=
  sorry

instance : proAffineEtale.IsStableUnderComposition := by
  rw [proAffineEtale]
  infer_instance

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
    haveI hAff : ∀ j, IsAffine (D.obj j) := fun j ↦
      ofObjectProperty_top_right_iff.mp (hts j).1.2
    let Φ : Jᵒᵖ ⥤ CommRingCat.{u} := D.op ⋙ Scheme.Γ
    let σ : ∀ j' : Jᵒᵖ, Φ.obj j' ⟶ S := fun j' ↦
      Spec.preimage (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom)
    let τ : ∀ j' : Jᵒᵖ, R ⟶ Φ.obj j' := fun j' ↦
      Spec.preimage ((D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop)
    have hSpec_σ : ∀ j' : Jᵒᵖ,
        Spec.map (σ j') = s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom :=
      fun j' ↦ Spec.map_preimage _
    have hSpec_τ : ∀ j' : Jᵒᵖ,
        Spec.map (τ j') = (D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop :=
      fun j' ↦ Spec.map_preimage _
    let τNat : (Functor.const Jᵒᵖ).obj R ⟶ Φ :=
      { app := τ
        naturality := fun j' k' α ↦ by
          haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
          haveI : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.id_comp]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_τ k', hSpec_τ j']
          have htn : t.app k'.unop = D.map α.unop ≫ t.app j'.unop := by
            have := t.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
            exact this.symm
          rw [htn, show Φ.map α = (D.map α.unop).appTop from Scheme.Γ_map_op (D.map α.unop)]
          exact (Scheme.isoSpec_inv_naturality_assoc (D.map α.unop) (t.app j'.unop)).symm }
    let σNat : Φ ⟶ (Functor.const Jᵒᵖ).obj S :=
      { app := σ
        naturality := fun j' k' α ↦ by
          haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
          haveI : IsAffine (D.obj k'.unop) := hAff k'.unop
          dsimp
          rw [Category.comp_id]
          apply Spec.map_injective
          rw [Spec.map_comp, hSpec_σ k', hSpec_σ j']
          have hsn : s.app j'.unop = s.app k'.unop ≫ D.map α.unop := by
            have := s.naturality α.unop
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
            exact this
          rw [hsn, show Φ.map α = (D.map α.unop).appTop from Scheme.Γ_map_op (D.map α.unop),
            Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc] }
    let legSpec : (c' : Cocone Φ) → (i : J) → (Spec c'.pt ⟶ D.obj i) :=
      fun c' i ↦ Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv
    let mkScheme : Cocone Φ → Cone D := fun c' ↦
      { pt := Spec c'.pt
        π :=
          { app := legSpec c'
            naturality := fun i i' α ↦ by
              haveI : IsAffine (D.obj i) := hAff i
              haveI : IsAffine (D.obj i') := hAff i'
              dsimp only [legSpec, Functor.const_obj_obj, Functor.const_obj_map]
              rw [Category.id_comp]
              have hcnat : Φ.map α.op ≫ c'.ι.app (Opposite.op i) =
                  c'.ι.app (Opposite.op i') := by
                have := c'.ι.naturality α.op
                simp only [Functor.const_obj_obj, Functor.const_obj_map,
                  Category.comp_id] at this
                exact this
              rw [show Φ.map α.op = (D.map α).appTop from Scheme.Γ_map_op (D.map α)] at hcnat
              rw [← hcnat, Spec.map_comp, Category.assoc,
                Scheme.isoSpec_inv_naturality, ← Category.assoc] } }
    refine ⟨Jᵒᵖ, inferInstance, inferInstance, Φ, τNat, σNat, ?_, fun j' ↦ ⟨?_, ?_⟩⟩
    · refine
        { desc := fun c' ↦ Spec.preimage (hs.lift (mkScheme c'))
          fac := fun c' j' ↦ ?_
          uniq := fun c' m hm ↦ ?_ }
      · apply Spec.map_injective
        haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
        have hliftFac : hs.lift (mkScheme c') ≫ s.app j'.unop =
            Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
              (D.obj j'.unop).isoSpec.inv := hs.fac (mkScheme c') j'.unop
        rw [Spec.map_comp, Spec.map_preimage, hSpec_σ, ← Category.assoc, hliftFac,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · apply Spec.map_injective
        refine (hs.uniq (mkScheme c') (Spec.map m) ?_).trans
          (Spec.map_preimage (hs.lift (mkScheme c'))).symm
        intro i
        haveI : IsAffine (D.obj i) := hAff i
        have hmi : σNat.app (Opposite.op i) ≫ m = c'.ι.app (Opposite.op i) :=
          hm (Opposite.op i)
        have hcπ : Spec.map (c'.ι.app (Opposite.op i)) =
            Spec.map m ≫ s.app i ≫ (D.obj i).isoSpec.hom := by
          rw [← hSpec_σ (Opposite.op i), ← Spec.map_comp, hmi]
        rw [show (mkScheme c').π.app i =
            Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv from rfl, hcπ,
          Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change Q (τNat.app j').hom
      rw [← HasRingHomProperty.Spec_iff (P := P), hSpec_τ]
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
    · change P (Spec.map (t.app j'.unop))
      rw [HasRingHomProperty.Spec_iff (P := P)]
      exact (hts j'.unop).1
    · change ofObjectProperty (IsAffine ·) ⊤ (Spec.map (t.app j'.unop))
      rw [ofObjectProperty_top_right_iff]
      exact AlgebraicGeometry.isAffine_Spec _
    · change Spec.map (s.app j'.unop) ≫ Spec.map (t.app j'.unop) = Spec.map f
      rw [← Spec.map_comp]
      exact congrArg Spec.map (hts j'.unop).2

/-- A morphism `Spec.map f` between affine schemes is pro-affine étale if and only
if `f` is ind-étale. -/
lemma proAffineEtale_Spec_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    proAffineEtale (Spec.map f) ↔ f.hom.IndEtale := by
  rw [proAffineEtale, pro_inf_isAffine_Spec_iff (P := @Etale) f, RingHom.IndEtale.iff_ind_etale]
  rfl

end AlgebraicGeometry
