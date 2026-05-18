/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Topology.Comparison.Etale
import Proetale.Topology.Coherent.Affine
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Basic
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.PresheafColimit
import Proetale.Morphisms.ProAffineEtale
import Proetale.Topology.LocalProperties
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.Sites.Grothendieck
import Proetale.Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Affine pro-étale site

In this file we study the small affine pro-étale site of a scheme `S`: Its objects
are affine schemes `X` that can be written as `X = limᵢ Xᵢ` where `Xᵢ` is an
affine étale `S`-scheme.
-/

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : C ⥤ D) (R : D ⥤ C)
  {A : Type*} [Category A]

namespace MorphismProperty

variable {J : Type*} [Category* J] {C : Type*} [Category* C]
variable {P Q : MorphismProperty C} [Q.IsMultiplicative]

@[simps!]
def Over.lift' (D : J ⥤ C) {S : C} (s : D ⟶ (Functor.const J).obj S)
    (hs : ∀ j, P (s.app j)) (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f)) :
    J ⥤ P.Over Q S :=
  Over.lift (CategoryTheory.Over.lift D s) hs hD

@[simps]
def Over.iteratedLift {S : C} (D : J ⥤ P.Over Q S)
    {X : P.Over Q S}
    (s : D ⟶ (Functor.const J).obj X) (hs : ∀ j, P (s.app j).left)
    (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f).left := by cat_disch) :
    J ⥤ P.Over Q X.left where
  obj j := Over.mk _ (s.app j).left (hs j)
  map {i j} f := Over.homMk (D.map f).left
    (by simpa [-NatTrans.naturality] using congr($(s.naturality f).left)) (hD f)

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The pro-étale affine site is the full subcategory of the pro-étale site where every
object can be written as a cofiltered limit of affine étale schemes over `S`. -/
def AffineProEt (S : Scheme.{u}) : Type (u + 1) :=
  proAffineEtale.Over ⊤ S

abbrev AffineProEt.ofEtale {S : Scheme.{u}} {X : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    [Etale f] :
    S.AffineProEt :=
  .mk _ f (.of_isAffine _)

variable (S : Scheme.{u})
variable (A : Type*) [Category A]

noncomputable instance : Category S.AffineProEt :=
  inferInstanceAs <| Category <| proAffineEtale.Over ⊤ S

namespace AffineProEt

variable {S}

@[simps!]
def mk {X : Scheme.{u}} (f : X ⟶ S) (hf : proAffineEtale f) : S.AffineProEt :=
  MorphismProperty.Over.mk _ _ hf

lemma proAffineEtale_hom {X Y : S.AffineProEt} (f : X ⟶ Y) : proAffineEtale f.left :=
  MorphismProperty.of_postcomp _ _ Y.hom Y.prop <| by simpa using X.prop

-- TODO: move me
instance {X Y : S.ProEt} (f : X ⟶ Y) : WeaklyEtale f.left :=
  have : WeaklyEtale (f.left ≫ Y.hom) := by simp [X.prop]
  .of_comp _ Y.hom

/-- The inclusion of the affine pro-étale site into the pro-étale site. -/
@[simps! map]
def toProEt (S : Scheme.{u}) : S.AffineProEt ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale le_rfl

@[simp]
lemma toProEt_obj_left (X : S.AffineProEt) : ((toProEt S).obj X).left = X.left := rfl

@[simp]
lemma toProEt_obj_hom (X : S.AffineProEt) : ((toProEt S).obj X).hom = X.hom := rfl

instance : (toProEt S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale _).Full
instance : (toProEt S).Faithful :=
  inferInstanceAs <|
    (MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale le_rfl).Faithful

instance : HasPullbacks (AffineProEt S) :=
  sorry

/-- The affine pro-étale site embeds densely in the pro-étale site. The key ingredient
of the proof is the commutative algebra lemma `RingHom.WeaklyEtale.exists_indEtale_comp`. -/
instance isCoverDense_toProEt : (toProEt S).IsCoverDense (ProEt.topology S) := by
  wlog hS : ∃ R, S = Spec R generalizing S
  · let X (i : S.affineCover.I₀) : S.AffineProEt := .ofEtale (S.affineCover.f i)
    let f (i : S.affineCover.I₀) : (toProEt S).obj (X i) ⟶ .mk (𝟙 S) :=
      Over.homMk (S.affineCover.f i)
    refine .of_coversTop _ _ (fun i : S.affineCover.I₀ ↦ X i) ?_ ?_
    · dsimp
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (.mk (𝟙 S))]
      · refine GrothendieckTopology.superset_covering
          (S := Sieve.ofArrows _ f) _ ?_ ?_
        · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
          intro i
          -- TODO: make this a separate lemma
          rw [Sieve.mem_ofObjects_iff]
          use i
          constructor
          exact 𝟙 _
        · apply Precoverage.generate_mem_toGrothendieck
          simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Functor.comp_obj,
            ProEt.forget_obj, Over.forget_obj, ProEt.mk_left, Presieve.map_ofArrows,
            toProEt_obj_left, Functor.comp_map, ProEt.forget_map, Over.forget_map]
          apply zariskiPrecoverage_le_propQCPrecoverage
          exact S.affineCover.mem₀
      · apply MorphismProperty.Over.mkIdTerminal
    · intro i
      have h1 : inverseImage (@WeaklyEtale)
          (MorphismProperty.Over.forget @WeaklyEtale ⊤ S ⋙ CategoryTheory.Over.forget S) = ⊤ := by
        rw [eq_top_iff]
        intro X Y f _
        simp only [inverseImage_iff, Functor.comp_obj, Comma.forget_obj, Over.forget_obj,
          Functor.comp_map, Comma.forget_map, Over.forget_map]
        infer_instance
      have h2 : proAffineEtale.inverseImage
          (MorphismProperty.Over.forget proAffineEtale ⊤ S ⋙ CategoryTheory.Over.forget S) = ⊤ := by
        rw [eq_top_iff]
        intro X Y f _
        exact proAffineEtale_hom _
      let eL : Over (X i) ≌ (X i).left.AffineProEt :=
        (CategoryTheory.MorphismProperty.Comma.equivOfEqTop _ _ h2).symm.trans
          (MorphismProperty.Over.iteratedSliceEquiv _)
      let eR : (X i).left.ProEt ≌ Over ((toProEt S).obj (X i)) :=
        (MorphismProperty.Over.iteratedSliceEquiv <| (toProEt S).obj (X i)).symm.trans
            (CategoryTheory.MorphismProperty.Comma.equivOfEqTop _ _ h1)
      let e : Over.post (X := X i) (toProEt S) ≅
          (eL.functor ⋙ (toProEt <| (X i).left)) ⋙ eR.functor := by
        refine NatIso.ofComponents ?_ ?_
        · intro A
          refine Over.isoMk ?_ ?_
          · exact MorphismProperty.Over.isoMk (Iso.refl _) (by simp [eL, eR])
          · cat_disch
        · cat_disch
      rw [CategoryTheory.Functor.IsCoverDense.iff_of_natIso e]
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_isCoverDense]
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_isEquivalence]
      have heq : eR.functor.inducedTopology
          ((ProEt.topology S).over ((toProEt S).obj ((fun i ↦ X i) i))) =
            ProEt.topology _ := by
        rw [ProEt.topology_eq_inducedTopology, ProEt.topology_eq_inducedTopology]
        dsimp
        ext U R
        simp only [Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff,
          Sieve.overEquiv, Equiv.coe_fn_mk, ProEt.forget_obj, ← Sieve.functorPushforward_comp]
        rfl
      rw [heq]
      exact this ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  constructor
  intro U
  wlog hU : ∃ (S : CommRingCat.{u}) (g : Spec S ⟶ Spec R) (_ : WeaklyEtale g),
      U = .mk g generalizing U
  · let X (i : U.left.affineCover.I₀) : (Spec R).ProEt := .mk (U.left.affineCover.f i ≫ U.hom)
    let f (i : U.left.affineCover.I₀) : X i ⟶ U := Over.homMk (U.left.affineCover.f i) rfl
    have H (i) := this (X i) ⟨_, U.left.affineCover.f i ≫ U.hom, _, rfl⟩
    refine GrothendieckTopology.transitive_of_presieve (.ofArrows _ f) ?_ _ ?_
    · apply Precoverage.generate_mem_toGrothendieck
      apply zariskiPrecoverage_le_propQCPrecoverage
      simp only [Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, Presieve.map_ofArrows,
        Functor.comp_map, ProEt.forget_map, Over.forget_map]
      exact U.left.affineCover.mem₀
    · intro Y g ⟨i⟩
      refine GrothendieckTopology.superset_covering _ ?_ (H i)
      exact Sieve.le_pullback_coverByImage (toProEt (Spec R)) (f i)
  obtain ⟨S, g, hg, rfl⟩ := hU
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  simp only [WeaklyEtale.Spec_iff] at hg
  obtain ⟨T, _, g, h₁, h₂, h₃⟩ := hg.exists_indEtale_comp
  let U : AffineProEt (Spec R) := mk (Spec.map (CommRingCat.ofHom g) ≫ Spec.map φ) <| by
    rwa [← Spec.map_comp, proAffineEtale_Spec_iff]
  let g' : (toProEt _).obj U ⟶ ProEt.mk (Spec.map φ) :=
    Over.homMk (Spec.map <| CommRingCat.ofHom g) rfl
  have : IsAffine U.left := by dsimp [U]; infer_instance
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective] at h₂
  have : Surjective (Over.Hom.left (Comma.Hom.hom g')) := by
    dsimp [g']
    constructor
    exact h₂.right
  refine GrothendieckTopology.superset_covering (S := .generate <| .singleton g') _ ?_ ?_
  · rw [Sieve.generate_le_iff]
    intro _ _ ⟨⟩
    apply Presieve.in_coverByImage
  · apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.precoverage]
    simp only [Precoverage.mem_comap_iff, Functor.comp_obj, ProEt.forget_obj, Over.forget_obj,
      ProEt.mk_left, Presieve.map_singleton, toProEt_obj_left, Functor.comp_map, ProEt.forget_map,
      Over.forget_map]
    apply Hom.singleton_mem_propQCPrecoverage
    change WeaklyEtale (Spec.map (CommRingCat.ofHom g))
    rw [WeaklyEtale.Spec_iff]
    exact h₁.weaklyEtale

instance : (toProEt S).LocallyCoverDense (ProEt.zariskiTopology S) :=
  sorry

variable (S)

noncomputable def topology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.topology S)

noncomputable def zariskiTopology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.zariskiTopology S)

instance : (toProEt S).IsContinuous (topology S) (ProEt.topology S) := by
  dsimp [topology]
  infer_instance

instance : (toProEt S).IsDenseSubsite (topology S) (ProEt.topology S) where
  functorPushforward_mem_iff := by rfl

/-- Restriction along inclusion of the affine pro-étale site into the pro-étale site induces an
equivalence of categories of sheaves of `Ab.{u + 1}`, or more generally any category
having large enough limits. -/
instance isEquivalence_sheafPushforwardContinuous_toProEt {A : Type*} [Category* A]
    [HasLimitsOfSize.{u, u + 1} A] :
    ((toProEt.{u} S).sheafPushforwardContinuous A
      (topology S) (ProEt.topology S)).IsEquivalence :=
  inferInstance

/-- The restriction of sheafs on the pro-étale site to sheaf on the affine pro-étale site. -/
noncomputable
def sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (AffineProEt.topology S) A :=
  (toProEt S).sheafPushforwardContinuous _ _ _

/-- To show a presheaf of types is a sheaf on the affine pro-étale site, it suffices to show
it is a Zariksi sheaf and satifies the sheaf condition for single surjective morphisms. -/
lemma isSheaf {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : Presheaf.IsSheaf (zariskiTopology S) F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.hom.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F :=
  sorry

end AffineProEt

noncomputable def ProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.ProEt ⥤ S.ProEt :=
  MorphismProperty.Over.pullback _ _ f

noncomputable def AffineProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) [IsAffineHom f] :
    T.AffineProEt ⥤ S.AffineProEt :=
  MorphismProperty.Over.pullback _ _ f

/-- The inclusion of the affine étale site into the affine pro-étale site. -/
noncomputable def AffineEtale.toAffineProEt (S : Scheme.{u}) :
    S.AffineEtale ⥤ S.AffineProEt :=
  MorphismProperty.CostructuredArrow.pre Scheme.Spec (𝟭 _) S
    (by
      intro X Y f ⟨hf, hf'⟩
      rw [ofObjectProperty_top_right_iff, Functor.comp_id, essImage_Spec] at hf'
      exact .of_isAffine f)
    (by simp)

/-- The topology on the affine pro-étale site is generated by limits
of `1`-hypercovers in the affine étale site. -/
instance :
    (GrothendieckTopology.oneHypercoverRelativelyRepresentable.{u}
      (AffineEtale.toAffineProEt S) (Type u)
      (AffineEtale.topology S) (AffineProEt.topology S)).IsGenerating :=
  sorry

end AlgebraicGeometry.Scheme
