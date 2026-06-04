/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Finite
import Proetale.Mathlib.CategoryTheory.Sites.MorphismProperty
import Proetale.Topology.Comparison.Etale
import Proetale.Topology.Coherent.Affine
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Basic
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.PresheafColimit
import Proetale.Pro.Generating
import Proetale.Morphisms.ProAffineEtale
import Proetale.Topology.LocalProperties
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.Sites.Grothendieck
import Proetale.Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Proetale.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Proetale.Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Filtered.Connected

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

instance {X Y : S.AffineProEt} (f : X ⟶ Y) : WeaklyEtale f.left :=
  proAffineEtale_le_weaklyEtale _ (proAffineEtale_hom f)

instance (X : S.AffineProEt) : IsAffine X.left :=
  X.prop.isAffine

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

noncomputable
def precoverage : Precoverage (AffineProEt S) :=
  Precoverage.comap (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) Scheme.proetalePrecoverage

instance : PreservesLimitsOfShape WalkingCospan (toProEt S) :=
  sorry

variable (S) in
/-- The Zariski precoverage on the affine pro-étale site. -/
noncomputable def zariskiPrecoverage : Precoverage (AffineProEt S) :=
  Precoverage.comap (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) Scheme.zariskiPrecoverage
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderComposition,
    Precoverage.IsStableUnderBaseChange

instance : (toProEt S).LocallyCoverDense (ProEt.zariskiTopology S) :=
  sorry

variable (S)

noncomputable def topology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.topology S)

noncomputable def zariskiTopology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.zariskiTopology S)

lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S := by
  intro X R hR
  exact ProEt.zariskiTopology_le_topology _ _ hR

lemma zariskiTopology_eq_toGrothendieck_zariskiPrecoverage :
    zariskiTopology S = (zariskiPrecoverage S).toGrothendieck := by
  sorry

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
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F :=
  sorry

lemma _root_.AlgebraicGeometry.Scheme.OpenCover.exists_finite_restrictIndex_mem {X : Scheme.{u}}
    [CompactSpace X] (𝒰 : X.OpenCover) :
    ∃ (ι : Type u) (_ : Finite ι) (s : ι → 𝒰.I₀),
      (𝒰.restrictIndex s).presieve₀ ∈ Scheme.zariskiPrecoverage X :=
  ⟨𝒰.finiteSubcover.I₀, inferInstance, _, 𝒰.finiteSubcover.mem₀⟩

noncomputable
def minimalPrecoverage : Precoverage (AffineProEt S) :=
  -- Finite Zariski coverings
  (.finite _ ⊓ zariskiPrecoverage S) ⊔
  -- Singleton coverings by surjective morphisms
  (.singleton _ ⊓ MorphismProperty.precoverage (fun _ _ f ↦ Surjective f.left))

lemma minimalPrecoverage_le_finite : minimalPrecoverage S ≤ .finite _ := by
  rw [minimalPrecoverage, sup_le_iff]
  exact ⟨inf_le_left, le_trans inf_le_left (Precoverage.singleton_le_finite _)⟩

lemma _root_.CategoryTheory.Presieve.IsSheafFor.of_le {C : Type*} [Category* C]
    {F : Cᵒᵖ ⥤ Type*}
    {X : C} {R S : Presieve X} (hle : R ≤ S)
    (h₁ : Presieve.IsSheafFor F R)
    (h₂ : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f →
      Presieve.IsSeparatedFor F (Sieve.pullback f (.generate R)).arrows) :
    Presieve.IsSheafFor F S := by
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨fun x t₁ t₂ ht₁ ht₂ ↦ ?_, ?_⟩
  · exact h₁.isSeparatedFor _ _ _ (Presieve.isAmalgamation_restrict hle x t₁ ht₁)
      (Presieve.isAmalgamation_restrict hle x t₂ ht₂)
  · intro x hx
    use h₁.amalgamate _ (hx.restrict hle)
    intro W j hj
    apply (h₂ hj).ext
    intro Y f ⟨U, v, v', hv', heq⟩
    rw [← comp_apply, ← F.map_comp, ← op_comp, ← heq, op_comp, F.map_comp, comp_apply,
      h₁.valid_glue _ _ hv', Presieve.FamilyOfElements.restrict,
      hx _ _ (hle _ _ hv') hj heq]

lemma generates_minimalPrecoverage :
      (minimalPrecoverage S).Generates (topology S) where
  le_toPrecoverage := by
    -- TODO: clean up these proofs when the induced topology is refactored
    rw [minimalPrecoverage, sup_le_iff]
    refine ⟨?_, ?_⟩
    · refine le_trans inf_le_right ?_
      intro X R hR
      simp only [topology, GrothendieckTopology.mem_toPrecoverage_iff,
        Functor.mem_inducedTopology_sieves_iff]
      rw [ProEt.topology, ← Sieve.generate_map_eq_functorPushforward]
      refine Precoverage.generate_mem_toGrothendieck ?_
      simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Functor.comp_obj, ProEt.forget_obj,
        Over.forget_obj, toProEt_obj_left, Presieve.map_comp]
      simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Functor.comp_obj, ProEt.forget_obj,
        Over.forget_obj, toProEt_obj_left, Presieve.map_comp] at hR
      exact zariskiPrecoverage_le_propQCPrecoverage _ hR
    · rintro X R ⟨⟨Y, f, rfl⟩, hf⟩
      simp only [MorphismProperty.singleton_mem_precoverage_iff] at hf
      simp only [topology, ProEt.topology, GrothendieckTopology.mem_toPrecoverage_iff,
        Functor.mem_inducedTopology_sieves_iff]
      rw [← Sieve.generate_map_eq_functorPushforward]
      refine Precoverage.generate_mem_toGrothendieck ?_
      simp only [ProEt.precoverage, Presieve.map_singleton, toProEt_map, Precoverage.mem_comap_iff,
        Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, toProEt_obj_left, Functor.comp_map,
        ProEt.forget_map, Comma.Hom.hom_mk, Over.forget_map]
      exact f.left.singleton_mem_propQCPrecoverage inferInstance
  isSheaf_of_forall_max F hF := by
    rw [← isSheaf_iff_isSheaf_of_type]
    refine isSheaf _ ?_ ?_
    · rw [isSheaf_iff_isSheaf_of_type]
      intro X R hR
      rw [zariskiTopology_eq_toGrothendieck_zariskiPrecoverage] at hR
      rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hR
      simp_rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
      obtain ⟨_, ⟨𝒰, _, rfl⟩, hle⟩ := hR
      obtain ⟨ι, hι, s, hs⟩ := Scheme.OpenCover.exists_finite_restrictIndex_mem (X := X.left)
        (𝒰.map _ le_rfl)
      let 𝒱 : (zariskiPrecoverage S).ZeroHypercover X :=
        ⟨𝒰.restrictIndex s, by
          simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Functor.comp_obj,
            ProEt.forget_obj, Over.forget_obj, toProEt_obj_left, Presieve.map_ofArrows,
            PreZeroHypercover.restrictIndex_I₀, PreZeroHypercover.restrictIndex_X,
            Function.comp_apply, PreZeroHypercover.restrictIndex_f, Functor.comp_map, toProEt_map,
            ProEt.forget_map, Comma.Hom.hom_mk, Over.forget_map]
          exact hs⟩
      have : Finite 𝒱.I₀ := hι
      refine Presieve.IsSheafFor.of_le (R := 𝒱.presieve₀) (le_trans (by simp [𝒱]) hle) ?_ ?_
      · apply hF
        refine .inl ⟨?_, 𝒱.mem₀⟩
        simp [Set.finite_range]
      · intro Y f hf
        rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
        rw [← 𝒱.presieve₀_pullback₁]
        apply (hF _ _).isSeparatedFor
        refine .inl ⟨?_, (𝒱.pullback₂ _).mem₀⟩
        simp [Set.finite_range]
    · intro U V f hf
      apply hF
      exact .inr ⟨by simp, by simpa⟩

end AffineProEt

noncomputable def ProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.ProEt ⥤ S.ProEt :=
  MorphismProperty.Over.pullback _ _ f

noncomputable def AffineProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) [IsAffineHom f] :
    T.AffineProEt ⥤ S.AffineProEt :=
  MorphismProperty.Over.pullback _ _ f

/-- The inclusion of the affine étale site into the affine pro-étale site. -/
@[simps! obj_left map_left obj_hom]
noncomputable def AffineEtale.toAffineProEt (S : Scheme.{u}) :
    S.AffineEtale ⥤ S.AffineProEt :=
  MorphismProperty.CostructuredArrow.pre Scheme.Spec (𝟭 _) S
    (by
      intro X Y f ⟨hf, hf'⟩
      rw [ofObjectProperty_top_right_iff, Functor.comp_id, essImage_Spec] at hf'
      exact .of_isAffine f)
    (by simp)

namespace AffineProEt

instance : ReflectsCofilteredLimitsOfSize.{u, u} (CategoryTheory.Over.forget S) where
  reflects_cofiltered_limits J _ _ := by
    have : IsConnected J := IsCofiltered.isConnected _
    infer_instance

instance : PreservesCofilteredLimitsOfSize.{u, u} (CategoryTheory.Over.forget S) where
  preserves_cofiltered_limits J _ _ := by
    have : IsConnected J := IsCofiltered.isConnected _
    infer_instance

-- TODO: Consider if we should make this the definition of `AffineProEt`
lemma exists_relativeLimitPresentation (X : S.AffineProEt) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J),
      Nonempty (RelativeLimitPresentation J (AffineEtale.toAffineProEt S) X) := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := X.prop
  have (j : J) : IsAffine (D.obj j) := (hts j).left.right.left
  have (j : J) : Etale (t.app j) := (hts j).left.left
  refine ⟨J, inferInstance, inferInstance, ⟨⟨?_, ?_, ?_⟩⟩⟩
  · refine
      { obj j := AffineEtale.mk ((Scheme.isoSpec _).inv ≫ t.app j)
        map {i j} u := by
          refine MorphismProperty.CostructuredArrow.homMk (.op (D.map u).appTop) trivial ?_
          have : D.map u ≫ t.app j = t.app i := by simp
          simp only [Functor.const_obj_obj, AffineEtale.mk_left, Spec_obj, Spec_map,
            Quiver.Hom.unop_op, AffineEtale.mk_hom]
          rw [← this, Scheme.isoSpec_inv_naturality_assoc] }
  · refine { app := ?_, naturality := ?_ }
    · intro j
      dsimp
      dsimp at s
      refine MorphismProperty.Over.homMk (s.app j ≫ (Scheme.isoSpec _).hom) ?_ trivial
      cat_disch
    · intro i j u
      dsimp [Scheme.AffineProEt]
      ext
      simp [Scheme.isoSpec_hom_naturality, ← s.naturality_assoc]
  · refine isLimitOfReflects (toProEt S ⋙ ProEt.forget _ ⋙ Over.forget _) ?_
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ hs
    · refine NatIso.ofComponents (fun j ↦ Scheme.isoSpec _) ?_
      simp [Scheme.isoSpec_hom_naturality]
    · refine Cone.ext (Iso.refl _) (by cat_disch)

instance : PreservesLimitsOfShape WalkingCospan (AffineEtale.toAffineProEt S) :=
  sorry

noncomputable
abbrev toScheme : AffineProEt S ⥤ Scheme.{u} :=
  toProEt S ⋙ ProEt.forget _ ⋙ Over.forget _

instance : PreservesCofilteredLimitsOfSize.{u, u} (toProEt S) :=
  sorry

instance : PreservesCofilteredLimitsOfSize.{u, u} (ProEt.forget S) :=
  sorry

lemma singleton_inf_le_relativelyPresentable :
    (Precoverage.singleton S.AffineProEt ⊓
      MorphismProperty.precoverage fun _ _ f ↦ Surjective f.left) ≤
      Precoverage.relativelyPresentable (AffineEtale.toAffineProEt S) (AffineEtale.topology S) :=
  sorry

/-- The coverings in the minimal precoverage on the affine pro-étale site can be written
as cofiltered limits of coverings in the affine étale site. -/
lemma minimalPrecoverage_le_relativelyPresentable :
    AffineProEt.minimalPrecoverage S ≤
      Precoverage.relativelyPresentable.{u}
        (AffineEtale.toAffineProEt S) (AffineEtale.topology S) := by
  rw [AffineProEt.minimalPrecoverage, sup_le_iff]
  refine ⟨?_, ?_⟩
  · intro X R hR
    let 𝒰 := Precoverage.ZeroHypercover.mk R.preZeroHypercover (by simpa)
    obtain ⟨J, _, _, ⟨pres⟩⟩ := X.exists_relativeLimitPresentation
    let 𝒰' : X.left.OpenCover :=
      𝒰.map (AffineProEt.toProEt _ ⋙ ProEt.forget _ ⋙ Over.forget _) inf_le_right
    have : ∀ (i : 𝒰'.I₀), IsAffine (𝒰'.X i) := by
      dsimp [𝒰']
      infer_instance
    let F' : AffineProEt S ⥤ Scheme.{u} := toProEt _ ⋙ ProEt.forget _ ⋙ Over.forget _
    let F : S.AffineEtale ⥤ Scheme.{u} := AffineEtale.Spec _ ⋙ Etale.forget _ ⋙ Over.forget _
    have : ∀ (i : J), IsAffine ((pres.diag ⋙ F).obj i) := by
      dsimp [F, Etale.forget]
      infer_instance
    let x := (toScheme S).mapCone pres.cone
    have : Finite 𝒰'.I₀ := hR.left
    obtain ⟨i, A, v, hv, g, hg⟩ := 𝒰'.exists_of_isCofiltered_of_finite (pres.diag ⋙ F) x
      (isLimitOfPreserves _ pres.isLimit)
    have _ (a) : IsOpenImmersion (v a) := hv.right ⟨a⟩
    -- TODO: make this an instance
    have : Etale (pres.diag.obj i).hom := (pres.diag.obj i).prop
    let V (a : 𝒰.I₀) : S.AffineEtale :=
      AffineEtale.mk (v a ≫ (pres.diag.obj i).hom)
    let v' (a : 𝒰.I₀) : V a ⟶ pres.diag.obj i :=
      CostructuredArrow.homMk (Spec.preimage (v a)).op trivial (by simp [V])
    let g' (a : 𝒰.I₀) : 𝒰.X a ⟶ (AffineEtale.toAffineProEt S).obj (V a) := by
      refine MorphismProperty.Over.homMk (g a) ?_ trivial
      -- TODO: add API for MorphismProperty.CostructuredArrow
      have h1 := CostructuredArrow.w (𝒰.f a).toCommaMorphism
      dsimp at h1
      have h2 := CostructuredArrow.w (pres.π.app i).toCommaMorphism
      dsimp at h2
      simp [V, (hg a).w_assoc, x, 𝒰', h2, h1]
    let 𝒱 : Scheme.OpenCover (Spec (pres.diag.obj _).left.unop) := ⟨⟨_, _, v⟩, hv⟩
    let covpres : 𝒰.RelativeLimitPresentation (AffineEtale.toAffineProEt S) (Over i) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact pres.precomp (Over.forget i)
      · intro a
        refine pres.restrict (v' a) _ (g' a) (𝒰.f a) ?_
        refine IsPullback.of_map_of_faithful F' ?_
        simpa [F', v'] using hg a
      · intro a
        apply RelativeLimitPresentation.restrictHom
      · simp
    refine ⟨Over i, inferInstance, inferInstance, covpres, ?_⟩
    intro a
    apply AffineEtale.zariskiTopology_le_topology
    let iso : (covpres.preZeroHypercover a).map (AffineEtale.toScheme S) ≅
        (𝒱.pullback₁ (Spec.map (pres.diag.map a.hom).left.unop)).toPreZeroHypercover := by
      refine PreZeroHypercover.isoMk (.refl _) ?_ ?_
      · intro k
        dsimp [Etale.forget, covpres, 𝒱]
        refine Scheme.Spec.mapIso ?_ ≪≫
            PreservesPullback.iso Scheme.Spec (pres.diag.map a.hom).left (v' k).left ≪≫ ?_
        · exact PreservesPullback.iso
            (MorphismProperty.CostructuredArrow.forget _ _ _ _ ⋙
              CategoryTheory.CostructuredArrow.proj _ _) _ _
        · refine pullback.congrHom rfl ?_
          simp only [Spec_obj, MorphismProperty.CostructuredArrow.homMk_left, Spec_map,
            Quiver.Hom.unop_op, Spec.map_preimage, v']
          rfl
      · intro k
        -- TODO: Improve this by defining a `AffineEtale.toRing`
        simp only [Functor.comp_obj, Over.forget_obj, PreZeroHypercover.map_X,
          PreZeroHypercover.RelativeLimitPresentation.preZeroHypercover_X,
          Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.map_I₀,
          PreZeroHypercover.RelativeLimitPresentation.preZeroHypercover_I₀,
          PreZeroHypercover.pullback₁_I₀, PreZeroHypercover.pullback₁_X, Spec_obj, Spec_map, id_eq,
          Iso.trans_hom, Functor.mapIso_hom, PreservesPullback.iso_hom, pullback.congrHom_hom,
          PreZeroHypercover.pullback₁_f, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
          PullbackCone.mk_π_app, Category.comp_id, PreZeroHypercover.map_f,
          PreZeroHypercover.RelativeLimitPresentation.preZeroHypercover_f, Functor.comp_map,
          Etale.forget_map, Over.forget_map, AffineEtale.Spec_map_left, 𝒱]
        simp only [← Scheme.Spec_map]
        rw [pullbackComparison_comp_fst]
        simp only [Spec_map, ← Spec.map_comp, ← unop_comp]
        congr 2
        apply pullbackComparison_comp_fst
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀]
    refine Precoverage.generate_mem_toGrothendieck ?_
    simp only [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
    apply PreZeroHypercover.mem_of_iso iso.symm
    exact (𝒱.pullback₁ (Spec.map (pres.diag.map a.hom).left.unop)).mem₀
  · apply singleton_inf_le_relativelyPresentable

end AffineProEt

end AlgebraicGeometry.Scheme
