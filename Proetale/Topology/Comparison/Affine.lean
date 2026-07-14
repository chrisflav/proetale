/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Finite
import Proetale.Mathlib.CategoryTheory.Sites.Pullback
import Proetale.Mathlib.CategoryTheory.Sites.Sheafification
import Proetale.Mathlib.CategoryTheory.Sites.MorphismProperty
import Proetale.Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Proetale.Topology.Coherent.Affine
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Basic
import Proetale.Mathlib.CategoryTheory.Comma.ArrowRefinement
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.PresheafColimit
import Proetale.Pro.Generating
import Proetale.Morphisms.ProAffineEtale
import Proetale.Topology.LocalProperties
import Proetale.Algebra.WeaklyEtaleIndEtale
import Proetale.Mathlib.CategoryTheory.Sites.Grothendieck
import Proetale.Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Proetale.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Proetale.Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Proetale.Mathlib.AlgebraicGeometry.Sites.AffineRefinement
import Proetale.Topology.Proetale.Sheafification
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.AlgebraicGeometry.Sites.Small
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

/-- A `proAffineEtale` morphism between affine schemes induces an ind-étale ring map
on global sections. -/
lemma indEtale_appTop_of_proAffineEtale {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {f : X ⟶ Y} (hf : proAffineEtale f) : f.appTop.hom.IndEtale := by
  rw [← proAffineEtale_Spec_iff]
  have heq : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  rw [heq, proAffineEtale.cancel_left_of_respectsIso,
    proAffineEtale.cancel_right_of_respectsIso]
  exact hf

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

/-- The affine pro-étale site has pullbacks, computed as in `Over S`. -/
instance : HasPullbacks (AffineProEt S) := by
  -- `allowSynthFailures` is needed because the closure instance is registered on
  -- `proAffineEtale.overObj S`, but the goal here is phrased in terms of `commaObj`.
  apply (config := { allowSynthFailures := true })
    MorphismProperty.Comma.hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (Over S))
  · exact inferInstanceAs ((proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape _)

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

/-- The forgetful functor from the affine pro-étale site to `Over S` creates pullbacks,
since `proAffineEtale` structure maps are closed under cospan limits in `Over S`. -/
noncomputable instance : CreatesLimitsOfShape WalkingCospan
    (MorphismProperty.Over.forget proAffineEtale ⊤ S) := by
  -- `allowSynthFailures` is needed because the closure instance is registered on
  -- `proAffineEtale.overObj S`, but the goal here is phrased in terms of `commaObj`.
  apply (config := { allowSynthFailures := true })
    MorphismProperty.Comma.forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (Over S))
  · exact inferInstanceAs ((proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape _)

instance : PreservesLimitsOfShape WalkingCospan (toProEt S) :=
  have : PreservesLimitsOfShape WalkingCospan (toProEt S ⋙ ProEt.forget S) :=
    inferInstanceAs <| PreservesLimitsOfShape WalkingCospan
      (MorphismProperty.Over.forget proAffineEtale ⊤ S)
  preservesLimitsOfShape_of_reflects_of_preserves (toProEt S) (ProEt.forget S)

variable (S) in
/-- The Zariski precoverage on the affine pro-étale site. -/
noncomputable def zariskiPrecoverage : Precoverage (AffineProEt S) :=
  Precoverage.comap (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S) Scheme.zariskiPrecoverage
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderComposition,
    Precoverage.IsStableUnderBaseChange

/-- If a sieve on `(toProEt S).obj X` is a covering sieve for the Zariski topology on the
pro-étale site, it contains, for every point `x` of `X`, a basic open immersion of `X`
whose image contains `x` and which lies in the affine pro-étale site. -/
lemma exists_basicOpen_mem_of_mem_zariskiTopology {X : S.AffineProEt}
    {T : Sieve ((toProEt S).obj X)}
    (hT : T ∈ ProEt.zariskiTopology S ((toProEt S).obj X)) :
    ∃ (Z : X.left → S.AffineProEt) (ι : ∀ x, Z x ⟶ X),
      (∀ x, IsOpenImmersion (ι x).left) ∧ (∀ x, x ∈ Set.range (ι x).left.base) ∧
      (∀ x, T ((toProEt S).map (ι x))) := by
  have hTP : T.functorPushforward (MorphismProperty.Over.forget @WeaklyEtale ⊤ S) ∈
      S.overGrothendieckTopology @IsOpenImmersion X.toComma :=
    hT
  obtain ⟨𝒰, _, hle⟩ :=
    (Scheme.mem_overGrothendieckTopology (S := S) (P := @IsOpenImmersion)
      X.toComma _).mp hTP
  have hcov : ⋃ j, Set.range (𝒰.f j).base = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨j, y, hy⟩ := Scheme.Cover.exists_eq 𝒰 x
    exact Set.mem_iUnion.mpr ⟨j, y, hy⟩
  obtain ⟨idx, g, e, hmem, he⟩ :=
    exists_basicOpen_lift_of_isAffine_cover 𝒰.f hcov
  let Z : X.left → S.AffineProEt := fun x ↦
    AffineProEt.mk ((X.left.basicOpen (g x)).ι ≫ X.hom)
      (proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) X.prop)
  let ι' : ∀ x, Z x ⟶ X := fun x ↦
    MorphismProperty.Over.homMk (X.left.basicOpen (g x)).ι
  -- For each `x : X.left` the basic open `D(g x)` factors through some `Z'` in the
  -- pushforward sieve, hence `(ι' x)` itself lies in `T`.
  have hT_map : ∀ x : X.left, T ((toProEt S).map (ι' x)) := by
    intro x
    obtain ⟨Z', h, k, hTh, hcomp⟩ :=
      hle ((𝒰.X (idx x)).asOver S) ((𝒰.f (idx x)).asOver S) ⟨idx x⟩
    have hk_over : k.left ≫ h.left = 𝒰.f (idx x) := by
      simpa using (congr_arg Over.Hom.left hcomp).symm
    have hZ' : Z'.hom = h.left ≫ X.hom := by
      simpa using h.toCommaMorphism.w.symm
    have h_assoc : (e x ≫ k.left) ≫ h.left = (X.left.basicOpen (g x)).ι := by
      rw [Category.assoc, hk_over, he]
    have heq : (e x ≫ k.left) ≫ Z'.hom = (Z x).hom := by
      rw [hZ', ← Category.assoc, h_assoc]
      rfl
    let f_x : (toProEt S).obj (Z x) ⟶ Z' :=
      MorphismProperty.Over.homMk (e x ≫ k.left) heq
    have : f_x ≫ h = (toProEt S).map (ι' x) :=
      MorphismProperty.Over.Hom.ext h_assoc
    rw [← this]
    exact T.downward_closed hTh f_x
  exact ⟨Z, ι', fun x ↦ inferInstanceAs (IsOpenImmersion (X.left.basicOpen (g x)).ι),
    fun x ↦ ⟨⟨x, hmem x⟩, rfl⟩, hT_map⟩

instance : (toProEt S).LocallyCoverDense (ProEt.zariskiTopology S) := by
  refine ⟨fun {X} T ↦ ?_⟩
  obtain ⟨Z, ι', hoi, hrange, hT_map⟩ :=
    exists_basicOpen_mem_of_mem_zariskiTopology T.property
  -- Reduce to producing, pointwise, an element of the generating Zariski precoverage.
  simp only [ProEt.zariskiTopology,
    Scheme.smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology]
  apply (Scheme.mem_toGrothendieck_smallPretopology _ _).mpr
  intro x
  obtain ⟨y, hy⟩ := hrange x
  refine ⟨(toProEt S).obj (Z x), (toProEt S).map (ι' x), y, ?_, hoi x, hy⟩
  exact ⟨Z x, ι' x, 𝟙 _, hT_map x, (Category.id_comp _).symm⟩

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
  refine le_antisymm (fun X T hT ↦ ?_) ?_
  · -- A Zariski covering sieve contains a pointwise family of basic open immersions,
    -- which is a covering in the Zariski precoverage.
    obtain ⟨Z, ι, hoi, hrange, hTmem⟩ := exists_basicOpen_mem_of_mem_zariskiTopology hT
    have hT' : ∀ x, T (ι x) := fun x ↦ by
      have h := hTmem x
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at h
    refine GrothendieckTopology.superset_covering _
      (S := Sieve.generate (Presieve.ofArrows Z ι)) ?_ ?_
    · rw [Sieve.generate_le_iff]
      rintro - - ⟨x⟩
      exact hT' x
    · refine Precoverage.generate_mem_toGrothendieck ?_
      simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
        Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, toProEt_obj_left, Functor.comp_map,
        ProEt.forget_map, Over.forget_map, toProEt_map,
        Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨x, hrange x⟩, hoi⟩
  · rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    rw [GrothendieckTopology.mem_toPrecoverage_iff]
    simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, toProEt_obj_left, Functor.comp_map,
      ProEt.forget_map, Over.forget_map, toProEt_map,
      Scheme.ofArrows_mem_precoverage_iff] at hR
    obtain ⟨hsurj, hoi⟩ := hR
    change (Sieve.generate _).functorPushforward (toProEt S) ∈ ProEt.zariskiTopology S _
    simp only [ProEt.zariskiTopology,
      Scheme.smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology]
    apply (Scheme.mem_toGrothendieck_smallPretopology _ _).mpr
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(toProEt S).obj (Y i), (toProEt S).map (f i), y, ?_, hoi i, hy⟩
    exact ⟨Y i, f i, 𝟙 _, ⟨Y i, 𝟙 _, f i, ⟨i⟩, Category.id_comp _⟩,
      (Category.id_comp _).symm⟩

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

lemma _root_.CategoryTheory.Presieve.IsSeparatedFor.of_le {C : Type*} [Category* C]
    {F : Cᵒᵖ ⥤ Type*} {X : C} {R R' : Presieve X} (h : Presieve.IsSeparatedFor F R)
    (hle : R ≤ R') :
    Presieve.IsSeparatedFor F R' := fun x t₁ t₂ ht₁ ht₂ ↦
  h (x.restrict hle) t₁ t₂ (Presieve.isAmalgamation_restrict hle x t₁ ht₁)
    (Presieve.isAmalgamation_restrict hle x t₂ ht₂)

/-- A finite product of ind-étale ring homomorphisms is ind-étale. -/
lemma _root_.RingHom.IndEtale.pi {R : Type u} [CommRing R] {I : Type u} [Finite I]
    {A : I → Type u} [∀ i, CommRing (A i)] (f : ∀ i, R →+* A i)
    (hf : ∀ i, (f i).IndEtale) :
    (Pi.ringHom f).IndEtale := by
  letI : ∀ i, Algebra R (A i) := fun i ↦ (f i).toAlgebra
  haveI : ∀ i, Algebra.IndEtale R (A i) := hf
  have h : (Pi.ringHom f).toAlgebra = Pi.algebra I A := by
    apply Algebra.algebra_ext
    intro r
    rfl
  change @Algebra.IndEtale R (∀ i, A i) _ _ (Pi.ringHom f).toAlgebra
  rw [h]
  infer_instance

variable {S} in
/-- A jointly surjective family of open immersions in the affine pro-étale site
generates a covering sieve for the Zariski topology. -/
lemma generate_mem_zariskiTopology {X : S.AffineProEt} {ι : Type*} {V : ι → S.AffineProEt}
    (g : ∀ i, V i ⟶ X) (hoi : ∀ i, IsOpenImmersion (g i).left)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((g i).left.base)) :
    Sieve.generate (Presieve.ofArrows V g) ∈ zariskiTopology S X := by
  rw [zariskiTopology_eq_toGrothendieck_zariskiPrecoverage]
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, toProEt_obj_left, Functor.comp_map,
    ProEt.forget_map, Over.forget_map, toProEt_map,
    Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hsurj, hoi⟩

variable {S} in
/-- Pullback squares in the affine pro-étale site induce pullback squares of
underlying schemes. -/
lemma isPullback_left {P X Y Z : S.AffineProEt} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    IsPullback fst.left snd.left f.left g.left :=
  h.map (toProEt S ⋙ ProEt.forget S ⋙ Over.forget S)

variable {S} in
/-- Points of pullbacks in the affine pro-étale site surject onto compatible pairs
of points. -/
lemma exists_left_base_preimage {P X Y Z : S.AffineProEt} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X.left) (y : Y.left)
    (hxy : f.left.base x = g.left.base y) :
    ∃ p : P.left, fst.left.base p = x ∧ snd.left.base p = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have hL := isPullback_left h
  refine ⟨hL.isoPullback.inv.base z, ?_, ?_⟩
  · calc fst.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ fst.left).base z := rfl
      _ = (pullback.fst f.left g.left).base z := by rw [hL.isoPullback_inv_fst]
      _ = x := hz₁
  · calc snd.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ snd.left).base z := rfl
      _ = (pullback.snd f.left g.left).base z := by rw [hL.isoPullback_inv_snd]
      _ = y := hz₂

set_option maxHeartbeats 1600000 in
-- The arrow-refinement construction elaborates many large pullback presentations.
variable {S} in
/-- Given a finite jointly surjective family `f i : V i ⟶ X` in the affine pro-étale site,
`W := Spec (∏ᵢ Γ(Vᵢ))` (the disjoint union of the `V i`) factors the family through a single
surjection `q : W ⟶ X` such that the pieces `j i : V i ⟶ W` form a Zariski cover of `W`. -/
lemma exists_surjective_factorization {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      ∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base) := by
  -- The product of the rings of global sections; `Spec` of it is the disjoint union.
  let R : CommRingCat.{u} := .of (Π i, Γ((V i).left, ⊤))
  let φ : Γ(X.left, ⊤) ⟶ R := CommRingCat.ofHom (Pi.ringHom fun i ↦ ((f i).left.appTop).hom)
  have hφ : φ.hom.IndEtale :=
    RingHom.IndEtale.pi _ fun i ↦ indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (f i))
  let q₀ : Spec R ⟶ X.left := Spec.map φ ≫ X.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφ)
  let W : S.AffineProEt := mk (q₀ ≫ X.hom) (proAffineEtale.comp_mem _ _ hq₀ X.prop)
  let q : W ⟶ X := MorphismProperty.Over.homMk q₀ rfl trivial
  let e : ∀ i, (V i).left ⟶ Spec R := fun i ↦
    (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  have he : ∀ i, e i ≫ q₀ = (f i).left := by
    intro i
    have h1 : φ ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = (f i).left.appTop := by
      ext x
      rfl
    change ((V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))) ≫
      Spec.map φ ≫ X.left.isoSpec.inv = (f i).left
    rw [Category.assoc, ← Spec.map_comp_assoc, h1, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hw : ∀ i, e i ≫ W.hom = (V i).hom := fun i ↦ by
    change e i ≫ q₀ ≫ X.hom = (V i).hom
    rw [← Category.assoc, he i, MorphismProperty.Over.w (f i)]
  let j : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (e i) (hw i) trivial
  have hcomp : ∀ i, j i ≫ q = f i := by
    intro i
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    exact he i
  have hoiSpec (i : ι) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i))) := by
    rw [← ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i]
    infer_instance
  have hoi : ∀ i, IsOpenImmersion (j i).left := fun i ↦ by
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    rw [hj]
    haveI := hoiSpec i
    infer_instance
  have hcov : ∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base) := by
    intro w
    obtain ⟨p, hp⟩ := (sigmaSpec fun i ↦ Γ((V i).left, ⊤)).surjective w
    obtain ⟨i, y, hy⟩ : ∃ (i : ι) (y : Spec (Γ((V i).left, ⊤))),
        ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i) y = p :=
      ⟨_, (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).covers p⟩
    have h2 : (V i).left.isoSpec.inv ≫ e i =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := by
      change (V i).left.isoSpec.inv ≫ (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) = _
      rw [Iso.inv_hom_id_assoc]
    have hmor : (V i).left.isoSpec.inv ≫ (j i).left =
        (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
          sigmaSpec fun k ↦ Γ((V k).left, ⊤) := by
      have hj : (j i).left = e i := rfl
      rw [hj, h2, show (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i =
        Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i from rfl, ι_sigmaSpec]
    refine ⟨i, (V i).left.isoSpec.inv y, ?_⟩
    calc (j i).left ((V i).left.isoSpec.inv y)
        = ((V i).left.isoSpec.inv ≫ (j i).left) y := (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
            sigmaSpec fun k ↦ Γ((V k).left, ⊤)) y := congrArg (fun g ↦ g y) hmor
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i y) :=
          Scheme.Hom.comp_apply _ _ _
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤)) p := by rw [hy]
      _ = w := hp
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(e i).base y, ?_⟩
    calc q₀.base ((e i).base y) = (e i ≫ q₀).base y := rfl
      _ = (f i).left.base y := by rw [he i]
      _ = x := hy
  exact ⟨W, q, j, ⟨hq₀surj⟩, hcomp, hoi, hcov⟩

variable {S} in
/-- The sheaf condition for a finite, jointly surjective family in the affine pro-étale site
follows from the Zariski sheaf condition together with the sheaf condition for single
surjections. This is the key step in Bhatt–Scholze, Lemma 4.2.4. -/
lemma isSheafFor_ofArrows_of_finite {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : Presheaf.IsSheaf (zariskiTopology S) F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.left],
      (Presieve.singleton f).IsSheafFor F)
    {X : S.AffineProEt} {ι : Type u} [Finite ι] (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    (Presieve.ofArrows V f).IsSheafFor F := by
  replace h₁ := (isSheaf_iff_isSheaf_of_type _ _).mp h₁
  obtain ⟨W, q, j, hq, hcomp, hoi, hcov⟩ := exists_surjective_factorization V f hsurj
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  -- Step 1: glue the `x i` over the Zariski cover `{j i}` of `W` to obtain `z : F(W)`.
  have hW : (Presieve.ofArrows V j).IsSheafFor F :=
    (Presieve.isSheafFor_iff_generate _).mpr (h₁ _ (generate_mem_zariskiTopology j hoi hcov))
  rw [Presieve.isSheafFor_arrows_iff] at hW
  obtain ⟨z, hz, hzuniq⟩ := hW x (fun a b Q ga gb hab ↦ hx a b Q ga gb (by
    rw [← hcomp a, ← hcomp b, ← Category.assoc, hab, Category.assoc]))
  -- Step 2: the singleton family `q ↦ z` is compatible. This is checked on a Zariski cover
  -- by double pullbacks, using compatibility of `x` over `X`.
  have hsep : ∀ {Q : S.AffineProEt} (g₁ g₂ : Q ⟶ W), g₁ ≫ q = g₂ ≫ q →
      F.map g₁.op z = F.map g₂.op z := by
    intro Q g₁ g₂ hg
    have hAoi : ∀ a : ι, IsOpenImmersion (pullback.fst g₁ (j a)).left := fun a ↦
      MorphismProperty.of_isPullback
        (isPullback_left (IsPullback.of_hasPullback g₁ (j a)).flip) (hoi a)
    have hBoi : ∀ a b : ι,
        IsOpenImmersion (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b)).left := fun a b ↦
      MorphismProperty.of_isPullback
        (isPullback_left (IsPullback.of_hasPullback (pullback.fst g₁ (j a) ≫ g₂) (j b)).flip)
        (hoi b)
    let r : ∀ p : ι × ι, pullback (pullback.fst g₁ (j p.1) ≫ g₂) (j p.2) ⟶ Q := fun p ↦
      pullback.fst (pullback.fst g₁ (j p.1) ≫ g₂) (j p.2) ≫ pullback.fst g₁ (j p.1)
    have hroi : ∀ p : ι × ι, IsOpenImmersion (r p).left := fun p ↦ by
      haveI := hAoi p.1
      haveI := hBoi p.1 p.2
      change IsOpenImmersion
        (pullback.fst (pullback.fst g₁ (j p.1) ≫ g₂) (j p.2) ≫ pullback.fst g₁ (j p.1)).left
      rw [MorphismProperty.Comma.comp_left]
      infer_instance
    have hrcov : ∀ zq : Q.left, ∃ p : ι × ι, zq ∈ Set.range ((r p).left.base) := by
      intro zq
      obtain ⟨a, v₁, hv₁⟩ := hcov (g₁.left.base zq)
      obtain ⟨pA, hpA₁, hpA₂⟩ := exists_left_base_preimage
        (IsPullback.of_hasPullback g₁ (j a)) zq v₁ hv₁.symm
      obtain ⟨b, v₂, hv₂⟩ := hcov (g₂.left.base ((pullback.fst g₁ (j a)).left.base pA))
      obtain ⟨pB, hpB₁, hpB₂⟩ := exists_left_base_preimage
        (IsPullback.of_hasPullback (pullback.fst g₁ (j a) ≫ g₂) (j b)) pA v₂ (by
          calc (pullback.fst g₁ (j a) ≫ g₂).left.base pA
              = g₂.left.base ((pullback.fst g₁ (j a)).left.base pA) := rfl
            _ = (j b).left.base v₂ := hv₂.symm)
      refine ⟨⟨a, b⟩, pB, ?_⟩
      calc (r (a, b)).left.base pB
          = (pullback.fst g₁ (j a)).left.base
              ((pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b)).left.base pB) := rfl
        _ = (pullback.fst g₁ (j a)).left.base pA := by rw [hpB₁]
        _ = zq := hpA₁
    have hsepZ : (Presieve.ofArrows _ r).IsSeparatedFor F :=
      ((Presieve.isSheafFor_iff_generate _).mpr
        (h₁ _ (generate_mem_zariskiTopology r hroi hrcov))).isSeparatedFor
    refine hsepZ.ext fun Q' g' hg' ↦ ?_
    obtain ⟨p⟩ := hg'
    obtain ⟨a, b⟩ := p
    have e₁ : r (a, b) ≫ g₁ =
        (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.snd g₁ (j a)) ≫ j a := by
      change (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.fst g₁ (j a)) ≫ g₁ = _
      rw [Category.assoc, pullback.condition (f := g₁) (g := j a), Category.assoc]
    have e₂ : r (a, b) ≫ g₂ =
        pullback.snd (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ j b := by
      change (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.fst g₁ (j a)) ≫ g₂ = _
      rw [Category.assoc, pullback.condition (f := pullback.fst g₁ (j a) ≫ g₂) (g := j b)]
    have key : (pullback.fst (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ pullback.snd g₁ (j a)) ≫ f a =
        pullback.snd (pullback.fst g₁ (j a) ≫ g₂) (j b) ≫ f b := by
      rw [← hcomp a, ← hcomp b, ← Category.assoc, ← Category.assoc, ← e₁, ← e₂,
        Category.assoc, Category.assoc, hg]
      simp only [r, Category.assoc]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      e₁, e₂]
    simp only [op_comp, Functor.map_comp_apply, hz]
    simpa using hx a b _ _ _ key
  -- Step 3: amalgamate `z` along the single surjection `q` using `h₂`.
  haveI : Surjective q.left := hq
  have hqsheaf := h₂ q
  rw [← Presieve.ofArrows_pUnit.{_, _, 0}, Presieve.isSheafFor_arrows_iff] at hqsheaf
  obtain ⟨t, ht, htuniq⟩ := hqsheaf (fun _ ↦ z) fun _ _ Q g₁ g₂ hgq ↦ hsep g₁ g₂ hgq
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [← hcomp i, op_comp, Functor.map_comp_apply, ht PUnit.unit, hz i]
  · refine htuniq t' fun _ ↦ ?_
    refine hzuniq (F.map q.op t') fun i ↦ ?_
    rw [← Functor.map_comp_apply, ← op_comp, hcomp i]
    exact ht' i

variable {S} in
/-- Any covering sieve of the affine pro-étale topology contains a finite jointly
surjective family. -/
lemma exists_finite_jointly_surjective_of_mem_topology {X : S.AffineProEt} {T : Sieve X}
    (hT : T ∈ topology S X) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X),
      (∀ i, T (f i)) ∧ ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base) := by
  have hT' : T.functorPushforward (toProEt S) ∈ ProEt.topology S ((toProEt S).obj X) := hT
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT'
  obtain ⟨R, hR, hle⟩ := hT'
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨E, rfl⟩ := hR
  -- The underlying scheme-level cover is quasi-compact, and `X.left` is affine, so finitely
  -- many components hit every point.
  have hmem : (E.toPreZeroHypercover.map (ProEt.forget S ⋙ Over.forget S)).presieve₀ ∈
      Scheme.proetalePrecoverage X.left := by
    rw [PreZeroHypercover.presieve₀_map]
    exact E.mem₀
  have hqc : QuasiCompactCover (E.toPreZeroHypercover.map (ProEt.forget S ⋙ Over.forget S)) := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact hmem.1
  have hcompact : IsCompact ((⊤ : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  obtain ⟨n, a, Vo, hVo, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact
    (E.toPreZeroHypercover.map (ProEt.forget S ⋙ Over.forget S)) (U := ⊤) hcompact
  -- Each of the chosen components factors through an arrow of `T`.
  have hpush : ∀ k : Fin n, ∃ (Z : S.AffineProEt) (t : Z ⟶ X)
      (l : E.X (a k) ⟶ (toProEt S).obj Z),
      T t ∧ E.f (a k) = l ≫ (toProEt S).map t := fun k ↦ hle _ _ (Presieve.ofArrows.mk (a k))
  choose Z t l ht hfac using hpush
  refine ⟨ULift.{u} (Fin n), inferInstance, fun k ↦ Z k.down, fun k ↦ t k.down,
    fun k ↦ ht k.down, ?_⟩
  intro x
  have hx : x ∈ ((⊤ : X.left.Opens) : Set X.left) := by
    rw [TopologicalSpace.Opens.coe_top]
    trivial
  rw [← hcov] at hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  obtain ⟨w, -, hw⟩ := hk
  refine ⟨⟨k⟩, (l k).left.base w, ?_⟩
  have h1 : (E.f (a k)).left = (l k).left ≫ ((toProEt S).map (t k)).left := by
    rw [hfac k]
    rfl
  have h2 : (E.f (a k)).left.base w = x := hw
  rw [h1] at h2
  exact h2

/-- To show a presheaf of types is a sheaf on the affine pro-étale site, it suffices to show
it is a Zariksi sheaf and satifies the sheaf condition for single surjective morphisms. -/
lemma isSheaf {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : Presheaf.IsSheaf (zariskiTopology S) F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X T hT
  obtain ⟨ι, _, V, f, hmem, hsurj⟩ := exists_finite_jointly_surjective_of_mem_topology hT
  refine Presieve.IsSheafFor.of_le (R := Presieve.ofArrows V f) ?_
    (isSheafFor_ofArrows_of_finite h₁ h₂ V f hsurj) ?_
  · rintro Y g ⟨i⟩
    exact hmem i
  · intro Y g hg
    have hsurj' : ∀ y : Y.left, ∃ i, y ∈ Set.range ((pullback.snd (f i) g).left.base) := by
      intro y
      obtain ⟨i, v, hv⟩ := hsurj (g.left.base y)
      obtain ⟨p, -, hp⟩ := exists_left_base_preimage (IsPullback.of_hasPullback (f i) g) v y hv
      exact ⟨i, p, hp⟩
    refine ((isSheafFor_ofArrows_of_finite h₁ h₂ _ _ hsurj').isSeparatedFor).of_le ?_
    rintro Q' h' ⟨i⟩
    exact ⟨V i, pullback.fst (f i) g, f i, ⟨i⟩, pullback.condition⟩

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

@[reassoc (attr := simp)]
lemma AffineEtale.SpecMap_hom {X Y : S.AffineEtale} (f : X ⟶ Y) :
    Spec.map f.left.unop ≫ Y.hom = X.hom := by
  simpa using CommaMorphism.w f.toCommaMorphism

variable {S} in
def AffineEtale.ring (X : S.AffineEtale) : CommRingCat :=
  X.left.unop

variable {S} in
def AffineEtale.Hom.ring {X Y : S.AffineEtale} (f : X ⟶ Y) :
    Y.ring ⟶ X.ring :=
  (CommaMorphism.left f.toCommaMorphism).unop

@[simp]
lemma AffineEtale.Hom.ring_comp {X Y Z : S.AffineEtale} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    Hom.ring (f ≫ g) = Hom.ring g ≫ Hom.ring f :=
  rfl

variable {S} in
noncomputable
def AffineEtale.homMk {X Y : S.AffineEtale} (f : Y.ring ⟶ X.ring)
    (h : Scheme.Spec.map f.op ≫ Y.hom = X.hom := by cat_disch) :
    X ⟶ Y :=
  MorphismProperty.CostructuredArrow.homMk f.op trivial h

@[simp]
lemma AffineEtale.homMk_left {X Y : S.AffineEtale} (f : Y.ring ⟶ X.ring)
    (h : Scheme.Spec.map f.op ≫ Y.hom = X.hom := by cat_disch) :
    Hom.ring (homMk f h) = f :=
  rfl

@[ext]
lemma AffineEtale.Hom.ext {X Y : S.AffineEtale} {f g : X ⟶ Y}
    (h : Hom.ring f = Hom.ring g) :
    f = g := by
  apply MorphismProperty.Comma.Hom.ext
  · apply Quiver.Hom.unop_inj
    exact h
  · simp

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

noncomputable
abbrev toScheme : AffineProEt S ⥤ Scheme.{u} :=
  toProEt S ⋙ ProEt.forget _ ⋙ Over.forget _

variable {S} in
/-- The composition `S.AffineProEt ⥤ Scheme` of the inclusion into the pro-étale site with
the forgetful functors preserves cofiltered limits: the candidate limit is the `Spec` of the
filtered colimit of global sections, which is pro-affine-étale over `S` since each transition
map is ind-étale on global sections. -/
noncomputable def isLimitMapConeToSchemeOfIsLimit {J : Type u} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ S.AffineProEt} (c : Cone D) (hc : IsLimit c) :
    IsLimit ((toScheme S).mapCone c) := by
  -- The diagram of (affine) schemes underlying `D`.
  let Dl : J ⥤ Scheme.{u} := D ⋙ toScheme S
  have hAff (j : J) : IsAffine (Dl.obj j) := inferInstanceAs (IsAffine (D.obj j).left)
  -- The corresponding diagram of rings of global sections.
  let Φ : J ⥤ CommRingCat.{u}ᵒᵖ := Dl ⋙ Scheme.Γ.rightOp
  -- A limit cone of `Dl` in `Scheme`, given by `Spec` of the (co)limit of `Φ`.
  let e : Dl ≅ Φ ⋙ Scheme.Spec :=
    NatIso.ofComponents (fun j ↦ (Dl.obj j).isoSpec)
      (fun {i j} u ↦ (Scheme.isoSpec_hom_naturality (Dl.map u)).symm)
  let cL : Cone Dl := (Cone.postcompose e.inv).obj (Scheme.Spec.mapCone (limit.cone Φ))
  have hL : IsLimit cL := (IsLimit.postcomposeInvEquiv e _).symm
    (isLimitOfPreserves Scheme.Spec (limit.isLimit Φ))
  have hne : Nonempty J := IsCofiltered.nonempty
  let j₀ : J := hne.some
  -- The ring of global sections of the limit is the filtered colimit of the global
  -- sections over the objects mapping to `j₀`.
  have hcK : IsLimit ((limit.cone Φ).whisker (Over.forget j₀)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget j₀) (limit.cone Φ)).symm
      (limit.isLimit Φ)
  have hcolim : IsColimit (coconeLeftOpOfCone ((limit.cone Φ).whisker (Over.forget j₀))) :=
    isColimitCoconeLeftOpOfCone _ hcK
  -- The transition maps out of `j₀`, as a natural transformation of ring diagrams.
  let t : (Functor.const (Over j₀)ᵒᵖ).obj ((Φ.obj j₀).unop) ⟶
      (Over.forget j₀ ⋙ Φ).leftOp :=
    { app k := (Φ.map k.unop.hom).unop
      naturality {k k'} u := by
        dsimp
        rw [Category.id_comp, ← unop_comp, ← Φ.map_comp, Over.w u.unop] }
  -- The projection to `Dl.obj j₀` is ind-étale on global sections.
  have hπ₀ : (limit.π Φ j₀).unop.hom.IndEtale := by
    refine RingHom.IndEtale.of_isColimit _ (Over j₀)ᵒᵖ _ (t := t) hcolim fun k ↦ ⟨?_, ?_⟩
    · exact indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (D.map k.unop.hom))
    · dsimp [t]
      rw [← unop_comp, limit.w]
  -- Hence the projection to `Dl.obj j₀` is pro-affine-étale.
  have hπ : proAffineEtale (cL.π.app j₀) := by
    have heq : cL.π.app j₀ = Spec.map ((limit.π Φ j₀).unop) ≫ (Dl.obj j₀).isoSpec.inv := rfl
    rw [heq, proAffineEtale.cancel_right_of_respectsIso, proAffineEtale_Spec_iff]
    exact hπ₀
  -- The structure morphism to `S` is independent of the choice of `j₀`.
  have hw (j : J) : cL.π.app j ≫ (D.obj j).hom = cL.π.app j₀ ≫ (D.obj j₀).hom := by
    obtain ⟨k, f₁, f₂, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
    have h₁ : cL.π.app k ≫ Dl.map f₁ = cL.π.app j := cL.w f₁
    have h₂ : cL.π.app k ≫ Dl.map f₂ = cL.π.app j₀ := cL.w f₂
    have w₁ : Dl.map f₁ ≫ (D.obj j).hom = (D.obj k).hom := MorphismProperty.Over.w (D.map f₁)
    have w₂ : Dl.map f₂ ≫ (D.obj j₀).hom = (D.obj k).hom := MorphismProperty.Over.w (D.map f₂)
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, w₁, w₂]
  -- Assemble the limit cone in the affine pro-étale site.
  have hℓ : proAffineEtale (cL.π.app j₀ ≫ (D.obj j₀).hom) :=
    proAffineEtale.comp_mem _ _ hπ (D.obj j₀).prop
  let cA : Cone D :=
    { pt := AffineProEt.mk (cL.π.app j₀ ≫ (D.obj j₀).hom) hℓ
      π :=
        { app j := MorphismProperty.Over.homMk (cL.π.app j) (hw j)
          naturality {i j} u := by
            refine MorphismProperty.Over.Hom.ext ?_
            dsimp
            rw [Category.id_comp]
            exact (cL.w u).symm } }
  have hmapA : IsLimit ((toScheme S).mapCone cA) :=
    hL.ofIsoLimit (Cone.ext (Iso.refl _) (fun j ↦ (Category.id_comp _).symm))
  have hcA : IsLimit cA := isLimitOfReflects (toScheme S) hmapA
  exact hmapA.ofIsoLimit ((Cone.functoriality D (toScheme S)).mapIso (hcA.uniqueUpToIso hc))

instance : PreservesCofilteredLimitsOfSize.{u, u} (toScheme S) where
  preserves_cofiltered_limits _ _ _ :=
    { preservesLimit :=
        { preserves := fun {c} hc ↦ ⟨isLimitMapConeToSchemeOfIsLimit c hc⟩ } }

instance : PreservesCofilteredLimitsOfSize.{u, u} (toProEt S) where
  preserves_cofiltered_limits _ _ _ :=
    { preservesLimit :=
        { preserves := fun {c} hc ↦
            ⟨isLimitOfReflects (ProEt.forget S ⋙ CategoryTheory.Over.forget S)
              ((isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
                (Functor.mapConeMapCone c).symm)⟩ } }

instance {X : S.AffineEtale} : Etale ((AffineEtale.toAffineProEt S).obj X).hom :=
  X.prop

instance {X : S.AffineEtale} : Etale X.hom :=
  X.prop

lemma exists_relativeLimitPresentation_hom {X Y : S.AffineProEt} (f : X ⟶ Y) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J)
      (pX : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) X)
      (pY : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) Y)
      (hom : pX.Hom pY),
      f = hom.map := by
  obtain ⟨J₁, _, _, ⟨pres₁⟩⟩ := Y.exists_relativeLimitPresentation
  obtain ⟨J₂, _, _, ⟨pres₂⟩⟩ := X.exists_relativeLimitPresentation
  have : ∀ (i : J₂),
      CompactSpace ↥(((pres₂.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S).obj i) := by
    dsimp; infer_instance
  have : ∀ {i j : J₂} (f : i ⟶ j),
      IsAffineHom (((pres₂.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S).map f) := by
    dsimp; infer_instance
  have (i : J₂) : QuasiSeparatedSpace
      ↥(((pres₂.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S).obj i) := by
    dsimp; infer_instance
  let t₂ : (pres₂.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S ⟶ (Functor.const J₂).obj S :=
    .mk fun _ ↦ Over.hom _
  have (i : J₂) : LocallyOfFinitePresentation (t₂.app i) := by dsimp [t₂]; infer_instance
  let t₁ : (pres₁.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S ⟶ (Functor.const J₁).obj S :=
    .mk fun _ ↦ Over.hom _
  have w (i : J₂) (i' : J₁) :
      (pres₂.π.app i).left ≫ t₂.app i =
        f.left ≫ (pres₁.π.app i').left ≫ t₁.app i' := by
    simp only [Functor.const_obj_obj, Functor.comp_obj, AffineEtale.toAffineProEt_obj_left,
      ProEt.forget_obj, toProEt_obj_hom, AffineEtale.toAffineProEt_obj_hom, t₁, t₂]
    have := MorphismProperty.Over.w (pres₂.π.app i)
    dsimp at this
    rw [this]
    have := MorphismProperty.Over.w (pres₁.π.app i')
    dsimp at this
    rw [this]
    simp
  have (i : J₁) : LocallyOfFinitePresentation (t₁.app i) := by dsimp [t₁]; infer_instance
  obtain ⟨J, _, _, G, G', _, _, g, hg, hfac⟩ := exists_eq_isLimitMap_whisker (S := S) _
    t₂ _ (isLimitOfPreserves (toScheme S) pres₂.isLimit) _ t₁ _
    (isLimitOfPreserves (toScheme S) pres₁.isLimit) f.left w
  refine ⟨J, inferInstance, inferInstance, pres₂.precomp G, pres₁.precomp G', ?_, ?_⟩
  · refine { natTrans.app := ?_, natTrans.naturality := ?_ }
    · intro j
      refine AffineEtale.homMk (Spec.preimage (g.app j)) ?_
      simpa using hfac j
    · intro i j u
      simp only [RelativeLimitPresentation.precomp_diag, Functor.comp_obj, Functor.comp_map]
      ext : 1
      simp only [AffineEtale.Hom.ring_comp, AffineEtale.homMk_left]
      apply Spec.map_injective
      simpa using g.naturality u
  · apply (pres₁.precomp G').isLimit.hom_ext
    intro j
    rw [RelativeLimitPresentation.Hom.map_π]
    simp only [RelativeLimitPresentation.precomp_diag, Functor.comp_obj,
      RelativeLimitPresentation.precomp_π, Functor.whiskeringLeft_obj_obj, NatTrans.comp_app,
      Functor.const_obj_obj, Functor.constCompWhiskeringLeftIso_inv_app_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Category.comp_id, Category.id_comp]
    apply (toScheme S).map_injective
    dsimp
    have := hg =≫ (Cone.whisker G' ((toScheme S).mapCone { pt := Y, π := pres₁.π })).π.app j
    rw [IsLimit.map_π] at this
    change f.left ≫ _ = _ ≫ _
    simpa [AffineEtale.homMk] using this

instance : PreservesLimitsOfShape WalkingCospan (AffineEtale.Spec S) :=
  inferInstanceAs <| PreservesLimitsOfShape WalkingCospan
    (MorphismProperty.CostructuredArrow.toOver @Etale Scheme.Spec S)

instance : PreservesLimitsOfShape WalkingCospan (AffineEtale.toAffineProEt S) :=
  have : PreservesLimitsOfShape WalkingCospan (AffineEtale.toAffineProEt S ⋙ toScheme S) :=
    inferInstanceAs <| PreservesLimitsOfShape WalkingCospan
      (AffineEtale.Spec S ⋙ Etale.forget S ⋙ CategoryTheory.Over.forget S)
  preservesLimitsOfShape_of_reflects_of_preserves _ (toScheme S)

set_option maxHeartbeats 1600000 in
-- The arrow-refinement construction elaborates many large pullback presentations.
lemma singleton_inf_le_relativelyPresentable :
    (Precoverage.singleton S.AffineProEt ⊓
      MorphismProperty.precoverage fun _ _ f ↦ Surjective f.left) ≤
      Precoverage.relativelyPresentable.{u}
        (AffineEtale.toAffineProEt S) (AffineEtale.topology S) := by
  rintro X R ⟨⟨Y, f, rfl⟩, hf⟩
  obtain ⟨J, _, _, pY, pX, hom, rfl⟩ := exists_relativeLimitPresentation_hom _ f
  simp only [MorphismProperty.singleton_mem_precoverage_iff] at hf
  -- Scheme-level diagrams, limit cones and the level-wise comparison map.
  let GX : J ⥤ Scheme.{u} := (pX.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S
  let GY : J ⥤ Scheme.{u} := (pY.diag ⋙ AffineEtale.toAffineProEt S) ⋙ toScheme S
  have hcX : IsLimit ((toScheme S).mapCone pX.cone) :=
    isLimitMapConeToSchemeOfIsLimit pX.cone pX.isLimit
  let g : GY ⟶ GX :=
    Functor.whiskerRight (Functor.whiskerRight hom.natTrans (AffineEtale.toAffineProEt S))
      (toScheme S)
  -- The level-wise comparison maps are étale, hence open.
  have hetale (k : J) : Etale (g.app k) := by
    have h1 : Etale ((AffineEtale.toAffineProEt S).map (hom.natTrans.app k)).left := by
      refine MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _
        ((AffineEtale.toAffineProEt S).obj (pX.diag.obj k)).hom ?_ ?_
      · have h2 : Etale (pX.diag.obj k).hom := (pX.diag.obj k).prop
        simpa using h2
      · rw [MorphismProperty.Over.w
          ((AffineEtale.toAffineProEt S).map (hom.natTrans.app k))]
        have h2 : Etale (pY.diag.obj k).hom := (pY.diag.obj k).prop
        simpa using h2
    exact h1
  have hopen (k : J) : IsOpenMap (g.app k).base := by
    have := hetale k
    exact isOpenMap_of_generalizingMap _ (Flat.generalizingMap _)
  -- Identify the limit of the comparison maps with `hom.map.left`.
  have heq : IsLimit.map ((toScheme S).mapCone pY.cone) hcX g = (toScheme S).map hom.map := by
    apply hcX.hom_ext
    intro k
    rw [IsLimit.map_π]
    have h2 := congrArg (toScheme S).map (hom.map_π k)
    simp only [Functor.map_comp] at h2
    exact h2.symm
  have hsurjlim : Surjective (IsLimit.map ((toScheme S).mapCone pY.cone) hcX g) := by
    rw [heq]
    exact hf
  -- Instances for the spreading lemma.
  haveI haff (i : J) : IsAffine (GX.obj i) :=
    inferInstanceAs (IsAffine ((AffineEtale.toAffineProEt S).obj (pX.diag.obj i)).left)
  haveI (i : J) : CompactSpace (GX.obj i) := by
    have : IsAffine (GX.obj i) := haff i
    infer_instance
  -- The arrow property: the image of the transition map is contained in the image of the
  -- level-wise comparison map.
  let Φ : ObjectProperty (Arrow J) := fun u ↦
    Set.range (GX.map u.hom).base ⊆ Set.range (g.app u.right).base
  have hpre : ∀ {l' l k : J} (a : l' ⟶ l) (u : l ⟶ k),
      Φ (Arrow.mk u) → Φ (Arrow.mk (a ≫ u)) := by
    intro l' l k a u hu
    rintro x ⟨y, rfl⟩
    refine hu ⟨(GX.map a) y, ?_⟩
    calc (GX.map u) ((GX.map a) y)
        = (GX.map a ≫ GX.map u) y := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (GX.map (a ≫ u)) y := congrArg (fun q ↦ q y) (GX.map_comp a u).symm
  have hex : ∀ k : J, ∃ (m : J) (w : m ⟶ k), Φ (Arrow.mk w) := by
    intro k
    obtain ⟨m, w, hw⟩ := exists_range_map_subset_range_app_of_surjective_isLimitMap
      GY ((toScheme S).mapCone pY.cone) GX ((toScheme S).mapCone pX.cone) hcX g k
      (hopen k).isOpen_range hsurjlim
    exact ⟨m, w, hw⟩
  -- The refinement index category.
  haveI hAcof : IsCofiltered Φ.FullSubcategory :=
    CategoryTheory.ArrowRefinement.isCofiltered Φ hpre hex
  haveI := CategoryTheory.ArrowRefinement.initial_leftFunc Φ hpre hex
  haveI := CategoryTheory.ArrowRefinement.initial_rightFunc Φ hpre hex
  -- Presentations over the refinement category.
  let presBase := pX.precomp (Φ.ι ⋙ Arrow.leftFunc)
  let presXc := pX.precomp (Φ.ι ⋙ Arrow.rightFunc)
  let presYc := pY.precomp (Φ.ι ⋙ Arrow.rightFunc)
  -- The transition `Hom` from `presBase` to `presXc`, with `map = 𝟙 X`.
  let pfT : presBase.Hom presXc :=
    { natTrans :=
      { app := fun u ↦ pX.diag.map u.obj.hom
        naturality := fun u v m ↦ by
          dsimp [presBase, presXc]
          rw [← Functor.map_comp, ← Functor.map_comp, CategoryTheory.Arrow.w m.hom] } }
  have hpfT : pfT.map = 𝟙 X := by
    apply presXc.isLimit.hom_ext
    intro u
    rw [RelativeLimitPresentation.Hom.map_π, Category.id_comp]
    have h2 := pX.π.naturality u.obj.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      Functor.comp_map] at h2
    dsimp [presBase, presXc, pfT]
    simp only [Category.id_comp]
    exact h2.symm
  -- The level-wise comparison `Hom` from `presYc` to `presXc`, with `map = hom.map`.
  let homc : presYc.Hom presXc :=
    { natTrans := Functor.whiskerLeft (Φ.ι ⋙ Arrow.rightFunc) hom.natTrans }
  have hhomc : homc.map = hom.map := by
    apply presXc.isLimit.hom_ext
    intro u
    rw [RelativeLimitPresentation.Hom.map_π]
    have h2 := hom.map_π ((Φ.ι ⋙ Arrow.rightFunc).obj u)
    dsimp [presYc, presXc, homc]
    simp only [Category.id_comp, Category.comp_id]
    exact h2.symm
  -- The pullback cone exhibiting `Y` as `X ×_X Y`.
  have hP : IsPullback hom.map (𝟙 Y) (𝟙 X) hom.map :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  -- The presentation of `Y` by level-wise pullbacks.
  let presPull : RelativeLimitPresentation Φ.FullSubcategory
      (AffineEtale.toAffineProEt S) Y :=
    RelativeLimitPresentation.pullback (F := AffineEtale.toAffineProEt S)
      (𝟙 X) hom.map hP.cone hP.isLimit
      presBase presYc presXc pfT homc hpfT hhomc
  -- The covering `Hom` from `presPull` to `presBase`, with `map = hom.map`.
  let coverHom : presPull.Hom presBase :=
    { natTrans :=
      { app := fun u ↦ pullback.fst (pfT.natTrans.app u) (homc.natTrans.app u)
        naturality := fun u v m ↦ by
          dsimp [presPull]
          simp } }
  have hcover : coverHom.map = hom.map := by
    apply presBase.isLimit.hom_ext
    intro u
    rw [RelativeLimitPresentation.Hom.map_π]
    dsimp only [coverHom, presPull, RelativeLimitPresentation.pullback]
    rw [IsPullback.lift_fst]
    have h2 : hP.cone.fst = hom.map := rfl
    rw [h2]
  -- Surjectivity of the level-wise covers.
  have hsurjU (u : Φ.FullSubcategory) : Function.Surjective
      ((AffineEtale.toScheme S).map
        (pullback.fst (pfT.natTrans.app u) (homc.natTrans.app u))).base := by
    have hpb := (IsPullback.of_hasPullback (pfT.natTrans.app u)
      (homc.natTrans.app u)).map (AffineEtale.toScheme S)
    intro x
    have hx : ((AffineEtale.toScheme S).map (pfT.natTrans.app u)) x ∈
        Set.range ((AffineEtale.toScheme S).map (homc.natTrans.app u)).base := by
      have hΦ : Φ u.obj := u.2
      exact hΦ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hx
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨hpb.isoPullback.inv z, ?_⟩
    calc ((AffineEtale.toScheme S).map (pullback.fst _ _)) (hpb.isoPullback.inv z)
        = (hpb.isoPullback.inv ≫
            (AffineEtale.toScheme S).map (pullback.fst _ _)) z :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = (pullback.fst ((AffineEtale.toScheme S).map (pfT.natTrans.app u))
            ((AffineEtale.toScheme S).map (homc.natTrans.app u))) z :=
          congrArg (fun q ↦ q z) hpb.isoPullback_inv_fst
      _ = x := hz1
  -- Assemble; abstract the covering morphism so that dependent matching succeeds.
  suffices h : ∀ (t : Y ⟶ X), coverHom.map = t →
      Presieve.singleton t ∈
        Precoverage.relativelyPresentable.{u} (AffineEtale.toAffineProEt S)
          (AffineEtale.topology S) X by
    exact h hom.map hcover
  intro t ht
  refine ⟨Φ.FullSubcategory, inferInstance, hAcof,
    { pres := presBase
      pres₀ := fun i ↦ match i with
        | ⟨⟨_, _⟩, .mk⟩ => presPull
      f := fun i ↦ match i with
        | ⟨⟨_, _⟩, .mk⟩ => coverHom
      hf := fun i ↦ match i with
        | ⟨⟨_, _⟩, .mk⟩ => ht }, fun u ↦ ?_⟩
  -- The level-wise covering sieve is generated by a single surjective étale morphism.
  refine (AffineEtale.topology S).superset_covering ?_
    (AffineEtale.generate_singleton_mem_topology S
      (pullback.fst (pfT.natTrans.app u) (homc.natTrans.app u)) (hsurjU u))
  rw [Sieve.generate_le_iff]
  rintro Z gz ⟨⟩
  exact ⟨_, 𝟙 _, _,
    Presieve.ofArrows.mk (⟨⟨_, t⟩, Presieve.singleton.mk⟩ :
      (Presieve.singleton t).preZeroHypercover.I₀),
    (Category.id_comp _).symm⟩

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

section SheafComparison

instance : AB5OfSize.{u, u} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{_, _, u + 1, u + 1} Ab

noncomputable
def AffineEtale.toAffineProEtCompToProEtIso :
    AffineEtale.toAffineProEt S ⋙ AffineProEt.toProEt S ≅
      AffineEtale.Spec S ⋙ toProEtale S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

variable {S} in
/-- Since `ProEt.forget S` is fully faithful, mapping into `(ProEt.forget S).obj V` is
naturally isomorphic to mapping into `V`. -/
noncomputable def ProEt.forgetOpCompYonedaIso (V : S.ProEt) :
    (ProEt.forget S).op ⋙ yoneda.obj ((ProEt.forget S).obj V) ≅ yoneda.obj V :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso (ProEt.forgetFullyFaithful S).homEquiv.symm)
    (fun {U U'} f ↦ by
      ext g
      apply (ProEt.forget S).map_injective
      simp [Functor.FullyFaithful.homEquiv]
      rfl)

/-- The presheaf pullback (i.e., the left Kan extension) of a presheaf on the small étale
site to the small pro-étale site sends cofiltered limits of affine étale `S`-schemes to
colimits, when restricted to the small affine pro-étale site.

The key input is `AlgebraicGeometry.Scheme.preservesColimit_yoneda`: maps out of a
cofiltered limit of quasi-compact, quasi-separated schemes into a scheme locally of finite
presentation over the base are a filtered colimit of hom sets. -/
instance ProEt.preservesRelativeFilteredColimits_lan_toProEtale (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
      ((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  -- The limit cone in the pro-étale site.
  have hc₁ : IsLimit ((AffineProEt.toProEt S).mapCone c) := isLimitOfPreserves _ hc
  -- The limit cone in `Over S`, obtained by reflecting the `Scheme`-level limit cone
  -- along `Over.forget S`.
  have hcOver : IsLimit ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  -- The comparison of the two relevant diagrams in the pro-étale site.
  have e : (K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S ≅
      (K ⋙ AffineEtale.Spec S) ⋙ toProEtale S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (AffineEtale.toAffineProEtCompToProEtIso S) ≪≫
      (Functor.associator _ _ _).symm
  -- Mapping into an étale `S`-scheme commutes with the cofiltered limit, by
  -- `Scheme.preservesColimit_yoneda`.
  have hpres : ∀ (X : S.Etaleᵒᵖ),
      PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (toProEtale S).op)
        (coyoneda.obj (Opposite.op ((toProEtale S).op.obj X))) := by
    intro X
    have h₁ : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).map f).left :=
      fun f ↦ inferInstanceAs
        (IsAffineHom ((AffineEtale.toAffineProEt S).map (K.map f)).left)
    have h₂ : ∀ (i : I), CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₃ : ∀ (i : I), QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs
        (QuasiSeparatedSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation
        ((ProEt.forget S).obj ((toProEtale S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    haveI := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙ ProEt.forget S)
      ((ProEt.forget S).obj ((toProEtale S).obj X.unop))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget S).obj ((toProEtale S).obj X.unop))).mapCocone
          ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((toProEtale S).obj X.unop)).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((toProEtale S).obj X.unop))
        (by exact hyon)
    have hco : IsColimit ((coyoneda.obj (Opposite.op ((toProEtale S).op.obj X))).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
    letI : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
        (coyoneda.obj (Opposite.op ((toProEtale S).op.obj X))) :=
      preservesColimit_of_preserves_colimit_cocone hc₁.op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  letI : PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (toProEtale S).op)
      ((toProEtale S).op.leftKanExtension F) := inferInstance
  have e' : (K ⋙ AffineEtale.Spec S).op ⋙ (toProEtale S).op ≅
      ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op := NatIso.op e
  letI : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
      ((toProEtale S).op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ e'
  exact ⟨isColimitOfPreserves ((toProEtale S).op.leftKanExtension F) hc₁.op⟩

/-- If `F` is a sheaf on the small étale site, the presheaf pullback of `F`
to the small pro-étale site (i.e., the left Kan extension) is a
sheaf when restricted to the small affine pro-étale site. -/
lemma isSheaf_lan_toProEtale (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1})
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F) := by
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
      (AffineEtale.toAffineProEt S) (AffineProEt.minimalPrecoverage S)
      (AffineEtale.topology S)
  · let iso : (AffineEtale.toAffineProEt S).op ⋙
        (AffineProEt.toProEt S).op ⋙ S.toProEtale.op.lan.obj F ≅
        (AffineEtale.Spec S).op ⋙ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso <| ((toProEtale S).op.lanUnit.app F)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF
  · exact AffineProEt.generates_minimalPrecoverage S
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable S
  · exact AffineProEt.minimalPrecoverage_le_finite S

namespace ProEt

open Functor in
/-- The pullback of an étale sheaf `F` to the pro-étale site is isomorphic to the presheaf-pullback
of `F` (i.e., left Kan extension) after restricting to the affine pro-étale site. -/
noncomputable def sheafPullbackCompIso :
    ProEt.sheafPullback S Ab.{u + 1} ⋙
      Functor.sheafPushforwardContinuous (AffineProEt.toProEt S) _ (AffineProEt.topology S) _ ⋙
      sheafToPresheaf _ _ ≅
    sheafToPresheaf _ _ ⋙ (toProEtale S).op.lan ⋙
      (Functor.whiskeringLeft _ _ _).obj (AffineProEt.toProEt S).op :=
  isoWhiskerRight (Functor.sheafPullbackIso _ _ _ _) _ ≪≫
    (associator _ _ _) ≪≫
    isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _).symm) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (isoWhiskerRight (IsDenseSubsite.sheafEquivSheafificationCompatibility _ _ _ _).symm _)) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _ (associator _ _ _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    presheafToSheafSheafToPresheafIso _ _ (fun F ↦ isSheaf_lan_toProEtale _ _ F.property) ≪≫
    Functor.associator _ _ _

lemma sheafPullbackCompIso_inv_app (F : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    dsimp% (sheafPullbackCompIso S).inv.app F =
      Functor.whiskerLeft (AffineProEt.toProEt S).op
        (toSheafify (ProEt.topology S) (S.toProEtale.op.lan.obj F.obj)) ≫
      Functor.whiskerLeft (AffineProEt.toProEt S).op
        ((Functor.sheafPullbackIso _ _ _ _).inv.app _).hom := by
  dsimp [sheafPullbackCompIso, presheafToSheafSheafToPresheafIso]
  simp [Functor.sheafPushforwardContinuous]

noncomputable
def sheafPullbackCompSheafPushforwardIso :
    sheafPullback S Ab.{u + 1} ⋙ sheafPushforward S Ab.{u + 1} ⋙
      Functor.sheafPushforwardContinuous (AffineEtale.Spec S) _ (AffineEtale.topology S) _ ⋙
      sheafToPresheaf _ _ ≅
    sheafToPresheaf _ _ ⋙ (toProEtale S).op.lan ⋙
      (Functor.whiskeringLeft _ _ _).obj (toProEtale S).op ⋙
      (Functor.whiskeringLeft _ _ _).obj (AffineEtale.Spec S).op :=
  let e : ProEt.sheafPushforward S Ab.{u + 1} ⋙
        Functor.sheafPushforwardContinuous (AffineEtale.Spec S) _ (AffineEtale.topology S) _ ⋙
        sheafToPresheaf _ _ ≅
      Functor.sheafPushforwardContinuous (AffineProEt.toProEt S) _ (AffineProEt.topology S) _ ⋙
      sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj (AffineEtale.toAffineProEt S).op :=
    Iso.refl _
  Functor.isoWhiskerLeft _ e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _ ≪≫ sheafPullbackCompIso S) _ ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    -- this is some def-eq abuse of composition and `Functor.whiskeringLeft`
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Iso.refl _))

lemma sheafPullbackCompSheafPushforwardIso_inv_app (F : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    (sheafPullbackCompSheafPushforwardIso S).inv.app F =
      Functor.whiskerLeft _ (Functor.whiskerLeft _
        (toSheafify (ProEt.topology S) (S.toProEtale.op.lan.obj F.obj))) ≫
      Functor.whiskerLeft _ (Functor.whiskerLeft _
        ((Functor.sheafPullbackIso _ _ _ _).inv.app _).hom) := by
  dsimp [sheafPullbackCompSheafPushforwardIso]
  rw [sheafPullbackCompIso_inv_app]
  rfl

instance isIso_unit_sheafAdjunction : IsIso (sheafAdjunction S Ab.{u + 1}).unit := by
  -- It suffices to check the isomorphism on the small affine étale site.
  suffices h : IsIso (Functor.whiskerRight (sheafAdjunction S Ab.{u + 1}).unit
      (Functor.sheafPushforwardContinuous (AffineEtale.Spec S) _ (AffineEtale.topology S) _ ⋙
        sheafToPresheaf _ _)) by
    rw [← Functor.whiskeringRight_obj_map] at h
    apply isIso_of_reflects_iso _
      ((Functor.whiskeringRight _ _ _).obj
      (Functor.sheafPushforwardContinuous (AffineEtale.Spec S) _ (AffineEtale.topology S) _ ⋙
        sheafToPresheaf _ _))
  let munit := Functor.whiskerRight
    (Functor.whiskerLeft (sheafToPresheaf (smallEtaleTopology S) _)
      ((toProEtale S).op.lanUnit (H := Ab.{u + 1})))
    ((Functor.whiskeringLeft _ _ _).obj (AffineEtale.Spec S).op)
  have heq :
      Functor.whiskerRight (sheafAdjunction _ Ab.{u + 1}).unit
        (Functor.sheafPushforwardContinuous (AffineEtale.Spec S) _ (AffineEtale.topology S) _ ⋙
          sheafToPresheaf _ _) =
      (Functor.leftUnitor _).hom ≫
        (Functor.sheafPushforwardContinuousCompSheafToPresheafIso _ _ _ _).hom ≫
        Functor.whiskerRight (Functor.rightUnitor _).inv _ ≫
        munit ≫
        (Functor.associator _ _ _).hom ≫
        (Functor.whiskerLeft _ (Functor.associator _ _ _).hom) ≫
        (sheafPullbackCompSheafPushforwardIso S).inv ≫
        (Functor.associator _ _ _).inv := by
    ext F U : 4
    dsimp [munit]
    simp only [Category.id_comp]
    dsimp [Functor.sheafPushforwardContinuous]
    simp only [Category.comp_id]
    rw [sheafPullbackCompSheafPushforwardIso_inv_app]
    simp only [Functor.whiskerLeft_twice, Category.assoc, Iso.hom_inv_id_assoc]
    have := Functor.lanUnit_toSheafify_sheafPullbackIso_inv_app_hom_app
      (toProEtale S) _ _ (ProEt.topology S) F (.op <| ((AffineEtale.Spec S).obj (Opposite.unop U)))
    dsimp
    simp [sheafAdjunction, Functor.lan, this]
  rw [heq]
  infer_instance

instance faithful_sheafPullback : (sheafPullback S Ab.{u + 1}).Faithful :=
  (sheafAdjunction S Ab.{u + 1}).faithful_L_of_mono_unit_app

instance full_sheafPullback : (sheafPullback S Ab.{u + 1}).Full :=
  (sheafAdjunction S Ab.{u + 1}).full_L_of_isSplitEpi_unit_app

end ProEt

end SheafComparison

end AlgebraicGeometry.Scheme
