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

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange]
variable (A : Type*) [Category* A]

instance :
    (Over.pullback P ⊤ f).PreservesOneHypercovers
      (T.smallGrothendieckTopology P)
      (S.smallGrothendieckTopology P) := by
  intro X E
  constructor
  · sorry
  · sorry

noncomputable
abbrev smallPushforward :
    Sheaf (S.smallGrothendieckTopology P) A ⥤ Sheaf (T.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPushforwardContinuous _ _ _

instance :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology P)
      (smallGrothendieckTopology P)).IsRightAdjoint :=
  sorry

noncomputable
abbrev smallPullback :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPullback _ _ _

noncomputable
def smallPullbackPushforwardAdj :
    smallPullback f P A ⊣ smallPushforward f P A :=
  (Over.pullback P ⊤ f).sheafAdjunctionContinuous A _ _

instance (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology P) (smallGrothendieckTopology P) :=
  sorry

def smallSheafRestrict (hf : P f) :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.map ⊤ hf).sheafPushforwardContinuous _ _ _

noncomputable def smallSheafRestrictAdj (hf : P f) :
    smallSheafRestrict f P A hf ⊣ smallPushforward f P A :=
  (Over.mapPullbackAdj P ⊤ f hf trivial).sheaf _ _

/-- If `f : S ⟶ T` satisfies `P` the pullback functor `Shv(T) ⥤ Shv(S)` is
naturally isomorphic to the restriction functor. -/
noncomputable def smallPullbackIsoRestrict (hf : P f) :
    smallPullback f P A ≅ smallSheafRestrict f P A hf :=
  (conjugateIsoEquiv (smallSheafRestrictAdj f P A hf) (smallPullbackPushforwardAdj f P A)).symm
    (Iso.refl _)

end

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
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale le_rfl).Faithful

-- TODO: move me
lemma _root_.CategoryTheory.GrothendieckTopology.transitive_of_presieve {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {X : C} (R : Presieve X) (hR : .generate R ∈ J X) (S : Sieve X)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → S.pullback g ∈ J Y) :
    S ∈ J X := by
  refine J.transitive hR _ ?_
  rintro Y f ⟨W, g, v, hv, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable _ (h _ hv)

@[simp]
lemma _root_.CategoryTheory.Presieve.map_comp {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (F : C ⥤ D) (G : D ⥤ E) {X : C} (R : Presieve X) :
    R.map (F ⋙ G) = (R.map F).map G := by
  refine le_antisymm ?_ ?_
  · rw [Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    apply Presieve.map_map
    exact hf
  · rw [Presieve.map_le_iff_le_functorPullback, Presieve.map_le_iff_le_functorPullback]
    intro Y f hf
    apply Presieve.map_map
    exact hf

@[simps]
def _root_.CategoryTheory.PreZeroHypercover.equivOfIso {C : Type*} [Category* C] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) :
    E.I₀ ≃ F.I₀ where
  toFun := e.hom.s₀
  invFun := e.inv.s₀
  left_inv _ := by simp
  right_inv _ := by simp

lemma _root_.CategoryTheory.PreZeroHypercover.mem_of_iso {C : Type*} [Category* C]
    {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F)
    (hE : E.presieve₀ ∈ K X) :
    F.presieve₀ ∈ K X := by
  have : F.presieve₀ =
      Presieve.ofArrows (fun (i : Σ (_ : F.I₀), Unit) ↦ _)
        (fun i ↦ e.inv.h₀ i.1 ≫ E.f _) := by
    simp [PreZeroHypercover.presieve₀]
    refine le_antisymm ?_ ?_
    · rw [Presieve.ofArrows_le_iff]
      intro i
      exact .mk (⟨i, ⟨⟩⟩ : Σ (_ : F.I₀), Unit)
    · rw [Presieve.ofArrows_le_iff]
      simp
  rw [this]
  refine K.comp_mem_coverings (fun i ↦ E.f (e.inv.s₀ i)) ?_ (fun i (k : Unit) ↦ e.inv.h₀ i) ?_
  · rwa [← E.presieve₀_reindex (PreZeroHypercover.equivOfIso e.symm)] at hE
  · intro i
    rw [Presieve.ofArrows_pUnit]
    exact K.mem_coverings_of_isIso _

lemma _root_.CategoryTheory.PreZeroHypercover.mem_iff_of_iso {C : Type*} [Category* C]
    {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) :
    E.presieve₀ ∈ K X ↔ F.presieve₀ ∈ K X :=
  ⟨fun h ↦ PreZeroHypercover.mem_of_iso e h, fun h ↦ PreZeroHypercover.mem_of_iso e.symm h⟩

--lemma _root_.CategoryTheory.Precoverage.mem_of_asdf {C : Type*} [Category* C]
--    {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos]
--    {X : C} {R S : Presieve X} (h : R ∈ K X)
--    (h₁ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → ∃ (Z : C) (e : Z ≅ Y), S (e.hom ≫ f))
--    (h₂ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → ∃ (Z : C) (e : Z ≅ Y), R (e.hom ≫ f)) :
--    S ∈ K X := by
--  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
--  obtain ⟨σ, Z, g, rfl⟩ := S.exists_eq_ofArrows
--  choose W₁ a₁ ha₁ using fun i ↦ h₁ (f i) ⟨i⟩
--  have : Presieve.ofArrows Z g =
--      Presieve.ofArrows (fun (k : Σ (_ : ι), Unit) ↦ _)
--        (fun k ↦ (a₁ k.1).hom ≫ f _) := by
--    refine le_antisymm ?_ ?_
--    · rw [Presieve.ofArrows_le_iff]
--      intro j
--      obtain ⟨W, u, v⟩ := h₂ _ ⟨j⟩
--      refine Presieve.ofArrows.mk' ⟨v.idx, ⟨⟩⟩ ?_ ?_
--      · sorry
--      · sorry
--    · rw [Presieve.ofArrows_le_iff]
--      intro i
--      apply ha₁
--  sorry
--  --let E := R.preZeroHypercover
--  --let F := S.preZeroHypercover
--  ---- rw [← S.presieve₀_preZeroHypercover]
--  --have (i : E.I₀) := h₁ (E.f i) i.2
--  --choose W₁ a₁ ha₁ using fun i ↦ h₁ (E.f i) i.2
--  --choose W₂ a₂ ha₂ using fun i ↦ h₂ (F.f i) i.2
--  --let u (i : E.I₀) : F.I₀ := ⟨⟨_, _⟩, ha₁ i⟩
--  --let v (i : F.I₀) : E.I₀ := ⟨⟨_, _⟩, ha₂ i⟩
--  --have h1 (i : E.I₀) : v (u i) = i := by
--  --  simp [v, u]
--  --  dsimp [E, F, Presieve.preZeroHypercover]
--  --  ext
--  --  simp
--  --  sorry
--  --  sorry
--  --have : Function.Bijective u := by
--  --  refine ⟨?_, ?_⟩
--  --  · sorry
--  --  · intro j
--  --    sorry
--  ----let eq : E.I₀ ≃ F.I₀ :=
--  ----  Equiv.ofBijective _ _
--  --let e : E ≅ F :=
--  --  sorry
--  ----have : Presieve.ofArrows Z g =
--  ----    _ :=
--  ----  sorry
--  --sorry

lemma _root_.CategoryTheory.Presieve.map_functorPullback_of_forall_exists
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {X : C}
    (R : Presieve (F.obj X)) [F.Full]
    (H : ∀ ⦃Y : D⦄ (f : Y ⟶ F.obj X), ∃ (Z : C) (g : Z ⟶ X) (e : F.obj Z = Y),
      F.map g = eqToHom e ≫ f) :
    Presieve.map F (Presieve.functorPullback F R) = R := by
  refine le_antisymm ?_ ?_
  · rw [Presieve.map_le_iff_le_functorPullback]
  · intro Y f hf
    obtain ⟨Z, g, rfl, hg⟩ := H f
    rw [Presieve.map_iff]
    use Z, rfl, g
    simpa [Presieve.functorPullback_mem, hg, and_true]

attribute [ext] CategoryTheory.Comma
attribute [ext] CategoryTheory.MorphismProperty.Comma

/-- The affine pro-étale site embeds densely in the pro-étale site. The key ingredient
of the proof is the commutative algebra lemma `RingHom.WeaklyEtale.exists_indEtale_comp`. -/
instance isCoverDense_toProEt : (toProEt S).IsCoverDense (ProEt.topology S) := by
  wlog hS : ∃ R, S = Spec R generalizing S
  · let X (i : S.affineCover.I₀) : S.AffineProEt := .ofEtale (S.affineCover.f i)
    let f (i : S.affineCover.I₀) : (toProEt S).obj (X i) ⟶ .mk (𝟙 S) := Over.homMk (S.affineCover.f i)
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
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_locallyCoverDense]
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_isEquivalence]
      have heq : eR.functor.inducedTopology
          ((ProEt.topology S).over ((toProEt S).obj ((fun i ↦ X i) i))) =
            ProEt.topology _ := by
        rw [ProEt.topology_eq_inducedTopology]
        rw [ProEt.topology_eq_inducedTopology]
        dsimp
        ext U R
        refine ⟨?_, ?_⟩
        · intro hR
          simp [GrothendieckTopology.mem_over_iff] at hR
          sorry
        · sorry
        --rw [over_toGrothendieck_eq_toGrothendieck_comap_forget,
        --  ← Precoverage.toGrothendieck_comap_eq_inducedTopology]
        --· rw [ProEt.topology, ProEt.precoverage, ProEt.precoverage]
        --  simp_rw [← Precoverage.comap_comp]
        --  rfl
        --· intro U R hR
        --  simp at hR ⊢
        --  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
        --  rw [← E.presieve₀_map] at hR
        --  -- rw [← PreZeroHypercover.presieve₀_map]
        --  convert hR
        --  apply Presieve.map_functorPullback_of_forall_exists
        --  intro Y g
        --  refine ⟨.mk Y.hom.left, Over.homMk g.left.left (congr($(Over.w g).left)), ?_, ?_⟩
        --  · dsimp [eR]
        --    apply CategoryTheory.Comma.ext
        --    dsimp
        --    apply MorphismProperty.Comma.ext
        --    · dsimp
        --    · simp
        --    · simp
        --      exact Over.w Y.hom
        --    · simp
        --    · simp
        --      sorry
        --  · ext
        --    simp [eR]
        --    apply MorphismProperty.Comma.Hom.ext
        --    · simp
        --      rw [MorphismProperty.Comma.comp_left]
        --      simp
        --      rw [← Category.id_comp g.left.left]
        --      congr
        --      symm
        --      sorry
        --    · simp
        --  --refine le_antisymm ?_ ?_
          --· rw [Presieve.map_le_iff_le_functorPullback]
          --· intro A f hf
          --  -- have : f = eR.functor.map (eR.inverse.map f) := sorry
          --  rw [Presieve.map_iff]
          --  refine ⟨?_, ?_, ?_, ?_, ?_⟩
          --  · exact ProEt.mk A.hom.left
          --  · sorry
          --  · exact Over.homMk f.left.left sorry
          --  · sorry
          --  · sorry
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
    simp [g']
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

instance : HasPullbacks (AffineProEt S) :=
  sorry

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
