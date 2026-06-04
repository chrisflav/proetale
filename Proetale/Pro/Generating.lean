import Proetale.Pro.Basic
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import Proetale.Mathlib.CategoryTheory.Sites.PrecoverageGenerating
import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Hypercover.Saturate
import Mathlib.CategoryTheory.Sites.Finite

/-!
# Sheaf condition in pro-category when pullbacks exist

In this file we deduce an important special case of the material developed
in `Proetale/Pro.lean`: If pullbacks exist and the functor `F : C ⥤ D`
(think `D = Pro C`) preserves them, then, to apply the sheaf criterion,
it suffices to show that presieves (i.e. `0`-hypercovers) are relatively
presentable under `F`.
-/

universe t w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D)
variable {X : C} (R : Presieve X)
variable (A : Type*) [Category* A]

variable (B : Precoverage D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

structure PreZeroHypercover.RelativeLimitPresentation (J : Type*) [Category* J] {X : D}
    (E : PreZeroHypercover.{w} X) where
  pres : Limits.RelativeLimitPresentation J F X
  pres₀ : ∀ i : E.I₀, Limits.RelativeLimitPresentation J F (E.X i)
  f : ∀ i, (pres₀ i).Hom pres
  hf : ∀ i, (f i).map = E.f i

variable {F} in
@[simps]
def PreZeroHypercover.RelativeLimitPresentation.preZeroHypercover {J : Type*} [Category* J] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F J) (j : J) :
    PreZeroHypercover.{w} (pres.pres.diag.obj j) where
  I₀ := E.I₀
  X i := (pres.pres₀ i).diag.obj j
  f i := (pres.f i).natTrans.app j

section

variable [Limits.HasPullbacks C] [Limits.HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.pullback {X Y S : D} (f : X ⟶ S) (g : Y ⟶ S)
    (p : PullbackCone f g) (hp : IsLimit p) {J : Type*} [Category* J]
    (pX : RelativeLimitPresentation J F X) (pY : RelativeLimitPresentation J F Y)
    (pS : RelativeLimitPresentation J F S)
    (pf : pX.Hom pS) (pg : pY.Hom pS) (hf : pf.map = f) (hg : pg.map = g) :
    RelativeLimitPresentation J F p.pt where
  diag.obj j := Limits.pullback (pf.natTrans.app j) (pg.natTrans.app j)
  diag.map {i j} f := pullback.map _ _ _ _ (pX.diag.map f) (pY.diag.map f) (pS.diag.map f)
    (by simp) (by simp)
  π.app j := by
    refine (IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j))).lift
      (p.fst ≫ pX.π.app j) (p.snd ≫ pY.π.app j) ?_
    subst hf hg
    simpa using p.condition =≫ pS.π.app j
  π.naturality {i j} f := by
    subst hf hg
    apply ((IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j)))).hom_ext
    · have := pX.π.naturality f
      simp at this
      simp [← Functor.map_comp]
      simp [this]
    · have := pY.π.naturality f
      simp at this
      simp [← Functor.map_comp]
      simp [this]
  isLimit := by
    refine .mk ?_ ?_ ?_
    · intro s
      dsimp
      refine PullbackCone.IsLimit.lift hp ?_ ?_ ?_
      · let sX : Cone (pX.diag ⋙ F) :=
          { pt := s.pt
            π.app j := s.π.app j ≫ F.map (pullback.fst _ _)
            π.naturality i j f := by
              have := s.π.naturality f
              simp at this
              simp [this, ← Functor.map_comp] }
        exact pX.isLimit.lift sX
      · let sY : Cone (pY.diag ⋙ F) :=
          { pt := s.pt
            π.app j := s.π.app j ≫ F.map (pullback.snd _ _)
            π.naturality i j f := by
              have := s.π.naturality f
              simp at this
              simp [this, ← Functor.map_comp] }
        exact pY.isLimit.lift sY
      · subst hf hg
        apply pS.isLimit.hom_ext
        intro j
        simp [← Functor.map_comp, pullback.condition]
    · intro s j
      apply ((IsPullback.map F (.of_hasPullback (pf.natTrans.app j) (pg.natTrans.app j)))).hom_ext
      · simp
      · simp
    · intro s m hm
      apply PullbackCone.IsLimit.hom_ext hp
      · apply pX.isLimit.hom_ext
        intro j
        simpa using hm j =≫ F.map (pullback.fst _ _)
      · apply pY.isLimit.hom_ext
        intro j
        simpa using hm j =≫ F.map (pullback.snd _ _)

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.precomp
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {J K : Type*} [Category* J] [Category* K]
    {X : D} (pres : RelativeLimitPresentation J F X)
    (G : K ⥤ J) [G.Initial] :
    RelativeLimitPresentation K F X where
  diag := G ⋙ pres.diag
  π := (Functor.constCompWhiskeringLeftIso _ _).inv.app _ ≫
    Functor.whiskerLeft _ pres.π ≫ (Functor.associator _ _ _).inv
  isLimit := by
    refine IsLimit.postcomposeHomEquiv (Functor.associator _ _ _).symm _ ?_
    refine (Functor.Initial.isLimitExtendConeEquiv (G := pres.diag ⋙ F) G _) ?_
    refine IsLimit.equivOfNatIsoOfIso (Iso.refl _) _ _ ?_ pres.isLimit
    refine Cone.ext (.refl _) fun j ↦ ?_
    simpa using pres.π.naturality _

@[simps!]
noncomputable
def Limits.RelativeLimitPresentation.restrict
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [IsCofiltered J]
    [PreservesLimitsOfShape WalkingCospan F]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    RelativeLimitPresentation (Over j) F V :=
  haveI : CategoryTheory.IsConnected (Over j) := IsCofiltered.isConnected _
  RelativeLimitPresentation.pullback _ _ (F.map f) hg.flip.cone hg.flip.isLimit
    (pres.precomp (Over.forget j))
    (.self _)
    (.self _)
    { natTrans.app j := pres.diag.map j.hom
      natTrans.naturality := by simp [← Functor.map_comp] }
    (.self f)
    (by
      apply ((RelativeLimitPresentation.self (F := F) (J := Over j) _)).isLimit.hom_ext
      intro k
      rw [RelativeLimitPresentation.Hom.map_π]
      simpa using (pres.π.naturality k.hom).symm)
    (by simp)

@[simps]
noncomputable
def Limits.RelativeLimitPresentation.restrictHom
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [PreservesLimitsOfShape WalkingCospan F]
    [IsCofiltered J]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    (pres.restrict _ _ _ _ hg).Hom (pres.precomp (Over.forget _)) where
  natTrans.app j := pullback.fst _ _

@[simp]
lemma Limits.RelativeLimitPresentation.restrictHom_map
    {C D : Type*} [Category* C] [HasPullbacks C] [Category* D] {F : C ⥤ D} {J : Type*} [Category* J]
    {X : D} (pres : RelativeLimitPresentation J F X)
    [PreservesLimitsOfShape WalkingCospan F]
    [IsCofiltered J]
    {j : J} {U : C} (f : U ⟶ pres.diag.obj j)
    (V : D) (fst : V ⟶ F.obj U) (snd : V ⟶ X)
    (hg : IsPullback fst snd (F.map f) (pres.π.app j)) :
    (pres.restrictHom _ _ _ _ hg).map = snd := by
  refine (pres.precomp (Over.forget j)).isLimit.hom_ext ?_
  intro i
  simp only [RelativeLimitPresentation.precomp_diag, Functor.comp_obj, Over.forget_obj,
    RelativeLimitPresentation.Hom.map_π, Functor.const_obj_obj,
    RelativeLimitPresentation.restrict_diag_obj, RelativeLimitPresentation.restrict_π_app,
    RelativeLimitPresentation.restrictHom_natTrans_app]
  simp

@[simps]
noncomputable
def PreZeroHypercover.RelativeLimitPresentation.onePullbacks {J : Type*} [Category* J] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F J) :
    E.toPreOneHypercover.RelativeLimitPresentation J F where
  __ := pres
  pres₁ {i j} k := .pullback _ _ _ _ (limit.isLimit _) (pres.pres₀ i) (pres.pres₀ j) pres.pres
    (pres.f i) (pres.f j) (pres.hf i) (pres.hf j)
  p₁ k :=
    { natTrans.app j := pullback.fst _ _
      natTrans.naturality i j f := by simp }
  p₂ k :=
    { natTrans.app j := pullback.snd _ _
      natTrans.naturality i j f := by simp }
  hp₁ {i j} k := (pres.pres₀ i).isLimit.hom_ext (by simp)
  hp₂ {i j} k := (pres.pres₀ j).isLimit.hom_ext (by simp)
  w k := by ext; simp [pullback.condition]

noncomputable
def PreZeroHypercover.RelativeLimitPresentation.preOneHypercoverOnePullbacksIso
    {I : Type*} [Category* I] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F I) (a : I) :
    pres.onePullbacks.preOneHypercover a ≅ (pres.preZeroHypercover a).toPreOneHypercover :=
  Iso.refl _

@[simp]
lemma GrothendieckTopology.toGrothendieck_toPrecoverage {C : Type*} [Category* C]
    (J : GrothendieckTopology C) :
    J.toPrecoverage.toGrothendieck = J := by
  refine le_antisymm (toGrothendieck_toPrecoverage_le J) ?_
  intro X S hS
  rw [← S.generate_sieve]
  refine J.toPrecoverage.generate_mem_toGrothendieck ?_
  simpa [GrothendieckTopology.mem_toPrecoverage_iff]

def PreZeroHypercover.RelativeLimitPresentation.sieve₁_mem
    {I : Type*} [Category* I] {X : D}
    {E : PreZeroHypercover.{w} X} (pres : E.RelativeLimitPresentation F I)
    (h : ∀ j, (pres.preZeroHypercover j).sieve₀ ∈ J (pres.pres.diag.obj j))
    {i j : E.I₀} (a : I)
    (W : C) (p₁ : W ⟶ (pres.pres₀ i).diag.obj a)
    (p₂ : W ⟶ (pres.pres₀ j).diag.obj a) (w : p₁ ≫ (pres.f i).natTrans.app a =
      p₂ ≫ (pres.f j).natTrans.app a) :
    (pres.onePullbacks.preOneHypercover a).sieve₁ p₁ p₂ ∈ J W := by
  let E' : Precoverage.ZeroHypercover J.toPrecoverage _ :=
    ⟨pres.preZeroHypercover a, h _⟩
  simpa using (E'.toOneHypercover).mem₁ _ _ p₁ p₂ w

def PreZeroHypercover.IsRelativelyPresentable {X : D} (E : PreZeroHypercover.{w} X) : Prop :=
  ∃ (I : Type t) (_ : SmallCategory I) (_ : IsCofiltered I)
    (pres : E.RelativeLimitPresentation F I),
    ∀ j, (pres.preZeroHypercover j).sieve₀ ∈ J (pres.pres.diag.obj j)

lemma PreZeroHypercover.IsRelativelyPresentable.toPreOneHypercover {X : D} (E : PreZeroHypercover X)
    (h : PreZeroHypercover.IsRelativelyPresentable.{w} F J E) [E.Finite] :
    PreOneHypercover.IsRelativelyPresentable.{w} F J E.toPreOneHypercover := by
  obtain ⟨I, _, _, pres, hpres⟩ := h
  refine ⟨I, inferInstance, inferInstance, pres.onePullbacks, ?_⟩
  intro a
  refine ⟨hpres _, fun {i j} W p₁ p₂ w ↦ ?_⟩
  exact PreZeroHypercover.RelativeLimitPresentation.sieve₁_mem _ _ _ hpres _ _ _ _ w

end

def Precoverage.relativelyPresentable : Precoverage D where
  coverings _ R := PreZeroHypercover.IsRelativelyPresentable.{w} F J R.preZeroHypercover

lemma Presieve.finite_uncurry_iff {X : C} (R : Presieve X) :
    R.uncurry.Finite ↔ R.preZeroHypercover.Finite :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.finite₀⟩

lemma PreOneHypercover.isSheafFor_iff_isSheafFor_comp_coyoneda {X : C} {P : Cᵒᵖ ⥤ A}
    {E : PreOneHypercover X} :
    E.IsSheafFor P ↔ ∀ (M : A), E.IsSheafFor (P ⋙ coyoneda.obj (.op M)) :=
  ⟨fun h M ↦ ⟨Multifork.isLimitMapOfPreserves _ (coyoneda.obj (.op M)) h.some⟩,
    fun h ↦ ⟨coyonedaJointlyReflectsLimits _ _
      fun _ ↦ (Multifork.isLimitMapEquiv _ _).symm (h _).some⟩⟩

lemma PreZeroHypercover.isSheafFor_saturate_iff {X : C} {E : PreZeroHypercover X} {P : Cᵒᵖ ⥤ A} :
    E.saturate.IsSheafFor P ↔
      ∀ (M : A), Presieve.IsSheafFor (P ⋙ coyoneda.obj (.op M)) E.presieve₀ := by
  rw [PreOneHypercover.isSheafFor_iff_isSheafFor_comp_coyoneda]
  simp_rw [PreZeroHypercover.isLimit_saturate_type_iff]

lemma Precoverage.Generates.isSheaf_iff_preZeroHypercover (H : B.Generates K) (P : Dᵒᵖ ⥤ A) :
    Presheaf.IsSheaf K P ↔
      ∀ ⦃X : D⦄ (R : Presieve X), R ∈ B X → R.preZeroHypercover.saturate.IsSheafFor P := by
  simp [H.isSheaf_iff, PreZeroHypercover.isSheafFor_saturate_iff]

namespace Presheaf

variable [HasPullbacks C] [HasPullbacks D] [PreservesLimitsOfShape WalkingCospan F]

variable {A : Type*} [Category.{t} A]

/--
Suppose `C` and `D` have pullbacks and `F : C ⥤ D` preserves them. If `P` is a presheaf on `D` that

1. is a sheaf when restricted to `C`, and
2. preserves filtered colimits,

then `P` is a sheaf for any topology that is generated by finite, relatively presentable presieves,
i.e., cofiltered limits of covering presieves in `C`.

In our application to the affine pro-étale site, `B` will be the precoverage
given by finite Zariski coverings and single morphism coverings given by faithfully flat, pro-étale
morphisms between affine schemes. Both of these are ind-presentable wrt. to the
inclusion of the affine étale site into the affine pro-étale site.
-/
theorem isSheaf_of_generates_of_isRelativelyPresentable (P : Dᵒᵖ ⥤ A) (h : IsSheaf J (F.op ⋙ P))
    [PreservesFilteredColimitsOfSize.{w, w} P] [HasFilteredColimitsOfSize.{w, w} A]
    [AB5OfSize.{w} A] (H : B.Generates K)
    (h₁ : B ≤ Precoverage.relativelyPresentable.{w} F J)
    (h₂ : B ≤ Precoverage.finite _) :
    IsSheaf K P := by
  rw [H.isSheaf_iff_preZeroHypercover (A := A)]
  intro X R hR
  dsimp [PreOneHypercover.IsSheafFor]
  rw [(R.preZeroHypercover.isLimitSaturateEquivOfHasPullbacks _).nonempty_congr]
  have : R.preZeroHypercover.Finite := by
    rw [← Presieve.finite_uncurry_iff]
    exact h₂ _ hR
  apply PreOneHypercover.IsSheafFor.of_preservesFilteredColimitsOfSize.{_, w} J _ (F := F) h
    R.preZeroHypercover.toPreOneHypercover _
  exact (h₁ _ hR).toPreOneHypercover _ _ _

end Presheaf

end CategoryTheory
