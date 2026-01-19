/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Topology.Comparison.Etale
import Proetale.Topology.Coherent.Affine
import Proetale.Pro.Basic

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory

@[simps! obj_left obj_hom map_left]
def CostructuredArrow.lift {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C)
    {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    J ⥤ CostructuredArrow L X where
  obj j := .mk (s.app j)
  map {i j} f := CostructuredArrow.homMk (F.map f) (by simp [← Functor.comp_map])

@[simp]
lemma CostructuredArrow.lift_forget {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : J ⥤ C) {L : C ⥤ D} {X : D} (s : F ⋙ L ⟶ (Functor.const _).obj X) :
    lift F s ⋙ CategoryTheory.CostructuredArrow.proj _ _ = F :=
  rfl

/-- The assumption on `X` is in particular satisfied if `X` is finitely presentable
and `J` is a small filtered category. -/
lemma exists_hom_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

lemma exists_eq_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

lemma exists_eq_of_preservesColimit_coyoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a := by
  obtain ⟨j, u, v, heq⟩ := exists_eq_of_preservesColimit_coyoneda hc f g h
  use IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v
  rw [Functor.map_comp, reassoc_of% heq, ← Functor.map_comp, ← IsFiltered.coeq_condition]
  simp

lemma IsFinitelyPresentable.exists_eq_of_isColimit_self {C : Type*} [Category* C]
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D}
    (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a :=
  exists_eq_of_preservesColimit_coyoneda_self hc _ _ h

section

-- `F` is a presheaf
-- `L` is a continuous functor
variable {C D E A : Type*} [Category* C] [Category* D] [Category* A] [Category* E]
    (L : C ⥤ D) (F : C ⥤ A) [∀ (F : C ⥤ A), L.HasPointwiseLeftKanExtension F]
    (R : E ⥤ D)

variable {J : Type w} [SmallCategory J] (K : J ⥤ C) [IsFiltered J]
variable {c : Cocone (K ⋙ L)} (hc : IsColimit c)

-- The assumption `∀ X, IsFinitelyPresentable (L.obj X)` can (and should)
-- be replaced by something like `IsFinitelyPresentableFor (L.obj X) D`
include hc in
lemma final_costructuredArrowLift_of_isFinitelyPresentable
    [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful] :
    (CostructuredArrow.lift _ c.ι).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · intro d
    obtain ⟨j, p, hp⟩ := exists_hom_of_preservesColimit_coyoneda hc d.hom
    use j
    exact ⟨CostructuredArrow.homMk (L.preimage p)⟩
  · intro d j s s'
    obtain ⟨k, a, heq⟩ := exists_eq_of_preservesColimit_coyoneda_self hc (L.map s.left)
        (L.map s'.left) <| by
      trans d.hom
      · simpa using CostructuredArrow.w s
      · simpa using (CostructuredArrow.w s').symm
    refine ⟨k, a, ?_⟩
    ext
    exact L.map_injective (by simpa using heq)

variable [∀ X : C, PreservesColimit (K ⋙ L) (coyoneda.obj (.op <| L.obj X))] [L.Full] [L.Faithful]

include hc in
lemma hasColimit_of_isFinitelyPresentable : HasColimit (K ⋙ F) := by
  rw [← CostructuredArrow.lift_forget _ c.ι]
  suffices HasColimit (CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt ⋙ F) by
    exact hasColimit_of_iso (Functor.associator _ _ _)
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  exact Functor.Final.comp_hasColimit _

variable (c) in
@[simps]
noncomputable def cocone : Cocone (K ⋙ F) where
  pt := (L.leftKanExtension F).obj c.pt
  ι :=
    Functor.whiskerLeft K (L.leftKanExtensionUnit F) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight c.ι _ ≫
    (Functor.constComp _ _ _).hom

include L F

noncomputable def isColimitCocone : IsColimit (cocone L F K c) := by
  have : HasColimit (K ⋙ F) := hasColimit_of_isFinitelyPresentable _ _ _ hc
  have : HasColimit ((CostructuredArrow.lift K c.ι ⋙ CostructuredArrow.proj L c.pt) ⋙ F) := this
  have := final_costructuredArrowLift_of_isFinitelyPresentable _ _ hc
  let e : colimit (K ⋙ F) ⟶ _ :=
    (HasColimit.isoOfNatIso
      (Functor.associator (CostructuredArrow.lift K c.ι) (CostructuredArrow.proj L c.pt) _)).hom ≫
      colimit.pre _ _ ≫
      (Functor.leftKanExtensionObjIsoColimit L F c.pt).inv
  have heq : e = colimit.desc _ (cocone L F K c) :=
    colimit.hom_ext fun j ↦ by simp [e]
  suffices IsIso (colimit.desc _ (cocone L F K c)) by
    convert IsColimit.ofPointIso (colimit.isColimit <| K ⋙ F)
    assumption
  rw [← heq]
  infer_instance

instance : PreservesColimit (K ⋙ L) (L.leftKanExtension F) := by
  constructor
  intro c hc
  let natIso : K ⋙ L ⋙ L.leftKanExtension F ≅ K ⋙ F :=
    Functor.isoWhiskerLeft K (asIso <| (L.lanAdjunction A).unit.app F).symm
  refine ⟨?_⟩
  refine IsColimit.equivOfNatIsoOfIso natIso.symm (cocone L F K c)
      ((L.leftKanExtension F).mapCocone c) ?_ ?_
  · refine Cocones.ext (Iso.refl _) ?_
    intro j
    simp [natIso]
    rfl
  · exact isColimitCocone _ _ _ hc

-- `B = AffEt / S ᵒᵖ`
-- `T` = inclusion into `E = ProAffEt / S ᵒᵖ`
-- `S` = inclusion into `C = Et / S ᵒᵖ`
variable {B : Type*} [Category B] (T : B ⥤ E) (S : B ⥤ C)

-- GOAL under some additional assumptions on `R`
instance [PreservesFilteredColimitsOfSize.{w, w} R]
    (h : ∀ (X : E), ObjectProperty.ind.{w} T.essImage X) :
    PreservesFilteredColimitsOfSize.{w, w} (R ⋙ L.leftKanExtension F) := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  have (j : J) : ObjectProperty.ind.{w} T.essImage (K.obj j) := h _
  sorry

end

section

variable {C D E A : Type*} [Category* C] [Category* D] [Category* A] [Category* E]
    (L : C ⥤ D) [∀ (F : Cᵒᵖ ⥤ A), L.op.HasPointwiseLeftKanExtension F]
    (R : E ⥤ D)

variable
  (τC : GrothendieckTopology C)
  (τD : GrothendieckTopology D)
  (τE : GrothendieckTopology E)
  (F : Sheaf τC A)

/-- The presheaf pullback is a sheaf when restricted to the subcategory `E`. -/
lemma isSheaf_comp_leftKanExtension :
    Presheaf.IsSheaf τE (R.op ⋙ L.op.leftKanExtension F.val) :=
  sorry

end

variable {C D : Type*} [Category* C] [Category D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : C ⥤ D) (R : D ⥤ C)
  {A : Type*} [Category A]

@[upstreamed mathlib 33932]
instance : (⊤ : MorphismProperty C).HasOfPostcompProperty ⊤ where
  of_postcomp _ _ _ _ := trivial

@[simps]
def Adjunction.sheaf [L.IsContinuous J K] [R.IsContinuous K J] (adj : L ⊣ R) :
    L.sheafPushforwardContinuous A J K ⊣ R.sheafPushforwardContinuous A K J where
  unit.app F := ⟨(adj.op.whiskerLeft A).unit.app F.val⟩
  counit.app F := ⟨(adj.op.whiskerLeft A).counit.app F.val⟩
  right_triangle_components F := by
    ext1
    exact (adj.op.whiskerLeft A).right_triangle_components F.val
  left_triangle_components F := by
    ext1
    exact (adj.op.whiskerLeft A).left_triangle_components F.val

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

section

/-
`C = Et / S`
`D = ProEt / S`
`E = AffProEt / S`
-/
variable {C D E : Type*}
  [Category* C] [Category* D] [Category* E]
  (L : C ⥤ D) (R : E ⥤ D)
  (J : GrothendieckTopology C)
  (K : GrothendieckTopology D)
  (M : GrothendieckTopology E)
  [L.IsContinuous J K] [R.IsContinuous M K]
  {I : Type*} [Category* I]
  {X : E} (pres : RelativeLimitPresentation I L (R.obj X))
  {A : Type*} [Category* A] (F : Sheaf J A)
  [(L.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasBinaryProducts D]

noncomputable def cocone' : Cocone (pres.diag.op ⋙ F.val) where
  pt := ((L.sheafPullback A J K).obj F).val.obj (.op <| R.obj X)
  ι := Functor.whiskerLeft _ (((L.sheafAdjunctionContinuous A J K)).unit.app F).val ≫
    Functor.whiskerRight pres.cone.op.ι _ ≫
    (Functor.constComp _ _ _).hom

end

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

/-- An object of the pro-étale site of `S` is pro-affine, if it can be written
as `limᵢ (Spec Aᵢ)` where `Spec Aᵢ` is an étale `S`-scheme. -/
def ProEt.proAffine (S : Scheme.{u}) : ObjectProperty S.ProEt :=
  fun X ↦ ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J),
    Nonempty (RelativeLimitPresentation J (AffineEtale.Spec S ⋙ S.toProEtale) X)

/-- The pro-étale affine site is the full subcategory of the pro-étale site where every
object can be written as a cofiltered limit of affine étale schemes over `S`. -/
def AffineProEt (S : Scheme.{u}) : Type (u + 1) :=
  (ProEt.proAffine S).FullSubcategory

variable (S : Scheme.{u})
variable (A : Type*) [Category A]

noncomputable instance : Category S.AffineProEt :=
  inferInstanceAs <| Category <| ObjectProperty.FullSubcategory _

namespace AffineProEt

/-- The inclusion of the affine pro-étale site into the pro-étale site. -/
def toProEt (S : Scheme.{u}) : S.AffineProEt ⥤ S.ProEt :=
  (ProEt.proAffine S).ι

instance : (toProEt S).Full := inferInstanceAs <| (ProEt.proAffine S).ι.Full
instance : (toProEt S).Faithful := inferInstanceAs <| (ProEt.proAffine S).ι.Faithful

instance : (toProEt S).LocallyCoverDense (ProEt.topology S) :=
  sorry

def topology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.topology S)

instance : (toProEt S).IsContinuous (topology S) (ProEt.topology S) :=
  sorry

/-- The restriction of sheafs on the pro-étale site to sheaf on the affine pro-étale site. -/
noncomputable
def sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (AffineProEt.topology S) A :=
  (toProEt S).sheafPushforwardContinuous _ _ _

instance : HasPullbacks (AffineProEt S) :=
  sorry

variable {S} in
noncomputable def singleCover {X Y : AffineProEt S} (f : X ⟶ Y) [Surjective f.hom.left] :
    (topology S).OneHypercover Y where
  I₀ := PUnit
  X _ := X
  f _ := f
  I₁ _ _ := PUnit
  Y _ _ _ := pullback f f
  p₁ _ _ _ := pullback.fst f f
  p₂ _ _ _ := pullback.snd f f
  w _ _ _ := pullback.condition
  mem₀ := sorry
  mem₁ := sorry

def surjections : (AffineProEt.topology S).OneHypercoverFamily :=
  fun X E ↦
    ∃ (Y : AffineProEt S) (f : Y ⟶ X) (_ : Surjective f.hom.left), E = singleCover f

end AffineProEt

noncomputable def ProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.ProEt ⥤ S.ProEt :=
  MorphismProperty.Over.pullback _ _ f

noncomputable def AffineProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.AffineProEt ⥤ S.AffineProEt :=
  ObjectProperty.lift _ (AffineProEt.toProEt _ ⋙ ProEt.baseChange f) sorry

/-- The inclusion of the affine étale site into the affine pro-étale site. -/
noncomputable def AffineEtale.toAffineProEt (S : Scheme.{u}) :
    S.AffineEtale ⥤ S.AffineProEt :=
  ObjectProperty.lift _ (AffineEtale.Spec S ⋙ S.toProEtale) <| fun _ ↦
    ⟨PUnit, inferInstance, inferInstance, ⟨.self _⟩⟩

/-- The topology on the affine pro-étale site is generated by limits
of `1`-hypercovers in the affine étale site. -/
instance :
    (GrothendieckTopology.oneHypercoverRelativelyRepresentable.{u}
      (AffineEtale.toAffineProEt S) (Type u)
      (AffineEtale.topology S) (AffineProEt.topology S)).IsGenerating :=
  sorry

variable [(ProEt.sheafPushforward S A).IsRightAdjoint]

variable {J : Type*} [Category* J] [IsCofiltered J]
  [HasColimitsOfShape Jᵒᵖ A]
  {D : J ⥤ S.AffineEtale}
  (c : Cone (D ⋙ AffineEtale.Spec S ⋙ S.toProEtale))
  (hc : IsLimit c)

noncomputable
def cocone (F : Sheaf (smallEtaleTopology S) A) :
    Cocone ((D ⋙ AffineEtale.Spec S).op ⋙ F.val) where
  pt := ((ProEt.sheafPullback S A).obj F).val.obj (Opposite.op c.pt)
  ι := Functor.whiskerLeft _ (((ProEt.sheafAdjunction S A).unit.app F).val) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight c.op.ι _ ≫
    (Functor.constComp _ _ _).hom

noncomputable
def map (F : Sheaf (smallEtaleTopology S) A) :
    colimit ((D ⋙ AffineEtale.Spec S).op ⋙ F.val) ⟶
      ((ProEt.sheafPullback S A).obj F).val.obj (Opposite.op c.pt) :=
  colimit.desc _ (cocone S A _ _)

noncomputable
def vertLeft (F : Sheaf (smallEtaleTopology S) A)
    {T : Scheme.{u}} (f : T ⟶ S) :
    colimit ((D ⋙ AffineEtale.Spec S).op ⋙ F.val) ⟶
      colimit ((D ⋙ AffineEtale.Spec S ⋙ Over.pullback _ _ f).op ⋙
        ((smallPullback f _ _).obj F).val) :=
  colim.map
    { app j := by
        dsimp
        sorry
      naturality := sorry }

--def vertLeft (F : Sheaf (smallEtaleTopology S) A) :
--    colimit ((D ⋙ AffineEtale.Spec S).op ⋙ F.val) ≅
--      colimit ((Over.iteratedLift (D ⋙ AffineEtale.Spec S) _ _).op ⋙ _) :=
--  sorry

lemma isIso_map (F : Sheaf (smallEtaleTopology S) A) :
    IsIso (map S _ c F) := by
  wlog h : IsAffine S
  · -- inverse limit of affine schemes
    have : IsAffine c.pt.left := sorry
    sorry
  sorry

lemma foobazsdf {J : Type*} [Category* J] [IsCofiltered J]
    [HasColimitsOfShape Jᵒᵖ A]
    (X : S.ProEt)
    (pres : RelativeLimitPresentation J (AffineEtale.Spec S ⋙ S.toProEtale) X)
    (F : Sheaf (smallEtaleTopology S) A) :
    PreservesColimit (pres.diag ⋙ AffineEtale.Spec S ⋙ S.toProEtale).op
      ((ProEt.sheafPullback S A).obj F).val := by
  have : HasLimit (pres.diag ⋙ AffineEtale.Spec S ⋙ S.toProEtale) := ⟨_, pres.isLimit⟩
  rw [preservesColimit_iff_isIso_post]
  let res : Sheaf (ProEt.topology S) A ⥤ Sheaf (ProEt.topology X.left) A :=
    smallSheafRestrict X.hom _ _ X.prop
  sorry

instance
    (F : Sheaf (smallEtaleTopology S) A)
    {J : Type*} [Category* J] [Small.{u + 1} J] [IsFiltered J]
    [HasColimitsOfShape J A]
    (K : J ⥤ S.AffineProEtᵒᵖ)
    [HasColimit K] :
    PreservesColimit K
      ((ProEt.sheafPullback S A ⋙ AffineProEt.sheafPushforward S A).obj F).val := by
  sorry

instance preservesFilteredColimits_sheafPullback_obj (F : Sheaf (smallEtaleTopology S) A) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((ProEt.sheafPullback S A ⋙ AffineProEt.sheafPushforward S A).obj F).val := by
  sorry

section Presheaf

variable [∀ (F : S.Etaleᵒᵖ ⥤ A), S.toProEtale.op.HasLeftKanExtension F]

lemma preservesFilteredColimits_lan_toProEtale (F : S.Etaleᵒᵖ ⥤ A) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt S).op ⋙ S.toProEtale.op.leftKanExtension F) :=
  sorry

end Presheaf

end AlgebraicGeometry.Scheme
