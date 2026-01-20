import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

universe w

namespace CategoryTheory

variable {I J : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]

def Pi.eqToEquivalenceCompIso {I : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]
    (F : ∀ i, C i ⥤ D i) {i j : I} (h : i = j) :
    (eqToEquivalence C h).functor ⋙ F j ≅ F i ⋙ (eqToEquivalence D h).functor := by
  subst h
  exact Iso.refl _

@[reassoc (attr := simp)]
lemma Pi.eqToEquivalenceCompIso_naturality {I : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] (F : ∀ i, C i ⥤ D i) {i j : I} (h : j = i) (a b : C j)
    (f : a ⟶ b) :
    (F i).map ((eqToEquivalence C h).functor.map f) ≫
      (eqToEquivalenceCompIso C D F h).hom.app b =
    (eqToEquivalenceCompIso C D F h).hom.app a ≫
      (eqToEquivalence D h).functor.map ((F j).map f) :=
  (eqToEquivalenceCompIso _ _ _ h).hom.naturality _

def Functor.piCompEval {I : Type*} {C D : I → Type*} [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] (F : ∀ i, C i ⥤ D i) (i : I) :
    Functor.pi F ⋙ Pi.eval _ i ≅ Pi.eval _ i ⋙ F i :=
  Iso.refl _

noncomputable def Pi.equivalenceOfEquivCompEvalIso {I J : Type*} (C : I → Type*)
    [∀ i, Category* (C i)] (e : J ≃ I) (j : J) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Pi.eval C (e j) ≅ Pi.eval _ j :=
  (Functor.pi'CompEval _ _) ≪≫
    Functor.isoWhiskerLeft _ (Pi.eqToEquivalenceFunctorIso _ _ _) ≪≫
    Pi.evalCompEqToEquivalenceFunctor (fun j ↦ C (e j)) (show e.symm (e j) = j by simp)

noncomputable def Pi.equivalenceOfEquivCompEvalIso' {I J : Type*} (C : I → Type*)
    [∀ i, Category* (C i)] (e : J ≃ I) (i : I) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Pi.eval C i ≅
      Pi.eval _ (e.symm i) ⋙ (Pi.eqToEquivalence _ <| by simp).functor :=
  Iso.refl _

@[simp]
lemma Pi.eqToEquivalence_rfl {I : Type*} (C : I → Type*) [∀ i, Category* (C i)] (i : I) :
    Pi.eqToEquivalence C (refl i) = .refl :=
  rfl

attribute [-simp] Pi.equivalenceOfEquiv_functor Pi.equivalenceOfEquiv_inverse

noncomputable
def Pi.equivalenceOfEquivCompPiIso {I J : Type*} (C D : I → Type*) [∀ i, Category* (C i)]
    [∀ i, Category* (D i)]
    (e : J ≃ I) (F : ∀ i, C i ⥤ D i) :
    (Pi.equivalenceOfEquiv C e).functor ⋙ Functor.pi F ≅
      Functor.pi (fun j ↦ F (e j)) ⋙ (Pi.equivalenceOfEquiv D e).functor :=
  NatIso.ofComponents
    (fun a ↦ isoMk fun i ↦ (Pi.eqToEquivalenceCompIso _ _ F _).app (a (e.symm i))) <| by
    intro a b f
    ext i
    simp [Functor.pi, equivalenceOfEquiv]

namespace Limits

variable (ι : Type*) {C : Type*} [Category* C]

@[simps]
noncomputable def Pi.functor [HasProductsOfShape ι C] : (ι → C) ⥤ C where
  obj f := ∏ᶜ f
  map {f g} t := Pi.map t

variable {ι}
variable [HasProductsOfShape ι C] {J : ι → Type*} [∀ i, Category* (J i)]

@[simps!]
noncomputable def Pi.constCompPiIsoConst (X : ι → C) :
    Functor.pi (fun i ↦ (Functor.const (J i)).obj (X i)) ⋙
      Pi.functor ι ≅ (Functor.const _).obj (∏ᶜ X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[simps]
noncomputable
def coconePointwiseProduct' {F : ∀ i, J i ⥤ C} (c : ∀ i, (Cocone (F i))) :
    Cocone (Functor.pi F ⋙ Pi.functor _) where
  pt := ∏ᶜ fun i ↦ (c i).pt
  ι := Functor.whiskerRight (NatTrans.pi fun i ↦ (c i).ι) _ ≫ (Pi.constCompPiIsoConst _).hom

noncomputable
def Pi.equivalenceOfEquivCompPiFunctorIso (F : ∀ i, J i ⥤ C) {ι' : Type*} (f : ι' ≃ ι)
    [HasProductsOfShape ι' C] :
    (Pi.equivalenceOfEquiv (fun j ↦ J j) f).inverse ⋙ Functor.pi (fun j ↦ F (f j)) ⋙ Pi.functor ι' ≅
      Functor.pi F ⋙ Pi.functor ι :=
  (NatIso.ofComponents
    fun a ↦ (Pi.whiskerEquiv f (fun j ↦ (Iso.refl ((F (f j)).obj <| a (f j))))).symm).symm

class IsIPCOfShape (ι : Type*) (C : Type*) [Category* C] [HasProductsOfShape ι C] : Prop where
  nonempty_isColimit ⦃J : ι → Type w⦄ [∀ i, SmallCategory (J i)]
    [∀ i, IsFiltered (J i)] ⦃F : ∀ i, J i ⥤ C⦄ ⦃c : ∀ i, Cocone (F i)⦄ :
    (∀ i, IsColimit (c i)) → Nonempty (IsColimit (coconePointwiseProduct' c))

lemma IsIPCOfShape.of_equiv {ι' : Type*} [HasProductsOfShape ι' C] [IsIPCOfShape.{w} ι C]
    (e : ι ≃ ι') :
    IsIPCOfShape.{w} ι' C where
  nonempty_isColimit J _ _ F c hc := by
    obtain ⟨h⟩ := nonempty_isColimit fun i : ι ↦ hc (e i)
    constructor
    apply IsColimit.equivOfNatIsoOfIso _ _ _ _ <| h.whiskerEquivalence (Pi.equivalenceOfEquiv J e).symm
    · exact (Pi.equivalenceOfEquivCompPiFunctorIso F e)
    · -- Without the double `symm`, one runs into (hard) DTT hell
      symm
      refine Cocones.ext ?_ ?_
      · exact (Pi.whiskerEquiv e fun _ ↦ Iso.refl _).symm
      · intro a
        apply Pi.hom_ext
        simp [Pi.equivalenceOfEquivCompPiFunctorIso, Pi.equivalenceOfEquiv, Functor.pi]

noncomputable
def isColimitCoconePointwiseProduct' [IsIPCOfShape.{w} ι C]
    {J : ι → Type w} [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)] {F : ∀ i, J i ⥤ C}
    {c : ∀ i, (Cocone (F i))} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (coconePointwiseProduct' c) :=
  (IsIPCOfShape.nonempty_isColimit hc).some

end Limits

open Limits

variable {C D : Type*} [Category C] [Category D]

lemma ObjectProperty.ind_iff_of_equivalence (e : C ≌ D) (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] (X : D) :
    ObjectProperty.ind.{w} P X ↔
      ObjectProperty.ind.{w} (P.inverseImage e.functor) (e.inverse.obj X) := by
  dsimp only [ObjectProperty.ind]
  congr!
  refine ⟨fun ⟨pres, h⟩ ↦ ?_, fun ⟨pres, h⟩ ↦ ?_⟩
  · refine ⟨pres.map e.inverse, ?_⟩
    intro i
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      ObjectProperty.prop_inverseImage_iff]
    exact P.prop_of_iso ((e.counitIso.app _).symm) (h i)
  · refine ⟨.ofIso (pres.map e.functor) (e.counitIso.app X), fun i ↦ h i⟩

namespace ObjectProperty

lemma ind_inverseImage_le
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D)
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

lemma ind_inverseImage_eq_of_isEquivalence
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [F.IsEquivalence] :
    ind.{w} (P.inverseImage F) = (ind.{w} P).inverseImage F := by
  refine le_antisymm (ind_inverseImage_le _ _) fun X ⟨J, _, _, pres, h⟩ ↦ ?_
  refine ⟨J, ‹_›, ‹_›, .ofIso (pres.map F.asEquivalence.inverse) ?_, fun j ↦ ?_⟩
  · exact (F.asEquivalence.unitIso.app X).symm
  · exact P.prop_of_iso ((F.asEquivalence.counitIso.app _).symm) (h j)

variable (P : ObjectProperty C)

section Products

lemma ind_pi_of_ind {ι : Type w} [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C]
    {X : ι → C} (hc : ∀ i, ind.{w} P (X i)) :
    ind.{w} P (∏ᶜ X) := by
  choose J _ _ pres hpres using hc
  use ∀ j, J j, inferInstance, inferInstance
  refine ⟨?_, ?_⟩
  · refine { diag := ?_
             ι := ?_
             isColimit := ?_  }
    · exact Functor.pi (fun i ↦ (pres i).diag) ⋙ Pi.functor _
    · exact (coconePointwiseProduct' fun i ↦ (pres i).cocone).ι
    · exact isColimitCoconePointwiseProduct' fun i ↦ (pres i).isColimit
  · intro i
    exact P.prop_limit _ fun a ↦ hpres a.1 _

instance {ι : Type*} [Small.{w} ι] [P.IsClosedUnderLimitsOfShape (Discrete ι)]
    [HasProductsOfShape ι C] [IsIPCOfShape.{w} ι C] :
    (ind.{w} P).IsClosedUnderLimitsOfShape (Discrete ι) := by
  refine .mk' fun X ⟨Y, h⟩ ↦ ?_
  let e := equivShrink ι
  have : HasProductsOfShape (Shrink.{w} ι) C :=
    hasLimitsOfShape_of_equivalence (Discrete.equivalence e)
  have : IsIPCOfShape.{w} (Shrink.{w} ι) C := .of_equiv e
  have : P.IsClosedUnderLimitsOfShape (Discrete (Shrink.{w} ι)) :=
    .of_equivalence (Discrete.equivalence e)
  let iso : limit Y ≅ ∏ᶜ fun i ↦ Y.obj ⟨e.symm i⟩ :=
    (Pi.isoLimit _).symm ≪≫ (Pi.reindex e.symm _).symm
  rw [(ind.{w} P).prop_iff_of_iso iso]
  apply ind_pi_of_ind
  intro i
  apply h

end Products

end ObjectProperty

end CategoryTheory
