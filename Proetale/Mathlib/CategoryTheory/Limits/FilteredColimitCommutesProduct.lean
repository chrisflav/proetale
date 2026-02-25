import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

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
    simp only [Functor.comp_obj, Functor.comp_map, isoMk_hom, Pi.isoMk]
    have := (Pi.eqToEquivalenceCompIso C D F (e.apply_symm_apply i)).hom.naturality
      (f (e.symm i))
    simp only [Functor.comp_obj, Functor.comp_map] at this
    exact this

@[simps!]
def Functor.piCompIso {I : Type*} {C D E : I → Type*} [∀ i, Category* (C i)]
    [∀ i, Category* (D i)] [∀ i, Category* (E i)] (F : ∀ i, C i ⥤ D i) (G : ∀ i, D i ⥤ E i) :
    Functor.pi (fun i ↦ F i ⋙ G i) ≅ Functor.pi F ⋙ Functor.pi G :=
  NatIso.ofComponents (fun a ↦ Pi.isoMk fun i ↦ Iso.refl _)

namespace Limits

variable (ι : Type*) {C : Type*} [Category* C]

@[simps]
noncomputable def Pi.functor [HasProductsOfShape ι C] : (ι → C) ⥤ C where
  obj f := ∏ᶜ f
  map {f g} t := Pi.map t

@[simps!]
noncomputable
def Pi.functorCompIso {D : Type*} [Category* D] (F : C ⥤ D) [PreservesLimitsOfShape (Discrete ι) F]
    [HasProductsOfShape ι C] [HasProductsOfShape ι D] :
    Pi.functor ι ⋙ F ≅ Functor.pi (fun _ ↦ F) ⋙ Pi.functor ι :=
  NatIso.ofComponents (fun a ↦ PreservesProduct.iso F a) fun {a b} f ↦ by
    apply Pi.hom_ext
    intro i
    suffices h : F.map (map f) ≫ F.map (π b i) = F.map (π a i) ≫ F.map (f i) by simpa [Functor.pi]
    rw [← F.map_comp, Pi.map_π]
    simp

variable {ι}
variable [HasProductsOfShape ι C] {J : ι → Type*} [∀ i, Category* (J i)]

@[simps!]
noncomputable def Pi.constCompPiIsoConst (X : ι → C) :
    Functor.pi (fun i ↦ (Functor.const (J i)).obj (X i)) ⋙
      Pi.functor ι ≅ (Functor.const _).obj (∏ᶜ X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro _ _ _
    simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj, Functor.const_obj_map,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Pi.hom_ext; intro i
    simp [Functor.pi, functor])

@[simps]
noncomputable
def coconePointwiseProduct' {F : ∀ i, J i ⥤ C} (c : ∀ i, (Cocone (F i))) :
    Cocone (Functor.pi F ⋙ Pi.functor _) where
  pt := ∏ᶜ fun i ↦ (c i).pt
  ι := Functor.whiskerRight (NatTrans.pi fun i ↦ (c i).ι) _ ≫ (Pi.constCompPiIsoConst _).hom

noncomputable
def coconePointwiseProductIso (F : ∀ i, J i ⥤ C) [∀ i, HasColimit (F i)]
    [∀ (i : ι), HasColimitsOfShape (J i) C] :
    coconePointwiseProduct F ≅ coconePointwiseProduct' fun i ↦ colimit.cocone (F i) := by
  refine Cocones.ext (Iso.refl _) fun _ ↦ ?_
  apply Pi.hom_ext
  simp [Functor.pi]

noncomputable
def Pi.equivalenceOfEquivCompPiFunctorIso (F : ∀ i, J i ⥤ C) {ι' : Type*} (f : ι' ≃ ι)
    [HasProductsOfShape ι' C] :
    (Pi.equivalenceOfEquiv (fun j ↦ J j) f).inverse ⋙ Functor.pi (fun j ↦ F (f j)) ⋙ Pi.functor ι' ≅
      Functor.pi F ⋙ Pi.functor ι :=
  (NatIso.ofComponents
    (fun a ↦ (Pi.whiskerEquiv f (fun j ↦ (Iso.refl ((F (f j)).obj <| a (f j))))).symm)
    (by
      intro a b g
      apply Pi.hom_ext; intro i
      simp [Pi.whiskerEquiv, Functor.pi, Pi.equivalenceOfEquiv, Pi.functor])).symm

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
def IsIPCOfShape.isColimitCoconePointwiseProduct' [IsIPCOfShape.{w} ι C]
    {J : ι → Type w} [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)] {F : ∀ i, J i ⥤ C}
    {c : ∀ i, (Cocone (F i))} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (coconePointwiseProduct' c) :=
  (IsIPCOfShape.nonempty_isColimit hc).some

lemma IsIPC.of_isIPCOfShape [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C]
    (h : ∀ (ι : Type w), IsIPCOfShape.{w} ι C) :
    IsIPC.{w} C where
  isIso α I _ _ F := by
    let e : coconePointwiseProduct F ≅ coconePointwiseProduct' fun i ↦ colimit.cocone (F i) := by
      refine Cocones.ext (Iso.refl _) fun _ ↦ ?_
      apply Pi.hom_ext
      simp [Functor.pi]
    obtain ⟨hc⟩ := IsIPCOfShape.nonempty_isColimit fun i ↦ (colimit.isColimit (F i))
    have hc' : IsColimit (coconePointwiseProduct F) := hc.ofIsoColimit e.symm
    exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).mp ⟨hc'⟩

instance [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w, w} C] [IsIPC.{w} C]
    (ι : Type*) [Small.{w} ι] [HasProductsOfShape ι C] :
    IsIPCOfShape.{w} ι C := by
  suffices IsIPCOfShape (Shrink.{w, u_8} ι) C from .of_equiv (equivShrink ι).symm
  constructor
  intro J _ _ F c hc
  -- Use that `IsIPC` gives us `IsColimit (coconePointwiseProduct F)` (via IsIso desc)
  haveI : IsIso (colimitPointwiseProductToProductColimit F) := IsIPC.isIso _ _ F
  haveI : IsIso ((colimit.isColimit (pointwiseProduct F)).desc (coconePointwiseProduct F)) :=
    this
  have hF : IsColimit (coconePointwiseProduct F) :=
    (colimit.isColimit _).ofPointIso
  -- coconePointwiseProduct' c ≅ coconePointwiseProduct F followed by mapIso
  let e : coconePointwiseProduct F ≅ coconePointwiseProduct' fun i ↦ colimit.cocone (F i) := by
    refine Cocones.ext (Iso.refl _) fun _ ↦ ?_
    apply Pi.hom_ext; simp [Functor.pi]
  have hF' : IsColimit (coconePointwiseProduct' fun i ↦ colimit.cocone (F i)) :=
    hF.ofIsoColimit e
  -- Transfer from colimit.cocone to c via the unique iso
  constructor
  exact IsColimit.ofIsoColimit hF' (Cocones.ext
    (Pi.mapIso fun i ↦ (colimit.isColimit _).coconePointUniqueUpToIso (hc i))
    (by
      intro a; apply Pi.hom_ext; intro i
      simp only [coconePointwiseProduct'_ι, NatTrans.comp_app, Functor.whiskerRight_app,
        Pi.constCompPiIsoConst_hom_app, Pi.functor_map]
      erw [Category.comp_id, Category.comp_id]
      have hmapIso :
        (Pi.mapIso fun i ↦ (colimit.isColimit (F i)).coconePointUniqueUpToIso (hc i)).hom =
          Pi.map (fun i ↦ ((colimit.isColimit (F i)).coconePointUniqueUpToIso (hc i)).hom) := rfl
      rw [hmapIso]
      erw [Category.assoc, Pi.map_π, Pi.map_π, ← Category.assoc, Pi.map_π,
        Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
      rfl))

lemma IsIPCOfShape.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    {ι : Type*} [HasProductsOfShape ι D] [IsIPCOfShape.{w} ι D] [HasProductsOfShape ι C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfShape (Discrete ι) F]
    -- TODO: this assumption is seemingly hard for typeclass search
    [∀ (J : ι → Type w) [∀ i, SmallCategory (J i)] [∀ i, IsFiltered (J i)],
      ReflectsColimitsOfShape (∀ i, J i) F] :
    IsIPCOfShape.{w} ι C where
  nonempty_isColimit J _ _ D c hc := by
    obtain ⟨h⟩ := IsIPCOfShape.nonempty_isColimit (fun i ↦ isColimitOfPreserves F (hc i))
    constructor
    apply isColimitOfReflects F
    refine IsColimit.equivOfNatIsoOfIso ?_ _ _ ?_ h
    · exact Functor.isoWhiskerRight (Functor.piCompIso _ _) _ ≪≫
        (Functor.associator _ _ _) ≪≫
        (Functor.isoWhiskerLeft _ <| (Pi.functorCompIso _ _).symm) ≪≫
        (Functor.associator _ _ _).symm
    · refine Cocones.ext (PreservesProduct.iso F _).symm ?_
      intro a
      dsimp
      simp only [Category.id_comp, Category.comp_id, Category.assoc]
      rw [← cancel_mono (PreservesProduct.iso F _).hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply Pi.hom_ext
      intro i
      simp [Functor.pi, NatTrans.pi, ← Functor.map_comp]

lemma IsIPC.of_preservesFilteredColimitsOfSize {D : Type*} [Category* D] (F : C ⥤ D)
    [HasProducts D] [HasFilteredColimitsOfSize.{w, w} D] [IsIPC.{w} D]
    [HasProducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] [PreservesLimitsOfSize.{w, w} F]
    [ReflectsFilteredColimitsOfSize.{w, w} F] :
    IsIPC.{w} C :=
  .of_isIPCOfShape fun ι ↦ by
    convert IsIPCOfShape.of_preservesFilteredColimitsOfSize.{w} F
    · infer_instance
    · infer_instance
    · intro J
      infer_instance

end Limits

end CategoryTheory
