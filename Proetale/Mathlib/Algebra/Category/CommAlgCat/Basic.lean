import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

universe v u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

def CategoryTheory.CommAlgCat.functorMk {J : Type*} [Category J] (F : J ⥤ CommRingCat.{u})
    (t : (Functor.const J).obj (.of R) ⟶ F) :
    J ⥤ CommAlgCat.{u} R where
  obj j :=
    letI : Algebra R (F.obj j) := (t.app j).hom.toAlgebra
    .of R (F.obj j)
  map {i j} f :=
    letI _ (j) : Algebra R (F.obj j) := (t.app j).hom.toAlgebra
    CommAlgCat.ofHom ⟨(F.map f).hom, fun r ↦ congr($(t.naturality f).hom r).symm⟩

def CategoryTheory.CommAlgCat.hom (S : CommAlgCat.{u} R) : CommRingCat.of R ⟶ (forget₂ _ _).obj S :=
  CommRingCat.ofHom (algebraMap R S)

def CategoryTheory.CommAlgCat.natTransMk {J : Type*} [Category J] {F G : J ⥤ CommAlgCat.{u} R}
    (t : F ⋙ forget₂ _ CommRingCat ⟶ G ⋙ forget₂ _ CommRingCat)
    (ht : ∀ (i : J), (F.obj i).hom ≫ t.app i = (G.obj i).hom) :
    F ⟶ G where
  app j := CommAlgCat.ofHom ⟨(t.app j).hom, fun _ ↦ congr($(ht j).hom _)⟩
  naturality {_ _} f := (forget₂ _ CommRingCat).map_injective (t.naturality f)

instance : (forget₂ (CommAlgCat.{v} R) CommRingCat.{v}).ReflectsIsomorphisms := by
  refine ⟨fun {A B} f hf ↦ ?_⟩
  refine ⟨CommAlgCat.ofHom ⟨(inv ((forget₂ _ CommRingCat).map f)).hom, fun r ↦ ?_⟩, ?_, ?_⟩
  · apply ConcreteCategory.injective_of_mono_of_preservesPullback ((forget₂ _ CommRingCat).map f)
    simp only [CommAlgCat.forget₂_commRingCat_obj, CommAlgCat.forget₂_commRingCat_map,
      CommRingCat.hom_ofHom, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      RingHom.coe_coe, AlgHom.commutes]
    exact congr($(IsIso.inv_hom_id ((forget₂ _ CommRingCat).map f)).hom (algebraMap R B r))
  · ext
    exact congr($(IsIso.hom_inv_id ((forget₂ _ CommRingCat).map f)).hom _)
  · ext
    exact congr($(IsIso.inv_hom_id ((forget₂ _ CommRingCat).map f)).hom _)

instance (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  show PreservesFilteredColimits <| (commAlgCatEquivUnder (.of R)).functor ⋙ Under.forget (CommRingCat.of R)
  infer_instance

instance : ReflectsFilteredColimits (forget₂ (CommAlgCat.{u} R) (CommRingCat.{u})) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms
