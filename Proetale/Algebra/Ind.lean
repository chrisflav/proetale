/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib

open CategoryTheory

variable {R : Type*} [CommRing R]

universe u v w w'

open CategoryTheory Limits

open Algebra
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

section

variable {ι : Type*} [Preorder ι] (F : ι → Type*) (f : ∀ ⦃i j : ι⦄, i ≤ j → F i → F j)
  [DirectedSystem F f]

/-- A characterization of a type being the direct colimit of a directed system. -/
class IsDirectLimit (G : Type*) (g : ∀ i, F i → G) : Prop where
  comp_eq {i j : ι} (hij : i ≤ j) : g j ∘ f hij = g i
  jointly_surjective (x : G) : ∃ i, x ∈ Set.range (g i)
  eq_iff {i j : ι} (x : F i) (y : F j) : g i x = g j y ↔ ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
    f hik x = f hjk y

variable [IsDirected ι (· ≤ ·)]
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort*} (f : ∀ i j (h : i ≤ j), T h)
variable [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)] [DirectedSystem F (f · · ·)]

variable (G : Type*) (g : ∀ i, F i → G)

/--
A directed ind-presentation of `S` over `R` is a directed system of `R`-algebras, whose
colimit is `S`.
-/
@[ext]
structure Algebra.DirectedIndPresentation (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (ι : Type*) [Preorder ι] where
  [isDirected : IsDirected ι (fun i j : ι ↦ i ≤ j)]
  F : ι → Type v
  [commRing : ∀ i, CommRing (F i)]
  [algebra : ∀ i, Algebra R (F i)]
  f : ∀ ⦃i j : ι⦄, i ≤ j → F i →ₐ[R] F j
  g : ∀ i, F i →ₐ[R] S
  [directedSystem : DirectedSystem F (fun _ _ hij ↦ ⇑(f hij))]
  [isDirectLimit : IsDirectLimit F (fun _ _ hij ↦ ⇑(f hij)) S (fun i ↦ ⇑(g i))]

/--
An ind-presentation of `S` over `R` is a filtered system of `R`-algebras, whose
colimit is `S`.
-/
@[ext]
structure Algebra.IndPresentation (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (J : Type*) [Category J] where
  [isFiltered : IsFiltered J]
  F : J ⥤ CommAlgCat.{v} R
  t : F ⟶ (Functor.const J).obj (.of R S)
  hc : IsColimit (Cocone.mk _ t)

namespace Algebra.DirectedIndPresentation

attribute [instance] commRing algebra directedSystem

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

@[simps]
def self : DirectedIndPresentation R S Unit where
  isDirected := by
    constructor
    intro _ _
    use ()
  F _ := S
  f _ _ _ := AlgHom.id _ _
  g i := AlgHom.id _ _
  directedSystem := by constructor <;> simp
  isDirectLimit := by constructor <;> simp

end Algebra.DirectedIndPresentation

/-- An algebra is ind-étale if it can be written as the filtered colimit of étale
algebras. -/
class Algebra.IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  out : ∃ (ι : Type u) (_ : SmallCategory ι) (P : Algebra.IndPresentation R S ι),
    ∀ (i : ι), Algebra.Etale R (P.F.obj i)

/-- A ring hom is ind-étale if and only if it is an ind-étale algebra. -/
def RingHom.IndEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndEtale R S

instance (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  show PreservesFilteredColimits <| (commAlgCatEquivUnder (.of R)).functor ⋙ Under.forget (CommRingCat.of R)
  infer_instance

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

instance : ReflectsFilteredColimits (forget₂ (CommAlgCat.{u} R) (CommRingCat.{u})) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- A ring hom is ind-étale if and only if it can be written as a colimit
of étale ring homs.. -/
lemma RingHom.IndEtale.iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndEtale ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (c : D ⟶ (Functor.const J).obj S) (_ : IsColimit (.mk _ c)) (t : (Functor.const J).obj R ⟶ D),
      (∀ i, t.app i ≫ c.app i = f) ∧ ∀ i, (t.app i).hom.Etale := by
  algebraize [f.hom]
  refine ⟨fun hf ↦ ?_, ?_⟩
  · obtain ⟨J, _, P, hP⟩ := hf.out
    refine ⟨J, inferInstance, P.isFiltered, P.F ⋙ forget₂ _ _, ?_, ?_, ?_, ?_, ?_⟩
    · exact Functor.whiskerRight P.t _
    · have : IsFiltered J := P.isFiltered
      have : IsColimit <| (forget₂ _ CommRingCat).mapCocone (Cocone.mk _ P.t) :=
        isColimitOfPreserves _ P.hc
      exact this
    · exact ⟨fun j ↦ CommRingCat.ofHom <| algebraMap _ _, by intros; ext; simp⟩
    · intro i
      ext
      simp [RingHom.algebraMap_toAlgebra]
    · intro i
      simpa [Functor.const_obj_obj, Functor.comp_obj, CommAlgCat.forget₂_commRingCat_obj,
        CommRingCat.hom_ofHom, RingHom.etale_algebraMap] using hP i
  · intro ⟨J, _, D, c, g, hc, t, H1, H2⟩
    refine ⟨⟨J, inferInstance, ⟨CommAlgCat.functorMk _ c t, CommAlgCat.natTransMk _ g H1, ?_⟩, H2⟩⟩
    exact isColimitOfReflects (forget₂ _ CommRingCat) hc

end
