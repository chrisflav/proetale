/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Proetale.Mathlib.RingTheory.RingHom.Flat
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.Algebra.Homology.ShortComplex.Exact
import Proetale.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Algebra.Ind
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Proetale.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits

/-!
# Ind-(faithfully flat) is faithfully flat

-/

universe w v u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

/-- The object property of flat modules. -/
def flat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Flat R M

variable (R : Type u) [CommRing R]

@[simp]
lemma flat_iff (M : ModuleCat R) : flat R M ↔ Module.Flat R M :=
  .rfl

/-- The object property of faithfully flat modules. -/
def faithfullyFlat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FaithfullyFlat R M

@[simp]
lemma faithfullyFlat_iff (M : ModuleCat R) : faithfullyFlat R M ↔ Module.FaithfullyFlat R M :=
  .rfl

variable {R} in
open MonoidalCategory in
lemma flat_of_colimitPresentation {M : ModuleCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J M)
    (h : ∀ j, Module.Flat R (pres.diag.obj j)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  intro C hC
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    { X₁ := pres.diag ⋙ tensorRight C.X₁
      X₂ := pres.diag ⋙ tensorRight C.X₂
      X₃ := pres.diag ⋙ tensorRight C.X₃
      f := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.f
      g := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.g
      zero := by simp [← CategoryTheory.Functor.whiskerLeft_comp, ← Functor.map_comp, C.zero] }
  apply colim.exact_mapShortComplex (S := S)
      (hc₁ := isColimitOfPreserves _ pres.isColimit)
      (hc₂ := isColimitOfPreserves _ pres.isColimit)
      (hc₃ := isColimitOfPreserves _ pres.isColimit)
  · rw [CategoryTheory.ShortComplex.exact_iff_evaluation]
    intro j
    exact Module.Flat.lTensor_shortComplex_exact (pres.diag.obj j) C hC
  · simp [S, whisker_exchange]
  · simp [S, whisker_exchange]

open MonoidalCategory in
@[simp]
lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm (fun M ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact flat_of_colimitPresentation pres h

end ModuleCat

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The object property of flat `R`-algebras. -/
def flat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.flat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma flat_iff {S : CommAlgCat R} : flat R S ↔ Module.Flat R S := .rfl

lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm ?_ (ObjectProperty.le_ind _)
  rw [flat]
  refine le_trans (ObjectProperty.ind_inverseImage_le _ _) ?_
  rw [ModuleCat.ind_flat]

/-- The object property of faithfully-flat `R`-algebras. -/
def faithfullyFlat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.faithfullyFlat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma faithfullyFlat_iff {S : CommAlgCat R} :
    faithfullyFlat R S ↔ Module.FaithfullyFlat R S := .rfl

lemma faithfullyFlat_of_colimitPresentation {S : CommAlgCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S)
    (h : ∀ j, Module.FaithfullyFlat R (pres.diag.obj j)) :
    Module.FaithfullyFlat R S := by
  have : Module.Flat R S := by
    rw [← flat_iff, flat, ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
      ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨J, ‹_›, ‹_›, pres, fun j ↦ ?_⟩
    exact (h j).1
  refine Module.FaithfullyFlat.of_nontrivial_tensor_quotient fun m hm ↦ ?_
  let qpres : ColimitPresentation J (CommAlgCat.of R <| (R ⧸ m) ⊗[R] S) :=
    pres.map <| MonoidalCategory.tensorLeft (CommAlgCat.of R (R ⧸ m))
  have (j : J) : Nontrivial ((qpres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat).obj j) := by
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      MonoidalCategory.curriedTensor_obj_obj, forget₂_commRingCat_obj, coe_tensorObj,
      Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left, qpres]
    infer_instance
  change Nontrivial ((forget₂ _ CommRingCat).mapCocone qpres.cocone).pt
  exact CommRingCat.FilteredColimits.nontrivial (isColimitOfPreserves _ qpres.isColimit)

lemma ind_faithfullyFlat :
    ObjectProperty.ind.{u} (faithfullyFlat.{u} R) = faithfullyFlat.{u} R := by
  refine le_antisymm (fun S ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact faithfullyFlat_of_colimitPresentation pres h

end CommAlgCat

namespace CommRingCat

/-- The morphism property of ring maps inducing surjective maps on prime spectra. -/
def surjectiveSpec : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ Function.Surjective (PrimeSpectrum.comap f)

@[simp]
lemma surjectiveSpec_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    surjectiveSpec f ↔ Function.Surjective (PrimeSpectrum.comap f.hom) := .rfl

/-- The morphism property of faithfully flat ring maps. -/
def faithfullyFlat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.FaithfullyFlat

@[simp]
lemma faithfullyFlat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    faithfullyFlat f ↔ f.hom.FaithfullyFlat := .rfl

lemma faithfullyFlat_eq : faithfullyFlat = flat ⊓ surjectiveSpec := by
  ext X Y f
  simp only [faithfullyFlat_iff, RingHom.FaithfullyFlat.eq_and]
  rfl

instance : faithfullyFlat.IsStableUnderCobaseChange := by
  rw [faithfullyFlat, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.FaithfullyFlat.isStableUnderBaseChange

instance : surjectiveSpec.IsMultiplicative where
  id_mem R := Function.surjective_id
  comp_mem _ _ h1 h2 := by simpa using h1.comp h2

instance : faithfullyFlat.IsMultiplicative where
  id_mem _ := .of_bijective Function.bijective_id
  comp_mem _ _ := RingHom.FaithfullyFlat.stableUnderComposition _ _

lemma ind_flat_eq_flat : MorphismProperty.ind.{u} flat.{u} = flat := by
  refine le_antisymm (fun {R S} f hf ↦ ?_) (MorphismProperty.le_ind _)
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  algebraize [f.hom]
  suffices h : ObjectProperty.ind.{u} (ModuleCat.flat.{u} R) (ModuleCat.of R S) by
    rwa [ModuleCat.ind_flat] at h
  let F : Under R ⥤ ModuleCat R := (commAlgCatEquivUnder R).inverse ⋙
    forget₂ (CommAlgCat R) (AlgCat R) ⋙
    forget₂ (AlgCat R) (ModuleCat R)
  apply ObjectProperty.ind_inverseImage_le (F := F) (P := ModuleCat.flat.{u} R)
    (Under.mk f)
  exact hf

lemma ind_faithfullyFlat_eq_faithfullyFlat :
    MorphismProperty.ind.{u} faithfullyFlat.{u} = faithfullyFlat.{u} := by
  refine le_antisymm (fun {R S} f hf ↦ ?_) (MorphismProperty.le_ind _)
  rw [MorphismProperty.ind_iff_ind_underMk] at hf
  algebraize [f.hom]
  suffices h : ObjectProperty.ind.{u} (CommAlgCat.faithfullyFlat.{u} R) (.of R S) by
    rwa [CommAlgCat.ind_faithfullyFlat] at h
  exact ObjectProperty.ind_inverseImage_le (F := (commAlgCatEquivUnder R).inverse)
    (P := CommAlgCat.faithfullyFlat.{u} R) (Under.mk f) hf

end CommRingCat

namespace Module

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} [CommRing S]

namespace Flat

/-- A module is flat if it can be written as a filtered colimit of flat modules. -/
theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (ModuleCat.of R M))
    (h : ∀ (i : ι), Module.Flat R (P.diag.obj i)) : Module.Flat R M :=
  ModuleCat.flat_of_colimitPresentation (M := .of R M) P h

/-- Flat is equivalent to ind-flat. -/
theorem iff_ind_flat [Algebra R S] : Module.Flat R S ↔
    ObjectProperty.ind.{u} (CommAlgCat.flat R) (.of R S) := by
  rw [CommAlgCat.ind_flat]
  rfl

end Flat

namespace FaithfullyFlat

-- `Do we need SmallCategory here?`
theorem of_colimitPresentation [Algebra R S] {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Module.FaithfullyFlat R (P.diag.obj i)) : Module.FaithfullyFlat R S :=
  CommAlgCat.faithfullyFlat_of_colimitPresentation P h

theorem iff_ind_faithfullyFlat [Algebra R S] :
    Module.FaithfullyFlat R S ↔ ObjectProperty.ind.{u}
      (CommAlgCat.faithfullyFlat R) (.of R S) := by
  rw [CommAlgCat.ind_faithfullyFlat]
  rfl

end FaithfullyFlat

end Module

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

namespace Flat

/-- Flat is equivalent to ind-flat. -/
lemma iff_ind_flat (f : R →+* S) :
    f.Flat ↔ MorphismProperty.ind.{u} CommRingCat.flat (CommRingCat.ofHom f) := by
  rw [CommRingCat.ind_flat_eq_flat]
  rfl

/-- A ring map is flat if it can be written as a filtered colimit of flat ring maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.Flat ∧ t.app i ≫ c.app i = f) : f.hom.Flat :=
  (iff_ind_flat _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

end Flat

namespace FaithfullyFlat

/-- Faithfully flat is equivalent to ind-(faithfully flat). -/
lemma iff_ind_faithfullyFlat (f : R →+* S) :
    f.FaithfullyFlat ↔ MorphismProperty.ind.{u}
      CommRingCat.faithfullyFlat (CommRingCat.ofHom f) := by
  rw [CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
  rfl

/-- A ring hom is faithfully flat if it can be written as a colimit of faithfully flat ring maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.FaithfullyFlat ∧ t.app i ≫ c.app i = f) : f.hom.FaithfullyFlat :=
  (iff_ind_faithfullyFlat _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

end FaithfullyFlat

end RingHom
