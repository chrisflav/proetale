import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

universe u

open CategoryTheory Limits IsFiltered

namespace AlgCat.FilteredColimits

/-!
# Filtered colimits in `AlgCat R`

Given a small filtered category `J` and a functor `F : J ⥤ AlgCat R`, we construct
the filtered colimit in `AlgCat R` by taking the filtered colimit in `RingCat` and
equipping it with an `R`-algebra structure via the canonical map `R → colimit`.
-/

variable {R : Type u} [CommRing R]
variable {J : Type u} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ AlgCat.{u} R)

/-- The ring diagram underlying `F : J ⥤ AlgCat R`. -/
private noncomputable def algRingDiagram : J ⥤ RingCat.{u} :=
  F ⋙ forget₂ (AlgCat.{u} R) RingCat.{u}

/-- The monoid diagram, used for colimit multiplication computation. -/
private noncomputable def algMonDiagram : J ⥤ MonCat.{u} :=
  algRingDiagram F ⋙ forget₂ RingCat.{u} SemiRingCat.{u} ⋙ forget₂ SemiRingCat.{u} MonCat.{u}

/-- The colimit cocone in `RingCat` for the underlying ring diagram. -/
private noncomputable def algColimitRingCocone : Cocone (algRingDiagram F) :=
  RingCat.FilteredColimits.colimitCocone.{u, u} (algRingDiagram F)

private noncomputable def algColimitRingIsColimit :
    IsColimit (algColimitRingCocone F) :=
  RingCat.FilteredColimits.colimitCoconeIsColimit.{u, u} (algRingDiagram F)

/-- The canonical algebra map `R → (algColimitRingCocone F).pt`. -/
private noncomputable def algMapToColimit : R →+* (algColimitRingCocone F).pt :=
  ((algColimitRingCocone F).ι.app IsFiltered.nonempty.some).hom.comp
    (algebraMap R (F.obj IsFiltered.nonempty.some))

omit [IsFiltered J] in
private lemma algebraMap_compatible {j k : J} (f : j ⟶ k) (r : R) :
    (algMonDiagram F).map f (algebraMap R (F.obj j) r) = algebraMap R (F.obj k) r := by
  simp only [algMonDiagram, algRingDiagram, Functor.comp_map]
  exact (F.map f).hom.commutes r

/-- The algebra map is independent of the chosen index. -/
private lemma algMapToColimit_eq (j : J) (r : R) :
    algMapToColimit F r = (algColimitRingCocone F).ι.app j (algebraMap R (F.obj j) r) := by
  let j₀ := nonempty.some (α := J)
  simp only [algMapToColimit, algColimitRingCocone, algRingDiagram]
  apply Quot.eq.mpr
  let k := IsFiltered.max j₀ j
  refine .trans _ ⟨k, algebraMap R (F.obj k) r⟩ _ ?_ (.symm _ _ ?_)
  · exact .rel _ _ ⟨IsFiltered.leftToMax j₀ j,
      (algebraMap_compatible F (IsFiltered.leftToMax j₀ j) r).symm⟩
  · exact .rel _ _ ⟨IsFiltered.rightToMax j₀ j,
      (algebraMap_compatible F (IsFiltered.rightToMax j₀ j) r).symm⟩

/-- The algebra map commutes with all colimit elements. -/
private lemma algMapToColimit_commutes (r : R) (x : (algColimitRingCocone F).pt) :
    algMapToColimit F r * x = x * algMapToColimit F r := by
  refine Quot.inductionOn x ?_
  rintro ⟨j, y⟩
  rw [algMapToColimit_eq F j r]
  let f : F.obj j →+* (algColimitRingCocone F).pt :=
    ((algColimitRingCocone F).ι.app j).hom
  change f (algebraMap R (F.obj j) r) * f y = f y * f (algebraMap R (F.obj j) r)
  rw [← map_mul, ← map_mul, Algebra.commutes]

/-- The `R`-algebra structure on the colimit ring. -/
noncomputable instance colimitAlgebra : Algebra R (algColimitRingCocone F).pt :=
  (algMapToColimit F).toAlgebra' (algMapToColimit_commutes F)

/-- The colimit map `F.obj j →+* colimit` is also an `R`-algebra hom. -/
private noncomputable def colimitAlgHom (j : J) :
    F.obj j →ₐ[R] AlgCat.of R (algColimitRingCocone F).pt where
  __ := ((algColimitRingCocone F).ι.app j).hom
  commutes' r := (algMapToColimit_eq F j r).symm

/-- The filtered colimit cocone for `F : J ⥤ AlgCat R`. -/
noncomputable def colimitCocone : Cocone F where
  pt := AlgCat.of R (algColimitRingCocone F).pt
  ι.app j := AlgCat.ofHom (colimitAlgHom F j)
  ι.naturality {i k} f := by
    apply AlgCat.hom_ext
    ext x
    have := ConcreteCategory.congr_hom ((algColimitRingCocone F).ι.naturality f) x
    simp only [Functor.const_obj_obj, AlgCat.hom_comp, colimitAlgHom]
    simp only [algColimitRingCocone, algRingDiagram, Functor.comp_obj, Functor.comp_map,
      Functor.const_obj_obj] at this
    exact this

/-- The mediating ring hom. -/
private noncomputable def descRingHom (s : Cocone F) :
    (algColimitRingCocone F).pt →+* s.pt :=
  ((algColimitRingIsColimit F).desc ((forget₂ (AlgCat R) RingCat).mapCocone s)).hom

private lemma descRingHom_fac (s : Cocone F) (j : J) (x : F.obj j) :
    descRingHom F s ((algColimitRingCocone F).ι.app j x) = (s.ι.app j).hom x := by
  have := ConcreteCategory.congr_hom
    ((algColimitRingIsColimit F).fac ((forget₂ (AlgCat R) RingCat).mapCocone s) j) x
  simp only [Functor.mapCocone_ι_app, Functor.comp_obj,
    descRingHom, algColimitRingCocone, algRingDiagram] at this ⊢
  exact this

private lemma descRingHom_commutes (s : Cocone F) (r : R) :
    descRingHom F s (algebraMap R (algColimitRingCocone F).pt r) = algebraMap R s.pt r := by
  let j := IsFiltered.nonempty.some (α := J)
  rw [show algebraMap R (algColimitRingCocone F).pt r = algMapToColimit F r from rfl,
    algMapToColimit_eq F j r, descRingHom_fac F s j]
  exact (s.ι.app j).hom.commutes r

/-- The filtered colimit cocone is a limiting cocone. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s := AlgCat.ofHom
    { descRingHom F s with
      commutes' := descRingHom_commutes F s }
  fac s j := by
    apply AlgCat.hom_ext
    ext x
    simp only [colimitCocone, AlgCat.hom_comp, colimitAlgHom]
    exact descRingHom_fac F s j x
  uniq s m hm := by
    apply AlgCat.hom_ext
    have key : RingCat.ofHom m.hom.toRingHom =
        (algColimitRingIsColimit F).desc ((forget₂ (AlgCat R) RingCat).mapCocone s) :=
      (algColimitRingIsColimit F).hom_ext fun j ↦ by
        apply RingCat.hom_ext
        ext z
        have hmj : (colimitCocone F).ι.app j ≫ m = s.ι.app j := hm j
        have hlhs : m.hom ((colimitAlgHom F j) z) = (s.ι.app j).hom z := by
          have h := congrArg AlgCat.Hom.hom hmj
          simp only [AlgCat.hom_comp, colimitCocone, colimitAlgHom] at h
          exact congrFun (congrArg DFunLike.coe h) z
        have hrhs : descRingHom F s ((algColimitRingCocone F).ι.app j z) = (s.ι.app j).hom z :=
          descRingHom_fac F s j z
        simp only [colimitAlgHom, AlgHom.coe_mk, descRingHom] at *
        exact hlhs.trans hrhs.symm
    ext x
    have h := DFunLike.congr_fun (congrArg RingCat.Hom.hom key) x
    simp only [descRingHom]
    exact h

end AlgCat.FilteredColimits

namespace AlgCat

instance forget₂Ring_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (AlgCat.{u} R) RingCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone
          (AlgCat.FilteredColimits.colimitCoconeIsColimit F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ (AlgCat.{u} R) RingCat.{u})) }

instance forget_preservesFilteredColimits (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (AlgCat.{u} R)) :=
  HasForget₂.forget_comp (C := AlgCat.{u} R) (D := RingCat.{u}) ▸
    (Limits.comp_preservesFilteredColimits
        (forget₂ (AlgCat.{u} R) RingCat.{u})
        (forget RingCat.{u}) : PreservesFilteredColimitsOfSize.{u, u} _)

end AlgCat
