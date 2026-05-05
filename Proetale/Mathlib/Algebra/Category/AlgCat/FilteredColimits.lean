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
  clear x; intro ⟨j, y⟩
  rw [algMapToColimit_eq F j r]
  simp only [algColimitRingCocone, algRingDiagram]
  erw [MonCat.FilteredColimits.colimit_mul_mk_eq
         (algMonDiagram F) ⟨j, _⟩ ⟨j, y⟩ j (𝟙 j) (𝟙 j),
       MonCat.FilteredColimits.colimit_mul_mk_eq
         (algMonDiagram F) ⟨j, y⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
  apply MonCat.FilteredColimits.M.mk_eq
  refine ⟨j, 𝟙 j, 𝟙 j, ?_⟩
  -- After unfolding the diagram maps and applying id, the goal reduces to showing
  -- (id ∘ ...) (algebraMap r * y) = (id ∘ ...) (y * algebraMap r) in the monoid type.
  -- We simplify the identity homs and reduce to mul_comm in the commutative ring F.obj j.
  simp only [algMonDiagram, algRingDiagram, Functor.comp_map, Functor.comp_obj,
    CategoryTheory.Functor.map_id, CategoryTheory.hom_id, id_eq]
  -- The goal is: algebraMap R (F.obj j) r * y = y * algebraMap R (F.obj j) r
  -- where the elements have a complex functor-composition type definitionally equal to F.obj j.
  -- We use Algebra.commutes to close the goal.
  exact Algebra.commutes r (show F.obj j from y)

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
    simp only [Functor.const_obj_obj, AlgCat.hom_comp, colimitAlgHom, AlgHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    simp only [algColimitRingCocone, algRingDiagram, Functor.comp_obj, Functor.comp_map,
      Functor.const_obj_obj, Functor.mapCocone_ι_app, ConcreteCategory.hom_ofHom] at this
    exact this

/-- The mediating ring hom. -/
private noncomputable def descRingHom (s : Cocone F) :
    (algColimitRingCocone F).pt →+* s.pt :=
  ((algColimitRingIsColimit F).desc ((forget₂ (AlgCat R) RingCat).mapCocone s)).hom

private lemma descRingHom_fac (s : Cocone F) (j : J) (x : F.obj j) :
    descRingHom F s ((algColimitRingCocone F).ι.app j x) = (s.ι.app j).hom x := by
  have := ConcreteCategory.congr_hom
    ((algColimitRingIsColimit F).fac ((forget₂ (AlgCat R) RingCat).mapCocone s) j) x
  simp only [Functor.mapCocone_ι_app, Functor.comp_obj, Functor.comp_map,
    ConcreteCategory.hom_ofHom, descRingHom, algColimitRingCocone, algRingDiagram] at this ⊢
  exact this

private lemma descRingHom_commutes (s : Cocone F) (r : R) :
    descRingHom F s (algebraMap R (algColimitRingCocone F).pt r) = algebraMap R s.pt r := by
  let j := IsFiltered.nonempty.some (α := J)
  show descRingHom F s (algMapToColimit F r) = algebraMap R s.pt r
  rw [algMapToColimit_eq F j r]
  rw [descRingHom_fac F s j]
  exact (s.ι.app j).hom.commutes r

/-- The filtered colimit cocone is a limiting cocone. -/
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone F) where
  desc s := AlgCat.ofHom
    { descRingHom F s with
      commutes' := descRingHom_commutes F s }
  fac s j := by
    apply AlgCat.hom_ext
    ext x
    simp only [colimitCocone, AlgCat.hom_comp, colimitAlgHom, AlgHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk]
    exact descRingHom_fac F s j x
  uniq s m hm := by
    apply AlgCat.hom_ext
    have key : RingCat.ofHom m.hom.toRingHom =
        (algColimitRingIsColimit F).desc ((forget₂ (AlgCat R) RingCat).mapCocone s) :=
      (algColimitRingIsColimit F).hom_ext (fun j => by
          apply RingCat.hom_ext; ext z
          -- Goal: m.hom.toRingHom (ι.app j z) = (algColimitRingIsColimit F).desc (mapCocone s) (ι.app j z)
          -- Both sides equal (s.ι.app j).hom z.
          have hmj : (colimitCocone F).ι.app j ≫ m = s.ι.app j := hm j
          have hlhs : m.hom ((colimitAlgHom F j) z) = (s.ι.app j).hom z := by
            have h := congrArg AlgCat.Hom.hom hmj
            simp only [AlgCat.hom_comp, colimitCocone, colimitAlgHom, AlgHom.coe_mk] at h
            exact congrFun (congrArg DFunLike.coe h) z
          -- Use descRingHom_fac for the RHS
          have hrhs : descRingHom F s ((algColimitRingCocone F).ι.app j z) = (s.ι.app j).hom z :=
            descRingHom_fac F s j z
          -- descRingHom is definitionally (desc ...).hom, so we can use hrhs
          simp only [RingCat.ofHom_hom, AlgHom.coe_toRingHom, colimitAlgHom, AlgHom.coe_mk,
            descRingHom] at *
          exact hlhs.trans hrhs.symm)
    ext x
    have h := DFunLike.congr_fun (congrArg RingCat.Hom.hom key) x
    simp only [RingCat.ofHom_hom, AlgHom.coe_toRingHom] at h
    simp only [AlgCat.ofHom_hom, AlgHom.coe_mk, descRingHom]
    exact h

end AlgCat.FilteredColimits
