/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Flat
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.Ind
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Algebra.Pi
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Ind-Zariski algebras and ring homomorphisms

In this file we define ind-Zariski algebras.
-/
universe u

open CategoryTheory Limits

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

section Algebra

variable [Algebra R S] [Algebra R T]

/-- The object property on commutative `R`-algebras of being a local isomorphism. -/
def CommAlgCat.isLocalIso : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.IsLocalIso R S

lemma CommAlgCat.isLocalIso_eq : isLocalIso R = RingHom.toObjectProperty RingHom.IsLocalIso R := by
  ext S
  exact RingHom.isLocalIso_algebraMap.symm

instance : (CommAlgCat.isLocalIso R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.isLocalIso_eq]
  exact RingHom.IsLocalIso.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

instance : (CommAlgCat.isLocalIso R).IsClosedUnderFiniteProducts :=
  .of_isClosedUnderLimitsOfShape_discrete fun ι ↦ by
    intro
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let S : ι → CommAlgCat.{u} R := fun i ↦ F.obj ⟨i⟩
    let natIso : F ≅ Discrete.functor S := Discrete.natIso (fun i ↦ Iso.refl _)
    let isoPi : (CommAlgCat.piFan S).pt ≅ limit (Discrete.functor S) :=
      (limit.isoLimitCone ⟨CommAlgCat.piFan S, CommAlgCat.isLimitPiFan S⟩).symm
    let isoLim : limit (Discrete.functor S) ≅ limit F :=
      (HasLimit.isoOfNatIso natIso).symm
    apply (CommAlgCat.isLocalIso R).prop_of_iso (isoPi ≪≫ isoLim)
    have inst (i : ι) : Algebra.IsLocalIso R (S i) := hF ⟨i⟩
    exact Algebra.IsLocalIso.pi_of_finite R (fun i ↦ S i)

/-- An algebra is ind-Zariski if it can be written as the filtered colimit of locally isomorphic
algebras. -/
@[stacks 096N, mk_iff]
class Algebra.IndZariski (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.IsLocalIso R (P.diag.obj i)

namespace Algebra.IndZariski

lemma iff_ind_isLocalIso :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (.of R S) :=
  Algebra.indZariski_iff R S

lemma of_equiv (e : S ≃ₐ[R] T) [IndZariski R S] : IndZariski R T := by
  rwa [iff_ind_isLocalIso, (CommAlgCat.isLocalIso R).ind.prop_iff_of_iso (CommAlgCat.isoMk e.symm),
    ← iff_ind_isLocalIso]

lemma trans [Algebra S T] [IsScalarTower R S T] [Algebra.IndZariski R S] [Algebra.IndZariski S T] :
    Algebra.IndZariski R T :=
  sorry

instance pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.IndZariski R (S i)] : Algebra.IndZariski R (∀ i, S i) := by
  rw [iff_ind_isLocalIso]
  apply ObjectProperty.LimitOfShape.prop (J := Discrete ι)
  refine ⟨⟨Discrete.functor fun i ↦ .of R (S i),
      Discrete.natTrans fun i ↦ CommAlgCat.ofHom (Pi.evalAlgHom _ _ _), ?_⟩, ?_⟩
  · exact CommAlgCat.isLimitPiFan fun i ↦ .of R (S i)
  · intro j
    dsimp
    rw [← iff_ind_isLocalIso]
    infer_instance

/-- The product of two ind-Zariski algebras is ind-Zariski. -/
instance prod [Algebra.IndZariski R S] [Algebra.IndZariski R T] :
    Algebra.IndZariski R (S × T) := by
  let F : ULift.{u} (Fin 2) → Type u := fun | ⟨0⟩ => S | ⟨1⟩ => T
  letI : ∀ i, CommRing (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  letI : ∀ i, Algebra R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  haveI : ∀ i, IndZariski R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  have := pi R F
  let e : (∀ i, F i) ≃ₐ[R] S × T :=
    { toFun := fun f ↦ (f ⟨0⟩, f ⟨1⟩)
      invFun := fun p ↦ fun | ⟨0⟩ => p.1 | ⟨1⟩ => p.2
      left_inv := fun f ↦ by ext ⟨i⟩; fin_cases i <;> rfl
      right_inv := fun ⟨_, _⟩ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact Algebra.IndZariski.of_equiv (R := R) (S := ∀ i, F i) (T := S × T) e

instance function {ι : Type u} [_root_.Finite ι] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.IndZariski R S] : Algebra.IndZariski R (ι → S) :=
  pi R (fun _ ↦ S)

variable {R}

instance (priority := 100) of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ObjectProperty.le_ind _ _ ‹_›

instance refl : Algebra.IndZariski R R :=
  Algebra.IndZariski.of_isLocalIso _

/-- The index category for the colimit presentation `M⁻¹R = colim_{m ∈ M} R[1/m]`:
a wrapper around the submonoid `M`, equipped with the divisibility preorder. -/
@[ext]
structure AwayIndex {R : Type u} [CommRing R] (M : Submonoid R) where
  /-- The underlying element of the submonoid. -/
  val : R
  /-- The element belongs to `M`. -/
  property : val ∈ M

namespace AwayIndex

variable {R : Type u} [CommRing R] {M : Submonoid R}

instance : Preorder (AwayIndex M) where
  le m m' := m.val ∣ m'.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

instance : IsDirected (AwayIndex M) (· ≤ ·) :=
  ⟨fun m m' ↦ ⟨⟨m.val * m'.val, M.mul_mem m.2 m'.2⟩,
    ⟨m'.val, rfl⟩, ⟨m.val, mul_comm _ _⟩⟩⟩

instance : Nonempty (AwayIndex M) := ⟨⟨1, M.one_mem⟩⟩

end AwayIndex

/-- The transition map `Localization.Away m → Localization.Away m'` when `m ∣ m'`,
viewed as an `R`-algebra homomorphism. -/
noncomputable def awayDvdHom (R : Type u) [CommRing R] {m m' : R} (h : m ∣ m')
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalization.Away m A] [IsLocalization.Away m' B] : A →ₐ[R] B where
  __ := IsLocalization.Away.lift (S := A) m
    (g := algebraMap R B) (IsLocalization.Away.isUnit_of_dvd m' h)
  commutes' _ := IsLocalization.Away.lift_eq _ _ _

/-- The diagram `m ↦ Localization.Away m` indexed by elements of a submonoid `M ⊆ R`. -/
noncomputable def awayDiag (R : Type u) [CommRing R] (M : Submonoid R) :
    AwayIndex M ⥤ CommAlgCat.{u} R where
  obj m := .of R (Localization.Away m.val)
  map {m m'} h := CommAlgCat.ofHom (awayDvdHom R (m := m.val) (m' := m'.val) h.le)
  map_id m := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    refine IsLocalization.ringHom_ext (.powers m.val) ?_
    ext _
    simp [awayDvdHom, IsLocalization.Away.lift]
  map_comp {m _ _} _ _ := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    refine IsLocalization.ringHom_ext (.powers m.val) ?_
    ext _
    simp [awayDvdHom, IsLocalization.Away.lift]

instance (R : Type u) [CommRing R] (M : Submonoid R) (m : AwayIndex M) :
    IsLocalization.Away m.val ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (IsLocalization.Away m.val (Localization.Away m.val))

instance (R : Type u) [CommRing R] (M : Submonoid R) (m : AwayIndex M) :
    Algebra.IsLocalIso R ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (Algebra.IsLocalIso R (Localization.Away m.val))

/-- The `R`-algebra homomorphism `Localization.Away m → S` induced by the universal property,
where `S` is a localization of `R` at a submonoid `M` containing `m`. -/
noncomputable def awayToLocalization (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] (m : AwayIndex M) :
    Localization.Away m.val →ₐ[R] S where
  __ := IsLocalization.Away.lift (S := Localization.Away m.val) m.val
    (g := algebraMap R S) (IsLocalization.map_units S ⟨m.val, m.property⟩)
  commutes' _ := IsLocalization.Away.lift_eq _ _ _

/-- The cocone over `awayDiag R M` with apex `S` given by the maps `awayToLocalization`. -/
noncomputable def awayCocone (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    awayDiag R M ⟶ (Functor.const (AwayIndex M)).obj (CommAlgCat.of R S) where
  app m := CommAlgCat.ofHom (awayToLocalization R M S m)
  naturality {m m'} _ := by
    refine CommAlgCat.hom_ext ?_
    have : Subsingleton (((awayDiag R M).obj m : Type u) →ₐ[R]
        (((Functor.const (AwayIndex M)).obj (CommAlgCat.of R S)).obj m' : Type u)) :=
      IsLocalization.algHom_subsingleton (.powers m.val)
    exact Subsingleton.elim _ _

/-- A localization of `R` at a submonoid `M` is the filtered colimit of `R[1/m]`
over `m ∈ M`, in the category of `R`-algebras. -/
noncomputable def awayColimitPresentation (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    ColimitPresentation (AwayIndex M) (CommAlgCat.of R S) where
  diag := awayDiag R M
  ι := awayCocone R M S
  isColimit :=
    { desc c := CommAlgCat.ofHom <| IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R c.pt) fun y ↦ by
          have key : (c.ι.app ⟨y.val, y.2⟩).hom
              (algebraMap R (Localization.Away y.val) y.val) = algebraMap R c.pt y.val :=
            (c.ι.app ⟨y.val, y.2⟩).hom.commutes y.val
          rw [Algebra.ofId_apply, ← key]
          exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.val) y.val).map
            (c.ι.app ⟨y.val, y.2⟩).hom
      fac c m := by
        refine CommAlgCat.hom_ext ?_
        have : Subsingleton (((awayDiag R M).obj m : Type u) →ₐ[R] (c.pt : Type u)) :=
          IsLocalization.algHom_subsingleton (.powers m.val)
        exact Subsingleton.elim _ _
      uniq c _ _ := by
        refine CommAlgCat.hom_ext ?_
        have : Subsingleton (S →ₐ[R] (c.pt : Type u)) :=
          IsLocalization.algHom_subsingleton M
        exact Subsingleton.elim _ _ }

lemma of_isLocalization (M : Submonoid R) [IsLocalization M S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ⟨AwayIndex M, inferInstance, inferInstance, awayColimitPresentation R M S,
    fun m ↦ inferInstanceAs (Algebra.IsLocalIso R (Localization.Away m.val))⟩

instance localization (M : Submonoid R) : Algebra.IndZariski R (Localization M) :=
  of_isLocalization _ M

variable (R)

instance (priority := 100) _root_.Module.Flat.of_indZariski [Algebra.IndZariski R S] :
    Module.Flat R S := by
  rw [Module.Flat.iff_ind_flat]
  obtain ⟨J, _, _, pres, h⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  refine ⟨J, inferInstance, inferInstance, pres, fun i ↦ ?_⟩
  rw [CommAlgCat.flat_iff]
  exact @Algebra.IsLocalIso.flat _ _ _ _ _ (h i)

@[stacks 096T]
theorem bijectiveOnStalks_algebraMap [Algebra.IndZariski R S] :
    (algebraMap R S).BijectiveOnStalks :=
  sorry

theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := sorry

end Algebra.IndZariski

end Algebra

section RingHom

/-- A ring hom is ind-Zariski if and only if it is an ind-Zariski algebra. -/
@[stacks 096N, algebraize Algebra.IndZariski]
def RingHom.IndZariski {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndZariski R S

namespace RingHom.IndZariski

lemma algebraMap_iff [Algebra R S] :
    (algebraMap R S).IndZariski ↔ Algebra.IndZariski R S:=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

variable {R S T}

lemma iff_ind_isLocalIso (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndZariski, Algebra.IndZariski.iff_ind_isLocalIso, ← f.algebraMap_toAlgebra,
    RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.isLocalIso_eq]

/-- A ring hom is ind-Zariski if and only if it can be written
as a colimit of local isomorphisms. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndZariski ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S)
      (_ : IsColimit (.mk _ c)), ∀ i, (t.app i).hom.IsLocalIso ∧ t.app i ≫ c.app i = f :=
  RingHom.IndZariski.iff_ind_isLocalIso _

lemma id : (RingHom.id R).IndZariski :=
  Algebra.IndZariski.refl

variable {f : R →+* S} {g : S →+* T}

lemma comp (hg : g.IndZariski) (hf : f.IndZariski) : (g.comp f).IndZariski := by
  algebraize [f, g, g.comp f]
  exact Algebra.IndZariski.trans R S T

lemma prod {g : R →+* T} (hf : f.IndZariski) (hg : g.IndZariski) : (f.prod g).IndZariski := by
  algebraize [f, g]
  exact Algebra.IndZariski.prod R S T

lemma pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* (S i)) (hf : ∀ i, (f i).IndZariski) : (Pi.ringHom f).IndZariski := by
  let (i : ι) : Algebra R (S i) := (f i).toAlgebra
  have (i : ι) : Algebra.IndZariski R (S i) := hf i
  exact Algebra.IndZariski.pi R S

lemma flat (h : f.IndZariski) : f.Flat := by
  algebraize [f]
  exact .of_indZariski R S

@[stacks 096T]
theorem bijectiveOnStalks (h : f.IndZariski) : f.BijectiveOnStalks := by
  algebraize [f]
  exact Algebra.IndZariski.bijectiveOnStalks_algebraMap R S

/-- Ind-Zariski is equivalent to ind-ind-Zariski. -/
lemma iff_ind_indZariski (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndZariski) (CommRingCat.ofHom f) := by
  algebraize [f]
  sorry

/-- A ring hom is ind-Zariski if it can be written as a filtered colimit of ind-Zariski maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndZariski ∧ t.app i ≫ c.app i = f) : f.hom.IndZariski :=
  (iff_ind_indZariski _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

theorem _root_.Algebra.IndZariski.iff_ind_indZariksi [Algebra R S] :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndZariski R) (.of R S) := by
  sorry

end RingHom.IndZariski

end RingHom
