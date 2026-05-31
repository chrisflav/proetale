/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.FinitePresentation
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

/-- The object property on commutative `R`-algebras of being finitely presented. -/
def CommAlgCat.finitePresentation : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ RingHom.FinitePresentation (algebraMap R S)

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

/-- Étaleness is local on the target: if `s` spans the unit ideal of `S` and every
`Localization.Away g` for `g ∈ s` is étale over `R`, then `S` is étale over `R`. -/
lemma Algebra.Etale.of_span_eq_top_target (s : Set S) (hs : Ideal.span s = ⊤)
    (h : ∀ g ∈ s, Algebra.Etale R (Localization.Away g)) : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap]
  refine RingHom.Etale.ofLocalizationSpanTarget (algebraMap R S) s hs fun ⟨g, hg⟩ ↦ ?_
  have : Algebra.Etale R (Localization.Away g) := h g hg
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- Local isomorphisms of `R`-algebras are étale. -/
lemma Algebra.IsLocalIso.etale [Algebra.IsLocalIso R S] : Algebra.Etale R S :=
  Algebra.Etale.of_span_eq_top_target R S _
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S) fun g hg ↦ by
      obtain ⟨r, _⟩ := hg.exists_away
      exact Algebra.Etale.of_isLocalizationAway r

/-- A local isomorphism of `R`-algebras is finitely presented. -/
lemma Algebra.IsLocalIso.finitePresentation [Algebra.IsLocalIso R S] :
    Algebra.FinitePresentation R S := by
  have := Algebra.IsLocalIso.etale R S
  infer_instance

/-- Finitely presented `R`-algebras are finitely presentable objects in `CommAlgCat R`. -/
lemma CommAlgCat.finitePresentation_le_isFinitelyPresentable :
    CommAlgCat.finitePresentation R ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := by
  intro S hS
  have hunder : IsFinitelyPresentable.{u} ((commAlgCatEquivUnder (.of R)).functor.obj S) :=
    CommRingCat.isFinitelyPresentable_under _ _ (by convert hS using 1)
  have : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact (isCardinalPresentable_iff_of_isEquivalence (X := S) (κ := .aleph0)
    (commAlgCatEquivUnder (.of R)).functor).mp hunder

/-- Local isomorphisms are finitely presentable in `CommAlgCat R`. -/
lemma CommAlgCat.isLocalIso_le_isFinitelyPresentable :
    CommAlgCat.isLocalIso R ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := fun S hS ↦
  have : Algebra.IsLocalIso R S := hS
  have := Algebra.IsLocalIso.finitePresentation R S
  CommAlgCat.finitePresentation_le_isFinitelyPresentable R S
    (RingHom.finitePresentation_algebraMap.mpr ‹_›)

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

end Algebra.IndZariski

namespace Algebra.BijectiveOnStalks

section ColimitPresentation

variable {R S}
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
  (P : ColimitPresentation ι (CommAlgCat.of R S))

/-- The contraction of a prime `p` of the colimit `S` to a constituent `P.diag.obj i`. -/
private noncomputable def colimitPrime (p : Ideal S) (i : ι) : Ideal (P.diag.obj i) :=
  p.comap (P.ι.app i).hom.toRingHom

private instance (p : Ideal S) [p.IsPrime] (i : ι) : (colimitPrime P p i).IsPrime :=
  Ideal.IsPrime.comap _

omit [IsFiltered ι] in
private lemma colimitPrime_comap_algebraMap (p : Ideal S) (i : ι) :
    p.comap (algebraMap R S) =
      (colimitPrime P p i).comap (algebraMap R (P.diag.obj i)) := by
  have hcomm (r : R) :
      (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
    (P.ι.app i).hom.commutes r
  ext r
  simp only [Ideal.mem_comap, colimitPrime, ← hcomm r]
  rfl

omit [IsFiltered ι] in
private lemma colimitPrime_comap_diag (p : Ideal S) {i j : ι} (f : i ⟶ j) :
    colimitPrime P p i = (colimitPrime P p j).comap (P.diag.map f).hom.toRingHom := by
  ext r
  show (P.ι.app i).hom r ∈ p ↔ (P.ι.app j).hom ((P.diag.map f).hom r) ∈ p
  rw [DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) r]

variable (p : Ideal S) [p.IsPrime]

/-- The diagram of localizations `Localization.AtPrime (colimitPrime P p i)` for `i : ι`, with
transition maps given by `Localization.localRingHom`. -/
noncomputable def localizationDiag : ι ⥤ CommRingCat.{u} where
  obj i := .of (Localization.AtPrime (colimitPrime P p i))
  map {i j} f := CommRingCat.ofHom <| Localization.localRingHom _ _
    (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f)
  map_id i := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_id]
    refine Localization.localRingHom_unique _ _ _ _ fun r ↦ ?_
    show RingHom.id _ _ = algebraMap _ _ ((P.diag.map (𝟙 i)).hom.toRingHom r)
    rw [P.diag.map_id, RingHom.id_apply]; rfl
  map_comp {i j k} f g := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_ofHom, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    refine Localization.localRingHom_unique _ _ _ _ fun r ↦ ?_
    show ((Localization.localRingHom _ _ _ _).comp (Localization.localRingHom _ _ _ _)) _ =
      algebraMap _ _ ((P.diag.map (f ≫ g)).hom.toRingHom r)
    rw [RingHom.comp_apply, Localization.localRingHom_to_map, Localization.localRingHom_to_map,
      P.diag.map_comp]; rfl

/-- The cocone over `localizationDiag P p` with apex `Localization.AtPrime p`, with structure maps
the canonical `Localization.localRingHom` induced by the colimit injections. -/
noncomputable def localizationCocone : Cocone (localizationDiag P p) where
  pt := .of (Localization.AtPrime p)
  ι :=
    { app i := CommRingCat.ofHom <|
        Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl
      naturality {i j} f := by
        apply CommRingCat.hom_ext
        refine RingHom.ext fun x ↦ ?_
        obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective
          (colimitPrime P p i).primeCompl x
        show (Localization.localRingHom (colimitPrime P p j) p (P.ι.app j).hom.toRingHom rfl)
            ((Localization.localRingHom (colimitPrime P p i) (colimitPrime P p j)
              (P.diag.map f).hom.toRingHom (colimitPrime_comap_diag P p f))
                (IsLocalization.mk' _ r ⟨s, hs⟩)) =
          (Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl)
            (IsLocalization.mk' _ r ⟨s, hs⟩)
        rw [Localization.localRingHom_mk', Localization.localRingHom_mk',
          Localization.localRingHom_mk']
        refine congrArg₂ (IsLocalization.mk' _) ?_ (Subtype.ext ?_)
        · exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) r
        · exact DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) s }

/-- **Surjectivity** for the colimit recognition: every element of `Localization.AtPrime p` (where
`p ⊆ S = colim Aᵢ`) is the image of an element of `Localization.AtPrime (colimitPrime P p i)`
for some `i`. -/
private lemma exists_localizationCocone_eq (z : Localization.AtPrime p) :
    ∃ (i : ι) (zᵢ : Localization.AtPrime (colimitPrime P p i)),
      (localizationCocone P p).ι.app i zᵢ = z := by
  obtain ⟨⟨s, u, hu⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
  obtain ⟨i₁, s₀, hs₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit s
  obtain ⟨i₂, u₀, hu₀⟩ := Concrete.isColimit_exists_rep _ P.isColimit u
  let i : ι := IsFiltered.max i₁ i₂
  let s' : P.diag.obj i := (P.diag.map (IsFiltered.leftToMax i₁ i₂)).hom s₀
  let u' : P.diag.obj i := (P.diag.map (IsFiltered.rightToMax i₁ i₂)).hom u₀
  have hnat {a b : ι} (f : a ⟶ b) (x : P.diag.obj a) :
      (P.ι.app b).hom ((P.diag.map f).hom x) = (P.ι.app a).hom x :=
    DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) x
  have hs' : (P.ι.app i).hom s' = s := (hnat (IsFiltered.leftToMax i₁ i₂) s₀).trans hs₀
  have hu' : (P.ι.app i).hom u' = u := (hnat (IsFiltered.rightToMax i₁ i₂) u₀).trans hu₀
  have hu'_mem : u' ∈ (colimitPrime P p i).primeCompl := fun hmem ↦ hu (hu' ▸ hmem)
  refine ⟨i, IsLocalization.mk' _ s' ⟨u', hu'_mem⟩, ?_⟩
  change Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl
    (IsLocalization.mk' _ s' ⟨u', hu'_mem⟩) = _
  rw [Localization.localRingHom_mk']
  exact congrArg₂ (IsLocalization.mk' _) hs' (Subtype.ext hu')

/-- **Injectivity** for the colimit recognition: if two elements of
`Localization.AtPrime (colimitPrime P p i)` have equal image in `Localization.AtPrime p`, then
they become equal in `Localization.AtPrime (colimitPrime P p k)` for some morphism `i ⟶ k`. -/
private lemma exists_eq_of_localizationCocone_eq (i : ι)
    (x y : Localization.AtPrime (colimitPrime P p i))
    (hxy : (localizationCocone P p).ι.app i x = (localizationCocone P p).ι.app i y) :
    ∃ (k : ι) (f : i ⟶ k),
      (localizationDiag P p).map f x = (localizationDiag P p).map f y := by
  change Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl x =
    Localization.localRingHom (colimitPrime P p i) p (P.ι.app i).hom.toRingHom rfl y at hxy
  obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (colimitPrime P p i).primeCompl x
  obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (colimitPrime P p i).primeCompl y
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
  obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
  obtain ⟨k₀, c', hc'⟩ := Concrete.isColimit_exists_rep _ P.isColimit c
  have hnat {a b : ι} (f : a ⟶ b) (x : P.diag.obj a) :
      (P.ι.app b).hom ((P.diag.map f).hom x) = (P.ι.app a).hom x :=
    DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w f)) x
  let i' : ι := IsFiltered.max i k₀
  let li : i ⟶ i' := IsFiltered.leftToMax i k₀
  let rk : k₀ ⟶ i' := IsFiltered.rightToMax i k₀
  let c'' : P.diag.obj i' := (P.diag.map rk).hom c'
  have hkey :
      (P.ι.app i').hom (c'' * ((P.diag.map li).hom s₂ * (P.diag.map li).hom r₁)) =
        (P.ι.app i').hom (c'' * ((P.diag.map li).hom s₁ * (P.diag.map li).hom r₂)) := by
    simp only [map_mul, hnat li, hnat rk, c'', hc']
    exact hc
  obtain ⟨k, fij, hjeq⟩ := (IsColimit.eq_iff' P.isColimit _ _).mp hkey
  refine ⟨k, li ≫ fij, ?_⟩
  let ck : P.diag.obj k := (P.diag.map fij).hom c''
  have hck_to_c : (P.ι.app k).hom ck = c := by
    show (P.ι.app k).hom ((P.diag.map fij).hom ((P.diag.map rk).hom c')) = c
    rw [hnat fij, hnat rk, hc']
  have hck_mem : ck ∈ (colimitPrime P p k).primeCompl := fun hmem ↦ hcp (hck_to_c ▸ hmem)
  have hcomp (x : P.diag.obj i) :
      (P.diag.map fij).hom ((P.diag.map li).hom x) = (P.diag.map (li ≫ fij)).hom x := by
    show ((P.diag.map fij).hom ∘ (P.diag.map li).hom) x = _
    rw [P.diag.map_comp]; rfl
  have hs₁_pc : (P.diag.map (li ≫ fij)).hom s₁ ∈ (colimitPrime P p k).primeCompl := by
    intro hmem
    apply hs₁
    show (P.ι.app i).hom s₁ ∈ p
    rw [← DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w (li ≫ fij))) s₁]
    exact hmem
  have hs₂_pc : (P.diag.map (li ≫ fij)).hom s₂ ∈ (colimitPrime P p k).primeCompl := by
    intro hmem
    apply hs₂
    show (P.ι.app i).hom s₂ ∈ p
    rw [← DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (P.w (li ≫ fij))) s₂]
    exact hmem
  change Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (colimitPrime_comap_diag P p (li ≫ fij)) _ =
    Localization.localRingHom (colimitPrime P p i) (colimitPrime P p k)
      (P.diag.map (li ≫ fij)).hom.toRingHom (colimitPrime_comap_diag P p (li ≫ fij)) _
  rw [Localization.localRingHom_mk', Localization.localRingHom_mk', IsLocalization.eq]
  refine ⟨⟨ck, hck_mem⟩, ?_⟩
  have hjeq' :
      (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₂ * (P.diag.map li).hom r₁)) =
        (P.diag.map fij).hom (c'' * ((P.diag.map li).hom s₁ * (P.diag.map li).hom r₂)) := hjeq
  simp only [map_mul, hcomp] at hjeq'
  show (((P.diag.map (li ≫ fij)).hom r₁) * (P.diag.map (li ≫ fij)).hom s₂) * ck =
    (((P.diag.map (li ≫ fij)).hom r₂) * (P.diag.map (li ≫ fij)).hom s₁) * ck
  show _ * _ * (P.diag.map fij).hom c'' = _ * _ * (P.diag.map fij).hom c''
  linear_combination hjeq'

/-- **Localization of a filtered colimit at a prime is the colimit of localizations**.

If `S = colim Aᵢ` is a filtered colimit of `R`-algebras and `p ⊆ S` is a prime, then
`Localization.AtPrime p` is the colimit of the diagram `localizationDiag P p`, i.e. of the
localizations `(Aᵢ)_{p ∩ Aᵢ}` along the canonical `Localization.localRingHom` transition maps. -/
noncomputable def isColimitLocalizationCocone : IsColimit (localizationCocone P p) := by
  have : ReflectsFilteredColimits (forget CommRingCat.{u}) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  exact ReflectsColimit.reflects (F := forget _)
    (Types.FilteredColimit.isColimitOf' _
      (fun z ↦ (exists_localizationCocone_eq P p z).imp fun _ ⟨zᵢ, hz⟩ ↦ ⟨zᵢ, hz.symm⟩)
      (fun i x y hxy ↦ exists_eq_of_localizationCocone_eq P p i x y hxy))

/-- If `S` is a filtered colimit of `R`-algebras `Aᵢ` and each `R → Aᵢ` is bijective on
stalks, then so is `R → S`.

The proof factors through `isColimitLocalizationCocone`: the localization of `S` at `p` is the
filtered colimit of the localizations of `Aᵢ` at the preimages of `p`. The natural map
`R_{p ∩ R} → S_p` factors through each `R_{p ∩ R} → (Aᵢ)_{p ∩ Aᵢ}`, and bijectivity propagates
through the colimit. -/
lemma of_colimitPresentation
    (h : ∀ i, Algebra.BijectiveOnStalks R (P.diag.obj i)) :
    Algebra.BijectiveOnStalks R S := by
  refine ⟨fun p hp ↦ ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨i⟩ : Nonempty ι := IsFiltered.nonempty
    let xi : Localization.AtPrime (colimitPrime P p i) :=
      Localization.localRingHom _ _ (algebraMap R (P.diag.obj i))
        (colimitPrime_comap_algebraMap P p i) x
    let yi : Localization.AtPrime (colimitPrime P p i) :=
      Localization.localRingHom _ _ (algebraMap R (P.diag.obj i))
        (colimitPrime_comap_algebraMap P p i) y
    have hxy_i : (localizationCocone P p).ι.app i xi = (localizationCocone P p).ι.app i yi := by
      show (Localization.localRingHom _ _ _ _).comp
          (Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) x =
        (Localization.localRingHom _ _ _ _).comp
          (Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) y
      rw [← Localization.localRingHom_comp, ← Localization.localRingHom_comp]
      convert hxy using 2 <;>
      · ext r; exact ((P.ι.app i).hom.commutes r).symm
    obtain ⟨k, f, hk⟩ :=
      (IsColimit.eq_iff' (isColimitLocalizationCocone P p) xi yi).mp hxy_i
    have hk' :
        Localization.localRingHom _ _ (algebraMap R (P.diag.obj k))
          (colimitPrime_comap_algebraMap P p k) x =
        Localization.localRingHom _ _ (algebraMap R (P.diag.obj k))
          (colimitPrime_comap_algebraMap P p k) y := by
      change (Localization.localRingHom _ _ (P.diag.map f).hom.toRingHom _).comp
          (Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) x =
        (Localization.localRingHom _ _ (P.diag.map f).hom.toRingHom _).comp
          (Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) y at hk
      rw [← Localization.localRingHom_comp, ← Localization.localRingHom_comp] at hk
      convert hk using 2 <;>
      · ext r; show algebraMap R (P.diag.obj k) r = _
        rw [← (P.diag.map f).hom.commutes r]; rfl
    exact ((RingHom.bijectiveOnStalks_algebraMap.mpr (h k)).localRingHom_of_eq
      (colimitPrime_comap_algebraMap P p k)).1 hk'
  · intro z
    obtain ⟨i, zᵢ, hzᵢ⟩ := exists_localizationCocone_eq P p z
    obtain ⟨w, hw⟩ :=
      ((RingHom.bijectiveOnStalks_algebraMap.mpr (h i)).localRingHom_of_eq
        (colimitPrime_comap_algebraMap P p i)).2 zᵢ
    refine ⟨w, ?_⟩
    rw [← hzᵢ, ← hw]
    show ((localizationCocone P p).ι.app i).hom
        ((Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) w) = _
    show (Localization.localRingHom _ _ _ _).comp
        (Localization.localRingHom _ _ (algebraMap R (P.diag.obj i)) _) w = _
    rw [← Localization.localRingHom_comp]
    refine congrFun (congrArg DFunLike.coe ?_) w
    refine Localization.localRingHom_unique _ _ _ _ fun r ↦ ?_
    show algebraMap _ _ ((P.ι.app i).hom.toRingHom (algebraMap R (P.diag.obj i) r)) =
      algebraMap _ _ (algebraMap R S r)
    rw [(P.ι.app i).hom.commutes]

end ColimitPresentation

end Algebra.BijectiveOnStalks

namespace Algebra.IndZariski

@[stacks 096T]
theorem bijectiveOnStalks [Algebra.IndZariski R S] :
    Algebra.BijectiveOnStalks R S := by
  obtain ⟨ι, _, _, P, h⟩ := IndZariski.exists_colimitPresentation (R := R) (S := S)
  exact Algebra.BijectiveOnStalks.of_colimitPresentation P fun i ↦
    RingHom.bijectiveOnStalks_algebraMap.mp
      (RingHom.IsLocalIso.bijectiveOnStalks (RingHom.isLocalIso_algebraMap.mpr (h i)))

/-- If `S` is a filtered colimit of ind-Zariski `R`-algebras, then `S` is ind-Zariski. -/
theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso,
    ← ObjectProperty.ind_ind (CommAlgCat.isLocalIso_le_isFinitelyPresentable R)]
  exact ⟨ι, ‹_›, ‹_›, P, fun i ↦ (iff_ind_isLocalIso R _).mp (h i)⟩

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
  exact RingHom.bijectiveOnStalks_algebraMap.mpr
    (Algebra.IndZariski.bijectiveOnStalks R S)

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
