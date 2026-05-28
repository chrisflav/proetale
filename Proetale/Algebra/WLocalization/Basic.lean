/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocal
import Proetale.Algebra.IndZariski
import Proetale.Algebra.IndEtale
import Proetale.Algebra.StalkAlgebraic
import Proetale.Algebra.Preliminaries.Ideal

/-!
# w-localization

In this file we show that every ring admits a faithfully flat, ind-Zariski w-local algebra.
-/

universe u

open CategoryTheory Limits PrimeSpectrum

namespace WLocalization

variable {A : Type*} [CommRing A]

/-- The submonoid of `A` consisting of elements that become invertible in `(A / I)_f`. -/
def Generalization.submonoid (f : A) (I : Ideal A) : Submonoid A :=
  Submonoid.comap (algebraMap A (Localization.Away <| Ideal.Quotient.mk I f))
    (IsUnit.submonoid _)

/-- The localization of `A` at all elements invertible in `(A / I)_f`. -/
def Generalization (f : A) (I : Ideal A) : Type _ :=
  Localization (Generalization.submonoid f I)

namespace Generalization

variable (f : A) (I : Ideal A)

instance : CommRing (Generalization f I) := fast_instance%
  inferInstanceAs <| CommRing <| Localization (Generalization.submonoid f I)

instance : Algebra A (Generalization f I) := fast_instance%
  inferInstanceAs <| Algebra A <| Localization (Generalization.submonoid f I)

instance : IsLocalization (Generalization.submonoid f I) (Generalization f I) :=
  inferInstanceAs <| IsLocalization _ <| Localization (Generalization.submonoid f I)

/-- The canonical map from the generalization at `(f, I)` to `(A ⧸ I)_f`. -/
noncomputable
def toLocQuotient (f : A) (I : Ideal A) :
    Generalization f I →ₐ[A] Localization.Away (Ideal.Quotient.mk I f) :=
  IsLocalization.liftAlgHom (f := Algebra.ofId _ _) (M := submonoid f I) fun y ↦ y.2

/--
The kernel of the canonical map from the generalization at `(f, I)` to `(A ⧸ I)_f`.
This ideal defines a closed subset of the prime spectrum of the generalization at `(f, I)` that
maps homeomorphically to `D(f) ∩ V(I)`.
-/
noncomputable
def ideal (f : A) (I : Ideal A) : Ideal (Generalization f I) :=
  RingHom.ker (toLocQuotient f I)

instance indZariski : Algebra.IndZariski A (Generalization f I) := by
  dsimp [Generalization]
  infer_instance

def locClosedSubset (f : A) (I : Ideal A) : Set (PrimeSpectrum A) :=
  basicOpen f ∩ zeroLocus I

/-- The image of `Spec (Generalization f I)` in `Spec A` is equal to
the generalization hull of `D(f) ∩ V(I)`. -/
lemma range_algebraMap_generalization (f : A) (I : Ideal A) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) =
    generalizationHull (locClosedSubset f I) :=
  sorry

lemma bijOn_algebraMap_generalization_specComap_zeroLocus_ideal (f : A) (I : Ideal A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (Generalization f I)) (zeroLocus (ideal f I))
    (locClosedSubset f I) :=
  sorry

theorem submonoid_le {f f' : A} {I I' : Ideal A} (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    submonoid f I ≤ submonoid f' I' :=
  sorry

noncomputable def map {f f' : A} {I I' : Ideal A}
    (h : locClosedSubset f' I' ⊆ locClosedSubset f I) :
    Generalization f I →ₐ[A] Generalization f' I' where
  toRingHom := IsLocalization.map (T := Generalization.submonoid f' I')
    (Generalization f' I') (RingHom.id A) (submonoid_le h)
  commutes' := sorry

lemma exists_specializes_zeroLocus_ideal {f : A} (I : Ideal A)
    (x : PrimeSpectrum (Generalization f I)) : ∃ y ∈ zeroLocus (ideal f I), x ⤳ y :=
  sorry

/-- If `I ≤ I'` and `f ∣ f'`, the map `Generalization f I → Generalization f' I'` sends elements
of the kernel `ideal f I` to elements of the kernel `ideal f' I'`. -/
lemma map_mem_ideal_of_strata {f f' : A} {I I' : Ideal A}
    (h_sub : locClosedSubset f' I' ⊆ locClosedSubset f I) (hI : I ≤ I')
    (hf : f ∣ f') (z : Generalization f I) (hz : z ∈ ideal f I) :
    map h_sub z ∈ ideal f' I' := by
  simp only [ideal, RingHom.mem_ker] at hz ⊢
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (submonoid f I) z
  have hz' : algebraMap A (Localization.Away (Ideal.Quotient.mk I f)) a = 0 := by
    have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
    have h4 := congr_arg (toLocQuotient f I) h3
    rw [map_mul, hz, zero_mul, (toLocQuotient f I).commutes] at h4
    exact h4.symm
  have hz_factor : algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))
      (Ideal.Quotient.mk I a) = 0 := by
    rwa [IsScalarTower.algebraMap_apply A (A ⧸ I)] at hz'
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk I f))
    (Localization.Away (Ideal.Quotient.mk I f)) _).mp hz_factor
  have hfna : f ^ n * a ∈ I := by
    have : Ideal.Quotient.mk I (f ^ n * a) = 0 := by rw [map_mul, map_pow]; exact hc
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨g, hfg⟩ := hf
  have hf'na : f' ^ n * a ∈ I' := by
    rw [hfg, mul_pow]
    have heq : f ^ n * g ^ n * a = g ^ n * (f ^ n * a) := by ring
    rw [heq]
    exact I'.mul_mem_left _ (hI hfna)
  have ha_zero : algebraMap A (Localization.Away (Ideal.Quotient.mk I' f')) a = 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ I')]
    refine (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk I' f'))
      (Localization.Away (Ideal.Quotient.mk I' f')) (Ideal.Quotient.mk I' a)).mpr
      ⟨⟨_, n, rfl⟩, ?_⟩
    have : Ideal.Quotient.mk I' (f' ^ n * a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hf'na
    rwa [map_mul, map_pow] at this
  have h3 := IsLocalization.mk'_spec (M := submonoid f I) (Generalization f I) a s
  have h4 : map h_sub (IsLocalization.mk' (Generalization f I) a s *
      algebraMap A (Generalization f I) (s : A)) =
      map h_sub (algebraMap A (Generalization f I) a) := congr_arg _ h3
  rw [map_mul, (map h_sub).commutes, (map h_sub).commutes] at h4
  have h5 := congr_arg (toLocQuotient f' I') h4
  rw [map_mul, (toLocQuotient f' I').commutes, (toLocQuotient f' I').commutes, ha_zero] at h5
  have hs_unit : IsUnit (algebraMap A (Localization.Away (Ideal.Quotient.mk I' f')) (s : A)) :=
    submonoid_le h_sub s.2
  exact hs_unit.mul_left_eq_zero.mp h5

end Generalization

/-- The single stratum `Z(E, F)` in `Spec A`. -/
def stratum (E F : Finset A) : Set (PrimeSpectrum A) :=
  (⋂ f ∈ E, basicOpen f) ∩ zeroLocus (Ideal.span (F : Set A))

lemma stratum_eq_basicOpen_inter_zeroLocus (E F : Finset A) :
    stratum E F = (basicOpen (∏ f ∈ E, f) : Set _) ∩ zeroLocus (Ideal.span (F : Set A)) := by
  classical
  rw [stratum]
  congr
  induction E using Finset.induction_on with
  | empty =>
    simp
  | insert a s h1 h2 =>
    simp [h2, Finset.prod_insert h1, -basicOpen_eq_zeroLocus_compl, basicOpen_mul]

lemma stratum_anti {E F E' F' : Finset A} (hEE' : E ⊆ E') (hFF' : F ⊆ F') :
    stratum E' F' ⊆ stratum E F := by
  rw [stratum, stratum]
  apply Set.inter_subset_inter
  · exact Set.biInter_mono hEE' fun x a ⦃a⦄ a ↦ a
  · apply zeroLocus_anti_mono
    exact Ideal.span_mono (Finset.coe_subset.mpr hFF')

/-- The type of disjoint union decompositions of `E` into two finite sets. -/
structure Stratification.Index (E : Finset A) where
  left : Finset A
  right : Finset A
  disjoint : Disjoint left right
  union_eq : (left : Set A) ∪ (right : Set A) = E

/-- Given a disjoint union decomposition `E = E' ⨿ E''`, this is product of the `f ∈ E'. -/
def Stratification.Index.function {E : Finset A} (i : Stratification.Index E) : A :=
  ∏ f ∈ i.left, f

/-- Given a disjoint union decomposition `E = E' ⨿ E''`, this is the ideal spanned by `E''`. -/
def Stratification.Index.ideal {E : Finset A} (i : Stratification.Index E) : Ideal A :=
  Ideal.span i.right

lemma locClosedSubset_function_ideal {E : Finset A} (i : Stratification.Index E) :
    Generalization.locClosedSubset i.function i.ideal = stratum i.left i.right := by
  rw [Generalization.locClosedSubset, stratum_eq_basicOpen_inter_zeroLocus]
  rfl

/-- Restrict a disjoint union decomposition of `F` to `E`. -/
@[simps]
noncomputable
def Stratification.Index.restrict {E F : Finset A} (i : Stratification.Index F)
    (h : E ⊆ F) : Stratification.Index E where
  left := open Classical in E ∩ i.left
  right := open Classical in E ∩ i.right
  disjoint :=
    open Classical in i.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right
  union_eq := by
    classical
    simp only [Finset.coe_inter]
    rw [← Set.inter_union_distrib_left, i.union_eq,
      Set.inter_eq_left.mpr (Finset.coe_subset.mpr h)]

lemma Stratification.Index.iUnion_stratum (E : Finset A) :
    ⋃ (i : Stratification.Index E), stratum i.left i.right = .univ := by
  classical
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨⟨E.filter (· ∉ p.asIdeal), E.filter (· ∈ p.asIdeal), ?_, ?_⟩, ?_⟩
  · rw [Finset.disjoint_filter]
    exact fun _ _ h1 h2 ↦ h1 h2
  · ext x
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hx : x ∈ p.asIdeal
      · exact Or.inr ⟨h, hx⟩
      · exact Or.inl ⟨h, hx⟩
  · refine ⟨?_, ?_⟩
    · simp only [Set.mem_iInter, Finset.mem_filter]
      intro f ⟨_, hf⟩
      exact hf
    · rw [PrimeSpectrum.mem_zeroLocus]
      refine Ideal.span_le.mpr fun x hx ↦ ?_
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2

/-- The product of the generalizations of `Z(E', E'')` indexed by all disjoint union decompositions
`E = E' ⨿ E''`. -/
def ProdStrata (E : Finset A) : Type _ :=
  ∀ (i : Stratification.Index E), Generalization i.function i.ideal

@[ext]
lemma ProdStrata.ext {E : Finset A} (x y : ProdStrata E) (h : ∀ i, x i = y i) : x = y := by
  dsimp [ProdStrata] at *
  ext i
  exact h i

instance (E : Finset A) : CommRing (ProdStrata E) := fast_instance%
  inferInstanceAs <| CommRing <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

instance (E : Finset A) : Algebra A (ProdStrata E) := fast_instance%
  inferInstanceAs <| Algebra A <|
    ∀ (i : Stratification.Index E), Generalization i.function i.ideal

/-- The ideal of the stratification product, given by the product of the ideals defining
`Z(E', E'')` in its generalization. -/
noncomputable def ProdStrata.ideal (E : Finset A) : Ideal (ProdStrata E) :=
  Ideal.pi fun _ ↦ Generalization.ideal _ _

-- wrong
lemma ProdStrata.bijOn_algebraMap_specComap_zeroLocus_ideal (E : Finset A) :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (ProdStrata E))
    (zeroLocus (ProdStrata.ideal E)) .univ :=
  sorry

lemma ProdStrata.exists_specializes_zeroLocus_ideal {E : Finset A}
    (x : PrimeSpectrum (ProdStrata E)) :
    ∃ y ∈ zeroLocus (ProdStrata.ideal E), x ⤳ y :=
  sorry

lemma ProdStrata.mem_zeroLocus_ideal_of_isClosed {E : Finset A} {x : PrimeSpectrum (ProdStrata E)}
    (hx : IsClosed {x}) : x ∈ zeroLocus (ProdStrata.ideal E) := by
  obtain ⟨y, hmem, hy⟩ := exists_specializes_zeroLocus_ideal x
  have := hy.mem_closed hx (by simp)
  grind only [= Set.mem_singleton_iff]

/-- If `E ⊆ F`, this is the canonical map `A_E → A_F`. -/
noncomputable def ProdStrata.map {E F : Finset A} (h : E ⊆ F) :
    ProdStrata E →ₐ[A] ProdStrata F :=
  Pi.algHom _ _ fun i ↦
    AlgHom.comp
      (Generalization.map <| by
        rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
        apply stratum_anti <;> simp)
      (Pi.evalAlgHom _ _ (i.restrict h))

lemma ProdStrata.map_apply {E F : Finset A} (h : E ⊆ F) (x : ProdStrata E)
    (i : Stratification.Index F) :
    ProdStrata.map h x i = Generalization.map (by
      rw [locClosedSubset_function_ideal, locClosedSubset_function_ideal]
      apply stratum_anti <;> simp) (x (i.restrict h)) := rfl

lemma ProdStrata.mapsTo_map_specComap {E F : Finset A} (h : E ⊆ F) :
    Set.MapsTo (PrimeSpectrum.comap (map h).toRingHom)
      (zeroLocus (ideal F)) (zeroLocus (ideal E)) := by
  classical
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
  refine fun z hz ↦ hp ?_
  change ∀ i, map h z i ∈ Generalization.ideal i.function i.ideal
  intro i
  rw [map_apply]
  refine Generalization.map_mem_ideal_of_strata _ ?_ ?_ _ ((Ideal.mem_pi _ z).mp hz _)
  · exact Ideal.span_mono (Finset.coe_subset.mpr Finset.inter_subset_right)
  · exact Finset.prod_dvd_prod_of_subset _ _ id Finset.inter_subset_right

variable (A) in
/-- The diagram whose colimit is the w-localization of `A`. -/
noncomputable def diag : Finset A ⥤ CommAlgCat A where
  obj E := .of A (ProdStrata E)
  map {E F} f := CommAlgCat.ofHom (ProdStrata.map <| leOfHom f)
  map_id E := sorry
  map_comp := sorry

variable (A) in
/-- The w-localization of a ring as an object of `CommAlgCat A` is the colimit over
the rings `A_E`. -/
noncomputable def commAlgCat : CommAlgCat A :=
  colimit (diag A)

noncomputable def colimitPresentation : ColimitPresentation (Finset A) (commAlgCat A) where
  diag := diag A
  ι := (colimit.cocone _).ι
  isColimit := colimit.isColimit _

end WLocalization

/-- The w-localization of a ring. -/
def WLocalization (A : Type u) [CommRing A] : Type _ :=
  WLocalization.commAlgCat A

namespace WLocalization

variable (A : Type u) [CommRing A]

noncomputable instance commRing : CommRing (WLocalization A) :=
  inferInstanceAs <| CommRing (WLocalization.commAlgCat A)

noncomputable instance algebra : Algebra A (WLocalization A) :=
  inferInstanceAs <| Algebra A (WLocalization.commAlgCat A)

noncomputable def ideal : Ideal (WLocalization A) :=
  ⨆ E : Finset A, Ideal.map (colimitPresentation.ι.app E).hom (ProdStrata.ideal E)

lemma bijOn_algebraMap_specComap_zeroLocus_ideal :
    Set.BijOn (PrimeSpectrum.comap <| algebraMap A (WLocalization A))
      (zeroLocus (ideal A)) .univ :=
  sorry

lemma exists_mem_zeroLocus_ideal_specializes (x : PrimeSpectrum (WLocalization A)) :
    ∃ y ∈ zeroLocus (ideal A), x ⤳ y :=
  sorry

lemma zeroLocus_ideal_eq : zeroLocus (ideal A) = closedPoints (PrimeSpectrum (WLocalization A)) :=
  sorry

instance isWLocalRing : IsWLocalRing (WLocalization A) :=
  sorry

instance (E : Finset A) : Finite (Stratification.Index E) := by
  classical
  refine Finite.of_injective (β := Set ↥E × Set ↥E)
    (fun i ↦ ((↑) ⁻¹' (i.left : Set A), (↑) ⁻¹' (i.right : Set A))) ?_
  rintro ⟨l₁, r₁, _, u₁⟩ ⟨l₂, r₂, _, u₂⟩ heq
  obtain ⟨hL, hR⟩ := Prod.mk.inj heq
  have aux : ∀ {s₁ s₂ : Finset A}, (s₁ : Set A) ⊆ E → (s₂ : Set A) ⊆ E →
      ((↑) : ↥E → A) ⁻¹' (s₁ : Set A) = ((↑) : ↥E → A) ⁻¹' (s₂ : Set A) → s₁ = s₂ := by
    intro s₁ s₂ h₁ h₂ hst
    ext a
    refine ⟨fun ha ↦ (Set.ext_iff.mp hst ⟨a, h₁ ha⟩).mp ha,
            fun ha ↦ (Set.ext_iff.mp hst ⟨a, h₂ ha⟩).mpr ha⟩
  have sub : ∀ {l r : Finset A}, (l : Set A) ∪ r = E →
      (l : Set A) ⊆ E ∧ (r : Set A) ⊆ E :=
    fun h ↦ ⟨fun a ha ↦ h ▸ Set.mem_union_left _ ha,
            fun a ha ↦ h ▸ Set.mem_union_right _ ha⟩
  obtain ⟨hl₁, hr₁⟩ := sub u₁
  obtain ⟨hl₂, hr₂⟩ := sub u₂
  exact (Stratification.Index.mk.injEq ..).mpr ⟨aux hl₁ hl₂ hL, aux hr₁ hr₂ hR⟩

lemma indZariski_prodStrata (E : Finset A) :
    Algebra.IndZariski A (ProdStrata E) := by
  change Algebra.IndZariski A
    (∀ i : Stratification.Index E, Generalization i.function i.ideal)
  exact Algebra.IndZariski.pi A _

instance indZariski : Algebra.IndZariski A (WLocalization A) := by
  have h := fun E => indZariski_prodStrata (A := A) E
  exact @Algebra.IndZariski.of_colimitPresentation A (WLocalization A) _ _ _
    (Finset A) _ _ colimitPresentation h

instance faithfullyFlat : Module.FaithfullyFlat A (WLocalization A) :=
  sorry

/-- If `V(I) ⊆ Spec A` consists only of closed points, then `V(I·WLocA) → V(I)` is a bijection.
This restricts the bijection `V(WLocalization.ideal A) ≃ Spec A` to `V(I·WLocA) ⊆ closedPoints`. -/
lemma bijOn_specComap_zeroLocus_map (I : Ideal A)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Set.BijOn (PrimeSpectrum.comap (algebraMap A (WLocalization A)))
      (zeroLocus (I.map (algebraMap A (WLocalization A)))) (zeroLocus I) := by
  have hsub : zeroLocus (I.map (algebraMap A (WLocalization A))) ⊆
      zeroLocus (WLocalization.ideal A : Set (WLocalization A)) := by
    rw [zeroLocus_ideal_eq]
    intro q hq
    simp only [mem_zeroLocus, SetLike.coe_subset_coe, mem_closedPoints_iff,
      isClosed_singleton_iff_isMaximal] at hq ⊢
    set m := PrimeSpectrum.comap (algebraMap A (WLocalization A)) q with hm_def
    have hm : m.asIdeal.IsMaximal := by
      simpa [isClosed_singleton_iff_isMaximal] using hI (Ideal.le_comap_of_map_le hq)
    have : q.asIdeal.LiesOver m.asIdeal := ⟨PrimeSpectrum.ext_iff.mp hm_def⟩
    letI := Localization.AtPrime.algebraOfLiesOver m.asIdeal q.asIdeal
    have : Algebra.IsSeparable m.asIdeal.ResidueField q.asIdeal.ResidueField :=
      Algebra.IndEtale.isSeparable_residueField (R := A) (S := WLocalization A) m.asIdeal
        q.asIdeal
    exact Ideal.IsMaximal.of_isAlgebraic m.asIdeal q.asIdeal
  have hbij := bijOn_algebraMap_specComap_zeroLocus_ideal A
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [mem_zeroLocus, SetLike.coe_subset_coe] at hp ⊢
    rwa [comap_asIdeal, ← Ideal.map_le_iff_le_comap]
  · exact hbij.injOn.mono hsub
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := hbij.surjOn (Set.mem_univ q)
    refine ⟨p, ?_, hpq⟩
    simp only [mem_zeroLocus, SetLike.coe_subset_coe] at hq ⊢
    have hpq' : p.asIdeal.comap (algebraMap A (WLocalization A)) = q.asIdeal := by
      rw [← comap_asIdeal, hpq]
    rw [Ideal.map_le_iff_le_comap, hpq']
    exact hq

/-- If `V(I) ⊆ Spec A` consists only of closed points, then the quotient map
`A/I → WLocA/(I·WLocA)` is bijective. -/
lemma quotientMap_algebraMap_bijective_of_ideal (I : Ideal A)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap A (WLocalization A)))
        (algebraMap A (WLocalization A)) I.le_comap_map) := by
  set f := algebraMap A (WLocalization A)
  set J := I.map f
  set φ := Ideal.quotientMap J f I.le_comap_map
  refine RingHom.BijectiveOnStalks.bijective_of_bijective ?_ ?_
  · exact (Algebra.IndZariski.bijectiveOnStalks_algebraMap A (WLocalization A)).quotientMap I
  · have hbij : Set.BijOn (PrimeSpectrum.comap f) (zeroLocus J) (zeroLocus I) :=
      bijOn_specComap_zeroLocus_map A I hI
    have hI_inj : Function.Injective (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
      PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hJ_inj : Function.Injective (PrimeSpectrum.comap (Ideal.Quotient.mk J)) :=
      PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have hI_range : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = zeroLocus I := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have hJ_range : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) = zeroLocus J := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    have hcomm : ∀ y : PrimeSpectrum (WLocalization A ⧸ J),
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap φ y) =
          PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) y) := fun y ↦ by
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
        Ideal.quotientMap_comp_mk]
    refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
    · have hx : PrimeSpectrum.comap (Ideal.Quotient.mk J) x ∈ zeroLocus J :=
        hJ_range ▸ Set.mem_range_self x
      have hy : PrimeSpectrum.comap (Ideal.Quotient.mk J) y ∈ zeroLocus J :=
        hJ_range ▸ Set.mem_range_self y
      have heq : PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) x) =
          PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk J) y) := by
        rw [← hcomm, ← hcomm, hxy]
      exact hJ_inj (hbij.injOn hx hy heq)
    · obtain ⟨y', hy'mem, hy'⟩ := hbij.surjOn (hI_range ▸ Set.mem_range_self x)
      obtain ⟨y, rfl⟩ : ∃ y, PrimeSpectrum.comap (Ideal.Quotient.mk J) y = y' := by
        rwa [← Set.mem_range, hJ_range]
      exact ⟨y, hI_inj <| (hcomm y).trans hy'⟩

open PrimeSpectrum

end WLocalization
