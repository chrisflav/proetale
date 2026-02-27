/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Proetale.Algebra.IndZariski
import Proetale.Algebra.Etale

/-!
# Ind-étale algebras

In this file we define ind-étale algebras and ring homomorphisms.
-/

universe u

open CategoryTheory Limits TensorProduct

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The object property on commutative `R`-algebras of being étale. -/
def CommAlgCat.etale : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.Etale R S

lemma CommAlgCat.etale_eq : etale R = RingHom.toObjectProperty RingHom.Etale R := by
  ext S
  exact RingHom.etale_algebraMap.symm

/-- An algebra is ind-étale if it can be written as the filtered colimit of étale
algebras. -/
@[mk_iff]
class Algebra.IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.Etale R (P.diag.obj i)

namespace Algebra.IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma iff_ind_etale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u} (CommAlgCat.etale R) (.of R S) :=
  Algebra.indEtale_iff R S

/-- If `R → S` is ind-étale and `S → A` is étale, then `R → A` is ind-étale.
This is the key technical step for transitivity: ind(étale) ∘ étale ⊆ ind(étale).
The proof uses PreIndSpreads to descend the étale map S → A to a finite level S_j → A',
then forms pushouts along the filtered colimit diagram for S to recover A as a
filtered colimit of étale R-algebras. -/
private lemma of_indEtale_etale (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra.IndEtale R S] [Algebra.Etale S A] :
    Algebra.IndEtale R A := by
  -- Uses PreIndSpreads to descend S → A to a finite level S_j → A',
  -- then forms pushouts along the filtered colimit diagram for S to recover A as a
  -- filtered colimit of étale R-algebras.
  -- The full proof has type coercion issues in CommRingCat; left as sorry.
  sorry

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T := by
  -- Strategy: T = colim D_j in CommRingCat (from IndEtale S T, each S → D_j étale).
  -- For each j, R → D_j is ind(étale) by of_indEtale_etale.
  -- Then R → T is ind(ind(étale)) = ind(étale) by ind_ind.
  -- Convert to MorphismProperty.ind level.
  suffices MorphismProperty.ind.{u} CommRingCat.etale
      (CommRingCat.ofHom (algebraMap R T)) by
    rw [iff_ind_etale, CommAlgCat.etale_eq,
      ← RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]
    exact this
  -- Convert IndEtale S T to MorphismProperty.ind form.
  have hST : MorphismProperty.ind.{u} CommRingCat.etale
      (CommRingCat.ofHom (algebraMap S T)) := by
    have : Algebra.IndEtale S T := inferInstance
    rwa [iff_ind_etale S, CommAlgCat.etale_eq,
      ← RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  obtain ⟨J, hJ, hFilt, D, s₂, t₂, ht₂, hst₂⟩ := hST
  -- For each j, R → D_j is ind(etale) by of_indEtale_etale.
  have hIndEtale_j : ∀ j, MorphismProperty.ind.{u} CommRingCat.etale
      (CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j) := by
    intro j
    have hEtale_j : (s₂.app j).hom.Etale := (hst₂ j).1
    letI : Algebra S (D.obj j) := (s₂.app j).hom.toAlgebra
    letI : Algebra R (D.obj j) :=
      ((CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j).hom).toAlgebra
    haveI : IsScalarTower R S (D.obj j) := .of_algebraMap_eq' rfl
    haveI : Algebra.Etale S (D.obj j) := RingHom.etale_algebraMap.mp hEtale_j
    have := of_indEtale_etale R S (D.obj j)
    rwa [iff_ind_etale, CommAlgCat.etale_eq,
      ← RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  -- R → T is ind(ind(etale)): T = colim D_j with each R → D_j being ind(etale).
  have hind_ind : MorphismProperty.ind.{u} (MorphismProperty.ind.{u} CommRingCat.etale)
      (CommRingCat.ofHom (algebraMap R T)) :=
    ⟨J, hJ, hFilt, D,
      (Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂,
      t₂, ht₂, fun j => ⟨hIndEtale_j j, by
        -- Goal: ((Functor.const J).map (ofHom (algebraMap R S)) ≫ s₂).app j ≫ t₂.app j
        --       = ofHom (algebraMap R T)
        -- This is: ofHom (algebraMap R S) ≫ s₂.app j ≫ t₂.app j = ofHom (algebraMap R T)
        -- By (hst₂ j).2: s₂.app j ≫ t₂.app j = ofHom (algebraMap S T)
        -- So LHS = ofHom (algebraMap R S) ≫ ofHom (algebraMap S T) = ofHom (algebraMap R T)
        -- by IsScalarTower.
        show ((Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂).app j ≫ t₂.app j =
          CommRingCat.ofHom (algebraMap R T)
        simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app, Category.assoc]
        -- after simp, the goal should be in a simplified form
        -- try to just use (hst₂ j).2 at the element level
        ext x
        show (t₂.app j).hom ((s₂.app j).hom ((algebraMap R S) x)) = (algebraMap R T) x
        have h := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp (hst₂ j).2) ((algebraMap R S) x)
        simp only [CommRingCat.comp_apply] at h
        rw [h]; exact (IsScalarTower.algebraMap_apply R S T x).symm⟩⟩
  -- By ind_ind: ind(ind(etale)) = ind(etale).
  have key : MorphismProperty.ind.{u} (MorphismProperty.ind.{u} CommRingCat.etale) =
      MorphismProperty.ind.{u} CommRingCat.etale :=
    MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable
  rw [key] at hind_ind
  exact hind_ind

private lemma etale_le_isFinitelyPresentable :
    CommAlgCat.etale R ≤ ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := by
  intro S hS
  -- hS : Algebra.Etale R S, which implies algebraMap R S is FinitePresentation.
  have hfp : RingHom.FinitePresentation (algebraMap R S) :=
    (RingHom.etale_algebraMap.mpr hS).2
  -- Transfer via commAlgCatEquivUnder: Under version is finitely presentable.
  have hunder : IsFinitelyPresentable.{u}
      ((commAlgCatEquivUnder (.of R)).functor.obj S) :=
    CommRingCat.isFinitelyPresentable_under _ _ (by convert hfp using 1)
  -- Transfer back via the equivalence.
  haveI : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact (@isCardinalPresentable_iff_of_isEquivalence
    (CommAlgCat.{u} R) _ S (Cardinal.aleph0 : Cardinal.{u}) this
    (Under (CommRingCat.of.{u} R)) _
    (commAlgCatEquivUnder (.of R)).functor inferInstance).mp hunder

theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndEtale R (P.diag.obj i)) : Algebra.IndEtale R S := by
  rw [iff_ind_etale]
  have h' : ∀ (i : ι), ObjectProperty.ind.{u} (CommAlgCat.etale R) (P.diag.obj i) :=
    fun i => (iff_ind_etale R (P.diag.obj i)).mp (h i)
  -- Each P.diag.obj i satisfies ind (etale R), so S satisfies ind (ind (etale R)).
  have hind_ind : ObjectProperty.ind.{u} (ObjectProperty.ind.{u} (CommAlgCat.etale R))
      (.of R S) :=
    ⟨ι, ‹_›, ‹_›, P, h'⟩
  -- By ind_ind (etale R ≤ isFinitelyPresentable), ind (ind (etale R)) = ind (etale R).
  rwa [ObjectProperty.ind_ind (etale_le_isFinitelyPresentable R)] at hind_ind

private lemma isLocalIso_le_etale (R : Type u) [CommRing R] :
    CommAlgCat.isLocalIso R ≤ CommAlgCat.etale R := by
  intro X (hX : Algebra.IsLocalIso R X)
  show Algebra.Etale R X
  rw [← RingHom.etale_algebraMap]
  let s : Set X := {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgm, hstd⟩ := hX.exists_notMem_isStandardOpenImmersion m
    exact hgm (hms (Ideal.subset_span (show g ∈ s from hstd)))
  exact RingHom.Etale.ofLocalizationSpanTarget (algebraMap R X) s hs (fun ⟨g, hg⟩ => by
    -- hg : Algebra.IsStandardOpenImmersion R (Localization.Away g)
    -- Goal: RingHom.Etale ((algebraMap X (Localization.Away g)).comp (algebraMap R X))
    -- This composition equals algebraMap R (Localization.Away g) via IsScalarTower
    obtain ⟨r, hr⟩ := hg.exists_away
    -- hr : IsLocalization.Away r (Localization.Away g) as R-algebra
    haveI : Algebra.Etale R (Localization.Away g) := Algebra.Etale.of_isLocalizationAway r
    rw [show (algebraMap X (Localization.Away g)).comp (algebraMap R X) =
      algebraMap R (Localization.Away g) from by
      ext x; simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R X]]
    exact RingHom.etale_algebraMap.mpr inferInstance)

instance (priority := 100) of_indZariski [IndZariski R S] : IndEtale R S := by
  rw [iff_ind_etale]
  rw [Algebra.IndZariski.iff_ind_isLocalIso] at *
  exact ObjectProperty.ind_mono (isLocalIso_le_etale R) _ ‹_›


-- Helper: if A is etale over a field k, and we have a k-algebra hom to a local ring B,
-- then every element's image has separable minimal polynomial.
-- Uses the product decomposition A ≅ ∏ Lᵢ (finite separable field extensions)
-- and the fact that the map factors through one component (idempotent argument).
-- In a local ring, every idempotent is 0 or 1.
private lemma IsIdempotentElem.eq_zero_or_one_of_isLocalRing {R : Type*} [CommRing R]
    [IsLocalRing R] {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h1 : e + (1 - e) = 1 := by ring
  have h2 : e * (1 - e) = 0 := by
    have heq := he.eq  -- e * e = e
    have : e * (1 - e) = e - e * e := by ring
    rw [this, heq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with hu | hu
  · -- e is a unit; from e * (1 - e) = 0, get 1 - e = 0, hence e = 1.
    right
    have h3 := hu.mul_right_eq_zero.mp h2
    -- h3 : 1 - e = 0, want e = 1
    exact (sub_eq_zero.mp h3).symm
  · -- 1 - e is a unit; from (1 - e) * e = 0, get e = 0.
    left
    have h3 : (1 - e) * e = 0 := by rw [mul_comm]; exact h2
    exact hu.mul_right_eq_zero.mp h3

-- Helper: an AlgHom from a product of fields to a local ring factors through one component.
-- More precisely, there exists an index j such that ψ(Pi.single j 1) = 1.
private lemma exists_unique_index_of_algHom_pi_to_local
    {k : Type u} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra k (Ai i)]
    {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B] [Nontrivial B]
    (ψ : (∀ i, Ai i) →ₐ[k] B) :
    ∃ j : I, ψ (Pi.single j 1) = 1 ∧ ∀ i, i ≠ j → ψ (Pi.single i 1) = 0 := by
  have hcoi : CompleteOrthogonalIdempotents
      (fun i : I => Pi.single (M := fun i => Ai i) i (1 : Ai i)) :=
    CompleteOrthogonalIdempotents.single (fun i => Ai i)
  have hidem : ∀ i, IsIdempotentElem (ψ (Pi.single i 1)) :=
    fun i => (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.idem i
  have h01 : ∀ i, ψ (Pi.single i 1) = 0 ∨ ψ (Pi.single i 1) = 1 :=
    fun i => IsIdempotentElem.eq_zero_or_one_of_isLocalRing (hidem i)
  have hsum : ∑ i : I, ψ (Pi.single i 1) = 1 := by
    rw [← map_sum]; simp [hcoi.complete]
  have hortho : ∀ i j, i ≠ j → ψ (Pi.single i 1) * ψ (Pi.single j 1) = 0 := by
    intro i j hij
    have := (hcoi.map ψ.toRingHom).toOrthogonalIdempotents.ortho hij
    -- `this` is about `(ψ.toRingHom ∘ fun i => Pi.single i 1) i * ... j = 0`
    -- which simplifies to `ψ (Pi.single i 1) * ψ (Pi.single j 1) = 0`
    simpa [Function.comp_def] using this
  have : ∃ j, ψ (Pi.single j 1) = 1 := by
    by_contra hall; push_neg at hall
    have : ∀ i, ψ (Pi.single i 1) = 0 := fun i => (h01 i).resolve_right (hall i)
    simp [this] at hsum
  obtain ⟨j, hj⟩ := this
  exact ⟨j, hj, fun i hi => by
    have := hortho i j hi; rw [hj, mul_one] at this; exact this⟩

-- Helper: build the k-algebra hom from Ai j to B through the product, given the special index j.
private noncomputable def algHomSingleComponent
    {k : Type u} [Field k] {I : Type*} [Fintype I] [DecidableEq I]
    {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra k (Ai i)]
    {B : Type u} [CommRing B] [Algebra k B] [IsLocalRing B]
    (ψ : (∀ i, Ai i) →ₐ[k] B) (j : I)
    (hj : ψ (Pi.single j 1) = 1)
    (hothers : ∀ i, i ≠ j → ψ (Pi.single i 1) = 0) : Ai j →ₐ[k] B where
  toFun y := ψ (Pi.single j y)
  map_one' := hj
  map_mul' y1 y2 := by
    show ψ (Pi.single j (y1 * y2)) = ψ (Pi.single j y1) * ψ (Pi.single j y2)
    rw [Pi.single_mul, map_mul]
  map_zero' := by simp [map_zero]
  map_add' y1 y2 := by
    show ψ (Pi.single j (y1 + y2)) = ψ (Pi.single j y1) + ψ (Pi.single j y2)
    have : Pi.single j (y1 + y2) = Pi.single j y1 + Pi.single j y2 := by
      ext i
      by_cases hij : i = j
      · subst hij; simp [Pi.single_eq_same]
      · -- i ≠ j case: Pi.single j x i = 0 for any x
        have h1 := Pi.single_eq_of_ne hij (y1 + y2)
        have h2 := Pi.single_eq_of_ne hij y1
        have h3 := Pi.single_eq_of_ne hij y2
        simp only [Pi.add_apply, h1, h2, h3, add_zero]
    rw [this, map_add]
  commutes' c := by
    show ψ (Pi.single j (algebraMap k (Ai j) c)) = algebraMap k B c
    -- Pi.single j (algebraMap k (Ai j) c) = (algebraMap k (∀ i, Ai i) c) * Pi.single j 1
    have heq : Pi.single j (algebraMap k (Ai j) c) =
        (algebraMap k (∀ i, Ai i) c) * Pi.single j 1 := by
      ext i
      by_cases hij : i = j
      · subst hij; simp [Pi.single_eq_same, Pi.mul_apply, Pi.algebraMap_apply]
      · have h1 := Pi.single_eq_of_ne hij (algebraMap k (Ai j) c)
        have h2 := Pi.single_eq_of_ne hij (1 : Ai j)
        simp only [Pi.mul_apply, Pi.algebraMap_apply, h1, h2, mul_zero]
    rw [heq, map_mul, AlgHom.commutes, hj, mul_one]

private lemma isSeparable_of_etale_to_local (k : Type u) [Field k] (A : Type u) [CommRing A]
    [Algebra k A] [Algebra.Etale k A] (B : Type u) [CommRing B] [Algebra k B] [IsLocalRing B]
    (φ : A →ₐ[k] B) (a : A) : IsSeparable k (φ a) := by
  -- If B is trivial, everything is separable.
  by_cases hB : Nontrivial B
  · -- Product decomposition: A ≅_k ∏ Lᵢ (finite separable field extensions).
    haveI : Module.Finite k A := FormallyUnramified.finite_of_free k A
    obtain ⟨I, hfin, Ai, hfield, halg, e, hprop⟩ :=
      (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := A)).mp inferInstance
    haveI := hfin; haveI : Fintype I := Fintype.ofFinite I
    letI (i : I) : Field (Ai i) := hfield i
    letI (i : I) : Algebra k (Ai i) := halg i
    classical
    -- Compose to get ψ : ∏ Ai → B.
    let ψ : (∀ i, Ai i) →ₐ[k] B := φ.comp e.symm.toAlgHom
    -- Find the unique index j with ψ(Pi.single j 1) = 1.
    obtain ⟨j, hj, hothers⟩ := exists_unique_index_of_algHom_pi_to_local ψ
    -- Build the algebra hom τ : Ai j →ₐ[k] B.
    let τ := algHomSingleComponent ψ j hj hothers
    -- φ(a) = ψ(e a) and ψ(x) = ψ(Pi.single j (x j)) for all x.
    have hfactor : ∀ x : ∀ i, Ai i, ψ x = τ (x j) := by
      intro x
      show ψ x = ψ (Pi.single j (x j))
      conv_lhs => rw [← Finset.univ_sum_single x]
      rw [map_sum]
      apply Finset.sum_eq_single_of_mem j (Finset.mem_univ _)
      intro i _ hi
      have : Pi.single (M := fun i => Ai i) i (x i) = Pi.single i 1 * x := by
        rw [← Pi.single_mul_left]; simp
      rw [this, map_mul, hothers i hi, zero_mul]
    have hφa : φ a = τ ((e a) j) := by
      -- τ ((e a) j) = ψ (Pi.single j ((e a) j)) by definition
      -- hfactor says ψ (e a) = τ ((e a) j)
      -- and ψ (e a) = (φ.comp e.symm.toAlgHom) (e a) = φ (e.symm (e a)) = φ a
      have h1 := hfactor (e a)
      -- h1 : ψ (e a) = τ ((e a) j)
      rw [← h1]
      -- goal: φ a = ψ (e a), i.e., φ a = (φ.comp e.symm.toAlgHom) (e a)
      simp [ψ, AlgHom.comp_apply, AlgEquiv.symm_apply_apply]
    -- Conclude: (e a) j ∈ Ai j, which is a finite separable field extension of k.
    rw [hφa]
    -- τ is a k-algebra hom from a finite separable field extension to B.
    -- minpoly k (τ b) | minpoly k b by Polynomial.aeval_algHom_apply + minpoly.dvd.
    -- minpoly k b is separable since Ai j is separable over k.
    have hfin_j : Module.Finite k (Ai j) := (hprop j).1
    have hsep_j : Algebra.IsSeparable k (Ai j) := (hprop j).2
    set b := (e a) j with hb_def
    have hb_sep : IsSeparable k b := Algebra.IsSeparable.isSeparable k b
    have hdvd : minpoly k (τ b) ∣ minpoly k b :=
      minpoly.dvd k (τ b) (by
        rw [Polynomial.aeval_algHom_apply]; simp [minpoly.aeval])
    exact hb_sep.of_dvd hdvd
  · -- B is not nontrivial, so B is trivial (subsingleton).
    haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
    -- In the zero ring, everything is zero. The polynomial 1 annihilates φ a.
    have hint : IsIntegral k (φ a) :=
      ⟨Polynomial.X, Polynomial.monic_X, by simp [Subsingleton.elim (φ a) 0]⟩
    have hdvd1 : minpoly k (φ a) ∣ 1 :=
      minpoly.dvd k (φ a) (by simp [Subsingleton.elim (Polynomial.aeval (φ a) 1) 0])
    have heq1 : minpoly k (φ a) = 1 :=
      (minpoly.monic hint).eq_one_of_isUnit (isUnit_of_dvd_one hdvd1)
    rw [IsSeparable, heq1]
    exact Polynomial.separable_one

instance isSeparable (k : Type u) [Field k] [hAlg : Algebra k R] [IndEtale k R] [IsLocalRing R] :
    Algebra.IsSeparable k R := by
  obtain ⟨ι, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := k) (S := R)
  letI := hcat; letI := hfilt
  constructor
  intro x
  -- Use that the colimit is jointly surjective: find preimage of x in some P.diag.obj i.
  have hcolim : IsColimit ((forget (CommAlgCat.{u} k)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} k)) P.isColimit
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hcolim x
  -- ha : (forget ...).map (P.ι.app i) a = x, i.e., (P.ι.app i).hom a = x
  rw [← ha]
  haveI : Algebra.Etale k (P.diag.obj i) := hP i
  exact @isSeparable_of_etale_to_local k _ (P.diag.obj i) _ _ _ R _ hAlg _ (P.ι.app i).hom a

-- Helper: for s : S with R → S ind-étale, the image of s in q.ResidueField is separable
-- over p.ResidueField. Uses base change of the étale algebra Aᵢ to p.ResidueField,
-- then applies isSeparable_of_etale_to_local.
set_option maxHeartbeats 400000 in
private lemma isSeparable_image_of_indEtale [Algebra.IndEtale R S]
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    (s : S) : IsSeparable (Ideal.ResidueField p) (algebraMap S (Ideal.ResidueField q) s) := by
  -- Write S as filtered colimit of étale R-algebras Aᵢ
  obtain ⟨ι, hcat, hfilt, P, hP⟩ := IndEtale.exists_colimitPresentation (R := R) (S := S)
  letI := hcat; letI := hfilt
  -- Lift s to some Aᵢ
  have hcolim : IsColimit ((forget (CommAlgCat.{u} R)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} R)) P.isColimit
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hcolim s
  haveI : Algebra.Etale R (P.diag.obj i) := hP i
  -- The map Aᵢ → S → κ(q) as R-algebra hom
  have himage : algebraMap S (Ideal.ResidueField q) s =
      algebraMap S (Ideal.ResidueField q) ((P.ι.app i).hom a) :=
    congrArg (algebraMap S (Ideal.ResidueField q)) ha.symm
  rw [himage]
  -- Factor through base change: κ(p) ⊗[R] Aᵢ is étale over κ(p)
  -- Build the R-algebra hom φ : Aᵢ → κ(q) and the κ(p)-algebra hom Φ : κ(p) ⊗[R] Aᵢ → κ(q)
  let φ : (P.diag.obj i : Type u) →ₐ[R] (Ideal.ResidueField q) :=
    (IsScalarTower.toAlgHom R S (Ideal.ResidueField q)).comp (P.ι.app i).hom
  -- Explicitly ensure Algebra R κ(p) is available for tensor product
  letI : Algebra R (Ideal.ResidueField p) := inferInstance
  let Φ : ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) →ₐ[Ideal.ResidueField p]
      (Ideal.ResidueField q) :=
    Algebra.TensorProduct.lift
      (Algebra.ofId (Ideal.ResidueField p) (Ideal.ResidueField q))
      φ (fun _ _ => Commute.all _ _)
  -- Φ(1 ⊗ a) = φ(a) = algebraMap S κ(q) ((P.ι.app i).hom a)
  have hΦ : Φ (1 ⊗ₜ[R] a) = algebraMap S (Ideal.ResidueField q) ((P.ι.app i).hom a) := by
    show (Algebra.ofId (Ideal.ResidueField p) (Ideal.ResidueField q)) 1 * φ a = _
    simp [Algebra.ofId_apply, φ, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
  rw [← hΦ]
  -- κ(p) ⊗[R] Aᵢ is étale over κ(p) (base change of étale along R → κ(p) is étale)
  -- All instances (rightAlgebra, scalar towers, IsPushout) are built inside the by block
  -- to avoid leaking them and confusing instance search.
  haveI : Algebra.Etale (Ideal.ResidueField p)
      ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) := by
    rw [← RingHom.etale_algebraMap]
    letI : Algebra (↥(P.diag.obj i))
        ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : IsScalarTower R (↥(P.diag.obj i))
        ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) :=
      Algebra.TensorProduct.right_isScalarTower
    haveI hst : IsScalarTower R (Ideal.ResidueField p)
        ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) :=
      .of_algebraMap_eq' rfl
    exact @RingHom.Etale.isStableUnderBaseChange R (↥(P.diag.obj i)) (Ideal.ResidueField p)
      ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u))
      _ _ _ _
      _ _ _ _ _
      _ hst
      TensorProduct.isPushout'
      (RingHom.etale_algebraMap.mpr ‹Algebra.Etale R (P.diag.obj i)›)
  -- κ(q) is a field, hence a local ring — apply isSeparable_of_etale_to_local
  exact isSeparable_of_etale_to_local (Ideal.ResidueField p)
    ((Ideal.ResidueField p) ⊗[R] (P.diag.obj i : Type u)) (Ideal.ResidueField q) Φ (1 ⊗ₜ[R] a)

set_option maxHeartbeats 800000 in
instance isSeparable_residueField [Algebra.IndEtale R S] (p : Ideal R) (q : Ideal S)
    [q.LiesOver p] [p.IsPrime] [q.IsPrime] :
    Algebra.IsSeparable (Ideal.ResidueField p) (Ideal.ResidueField q) := by
  set κp := Ideal.ResidueField p
  set κq := Ideal.ResidueField q
  constructor
  intro x
  -- Every element of κ(q) = FractionField(S/q) can be written as a/b
  -- with a, b ∈ S/q, and each element of S/q is the image of some s ∈ S.
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := S ⧸ q) (K := κq) x
  rw [← hab]
  -- Lift a, b from S/q to S
  obtain ⟨sa, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨sb, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- algebraMap (S ⧸ q) κq (Ideal.Quotient.mk q s) = algebraMap S κq s
  -- These are definitionally equal via IsScalarTower R (S ⧸ q) κq
  change IsSeparable κp (algebraMap (S ⧸ q) κq (Ideal.Quotient.mk q sa) /
    algebraMap (S ⧸ q) κq (Ideal.Quotient.mk q sb))
  rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk]
  -- div = mul * inv
  rw [div_eq_mul_inv]
  exact Field.isSeparable_mul
    (isSeparable_image_of_indEtale R S p q sa)
    (Field.isSeparable_inv (isSeparable_image_of_indEtale R S p q sb))

end Algebra.IndEtale

/-- A ring hom is ind-étale if and only if it is an ind-étale algebra. -/
@[algebraize Algebra.IndEtale]
def RingHom.IndEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndEtale R S

namespace RingHom.IndEtale

variable (S) in
lemma algebraMap_iff : (algebraMap R S).IndEtale ↔ Algebra.IndEtale R S :=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

lemma iff_ind_etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u} CommRingCat.etale (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndEtale, Algebra.IndEtale.iff_ind_etale, ← f.algebraMap_toAlgebra,
    CommAlgCat.etale_eq,
    ← RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]
  rfl

/-- A ring hom is ind-étale if and only if it can be written as a colimit of étale ring homs. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndEtale ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S) (_ : IsColimit (.mk _ c)),
      ∀ i, (t.app i).hom.Etale ∧ t.app i ≫ c.app i = f :=
  RingHom.IndEtale.iff_ind_etale _

variable {R S : Type u} [CommRing R] [CommRing S]

lemma comp {T : Type u} [CommRing T] {g : S →+* T} {f : R →+* S} (hg : g.IndEtale)
    (hf : f.IndEtale) : (g.comp f).IndEtale := by
  algebraize [f, g, (g.comp f)]
  exact Algebra.IndEtale.trans R S T

lemma isStableUnderBaseChange : IsStableUnderBaseChange IndEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush hRS
  rw [iff_ind_etale] at hRS ⊢
  rw [← CommRingCat.isPushout_iff_isPushout] at hpush
  exact (inferInstance : (MorphismProperty.ind CommRingCat.etale).IsStableUnderCobaseChange).1
    hpush.flip hRS

/-- Ind-étale is equivalent to ind-ind-étale. -/
lemma iff_ind_indEtale (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndEtale) (CommRingCat.ofHom f) := by
  rw [iff_ind_etale]
  have heq : RingHom.toMorphismProperty RingHom.IndEtale =
      MorphismProperty.ind.{u} CommRingCat.etale := by
    ext X Y g
    exact iff_ind_etale g.hom
  rw [heq]; constructor
  · exact MorphismProperty.le_ind _ _
  · intro h
    have key : MorphismProperty.ind.{u} (MorphismProperty.ind.{u} CommRingCat.etale) =
        MorphismProperty.ind.{u} CommRingCat.etale :=
      MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable
    rw [key] at h; exact h

/-- A ring hom is ind-étale if it can be written as a filtered colimit of ind-étale maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndEtale ∧ t.app i ≫ c.app i = f) : f.hom.IndEtale :=
  (iff_ind_indEtale _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

private lemma indEtale_respectsIso :
    RingHom.RespectsIso
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndEtale) := by
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  have heq : RingHom.toMorphismProperty
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndEtale) =
      MorphismProperty.ind.{u} CommRingCat.etale := by
    ext X Y g
    exact iff_ind_etale g.hom
  rw [heq]
  infer_instance

theorem _root_.Algebra.IndEtale.iff_ind_indEtale [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndEtale R) (.of R S) :=
  (algebraMap_iff (R := R) S).symm.trans
    ((RingHom.IndEtale.iff_ind_indEtale _).trans
      indEtale_respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty)

lemma _root_.RingHom.IndZariski.indEtale {f : R →+* S}
    (hf : f.IndZariski) : f.IndEtale := by
  algebraize [f]
  exact .of_indZariski R S

end RingHom.IndEtale
