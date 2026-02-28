/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.StalkAlgebraic
import Proetale.Mathlib.RingTheory.Ideal.GoingDown

/-!
# w-localization w.r.t an ideal

In this file, we define the w-localization w.r.t an ideal and prove [Tag 097A, Stacks Project].

Let `A` be a w-local ring. Let `I ⊆ A` be an ideal cutting out the set `X^c` of closed points
in `X = Spec(A)`. Let `A → B` be a ring map inducing algebraic extensions on residue fields at
primes. Then there exists an ind-Zariski ring map `B → C` such that

- `B/IB → C/IC` is an isomorphism,
- `C` is w-local
- the map `p : Y = Spec C → X` induced by the ring map `A → B → C` is w-local, and
- `p⁻¹(X^c)` is the set of closed points of `Y`.

In particular, the composition `A → B → C` is faithfully flat if `A → B` is faithfully flat.
-/

universe u

open WLocalization PrimeSpectrum

variable {A B : Type u} [CommRing A] [CommRing B] (I :Ideal A)

instance isWLocalRing_generalization_one [IsWLocalRing A] : IsWLocalRing (Generalization 1 I) := by
  constructor
  have hemb : Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) :=
    PrimeSpectrum.localization_comap_isEmbedding (Generalization 1 I) (Generalization.submonoid 1 I)
  have hrange : Set.range (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) =
      generalizationHull (Generalization.locClosedSubset 1 I) :=
    Generalization.range_algebraMap_generalization 1 I
  have hloc : Generalization.locClosedSubset 1 I = zeroLocus (I : Set A) := by
    simp [Generalization.locClosedSubset, basicOpen_one, TopologicalSpace.Opens.coe_top]
  have hstable : StableUnderSpecialization (generalizationHull (Generalization.locClosedSubset 1 I)) := by
    rw [hloc]
    exact (isClosed_zeroLocus _).stableUnderSpecialization.generalizationHull_of_wLocalSpace
  exact hemb.wLocalSpace_of_stableUnderSpecialization_range (hrange ▸ hstable)

variable {I}

-- Helper: BijectiveOnStalks implies algebraic extensions on residue fields.
-- If f : A →+* B has bijective stalk maps, then for any prime q lying over m,
-- the residue field extension κ(m) → κ(q) is algebraic (in fact, an isomorphism).
private lemma bijectiveOnStalks_isAlgebraic_residueField
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hbij : (algebraMap R S).BijectiveOnStalks)
    (m : Ideal R) (q : Ideal S) [m.IsMaximal] [q.IsPrime] [q.LiesOver m] :
    Algebra.IsAlgebraic m.ResidueField q.ResidueField := by
  -- BijectiveOnStalks implies SurjectiveOnStalks
  have hsurj : (algebraMap R S).SurjectiveOnStalks := fun p hp => (hbij p).surjective
  -- SurjectiveOnStalks gives bijective ResidueField.map
  have hmap_bij : Function.Bijective
      (Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)) :=
    hsurj.residueFieldMap_bijective m q (q.over_def m)
  -- The ResidueField.map and algebraMap agree on elements from R (the base ring)
  -- Use the mapₐ construction which is an R-algebra hom
  let φ : m.ResidueField →ₐ[R] q.ResidueField :=
    Ideal.ResidueField.mapₐ m q (Algebra.ofId R S) (q.over_def m)
  -- φ as a ring hom equals ResidueField.map
  have hφ_eq : (φ : m.ResidueField →+* q.ResidueField) =
      Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m) := rfl
  -- φ is an AlgHom, so it equals the algebraMap between residue fields
  -- because both are R-algebra homs from m.ResidueField (a localization of R/m)
  -- to q.ResidueField, and they agree on R (by being R-algebra maps).
  -- By Ideal.ResidueField.algHom_ext, they are equal.
  have hφ_eq_algMap : (φ : m.ResidueField →+* q.ResidueField) =
      algebraMap m.ResidueField q.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext (I := m) (S := q.ResidueField)
    ext r
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    -- φ (algebraMap R m.ResidueField r) = algebraMap R q.ResidueField r (since φ is an R-alg hom)
    rw [φ.commutes]
    -- algebraMap m.ResidueField q.ResidueField (algebraMap R m.ResidueField r) =
    -- algebraMap R q.ResidueField r (by scalar tower)
    exact IsScalarTower.algebraMap_apply R m.ResidueField q.ResidueField r
  -- Transfer bijectivity: ResidueField.map = algebraMap
  have hmap_bij' : Function.Bijective (algebraMap m.ResidueField q.ResidueField) := by
    have : (algebraMap m.ResidueField q.ResidueField) =
        (Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)) := by
      rw [← hφ_eq_algMap, hφ_eq]
    rwa [this]
  -- Since algebraMap is bijective (hence surjective), Module.Finite, hence IsAlgebraic
  haveI : Module.Finite m.ResidueField q.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap m.ResidueField q.ResidueField)
      hmap_bij'.surjective
  exact Algebra.IsAlgebraic.of_finite m.ResidueField q.ResidueField

-- Helper: I.map algebraMap ≤ Generalization.ideal 1 I
private lemma Ideal_map_le_ideal_one (I : Ideal A) :
    I.map (algebraMap A (Generalization 1 I)) ≤ Generalization.ideal 1 I := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  show algebraMap A (Generalization 1 I) x ∈ Generalization.ideal 1 I
  rw [Generalization.ideal, RingHom.mem_ker]
  -- toLocQuotient is an A-algebra map, so toLocQuotient (algebraMap x) = algebraMap x
  rw [show (Generalization.toLocQuotient 1 I) (algebraMap A (Generalization 1 I) x) =
      algebraMap A (Localization.Away (Ideal.Quotient.mk I 1)) x from
    AlgHom.commutes (Generalization.toLocQuotient 1 I) x]
  -- algebraMap A (Localization.Away(mk I 1)) factors through A/I
  show (algebraMap (A ⧸ I) (Localization.Away (Ideal.Quotient.mk I 1)))
    ((algebraMap A (A ⧸ I)) x) = 0
  rw [show (algebraMap A (A ⧸ I)) x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq [IsWLocalRing A]
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A (Generalization 1 I))) =
    closedPoints (PrimeSpectrum (Generalization 1 I)) := by
  have hemb : Topology.IsEmbedding (PrimeSpectrum.comap (algebraMap A (Generalization 1 I))) :=
    PrimeSpectrum.localization_comap_isEmbedding (Generalization 1 I) (Generalization.submonoid 1 I)
  ext q
  constructor
  · -- zeroLocus(I.map) ⊆ closedPoints
    -- If q ∈ V(I·S), then comap q ∈ V(I) ⊆ closedPoints, so {comap q} is closed.
    -- Preimage of {comap q} under comap is closed, and equals {q} by injectivity.
    intro hq
    rw [mem_closedPoints_iff]
    have hcomap_mem : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q ∈
        zeroLocus (I : Set A) := by
      rw [mem_zeroLocus, SetLike.coe_subset_coe]
      exact Ideal.le_comap_of_map_le ((mem_zeroLocus _ _).mp hq)
    have hclosed_comap : IsClosed ({PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q} :
        Set (PrimeSpectrum A)) := by
      rw [← mem_closedPoints_iff]
      exact hI hcomap_mem
    have hpreimage_closed : IsClosed
        (PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) ⁻¹'
          {PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q}) :=
      hclosed_comap.preimage hemb.continuous
    have : PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) ⁻¹'
        {PrimeSpectrum.comap (algebraMap A (Generalization 1 I)) q} = {q} := by
      rw [← Set.image_singleton, hemb.injective.preimage_image]
    rwa [this] at hpreimage_closed
  · -- closedPoints ⊆ zeroLocus(I.map)
    -- If q is a closed point, it specializes to some y ∈ V(ideal 1 I) ⊆ V(I.map).
    -- Since q is closed, q = y, so q ∈ V(I.map).
    intro hq
    have ⟨y, hy_mem, hspec⟩ := Generalization.exists_specializes_zeroLocus_ideal I q
    rw [mem_closedPoints_iff] at hq
    have hqy : q = y := by
      have : y ∈ ({q} : Set _) := hspec.mem_closed hq (Set.mem_singleton q)
      exact (Set.mem_singleton_iff.mp this).symm
    rw [hqy]
    exact zeroLocus_anti_mono (SetLike.coe_subset_coe.mpr (Ideal_map_le_ideal_one I)) hy_mem

theorem zeroLocus_map_algebraMap_subset_closedPoints [Algebra A B]
    (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime],
    Algebra.IsAlgebraic m.ResidueField q.ResidueField)
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) := by
  intro q hq
  simp only [mem_zeroLocus, SetLike.coe_subset_coe, mem_closedPoints_iff,
    isClosed_singleton_iff_isMaximal] at ⊢ hq
  set m := comap (algebraMap A B) q with hm_def
  have hm : m.asIdeal.IsMaximal := by
    simpa [isClosed_singleton_iff_isMaximal] using hI (Ideal.le_comap_of_map_le hq)
  have : q.asIdeal.LiesOver m.asIdeal := ⟨PrimeSpectrum.ext_iff.mp hm_def⟩
  have := h m.asIdeal q.asIdeal
  exact Ideal.IsMaximal.of_isAlgebraic m.asIdeal q.asIdeal

variable (I) in
/--
The w-localization with respect to an ideal `I`.
-/
protected def Ideal.WLocalization : Type u :=
  Generalization 1 (I.map (algebraMap A (WLocalization A)))

namespace Ideal.WLocalization

noncomputable instance commRing : CommRing I.WLocalization := fast_instance%
  inferInstanceAs <| CommRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isWLocalRing : IsWLocalRing I.WLocalization :=
  inferInstanceAs <| IsWLocalRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebraWLocalization: Algebra (WLocalization A) I.WLocalization :=
  fast_instance% inferInstanceAs <| Algebra (WLocalization A) <|
    Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebra : Algebra A I.WLocalization :=
  Algebra.compHom _ (algebraMap A (WLocalization A))

instance isScalarTower : IsScalarTower A (WLocalization A) I.WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

instance indZariski : Algebra.IndZariski A I.WLocalization := by
  have : Algebra.IndZariski (WLocalization A) I.WLocalization :=
    inferInstanceAs (Algebra.IndZariski (WLocalization A)
      (Generalization 1 (I.map (algebraMap A (WLocalization A)))))
  exact Algebra.IndZariski.trans A (WLocalization A) I.WLocalization

theorem zeroLocus_map_algebraMap_eq_closedPoints
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A I.WLocalization)) =
    closedPoints (PrimeSpectrum I.WLocalization) := by
  -- I.WLocalization = Generalization 1 J where J = I.map(algebraMap A (WLocalization A))
  -- I.map(algebraMap A I.WLocalization) = J.map(algebraMap (WLocalization A) (Generalization 1 J))
  -- We apply zeroLocus_map_algebraMap_generalization_one_eq to WLocalization A and ideal J.
  set J := I.map (algebraMap A (WLocalization A))
  -- The algebra map A → I.WLocalization factors through WLocalization A
  have hfactor : I.map (algebraMap A I.WLocalization) =
      J.map (algebraMap (WLocalization A) (Generalization 1 J)) := by
    show I.map (algebraMap A I.WLocalization) =
      (I.map (algebraMap A (WLocalization A))).map
        (algebraMap (WLocalization A) (Generalization 1 (I.map (algebraMap A (WLocalization A)))))
    rw [Ideal.map_map]; congr 1
  rw [hfactor]
  -- Apply the proved lemma with base = WLocalization A
  apply IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq
  -- Need: zeroLocus J ⊆ closedPoints(Spec(WLocalization A))
  -- J = I.map(algebraMap A (WLocalization A))
  -- Use zeroLocus_map_algebraMap_subset_closedPoints with B = WLocalization A
  -- This requires algebraic extensions condition.
  -- Ind-Zariski implies bijective on stalks, which implies algebraic on residue fields.
  apply zeroLocus_map_algebraMap_subset_closedPoints
  · intro m q _ _ _
    -- Algebraic extension on residue fields from ind-Zariski property
    -- The map A → WLocalization A is ind-Zariski, hence bijective on stalks,
    -- hence induces algebraic (in fact isomorphic) extensions on residue fields.
    exact bijectiveOnStalks_isAlgebraic_residueField
      (Algebra.IndZariski.bijectiveOnStalks_algebraMap A (WLocalization A)) m q
  · exact hI

-- The WLocalization is faithfully flat: it is flat (ind-Zariski => flat) and
-- PrimeSpectrum.comap is surjective (bijOn_algebraMap_specComap_zeroLocus_ideal).
private noncomputable instance wLocalization_faithfullyFlat :
    Module.FaithfullyFlat A (WLocalization A) := by
  apply Module.FaithfullyFlat.of_comap_surjective
  intro q
  obtain ⟨p, _, hp⟩ :=
    (WLocalization.bijOn_algebraMap_specComap_zeroLocus_ideal A).surjOn (Set.mem_univ q)
  exact ⟨p, hp⟩

-- For f = 1: ideal 1 J = J.map(algebraMap B C) where C = Generalization 1 J.
-- Both directions use the S-saturation of J (elements of submonoid 1 J are units mod J).
private lemma ideal_one_eq_map (J : Ideal (WLocalization A)) :
    Generalization.ideal 1 J =
    J.map (algebraMap (WLocalization A) (Generalization 1 J)) := by
  set B := WLocalization A
  set S := Generalization.submonoid 1 J
  set C := Generalization 1 J
  -- Both inclusions
  apply le_antisymm
  · -- ideal 1 J ≤ J.map: if c ∈ ker(toLocQuotient), then c ∈ J.map
    intro c hc
    rw [Generalization.ideal, RingHom.mem_ker] at hc
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S c
    rw [IsLocalization.mk'_mem_map_algebraMap_iff S]
    -- toLocQuotient(mk'(b,s)) = 0 means algebraMap b = 0 in (B/J)_1
    have key : (algebraMap B (Localization.Away (Ideal.Quotient.mk J 1))) b = 0 := by
      have hspec := IsLocalization.mk'_spec (M := S) C b s
      have h1 := congr_arg (Generalization.toLocQuotient 1 J) hspec
      rw [map_mul, hc, zero_mul, AlgHom.commutes] at h1
      exact h1.symm
    -- algebraMap B ((B/J)_1) b = 0 means ∃ m ∈ powers(mk J 1), m * (mk J b) = 0 in B/J
    rw [IsScalarTower.algebraMap_apply B (B ⧸ J)] at key
    rw [← Ideal.Quotient.algebraMap_eq] at key
    obtain ⟨⟨c, hc_mem⟩, hcb⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk J 1))
      (Localization.Away (Ideal.Quotient.mk J 1))
      (Ideal.Quotient.mk J b)).mp key
    -- c ∈ powers(mk J 1), so c = (mk J 1)^n = 1^n = 1
    rw [Submonoid.mem_powers_iff] at hc_mem
    obtain ⟨n, rfl⟩ := hc_mem
    -- hcb : c * (mk J b) = 0 where c = (mk J 1)^n = 1^n = 1
    have hb : b ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      -- The coercion ↑⟨(mk J 1)^n, _⟩ = (mk J 1)^n = 1
      have h1 : (⟨(Ideal.Quotient.mk J 1) ^ n, hc_mem⟩ :
          Submonoid.powers (Ideal.Quotient.mk J 1)).val = (1 : B ⧸ J) := by
        show (Ideal.Quotient.mk J 1) ^ n = 1
        have : Ideal.Quotient.mk J 1 = (1 : B ⧸ J) := map_one _
        rw [this]; exact one_pow n
      calc Ideal.Quotient.mk J b
          = (1 : B ⧸ J) * Ideal.Quotient.mk J b := (one_mul _).symm
        _ = (⟨(Ideal.Quotient.mk J 1) ^ n, hc_mem⟩ :
              Submonoid.powers (Ideal.Quotient.mk J 1)).val * Ideal.Quotient.mk J b := by
            congr 1; exact h1.symm
        _ = 0 := hcb
    exact ⟨1, S.one_mem, by simpa using hb⟩
  · -- J.map ≤ ideal 1 J: if b ∈ J, then algebraMap(b) ∈ ker(toLocQuotient)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show algebraMap B C b ∈ Generalization.ideal 1 J
    rw [Generalization.ideal, RingHom.mem_ker]
    -- toLocQuotient(algebraMap b) = algebraMap_to_(B/J)_1 (b) = 0 since b ∈ J
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B (B ⧸ J)]
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]

variable (I) in
@[stacks 097A "(2)(a)"]
theorem quotientMap_algebraMap_bijective :
    Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := by
  -- Strategy: Show A/I → C/IC is bijective by showing it factors as
  -- A/I → B/J →≅ C/JC = C/IC where B = WLocalization A, J = I.map(algebraMap A B),
  -- C = Generalization 1 J = I.WLocalization.
  -- The first map A/I → B/J is bijective because A → B is faithfully flat
  -- (comap_map_eq_self gives injectivity), and the composition is bijective
  -- by BijectiveOnStalks + Spec-bijective.
  --
  -- We directly prove injectivity and surjectivity of the quotient map.
  -- Use abbreviations for readability but work with I.WLocalization explicitly
  set B := WLocalization A
  set J := I.map (algebraMap A B) with hJ_def
  set S := Generalization.submonoid 1 J
  -- Note: I.WLocalization = Generalization 1 J (definitionally)
  -- S-saturation of J: elements of S are units mod J
  have hsat : ∀ (s : B) (b : B), s ∈ S → s * b ∈ J → b ∈ J := by
    intro s b hs hsb
    -- The localization (B/J)_1 is isomorphic to B/J since we localize at powers of 1
    have hpow1 : Submonoid.powers (Ideal.Quotient.mk J 1) ≤ IsUnit.submonoid (B ⧸ J) := by
      intro x hx; rw [Submonoid.mem_powers_iff] at hx; obtain ⟨n, rfl⟩ := hx
      rw [map_one]; exact isUnit_one.pow n
    have hequiv : (B ⧸ J) ≃ₐ[B ⧸ J]
        Localization.Away (Ideal.Quotient.mk J 1) :=
      IsLocalization.atUnits (B ⧸ J) (Submonoid.powers (Ideal.Quotient.mk J 1))
        (S := Localization.Away (Ideal.Quotient.mk J 1)) hpow1
    -- s ∈ S means s is a unit mod J
    have hs_unit : IsUnit (Ideal.Quotient.mk J s) := by
      change s ∈ Generalization.submonoid 1 J at hs
      rw [Generalization.submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
        IsScalarTower.algebraMap_apply B (B ⧸ J)] at hs
      -- hs : IsUnit (algebraMap (B ⧸ J) (Localization.Away (mk J 1)) (algebraMap B (B ⧸ J) s))
      -- algebraMap B (B ⧸ J) s = Ideal.Quotient.mk J s
      rw [Ideal.Quotient.algebraMap_eq] at hs
      -- hs : IsUnit (algebraMap (B ⧸ J) Loc (mk J s))
      -- hequiv (mk J s) = algebraMap (B ⧸ J) Loc (mk J s) since hequiv is a (B ⧸ J)-AlgEquiv
      rw [← hequiv.commutes (Ideal.Quotient.mk J s)] at hs
      exact (MulEquiv.isUnit_map (F := AlgEquiv (B ⧸ J) (B ⧸ J)
        (Localization.Away (Ideal.Quotient.mk J 1))) hequiv).mp hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (s * b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hsb
    rw [map_mul] at this
    exact hs_unit.mul_right_eq_zero.mp this
  -- J.map(B→WLoc).comap(B→WLoc) ≤ J (from S-saturation + localization)
  have hcomap_map_J : (J.map (algebraMap B I.WLocalization)).comap
      (algebraMap B I.WLocalization) ≤ J := by
    intro b hb
    rw [Ideal.mem_comap] at hb
    have : IsLocalization S I.WLocalization :=
      inferInstanceAs (IsLocalization (Generalization.submonoid 1 J) (Generalization 1 J))
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff S] at hb
    obtain ⟨s, hs, hsb⟩ := hb
    exact hsat s b hs hsb
  constructor
  · -- Injectivity: I.map(A→WLoc).comap(A→WLoc) ≤ I
    apply Ideal.quotientMap_injective'
    intro a ha
    rw [Ideal.mem_comap] at ha
    -- Factor: I.map(A→WLoc) = J.map(B→WLoc) by Ideal.map_map
    have hfactor : I.map (algebraMap A I.WLocalization) =
        J.map (algebraMap B I.WLocalization) := by
      show I.map (algebraMap A I.WLocalization) =
        (I.map (algebraMap A B)).map (algebraMap B (Generalization 1 (I.map (algebraMap A B))))
      rw [Ideal.map_map]; congr 1
    rw [hfactor] at ha
    -- algebraMap A WLoc a = algebraMap B WLoc (algebraMap A B a) by scalar tower
    have halg_factor : (algebraMap A I.WLocalization) a =
        (algebraMap B I.WLocalization) ((algebraMap A B) a) :=
      (IsScalarTower.algebraMap_apply A B I.WLocalization a).symm
    rw [halg_factor] at ha
    -- algebraMap B WLoc (algebraMap A B a) ∈ J.map(B→WLoc)
    -- So algebraMap A B a ∈ J.map(B→WLoc).comap(B→WLoc) ≤ J
    have ha_J : algebraMap A B a ∈ J := hcomap_map_J (Ideal.mem_comap.mpr ha)
    -- J = I.map(A→B), by faithful flatness: J.comap(A→B) = I
    have : J.comap (algebraMap A B) = I :=
      hJ_def ▸ Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) I
    rw [← this]
    exact Ideal.mem_comap.mpr ha_J
  · -- Surjectivity
    -- Blueprint: lemma:closed-closed-points-tilde-w-local (item 2). A/I → A_{w,I}/IA_{w,I} is bijective.
    sorry

variable (I) in
theorem bijOn_zeroLocus_map : Set.BijOn (PrimeSpectrum.comap (algebraMap A I.WLocalization))
    (zeroLocus (I.map (algebraMap A I.WLocalization))) (zeroLocus I) := by
    rw [← mk_ker (I := I.map _)]
    conv =>
      enter [3, 1, 1]
      rw [← mk_ker (I := I)]
    rw [← range_comap_of_surjective _ _ Quotient.mk_surjective,
      ← range_comap_of_surjective _ _ Quotient.mk_surjective,
      ← Set.image_univ, ← Set.image_univ]
    apply Set.bijOn_image_image
        (f := PrimeSpectrum.comap (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map))
    · intro
      ext1
      simp only [comap_asIdeal, comap_comap, Quotient.mk_comp_algebraMap]
      congr 1
    · rw [Set.bijOn_univ]
      exact (PrimeSpectrum.comapEquiv (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective I))).symm.bijective
    · apply Set.InjOn.image_of_comp
      rw [Set.injOn_univ, ← PrimeSpectrum.comap_comp]
      apply PrimeSpectrum.comap_injective_of_surjective
      rw [← Ideal.quotientMap_comp_mk I.le_comap_map]
      simp
      apply Function.Surjective.comp
      · exact (quotientMap_algebraMap_bijective I).surjective
      · exact Ideal.Quotient.mk_surjective

noncomputable instance [Algebra A B] : Algebra A (I.map (algebraMap A B)).WLocalization :=
  Algebra.compHom _ (algebraMap A B)

instance [Algebra A B] : IsScalarTower A B (I.map (algebraMap A B)).WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

@[stacks 097A "(2)(d)"]
theorem algebraMap_specComap_preimage_closedPoints_eq [IsWLocalRing A] [Algebra A B]
    (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) (h : ∀ (m : Ideal A) (q : Ideal B)
    [q.LiesOver m] [m.IsMaximal] [q.IsPrime], Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
    zeroLocus (I.map (algebraMap A (I.map (algebraMap A B)).WLocalization)) =
    closedPoints (PrimeSpectrum (I.map (algebraMap A B)).WLocalization) := by
  -- Factor I.map(algebraMap A C) through B:
  -- I.map(algebraMap A C) = (I.map(algebraMap A B)).map(algebraMap B C) by Ideal.map_map
  set J := I.map (algebraMap A B) with hJ_def
  -- C = J.WLocalization
  -- The algebra map A → C factors through B via the scalar tower A → B → C
  have hfactor : I.map (algebraMap A J.WLocalization) =
      J.map (algebraMap B J.WLocalization) := by
    show I.map (algebraMap A J.WLocalization) =
      (I.map (algebraMap A B)).map (algebraMap B J.WLocalization)
    rw [Ideal.map_map]; congr 1
  rw [hfactor]
  -- Apply zeroLocus_map_algebraMap_eq_closedPoints to B with ideal J
  -- This requires: zeroLocus J ⊆ closedPoints(Spec B)
  apply zeroLocus_map_algebraMap_eq_closedPoints
  -- V(IB) ⊆ closedPoints(Spec B) follows from the hypothesis h
  exact zeroLocus_map_algebraMap_subset_closedPoints h (hI ▸ Set.Subset.refl _)

theorem faithfullyFlat_map_algebraMap [IsWLocalRing A] [Algebra A B] [Module.FaithfullyFlat A B]
  (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) :
  Module.FaithfullyFlat A (I.map (algebraMap A B)).WLocalization := by
  have : Module.Flat A (I.map (algebraMap A B)).WLocalization :=
    Module.Flat.trans A B (I.map (algebraMap A B)).WLocalization
  apply Module.FaithfullyFlat.of_comap_surjective
  apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
  rw [← hI]
  calc
    zeroLocus I ⊆ PrimeSpectrum.comap (algebraMap A B) '' zeroLocus (I.map (algebraMap A B)) := by
      -- This should be separated as a lemma
      intro p hp
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_image] at hp ⊢
      obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat p (B := B)
      refine ⟨q, ?_, hq⟩
      simp only [← hq, comap_asIdeal] at hp
      exact Ideal.map_le_of_le_comap hp
    _ ⊆ PrimeSpectrum.comap (algebraMap A B) ''
        (PrimeSpectrum.comap (algebraMap B (I.map (algebraMap A B)).WLocalization) ''
        zeroLocus (I.map ((algebraMap B (I.map (algebraMap A B)).WLocalization).comp
        (algebraMap A B)))) := by
      apply Set.image_mono
      rw [← Ideal.map_map]
      intro p hp
      rw [(bijOn_zeroLocus_map (map (algebraMap A B) I)).image_eq]
      exact hp
    _ ⊆ _ := by
      rw [← Set.image_comp, ← comap_comp]
      exact Set.image_subset_range _ _

end Ideal.WLocalization
