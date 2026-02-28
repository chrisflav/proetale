/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.IndEtale
import Proetale.Algebra.ProEtaleContraction

/-!
# w-strict-localization

In this file we show that every ring admits a faithfully flat, ind-étale w-strictly-local algebra.
-/

universe u

section StrictlyHenselianWLocalizationOfIndEtaleContraction

/-! ### Strictly Henselian stalks of `WLocalization (IndEtaleContraction A)`

The key mathematical results needed for `WStrictLocalization`:

1. **cor:strictly-henselian-etale-contraction** (Blueprint): For any maximal ideal `m` of
   `IndEtaleContraction A`, `(IndEtaleContraction A)_m` is strictly Henselian. This follows from
   `prop:etale-contraction-retraction` (formalized as
   `RingHom.Etale.exists_comp_eq_id_indContraction`: every faithfully flat etale map out of
   `IndEtaleContraction A` has a retraction) and `lemma:retractions-strictly-henselian` (if every
   faithfully flat etale map has a retraction, then localizations at maximal ideals are strictly
   Henselian).

2. **thm:ind-Zariski-identifies-local-rings** (partially formalized as
   `bijectiveOnStalks_algebraMap`): The ind-Zariski map `IndEtaleContraction A -> WLocalization
   (IndEtaleContraction A)` has bijective stalk maps, so local rings are identified through ring
   isomorphisms.

3. **Transfer**: The bijective stalk map at a maximal ideal `m` of `WLocalization(IndEtaleContraction A)`
   gives a ring isomorphism between the localization at `m.comap` and the localization at `m`.
   Combined with (1), (2), and the fact that `m.comap` is maximal (which follows from the
   closed point structure of the WLocalization), this gives strictly Henselian stalks.

The full proof uses `lemma:retractions-strictly-henselian` (etale-ind-spreads, prime avoidance,
faithfully flat etale covers); see the docstring on the private lemma below for the outline.
-/

variable {A : Type u} [CommRing A]

/-- **lemma:retractions-strictly-henselian** (Blueprint): If every faithfully flat etale ring map
`A -> B` has a retraction, then every local ring `A_m` at a maximal ideal is strictly Henselian.

Blueprint proof outline (local-structure.tex, lines 1701–1740):
1. Factor `A_m → B → κ(m)^sep` where `A_m → B` is etale.
2. Descend `B` to an etale `A_f`-algebra `B'` via etale-ind-spreads (`A_m = colim A_f`).
3. Use prime avoidance to find `g` isolating a unique prime `q` of `B'_g` lying over `m`.
4. Construct the faithfully flat etale cover `A → B'_g × ∏ A_{aᵢ}`.
5. Apply the retraction hypothesis to obtain `σ`.
6. Localize `σ` at `q` to get `B'_q → A_m`, then extend to `B → A_m`. -/
private lemma isStrictlyHenselianLocalRing_of_exists_retraction
    (A : Type u) [CommRing A]
    (hret : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], ∃ σ : B →ₐ[A] A, True)
    (m : Ideal A) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  sorry

/-- **cor:strictly-henselian-etale-contraction** (Blueprint): For any maximal ideal `m` of
`IndEtaleContraction A`, the localization `(IndEtaleContraction A)_m` is strictly Henselian.

This follows from `prop:etale-contraction-retraction` (formalized as
`RingHom.Etale.exists_comp_eq_id_indContraction`) and `lemma:retractions-strictly-henselian`. -/
private lemma isStrictlyHenselianLocalRing_IndEtaleContraction
    (m : Ideal (IndEtaleContraction A)) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  apply isStrictlyHenselianLocalRing_of_exists_retraction
  intro B _ _ hEtale hFF
  -- By prop:etale-contraction-retraction, every faithfully flat etale ring map out of
  -- IndEtaleContraction A has a retraction.
  -- The algebraMap is etale as a ring hom:
  have hf_etale : (algebraMap (IndEtaleContraction A) B).Etale :=
    RingHom.etale_algebraMap.mpr hEtale
  -- Faithfully flat implies surjective Spec map:
  have hf_surj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap (IndEtaleContraction A) B)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  -- Apply exists_comp_eq_id_indContraction:
  obtain ⟨g, hg⟩ := RingHom.Etale.exists_comp_eq_id_indContraction
    (algebraMap (IndEtaleContraction A) B) hf_etale hf_surj
  -- g is a RingHom retraction: g ∘ algebraMap = id
  -- Convert g to an AlgHom:
  refine ⟨{ toRingHom := g, commutes' := fun r => ?_ }, trivial⟩
  -- Need: g (algebraMap r) = algebraMap r (where algebraMap : IndEtaleContraction A → IndEtaleContraction A = id)
  -- From hg: g ∘ algebraMap = RingHom.id, so g (algebraMap r) = r
  show g ((algebraMap (IndEtaleContraction A) B) r) =
    (algebraMap (IndEtaleContraction A) (IndEtaleContraction A)) r
  rw [show (algebraMap (IndEtaleContraction A) (IndEtaleContraction A)) r = r from rfl]
  exact RingHom.congr_fun hg r

lemma isStrictlyHenselianLocalRing_WLocalization_IndEtaleContraction
    (m : Ideal (WLocalization (IndEtaleContraction A))) (hm : m.IsMaximal) :
    @IsStrictlyHenselianLocalRing (Localization.AtPrime m) _ := by
  -- Strategy: The ind-Zariski map algebraMap : IndEtaleContraction A -> WLocalization(IndEtaleContraction A)
  -- has bijective stalk maps. The bijective stalk map at m gives a ring isomorphism
  -- Localization.AtPrime (m.comap algebraMap) ≃+* Localization.AtPrime m.
  -- If m.comap algebraMap is maximal in IndEtaleContraction A, then by
  -- isStrictlyHenselianLocalRing_IndEtaleContraction, the source is strictly Henselian.
  -- Transfer through the ring isomorphism.
  -- Blueprint: cor:strictly-henselian-etale-contraction. Uses ind-Zariski stalk bijection + maximality transfer.
  sorry

end StrictlyHenselianWLocalizationOfIndEtaleContraction

-- def Precontraction

/-- The w-strict localization of `R`. The construction proceeds as follows:
1. Take the w-localization `WLocalization R` (w-local, ind-Zariski, faithfully flat over `R`).
2. Take its ind-étale contraction `IndEtaleContraction (WLocalization R)` (ind-étale, faithfully
   flat, with strictly Henselian maximal ideal localizations).
3. Take the w-localization of the result (to restore the w-local property, while the ind-Zariski
   map preserves the strictly Henselian stalks). -/
def WStrictLocalization (R : Type u) [CommRing R] : Type u :=
  WLocalization (IndEtaleContraction (WLocalization R))

variable (R : Type u) [CommRing R]

noncomputable instance : CommRing (WStrictLocalization R) :=
  inferInstanceAs <| CommRing (WLocalization (IndEtaleContraction (WLocalization R)))

noncomputable instance : Algebra R (WStrictLocalization R) :=
  ((algebraMap (IndEtaleContraction (WLocalization R))
      (WLocalization (IndEtaleContraction (WLocalization R)))).comp
    ((algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R))).comp
      (algebraMap R (WLocalization R)))).toAlgebra

-- Intermediate algebra: R → IndEtaleContraction (WLocalization R) via WLocalization R.
private noncomputable instance algebraIndEtaleContraction :
    Algebra R (IndEtaleContraction (WLocalization R)) :=
  ((algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R))).comp
    (algebraMap R (WLocalization R))).toAlgebra

-- The canonical algebra structure: IndEtaleContraction(WLoc R) → WStrictLocalization R
-- This is WLocalization.algebra for the intermediate ring.
private noncomputable instance algebraWStrictOfIndEtale :
    Algebra (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra (IndEtaleContraction (WLocalization R))
    (WLocalization (IndEtaleContraction (WLocalization R)))

private instance scalarTower_WLoc :
    IsScalarTower R (WLocalization R) (IndEtaleContraction (WLocalization R)) :=
  IsScalarTower.of_algebraMap_eq' rfl

private instance scalarTower_IndEtale :
    IsScalarTower R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  IsScalarTower.of_algebraMap_eq' rfl

-- Composition of ind-Zariski (WLocalization) ∘ ind-étale (IndEtaleContraction) ∘ ind-Zariski
-- (WLocalization) is ind-étale. Uses `Algebra.IndEtale.trans` twice.
instance : Algebra.IndEtale R (WStrictLocalization R) := by
  -- Step 1: R → WLocalization R is ind-Zariski, hence ind-étale.
  -- Step 2: WLocalization R → IndEtaleContraction (WLocalization R) is ind-étale.
  -- By trans: R → IndEtaleContraction (WLocalization R) is ind-étale.
  have : Algebra.IndEtale R (IndEtaleContraction (WLocalization R)) :=
    Algebra.IndEtale.trans R (WLocalization R) (IndEtaleContraction (WLocalization R))
  -- Step 3: IndEtaleContraction (WLocalization R) → WStrictLocalization R is ind-Zariski, hence ind-étale.
  -- By trans: R → WStrictLocalization R is ind-étale.
  have : Algebra.IndEtale (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndEtale _ (WLocalization (IndEtaleContraction (WLocalization R)))
  exact Algebra.IndEtale.trans R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R)

-- Composition of three faithfully flat maps. Uses `Module.FaithfullyFlat.trans` twice.
instance : Module.FaithfullyFlat R (WStrictLocalization R) := by
  -- Step 1: R → WLocalization R is faithfully flat.
  -- Step 2: WLocalization R → IndEtaleContraction (WLocalization R) is faithfully flat.
  -- By trans: R → IndEtaleContraction (WLocalization R) is faithfully flat.
  have : Module.FaithfullyFlat R (IndEtaleContraction (WLocalization R)) :=
    Module.FaithfullyFlat.trans R (WLocalization R) (IndEtaleContraction (WLocalization R))
  -- Step 3: IndEtaleContraction (WLocalization R) → WStrictLocalization R is faithfully flat.
  -- By trans: R → WStrictLocalization R is faithfully flat.
  have : Module.FaithfullyFlat (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    WLocalization.faithfullyFlat (IndEtaleContraction (WLocalization R))
  exact Module.FaithfullyFlat.trans R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R)

-- `IsWLocalRing` follows from the outer `WLocalization`. Strictly Henselian stalks at maximal
-- ideals: the `IndEtaleContraction` makes stalks of `WLocalization R` strictly Henselian, and
-- the outer `WLocalization` (being ind-Zariski) identifies local rings at closed points.
instance : IsWStrictlyLocalRing (WStrictLocalization R) where
  -- The w-local property: WStrictLocalization R = WLocalization (...) is always w-local
  wLocalSpace_primeSepectrum :=
    (inferInstanceAs (IsWLocalRing (WLocalization (IndEtaleContraction (WLocalization R))))).wLocalSpace_primeSepectrum
  -- Strictly Henselian stalks: the IndEtaleContraction makes stalks of WLocalization R
  -- strictly Henselian (cor:strictly-henselian-etale-contraction in blueprint), and the
  -- outer WLocalization (being ind-Zariski) identifies local rings at closed points
  -- (thm:ind-Zariski-identifies-local-rings in blueprint).
  -- This requires deep infrastructure not yet formalized.
  isStrictlyHenselianLocalRing_localization := fun m => by
    -- WStrictLocalization R = WLocalization (IndEtaleContraction (WLocalization R))
    -- m is a maximal ideal of this ring.
    -- Apply the helper lemma with A := WLocalization R.
    -- The types are definitionally equal, but we need to help Lean with the instance.
    exact isStrictlyHenselianLocalRing_WLocalization_IndEtaleContraction (A := WLocalization R) m ‹_›

/-- Any ring has an ind-étale, faithfully flat cover that is w-strictly-local. -/
theorem exists_isWStrictlyLocalRing (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IndEtale R S)
      (_ : Module.FaithfullyFlat R S),
      IsWStrictlyLocalRing S := by
  use WStrictLocalization R, inferInstance, inferInstance, inferInstance, inferInstance
  infer_instance
