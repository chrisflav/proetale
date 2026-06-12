/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization.Ideal
import Proetale.Algebra.ProEtaleContraction
import Proetale.Algebra.RetractionsStrictlyHenselian
import Proetale.Algebra.IndEtale

/-!
# w-strict-localization

In this file we show that every ring admits a faithfully flat, ind-étale w-strictly-local
algebra, following the blueprint (`thm:ind-etale-w-strictly-local-cover`, Stacks 097X):
starting from `R`, pass to the w-localization `R_w`, take the ind-étale contraction
`T = IndEtaleContraction R_w` (whose local rings at maximal ideals are strictly henselian),
and finally w-localize `T` along the pullback of the ideal `I` cutting out the closed points
of `Spec R_w`. The last step produces a w-local ring whose closed points lie over maximal
ideals of `T`, so its local rings at maximal ideals remain strictly henselian.
-/

universe u

open PrimeSpectrum

variable (R : Type u) [CommRing R]

namespace WStrictLocalization

/-- The radical ideal of the w-localization of `R` cutting out the closed points. -/
noncomputable def closedIdeal : Ideal (WLocalization R) :=
  vanishingIdeal (closedPoints (PrimeSpectrum (WLocalization R)))

lemma zeroLocus_closedIdeal :
    zeroLocus (closedIdeal R) = closedPoints (PrimeSpectrum (WLocalization R)) := by
  rw [closedIdeal, zeroLocus_vanishingIdeal_eq_closure,
    IsClosed.closure_eq IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints]

/-- The pullback of `closedIdeal R` to the ind-étale contraction of the w-localization. -/
noncomputable def contractionIdeal : Ideal (IndEtaleContraction (WLocalization R)) :=
  (closedIdeal R).map
    (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))

end WStrictLocalization

/-- The w-strict localization of a ring `R`: a faithfully flat, ind-étale, w-strictly-local
`R`-algebra. It is obtained as the w-localization, along the closed points of `Spec R_w`,
of the ind-étale contraction of the w-localization `R_w` of `R`. -/
noncomputable def WStrictLocalization (R : Type u) [CommRing R] : Type u :=
  (WStrictLocalization.contractionIdeal R).WLocalization

namespace WStrictLocalization

noncomputable instance : CommRing (WStrictLocalization R) :=
  inferInstanceAs <| CommRing (contractionIdeal R).WLocalization

noncomputable instance algebraContraction :
    Algebra (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra _ (contractionIdeal R).WLocalization

noncomputable instance algebraWLocalization :
    Algebra (WLocalization R) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra (WLocalization R)
    ((closedIdeal R).map
      (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))).WLocalization

instance isScalarTower' : IsScalarTower (WLocalization R)
    (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| IsScalarTower (WLocalization R) _
    ((closedIdeal R).map
      (algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R)))).WLocalization

end WStrictLocalization

noncomputable instance : Algebra R (WStrictLocalization R) :=
  Algebra.compHom _ (algebraMap R (WLocalization R))

instance : IsScalarTower R (WLocalization R) (WStrictLocalization R) :=
  .of_algebraMap_eq' rfl

namespace WStrictLocalization

instance indEtale' : Algebra.IndEtale (WLocalization R) (WStrictLocalization R) :=
  have : Algebra.IndZariski (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndZariski _ (contractionIdeal R).WLocalization
  Algebra.IndEtale.trans (WLocalization R) (S := IndEtaleContraction (WLocalization R))
    (WStrictLocalization R)

instance indEtale : Algebra.IndEtale R (WStrictLocalization R) :=
  Algebra.IndEtale.trans R (S := WLocalization R) (WStrictLocalization R)

instance faithfullyFlat' :
    Module.FaithfullyFlat (WLocalization R) (WStrictLocalization R) :=
  Ideal.WLocalization.faithfullyFlat_map_algebraMap (zeroLocus_closedIdeal R)
    (fun _ _ ↦ inferInstance)

instance faithfullyFlat : Module.FaithfullyFlat R (WStrictLocalization R) :=
  Module.FaithfullyFlat.trans R (WLocalization R) (WStrictLocalization R)

instance isWLocalRing : IsWLocalRing (WStrictLocalization R) :=
  inferInstanceAs <| IsWLocalRing (contractionIdeal R).WLocalization

/-- The closed points of the w-strict localization are cut out by the pullback of the
ideal of closed points of `Spec R_w`. -/
lemma zeroLocus_map_eq_closedPoints :
    zeroLocus ((closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R))) =
      closedPoints (PrimeSpectrum (WStrictLocalization R)) :=
  Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq
    (zeroLocus_closedIdeal R) (fun _ _ ↦ inferInstance)

instance isWStrictlyLocalRing : IsWStrictlyLocalRing (WStrictLocalization R) := by
  refine ⟨fun n hn ↦ ?_⟩
  haveI : n.IsPrime := hn.isPrime
  set B' := IndEtaleContraction (WLocalization R)
  -- `n` is a closed point of the w-strict localization, hence contains the pulled-back ideal.
  have hn_mem : (⟨n, inferInstance⟩ : PrimeSpectrum (WStrictLocalization R)) ∈
      zeroLocus ((closedIdeal R).map
        (algebraMap (WLocalization R) (WStrictLocalization R))) := by
    rw [zeroLocus_map_eq_closedPoints]
    exact (isClosed_singleton_iff_isMaximal _).mpr hn
  -- Its restriction `q` to the ind-étale contraction contains `contractionIdeal R`.
  set q : Ideal B' := n.comap (algebraMap B' (WStrictLocalization R)) with hq_def
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  have hq_mem : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ zeroLocus (contractionIdeal R) := by
    rw [mem_zeroLocus] at hn_mem ⊢
    intro x hx
    have : algebraMap B' (WStrictLocalization R) x ∈ n := by
      apply hn_mem
      have : (closedIdeal R).map (algebraMap (WLocalization R) (WStrictLocalization R)) =
          (contractionIdeal R).map (algebraMap B' (WStrictLocalization R)) := by
        rw [contractionIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    exact this
  -- `q` lies in the zero locus of the pullback of `closedIdeal R`, hence is maximal.
  have hq_closed : (⟨q, inferInstance⟩ : PrimeSpectrum B') ∈ closedPoints (PrimeSpectrum B') :=
    zeroLocus_map_algebraMap_subset_closedPoints
      (fun _ _ ↦ inferInstance) (zeroLocus_closedIdeal R).le hq_mem
  haveI : q.IsMaximal := (isClosed_singleton_iff_isMaximal _).mp hq_closed
  -- The local ring of the contraction at `q` is strictly henselian, and the
  -- ind-Zariski map `B' → WStrictLocalization R` identifies local rings.
  haveI := IsStrictlyHenselianLocalRing.localization_atPrime_indEtaleContraction
    (WLocalization R) q
  haveI : Algebra.IndZariski B' (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndZariski _ (contractionIdeal R).WLocalization
  have hbos : Algebra.BijectiveOnStalks B' (WStrictLocalization R) :=
    RingHom.bijectiveOnStalks_algebraMap.mp <|
      RingHom.IndZariski.bijectiveOnStalks
        ((RingHom.IndZariski.algebraMap_iff (R := B') (S := WStrictLocalization R)).mpr
          inferInstance)
  exact IsStrictlyHenselianLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (hbos.bijective_localRingHom n))

end WStrictLocalization

/-- Any ring has an ind-étale, faithfully flat cover that is w-strictly-local. -/
theorem exists_isWStrictlyLocalRing (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IndEtale R S)
      (_ : Module.FaithfullyFlat R S),
      IsWStrictlyLocalRing S := by
  use WStrictLocalization R, inferInstance, inferInstance, inferInstance, inferInstance
  infer_instance
