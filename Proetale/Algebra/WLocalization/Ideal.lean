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

Let `A` be a w-local ring. Let `I ⊆ A` be an ideal cutting out the set `X^c` of closed points in `X = Spec(A)`. Let `A → B` be a ring map inducing algebraic extensions on residue fields at primes. Then there exists an ind-Zariski ring map `B → C` such that

- `B/IB → C/IC` is an isomorphism,
- `C` is w-local
- the map `p : Y = Spec C → X` induced by the ring map `A → B → C` is w-local, and
- `p⁻¹(X^c)` is the set of closed points of `Y`.

In particular, the composition `A → B → C` is faithfully flat if `A → B` is faithfully flat.
-/

universe u

open WLocalization PrimeSpectrum

variable {A B : Type u} [CommRing A] [CommRing B] (I :Ideal A)

instance isWLocalRing_generalization_one [IsWLocalRing A] : IsWLocalRing (Generalization 1 I) := sorry

variable {I}

theorem IsWLocalRing.zeroLocus_map_algebraMap_generalization_one_eq [IsWLocalRing A]
    (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A (Generalization 1 I))) = closedPoints (PrimeSpectrum (Generalization 1 I)) := by
  sorry

theorem zeroLocus_map_algebraMap_subset_closedPoints [Algebra A B] (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime], Algebra.IsAlgebraic m.ResidueField q.ResidueField) (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
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
protected def Ideal.WLocalization : Type u := Generalization 1 (I.map (algebraMap A (WLocalization A)))

namespace Ideal.WLocalization

noncomputable instance commRing : CommRing I.WLocalization := fast_instance%
  inferInstanceAs <| CommRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

instance isWLocalRing : IsWLocalRing I.WLocalization :=
  inferInstanceAs <| IsWLocalRing <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebraWLocalization: Algebra (WLocalization A) I.WLocalization := fast_instance%
  inferInstanceAs <| Algebra (WLocalization A) <| Generalization 1 (I.map (algebraMap A (WLocalization A)))

noncomputable instance algebra : Algebra A I.WLocalization := Algebra.compHom _ (algebraMap A (WLocalization A))

instance isScalarTower : IsScalarTower A (WLocalization A) I.WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

instance indZariski : Algebra.IndZariski A I.WLocalization := sorry

theorem zeroLocus_map_algebraMap_eq_closedPoints (hI : zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    zeroLocus (I.map (algebraMap A I.WLocalization)) =
    closedPoints (PrimeSpectrum I.WLocalization) := sorry

variable (I) in
@[stacks 097A "(2)(a)"]
theorem quotientMap_algebraMap_bijective : Function.Bijective (Ideal.quotientMap _ (algebraMap A I.WLocalization) I.le_comap_map) := sorry

noncomputable instance [Algebra A B] : Algebra A (I.map (algebraMap A B)).WLocalization := Algebra.compHom _ (algebraMap A B)

instance [Algebra A B] : IsScalarTower A B (I.map (algebraMap A B)).WLocalization :=
  ⟨fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc]; rfl⟩

@[stacks 097A "(2)(d)"]
theorem algebraMap_specComap_preimage_closedPoints_eq [IsWLocalRing A] [Algebra A B] (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime], Algebra.IsAlgebraic m.ResidueField q.ResidueField) :
    zeroLocus (I.map (algebraMap A (I.map (algebraMap A B)).WLocalization)) = closedPoints (PrimeSpectrum (I.map (algebraMap A B)).WLocalization) := sorry

theorem faithfullyFlat_map_algebraMap [IsWLocalRing A] [Algebra A B] [Module.FaithfullyFlat A B] (hI : zeroLocus I = closedPoints (PrimeSpectrum A)) (h : ∀ (m : Ideal A) (q : Ideal B) [q.LiesOver m] [m.IsMaximal] [q.IsPrime], Algebra.IsAlgebraic m.ResidueField q.ResidueField) : Module.FaithfullyFlat A (I.map (algebraMap A B)).WLocalization := by
  have : Module.Flat A (I.map (algebraMap A B)).WLocalization := Module.Flat.trans A B (I.map (algebraMap A B)).WLocalization
  apply Module.FaithfullyFlat.of_specComap_surjective
  apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
  rw [← hI]
  calc
    zeroLocus I ⊆ (algebraMap A B).specComap '' zeroLocus (I.map (algebraMap A B)) := by
      intro p hp
      simp only [mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_image] at hp ⊢
      obtain ⟨q, hq⟩ := PrimeSpectrum.specComap_surjective_of_faithfullyFlat p (B := B)
      refine ⟨q, ?_, hq⟩
      simp only [← hq, specComap_asIdeal] at hp
      exact Ideal.map_le_of_le_comap hp
    _ ⊆ (algebraMap A B).specComap '' ((algebraMap B (I.map (algebraMap A B)).WLocalization).specComap '' zeroLocus (I.map ((algebraMap B (I.map (algebraMap A B)).WLocalization).comp (algebraMap A B)))) := by
      apply Set.image_mono
      intro p hp
      simp at hp
      -- let p' := (Ideal.primeSpectrumQuotientOrderIsoZeroLocus (I.map (algebraMap A B))).symm ⟨p, hp⟩
      -- let q' := PrimeSpectrum.comapEquiv (RingEquiv.ofBijective _ (quotientMap_algebraMap_bijective (I.map (algebraMap A B)))) p'
      -- let q := (Ideal.primeSpectrumQuotientOrderIsoZeroLocus _) q'
      -- use q
      -- simp [q, q', p']
      sorry
    _ ⊆ _ := by
      rw [← Set.image_comp, ← specComap_comp]
      exact Set.image_subset_range _ _

end Ideal.WLocalization
