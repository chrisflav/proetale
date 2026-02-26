/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic

/-!
# IndZariski instances for w-localization

This file proves the computationally expensive `IndZariski` instances for w-localization
that require high heartbeat limits, factored out to allow separate compilation.

The key technique: `Stratification.Index E` is finite, so we reduce to `ULift (Fin n)`
via `AlgEquiv.piCongrLeft`, then apply `Algebra.IndZariski.pi` which is much faster
for `ULift (Fin n)` than for the structurally complex `Stratification.Index E`.
-/

universe u

open CategoryTheory Limits PrimeSpectrum Classical

namespace WLocalization

variable {A : Type u} [CommRing A]

-- Re-prove finiteness of Stratification.Index (the original is private in Basic.lean).
private instance finite_stratification_index' (E : Finset A) :
    Finite (Stratification.Index E) := by
  classical
  have left_mem : ∀ i : Stratification.Index E, i.left ∈ E.powerset := fun i =>
    Finset.mem_powerset.mpr fun a ha =>
      Finset.mem_coe.mp (i.union_eq ▸ Set.mem_union_left _ (Finset.mem_coe.mpr ha))
  apply Finite.of_injective
    (fun i => (⟨i.left, left_mem i⟩ : {s // s ∈ E.powerset}))
  intro i j hij
  simp only [Subtype.mk.injEq] at hij
  have hri : ∀ (k : Stratification.Index E), k.right = E \ k.left := by
    intro k
    ext a
    simp only [Finset.mem_sdiff]
    constructor
    · intro ha
      exact ⟨Finset.mem_coe.mp (k.union_eq ▸ Set.mem_union_right _ (Finset.mem_coe.mpr ha)),
             fun h => Finset.disjoint_left.mp k.disjoint h ha⟩
    · intro ⟨haE, hal⟩
      have hmem : (a : A) ∈ (k.left : Set A) ∪ (k.right : Set A) :=
        k.union_eq ▸ Finset.mem_coe.mpr haE
      exact hmem.resolve_left (Finset.mem_coe.mp · |> hal)
  have hr : i.right = j.right := by rw [hri i, hri j, hij]
  cases i; cases j; simp only [Stratification.Index.mk.injEq]; exact ⟨hij, hr⟩

-- ProdStrata E is ind-Zariski (finite product of ind-Zariski localizations).
-- We reduce to ULift (Fin n) index via AlgEquiv.piCongrLeft, avoiding the expensive
-- elaboration of Algebra.IndZariski.pi directly on Stratification.Index E.
set_option maxHeartbeats 12000000 in
instance prodStrata_indZariski' (E : Finset A) :
    Algebra.IndZariski A (ProdStrata E) := by
  change Algebra.IndZariski A
    (∀ (i : Stratification.Index E), Generalization i.function i.ideal)
  obtain ⟨n, ⟨e_fin⟩⟩ := Finite.exists_equiv_fin (Stratification.Index E)
  let e : ULift.{u} (Fin n) ≃ Stratification.Index E :=
    Equiv.ulift.trans e_fin.symm
  let S : Stratification.Index E → Type u := fun i => Generalization i.function i.ideal
  have h1 : Algebra.IndZariski A (∀ k : ULift.{u} (Fin n), S (e k)) :=
    Algebra.IndZariski.pi A (fun k => S (e k))
  exact Algebra.IndZariski.of_equiv
    (R := A) (S := ∀ k : ULift.{u} (Fin n), S (e k)) (T := ∀ i, S i)
    (AlgEquiv.piCongrLeft A S e)

-- WLocalization A is ind-Zariski: filtered colimit of ind-Zariski ProdStrata algebras.
set_option maxHeartbeats 6400000 in
instance indZariski' : Algebra.IndZariski A (WLocalization A) :=
  Algebra.IndZariski.of_colimitPresentation A (WLocalization A)
    colimitPresentation (fun E => prodStrata_indZariski' E)

end WLocalization
