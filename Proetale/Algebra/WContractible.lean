/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Proetale.Algebra.WStrictLocalization
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndZariski

/-!
# w-contractible rings

A ring is w-contractible if it is w-strictly-local and the space of connected components of
its prime spectrum is extremally disconnected.

Every w-contractible ring is indeed contractible in the ind-étale topology in the following
sense: If `R` is w-contractible, then every ind-étale faithfully flat map `R →+* S`
has a retraction.

The ind-étale site has enough contractible objects, in the sense that every ring admits a
faithfully flat, ind-étale algebra that is w-contractible.
-/

universe u

/-- A ring `R` is w-contractible if it is w-strictly-local and the space of connected components
of `Spec R` is extremally disconnected. -/
class IsWContractibleRing (R : Type*) [CommRing R] extends IsWStrictlyLocalRing R where
  extremallyDisconnected_connectedComponents :
    ExtremallyDisconnected (ConnectedComponents <| PrimeSpectrum R)

variable (R : Type u) [CommRing R]

/-- If `R` is w-contractible, every faithfully flat, ind-étale map `R →+* S` has a retraction. -/
theorem IsWContractibleRing.exists_retraction (R : Type u) [CommRing R] [IsWContractibleRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R :=
  sorry

/-- Any w-strictly-local ring has an ind-Zariski, faithfully flat cover that is w-contractible. -/
lemma exists_isWContractibleRing_of_isWStrictlyLocal (R : Type u) [CommRing R]
    [IsWStrictlyLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndZariski R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S :=
  sorry

/-- Any ring has an ind-étale, faithfully flat cover that is w-contractible. -/
theorem exists_isWContractibleRing (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S := by
  obtain ⟨S, _, _, _, _, _⟩ :=
    exists_isWContractibleRing_of_isWStrictlyLocal (WStrictLocalization R)
  letI : Algebra R S := Algebra.compHom _ (algebraMap R (WStrictLocalization R))
  have : IsScalarTower R (WStrictLocalization R) S := .of_algebraMap_eq' rfl
  refine ⟨S, inferInstance, inferInstance, ?_, ?_, inferInstance⟩
  · exact Algebra.IndEtale.trans _ (WStrictLocalization R) _
  · exact Module.FaithfullyFlat.trans _ (WStrictLocalization R) _

/-- Any ring has an ind-étale, faithfully flat cover for which every ind-étale
faithfully flat cover splits. -/
theorem exists_forall_exists_retraction (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧
      ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.IndEtale S T] [Module.FaithfullyFlat S T],
        ∃ (f : T →+* S), f.comp (algebraMap S T) = RingHom.id S := by
  obtain ⟨S, _, _, _, _, _⟩ := exists_isWContractibleRing R
  use S, inferInstance, inferInstance, inferInstance, inferInstance
  intro T _ _ _ _
  obtain ⟨f, hf⟩ := IsWContractibleRing.exists_retraction S T
  use f, hf
