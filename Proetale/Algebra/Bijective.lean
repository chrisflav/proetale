import Proetale.Algebra.WeaklyEtale

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open TensorProduct

namespace Algebra

lemma isLocalRing_tensorProduct_of_krullDimLE_zero (k : Type*) [Field k] (R : Type*)
    [CommRing R] [IsLocalRing R] [Algebra k R] [IsLocalHom (algebraMap k R)] [Ring.KrullDimLE 0 R]
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField R))) :
    IsLocalRing (R ⊗[k] R) :=
  sorry

lemma krullDimLE_zero_tensorProduct_of_krullDimLE_zero (k : Type*) [Field k] (R : Type*)
    [CommRing R] [IsLocalRing R] [Algebra k R] [IsLocalHom (algebraMap k R)] [Ring.KrullDimLE 0 R]
    (h : Function.Bijective (algebraMap k (IsLocalRing.ResidueField R))) :
    Ring.KrullDimLE 0 (R ⊗[k] R) :=
  sorry

/-- If all residue field extensions are trivial and the map on prime spectra is
bijective, the map `Spec S ⟶ Spec (S ⊗[R] S)` is bijective. -/
lemma bijective_comap_lmul'_of_bijective_of_bijective
    (hf : Function.Bijective (PrimeSpectrum.comap (algebraMap R S)))
    (h : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (PrimeSpectrum.comap <| (TensorProduct.lmul' (S := S) R).toRingHom) :=
  sorry

/-- A flat surjective map `R → S` that is bijective on prime spectra is an isomorphism. -/
lemma bijective_of_bijective_of_flat [Module.Flat R S]
    (hf : Function.Bijective (PrimeSpectrum.comap (algebraMap R S)))
    (hf' : Function.Surjective (algebraMap R S)) :
    Function.Bijective (algebraMap R S) := by
  refine ⟨?_, hf'⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  have e : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := (algebraMap R S).quotientKerEquivOfSurjective hf') fun _ ↦ rfl
  have : (RingHom.ker (algebraMap R S)).Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  have : (⊥ : Ideal R).Pure := Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot ⊥ rfl)
  rw [← Ideal.zeroLocus_inj_of_pure, PrimeSpectrum.zeroLocus_bot, Set.eq_univ_iff_forall]
  intro p
  obtain ⟨q, rfl⟩ := hf.surjective p
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  rw [SetLike.mem_coe, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    RingHom.mem_ker.mp hx]
  exact q.asIdeal.zero_mem

/-- A faithfully flat epimorphism `R → S` is an isomorphism. -/
lemma bijective_of_faithfullyFlat_of_isEpi [Module.FaithfullyFlat R S] [Algebra.IsEpi R S] :
    Function.Bijective (algebraMap R S) :=
  sorry

lemma bijective_of_bijective_residueFieldMap [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (h : Function.Bijective (PrimeSpectrum.comap <| algebraMap R S))
    (h : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (algebraMap R S) :=
  sorry

/-- Let `R → S` be a weakly étale local homomorphism of local rings.  If for every prime
`p ⊂ R` there is a unique prime `q ⊂ S` lying over `p` and `κ(p) = κ(q)`, then `R → S` is
an isomorphism. -/
lemma WeaklyEtale.bijective_algebraMap_of_bijective_residueFieldMap
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.WeaklyEtale R S]
    (h : Function.Bijective (PrimeSpectrum.comap <| algebraMap R S))
    (hres : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (algebraMap R S) :=
  sorry

end Algebra
