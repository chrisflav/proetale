import Proetale.Algebra.Bijective
import Proetale.Algebra.WeaklyEtaleField
import Proetale.Mathlib.RingTheory.Henselian

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing S]

open TensorProduct

/- We disable the functorial algebra structure on residue fields of local homomorphisms of
local rings in favour of the generic one, so that the algebra structure of `κ(p)` on residue
fields of primes of the fibre ring `κ(p) ⊗[R] S` agrees with the one used in
`Algebra.IndEtale.exists_isIdempotentElem_tensorProduct_of_residueField_ne`. -/
attribute [-instance] IsLocalRing.ResidueField.instAlgebra

namespace Algebra.WeaklyEtale

variable [Algebra R S] [IsLocalHom (algebraMap R S)]

section

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)] [WeaklyEtale R S]

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then for any algebraic field extension `L` of `κ(p)` the
tensorproduct `L ⊗[R] S` has no nontrivial idempotent elements. -/
lemma eq_of_isIdempotentElem (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra p.ResidueField L] [Algebra R L] [Algebra.IsAlgebraic p.ResidueField L]
    [IsScalarTower R p.ResidueField L] {e : L ⊗[R] S} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 :=
  sorry

/-- If `R → S` is a local homomorphism of local rings, `R` is henselian with separably
closed residue field and `S` is weakly étale over `R`, the fibre rings of `R → S` have a
single prime. -/
lemma subsingleton_primeSpectrum_fiber (p : Ideal R) [p.IsPrime] :
    Subsingleton (PrimeSpectrum (p.Fiber S)) := by
  have hind : IndEtale p.ResidueField (p.Fiber S) := indEtale_field p.ResidueField (p.Fiber S)
  refine ⟨fun q₁ q₂ ↦ ?_⟩
  by_contra hne
  obtain ⟨e, he, h0, h1⟩ := IndEtale.exists_isIdempotentElem_of_two_primes
    (K := p.ResidueField) (q₁ := q₁.asIdeal) (q₂ := q₂.asIdeal)
    fun h ↦ hne (PrimeSpectrum.ext h)
  rcases eq_of_isIdempotentElem p p.ResidueField he with h' | h'
  · exact h0 h'
  · exact h1 h'

set_option synthInstance.maxHeartbeats 400000 in
-- Instance searches on tensor products with residue fields of primes of the fibre ring
-- unfold long quotient/localization chains and exceed the default heartbeat limits.
set_option maxHeartbeats 1600000 in
-- Elaboration unfolds the same long quotient/localization chains as the instance searches.
/-- If `R → S` is a local homomorphism of local rings, `R` is henselian with separably
closed residue field and `S` is weakly étale over `R`, the residue field extensions of the
fibre rings of `R → S` are trivial. -/
lemma bijective_algebraMap_residueField_fiber (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have hind : IndEtale p.ResidueField (p.Fiber S) := indEtale_field p.ResidueField (p.Fiber S)
  by_contra h
  obtain ⟨e, he, h0, h1⟩ := IndEtale.exists_isIdempotentElem_tensorProduct_of_residueField_ne q h
  have habs : Ring.AbsolutelyFlat (p.Fiber S) :=
    .of_flat_lmul' p.ResidueField (p.Fiber S) (flat_lmul' p.ResidueField (p.Fiber S))
  have htfae : Ring.AbsolutelyFlat (p.Fiber S) ↔
      IsReduced (p.Fiber S) ∧ ∀ P : Ideal (p.Fiber S), P.IsPrime → P.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae (p.Fiber S)).out 0 1
  have hmax : q.IsMaximal := (htfae.mp habs).2 q inferInstance
  have hsurj : Function.Surjective (algebraMap (p.Fiber S) q.ResidueField) := by
    rw [IsScalarTower.algebraMap_eq (p.Fiber S) (p.Fiber S ⧸ q) q.ResidueField]
    exact (Ideal.bijective_algebraMap_quotient_residueField q).surjective.comp
      Ideal.Quotient.mk_surjective
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := hsurj y
    exact IndEtale.isSeparable_of_algHom_to_isLocalRing p.ResidueField q.ResidueField
      (IsScalarTower.toAlgHom p.ResidueField (p.Fiber S) q.ResidueField) b
  have halg : Algebra.IsAlgebraic p.ResidueField q.ResidueField :=
    Algebra.IsSeparable.isAlgebraic p.ResidueField q.ResidueField
  have htower : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R (p.Fiber S) q.ResidueField,
        IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber S),
        ← IsScalarTower.algebraMap_apply p.ResidueField (p.Fiber S) q.ResidueField]
  let φ := Algebra.TensorProduct.cancelBaseChange R p.ResidueField q.ResidueField
    q.ResidueField S
  rcases eq_of_isIdempotentElem p q.ResidueField (he.map φ) with h' | h'
  · exact h0 ((map_eq_zero_iff φ φ.injective).mp h')
  · exact h1 ((map_eq_one_iff φ φ.injective).mp h')

end

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then `R → S` is an isomorphism. -/
lemma bijective_of_henselianLocalRing [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [Algebra.WeaklyEtale R S] :
    Function.Bijective (algebraMap R S) := by
  have hff : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  refine bijective_algebraMap_of_bijective_residueFieldMap
    ⟨fun q₁ q₂ hq ↦ ?_, PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩ ?_
  · -- Injectivity of `Spec S → Spec R`: the fibres of `Spec S → Spec R` have a single point.
    have hsub : Subsingleton
        (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
          {PrimeSpectrum.comap (algebraMap R S) q₁} : Set (PrimeSpectrum S)) :=
      have := subsingleton_primeSpectrum_fiber (S := S)
        (PrimeSpectrum.comap (algebraMap R S) q₁).asIdeal
      (PrimeSpectrum.preimageEquivFiber R S _).subsingleton
    exact congrArg Subtype.val (Subsingleton.elim (h := hsub) ⟨q₁, rfl⟩ ⟨q₂, hq.symm⟩)
  · -- Triviality of the residue field extensions, via the corresponding prime of the fibre.
    intro p hp q hq hlies
    have hQ : PrimeSpectrum.comap (algebraMap R S) ⟨q, hq⟩ = (⟨p, hp⟩ : PrimeSpectrum R) :=
      PrimeSpectrum.ext hlies.over.symm
    set q' : PrimeSpectrum (p.Fiber S) :=
      PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩ ⟨⟨q, hq⟩, hQ⟩ with hq'def
    have hcomap : q'.asIdeal.comap
        (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)
          (B := S)).toRingHom = q := by
      have h1 := (PrimeSpectrum.preimageEquivFiber R S ⟨p, hp⟩).symm_apply_apply ⟨⟨q, hq⟩, hQ⟩
      have h2 : PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom q'
          = (⟨q, hq⟩ : PrimeSpectrum S) := congrArg Subtype.val h1
      exact congrArg PrimeSpectrum.asIdeal h2
    have hbij := bijective_algebraMap_residueField_fiber (S := S) p q'.asIdeal
    have htri : (Ideal.ResidueField.map q q'.asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hcomap.symm).comp
        (Ideal.ResidueField.map p q (algebraMap R S) hlies.over) =
        algebraMap p.ResidueField q'.asIdeal.ResidueField := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p))
      rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective (I := p))]
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply,
        Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      rw [← IsScalarTower.algebraMap_apply R (p.Fiber S) q'.asIdeal.ResidueField,
        ← IsScalarTower.algebraMap_apply R p.ResidueField q'.asIdeal.ResidueField]
    refine ⟨RingHom.injective _, fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hbij.surjective (Ideal.ResidueField.map q q'.asIdeal
      Algebra.TensorProduct.includeRight.toRingHom hcomap.symm y)
    refine ⟨x, RingHom.injective (Ideal.ResidueField.map q q'.asIdeal
      Algebra.TensorProduct.includeRight.toRingHom hcomap.symm) ?_⟩
    rw [← hx, ← htri, RingHom.comp_apply]

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly étale over `R`, then `R → S` is an isomorphism. -/
lemma bijective_of_isStrictlyHenselianLocalRing [IsStrictlyHenselianLocalRing R]
    [Algebra.WeaklyEtale R S] :
    Function.Bijective (algebraMap R S) :=
  bijective_of_henselianLocalRing

end Algebra.WeaklyEtale
