import Proetale.Algebra.WeaklyEtale

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing S]

open TensorProduct

namespace Algebra

variable [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then for any algebraic field extension `L` of `κ(p)` the
tensorproduct `L ⊗[R] S` has no nontrivial idempotent elements. -/
lemma WeaklyEtale.eq_of_isIdempotentElem [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [WeaklyEtale R S]
    (p : Ideal R) [p.IsPrime] (L : Type*) [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [Algebra R L] [Algebra.IsAlgebraic (IsLocalRing.ResidueField R) L]
    [IsScalarTower R (IsLocalRing.ResidueField R) L] {e : L ⊗[R] S} (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 :=
  sorry

/-- If `R → S` is a local homomorphism of local rings, `R` is strictly henselian and `S` is
weakly-étale over `R`, then `R → S` is an isomorphism. -/
lemma WeaklyEtale.bijective_of_henselianLocalRing [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] [Algebra.WeaklyEtale R S] :
    Function.Bijective (algebraMap R S) :=
  sorry

end Algebra
