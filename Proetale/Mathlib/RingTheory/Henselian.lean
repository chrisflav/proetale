import Mathlib

-- Rename `HenselianRing` to `IsHenselianRing`, ``HenselianLocalRing` to `IsHenselianLocalRing`.

class IsStrictlyHenselianLocalRing (R : Type*) [CommRing R] : Prop
    extends HenselianLocalRing R where
  isSepClosed_residueField : IsSepClosed (IsLocalRing.ResidueField R)

instance (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

universe u

open Polynomial Ideal Quotient

def one_add_I (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a₀ : R ⧸ I) :
    Submonoid (R[X] ⧸ Ideal.span {f}) where
  carrier := {a : R[X]⧸span {f} | ∃ i ∈ span (I.map (algebraMap R (R[X]⧸Ideal.span {f}))) ⊔ span {mk (span {f}) (X - C (Quotient.out a₀) : R[X])}, a = 1 + i}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨i, hi1, hi2⟩
    rcases hb with ⟨j, hj1, hj2⟩
    use i + j + i * j
    constructor
    · apply Ideal.add_mem
      · apply Ideal.add_mem
        assumption
        assumption
      · apply Ideal.mul_mem_left
        assumption
    · rw [hi2, hj2]
      ring
  one_mem' := by
    use 0
    simp

def s_prime (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a₀ : R ⧸ I) : Type u :=
  Localization (one_add_I R I f a₀)

noncomputable
instance (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a₀ : R ⧸ I) :
  CommRing (s_prime R I f a₀) := inferInstanceAs (CommRing (Localization (one_add_I R I f a₀)))

noncomputable
instance (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a₀ : R ⧸ I) :
  Algebra R (s_prime R I f a₀) := inferInstanceAs (Algebra R (Localization (one_add_I R I f a₀)))

instance (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a₀ : R ⧸ I) :
  Algebra.Etale R (s_prime R I f a₀) := sorry

theorem henselian_if_exists_section (R : Type u)
    [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S] (g : S →ₐ[R] R ⧸ I),
    ∃ σ : S →+* R, σ.comp (algebraMap R S) = RingHom.id R) :
    HenselianRing R I := sorry

theorem exsits_section_if_henselian (R S : Type u)
    [CommRing R] (I : Ideal R) [HenselianRing R I]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (g : S →ₐ[R] R ⧸ I) :
    ∃ σ : S →+* R,
    σ.comp (algebraMap R S) = RingHom.id R := sorry
