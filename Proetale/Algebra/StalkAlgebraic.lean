import Mathlib

lemma Ideal.isMaximal_of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [q.IsPrime]
    [q.LiesOver m] [Algebra.IsAlgebraic m.ResidueField q.ResidueField] : q.IsMaximal :=
  sorry
