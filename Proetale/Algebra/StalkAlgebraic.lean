import Mathlib


lemma Ideal.isMaximal_of_isAlgebraic_isField (A B C: Type*) [Field A] [CommRing B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [FaithfulSMul B C]
    [Algebra.IsAlgebraic A C] : IsField B := by

  let g : B →ₐ[A] C := IsScalarTower.toAlgHom _ _ _
  let B' : Subalgebra A C := g.range
  have hb : IsField B' := Subalgebra.isField_of_algebraic B'
  have hc : Function.Injective g := FaithfulSMul.algebraMap_injective B C
  let g' := AlgEquiv.ofInjective g hc
  apply MulEquiv.isField hb g'


lemma Ideal.isMaximal_of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [Ideal.IsPrime q]
    [q.LiesOver m] [Algebra.IsAlgebraic m.ResidueField q.ResidueField] : q.IsMaximal := by

  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  let k : m.ResidueField →+* q.ResidueField := algebraMap _ _
  let fB : B ⧸ q →+* q.ResidueField := algebraMap (B ⧸ q) q.ResidueField
  let fA : A ⧸ m →+* m.ResidueField := algebraMap (A ⧸ m) m.ResidueField
  let of : A ⧸ m →+* B ⧸ q := algebraMap _ _
  let lf : m.ResidueField →+* B ⧸ q :=
    IsLocalization.lift (M := nonZeroDivisors _ ) (g := of) <| by
      intro y
      apply IsUnit.map
      let I := Ideal.Quotient.field m
      apply isUnit_of_mem_nonZeroDivisors y.2
  algebraize [lf]
  have h : IsScalarTower m.ResidueField (B ⧸ q) q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ m))
    rw [← RingHom.cancel_right Ideal.Quotient.mk_surjective]
    ext
    dsimp only [RingHom.coe_comp, Function.comp_apply]
    simp only [RingHom.algebraMap_toAlgebra lf, lf, IsLocalization.lift_eq]
    simp
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ B]
    rfl
  have h : FaithfulSMul (B ⧸ q) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]
    apply IsFractionRing.injective
  exact Ideal.isMaximal_of_isAlgebraic_isField m.ResidueField (B ⧸ q) q.ResidueField


lemma PrimeSpectrum.isClosed_of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A)
    (ha : ∀(q : Ideal B) [q.IsPrime], Algebra.IsAlgebraic
        (q.comap (algebraMap A B)).ResidueField q.ResidueField)
    (hc : PrimeSpectrum.zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    (PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B))
     := by
  intro q hq
  let p := q.comap (algebraMap A B)
  have hi : (p ∈ PrimeSpectrum.zeroLocus I) := by
    rw [Ideal.map, PrimeSpectrum.zeroLocus_span, ← PrimeSpectrum.preimage_specComap_zeroLocus] at hq
    simp at hq
    simp [p]
    assumption
  have hcc : IsClosed {p} := hc hi
  have hm : Ideal.IsMaximal p.asIdeal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact hcc
  have hhh : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have haa : Algebra.IsAlgebraic (p.asIdeal.ResidueField) (q.asIdeal.ResidueField) := by
    apply ha
  have hmm : Ideal.IsMaximal q.asIdeal := by
    apply Ideal.isMaximal_of_isAlgebraic p.asIdeal q.asIdeal
  simp
  rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  exact hmm


lemma PrimeSpectrum.Surjective_HasGoingDown
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.HasGoingDown A B]
    (hs : ∀(p : PrimeSpectrum A) (hc: IsClosed {p}),
    ∃(q : PrimeSpectrum B), p = (q.comap (algebraMap A B))):
--    ∀(p : PrimeSpectrum A), ∃(q : PrimeSpectrum B), p = (q.comap (algebraMap A B))
    Function.Surjective (PrimeSpectrum.comap (algebraMap A B))
     := by
  intro p
  have hm : ∃(m : PrimeSpectrum A), (m.asIdeal.IsMaximal) ∧ (p.asIdeal ≤ m.asIdeal)
  := by
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
    use ⟨m, inferInstance⟩, hm, hle
  obtain ⟨m, hcm, h⟩ := hm
  have he : ∃(n : PrimeSpectrum B), m = (n.comap (algebraMap A B)) := by
    apply hs
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    apply hcm
  obtain ⟨n, hcn⟩ := he
  have : n.asIdeal.LiesOver m.asIdeal := ⟨congr($(hcn).1)⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_ideal_le_liesOver_of_le n.asIdeal h
  use ⟨q, hqp.1⟩
  ext1
  exact hqp.2.1.symm
