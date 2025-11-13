import Mathlib


lemma Ideal.isMaximal_of_isAlgebraic_isField (A B C: Type*) [Field A] [CommRing B] [Field C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [FaithfulSMul B C]
    [Algebra.IsAlgebraic A C] : IsField B := by

  let g : B →ₐ[A] C := IsScalarTower.toAlgHom _ _ _
  let B' : Subalgebra A C := g.range
  have h_1 : IsField B' := Subalgebra.isField_of_algebraic B'
  have h : Function.Injective g := FaithfulSMul.algebraMap_injective B C
  let g' := AlgEquiv.ofInjective g h
  apply MulEquiv.isField h_1 g'


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
--      apply isUnit_of_mem_nonZeroDivisors
--      apply Ne.isUnit
      letI := Ideal.Quotient.field m
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
