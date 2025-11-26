import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Topology.JacobsonSpace

/-- `IsScalarTower` version of `Subalgebra.isField_of_algebraic`. -/
lemma IsField.of_isScalarTower_of_isAlgebraic (k R K : Type*) [Field k] [Field K]
    [CommSemiring R] [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic k K] : IsField R :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom k R K)
    (FaithfulSMul.algebraMap_injective R K) |>.isField <| Subalgebra.isField_of_algebraic _

/-- If `q` lies over a maximal ideal `m` and the residue field extension is algebraic, `q`
is maximal. -/
@[stacks 00GA]
lemma Ideal.IsMaximal.of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [Ideal.IsPrime q]
    [q.LiesOver m] [Algebra.IsAlgebraic m.ResidueField q.ResidueField] : q.IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  letI := Ideal.Quotient.field m
  let lf : m.ResidueField →+* B ⧸ q :=
    IsLocalization.lift (M := nonZeroDivisors _ ) (g := algebraMap (A ⧸ m) (B ⧸ q))
      fun y ↦ (isUnit_of_mem_nonZeroDivisors y.2).map _
  algebraize [lf]
  have h : IsScalarTower m.ResidueField (B ⧸ q) q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ m))
    rw [← RingHom.cancel_right Ideal.Quotient.mk_surjective]
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra lf, lf,
      IsLocalization.lift_eq]
    rw [algebraMap_mk, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ B]
    rfl
  have h : FaithfulSMul (B ⧸ q) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]
    apply IsFractionRing.injective
  exact .of_isScalarTower_of_isAlgebraic m.ResidueField (B ⧸ q) q.ResidueField

/-- Let `B` be an `A`-algebra inducing algebraic extensions on residue fields.
If `V(I) ⊆ Spec A` only contains closed points, also `V(IB)` only contains closed points. -/
lemma PrimeSpectrum.zeroLocus_subset_closedPoints_of_isAlgebraic {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (I : Ideal A) (ha : ∀ (q : Ideal B) [q.IsPrime], Algebra.IsAlgebraic
      (q.comap (algebraMap A B)).ResidueField q.ResidueField)
    (hc : PrimeSpectrum.zeroLocus I ⊆ closedPoints (PrimeSpectrum A)) :
    PrimeSpectrum.zeroLocus (I.map (algebraMap A B)) ⊆ closedPoints (PrimeSpectrum B) := by
  intro q hq
  let p := q.comap (algebraMap A B)
  have hi : p ∈ PrimeSpectrum.zeroLocus I := by
    simpa [Ideal.map, ← PrimeSpectrum.preimage_specComap_zeroLocus] using hq
  have hm : Ideal.IsMaximal p.asIdeal := by
    rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    exact hc hi
  have hhh : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have haa : Algebra.IsAlgebraic (p.asIdeal.ResidueField) (q.asIdeal.ResidueField) := ha _
  simpa [PrimeSpectrum.isClosed_singleton_iff_isMaximal] using .of_isAlgebraic p.asIdeal q.asIdeal

/-- If `B` satisfies going-down over `A` and every closed point is in the image
of `Spec B → Spec A`, the map is surjective. -/
lemma PrimeSpectrum.comap_surjective_of_hasGoingDown {A B : Type*} [CommRing A] [CommRing B]
      [Algebra A B] [Algebra.HasGoingDown A B]
      (hs : ∀ p ∈ closedPoints (PrimeSpectrum A),
        ∃ (q : PrimeSpectrum B), p = q.comap (algebraMap A B)) :
    Function.Surjective (comap (algebraMap A B)) := by
  intro p
  obtain ⟨m, hcm, h⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  obtain ⟨n, hcn⟩ := hs ⟨m, hcm.isPrime⟩ (by simpa [PrimeSpectrum.isClosed_singleton_iff_isMaximal])
  have : n.asIdeal.LiesOver m := ⟨congr($(hcn).1)⟩
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_ideal_le_liesOver_of_le n.asIdeal h
  use ⟨q, hqp.1⟩
  ext1
  exact hqp.2.1.symm
