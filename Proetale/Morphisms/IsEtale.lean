import Mathlib

universe u

open CategoryTheory Limits MorphismProperty Algebra IsLocalRing

section ring

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma Algebra.isEtaleAt_iff_isUnramifiedAt_and_isSmoothAt
    (q : Ideal S) [q.IsPrime] :
    Algebra.IsEtaleAt R q ↔ Algebra.IsUnramifiedAt R q ∧ Algebra.IsSmoothAt R q := by
  -- This is just `FormallyEtale ↔ FormallyUnramified ∧ FormallySmooth` on the localization.
  simp [Algebra.IsEtaleAt, Algebra.IsUnramifiedAt, Algebra.IsSmoothAt,
    Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth]

lemma Algebra.isUnramifiedAt_of_isSeparable_of_map_eq [FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hr : Algebra.IsSeparable p.ResidueField q.ResidueField)
    (hpq : p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q)) :
    Algebra.IsUnramifiedAt R q := by
  -- `FiniteType` implies `EssFiniteType`, so we can use the local criterion.
  haveI : EssFiniteType R S := inferInstance
  -- Use the characterization `isUnramifiedAt_iff_map_eq`.
  have h := (Algebra.isUnramifiedAt_iff_map_eq (R := R) (S := S) p q)
  exact (h.mpr ⟨hr, hpq⟩)

lemma Algebra.formallyUnramified_atPrime_of_isUnramifiedAt [EssFiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (h : Algebra.IsUnramifiedAt R q) :
    Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) := by
  -- Put the natural `Rₚ`-algebra structure on `S_q`.
  classical
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) Ideal.LiesOver.over).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map p q (algebraMap R S) Ideal.LiesOver.over x).symm
  -- `IsUnramifiedAt R q` is by definition `FormallyUnramified R S_q`.
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime q) := by
    simpa [Algebra.IsUnramifiedAt] using h
  exact Algebra.FormallyUnramified.of_restrictScalars (R := R) (A := Localization.AtPrime p)
    (B := Localization.AtPrime q)

lemma Algebra.isSmoothAt_of_flat_of_isUnramifiedAt [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    (h : Algebra.IsUnramifiedAt R q) :
    Algebra.IsSmoothAt R q := by
  -- TODO (Stacks 00U6 specialized to the étale case): under finite presentation,
  -- `Rₚ → S_q` flat plus `R → S` unramified at `q` implies `R → S` smooth at `q`.
  --
  -- A viable Mathlib-style route is:
  -- 1. Reduce to `FormallySmooth Rₚ S_q` and use `FormallySmooth.comp` with `R → Rₚ`.
  -- 2. Use the local Jacobian criterion (`Mathlib/RingTheory/Smooth/Local.lean`) for `Rₚ → S_q`.
  -- 3. Choose a finite presentation `P` of `S` over `R`, localize it at `q`, and show the
  --    required injectivity on the cotangent complex after tensoring with `ResidueField S_q`,
  --    using flatness and the unramified criterion `isUnramifiedAt_iff_map_eq`.
  sorry

@[stacks 00TF]
lemma Algebra.isEtaleAt_of_flat_of_unramified [FinitePresentation R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)]
    (hr : Algebra.IsSeparable p.ResidueField q.ResidueField)
    (hpq : p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal _) :
    Algebra.IsEtaleAt R q := by
  -- Reduce to unramified + smooth at `q`.
  refine (Algebra.isEtaleAt_iff_isUnramifiedAt_and_isSmoothAt (R := R) (S := S) q).2 ?_
  refine ⟨?_, ?_⟩
  · -- Unramified at `q` comes from separability on residue fields plus `pS_q = m_q`.
    haveI : FiniteType R S := inferInstance
    exact Algebra.isUnramifiedAt_of_isSeparable_of_map_eq (R := R) (S := S) p q hr hpq
  · exact Algebra.isSmoothAt_of_flat_of_isUnramifiedAt (R := R) (S := S) p q
      (Algebra.isUnramifiedAt_of_isSeparable_of_map_eq (R := R) (S := S) p q hr hpq)

end ring
