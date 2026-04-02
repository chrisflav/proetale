/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Proetale.Algebra.WeaklyEtale
import Mathlib

/-!
# Weak dimension of a commutative ring

Since mathlib does not have `Tor`, we only define some special cases in low dimensions.
-/

/-- A ring `R` is absolutely flat if every ideal of `R` is pure, i.e. `R ⧸ I` is flat. -/
class Ring.AbsolutelyFlat (R : Type*) [CommRing R] where
  flat (I : Ideal R) : Module.Flat R (R ⧸ I)

/-- A ring `R` is of weak dimension `≤ 1` if any finitely generated ideal is flat. -/
class Ring.WeakDimensionLEOne (R : Type*) [CommRing R] where
  flat_of_fg (I : Ideal R) : I.FG → Module.Flat R I

-- Follows from `Ideal.exists_eq_mul_of_pure` in mathlib
lemma exists_eq_mul_of_surjective_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (x : R) (hx : f x = 0) : ∃ y : R, f y = 1 ∧ y * x = 0 := sorry

lemma exists_eq_mul_of_surjective_flat' {R S ι : Type*} [CommRing R] [CommRing S] [Finite ι]
    (f : R →+* S) (hf : f.Flat) (x : ι → R) (hx : ∀ i, f (x i) = 0) : ∃ y : R, f y = 1 ∧ ∀ i : ι, y * x i = 0 := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp e) (by grind)
    refine ⟨y, hy, fun i ↦ by simpa using hy' (e.symm i)⟩
  | h_empty => exact ⟨1, by simp, by simp⟩
  | h_option h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp Option.some) (by grind)
    obtain ⟨z, hz, hz'⟩ := exists_eq_mul_of_surjective_flat f hf (x .none) (by grind)
    refine ⟨y * z, by simp [hy, hz], fun | some i => by grind | none => by grind⟩

namespace Ring.WeakDimensionLEOne

variable (R : Type*) [CommRing R]

/-- If `R` is of weak dimension `≤ 1` if any submodule of a flat module is flat. -/
lemma flat_submodule [Ring.WeakDimensionLEOne R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N :=
  sorry

end Ring.WeakDimensionLEOne

namespace Ring.AbsolutelyFlat

instance of_field (R : Type*) [Field R] : AbsolutelyFlat R where
  flat _ := inferInstance

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

lemma of_isField (h : IsField R) : AbsolutelyFlat R := @of_field R h.toField

lemma isField_of_isLocalRing [IsLocalRing R] [AbsolutelyFlat R] : IsField R := by
  apply Ring.isField_iff_maximal_bot.mpr
  suffices h : IsLocalRing.maximalIdeal R = ⊥ from h ▸ inferInstance
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  obtain ⟨y, hy, hy'⟩ := exists_eq_mul_of_surjective_flat
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)) (AbsolutelyFlat.flat _)
    x (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  obtain ⟨y, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp
    fun hy'' ↦ one_ne_zero <| hy.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hy'')
  simpa using congr(y⁻¹ * $hy')

variable {R} in
lemma of_isLocalization [AbsolutelyFlat R] (s : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization s S] : AbsolutelyFlat S := by
  refine .mk fun I ↦ ?_
  -- `obtain` is used to erase the value so that `subst` doesn't give a recursive error.
  obtain ⟨I', hI'⟩ : ∃ I' : Ideal R, I' = I.comap (algebraMap R S) := ⟨_, rfl⟩
  have := AbsolutelyFlat.flat I'
  have : I = Submodule.localized' S s (Algebra.linearMap R S) I' := by
    simp only [Ideal.localized'_eq_map, hI', IsLocalization.map_comap s S I]
  subst this
  let f := Submodule.toLocalizedQuotient' S s (Algebra.linearMap R S) I'
  exact Module.Flat.of_isLocalizedModule (R := R) (M := R ⧸ I') S s f

lemma localizationPreserves : LocalizationPreserves fun R _ ↦ AbsolutelyFlat R :=
    fun s S _ _ _ _ ↦ of_isLocalization s S

instance [AbsolutelyFlat R] (s : Submonoid R) : AbsolutelyFlat (Localization s) :=
  localizationPreserves s _ inferInstance

lemma isField_of_isLocalization_prime [AbsolutelyFlat R] (p : Ideal R) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p] :
    IsField S := @isField_of_isLocalRing _ _ (IsLocalization.AtPrime.isLocalRing S p)
  (of_isLocalization p.primeCompl S)

lemma _root_.Module.flat_of_localization_atPrime_isField
    (h : ∀ (P : Ideal R) [P.IsPrime], IsField (Localization.AtPrime P)) : Module.Flat R M := by
  refine Module.flat_of_localized_maximal (R := R) M fun P hP ↦ ?_
  suffices Module.Flat (Localization P.primeCompl) (LocalizedModule P.primeCompl M)
    from (Localization.flat R P.primeCompl).trans _ _ _
  let := (h P).toField
  infer_instance

instance [AbsolutelyFlat R] : Module.Flat R M :=
  Module.flat_of_localization_atPrime_isField _ _ (fun _ _ ↦ isField_of_isLocalRing _)

theorem tfae : [AbsolutelyFlat R,
    IsReduced R ∧ ∀ P : Ideal R, P.IsPrime → P.IsMaximal,
    IsReduced R ∧ Ring.KrullDimLE 0 R,
    ∀ (P : Ideal R) [P.IsPrime], IsField (Localization.AtPrime P)].TFAE := by
  tfae_have 1 ↔ 4 := ⟨fun _ _ ↦ isField_of_isLocalRing _,
    fun h ↦ .mk fun I ↦ Module.flat_of_localization_atPrime_isField _ _ h⟩
  tfae_have 2 ↔ 3 := and_congr_right_iff.mpr fun _ ↦ krullDimLE_zero_iff.symm
  tfae_have 2 → 4 := by
    rintro ⟨_, h'⟩ P hP
    have : KrullDimLE 0 (Localization.AtPrime P) := Ring.krullDimLE_iff.mpr <| le_trans
      (by simpa [IsLocalization.AtPrime.ringKrullDim_eq_height P] using
        P.height_le_ringKrullDim_of_ne_top hP.ne_top)
      ((Ring.krullDimLE_iff (R := R)).mp (.mk₀ h'))
    exact Ring.KrullDimLE.isField_of_isReduced
  tfae_have 4 → 2 := fun h ↦ by
    let (P : Ideal R) [P.IsPrime] := (h P).toField
    refine ⟨isReduced_ofLocalizationMaximal _ fun P hP ↦ ?_, Ring.krullDimLE_zero_iff.mp ?_⟩
    · infer_instance
    · exact Ring.krullDimLE_of_isLocalization_maximal (fun P hP ↦ Localization.AtPrime P)
        fun P hP ↦ inferInstance
  tfae_finish

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat)

open TensorProduct

include h in
@[stacks 092C]
theorem _root_.Module.Flat.of_flat_lmul'_of_flat [Module.Flat R M] : Module.Flat S M := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hx ↦ ?_
  obtain ⟨t, ht, ht'⟩ := exists_eq_mul_of_surjective_flat' _ h
    (fun i : Fin l ↦ (1 : S) ⊗ₜ[R] (f i) - (f i) ⊗ₜ[R] (1 : S)) (fun i ↦ by simp)
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  simp only [AlgHom.toRingHom_eq_coe, map_sum, RingHom.coe_coe,
    Algebra.TensorProduct.lmul'_apply_tmul] at ht
  simp only [Finset.sum_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, sub_eq_zero] at ht'
  let φ (i : Fin l) : S ⊗[R] S →ₗ[R] S ⊗[R] M := LinearMap.lTensor S (LinearMap.toSpanSingleton S M (x i))
  have hg : ∑ y : s ×ˢ Finset.univ, (y.1.1.1 * f y.1.2) ⊗ₜ[R] (y.1.1.2 • x y.1.2) = 0 := by
    simp only [Finset.sum_coe_sort _ (fun y : (S × S) × Fin l ↦ (y.1.1 * f y.2) ⊗ₜ[R] (y.1.2 • x y.2)),
      Finset.sum_product, Finset.sum_comm (s := s)]
    replace ht' := by simpa [φ] using congr(fun i ↦ (φ i) $(ht' i))
    simp only [← ht', Finset.sum_comm (t := s), ← tmul_sum, mul_smul, ← Finset.smul_sum, hx,
      smul_zero, tmul_zero, Finset.sum_const_zero]
  obtain ⟨l', g, y, ha, ha'⟩ := vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective R
    (Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)) hg
  refine ⟨l', fun i j ↦ s.attach.sum fun x ↦ x.1.1 * (algebraMap R S) (g ⟨⟨x.1, i⟩, by simp⟩ j),
    y, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp only [Finset.sum_smul, mul_smul, Finset.sum_comm, ← Finset.smul_sum, algebraMap_smul]
    simp only [← ha, ← mul_smul, ← Finset.sum_smul, ← Finset.sum_coe_sort_eq_attach,
      Finset.sum_coe_sort _ fun (i : S × S) ↦ i.1 * i.2, ht, one_smul]
  · simp only [Finset.mul_sum, ← ha' j, ← Finset.sum_product_right']
    exact Finset.sum_bij' (fun a _ ↦ ⟨⟨a.1, a.2⟩, by simp⟩) (fun a _ ↦ ⟨⟨a.1.1, by grind⟩, a.1.2⟩)
      (by simp) (by simp) (by simp) (by simp)
      (by simp_rw [← mul_assoc, mul_comm (f _), mul_comm (_ * _), Algebra.smul_def, forall_true_iff])

include h in
@[stacks 092I "(1)"]
theorem of_flat_lmul' [AbsolutelyFlat R] : AbsolutelyFlat S :=
  ⟨fun _ ↦ Module.Flat.of_flat_lmul'_of_flat R S _ h⟩

end Ring.AbsolutelyFlat
