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

/-- If `f : R →+* S` is a surjective flat ring map and `f x = 0`, then there exists `y : R`
such that `f y = 1` and `y * x = 0`. This expresses that the kernel of a surjective flat
map is pure. -/
lemma exists_eq_mul_of_surjective_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (hsurj : Function.Surjective f)
    (x : R) (hx : f x = 0) : ∃ y : R, f y = 1 ∧ y * x = 0 := by
  algebraize [f]
  have e : (R ⧸ RingHom.ker f) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := f.quotientKerEquivOfSurjective hsurj) fun _ ↦ rfl
  have : (RingHom.ker f).Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  obtain ⟨z, hzker, hxz⟩ := Ideal.exists_eq_mul_of_pure (show x ∈ RingHom.ker f from hx)
  refine ⟨1 - z, ?_, ?_⟩
  · rw [map_sub, map_one, RingHom.mem_ker.mp hzker, sub_zero]
  · rw [sub_mul, one_mul, mul_comm, ← hxz, sub_self]

lemma exists_eq_mul_of_surjective_flat' {R S ι : Type*} [CommRing R] [CommRing S] [Finite ι]
    (f : R →+* S) (hf : f.Flat) (hsurj : Function.Surjective f)
    (x : ι → R) (hx : ∀ i, f (x i) = 0) : ∃ y : R, f y = 1 ∧ ∀ i : ι, y * x i = 0 := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp e) (by grind)
    refine ⟨y, hy, fun i ↦ by simpa using hy' (e.symm i)⟩
  | h_empty => exact ⟨1, by simp, by simp⟩
  | h_option h =>
    obtain ⟨y, hy, hy'⟩ := h (x.comp Option.some) (by grind)
    obtain ⟨z, hz, hz'⟩ := exists_eq_mul_of_surjective_flat f hf hsurj (x .none) (by grind)
    refine ⟨y * z, by simp [hy, hz], fun | some i => by grind | none => by grind⟩

namespace Ring.WeakDimensionLEOne

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- If `R` is of weak dimension `≤ 1`, then any submodule of a flat module is flat. -/
lemma flat_submodule [Ring.WeakDimensionLEOne R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N := by
  rw [Module.Flat.iff_lTensor_injective]
  intro I hI
  have : Module.Flat R I := Ring.WeakDimensionLEOne.flat_of_fg I hI
  have h : Function.Injective (⇑(I.subtype.lTensor M) ∘ ⇑(N.subtype.rTensor I)) :=
    (Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ N.injective_subtype)
  have hnat : ⇑(I.subtype.lTensor M) ∘ ⇑(N.subtype.rTensor I) =
      ⇑(N.subtype.rTensor R) ∘ ⇑(I.subtype.lTensor N) := by
    rw [← LinearMap.coe_comp, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.coe_comp]
  exact (hnat ▸ h).of_comp

lemma flat_ideal [Ring.WeakDimensionLEOne R] (I : Ideal R) :
    Module.Flat R I :=
  flat_submodule _ _

/-- If `R` is of weak dimension `≤ 1` and `S` is weakly étale over `R`, then the same holds for
`S`. -/
lemma of_weaklyEtale [Ring.WeakDimensionLEOne R] [Algebra.WeaklyEtale R S] :
    Ring.WeakDimensionLEOne S :=
  sorry

/-- The product of valuation rings is of weak dimension `≤ 1`. -/
lemma pi_of_isValuationRing {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, ValuationRing (R i)] :
    WeakDimensionLEOne (Π i, R i) :=
  sorry

/-- If `R` is of weak dimension `≤ 1`, it is integrally closed in any flat extension `S` such
that `R → S` is an epi. -/
lemma isIntegrallyClosedIn_of_isEpi [WeakDimensionLEOne R] [Module.Flat R S] [FaithfulSMul R S]
    [Algebra.IsEpi R S] :
    IsIntegrallyClosedIn R S := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨FaithfulSMul.algebraMap_injective R S, fun {x} hx ↦ ?_⟩
  let A : Subalgebra R S := Algebra.adjoin R {x}
  have : Module.Finite R A := Algebra.finite_adjoin_simple_of_isIntegral hx
  have : Module.Flat R A := flat_submodule R (Subalgebra.toSubmodule A)
  have : Algebra.IsEpi R A := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro a
    have hinj : Function.Injective ((TensorProduct.lift (LinearMap.mul R S)) ∘ₗ
        TensorProduct.map A.val.toLinearMap A.val.toLinearMap) :=
      Algebra.IsEpi.injective_lift_mul.comp <| TensorProduct.map_injective_of_flat_flat _ _
        Subtype.val_injective Subtype.val_injective
    exact hinj (by simp)
  obtain ⟨y, hy⟩ := (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := R) (A := A)).mp
    ‹_› ⟨x, Algebra.self_mem_adjoin_singleton R x⟩
  exact ⟨y, by simpa using congrArg Subtype.val hy⟩

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
    Ideal.Quotient.mk_surjective x (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
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
    simp only [Ideal.localized'_eq_map, hI', IsLocalization.map_under s S I]
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

variable {R} in
/-- In an absolutely flat ring every element `a` can be written as `a = a * a * b`,
i.e. absolutely flat commutative rings are von Neumann regular. -/
theorem exists_eq_mul_self_mul [AbsolutelyFlat R] (a : R) : ∃ b, a = a * a * b := by
  have : (Ideal.span {a}).Pure := AbsolutelyFlat.flat _
  obtain ⟨y, hy, heq⟩ := Ideal.exists_eq_mul_of_pure (Ideal.mem_span_singleton_self a)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨b, by linear_combination heq⟩

variable {R} in
/-- A commutative ring in which every element `a` can be written as `a = a * a * b`
(i.e. a von Neumann regular commutative ring) is absolutely flat. This is the converse of
`Ring.AbsolutelyFlat.exists_eq_mul_self_mul`. -/
theorem of_forall_exists_eq_mul_self_mul (h : ∀ a : R, ∃ b, a = a * a * b) :
    AbsolutelyFlat R := by
  refine ⟨fun I ↦ Ideal.Pure.of_inf_eq_mul I fun J _ ↦
    le_antisymm (fun y hy ↦ ?_) (Ideal.mul_le_inf)⟩
  obtain ⟨hyI, hyJ⟩ := Submodule.mem_inf.mp hy
  obtain ⟨b, hb⟩ := h y
  have hy' : y * (b * y) = y := by linear_combination -hb
  exact hy' ▸ Ideal.mul_mem_mul hyI (J.mul_mem_left b hyJ)

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

instance (priority := low) [AbsolutelyFlat R] : IsReduced R := by
  have h : AbsolutelyFlat R ↔ IsReduced R ∧ ∀ P : Ideal R, P.IsPrime → P.IsMaximal :=
    (tfae R).out 0 1
  exact (h.mp ‹_›).1

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat)

open TensorProduct

include h in
@[stacks 092C]
theorem _root_.Module.Flat.of_flat_lmul'_of_flat [Module.Flat R M] : Module.Flat S M := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hx ↦ ?_
  obtain ⟨t, ht, ht'⟩ := exists_eq_mul_of_surjective_flat' _ h (fun x ↦ ⟨1 ⊗ₜ[R] x, by simp⟩)
    (fun i : Fin l ↦ (1 : S) ⊗ₜ[R] (f i) - (f i) ⊗ₜ[R] (1 : S)) (fun i ↦ by simp)
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
  simp only [AlgHom.toRingHom_eq_coe, map_sum, RingHom.coe_coe,
    Algebra.TensorProduct.lmul'_apply_tmul] at ht
  simp only [Finset.sum_mul, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, sub_eq_zero] at ht'
  let φ (i : Fin l) : S ⊗[R] S →ₗ[R] S ⊗[R] M :=
    LinearMap.lTensor S (LinearMap.toSpanSingleton S M (x i))
  have hg : ∑ y : s ×ˢ Finset.univ, (y.1.1.1 * f y.1.2) ⊗ₜ[R] (y.1.1.2 • x y.1.2) = 0 := by
    simp only [Finset.sum_coe_sort _
        (fun y : (S × S) × Fin l ↦ (y.1.1 * f y.2) ⊗ₜ[R] (y.1.2 • x y.2)),
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
      (by simp_rw [← mul_assoc, mul_comm (f _), mul_comm (_ * _), Algebra.smul_def,
        forall_true_iff])

include h in
@[stacks 092I "(1)"]
theorem of_flat_lmul' [AbsolutelyFlat R] : AbsolutelyFlat S :=
  ⟨fun _ ↦ Module.Flat.of_flat_lmul'_of_flat R S _ h⟩

end Ring.AbsolutelyFlat

universe u v

open TensorProduct in
/-- If `A` is a domain that is integrally closed in an algebraic field extension `L` of its
fraction field, there is a "cartesian diagram" of rings with vertices `A`, `L`, `S` and `T`,
where `S` has weak dimension at most one and `S → T` is a flat, injective ring epimorphism.
Cartesianness is expressed as exactness of `0 → A → L × S → T`, where the first map is
`a ↦ (a, a)` and the second map is the difference of the two canonical maps. -/
@[stacks 092U]
theorem IsIntegrallyClosedIn.exists_weakDimensionLEOne_isEpi_exact
    (A : Type u) (L : Type v) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [FaithfulSMul A L] [Algebra.IsAlgebraic A L] [IsIntegrallyClosedIn A L] :
    ∃ (S T : Type v) (_ : CommRing S) (_ : CommRing T) (_ : Algebra A S) (_ : Algebra A T)
      (_ : Algebra S T) (_ : Algebra L T) (_ : IsScalarTower A S T) (_ : IsScalarTower A L T),
      Ring.WeakDimensionLEOne S ∧ Module.Flat S T ∧ FaithfulSMul S T ∧ Algebra.IsEpi S T ∧
      Function.Exact (LinearMap.prod (Algebra.linearMap A L) (Algebra.linearMap A S))
        ((IsScalarTower.toAlgHom A L T).toLinearMap ∘ₗ LinearMap.fst A L S -
          (IsScalarTower.toAlgHom A S T).toLinearMap ∘ₗ LinearMap.snd A L S) :=
  sorry

open TensorProduct in
/-- Ring epimorphisms are stable under base change: if `S → T` is an epimorphism of
commutative rings and `B` is any `R`-algebra, then `S ⊗[R] B → T ⊗[R] B` is an
epimorphism. -/
lemma Algebra.IsEpi.tensorProductMap {R S T B : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing B] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R B]
    [Algebra.IsEpi S T] :
    letI := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (AlgHom.id R B)).toRingHom.toAlgebra
    Algebra.IsEpi (S ⊗[R] B) (T ⊗[R] B) := by
  letI : Algebra (S ⊗[R] B) (T ⊗[R] B) := (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom R S T) (AlgHom.id R B)).toRingHom.toAlgebra
  haveI : IsScalarTower S (S ⊗[R] B) (T ⊗[R] B) := .of_algebraMap_eq fun s ↦ by
    change algebraMap S (T ⊗[R] B) s = (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (AlgHom.id R B)) (algebraMap S (S ⊗[R] B) s)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.map_tmul, map_one]
    simp
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  -- The images of `S ⊗[R] B` satisfy the tensor identity for trivial reasons.
  have hb : ∀ c : S ⊗[R] B, (1 : T ⊗[R] B) ⊗ₜ[S ⊗[R] B]
      (algebraMap (S ⊗[R] B) (T ⊗[R] B) c) =
      (algebraMap (S ⊗[R] B) (T ⊗[R] B) c) ⊗ₜ[S ⊗[R] B] (1 : T ⊗[R] B) := fun c ↦ by
    have h1 := (Algebra.TensorProduct.includeRight (R := S ⊗[R] B) (A := T ⊗[R] B)
      (B := T ⊗[R] B)).commutes c
    have h2 := (Algebra.TensorProduct.includeLeft (R := S ⊗[R] B) (S := S ⊗[R] B)
      (A := T ⊗[R] B) (B := T ⊗[R] B)).commutes c
    exact h1.trans h2.symm
  -- The elements `t ⊗ 1` satisfy it because `S → T` is an epimorphism.
  have key : ∀ t : T, (1 : T ⊗[R] B) ⊗ₜ[S ⊗[R] B] (t ⊗ₜ[R] (1 : B)) =
      (t ⊗ₜ[R] (1 : B)) ⊗ₜ[S ⊗[R] B] (1 : T ⊗[R] B) := by
    intro t
    haveI : SMulCommClass (S ⊗[R] B) S (T ⊗[R] B) :=
      ⟨fun c s x ↦ by simp only [Algebra.smul_def]; ring⟩
    let φ : T →ₗ[S] T →ₗ[S] ((T ⊗[R] B) ⊗[S ⊗[R] B] (T ⊗[R] B)) := LinearMap.mk₂ S
      (fun u v ↦ (u ⊗ₜ[R] (1 : B)) ⊗ₜ[S ⊗[R] B] (v ⊗ₜ[R] (1 : B)))
      (fun u₁ u₂ v ↦ by simp [TensorProduct.add_tmul])
      (fun s u v ↦ by simp [← TensorProduct.smul_tmul'])
      (fun u v₁ v₂ ↦ by simp [TensorProduct.tmul_add, TensorProduct.add_tmul])
      (fun s u v ↦ by simp [← TensorProduct.smul_tmul', TensorProduct.tmul_smul])
    have h := (Algebra.isEpi_iff_forall_one_tmul_eq S T).mp inferInstance t
    have h2 := congrArg (_root_.TensorProduct.lift φ) h
    simpa [φ, ← Algebra.TensorProduct.one_def] using h2
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, TensorProduct.zero_tmul]
  | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, TensorProduct.add_tmul, h₁, h₂]
  | tmul t b =>
    have h1 : (t ⊗ₜ[R] b : T ⊗[R] B) =
        (t ⊗ₜ[R] (1 : B)) * algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b) := by
      have h2 : algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b) = (1 : T) ⊗ₜ[R] b := by
        change (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R B))
          ((1 : S) ⊗ₜ[R] b) = _
        rw [Algebra.TensorProduct.map_tmul, map_one]
        rfl
      rw [h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1]
    calc (1 : T ⊗[R] B) ⊗ₜ[S ⊗[R] B]
          ((t ⊗ₜ[R] (1 : B)) * algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b))
        = ((1 : T ⊗[R] B) ⊗ₜ[S ⊗[R] B] (t ⊗ₜ[R] (1 : B))) *
          ((1 : T ⊗[R] B) ⊗ₜ[S ⊗[R] B]
            (algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b))) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      _ = ((t ⊗ₜ[R] (1 : B)) ⊗ₜ[S ⊗[R] B] (1 : T ⊗[R] B)) *
          ((algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b)) ⊗ₜ[S ⊗[R] B]
            (1 : T ⊗[R] B)) := by rw [key t, hb]
      _ = ((t ⊗ₜ[R] (1 : B)) * algebraMap (S ⊗[R] B) (T ⊗[R] B) ((1 : S) ⊗ₜ[R] b))
            ⊗ₜ[S ⊗[R] B] (1 : T ⊗[R] B) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

open TensorProduct in
/-- Let `A` be a domain and `B` a weakly étale `A`-algebra. If `L` is an algebraic field
extension of the fraction field of `A` and `A` is integrally closed in `L`, then `B` is
integrally closed in `B ⊗[A] L`. -/
@[stacks 092W]
theorem Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct
    (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] [Field L] [Algebra A L] [FaithfulSMul A L]
    [Algebra.IsAlgebraic A L] [IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) := by
  obtain ⟨S, T, _, _, _, _, _, _, _, _, hwd, hMflat, hfaith, hepi, hexact⟩ :=
    IsIntegrallyClosedIn.exists_weakDimensionLEOne_isEpi_exact A L
  -- The cartesian diagram base changed along the flat `A`-algebra `B`.
  set g : S ⊗[A] B →ₐ[A] T ⊗[A] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S T) (AlgHom.id A B) with hgdef
  set hL : L ⊗[A] B →ₐ[A] T ⊗[A] B :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A L T) (AlgHom.id A B) with hLdef
  letI : Algebra (S ⊗[A] B) (T ⊗[A] B) := g.toRingHom.toAlgebra
  -- `S ⊗[A] B` has weak dimension at most one, and `S ⊗[A] B → T ⊗[A] B` is a flat,
  -- injective ring epimorphism. Hence `S ⊗[A] B` is integrally closed in `T ⊗[A] B`.
  haveI : Ring.WeakDimensionLEOne (S ⊗[A] B) :=
    Ring.WeakDimensionLEOne.of_weaklyEtale (R := S)
  haveI : Module.Flat (S ⊗[A] B) (T ⊗[A] B) :=
    RingHom.Flat.tensorProductMap (RingHom.flat_algebraMap_iff.mpr hMflat) (RingHom.Flat.id B)
  have hg_eq : ∀ v, g v = (IsScalarTower.toAlgHom A S T).toLinearMap.rTensor B v := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb]
    | tmul s b => simp [hgdef]
  have hginj : Function.Injective g := fun a b hab ↦
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) _
      (FaithfulSMul.algebraMap_injective S T) (by rw [← hg_eq a, ← hg_eq b]; exact hab)
  haveI : FaithfulSMul (S ⊗[A] B) (T ⊗[A] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
  haveI : Algebra.IsEpi (S ⊗[A] B) (T ⊗[A] B) := Algebra.IsEpi.tensorProductMap
  haveI hic : IsIntegrallyClosedIn (S ⊗[A] B) (T ⊗[A] B) :=
    Ring.WeakDimensionLEOne.isIntegrallyClosedIn_of_isEpi (S ⊗[A] B)
  -- The base changed sequence `0 → B → (L × S) ⊗[A] B → T ⊗[A] B` is exact.
  have hexactB := Module.Flat.rTensor_exact B hexact
  set e : ((L × S) ⊗[A] B) ≃ₗ[A] (L ⊗[A] B) × (S ⊗[A] B) := TensorProduct.prodLeft A A L S B
    with hedef
  have hGe : ∀ w : (L × S) ⊗[A] B,
      ((IsScalarTower.toAlgHom A L T).toLinearMap ∘ₗ LinearMap.fst A L S -
        (IsScalarTower.toAlgHom A S T).toLinearMap ∘ₗ LinearMap.snd A L S).rTensor B w =
      hL (e w).1 - g (e w).2 := by
    intro w
    induction w with
    | zero => simp
    | add w₁ w₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂, Prod.fst_add, Prod.snd_add]
      ring
    | tmul p b =>
      obtain ⟨l, s⟩ := p
      simp [hedef, hLdef, hgdef]
  rw [isIntegrallyClosedIn_iff]
  constructor
  · -- `B → B ⊗[A] L` is injective since `B` is flat over `A` and `A → L` is injective.
    have h1 : Function.Injective ((Algebra.linearMap A L).rTensor B) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (FaithfulSMul.algebraMap_injective A L)
    have h2 : ∀ b : B, (Algebra.linearMap A L).rTensor B ((TensorProduct.lid A B).symm b) =
        Algebra.TensorProduct.comm A B L (algebraMap B (B ⊗[A] L) b) := fun b ↦ by
      simp [TensorProduct.lid_symm_apply, Algebra.TensorProduct.algebraMap_apply]
    intro b₁ b₂ hb
    have h3 := congrArg (Algebra.TensorProduct.comm A B L) hb
    rw [← h2, ← h2] at h3
    exact (TensorProduct.lid A B).symm.injective (h1 h3)
  · -- An element of `B ⊗[A] L` integral over `B` maps to an element of `T ⊗[A] B` integral
    -- over `S ⊗[A] B`, hence to an element of `S ⊗[A] B`. By cartesianness it lies in `B`.
    intro x hx
    set x' := Algebra.TensorProduct.comm A B L x with hx'def
    obtain ⟨z, hz⟩ : ∃ z, algebraMap (S ⊗[A] B) (T ⊗[A] B) z = hL x' := by
      rw [← IsIntegrallyClosedIn.isIntegral_iff]
      obtain ⟨P, hPm, hPe⟩ := hx
      refine ⟨P.map (Algebra.TensorProduct.includeRight (R := A) (A := S)).toRingHom,
        hPm.map _, ?_⟩
      have hsq : (algebraMap (S ⊗[A] B) (T ⊗[A] B)).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom =
          (hL.toRingHom.comp
            (Algebra.TensorProduct.comm A B L).toAlgHom.toRingHom).comp
            (algebraMap B (B ⊗[A] L)) := by
        ext b
        simp [hgdef, hLdef, RingHom.algebraMap_toAlgebra,
          Algebra.TensorProduct.algebraMap_apply]
      have hy_eq : hL x' = (hL.toRingHom.comp
          (Algebra.TensorProduct.comm A B L).toAlgHom.toRingHom) x := rfl
      rw [Polynomial.eval₂_map, hsq, hy_eq, ← Polynomial.hom_eval₂, hPe, map_zero]
    set u := e.symm (x', z) with hudef
    have hu : (((IsScalarTower.toAlgHom A L T).toLinearMap ∘ₗ LinearMap.fst A L S -
        (IsScalarTower.toAlgHom A S T).toLinearMap ∘ₗ LinearMap.snd A L S).rTensor B) u = 0 := by
      rw [hGe u, hudef, e.apply_symm_apply]
      change hL x' - g z = 0
      rw [show g z = algebraMap (S ⊗[A] B) (T ⊗[A] B) z from rfl, hz, sub_self]
    obtain ⟨v, hv⟩ := (hexactB u).mp hu
    refine ⟨TensorProduct.lid A B v, ?_⟩
    have hv1 : v = (1 : A) ⊗ₜ[A] (TensorProduct.lid A B v) := by
      rw [← TensorProduct.lid_symm_apply]
      exact ((TensorProduct.lid A B).symm_apply_apply v).symm
    have hfst : (e ((LinearMap.prod (Algebra.linearMap A L)
        (Algebra.linearMap A S)).rTensor B v)).1 =
        (1 : L) ⊗ₜ[A] (TensorProduct.lid A B v) := by
      conv_lhs => rw [hv1]
      simp [hedef]
    apply (Algebra.TensorProduct.comm A B L).injective
    have hcomm_alg : Algebra.TensorProduct.comm A B L (algebraMap B (B ⊗[A] L)
        (TensorProduct.lid A B v)) = (1 : L) ⊗ₜ[A] (TensorProduct.lid A B v) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    rw [hcomm_alg, ← hfst, hv, hudef, e.apply_symm_apply]
