/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaFunction

/-!
# Points with finite residue field and closed points

Every point of a scheme with finite residue field is a closed point: in any affine open
`Spec A` containing it, the quotient of `A` by the corresponding prime embeds into the
finite residue field, so it is a finite integral domain, hence a field, and the prime is
maximal.

Conversely, if `X` is locally of finite type over `ℤ`, every closed point of `X` has
finite residue field: this is the general Nullstellensatz (Zariski's lemma over the
Jacobson ring `ℤ`), by which the residue field is a finitely generated `ℤ`-module, and a
field which is finitely generated as a `ℤ`-module is finite.

## Main statements

- `AlgebraicGeometry.Scheme.isClosed_singleton_of_mem_finitePoints`
- `AlgebraicGeometry.Scheme.finitePoints_eq_closedPoints`
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

section Auxiliary

variable {X}

/-- `ℤ` is a Jacobson ring: the Jacobson radical is trivial (no nonzero integer is
divisible by all primes) and every nonzero prime ideal is maximal. -/
private instance : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hbot
  · refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := hx 1
    have h2 := hx (-1)
    rw [Int.isUnit_iff] at h1 h2
    rw [Ideal.mem_bot]
    omega
  · haveI := hP
    haveI := IsPrime.to_maximal_ideal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field which is a finitely generated `ℤ`-module is finite. -/
private lemma finite_of_field_of_moduleFinite_int (K : Type*) [Field K] [Module.Finite ℤ K] :
    Finite K := by
  have hint : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · haveI : Fact (ringChar K).Prime := ⟨hp⟩
    letI : Algebra (ZMod (ringChar K)) K := ZMod.algebra K (ringChar K)
    have : Module.Finite (ZMod (ringChar K)) K :=
      Module.Finite.of_restrictScalars_finite ℤ (ZMod (ringChar K)) K
    exact Module.finite_of_finite (ZMod (ringChar K))
  · haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    have hinj : Function.Injective (algebraMap ℤ K) := by
      rw [algebraMap_int_eq]
      exact Int.cast_injective
    exact absurd (isField_of_isIntegral_of_isField hinj (Field.toIsField K)) Int.not_isField

/-- The residue field of `X` at a point `x` of an affine open `U` is isomorphic to the
residue field of the corresponding prime ideal of `Γ(X, U)`. -/
private noncomputable def residueFieldEquivPrimeIdealOf {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) :
    (hU.primeIdealOf x).asIdeal.ResidueField ≃+* X.residueField x.1 :=
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
      (X.presheaf.stalk x.1)).toRingEquiv

private lemma finite_residueField_iff_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) :
    Finite (X.residueField x.1) ↔ Finite (hU.primeIdealOf x).asIdeal.ResidueField :=
  ((residueFieldEquivPrimeIdealOf hU x).toEquiv.finite_iff).symm

/-- If the residue field of `X` at `x ∈ U` is finite, then the prime ideal of `Γ(X, U)`
corresponding to `x` is maximal: `Γ(X, U) ⧸ p` embeds into the finite residue field, so
it is a finite integral domain, hence a field. -/
private lemma isMaximal_primeIdealOf_of_finite_residueField {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (h : Finite (X.residueField x.1)) :
    (hU.primeIdealOf x).asIdeal.IsMaximal := by
  have h1 : Finite (hU.primeIdealOf x).asIdeal.ResidueField :=
    (finite_residueField_iff_primeIdealOf hU x).mp h
  have h2 : Finite (Γ(X, U) ⧸ (hU.primeIdealOf x).asIdeal) :=
    Finite.of_injective _
      (hU.primeIdealOf x).asIdeal.injective_algebraMap_quotient_residueField
  exact Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)

/-- If the prime ideal of `Γ(X, U)` corresponding to `x ∈ U` is maximal, then `x` is a
closed point of `U`. This is the converse of `IsAffineOpen.primeIdealOf_isMaximal_of_isClosed`. -/
private lemma isClosed_singleton_of_isMaximal_primeIdealOf {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (h : (hU.primeIdealOf x).asIdeal.IsMaximal) :
    IsClosed ({x} : Set U) := by
  have hh : IsHomeomorph (⇑hU.isoSpec.hom.base) :=
    (TopCat.isIso_iff_isHomeomorph _).mp inferInstance
  refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed
    hh.isClosedEmbedding).mpr ?_
  rw [Set.image_singleton]
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr h

end Auxiliary

/-- A point with finite residue field is a closed point. -/
lemma isClosed_singleton_of_mem_finitePoints {x : X} (hx : x ∈ X.finitePoints) :
    IsClosed ({x} : Set X) := by
  rw [mem_finitePoints] at hx
  have hcover : TopologicalSpace.IsOpenCover (fun U : X.affineOpens => (U : X.Opens)) :=
    iSup_affineOpens_eq_top X
  rw [hcover.isClosed_iff_coe_preimage]
  intro U
  by_cases hxU : x ∈ (U : X.Opens)
  · have heq : (Subtype.val ⁻¹' {x} : Set (U : X.Opens)) = {⟨x, hxU⟩} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
    rw [heq]
    exact isClosed_singleton_of_isMaximal_primeIdealOf U.2 ⟨x, hxU⟩
      (isMaximal_primeIdealOf_of_finite_residueField U.2 ⟨x, hxU⟩ hx)
  · have heq : (Subtype.val ⁻¹' {x} : Set (U : X.Opens)) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => hxU ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
      exact hy ▸ y.2
    rw [heq]
    exact isClosed_empty

/-- If `X` is locally of finite type over `ℤ`, the points with finite residue field are
exactly the closed points. This is a consequence of the general Nullstellensatz. -/
theorem finitePoints_eq_closedPoints (f : X ⟶ Spec (.of (ULift.{u} ℤ)))
    [LocallyOfFiniteType f] :
    X.finitePoints = {x | IsClosed ({x} : Set X)} := by
  ext x
  simp only [Set.mem_setOf_eq]
  refine ⟨fun hx => X.isClosed_singleton_of_mem_finitePoints hx, fun hx => ?_⟩
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have hx' : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx'
    exact TopologicalSpace.Opens.mem_iSup.mp hx'
  haveI hmax : (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal :=
    U.2.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  rw [mem_finitePoints]
  refine (finite_residueField_iff_primeIdealOf U.2 ⟨x, hxU⟩).mpr ?_
  set m : Ideal Γ(X, U.1) := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal with hm
  letI : Field (Γ(X, U.1) ⧸ m) := Ideal.Quotient.field m
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ ⊤ := le_top
  have h1 : (Int.castRingHom (ULift.{u} ℤ)).FiniteType :=
    RingHom.FiniteType.of_surjective _ fun a => ⟨a.down, rfl⟩
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (f.appLE ⊤ (U : X.Opens) e).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) U.2 e
  have h4 : (Ideal.Quotient.mk m).FiniteType :=
    RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
  have hχ := ((h4.comp h3).comp h2).comp h1
  have hft : (algebraMap ℤ (Γ(X, U.1) ⧸ m)).FiniteType := by
    rw [algebraMap_int_eq, ← RingHom.eq_intCast'
      ((((Ideal.Quotient.mk m).comp (f.appLE ⊤ (U : X.Opens) e).hom).comp
        (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} ℤ))).inv.hom).comp
        (Int.castRingHom (ULift.{u} ℤ)))]
    exact hχ
  have hFT : Algebra.FiniteType ℤ (Γ(X, U.1) ⧸ m) := RingHom.finiteType_algebraMap.mp hft
  have hMF : Module.Finite ℤ (Γ(X, U.1) ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing ℤ (Γ(X, U.1) ⧸ m)
  have hKfin : Finite (Γ(X, U.1) ⧸ m) := finite_of_field_of_moduleFinite_int _
  exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField m).surjective

end AlgebraicGeometry.Scheme
