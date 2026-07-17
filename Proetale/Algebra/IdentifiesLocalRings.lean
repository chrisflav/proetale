/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.RingTheory.LocalRing.RingHom.Basic
import Proetale.Mathlib.RingTheory.Spectrum.Prime.Localization

/-!
# Hom-set bijection for algebras identifying local rings

Let `A` be a commutative ring and let `B`, `C` be `A`-algebras such that `A → B`
identifies local rings (Lean class `Algebra.BijectiveOnStalks`). In this file we
construct the hom-set bijection
$$
  \operatorname{Hom}_{A\text{-alg}}(B, C)
    \;\simeq\; \operatorname{Hom}_{\operatorname{Top}_{\operatorname{Spec} A}}
      (\operatorname{Spec} C, \operatorname{Spec} B)
$$
of Stacks Tag 096L, with `C` an arbitrary `A`-algebra. Specialized to `A → C` also
identifying local rings, this is the fully faithfulness of `B ↦ Spec B` from
`A`-algebras identifying local rings to topological spaces over `Spec A`.

## Main declarations

* `Algebra.BijectiveOnStalks.HomOver A B C`: continuous maps
  `PrimeSpectrum C → PrimeSpectrum B` lying over `PrimeSpectrum A`.
* `Algebra.BijectiveOnStalks.continuousMapOfAlgHom`: the forward direction of the
  bijection, induced by `Spec` functoriality of `PrimeSpectrum.comap`.
* `Algebra.BijectiveOnStalks.continuousMapOfAlgHom_bijective`: the forward direction
  is a bijection.
* `Algebra.BijectiveOnStalks.algHomEquivContinuousMap`: the resulting equivalence of
  hom-sets.
* `Algebra.BijectiveOnStalks.algHomOfContinuousMap`: the inverse direction.

## Proof sketch for the inverse direction

Given a continuous map `φ : Spec C → Spec B` over `Spec A`, we construct a ring map
`B →+* C` as follows. For each prime `p` of `C`, both localized maps
`K : A_{φ(p) ∩ A} →+* B_{φ(p)}` and `L : A_{p ∩ A} →+* C_p` are bijective
(note `φ(p) ∩ A = p ∩ A` because `φ` lies over `Spec A`), so we obtain a per-prime
ring map `B →+* C_p` as the composite `B → B_{φ(p)} ≃ A_{p ∩ A} → C_p`.
The resulting family `p ↦ (image of b)` is a section of the structure sheaf of
`Spec C` over `⊤`: locally around `p` it is the constant fraction `a/t` with
`a, t ∈ A`, where `b = a/t` in `B_{φ(p)}`; continuity of `φ` provides the
neighbourhood. Since `Γ(Spec C, 𝒪) = C`, this glues to an element of `C`,
giving a ring map `B →+* C` which is `A`-linear and induces `φ` on spectra.
-/

universe u v w

open AlgebraicGeometry TopologicalSpace

namespace Algebra.BijectiveOnStalks

variable (A : Type u) (B : Type v) (C : Type w)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Continuous maps `PrimeSpectrum C → PrimeSpectrum B` compatible with the
structure maps to `PrimeSpectrum A`. Equivalently, morphisms in the
overcategory `TopCat / PrimeSpectrum A` from `PrimeSpectrum C` to
`PrimeSpectrum B`. -/
structure HomOver where
  /-- The underlying continuous map. -/
  toContinuousMap : C(PrimeSpectrum C, PrimeSpectrum B)
  /-- Compatibility with the structure maps to `PrimeSpectrum A`. -/
  comp_comap_algebraMap (p : PrimeSpectrum C) :
    PrimeSpectrum.comap (algebraMap A B) (toContinuousMap p) =
      PrimeSpectrum.comap (algebraMap A C) p

namespace HomOver

variable {A B C}

instance : FunLike (HomOver A B C) (PrimeSpectrum C) (PrimeSpectrum B) where
  coe φ := φ.toContinuousMap
  coe_injective' := by
    rintro ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ (rfl : f = g)
    rfl

@[ext]
theorem ext {φ ψ : HomOver A B C} (h : ∀ p, φ p = ψ p) : φ = ψ :=
  DFunLike.ext _ _ h

theorem continuous (φ : HomOver A B C) : Continuous φ :=
  φ.toContinuousMap.continuous

/-- The compatibility over `Spec A`, read off as an identity of prime ideals. -/
theorem comap_asIdeal (φ : HomOver A B C) (p : PrimeSpectrum C) :
    (φ p).asIdeal.comap (algebraMap A B) = p.asIdeal.comap (algebraMap A C) :=
  congrArg PrimeSpectrum.asIdeal (φ.comp_comap_algebraMap p)

end HomOver

variable {A B C}

/-- The continuous map `Spec C → Spec B` over `Spec A` induced by an
`A`-algebra homomorphism `f : B →ₐ[A] C`. This is the forward direction of
the hom-set bijection from Stacks 096L. -/
@[stacks 096L "The forward map on hom sets."]
def continuousMapOfAlgHom (f : B →ₐ[A] C) : HomOver A B C where
  toContinuousMap :=
    { toFun := PrimeSpectrum.comap f.toRingHom
      continuous_toFun := PrimeSpectrum.continuous_comap _ }
  comp_comap_algebraMap p := by
    ext x
    simp only [ContinuousMap.coe_mk, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

@[simp]
lemma continuousMapOfAlgHom_apply (f : B →ₐ[A] C) (p : PrimeSpectrum C) :
    continuousMapOfAlgHom f p = PrimeSpectrum.comap f.toRingHom p :=
  rfl

section Inverse

/-! Note: the construction of the inverse direction only uses that `A → B` identifies
local rings; the hypothesis `Algebra.BijectiveOnStalks A C` is not needed. -/

variable [Algebra.BijectiveOnStalks A B]

/-- (Implementation) For `p : Spec C`, the bijective localized ring map
`A_{φ(p) ∩ A} →+* B_{φ(p)}`, as a ring isomorphism. Here we use that `A → B`
identifies local rings. -/
private noncomputable def stalkEquivAt (φ : HomOver A B C) (p : PrimeSpectrum C) :
    have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    Localization.AtPrime ((φ p).asIdeal.comap (algebraMap A B)) ≃+*
      Localization.AtPrime (φ p).asIdeal :=
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  RingEquiv.ofBijective
    (Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) (φ p).asIdeal
      (algebraMap A B) rfl)
    (Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (φ p).asIdeal)

/-- (Implementation) The per-prime ring homomorphism `B →+* C_p` obtained as the
composite `B → B_{φ(p)} ≃ A_{p ∩ A} → C_p`, where the middle map is the inverse
of `stalkEquivAt` and the last map is the localized map of `A → C` (which is
bijective, but we do not need this here). -/
private noncomputable def localRingHomAt (φ : HomOver A B C) (p : PrimeSpectrum C) :
    B →+* Localization.AtPrime p.asIdeal :=
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  ((Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
      (algebraMap A C) (φ.comap_asIdeal p)).comp
    (stalkEquivAt φ p).symm.toRingHom).comp
    (algebraMap B (Localization.AtPrime (φ p).asIdeal))

/-- (Implementation) Characterization of `localRingHomAt`: if `z : A_{p ∩ A}` maps
to `b/1` in `B_{φ(p)}`, then `localRingHomAt φ p b` is the image of `z` in `C_p`. -/
private theorem localRingHomAt_eq (φ : HomOver A B C) (p : PrimeSpectrum C) (b : B)
    {hP : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime}
    (z : Localization.AtPrime ((φ p).asIdeal.comap (algebraMap A B)))
    (hz : Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) (φ p).asIdeal
        (algebraMap A B) rfl z =
      algebraMap B (Localization.AtPrime (φ p).asIdeal) b) :
    localRingHomAt φ p b =
      Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
        (algebraMap A C) (φ.comap_asIdeal p) z := by
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  have hsymm : (stalkEquivAt φ p).symm
      (algebraMap B (Localization.AtPrime (φ p).asIdeal) b) = z :=
    (RingEquiv.symm_apply_eq _).mpr hz.symm
  simp only [localRingHomAt, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hsymm]

/-- (Implementation) `localRingHomAt` is compatible with the algebra maps from `A`. -/
private theorem localRingHomAt_algebraMap (φ : HomOver A B C) (p : PrimeSpectrum C)
    (a : A) :
    localRingHomAt φ p (algebraMap A B a) =
      algebraMap C (Localization.AtPrime p.asIdeal) (algebraMap A C a) := by
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  rw [localRingHomAt_eq φ p _ (algebraMap A _ a) (by rw [Localization.localRingHom_to_map]),
    Localization.localRingHom_to_map]

/-- (Implementation) The family `p ↦ localRingHomAt φ p b` is a section of the
structure sheaf of `Spec C`: it is locally a fraction (with numerator and
denominator in the image of `A`). This is where continuity of `φ` is used. -/
private theorem isLocallyFraction_localRingHomAt (φ : HomOver A B C) (b : B) :
    (StructureSheaf.isLocallyFraction C C).pred
      (fun p : (⊤ : Opens (PrimeSpectrum.Top C)) ↦
        (localRingHomAt φ p.1 b : StructureSheaf.Localizations C p.1)) := by
  rintro ⟨p, -⟩
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  -- Write the element of `A_{p ∩ A}` corresponding to `b/1 ∈ B_{φ(p)}` as a
  -- fraction `a/t` with `a, t : A`, `t ∉ φ(p) ∩ A`.
  obtain ⟨a, t, hat⟩ := IsLocalization.exists_mk'_eq
    ((φ p).asIdeal.comap (algebraMap A B)).primeCompl
    ((stalkEquivAt φ p).symm (algebraMap B (Localization.AtPrime (φ p).asIdeal) b))
  -- Then `b/1 = aᴮ/tᴮ` in `B_{φ(p)}`, i.e. `u * (b * tᴮ - aᴮ) = 0` for some
  -- `u ∉ φ(p)`.
  have hKmk : Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B))
      (φ p).asIdeal (algebraMap A B) rfl
        (IsLocalization.mk' _ a t) =
      algebraMap B (Localization.AtPrime (φ p).asIdeal) b := by
    rw [hat]
    exact (stalkEquivAt φ p).apply_symm_apply _
  rw [Localization.localRingHom_mk'] at hKmk
  rw [IsLocalization.mk'_eq_iff_eq_mul] at hKmk
  have hzero : algebraMap B (Localization.AtPrime (φ p).asIdeal)
      (b * algebraMap A B t - algebraMap A B a) = 0 := by
    rw [map_sub, sub_eq_zero, map_mul, ← hKmk]
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff (φ p).asIdeal.primeCompl _ _).mp hzero
  -- The open neighbourhood of `φ(p)` in `Spec B` on which the fraction
  -- representation is valid, and its preimage in `Spec C`.
  set g : B := u.1 * algebraMap A B t
  have htB : algebraMap A B t.1 ∈ (φ p).asIdeal.primeCompl := t.2
  have hφp : φ p ∈ PrimeSpectrum.basicOpen g :=
    (PrimeSpectrum.mem_basicOpen _ _).mpr ((φ p).asIdeal.primeCompl.mul_mem u.2 htB)
  let V : Opens (PrimeSpectrum.Top C) :=
    ⟨φ ⁻¹' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)),
      (PrimeSpectrum.basicOpen g).2.preimage φ.continuous⟩
  refine ⟨V, hφp, CategoryTheory.homOfLE le_top, algebraMap A C a, algebraMap A C t,
    fun q ↦ ?_⟩
  -- Now check the fraction representation at each `q ∈ V`.
  obtain ⟨q, hq⟩ := q
  have : ((φ q).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  have hgq : g ∉ (φ q).asIdeal := hq
  have huq : u.1 ∉ (φ q).asIdeal := fun h ↦ hgq (Ideal.mul_mem_right _ _ h)
  have htq : algebraMap A B t ∉ (φ q).asIdeal := fun h ↦ hgq (Ideal.mul_mem_left _ _ h)
  have htqA : t.1 ∈ ((φ q).asIdeal.comap (algebraMap A B)).primeCompl := htq
  have htC : algebraMap A C t ∉ q.asIdeal := by
    intro h
    apply htq
    have ht' : t.1 ∈ q.asIdeal.comap (algebraMap A C) := h
    rw [← φ.comap_asIdeal q] at ht'
    exact ht'
  refine ⟨htC, ?_⟩
  -- `b/1 = aᴮ/tᴮ` holds in `B_{φ(q)}` as well, by the same witness `u`.
  have hKmk' : Localization.localRingHom ((φ q).asIdeal.comap (algebraMap A B))
      (φ q).asIdeal (algebraMap A B) rfl
        (IsLocalization.mk' _ a ⟨t.1, htqA⟩) =
      algebraMap B (Localization.AtPrime (φ q).asIdeal) b := by
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq_mul, eq_comm, ← map_mul,
      ← sub_eq_zero, ← map_sub]
    exact (IsLocalization.map_eq_zero_iff (φ q).asIdeal.primeCompl _ _).mpr
      ⟨⟨u.1, huq⟩, hu⟩
  change localRingHomAt φ q b = LocalizedModule.mk (algebraMap A C a) ⟨algebraMap A C t.1, htC⟩
  rw [localRingHomAt_eq φ q b _ hKmk', Localization.localRingHom_mk']
  change IsLocalization.mk' (Localization.AtPrime q.asIdeal) _ _ =
    Localization.mk (algebraMap A C a) ⟨algebraMap A C t.1, htC⟩
  rw [Localization.mk_eq_mk']

/-- (Implementation) The ring homomorphism from `B` to the global sections of the
structure sheaf of `Spec C`, given pointwise by `localRingHomAt`. -/
private noncomputable def toSections (φ : HomOver A B C) :
    B →+* (structureSheafInType C C).1.obj
      (Opposite.op (⊤ : Opens (PrimeSpectrum.Top C))) where
  toFun b := ⟨fun p ↦ localRingHomAt φ p.1 b, isLocallyFraction_localRingHomAt φ b⟩
  map_one' := Subtype.ext <| funext fun p ↦ map_one (localRingHomAt φ p.1)
  map_mul' x y := Subtype.ext <| funext fun p ↦ map_mul (localRingHomAt φ p.1) x y
  map_zero' := Subtype.ext <| funext fun p ↦ map_zero (localRingHomAt φ p.1)
  map_add' x y := Subtype.ext <| funext fun p ↦ map_add (localRingHomAt φ p.1) x y

/-- (Implementation) The ring homomorphism `B →+* C` induced by a continuous map
`Spec C → Spec B` over `Spec A`: glue the per-prime maps `localRingHomAt` via
`Γ(Spec C, 𝒪) = C`. -/
private noncomputable def ringHomOfHomOver (φ : HomOver A B C) : B →+* C :=
  ((RingEquiv.ofBijective _
      (StructureSheaf.algebraMap_obj_top_bijective (R := C))).symm).toRingHom.comp
    (toSections φ)

/-- (Implementation) The defining property of `ringHomOfHomOver`: its localization
at each prime `p` of `C` is `localRingHomAt φ p`. -/
private theorem algebraMap_ringHomOfHomOver (φ : HomOver A B C) (b : B)
    (p : PrimeSpectrum C) :
    algebraMap C (Localization.AtPrime p.asIdeal) (ringHomOfHomOver φ b) =
      localRingHomAt φ p b := by
  have h : algebraMap C ((structureSheafInType C C).1.obj
      (Opposite.op (⊤ : Opens (PrimeSpectrum.Top C)))) (ringHomOfHomOver φ b) =
      toSections φ b :=
    (RingEquiv.ofBijective _
      (StructureSheaf.algebraMap_obj_top_bijective (R := C))).apply_symm_apply _
  exact congrFun (congrArg Subtype.val h) ⟨p, trivial⟩

/-- (Implementation) `ringHomOfHomOver` is `A`-linear. -/
private theorem ringHomOfHomOver_algebraMap (φ : HomOver A B C) (a : A) :
    ringHomOfHomOver φ (algebraMap A B a) = algebraMap A C a :=
  PrimeSpectrum.eq_of_localizationAtPrime_eq fun p ↦ by
    rw [algebraMap_ringHomOfHomOver, localRingHomAt_algebraMap]

/-- (Implementation) `ringHomOfHomOver` induces `φ` on prime spectra. -/
private theorem comap_ringHomOfHomOver (φ : HomOver A B C) (p : PrimeSpectrum C) :
    PrimeSpectrum.comap (ringHomOfHomOver φ) p = φ p := by
  have : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
  ext b
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  set K := Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) (φ p).asIdeal
    (algebraMap A B) rfl
  set L := Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
    (algebraMap A C) (φ.comap_asIdeal p)
  have : IsLocalHom K := Localization.isLocalHom_localRingHom _ _ _ rfl
  have : IsLocalHom L := Localization.isLocalHom_localRingHom _ _ _ _
  set z := (stalkEquivAt φ p).symm (algebraMap B (Localization.AtPrime (φ p).asIdeal) b)
  have hKz : K z = algebraMap B (Localization.AtPrime (φ p).asIdeal) b :=
    (stalkEquivAt φ p).apply_symm_apply _
  have hLz : localRingHomAt φ p b = L z := localRingHomAt_eq φ p b z hKz
  calc ringHomOfHomOver φ b ∈ p.asIdeal
      ↔ algebraMap C (Localization.AtPrime p.asIdeal) (ringHomOfHomOver φ b) ∈
          IsLocalRing.maximalIdeal _ :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal _).symm
    _ ↔ L z ∈ IsLocalRing.maximalIdeal _ := by
        rw [algebraMap_ringHomOfHomOver, hLz]
    _ ↔ z ∈ IsLocalRing.maximalIdeal _ := IsLocalRing.map_mem_maximalIdeal_iff L z
    _ ↔ K z ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.map_mem_maximalIdeal_iff K z).symm
    _ ↔ b ∈ (φ p).asIdeal := by
        rw [hKz]
        exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ (φ p).asIdeal _

end Inverse

variable (A B C)

/-- **Stacks 096L, fully faithfulness.** When `A → B` identifies local rings, the map
sending an `A`-algebra homomorphism `B →ₐ[A] C` to the induced continuous map
`Spec C → Spec B` over `Spec A` is a bijection. Here `C` is an arbitrary `A`-algebra;
specializing to `A → C` also identifying local rings recovers the fully faithfulness
of `B ↦ Spec B` on the category of `A`-algebras identifying local rings. -/
@[stacks 096L]
theorem continuousMapOfAlgHom_bijective [Algebra.BijectiveOnStalks A B] :
    Function.Bijective (continuousMapOfAlgHom : (B →ₐ[A] C) → HomOver A B C) := by
  constructor
  · -- Injectivity: an `A`-algebra map `B → C` is determined by its localizations,
    -- which factor through the bijective maps `A_{p ∩ A} → B_{φ(p)}`.
    intro f₁ f₂ heq
    have hcomap (p : PrimeSpectrum C) :
        p.asIdeal.comap f₁.toRingHom = p.asIdeal.comap f₂.toRingHom :=
      congrArg PrimeSpectrum.asIdeal (DFunLike.congr_fun heq p)
    ext b
    refine PrimeSpectrum.eq_of_localizationAtPrime_eq fun p ↦ ?_
    have : (p.asIdeal.comap f₁.toRingHom).IsPrime := Ideal.IsPrime.comap _
    set q := p.asIdeal.comap f₁.toRingHom with hq
    have : (q.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    set K := Localization.localRingHom (q.comap (algebraMap A B)) q (algebraMap A B) rfl
      with hK
    have hKbij : Function.Bijective K :=
      Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) q
    set M₁ := Localization.localRingHom q p.asIdeal f₁.toRingHom rfl with hM₁
    set M₂ := Localization.localRingHom q p.asIdeal f₂.toRingHom (hcomap p) with hM₂
    have hMcomp : M₁.comp K = M₂.comp K := by
      refine IsLocalization.ringHom_ext (q.comap (algebraMap A B)).primeCompl
        (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.coe_comp, Function.comp_apply, hK, hM₁, hM₂,
        Localization.localRingHom_to_map]
      have hc₁ : f₁.toRingHom (algebraMap A B a) = algebraMap A C a := f₁.commutes a
      have hc₂ : f₂.toRingHom (algebraMap A B a) = algebraMap A C a := f₂.commutes a
      rw [hc₁, hc₂]
    have hM : M₁ = M₂ := RingHom.ext fun x ↦ by
      obtain ⟨y, rfl⟩ := hKbij.surjective x
      exact RingHom.congr_fun hMcomp y
    change algebraMap C (Localization.AtPrime p.asIdeal) (f₁.toRingHom b) =
      algebraMap C (Localization.AtPrime p.asIdeal) (f₂.toRingHom b)
    rw [← Localization.localRingHom_to_map q p.asIdeal f₁.toRingHom rfl b,
      ← Localization.localRingHom_to_map q p.asIdeal f₂.toRingHom (hcomap p) b,
      ← hM₁, ← hM₂, hM]
  · -- Surjectivity: glue the per-prime maps via the structure sheaf of `Spec C`.
    intro φ
    refine ⟨{ ringHomOfHomOver φ with commutes' := ringHomOfHomOver_algebraMap φ }, ?_⟩
    exact HomOver.ext fun p ↦ comap_ringHomOfHomOver φ p

/-- The hom-set bijection `(B →ₐ[A] C) ≃ HomOver A B C` when `A → B` identifies local
rings, with `C` an arbitrary `A`-algebra. This formalizes Stacks 096L
(`thm:identifies-local-ring-to-top-fully-faithful` and
`def:identifies-local-ring-hom-set-bijection` in the blueprint). -/
@[stacks 096L]
noncomputable def algHomEquivContinuousMap [Algebra.BijectiveOnStalks A B] :
    (B →ₐ[A] C) ≃ HomOver A B C :=
  Equiv.ofBijective continuousMapOfAlgHom (continuousMapOfAlgHom_bijective A B C)

/-- The `A`-algebra homomorphism `B →ₐ[A] C` induced by a continuous map
`Spec C → Spec B` over `Spec A`, when `A → B` identifies local rings. This is the
inverse direction of the hom-set bijection from Stacks 096L. -/
noncomputable def algHomOfContinuousMap [Algebra.BijectiveOnStalks A B]
    (φ : HomOver A B C) : B →ₐ[A] C :=
  (algHomEquivContinuousMap A B C).symm φ

@[simp]
lemma continuousMapOfAlgHom_algHomOfContinuousMap [Algebra.BijectiveOnStalks A B]
    (φ : HomOver A B C) :
    continuousMapOfAlgHom (algHomOfContinuousMap A B C φ) = φ :=
  (algHomEquivContinuousMap A B C).apply_symm_apply φ

@[simp]
lemma algHomOfContinuousMap_continuousMapOfAlgHom [Algebra.BijectiveOnStalks A B]
    (f : B →ₐ[A] C) :
    algHomOfContinuousMap A B C (continuousMapOfAlgHom f) = f :=
  (algHomEquivContinuousMap A B C).symm_apply_apply f

end Algebra.BijectiveOnStalks
