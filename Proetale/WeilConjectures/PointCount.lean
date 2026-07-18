/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.WeilConjectures.ZetaSeries

/-!
# Counting rational points via closed points

For a scheme `X` of finite type over a finite field `k`, given by a structure morphism
`f : X ⟶ Spec k`, this file establishes the point counting formula

`N_n = ∑ deg x`,

the sum running over all points `x` of `X` whose degree `deg x = [κ(x) : k]` divides `n`,
together with the finiteness statements needed to make sense of it: `X` has only finitely
many `K`-rational points for every finite extension `K` of `k`, and only finitely many
points of bounded degree.

The proof is based on the bijection between `K`-rational points of `X` over `k` and pairs
of a point `x : X` together with a `k`-embedding `κ(x) → K` (a relative version of
`AlgebraicGeometry.Scheme.SpecToEquivOfField`), and the Galois theory of finite fields:
a finite field `κ` with `[κ : k] = d` admits exactly `d` distinct `k`-embeddings into
`𝔽_(q ^ n)` if `d ∣ n`, and none otherwise.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.specMap_residueFieldAlgebraMap`: the geometric
  characterization of `Hom.residueFieldAlgebraMap`.
- `AlgebraicGeometry.Scheme.Hom.finite_fieldPoints`: a scheme of finite type over a
  finite field has finitely many points in any finite field extension.
- `AlgebraicGeometry.Scheme.Hom.finite_setOf_degreeOver_le`: a scheme of finite type
  over a finite field has finitely many points of bounded degree.
- `AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum`: the point counting formula.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The embedding of the base field into a residue field is characterized geometrically:
its induced morphism on spectra is the canonical map `Spec κ(x) ⟶ X` followed by the
structure morphism. -/
theorem Hom.specMap_residueFieldAlgebraMap (f : X.Hom (Spec (.of k))) (x : X) :
    Spec.map (CommRingCat.ofHom (f.residueFieldAlgebraMap x)) =
      X.fromSpecResidueField x ≫ f := by
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x,
    ← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj]
  ext a
  rfl

/-- The degree of a point with finite residue field is positive. -/
theorem Hom.degreeOver_ne_zero [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) : f.degreeOver x ≠ 0 := by
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  haveI : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  exact Module.finrank_pos.ne'

/-- The degree of a point with infinite residue field is `0` (by junk convention). -/
theorem Hom.degreeOver_eq_zero [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∉ X.finitePoints) : f.degreeOver x = 0 := by
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  have h : ¬ Module.Finite k (X.residueField x) := fun _ ↦
    hx (X.mem_finitePoints.mpr (Module.finite_of_finite k))
  exact Module.finrank_of_not_finite h

/-- Ring homomorphisms from a finitely generated ring into a finite ring form a finite
type. -/
private lemma finite_ringHom {A B : Type u} [CommRing A] [CommRing B] [Finite B]
    {s : Set A} (hs : s.Finite) (hcl : Subring.closure s = ⊤) : Finite (A →+* B) := by
  haveI := hs.to_subtype
  refine Finite.of_injective (fun φ (x : s) ↦ φ x.1) fun φ ψ h ↦ ?_
  have hle : Subring.closure s ≤ φ.eqLocus ψ :=
    Subring.closure_le.mpr fun x hx ↦ congrFun h ⟨x, hx⟩
  ext a
  exact hle (by rw [hcl]; exact Subring.mem_top a)

/-- An affine scheme of finite type over a finite field admits only finitely many
morphisms from the spectrum of a finite ring. -/
private lemma finite_hom_of_isAffine [Finite k] {U : Scheme.{u}} [IsAffine U]
    (g : U ⟶ Spec (.of k)) [LocallyOfFiniteType g] (K : Type u) [CommRing K] [Finite K] :
    Finite (Spec (.of K) ⟶ U) := by
  have hft : RingHom.FiniteType (g.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹LocallyOfFiniteType g›
  letI : Algebra Γ(Spec (.of k), ⊤) Γ(U, ⊤) := (g.appTop).hom.toAlgebra
  have halg : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(U, ⊤) := hft
  obtain ⟨s, hs⟩ := halg.out
  haveI : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_injective _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective
  have hcl : Subring.closure
      (Set.range (algebraMap Γ(Spec (.of k), ⊤) Γ(U, ⊤)) ∪ ↑s) = ⊤ := by
    have h := Algebra.adjoin_eq_ring_closure (R := Γ(Spec (.of k), ⊤)) (↑s : Set Γ(U, ⊤))
    rw [hs] at h
    rw [← h]
    exact Algebra.top_toSubring
  haveI : Finite (Γ(U, ⊤) →+* K) :=
    finite_ringHom ((Set.finite_range _).union s.finite_toSet) hcl
  refine Finite.of_injective
    (fun h : Spec (.of K) ⟶ U ↦ (Spec.preimage (h ≫ U.isoSpec.hom)).hom) fun h₁ h₂ e ↦ ?_
  have he : h₁ ≫ U.isoSpec.hom = h₂ ≫ U.isoSpec.hom := by
    have h := congrArg Spec.map (CommRingCat.hom_ext e)
    rwa [Spec.map_preimage, Spec.map_preimage] at h
  exact (cancel_mono U.isoSpec.hom).mp he

/-- A scheme of finite type over a finite field admits only finitely many morphisms from
the spectrum of a finite field. -/
private lemma finite_hom [Finite k] (f : X.Hom (Spec (.of k))) [QuasiCompact f]
    [LocallyOfFiniteType f] (K : Type u) [Field K] [Finite K] :
    Finite (Spec (.of K) ⟶ X) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  haveI : Fintype 𝒰.I₀ := inferInstanceAs (Fintype X.affineCover.finiteSubcover.I₀)
  haveI : ∀ i, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (X.affineCover.X _))
  haveI : ∀ i, Finite (Spec (.of K) ⟶ 𝒰.X i) := fun i ↦
    finite_hom_of_isAffine (𝒰.f i ≫ f) K
  have key : ∀ g : Spec (.of K) ⟶ X,
      ∃ p : Σ i, (Spec (.of K) ⟶ 𝒰.X i), p.2 ≫ 𝒰.f p.1 = g := by
    intro g
    have hsub : Set.range ⇑g ⊆ Set.range ⇑(𝒰.f (𝒰.idx (g default))) := by
      rintro - ⟨y, rfl⟩
      rw [Unique.eq_default y]
      exact 𝒰.covers _
    exact ⟨⟨𝒰.idx (g default), IsOpenImmersion.lift (𝒰.f _) g hsub⟩,
      IsOpenImmersion.lift_fac _ _ hsub⟩
  choose F hF using key
  exact Finite.of_injective F fun g₁ g₂ e ↦ by rw [← hF g₁, ← hF g₂, e]

/-- A scheme of finite type over a finite field has only finitely many rational points
in any finite field extension of the base field. -/
theorem Hom.finite_fieldPoints [Finite k] (f : X.Hom (Spec (.of k))) (K : Type u)
    [Field K] [Algebra k K] [Finite K] [QuasiCompact f] [LocallyOfFiniteType f] :
    Finite (f.fieldPoints K) := by
  haveI : Finite (Spec (.of K) ⟶ X) := finite_hom f K
  exact Finite.of_injective (fun g : f.fieldPoints K ↦ g.1) fun g₁ g₂ h ↦ Subtype.ext h

/-- A morphism `Spec K ⟶ X` built from an embedding of a residue field lies over `k` if
and only if the embedding is compatible with the base field embeddings. -/
private lemma comp_eq_iff (f : X.Hom (Spec (.of k))) {K : Type u} [Field K] [Algebra k K]
    (x : X) (φ : X.residueField x ⟶ .of K) :
    (Spec.map φ ≫ X.fromSpecResidueField x) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ↔
      φ.hom.comp (f.residueFieldAlgebraMap x) = algebraMap k K := by
  rw [Category.assoc, ← f.specMap_residueFieldAlgebraMap x, ← Spec.map_comp, Spec.map_inj]
  exact ⟨fun h ↦ congrArg CommRingCat.Hom.hom h, fun h ↦ CommRingCat.hom_ext h⟩

/-- The fiber of the point-embedding correspondence over a point `x`: embeddings of the
residue field of `x` into `K` compatible with the base field embeddings. -/
private def Hom.FieldPointFiber (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] (x : X) : Type u :=
  {φ : X.residueField x ⟶ CommRingCat.of K //
    φ.hom.comp (f.residueFieldAlgebraMap x) = algebraMap k K}

/-- The fibers of the point-embedding correspondence are `k`-algebra homomorphisms of
residue fields. -/
private noncomputable def algHomEquivFieldPointFiber (f : X.Hom (Spec (.of k)))
    (K : Type u) [Field K] [Algebra k K] (x : X) :
    letI := (f.residueFieldAlgebraMap x).toAlgebra
    (X.residueField x →ₐ[k] K) ≃ f.FieldPointFiber K x :=
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  { toFun := fun ψ ↦ ⟨CommRingCat.ofHom ψ.toRingHom, ψ.comp_algebraMap⟩
    invFun := fun φ ↦ { toRingHom := φ.1.hom, commutes' := fun a ↦ RingHom.congr_fun φ.2 a }
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- The rational points of `X` over `k` with values in `K` are pairs of a point of `X`
and a compatible embedding of its residue field into `K`. -/
private noncomputable def fieldPointsEquivSigma (f : X.Hom (Spec (.of k))) (K : Type u) [Field K]
    [Algebra k K] :
    f.fieldPoints K ≃ Σ x : X, f.FieldPointFiber K x :=
  ((SpecToEquivOfField K X).symm.subtypeEquiv fun p ↦
      (comp_eq_iff f p.1 p.2).symm).symm.trans
    { toFun := fun p ↦ ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun q ↦ ⟨⟨q.1, q.2.1⟩, q.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Counting the fibers of the point-embedding correspondence via the Galois theory of
finite fields: over the degree `n` extension of `k`, the fiber over `x` has `deg x`
elements if `deg x ∣ n` and is empty otherwise. -/
private lemma nat_card_fieldPointFiber [Finite k] (f : X.Hom (Spec (.of k))) {n : ℕ}
    (hn : n ≠ 0) (x : X) :
    Nat.card (f.FieldPointFiber (FiniteField.galoisExtension k n) x) =
      if f.degreeOver x ∣ n then f.degreeOver x else 0 := by
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  haveI : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  rw [← Nat.card_congr (algHomEquivFieldPointFiber f (FiniteField.galoisExtension k n) x)]
  by_cases hdvd : f.degreeOver x ∣ n
  · rw [if_pos hdvd]
    have hdvd' : Module.finrank k (X.residueField x) ∣
        Module.finrank k (FiniteField.galoisExtension k n) := by
      rw [FiniteField.finrank_galoisExtension k n hn]
      exact hdvd
    rw [FiniteField.natCard_algHom_of_finrank_dvd hdvd']
    rfl
  · rw [if_neg hdvd]
    haveI : IsEmpty (X.residueField x →ₐ[k] FiniteField.galoisExtension k n) := by
      rw [← not_nonempty_iff, FiniteField.nonempty_algHom_iff_finrank_dvd,
        FiniteField.finrank_galoisExtension k n hn]
      exact hdvd
    exact Nat.card_of_isEmpty

/-- If the degree of `x` divides `n`, the fiber of the point-embedding correspondence
over `x` is nonempty. -/
private lemma nonempty_fieldPointFiber [Finite k] (f : X.Hom (Spec (.of k))) {n : ℕ}
    (hn : n ≠ 0) {x : X} (hdvd : f.degreeOver x ∣ n) :
    Nonempty (f.FieldPointFiber (FiniteField.galoisExtension k n) x) := by
  have h := nat_card_fieldPointFiber f hn x
  rw [if_pos hdvd] at h
  have hpos : 0 < Nat.card (f.FieldPointFiber (FiniteField.galoisExtension k n) x) := by
    rw [h]
    exact Nat.pos_of_ne_zero fun h0 ↦ hn (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  exact (Nat.card_pos_iff.mp hpos).1

/-- A point with nonempty fiber of the point-embedding correspondence over the degree `n`
extension has degree dividing `n`. -/
private lemma degreeOver_dvd_of_fieldPointFiber [Finite k] (f : X.Hom (Spec (.of k)))
    {n : ℕ} (hn : n ≠ 0) {x : X}
    (φ : f.FieldPointFiber (FiniteField.galoisExtension k n) x) :
    f.degreeOver x ∣ n := by
  letI := (f.residueFieldAlgebraMap x).toAlgebra
  haveI : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  have h : Nonempty (X.residueField x →ₐ[k] FiniteField.galoisExtension k n) :=
    ⟨(algHomEquivFieldPointFiber f (FiniteField.galoisExtension k n) x).symm φ⟩
  rw [FiniteField.nonempty_algHom_iff_finrank_dvd,
    FiniteField.finrank_galoisExtension k n hn] at h
  exact h

/-- A point with nonempty fiber of the point-embedding correspondence into a finite field
has finite residue field. -/
private lemma mem_finitePoints_of_fieldPointFiber (f : X.Hom (Spec (.of k))) {K : Type u}
    [Field K] [Algebra k K] [Finite K] {x : X} (φ : f.FieldPointFiber K x) :
    x ∈ X.finitePoints :=
  X.mem_finitePoints.mpr (Finite.of_injective _ φ.1.hom.injective)

/-- The fibers of the point-embedding correspondence over points with finite residue field
are finite. -/
private lemma finite_fieldPointFiber (f : X.Hom (Spec (.of k))) {K : Type u} [Field K]
    [Algebra k K] [Finite K] {x : X} (hx : x ∈ X.finitePoints) :
    Finite (f.FieldPointFiber K x) := by
  haveI : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  exact Finite.of_injective
    (fun φ : f.FieldPointFiber K x ↦ (φ.1.hom : X.residueField x → K))
    fun φ ψ h ↦ Subtype.ext (CommRingCat.hom_ext (DFunLike.coe_injective h))

/-- A scheme of finite type over a finite field has only finitely many points of bounded
degree. -/
theorem Hom.finite_setOf_degreeOver_le [Finite k] (f : X.Hom (Spec (.of k)))
    [QuasiCompact f] [LocallyOfFiniteType f] (n : ℕ) :
    {x : X.finitePoints | f.degreeOver x.1 ≤ n}.Finite := by
  haveI : Finite (FiniteField.galoisExtension k n.factorial) := Module.finite_of_finite k
  haveI := f.finite_fieldPoints (FiniteField.galoisExtension k n.factorial)
  rw [← Set.finite_coe_iff]
  have key : ∀ x : {x : X.finitePoints | f.degreeOver x.1 ≤ n},
      Nonempty (f.FieldPointFiber (FiniteField.galoisExtension k n.factorial) x.1.1) := fun x ↦
    nonempty_fieldPointFiber f n.factorial_ne_zero
      (Nat.dvd_factorial (Nat.pos_of_ne_zero (f.degreeOver_ne_zero x.1.2)) x.2)
  refine Finite.of_injective (β := f.fieldPoints (FiniteField.galoisExtension k n.factorial))
    (fun x ↦ ⟨Spec.map (key x).some.1 ≫ X.fromSpecResidueField x.1.1,
      (comp_eq_iff f x.1.1 (key x).some.1).mpr (key x).some.2⟩) fun x y hxy ↦ ?_
  have h := congrArg
    (fun g : f.fieldPoints (FiniteField.galoisExtension k n.factorial) ↦ g.1 default) hxy
  simp only [Hom.comp_apply, fromSpecResidueField_apply] at h
  exact Subtype.ext (Subtype.ext h)

/-- **The point counting formula**: the number of points of a scheme `X` of finite type
over a finite field `k` which are rational over the degree `n` extension of `k` is
`∑ deg x`, the sum running over the (finitely many) points of `X` whose degree divides
`n`. -/
theorem Hom.pointCount_eq_sum [Finite k] (f : X.Hom (Spec (.of k)))
    [QuasiCompact f] [LocallyOfFiniteType f] {n : ℕ} (hn : n ≠ 0)
    {T : Finset X.finitePoints}
    (hT : ∀ x : X.finitePoints, f.degreeOver x.1 ∣ n → x ∈ T) :
    f.pointCount n = ∑ x ∈ T with f.degreeOver x.1 ∣ n, f.degreeOver x.1 := by
  set K := FiniteField.galoisExtension k n with hK
  haveI : Finite K := Module.finite_of_finite k
  set T' : Finset X.finitePoints := T.filter (fun x ↦ f.degreeOver x.1 ∣ n) with hT'
  have h₁ : ∀ (x : X), f.FieldPointFiber K x → x ∈ X.finitePoints := fun x φ ↦
    mem_finitePoints_of_fieldPointFiber f φ
  have h₂ : ∀ (x : X) (φ : f.FieldPointFiber K x), (⟨x, h₁ x φ⟩ : X.finitePoints) ∈ T' :=
    fun x φ ↦ Finset.mem_filter.mpr
      ⟨hT _ (degreeOver_dvd_of_fieldPointFiber f hn φ),
        degreeOver_dvd_of_fieldPointFiber f hn φ⟩
  let E : (Σ x : X, f.FieldPointFiber K x) ≃ Σ x : T', f.FieldPointFiber K x.1.1 :=
    { toFun := fun p ↦ ⟨⟨⟨p.1, h₁ p.1 p.2⟩, h₂ p.1 p.2⟩, p.2⟩
      invFun := fun q ↦ ⟨q.1.1.1, q.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI : ∀ q : T', Finite (f.FieldPointFiber K q.1.1) := fun q ↦
    finite_fieldPointFiber f q.1.2
  calc f.pointCount n
      = Nat.card (f.fieldPoints K) := rfl
    _ = Nat.card (Σ x : T', f.FieldPointFiber K x.1.1) :=
        Nat.card_congr ((fieldPointsEquivSigma f K).trans E)
    _ = ∑ q : T', Nat.card (f.FieldPointFiber K q.1.1) := Nat.card_sigma
    _ = ∑ q : T', f.degreeOver q.1.1 := Finset.sum_congr rfl fun q _ ↦ by
        rw [nat_card_fieldPointFiber f hn, if_pos (Finset.mem_filter.mp q.2).2]
    _ = ∑ x ∈ T', f.degreeOver x.1 :=
        Finset.sum_coe_sort T' (fun x : X.finitePoints ↦ f.degreeOver x.1)

end AlgebraicGeometry.Scheme
