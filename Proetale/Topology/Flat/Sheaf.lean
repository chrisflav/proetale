/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers

import Proetale.Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Proetale.Topology.Flat.QuasiCompactTopology

/-!
# The fpqc topology is subcanonical

In this file we show that the fqpc topology of a scheme is subcanonical. This implies that
all coarser topologies, e.g., the (pro)étale topology, are subcanonical.
-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}}

open Scheme

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

open Opposite

variable {P}

abbrev fpqcPrecoverage : Precoverage Scheme.{u} := propqcPrecoverage @Flat

/-- The fpqc-topology on the category of schemes is the Grothendieck topology associated
to the pretopology given by fpqc-covers. -/
abbrev fpqcTopology : GrothendieckTopology Scheme.{u} := fpqcPrecoverage.toGrothendieck

lemma isSheaf_fpqcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf fpqcTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (_ : f.hom.Flat) (_ : Surjective (Spec.map f)),
          Presieve.IsSheafFor F (Presieve.singleton (Spec.map f)) := by
  rw [isSheaf_propqcTopology_iff]
  congr!
  exact HasRingHomProperty.Spec_iff

@[simp]
lemma Scheme.Hom.generate_singleton_mem_fpqcTopology_of_locallyOfFinitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    Sieve.generate (Presieve.singleton f) ∈ fpqcTopology Y := by
  have : QuasiCompactCover (cover f ‹Flat f›).toPreZeroHypercover := by
    refine ⟨fun {U} hU ↦ .of_isOpenMap ?_ ?_ ?_ ?_ ?_⟩
    · intro
      exact f.continuous
    · intro
      exact f.isOpenMap
    · intro x hx
      use ⟨⟩
      exact f.surjective x
    · exact U.2
    · exact hU.isCompact
  rw [← Presieve.ofArrows_pUnit.{u}]
  exact (f.cover _).generate_ofArrows_mem_propqcTopology

-- Amitsur exact sequence: for faithfully flat f : R → S, the equalizer of
-- includeLeft, includeRight : S → S ⊗_R S in CommRingCat is (isomorphic to) R.
-- This is the key algebraic input for proving that flat surjective morphisms of
-- affine schemes are effective epimorphisms.

section AmitsurExact

open scoped TensorProduct

-- The Amitsur fork: R is the equalizer of pushout.inl and pushout.inr
-- in CommRingCat, when the pushout is of f with itself.
private noncomputable def amitsurFork {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Fork (pushout.inl f f) (pushout.inr f f) :=
  Fork.ofι f (by simp [pushout.condition])

-- The Amitsur exact sequence for faithfully flat R → S:
-- the sequence R → S → S ⊗_R S (with d(s) = s ⊗ 1 - 1 ⊗ s) is exact at S.
-- Proof: tensor with S, verify split exactness via the multiplication map, reflect.
set_option maxHeartbeats 800000 in
private lemma amitsur_exact_tensor {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] :
    Function.Exact (Algebra.linearMap R S)
      ((Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := S) (B := S) :
         S →ₐ[R] S ⊗[R] S).toLinearMap -
       (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S) :
         S →ₐ[R] S ⊗[R] S).toLinearMap) := by
  set iL : S →ₐ[R] S ⊗[R] S :=
    Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := S) (B := S)
  set iR : S →ₐ[R] S ⊗[R] S := Algebra.TensorProduct.includeRight
  set f := Algebra.linearMap R S
  set d : S →ₗ[R] S ⊗[R] S := iL.toLinearMap - iR.toLinearMap
  -- Use faithful flatness to reflect exactness from the tensored sequence.
  apply Module.FaithfullyFlat.lTensor_reflects_exact R S
  rw [LinearMap.exact_iff]
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · -- ker(lTensor S d) ⊆ range(lTensor S f): the key direction
    -- Uses the homotopy identity: x = includeLeft(lmul'(x)) when (lTensor S d)(x) = 0.
    intro hx
    suffices key : ∀ (y : S ⊗[R] S), d.lTensor S y = 0 →
        y = (Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) y) : S ⊗[R] S) by
      have hkey := key x hx
      refine ⟨(Algebra.TensorProduct.lmul' (R := R) x) ⊗ₜ[R] (1 : R), ?_⟩
      simp only [f, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
      exact hkey.symm
    -- Define the contraction map σ : S ⊗[R] (S ⊗[R] S) → S ⊗[R] S
    -- by σ(a ⊗ (b ⊗ c)) = (a*b) ⊗ c.
    intro y hy
    let σ : S ⊗[R] (S ⊗[R] S) →ₗ[R] S ⊗[R] S :=
      (Algebra.TensorProduct.lmul' (R := R) (S := S)).toLinearMap.rTensor S ∘ₗ
        (TensorProduct.assoc R S S S).symm.toLinearMap
    -- Key identity: for ALL z, z - includeLeft(lmul'(z)) = -σ((lTensor S d)(z)).
    suffices hident : ∀ (z : S ⊗[R] S),
        z - (Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) z) : S ⊗[R] S) =
        -σ (d.lTensor S z) by
      have := hident y
      rw [hy, map_zero, neg_zero, sub_eq_zero] at this
      exact this
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [map_zero, sub_self]
    | add x y hx hy =>
      simp only [map_add, map_neg]
      -- (x + y) - (iL(m x) + iL(m y)) = -(σ(d' x) + σ(d' y))
      -- rewrite as (x - iL(m x)) + (y - iL(m y)) = -σ(d' x) + -σ(d' y)
      have : x + y - (Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) x) +
        Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) y) : S ⊗[R] S) =
        (x - Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) x)) +
        (y - Algebra.TensorProduct.includeLeft (S := R)
          (Algebra.TensorProduct.lmul' (R := R) y)) := by abel
      rw [this, hx, hy]
      abel
    | tmul a b =>
      change a ⊗ₜ[R] b - (Algebra.TensorProduct.includeLeft (S := R)
        (Algebra.TensorProduct.lmul' (R := R) (a ⊗ₜ[R] b)) : S ⊗[R] S) =
        -σ (d.lTensor S (a ⊗ₜ[R] b))
      simp only [Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.includeLeft_apply]
      -- LHS: a ⊗ b - (a*b) ⊗ 1.  RHS: -σ(lTensor S d (a ⊗ b))
      have hd : d.lTensor S (a ⊗ₜ[R] b) =
        a ⊗ₜ[R] (b ⊗ₜ[R] (1 : S)) - a ⊗ₜ[R] ((1 : S) ⊗ₜ[R] b) := by
        show a ⊗ₜ[R] d b = _
        simp only [d, iL, iR, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          TensorProduct.tmul_sub]
      rw [hd]
      simp only [σ, LinearMap.comp_apply, map_sub, LinearEquiv.coe_coe,
        TensorProduct.assoc_symm_tmul a b (1 : S),
        TensorProduct.assoc_symm_tmul a (1 : S) b,
        LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lmul'_apply_tmul,
        mul_one, one_mul]
      abel
  · -- range(lTensor S f) ⊆ ker(lTensor S d)
    rintro ⟨y, rfl⟩
    show d.lTensor S (f.lTensor S y) = 0
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a r =>
      simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, d,
        LinearMap.sub_apply, AlgHom.toLinearMap_apply]
      -- Goal: a ⊗ (iL(algebraMap R S r) - iR(algebraMap R S r)) = 0
      -- iL(algebraMap R S r) = algebraMap R S r ⊗ 1 = algebraMap R (S ⊗ S) r
      -- iR(algebraMap R S r) = 1 ⊗ algebraMap R S r = algebraMap R (S ⊗ S) r
      have : iL (f r) = iR (f r) := by
        show iL (algebraMap R S r) = iR (algebraMap R S r)
        simp only [iL, iR, AlgHom.commutes]
      rw [this, sub_self, TensorProduct.tmul_zero]
    | add x y hx hy => simp [hx, hy]

-- The Amitsur exact sequence implies range(f) = eqLocus(pushout.inl, pushout.inr).
private lemma amitsur_range_eq_eqLocus {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hff : f.hom.FaithfullyFlat) :
    Set.range f.hom = RingHom.eqLocus (pushout.inl f f).hom (pushout.inr f f).hom := by
  algebraize [f.hom]
  let hp := CommRingCat.isPushout_tensorProduct R S S
  let e := hp.isoPushout
  have hinl : ∀ s : S, (pushout.inl f f).hom s =
      e.hom.hom (Algebra.TensorProduct.includeLeftRingHom (R := R) s) := fun s =>
    (ConcreteCategory.congr_hom hp.inl_isoPushout_hom s).symm
  have hinr : ∀ s : S, (pushout.inr f f).hom s =
      e.hom.hom ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom s) :=
    fun s => (ConcreteCategory.congr_hom hp.inr_isoPushout_hom s).symm
  have he_inj : Function.Injective e.hom.hom :=
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp (Iso.isIso_hom e)).1
  ext s
  simp only [Set.mem_range, RingHom.mem_eqLocus]
  constructor
  · rintro ⟨r, rfl⟩
    show (pushout.inl f f).hom (f.hom r) = (pushout.inr f f).hom (f.hom r)
    exact ConcreteCategory.congr_hom (pushout.condition (f := f) (g := f)) r
  · intro heq
    have hincl : (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := S)) s =
        (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom s :=
      he_inj (by rw [← hinl, ← hinr]; exact heq)
    have hexact := @amitsur_exact_tensor R S _ _ _ ‹Module.FaithfullyFlat R S›
    rw [LinearMap.exact_iff] at hexact
    have hker : s ∈ LinearMap.ker
        ((Algebra.TensorProduct.includeLeft (S := R) (R := R) (A := S) (B := S) :
           S →ₐ[R] S ⊗[R] S).toLinearMap -
          (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toLinearMap) := by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]
      exact hincl
    rw [hexact] at hker
    obtain ⟨r, hr⟩ := hker
    exact ⟨r, hr⟩

-- Key: the Amitsur fork is a limit for faithfully flat ring maps.
private noncomputable def amitsurForkIsLimit {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hff : f.hom.FaithfullyFlat) :
    IsLimit (amitsurFork f) := by
  have hfinj : Function.Injective f.hom := hff.injective
  let eqFork := CommRingCat.equalizerFork (pushout.inl f f) (pushout.inr f f)
  let eqIsLimit := CommRingCat.equalizerForkIsLimit (pushout.inl f f) (pushout.inr f f)
  have hfeq : ∀ r : R, (pushout.inl f f).hom (f.hom r) = (pushout.inr f f).hom (f.hom r) := by
    intro r
    exact ConcreteCategory.congr_hom (pushout.condition (f := f) (g := f)) r
  let fwd : R →+* RingHom.eqLocus (pushout.inl f f).hom (pushout.inr f f).hom :=
    f.hom.codRestrict _ hfeq
  have hfwd_bij : Function.Bijective fwd := by
    constructor
    · intro a b hab
      apply hfinj
      exact Subtype.ext_iff.mp hab
    · intro ⟨s, hs⟩
      have : s ∈ Set.range f.hom := by
        rw [amitsur_range_eq_eqLocus f hff]; exact hs
      obtain ⟨r, hr⟩ := this
      exact ⟨r, Subtype.ext hr⟩
  let re := RingEquiv.ofBijective fwd hfwd_bij
  let e : R ≅ eqFork.pt := re.toCommRingCatIso
  have hcompat : e.hom ≫ eqFork.ι = f := by
    apply CommRingCat.hom_ext
    ext r
    show ((RingHom.eqLocus (pushout.inl f f).hom (pushout.inr f f).hom).subtype)
      (fwd r) = f.hom r
    simp [fwd, RingHom.codRestrict]
  -- The amitsurFork is isomorphic to eqFork via e, hence also a limit
  exact IsLimit.ofIsoLimit eqIsLimit (Fork.ext e hcompat).symm

end AmitsurExact

-- Helper: For faithfully flat f : R → S, the fork
--   Hom(Spec R, Y) → Hom(Spec S, Y) ⇉ Hom(Spec(S ⊗_R S), Y)
-- is a limit in Type for any affine Y = Spec T.
-- This follows from amitsurForkIsLimit by applying the representable functor Hom(T, -).
private lemma isSheafFor_yoneda_affine {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hff : f.hom.FaithfullyFlat) (T : CommRingCat.{u}) :
    Presieve.IsSheafFor (yoneda.obj (Spec T)) (Presieve.singleton (Spec.map f)) := by
  haveI : Flat (Spec.map f) := ((flat_and_surjective_SpecMap_iff f).mpr hff).1
  haveI : Surjective (Spec.map f) := ((flat_and_surjective_SpecMap_iff f).mpr hff).2
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective x
  -- Descent condition: pushout.inl and pushout.inr give the same after composing with x
  have hcond : Spec.map (pushout.inl f f) ≫ x = Spec.map (pushout.inr f f) ≫ x := by
    apply hx
    show Spec.map (pushout.inl f f) ≫ Spec.map f = Spec.map (pushout.inr f f) ≫ Spec.map f
    simp only [← Spec.map_comp, pushout.condition]
  -- Transfer to CommRingCat: φ equalizes pushout.inl and pushout.inr
  have hcond' : φ ≫ pushout.inl f f = φ ≫ pushout.inr f f := by
    apply Spec.map_injective
    simp only [Spec.map_comp, hφ]
    exact hcond
  -- Amitsur fork gives factorization
  obtain ⟨ψ, hψ⟩ := Fork.IsLimit.lift' (amitsurForkIsLimit f hff) φ hcond'
  -- hψ : ψ ≫ Fork.ι (amitsurFork f) = φ, i.e., ψ ≫ f = φ
  have hψ' : ψ ≫ f = φ := by simpa [amitsurFork, Fork.ofι] using hψ
  have hfact : Spec.map f ≫ Spec.map ψ = x := by
    calc Spec.map f ≫ Spec.map ψ
        = Spec.map (ψ ≫ f) := (Spec.map_comp ψ f).symm
      _ = Spec.map φ := by rw [hψ']
      _ = x := hφ
  refine ⟨Spec.map ψ, hfact, fun m hm ↦ ?_⟩
  -- hm : (yoneda.obj (Spec T)).map (Spec.map f).op m = x
  -- which is definitionally Spec.map f ≫ m = x
  have hm' : Spec.map f ≫ m = x := hm
  have hepi : Epi (Spec.map f) := Flat.epi_of_flat_of_surjective _
  exact hepi.left_cancellation _ _ (by rw [hm', hfact])

-- Helper: For a flat surjective morphism g between affine schemes and an affine test object,
-- the singleton sheaf condition holds. Reduces to isSheafFor_yoneda_affine via isoSpec.
set_option maxHeartbeats 800000 in
private lemma isSheafFor_yoneda_of_isAffine {X Z : Scheme.{u}}
    [IsAffine X] [IsAffine Z] (g : X ⟶ Z) [Flat g] [Surjective g]
    (T : CommRingCat.{u}) :
    Presieve.IsSheafFor (yoneda.obj (Spec T)) (Presieve.singleton g) := by
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  -- Convert hx from yoneda form to composition form
  replace hx : ∀ ⦃W : Scheme.{u}⦄ (p₁ p₂ : W ⟶ X),
      p₁ ≫ g = p₂ ≫ g → p₁ ≫ x = p₂ ≫ x := by
    intro W p₁ p₂ h; have := hx p₁ p₂ h; dsimp [yoneda] at this; exact this
  have hff : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (f := g)).mp ⟨‹_›, ‹_›⟩
  have hsheaf := isSheafFor_yoneda_affine g.appTop hff T
  rw [Presieve.isSheafFor_singleton] at hsheaf
  -- Transport: x' = X.isoSpec.inv ≫ x : Spec(Γ(X)) → Spec T
  set x' := X.isoSpec.inv ≫ x with hx'_def
  have hx' : ∀ ⦃W : Scheme.{u}⦄ (p₁ p₂ : W ⟶ Spec Γ(X, ⊤)),
      p₁ ≫ Spec.map g.appTop = p₂ ≫ Spec.map g.appTop →
      (yoneda.obj (Spec T)).map p₁.op x' = (yoneda.obj (Spec T)).map p₂.op x' := by
    intro W p₁ p₂ hp
    show p₁ ≫ X.isoSpec.inv ≫ x = p₂ ≫ X.isoSpec.inv ≫ x
    rw [← Category.assoc, ← Category.assoc]
    apply hx
    rw [Category.assoc, Category.assoc, ← Scheme.isoSpec_inv_naturality,
      ← Category.assoc, ← Category.assoc, hp]
  obtain ⟨d', hd', _⟩ := @hsheaf x' @hx'
  -- hd' : Spec.map g.appTop ≫ d' = x'
  change Spec.map g.appTop ≫ d' = x' at hd'
  refine ⟨Z.isoSpec.hom ≫ d', ?_, ?_⟩
  · -- g ≫ Z.isoSpec.hom ≫ d' = x
    show g ≫ Z.isoSpec.hom ≫ d' = x
    rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, hd',
      hx'_def, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · -- uniqueness from Epi
    intro y
    show g ≫ y = x → y = Z.isoSpec.hom ≫ d'
    intro hy
    have hepi : Epi g := Flat.epi_of_flat_of_surjective _
    exact hepi.left_cancellation _ _ (by
      rw [hy, ← Category.assoc, ← Scheme.isoSpec_hom_naturality, Category.assoc, hd',
        hx'_def, ← Category.assoc, Iso.hom_inv_id, Category.id_comp])

-- Fiber constancy: x is constant on fibers of Spec.map f.
-- Given the cocycle condition, if f(a) = f(b) then x(a) = x(b).
private lemma fiber_constant {R S : CommRingCat.{u}} {f : R ⟶ S} {Y : Scheme.{u}}
    {x : Spec S ⟶ Y}
    (hx : ∀ ⦃Z : Scheme.{u}⦄ (p₁ p₂ : Z ⟶ Spec S),
      p₁ ≫ Spec.map f = p₂ ≫ Spec.map f → p₁ ≫ x = p₂ ≫ x)
    (a b : Spec S) (hab : (Spec.map f) a = (Spec.map f) b) :
    x a = x b := by
  obtain ⟨c, hc1, hc2⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  have key := hx (pullback.fst (Spec.map f) (Spec.map f))
    (pullback.snd (Spec.map f) (Spec.map f)) pullback.condition
  have ha : (pullback.fst (Spec.map f) (Spec.map f) ≫ x) c = x a := by
    simp [Scheme.Hom.comp_apply, hc1]
  have hb : (pullback.snd (Spec.map f) (Spec.map f) ≫ x) c = x b := by
    simp [Scheme.Hom.comp_apply, hc2]
  rw [key] at ha; exact ha.symm.trans hb

-- For a faithfully flat ring map f : R → S, showing IsSheafFor (yoneda.obj Y) for
-- the singleton presieve {Spec.map f} and any scheme Y.
-- Equivalently, Spec.map f is an effective epimorphism.
-- The proof uses the affine case combined with Zariski gluing.
-- Stacks 023Q: faithfully flat descent for morphisms of schemes.
--
-- Proof strategy:
-- 1. Uniqueness follows from Epi (flat + surjective ⟹ Epi).
-- 2. For existence, cover Spec R by basic opens D(r) such that x maps D(f(r))
--    into an affine open V_j of Y. On each D(r), construct the descended morphism
--    using isSheafFor_yoneda_affine. Compatibility on overlaps follows from Epi of
--    the base change of f (which is still flat + surjective). Glue using glueMorphisms.
set_option maxHeartbeats 1600000 in
private lemma isSheafFor_yoneda_general {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hff : f.hom.FaithfullyFlat) (Y : Scheme.{u}) :
    Presieve.IsSheafFor (yoneda.obj Y) (Presieve.singleton (Spec.map f)) := by
  haveI : Flat (Spec.map f) := ((flat_and_surjective_SpecMap_iff f).mpr hff).1
  haveI : Surjective (Spec.map f) := ((flat_and_surjective_SpecMap_iff f).mpr hff).2
  rw [Presieve.isSheafFor_singleton]
  intro (x : Spec S ⟶ Y) hx
  have hepi : Epi (Spec.map f) := Flat.epi_of_flat_of_surjective _
  -- Convert hx from yoneda form to composition form
  have hx' : ∀ ⦃Z : Scheme.{u}⦄ (p₁ p₂ : Z ⟶ Spec S),
      p₁ ≫ Spec.map f = p₂ ≫ Spec.map f → p₁ ≫ x = p₂ ≫ x := by
    intro Z p₁ p₂ h
    have := hx p₁ p₂ h
    dsimp [yoneda] at this
    exact this
  -- x is constant on fibers
  have hfiber : ∀ (a b : Spec S), (Spec.map f) a = (Spec.map f) b → x a = x b :=
    fiber_constant hx'
  -- Spec.map f is a quotient map
  have hqm : Topology.IsQuotientMap (Spec.map f) := Flat.isQuotientMap_of_surjective _
  -- The affine cover of Y
  let 𝒱 := Y.affineCover
  -- Fiber saturation: x⁻¹(V_j) is saturated for f
  have hsat : ∀ j, (Spec.map f).base ⁻¹' ((Spec.map f).base ''
      (x.base ⁻¹' Set.range (𝒱.f j))) = x.base ⁻¹' Set.range (𝒱.f j) := by
    intro j; ext s; simp only [Set.mem_preimage, Set.mem_image]
    exact ⟨fun ⟨t, htV, htf⟩ ↦ by rwa [hfiber s t htf.symm], fun hs ↦ ⟨s, hs, rfl⟩⟩
  -- The descended opens U_j are open
  have hU_open : ∀ j, IsOpen ((Spec.map f).base '' (x.base ⁻¹' Set.range (𝒱.f j))) := by
    intro j; rw [← hqm.isOpen_preimage, hsat j]
    exact x.continuous.isOpen_preimage _ (IsOpenImmersion.isOpen_range _)
  -- U_j's cover Spec R
  have hU_cover : ∀ p : Spec R,
      ∃ j, p ∈ (Spec.map f).base '' (x.base ⁻¹' Set.range (𝒱.f j)) := by
    intro p
    obtain ⟨q, hq⟩ := (Spec.map f).surjective p
    exact ⟨𝒱.idx (x q), q, 𝒱.covers (x q), hq⟩
  -- Uniqueness from Epi
  suffices ∃ d : Spec R ⟶ Y, Spec.map f ≫ d = x from
    ⟨this.choose, this.choose_spec, fun y (hy : Spec.map f ≫ y = x) ↦
      hepi.left_cancellation _ _ (by rw [hy, this.choose_spec])⟩
  -- For each point p of Spec R, choose j(p) with p in the descended open U_{j(p)},
  -- and a basic open D(r_p) with p ∈ D(r_p) ⊂ U_{j(p)}.
  have hchoice : ∀ p : Spec R, ∃ (j : 𝒱.I₀) (r : Γ(Spec R, ⊤)),
      p ∈ (Spec R).basicOpen r ∧
      ((Spec R).basicOpen r : Set (Spec R)) ⊆
        (Spec.map f).base '' (x.base ⁻¹' Set.range (𝒱.f j)) := by
    intro p
    obtain ⟨j, hj⟩ := hU_cover p
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpt, htsub⟩ :=
      (isBasis_basicOpen (Spec R)).exists_subset_of_mem_open hj (hU_open j)
    exact ⟨j, r, hpt, htsub⟩
  choose jfun rfun hpr hsub using hchoice
  -- Define the open cover of Spec R
  let 𝒰 : (Spec R).OpenCover := (Spec R).openCoverOfIsOpenCover
    (fun p ↦ (Spec R).basicOpen (rfun p))
    (by
      rw [TopologicalSpace.IsOpenCover, ← TopologicalSpace.Opens.coe_inj,
        TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
      ext q; exact ⟨fun _ ↦ trivial, fun _ ↦ Set.mem_iUnion.mpr ⟨q, hpr q⟩⟩)
  -- For each p, the preimage f⁻¹(D(r_p)) maps into V_{j(p)} under x
  have hDsub : ∀ p (s : (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p))),
      x (((Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι) s) ∈
        Set.range (𝒱.f (jfun p)) := by
    intro p s
    have hfs : (Spec.map f).base
        (((Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι) s) ∈
        ((Spec R).basicOpen (rfun p) : Set (Spec R)) := s.2
    obtain ⟨t, ht, htf⟩ := hsub p hfs
    exact (hfiber _ t htf.symm) ▸ ht
  -- Step 1: For each p, the restriction f ∣_ D(r_p) is flat + surjective (by base change).
  have hflat_res (p : Spec R) : Flat (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (Spec.map f) ((Spec R).basicOpen (rfun p))).flip ‹_›
  have hsurj_res (p : Spec R) : Surjective (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) :=
    MorphismProperty.of_isPullback
      (isPullback_morphismRestrict (Spec.map f) ((Spec R).basicOpen (rfun p))).flip ‹_›
  -- Step 2: For each p, the image of the inclusion composed with x lies in range of 𝒱.f
  have hrange (p : Spec R) :
      Set.range ((Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι ≫ x).base ⊆
        Set.range (𝒱.f (jfun p)).base := by
    rintro y ⟨s, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hDsub p s
  -- Step 3: Lift x restricted to the preimage through the affine cover piece
  have hxlift' (p : Spec R) :
      ∃ (g : (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).toScheme ⟶ 𝒱.X (jfun p)),
        g ≫ 𝒱.f (jfun p) = (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι ≫ x :=
    ⟨IsOpenImmersion.lift _ _ (hrange p), IsOpenImmersion.lift_fac _ _ _⟩
  choose xlift hxlift using hxlift'
  -- Step 4: Descend xlift p through f ∣_ D(r_p) using isSheafFor_yoneda_of_isAffine
  have hdesc (p : Spec R) :
      ∃ dp : ((Spec R).basicOpen (rfun p)).toScheme ⟶ 𝒱.X (jfun p),
        (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) ≫ dp = xlift p := by
    haveI := hflat_res p
    haveI := hsurj_res p
    haveI : IsAffine (𝒱.X (jfun p)) := Scheme.isAffine_affineCover Y (jfun p)
    -- Descend xlift p ≫ isoSpec.hom via isSheafFor_yoneda_of_isAffine, then compose back
    set T := Γ(𝒱.X (jfun p), ⊤)
    set xp' := xlift p ≫ (𝒱.X (jfun p)).isoSpec.hom
    have hxp'_cocycle : ∀ ⦃W : Scheme⦄
        (p₁ p₂ : W ⟶ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p))),
        p₁ ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) =
          p₂ ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) →
        (yoneda.obj (Spec T)).map p₁.op xp' = (yoneda.obj (Spec T)).map p₂.op xp' := by
      intro W p₁ p₂ hp
      show p₁ ≫ xlift p ≫ _ = p₂ ≫ xlift p ≫ _
      have key : p₁ ≫ xlift p = p₂ ≫ xlift p := by
        haveI : Mono (𝒱.f (jfun p)) := inferInstance
        have h : p₁ ≫ xlift p ≫ 𝒱.f (jfun p) = p₂ ≫ xlift p ≫ 𝒱.f (jfun p) := by
          rw [hxlift, ← Category.assoc, ← Category.assoc]
          apply hx' (p₁ ≫ _) (p₂ ≫ _)
          have h_morph : ∀ (q : W ⟶ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p))),
              (q ≫ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι) ≫ Spec.map f =
              (q ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun p))) ≫
                ((Spec R).basicOpen (rfun p)).ι := by
            intro q; rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
          rw [h_morph, h_morph, hp]
        exact (cancel_mono (𝒱.f (jfun p))).mp (by simpa only [Category.assoc] using h)
      simp only [← Category.assoc, key]
    haveI : IsAffine ((Spec R).basicOpen (rfun p)).toScheme := inferInstance
    haveI : IsAffine (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).toScheme :=
      ((isAffineOpen_top (Spec R)).basicOpen (rfun p)).preimage (Spec.map f)
    have hsheaf := isSheafFor_yoneda_of_isAffine
      (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) T
    rw [Presieve.isSheafFor_singleton] at hsheaf
    obtain ⟨dp', hdp', _⟩ := @hsheaf xp' @hxp'_cocycle
    change (Spec.map f ∣_ _) ≫ dp' = xp' at hdp'
    exact ⟨dp' ≫ (𝒱.X (jfun p)).isoSpec.inv, by
      rw [← Category.assoc, hdp', Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  choose dp hdp using hdesc
  -- Step 5: Define the morphism on each cover piece
  let emor (p : 𝒰.I₀) : 𝒰.X p ⟶ Y := dp p ≫ 𝒱.f (jfun p)
  -- Step 6: Compatibility on overlaps.
  -- Both sides, precomposed with the base change of Spec.map f to the overlap (which is epi),
  -- give x restricted to the overlap. By epi, both sides are equal.
  have hcompat : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ emor a =
      pullback.snd (𝒰.f a) (𝒰.f b) ≫ emor b := by
    intro a b
    -- The inclusion of the overlap into Spec R
    set ι_ab : pullback (𝒰.f a) (𝒰.f b) ⟶ Spec R :=
      pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a
    -- pullback.snd (Spec.map f) ι_ab is the base change of Spec.map f along ι_ab: epi
    haveI : Flat (pullback.snd (Spec.map f) ι_ab) :=
      MorphismProperty.pullback_snd _ _ ‹Flat (Spec.map f)›
    haveI : Surjective (pullback.snd (Spec.map f) ι_ab) :=
      MorphismProperty.pullback_snd _ _ ‹Surjective (Spec.map f)›
    haveI : Epi (pullback.snd (Spec.map f) ι_ab) :=
      Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.snd (Spec.map f) ι_ab)]
    -- Factor pullback.fst through the preimages f⁻¹ D(r_a) and f⁻¹ D(r_b)
    have hfact_a : Set.range (pullback.fst (Spec.map f) ι_ab).base ⊆
        Set.range (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun a)).ι.base := by
      rintro y ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.coe_preimage, Set.mem_preimage]
      -- goal: (Spec.map f) ((pullback.fst ..).base z) ∈ ↑D(r_a)
      have hcond : (Spec.map f) ((pullback.fst (Spec.map f) ι_ab).base z) =
          (pullback.snd (Spec.map f) ι_ab ≫ ι_ab) z := by
        show (pullback.fst (Spec.map f) ι_ab ≫ Spec.map f) z = _
        rw [pullback.condition]
      rw [hcond, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact (pullback.fst (𝒰.f a) (𝒰.f b) ((pullback.snd (Spec.map f) ι_ab) z)).2
    let fac_a := IsOpenImmersion.lift
      (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun a)).ι
      (pullback.fst (Spec.map f) ι_ab) hfact_a
    have hfac_a_ι : fac_a ≫ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun a)).ι =
        pullback.fst (Spec.map f) ι_ab := IsOpenImmersion.lift_fac _ _ _
    have hfact_b : Set.range (pullback.fst (Spec.map f) ι_ab).base ⊆
        Set.range (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun b)).ι.base := by
      rintro y ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.coe_preimage, Set.mem_preimage]
      -- goal: (Spec.map f) ((pullback.fst ..).base z) ∈ ↑D(r_b)
      have hcond : (Spec.map f) ((pullback.fst (Spec.map f) ι_ab).base z) =
          (pullback.snd (Spec.map f) ι_ab ≫ ι_ab) z := by
        show (pullback.fst (Spec.map f) ι_ab ≫ Spec.map f) z = _
        rw [pullback.condition]
      rw [hcond, Scheme.Hom.comp_apply]
      -- goal: ι_ab (snd z) ∈ ↑D(r_b), where ι_ab = fst_ab ≫ 𝒰.f a = snd_ab ≫ 𝒰.f b
      have hpb : ι_ab ((pullback.snd (Spec.map f) ι_ab) z) =
          (𝒰.f b) ((pullback.snd (𝒰.f a) (𝒰.f b) (pullback.snd (Spec.map f) ι_ab z))) := by
        show (pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a) (pullback.snd (Spec.map f) ι_ab z) =
          (pullback.snd (𝒰.f a) (𝒰.f b) ≫ 𝒰.f b) (pullback.snd (Spec.map f) ι_ab z)
        rw [pullback.condition]
      rw [hpb]
      exact (pullback.snd (𝒰.f a) (𝒰.f b) ((pullback.snd (Spec.map f) ι_ab) z)).2
    let fac_b := IsOpenImmersion.lift
      (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun b)).ι
      (pullback.fst (Spec.map f) ι_ab) hfact_b
    have hfac_b_ι : fac_b ≫ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun b)).ι =
        pullback.fst (Spec.map f) ι_ab := IsOpenImmersion.lift_fac _ _ _
    -- Key: relate fac_a ≫ (f ∣_ D(r_a)) to snd ≫ fst_ab (and similarly for b)
    have hfac_rest_a : fac_a ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun a)) =
        pullback.snd (Spec.map f) ι_ab ≫ pullback.fst (𝒰.f a) (𝒰.f b) := by
      have hmono : Mono (𝒰.f a) := inferInstance
      have hLHS : (fac_a ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun a))) ≫ 𝒰.f a =
          pullback.snd (Spec.map f) ι_ab ≫ ι_ab := by
        conv_lhs => rw [Category.assoc]
        change fac_a ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun a)) ≫
          ((Spec R).basicOpen (rfun a)).ι = _
        rw [morphismRestrict_ι, ← Category.assoc, hfac_a_ι,
          (pullback.condition (f := Spec.map f) (g := ι_ab))]
      have hRHS : (pullback.snd (Spec.map f) ι_ab ≫ pullback.fst (𝒰.f a) (𝒰.f b)) ≫ 𝒰.f a =
          pullback.snd (Spec.map f) ι_ab ≫ ι_ab := by
        rw [Category.assoc]
      exact hmono.right_cancellation _ _ (hLHS.trans hRHS.symm)
    have hfac_rest_b : fac_b ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun b)) =
        pullback.snd (Spec.map f) ι_ab ≫ pullback.snd (𝒰.f a) (𝒰.f b) := by
      have hmono : Mono (𝒰.f b) := inferInstance
      have hLHS : (fac_b ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun b))) ≫ 𝒰.f b =
          pullback.snd (Spec.map f) ι_ab ≫ ι_ab := by
        conv_lhs => rw [Category.assoc]
        change fac_b ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun b)) ≫
          ((Spec R).basicOpen (rfun b)).ι = _
        rw [morphismRestrict_ι, ← Category.assoc, hfac_b_ι,
          (pullback.condition (f := Spec.map f) (g := ι_ab))]
      have hRHS : (pullback.snd (Spec.map f) ι_ab ≫ pullback.snd (𝒰.f a) (𝒰.f b)) ≫ 𝒰.f b =
          pullback.snd (Spec.map f) ι_ab ≫ ι_ab := by
        rw [Category.assoc, ← pullback.condition (f := 𝒰.f a) (g := 𝒰.f b)]
      exact hmono.right_cancellation _ _ (hLHS.trans hRHS.symm)
    -- Both sides equal pullback.fst ≫ x
    -- Side a: snd ≫ fst_ab ≫ emor a = snd ≫ fst_ab ≫ dp a ≫ 𝒱.f
    --   = fac_a ≫ (f ∣_ D(r_a)) ≫ dp a ≫ 𝒱.f (by hfac_rest_a)
    --   = fac_a ≫ xlift a ≫ 𝒱.f (by hdp a)
    --   = fac_a ≫ (f⁻¹ D(r_a)).ι ≫ x (by hxlift)
    --   = pullback.fst ≫ x (by hfac_a_ι)
    -- Both sides equal pullback.fst ≫ x after unfolding
    -- Key helper: compute the chain fac_? ≫ (f ∣_ D(r_?)) ≫ dp ? ≫ 𝒱.f = fac_? ≫ ι ≫ x
    have hchain_a : fac_a ≫ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun a)).ι ≫ x =
        pullback.fst (Spec.map f) ι_ab ≫ x := by
      rw [← Category.assoc, hfac_a_ι]
    have hchain_b : fac_b ≫ (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun b)).ι ≫ x =
        pullback.fst (Spec.map f) ι_ab ≫ x := by
      rw [← Category.assoc, hfac_b_ι]
    -- Key helper: (f ∣_ D(r_p)) ≫ emor p = ι_p ≫ x
    have hkey_a : (Spec.map f ∣_ (Spec R).basicOpen (rfun a)) ≫ emor a =
        (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun a)).ι ≫ x := by
      show (Spec.map f ∣_ (Spec R).basicOpen (rfun a)) ≫ dp a ≫ 𝒱.f (jfun a) = _
      rw [← Category.assoc, hdp, hxlift]
    have hkey_b : (Spec.map f ∣_ (Spec R).basicOpen (rfun b)) ≫ emor b =
        (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun b)).ι ≫ x := by
      show (Spec.map f ∣_ (Spec R).basicOpen (rfun b)) ≫ dp b ≫ 𝒱.f (jfun b) = _
      rw [← Category.assoc, hdp, hxlift]
    -- Use term-level Category.assoc to avoid the let-binding issue with fac_a/fac_b
    have hassoc_rest_a : fac_a ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun a)) ≫ emor a =
        (pullback.snd (Spec.map f) ι_ab ≫ pullback.fst (𝒰.f a) (𝒰.f b)) ≫ emor a :=
      (Category.assoc ..).symm.trans (congrArg (· ≫ emor a) hfac_rest_a)
    have hassoc_rest_b : fac_b ≫ (Spec.map f ∣_ (Spec R).basicOpen (rfun b)) ≫ emor b =
        (pullback.snd (Spec.map f) ι_ab ≫ pullback.snd (𝒰.f a) (𝒰.f b)) ≫ emor b :=
      (Category.assoc ..).symm.trans (congrArg (· ≫ emor b) hfac_rest_b)
    have hside_a : pullback.snd (Spec.map f) ι_ab ≫
        pullback.fst (𝒰.f a) (𝒰.f b) ≫ emor a =
        pullback.fst (Spec.map f) ι_ab ≫ x := by
      rw [← Category.assoc (pullback.snd _ _) (pullback.fst _ _), ← hassoc_rest_a,
        hkey_a]
      exact (Category.assoc ..).symm.trans (congrArg (· ≫ x) hfac_a_ι)
    have hside_b : pullback.snd (Spec.map f) ι_ab ≫
        pullback.snd (𝒰.f a) (𝒰.f b) ≫ emor b =
        pullback.fst (Spec.map f) ι_ab ≫ x := by
      rw [← Category.assoc (pullback.snd _ _) (pullback.snd _ _), ← hassoc_rest_b,
        hkey_b]
      exact (Category.assoc ..).symm.trans (congrArg (· ≫ x) hfac_b_ι)
    rw [hside_a, hside_b]
  -- Step 7: Glue and verify
  refine ⟨𝒰.glueMorphisms emor hcompat, ?_⟩
  -- Verify: Spec.map f ≫ d = x using hom_ext_of_forall on Spec S
  apply hom_ext_of_forall
  intro s
  -- For each s : Spec S, let p = f(s) and use the open f⁻¹(D(r_p))
  set p := (Spec.map f).base s
  refine ⟨Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p), hpr p, ?_⟩
  -- On this open: ι ≫ (Spec.map f ≫ d) = ι ≫ x
  -- ι ≫ Spec.map f = (f ∣_ D(r_p)) ≫ D(r_p).ι = (f ∣_ D(r_p)) ≫ 𝒰.f p
  -- So ι ≫ (Spec.map f ≫ d) = (f ∣_ D(r_p)) ≫ (𝒰.f p ≫ d) = (f ∣_ D(r_p)) ≫ emor p
  -- = (f ∣_ D(r_p)) ≫ dp p ≫ 𝒱.f (jfun p) = xlift p ≫ 𝒱.f (jfun p) = ι ≫ x
  calc (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι ≫ (Spec.map f ≫ 𝒰.glueMorphisms emor hcompat)
      = ((Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι ≫ Spec.map f) ≫
          𝒰.glueMorphisms emor hcompat := by rw [Category.assoc]
    _ = ((Spec.map f ∣_ (Spec R).basicOpen (rfun p)) ≫ ((Spec R).basicOpen (rfun p)).ι) ≫
          𝒰.glueMorphisms emor hcompat := by rw [morphismRestrict_ι]
    _ = (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) ≫
          (((Spec R).basicOpen (rfun p)).ι ≫ 𝒰.glueMorphisms emor hcompat) := by
        rw [Category.assoc]
    _ = (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) ≫ emor p := by
        congr 1; exact 𝒰.ι_glueMorphisms emor hcompat p
    _ = (Spec.map f ⁻¹ᵁ (Spec R).basicOpen (rfun p)).ι ≫ x := by
        -- emor p = dp p ≫ 𝒱.f (jfun p) definitionally
        show (Spec.map f ∣_ (Spec R).basicOpen (rfun p)) ≫ dp p ≫ 𝒱.f (jfun p) = _
        rw [← Category.assoc, hdp, hxlift]

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) := by
  have hff : f.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff]
    exact ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hf, hs⟩
  rw [← Sieve.effectiveEpimorphic_singleton,
      Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Y
  exact isSheafFor_yoneda_general f hff Y

/-- The fpqc topology is subcanonical. -/
instance subcanonical_fpqcTopology : fpqcTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
  rw [isSheaf_fpqcTopology_iff (yoneda.obj X)]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)
  · intro R S f hf hs
    revert X
    rw [← Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda,
      Sieve.effectiveEpimorphic_singleton]
    exact effectiveEpi_of_flat _ hf hs

/-- A quasi-compact flat cover is an effective epimorphism family. -/
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}}
    (𝒰 : Cover.{u} (precoverage @Flat) X)
    [QuasiCompactCover 𝒰.1] : EffectiveEpiFamily 𝒰.X 𝒰.f := by
  rw [← Sieve.effectiveEpimorphic_family]
  refine .of_subcanonical fpqcTopology _ ?_
  exact 𝒰.generate_ofArrows_mem_propqcTopology

/-- Any surjective, quasi-compact and flat morphism is an effective epimorphism. -/
instance {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [Surjective f] [Flat f] : EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]
  refine .of_subcanonical fpqcTopology _ ?_
  exact f.generate_singleton_mem_propqcTopology ‹_›

/-- Any surjective, flat morphism locally of finite presentation is an effective epimorphism.
In particular, étale surjections satisfy this.-/
instance {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Surjective f] [Flat f] :
    EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]
  refine .of_subcanonical fpqcTopology _ ?_
  exact f.generate_singleton_mem_fpqcTopology_of_locallyOfFinitePresentation

end AlgebraicGeometry
