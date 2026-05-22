/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.RingTheory.RingHom.Flat
import Proetale.Mathlib.RingTheory.TensorProduct.Maps

/-!
# Weakly étale algebras

-/

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct

lemma RingHom.Flat.iff_ringEquiv_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S}
    {e : S ≃+* T} :
    (e.toRingHom.comp f).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp hf (.of_bijective e.bijective)⟩
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)

lemma RingHom.Flat.iff_comp_ringEquiv {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S}
    {e : T ≃+* R} :
    (f.comp e.toRingHom).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp (.of_bijective e.bijective) hf⟩
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

def TensorProduct.congrRing
    {R S : Type*} (M N : Type*) [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) :
    M ⊗[R] N ≃ₗ[S] M ⊗[S] N :=
  letI f : M ⊗[R] N →ₗ[S] M ⊗[S] N :=
    { __ := lift ((TensorProduct.mk S M N).restrictScalars₁₂ R R)
      map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
  letI b : M →ₗ[S] N →ₗ[S] M ⊗[R] N := --TensorProduct.mk R M N
    { toFun m :=
        { __ := TensorProduct.mk R M N m
          map_smul' s x := by obtain ⟨r, rfl⟩ := h s; simp }
      map_add' _ _ := by ext; simp
      map_smul' s x := by ext; obtain ⟨r, rfl⟩ := h s; simp }
  .ofLinear f (lift b) (by ext; rfl) (by ext; rfl)

@[simp]
lemma TensorProduct.congrRing_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    TensorProduct.congrRing M N h (m ⊗ₜ[R] n) = m ⊗ₜ[S] n :=
  rfl

@[simp]
lemma TensorProduct.congrRing_symm_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module S M] [Module S N]
    [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (m : M) (n : N) :
    (TensorProduct.congrRing M N h).symm (m ⊗ₜ[S] n) = m ⊗ₜ[R] n :=
  rfl

def Algebra.TensorProduct.congrRing
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) :
    A ⊗[R] B ≃ₐ[T] A ⊗[S] B where
  __ := _root_.TensorProduct.congrRing A B h
  map_mul' := LinearMap.map_mul_of_map_mul_tmul (by simp)
  commutes' _ := rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    Algebra.TensorProduct.congrRing T A B h (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

@[simp]
lemma Algebra.TensorProduct.congrRing_symm_tmul
    {R S : Type*} (T A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra S A] [Algebra S B]
    [Algebra R S] [IsScalarTower R S A] [IsScalarTower R S B] [Algebra T A]
    (h : Function.Surjective (algebraMap R S)) (a : A) (b : B) :
    (Algebra.TensorProduct.congrRing T A B h).symm (a ⊗ₜ b) = a ⊗ₜ b :=
  rfl

def TensorProduct.uliftEquiv
    (R M N : Type*) [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] :
    ULift.{u₁} (M ⊗[R] N) ≃ₗ[R] ULift.{u₂} M ⊗[ULift.{u₃} R] ULift.{u₄} N :=
  ULift.moduleEquiv ≪≫ₗ
    TensorProduct.congr ULift.moduleEquiv.symm ULift.moduleEquiv.symm ≪≫ₗ
    ((TensorProduct.congrRing (R := R) _ _ (by exact ULift.up_surjective)).restrictScalars R)

@[simp]
lemma TensorProduct.down_uliftEquiv_symm_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : ULift M) (n : ULift N) :
    ((TensorProduct.uliftEquiv R M N).symm (m ⊗ₜ n)).down = m.down ⊗ₜ n.down :=
  rfl

@[simp]
lemma TensorProduct.uliftEquiv_tmul
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (m : M) (n : N) :
    TensorProduct.uliftEquiv R M N ⟨m ⊗ₜ n⟩ = ⟨m⟩ ⊗ₜ ⟨n⟩ :=
  rfl

open CategoryTheory Limits

-- `(S ⊗[R] S) (T ⊗[R] A) S (T ⊗[S] A)`
lemma RingHom.Flat.lift_includeLeft_includeRight {R S : Type u} (T A : Type u)
    [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat) :
    (Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft)
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (fun _ _ ↦ .all _ _) : T ⊗[R] A →ₐ[T] T ⊗[S] A).Flat := by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp

namespace Algebra

section

attribute [local instance] TensorProduct.rightAlgebra in
lemma TensorProduct.flat_lTensor {R S : Type*} (A : Type*) {B D : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    {f : B →ₐ[R] D} (hf : f.Flat) :
    (TensorProduct.lTensor (S := S) A f).Flat := by
  algebraize [f.toRingHom, (lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(IsPushout.cancelBaseChange_symm_comp_lTensor R _ _ _) x) }
  exact .of_linearEquiv e.toLinearEquiv

lemma TensorProduct.flat_map {R S A B C D : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    [Algebra S C] [IsScalarTower R S C] [CommRing D] [Algebra R D]
    {f : A →ₐ[S] C} {g : B →ₐ[R] D}
    (hf : f.Flat) (hg : g.Flat) :
    (TensorProduct.map f g).Flat := by
  have heq : TensorProduct.map f g =
      (TensorProduct.map f (.id R D)).comp (TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact TensorProduct.flat_lTensor _ hg
  · have : (map f (AlgHom.id R D)).restrictScalars R =
        (TensorProduct.comm _ _ _).toAlgHom.comp
          ((lTensor _ (f.restrictScalars R)).comp
            (TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (lTensor D (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective)
      (TensorProduct.flat_lTensor D hf)

end

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The kernel of a flat surjective ring map is a pure ideal. -/
lemma _root_.RingHom.ker_pure_of_flat_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (hsurj : Function.Surjective f) :
    (RingHom.ker f).Pure := by
  letI := f.toAlgebra
  haveI : Module.Flat A B := by rwa [← RingHom.flat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
  exact .of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective
    (f := Algebra.ofId A B) hsurj).toLinearEquiv

lemma FormallyUnramified.of_flat_lmul' (h : (TensorProduct.lmul' (S := S) R).Flat) :
    FormallyUnramified R S := by
  haveI : (KaehlerDifferential.ideal R S).Pure :=
    RingHom.ker_pure_of_flat_surjective (TensorProduct.lmul' (S := S) R).toRingHom h
      (fun x ↦ ⟨1 ⊗ₜ x, by simp⟩)
  rw [formallyUnramified_iff]
  exact (Ideal.cotangent_subsingleton_iff _).mpr (Ideal.isIdempotentElem_of_pure _)

namespace WeaklyEtale

instance (priority := low) [WeaklyEtale R S] : FormallyUnramified R S :=
  .of_flat_lmul' (flat_lmul' R S)

instance (priority := low) [WeaklyEtale R S] [FinitePresentation R S] : Etale R S :=
  .of_formallyUnramified_of_flat

end WeaklyEtale

end Algebra

namespace RingHom

@[algebraize]
def WeaklyEtale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.WeaklyEtale R S

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma weaklyEtale_algebraMap_iff [Algebra R S] :
    (algebraMap R S).WeaklyEtale ↔ Algebra.WeaklyEtale R S := by
  rw [WeaklyEtale, toAlgebra_algebraMap]

/-- A weakly étale ring map is formally unramified. -/
lemma WeaklyEtale.formallyUnramified {f : R →+* S} (hf : f.WeaklyEtale) :
    f.FormallyUnramified := by
  algebraize [f]
  have : Algebra.WeaklyEtale R S := hf
  exact (inferInstance : Algebra.FormallyUnramified R S)

end RingHom
