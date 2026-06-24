/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.WeaklyEtale
import Proetale.Mathlib.CategoryTheory.Limits.Presentation

/-!
# Filtered colimit stability of `Algebra.TensorProduct.lmul'.Flat`

If `R → S` is a filtered colimit of `R`-algebras `Sᵢ` (in `CommAlgCat R`) and each
`lmul'_{Sᵢ/R} : Sᵢ ⊗[R] Sᵢ → Sᵢ` is flat, then `lmul'_{S/R} : S ⊗[R] S → S` is flat.

This is used to prove the instance `Algebra.IndEtale R S → Algebra.WeaklyEtale R S`.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace RingHom.Flat

variable {R : Type u} [CommRing R]
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- If `S = colim_i Sᵢ` is a filtered colimit in `CommAlgCat R` and each `Sᵢ` is a weakly
étale `R`-algebra (i.e., each `lmul' R : Sᵢ ⊗[R] Sᵢ → Sᵢ` is flat), then
`lmul' R : S ⊗[R] S → S` is also flat.

This is the key colimit-stability lemma used to prove that ind-étale algebras are weakly
étale (since étale implies weakly étale). -/
theorem of_filteredColimit_lmul'
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ i, (Algebra.TensorProduct.lmul' R (S := P.diag.obj i)).Flat) :
    (Algebra.TensorProduct.lmul' R (S := S)).Flat := by
  have : IsConnected ι := IsFiltered.isConnected ι
  -- 1. Project P to a colim presentation Q in CommRingCat.
  let Q : ColimitPresentation ι (CommRingCat.of S) :=
    P.map (forget₂ (CommAlgCat R) CommRingCat)
  -- The diagram D in CommRingCat and the codiagonal cocone (SR, c).
  let SS : CommRingCat.{u} := CommRingCat.of (S ⊗[R] S)
  let SR : CommRingCat.{u} := CommRingCat.of S
  let lmulMap : SS ⟶ SR :=
    CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  -- Apply `RingHom.Flat.of_isColimit` to lmulMap.
  let D : ι ⥤ CommRingCat.{u} := Q.diagPushout
  let c : D ⟶ (Functor.const ι).obj SR := Q.diagPushoutCocone
  have hc : IsColimit (Cocone.mk SR c) := Q.isColimitDiagPushout
  -- Build `t : (const SS) ⟶ D` via the iso `pushout(R → S, R → S) ≅ SS`.
  let isoSS : pushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R S)) ≅ SS :=
    (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
  -- For each i, the natural map pushout(R → S, R → S) → pushout(Q.ι.app i, Q.ι.app i).
  let tRaw : (i : ι) → pushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R S)) ⟶ D.obj i := fun i ↦
    pushout.desc (pushout.inl (Q.ι.app i) (Q.ι.app i))
      (pushout.inr (Q.ι.app i) (Q.ι.app i))
      (by
        have hRSi : CommRingCat.ofHom (algebraMap R S) =
            CommRingCat.ofHom (algebraMap R (P.diag.obj i)) ≫ Q.ι.app i := by
          ext r
          change (algebraMap R S) r = (Q.ι.app i).hom ((algebraMap R (P.diag.obj i)) r)
          exact ((P.ι.app i).hom.commutes r).symm
        have hcond : Q.ι.app i ≫ pushout.inl (Q.ι.app i) (Q.ι.app i) =
            Q.ι.app i ≫ pushout.inr (Q.ι.app i) (Q.ι.app i) := pushout.condition
        rw [hRSi]
        exact ((Category.assoc _ _ _).trans (congrArg _ hcond)).trans
          (Category.assoc _ _ _).symm)
  have htRaw_nat : ∀ {i j : ι} (h : i ⟶ j), tRaw i ≫ D.map h = tRaw j := by
    intro i j h
    apply pushout.hom_ext
    · simp only [tRaw, D, pushout.inl_desc_assoc, pushout.inl_desc]
      exact Q.diagPushout_inl_map h
    · simp only [tRaw, D, pushout.inr_desc_assoc, pushout.inr_desc]
      exact Q.diagPushout_inr_map h
  let t : (Functor.const ι).obj SS ⟶ D :=
    { app := fun i ↦ isoSS.inv ≫ tRaw i
      naturality := fun {i j} h ↦ by
        dsimp
        rw [Category.id_comp, Category.assoc, htRaw_nat h] }
  -- The composition `t.app i ≫ c.app i = lmulMap`.
  have htc_eq : ∀ i, t.app i ≫ c.app i = lmulMap := by
    intro i
    simp only [t, c, Category.assoc]
    -- tRaw i ≫ c.app i is the codiagonal pushout map on pushout(R → S, R → S).
    have hraw_codiag : tRaw i ≫ Q.diagPushoutCocone.app i =
        pushout.desc (𝟙 SR) (𝟙 SR) rfl := by
      apply pushout.hom_ext
      · simp only [tRaw, SR, pushout.inl_desc_assoc, Q.diagPushoutCocone_app, pushout.inl_desc]
      · simp only [tRaw, SR, pushout.inr_desc_assoc, Q.diagPushoutCocone_app, pushout.inr_desc]
    rw [hraw_codiag]
    -- isoSS.inv ≫ (codiagonal of pushout(R→S, R→S)) = lmulMap.
    -- Verify via IsPushout.hom_ext for the includeLeft/includeRight presentation of SS.
    apply (CommRingCat.isPushout_tensorProduct R S S).hom_ext
    · have hinl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := R) (A := S) (B := S)) ≫ isoSS.inv =
          pushout.inl (CommRingCat.ofHom (algebraMap R S))
            (CommRingCat.ofHom (algebraMap R S)) :=
        (CommRingCat.isPushout_tensorProduct R S S).inl_isoPushout_hom
      calc CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
            isoSS.inv ≫ pushout.desc (𝟙 SR) (𝟙 SR) rfl
          = pushout.inl (CommRingCat.ofHom (algebraMap R S))
              (CommRingCat.ofHom (algebraMap R S)) ≫
              pushout.desc (𝟙 SR) (𝟙 SR) rfl := by rw [← Category.assoc, hinl]
        _ = 𝟙 SR := pushout.inl_desc _ _ _
        _ = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ lmulMap := by
            ext a
            change a = (Algebra.TensorProduct.lmul' R)
              (Algebra.TensorProduct.includeLeftRingHom a)
            rw [Algebra.TensorProduct.includeLeftRingHom_apply,
              Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
    · have hinr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := S) (B := S)).toRingHom ≫ isoSS.inv =
          pushout.inr (CommRingCat.ofHom (algebraMap R S))
            (CommRingCat.ofHom (algebraMap R S)) :=
        (CommRingCat.isPushout_tensorProduct R S S).inr_isoPushout_hom
      calc CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := R) (A := S) (B := S)).toRingHom ≫
            isoSS.inv ≫ pushout.desc (𝟙 SR) (𝟙 SR) rfl
          = pushout.inr (CommRingCat.ofHom (algebraMap R S))
              (CommRingCat.ofHom (algebraMap R S)) ≫
              pushout.desc (𝟙 SR) (𝟙 SR) rfl := by rw [← Category.assoc, hinr]
        _ = 𝟙 SR := pushout.inr_desc _ _ _
        _ = CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := R) (A := S) (B := S)).toRingHom ≫ lmulMap := by
            ext a
            change a = (Algebra.TensorProduct.lmul' R)
              (Algebra.TensorProduct.includeRight (A := S) a)
            rw [Algebra.TensorProduct.includeRight_apply,
              Algebra.TensorProduct.lmul'_apply_tmul, one_mul]
  -- Flatness of t.app i: comes from lift_includeLeft_includeRight applied to h i.
  have htflat : ∀ i, (t.app i).hom.Flat := by
    intro i
    -- Setup algebra structures via `Q.ι.app i`.
    letI : Algebra (P.diag.obj i) S := ((P.ι.app i).hom).toAlgebra
    have : IsScalarTower R (P.diag.obj i) S :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((P.ι.app i).hom.commutes r).symm
    -- The lift map α : S ⊗[R] S → S ⊗[P.diag.obj i] S as an algebra hom.
    let α : S ⊗[R] S →ₐ[S] S ⊗[P.diag.obj i] S := Algebra.TensorProduct.lift
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (fun _ _ ↦ mul_comm _ _)
    have hα : α.toRingHom.Flat :=
      RingHom.Flat.lift_includeLeft_includeRight (R := R) (S := P.diag.obj i) S S (h i)
    -- The iso S ⊗[P.diag.obj i] S ≅ D.obj i (defeq via letI).
    let γ : CommRingCat.of (S ⊗[P.diag.obj i] S) ≅ D.obj i :=
      (CommRingCat.isPushout_tensorProduct (P.diag.obj i) S S).isoPushout
    -- The key identification: t.app i = ofHom α.toRingHom ≫ γ.hom.
    have heq : t.app i = CommRingCat.ofHom α.toRingHom ≫ γ.hom := by
      apply (CommRingCat.isPushout_tensorProduct R S S).hom_ext
      · -- Left leg: includeLeftRingHom (R, S, S)
        have ht_inl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
              (R := R) (A := S) (B := S)) ≫ t.app i =
            pushout.inl (Q.ι.app i) (Q.ι.app i) := by
          simp only [t, tRaw]
          have hinl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
                (R := R) (A := S) (B := S)) ≫ isoSS.inv =
              pushout.inl (CommRingCat.ofHom (algebraMap R S))
                (CommRingCat.ofHom (algebraMap R S)) :=
            (CommRingCat.isPushout_tensorProduct R S S).inl_isoPushout_hom
          rw [← Category.assoc, hinl, pushout.inl_desc]
        have hα_inl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
              (R := R) (A := S) (B := S)) ≫ CommRingCat.ofHom α.toRingHom =
            CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
              (R := P.diag.obj i) (A := S) (B := S)) := by
          ext a
          change α (Algebra.TensorProduct.includeLeftRingHom a) =
            Algebra.TensorProduct.includeLeftRingHom a
          simp [α, Algebra.TensorProduct.includeLeftRingHom_apply,
            Algebra.TensorProduct.lift_tmul]
        have hγ_inl : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
              (R := P.diag.obj i) (A := S) (B := S)) ≫ γ.hom =
            pushout.inl (CommRingCat.ofHom (algebraMap (P.diag.obj i) S))
              (CommRingCat.ofHom (algebraMap (P.diag.obj i) S)) :=
          (CommRingCat.isPushout_tensorProduct (P.diag.obj i) S S).inl_isoPushout_hom
        rw [ht_inl, ← Category.assoc, hα_inl, hγ_inl]
        rfl
      · -- Right leg: includeRight (R, S, S)
        have ht_inr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := R) (A := S) (B := S)).toRingHom ≫ t.app i =
            pushout.inr (Q.ι.app i) (Q.ι.app i) := by
          simp only [t, tRaw]
          have hinr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
                (R := R) (A := S) (B := S)).toRingHom ≫ isoSS.inv =
              pushout.inr (CommRingCat.ofHom (algebraMap R S))
                (CommRingCat.ofHom (algebraMap R S)) :=
            (CommRingCat.isPushout_tensorProduct R S S).inr_isoPushout_hom
          rw [← Category.assoc, hinr, pushout.inr_desc]
        have hα_inr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := R) (A := S) (B := S)).toRingHom ≫ CommRingCat.ofHom α.toRingHom =
            CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := P.diag.obj i) (A := S) (B := S)).toRingHom := by
          ext a
          change α (Algebra.TensorProduct.includeRight a) =
            Algebra.TensorProduct.includeRight a
          simp [α, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.lift_tmul]
        have hγ_inr : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
              (R := P.diag.obj i) (A := S) (B := S)).toRingHom ≫ γ.hom =
            pushout.inr (CommRingCat.ofHom (algebraMap (P.diag.obj i) S))
              (CommRingCat.ofHom (algebraMap (P.diag.obj i) S)) :=
          (CommRingCat.isPushout_tensorProduct (P.diag.obj i) S S).inr_isoPushout_hom
        rw [ht_inr, ← Category.assoc, hα_inr, hγ_inr]
        rfl
    rw [heq, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact RingHom.Flat.comp hα (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso γ.hom))
  -- Apply of_isColimit.
  exact RingHom.Flat.of_isColimit lmulMap ι D hc
    (fun i ↦ ⟨htflat i, htc_eq i⟩)

end RingHom.Flat
