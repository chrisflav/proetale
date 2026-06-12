/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Filtered
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.WeaklyEtale
import Proetale.Mathlib.CategoryTheory.Limits.Presentation

/-!
# Filtered colimit stability of `Algebra.TensorProduct.lmul'.Flat`

If `R → S` is a filtered colimit of `R`-algebras `Sᵢ` (in `CommAlgCat R`) and each
`lmul'_{Sᵢ/R} : Sᵢ ⊗[R] Sᵢ → Sᵢ` is flat, then `lmul'_{S/R} : S ⊗[R] S → S` is flat.

This is used to prove the instance `Algebra.IndEtale R S → Algebra.WeaklyEtale R S`.

## Strategy

Apply `RingHom.Flat.of_isColimit` with the diagram
`D : ι ⥤ CommRingCat`, `D.obj i = pushout(pi.app i, pi.app i) = S ⊗[Sᵢ] S`,
and the cocone `(S, c)` where each `c.app i : S ⊗[Sᵢ] S → S` is the codiagonal.
The cocone `(S, c)` is a colimit cocone (this is the "filtered colim of `S ⊗[Sᵢ] S`
via codiagonals identifies with `S`" identity), which follows from filtered colim
commuting with pushouts.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

namespace ColimitPresentation

variable [HasPushouts C]
variable {ι : Type*} [Category ι] {X : C} (P : ColimitPresentation ι X)

/-- The codiagonal cocone: `app i = pushout.desc (𝟙 X) (𝟙 X) rfl`. -/
@[simps]
noncomputable def diagPushoutCocone : P.diagPushout ⟶ (Functor.const ι).obj X where
  app i := pushout.desc (𝟙 X) (𝟙 X) rfl
  naturality {i j} h := by
    dsimp [diagPushout]
    apply pushout.hom_ext
    all_goals
      simp only [← Category.assoc, pushout.inl_desc, pushout.inr_desc,
        Category.id_comp, Category.comp_id]

/-- The descent cocone over `P.diag` induced by a cocone over `P.diagPushout`. -/
noncomputable def diagPushoutCoconeDescAux (s : Cocone P.diagPushout) :
    Cocone P.diag where
  pt := s.pt
  ι :=
    { app := fun i => P.ι.app i ≫ pushout.inl _ _ ≫ s.ι.app i
      naturality := fun {i j} h => by
        dsimp
        rw [Category.comp_id]
        have hpi : P.diag.map h ≫ P.ι.app j = P.ι.app i := P.w h
        have hs : P.diagPushout.map h ≫ s.ι.app j = s.ι.app i := by
          have := s.ι.naturality h
          simpa using this
        have hinl_a : pushout.inl (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map h ≫ s.ι.app j =
            pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j :=
          P.diagPushout_inl_map_assoc h _
        -- Build the trans chain as a pure term to avoid `rw` motive/assoc issues.
        have step1 : P.diag.map h ≫ P.ι.app j ≫ pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j =
            P.ι.app i ≫ pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j) hpi)
        have step2 : P.ι.app i ≫ pushout.inl (P.ι.app j) (P.ι.app j) ≫ s.ι.app j =
            P.ι.app i ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i :=
          (congrArg (P.ι.app i ≫ ·) hinl_a.symm).trans
            (congrArg (fun X => P.ι.app i ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ X) hs)
        exact step1.trans step2 }

variable [IsFiltered ι]

/-- The codiagonal cocone over the diagonal pushout diagram is a colimit. -/
noncomputable def isColimitDiagPushout :
    IsColimit (Cocone.mk X P.diagPushoutCocone) where
  desc s := P.isColimit.desc (P.diagPushoutCoconeDescAux s)
  fac s i := by
    change pushout.desc (𝟙 X) (𝟙 X) rfl ≫ P.isColimit.desc (P.diagPushoutCoconeDescAux s) =
      s.ι.app i
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, Category.id_comp]
      -- Goal: P.isColimit.desc (P.diagPushoutCoconeDescAux s) =
      --       pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i.
      -- By hom_ext: precompose with P.ι.app k.
      apply P.isColimit.hom_ext
      intro k
      have := P.isColimit.fac (P.diagPushoutCoconeDescAux s) k
      -- this : P.ι.app k ≫ P.isColimit.desc (P.diagPushoutCoconeDescAux s) =
      --        (P.diagPushoutCoconeDescAux s).ι.app k = P.ι.app k ≫ pushout.inl _ _ ≫ s.ι.app k.
      rw [this]
      -- Goal: P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k =
      --       P.ι.app k ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i.
      -- Bridge through `m := max i k`.
      let m := IsFiltered.max i k
      let ai : i ⟶ m := IsFiltered.leftToMax i k
      let ak : k ⟶ m := IsFiltered.rightToMax i k
      have hs_i : P.diagPushout.map ai ≫ s.ι.app m = s.ι.app i := by
        have := s.ι.naturality ai
        simpa using this
      have hs_k : P.diagPushout.map ak ≫ s.ι.app m = s.ι.app k := by
        have := s.ι.naturality ak
        simpa using this
      have hinl_i : pushout.inl (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map ai ≫ s.ι.app m =
          pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        P.diagPushout_inl_map_assoc ai _
      have hinl_k : pushout.inl (P.ι.app k) (P.ι.app k) ≫ P.diagPushout.map ak ≫ s.ι.app m =
          pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        P.diagPushout_inl_map_assoc ak _
      have eq_i : P.ι.app k ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i =
          P.ι.app k ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        (congrArg (fun X => P.ι.app k ≫ pushout.inl (P.ι.app i) (P.ι.app i) ≫ X) hs_i.symm).trans
          (congrArg (P.ι.app k ≫ ·) hinl_i)
      have eq_k : P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k =
          P.ι.app k ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        (congrArg (fun X => P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ X) hs_k.symm).trans
          (congrArg (P.ι.app k ≫ ·) hinl_k)
      exact eq_k.trans eq_i.symm
    · rw [← Category.assoc, pushout.inr_desc, Category.id_comp]
      apply P.isColimit.hom_ext
      intro k
      have := P.isColimit.fac (P.diagPushoutCoconeDescAux s) k
      rw [this]
      let m := IsFiltered.max i k
      let ai : i ⟶ m := IsFiltered.leftToMax i k
      let ak : k ⟶ m := IsFiltered.rightToMax i k
      have hs_i : P.diagPushout.map ai ≫ s.ι.app m = s.ι.app i := by
        have := s.ι.naturality ai
        simpa using this
      have hs_k : P.diagPushout.map ak ≫ s.ι.app m = s.ι.app k := by
        have := s.ι.naturality ak
        simpa using this
      have hinr_i : pushout.inr (P.ι.app i) (P.ι.app i) ≫ P.diagPushout.map ai ≫ s.ι.app m =
          pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        P.diagPushout_inr_map_assoc ai _
      have hinl_k : pushout.inl (P.ι.app k) (P.ι.app k) ≫ P.diagPushout.map ak ≫ s.ι.app m =
          pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
        P.diagPushout_inl_map_assoc ak _
      -- Now we need pushout.inl ≫ s = pushout.inr ≫ s at the same index `m`,
      -- which holds because `s.ι.app m : pushout(_, _) → s.pt` is one map and
      -- by pushout.condition, inl and inr agree after composing with s.
      -- Actually no — we need to bridge differently for the `inr` case.
      -- For the `inr` case, the goal after `rw [this]` is:
      --   P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k =
      --   P.ι.app k ≫ pushout.inr (P.ι.app i) (P.ι.app i) ≫ s.ι.app i.
      -- Use that pushout.inl m ≫ s_m = pushout.inr m ≫ s_m via:
      --   pi.app m ≫ pushout.inl m = pi.app m ≫ pushout.inr m  (pushout condition)
      --   so pi.app m ≫ pushout.inl m ≫ s_m = pi.app m ≫ pushout.inr m ≫ s_m.
      -- But we don't have pi.app m on the LHS of `eq_k`; we have P.ι.app k.
      -- Bridge using filteredness: pick `m` and use functoriality.
      -- Actually, the LHS goes via inl_k and the RHS via inr_i. These should bridge
      -- through inl_m vs inr_m, which agree after composing with s.ι.app m (since
      -- the cocone's inl/inr identification at m is the multiplication factor).
      -- Specifically, the codiagonal s.ι.app m satisfies pushout.inl _ _ ≫ s.ι.app m
      -- = pushout.inr _ _ ≫ s.ι.app m? No, that's not generally true.
      -- BUT in our diagram, P.ι.app m ≫ inl_m = P.ι.app m ≫ inr_m (pushout.condition).
      -- And P.ι.app k = P.diag.map ak ≫ P.ι.app m (by P.w).
      -- So we can move P.ι.app k inside and use the pushout condition there.
      have hpi : P.diag.map ak ≫ P.ι.app m = P.ι.app k := P.w ak
      have pcond : P.ι.app m ≫ pushout.inl (P.ι.app m) (P.ι.app m) =
          P.ι.app m ≫ pushout.inr (P.ι.app m) (P.ι.app m) := pushout.condition
      have eq_k_via_m : P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ s.ι.app k =
          P.diag.map ak ≫ P.ι.app m ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m := by
        have c1 := congrArg (fun X => P.ι.app k ≫ pushout.inl (P.ι.app k) (P.ι.app k) ≫ X)
          hs_k.symm
        have c2 := congrArg (P.ι.app k ≫ ·) hinl_k
        have c3 : P.ι.app k ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m =
            P.diag.map ak ≫ P.ι.app m ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
          (congrArg (· ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m) hpi.symm).trans
            (Category.assoc _ _ _)
        exact (c1.trans c2).trans c3
      have eq_i_via_m : P.ι.app k ≫ pushout.inr (P.ι.app i) (P.ι.app i) ≫ s.ι.app i =
          P.diag.map ak ≫ P.ι.app m ≫ pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m := by
        have c1 := congrArg (fun X => P.ι.app k ≫ pushout.inr (P.ι.app i) (P.ι.app i) ≫ X)
          hs_i.symm
        have c2 := congrArg (P.ι.app k ≫ ·) hinr_i
        have c3 : P.ι.app k ≫ pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m =
            P.diag.map ak ≫ P.ι.app m ≫ pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m :=
          (congrArg (· ≫ pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m) hpi.symm).trans
            (Category.assoc _ _ _)
        exact (c1.trans c2).trans c3
      have pcond_s : P.diag.map ak ≫ P.ι.app m ≫ pushout.inl (P.ι.app m) (P.ι.app m) ≫ s.ι.app m =
          P.diag.map ak ≫ P.ι.app m ≫ pushout.inr (P.ι.app m) (P.ι.app m) ≫ s.ι.app m := by
        congr 1
        rw [← Category.assoc, pcond, Category.assoc]
      exact (eq_k_via_m.trans pcond_s).trans eq_i_via_m.symm
  uniq s m hm := by
    apply P.isColimit.hom_ext
    intro i
    change P.ι.app i ≫ m = P.ι.app i ≫ P.isColimit.desc (P.diagPushoutCoconeDescAux s)
    rw [P.isColimit.fac]
    change P.ι.app i ≫ m = P.ι.app i ≫ pushout.inl _ _ ≫ s.ι.app i
    have hi := hm i
    -- hi : pushout.desc (𝟙 X) (𝟙 X) rfl ≫ m = s.ι.app i
    have h : m = pushout.inl (P.ι.app i) (P.ι.app i) ≫ s.ι.app i := by
      have := congrArg (pushout.inl (P.ι.app i) (P.ι.app i) ≫ ·) hi
      simpa [P.diagPushoutCocone_app, pushout.inl_desc_assoc] using this
    rw [h]

end CategoryTheory.Limits.ColimitPresentation

namespace RingHom.Flat

variable {R : Type u} [CommRing R]
variable {ι : Type u} [SmallCategory ι] [IsFiltered ι]
variable {S : Type u} [CommRing S] [Algebra R S]

/-- If `S = colim_i Sᵢ` is a filtered colimit in `CommAlgCat R` and each `Sᵢ` is a weakly
étale `R`-algebra (i.e., each `lmul' R : Sᵢ ⊗[R] Sᵢ → Sᵢ` is flat), then
`lmul' R : S ⊗[R] S → S` is also flat.

This is the key colimit-stability lemma used to prove that ind-étale algebras are weakly
étale (since étale implies weakly étale).

The proof reduces to constructing an `IsColimit` witness for the diagonal pushout diagram
`i ↦ pushout (pi.app i) (pi.app i)` in `CommRingCat`, with cocone given by the codiagonals. -/
theorem of_filteredColim_lmul'
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ i, (Algebra.TensorProduct.lmul' R (S := P.diag.obj i)).Flat) :
    (Algebra.TensorProduct.lmul' R (S := S)).Flat := by
  -- 1. Project P to a colim presentation Q in CommRingCat.
  let Q : ColimitPresentation ι (CommRingCat.of S) :=
    P.map (forget₂ (CommAlgCat R) CommRingCat)
  -- The diagram D in CommRingCat and the codiagonal cocone (SR, c).
  let SS : CommRingCat.{u} := CommRingCat.of (S ⊗[R] S)
  let SR : CommRingCat.{u} := CommRingCat.of S
  let lmulMap : SS ⟶ SR :=
    CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := S)).toRingHom
  -- Reduce: it suffices to show lmulMap.hom.Flat.
  suffices hgoal : lmulMap.hom.Flat by exact hgoal
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
      (CommRingCat.ofHom (algebraMap R S)) ⟶ D.obj i := fun i =>
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
    · change pushout.inl (CommRingCat.ofHom (algebraMap R S))
           (CommRingCat.ofHom (algebraMap R S)) ≫
         pushout.desc (pushout.inl (Q.ι.app i) (Q.ι.app i))
           (pushout.inr (Q.ι.app i) (Q.ι.app i)) _ ≫ Q.diagPushout.map h =
       pushout.inl (CommRingCat.ofHom (algebraMap R S))
         (CommRingCat.ofHom (algebraMap R S)) ≫
       pushout.desc (pushout.inl (Q.ι.app j) (Q.ι.app j))
         (pushout.inr (Q.ι.app j) (Q.ι.app j)) _
      simp only [pushout.inl_desc_assoc, pushout.inl_desc]
      exact Q.diagPushout_inl_map h
    · change pushout.inr (CommRingCat.ofHom (algebraMap R S))
           (CommRingCat.ofHom (algebraMap R S)) ≫
         pushout.desc (pushout.inl (Q.ι.app i) (Q.ι.app i))
           (pushout.inr (Q.ι.app i) (Q.ι.app i)) _ ≫ Q.diagPushout.map h =
       pushout.inr (CommRingCat.ofHom (algebraMap R S))
         (CommRingCat.ofHom (algebraMap R S)) ≫
       pushout.desc (pushout.inl (Q.ι.app j) (Q.ι.app j))
         (pushout.inr (Q.ι.app j) (Q.ι.app j)) _
      simp only [pushout.inr_desc_assoc, pushout.inr_desc]
      exact Q.diagPushout_inr_map h
  let t : (Functor.const ι).obj SS ⟶ D :=
    { app := fun i => isoSS.inv ≫ tRaw i
      naturality := fun {i j} h => by
        dsimp
        rw [Category.id_comp, Category.assoc, htRaw_nat h] }
  -- The composition `t.app i ≫ c.app i = lmulMap`.
  have htc_eq : ∀ i, t.app i ≫ c.app i = lmulMap := by
    intro i
    change isoSS.inv ≫ tRaw i ≫ c.app i = lmulMap
    -- tRaw i ≫ c.app i is the codiagonal pushout map on pushout(R → S, R → S).
    have hraw_codiag : tRaw i ≫ c.app i =
        pushout.desc (𝟙 SR) (𝟙 SR) rfl := by
      apply pushout.hom_ext
      · change pushout.inl _ _ ≫ pushout.desc _ _ _ ≫ Q.diagPushoutCocone.app i =
          pushout.inl _ _ ≫ pushout.desc (𝟙 SR) (𝟙 SR) rfl
        rw [pushout.inl_desc_assoc, Q.diagPushoutCocone_app]
        exact (pushout.inl_desc _ _ _).trans (pushout.inl_desc _ _ _).symm
      · change pushout.inr _ _ ≫ pushout.desc _ _ _ ≫ Q.diagPushoutCocone.app i =
          pushout.inr _ _ ≫ pushout.desc (𝟙 SR) (𝟙 SR) rfl
        rw [pushout.inr_desc_assoc, Q.diagPushoutCocone_app]
        exact (pushout.inr_desc _ _ _).trans (pushout.inr_desc _ _ _).symm
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
    haveI : IsScalarTower R (P.diag.obj i) S :=
      IsScalarTower.of_algebraMap_eq fun r => ((P.ι.app i).hom.commutes r).symm
    -- The lift map α : S ⊗[R] S → S ⊗[P.diag.obj i] S as an algebra hom.
    let α : S ⊗[R] S →ₐ[S] S ⊗[P.diag.obj i] S := Algebra.TensorProduct.lift
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (fun _ _ => mul_comm _ _)
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
          change CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
            isoSS.inv ≫ tRaw i = pushout.inl (Q.ι.app i) (Q.ι.app i)
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
          change CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := S) (B := S)).toRingHom ≫
            isoSS.inv ≫ tRaw i = pushout.inr (Q.ι.app i) (Q.ι.app i)
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
    rw [heq]
    change (γ.hom.hom.comp α.toRingHom).Flat
    exact RingHom.Flat.comp hα (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso γ.hom))
  -- Apply of_isColimit.
  exact RingHom.Flat.of_isColimit lmulMap ι D hc
    (fun i => ⟨htflat i, htc_eq i⟩)

end RingHom.Flat
