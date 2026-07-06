/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Definitions
import Proetale.Topology.Comparison.EllAdicLimit
import Proetale.Topology.Comparison.LimitComparison

/-!
# The canonical comparison maps between `ℓ`-adic and étale cohomology

This file proves the theorems of the comparator challenge (`Comparator/Challenge.lean`)
about the canonical comparison maps constructed in the mathlib-only shared definitions
file `Comparator/Definitions.lean` (namespace `EllAdicEtaleComparison`):

- `AlgebraicGeometry.Scheme.ProEt.bijective_etaleToProetaleCohomology`: the canonical
  comparison map from étale to pro-étale cohomology with `ℤ/ℓⁿℤ`-coefficients is
  bijective in every degree (BS, Corollary 5.1.6).
- `AlgebraicGeometry.Scheme.ProEt.bijective_ellAdicCohomologyToLimit_of_finite`: the
  canonical map from `ℓ`-adic cohomology to the inverse limit of the pro-étale
  cohomology groups of `ℤ/ℓⁿℤ` is bijective in degree `i + 1` whenever the étale
  cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite.
- `AlgebraicGeometry.Scheme.ProEt.existsUnique_ellAdicCohomology_addEquiv_limit_of_finite`:
  consequently there is a unique additive equivalence between `ℓ`-adic cohomology and
  the inverse limit of the étale cohomology groups compatible with the two canonical
  maps.

The definitions in `EllAdicEtaleComparison` are definitionally equal to the
corresponding constructions of this repository (`toProEtale`, `ProEt.sheafPullback`,
`ProEt.topologicalSheafLifted`, ...); the two agreement lemmas
`pullbackConstantToTopological_eq` and `pullbackConstantComparison_eq` identify the
adjunction-theoretic canonical constant sheaf comparisons of `Definitions.lean` with
the isomorphisms `ProEt.sheafPullbackConstantTopologicalIso` and
`ProEt.sheafPullbackConstantIso` of this repository. Everything else is assembled from
`ProEt.mapExt_bijective_sheafPullback` (étale/pro-étale comparison),
`ellAdicSheafLimitIso` (the `ℓ`-adic sheaf as a limit) and the canonical-map limit
comparison `ProEt.bijective_extLimitToLimit_of_isMittagLeffler`
(`Proetale/Topology/Comparison/LimitComparison.lean`).
-/

universe u

open CategoryTheory Limits Opposite Abelian

section Mates

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Conjugation intertwines the hom-set transposes of two adjunctions: precomposition
with the conjugate of `β` transposes to postcomposition with `β`. -/
lemma conjugateEquiv_symm_app_comp_homEquiv_symm (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : R₁ ⟶ R₂) {X : C} {Y : D} (g : X ⟶ R₁.obj Y) :
    ((conjugateEquiv adj₁ adj₂).symm β).app X ≫ (adj₁.homEquiv X Y).symm g =
      (adj₂.homEquiv X Y).symm (g ≫ β.app Y) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, conjugateEquiv_counit_symm adj₁ adj₂ β Y, ← Category.assoc,
    ← NatTrans.naturality, Category.assoc]

end Mates

namespace AlgebraicGeometry.Scheme.ProEt

variable (X : Scheme.{u})

/-! ### Agreement of the canonical constant sheaf comparisons -/

/-- The canonical morphism `EllAdicEtaleComparison.pullbackConstantToTopological` from
the pullback of the constant étale sheaf to the sheaf of continuous functions agrees
with the comparison isomorphism `ProEt.sheafPullbackConstantTopologicalIso`. -/
lemma pullbackConstantToTopological_eq (M : Type) [TopologicalSpace M] [AddCommGroup M]
    [IsTopologicalAddGroup M] [DiscreteTopology M] :
    EllAdicEtaleComparison.pullbackConstantToTopological X M =
      (sheafPullbackConstantTopologicalIso X M).hom := by
  -- Both sides are transposes of the "constants" map `M → C(X, M)`:
  -- `sheafPullbackConstantIso` is a conjugate isomorphism
  -- (`constantSheafCompSheafPullbackIso`, via `conjugateIsoEquiv` between the composed
  -- adjunction `(constantSheafAdj J).comp (sheafAdjunctionContinuous)` and
  -- `constantSheafAdj K`), so by the mate calculus
  -- (`conjugateEquiv_symm_app_comp_homEquiv_symm`) precomposing the transpose of the
  -- constants map under `constantSheafAdj K` with it yields the transpose under the
  -- composed adjunction, which is the double transpose defining
  -- `pullbackConstantToTopological`.
  have h := conjugateEquiv_symm_app_comp_homEquiv_symm
    (constantSheafAdj (ProEt.topology X) Ab.{u + 1} (isTerminalMkIdProEt X))
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).comp
      ((toProEtale X).sheafAdjunctionContinuous Ab.{u + 1} X.smallEtaleTopology
        (ProEt.topology X)))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)).inv
    (X := AddCommGrpCat.of (ULift.{u + 1} M))
    (Y := topologicalSheafLifted X M)
    (g := AddCommGrpCat.ofHom
      { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })
  simp only [NatIso.ofComponents_inv_app, Iso.refl_inv, Category.comp_id] at h
  rw [Adjunction.comp_homEquiv] at h
  simp only [Equiv.symm_trans_apply] at h
  have h1 : (sheafPullbackConstantTopologicalIso X M).hom =
      (sheafPullbackConstantIso X (AddCommGrpCat.of (ULift.{u + 1} M))).hom ≫
        constantToTopologicalSheafLifted X M := rfl
  rw [h1]
  exact h.symm

/-- The canonical morphism `EllAdicEtaleComparison.pullbackConstantComparison` from the
constant pro-étale sheaf to the pullback of the constant étale sheaf agrees with the
inverse of the comparison isomorphism `ProEt.sheafPullbackConstantIso`. -/
lemma pullbackConstantComparison_eq (M : AddCommGrpCat.{u + 1}) :
    EllAdicEtaleComparison.pullbackConstantComparison X M =
      (sheafPullbackConstantIso X M).inv := by
  -- The transpose of the conjugate isomorphism under `constantSheafAdj K` is the unit
  -- of the composed adjunction (`unit_conjugateEquiv_symm`), and `comp_unit_app`
  -- identifies the latter with the composite defining `pullbackConstantComparison`.
  have h := unit_conjugateEquiv_symm
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).comp
      ((toProEtale X).sheafAdjunctionContinuous Ab.{u + 1} X.smallEtaleTopology
        (ProEt.topology X)))
    (constantSheafAdj (ProEt.topology X) Ab.{u + 1} (isTerminalMkIdProEt X))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _)).hom M
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom] at h
  have h2 : (constantSheafAdj (ProEt.topology X) Ab.{u + 1}
      (isTerminalMkIdProEt X)).homEquiv M _
      (((conjugateEquiv ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
        (isTerminalMkId X)).comp ((toProEtale X).sheafAdjunctionContinuous Ab.{u + 1}
          X.smallEtaleTopology (ProEt.topology X)))
        (constantSheafAdj (ProEt.topology X) Ab.{u + 1}
          (isTerminalMkIdProEt X))).symm
        (NatIso.ofComponents (fun _ ↦ Iso.refl _)).hom).app M) =
      ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).comp
        ((toProEtale X).sheafAdjunctionContinuous Ab.{u + 1} X.smallEtaleTopology
          (ProEt.topology X))).unit.app M := by
    rw [Adjunction.homEquiv_unit]
    exact h.symm
  have E : (sheafPullbackConstantIso X M).inv =
      ((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
        (isTerminalMkIdProEt X)).homEquiv M _).symm
        (((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).comp
          ((toProEtale X).sheafAdjunctionContinuous Ab.{u + 1} X.smallEtaleTopology
            (ProEt.topology X))).unit.app M) := by
    rw [← h2, Equiv.symm_apply_apply]
    rfl
  rw [E, Adjunction.comp_unit_app]
  rfl

instance (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
    [DiscreteTopology M] :
    IsIso (EllAdicEtaleComparison.pullbackConstantToTopological X M) := by
  rw [pullbackConstantToTopological_eq]
  infer_instance

instance (M : AddCommGrpCat.{u + 1}) :
    IsIso (EllAdicEtaleComparison.pullbackConstantComparison X M) := by
  rw [pullbackConstantComparison_eq]
  infer_instance

/-! ### The levelwise comparison of étale and pro-étale cohomology -/

/-- Postcomposition with (the degree zero class of) an isomorphism is a bijection on
`Ext`-groups. -/
lemma bijective_comp_mk₀ {A : Type*} [Category A] [Abelian A] [HasExt.{u + 1} A]
    {Z B B' : A} (w : B ⟶ B') [IsIso w] (m : ℕ) :
    Function.Bijective (fun x : Ext Z B m ↦ x.comp (Ext.mk₀ w) (add_zero m)) := by
  constructor
  · intro x y hxy
    have h := congrArg (fun t : Ext Z B' m ↦ t.comp (Ext.mk₀ (inv w)) (add_zero m)) hxy
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.hom_inv_id,
      Ext.comp_mk₀_id] using h
  · intro y
    refine ⟨y.comp (Ext.mk₀ (inv w)) (add_zero m), ?_⟩
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, IsIso.inv_hom_id,
      Ext.comp_mk₀_id]

/-- **Étale and pro-étale cohomology with `ℤ/ℓⁿℤ`-coefficients agree**: the canonical
comparison map of `Definitions.lean` is bijective in every degree
(BS, Corollary 5.1.6). -/
theorem bijective_etaleToProetaleCohomology (ℓ m n : ℕ) :
    Function.Bijective (ConcreteCategory.hom
      ((EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ m).app (op n))) := by
  have h1 : Function.Bijective (Ext.mapExactFunctor
      (EllAdicEtaleComparison.sheafPullback X)
      (X := EllAdicEtaleComparison.etaleConstantUnit X)
      (Y := (EllAdicEtaleComparison.zmodAbSystem ℓ ⋙
        constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (op n)) (n := m)) :=
    mapExt_bijective_sheafPullback _ _ m
  have h2 := (Ext.precompAddEquiv (asIso (EllAdicEtaleComparison.pullbackConstantComparison
    X (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
    ((EllAdicEtaleComparison.sheafPullback X).obj
      ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))) m).bijective
  haveI : IsIso
      ((EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ).app (op n)) :=
    inferInstanceAs (IsIso
      (EllAdicEtaleComparison.pullbackConstantToTopological X (ZMod (ℓ ^ n))))
  have h3 := bijective_comp_mk₀
    (Z := EllAdicEtaleComparison.proetaleConstantUnit X)
    ((EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ).app (op n)) m
  exact h3.comp (h2.comp h1)

/-! ### The canonical map from `ℓ`-adic cohomology to the limit -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The canonical map `EllAdicEtaleComparison.ellAdicCohomologyToLimit` factors as the
identification of the `ℓ`-adic sheaf with the limit of the pulled-back constant sheaves
(`ellAdicSheafLimitIso`), followed by the canonical limit comparison map
(`Ext.extLimitToLimit`), followed by the comparison of the pulled-back constant sheaves
with the sheaves of continuous functions. -/
lemma ellAdicCohomologyToLimit_eq (m : ℕ) :
    EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ m =
      (extFunctorObj (proetaleConstantUnit X) m).map (ellAdicSheafLimitIso X ℓ).hom ≫
        Ext.extLimitToLimit (proetaleConstantUnit X)
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) m ≫
        limMap (Functor.whiskerRight
          (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ)
          (extFunctorObj (proetaleConstantUnit X) m)) := by
  apply limit.hom_ext
  intro k
  have hsheaf : (EllAdicEtaleComparison.ellAdicCone X ℓ).π.app k =
      (ellAdicSheafLimitIso X ℓ).hom ≫
        limit.π (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) k ≫
        (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ).app k := by
    have hπ := ellAdicSheafLimitIso_hom_π X ℓ k.unop
    calc (EllAdicEtaleComparison.ellAdicCone X ℓ).π.app k
        = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow k.unop).toAddMonoidHom
            (continuous_toZModPow ℓ k.unop) ≫
            (sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ k.unop))).inv ≫
            (sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ k.unop))).hom := by
          rw [Iso.inv_hom_id, Category.comp_id]
          rfl
      _ = ((ellAdicSheafLimitIso X ℓ).hom ≫
            limit.π (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) (op k.unop)) ≫
            (sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ k.unop))).hom := by
          rw [← Category.assoc, hπ]
      _ = (ellAdicSheafLimitIso X ℓ).hom ≫
            limit.π (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) k ≫
            (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ).app k := by
          rw [Category.assoc, ← pullbackConstantToTopological_eq]
          rfl
  have hlift : EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ m ≫
      limit.π (EllAdicEtaleComparison.proetaleCohomologySystem X ℓ m) k =
      (extFunctorObj (proetaleConstantUnit X) m).map
        ((EllAdicEtaleComparison.ellAdicCone X ℓ).π.app k) :=
    limit.lift_π _ _
  have hmap : limMap (Functor.whiskerRight
      (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ)
      (extFunctorObj (proetaleConstantUnit X) m)) ≫
      limit.π (EllAdicEtaleComparison.proetaleCohomologySystem X ℓ m) k =
      limit.π (Ext.levelSystem (proetaleConstantUnit X)
        (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) m) k ≫
      (extFunctorObj (proetaleConstantUnit X) m).map
        ((EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ).app k) :=
    limMap_π _ _
  rw [hlift, hsheaf, Category.assoc, Category.assoc, hmap, Functor.map_comp,
    Functor.map_comp, Ext.extLimitToLimit_π_assoc]

/-- **`ℓ`-adic cohomology is the inverse limit of the pro-étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees: the canonical map of `Definitions.lean` induced by the
reductions `ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves is bijective in degree `i + 1`,
whenever the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite. -/
theorem bijective_ellAdicCohomologyToLimit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType
      ((EllAdicEtaleComparison.etaleCohomologySystem X ℓ i).obj (op n)))) :
    Function.Bijective (ConcreteCategory.hom
      (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1))) := by
  -- The pro-étale level system consists of finite groups, hence is Mittag-Leffler.
  have hfin' : ∀ n : ℕ, Finite (ToType ((Ext.levelSystem (proetaleConstantUnit X)
      (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) i).obj (op n))) := by
    intro n
    haveI : Finite (Ext (etaleConstantUnit X) ((zmodSystem X ℓ).obj (op n)) i) := hfin n
    exact Finite.of_equiv _
      ((Equiv.ofBijective _ (mapExt_bijective_sheafPullback
          (etaleConstantUnit X) ((zmodSystem X ℓ).obj (op n)) i)).trans
        (Ext.precompAddEquiv (asIso (EllAdicEtaleComparison.pullbackConstantComparison
          X (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
          ((ProEt.sheafPullback X Ab.{u + 1}).obj ((zmodSystem X ℓ).obj (op n)))
          i).toEquiv)
  have hML := Ext.isMittagLeffler_forget_of_finite _ hfin'
  haveI h1 : IsIso ((extFunctorObj (proetaleConstantUnit X) (i + 1)).map
      (ellAdicSheafLimitIso X ℓ).hom) := inferInstance
  haveI h2 : IsIso (Ext.extLimitToLimit (proetaleConstantUnit X)
      (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) (i + 1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_extLimitToLimit_of_isMittagLeffler (zmodSystem X ℓ)
        (epi_transition_zmodSystem X ℓ) i hML)
  haveI h3 : IsIso (Functor.whiskerRight
      (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ)
      (extFunctorObj (proetaleConstantUnit X) (i + 1))) := by
    haveI : ∀ k : ℕᵒᵖ, IsIso ((Functor.whiskerRight
        (EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom X ℓ)
        (extFunctorObj (proetaleConstantUnit X) (i + 1))).app k) := by
      intro k
      haveI : IsIso ((EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom
          X ℓ).app k) :=
        inferInstanceAs (IsIso
          (EllAdicEtaleComparison.pullbackConstantToTopological X (ZMod (ℓ ^ k.unop))))
      exact inferInstanceAs (IsIso ((extFunctorObj (proetaleConstantUnit X)
        (i + 1)).map ((EllAdicEtaleComparison.pullbackConstantToTopologicalSystemHom
          X ℓ).app k)))
    exact NatIso.isIso_of_isIso_app _
  rw [ellAdicCohomologyToLimit_eq]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-! ### The unique compatible equivalence -/

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, whenever the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)`
one degree lower are finite: there is a unique additive equivalence compatible with the
canonical comparison maps into the inverse limit of the pro-étale cohomology groups. -/
theorem existsUnique_ellAdicCohomology_addEquiv_limit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType
      ((EllAdicEtaleComparison.etaleCohomologySystem X ℓ i).obj (op n)))) :
    ∃! e : X.EllAdicCohomology ℓ (i + 1) ≃+
        ↥(limit (EllAdicEtaleComparison.etaleCohomologySystem X ℓ (i + 1))),
      ∀ x, ConcreteCategory.hom (limMap
          (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))
          (e x) =
        ConcreteCategory.hom
          (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1)) x := by
  have hρ := bijective_ellAdicCohomologyToLimit_of_finite X ℓ i hfin
  have hlim : Function.Bijective (ConcreteCategory.hom (limMap
      (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))) := by
    haveI : ∀ k : ℕᵒᵖ, IsIso
        ((EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)).app k) :=
      fun k ↦ (ConcreteCategory.isIso_iff_bijective _).mpr
        (bijective_etaleToProetaleCohomology X ℓ (i + 1) k.unop)
    haveI : IsIso (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)) :=
      NatIso.isIso_of_isIso_app _
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  set e₁ := AddEquiv.ofBijective (ConcreteCategory.hom
    (EllAdicEtaleComparison.ellAdicCohomologyToLimit X ℓ (i + 1))) hρ with he₁
  set e₂ := AddEquiv.ofBijective (ConcreteCategory.hom (limMap
    (EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom X ℓ (i + 1)))) hlim
    with he₂
  refine ⟨e₁.trans e₂.symm, fun x ↦ ?_, fun e' he' ↦ ?_⟩
  · exact e₂.apply_symm_apply (e₁ x)
  · ext x
    apply e₂.injective
    exact (he' x).trans (e₂.apply_symm_apply (e₁ x)).symm

end AlgebraicGeometry.Scheme.ProEt
