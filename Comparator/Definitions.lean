/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Definitions: comparison maps between `ℓ`-adic and étale cohomology

This file provides the definitions shared by the `leanprover/comparator`
challenge/solution pair in this directory (see `Challenge.lean` and `Solution.lean`).
It only imports mathlib.

This file constructs, two canonical comparison maps relating it to the étale
cohomology of the constant sheaves `ℤ/ℓⁿℤ`. The
canonical comparison is the zig-zag

`X.EllAdicCohomology ℓ m ⟶ lim_n Hᵐ(X_proét, ℤ/ℓⁿℤ) ⟵ lim_n Hᵐ(X_ét, ℤ/ℓⁿℤ)`

through the pro-étale cohomology of the sheaves of continuous (equivalently, locally
constant) `ℤ/ℓⁿℤ`-valued functions, defined in exact analogy with mathlib's
`ellAdicSheaf`:

- `EllAdicEtaleComparison.ellAdicCohomologyToLimit`: the first map, induced by the
  reductions `ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves.
- `EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom`: the levelwise second
  map, given by functoriality of `Ext` along the pullback `ν^*` from the small étale
  site to the pro-étale site, together with the canonical comparison morphisms of
  constant sheaves (all obtained from adjunctions).
-/

universe u v w

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty

instance Ab.hasFilteredColimitsOfSize [UnivLE.{u, v}] [UnivLE.{u, w}] [UnivLE.{v, w}] :
    HasFilteredColimitsOfSize.{u, v} Ab.{w} :=
  hasFilteredColimitsOfSize_of_univLE.{u, v, w}

instance Ab.ab5OfSize [UnivLE.{u, v}] [UnivLE.{u, w}] [UnivLE.{v, w}] : AB5OfSize.{u, v} Ab.{w} :=
  AB5OfSize_of_univLE.{u, v, w, w} Ab.{w}

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

variable (X : Scheme.{u})

/-! ### The inclusion of the small étale site into the pro-étale site

We equip the inclusion `ν : X.Etale ⥤ X.ProEt` with its continuity and flatness
instances, and record that the associated pullback functor on abelian sheaves is exact.
-/

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the étale site into the pro-étale site. -/
@[simps! obj_toComma]
def toProEtale (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

variable (S : Scheme.{u})

instance : (toProEtale S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance : (toProEtale S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful

instance : HasFiniteLimits S.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ S)

instance : PreservesFiniteLimits (toProEtale S) := by
  have : PreservesFiniteLimits (toProEtale S ⋙ ProEt.forget S) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ S)
  exact preservesFiniteLimits_of_reflects_of_preserves (toProEtale S) (ProEt.forget S)

instance representablyFlat_toProEtale : RepresentablyFlat (toProEtale S) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the étale site into the pro-étale site is continuous. -/
instance isContinuous_toProEtale :
    (toProEtale S).IsContinuous (smallEtaleTopology S) (ProEt.topology S) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (toProEtale S)) ?_
  refine ⟨fun {X R} hR ↦ ?_⟩
  rw [ProEt.topology_eq_inducedTopology, Functor.mem_inducedTopology_sieves_iff,
    ← Sieve.functorPushforward_comp]
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ S) ∈ etaleTopology.over S _ := hR
  rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
  exact etaleTopology_le_proetaleTopology _ hR'

namespace ProEt

variable (A : Type*) [Category A]

/-- The direct image functor from pro-étale sheafs to étale sheafs. -/
@[simps! obj_obj]
abbrev sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (smallEtaleTopology S) A :=
  (toProEtale S).sheafPushforwardContinuous _ _ _

instance (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) : (toProEtale S).op.HasPointwiseLeftKanExtension F :=
  inferInstance

/-- The direct image functor from pro-étale sheafs to étale sheafs has a left-adjoint. -/
instance : (ProEt.sheafPushforward S Ab.{u + 1}).IsRightAdjoint := inferInstance

variable [(sheafPushforward S A).IsRightAdjoint]

/-- The inverse image functor from étale sheafs to pro-étale sheafs. -/
noncomputable abbrev sheafPullback :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (ProEt.topology S) A :=
  (toProEtale S).sheafPullback _ _ _

/-- The inverse image - direct image adjunction for the pro-étale site. -/
noncomputable abbrev sheafAdjunction :
    ProEt.sheafPullback S A ⊣ ProEt.sheafPushforward S A :=
  (toProEtale S).sheafAdjunctionContinuous _ _ _

end ProEt

end AlgebraicGeometry.Scheme

open AlgebraicGeometry.Scheme ProEt

namespace EllAdicEtaleComparison

section LanEvaluation

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved. -/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (Y : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F Y) E] :
    F.lan ⋙ (evaluation D E).obj Y ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F Y) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ Y).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end LanEvaluation

/-- The left Kan extension of abelian presheaves along the inclusion of the étale site
into the pro-étale site is exact, since the inclusion is representably flat. -/
noncomputable instance preservesFiniteLimits_lan :
    PreservesFiniteLimits ((toProEtale X).op.lan :
      (X.Etaleᵒᵖ ⥤ Ab.{u + 1}) ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1}) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro K
  haveI : IsFiltered (CostructuredArrow (toProEtale X).op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (toProEtale X) (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim' (toProEtale X).op K).symm

instance : PreservesFiniteLimits (sheafPullback X Ab) := by
  infer_instance

instance : PreservesColimitsOfSize.{0, 0} (sheafPullback X Ab) :=
  (sheafAdjunction X Ab).leftAdjoint_preservesColimits

instance : PreservesFiniteColimits (sheafPullback X Ab) := by
  infer_instance

instance : (sheafPullback X Ab).Additive := by
  haveI : (sheafPullback X Ab).IsLeftAdjoint := (sheafAdjunction X Ab).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-! ### Terminal objects and constant sheaf units -/

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantInt : Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant abelian sheaf `ℤ` on the pro-étale site. -/
noncomputable abbrev proetaleConstantInt : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-! ### The étale side: the system of constant sheaves `ℤ/ℓⁿℤ` -/

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

/-- The transition maps of `zmodAbSystem` are the (`ULift`ed) reduction maps. -/
lemma zmodAbSystem_map_succ (ℓ n : ℕ) :
    (zmodAbSystem.{u} ℓ).map (homOfLE (Nat.le_succ n)).op =
      AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom) :=
  congrArg Quiver.Hom.unop
    (Functor.ofSequence_map_homOfLE_succ
      (X := fun n ↦ op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (f := fun n ↦ (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)
      n)

/-- The inverse system `n ↦ Hᵐ(X_ét, ℤ/ℓⁿℤ)` of étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ` on the small étale site of `X`, with transition maps induced by the
reduction maps. Its value at `n` is
`AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab).obj
  (AddCommGrpCat.of (ULift (ZMod (ℓ ^ n))))) m)`. -/
noncomputable def etaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙
    extFunctorObj (etaleConstantInt X) m

/-- The value of `etaleCohomologySystem` at level `n` is the étale cohomology
`Hᵐ(X_ét, ℤ/ℓⁿℤ)` in the sense of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem etaleCohomologySystem_obj (ℓ m n : ℕ) :
    (etaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) m) :=
  rfl

/-! ### The pro-étale side: the system of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions

In analogy with mathlib's `ellAdicSheaf` (`U ↦ C(U, ℤ_[ℓ])`), we consider the sheaves
`U ↦ C(U, ℤ/ℓⁿℤ)` on the pro-étale site of `X`. Since `ℤ/ℓⁿℤ` is discrete, these are
the sheaves of locally constant `ℤ/ℓⁿℤ`-valued functions; their cohomology is the
pro-étale cohomology of `X` with `ℤ/ℓⁿℤ`-coefficients.
-/

section Topological

variable (M : Type v) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{max u v} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb.{v} M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl

/-- Postcomposition with a continuous additive map, as a morphism of the sheaves of
continuous maps. -/
noncomputable def topologicalSheafMap {M' : Type v} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheaf X M ⟶ topologicalSheaf X M' where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun g ↦ (ContinuousMap.mk f hf).comp g)
          (fun g₁ g₂ ↦ by ext x; exact map_add f _ _))
      naturality := by
        intro U V h
        apply ConcreteCategory.hom_ext
        intro g
        rfl }

/-- Functoriality of `topologicalSheafMap` in the coefficient map. -/
lemma topologicalSheafMap_comp
    {M₂ M₃ : Type v} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafMap X M f hf ≫ topologicalSheafMap X M₂ g hg =
      topologicalSheafMap X M (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, as a functor in the coefficient
topological abelian group `M`. On objects it is `topologicalSheaf`, on morphisms
`topologicalSheafMap`. -/
noncomputable def topologicalSheafFunctor :
    TopModuleCat.{v} ℤ ⥤ Sheaf (ProEt.topology X) Ab.{max u v} where
  obj N := topologicalSheaf X N
  map f := topologicalSheafMap X _ f.hom.toLinearMap.toAddMonoidHom f.hom.continuous
  map_id N := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    rfl

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- Universe lifting on sheaves of abelian groups: `Sheaf J Ab.{u} ⥤ Sheaf J Ab.{u + 1}`,
obtained by postcomposition with `AddCommGrpCat.uliftFunctor`. -/
noncomputable def _root_.Sheaf.uliftFunctor : Sheaf J Ab.{u} ⥤ Sheaf J Ab.{max u v} :=
  sheafCompose J AddCommGrpCat.uliftFunctor

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafULift : Sheaf (ProEt.topology X) Ab.{max u v w} :=
  Sheaf.uliftFunctor.obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafULiftMap {M' : Type v} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    Sheaf.uliftFunctor.obj (topologicalSheaf X M) ⟶ topologicalSheafULift X M' :=
  Sheaf.uliftFunctor.map (topologicalSheafMap X M f hf)

/-- Functoriality of `topologicalSheafULiftMap` in the coefficient map. -/
lemma topologicalSheafULiftMap_comp
    {M₂ M₃ : Type v} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafULiftMap X M f hf ≫ topologicalSheafULiftMap X M₂ g hg =
      topologicalSheafULiftMap X M (g.comp f) (hg.comp hf) := by
  simp only [topologicalSheafULiftMap, ← topologicalSheafMap_comp X M f hf g hg]
  exact Sheaf.uliftFunctor.map_comp
    (topologicalSheafMap X M f hf) (topologicalSheafMap X M₂ g hg)

end Topological

/-- The inverse system `n ↦ ℤ/ℓⁿℤ` of (discrete) topological abelian groups, with the
reduction maps as transition maps. -/
noncomputable def zmodTopSystem (ℓ : ℕ) : ℕᵒᵖ ⥤ TopModuleCat.{0} ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ TopModuleCat.of ℤ (ZMod (ℓ ^ n)))
    (fun n ↦ TopModuleCat.ofHom
      { toLinearMap := (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
          (ZMod (ℓ ^ n))).toAddMonoidHom.toIntLinearMap
        cont := continuous_of_discreteTopology })

/-- The inverse system `n ↦ (U ↦ C(U, ℤ/ℓⁿℤ))` of abelian sheaves on the pro-étale site
of `X`, with the reduction maps as transition maps. It is the composition of the system
of coefficient groups `zmodTopSystem` with the (lifted) sheaf-of-continuous-functions
functor. -/
noncomputable def zmodContinuousSystem (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{max u v} :=
  zmodTopSystem ℓ ⋙ topologicalSheafFunctor.{u, 0} X ⋙ Sheaf.uliftFunctor.{u, v}

/-- The transition maps of `zmodContinuousSystem` are induced by the reduction maps. -/
lemma zmodContinuousSystem_map_succ (ℓ n : ℕ) :
    (zmodContinuousSystem X ℓ).map (homOfLE (Nat.le_succ n)).op =
      Sheaf.uliftFunctor.map (topologicalSheafMap X (ZMod (ℓ ^ (n + 1)))
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
        continuous_of_discreteTopology) := by
  simp only [zmodContinuousSystem, Functor.comp_map, zmodTopSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- The inverse system `n ↦ Hᵐ(X_proét, ℤ/ℓⁿℤ)` of pro-étale cohomology groups of the
sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with transition maps induced by the
reduction maps. -/
noncomputable def proetaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  zmodContinuousSystem.{u, u + 1} X ℓ ⋙ extFunctorObj (proetaleConstantInt X) m

/-- The value of `proetaleCohomologySystem` at level `n` is the pro-étale cohomology
`Hᵐ(X_proét, ℤ/ℓⁿℤ)` of the sheaf of continuous `ℤ/ℓⁿℤ`-valued functions in the sense
of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem proetaleCohomologySystem_obj (ℓ m n : ℕ) :
    (proetaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H (topologicalSheafULift.{u, 0, u + 1} X (ZMod (ℓ ^ n))) m) :=
  rfl

/-! ### The reduction map from `ℓ`-adic cohomology to the limit -/

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The projections `ℤ_[ℓ] → ℤ/ℓⁿℤ` are continuous: their fibers are unions of balls
of radius `ℓ⁻ⁿ`. -/
lemma continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  have hℓ : (0 : ℝ) < (ℓ : ℝ) := by
    exact_mod_cast (Fact.out (p := ℓ.Prime)).pos
  refine continuous_def.mpr fun s _ ↦ Metric.isOpen_iff.mpr fun x hx ↦ ?_
  refine ⟨(ℓ : ℝ) ^ (-(n : ℤ) + 1), zpow_pos hℓ _, fun y hy ↦ ?_⟩
  have h1 : ‖y - x‖ < (ℓ : ℝ) ^ (-(n : ℤ) + 1) := by
    rw [← dist_eq_norm]
    exact hy
  have h2 : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (y - x) (-(n : ℤ))).mpr h1
  have h3 : PadicInt.toZModPow (p := ℓ) n (y - x) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp h2
  have h4 : PadicInt.toZModPow (p := ℓ) n y = PadicInt.toZModPow (p := ℓ) n x := by
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  change PadicInt.toZModPow (p := ℓ) n y ∈ s
  rw [h4]
  exact hx

/-- The reduction map from the (`ULift`ed) `ℓ`-adic sheaf to the sheaf of continuous
`ℤ/ℓⁿℤ`-valued functions, induced by `PadicInt.toZModPow`. -/
noncomputable def ellAdicToZModContinuous (n : ℕ) :
    Sheaf.uliftFunctor.obj (X.ellAdicSheaf ℓ) ⟶
      Sheaf.uliftFunctor.obj (topologicalSheaf X (ZMod (ℓ ^ n))) :=
  topologicalSheafULiftMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
    (continuous_toZModPow ℓ n)

/-- The reduction maps `ellAdicToZModContinuous` assemble into a cone over the system
of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with apex the `ℓ`-adic sheaf. -/
noncomputable def ellAdicCone : Cone (zmodContinuousSystem X ℓ) where
  pt := topologicalSheafULift.{u, 0, u + 1} X ℤ_[ℓ]
  π := NatTrans.ofOpSequence
    (app := fun n ↦ ellAdicToZModContinuous X ℓ n)
    (naturality := fun n ↦ by
      simp only [Functor.const_obj_map]
      rw [zmodContinuousSystem_map_succ]
      change topologicalSheafULiftMap .. =
        topologicalSheafULiftMap .. ≫ topologicalSheafULiftMap ..
      rw [topologicalSheafULiftMap_comp]
      congr 1
      ext x
      exact (RingHom.congr_fun
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) x).symm)

/-- **The canonical map from `ℓ`-adic cohomology to the inverse limit of the pro-étale
cohomology groups with `ℤ/ℓⁿℤ`-coefficients**, induced by the reduction maps
`ℤ_[ℓ] → ℤ/ℓⁿℤ` of coefficient sheaves. -/
noncomputable def ellAdicCohomologyToLimit (m : ℕ) :
    AddCommGrpCat.of (X.EllAdicCohomology ℓ m) ⟶ limit (proetaleCohomologySystem X ℓ m) :=
  limit.lift _ ((extFunctorObj (proetaleConstantInt X) m).mapCone (ellAdicCone X ℓ))

end Padic

/-! ### The comparison map from étale to pro-étale cohomology -/

/-- The canonical morphism from the constant pro-étale sheaf to the pullback of the
constant étale sheaf, obtained by transposing (along the constant sheaf adjunction of
the pro-étale site) the composite of the unit of the constant sheaf adjunction of the
étale site with the sections of the unit of the adjunction `ν^* ⊣ ν_*`. -/
noncomputable def pullbackConstantComparison (M : AddCommGrpCat.{u + 1}) :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj M ⟶
      (sheafPullback X Ab).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M) :=
  ((constantSheafAdj (ProEt.topology X) Ab.{u + 1} (Over.mkIdTerminal _ _)).homEquiv _ _).symm
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (Over.mkIdTerminal _ _)).unit.app M ≫
        ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
          (op (Over.mk ⊤ (𝟙 X) (id_mem _ X)))).map ((sheafAdjunction X Ab).unit.app
            ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)))

section PullbackToTopological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The constants map `M → C(X, M)` as a morphism into the sections of `ν_*` of the
lifted sheaf of continuous `M`-valued functions over the terminal étale `X`-scheme. -/
noncomputable def constantsToSectionsPushforward :
    AddCommGrpCat.of (ULift.{u + 1} M) ⟶
      ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
        (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))).obj
        ((sheafPushforward X Ab).obj (topologicalSheafULift.{u, 0, u + 1} X M)) :=
  AddCommGrpCat.ofHom
    { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The canonical morphism from the pullback of the constant étale sheaf on `M` to the
sheaf of continuous `M`-valued functions on the pro-étale site: the double transpose
(along `ν^* ⊣ ν_*` and the constant sheaf adjunction of the étale site) of the
constants map `M → C(X, M)`. -/
noncomputable def pullbackConstantToTopological :
    (sheafPullback X Ab).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M))) ⟶
      topologicalSheafULift.{u, 0, u + 1} X M :=
  ((sheafAdjunction X Ab).homEquiv _ _).symm
    (((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (Over.mkIdTerminal _ _)).homEquiv
      _ _).symm (constantsToSectionsPushforward X M))

/-- Naturality of `pullbackConstantToTopological` in the coefficient group. -/
lemma pullbackConstantToTopological_naturality {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    (sheafPullback X Ab).map ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
        (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f))) ≫
      pullbackConstantToTopological X M' =
        pullbackConstantToTopological X M ≫ topologicalSheafULiftMap X M f hf := by
  unfold pullbackConstantToTopological
  refine Eq.trans (Eq.trans
    ((sheafAdjunction X Ab).homEquiv_naturality_left_symm _ _).symm ?_)
    ((sheafAdjunction X Ab).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((sheafAdjunction X Ab).homEquiv _ _).symm) ?_
  refine Eq.trans (Eq.trans
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (Over.mkIdTerminal _ _)).homEquiv_naturality_left_symm _ _).symm ?_)
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (Over.mkIdTerminal _ _)).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (Over.mkIdTerminal _ _)).homEquiv _ _).symm) ?_
  apply ConcreteCategory.hom_ext
  intro m
  rfl

end PullbackToTopological

/-- The sheaf-level comparison: the canonical morphism of inverse systems from the
pullbacks of the constant étale sheaves `ℤ/ℓⁿℤ` to the sheaves of continuous
`ℤ/ℓⁿℤ`-valued functions on the pro-étale site. Each component is an isomorphism
("locally constant = continuous into a discrete group"), but this is a theorem
(BS, Lemma 4.2.12) and not part of the definition. -/
noncomputable def pullbackConstantToTopologicalSystemHom (ℓ : ℕ) :
    (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙ sheafPullback X Ab ⟶
      zmodContinuousSystem.{u, u + 1} X ℓ :=
  NatTrans.ofOpSequence
    (app := fun n ↦ pullbackConstantToTopological X (ZMod (ℓ ^ n)))
    (naturality := fun n ↦ by
      change (sheafPullback X Ab).map ((constantSheaf _ _).map
          ((zmodAbSystem ℓ).map (homOfLE (n.le_add_right 1)).op)) ≫ _ = _
      rw [zmodAbSystem_map_succ, zmodContinuousSystem_map_succ,
        pullbackConstantToTopological_naturality X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology]
      cat_disch)

/-- **The canonical comparison map from étale to pro-étale cohomology with
`ℤ/ℓⁿℤ`-coefficients**, as a morphism of inverse systems: on each level it is given by
the functoriality of `Ext`-groups along the exact functor `ν^*` together with the
canonical constant sheaf comparisons `pullbackConstantComparison` (on the cohomological
unit) and `pullbackConstantToTopological` (on the coefficients). -/
noncomputable def etaleToProetaleCohomologySystemHom (ℓ m : ℕ) :
    etaleCohomologySystem X ℓ m ⟶ proetaleCohomologySystem X ℓ m where
  app k := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ((Ext.mk₀ (pullbackConstantComparison X
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).comp
          (Ext.mapExactFunctor (sheafPullback X Ab) x) (zero_add m)).comp
        (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k)) (add_zero m)
      map_zero' := by
        rw [Ext.mapExactFunctor_zero, Ext.comp_zero, Ext.zero_comp]
      map_add' := fun x y ↦ by
        rw [Ext.mapExactFunctor_add, Ext.comp_add, Ext.add_comp] }
  naturality {k k'} f := by
    apply ConcreteCategory.hom_ext
    intro x
    refine (ConcreteCategory.comp_apply _ _ _).trans
      (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm)
    change ((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X Ab)
        (x.comp (Ext.mk₀ ((zmodAbSystem ℓ ⋙
          constantSheaf X.smallEtaleTopology Ab.{u + 1}).map f)) (add_zero m)))
          (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k')) (add_zero m) =
      (((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X Ab) x) (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k)) (add_zero m)).comp
        (Ext.mk₀ ((zmodContinuousSystem X ℓ).map f)) (add_zero m)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    rw [← Functor.comp_map (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (sheafPullback X Ab), (pullbackConstantToTopologicalSystemHom X ℓ).naturality f]

end EllAdicEtaleComparison
