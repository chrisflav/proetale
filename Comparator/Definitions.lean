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

universe u

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty

instance Ab.hasFilteredColimitsOfSize : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance Ab.ab5OfSize : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

namespace EllAdicEtaleComparison

variable (X : Scheme.{u})

/-! ### The inclusion of the small étale site into the pro-étale site

We equip the inclusion `ν : X.Etale ⥤ X.ProEt` with its continuity and flatness
instances, and record that the associated pullback functor on abelian sheaves is exact.
-/

/-- The inclusion of the small étale site into the pro-étale site. -/
def toProEtale : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

instance : (toProEtale X).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance : (toProEtale X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful

instance : HasFiniteLimits X.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ X)

instance : PreservesFiniteLimits (toProEtale X) := by
  have : PreservesFiniteLimits (toProEtale X ⋙ ProEt.forget X) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ X)
  exact preservesFiniteLimits_of_reflects_of_preserves (toProEtale X) (ProEt.forget X)

instance representablyFlat_toProEtale : RepresentablyFlat (toProEtale X) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the étale site into the pro-étale site is continuous. -/
instance isContinuous_toProEtale :
    (toProEtale X).IsContinuous (smallEtaleTopology X) (ProEt.topology X) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (toProEtale X)) ?_
  refine ⟨fun {Y R} hR ↦ ?_⟩
  rw [ProEt.topology_eq_inducedTopology, Functor.mem_inducedTopology_sieves_iff,
    ← Sieve.functorPushforward_comp]
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ X) ∈ etaleTopology.over X _ := hR
  rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
  exact etaleTopology_le_proetaleTopology _ hR'

/-- The direct image functor `ν_*` from abelian pro-étale sheaves to étale sheaves. -/
abbrev sheafPushforward :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (toProEtale X).sheafPushforwardContinuous _ _ _

instance (F : X.Etaleᵒᵖ ⥤ Ab.{u + 1}) : (toProEtale X).op.HasPointwiseLeftKanExtension F :=
  inferInstance

instance : (sheafPushforward X).IsRightAdjoint := inferInstance

/-- The inverse image functor `ν^*` from abelian étale sheaves to pro-étale sheaves. -/
noncomputable abbrev sheafPullback :
    Sheaf X.smallEtaleTopology Ab.{u + 1} ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (toProEtale X).sheafPullback _ _ _

/-- The adjunction `ν^* ⊣ ν_*`. -/
noncomputable abbrev sheafAdjunction : sheafPullback X ⊣ sheafPushforward X :=
  (toProEtale X).sheafAdjunctionContinuous _ _ _

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

instance : PreservesFiniteLimits (sheafPullback X) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (toProEtale X) Ab.{u + 1}
    (smallEtaleTopology X) (ProEt.topology X)

instance : PreservesFiniteColimits (sheafPullback X) :=
  haveI : PreservesColimitsOfSize.{0, 0} (sheafPullback X) :=
    (sheafAdjunction X).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

instance : (sheafPullback X).Additive := by
  haveI : (sheafPullback X).IsLeftAdjoint := (sheafAdjunction X).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

/-! ### Terminal objects and constant sheaf units -/

/-- `X` with the identity is a terminal object of the small étale site of `X`. -/
noncomputable def isTerminalMkId :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X) : X.Etale) :=
  MorphismProperty.Over.mkIdTerminal _ _

/-- The image of the terminal object of the small étale site of `X` in the pro-étale
site of `X` is terminal. -/
noncomputable def isTerminalMkIdProEt :
    IsTerminal ((toProEtale X).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X))) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantUnit : Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant abelian sheaf `ℤ` on the pro-étale site. -/
noncomputable abbrev proetaleConstantUnit : Sheaf (ProEt.topology X) Ab.{u + 1} :=
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
    extFunctorObj (etaleConstantUnit X) m

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

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafLifted : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafLiftedMap {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheafLifted X M ⟶ topologicalSheafLifted X M' where
  hom :=
    { app := fun U ↦ AddCommGrpCat.uliftFunctor.{u + 1}.map
        (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (fun g ↦ (ContinuousMap.mk f hf).comp g)
            (fun g₁ g₂ ↦ by ext x; exact map_add f _ _)))
      naturality := by
        intro U V h
        apply ConcreteCategory.hom_ext
        intro g
        rfl }

/-- Functoriality of `topologicalSheafLiftedMap` in the coefficient map. -/
lemma topologicalSheafLiftedMap_comp
    {M₂ M₃ : Type} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafLiftedMap X M f hf ≫ topologicalSheafLiftedMap X M₂ g hg =
      topologicalSheafLiftedMap X M (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end Topological

/-- The inverse system `n ↦ (U ↦ C(U, ℤ/ℓⁿℤ))` of abelian sheaves on the pro-étale site
of `X`, with the reduction maps as transition maps. -/
noncomputable def zmodContinuousSystem (ℓ : ℕ) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ topologicalSheafLifted X (ZMod (ℓ ^ n)))
    (fun n ↦ topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology)

/-- The transition maps of `zmodContinuousSystem` are induced by the reduction maps. -/
lemma zmodContinuousSystem_map_succ (ℓ n : ℕ) :
    (zmodContinuousSystem X ℓ).map (homOfLE (Nat.le_succ n)).op =
      topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
        continuous_of_discreteTopology :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The inverse system `n ↦ Hᵐ(X_proét, ℤ/ℓⁿℤ)` of pro-étale cohomology groups of the
sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with transition maps induced by the
reduction maps. -/
noncomputable def proetaleCohomologySystem (ℓ : ℕ) (m : ℕ) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  zmodContinuousSystem X ℓ ⋙ extFunctorObj (proetaleConstantUnit X) m

/-- The value of `proetaleCohomologySystem` at level `n` is the pro-étale cohomology
`Hᵐ(X_proét, ℤ/ℓⁿℤ)` of the sheaf of continuous `ℤ/ℓⁿℤ`-valued functions in the sense
of mathlib's `CategoryTheory.Sheaf.H`. -/
theorem proetaleCohomologySystem_obj (ℓ m n : ℕ) :
    (proetaleCohomologySystem X ℓ m).obj (op n) =
      AddCommGrpCat.of (Sheaf.H (topologicalSheafLifted X (ZMod (ℓ ^ n))) m) :=
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
    (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) ⟶
      topologicalSheafLifted X (ZMod (ℓ ^ n)) :=
  topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
    (continuous_toZModPow ℓ n)

/-- The reduction maps `ellAdicToZModContinuous` assemble into a cone over the system
of sheaves of continuous `ℤ/ℓⁿℤ`-valued functions, with apex the `ℓ`-adic sheaf. -/
noncomputable def ellAdicCone : Cone (zmodContinuousSystem X ℓ) where
  pt := (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)
  π := NatTrans.ofOpSequence
    (app := fun n ↦ ellAdicToZModContinuous X ℓ n)
    (naturality := fun n ↦ by
      simp only [Functor.const_obj_map]
      rw [zmodContinuousSystem_map_succ]
      change topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
          (continuous_toZModPow ℓ n) =
        topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫ _
      rw [topologicalSheafLiftedMap_comp]
      congr 1
      ext x
      exact (RingHom.congr_fun
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) x).symm)

/-- **The canonical map from `ℓ`-adic cohomology to the inverse limit of the pro-étale
cohomology groups with `ℤ/ℓⁿℤ`-coefficients**, induced by the reduction maps
`ℤ_[ℓ] → ℤ/ℓⁿℤ` of coefficient sheaves. -/
noncomputable def ellAdicCohomologyToLimit (m : ℕ) :
    AddCommGrpCat.of (X.EllAdicCohomology ℓ m) ⟶ limit (proetaleCohomologySystem X ℓ m) :=
  limit.lift _ ((extFunctorObj (proetaleConstantUnit X) m).mapCone (ellAdicCone X ℓ))

end Padic

/-! ### The comparison map from étale to pro-étale cohomology -/

/-- The canonical morphism from the constant pro-étale sheaf to the pullback of the
constant étale sheaf, obtained by transposing (along the constant sheaf adjunction of
the pro-étale site) the composite of the unit of the constant sheaf adjunction of the
étale site with the sections of the unit of the adjunction `ν^* ⊣ ν_*`. -/
noncomputable def pullbackConstantComparison (M : AddCommGrpCat.{u + 1}) :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj M ⟶
      (sheafPullback X).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M) :=
  ((constantSheafAdj (ProEt.topology X) Ab.{u + 1} (isTerminalMkIdProEt X)).homEquiv
    _ _).symm
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).unit.app M ≫
      ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
        (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))).map
        ((sheafAdjunction X).unit.app
          ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj M)))

section PullbackToTopological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The constants map `M → C(X, M)` as a morphism into the sections of `ν_*` of the
lifted sheaf of continuous `M`-valued functions over the terminal étale `X`-scheme. -/
noncomputable def constantsToSectionsPushforward :
    AddCommGrpCat.of (ULift.{u + 1} M) ⟶
      ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj
        (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)))).obj
        ((sheafPushforward X).obj (topologicalSheafLifted X M)) :=
  AddCommGrpCat.ofHom
    { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The canonical morphism from the pullback of the constant étale sheaf on `M` to the
sheaf of continuous `M`-valued functions on the pro-étale site: the double transpose
(along `ν^* ⊣ ν_*` and the constant sheaf adjunction of the étale site) of the
constants map `M → C(X, M)`. -/
noncomputable def pullbackConstantToTopological :
    (sheafPullback X).obj ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M))) ⟶
      topologicalSheafLifted X M :=
  ((sheafAdjunction X).homEquiv _ _).symm
    (((constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X)).homEquiv
      _ _).symm (constantsToSectionsPushforward X M))

/-- Naturality of `pullbackConstantToTopological` in the coefficient group. -/
lemma pullbackConstantToTopological_naturality {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    (sheafPullback X).map ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
        (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f))) ≫
      pullbackConstantToTopological X M' =
        pullbackConstantToTopological X M ≫ topologicalSheafLiftedMap X M f hf := by
  unfold pullbackConstantToTopological
  refine Eq.trans (Eq.trans
    ((sheafAdjunction X).homEquiv_naturality_left_symm _ _).symm ?_)
    ((sheafAdjunction X).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((sheafAdjunction X).homEquiv _ _).symm) ?_
  refine Eq.trans (Eq.trans
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (isTerminalMkId X)).homEquiv_naturality_left_symm _ _).symm ?_)
    ((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
      (isTerminalMkId X)).homEquiv_naturality_right_symm _ _)
  refine congrArg ⇑(((constantSheafAdj X.smallEtaleTopology Ab.{u + 1}
    (isTerminalMkId X)).homEquiv _ _).symm) ?_
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
    (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}) ⋙ sheafPullback X ⟶
      zmodContinuousSystem X ℓ :=
  NatTrans.ofOpSequence
    (app := fun n ↦ pullbackConstantToTopological X (ZMod (ℓ ^ n)))
    (naturality := fun n ↦ by
      change (sheafPullback X).map ((constantSheaf _ _).map
          ((zmodAbSystem ℓ).map (homOfLE (n.le_add_right 1)).op)) ≫ _ = _
      rw [zmodAbSystem_map_succ, zmodContinuousSystem_map_succ,
        pullbackConstantToTopological_naturality X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology])

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
          (Ext.mapExactFunctor (sheafPullback X) x) (zero_add m)).comp
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
    change ((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X)
        (x.comp (Ext.mk₀ ((zmodAbSystem ℓ ⋙
          constantSheaf X.smallEtaleTopology Ab.{u + 1}).map f)) (add_zero m)))
          (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k')) (add_zero m) =
      (((Ext.mk₀ _).comp (Ext.mapExactFunctor (sheafPullback X) x) (zero_add m)).comp
          (Ext.mk₀ ((pullbackConstantToTopologicalSystemHom X ℓ).app k)) (add_zero m)).comp
        (Ext.mk₀ ((zmodContinuousSystem X ℓ).map f)) (add_zero m)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    rw [← Functor.comp_map (zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1})
      (sheafPullback X), (pullbackConstantToTopologicalSystemHom X ℓ).naturality f]

end EllAdicEtaleComparison
