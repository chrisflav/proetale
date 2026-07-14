/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology

/-!
# The sheaf of continuous functions on the pro-étale site

For a scheme `X` and a topological abelian group `M`, we define the sheaf
`AlgebraicGeometry.Scheme.topologicalSheaf X M` on the pro-étale site of `X`, sending an
object `U` to the group `C(U, M)` of continuous `M`-valued functions. This is the direct
generalization of mathlib's `AlgebraicGeometry.Scheme.ellAdicSheaf`, which is the special
case `M = ℤ_[ℓ]` (`ellAdicSheaf_eq_topologicalSheaf`).

Its functoriality in continuous additive maps of the coefficient group is `topologicalSheafMap`.
We also provide the `ULift`ed variant `topologicalSheafLifted X M` valued in `Ab.{u + 1}`,
together with its functoriality `topologicalSheafLiftedMap`, obtained by applying the universe
lifting functor `CategoryTheory.Sheaf.uliftFunctor` to the unlifted data.

These are used to spell out the pro-étale cohomology of `X` with `ℤ/ℓⁿℤ`-coefficients (the
sheaves of continuous, equivalently locally constant, `ℤ/ℓⁿℤ`-valued functions) in exact
analogy with the `ℓ`-adic coefficient sheaf.
-/

universe u

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C)

/-- Universe lifting on sheaves of abelian groups: `Sheaf J Ab.{u} ⥤ Sheaf J Ab.{u + 1}`,
obtained by postcomposition with `AddCommGrpCat.uliftFunctor`. -/
noncomputable def uliftFunctor : Sheaf J Ab.{u} ⥤ Sheaf J Ab.{u + 1} :=
  sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1}

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

section Topological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally, see
`ellAdicSheaf_eq_topologicalSheaf`). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl

/-- Postcomposition with a continuous additive map, as a morphism of the sheaves of
continuous maps. -/
noncomputable def topologicalSheafMap {M' : Type} [TopologicalSpace M']
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
    {M₂ M₃ : Type} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
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

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafLifted : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (Sheaf.uliftFunctor _).obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafLiftedMap {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheafLifted X M ⟶ topologicalSheafLifted X M' :=
  (Sheaf.uliftFunctor _).map (topologicalSheafMap X M f hf)

/-- Functoriality of `topologicalSheafLiftedMap` in the coefficient map. -/
lemma topologicalSheafLiftedMap_comp
    {M₂ M₃ : Type} [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafLiftedMap X M f hf ≫ topologicalSheafLiftedMap X M₂ g hg =
      topologicalSheafLiftedMap X M (g.comp f) (hg.comp hf) := by
  simp only [topologicalSheafLiftedMap, ← topologicalSheafMap_comp X M f hf g hg]
  exact (Sheaf.uliftFunctor (ProEt.topology X)).map_comp
    (topologicalSheafMap X M f hf) (topologicalSheafMap X M₂ g hg)

end Topological

end AlgebraicGeometry.Scheme
