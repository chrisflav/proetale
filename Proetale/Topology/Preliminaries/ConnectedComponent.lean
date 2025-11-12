/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Connected Components Factors Through Maps to Totally Disconnected Spaces

-/
-- TODO: Should upgrade `ConnectedComponents.mk` to `ContinuousMap`
namespace ConnectedComponents

theorem factorsThrough_mk {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (f : C(X, Y)) : Function.FactorsThrough f mk := by
  intro x y h
  simp only [coe_eq_coe] at h
  rw [← Set.singleton_eq_singleton_iff, ← Continuous.image_connectedComponent_eq_singleton, h, Continuous.image_connectedComponent_eq_singleton]
  exacts [f.2, f.2]

/--
If \(f: X \to Y\) is a continuous map and \(Y\) is totally disconnected, then \(f\) factors uniquely
through the connected components of \(X\).
-/
@[stacks 08ZL]
noncomputable def lift {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (f : C(X, Y)) :
    C(ConnectedComponents X, Y) :=
  Topology.IsQuotientMap.lift (f := ⟨mk, continuous_coe⟩) isQuotientMap_coe f (factorsThrough_mk f)

-- If `mk` is `ContinuousMap`, then we can use `ContinuousMap.comp`
@[simp]
theorem lift_comp {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (f : C(X, Y)) :
    lift f ∘ mk = f := by
  ext x
  exact (ContinuousMap.ext_iff.mp (Topology.IsQuotientMap.lift_comp (f := ⟨mk, continuous_coe⟩) isQuotientMap_coe f (factorsThrough_mk f))) x

@[simp]
theorem lift_comp_apply {X : Type*} [TopologicalSpace X] (x : X)
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (f : C(X, Y)) :
    (lift f) (mk x) = f x :=
  congr_fun (lift_comp f) x

theorem injective_lift {X : Type*} [TopologicalSpace X] (x : X)
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] (f : C(X, Y))
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) : Function.Injective (lift f) := by
  sorry

end ConnectedComponents
