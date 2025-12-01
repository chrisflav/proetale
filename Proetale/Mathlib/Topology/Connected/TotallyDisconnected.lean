import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

variable {X : Type*} [TopologicalSpace X]

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form IsPreconnected.foo
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X] (x : X)
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) : Function.Injective (hf.connectedComponentsLift) := by
  sorry

-- end of the file
variable (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]

theorem connectedComponent.prod (s : S) (t : T) :
    connectedComponent (s, t) = connectedComponent s ×ˢ connectedComponent t :=
  sorry

theorem ConnectedComponents.isHomeomorph_connectedComponentsLift_prod :
    IsHomeomorph (Continuous.connectedComponentsLift
    (f := fun x : S × T ↦ (mk x.1, mk x.2)) (by continuity)) where
  continuous := Continuous.connectedComponentsLift_continuous (by continuity)
  isOpenMap := sorry
  bijective := sorry

variable {S T} in
noncomputable def ConnectedComponents.prodMap :
    ConnectedComponents (S × T) ≃ₜ ConnectedComponents S × ConnectedComponents T :=
  IsHomeomorph.homeomorph (Continuous.connectedComponentsLift
    (by continuity)) (isHomeomorph_connectedComponentsLift_prod S T)

def ConnectedComponents.mkHomeomorph [TotallyDisconnectedSpace S] : S ≃ₜ ConnectedComponents S where
  toFun := mk
  invFun := continuous_id.connectedComponentsLift
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := continuous_coe
  continuous_invFun := continuous_id.connectedComponentsLift_continuous
