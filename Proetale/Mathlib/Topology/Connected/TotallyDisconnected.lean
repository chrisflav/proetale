import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

variable {X : Type*} [TopologicalSpace X]

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form IsPreconnected.foo
-- `by copilot`
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X] (x : X)
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) : Function.Injective (hf.connectedComponentsLift) := by
  intro a b hEq
  set g := hf.connectedComponentsLift
  have hEq' : g a = g b := hEq
  let y := g a
  have hgb : g b = y := by simpa [y] using hEq'.symm
  -- Consider the fiber t = g ⁻¹' {y}.
  let t : Set (ConnectedComponents X) := g ⁻¹' {y}
  -- We show t is preconnected by identifying it with the image of a preconnected set under the projection.
  have h_apply_coe : ∀ x : X, g (((↑) : X → ConnectedComponents X) x) = f x := by
    intro x'
    simpa [g] using hf.connectedComponentsLift_apply_coe x'
  have ht_eq_image : t = ((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y}) := by
    ext z; constructor
    · intro hz
      have hz' : g z = y := by
        simpa [t, Set.mem_preimage, Set.mem_singleton_iff] using hz
      rcases Quot.exists_rep z with ⟨x', rfl⟩
      have hx' : f x' = y := by simpa [h_apply_coe x'] using hz'
      exact ⟨x', by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      have hx'y : f x' = y := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx'
      have : g (((↑) : X → ConnectedComponents X) x') = y := by
        simpa [h_apply_coe x', hx'y]
      simpa [t, Set.mem_preimage, Set.mem_singleton_iff]
  have ht_pre : IsPreconnected t := by
    have : IsPreconnected (((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y})) :=
      IsPreconnected.image (H := h y)
        (f := ((↑) : X → ConnectedComponents X))
        (hf := ConnectedComponents.continuous_coe.continuousOn)
    simpa [ht_eq_image] using this
  have ha : a ∈ t := by
    simp [t, y]
  have hb : b ∈ t := by
    simp [t, hgb]
  have hsubset : t ⊆ connectedComponent a :=
    IsPreconnected.subset_connectedComponent (x := a) (s := t) ht_pre ha
  have hb_in : b ∈ connectedComponent a := hsubset hb
  have hsingle :
      connectedComponent a = ({a} : Set (ConnectedComponents X)) :=
    (totallyDisconnectedSpace_iff_connectedComponent_singleton.mp
      (inferInstance : TotallyDisconnectedSpace (ConnectedComponents X))) a
  have : b ∈ ({a} : Set (ConnectedComponents X)) := by simpa [hsingle] using hb_in
  have hba : b = a := by simpa [Set.mem_singleton_iff] using this
  exact hba.symm

-- end of the file
variable (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]

-- `by copilot`
theorem connectedComponent.prod (s : S) (t : T) :
    connectedComponent (s, t) = connectedComponent s ×ˢ connectedComponent t := by
  apply Set.Subset.antisymm
  · intro p hp
    have hconn : IsConnected (connectedComponent (s, t) : Set (S × T)) :=
      isConnected_connectedComponent
    have hpst : (s, t) ∈ (connectedComponent (s, t) : Set (S × T)) :=
      mem_connectedComponent
    have hfst :
        (Prod.fst '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent s :=
      (hconn.image _ (continuous_fst.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have hs' : p.1 ∈ connectedComponent s := by
      have : p.1 ∈ Prod.fst '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hfst this
    have hsnd :
        (Prod.snd '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent t :=
      (hconn.image _ (continuous_snd.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have ht' : p.2 ∈ connectedComponent t := by
      have : p.2 ∈ Prod.snd '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hsnd this
    exact ⟨hs', ht'⟩
  · intro p hp
    have hs : p.1 ∈ connectedComponent s := hp.1
    have ht : p.2 ∈ connectedComponent t := hp.2
    have hconn_prod :
        IsConnected (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact (isConnected_connectedComponent (x := s)).prod (isConnected_connectedComponent (x := t))
    have hmem : (s, t) ∈ (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact ⟨mem_connectedComponent, mem_connectedComponent⟩
    have hsub :
        (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) ⊆ connectedComponent (s, t) :=
      hconn_prod.subset_connectedComponent hmem
    exact hsub ⟨hs, ht⟩

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
