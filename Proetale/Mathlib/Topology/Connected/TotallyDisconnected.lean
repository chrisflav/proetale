import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

variable {X : Type*} [TopologicalSpace X]

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form IsPreconnected.foo
-- `by copilot`
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X]
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
    simp [g]
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
        simp [h_apply_coe x', hx'y]
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
  isOpenMap := by
    -- ⊇ direction: uses that π₀(X × Y) ≅ π₀(X) × π₀(Y) as topological spaces (blueprint: thm:pi0-prod)
    sorry
  bijective := by
    constructor
    · -- Injective: two elements with same image must be equal.
      intro a b hab
      -- Work with representatives
      revert hab
      refine Quotient.inductionOn₂ a b (fun p₁ p₂ h => ?_)
      -- h says: g(mk p₁) = g(mk p₂), i.e., (mk p₁.1, mk p₁.2) = (mk p₂.1, mk p₂.2)
      have key := fun p : S × T => Continuous.connectedComponentsLift_apply_coe
        (by continuity : Continuous (fun x : S × T ↦ ((x.1 : ConnectedComponents S),
          (x.2 : ConnectedComponents T)))) p
      have h' : ((p₁.1 : ConnectedComponents S), (p₁.2 : ConnectedComponents T)) =
          ((p₂.1 : ConnectedComponents S), (p₂.2 : ConnectedComponents T)) :=
        (key p₁).symm.trans (h.trans (key p₂))
      -- Extract component equalities
      have hs : (p₁.1 : ConnectedComponents S) = p₂.1 := (Prod.mk.inj h').1
      have ht : (p₁.2 : ConnectedComponents T) = p₂.2 := (Prod.mk.inj h').2
      -- These mean p₁ and p₂ are in the same connected component
      -- ⟦p₁⟧ = ⟦p₂⟧ iff p₁ and p₂ are in the same connected component
      show (p₁ : ConnectedComponents (S × T)) = (p₂ : ConnectedComponents (S × T))
      rw [ConnectedComponents.coe_eq_coe]
      rw [connectedComponent.prod, connectedComponent.prod]
      have hs' : connectedComponent p₁.1 = connectedComponent p₂.1 :=
        connectedComponent_eq (ConnectedComponents.coe_eq_coe'.mp hs.symm)
      have ht' : connectedComponent p₁.2 = connectedComponent p₂.2 :=
        connectedComponent_eq (ConnectedComponents.coe_eq_coe'.mp ht.symm)
      rw [hs', ht']
    · -- Surjective
      intro ⟨c₁, c₂⟩
      obtain ⟨s, rfl⟩ := Quot.exists_rep c₁
      obtain ⟨t, rfl⟩ := Quot.exists_rep c₂
      exact ⟨ConnectedComponents.mk (s, t),
        Continuous.connectedComponentsLift_apply_coe (by continuity) (s, t)⟩

variable {S T} in
noncomputable def ConnectedComponents.prodMap :
    ConnectedComponents (S × T) ≃ₜ ConnectedComponents S × ConnectedComponents T :=
  IsHomeomorph.homeomorph (Continuous.connectedComponentsLift
    (by continuity)) (isHomeomorph_connectedComponentsLift_prod S T)

-- TODO: unbundle this
def ConnectedComponents.mkHomeomorph [TotallyDisconnectedSpace S] : S ≃ₜ ConnectedComponents S where
  toFun := mk
  invFun := continuous_id.connectedComponentsLift
  left_inv := fun s => continuous_id.connectedComponentsLift_apply_coe s
  right_inv := by
    intro c
    obtain ⟨s, rfl⟩ := Quot.exists_rep c
    exact congrArg mk (continuous_id.connectedComponentsLift_apply_coe s)
  continuous_toFun := continuous_coe
  continuous_invFun := continuous_id.connectedComponentsLift_continuous
