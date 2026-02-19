import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) : QuasiSeparatedSpace β :=
  (quasiSeparatedSpace_congr f).1 inferInstance

/-- A function between topological spaces is quasi-compact if the preimages of compact open sets
are compact. -/
def QuasiCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

variable {X : Type*} [TopologicalSpace X]

theorem quasiSeparatedSpace_of_quasiCompact_diagonal (h : QuasiCompact (fun x : X ↦ (x, x))) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff]
  intro U V hUopen hUcomp hVopen hVcomp
  have hpre : (fun x : X ↦ (x, x)) ⁻¹' (U ×ˢ V) = U ∩ V := by
    ext x
    simp
  simpa [hpre] using h (U ×ˢ V) (hUopen.prod hVopen) (hUcomp.prod hVcomp)

theorem quasiCompact_diagonal_of_quasiSeparatedSpace [QuasiSeparatedSpace X] [PrespectralSpace X] :
    QuasiCompact (fun x : X ↦ (x, x)) := by
  intro s hsOpen hsCompact
  -- Cover `s` by compact open rectangles using the prespectral basis.
  have h_rect :
      ∀ p : s,
        ∃ (U V : Set X),
          IsOpen U ∧ IsCompact U ∧ p.1.1 ∈ U ∧
          IsOpen V ∧ IsCompact V ∧ p.1.2 ∈ V ∧ U ×ˢ V ⊆ s := by
    intro p
    have hsNhds : s ∈ 𝓝 p.1 := hsOpen.mem_nhds p.2
    rcases (mem_nhds_prod_iff'.1 hsNhds) with ⟨u, v, hu, hxu, hv, hyv, huv⟩
    obtain ⟨U, ⟨hUo, hUc⟩, hxU, hUu⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxu hu
    obtain ⟨V, ⟨hVo, hVc⟩, hyV, hVv⟩ :=
      (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hyv hv
    refine ⟨U, V, hUo, hUc, hxU, hVo, hVc, hyV, ?_⟩
    intro z hz
    have hz' : z ∈ u ×ˢ v := by
      have : z.1 ∈ u ∧ z.2 ∈ v := by
        have hzUV : z.1 ∈ U ∧ z.2 ∈ V := by simpa [Set.mem_prod] using hz
        exact ⟨hUu hzUV.1, hVv hzUV.2⟩
      simpa [Set.mem_prod] using this
    exact huv hz'
  choose U V hUV using h_rect
  let R : s → Set (X × X) := fun p ↦ U p ×ˢ V p
  have hRopen : ∀ p : s, IsOpen (R p) := by
    intro p
    rcases hUV p with ⟨hUo, -, -, hVo, -, -, -⟩
    exact hUo.prod hVo
  have hRsub : ∀ p : s, R p ⊆ s := by
    intro p
    rcases hUV p with ⟨_, _, _, _, _, _, hsub⟩
    simpa [R] using hsub
  have hRmem : ∀ p : s, p.1 ∈ R p := by
    intro p
    rcases hUV p with ⟨_, _, hxU, _, _, hyV, _⟩
    simpa [R, Set.mem_prod] using And.intro hxU hyV
  have hcover : s ⊆ ⋃ p : s, R p := by
    intro z hz
    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨z, hz⟩, ?_⟩
    simpa using hRmem ⟨z, hz⟩
  obtain ⟨t, ht⟩ := hsCompact.elim_finite_subcover R hRopen hcover
  have hs_eq : s = ⋃ p ∈ t, R p := by
    apply le_antisymm
    · exact ht
    · intro z hz
      rcases Set.mem_iUnion₂.1 hz with ⟨p, hp, hz'⟩
      exact hRsub p hz'
  have hs_pre :
      (fun x : X ↦ (x, x)) ⁻¹' s = ⋃ p ∈ t, (fun x : X ↦ (x, x)) ⁻¹' R p := by
    ext x
    change (x, x) ∈ s ↔ x ∈ ⋃ p ∈ t, (fun x : X ↦ (x, x)) ⁻¹' R p
    have hsiff :
        ((x, x) ∈ s) ↔ ((x, x) ∈ ⋃ p ∈ t, R p) := by
      constructor
      · intro hx
        exact hs_eq ▸ hx
      · intro hx
        exact hs_eq.symm ▸ hx
    refine hsiff.trans ?_
    constructor
    · intro hx
      rcases Set.mem_iUnion₂.1 hx with ⟨p, hp, hxRp⟩
      refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
      simpa using hxRp
    · intro hx
      rcases Set.mem_iUnion₂.1 hx with ⟨p, hp, hxRp⟩
      refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
      simpa using hxRp
  have hcomp : IsCompact (⋃ p ∈ t, (fun x : X ↦ (x, x)) ⁻¹' R p) := by
    refine t.isCompact_biUnion ?_
    intro p hp
    have hpre : (fun x : X ↦ (x, x)) ⁻¹' R p = U p ∩ V p := by
      ext x
      simp [R]
    rcases hUV p with ⟨hUo, hUc, -, hVo, hVc, -, -⟩
    simpa [hpre] using
      (IsCompact.inter_of_isOpen (U := U p) (V := V p) hUc hVc hUo hVo)
  simpa [hs_pre] using hcomp

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [PrespectralSpace α]
    [QuasiSeparatedSpace β] [PrespectralSpace β] : QuasiSeparatedSpace (α × β) := by
  let b :
      ({ U : Set α // IsOpen U ∧ IsCompact U } × { V : Set β // IsOpen V ∧ IsCompact V }) →
        Set (α × β) := fun i ↦ (i.1.1 : Set α) ×ˢ (i.2.1 : Set β)
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := b) ?_ ?_
  · have hbα :
        IsTopologicalBasis ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α)) :=
      PrespectralSpace.isTopologicalBasis (X := α)
    have hbβ :
        IsTopologicalBasis ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) :=
      PrespectralSpace.isTopologicalBasis (X := β)
    have hbprod :
        IsTopologicalBasis
          (Set.image2 (· ×ˢ ·) ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α))
            ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β))) :=
      hbα.prod hbβ
    have hrange :
        Set.range b =
          Set.image2 (· ×ˢ ·) ({ U : Set α | IsOpen U ∧ IsCompact U } : Set (Set α))
            ({ V : Set β | IsOpen V ∧ IsCompact V } : Set (Set β)) := by
      ext s
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.1.1, i.1.2, i.2.1, i.2.2, rfl⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
    simpa [hrange] using hbprod
  · intro i j
    have hA : IsCompact ((i.1.1 : Set α) ∩ (j.1.1 : Set α)) :=
      IsCompact.inter_of_isOpen (U := (i.1.1 : Set α)) (V := (j.1.1 : Set α))
        i.1.2.2 j.1.2.2 i.1.2.1 j.1.2.1
    have hB : IsCompact ((i.2.1 : Set β) ∩ (j.2.1 : Set β)) :=
      IsCompact.inter_of_isOpen (U := (i.2.1 : Set β)) (V := (j.2.1 : Set β))
        i.2.2.2 j.2.2.2 i.2.2.1 j.2.2.1
    simpa [b, Set.prod_inter_prod] using hA.prod hB
