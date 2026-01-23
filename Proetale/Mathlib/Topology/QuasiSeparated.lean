import Mathlib.Topology.QuasiSeparated
import Proetale.Mathlib.Topology.Spectral.Prespectral

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) : QuasiSeparatedSpace β :=
  (quasiSeparatedSpace_congr f).1 inferInstance

/-- A function between topological spaces is quasi-compact if the preimages of compact open sets
are compact. -/
def QuasiCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

theorem QuasiCompact.prod_map {X₁ Y₁ X₂ Y₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
    [TopologicalSpace X₂] [TopologicalSpace Y₂] [PrespectralSpace Y₁] [PrespectralSpace Y₂]
    {f : X₁ → Y₁} {g : X₂ → Y₂} (hf : QuasiCompact f) (hg : QuasiCompact g) :
    QuasiCompact (Prod.map f g) := by
  classical
  let b :
      ({ U : Set Y₁ // IsOpen U ∧ IsCompact U } × { V : Set Y₂ // IsOpen V ∧ IsCompact V }) →
        Set (Y₁ × Y₂) := fun i ↦ (i.1.1 : Set Y₁) ×ˢ (i.2.1 : Set Y₂)
  have hb₁ :
      IsTopologicalBasis ({ U : Set Y₁ | IsOpen U ∧ IsCompact U } : Set (Set Y₁)) :=
    PrespectralSpace.isTopologicalBasis (X := Y₁)
  have hb₂ :
      IsTopologicalBasis ({ V : Set Y₂ | IsOpen V ∧ IsCompact V } : Set (Set Y₂)) :=
    PrespectralSpace.isTopologicalBasis (X := Y₂)
  have hbprod :
      IsTopologicalBasis
        (Set.image2 (· ×ˢ ·) ({ U : Set Y₁ | IsOpen U ∧ IsCompact U } : Set (Set Y₁))
          ({ V : Set Y₂ | IsOpen V ∧ IsCompact V } : Set (Set Y₂))) :=
    hb₁.prod hb₂
  have hrange :
      Set.range b =
        Set.image2 (· ×ˢ ·) ({ U : Set Y₁ | IsOpen U ∧ IsCompact U } : Set (Set Y₁))
          ({ V : Set Y₂ | IsOpen V ∧ IsCompact V } : Set (Set Y₂)) := by
    ext s
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1.1, i.1.2, i.2.1, i.2.2, rfl⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), rfl⟩
  have hb : IsTopologicalBasis (Set.range b) := by
    simpa [hrange] using hbprod
  have aux :=
    isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b hb fun i ↦ by
      simpa [b] using i.1.2.2.prod i.2.2.2
  intro s hsOpen hsCompact
  obtain ⟨t, ht, rfl⟩ := (aux s).1 ⟨hsCompact, hsOpen⟩
  have hs_pre :
      (Prod.map f g) ⁻¹' (⋃ i ∈ t, b i) = ⋃ i ∈ t, (Prod.map f g) ⁻¹' b i := by
    ext x
    simp [b]
  have hcomp : IsCompact (⋃ i ∈ t, (Prod.map f g) ⁻¹' b i) := by
    refine ht.isCompact_biUnion ?_
    intro i hi
    have hpre :
        (Prod.map f g) ⁻¹' b i = (f ⁻¹' (i.1.1 : Set Y₁)) ×ˢ (g ⁻¹' (i.2.1 : Set Y₂)) := by
      ext x
      simp [b, Set.mem_prod, Prod.map]
    have h1 : IsCompact (f ⁻¹' (i.1.1 : Set Y₁)) := hf _ i.1.2.1 i.1.2.2
    have h2 : IsCompact (g ⁻¹' (i.2.1 : Set Y₂)) := hg _ i.2.2.1 i.2.2.2
    simpa [hpre] using h1.prod h2
  simpa [hs_pre] using hcomp

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
  classical
  refine quasiSeparatedSpace_of_quasiCompact_diagonal (X := α × β) ?_
  have hδα : QuasiCompact (fun a : α ↦ (a, a)) :=
    quasiCompact_diagonal_of_quasiSeparatedSpace (X := α)
  have hδβ : QuasiCompact (fun b : β ↦ (b, b)) :=
    quasiCompact_diagonal_of_quasiSeparatedSpace (X := β)
  let e : ((α × β) × (α × β)) ≃ₜ ((α × α) × (β × β)) :=
    { toEquiv :=
        { toFun := fun p ↦ ((p.1.1, p.2.1), (p.1.2, p.2.2))
          invFun := fun q ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2))
          left_inv := by intro p; rfl
          right_inv := by intro q; rfl }
      continuous_toFun := by
        have c11 : Continuous fun p : (α × β) × (α × β) ↦ p.1.1 := continuous_fst.fst
        have c21 : Continuous fun p : (α × β) × (α × β) ↦ p.2.1 := continuous_snd.fst
        have c12 : Continuous fun p : (α × β) × (α × β) ↦ p.1.2 := continuous_fst.snd
        have c22 : Continuous fun p : (α × β) × (α × β) ↦ p.2.2 := continuous_snd.snd
        exact (c11.prodMk c21).prodMk (c12.prodMk c22)
      continuous_invFun := by
        have c11 : Continuous fun q : (α × α) × (β × β) ↦ q.1.1 := continuous_fst.fst
        have c21 : Continuous fun q : (α × α) × (β × β) ↦ q.2.1 := continuous_snd.fst
        have c12 : Continuous fun q : (α × α) × (β × β) ↦ q.1.2 := continuous_fst.snd
        have c22 : Continuous fun q : (α × α) × (β × β) ↦ q.2.2 := continuous_snd.snd
        exact (c11.prodMk c21).prodMk (c12.prodMk c22) }
  have hprod :
      QuasiCompact (Prod.map (fun a : α ↦ (a, a)) (fun b : β ↦ (b, b))) :=
    QuasiCompact.prod_map (f := fun a : α ↦ (a, a)) (g := fun b : β ↦ (b, b)) hδα hδβ
  intro s hsOpen hsCompact
  have hsOpen' : IsOpen (e '' s) := e.isOpenMap _ hsOpen
  have hsCompact' : IsCompact (e '' s) := hsCompact.image e.continuous
  have hcomp :
      IsCompact
        ((Prod.map (fun a : α ↦ (a, a)) (fun b : β ↦ (b, b))) ⁻¹' (e '' s)) :=
    hprod _ hsOpen' hsCompact'
  have hpre :
      (fun x : α × β ↦ (x, x)) ⁻¹' s =
        (Prod.map (fun a : α ↦ (a, a)) (fun b : β ↦ (b, b))) ⁻¹' (e '' s) := by
    ext x
    change (x, x) ∈ s ↔ Prod.map (fun a : α ↦ (a, a)) (fun b : β ↦ (b, b)) x ∈ e '' s
    constructor
    · intro hx
      refine ⟨(x, x), hx, ?_⟩
      rfl
    · rintro ⟨y, hy, hy'⟩
      have : y = (x, x) := by
        apply e.injective
        simpa [e, Prod.map] using hy'
      simpa [this] using hy
  simpa [hpre] using hcomp
