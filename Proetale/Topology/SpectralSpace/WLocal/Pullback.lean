/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.ClosedPoints
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Pullback of w-local spaces

Stacks Project 096C
-/

open CategoryTheory TopCat

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

-- Helper: In the pullback, the map (f, g) is injective (since Y is homeomorphic to a subspace of X × T).
private lemma ConnectedComponents.fg_injective_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hf : f y₁ = f y₂) (hg : g y₁ = g y₂) : y₁ = y₂ := by
  have inst_hp := pb.hasPullback
  let E := homeoOfIso (pb.isoPullback ≪≫
    pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
  have hE_g : ∀ y, (E y).val.1 = g y := by
    intro y
    show ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.1 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
  have hE_f : ∀ y, (E y).val.2 = f y := by
    intro y
    show ((pb.isoPullback ≪≫
      pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y).val.2 = _
    simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [pullbackIsoProdSubtype_hom_apply]
    exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
  apply E.injective
  apply Subtype.ext
  apply Prod.ext
  · simp only [hE_g]; exact hg
  · simp only [hE_f]; exact hf

-- Helper: commutativity of the pullback square
private lemma ConnectedComponents.hw_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    (y : Y) : i (g y) = (f y : ConnectedComponents X) :=
  ConcreteCategory.congr_hom pb.w y

-- Helper: In the pullback, g restricted to f⁻¹'(closedPoints X) is injective
private lemma ConnectedComponents.g_injective_on_preimage_closedPoints
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    {y₁ y₂ : Y} (hy₁ : f y₁ ∈ closedPoints X) (hy₂ : f y₂ ∈ closedPoints X)
    (hg : g y₁ = g y₂) : y₁ = y₂ := by
  have hw := hw_of_isPullback pb
  -- From hg: i(g y₁) = i(g y₂), so mk(f y₁) = mk(f y₂)
  have hmk : (f y₁ : ConnectedComponents X) = f y₂ :=
    (hw y₁).symm.trans (congrArg i hg ▸ hw y₂)
  -- closedPoints X -> ConnectedComponents X is injective (from w-local)
  have hinj := (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).bijective.1
  have hf : f y₁ = f y₂ := by
    have := @hinj ⟨f y₁, hy₁⟩ ⟨f y₂, hy₂⟩
    simp only [Function.comp] at this
    exact congrArg Subtype.val (this hmk)
  exact fg_injective_of_isPullback pb hf hg

@[stacks 096C "second part"]
theorem ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  have hw := hw_of_isPullback pb
  ext y; constructor
  · -- Forward: if f(y) is a closed point of X, then y is a closed point of Y.
    -- Strategy: if y ⤳ y' then f(y) ⤳ f(y') and g(y) ⤳ g(y'). Since f(y) is closed, f(y) = f(y').
    -- Since T is T1 (T2 in fact), g(y) = g(y'). Since (f,g) is injective, y = y'.
    intro hy
    rw [Set.mem_preimage, mem_closedPoints_iff] at hy
    rw [mem_closedPoints_iff]
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    -- z ≠ y, and we want to find an open set containing z but not y.
    -- Since (f,g) separates points of Y (via the pullback), f(z) ≠ f(y) or g(z) ≠ g(y).
    by_cases hfzy : f z = f y
    · -- f(z) = f(y), so g(z) ≠ g(y) (otherwise z = y by injectivity of (f,g))
      have hgzy : g z ≠ g y := fun h => hz (fg_injective_of_isPullback pb hfzy h)
      -- T is T2, so we can separate g(z) and g(y)
      obtain ⟨U, V, hU, hV, hgzU, hgyV, hUV⟩ := t2_separation hgzy
      exact ⟨g ⁻¹' U, fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq; subst heq
        exact Set.disjoint_left.mp hUV hw hgyV,
        hU.preimage g.2, hgzU⟩
    · -- f(z) ≠ f(y), and {f(y)} is closed. So f(y) ∈ {f(y)} and z ∈ {f(y)}ᶜ.
      -- f⁻¹'({f(y)}ᶜ) is open and contains z but not y.
      exact ⟨f ⁻¹' {f y}ᶜ, fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] at hw ⊢
        intro heq; subst heq; exact hw rfl,
        hy.isOpen_compl.preimage f.2,
        by simp [hfzy]⟩
  · -- Backward: if y is a closed point of Y, then f(y) is a closed point of X.
    -- Strategy: if f(y) is not closed, f(y) specializes to some distinct x' in X.
    -- We show y must specialize to some y' ≠ y with f(y') = x', contradicting y closed.
    intro hy
    rw [Set.mem_preimage, mem_closedPoints_iff]
    rw [mem_closedPoints_iff] at hy
    -- In a spectral space, every point specializes to a closed point.
    haveI : SpectralSpace Y := pb.spectralSpace
    -- Suppose f(y) is not closed. Then there exists z with f(y) ⤳ z and f(y) ≠ z.
    -- In X (w-local), f(y) specializes to a unique closed point x_c.
    obtain ⟨x_c, hx_c_closed, hfy_xc⟩ := exists_isClosed_specializes (f y)
    -- Need to show f(y) = x_c, i.e., f(y) is already closed.
    -- mk(x_c) = mk(f(y)) since x_c is in the closure of f(y), hence in same connected component.
    have hcc : ConnectedComponents.mk x_c = ConnectedComponents.mk (f y) := by
      rw [ConnectedComponents.coe_eq_coe']
      exact closure_minimal (Set.singleton_subset_iff.mpr mem_connectedComponent)
        isClosed_connectedComponent hfy_xc.mem_closure
    -- So i(g(y)) = mk(f(y)) = mk(x_c)
    have hmk_eq : mk x_c = i (g y) := hcc.trans (hw y).symm
    -- By pullback lifting: there exists y_c in Y with f(y_c) = x_c and g(y_c) = g(y)
    let y_c := pb.lift (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
      (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
      (by ext ⟨⟩; exact hmk_eq.symm) PUnit.unit
    have hgy_c : g y_c = g y := ConcreteCategory.congr_hom
      (pb.lift_fst (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
        (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
        (by ext ⟨⟩; exact hmk_eq.symm)) PUnit.unit
    have hfy_c : f y_c = x_c := ConcreteCategory.congr_hom
      (pb.lift_snd (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} (g y)))
        (TopCat.ofHom (ContinuousMap.const PUnit.{u+1} x_c))
        (by ext ⟨⟩; exact hmk_eq.symm)) PUnit.unit
    -- y ⤳ y_c: we need to show y_c ∈ closure{y}
    -- We show this using the fact that f(y) ⤳ x_c = f(y_c) and g(y) = g(y_c)
    -- In the pullback (subspace of X × T), specialization is componentwise.
    -- If y ⤳ y_c in Y, then since y is a closed point, y = y_c, so f(y) = x_c.
    -- The question is: does y ⤳ y_c?
    -- In the pullback {(x,t) | mk(x) = i(t)} ⊆ X × T, y corresponds to (f(y), g(y))
    -- and y_c corresponds to (x_c, g(y)). Since f(y) ⤳ x_c in X and g(y) = g(y) in T,
    -- we get (f(y), g(y)) ⤳ (x_c, g(y)) in X × T, which restricts to y ⤳ y_c in Y.
    have hy_spec_yc : y ⤳ y_c := by
      -- Strategy: use specializes_iff_mem_closure and show y_c ∈ closure({y}).
      -- closure({y}) = { z | y ⤳ z }. We use the homeomorphism E to transfer.
      rw [specializes_iff_mem_closure]
      -- Use the homeomorphism E : Y ≃ₜ {p : T × X | i p.1 = mk p.2}
      have inst_hp := pb.hasPullback
      let E := homeoOfIso (pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
      have hE_g : ∀ y', (E y').val.1 = g y' := by
        intro y'
        show ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.1 = _
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact ConcreteCategory.congr_hom pb.isoPullback_hom_fst y'
      have hE_f : ∀ y', (E y').val.2 = f y' := by
        intro y'
        show ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.2 = _
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact ConcreteCategory.congr_hom pb.isoPullback_hom_snd y'
      -- f(y) ⤳ f(y_c) in X and g(y) = g(y_c) in T
      -- We use continuity of f and g to pull back closure from X and T to Y.
      -- y_c ∈ f ⁻¹' (closure {f y}) ∩ g ⁻¹' (closure {g y})
      -- and closure {y} ⊇ f ⁻¹' (closure {f y}) ∩ g ⁻¹' (closure {g y})? No, this is wrong.
      -- Instead, use the embedding. E maps closure to closure.
      -- E(y_c) ∈ closure {E(y)} in the subtype because:
      --   (E y_c).val ∈ closure {(E y).val} in T × X (from componentwise specialization)
      --   and closure in subtype ⊇ (closure in ambient) ∩ subtype
      -- Actually, for subtypes: closure_subtype = (closure in ambient) ∩ subtype
      -- So E(y_c) ∈ closure {E(y)} ↔ (E y_c).val ∈ closure {(E y).val}
      -- Since E is a homeomorphism, closure {y} = E⁻¹ '' closure {E(y)}.
      -- So y_c ∈ closure {y} ↔ E(y_c) ∈ closure {E(y)} ↔ (E y_c).val ∈ closure {(E y).val}.
      -- (E y).val = (g y, f y) and (E y_c).val = (g y_c, f y_c) = (g y, x_c).
      -- closure {(g y, f y)} in T × X = closure {g y} ×ˢ closure {f y}
      -- (g y, x_c) ∈ closure {g y} ×ˢ closure {f y} ↔ g y ∈ closure {g y} ∧ x_c ∈ closure {f y}
      -- First is trivial, second is hfy_xc.mem_closure.
      -- Pull back to Y via E.
      have hval_spec : (E y).val ⤳ (E y_c).val := by
        rw [specializes_prod]
        constructor
        · -- g-component: g(y) ⤳ g(y_c) = g(y)
          show (E y).val.1 ⤳ (E y_c).val.1
          rw [hE_g, hE_g, hgy_c]
        · -- f-component: f(y) ⤳ x_c
          show (E y).val.2 ⤳ (E y_c).val.2
          rw [hE_f, hE_f, hfy_c]; exact hfy_xc
      -- Transfer from ambient to subtype via IsInducing
      have hsub_spec : E y ⤳ E y_c :=
        Topology.IsInducing.subtypeVal.specializes_iff.mp hval_spec
      -- Transfer from subtype to Y via homeomorphism E
      exact (E.isInducing.specializes_iff.mp hsub_spec).mem_closure
    -- Since y is a closed point, y = y_c
    have heq : y = y_c := by
      have hmem : y_c ∈ closure ({y} : Set Y) := hy_spec_yc.mem_closure
      rw [hy.closure_eq] at hmem
      rw [Set.mem_singleton_iff] at hmem; exact hmem.symm
    -- So f(y) = f(y_c) = x_c, which is closed
    have : f y = x_c := by rw [heq, hfy_c]
    rw [this]; exact hx_c_closed

@[stacks 096C "second part"]
theorem ConnectedComponents.wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := by
    intro y c c' hc hc' hyc hyc'
    -- c, c' are closed points of Y, so f(c), f(c') are closed points of X
    have hfc : f c ∈ closedPoints X := by
      have : c ∈ closedPoints Y := mem_closedPoints_iff.mpr hc
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at this
    have hfc' : f c' ∈ closedPoints X := by
      have : c' ∈ closedPoints Y := mem_closedPoints_iff.mpr hc'
      rwa [← preimage_closedPoints_eq_closedPoints_of_isPullback pb] at this
    -- f(y) ⤳ f(c) and f(y) ⤳ f(c'), and both f(c), f(c') are closed
    have hfyc : f y ⤳ f c := hyc.map f.2
    have hfyc' : f y ⤳ f c' := hyc'.map f.2
    have hfc_closed := mem_closedPoints_iff.mp hfc
    have hfc'_closed := mem_closedPoints_iff.mp hfc'
    -- By w-local property of X: f(c) = f(c')
    have hf_eq : f c = f c' := WLocalSpace.eq_of_specializes hfc_closed hfc'_closed hfyc hfyc'
    -- g(y) ⤳ g(c) and g(y) ⤳ g(c') in T. Since T is T1, g(c) = g(y) = g(c').
    have hgyc : g y ⤳ g c := hyc.map g.2
    have hgyc' : g y ⤳ g c' := hyc'.map g.2
    have hg_eq : g c = g c' := by
      have h1 : g y = g c := hgyc.eq
      have h2 : g y = g c' := hgyc'.eq
      rw [← h1, ← h2]
    -- Since (f,g) is injective on Y (pullback), c = c'
    exact fg_injective_of_isPullback pb hf_eq hg_eq
  isClosed_closedPoints := by
    have h := preimage_closedPoints_eq_closedPoints_of_isPullback pb
    rw [← h]
    exact (WLocalSpace.isClosed_closedPoints (X := X)).preimage f.2

@[stacks 096C "second part"]
theorem ConnectedComponents.isWLocalMap_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f where
  toIsSpectralMap := by
    haveI := pb.spectralSpace
    haveI := wlocalSpace_of_isPullback pb
    constructor
    · exact f.2
    · -- f is proper (hence spectral):
      -- Y ≅ {(t,x) : T × X | i(t) = mk(x)} is a closed subspace of T × X
      -- (closed because i(t) = mk(x) is an equalizer of continuous maps to T2 space).
      -- The projection T × X → X is proper (T compact). Proper ∘ closed embedding = proper.
      -- A proper map is spectral.
      have inst_hp := pb.hasPullback
      let E := homeoOfIso (pb.isoPullback ≪≫
        pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
      -- The subtype {p : T × X | i p.1 = mk p.2} is closed in T × X
      have hclosed : IsClosed {p : T × X | i p.1 = ConnectedComponents.mk p.2} :=
        isClosed_eq (i.2.comp continuous_fst) (continuous_coe.comp continuous_snd)
      -- Subtype val ∘ E gives an embedding Y ↪ T × X
      -- The projection Prod.snd : T × X → X is proper
      have hsnd_proper : IsProperMap (Prod.snd : T × X → X) :=
        isProperMap_snd_of_compactSpace
      -- f = Prod.snd ∘ Subtype.val ∘ E
      have hf_eq : ∀ y, f y = (E y).val.2 := by
        intro y'
        show f y' = ((pb.isoPullback ≪≫
          pullbackIsoProdSubtype (ofHom i) (ofHom ⟨mk, continuous_coe⟩)).hom y').val.2
        simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
        rw [pullbackIsoProdSubtype_hom_apply]
        exact (ConcreteCategory.congr_hom pb.isoPullback_hom_snd y').symm
      -- f is proper as composition: proper Prod.snd ∘ proper subtypeVal ∘ homeomorphism
      -- f = Prod.snd ∘ Subtype.val ∘ E
      have hcomp_proper : IsProperMap (Prod.snd ∘ Subtype.val ∘ E :
          Y → X) :=
        (hsnd_proper.comp hclosed.isProperMap_subtypeVal).comp E.isProperMap
      -- But f and this composition agree
      have hf_proper : IsProperMap f := by
        have heq : f = Prod.snd ∘ Subtype.val ∘ E := funext hf_eq
        rw [heq]; exact hcomp_proper
      intro s hs hsc
      exact hf_proper.isSpectralMap.isCompact_preimage_of_isOpen hs hsc
  image_closedPoints := by
    intro y hy
    rwa [preimage_closedPoints_eq_closedPoints_of_isPullback pb]
