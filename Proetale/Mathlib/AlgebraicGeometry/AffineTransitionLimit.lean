import Mathlib.AlgebraicGeometry.AffineTransitionLimit

universe t u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (c : Cone D) (hc : IsLimit c)

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ (i : I), CompactSpace (D.obj i)] [∀ (i : I), QuasiSeparatedSpace (D.obj i)]

open TopologicalSpace

-- TODO: this is taken from mathlib and slightly modified to assume `J` is finite: in this case
-- we can descend the full cover
include hc in
lemma Scheme.exists_isOpenCover_and_isAffine_of_finite
    {J : Type*} [Finite J] (U : J → c.pt.Opens) (hU : IsOpenCover U)
    (hU' : ∀ i, IsAffineOpen (U i)) :
    ∃ (i : I) (V : J → (D.obj i).Opens),
      IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  classical
  have := compactSpace_of_isLimit D c hc
  choose j V hV hVU using fun k ↦ exists_isAffineOpen_preimage_eq D c hc (U k) (hU' k)
  cases nonempty_fintype J
  obtain ⟨i, fi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  replace fi : ∀ k, i ⟶ j k := fun k ↦ (fi (by simp)).some
  obtain ⟨k, fkj, e⟩ := exists_map_eq_top D c hc (⨆ (k), D.map (fi k) ⁻¹ᵁ V k) (by
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, c.w, hVU]
    exact hU)
  refine ⟨k, fun x ↦ D.map (fkj ≫ fi x) ⁻¹ᵁ V _, ?_, fun k ↦ ⟨(hV k).preimage _, ?_⟩⟩
  · refine top_le_iff.mp (e.symm.trans_le ?_)
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, ← D.map_comp]
    simp
  · rw [← hVU, ← Hom.comp_preimage, c.w]

include hc in
lemma Scheme.OpenCover.exists_of_isCofiltered_of_finite
    (𝒰 : OpenCover.{t} c.pt) [∀ i, IsAffine (𝒰.X i)] [Finite 𝒰.I₀] :
    ∃ (i : I)
      (R : 𝒰.I₀ → CommRingCat.{u})
      (f : ∀ (a : 𝒰.I₀), Spec (R a) ⟶ (D.obj i))
      (_ : Presieve.ofArrows _ f ∈ zariskiPrecoverage _)
      (g : ∀ (j : 𝒰.I₀), 𝒰.X j ⟶ Spec (R j)),
      ∀ (j : 𝒰.I₀), IsPullback (g j) (𝒰.f j) (f j) (c.π.app i) := by
  obtain ⟨i, V, hV, hV'⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite _ _ hc _
    𝒰.isOpenCover_opensRange fun k ↦ isAffineOpen_opensRange (𝒰.f k)
  have hV'' (k) := congr($((hV' k).right).carrier)
  dsimp at hV''
  refine ⟨i, fun k ↦ Γ(_, V k), ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp
    exact (hV' k).left.isoSpec.inv ≫ (V k).ι
  · simp only [IsAffineOpen.isoSpec_inv_ι, id_eq, ofArrows_mem_precoverage_iff,
      IsAffineOpen.range_fromSpec, SetLike.mem_coe]
    exact ⟨fun x ↦ hV.exists_mem x, inferInstance⟩
  · intro k
    dsimp
    refine ?_ ≫ (hV' k).left.isoSpec.hom
    refine IsOpenImmersion.lift (V k).ι ?_ ?_
    · exact 𝒰.f _ ≫ c.π.app i
    · simp [hV'', Set.range_comp]
  · intro k
    dsimp
    refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · simp [← IsAffineOpen.isoSpec_inv_ι]
    · intro s
      refine IsOpenImmersion.lift (𝒰.f k) ?_ ?_
      · exact s.snd
      · rw [hV'']
        have := s.condition
        rw [Set.range_subset_iff]
        simp only [Set.mem_preimage, SetLike.mem_coe]
        intro y
        rw [← Scheme.Hom.comp_apply, ← s.condition]
        simp only [Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]
        simp_rw [← IsAffineOpen.isoSpec_inv_ι]
        rw [Scheme.Hom.comp_apply]
        dsimp
        exact SetLike.coe_mem ((hV' k).left.isoSpec.inv ((TopCat.Hom.hom s.fst.base) y))
    · intro s
      rw [← cancel_mono (hV' _).left.isoSpec.inv]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← cancel_mono (V k).ι]
      simp [s.condition]
    · intro s
      simp
    · intro s m hm hm'
      simp [← cancel_mono (𝒰.f k), hm']

include hc in
-- Use `Scheme.exists_isOpenCover_and_isAffine`
lemma Scheme.OpenCover.exists_of_isCofiltered (𝒰 : OpenCover.{t} c.pt) [∀ i, IsAffine (𝒰.X i)] :
    ∃ (i : I) (𝒱 : Scheme.AffineOpenCover.{t} (D.obj i)) (s : 𝒱.I₀ → 𝒰.I₀) (_ : Finite 𝒱.I₀)
      (g : ∀ (j : 𝒱.I₀), 𝒰.X (s j) ⟶ 𝒱.openCover.X j),
      ∀ (j : 𝒱.I₀), IsPullback (g j) (𝒰.f (s j)) (𝒱.f j) (c.π.app i) :=
  sorry

end AlgebraicGeometry
