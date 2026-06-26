import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Proetale.Mathlib.CategoryTheory.Limits.FunctorToTypes
import Proetale.Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

universe t u
universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

namespace CategoryTheory

lemma IsConnected.of_forall_nonempty_hom_left {C : Type*} [Category* C]
    (X : C) (h : ∀ (Y : C), Nonempty (X ⟶ Y)) :
    IsConnected C :=
  have : Nonempty C := ⟨X⟩
  zigzag_isConnected fun _ _ ↦ .trans (.of_inv (h _).some) (.of_hom (h _).some)

lemma IsConnected.of_forall_nonempty_hom_right {C : Type*} [Category* C]
    (X : C) (h : ∀ (Y : C), Nonempty (Y ⟶ X)) :
    IsConnected C :=
  have : Nonempty C := ⟨X⟩
  zigzag_isConnected fun _ _ ↦ .trans (.of_hom (h _).some) (.of_inv (h _).some)

variable {C : Type u₁} [Category.{v₁} C]
  {I : Type u₂} {I' : Type u₃} [Category.{v₂} I]
  [Category.{v₃} I']
  {D : I ⥤ C} {D' : I' ⥤ C}
  {c : Cone D} {c' : Cone D'}
  (hc : IsLimit c) (hc' : IsLimit c')
  (f : c.pt ⟶ c'.pt)

namespace ConstructLimitMap

def Aux : ObjectProperty (Comma D D') :=
  fun A ↦ c.π.app A.left ≫ A.hom = f ≫ c'.π.app A.right

@[reassoc]
lemma Aux.w (A : (Aux f).FullSubcategory) :
    c.π.app A.obj.left ≫ A.obj.hom = f ≫ c'.π.app A.obj.right :=
  A.property

@[simps!]
def Aux.projLeft : (Aux f).FullSubcategory ⥤ I :=
  (Aux f).ι ⋙ Comma.fst _ _

@[simps!]
def Aux.projRight : (Aux f).FullSubcategory ⥤ I' :=
  (Aux f).ι ⋙ Comma.snd _ _

variable
  [IsCofiltered I] [IsCofiltered I']
  [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

/-! TODO: The following three proofs are very similar, unify them. -/

include hc in
lemma isCofiltered : IsCofiltered (Aux f).FullSubcategory := by
  obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
  obtain ⟨a, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
  have : Nonempty (Aux f).FullSubcategory := ⟨⟨a, i', p⟩, hp⟩
  have : IsCofilteredOrEmpty (Aux f).FullSubcategory := by
    refine ⟨?_, ?_⟩
    · intro j₁ j₂
      let l' := IsCofiltered.min j₁.obj.right j₂.obj.right
      let lp₁ := IsCofiltered.minToLeft j₁.obj.right j₂.obj.right
      let lp₂ := IsCofiltered.minToRight j₁.obj.right j₂.obj.right
      obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
        (f ≫ c'.π.app (IsCofiltered.min j₁.obj.right j₂.obj.right))
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map lp₁) j₁.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map lp₂) j₂.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
      refine ⟨⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq, l']⟩, ?_, ?_, trivial⟩
      · exact ObjectProperty.homMk ⟨il₀ ≫ va₂, lp₁, by simp [heqa]⟩
      · exact ObjectProperty.homMk ⟨ir₀ ≫ vb₂, lp₂, by
          dsimp
          rw [← Functor.map_comp_assoc, heq]
          simp [heqb]⟩
    · intro j₁ j₂ u v
      obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
        (f ≫ c'.π.app (IsCofiltered.eq u.hom.right v.hom.right))
      obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
        (q ≫ D'.map (IsCofiltered.eqHom _ _)) j₁.obj.hom (by simp [reassoc_of% hq, Aux.w])
      obtain ⟨i₀, α, β, hα, hβ⟩ := IsCofiltered.bowtie u.hom.left (va₂ ≫ v.hom.left) (𝟙 _) va₂
      refine ⟨⟨⟨i₀, IsCofiltered.eq u.hom.right v.hom.right,
          D.map β ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq]⟩, ?_, ?_⟩
      · refine ObjectProperty.homMk
          ⟨β ≫ va₂, IsCofiltered.eqHom _ _, ?_⟩
        simp [heqa]
      · ext
        · simp only [Category.comp_id] at hβ
          subst hβ
          simpa using hα
        · simp [← IsCofiltered.eq_condition]
  constructor

include hc in
lemma initial_projLeft : (Aux.projLeft f).Initial := by
  constructor
  intro i
  have : Nonempty (CostructuredArrow (Aux.projLeft f) i) := by
    obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
    obtain ⟨a, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨CostructuredArrow.mk
      (Y := ⟨⟨IsCofiltered.min i a, i', D.map (IsCofiltered.minToRight _ _) ≫ p⟩, by
        simp [Aux, hp]⟩)
      (IsCofiltered.minToLeft _ _)⟩
  refine zigzag_isConnected fun j₁ j₂ ↦ ?_
  obtain ⟨i₁, l, r, hlr⟩ := IsCofiltered.cospan j₁.hom j₂.hom
  obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc
    (f ≫ c'.π.app (IsCofiltered.min j₁.left.obj.right j₂.left.obj.right))
  let l' := IsCofiltered.min j₁.left.obj.right j₂.left.obj.right
  let lp₁ := IsCofiltered.minToLeft j₁.left.obj.right j₂.left.obj.right
  let lp₂ := IsCofiltered.minToRight j₁.left.obj.right j₂.left.obj.right
  obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₁) j₁.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₂) j₂.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨i₀, il₀, ir₀, heq₁, heq₂⟩ := IsCofiltered.bowtie va₁ vb₁ (va₂ ≫ j₁.hom) (vb₂ ≫ j₂.hom)
  let middle : CostructuredArrow (Aux.projLeft f) i :=
    CostructuredArrow.mk (Y := ⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq, l']⟩)
      (il₀ ≫ va₂ ≫ j₁.hom)
  trans middle
  · refine .of_inv ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (il₀ ≫ va₂) lp₁ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc]
        simp only [Functor.map_comp, Category.assoc]
        rw [heqa]
    · simp [middle]
  · refine .of_hom ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (ir₀ ≫ vb₂) lp₂ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc, heq₁]
        simp [heqb]
    · simp [middle, heq₂]

include hc in
lemma initial_projRight : (Aux.projRight f).Initial := by
  refine ⟨fun i' ↦ ?_⟩
  have : Nonempty (CostructuredArrow (Aux.projRight f) i') := by
    obtain ⟨i, p, hp⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app i')
    exact ⟨CostructuredArrow.mk (Y := ⟨Comma.mk i i' p, hp⟩) <| 𝟙 _⟩
  refine zigzag_isConnected fun j₁ j₂ ↦ ?_
  obtain ⟨l', lp₁, lp₂, hlp⟩ := IsCofiltered.cospan j₁.hom j₂.hom
  obtain ⟨a, q, hq⟩ := exists_hom_of_preservesColimit_yoneda hc (f ≫ c'.π.app l')
  obtain ⟨ia, va₁, va₂, heqa⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₁) j₁.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨ib, vb₁, vb₂, heqb⟩ := exists_eq_of_preservesColimit_yoneda hc
    (q ≫ D'.map lp₂) j₂.left.obj.hom (by simp [reassoc_of% hq, Aux.w])
  obtain ⟨i₀, il₀, ir₀, heq⟩ := IsCofiltered.cospan va₁ vb₁
  let middle : CostructuredArrow (Aux.projRight f) i' :=
    CostructuredArrow.mk (Y := ⟨⟨i₀, l', D.map il₀ ≫ D.map va₁ ≫ q⟩, by simp [Aux, hq]⟩)
      (lp₁ ≫ j₁.hom)
  trans middle
  · refine .of_inv ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (il₀ ≫ va₂) lp₁ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc]
        simp only [Functor.map_comp, Category.assoc]
        rw [heqa]
    · simp [middle]
  · refine .of_hom ?_
    refine CostructuredArrow.homMk ?_ ?_
    · refine ObjectProperty.homMk ?_
      refine .mk (ir₀ ≫ vb₂) lp₂ ?_
      · dsimp [middle]
        rw [← Functor.map_comp_assoc, heq]
        simp [heqb]
    · simp [middle, hlp]

@[simps]
def map : Aux.projLeft f ⋙ D ⟶ Aux.projRight f ⋙ D' where
  app A := A.obj.hom

end ConstructLimitMap

variable
  [IsCofiltered I] [IsCofiltered I']
  [∀ i : I', PreservesColimit D.op (yoneda.obj (D'.obj i))]

set_option linter.unusedSectionVars false in
open ConstructLimitMap in
include hc hc' in
lemma Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda :
    ∃ (J : Type (max u₂ u₃ v₁))
      (_ : Category.{max v₂ v₃} J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g := by
  have := initial_projRight hc f
  have := initial_projLeft hc f
  use (Aux f).FullSubcategory, inferInstance, isCofiltered hc f,
    Aux.projLeft f, Aux.projRight f, inferInstance, inferInstance, map f
  apply ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc').hom_ext
  intro i'
  rw [IsLimit.map_π]
  dsimp
  apply i'.property.symm

end CategoryTheory

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

instance Scheme.preservesColimit_yoneda {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ (i : I), CompactSpace (D.obj i).left] [∀ (i : I), QuasiSeparatedSpace (D.obj i).left]
    (X : Over S) [LocallyOfFinitePresentation X.hom] :
    PreservesColimit D.op (yoneda.obj X) := by
  constructor
  intro c hc
  rw [Limits.Types.isColimit_iff_coconeTypesIsColimit]
  have (i : I) : CompactSpace ↥((D ⋙ Over.forget S).obj i) := by dsimp; infer_instance
  have (i : I) : QuasiSeparatedSpace ↥((D ⋙ Over.forget S).obj i) := by dsimp; infer_instance
  have {i j : I} (f : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map f) := by
    dsimp; infer_instance
  constructor
  refine ⟨?_, ?_⟩
  · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered']
    intro k g₁ g₂ hg
    dsimp at g₁ g₂
    obtain ⟨k, hik, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
      (D ⋙ Over.forget _) (.mk (fun _ ↦ (D.obj _).hom))
      X.hom _ (isLimitOfPreserves _ hc.unop) g₁.left g₂.left
      (Over.w g₁).symm (Over.w g₂).symm congr($(hg).left)
    use .op k, hik.op
    dsimp
    ext
    exact heq
  · intro g
    obtain ⟨k, u, h, h'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (D ⋙ Over.forget _) (.mk (fun _ ↦ (D.obj _).hom))
      X.hom _ (isLimitOfPreserves _ hc.unop) g.left (by ext; simp)
    use Functor.ιColimitType _ (.op k) (Over.homMk u)
    dsimp
    ext
    simpa using h

variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (c : Cone D) (hc : IsLimit c)

variable [IsCofiltered I]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
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

section

variable (D' : I ⥤ Scheme.{u}) (t' : D' ⟶ (Functor.const I).obj S) (c' : Cone D')
  (hc' : IsLimit c')

variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D'.map f)]
  [∀ (i : I), CompactSpace (D'.obj i)] [∀ (i : I), QuasiSeparatedSpace (D'.obj i)]

omit [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ (i : I), CompactSpace ↥(D.obj i)]
  [∀ (i : I), QuasiSeparatedSpace ↥(D.obj i)] [∀ (i : I), QuasiSeparatedSpace ↥(D'.obj i)] in
include hc' in
/-- If `lim fᵢ` is surjective and `fᵢ` has open image (e.g. if `fᵢ` is étale), then the image of
a deep enough transition map `D'ₖ ⟶ D'ᵢ` is contained in the image of `fᵢ`. In particular, the
base change of `fᵢ` along `D'ₖ ⟶ D'ᵢ` is surjective. Compare [EGA4.3, Thm. 8.10.5 (vi)].

Note that the naive statement "`fₖ` is surjective for all `k ⟶ i` for `i` deep enough" is false
for a general natural transformation `f`: EGA 8.10.5 considers systems induced from a single
morphism by base change. (Counterexample: `I = ℕᵒᵖ`, `D k = 𝔸¹ ∖ {0, …, k}`,
`D' k = 𝔸¹ ∖ {0, …, k - 1}` with `f.app k` the open immersion; no `f.app k` is surjective,
but the limit map is an isomorphism.) -/
lemma exists_range_map_subset_range_app_of_surjective_isLimitMap (f : D ⟶ D') (i : I)
    (hopen : IsOpen (Set.range (f.app i).base))
    (hf : Surjective (IsLimit.map c hc' f)) :
    ∃ (k : I) (fki : k ⟶ i), Set.range (D'.map fki).base ⊆ Set.range (f.app i).base := by
  let U : (D'.obj i).Opens := ⟨Set.range (f.app i).base, hopen⟩
  obtain ⟨k, fki, hk⟩ := exists_map_eq_top D' c' hc' (i := i) U <| by
    rw [TopologicalSpace.Opens.ext_iff]
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hf.surj y
    refine ⟨c.π.app i x, ?_⟩
    calc f.app i (c.π.app i x)
        = (c.π.app i ≫ f.app i) x := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (IsLimit.map c hc' f ≫ c'.π.app i) x :=
        (congrArg (fun g : c.pt ⟶ D'.obj i ↦ g x) (IsLimit.map_π c hc' f i)).symm
      _ = c'.π.app i (IsLimit.map c hc' f x) := Scheme.Hom.comp_apply _ _ _
  refine ⟨k, fki, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : z ∈ (D'.map fki ⁻¹ᵁ U : Set (D'.obj k)) := by
    rw [hk]
    trivial
  exact this

end

variable {I' : Type u} [SmallCategory I'] (D' : I' ⥤ Scheme.{u})
  (t' : D' ⟶ (Functor.const I').obj S)
  (c' : Cone D') (hc' : IsLimit c')

variable [IsCofiltered I']

instance {C : Type*} [Category* C] (X : C) : Nonempty (Over X) :=
  ⟨Over.mk (𝟙 X)⟩

instance {C : Type*} [Category* C] (X : C) : Nonempty (Under X) :=
  ⟨Under.mk (𝟙 X)⟩

include hc hc' in
lemma exists_eq_isLimitMap_whisker (f : c.pt ⟶ c'.pt)
    (hf : ∀ (i : I) (i' : I'), c.π.app i ≫ t.app i = f ≫ c'.π.app i' ≫ t'.app i')
    [∀ i, LocallyOfFinitePresentation (t.app i)] [∀ i, LocallyOfFinitePresentation (t'.app i)] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J) (G : J ⥤ I) (G' : J ⥤ I')
      (_ : G.Initial) (_ : G'.Initial) (g : G ⋙ D ⟶ G' ⋙ D'),
      f = IsLimit.map (c.whisker _) ((Functor.Initial.isLimitWhiskerEquiv _ _).symm hc') g ∧
      (∀ j, g.app j ≫ t'.app _ = t.app _) := by
  obtain ⟨i'⟩ := IsCofiltered.nonempty (C := I')
  obtain ⟨i, g, hi, hg⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation _ t
    (t'.app i') _ hc (f ≫ c'.π.app i') (by ext; simp [hf _ i'])
  let p' : c'.pt ⟶ S :=
    c'.π.app i' ≫ t'.app i'
  have hp' (j' : Over i') : c'.π.app j'.left ≫ t'.app j'.left = p' := by
    simp only [p']
    have h1 := t'.naturality j'.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h1
    have h2 := c'.π.naturality j'.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at h2
    rw [h2, Category.assoc, h1]
  let p : c.pt ⟶ S :=
    f ≫ p'
  have hp (j : Over i) : c.π.app j.left ≫ t.app j.left = p := by
    simp only [p, p', hf _ i']
  have hc₀ : IsLimit (Cone.whisker (Over.forget i) c) :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc
  have hc'₀ : IsLimit (Cone.whisker (Over.forget i') c') :=
    (Functor.Initial.isLimitWhiskerEquiv _ _).symm hc'
  have : IsCofiltered (Over i) := inferInstance
  have (j' : Over i') :
      PreservesColimit (Over.lift (Over.forget i ⋙ D) ((Over.forget i).whiskerLeft t)).op
        (yoneda.obj ((Over.lift (Over.forget i' ⋙ D')
        ((Over.forget i').whiskerLeft t')).obj j')) := by
    apply +allowSynthFailures @Scheme.preservesColimit_yoneda
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  obtain ⟨J, _, _, G, G', _, _, g, hg⟩ := Limits.exists_eq_isLimitMap_of_preservesColimit_yoneda
    (D := Over.lift (Over.forget i ⋙ D) (Functor.whiskerLeft _ t))
    (D' := Over.lift (Over.forget i' ⋙ D') (Functor.whiskerLeft _ t'))
    (c := Over.liftCone _ _ (c.whisker _) p hp)
    (c' := Over.liftCone _ _ (c'.whisker _) p' hp')
    (hc := Over.isLimitLiftCone _ _ _ _ _ hc₀)
    (hc' := Over.isLimitLiftCone _ _ _ _ _ hc'₀)
    (Over.homMk f rfl)
  use J, inferInstance, inferInstance, G ⋙ Over.forget _, G' ⋙ Over.forget _, inferInstance,
    inferInstance
  refine ⟨Functor.whiskerRight g (Over.forget S), ?_, ?_⟩
  · apply ((Functor.Initial.isLimitWhiskerEquiv (G' ⋙ Over.forget i') c').symm hc').hom_ext
    intro j
    rw [IsLimit.map_π]
    have := hg =≫ (Cone.whisker G'
      (Over.liftCone _ ((Over.forget i').whiskerLeft t') (Cone.whisker _ _) _ hp')).π.app j
    rw [IsLimit.map_π] at this
    simpa using congr($(this).left)
  · simp only [Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj, Functor.whiskerRight_app,
      Over.lift_obj, Functor.whiskerLeft_app, Over.forget_map]
    intro j
    simpa using Over.w (g.app j)

end AlgebraicGeometry
