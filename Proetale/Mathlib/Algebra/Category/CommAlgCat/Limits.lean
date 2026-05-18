import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Proetale.Mathlib.Algebra.Category.AlgCat.FilteredColimits
import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

universe u

open CategoryTheory Limits
open scoped MonoidalCategory

namespace CommAlgCat

variable {R : Type u} [CommRing R]

-- `AI generated`
instance preservesColimitsOfShape_tensorLeft
    {J : Type*} [Category J] [IsFiltered J] (M : CommAlgCat R) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft M) := by
  classical
  haveI : CategoryTheory.IsConnected J := CategoryTheory.IsFiltered.isConnected J
  refine ⟨?_⟩
  intro K
  refine ⟨?_⟩
  intro c hc
  refine ⟨?_⟩
  let t : Cocone (K ⋙ MonoidalCategory.tensorLeft M) :=
    (MonoidalCategory.tensorLeft M).mapCocone c
  -- A cocone on the constant diagram `M`, induced by left injections.
  let leftCocone (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      Cocone ((Functor.const J).obj M) :=
    { pt := s.pt
      ι :=
        { app := fun j => (binaryCofan M (K.obj j)).inl ≫ s.ι.app j
          naturality := by
            intro j j' u
            have hu := s.w u
            have hinl :
                (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u) = (binaryCofan M (K.obj j')).inl := by
              apply CommAlgCat.hom_ext
              ext x
              simp [binaryCofan, whiskerLeft_hom]
            have hu' := congrArg (fun f => (binaryCofan M (K.obj j)).inl ≫ f) hu
            -- Rewrite the left-hand side using `hinl`.
            -- `hu' : inl_j ≫ (M ◁ K.map u) ≫ s.ι.app j' = inl_j ≫ s.ι.app j`.
            have step1 :
                (binaryCofan M (K.obj j')).inl ≫ s.ι.app j' =
                  (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u) ≫ s.ι.app j' := by
              simpa [Category.assoc] using congrArg (fun f => f ≫ s.ι.app j') hinl.symm
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.comp_id]
            exact step1.trans hu' } }
  let leftMap (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : M ⟶ s.pt :=
    (isColimitConstCocone J M).desc (leftCocone s)
  -- A cocone on `K`, induced by right injections.
  let rightCocone (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : Cocone K :=
    { pt := s.pt
      ι :=
        { app := fun j => (binaryCofan M (K.obj j)).inr ≫ s.ι.app j
          naturality := by
            intro j j' u
            have hu := s.w u
            have hinr :
                (binaryCofan M (K.obj j)).inr ≫ (M ◁ K.map u) =
                  K.map u ≫ (binaryCofan M (K.obj j')).inr := by
              apply CommAlgCat.hom_ext
              ext x
              simp [binaryCofan, whiskerLeft_hom]
            simpa [Category.assoc, hinr] using
              congrArg (fun f => (binaryCofan M (K.obj j)).inr ≫ f) hu } }
  let rightMap (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : c.pt ⟶ s.pt :=
    hc.desc (rightCocone s)
  let descFun (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : t.pt ⟶ s.pt :=
    (binaryCofanIsColimit M c.pt).desc (BinaryCofan.mk (leftMap s) (rightMap s))
  have leftMap_eq (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) (j : J) :
      leftMap s = (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
    simpa [leftMap, leftCocone] using (isColimitConstCocone J M).fac (leftCocone s) j
  have rightMap_eq (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) (j : J) :
      c.ι.app j ≫ rightMap s = (binaryCofan M (K.obj j)).inr ≫ s.ι.app j :=
    hc.fac (rightCocone s) j
  have descFun_inl (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      (binaryCofan M c.pt).inl ≫ descFun s = leftMap s := by
    simpa [descFun, BinaryCofan.ι_app_left] using
      (binaryCofanIsColimit M c.pt).fac (BinaryCofan.mk (leftMap s) (rightMap s))
        (Discrete.mk WalkingPair.left)
  have descFun_inr (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) :
      (binaryCofan M c.pt).inr ≫ descFun s = rightMap s := by
    simpa [descFun, BinaryCofan.ι_app_right] using
      (binaryCofanIsColimit M c.pt).fac (BinaryCofan.mk (leftMap s) (rightMap s))
        (Discrete.mk WalkingPair.right)
  refine (show IsColimit t from ?_)
  refine ⟨descFun, ?_, ?_⟩
  · intro s j
    apply (BinaryCofan.IsColimit.hom_ext (binaryCofanIsColimit M (K.obj j)))
    · have hinl :
          (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl := by
        apply CommAlgCat.hom_ext
        ext x
        simp [binaryCofan, whiskerLeft_hom]
      -- left part
      have step1 : (binaryCofan M (K.obj j)).inl ≫ t.ι.app j ≫ descFun s =
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have step2 : (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s =
            (binaryCofan M c.pt).inl ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinl
      exact step1.trans (step2.trans ((descFun_inl s).trans (leftMap_eq s j)))
    · have hinr :
          (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
            c.ι.app j ≫ (binaryCofan M c.pt).inr := by
        apply CommAlgCat.hom_ext
        ext x
        simp [binaryCofan, whiskerLeft_hom]
      -- right part
      have rstep1 : (binaryCofan M (K.obj j)).inr ≫ t.ι.app j ≫ descFun s =
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have rstep2 : (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s =
            c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinr
      have rstep3 : c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s =
            c.ι.app j ≫ rightMap s := by
        simpa [Category.assoc] using congrArg (fun f => c.ι.app j ≫ f) (descFun_inr s)
      have rstep4 : c.ι.app j ≫ rightMap s =
            (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by simpa using rightMap_eq s j
      exact rstep1.trans (rstep2.trans (rstep3.trans rstep4))
  · intro s m hm
    apply (BinaryCofan.IsColimit.hom_ext (binaryCofanIsColimit M c.pt))
    · -- equality after `inl`
      have hleft : (binaryCofan M c.pt).inl ≫ m = leftMap s := by
        -- Use uniqueness for the colimit of the constant diagram.
        refine (isColimitConstCocone J M).uniq (leftCocone s) ((binaryCofan M c.pt).inl ≫ m) ?_
        intro j
        have hinl :
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl := by
          apply CommAlgCat.hom_ext
          ext x
          simp [binaryCofan, whiskerLeft_hom]
        have h := congrArg (fun f => (binaryCofan M (K.obj j)).inl ≫ f) (hm j)
        have h' :
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ m =
              (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
          simpa [t] using h
        have h'' :
            (binaryCofan M c.pt).inl ≫ m =
              (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
          have h₁ :
              ((binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j)) ≫ m =
                (binaryCofan M (K.obj j)).inl ≫ s.ι.app j := by
            simpa [Category.assoc] using h'
          have h₂ :
              (binaryCofan M c.pt).inl ≫ m =
                ((binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j)) ≫ m := by
            simpa [Category.assoc] using (congrArg (fun f => f ≫ m) hinl).symm
          exact h₂.trans h₁
        simpa [leftCocone] using h''
      exact hleft.trans (by simpa using (descFun_inl s).symm)
    · -- equality after `inr`
      have hright : (binaryCofan M c.pt).inr ≫ m = rightMap s := by
        -- Use that `c` is a colimit cocone.
        apply hc.hom_ext
        intro j
        have hinr :
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
              c.ι.app j ≫ (binaryCofan M c.pt).inr := by
          apply CommAlgCat.hom_ext
          ext x
          simp [binaryCofan, whiskerLeft_hom]
        have h := congrArg (fun f => (binaryCofan M (K.obj j)).inr ≫ f) (hm j)
        have h' :
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ m =
              (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by
          simpa [t] using h
        have h'' :
            c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ m =
              (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by
          simpa [Category.assoc, hinr] using h'
        -- Rewrite the RHS using the definition of `rightMap`.
        rw [rightMap_eq s j]
        simpa [Category.assoc] using h''
      exact hright.trans (by simpa using (descFun_inr s).symm)

-- `forget₂ (CommAlgCat R) CommRingCat` preserves filtered colimits because it factors as
-- `(commAlgCatEquivUnder R).functor ⋙ Under.forget R`, where the equivalence preserves all
-- colimits and `Under.forget` preserves connected (hence filtered) colimits.
instance preservesFilteredColimitsOfSize_forget_commRingCat :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) where
  preserves_filtered_colimits J _ _ := by
    have : IsConnected J := IsFiltered.isConnected J
    exact (inferInstance :
      PreservesColimitsOfShape J
        ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
          Under.forget (CommRingCat.of R)))

instance preservesFilteredColimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) :=
  HasForget₂.forget_comp (C := CommAlgCat.{u} R) (D := CommRingCat.{u}) ▸
    (Limits.comp_preservesFilteredColimits
        (forget₂ (CommAlgCat.{u} R) CommRingCat.{u})
        (forget CommRingCat.{u}) : PreservesFilteredColimitsOfSize.{u, u} _)

instance preservesFilteredColimitsOfSize_forget_algCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget (AlgCat.{u} R) =
        forget (CommAlgCat.{u} R) := HasForget₂.forget_comp
    have : HasColimitsOfShape J (AlgCat.{u} R) :=
      { has_colimit := fun F ↦ ⟨_, AlgCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
    have : PreservesColimitsOfShape J (forget (AlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (AlgCat.{u} R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (AlgCat.{u} R))
    have hpres : PreservesColimitsOfShape J (forget (CommAlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙ forget (AlgCat.{u} R)) :=
      h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R)) (forget (AlgCat.{u} R))

instance preservesLimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesLimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) := by
  have hfunctor : forget₂ (CommAlgCat.{u} R) CommRingCat.{u} =
      (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R) := rfl
  have : PreservesLimitsOfSize.{u, u} (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
    rw [hfunctor]
    infer_instance
  have h : forget₂ (CommAlgCat.{u} R) CommRingCat.{u} ⋙ forget CommRingCat.{u} =
      forget (CommAlgCat.{u} R) := HasForget₂.forget_comp
  rw [← h]
  infer_instance

instance : ReflectsFilteredColimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) where
  reflects_filtered_colimits _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

instance : IsIPC.{u} (CommAlgCat.{u} R) :=
  .of_preservesFilteredColimitsOfSize (forget (CommAlgCat.{u} R))

section Pi

variable {ι : Type u} (S : ι → CommAlgCat.{u} R)

/-- The fan given by the type theoretic product. -/
@[simps! pt]
def piFan : Fan S :=
  Fan.mk (.of R (∀ i, S i)) fun i ↦ ofHom <| Pi.evalAlgHom _ _ i

/-- The categorical product of `R`-algebras is the type theoretic product. -/
def isLimitPiFan : IsLimit (piFan S) where
  lift s := ofHom <| Pi.algHom R (fun i ↦ S i) (fun i ↦ (s.π.app ⟨i⟩).hom)
  fac s := fun ⟨i⟩ ↦ by
    apply CommAlgCat.hom_ext
    ext x
    rfl
  uniq s m hm := by
    apply CommAlgCat.hom_ext
    ext x
    funext i
    have hi := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hm ⟨i⟩)) x
    simp only [piFan_pt, Functor.const_obj_obj, Discrete.functor_obj_eq_as,
      ConcreteCategory.hom_ofHom, Pi.algHom_apply] at hi ⊢
    exact hi

end Pi

end CommAlgCat

instance AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u} (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) where
  preserves_filtered_colimits J _ _ := by
    have h : forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R) =
        forget (AlgCat.{u} R) := HasForget₂.forget_comp
    have : PreservesColimitsOfShape J (forget (ModuleCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : ReflectsColimitsOfShape J (forget (ModuleCat.{u} R)) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms (J := J) (G := forget (ModuleCat.{u} R))
    have hpres : PreservesColimitsOfShape J (forget (AlgCat.{u} R)) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits J
    have : PreservesColimitsOfShape J
        (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R)) :=
      h.symm ▸ hpres
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) (forget (ModuleCat.{u} R))
