import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Proetale.Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct

universe u

open CategoryTheory Limits
open scoped MonoidalCategory

namespace CommAlgCat

variable {R : Type u} [CommRing R]

-- Helper lemmas for whiskerLeft interactions with binaryCofan
private lemma binaryCofan_inl_whiskerLeft {M A B : CommAlgCat R} (f : A ⟶ B) :
    (binaryCofan M A).inl ≫ (M ◁ f) = (binaryCofan M B).inl := by
  ext1; dsimp
  exact Algebra.TensorProduct.map_comp_includeLeft _ _  |>.trans (AlgHom.comp_id _)

private lemma binaryCofan_inr_whiskerLeft {M A B : CommAlgCat R} (f : A ⟶ B) :
    (binaryCofan M A).inr ≫ (M ◁ f) = f ≫ (binaryCofan M B).inr := by
  ext1; dsimp
  exact Algebra.TensorProduct.map_comp_includeRight _ _

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
  let leftCocone (s : Cocone (K ⋙ MonoidalCategory.tensorLeft M)) : Cocone ((Functor.const J).obj M) :=
    { pt := s.pt
      ι :=
        { app := fun j => (binaryCofan M (K.obj j)).inl ≫ s.ι.app j
          naturality := by
            intro j j' u
            have hu := s.w u
            have hinl :
                (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u) = (binaryCofan M (K.obj j')).inl :=
              binaryCofan_inl_whiskerLeft _
            have hu' := congrArg (fun f => (binaryCofan M (K.obj j)).inl ≫ f) hu
            -- Rewrite the left-hand side using `hinl`.
            -- `hu' : inl_j ≫ (M ◁ K.map u) ≫ s.ι.app j' = inl_j ≫ s.ι.app j`.
            rw [show (binaryCofan M (K.obj j')).inl = (binaryCofan M (K.obj j)).inl ≫ (M ◁ K.map u)
                  from hinl.symm, Category.assoc]
            exact hu' } }

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
                  K.map u ≫ (binaryCofan M (K.obj j')).inr :=
              binaryCofan_inr_whiskerLeft _
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
      c.ι.app j ≫ rightMap s = (binaryCofan M (K.obj j)).inr ≫ s.ι.app j := by
    exact hc.fac (rightCocone s) j

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
          (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl :=
        binaryCofan_inl_whiskerLeft _
      -- left part
      have step1 : (binaryCofan M (K.obj j)).inl ≫ t.ι.app j ≫ descFun s =
          (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have step2 : (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) ≫ descFun s =
          (binaryCofan M c.pt).inl ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinl
      exact step1.trans (step2.trans ((descFun_inl s).trans (leftMap_eq s j)))
    · have hinr :
          (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
            c.ι.app j ≫ (binaryCofan M c.pt).inr :=
        binaryCofan_inr_whiskerLeft _
      -- right part
      have step1 : (binaryCofan M (K.obj j)).inr ≫ t.ι.app j ≫ descFun s =
          (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s := by simp [t]
      have step2 : (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) ≫ descFun s =
          c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s := by
        simpa [Category.assoc] using congrArg (fun f => f ≫ descFun s) hinr
      have step3 : c.ι.app j ≫ (binaryCofan M c.pt).inr ≫ descFun s = c.ι.app j ≫ rightMap s := by
        simpa [Category.assoc] using congrArg (fun f => c.ι.app j ≫ f) (descFun_inr s)
      exact step1.trans (step2.trans (step3.trans (rightMap_eq s j)))
  · intro s m hm
    apply (BinaryCofan.IsColimit.hom_ext (binaryCofanIsColimit M c.pt))
    · -- equality after `inl`
      have hleft : (binaryCofan M c.pt).inl ≫ m = leftMap s := by
        -- Use uniqueness for the colimit of the constant diagram.
        refine (isColimitConstCocone J M).uniq (leftCocone s) ((binaryCofan M c.pt).inl ≫ m) ?_
        intro j
        have hinl :
            (binaryCofan M (K.obj j)).inl ≫ (M ◁ c.ι.app j) = (binaryCofan M c.pt).inl :=
          binaryCofan_inl_whiskerLeft _
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
      rw [hleft]
      simpa using (descFun_inl s).symm
    · -- equality after `inr`
      have hright : (binaryCofan M c.pt).inr ≫ m = rightMap s := by
        -- Use that `c` is a colimit cocone.
        apply hc.hom_ext
        intro j
        have hinr :
            (binaryCofan M (K.obj j)).inr ≫ (M ◁ c.ι.app j) =
              c.ι.app j ≫ (binaryCofan M c.pt).inr :=
          binaryCofan_inr_whiskerLeft _
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
        have := (rightMap_eq s j).symm
        exact h''.trans this
      rw [hright]
      simpa using (descFun_inr s).symm

instance preservesColimitsOfSize_forget_commRingCat :
  -- Blueprint: lemma:commalgcat-colimits. forget₂ CommAlgCat CommRingCat preserves colimits.
    PreservesColimits (forget₂ (CommAlgCat R) CommRingCat) :=
  sorry

-- Helper: cocone compatibility at element level for AlgCat cocones over a CommAlgCat diagram
private lemma algCat_cocone_w_apply {J : Type*} [Category J]
    {R' : Type u} [CommRing R']
    {K : J ⥤ CommAlgCat R'}
    {s : Cocone (K ⋙ forget₂ (CommAlgCat R') (AlgCat R'))}
    {i j : J} (f : i ⟶ j) (a : K.obj i) :
    (s.ι.app i).hom a = (s.ι.app j).hom ((K.map f).hom a) :=
  (congrFun (congrArg DFunLike.coe (congrArg AlgCat.Hom.hom (s.w f))) a).symm

-- Helper: cocone compatibility at element level for CommAlgCat cocones
private lemma commAlgCat_cocone_w_apply {J : Type*} [Category J]
    {R' : Type u} [CommRing R']
    {K : J ⥤ CommAlgCat R'} {c : Cocone K}
    {i j : J} (f : i ⟶ j) (a : K.obj i) :
    (c.ι.app i).hom a = (c.ι.app j).hom ((K.map f).hom a) :=
  (congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom (c.w f))) a).symm

-- Joint surjectivity for filtered colimits in CommAlgCat: every element of the colimit
-- is in the image of some cocone map.
set_option backward.isDefEq.respectTransparency false in
private theorem jointly_surjective_of_isColimit
    {J : Type*} [Category J] [IsFiltered J]
    {R' : Type u} [CommRing R']
    {K : J ⥤ CommAlgCat R'} {c : Cocone K} (hc : IsColimit c)
    (x : c.pt) : ∃ (j : J) (y : K.obj j), (c.ι.app j).hom y = x := by
  have hne : Nonempty J := IsFiltered.nonempty
  let S : Subalgebra R' c.pt := {
    carrier := Set.range (fun (p : Σ j, K.obj j) => (c.ι.app p.1).hom p.2)
    mul_mem' := by
      intro x y hx hy
      obtain ⟨⟨i, a⟩, ha⟩ := hx; obtain ⟨⟨j, b⟩, hb⟩ := hy; simp only at ha hb
      obtain ⟨k, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      exact ⟨⟨k, (K.map fi).hom a * (K.map fj).hom b⟩, by
        change (c.ι.app k).hom _ = x * y
        rw [map_mul, ← commAlgCat_cocone_w_apply fi a,
            ← commAlgCat_cocone_w_apply fj b, ha, hb]⟩
    add_mem' := by
      intro x y hx hy
      obtain ⟨⟨i, a⟩, ha⟩ := hx; obtain ⟨⟨j, b⟩, hb⟩ := hy; simp only at ha hb
      obtain ⟨k, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      exact ⟨⟨k, (K.map fi).hom a + (K.map fj).hom b⟩, by
        change (c.ι.app k).hom _ = x + y
        rw [map_add, ← commAlgCat_cocone_w_apply fi a,
            ← commAlgCat_cocone_w_apply fj b, ha, hb]⟩
    algebraMap_mem' := fun r => by
      obtain ⟨j⟩ := hne
      exact ⟨⟨j, algebraMap R' (K.obj j) r⟩, (c.ι.app j).hom.commutes r⟩
    zero_mem' := by obtain ⟨j⟩ := hne; exact ⟨⟨j, 0⟩, map_zero (c.ι.app j).hom⟩
    one_mem' := by obtain ⟨j⟩ := hne; exact ⟨⟨j, 1⟩, map_one (c.ι.app j).hom⟩
  }
  let ιS (j : J) : (K.obj j : Type _) →ₐ[R'] S := {
    toRingHom := {
      toFun := fun a => ⟨(c.ι.app j).hom a, ⟨⟨j, a⟩, rfl⟩⟩
      map_one' := Subtype.ext (map_one (c.ι.app j).hom)
      map_mul' := fun a b => Subtype.ext (map_mul (c.ι.app j).hom a b)
      map_zero' := Subtype.ext (map_zero (c.ι.app j).hom)
      map_add' := fun a b => Subtype.ext (map_add (c.ι.app j).hom a b)
    }
    commutes' := fun r => Subtype.ext ((c.ι.app j).hom.commutes r)
  }
  let cS : Cocone K := {
    pt := CommAlgCat.of R' S
    ι := { app := fun j => CommAlgCat.ofHom (ιS j)
           naturality := by
             intro i j f; ext a; apply Subtype.ext
             show (c.ι.app j).hom ((K.map f).hom a) = (c.ι.app i).hom a
             exact (commAlgCat_cocone_w_apply f a).symm } }
  let incl : cS.pt ⟶ c.pt := CommAlgCat.ofHom (Subalgebra.val S)
  let r : c.pt ⟶ cS.pt := hc.desc cS
  have h_incl_r : r ≫ incl = 𝟙 c.pt := by
    apply hc.hom_ext; intro j; ext a
    show incl.hom (r.hom ((c.ι.app j).hom a)) = (c.ι.app j).hom a
    have h := congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom (hc.fac cS j))) a
    conv_lhs => rw [show r.hom ((c.ι.app j).hom a) = (ιS j) a from h]
    rfl
  have h_surj : Function.Surjective (S.val : S → c.pt) := fun y =>
    ⟨r.hom y, congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom h_incl_r)) y⟩
  obtain ⟨⟨_, ⟨⟨j, y⟩, rfl⟩⟩, hx⟩ := h_surj x
  exact ⟨j, y, hx⟩

attribute [local instance] IsFiltered.nonempty

-- forget₂ (CommAlgCat R) (AlgCat R) preserves filtered colimits at all universes.
-- Strategy: given a colimit c in CommAlgCat and a cocone s in AlgCat,
-- build the image subalgebra in s.pt (commutative because elements from commutative algebras commute),
-- construct a CommAlgCat cocone through the image, use hc.desc, and compose with inclusion.
set_option backward.isDefEq.respectTransparency false in
noncomputable
instance preservesFilteredColimitsOfSize_forget_algCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (CommAlgCat R) (AlgCat R)) := by
  refine ⟨fun J hJ hJ' ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩⟩
  have hne : Nonempty J := IsFiltered.nonempty
  -- Build image subalgebra in s.pt and show commutativity
  let imgAlg : Subalgebra R s.pt := {
    carrier := Set.range (fun (p : Σ j, K.obj j) =>
      ((s.ι.app p.1).hom p.2 : (s.pt : Type _)))
    mul_mem' := by
      intro x y hx hy
      obtain ⟨⟨i, a⟩, ha⟩ := hx; obtain ⟨⟨j, b⟩, hb⟩ := hy; simp only at ha hb
      obtain ⟨k, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      exact ⟨⟨k, (K.map fi).hom a * (K.map fj).hom b⟩, by
        change (s.ι.app k).hom _ = x * y
        rw [map_mul, ← show (s.ι.app i).hom a = _ from algCat_cocone_w_apply fi a,
                      ← show (s.ι.app j).hom b = _ from algCat_cocone_w_apply fj b, ha, hb]⟩
    add_mem' := by
      intro x y hx hy
      obtain ⟨⟨i, a⟩, ha⟩ := hx; obtain ⟨⟨j, b⟩, hb⟩ := hy; simp only at ha hb
      obtain ⟨k, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
      exact ⟨⟨k, (K.map fi).hom a + (K.map fj).hom b⟩, by
        change (s.ι.app k).hom _ = x + y
        rw [map_add, ← show (s.ι.app i).hom a = _ from algCat_cocone_w_apply fi a,
                      ← show (s.ι.app j).hom b = _ from algCat_cocone_w_apply fj b, ha, hb]⟩
    algebraMap_mem' := fun r => by
      obtain ⟨j⟩ := hne
      exact ⟨⟨j, algebraMap R (K.obj j) r⟩, (s.ι.app j).hom.commutes r⟩
    zero_mem' := by obtain ⟨j⟩ := hne; exact ⟨⟨j, 0⟩, map_zero (s.ι.app j).hom⟩
    one_mem' := by obtain ⟨j⟩ := hne; exact ⟨⟨j, 1⟩, map_one (s.ι.app j).hom⟩
  }
  have imgAlg_comm : ∀ (a b : imgAlg), a * b = b * a := by
    rintro ⟨x, ⟨⟨i, a⟩, ha⟩⟩ ⟨y, ⟨⟨j, b⟩, hb⟩⟩; simp only at ha hb
    obtain ⟨k, fi, fj, _⟩ := IsFilteredOrEmpty.cocone_objs i j
    apply Subtype.ext; show x * y = y * x
    rw [← ha, ← hb, algCat_cocone_w_apply fi a, algCat_cocone_w_apply fj b]
    show (s.ι.app k).hom ((K.map fi).hom a) * (s.ι.app k).hom ((K.map fj).hom b) =
         (s.ι.app k).hom ((K.map fj).hom b) * (s.ι.app k).hom ((K.map fi).hom a)
    rw [show (s.ι.app k).hom ((K.map fi).hom a) * (s.ι.app k).hom ((K.map fj).hom b) =
            (s.ι.app k).hom ((K.map fi).hom a * (K.map fj).hom b) from (map_mul _ _ _).symm,
        show (s.ι.app k).hom ((K.map fj).hom b) * (s.ι.app k).hom ((K.map fi).hom a) =
            (s.ι.app k).hom ((K.map fj).hom b * (K.map fi).hom a) from (map_mul _ _ _).symm,
        mul_comm]
  letI : CommRing imgAlg := { imgAlg.toRing with mul_comm := imgAlg_comm }
  -- CommAlgCat cocone through imgAlg
  let sComm : Cocone K := {
    pt := CommAlgCat.of R imgAlg
    ι := {
      app := fun j => CommAlgCat.ofHom {
        toRingHom := {
          toFun := fun a => ⟨(s.ι.app j).hom a, ⟨⟨j, a⟩, rfl⟩⟩
          map_one' := Subtype.ext (map_one (s.ι.app j).hom)
          map_mul' := fun a b => Subtype.ext (map_mul (s.ι.app j).hom a b)
          map_zero' := Subtype.ext (map_zero (s.ι.app j).hom)
          map_add' := fun a b => Subtype.ext (map_add (s.ι.app j).hom a b)
        }
        commutes' := fun r => Subtype.ext ((s.ι.app j).hom.commutes r)
      }
      naturality := by
        intro i j f; ext a; apply Subtype.ext
        show (s.ι.app j).hom ((K.map f).hom a) = (s.ι.app i).hom a
        exact (algCat_cocone_w_apply f a).symm
    }
  }
  let descComm := hc.desc sComm
  -- The desc in AlgCat: compose descComm with inclusion
  let descFun : ((forget₂ (CommAlgCat R) (AlgCat R)).mapCocone c).pt ⟶ s.pt :=
    AlgCat.ofHom (imgAlg.val.comp descComm.hom)
  refine ⟨descFun, fun j => ?_, fun f hf => ?_⟩
  · -- Factorization
    ext a
    show imgAlg.val (descComm.hom ((c.ι.app j).hom a)) = (s.ι.app j).hom a
    have h := congrFun (congrArg DFunLike.coe
      (congrArg CommAlgCat.Hom.hom (hc.fac sComm j))) a
    conv_lhs => rw [show descComm.hom ((c.ι.app j).hom a) = (sComm.ι.app j).hom a from h]
    rfl
  · -- Uniqueness: if f satisfies the factorization, then f = descFun
    ext x
    -- By joint surjectivity: x = (c.ι.app j).hom a for some j, a
    obtain ⟨j, a, ha⟩ := jointly_surjective_of_isColimit hc x
    rw [← ha]
    have hDesc : descFun.hom ((c.ι.app j).hom a) = (s.ι.app j).hom a := by
      show imgAlg.val (descComm.hom ((c.ι.app j).hom a)) = (s.ι.app j).hom a
      have h := congrFun (congrArg DFunLike.coe
        (congrArg CommAlgCat.Hom.hom (hc.fac sComm j))) a
      conv_lhs => rw [show descComm.hom ((c.ι.app j).hom a) = (sComm.ι.app j).hom a from h]
      rfl
    have hF : f.hom ((c.ι.app j).hom a) = (s.ι.app j).hom a := by
      have := hf j
      exact congrFun (congrArg DFunLike.coe (congrArg AlgCat.Hom.hom this)) a
    rw [hDesc, hF]

/-- Natural isomorphism between `forget (CommAlgCat R)` and the composition through
the equivalence `CommAlgCat R ≌ Under (CommRingCat.of R)`. -/
private noncomputable def forgetNatIso (R : Type u) [CommRing R] :
    forget (CommAlgCat.{u} R) ≅
      (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
        Under.forget (CommRingCat.of R) ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun A => Iso.refl _) (by intros; dsimp; rfl)

-- forget₂ to CommRingCat preserves filtered colimits: factors through equivalence + Under.forget
instance preservesFilteredColimits_forget₂_commRingCat (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  show PreservesFilteredColimits <|
    (commAlgCatEquivUnder (.of R)).functor ⋙ Under.forget (CommRingCat.of R)
  infer_instance

-- forget preserves filtered colimits at {u, u}: forget = forget₂ ⋙ forget CommRingCat
instance preservesFilteredColimits_forget (R : Type u) [CommRing R] :
    PreservesFilteredColimits (forget (CommAlgCat.{u} R)) := by
  rw [show forget (CommAlgCat.{u} R) = forget₂ (CommAlgCat.{u} R) CommRingCat ⋙ forget CommRingCat
    from HasForget₂.forget_comp.symm]
  exact comp_preservesFilteredColimits _ _

-- Note: The output universe parameters of PreservesFilteredColimitsOfSize cannot be
-- resolved to {u, u} automatically; a direct colimit construction (like Under.forget's
-- instance in Preserves/Over.lean) would be needed for full generality. For now we use sorry.
-- The downstream uses (IsIPC, ReflectsFilteredColimitsOfSize) only need {u, u},
-- which is provided by the preservesFilteredColimits_forget instance above.
instance preservesFilteredColimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget (CommAlgCat.{u} R)) :=
  -- Blueprint: lemma:commalgcat-colimits. forget CommAlgCat preserves filtered colimits.
  sorry

instance preservesLimitsOfSize_forget (R : Type u) [CommRing R] :
    PreservesLimitsOfSize.{u, u} (forget (CommAlgCat.{u} R)) := by
  -- forget factors as: CommAlgCat R ≃ Under (CommRingCat.of R) → CommRingCat → Type
  -- The equivalence preserves limits, Under.forget creates (hence preserves) limits,
  -- and forget CommRingCat preserves limits.
  have h1 : PreservesLimitsOfSize.{u, u}
      (commAlgCatEquivUnder (CommRingCat.of R)).functor := inferInstance
  have h2 : PreservesLimitsOfSize.{u, u} (Under.forget (CommRingCat.of R)) := inferInstance
  have h3 : PreservesLimitsOfSize.{u, u} (forget CommRingCat.{u}) := inferInstance
  exact preservesLimits_of_natIso (forgetNatIso R).symm

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
def isLimitPiFan : IsLimit (piFan S) :=
  mkFanLimit _ (fun s => ofHom <| Pi.algHom R (fun i => ↑(S i)) fun i => (s.proj i).hom)
    (fun s i => by ext; simp [piFan])
    (fun s m hm => hom_ext <| DFunLike.ext _ _ fun x => funext fun i =>
      DFunLike.congr_fun (congrArg Hom.hom (hm i)) x)

end Pi

end CommAlgCat

instance AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat (R : Type u) [CommRing R] :
    PreservesFilteredColimitsOfSize (forget₂ (AlgCat R) (ModuleCat R)) :=
  -- Blueprint: lemma:commalgcat-colimits. forget₂ AlgCat ModuleCat preserves filtered colimits.
  sorry
