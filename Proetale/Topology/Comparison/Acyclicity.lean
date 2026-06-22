/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.Cartan
import Proetale.Topology.Comparison.CechColimit
import Proetale.Topology.Comparison.SectionsColimit
import Proetale.Topology.Comparison.FreeSheaf

/-!
# Acyclicity of pullbacks of injective sheaves on affine pro-étale objects

For an injective abelian sheaf `I` on the small étale site of a scheme `S`, the pullback
`ν^*I` to the pro-étale site has vanishing higher cohomology on every affine pro-étale
object. This is the key analytic input in the comparison of étale and pro-étale cohomology
([BS15, proof of Corollary 5.1.6]).

The proof is via Cartan's criterion (`CategoryTheory.Sheaf.ext_free_eq_zero_of_cech`):
every covering sieve of an affine pro-étale object refines through a single surjection
`q : W ⟶ U` between affine pro-étale objects which admits a relative limit presentation by
surjective étale covers at finite levels; the Čech complex of `ν^*I` along `q` is the
filtered colimit of the Čech complexes of `I` along the finite-level covers, each of which
is exact because `I` is injective.
-/

universe u

open CategoryTheory Limits Opposite Abelian

open scoped Simplicial

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

namespace AffineProEt

/-- Regard a pro-étale object with pro-affine-étale structure morphism as an object of the
affine pro-étale site. -/
def ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) : S.AffineProEt :=
  AffineProEt.mk X.hom hX

lemma toProEt_obj_ofProEt (X : S.ProEt) (hX : proAffineEtale X.hom) :
    (AffineProEt.toProEt S).obj (ofProEt X hX) = X :=
  rfl

/-- A variant of `AffineProEt.exists_surjective_factorization` which additionally records
that the open pieces `j i : V i ⟶ W` have pairwise disjoint ranges: `W` is the disjoint
union `Spec (∏ᵢ Γ(Vᵢ))` of the `V i`. -/
lemma exists_surjective_factorization_disjoint {X : S.AffineProEt} {ι : Type u} [Finite ι]
    (V : ι → S.AffineProEt) (f : ∀ i, V i ⟶ X)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ X) (j : ∀ i, V i ⟶ W),
      Surjective q.left ∧ (∀ i, j i ≫ q = f i) ∧ (∀ i, IsOpenImmersion (j i).left) ∧
      (∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by
  -- The product of the rings of global sections; `Spec` of it is the disjoint union.
  let R : CommRingCat.{u} := .of (Π i, Γ((V i).left, ⊤))
  let φ : Γ(X.left, ⊤) ⟶ R := CommRingCat.ofHom (Pi.ringHom fun i ↦ ((f i).left.appTop).hom)
  have hφ : φ.hom.IndEtale :=
    RingHom.IndEtale.pi _ fun i ↦ indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (f i))
  let q₀ : Spec R ⟶ X.left := Spec.map φ ≫ X.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφ)
  let W : S.AffineProEt := mk (q₀ ≫ X.hom) (proAffineEtale.comp_mem _ _ hq₀ X.prop)
  let q : W ⟶ X := MorphismProperty.Over.homMk q₀ rfl trivial
  let e : ∀ i, (V i).left ⟶ Spec R := fun i ↦
    (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))
  have he : ∀ i, e i ≫ q₀ = (f i).left := by
    intro i
    have h1 : φ ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = (f i).left.appTop := by
      ext x
      rfl
    change ((V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))) ≫
      Spec.map φ ≫ X.left.isoSpec.inv = (f i).left
    rw [Category.assoc, ← Spec.map_comp_assoc, h1, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hw : ∀ i, e i ≫ W.hom = (V i).hom := fun i ↦ by
    change e i ≫ q₀ ≫ X.hom = (V i).hom
    rw [← Category.assoc, he i, MorphismProperty.Over.w (f i)]
  let j : ∀ i, V i ⟶ W := fun i ↦ MorphismProperty.Over.homMk (e i) (hw i) trivial
  have hcomp : ∀ i, j i ≫ q = f i := by
    intro i
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left]
    exact he i
  have hoiSpec (i : ι) : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i))) := by
    rw [← ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i]
    infer_instance
  have hoi : ∀ i, IsOpenImmersion (j i).left := fun i ↦ by
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    rw [hj]
    haveI := hoiSpec i
    infer_instance
  -- The pieces `j i` factor through `sigmaSpec` via the coproduct inclusions.
  have key : ∀ (i : ι) (c : (V i).left),
      (j i).left c =
        (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
          ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) := by
    intro i c
    have hj : (j i).left = (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := rfl
    calc (j i).left c
        = (Spec.map (CommRingCat.ofHom
            (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)))
            ((V i).left.isoSpec.hom c) := by
          rw [hj]; exact Scheme.Hom.comp_apply _ _ _
      _ = (Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i ≫ sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((V i).left.isoSpec.hom c) :=
          congrArg (fun g ↦ g ((V i).left.isoSpec.hom c))
            (ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i).symm
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i) ((V i).left.isoSpec.hom c)) :=
          Scheme.Hom.comp_apply _ _ _
  have hcov : ∀ w : W.left, ∃ i, w ∈ Set.range ((j i).left.base) := by
    intro w
    obtain ⟨p, hp⟩ := (sigmaSpec fun i ↦ Γ((V i).left, ⊤)).surjective w
    obtain ⟨i, y, hy⟩ : ∃ (i : ι) (y : Spec (Γ((V i).left, ⊤))),
        ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i) y = p :=
      ⟨_, (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).covers p⟩
    have h2 : (V i).left.isoSpec.inv ≫ e i =
        Spec.map (CommRingCat.ofHom
          (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) := by
      change (V i).left.isoSpec.inv ≫ (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i)) = _
      rw [Iso.inv_hom_id_assoc]
    have hmor : (V i).left.isoSpec.inv ≫ (j i).left =
        (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
          sigmaSpec fun k ↦ Γ((V k).left, ⊤) := by
      have hj : (j i).left = e i := rfl
      rw [hj, h2, show (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i =
        Sigma.ι (fun k ↦ Spec (Γ((V k).left, ⊤))) i from rfl, ι_sigmaSpec]
    refine ⟨i, (V i).left.isoSpec.inv y, ?_⟩
    calc (j i).left ((V i).left.isoSpec.inv y)
        = ((V i).left.isoSpec.inv ≫ (j i).left) y := (Scheme.Hom.comp_apply _ _ _).symm
      _ = ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i ≫
            sigmaSpec fun k ↦ Γ((V k).left, ⊤)) y := congrArg (fun g ↦ g y) hmor
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤))
            ((sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).f i y) :=
          Scheme.Hom.comp_apply _ _ _
      _ = (sigmaSpec fun k ↦ Γ((V k).left, ⊤)) p := by rw [hy]
      _ = w := hp
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨(e i).base y, ?_⟩
    calc q₀.base ((e i).base y) = (e i ≫ q₀).base y := rfl
      _ = (f i).left.base y := by rw [he i]
      _ = x := hy
  -- Disjointness of the ranges of the pieces, via disjointness of the coproduct components.
  have hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hinj : Function.Injective (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).base :=
      (sigmaSpec fun m ↦ Γ((V m).left, ⊤)).isOpenEmbedding.injective
    have heq : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) =
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l) ((V l).left.isoSpec.hom b) := by
      apply hinj
      rw [← key k a, ← key l b]
      exact ha.trans hb.symm
    have hd := disjoint_opensRange_sigmaι (fun m ↦ Spec (Γ((V m).left, ⊤))) k l hkl
    have hmem : (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k) ((V k).left.isoSpec.hom a) ∈
        (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) k).opensRange ⊓
          (Sigma.ι (fun m ↦ Spec (Γ((V m).left, ⊤))) l).opensRange :=
      ⟨⟨_, rfl⟩, ⟨_, heq.symm⟩⟩
    simpa using hd.le_bot hmem
  exact ⟨W, q, j, ⟨hq₀surj⟩, hcomp, hoi, hcov, hdisj⟩

/-- **(D1)** Every covering sieve of an affine pro-étale object contains a finite jointly
surjective family which factors through a single surjective morphism `q : W ⟶ U₀` whose
source decomposes into finitely many disjoint open pieces mapping into the sieve. -/
lemma exists_singleton_refinement (U₀ : S.AffineProEt)
    {R : Sieve ((AffineProEt.toProEt S).obj U₀)}
    (hR : R ∈ ProEt.topology S ((AffineProEt.toProEt S).obj U₀)) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U₀) (ι : Type u) (_ : Finite ι)
      (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W),
      Surjective q.left ∧
      (∀ k, R.arrows ((AffineProEt.toProEt S).map (j k ≫ q))) ∧
      (∀ k, IsOpenImmersion (j k).left) ∧
      (∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base)) ∧
      (Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
        (Set.range ((j l).left.base))) := by
  -- The pullback of `R` to the affine pro-étale site is a covering sieve, since the
  -- affine pro-étale site is a dense subsite of the pro-étale site.
  have hR' : R.functorPullback (AffineProEt.toProEt S) ∈ AffineProEt.topology S U₀ :=
    Functor.IsCoverDense.functorPullback_pushforward_covering
      (G := AffineProEt.toProEt S) (K := ProEt.topology S) ⟨R, hR⟩
  obtain ⟨ι, _, V, f, hf, hsurj⟩ := exists_finite_jointly_surjective_of_mem_topology hR'
  obtain ⟨W, q, j, hq, hcomp, hoi, hcov, hdisj⟩ :=
    exists_surjective_factorization_disjoint V f hsurj
  refine ⟨W, q, ι, ‹_›, V, j, hq, fun k ↦ ?_, hoi, hcov, hdisj⟩
  rw [hcomp k]
  exact hf k

/-- A surjective morphism in the affine pro-étale site generates a covering sieve of the
pro-étale topology. -/
lemma generate_singleton_toProEt_map_mem {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
    (hq : Surjective q.left) :
    Sieve.generate (Presieve.singleton ((AffineProEt.toProEt S).map q)) ∈
      ProEt.topology S ((AffineProEt.toProEt S).obj U₀) := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton,
    AffineProEt.toProEt_map, Functor.comp_obj, ProEt.forget_obj, Over.forget_obj,
    AffineProEt.toProEt_obj_left, Functor.comp_map, ProEt.forget_map, Over.forget_map]
  haveI : Surjective q.left := hq
  exact Scheme.Hom.singleton_mem_propQCPrecoverage inferInstance

/-- The structure morphism of the `(n+1)`-fold fibre product of `W` over `U₀` in the
pro-étale site is pro-affine-étale, by induction on `n` using closure of pro-affine-étale
structure maps under binary pullbacks. -/
lemma proAffineEtale_widePullback_hom {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (n : ℕ) :
    proAffineEtale (widePullback ((AffineProEt.toProEt S).obj U₀)
      (fun _ : Fin (n + 1) ↦ (AffineProEt.toProEt S).obj W)
      (fun _ ↦ (AffineProEt.toProEt S).map q)).hom := by
  induction n with
  | zero =>
    -- The unary wide pullback is isomorphic to `W` via the projection.
    set g := (AffineProEt.toProEt S).map q
    let l : (AffineProEt.toProEt S).obj W ⟶
        widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin 1 ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) :=
      WidePullback.lift g (fun _ ↦ 𝟙 _) (fun _ ↦ Category.id_comp g)
    have h1 : WidePullback.π (fun _ : Fin 1 ↦ g) 0 ≫ l = 𝟙 _ := by
      apply WidePullback.hom_ext
      · intro i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, WidePullback.lift_base, WidePullback.π_arrow, Category.id_comp]
    have h2 : l ≫ WidePullback.π (fun _ : Fin 1 ↦ g) 0 = 𝟙 _ :=
      WidePullback.lift_π _ _ _ _ 0
    haveI : IsIso (WidePullback.π (fun _ : Fin 1 ↦ g) 0) := ⟨l, h1, h2⟩
    haveI : IsIso (WidePullback.π (fun _ : Fin 1 ↦ g) 0).left :=
      inferInstanceAs (IsIso ((ProEt.forget S ⋙ Over.forget S).map
        (WidePullback.π (fun _ : Fin 1 ↦ g) 0)))
    have hw : (WidePullback.π (fun _ : Fin 1 ↦ g) 0).left ≫
        ((AffineProEt.toProEt S).obj W).hom =
          (widePullback ((AffineProEt.toProEt S).obj U₀)
            (fun _ : Fin 1 ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g)).hom :=
      MorphismProperty.Over.w _
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso proAffineEtale _ _).mpr W.prop
  | succ n ih =>
    set g := (AffineProEt.toProEt S).map q
    -- The restriction morphism forgetting the first coordinate.
    let r : widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin (n + 2) ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) ⟶
        widePullback ((AffineProEt.toProEt S).obj U₀)
          (fun _ : Fin (n + 1) ↦ (AffineProEt.toProEt S).obj W) (fun _ ↦ g) :=
      WidePullback.lift (WidePullback.base _)
        (fun i ↦ WidePullback.π _ i.succ) (fun i ↦ WidePullback.π_arrow _ _)
    have hsq : WidePullback.π (fun _ : Fin (n + 2) ↦ g) 0 ≫ g =
        r ≫ WidePullback.base _ := by
      rw [WidePullback.π_arrow, WidePullback.lift_base]
    -- The `(n+2)`-fold fibre product is the binary pullback of the `(n+1)`-fold one with `W`.
    have hpb : IsPullback (WidePullback.π (fun _ : Fin (n + 2) ↦ g) 0) r g
        (WidePullback.base _) := by
      refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hsq
        (fun s ↦ WidePullback.lift (s.snd ≫ WidePullback.base _)
          (fun i ↦ Fin.cases s.fst (fun i' ↦ s.snd ≫ WidePullback.π _ i') i) ?_)
        (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_))
      · intro i
        induction i using Fin.cases with
        | zero => simpa using s.condition
        | succ i' => simp only [Fin.cases_succ, Category.assoc, WidePullback.π_arrow]
      · simp only [WidePullback.lift_π, Fin.cases_zero]
      · apply WidePullback.hom_ext
        · intro i
          rw [Category.assoc,
            show r ≫ WidePullback.π _ i = WidePullback.π _ i.succ from
              WidePullback.lift_π _ _ _ _ i,
            WidePullback.lift_π]
          simp
        · rw [Category.assoc,
            show r ≫ WidePullback.base _ = WidePullback.base _ from
              WidePullback.lift_base _ _ _ _,
            WidePullback.lift_base]
      · apply WidePullback.hom_ext
        · intro i
          rw [WidePullback.lift_π]
          induction i using Fin.cases with
          | zero => simpa using hm₁
          | succ i' =>
            have h3 : m ≫ WidePullback.π _ i'.succ = m ≫ r ≫ WidePullback.π _ i' := by
              rw [show r ≫ WidePullback.π _ i' = WidePullback.π _ i'.succ from
                WidePullback.lift_π _ _ _ _ i']
            rw [h3, ← Category.assoc, hm₂]
            simp
        · rw [WidePullback.lift_base]
          have h3 : m ≫ WidePullback.base _ = m ≫ r ≫ WidePullback.base _ := by
            rw [show r ≫ WidePullback.base _ = WidePullback.base _ from
              WidePullback.lift_base _ _ _ _]
          rw [h3, ← Category.assoc, hm₂]
    -- Transfer to `Over S` and apply closure of pro-affine-étale structure maps
    -- under pullbacks.
    have hpbO := hpb.map (ProEt.forget S)
    refine ObjectProperty.prop_of_isLimit (P := proAffineEtale.overObj (X := S))
      hpbO.isLimit ?_
    rintro (_ | _ | _)
    · exact U₀.prop
    · exact W.prop
    · exact ih

/-- **(D2)** The Čech nerve of a morphism of affine pro-étale objects consists of objects
with pro-affine-étale structure morphism. -/
lemma proAffineEtale_cechNerve_hom {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (n : ℕ) :
    proAffineEtale
      ((Arrow.mk ((AffineProEt.toProEt S).map q)).cechNerve.obj (op ⦋n⦌)).hom :=
  proAffineEtale_widePullback_hom q n

/-- Points of pullbacks in the pro-étale site surject onto compatible pairs of points. -/
lemma _root_.AlgebraicGeometry.Scheme.ProEt.exists_left_base_preimage
    {P X Y Z : S.ProEt} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X.left) (y : Y.left)
    (hxy : f.left.base x = g.left.base y) :
    ∃ p : P.left, fst.left.base p = x ∧ snd.left.base p = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have hL : IsPullback fst.left snd.left f.left g.left :=
    h.map (ProEt.forget S ⋙ Over.forget S)
  refine ⟨hL.isoPullback.inv.base z, ?_, ?_⟩
  · calc fst.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ fst.left).base z := rfl
      _ = (pullback.fst f.left g.left).base z := by rw [hL.isoPullback_inv_fst]
      _ = x := hz₁
  · calc snd.left.base (hL.isoPullback.inv.base z)
        = (hL.isoPullback.inv ≫ snd.left).base z := rfl
      _ = (pullback.snd f.left g.left).base z := by rw [hL.isoPullback_inv_snd]
      _ = y := hz₂

/-- A jointly surjective family of open immersions in the pro-étale site generates a
covering sieve for the pro-étale topology. -/
lemma _root_.AlgebraicGeometry.Scheme.ProEt.generate_ofArrows_mem_topology
    {X : S.ProEt} {κ : Type u} {V : κ → S.ProEt} (g : ∀ i, V i ⟶ X)
    (hoi : ∀ i, IsOpenImmersion (g i).left)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((g i).left.base)) :
    Sieve.generate (Presieve.ofArrows V g) ∈ ProEt.topology S X := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, Functor.comp_map,
    ProEt.forget_map, Over.forget_map]
  apply zariskiPrecoverage_le_propQCPrecoverage
  rw [Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hsurj, hoi⟩

/-- Coproducts of abelian sheaves on the pro-étale site indexed by a `u`-small type.
Typeclass search for this instance is catastrophically slow (it explores
countable-coproduct candidate paths and explodes in `whnf`), so we register the
generic instance explicitly. -/
instance (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

/-- Finite biproducts of abelian sheaves on the pro-étale site. Typeclass search fails
to find this through the `Abelian` instance, so we register it explicitly. -/
instance : HasFiniteBiproducts (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Abelian.hasFiniteBiproducts

instance (ι : Type u) [Finite ι] :
    HasBiproductsOfShape ι (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  hasBiproductsOfShape_finite (Sheaf (ProEt.topology S) Ab.{u + 1})

/-- The canonical map from the coproduct of the free abelian sheaves on finitely many
disjoint open pieces covering `W` to the free abelian sheaf on `W` is an isomorphism:
the corresponding map of presheaves of types is locally bijective. -/
lemma isIso_sigmaDesc_freeAbelianSheafFunctor_map {W : S.AffineProEt}
    {ι : Type u} (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W)
    (hoi : ∀ k, IsOpenImmersion (j k).left)
    (hcov : ∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base))
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base))) :
    IsIso (Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map (j k))) := by
  classical
  -- The comparison map of presheaves of types from the coproduct of the pieces to `W`.
  let y : ι → ((S.ProEt)ᵒᵖ ⥤ Type (u + 1)) :=
    fun k ↦ uliftYoneda.{u + 1}.obj ((AffineProEt.toProEt S).obj (V k))
  let φ : (∐ y) ⟶ uliftYoneda.{u + 1}.obj ((AffineProEt.toProEt S).obj W) :=
    Sigma.desc fun k ↦ uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))
  -- Sections of the coproduct come from the components.
  have jointly_surj : ∀ (T : (S.ProEt)ᵒᵖ) (x : ToType ((∐ y).obj T)),
      ∃ (k : ι) (z : ToType ((y k).obj T)), (Sigma.ι y k).app T z = x := by
    intro T x
    obtain ⟨⟨k⟩, z, hz⟩ := Types.jointly_surjective
      (Discrete.functor y ⋙ (CategoryTheory.evaluation (S.ProEt)ᵒᵖ (Type (u + 1))).obj T)
      (isColimitOfPreserves ((CategoryTheory.evaluation (S.ProEt)ᵒᵖ (Type (u + 1))).obj T)
        (colimit.isColimit (Discrete.functor y))) x
    exact ⟨k, z, hz⟩
  -- The comparison map evaluated on a component.
  have happ : ∀ (k : ι) (T : (S.ProEt)ᵒᵖ) (z : ToType ((y k).obj T)),
      φ.app T ((Sigma.ι y k).app T z) =
        (uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))).app T z := by
    intro k T z
    have h := NatTrans.congr_app (Sigma.ι_desc
      (f := y) (fun k ↦ uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))) k) T
    calc φ.app T ((Sigma.ι y k).app T z)
        = ((Sigma.ι y k).app T ≫ φ.app T) z := (ConcreteCategory.comp_apply _ _ _).symm
      _ = ((Sigma.ι y k ≫ φ).app T) z := by rw [NatTrans.comp_app]
      _ = (uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k))).app T z :=
          ConcreteCategory.congr_hom h z
  -- The comparison map is locally surjective: the pieces pull back to a Zariski cover.
  haveI : Presheaf.IsLocallySurjective (ProEt.topology S) φ := by
    constructor
    intro T s
    have hpboi : ∀ k, IsOpenImmersion
        (pullback.fst s.down ((AffineProEt.toProEt S).map (j k))).left := by
      intro k
      exact MorphismProperty.of_isPullback
        (((IsPullback.of_hasPullback s.down ((AffineProEt.toProEt S).map (j k))).flip).map
          (ProEt.forget S ⋙ Over.forget S)) (hoi k)
    have hpbsurj : ∀ x : T.left, ∃ k, x ∈ Set.range
        ((pullback.fst s.down ((AffineProEt.toProEt S).map (j k))).left.base) := by
      intro x
      obtain ⟨k, v, hv⟩ := hcov (s.down.left.base x)
      obtain ⟨pt, hp₁, -⟩ := ProEt.exists_left_base_preimage
        (IsPullback.of_hasPullback s.down ((AffineProEt.toProEt S).map (j k))) x v hv.symm
      exact ⟨k, pt, hp₁⟩
    refine (ProEt.topology S).superset_covering ?_
      (ProEt.generate_ofArrows_mem_topology
        (fun k ↦ pullback.fst s.down ((AffineProEt.toProEt S).map (j k))) hpboi hpbsurj)
    rintro T' h ⟨Z, h', l, ⟨k⟩, rfl⟩
    refine ⟨(Sigma.ι y k).app (op T')
      (ULift.up (h' ≫ pullback.snd s.down ((AffineProEt.toProEt S).map (j k)))), ?_⟩
    rw [happ]
    change ULift.up ((h' ≫ pullback.snd s.down ((AffineProEt.toProEt S).map (j k))) ≫
        (AffineProEt.toProEt S).map (j k)) =
      ULift.up ((h' ≫ pullback.fst s.down ((AffineProEt.toProEt S).map (j k))) ≫ s.down)
    refine congrArg ULift.up ?_
    rw [Category.assoc, Category.assoc, ← pullback.condition]
  -- The comparison map is locally injective, by disjointness of the pieces.
  haveI : Presheaf.IsLocallyInjective (ProEt.topology S) φ := by
    constructor
    intro T x₁ x₂ hx
    obtain ⟨k₁, z₁, hz₁⟩ := jointly_surj T x₁
    obtain ⟨k₂, z₂, hz₂⟩ := jointly_surj T x₂
    have heq : z₁.down ≫ (AffineProEt.toProEt S).map (j k₁) =
        z₂.down ≫ (AffineProEt.toProEt S).map (j k₂) := by
      have e₁ : φ.app T x₁ =
          ULift.up (z₁.down ≫ (AffineProEt.toProEt S).map (j k₁)) := by
        rw [← hz₁, happ]; rfl
      have e₂ : φ.app T x₂ =
          ULift.up (z₂.down ≫ (AffineProEt.toProEt S).map (j k₂)) := by
        rw [← hz₂, happ]; rfl
      exact congrArg ULift.down (e₁.symm.trans (hx.trans e₂))
    by_cases hk : k₁ = k₂
    · -- equal indices: the two sections agree since the piece is a monomorphism
      subst hk
      haveI hm : Mono ((j k₁).left) := inferInstance
      haveI : Mono ((AffineProEt.toProEt S).map (j k₁)) :=
        Functor.mono_of_mono_map (F := ProEt.forget S ⋙ Over.forget S)
          (f := (AffineProEt.toProEt S).map (j k₁)) hm
      have hzz : z₁ = z₂ := ULift.ext _ _ ((cancel_mono _).mp heq)
      rw [← hz₁, ← hz₂, hzz, Presheaf.equalizerSieve_self_eq_top]
      exact (ProEt.topology S).top_mem _
    · -- distinct indices: the object is empty by disjointness of the pieces
      haveI : IsEmpty T.unop.left := by
        constructor
        intro t
        have h1 : (j k₁).left.base (z₁.down.left.base t) =
            (j k₂).left.base (z₂.down.left.base t) := by
          have h2 := congrArg
            (fun (m : T.unop ⟶ (AffineProEt.toProEt S).obj W) ↦ m.left.base t) heq
          simpa [MorphismProperty.Comma.comp_left] using h2
        exact Set.disjoint_left.mp (hdisj hk) ⟨_, rfl⟩ ⟨_, h1.symm⟩
      exact (ProEt.topology S).superset_covering bot_le (ProEt.bot_mem_topology T.unop)
  -- Hence the comparison map of free abelian sheaves is an isomorphism.
  have hWφ : (ProEt.topology S).W φ :=
    (ProEt.topology S).W_of_isLocallyBijective φ
  have hW2 : (ProEt.topology S).W (Functor.whiskerRight φ AddCommGrpCat.free.{u + 1}) :=
    hWφ.whiskerRight_free
  haveI hiso : IsIso ((presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
      (Functor.whiskerRight φ AddCommGrpCat.free.{u + 1})) := by
    rw [← GrothendieckTopology.W_iff]
    exact hW2
  -- The sheaf-level comparison map from the coproduct of the free sheaves on the pieces.
  let L₁ := (Functor.whiskeringRight (S.ProEt)ᵒᵖ (Type (u + 1)) Ab.{u + 1}).obj
    AddCommGrpCat.free.{u + 1}
  haveI : L₁.IsLeftAdjoint :=
    (Adjunction.whiskerRight (S.ProEt)ᵒᵖ AddCommGrpCat.adj.{u + 1}).isLeftAdjoint
  haveI : IsIso ((presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
      (L₁.map φ)) := hiso
  have hceq : (Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
        ((AffineProEt.toProEt S).map (j k))) =
      sigmaComparison (presheafToSheaf (ProEt.topology S) Ab.{u + 1})
        (fun k ↦ L₁.obj (y k)) ≫
      (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (sigmaComparison L₁ y) ≫
      (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (L₁.map φ) := by
    refine colimit.hom_ext fun ⟨k⟩ ↦ ?_
    change Sigma.ι _ k ≫ _ = Sigma.ι _ k ≫ _
    rw [Sigma.ι_desc]
    have hk : Sigma.ι (fun k ↦ (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).obj
          (L₁.obj (y k))) k ≫
        sigmaComparison (presheafToSheaf (ProEt.topology S) Ab.{u + 1})
          (fun k ↦ L₁.obj (y k)) ≫
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (sigmaComparison L₁ y) ≫
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map (L₁.map φ) =
        (presheafToSheaf (ProEt.topology S) Ab.{u + 1}).map
          (L₁.map (Sigma.ι y k ≫ φ)) := by
      rw [ι_comp_sigmaComparison_assoc, ← Functor.map_comp_assoc, ι_comp_sigmaComparison,
        ← Functor.map_comp, ← Functor.map_comp]
    have hφk : Sigma.ι y k ≫ φ =
        uliftYoneda.{u + 1}.map ((AffineProEt.toProEt S).map (j k)) :=
      Sigma.ι_desc _ k
    exact (hk.trans (congrArg (fun t ↦ (presheafToSheaf (ProEt.topology S)
      Ab.{u + 1}).map (L₁.map t)) hφk)).symm
  rw [hceq]
  infer_instance

/-- **(D4)** If an `Ext`-class on `U₀` vanishes on the finitely many disjoint pieces of a
decomposition of `W`, it vanishes after restriction along `q : W ⟶ U₀`. -/
lemma ext_comp_eq_zero_of_components {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
    {ι : Type u} [Finite ι] (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W)
    (hoi : ∀ k, IsOpenImmersion (j k).left)
    (hcov : ∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base))
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base)))
    (F : Sheaf (ProEt.topology S) Ab.{u + 1}) (p : ℕ)
    (ξ : Ext ((freeAbelianSheafFunctor (ProEt.topology S)).obj
      ((AffineProEt.toProEt S).obj U₀)) F (p + 1))
    (hcomp : ∀ k, (Ext.mk₀ ((freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map (j k ≫ q)))).comp ξ (zero_add (p + 1)) = 0) :
    (Ext.mk₀ ((freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map q))).comp ξ (zero_add (p + 1)) = 0 := by
  classical
  cases nonempty_fintype ι
  haveI : IsIso (Sigma.desc fun k ↦
      (freeAbelianSheafFunctor (ProEt.topology S)).map
        ((AffineProEt.toProEt S).map (j k))) :=
    isIso_sigmaDesc_freeAbelianSheafFunctor_map V j hoi hcov hdisj
  -- Convert to a biproduct and conclude by additivity of `Ext` in the first variable.
  let Fk : ι → Sheaf (ProEt.topology S) Ab.{u + 1} :=
    fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).obj
      ((AffineProEt.toProEt S).obj (V k))
  let d : (⨁ Fk) ⟶
      (freeAbelianSheafFunctor (ProEt.topology S)).obj ((AffineProEt.toProEt S).obj W) :=
    (biproduct.isoCoproduct Fk).hom ≫ Sigma.desc fun k ↦
      (freeAbelianSheafFunctor (ProEt.topology S)).map ((AffineProEt.toProEt S).map (j k))
  haveI : IsIso d := by
    dsimp only [d]
    infer_instance
  have hdk : ∀ k, biproduct.ι Fk k ≫ d =
      (freeAbelianSheafFunctor (ProEt.topology S)).map
        ((AffineProEt.toProEt S).map (j k)) := by
    intro k
    dsimp only [d]
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc_assoc, Sigma.ι_desc]
  set η := (Ext.mk₀ d).comp
    ((Ext.mk₀ ((freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map q))).comp ξ (zero_add (p + 1))) (zero_add (p + 1))
    with hη
  have hcomps : ∀ k, (Ext.mk₀ (biproduct.ι Fk k)).comp η (zero_add (p + 1)) = 0 := by
    intro k
    rw [hη, Ext.mk₀_comp_mk₀_assoc, hdk k, Ext.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      ← Functor.map_comp]
    exact hcomp k
  have hη0 : η = 0 := by
    refine (Ext.biproductAddEquiv (biproduct.isBilimit Fk) F (p + 1)).injective ?_
    rw [map_zero]
    funext k
    exact hcomps k
  have hfin : (Ext.mk₀ (inv d)).comp η (zero_add (p + 1)) =
      (Ext.mk₀ ((freeAbelianSheafFunctor (ProEt.topology S)).map
        ((AffineProEt.toProEt S).map q))).comp ξ (zero_add (p + 1)) := by
    rw [hη, Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, Ext.mk₀_id_comp]
  rw [← hfin, hη0, Ext.comp_zero]

end AffineProEt

variable (S)

/-- For an injective abelian sheaf `I` on the small étale site, the pullback `ν^*I` to the
pro-étale site has no higher cohomology on affine pro-étale objects. -/
theorem ProEt.subsingleton_ext_sheafPullback_injective
    (I : Sheaf S.smallEtaleTopology Ab.{u + 1}) (hI : Injective I)
    (U : S.AffineProEt) (n : ℕ) :
    Subsingleton (Ext
      ((freeAbelianSheafFunctor (ProEt.topology S)).obj ((AffineProEt.toProEt S).obj U))
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I) (n + 1)) := by
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  refine Sheaf.ext_free_eq_zero_of_cech (fun X ↦ proAffineEtale X.hom)
    ((ProEt.sheafPullback S Ab.{u + 1}).obj I) ?_ n
    (by simpa using U.prop) ξ
  intro X hX R hR
  obtain ⟨W, q, ι, _, V, j, hq, hmem, hoi, hcov, hdisj⟩ :=
    AffineProEt.exists_singleton_refinement (AffineProEt.ofProEt X hX) hR
  refine ⟨_, (AffineProEt.toProEt S).map q,
    AffineProEt.generate_singleton_toProEt_map_mem q hq,
    fun n ↦ AffineProEt.proAffineEtale_cechNerve_hom q n,
    fun m φ hφ ↦ AffineProEt.exists_coboundary q hq I hI m φ hφ,
    fun p ξ' hξ' ↦ AffineProEt.ext_comp_eq_zero_of_components q V j hoi hcov hdisj _ p ξ'
      fun k ↦ hξ' _ (hmem k)⟩

end AlgebraicGeometry.Scheme
