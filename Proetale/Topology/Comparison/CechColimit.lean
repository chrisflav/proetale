/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.CechResolution
import Proetale.Mathlib.CategoryTheory.Sites.SheafCohomology.LocallyVanish
import Proetale.Topology.Comparison.SectionsColimit
import Proetale.Topology.Comparison.FreeSheaf

/-!
# Čech cocycles of pullbacks of injective sheaves are coboundaries

For a surjection `q : W ⟶ U₀` of affine pro-étale objects and an injective abelian sheaf
`I` on the small étale site, every positive-degree Čech cocycle of `ν^*I` along `q` is a
coboundary: the Čech complex of `ν^*I` along `q` is a filtered colimit of Čech complexes
of `I` along surjective étale covers at the finite stages of a relative limit presentation
of `q`, and these are exact since `I` is injective.
-/

universe w₂ w₁ u

open CategoryTheory Limits Opposite Abelian AlgebraicTopology

open scoped Simplicial

namespace AddCommGrpCat

lemma hom_zsmul_apply {M N : AddCommGrpCat.{u + 1}} (z : ℤ) (f : M ⟶ N) (x : M) :
    (z • f) x = z • f x :=
  rfl

lemma hom_sum_apply {M N : AddCommGrpCat.{u + 1}} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact hom_add_apply _ _ _

end AddCommGrpCat

namespace CategoryTheory

/-! ### Translation between morphisms out of free abelian sheaves and sections

We record that `freeAbelianSheafHomEquiv` is additive (via the "generator" trick: every
morphism out of the free abelian sheaf is determined by its value on the canonical
generating section), and compute the image of a composition with the Čech differential. -/

section SectionsTranslation

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]

/-- Every morphism out of a free abelian sheaf corresponds, under
`freeAbelianSheafHomEquiv`, to the value of its component at `U` on the canonical
generating section. -/
lemma freeAbelianSheafHomEquiv_eq_app {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    (φ : (freeAbelianSheafFunctor J).obj U ⟶ F) :
    freeAbelianSheafHomEquiv φ =
      φ.hom.app (op U)
        (freeAbelianSheafHomEquiv (𝟙 ((freeAbelianSheafFunctor J).obj U))) := by
  conv_lhs => rw [← Category.id_comp φ]
  exact freeAbelianSheafHomEquiv_naturality_right _ _

lemma freeAbelianSheafHomEquiv_zero {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}} :
    freeAbelianSheafHomEquiv (0 : (freeAbelianSheafFunctor J).obj U ⟶ F) =
      (0 : F.obj.obj (op U)) := by
  rw [freeAbelianSheafHomEquiv_eq_app]
  have h0 : (0 : (freeAbelianSheafFunctor J).obj U ⟶ F).hom = 0 := rfl
  rw [h0, NatTrans.app_zero]
  rfl

lemma freeAbelianSheafHomEquiv_sum {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    {ι : Type*} (s : Finset ι) (φ : ι → ((freeAbelianSheafFunctor J).obj U ⟶ F)) :
    freeAbelianSheafHomEquiv (∑ i ∈ s, φ i) =
      ∑ i ∈ s, freeAbelianSheafHomEquiv (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using freeAbelianSheafHomEquiv_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rw [freeAbelianSheafHomEquiv_eq_app, freeAbelianSheafHomEquiv_eq_app (φ i),
      freeAbelianSheafHomEquiv_eq_app (∑ j ∈ s, φ j), Sheaf.Hom.add_app]
    exact AddCommGrpCat.hom_add_apply _ _ _

lemma freeAbelianSheafHomEquiv_zsmul {U : C} {F : Sheaf J AddCommGrpCat.{u + 1}}
    (z : ℤ) (φ : (freeAbelianSheafFunctor J).obj U ⟶ F) :
    freeAbelianSheafHomEquiv (z • φ) = z • freeAbelianSheafHomEquiv φ := by
  rw [freeAbelianSheafHomEquiv_eq_app, freeAbelianSheafHomEquiv_eq_app φ]
  have h : (z • φ).hom = z • φ.hom := rfl
  rw [h, NatTrans.app_zsmul]
  exact AddCommGrpCat.hom_zsmul_apply _ _ _

variable [HasFiniteWidePullbacks C]

/-- The Čech differential of free abelian sheaves is the alternating sum of the images of
the face maps of the Čech nerve. -/
lemma cechFreeD_eq {U V : C} (f : V ⟶ U) (n : ℕ) :
    cechFreeD J f n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) := by
  have h1 : cechFreeD J f n =
      (presheafToSheaf J AddCommGrpCat.{u + 1}).map
        ((cechFreePresheafComplex f).d (n + 1) n) := rfl
  have h2 : (cechFreePresheafComplex f).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        freeAbelianPresheafFunctor.map ((Arrow.mk f).cechNerve.δ i) := by
    refine (AlternatingFaceMapComplex.obj_d_eq _ n).trans ?_
    exact Finset.sum_congr rfl fun i _ => by
      rw [SimplicialObject.whiskering_obj_obj_δ]
  rw [h1, h2, Functor.map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Functor.map_zsmul]; rfl

end SectionsTranslation

/-- The Čech differential on sections: the alternating sum of the restrictions along the
face maps of the Čech nerve. -/
noncomputable def cechPresheafD {D : Type w₂} [Category.{w₁} D] {V U : D} (g : V ⟶ U)
    [∀ k : ℕ, HasWidePullback (Arrow.mk g).right
      (fun _ : Fin (k + 1) => (Arrow.mk g).left) fun _ => (Arrow.mk g).hom]
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    F.obj (op ((Arrow.mk g).cechNerve.obj (op ⦋n⦌))) ⟶
      F.obj (op ((Arrow.mk g).cechNerve.obj (op ⦋n + 1⦌))) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Arrow.mk g).cechNerve.δ i).op

section SectionsTranslation

variable {C : Type (u + 1)} [Category.{u} C]
variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{u + 1}]
variable [HasFiniteWidePullbacks C]

/-- Under `freeAbelianSheafHomEquiv`, precomposition with the Čech differential of free
abelian sheaves corresponds to the Čech differential on sections. -/
lemma freeAbelianSheafHomEquiv_cechFreeD_comp {U V : C} (f : V ⟶ U)
    {F : Sheaf J AddCommGrpCat.{u + 1}} (n : ℕ) (ψ : cechFree J f n ⟶ F) :
    freeAbelianSheafHomEquiv (cechFreeD J f n ≫ ψ) =
      cechPresheafD f F.obj n (freeAbelianSheafHomEquiv ψ) := by
  rw [cechFreeD_eq, Preadditive.sum_comp]
  have h1 : ∀ i : Fin (n + 2),
      ((-1 : ℤ) ^ (i : ℕ) • (freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i)) ≫ ψ =
        (-1 : ℤ) ^ (i : ℕ) •
          ((freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) ≫ ψ) :=
    fun i => Preadditive.zsmul_comp _ _ _
  rw [Finset.sum_congr rfl fun i _ => h1 i, freeAbelianSheafHomEquiv_sum]
  have h2 : ∀ i : Fin (n + 2),
      freeAbelianSheafHomEquiv ((-1 : ℤ) ^ (i : ℕ) •
          ((freeAbelianSheafFunctor J).map ((Arrow.mk f).cechNerve.δ i) ≫ ψ)) =
        (-1 : ℤ) ^ (i : ℕ) •
          (F.obj.map ((Arrow.mk f).cechNerve.δ i).op (freeAbelianSheafHomEquiv ψ)) := by
    intro i
    rw [freeAbelianSheafHomEquiv_zsmul, freeAbelianSheafHomEquiv_naturality_left]
    rfl
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  have h3 : cechPresheafD f F.obj n (freeAbelianSheafHomEquiv ψ) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) • F.obj.map ((Arrow.mk f).cechNerve.δ i).op)
        (freeAbelianSheafHomEquiv ψ) := by
    rw [cechPresheafD]
    exact AddCommGrpCat.hom_sum_apply _ _ _
  rw [h3]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (AddCommGrpCat.hom_zsmul_apply _ _ _).symm

/-- The Čech complex of free abelian sheaves is exact in positive degrees; this holds
without any covering assumption on `f`. -/
lemma cechFree_exact_succ' {U V : C} (f : V ⟶ U) (n : ℕ) :
    (ShortComplex.mk (cechFreeD J f (n + 1)) (cechFreeD J f n)
      (cechFreeD_comp_d J f n)).Exact := by
  have hpsh : (ShortComplex.mk ((cechFreePresheafComplex f).d (n + 2) (n + 1))
      ((cechFreePresheafComplex f).d (n + 1) n)
      ((cechFreePresheafComplex f).d_comp_d _ _ _)).Exact := by
    apply shortComplex_exact_of_evaluation
    intro X
    obtain ⟨W⟩ := X
    exact cechFreeEval_exact_succ f W n
  exact hpsh.map (presheafToSheaf J AddCommGrpCat.{u + 1})

/-- A positive-degree Čech cocycle of an injective abelian sheaf on any site is a
coboundary. -/
lemma exists_cechPresheafD_eq {U V : C} (f : V ⟶ U)
    (I : Sheaf J AddCommGrpCat.{u + 1}) (hI : Injective I) (m : ℕ)
    (x : I.obj.obj (op ((Arrow.mk f).cechNerve.obj (op ⦋m + 1⦌))))
    (hx : cechPresheafD f I.obj (m + 1) x = 0) :
    ∃ y, cechPresheafD f I.obj m y = x := by
  haveI := hI
  have hφ : cechFreeD J f (m + 1) ≫ freeAbelianSheafHomEquiv.symm x = 0 := by
    apply freeAbelianSheafHomEquiv.injective
    rw [freeAbelianSheafHomEquiv_cechFreeD_comp, Equiv.apply_symm_apply, hx,
      freeAbelianSheafHomEquiv_zero]
  have hexact := cechFree_exact_succ' (J := J) f m
  refine ⟨freeAbelianSheafHomEquiv
    (hexact.descToInjective (freeAbelianSheafHomEquiv.symm x) hφ), ?_⟩
  rw [← freeAbelianSheafHomEquiv_cechFreeD_comp]
  have hψ : cechFreeD J f m ≫
      hexact.descToInjective (freeAbelianSheafHomEquiv.symm x) hφ =
        freeAbelianSheafHomEquiv.symm x :=
    hexact.comp_descToInjective (freeAbelianSheafHomEquiv.symm x) hφ
  rw [hψ, Equiv.apply_symm_apply]

end SectionsTranslation

/-! ### Objects carrying Čech nerve data

`IsCechNerveAt g n P` is data exhibiting `P` as the `n`-th object of the Čech nerve of
`g`, by means of `n + 1` projections and a base map together with a compatible
isomorphism to the wide pullback. Such data is stable under binary pullbacks
(`IsCechNerveAt.succ`), which is how the Čech nerve objects on the pro-étale site are
matched with cofiltered limits of Čech nerve objects on the étale site. -/

section CechIter

variable {D : Type w₂} [Category.{w₁} D] {V U : D}

variable (g : V ⟶ U) [∀ k : ℕ, HasWidePullback (Arrow.mk g).right
    (fun _ : Fin (k + 1) => (Arrow.mk g).left) fun _ => (Arrow.mk g).hom]

/-- Data exhibiting `P` as the `n`-th object of the Čech nerve of `g`. -/
structure IsCechNerveAt (n : ℕ) (P : D) where
  /-- The projections to `V`. -/
  π : Fin (n + 1) → (P ⟶ V)
  /-- The structure map to `U`. -/
  base : P ⟶ U
  wπ : ∀ j, π j ≫ g = base
  /-- The comparison isomorphism with the wide pullback. -/
  iso : P ≅ (Arrow.mk g).cechNerve.obj (op ⦋n⦌)
  iso_π : ∀ j, iso.hom ≫ WidePullback.π (fun _ : Fin (n + 1) => (Arrow.mk g).hom) j = π j
  iso_base : iso.hom ≫ WidePullback.base (fun _ : Fin (n + 1) => (Arrow.mk g).hom) = base

/-- Forgetting the last projection of a Čech nerve object. -/
noncomputable def cechNerveForgetLast (k : ℕ) :
    (Arrow.mk g).cechNerve.obj (op ⦋k + 1⦌) ⟶ (Arrow.mk g).cechNerve.obj (op ⦋k⦌) :=
  WidePullback.lift (WidePullback.base _)
    (fun j : Fin (k + 1) => WidePullback.π (fun _ : Fin (k + 2) => (Arrow.mk g).hom) j.castSucc)
    (fun _ => WidePullback.π_arrow _ _)

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_π (k : ℕ) (j : Fin (k + 1)) :
    cechNerveForgetLast g k ≫ WidePullback.π (fun _ : Fin (k + 1) => (Arrow.mk g).hom) j =
      WidePullback.π (fun _ : Fin (k + 2) => (Arrow.mk g).hom) j.castSucc :=
  WidePullback.lift_π _ _ _ _ j

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_base (k : ℕ) :
    cechNerveForgetLast g k ≫ WidePullback.base (fun _ : Fin (k + 1) => (Arrow.mk g).hom) =
      WidePullback.base (fun _ : Fin (k + 2) => (Arrow.mk g).hom) :=
  WidePullback.lift_base _ _ _ _

namespace IsCechNerveAt

variable {g} {n : ℕ} {P : D}

@[reassoc]
lemma inv_π (h : IsCechNerveAt g n P) (j : Fin (n + 1)) :
    h.iso.inv ≫ h.π j = WidePullback.π (fun _ : Fin (n + 1) => (Arrow.mk g).hom) j := by
  rw [← h.iso_π, Iso.inv_hom_id_assoc]

@[reassoc]
lemma inv_base (h : IsCechNerveAt g n P) :
    h.iso.inv ≫ h.base = WidePullback.base (fun _ : Fin (n + 1) => (Arrow.mk g).hom) := by
  rw [← h.iso_base, Iso.inv_hom_id_assoc]

lemma hom_ext (h : IsCechNerveAt g n P) {Z : D} {t₁ t₂ : Z ⟶ P}
    (hπ : ∀ j, t₁ ≫ h.π j = t₂ ≫ h.π j) (hbase : t₁ ≫ h.base = t₂ ≫ h.base) :
    t₁ = t₂ := by
  rw [← cancel_mono h.iso.hom]
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, h.iso_π, hπ]
  · rw [Category.assoc, Category.assoc, h.iso_base, hbase]

variable (g) in
/-- `V` itself is the `0`-th object of the Čech nerve of `g`. -/
noncomputable def zero : IsCechNerveAt g 0 V where
  π _ := 𝟙 V
  base := g
  wπ _ := Category.id_comp g
  iso :=
    { hom := WidePullback.lift g (fun _ : Fin 1 => 𝟙 V) (fun _ => Category.id_comp g)
      inv := WidePullback.π (fun _ : Fin 1 => (Arrow.mk g).hom) 0
      hom_inv_id := WidePullback.lift_π _ _ _ _ 0
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro j
          rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
          exact congrArg (WidePullback.π fun _ : Fin 1 => (Arrow.mk g).hom)
            (Subsingleton.elim (0 : Fin 1) j)
        · rw [Category.assoc, WidePullback.lift_base, Category.id_comp]
          exact WidePullback.π_arrow _ 0 }
  iso_π j := WidePullback.lift_π _ _ _ _ j
  iso_base := WidePullback.lift_base _ _ _ _

@[simp]
lemma zero_π (j : Fin 1) : (zero g).π j = 𝟙 V := rfl

@[simp]
lemma zero_base : (zero g).base = g := rfl

/-- Extend Čech nerve data one degree up along a binary pullback. The new projections,
base map and the comparison equations are supplied as data to avoid definitional
unfolding issues at use sites. -/
noncomputable def succ (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    IsCechNerveAt g (n + 1) P' := by
  have wπ' : ∀ j : Fin (n + 2), π' j ≫ g = base' := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hlast, hbase]
    | cast j => rw [hπ, hbase, Category.assoc, h.wπ, sq.w]
  have hcomm : (cechNerveForgetLast g n ≫ h.iso.inv) ≫ h.base =
      WidePullback.π (fun _ : Fin (n + 2) => (Arrow.mk g).hom) (Fin.last (n + 1)) ≫ g := by
    rw [Category.assoc, h.inv_base, cechNerveForgetLast_base]
    exact (WidePullback.π_arrow _ _).symm
  have hfst : WidePullback.lift (arrows := fun _ : Fin (n + 2) => (Arrow.mk g).hom)
      base' π' wπ' ≫ cechNerveForgetLast g n = fst ≫ h.iso.hom := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.assoc, cechNerveForgetLast_π, WidePullback.lift_π,
        h.iso_π, hπ]
    · rw [Category.assoc, Category.assoc, cechNerveForgetLast_base, WidePullback.lift_base,
        h.iso_base, hbase, sq.w]
  refine
    { π := π'
      base := base'
      wπ := wπ'
      iso :=
        { hom := WidePullback.lift (arrows := fun _ : Fin (n + 2) => (Arrow.mk g).hom)
            base' π' wπ'
          inv := sq.lift (cechNerveForgetLast g n ≫ h.iso.inv)
            (WidePullback.π (fun _ : Fin (n + 2) => (Arrow.mk g).hom) (Fin.last (n + 1)))
            hcomm
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      iso_π := fun j => WidePullback.lift_π _ _ _ _ j
      iso_base := WidePullback.lift_base _ _ _ _ }
  · apply sq.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, hfst, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, WidePullback.lift_π, hlast, Category.id_comp]
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      induction j using Fin.lastCases with
      | last => rw [WidePullback.lift_π, hlast, IsPullback.lift_snd]
      | cast j =>
        rw [WidePullback.lift_π, hπ, ← Category.assoc, IsPullback.lift_fst,
          Category.assoc, h.inv_π, cechNerveForgetLast_π]
    · rw [Category.assoc, Category.id_comp, WidePullback.lift_base, hbase,
        ← Category.assoc, IsPullback.lift_snd]
      exact WidePullback.π_arrow _ _

@[simp]
lemma succ_π (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) (j : Fin (n + 2)) :
    (h.succ sq π' base' hπ hlast hbase).π j = π' j := rfl

@[simp]
lemma succ_base (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    (h.succ sq π' base' hπ hlast hbase).base = base' := rfl

/-- The `i`-th face map between objects carrying Čech nerve data. -/
noncomputable def face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) : P' ⟶ P :=
  h'.iso.hom ≫ (Arrow.mk g).cechNerve.δ i ≫ h.iso.inv

@[reassoc]
lemma face_π {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    h'.face h i ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j) := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.π (fun _ : Fin (n + 1) => (Arrow.mk g).hom) j =
        WidePullback.π (fun _ : Fin (n + 2) => (Arrow.mk g).hom)
          ((SimplexCategory.δ i).toOrderHom j) :=
    cechNerve_map_comp_π g ((SimplexCategory.δ i).op) j
  rw [face, Category.assoc, Category.assoc, h.inv_π, hδ, h'.iso_π]

@[reassoc]
lemma face_base {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) :
    h'.face h i ≫ h.base = h'.base := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.base (fun _ : Fin (n + 1) => (Arrow.mk g).hom) =
        WidePullback.base (fun _ : Fin (n + 2) => (Arrow.mk g).hom) :=
    cechNerve_map_comp_base g ((SimplexCategory.δ i).op)
  rw [face, Category.assoc, Category.assoc, h.inv_base, hδ, h'.iso_base]

/-- A morphism satisfying the simplicial identities of the `i`-th face map is the `i`-th
face map. -/
lemma eq_face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) {t : P' ⟶ P}
    (htπ : ∀ j, t ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j))
    (htbase : t ≫ h.base = h'.base) :
    t = h'.face h i :=
  h.hom_ext (fun j => by rw [htπ, face_π]) (by rw [htbase, face_base])

/-- The alternating sum of the face maps, on sections of an abelian presheaf. -/
noncomputable def faceD {P' P : D} (h' : IsCechNerveAt g (n + 1) P')
    (h : IsCechNerveAt g n P) (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    F.obj (op P) ⟶ F.obj (op P') :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((h'.face h i).op)

/-- The alternating sum of the face maps is conjugate to the Čech differential on
sections. -/
lemma faceD_eq {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    h'.faceD h F =
      F.map (h.iso.inv.op) ≫ cechPresheafD g F n ≫ F.map (h'.iso.hom.op) := by
  rw [faceD, cechPresheafD, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [face, op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]

end IsCechNerveAt

/-- Restriction along an isomorphism followed by restriction along its inverse is the
identity, elementwise. -/
lemma map_op_hom_inv_apply {F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {X Y : D} (e : X ≅ Y)
    (t : F.obj (op Y)) :
    F.map (e.inv.op) (F.map (e.hom.op) t) = t := by
  have h : F.map (e.hom.op) ≫ F.map (e.inv.op) = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id]
  have := ConcreteCategory.congr_hom h t
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at this

/-- Restriction along the inverse of an isomorphism followed by restriction along the
isomorphism is the identity, elementwise. -/
lemma map_op_inv_hom_apply {F : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {X Y : D} (e : X ≅ Y)
    (t : F.obj (op X)) :
    F.map (e.hom.op) (F.map (e.inv.op) t) = t := by
  have h : F.map (e.inv.op) ≫ F.map (e.hom.op) = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id]
  have := ConcreteCategory.congr_hom h t
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at this

end CechIter

end CategoryTheory

namespace AlgebraicGeometry.Scheme.AffineProEt

/-! ### The tower of iterated fibre products

We construct, for a morphism `q : W ⟶ U₀` of affine pro-étale objects presented as a
morphism of relative limit presentations, the tower of iterated fibre products of `W`
over `U₀`, simultaneously with relative limit presentations whose stages carry étale
Čech nerve data and with pro-étale Čech nerve data on the total spaces. -/

variable {S : Scheme.{u}}

section Tower

variable {W U₀ : S.AffineProEt} (q : W ⟶ U₀)
variable {A : Type u} [SmallCategory A]
variable (presU : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) U₀)
variable (presW : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) W)
variable (fW : presW.Hom presU)

/-- The `n`-th level of the tower of iterated fibre products of `q : W ⟶ U₀`: an affine
pro-étale object `M` with a relative limit presentation whose stages carry Čech nerve
data for the étale level maps, and which itself carries Čech nerve data for `q` on the
pro-étale site. -/
structure CechTower (n : ℕ) where
  /-- The `n`-th iterated fibre product of `W` over `U₀`. -/
  M : S.AffineProEt
  /-- The relative limit presentation of `M`. -/
  presM : RelativeLimitPresentation A (AffineEtale.toAffineProEt S) M
  /-- The base morphism of presentations. -/
  bM : presM.Hom presU
  /-- The projections of `M` to `W`. -/
  πM : Fin (n + 1) → (M ⟶ W)
  /-- The stage-wise projections to the stages of `W`. -/
  πSt : ∀ a : A, Fin (n + 1) → (presM.diag.obj a ⟶ presW.diag.obj a)
  πM_π : ∀ (j : Fin (n + 1)) (a : A), πM j ≫ presW.π.app a =
    presM.π.app a ≫ (AffineEtale.toAffineProEt S).map (πSt a j)
  πSt_nat : ∀ {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)),
    presM.diag.map u ≫ πSt a' j = πSt a j ≫ presW.diag.map u
  /-- The Čech nerve data at the étale stages. -/
  ét : ∀ a : A, IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) n
    ((AffineEtale.Spec S).obj (presM.diag.obj a))
  ét_π : ∀ (a : A) (j : Fin (n + 1)), (ét a).π j = (AffineEtale.Spec S).map (πSt a j)
  ét_base : ∀ a : A, (ét a).base = (AffineEtale.Spec S).map (bM.natTrans.app a)
  /-- The Čech nerve data on the pro-étale site. -/
  pro : IsCechNerveAt ((AffineProEt.toProEt S).map q) n ((AffineProEt.toProEt S).obj M)
  pro_π : ∀ j : Fin (n + 1), pro.π j = (AffineProEt.toProEt S).map (πM j)
  pro_base : pro.base = (AffineProEt.toProEt S).map bM.map

namespace CechTower

variable {q presU presW fW}

/-- The zeroth level of the tower: `W` itself. -/
noncomputable def zero (hfW : fW.map = q) : CechTower q presU presW fW 0 where
  M := W
  presM := presW
  bM := fW
  πM _ := 𝟙 W
  πSt _ _ := 𝟙 _
  πM_π _ _ := by simp
  πSt_nat _ _ := by simp
  ét _ := .zero _
  ét_π _ _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  ét_base _ := rfl
  pro := .zero _
  pro_π _ := by rw [IsCechNerveAt.zero_π, CategoryTheory.Functor.map_id]
  pro_base := by rw [IsCechNerveAt.zero_base, hfW]

variable {n : ℕ}

/-- The presentation of the next level of the tower, by stage-wise pullbacks. -/
noncomputable def presNext (T : CechTower q presU presW fW n) (hfW : fW.map = q) :
    RelativeLimitPresentation A (AffineEtale.toAffineProEt S) (pullback T.bM.map q) :=
  RelativeLimitPresentation.pullback (F := AffineEtale.toAffineProEt S) T.bM.map q
    (IsPullback.of_hasPullback T.bM.map q).cone (IsPullback.of_hasPullback T.bM.map q).isLimit
    T.presM presW presU T.bM fW rfl hfW

variable (T : CechTower q presU presW fW n) (hfW : fW.map = q)

lemma presNext_π_app_fst (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.fst T.bM.map q ≫ T.presM.π.app a :=
  IsPullback.lift_fst _ _ _ _

lemma presNext_π_app_snd (a : A) :
    (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map
        (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)) =
      pullback.snd T.bM.map q ≫ presW.π.app a :=
  IsPullback.lift_snd _ _ _ _

lemma presNext_diag_map {a a' : A} (u : a ⟶ a') :
    (T.presNext hfW).diag.map u =
      pullback.map (T.bM.natTrans.app a) (fW.natTrans.app a) (T.bM.natTrans.app a')
        (fW.natTrans.app a') (T.presM.diag.map u) (presW.diag.map u) (presU.diag.map u)
        (by simp) (by simp) :=
  rfl

/-- The base morphism of presentations of the next level. -/
noncomputable def bMNext : (T.presNext hfW).Hom presU where
  natTrans :=
    { app a := pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a
      naturality a a' u := by
        rw [presNext_diag_map]
        rw [pullback.lift_snd_assoc, Category.assoc, fW.natTrans.naturality,
          Category.assoc] }

@[simp]
lemma bMNext_app (a : A) :
    (T.bMNext hfW).natTrans.app a =
      pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ fW.natTrans.app a :=
  rfl

lemma bMNext_map : (T.bMNext hfW).map = pullback.snd T.bM.map q ≫ q := by
  apply presU.isLimit.hom_ext
  intro a
  rw [RelativeLimitPresentation.Hom.map_π, bMNext_app, Functor.map_comp, ← Category.assoc,
    presNext_π_app_snd, Category.assoc, ← RelativeLimitPresentation.Hom.map_π fW a, hfW,
    Category.assoc]

/-- The projections of the next level of the tower. -/
noncomputable def πMNext : Fin (n + 2) → (pullback T.bM.map q ⟶ W) :=
  Fin.snoc (fun j => pullback.fst T.bM.map q ≫ T.πM j) (pullback.snd T.bM.map q)

/-- The stage-wise projections of the next level of the tower. -/
noncomputable def πStNext (a : A) :
    Fin (n + 2) → ((T.presNext hfW).diag.obj a ⟶ presW.diag.obj a) :=
  Fin.snoc (fun j => pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a) ≫ T.πSt a j)
    (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a))

lemma πMNext_π (j : Fin (n + 2)) (a : A) :
    T.πMNext j ≫ presW.π.app a =
      (T.presNext hfW).π.app a ≫ (AffineEtale.toAffineProEt S).map (T.πStNext hfW a j) := by
  induction j using Fin.lastCases with
  | last =>
    rw [πMNext, πStNext, Fin.snoc_last, Fin.snoc_last]
    exact (T.presNext_π_app_snd hfW a).symm
  | cast j =>
    rw [πMNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, Category.assoc, T.πM_π,
      CategoryTheory.Functor.map_comp, ← Category.assoc, ← presNext_π_app_fst,
      Category.assoc]

lemma πStNext_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 2)) :
    (T.presNext hfW).diag.map u ≫ T.πStNext hfW a' j =
      T.πStNext hfW a j ≫ presW.diag.map u := by
  induction j using Fin.lastCases with
  | last =>
    rw [πStNext, πStNext, Fin.snoc_last, Fin.snoc_last, presNext_diag_map,
      pullback.lift_snd]
  | cast j =>
    rw [πStNext, πStNext, Fin.snoc_castSucc, Fin.snoc_castSucc, presNext_diag_map,
      pullback.lift_fst_assoc, Category.assoc, T.πSt_nat, Category.assoc]

/-- The étale Čech nerve data of the next level of the tower. -/
noncomputable def étNext (a : A) :
    IsCechNerveAt ((AffineEtale.Spec S).map (fW.natTrans.app a)) (n + 1)
      ((AffineEtale.Spec S).obj ((T.presNext hfW).diag.obj a)) := by
  have sq : IsPullback
      ((AffineEtale.Spec S).map (pullback.fst (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((AffineEtale.Spec S).map (pullback.snd (T.bM.natTrans.app a) (fW.natTrans.app a)))
      ((T.ét a).base) ((AffineEtale.Spec S).map (fW.natTrans.app a)) := by
    rw [T.ét_base a]
    exact (IsPullback.of_hasPullback (T.bM.natTrans.app a) (fW.natTrans.app a)).map
      (AffineEtale.Spec S)
  refine (T.ét a).succ sq (fun j => (AffineEtale.Spec S).map (T.πStNext hfW a j))
    ((AffineEtale.Spec S).map ((T.bMNext hfW).natTrans.app a)) ?_ ?_ ?_
  · intro j
    simp only [πStNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.ét_π a j]
  · simp only [πStNext, Fin.snoc_last]
  · rw [bMNext_app, CategoryTheory.Functor.map_comp]

/-- The pro-étale Čech nerve data of the next level of the tower. -/
noncomputable def proNext :
    IsCechNerveAt ((AffineProEt.toProEt S).map q) (n + 1)
      ((AffineProEt.toProEt S).obj (pullback T.bM.map q)) := by
  have sq : IsPullback
      ((AffineProEt.toProEt S).map (pullback.fst T.bM.map q))
      ((AffineProEt.toProEt S).map (pullback.snd T.bM.map q))
      (T.pro.base) ((AffineProEt.toProEt S).map q) := by
    rw [T.pro_base]
    exact (IsPullback.of_hasPullback T.bM.map q).map (AffineProEt.toProEt S)
  refine T.pro.succ sq (fun j => (AffineProEt.toProEt S).map (T.πMNext j))
    ((AffineProEt.toProEt S).map ((T.bMNext hfW).map)) ?_ ?_ ?_
  · intro j
    simp only [πMNext, Fin.snoc_castSucc, CategoryTheory.Functor.map_comp, T.pro_π j]
  · simp only [πMNext, Fin.snoc_last]
  · rw [bMNext_map, CategoryTheory.Functor.map_comp]

/-- The next level of the tower. -/
noncomputable def succ : CechTower q presU presW fW (n + 1) where
  M := pullback T.bM.map q
  presM := T.presNext hfW
  bM := T.bMNext hfW
  πM := T.πMNext
  πSt := T.πStNext hfW
  πM_π := T.πMNext_π hfW
  πSt_nat := T.πStNext_nat hfW
  ét := T.étNext hfW
  ét_π _ _ := rfl
  ét_base _ := rfl
  pro := T.proNext hfW
  pro_π _ := rfl
  pro_base := rfl

end CechTower

namespace CechTower

variable {q presU presW fW} {n : ℕ}
variable (T' : CechTower q presU presW fW (n + 1)) (T : CechTower q presU presW fW n)

lemma ét_π_nat {a a' : A} (u : a ⟶ a') (j : Fin (n + 1)) :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').π j =
      (T.ét a).π j ≫ (AffineEtale.Spec S).map (presW.diag.map u) := by
  rw [T.ét_π a', T.ét_π a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.πSt_nat u]

lemma ét_base_nat {a a' : A} (u : a ⟶ a') :
    (AffineEtale.Spec S).map (T.presM.diag.map u) ≫ (T.ét a').base =
      (T.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
  rw [T.ét_base a', T.ét_base a, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, T.bM.natTrans.naturality u]

/-- The stage-wise face maps of consecutive levels of the tower assemble into a morphism
of presentations. -/
noncomputable def faceHom (i : Fin (n + 2)) : T'.presM.Hom T.presM where
  natTrans :=
    { app a := (AffineEtale.Spec S).preimage ((T'.ét a).face (T.ét a) i)
      naturality a a' u := by
        apply (AffineEtale.Spec S).map_injective
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          Functor.map_preimage, Functor.map_preimage]
        apply (T.ét a').hom_ext
        · intro j
          have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_π, T'.ét_π_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').π j =
                (T'.ét a).π ((SimplexCategory.δ i).toOrderHom j) ≫
                  (AffineEtale.Spec S).map (presW.diag.map u) := by
            rw [Category.assoc, T.ét_π_nat u, ← Category.assoc, IsCechNerveAt.face_π]
          rw [hL, hR]
        · have hL : ((AffineEtale.Spec S).map (T'.presM.diag.map u) ≫
              (T'.ét a').face (T.ét a') i) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, IsCechNerveAt.face_base, T'.ét_base_nat u]
          have hR : ((T'.ét a).face (T.ét a) i ≫
              (AffineEtale.Spec S).map (T.presM.diag.map u)) ≫ (T.ét a').base =
                (T'.ét a).base ≫ (AffineEtale.Spec S).map (presU.diag.map u) := by
            rw [Category.assoc, T.ét_base_nat u, ← Category.assoc, IsCechNerveAt.face_base]
          rw [hL, hR] }

@[simp]
lemma faceHom_app (i : Fin (n + 2)) (a : A) :
    (AffineEtale.Spec S).map ((T'.faceHom T i).natTrans.app a) =
      (T'.ét a).face (T.ét a) i :=
  Functor.map_preimage _ _

lemma faceHom_app_comp_πSt (i : Fin (n + 2)) (a : A) (j : Fin (n + 1)) :
    (T'.faceHom T i).natTrans.app a ≫ T.πSt a j =
      T'.πSt a ((SimplexCategory.δ i).toOrderHom j) := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_π, IsCechNerveAt.face_π,
    T'.ét_π]

lemma faceHom_app_comp_bM (i : Fin (n + 2)) (a : A) :
    (T'.faceHom T i).natTrans.app a ≫ T.bM.natTrans.app a = T'.bM.natTrans.app a := by
  apply (AffineEtale.Spec S).map_injective
  rw [CategoryTheory.Functor.map_comp, faceHom_app, ← T.ét_base, IsCechNerveAt.face_base,
    T'.ét_base]

lemma faceHom_map_comp_πM (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (T'.faceHom T i).map ≫ T.πM j = T'.πM ((SimplexCategory.δ i).toOrderHom j) := by
  apply presW.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.πM_π j a, T'.πM_π ((SimplexCategory.δ i).toOrderHom j) a,
    ← Category.assoc, (T'.faceHom T i).map_π a, Category.assoc,
    ← CategoryTheory.Functor.map_comp, faceHom_app_comp_πSt]

lemma faceHom_map_comp_bM (i : Fin (n + 2)) :
    (T'.faceHom T i).map ≫ T.bM.map = T'.bM.map := by
  apply presU.isLimit.hom_ext
  intro a
  rw [Category.assoc, T.bM.map_π a, ← Category.assoc, (T'.faceHom T i).map_π a,
    Category.assoc, ← CategoryTheory.Functor.map_comp, faceHom_app_comp_bM,
    T'.bM.map_π a]

lemma map_faceHom_map (i : Fin (n + 2)) :
    (AffineProEt.toProEt S).map ((T'.faceHom T i).map) = T'.pro.face T.pro i := by
  apply IsCechNerveAt.eq_face
  · intro j
    rw [T.pro_π, T'.pro_π, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_πM]
  · rw [T.pro_base, T'.pro_base, ← CategoryTheory.Functor.map_comp, faceHom_map_comp_bM]

section Differentials

variable (I : Sheaf S.smallEtaleTopology Ab.{u + 1})

/-- The Čech differential at the étale stages of the tower. -/
noncomputable def stageD (a : A) :
    I.obj.obj (op ((AffineEtale.Spec S).obj (T.presM.diag.obj a))) ⟶
      I.obj.obj (op ((AffineEtale.Spec S).obj (T'.presM.diag.obj a))) :=
  (T'.ét a).faceD (T.ét a) I.obj

/-- The Čech differential on the sections of the pullback sheaf over the tower. -/
noncomputable def proD :
    ((sheafToPresheaf (ProEt.topology S) Ab.{u + 1}).obj
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I)).obj
        (op ((AffineProEt.toProEt S).obj T.M)) ⟶
      ((sheafToPresheaf (ProEt.topology S) Ab.{u + 1}).obj
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I)).obj
        (op ((AffineProEt.toProEt S).obj T'.M)) :=
  T'.pro.faceD T.pro ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj

/-- The stage-wise Čech differentials intertwine the legs of the sections cocones. -/
lemma stageD_comp_ι (a : A) :
    T'.stageD T I a ≫ ProEt.sheafPullbackSectionsι I T'.presM a =
      ProEt.sheafPullbackSectionsι I T.presM a ≫ T'.proD T I := by
  rw [stageD, proD, IsCechNerveAt.faceD, IsCechNerveAt.faceD, Preadditive.sum_comp,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [← faceHom_app, ← map_faceHom_map]
  exact ProEt.sheafPullbackSectionsι_naturality I (T'.faceHom T i) a

/-- The stage-wise Čech differentials commute with the transition maps of the
presentations. -/
lemma map_comp_stageD {a a' : A} (u : a ⟶ a') :
    I.obj.map ((AffineEtale.Spec S).map (T.presM.diag.map u)).op ≫ T'.stageD T I a =
      T'.stageD T I a' ≫
        I.obj.map ((AffineEtale.Spec S).map (T'.presM.diag.map u)).op := by
  rw [stageD, stageD, IsCechNerveAt.faceD, IsCechNerveAt.faceD, Preadditive.comp_sum,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  rw [← faceHom_app T' T i a, ← faceHom_app T' T i a', ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun t => I.obj.map ((AffineEtale.Spec S).map t).op)
    ((T'.faceHom T i).natTrans.naturality u).symm

lemma stageD_eq (a : A) :
    T'.stageD T I a = I.obj.map ((T.ét a).iso.inv.op) ≫
      cechPresheafD ((AffineEtale.Spec S).map (fW.natTrans.app a)) I.obj n ≫
        I.obj.map ((T'.ét a).iso.hom.op) :=
  IsCechNerveAt.faceD_eq _ _ _

lemma proD_eq :
    T'.proD T I =
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map (T.pro.iso.inv.op) ≫
        cechPresheafD ((AffineProEt.toProEt S).map q)
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj n ≫
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map (T'.pro.iso.hom.op) :=
  IsCechNerveAt.faceD_eq _ _ _

end Differentials

end CechTower

variable {q presU presW fW} in
/-- The tower of iterated fibre products of `q`. -/
noncomputable def cechTower (hfW : fW.map = q) : ∀ n, CechTower q presU presW fW n :=
  fun n => Nat.rec (CechTower.zero hfW) (fun _ T => T.succ hfW) n

end Tower

/-- Positive-degree Čech cocycles of the pullback of an injective abelian sheaf
along a surjection of affine pro-étale objects are coboundaries. -/
lemma exists_coboundary {W U₀ : S.AffineProEt} (q : W ⟶ U₀) (hq : Surjective q.left)
    (I : Sheaf S.smallEtaleTopology Ab.{u + 1}) (hI : Injective I) (m : ℕ)
    (φ : cechFree (ProEt.topology S) ((AffineProEt.toProEt S).map q) (m + 1) ⟶
      (ProEt.sheafPullback S Ab.{u + 1}).obj I)
    (hφ : cechFreeD (ProEt.topology S) ((AffineProEt.toProEt S).map q) (m + 1) ≫ φ = 0) :
    ∃ ψ : cechFree (ProEt.topology S) ((AffineProEt.toProEt S).map q) m ⟶
        (ProEt.sheafPullback S Ab.{u + 1}).obj I,
      φ = cechFreeD (ProEt.topology S) ((AffineProEt.toProEt S).map q) m ≫ ψ := by
  classical
  -- Step 1: a relative limit presentation of the singleton cover of `q`.
  have hsing : Presieve.singleton q ∈ (Precoverage.singleton S.AffineProEt ⊓
      MorphismProperty.precoverage fun _ _ f ↦ Surjective f.left) U₀ :=
    ⟨⟨W, q, rfl⟩, by rwa [MorphismProperty.singleton_mem_precoverage_iff]⟩
  obtain ⟨A, instA, instAcof, pack, -⟩ :=
    AffineProEt.singleton_inf_le_relativelyPresentable S U₀ hsing
  let i₀ : (Presieve.singleton q).preZeroHypercover.I₀ := ⟨⟨W, q⟩, Presieve.singleton.mk⟩
  let presU := pack.pres
  let presW := pack.pres₀ i₀
  let fW : presW.Hom presU := pack.f i₀
  have hfW : fW.map = q := pack.hf i₀
  -- The tower of iterated fibre products.
  let T : ∀ n, CechTower q presU presW fW n := cechTower hfW
  -- Step 2: the cocycle as a section of the pullback sheaf.
  set x := freeAbelianSheafHomEquiv φ with hx
  have hcoc : cechPresheafD ((AffineProEt.toProEt S).map q)
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj (m + 1) x = 0 := by
    rw [hx, ← freeAbelianSheafHomEquiv_cechFreeD_comp, hφ, freeAbelianSheafHomEquiv_zero]
  -- Step 3: descend the cocycle to an étale stage.
  haveI : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set x' := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
    ((T (m + 1)).pro.iso.hom.op) x with hx'
  obtain ⟨aop, xa, hxa⟩ := Types.jointly_surjective _
    (isColimitOfPreserves (CategoryTheory.forget Ab.{u + 1})
      (ProEt.isColimitSheafPullbackSectionsCocone I (T (m + 1)).presM)) x'
  set a₀ := aop.unop with ha₀
  have hxa' : ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₀ xa = x' := hxa
  -- The stage-level cocycle dies in the colimit.
  have hdie : ProEt.sheafPullbackSectionsι I (T (m + 2)).presM a₀
      ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) = 0 := by
    have h1 := ConcreteCategory.congr_hom
      ((T (m + 2)).stageD_comp_ι (T (m + 1)) I a₀) xa
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1
    have h2 := ConcreteCategory.congr_hom ((T (m + 2)).proD_eq (T (m + 1)) I)
      (ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₀ xa)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
    rw [h1, h2, hxa', hx']
    have hcancel := map_op_hom_inv_apply (F := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj)
      ((T (m + 1)).pro.iso) x
    refine (congrArg (fun t => ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
        ((T (m + 2)).pro.iso.hom.op) (cechPresheafD ((AffineProEt.toProEt S).map q)
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj (m + 1) t)) hcancel).trans
      ((congrArg (fun t => ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
        ((T (m + 2)).pro.iso.hom.op) t) hcoc).trans (map_zero _))
  -- Step 4: the cocycle condition holds at a later stage.
  obtain ⟨kop, w, hw⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (CategoryTheory.forget Ab.{u + 1})
      (ProEt.isColimitSheafPullbackSectionsCocone I (T (m + 2)).presM))
    ((T (m + 2)).stageD (T (m + 1)) I a₀ xa)
    (0 : I.obj.obj
      (op ((AffineEtale.Spec S).obj ((T (m + 2)).presM.diag.obj a₀))))).mp
    (by
      have h0 : ProEt.sheafPullbackSectionsι I (T (m + 2)).presM a₀ (0 : I.obj.obj
          (op ((AffineEtale.Spec S).obj ((T (m + 2)).presM.diag.obj a₀)))) = 0 :=
        map_zero _
      exact hdie.trans h0.symm)
  set a₁ := kop.unop with ha₁
  set u : a₁ ⟶ a₀ := w.unop with hu
  set xa₁ := I.obj.map
    ((AffineEtale.Spec S).map ((T (m + 1)).presM.diag.map u)).op xa with hxa₁def
  have hxa₁ : ProEt.sheafPullbackSectionsι I (T (m + 1)).presM a₁ xa₁ = x' := by
    have h3 := ConcreteCategory.congr_hom
      (ProEt.map_sheafPullbackSectionsι I (T (m + 1)).presM u) xa
    rw [ConcreteCategory.comp_apply] at h3
    exact h3.trans hxa'
  have hw' : I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op
      ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) = 0 := by
    have h5 : I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op
        ((T (m + 2)).stageD (T (m + 1)) I a₀ xa) =
          I.obj.map ((AffineEtale.Spec S).map ((T (m + 2)).presM.diag.map u)).op 0 := hw
    rw [map_zero] at h5
    exact h5
  have hcoc₁ : (T (m + 2)).stageD (T (m + 1)) I a₁ xa₁ = 0 := by
    have h4 := ConcreteCategory.congr_hom
      ((T (m + 2)).map_comp_stageD (T (m + 1)) I u) xa
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h4
    exact h4.trans hw'
  -- Step 5: solve the cocycle at the étale stage, using injectivity of `I`.
  set xé := I.obj.map (((T (m + 1)).ét a₁).iso.inv.op) xa₁ with hxé
  have hcocé : cechPresheafD ((AffineEtale.Spec S).map (fW.natTrans.app a₁)) I.obj
      (m + 1) xé = 0 := by
    have h6 := ConcreteCategory.congr_hom
      ((T (m + 2)).stageD_eq (T (m + 1)) I a₁) xa₁
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hcoc₁] at h6
    have h7 := congrArg (I.obj.map (((T (m + 2)).ét a₁).iso.inv.op)) h6
    rw [map_zero, map_op_hom_inv_apply] at h7
    exact h7.symm
  obtain ⟨yé, hyé⟩ := exists_cechPresheafD_eq
    ((AffineEtale.Spec S).map (fW.natTrans.app a₁)) I hI m xé hcocé
  set ya := I.obj.map (((T m).ét a₁).iso.hom.op) yé with hya
  have hstep : (T (m + 1)).stageD (T m) I a₁ ya = xa₁ := by
    have h8 := ConcreteCategory.congr_hom ((T (m + 1)).stageD_eq (T m) I a₁) ya
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hya,
      map_op_hom_inv_apply, hyé, hxé, map_op_inv_hom_apply] at h8
    exact h8
  -- Step 6: go back up to the pro-étale site.
  set y' := ProEt.sheafPullbackSectionsι I (T m).presM a₁ ya with hy'
  have hxy : x' = (T (m + 1)).proD (T m) I y' := by
    have h9 := ConcreteCategory.congr_hom ((T (m + 1)).stageD_comp_ι (T m) I a₁) ya
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hstep, hxa₁] at h9
    rw [hy']
    exact h9
  set y := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
    ((T m).pro.iso.inv.op) y' with hy
  refine ⟨freeAbelianSheafHomEquiv.symm y, ?_⟩
  apply freeAbelianSheafHomEquiv.injective
  rw [freeAbelianSheafHomEquiv_cechFreeD_comp, Equiv.apply_symm_apply, ← hx]
  have h10 : x = ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj.map
      ((T (m + 1)).pro.iso.inv.op) x' := by
    rw [hx', map_op_hom_inv_apply]
  have h11 := ConcreteCategory.congr_hom ((T (m + 1)).proD_eq (T m) I) y'
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h11
  rw [h10, hxy, h11]
  refine (map_op_hom_inv_apply (F := ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj)
      ((T (m + 1)).pro.iso) _).trans ?_
  exact congrArg (fun t => cechPresheafD ((AffineProEt.toProEt S).map q)
    ((ProEt.sheafPullback S Ab.{u + 1}).obj I).obj m t) hy.symm

end AlgebraicGeometry.Scheme.AffineProEt
