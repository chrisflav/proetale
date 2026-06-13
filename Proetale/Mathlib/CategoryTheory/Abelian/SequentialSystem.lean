/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Inverse systems indexed by `ℕᵒᵖ`

We study functors `F : ℕᵒᵖ ⥤ C` ("inverse systems") in a category `C` with zero object
and zero morphisms. The *transition maps* of `F` are the maps
`F.obj (op (n + 1)) ⟶ F.obj (op n)`.

The key results concern injective objects of the functor category:

- `CategoryTheory.SequentialSystem.isSplitEpi_transition_of_injective`: the transition
  maps of an injective inverse system are split epimorphisms.
- `CategoryTheory.SequentialSystem.injective_obj_of_injective`: the objects of an
  injective inverse system are injective.

Both are proved using the "extension by zero" systems `extendSystem n M`, which take the
value `M` in degrees `≤ n` (with identity transitions) and `0` above, together with the
natural identification `(extendSystem n M ⟶ F) ≃ (M ⟶ F.obj (op n))` and the
monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`.

We also record stability properties of the class of systems with epimorphic transition
maps.
-/

universe w v v' u u'

open CategoryTheory Limits Opposite

open scoped ZeroObject

namespace CategoryTheory.SequentialSystem

variable {C : Type u} [Category.{v} C]

section Transition

/-- The `n`-th transition map of an inverse system. -/
abbrev transition (F : ℕᵒᵖ ⥤ C) (n : ℕ) : F.obj (op (n + 1)) ⟶ F.obj (op n) :=
  F.map (homOfLE (Nat.le_succ n)).op

/-- If the successive transition maps of an inverse system are epimorphisms, so are all
the maps `F.obj (op n) ⟶ F.obj (op m)` for `m ≤ n`. -/
lemma epi_map_of_epi_transition (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ n, Epi (transition F n)) {m n : ℕ} (hmn : m ≤ n) :
    Epi (F.map (homOfLE hmn).op) := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rw [Subsingleton.elim (homOfLE hmn) (𝟙 (0 : ℕ)), op_id, F.map_id]
    infer_instance
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm
      rw [Subsingleton.elim (homOfLE hmn) (𝟙 (n + 1 : ℕ)), op_id, F.map_id]
      infer_instance
    · have hmn' : m ≤ n := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmn hm)
      rw [Subsingleton.elim (homOfLE hmn) (homOfLE hmn' ≫ homOfLE (Nat.le_succ n)), op_comp,
        F.map_comp]
      haveI := hF n
      haveI := ih hmn'
      exact epi_comp _ _

/-- Transition maps of quotients of systems with epimorphic transitions are epimorphisms:
if `τ : F ⟶ G` is a levelwise epimorphism and `F` has epimorphic transition maps, then so
does `G`. -/
lemma epi_transition_of_epi_app {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G)
    (hτ : ∀ k, Epi (τ.app k)) (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition G n) := by
  have hnat : transition F n ≫ τ.app (op n) = τ.app (op (n + 1)) ≫ transition G n :=
    τ.naturality (homOfLE (Nat.le_succ n)).op
  haveI := hF n
  haveI := hτ (op n)
  haveI : Epi (τ.app (op (n + 1)) ≫ transition G n) := by
    rw [← hnat]
    exact epi_comp _ _
  exact epi_of_epi (τ.app (op (n + 1))) _

/-- Whiskering with a functor preserving epimorphisms preserves epimorphic transitions. -/
lemma epi_transition_whisker {D : Type u'} [Category.{v'} D] {F : ℕᵒᵖ ⥤ C} (L : C ⥤ D)
    [L.PreservesEpimorphisms] (hF : ∀ n, Epi (transition F n)) (n : ℕ) :
    Epi (transition (F ⋙ L) n) :=
  L.map_epi _

/-- A natural transformation from a constant functor to an inverse system is determined
by components compatible with the successive transition maps. -/
@[simps]
def natTransOfSucc {F : ℕᵒᵖ ⥤ C} {Z : C} (app : ∀ n, Z ⟶ F.obj (op n))
    (h : ∀ n, app (n + 1) ≫ transition F n = app n) :
    (Functor.const ℕᵒᵖ).obj Z ⟶ F where
  app k := app k.unop
  naturality {k k'} f := by
    have key : ∀ (m p : ℕ) (hmp : m ≤ p), app p ≫ F.map (homOfLE hmp).op = app m := by
      intro m p hmp
      induction p with
      | zero =>
        obtain rfl : m = 0 := Nat.le_zero.mp hmp
        rw [Subsingleton.elim (homOfLE hmp) (𝟙 (0 : ℕ)), op_id, F.map_id, Category.comp_id]
      | succ p ih =>
        by_cases hm : m = p + 1
        · subst hm
          rw [Subsingleton.elim (homOfLE hmp) (𝟙 (p + 1 : ℕ)), op_id, F.map_id,
            Category.comp_id]
        · have hmp' : m ≤ p := Nat.lt_succ_iff.mp (lt_of_le_of_ne hmp hm)
          have htr : app (p + 1) ≫ F.map (homOfLE (Nat.le_succ p)).op = app p := h p
          rw [Subsingleton.elim (homOfLE hmp) (homOfLE hmp' ≫ homOfLE (Nat.le_succ p)), op_comp,
            F.map_comp, ← Category.assoc, htr, ih hmp']
    have hf : f = (homOfLE (leOfHom f.unop)).op :=
      f.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
    rw [hf]
    exact (Category.id_comp _).trans (key k'.unop k.unop (leOfHom f.unop)).symm

end Transition

section Extend

variable [HasZeroMorphisms C] [HasZeroObject C]

open Classical in
/-- The inverse system which takes the value `M` in degrees `≤ n`, with identity
transition maps, and `0` in degrees `> n`. -/
noncomputable def extendSystem (n : ℕ) (M : C) : ℕᵒᵖ ⥤ C where
  obj k := if k.unop ≤ n then M else 0
  map {k k'} f :=
    if h : k.unop ≤ n then
      eqToHom (if_pos h) ≫ eqToHom (if_pos (le_trans (leOfHom f.unop) h)).symm
    else 0
  map_id := by
    intro k
    by_cases h : k.unop ≤ n
    · simp [dif_pos h]
    · exact ((isZero_zero C).of_iso (eqToIso (if_neg h))).eq_of_src _ _
  map_comp := by
    intro k k' k'' f g
    have hf := leOfHom f.unop
    by_cases h1 : k.unop ≤ n
    · have h2 : k'.unop ≤ n := le_trans hf h1
      simp [dif_pos h1, dif_pos h2]
    · simp [dif_neg h1]

variable (n : ℕ) (M : C) (F : ℕᵒᵖ ⥤ C)

/-- Morphisms out of `extendSystem n M` are morphisms `M ⟶ F.obj (op n)`. -/
@[simps! apply]
noncomputable def extendSystemHomEquiv : (extendSystem n M ⟶ F) ≃ (M ⟶ F.obj (op n)) where
  toFun φ := eqToHom (if_pos le_rfl).symm ≫ φ.app (op n)
  invFun u :=
    { app := fun k ↦
        if h : k.unop ≤ n then
          eqToHom (if_pos h) ≫ u ≫ F.map (homOfLE h).op
        else 0
      naturality := by
        intro k k' f
        have hf := leOfHom f.unop
        dsimp only [extendSystem]
        by_cases h1 : k.unop ≤ n
        · have h2 : k'.unop ≤ n := le_trans hf h1
          have hcomp : (homOfLE h1).op ≫ f = (homOfLE h2).op := by
            rw [← f.op_unop, ← op_comp]
            exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
          simp only [dif_pos h1, dif_pos h2]
          rw [← hcomp, F.map_comp]
          simp
        · simp [dif_neg h1] }
  left_inv := by
    intro φ
    ext k
    dsimp only
    by_cases h : k.unop ≤ n
    · simp only [dif_pos h]
      have hmap : (extendSystem n M).map (homOfLE h).op =
          eqToHom (if_pos (le_refl n)) ≫ eqToHom (if_pos h).symm := dif_pos le_rfl
      have hnat : φ.app (op n) ≫ F.map (homOfLE h).op =
          eqToHom (if_pos (le_refl n)) ≫ eqToHom (if_pos h).symm ≫ φ.app k := by
        rw [← Category.assoc, ← hmap]
        exact (φ.naturality (homOfLE h).op).symm
      simp only [Category.assoc]
      rw [hnat]
      simp
    · exact ((isZero_zero C).of_iso (eqToIso (if_neg h))).eq_of_src _ _
  right_inv := by
    intro u
    dsimp only
    rw [dif_pos (le_refl n)]
    simp

/-- The canonical monomorphism `extendSystem n M ⟶ extendSystem (n + 1) M`. -/
noncomputable def extendSystemι : extendSystem n M ⟶ extendSystem (n + 1) M where
  app k :=
    if h : k.unop ≤ n then
      eqToHom (if_pos h) ≫ eqToHom (if_pos (h.trans (Nat.le_succ n))).symm
    else 0
  naturality := by
    intro k k' f
    have hf := leOfHom f.unop
    dsimp only [extendSystem]
    by_cases h1 : k.unop ≤ n
    · have h2 : k'.unop ≤ n := le_trans hf h1
      have h3 : k.unop ≤ n + 1 := h1.trans (Nat.le_succ n)
      simp [dif_pos h1, dif_pos h2, dif_pos h3]
    · simp [dif_neg h1]

instance : Mono (extendSystemι n M) := by
  haveI : ∀ k, Mono ((extendSystemι n M).app k) := by
    intro k
    by_cases h : k.unop ≤ n
    · have e : (extendSystemι n M).app k =
          eqToHom (if_pos h) ≫ eqToHom (if_pos (h.trans (Nat.le_succ n))).symm := dif_pos h
      rw [e]
      infer_instance
    · exact mono_of_source_iso_zero _ (eqToIso (if_neg h))
  exact NatTrans.mono_of_mono_app _

/-- Compatibility of `extendSystemHomEquiv` with precomposition by `extendSystemι`:
restriction along `ι` corresponds to postcomposition with the transition map. -/
lemma extendSystemHomEquiv_ι_comp (ψ : extendSystem (n + 1) M ⟶ F) :
    extendSystemHomEquiv n M F (extendSystemι n M ≫ ψ) =
      extendSystemHomEquiv (n + 1) M F ψ ≫ transition F n := by
  have hι : (extendSystemι n M).app (op n) =
      eqToHom (if_pos (le_refl n)) ≫ eqToHom (if_pos ((le_refl n).trans (Nat.le_succ n))).symm :=
    dif_pos le_rfl
  have hmap : (extendSystem (n + 1) M).map (homOfLE (Nat.le_succ n)).op =
      eqToHom (if_pos (le_refl (n + 1))) ≫ eqToHom (if_pos (Nat.le_succ n)).symm :=
    dif_pos le_rfl
  have hnat : ψ.app (op (n + 1)) ≫ transition F n =
      eqToHom (if_pos (le_refl (n + 1))) ≫ eqToHom (if_pos (Nat.le_succ n)).symm ≫
        ψ.app (op n) := by
    rw [← Category.assoc, ← hmap]
    exact (ψ.naturality (homOfLE (Nat.le_succ n)).op).symm
  simp only [extendSystemHomEquiv_apply, NatTrans.comp_app, hι, Category.assoc]
  rw [hnat]
  simp

/-- The functoriality of `extendSystem n` in the object. -/
noncomputable def extendSystemMap {M M' : C} (h : M ⟶ M') :
    extendSystem n M ⟶ extendSystem n M' where
  app k :=
    if hk : k.unop ≤ n then eqToHom (if_pos hk) ≫ h ≫ eqToHom (if_pos hk).symm
    else 0
  naturality := by
    intro k k' f
    have hf := leOfHom f.unop
    dsimp only [extendSystem]
    by_cases h1 : k.unop ≤ n
    · have h2 : k'.unop ≤ n := le_trans hf h1
      simp [dif_pos h1, dif_pos h2]
    · simp [dif_neg h1]

instance {M M' : C} (h : M ⟶ M') [Mono h] : Mono (extendSystemMap n h) := by
  haveI : ∀ k, Mono ((extendSystemMap n h).app k) := by
    intro k
    by_cases hk : k.unop ≤ n
    · have e : (extendSystemMap n h).app k =
          eqToHom (if_pos hk) ≫ h ≫ eqToHom (if_pos hk).symm := dif_pos hk
      rw [e]
      infer_instance
    · exact mono_of_source_iso_zero _ (eqToIso (if_neg hk))
  exact NatTrans.mono_of_mono_app _

/-- Naturality of `extendSystemHomEquiv` in the object. -/
lemma extendSystemHomEquiv_map_comp {M M' : C} (h : M ⟶ M')
    (φ : extendSystem n M' ⟶ F) :
    extendSystemHomEquiv n M F (extendSystemMap n h ≫ φ) =
      h ≫ extendSystemHomEquiv n M' F φ := by
  have e : (extendSystemMap n h).app (op n) =
      eqToHom (if_pos (le_refl n)) ≫ h ≫ eqToHom (if_pos (le_refl n)).symm := dif_pos le_rfl
  simp only [extendSystemHomEquiv_apply, NatTrans.comp_app, e, Category.assoc]
  simp

/-- Naturality of `extendSystemHomEquiv` in the target system. -/
private lemma extendSystemHomEquiv_comp {G : ℕᵒᵖ ⥤ C} (φ : extendSystem n M ⟶ F) (τ : F ⟶ G) :
    extendSystemHomEquiv n M G (φ ≫ τ) = extendSystemHomEquiv n M F φ ≫ τ.app (op n) := by
  simp

/-- Monomorphisms of inverse systems are levelwise monomorphisms. This needs no assumption
on `C` beyond the existence of a zero object, since evaluation at `op n` has a left
adjoint given by `extendSystem n`. -/
private lemma mono_app_of_mono {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G) [Mono τ] :
    Mono (τ.app (op n)) := by
  constructor
  intro Z u v huv
  have h1 : extendSystemHomEquiv n Z G ((extendSystemHomEquiv n Z F).symm u ≫ τ) =
      extendSystemHomEquiv n Z G ((extendSystemHomEquiv n Z F).symm v ≫ τ) := by
    rw [extendSystemHomEquiv_comp, extendSystemHomEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, huv]
  exact (extendSystemHomEquiv n Z F).symm.injective
    ((cancel_mono τ).mp ((extendSystemHomEquiv n Z G).injective h1))

end Extend

section Coextend

variable [HasZeroMorphisms C] [HasZeroObject C]

open Classical in
/-- The inverse system which takes the value `M` in degrees `≥ n`, with identity
transition maps, and `0` in degrees `< n`. This is the right adjoint to evaluation at
`n` (in the partial sense recorded by `coextendSystemHomEquiv`). -/
noncomputable def coextendSystem (n : ℕ) (M : C) : ℕᵒᵖ ⥤ C where
  obj k := if n ≤ k.unop then M else 0
  map {k k'} f :=
    if h : n ≤ k'.unop then
      eqToHom (if_pos (h.trans (leOfHom f.unop))) ≫ eqToHom (if_pos h).symm
    else 0
  map_id := by
    intro k
    by_cases h : n ≤ k.unop
    · simp [dif_pos h]
    · exact ((isZero_zero C).of_iso (eqToIso (if_neg h))).eq_of_src _ _
  map_comp := by
    intro k k' k'' f g
    have hg := leOfHom g.unop
    by_cases h1 : n ≤ k''.unop
    · have h2 : n ≤ k'.unop := h1.trans hg
      simp [dif_pos h1, dif_pos h2]
    · simp [dif_neg h1]

variable (n : ℕ) (M : C) (F : ℕᵒᵖ ⥤ C)

/-- Morphisms into `coextendSystem n M` are morphisms `F.obj (op n) ⟶ M`. -/
@[simps! apply]
noncomputable def coextendSystemHomEquiv :
    (F ⟶ coextendSystem n M) ≃ (F.obj (op n) ⟶ M) where
  toFun φ := φ.app (op n) ≫ eqToHom (if_pos le_rfl)
  invFun u :=
    { app := fun k ↦
        if h : n ≤ k.unop then
          F.map (homOfLE h).op ≫ u ≫ eqToHom (if_pos h).symm
        else 0
      naturality := by
        intro k k' f
        have hf := leOfHom f.unop
        dsimp only [coextendSystem]
        by_cases h1 : n ≤ k'.unop
        · have h2 : n ≤ k.unop := h1.trans hf
          have hcomp : f ≫ (homOfLE h1).op = (homOfLE h2).op := by
            rw [← f.op_unop, ← op_comp]
            exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
          simp only [dif_pos h1, dif_pos h2]
          rw [← hcomp, F.map_comp]
          simp
        · simp [dif_neg h1] }
  left_inv := by
    intro φ
    ext k
    dsimp only
    by_cases h : n ≤ k.unop
    · simp only [dif_pos h]
      have hmap : (coextendSystem n M).map (homOfLE h).op =
          eqToHom (if_pos h) ≫ eqToHom (if_pos (le_refl n)).symm := dif_pos le_rfl
      have hnat : F.map (homOfLE h).op ≫ φ.app (op n) =
          φ.app k ≫ (eqToHom (if_pos h) ≫ eqToHom (if_pos (le_refl n)).symm) := by
        rw [← hmap]
        exact φ.naturality (homOfLE h).op
      simp only [← Category.assoc]
      rw [hnat]
      simp
    · exact ((isZero_zero C).of_iso (eqToIso (if_neg h))).eq_of_tgt _ _
  right_inv := by
    intro u
    dsimp only
    rw [dif_pos (le_refl n)]
    simp

/-- The component at `op n` of the adjunct of `u : F.obj (op n) ⟶ M` is `u` itself,
up to `eqToHom`. -/
private lemma coextendSystemHomEquiv_symm_app (u : F.obj (op n) ⟶ M) :
    ((coextendSystemHomEquiv n M F).symm u).app (op n) = u ≫ eqToHom (if_pos le_rfl).symm := by
  have h : ((coextendSystemHomEquiv n M F).symm u).app (op n) =
      F.map (homOfLE (le_refl n)).op ≫ u ≫ eqToHom (if_pos (le_refl n)).symm := dif_pos le_rfl
  rw [h, Subsingleton.elim (homOfLE (le_refl n)) (𝟙 n), op_id, F.map_id, Category.id_comp]

private lemma mono_coextendSystemHomEquiv_symm_app (u : F.obj (op n) ⟶ M) [Mono u] :
    Mono (((coextendSystemHomEquiv n M F).symm u).app (op n)) := by
  rw [coextendSystemHomEquiv_symm_app]
  infer_instance

/-- Naturality of `coextendSystemHomEquiv` in the source. -/
lemma coextendSystemHomEquiv_comp {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G)
    (φ : G ⟶ coextendSystem n M) :
    coextendSystemHomEquiv n M F (τ ≫ φ) =
      τ.app (op n) ≫ coextendSystemHomEquiv n M G φ := by
  simp

/-- `coextendSystem n J` is injective when `J` is: morphisms into it correspond to
morphisms out of the evaluation at `n`, and evaluation preserves monomorphisms. -/
instance (J : C) [Injective J] : Injective (coextendSystem n J) := by
  constructor
  intro X Y g f hf
  haveI := hf
  haveI := mono_app_of_mono n f
  obtain ⟨u, hu⟩ := Injective.factors (coextendSystemHomEquiv n J X g) (f.app (op n))
  refine ⟨(coextendSystemHomEquiv n J Y).symm u, ?_⟩
  apply (coextendSystemHomEquiv n J X).injective
  rw [coextendSystemHomEquiv_comp, Equiv.apply_symm_apply, hu]

end Coextend

section EnoughInjectives

variable [Abelian C] [EnoughInjectives C] [HasProductsOfShape ℕ C]

/-- The functor category `ℕᵒᵖ ⥤ C` has enough injectives when `C` is abelian with
enough injectives and countable products: embed `F` into
`∏ₙ coextendSystem n (Injective.under (F.obj (op n)))`. -/
instance enoughInjectives : EnoughInjectives (ℕᵒᵖ ⥤ C) where
  presentation F := by
    haveI key : ∀ k : ℕᵒᵖ, Mono ((Pi.lift fun p ↦ (coextendSystemHomEquiv p
        (Injective.under (F.obj (op p))) F).symm (Injective.ι (F.obj (op p)))).app k) := by
      intro k
      obtain ⟨m⟩ := k
      have h1 : (Pi.lift fun p ↦ (coextendSystemHomEquiv p (Injective.under (F.obj (op p))) F).symm
            (Injective.ι (F.obj (op p)))) ≫
          Pi.π (fun p ↦ coextendSystem p (Injective.under (F.obj (op p)))) m =
          (coextendSystemHomEquiv m (Injective.under (F.obj (op m))) F).symm
            (Injective.ι (F.obj (op m))) := by
        simp
      haveI : Mono ((Pi.lift fun p ↦ (coextendSystemHomEquiv p
            (Injective.under (F.obj (op p))) F).symm (Injective.ι (F.obj (op p)))).app (op m) ≫
          (Pi.π (fun p ↦ coextendSystem p (Injective.under (F.obj (op p)))) m).app (op m)) := by
        rw [← NatTrans.comp_app, h1]
        exact mono_coextendSystemHomEquiv_symm_app m (Injective.under (F.obj (op m))) F
          (Injective.ι (F.obj (op m)))
      exact mono_of_mono _
        ((Pi.π (fun p ↦ coextendSystem p (Injective.under (F.obj (op p)))) m).app (op m))
    exact ⟨{
      J := ∏ᶜ fun p ↦ coextendSystem p (Injective.under (F.obj (op p)))
      injective := inferInstance
      f := Pi.lift fun p ↦ (coextendSystemHomEquiv p (Injective.under (F.obj (op p))) F).symm
        (Injective.ι (F.obj (op p)))
      mono := NatTrans.mono_of_mono_app _ }⟩

end EnoughInjectives

section Injective

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- The transition maps of an injective inverse system are split epimorphisms. -/
theorem isSplitEpi_transition_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    IsSplitEpi (transition I n) := by
  have h := extendSystemHomEquiv_ι_comp n (I.obj (op n)) I
    (Injective.factorThru ((extendSystemHomEquiv n (I.obj (op n)) I).symm (𝟙 (I.obj (op n))))
      (extendSystemι n (I.obj (op n))))
  rw [Injective.comp_factorThru, Equiv.apply_symm_apply] at h
  exact IsSplitEpi.mk' ⟨_, h.symm⟩

/-- The objects of an injective inverse system are injective. -/
theorem injective_obj_of_injective (I : ℕᵒᵖ ⥤ C) [Injective I] (n : ℕ) :
    Injective (I.obj (op n)) := by
  constructor
  intro X Y g f hf
  haveI := hf
  have h := extendSystemHomEquiv_map_comp n I f
    (Injective.factorThru ((extendSystemHomEquiv n X I).symm g) (extendSystemMap n f))
  rw [Injective.comp_factorThru, Equiv.apply_symm_apply] at h
  exact ⟨_, h.symm⟩

end Injective

end CategoryTheory.SequentialSystem
