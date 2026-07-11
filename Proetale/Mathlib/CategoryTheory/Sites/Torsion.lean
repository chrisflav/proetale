/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.GroupTheory.Torsion

/-!
# Locally torsion abelian sheaves

An abelian sheaf on a site is *locally torsion* if every section is, locally on a
covering, killed by a positive integer. For sections over quasi-compact objects this
agrees with the section being torsion, but in general the local formulation is the
correct one; it is the torsion hypothesis in the proper base change theorem.

- `CategoryTheory.Sheaf.IsLocallyTorsion`: the definition.
- `CategoryTheory.Sheaf.isLocallyTorsion_of_isTorsion`: sectionwise torsion sheaves
  are locally torsion.
- `CategoryTheory.Sheaf.isLocallyTorsion_of_presheaf_isLocallySurjective`: a sheaf
  admitting a locally surjective map from a sectionwise torsion presheaf is locally
  torsion.
- `CategoryTheory.Sheaf.isLocallyTorsion_constantSheaf_of_isTorsion`: constant sheaves
  on torsion groups are locally torsion.
-/

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- An abelian sheaf is *locally torsion* if every section is locally killed by a
positive integer: for every section `s` over `U` there is a covering sieve of `U` such
that the restriction of `s` along every arrow of the sieve is killed by some positive
integer. -/
def IsLocallyTorsion (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∀ (U : Cᵒᵖ) (s : F.obj.obj U), ∃ S ∈ J U.unop, ∀ ⦃V : C⦄ (f : V ⟶ U.unop),
    S.arrows f → ∃ n : ℕ, 0 < n ∧ n • ConcreteCategory.hom (F.obj.map f.op) s = 0

/-- A sheaf all of whose sections are torsion is locally torsion. -/
lemma isLocallyTorsion_of_isTorsion (F : Sheaf J AddCommGrpCat.{w})
    (h : ∀ U : Cᵒᵖ, AddMonoid.IsTorsion (F.obj.obj U)) : IsLocallyTorsion F := by
  intro U s
  refine ⟨⊤, J.top_mem U.unop, fun V f _ ↦ ?_⟩
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (h (op V) (ConcreteCategory.hom (F.obj.map f.op) s))

/-- A sheaf admitting a locally surjective morphism from a sectionwise torsion
presheaf is locally torsion. -/
lemma isLocallyTorsion_of_presheaf_isLocallySurjective {P : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (G : Sheaf J AddCommGrpCat.{w}) (φ : P ⟶ G.obj)
    [Presheaf.IsLocallySurjective J φ]
    (hP : ∀ U : Cᵒᵖ, AddMonoid.IsTorsion (P.obj U)) : IsLocallyTorsion G := by
  intro U s
  refine ⟨Presheaf.imageSieve φ s, Presheaf.imageSieve_mem J φ s, fun V f hf ↦ ?_⟩
  obtain ⟨t, ht⟩ := hf
  obtain ⟨n, hn, hnt⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hP (op V) t)
  refine ⟨n, hn, ?_⟩
  rw [← ht, ← map_nsmul, hnt, map_zero]

/-- Locally torsion sheaves are stable under isomorphisms. -/
lemma IsLocallyTorsion.of_iso {F G : Sheaf J AddCommGrpCat.{w}} (e : F ≅ G)
    (hF : IsLocallyTorsion F) : IsLocallyTorsion G := by
  intro U s
  obtain ⟨S, hS, hkill⟩ := hF U (ConcreteCategory.hom (e.inv.hom.app U) s)
  refine ⟨S, hS, fun V f hfS ↦ ?_⟩
  obtain ⟨n, hn, hns⟩ := hkill f hfS
  refine ⟨n, hn, ?_⟩
  have hnat : ConcreteCategory.hom (G.obj.map f.op) s =
      ConcreteCategory.hom (e.hom.hom.app (op V))
        (ConcreteCategory.hom (F.obj.map f.op)
          (ConcreteCategory.hom (e.inv.hom.app U) s)) := by
    have h1 : ConcreteCategory.hom (e.hom.hom.app (op V))
        (ConcreteCategory.hom (F.obj.map f.op)
          (ConcreteCategory.hom (e.inv.hom.app U) s)) =
        ConcreteCategory.hom (G.obj.map f.op)
          (ConcreteCategory.hom (e.hom.hom.app U)
            (ConcreteCategory.hom (e.inv.hom.app U) s)) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) _).trans
          (ConcreteCategory.comp_apply _ _ _))
    rw [h1]
    have h2 : ConcreteCategory.hom (e.hom.hom.app U)
        (ConcreteCategory.hom (e.inv.hom.app U) s) = s := by
      have h3 : e.inv.hom.app U ≫ e.hom.hom.app U = 𝟙 (G.obj.obj U) :=
        congrArg (fun (φ : G ⟶ G) ↦ φ.hom.app U) e.inv_hom_id
      exact (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom h3 s).trans (ConcreteCategory.id_apply s))
    rw [h2]
  rw [hnat, ← map_nsmul, hns, map_zero]

/-- Zero sheaves are locally torsion. -/
lemma isLocallyTorsion_of_isZero {F : Sheaf J AddCommGrpCat.{w}} (h : Limits.IsZero F) :
    IsLocallyTorsion F := by
  intro U s
  refine ⟨⊤, J.top_mem U.unop, fun V f _ ↦ ⟨1, one_pos, ?_⟩⟩
  have hid : (𝟙 F : F ⟶ F) = 0 := h.eq_of_src _ _
  have h1 := ConcreteCategory.congr_hom (congrArg (fun (φ : F ⟶ F) ↦ φ.hom.app U) hid) s
  simp only [one_smul]
  have hs : s = 0 := by
    refine (ConcreteCategory.id_apply s).symm.trans (h1.trans ?_)
    simp
  rw [hs, map_zero]

/-- The constant sheaf on a torsion abelian group is locally torsion. -/
lemma isLocallyTorsion_constantSheaf_of_isTorsion [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : AddCommGrpCat.{w}) (hM : AddMonoid.IsTorsion M) :
    IsLocallyTorsion ((constantSheaf J AddCommGrpCat.{w}).obj M) :=
  isLocallyTorsion_of_presheaf_isLocallySurjective _
    (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (fun _ ↦ hM)

end CategoryTheory.Sheaf
