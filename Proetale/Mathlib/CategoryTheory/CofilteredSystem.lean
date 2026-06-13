/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# The Mittag-Leffler condition for `ℕᵒᵖ`-indexed systems

We specialize `CategoryTheory.Functor.IsMittagLeffler` to inverse systems indexed by
`ℕᵒᵖ`, where it takes the familiar form: for every level `n` there is an `m ≥ n` such
that the image of every level `k` in level `n` contains the image of level `m`
(`CategoryTheory.Functor.isMittagLeffler_nat_iff`).

We also record that a functor with finite values satisfies the Mittag-Leffler
condition (`CategoryTheory.Functor.isMittagLeffler_of_finite`) and that the
Mittag-Leffler condition descends along a levelwise bijective natural transformation
(`CategoryTheory.Functor.IsMittagLeffler.of_natTrans_bijective`).
-/

universe w v u

open Set

namespace CategoryTheory.Functor

/-- A functor with finite values satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler_of_finite {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J]
    (F : J ⥤ Type v) [∀ j, Finite (F.obj j)] : F.IsMittagLeffler :=
  F.isMittagLeffler_of_exists_finite_range fun j ↦ ⟨j, 𝟙 j, Set.toFinite _⟩

/-- The Mittag-Leffler condition descends along a levelwise bijective natural
transformation. -/
theorem IsMittagLeffler.of_natTrans_bijective {J : Type u} [Category.{w} J]
    {F G : J ⥤ Type v} (φ : F ⟶ G) (hφ : ∀ j, Function.Bijective (φ.app j))
    (hG : G.IsMittagLeffler) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := hG j
  refine ⟨i, f, fun k g ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  have h1 : φ.app j (F.map f x) = G.map f (φ.app i x) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (φ.naturality f) x).trans
        (ConcreteCategory.comp_apply _ _ _))
  obtain ⟨z, hz⟩ := hf g ⟨φ.app i x, h1.symm⟩
  obtain ⟨z', rfl⟩ := (hφ k).2 z
  refine ⟨z', (hφ j).1 ?_⟩
  have h2 : φ.app j (F.map g z') = G.map g (φ.app k z') :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (φ.naturality g) z').trans
        (ConcreteCategory.comp_apply _ _ _))
  exact h2.trans hz

variable (F : ℕᵒᵖ ⥤ Type v)

open Opposite in
/-- Over `ℕᵒᵖ`, the Mittag-Leffler condition states that for every level `n` there is
an `m ≥ n` such that the range of the transition map from any level `k ≥ n` into level
`n` contains the range of the transition map from level `m`. -/
theorem isMittagLeffler_nat_iff :
    F.IsMittagLeffler ↔ ∀ n : ℕ, ∃ (m : ℕ) (hm : n ≤ m), ∀ (k : ℕ) (hk : n ≤ k),
      range (F.map (homOfLE hm).op) ⊆ range (F.map (homOfLE hk).op) := by
  constructor
  · intro h n
    obtain ⟨i, f, hf⟩ := h (op n)
    have hfeq : f = (homOfLE (leOfHom f.unop)).op :=
      f.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    refine ⟨i.unop, leOfHom f.unop, fun k hk ↦ ?_⟩
    rw [← hfeq]
    exact hf ((homOfLE hk).op)
  · intro h j
    obtain ⟨m, hm, hsub⟩ := h j.unop
    refine ⟨op m, (homOfLE hm).op, fun k g ↦ ?_⟩
    have hgeq : g = (homOfLE (leOfHom g.unop)).op :=
      g.op_unop.symm.trans (congrArg Quiver.Hom.op (Subsingleton.elim _ _))
    rw [hgeq]
    exact hsub k.unop (leOfHom g.unop)

end CategoryTheory.Functor
