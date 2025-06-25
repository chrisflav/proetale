/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib

open CategoryTheory
variable {R : Type*} [CommRing R]
-- #synth Limits.HasColimits (AlgCat R) -- tensor product
#synth Limits.HasLimits (AlgCat R)

universe u v w w'

open CategoryTheory Limits

instance : Limits.HasColimits (AlgCat R) := sorry


--

-- `Question: Why Algebra.Etale is preferred over RingHom.IsEtale?`

-- `Ind P Q` for fixed universe. And IndEtale IndZariski,... for different universes.

-- universe

-- 2 versions of Ind Category:
-- 1. Filtered diagrams (satisfying certain property) in the category of algebras over a fixed base ring.
-- 2. There is a functor from 1 to the `AlgCat R` (by taking the colimit), the essential image of this functor.
-- For 1: Given a cocone, satisfying `IsColimit`

-- class Algebra.Ind (P : {R S : Type u} → [CommRing R] → [CommRing S] → [Algebra R S] → Prop) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
--   isColim : ∃ I : Type w, ∃ c : Category I, ∃ h : IsFiltered I, ∃ F : Functor I (AlgCat R),
-- `Order of (R : Type u) [CommRing R] (S : Type u) matters, [CommRing S] is not [Ring S]`
-- Becareful about the difference between CommRing S and Ring S.
-- structure Algebra.Ind (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
--     (R : Type u) [CommRing R] (I : Type w) [Category I] [IsFiltered I] where
--   functor : I ⥤ (CommAlgCat R)
--   cocone : Cocone functor
--   is_p (i : I) : P R (functor.obj i)
--   isColimit : IsColimit cocone
#check Algebra.FormallyEtale
#check Algebra.Unramified
#check Module.pi_induction
#check Ring.DirectLimit.commRing

class IsDirectLimit {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] {F : I → Type*} (map : ∀ ⦃i j : I⦄ (h : i ≤ j), F i → F j) [DirectedSystem F map] {A : Type*} (ι : ∀ i : I, F i → A ) : Prop where
  commute : ∀ {i j : I} (h : i ≤ j) (f : F i), ι j (map h f) = ι i f
  surj : ∀ a : A, ∃ i : I, ∃ f : F i, ι i f = a
  eq_of : ∀ {i j : I} (f : F i) (g : F j), ι i f = ι j g ↔ ∃ k : I, ∃ (hik : i ≤ k) (hjk : j ≤ k), map hik f = map hjk g


structure Algebra.IndPresentation (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] (I : Type*) [Preorder I] [IsDirected I (· ≤ ·)] where
  S : I → Type w
  commRing_S (i : I) : CommRing (S i)
  algebra_S (i : I) : Algebra R (S i)
  map_S ⦃i j : I⦄ (h : i ≤ j) : S i →ₐ[R] S j
  directedSystem_S : DirectedSystem S (fun _ _ h ↦ map_S h)
  IsomDirectLimit : DirectLimit S map_S ≃ₐ[R] A

structure Algebra.Ind' (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R : Type u) [CommRing R] where

variable (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R : Type u) [CommRing R] (ind : Algebra.Ind P R)

instance : Category ind.Index := ind.categoryIndex

class Algebra.IsInd (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  isInd : ∃ (ind : Algebra.Ind P R), ind.cocone.pt = S

open Algebra
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
#check IsInd Etale R S
