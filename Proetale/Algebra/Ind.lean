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

universe u v w w'

open CategoryTheory Limits

instance : Limits.HasColimits (AlgCat R) := sorry

-- `Question: Why Algebra.Etale is preferred over RingHom.IsEtale?`

-- I dont want to use this one!
--
-- universe

-- 2 versions of Ind Category:
-- 1. Filtered diagrams (satisfying certain property) in the category of algebras over a fixed base ring.
-- 2. There is a functor from 1 to the `AlgCat R` (by taking the colimit), the essential image of this functor.
-- For 1: Given a cocone, satisfying `IsColimit`

-- class Algebra.Ind (P : {R S : Type u} → [CommRing R] → [CommRing S] → [Algebra R S] → Prop) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
--   isColim : ∃ I : Type w, ∃ c : Category I, ∃ h : IsFiltered I, ∃ F : Functor I (AlgCat R),
-- `Order of (R : Type u) [CommRing R] (S : Type u) matters, [CommRing S] is not [Ring S]`
-- Becareful about the difference between CommRing S and Ring S.
structure Algebra.Ind (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R : Type u) [CommRing R] where
  Index : Type w
  categoryIndex : Category Index
  isFilteredIndex : IsFiltered Index
  functor : Index ⥤ (CommAlgCat R)
  cocone : Cocone functor
  is_p (i : Index) : P R (functor.obj i)
  isColimit : IsColimit cocone

variable (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R : Type u) [CommRing R] (ind : Algebra.Ind P R)

instance : Category ind.Index := ind.categoryIndex

class Algebra.IsInd (P : ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S], Prop)
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  isInd : ∃ (ind : Algebra.Ind P R), ind.cocone.pt = S

open Algebra
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

section

variable {ι : Type*} [Preorder ι] (F : ι → Type*) (f : ∀ ⦃i j : ι⦄, i ≤ j → F i → F j)
  [DirectedSystem F f]

/-- A characterization of a type being the direct colimit of a directed system. -/
class IsDirectLimit (G : Type*) (g : ∀ i, F i → G) : Prop where
  comp_eq {i j : ι} (hij : i ≤ j) : g j ∘ f hij = g i
  jointly_surjective (x : G) : ∃ i, x ∈ Set.range (g i)
  eq_iff {i j : ι} (x : F i) (y : F j) : g i x = g j y ↔ ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k),
    f hik x = f hjk y

variable (G : Type*) (g : ∀ i, F i → G)

/--
An ind-presentation of `S` over `R` is a directed system of `R`-algebras, whose
colimit is `S`.
-/
@[ext]
structure Algebra.IndPresentation (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (ι : Type*) [Preorder ι] where
  [isDirected : IsDirected ι (fun i j : ι ↦ i ≤ j)]
  F : ι → Type v
  [commRing : ∀ i, CommRing (F i)]
  [algebra : ∀ i, Algebra R (F i)]
  f : ∀ ⦃i j : ι⦄, i ≤ j → F i →ₐ[R] F j
  g : ∀ i, F i →ₐ[R] S
  [directedSystem : DirectedSystem F (fun _ _ hij ↦ ⇑(f hij))]
  [isDirectLimit : IsDirectLimit F (fun _ _ hij ↦ ⇑(f hij)) S (fun i ↦ ⇑(g i))]

namespace Algebra.IndPresentation

attribute [instance] commRing algebra directedSystem

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

@[simps]
def Algebra.IndPresentation.self : IndPresentation R S Unit where
  isDirected := by
    constructor
    intro _ _
    use ()
  F _ := S
  f _ _ _ := AlgHom.id _ _
  g i := AlgHom.id _ _
  directedSystem := by constructor <;> simp
  isDirectLimit := by constructor <;> simp

end Algebra.IndPresentation

/-- An algebra is ind-étale if it can be written as the directed colimit of étale
algebras. -/
class Algebra.IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  out : ∃ (ι : Type u) (_ : Preorder ι) (P : Algebra.IndPresentation R S ι),
    ∀ (i : ι), Algebra.Etale R (P.F i)

end
