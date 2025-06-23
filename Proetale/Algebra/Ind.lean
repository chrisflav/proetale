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

open CategoryTheory

instance : Limits.HasColimits (AlgCat R) := sorry


-- `Question: Why Algebra.Etale is preferred over RingHom.IsEtale?`

-- universe

-- 2 versions of Ind Category:
-- 1. Filtered diagrams (satisfying certain property) in the category of algebras over a fixed base ring.
-- 2. There is a functor from 1 to the `AlgCat R` (by taking the colimit), the essential image of this functor.
-- For 1: Given a cocone, satisfying `IsColimit`

-- class Algebra.Ind (P : {R S : Type u} → [CommRing R] → [CommRing S] → [Algebra R S] → Prop) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
--   isColim : ∃ I : Type w, ∃ c : Category I, ∃ h : IsFiltered I, ∃ F : Functor I (AlgCat R),
