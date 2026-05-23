/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.RingHom.FinitePresentation
import Proetale.Mathlib.Algebra.Algebra.Pi

/-!
# Formal-étaleness of binary products of rings

We deduce that the binary product of two formally-étale `R`-algebras is formally-étale,
and likewise for étale, formally unramified, and formally smooth, by transferring the
finite-Pi case from `Mathlib.RingTheory.Etale.Pi`.

Rather than using `Matrix.vecCons` (whose elaboration does not eagerly reduce
`![A, B] 0` to `A`), we use an explicit case-based family `fin2Fam A B i`
defined by `Fin` pattern matching on `Fin 2`, so that `fin2Fam A B 0 = A` and
`fin2Fam A B 1 = B` reduce definitionally.

## Main results

- `Algebra.FormallyEtale.prod`: `A × B` is `R`-formally-étale when `A` and `B` are.
- `Algebra.Etale.prod`: `A × B` is `R`-étale when `A` and `B` are.
- `Algebra.FormallyUnramified.prod`: `A × B` is `R`-formally-unramified when `A` and `B` are.
- `Algebra.FormallySmooth.prod`: `A × B` is `R`-formally-smooth when `A` and `B` are.
-/

universe u

namespace Algebra

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A binary family `Fin 2 → Type u`. Definitionally `fin2Fam A B 0 = A` and
`fin2Fam A B 1 = B`. -/
private def fin2Fam (A B : Type u) : Fin 2 → Type u
  | ⟨0, _⟩ => A
  | ⟨1, _⟩ => B

private instance fin2Fam_commRing :
    ∀ i : Fin 2, CommRing (fin2Fam A B i)
  | ⟨0, _⟩ => ‹CommRing A›
  | ⟨1, _⟩ => ‹CommRing B›

private instance fin2Fam_algebra :
    ∀ i : Fin 2, Algebra R (fin2Fam A B i)
  | ⟨0, _⟩ => ‹Algebra R A›
  | ⟨1, _⟩ => ‹Algebra R B›

instance FormallyUnramified.prod [FormallyUnramified R A] [FormallyUnramified R B] :
    FormallyUnramified R (A × B) :=
  letI : ∀ i : Fin 2, FormallyUnramified R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallyUnramified R A›
    | ⟨1, _⟩ => ‹FormallyUnramified R B›
  FormallyUnramified.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance FormallySmooth.prod [FormallySmooth R A] [FormallySmooth R B] :
    FormallySmooth R (A × B) :=
  letI : ∀ i : Fin 2, FormallySmooth R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallySmooth R A›
    | ⟨1, _⟩ => ‹FormallySmooth R B›
  FormallySmooth.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance FormallyEtale.prod [FormallyEtale R A] [FormallyEtale R B] :
    FormallyEtale R (A × B) :=
  letI : ∀ i : Fin 2, FormallyEtale R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FormallyEtale R A›
    | ⟨1, _⟩ => ‹FormallyEtale R B›
  FormallyEtale.of_equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

/-- `A × B` is finitely presented as an `R`-algebra when both factors are. -/
instance FinitePresentation.prod [FinitePresentation R A] [FinitePresentation R B] :
    FinitePresentation R (A × B) :=
  letI : ∀ i : Fin 2, FinitePresentation R (fin2Fam A B i)
    | ⟨0, _⟩ => ‹FinitePresentation R A›
    | ⟨1, _⟩ => ‹FinitePresentation R B›
  letI : FinitePresentation R ((i : Fin 2) → fin2Fam A B i) :=
    Algebra.FinitePresentation.pi (fin2Fam A B)
  Algebra.FinitePresentation.equiv (AlgEquiv.piFinTwo R (fin2Fam A B))

instance Etale.prod [Etale R A] [Etale R B] : Etale R (A × B) where

end Algebra
