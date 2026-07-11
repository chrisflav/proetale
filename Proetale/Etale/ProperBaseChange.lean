/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Proetale.Mathlib.AlgebraicGeometry.Sites.DerivedPushforward
import Proetale.Mathlib.CategoryTheory.Sites.Torsion

/-!
# The proper base change theorem for étale cohomology

Let

```
X' --g'--> X
|          |
f'         f
↓          ↓
S' --g---> S
```

be a cartesian square of schemes with `f` proper. The **proper base change theorem**
(SGA 4, Exp. XII; Stacks 0A4B) asserts that the derived base change transformation

`derivedBaseChangeNatTrans : Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*`

(`Proetale/Mathlib/AlgebraicGeometry/Sites/DerivedPushforward.lean`) is an isomorphism
on every bounded below complex of abelian sheaves on `X_ét` with locally torsion
cohomology sheaves.

This file contains the *statements*
(`AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app` and the single-sheaf
corollary); the proof is a long-term project, decomposed in the blueprint chapter
"Proper base change" (`blueprint-verso/ProetaleBlueprint/Chapters/ProperBaseChange.lean`).
All definitions entering the statement are sorry-free.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/-- **The proper base change theorem** (SGA 4, Exp. XII, 5.1; Stacks 0A4B): for a
cartesian square of schemes with `f` proper, the derived base change transformation
`Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` on bounded below derived categories of abelian sheaves
over the small étale sites is an isomorphism on every complex with locally torsion
cohomology sheaves. -/
theorem isIso_derivedBaseChangeNatTrans_app [IsProper f] (hc : IsPullback g' f' f g)
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ n : ℤ, Sheaf.IsLocallyTorsion
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' hc.w).app K) := by
  -- **Proof strategy** (SGA 4 XII, Stacks 0A4B; see the blueprint chapter
  -- "Proper base change" for the full decomposition):
  --
  -- 1. **Dévissage in `K`.** By the hypercohomology spectral sequence / induction on
  --    the (bounded below) range of `K` using the truncation triangles and the five
  --    lemma, reduce to `K = (DerivedCategoryPlus.singleFunctor _ 0).obj F` for a
  --    single locally torsion abelian sheaf `F`; by writing a torsion sheaf as a
  --    filtered colimit of its `n`-torsion subsheaves and compatibility of both sides
  --    with filtered colimits (qcqs sites, cohomology commutes with filtered
  --    colimits; `f` is qcqs since it is proper), reduce to sheaves of
  --    `ℤ/nℤ`-modules, and by localization to `ℤ/ℓᵏℤ` for primes `ℓ`.
  -- 2. **Stalkwise reformulation.** Isomorphy of a morphism of sheaves on the small
  --    étale site of `S'` may be checked on stalks at geometric points
  --    (`Scheme.geometricFiber`, `GrothendieckTopology.Point.sheafFiber`); the stalk
  --    of `R^q f'_*` at a geometric point of `S'` is computed, via the limit over
  --    étale neighbourhoods, as the cohomology of the base change of `X'` to the
  --    Spec of the strict henselization — this reduces the theorem to the
  --    **special case**: `S` the spectrum of a strictly henselian local ring, `S'`
  --    its closed point, i.e. `H^q(X, F) ≅ H^q(X₀, F|_{X₀})` for `X₀` the closed
  --    fiber.
  --    (Prerequisite gap: strictly henselian local rings and the geometric-point
  --    stalk machinery for the small étale site.)
  -- 3. **Degree `0` over a strictly henselian base**: sections over `X` biject with
  --    sections over the closed fiber. This uses the finite case (Stein
  --    factorization: `f_* 𝒪` finite over the henselian base splits into local
  --    factors, so the connected components of `X` and `X₀` correspond) — the
  --    idempotent-lifting argument.
  -- 4. **Finite morphisms**: for `f` finite, `R^q f_* = 0` for `q > 0` and base
  --    change holds — stalks of `f_*F` at geometric points are finite products of
  --    stalks of `F`, because a finite algebra over a strictly henselian local ring
  --    is a product of local henselian algebras.
  -- 5. **Curves**: `H^q(C, ℤ/nℤ)` for a proper curve `C` over an algebraically
  --    closed field: vanishing for `q > 2` and the computation in low degrees via
  --    Kummer/Artin–Schreier theory, the Picard group, and Tsen's theorem
  --    (`Br(function field) = 0`). This is the deepest missing mathlib input.
  -- 6. **Dévissage in `f`**: locally on `S`, factor `f` through projective space;
  --    by 4., Čech arguments and induction on the fiber dimension (fibrations in
  --    curves), reduce to relative dimension `≤ 1`, treated by 3.–5. via the Leray
  --    spectral sequence for a fibration in curves.
  sorry

/-- The proper base change theorem for a single locally torsion abelian sheaf, placed
in degree `0` of the bounded below derived category. -/
theorem isIso_derivedBaseChangeNatTrans_app_singleFunctor [IsProper f]
    (hc : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology Ab.{u + 1})
    (hF : Sheaf.IsLocallyTorsion F) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' hc.w).app
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)) := by
  -- Follows from `isIso_derivedBaseChangeNatTrans_app`: the homology of
  -- `singleFunctor 0` is `F` in degree `0` (locally torsion by `hF`) and zero
  -- elsewhere (zero sheaves are locally torsion).
  refine isIso_derivedBaseChangeNatTrans_app f g f' g' hc _ (fun n ↦ ?_)
  have e : (DerivedCategoryPlus.homologyFunctor
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F) ≅
      (HomologicalComplex.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1})
        (ComplexShape.up ℤ) n).obj ((HomologicalComplex.single
          (Sheaf X.smallEtaleTopology Ab.{u + 1}) (ComplexShape.up ℤ) 0).obj F) :=
    (DerivedCategoryPlus.homologyFunctorFactors
      (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).app _
  by_cases hn : n = 0
  · subst hn
    exact Sheaf.IsLocallyTorsion.of_iso
      (((HomologicalComplex.homologyFunctorSingleIso
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) (ComplexShape.up ℤ) 0).app F).symm ≪≫
          e.symm) hF
  · exact Sheaf.isLocallyTorsion_of_isZero
      ((HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 F n hn).of_iso e)

end AlgebraicGeometry.Scheme
