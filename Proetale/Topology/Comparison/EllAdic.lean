/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.EllAdicLimit
import Proetale.Topology.Comparison.ContinuousComparison
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.SequentialLimit

/-!
# `ℓ`-adic cohomology via étale cohomology

Let `X` be a scheme and `ℓ` a prime. Mathlib defines the `ℓ`-adic cohomology
`X.EllAdicCohomology ℓ n` as the cohomology of the pro-étale site of `X` with
coefficients in the sheaf of continuous `ℤ_[ℓ]`-valued functions
(`Mathlib.AlgebraicGeometry.Sites.ElladicCohomology`). We compare it with étale
cohomology of the finite coefficients `ℤ/ℓⁿℤ`:

- `AlgebraicGeometry.Scheme.ProEt.nonempty_ellAdicCohomology_addEquiv_continuousH`:
  unconditionally, `ℓ`-adic cohomology is the *continuous étale cohomology* (in the
  sense of Jannsen) of the inverse system `(ℤ/ℓⁿℤ)ₙ` of constant étale sheaves.
- `AlgebraicGeometry.Scheme.ProEt.nonempty_ellAdicCohomology_zero_addEquiv_limit` and
  `AlgebraicGeometry.Scheme.ProEt.nonempty_ellAdicCohomology_addEquiv_limit`:
  **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
  `ℤ/ℓⁿℤ`** — in degree `0` unconditionally, and in degree `i + 1` under the
  hypothesis that the degree-`i` étale cohomology system satisfies the Mittag-Leffler
  condition (`CategoryTheory.Functor.IsMittagLeffler`). Some such hypothesis is
  necessary: in general the two sides differ by a `lim¹`-term (Jannsen). The
  hypothesis holds when the transition maps of the degree-`i` system are surjective
  (`nonempty_ellAdicCohomology_addEquiv_limit_of_surjective`), and in particular
  whenever the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite
  (`nonempty_ellAdicCohomology_addEquiv_limit_of_finite`). Note that finiteness does
  *not* imply surjectivity of the transition maps — for `X = Spec ℝ`, `ℓ = 2`,
  `i = 1` the system is `ℤ/2 ← ℤ/2 ← ⋯` with zero transition maps — so the genuine
  Mittag-Leffler hypothesis is essential for the finite case.

These results are deduced from the comparison of continuous étale cohomology with
pro-étale cohomology (`nonempty_continuousH_addEquiv_H_limit`,
`Proetale/Topology/Comparison/ContinuousComparison.lean`, BS Proposition 5.6.2) using
the identification of the `ℓ`-adic sheaf with `lim ν^*(ℤ/ℓⁿℤ)`
(`Proetale/Topology/Comparison/EllAdicLimit.lean`).
-/

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

namespace ProEt

/-- **`ℓ`-adic cohomology is continuous étale cohomology of `(ℤ/ℓⁿℤ)ₙ`**: for any
scheme `X` and prime `ℓ`, the pro-étale cohomology of the `ℓ`-adic sheaf agrees with
the continuous étale cohomology (Jannsen) of the inverse system of constant étale
sheaves `ℤ/ℓⁿℤ`. -/
theorem nonempty_ellAdicCohomology_addEquiv_continuousH (i : ℕ) :
    Nonempty (X.EllAdicCohomology ℓ i ≃+ continuousH X (zmodSystem X ℓ) i) := by
  -- `X.EllAdicCohomology ℓ i` is by definition
  -- `Sheaf.H ((sheafCompose _ uliftFunctor).obj (X.ellAdicSheaf ℓ)) i`, i.e. the
  -- `Ext`-group from the constant sheaf `ℤ` into the lifted `ℓ`-adic sheaf.
  -- Transport along `ellAdicSheafLimitIso X ℓ` in the second variable (apply
  -- `(extFunctorObj (proetaleConstantUnit X) i).mapIso` and convert the resulting
  -- isomorphism of `AddCommGrpCat` into an additive equivalence — grep for an
  -- existing `AddCommGrpCat`-iso-to-`AddEquiv` conversion, or build it from
  -- `Iso.hom`/`Iso.inv` with `AddEquiv.mk'`); this identifies it with
  -- `Sheaf.H (limit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u+1})) i`.
  -- Then apply `(nonempty_continuousH_addEquiv_H_limit (zmodSystem X ℓ)
  -- (epi_transition_zmodSystem X ℓ) i).some.symm`. Mind that `EllAdicCohomology` is a
  -- `def`, so unfold it (`show`/`Sheaf.H`-level `rfl` bridges with fully spelled
  -- types, or `Nonempty.map` along definitional equalities).
  have e1 : X.EllAdicCohomology ℓ i ≃+
      Sheaf.H (limit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1})) i :=
    ((extFunctorObj (proetaleConstantUnit X) i).mapIso
      (ellAdicSheafLimitIso X ℓ)).addCommGroupIsoToAddEquiv
  have e2 : continuousH X (zmodSystem X ℓ) i ≃+
      Sheaf.H (limit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1})) i :=
    (nonempty_continuousH_addEquiv_H_limit (zmodSystem X ℓ)
      (epi_transition_zmodSystem X ℓ) i).some
  exact ⟨e1.trans e2.symm⟩

/-- The inverse system of étale cohomology groups `n ↦ Hⁱ(X_ét, ℤ/ℓⁿℤ)`. -/
noncomputable abbrev zmodCohomologySystem (i : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Ext.levelSystem (etaleConstantUnit X) (zmodSystem X ℓ) i

omit [Fact ℓ.Prime] in
/-- The terms of `zmodCohomologySystem` are the étale cohomology groups of the constant
sheaves `ℤ/ℓⁿℤ`. -/
lemma zmodCohomologySystem_obj (i n : ℕ) :
    (zmodCohomologySystem X ℓ i).obj (op n) =
      AddCommGrpCat.of (Sheaf.H ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))) i) :=
  rfl

/-- **`ℓ`-adic cohomology in degree `0` is the inverse limit of the étale cohomology
groups of `ℤ/ℓⁿℤ`.** -/
theorem nonempty_ellAdicCohomology_zero_addEquiv_limit :
    Nonempty (X.EllAdicCohomology ℓ 0 ≃+ ↥(limit (zmodCohomologySystem X ℓ 0))) := by
  -- Combine `nonempty_ellAdicCohomology_addEquiv_continuousH` in degree `0` with
  -- `Ext.zeroAddEquivLimitLevelSystem (etaleConstantUnit X) (zmodSystem X ℓ)`
  -- (`continuousH X F 0` is by definition
  -- `Ext ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit X)) F 0`).
  have e1 : X.EllAdicCohomology ℓ 0 ≃+ continuousH X (zmodSystem X ℓ) 0 :=
    (nonempty_ellAdicCohomology_addEquiv_continuousH X ℓ 0).some
  have e2 : continuousH X (zmodSystem X ℓ) 0 ≃+ ↥(limit (zmodCohomologySystem X ℓ 0)) :=
    Ext.zeroAddEquivLimitLevelSystem (etaleConstantUnit X) (zmodSystem X ℓ)
  exact ⟨e1.trans e2⟩

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, under the hypothesis that the étale cohomology system
one degree lower satisfies the Mittag-Leffler condition. In general the two sides
differ by a `lim¹`-term (Jannsen). The hypothesis holds e.g. when the transition maps
of that system are surjective
(`nonempty_ellAdicCohomology_addEquiv_limit_of_surjective`) or when its groups
`Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite
(`nonempty_ellAdicCohomology_addEquiv_limit_of_finite`). -/
theorem nonempty_ellAdicCohomology_addEquiv_limit (i : ℕ)
    (hML : (zmodCohomologySystem X ℓ i ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler) :
    Nonempty (X.EllAdicCohomology ℓ (i + 1) ≃+
      ↥(limit (zmodCohomologySystem X ℓ (i + 1)))) := by
  -- Combine `nonempty_ellAdicCohomology_addEquiv_continuousH` in degree `i + 1` with
  -- `Ext.nonempty_addEquiv_limit_levelSystem (etaleConstantUnit X) (zmodSystem X ℓ) i
  -- hML` (the required instances on the category of inverse systems of étale sheaves —
  -- enough injectives, `HasExt`, countable products — are provided in
  -- `Proetale/Topology/Comparison/ContinuousComparison.lean`).
  have e1 : X.EllAdicCohomology ℓ (i + 1) ≃+ continuousH X (zmodSystem X ℓ) (i + 1) :=
    (nonempty_ellAdicCohomology_addEquiv_continuousH X ℓ (i + 1)).some
  have e2 : continuousH X (zmodSystem X ℓ) (i + 1) ≃+
      ↥(limit (zmodCohomologySystem X ℓ (i + 1))) :=
    (Ext.nonempty_addEquiv_limit_levelSystem (etaleConstantUnit X)
      (zmodSystem X ℓ) i hML).some
  exact ⟨e1.trans e2⟩

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, when the transition maps of the étale cohomology system
one degree lower are surjective. Surjectivity of the transition maps is *strictly
stronger* than the Mittag-Leffler hypothesis of
`nonempty_ellAdicCohomology_addEquiv_limit`: for `X = Spec ℝ`, `ℓ = 2`, `i = 1` the
system consists of finite groups `ℤ/2` with zero transition maps, so it is
Mittag-Leffler but has no surjective transition map. -/
theorem nonempty_ellAdicCohomology_addEquiv_limit_of_surjective (i : ℕ)
    (hML : ∀ n, Function.Surjective (ConcreteCategory.hom
      ((zmodCohomologySystem X ℓ i).map (homOfLE (Nat.le_succ n)).op))) :
    Nonempty (X.EllAdicCohomology ℓ (i + 1) ≃+
      ↥(limit (zmodCohomologySystem X ℓ (i + 1)))) :=
  nonempty_ellAdicCohomology_addEquiv_limit X ℓ i
    (Ext.isMittagLeffler_forget_of_surjective_transition _ hML)

/-- **`ℓ`-adic cohomology is the inverse limit of the étale cohomology groups of
`ℤ/ℓⁿℤ`** in positive degrees, when the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` one
degree lower are finite: finiteness forces the Mittag-Leffler condition, since the
decreasing chain of images in a finite group stabilizes. -/
theorem nonempty_ellAdicCohomology_addEquiv_limit_of_finite (i : ℕ)
    (hfin : ∀ n : ℕ, Finite (ToType ((zmodCohomologySystem X ℓ i).obj (op n)))) :
    Nonempty (X.EllAdicCohomology ℓ (i + 1) ≃+
      ↥(limit (zmodCohomologySystem X ℓ (i + 1)))) :=
  nonempty_ellAdicCohomology_addEquiv_limit X ℓ i
    (Ext.isMittagLeffler_forget_of_finite _ hfin)

end ProEt

end AlgebraicGeometry.Scheme
