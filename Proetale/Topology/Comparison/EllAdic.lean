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
  Mittag-Leffler-type hypothesis that the transition maps of the degree-`i` étale
  cohomology system are surjective. Some such hypothesis is necessary: in general the
  two sides differ by a `lim¹`-term (Jannsen); the hypothesis holds e.g. whenever the
  étale cohomology groups `H^i(X_ét, ℤ/ℓⁿℤ)` are finite.

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
`ℤ/ℓⁿℤ`** in positive degrees, under the Mittag-Leffler-type hypothesis that the
transition maps of the étale cohomology system one degree lower are surjective (e.g.
because the groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite). In general the two sides differ by a
`lim¹`-term. -/
theorem nonempty_ellAdicCohomology_addEquiv_limit (i : ℕ)
    (hML : ∀ n, Function.Surjective (ConcreteCategory.hom
      ((zmodCohomologySystem X ℓ i).map (homOfLE (Nat.le_succ n)).op))) :
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

end ProEt

end AlgebraicGeometry.Scheme
