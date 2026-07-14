# Comparator challenge: ℓ-adic vs. étale cohomology

A [leanprover/comparator](https://github.com/leanprover/comparator) challenge/solution
pair for the headline result of this repository:

> If the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite, then the `ℓ`-adic
> cohomology `Hⁱ⁺¹(X_proét, ℤ_ℓ)` (mathlib's
> `AlgebraicGeometry.Scheme.EllAdicCohomology`) is the inverse limit over `n` of the
> étale cohomology groups `Hⁱ⁺¹(X_ét, ℤ/ℓⁿℤ)`, **canonically**.

Since there is no mathlib-definable natural map between the two sides in either
direction, the statement is formulated via the canonical comparison zig-zag

```
Hᵐ(X_proét, ℤ_ℓ) ──ρ──▸ lim_n Hᵐ(X_proét, ℤ/ℓⁿℤ) ◂──lim c── lim_n Hᵐ(X_ét, ℤ/ℓⁿℤ)
```

through the pro-étale cohomology of the sheaves of continuous (= locally constant)
`ℤ/ℓⁿℤ`-valued functions, where `ρ` is induced by the reduction maps `ℤ_[ℓ] → ℤ/ℓⁿℤ`
on coefficient sheaves and `c` is the levelwise étale-to-pro-étale comparison map. The
challenge theorems assert that `c` is levelwise bijective in every degree
(unconditionally), that `ρ` is bijective in degree `i + 1` under the finiteness
hypothesis, and that consequently there is a *unique* additive equivalence between the
two sides of the headline statement compatible with `ρ` and `c`.

- `Definitions.lean` — constructs the systems and the canonical maps using **only
  mathlib** (`import Mathlib`), from mathlib primitives (`Functor.ofSequence`,
  `ZMod.castHom`, `constantSheaf`, `continuousMapPresheafAb`, `extFunctorObj`,
  `Functor.sheafPullback`, `Functor.mapExtAddHom` and the adjunction calculus). The
  values of the cohomology systems are mathlib's `CategoryTheory.Sheaf.H` of the
  constant étale sheaves `ℤ/ℓⁿℤ`, resp. of the pro-étale sheaves of continuous
  `ℤ/ℓⁿℤ`-valued functions (so that the `ℤ_[ℓ]`-analogue of the latter is mathlib's
  `EllAdicCohomology` by definition).
- `Challenge.lean` — states the three theorems, with `sorry`.
- `Solution.lean` — proves the identical statements using this repository
  (`Proetale/Topology/Comparison/EllAdicCanonical.lean`).
- `config.json` — the comparator configuration.

To verify, build both modules and run comparator (see the comparator README for the
sandboxed invocation):

```bash
lake build Challenge Solution
lake env <path/to/comparator> Comparator/config.json
```
