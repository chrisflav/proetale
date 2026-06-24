# Comparator challenge: ℓ-adic vs. étale cohomology

A [leanprover/comparator](https://github.com/leanprover/comparator) challenge/solution
pair for the headline result of this repository:

> If the étale cohomology groups `Hⁱ(X_ét, ℤ/ℓⁿℤ)` are finite, then the `ℓ`-adic
> cohomology `Hⁱ⁺¹(X_proét, ℤ_ℓ)` (mathlib's
> `AlgebraicGeometry.Scheme.EllAdicCohomology`) is the inverse limit over `n` of the
> étale cohomology groups `Hⁱ⁺¹(X_ét, ℤ/ℓⁿℤ)`.

- `Challenge.lean` — states the theorem using **only mathlib** (`import Mathlib`),
  with `sorry`. The étale cohomology system is built from mathlib primitives
  (`Functor.ofSequence`, `ZMod.castHom`, `constantSheaf`, `extFunctorObj`); its values
  are mathlib's `CategoryTheory.Sheaf.H` of the constant sheaves `ℤ/ℓⁿℤ`.
- `Solution.lean` — proves the identical statement using this repository
  (`import Proetale`); the challenge's cohomology system is definitionally equal to
  `AlgebraicGeometry.Scheme.ProEt.zmodCohomologySystem`.
- `config.json` — the comparator configuration.

To verify, build both modules and run comparator (see the comparator README for the
sandboxed invocation):

```bash
lake build Challenge Solution
lake env <path/to/comparator> Comparator/config.json
```
