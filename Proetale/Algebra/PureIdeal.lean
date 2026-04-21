/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!

# Pure ideals

An ideal `I` of a ring `R` is called pure if `R ⧸ I` is flat over `R`
(see [Stacks 04PR](https://stacks.math.columbia.edu/tag/04PR)).
We don't actually define this term, but use `Module.Flat R (R ⧸ I)` instead. In this file we show
some properties of such ideals.

## Main results and definitions

- `Ideal.inf_eq_mul_of_flat`: If `I` is pure, `I ⊓ J = I * J` for every ideal `J`.
- `Ideal.flat_of_inf_eq_mul`: If for any f.g. ideal `J`, the equality `I ⊓ J = I * J` holds, then
  `I` is pure.
- `Ideal.zeroLocus_inj_of_flat`: If `I` and `J` are pure ideals such that `V(I) = V(J)`, then
  `I = J`.

-/

variable {R : Type*} [CommRing R]

open TensorProduct
