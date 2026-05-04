/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Morphisms.WeaklyEtale
import Proetale.Topology.Flat.QuasiCompactTopology

/-!
# The pro-étale site of a scheme

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable (X : Scheme.{u})

def zariskiTopology : GrothendieckTopology X.ProEt :=
  smallGrothendieckTopologyOfLE (P := @IsOpenImmersion) _ fun _ _ _ _ ↦ inferInstance

end ProEt

end AlgebraicGeometry.Scheme
