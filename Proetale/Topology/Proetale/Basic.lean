/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Proetale.Morphisms.WeaklyEtale
import Proetale.Topology.Flat.QuasiCompactTopology

/-!
# The pro-étale site of a scheme

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme

/-- The small pro-étale site on `X` is the category of schemes, weakly étale over `X`. -/
def ProEt (X : Scheme.{u}) := MorphismProperty.Over @WeaklyEtale ⊤ X

def proetaleTopology : GrothendieckTopology Scheme.{u} :=
  qcTopology @WeaklyEtale

end AlgebraicGeometry.Scheme
