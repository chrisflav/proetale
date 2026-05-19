/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.JacobsonSpace
import Proetale.Mathlib.Topology.Spectral.Basic
import Proetale.Topology.SpectralSpace.WLocal.Basic
import Proetale.Topology.SpectralSpace.Constructible

/-!
# Closed Points of w-local spaces is profinite

-/

variable {X : Type*} [TopologicalSpace X]

namespace WLocalSpace

instance spectralSpace_closedPoints [WLocalSpace X] : SpectralSpace (closedPoints X) :=
  SpectralSpace.of_isClosed X

instance t1Space_closedPoints : T1Space (closedPoints X) where
  t1 := closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

end WLocalSpace
