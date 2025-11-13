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

instance t2Space_closedPoints [WLocalSpace X] :
    T2Space (closedPoints X) :=
  SpectralSpace.t2Space_of_isClosed_singleton  closedPoints.isClosed_singleton

instance CompactSpace_closedPoints [WLocalSpace X] :
    CompactSpace (closedPoints X) :=
  (IsClosed.isClosedEmbedding_subtypeVal inferInstance).compactSpace

instance totallyDisconnected_closedPoints [WLocalSpace X] :
    TotallyDisconnectedSpace (closedPoints X) :=
  SpectralSpace.totallyDisconnectedSpace_of_isClosed_singleton closedPoints.isClosed_singleton

end WLocalSpace
