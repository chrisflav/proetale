/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Separation.Profinite

/-!
# Profinite spaces are spectral

-/

instance Prespectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : PrespectralSpace T :=
  PrespectralSpace.of_isTopologicalBasis isTopologicalBasis_isClopen
    fun _ hU => IsClosed.isCompact (IsClopen.isClosed hU)

instance Spectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : SpectralSpace T where
