/-
Copyright (c) 2025 Jiang Jiedong, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiang Jiedong, Christian Merten
-/
import Mathlib.Topology.Spectral.Basic

/-!
# Profinite spaces are spectral

-/

instance Prespectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : PrespectralSpace T := sorry

instance Spectral.of_profinite {T : Type*} [TopologicalSpace T] [T2Space T] [CompactSpace T]
  [TotallyDisconnectedSpace T] : SpectralSpace T where
