/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Separation.Profinite

/-!
# Named alias: totally disconnected locally compact T2 ⇒ totally separated
-/

universe u

/-- A totally disconnected, locally compact, T2 space is totally separated; in particular,
any two distinct points are separated by a clopen partition.

This is a `theorem`-shaped, stably-named alias for the anonymous Mathlib instance
in `Mathlib/Topology/Separation/Profinite.lean`. -/
theorem TotallyDisconnectedSpace.totallySeparatedSpace
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    TotallySeparatedSpace X := inferInstance
