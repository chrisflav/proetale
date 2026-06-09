/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Separation.Profinite

/-!
# Named alias: totally disconnected locally compact T2 ⇒ totally separated

This file provides a `theorem`-shaped, stably-named alias for the anonymous Mathlib instance
in `Mathlib/Topology/Separation/Profinite.lean` deriving `TotallySeparatedSpace` from
`LocallyCompactSpace`, `T2Space`, and `TotallyDisconnectedSpace`, so that the blueprint can
reference it by a stable identifier.
-/

/-- A totally disconnected, locally compact, T2 space is totally separated. -/
theorem TotallyDisconnectedSpace.totallySeparatedSpace
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    TotallySeparatedSpace X := inferInstance
