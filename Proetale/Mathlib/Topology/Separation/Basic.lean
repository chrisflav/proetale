import Mathlib.Topology.Separation.Basic

/-- In a compact, T0 space every point specializes to a (not necessarily unique) closed point. -/
lemma exists_isClosed_specializes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T0Space X] (x : X) :
    ∃ (c : X), IsClosed {c} ∧ x ⤳ c := by
  obtain ⟨c, hx, hc⟩ := IsClosed.exists_closed_singleton (isClosed_closure (s := {x}))
    (Set.singleton_nonempty x |>.closure)
  use c, hc
  rwa [specializes_iff_mem_closure]
