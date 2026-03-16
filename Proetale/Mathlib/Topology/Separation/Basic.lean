import Mathlib.Topology.Separation.Basic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed map sends closed singletons to closed singletons. -/
lemma IsClosedMap.isClosed_singleton {f : X → Y} (hf : IsClosedMap f)
    {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} := by
  rw [← Set.image_singleton]
  exact hf _ hx

/-- In a compact, T0 space every point specializes to a (not necessarily unique) closed point. -/
lemma exists_isClosed_specializes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T0Space X] (x : X) :
    ∃ (c : X), IsClosed {c} ∧ x ⤳ c := by
  obtain ⟨c, hx, hc⟩ := IsClosed.exists_closed_singleton (isClosed_closure (s := {x}))
    (Set.singleton_nonempty x |>.closure)
  use c, hc
  rwa [specializes_iff_mem_closure]
