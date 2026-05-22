import Mathlib.Topology.Separation.Basic
import Proetale.Mathlib.Topology.Maps.Basic

/-- In a compact, T0 space every point specializes to a (not necessarily unique) closed point. -/
lemma exists_isClosed_specializes {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T0Space X] (x : X) :
    ∃ (c : X), IsClosed {c} ∧ x ⤳ c := by
  obtain ⟨c, hx, hc⟩ := IsClosed.exists_closed_singleton (isClosed_closure (s := {x}))
    (Set.singleton_nonempty x |>.closure)
  use c, hc
  rwa [specializes_iff_mem_closure]

/-- In a `T1Space`, every set is stable under specialization. -/
lemma StableUnderSpecialization.of_t1Space {X : Type*} [TopologicalSpace X] [T1Space X]
    (s : Set X) : StableUnderSpecialization s :=
  fun _ _ hxy hx ↦ hxy.eq ▸ hx
