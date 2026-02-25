import Mathlib.Topology.Sober

-- after `quasiSober_iff`
-- `by copilot`
theorem Homeomorph.quasiSober {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] (f : X ≃ₜ Y) : QuasiSober Y := by
  -- Prove quasi-sobriety of `Y` by producing generic points for irreducible closed sets.
  refine ⟨?_⟩
  intro S hSirr hSclosed
  -- Pull back `S` along the homeomorphism.
  let T : Set X := f.symm '' S

  have hTclosed : IsClosed T := by
    -- `f.symm` is a homeomorphism `Y ≃ₜ X`, so it maps closed sets to closed sets.
    simpa [T] using (Homeomorph.isClosed_image (X := Y) (Y := X) f.symm (s := S)).2 hSclosed

  have hTirr : IsIrreducible T := by
    -- Use `IsIrreducible.image` with `ContinuousOn`.
    -- (`Continuous` implies `ContinuousOn`.)
    simpa [T] using hSirr.image (fun y : Y => f.symm y) (f.symm.continuous.continuousOn)

  -- Get a generic point of `T` in `X`, then transport it to `Y`.
  have hx : IsGenericPoint hTirr.genericPoint T :=
    hTirr.isGenericPoint_genericPoint hTclosed

  -- `hx.image` gives a generic point for `closure (f '' T)`
  have hy : IsGenericPoint (f hTirr.genericPoint) (closure (f '' T)) :=
    hx.image f.continuous

  -- Now show `closure (f '' T) = S`, so `f hTirr.genericPoint` is generic for `S`.
  have hclosure : closure (f '' T) = S := by
    -- First compute `f '' T = S`.
    have himage : f '' T = S := by
      -- `f '' (f.symm '' S) = S` for a homeomorphism.
      ext y
      constructor
      · rintro ⟨x, hxT, rfl⟩
        rcases hxT with ⟨y', hy'S, rfl⟩
        simpa using hy'S
      · intro hyS
        refine ⟨f.symm y, ?_, by simp⟩
        exact ⟨y, hyS, by simp⟩
    -- Since `S` is closed, `closure S = S`.
    simp [himage]

  -- Convert the generic-point target set using `hclosure`.
  have : IsGenericPoint (f hTirr.genericPoint) S := by
    simpa [hclosure] using hy

  exact ⟨f hTirr.genericPoint, this⟩

-- put this at end of the file
instance QuasiSober.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [QuasiSober X] [QuasiSober Y] : QuasiSober (X × Y) := by
  refine ⟨fun {S} hS hSclosed => ?_⟩
  -- Project S to X and Y; images are irreducible
  have hX : IsIrreducible (Prod.fst '' S : Set X) :=
    hS.image Prod.fst continuous_fst.continuousOn
  have hY : IsIrreducible (Prod.snd '' S : Set Y) :=
    hS.image Prod.snd continuous_snd.continuousOn
  -- Get generic points of closures
  let x₀ := hX.genericPoint
  let y₀ := hY.genericPoint
  have hx₀ : IsGenericPoint x₀ (closure (Prod.fst '' S)) :=
    hX.isGenericPoint_genericPoint_closure
  have hy₀ : IsGenericPoint y₀ (closure (Prod.snd '' S)) :=
    hY.isGenericPoint_genericPoint_closure
  -- Key step: (x₀, y₀) ∈ S by contradiction + irreducibility
  have hmem : (x₀, y₀) ∈ S := by
    by_contra hmem
    -- Since S is closed and (x₀, y₀) ∉ S, get open product neighborhood disjoint from S
    have hopen_compl : (x₀, y₀) ∈ Sᶜ := hmem
    have hSc_open : IsOpen Sᶜ := hSclosed.isOpen_compl
    rw [isOpen_prod_iff] at hSc_open
    obtain ⟨U, V, hU, hV, hx₀U, hy₀V, hUV⟩ := hSc_open x₀ y₀ hopen_compl
    -- S ⊆ Uᶜ ×ˢ univ ∪ univ ×ˢ Vᶜ (since S ∩ (U ×ˢ V) = ∅)
    have hcover : S ⊆ (Uᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Vᶜ) := by
      intro ⟨a, b⟩ hab
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and]
      by_contra h
      push_neg at h
      obtain ⟨ha, hb⟩ := h
      exact hUV (Set.mk_mem_prod ha hb) hab
    -- By irreducibility, S ⊆ Uᶜ ×ˢ univ or S ⊆ univ ×ˢ Vᶜ
    have hirr := isPreirreducible_iff_isClosed_union_isClosed.mp hS.isPreirreducible
    rcases hirr _ _ (hU.isClosed_compl.prod isClosed_univ) (isClosed_univ.prod hV.isClosed_compl)
      hcover with h | h
    · -- S ⊆ Uᶜ ×ˢ univ, so fst '' S ⊆ Uᶜ, hence closure(fst '' S) ⊆ Uᶜ
      have hfst : Prod.fst '' S ⊆ Uᶜ := by
        rintro a ⟨⟨a', b'⟩, hab', rfl⟩; exact (h hab').1
      have : closure (Prod.fst '' S) ⊆ Uᶜ := closure_minimal hfst hU.isClosed_compl
      -- x₀ ∈ closure {x₀} = closure(fst '' S) ⊆ Uᶜ, contradicting x₀ ∈ U
      have : x₀ ∈ Uᶜ := this (hx₀.def ▸ subset_closure (Set.mem_singleton x₀))
      exact this hx₀U
    · -- S ⊆ univ ×ˢ Vᶜ, so snd '' S ⊆ Vᶜ
      have hsnd : Prod.snd '' S ⊆ Vᶜ := by
        rintro b ⟨⟨a', b'⟩, hab', rfl⟩; exact (h hab').2
      have : closure (Prod.snd '' S) ⊆ Vᶜ := closure_minimal hsnd hV.isClosed_compl
      have : y₀ ∈ Vᶜ := this (hy₀.def ▸ subset_closure (Set.mem_singleton y₀))
      exact this hy₀V
  -- Now construct the generic point
  refine ⟨(x₀, y₀), ?_⟩
  -- Show closure {(x₀, y₀)} = S
  apply Set.Subset.antisymm
  · -- closure {(x₀, y₀)} ⊆ S: since S is closed and (x₀, y₀) ∈ S
    exact closure_minimal (Set.singleton_subset_iff.mpr hmem) hSclosed
  · -- S ⊆ closure {(x₀, y₀)}
    -- closure {(x₀, y₀)} = closure {x₀} ×ˢ closure {y₀} = closure(fst '' S) ×ˢ closure(snd '' S)
    have hcl : closure ({(x₀, y₀)} : Set (X × Y)) =
        closure ({x₀} : Set X) ×ˢ closure ({y₀} : Set Y) := by
      rw [← Set.singleton_prod_singleton, closure_prod_eq]
    rw [hcl, hx₀.def, hy₀.def]
    intro ⟨a, b⟩ hab
    exact ⟨subset_closure ⟨(a, b), hab, rfl⟩, subset_closure ⟨(a, b), hab, rfl⟩⟩
