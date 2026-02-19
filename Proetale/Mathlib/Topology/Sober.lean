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
  refine ⟨?_⟩
  intro S hS hSclosed
  -- Take generic points of the closures of the projections.
  have hS_fst : IsIrreducible (Prod.fst '' S) :=
    hS.image Prod.fst (continuous_fst.continuousOn)
  have hS_snd : IsIrreducible (Prod.snd '' S) :=
    hS.image Prod.snd (continuous_snd.continuousOn)
  obtain ⟨x, hx⟩ :=
    QuasiSober.sober (α := X) (S := closure (Prod.fst '' S)) hS_fst.closure isClosed_closure
  obtain ⟨y, hy⟩ :=
    QuasiSober.sober (α := Y) (S := closure (Prod.snd '' S)) hS_snd.closure isClosed_closure
  -- First, show `S ⊆ closure {(x,y)}`.
  have h₁ : S ⊆ closure ({(x, y)} : Set (X × Y)) := by
    intro p hp
    have hp₁ : p.1 ∈ closure ({x} : Set X) := by
      have : p.1 ∈ closure (Prod.fst '' S) := by
        exact subset_closure ⟨p, hp, rfl⟩
      simpa [hx.def] using this
    have hp₂ : p.2 ∈ closure ({y} : Set Y) := by
      have : p.2 ∈ closure (Prod.snd '' S) := by
        exact subset_closure ⟨p, hp, rfl⟩
      simpa [hy.def] using this
    have hEq :
        closure ({(x, y)} : Set (X × Y)) =
          closure ({x} : Set X) ×ˢ closure ({y} : Set Y) := by
      simpa [Set.singleton_prod_singleton] using
        (closure_prod_eq (s := ({x} : Set X)) (t := ({y} : Set Y)))
    rw [hEq]
    exact ⟨hp₁, hp₂⟩
  -- Next, show `(x,y) ∈ S`, hence `closure {(x,y)} ⊆ S` since `S` is closed.
  have hxy : (x, y) ∈ S := by
    by_contra hxy
    have hnhds : (Sᶜ : Set (X × Y)) ∈ nhds (x, y) :=
      hSclosed.isOpen_compl.mem_nhds (by simpa using hxy)
    rcases (mem_nhds_prod_iff').1 hnhds with ⟨U, V, hUo, hxU, hVo, hyV, hUV⟩
    have hSsub : S ⊆ (U ×ˢ V)ᶜ := by
      intro p hp
      have : p ∉ U ×ˢ V := by
        intro hpUV'
        exact (hUV hpUV') hp
      exact this
    have hSsub' : S ⊆ (Uᶜ ×ˢ (Set.univ : Set Y)) ∪ ((Set.univ : Set X) ×ˢ Vᶜ) := by
      simpa [Set.compl_prod_eq_union] using hSsub
    have hclosed₁ : IsClosed (Uᶜ ×ˢ (Set.univ : Set Y)) :=
      (hUo.isClosed_compl).prod isClosed_univ
    have hclosed₂ : IsClosed ((Set.univ : Set X) ×ˢ Vᶜ) :=
      isClosed_univ.prod (hVo.isClosed_compl)
    have hpre : IsPreirreducible S := hS.isPreirreducible
    have hcase :=
      (isPreirreducible_iff_isClosed_union_isClosed (s := S)).1 hpre _ _ hclosed₁ hclosed₂ hSsub'
    cases hcase with
    | inl hS₁ =>
        have hfstSub : Prod.fst '' S ⊆ Uᶜ := by
          rintro _ ⟨p, hp, rfl⟩
          exact (hS₁ hp).1
        have hx_in : x ∈ closure (Prod.fst '' S) := by
          have : x ∈ closure ({x} : Set X) := by
            simpa using (subset_closure (by simp : x ∈ ({x} : Set X)))
          simpa [hx.def] using this
        have hx_not : x ∈ Uᶜ := (hUo.isClosed_compl.closure_subset_iff.2 hfstSub) hx_in
        exact hx_not hxU
    | inr hS₂ =>
        have hsndSub : Prod.snd '' S ⊆ Vᶜ := by
          rintro _ ⟨p, hp, rfl⟩
          exact (hS₂ hp).2
        have hy_in : y ∈ closure (Prod.snd '' S) := by
          have : y ∈ closure ({y} : Set Y) := by
            simpa using (subset_closure (by simp : y ∈ ({y} : Set Y)))
          simpa [hy.def] using this
        have hy_not : y ∈ Vᶜ := (hVo.isClosed_compl.closure_subset_iff.2 hsndSub) hy_in
        exact hy_not hyV
  have h₂ : closure ({(x, y)} : Set (X × Y)) ⊆ S := by
    have : ({(x, y)} : Set (X × Y)) ⊆ S := by simpa [Set.singleton_subset_iff] using hxy
    exact closure_minimal this hSclosed
  refine ⟨(x, y), ?_⟩
  exact subset_antisymm h₂ h₁
