/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Separation.Profinite
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Proetale.Algebra.IndZariski

/-!
# The prime spectrum of rings of locally constant functions

Let `R` be a ring and `T` a profinite space. In this file we show that the ring
`LocallyConstant T R` of locally constant functions `T → R` satisfies
`Spec (LocallyConstant T R) ≃ₜ T × Spec R` and is ind-Zariski over `R`.

The ring `LocallyConstant T R` is the filtered colimit of the finite products
`LocallyConstant S R ≃ (S → R)` over the discrete quotients `S` of `T`, and the
homeomorphism is the topological incarnation of
`Spec (colim_S (S → R)) = lim_S (S × Spec R) = T × Spec R`; both facts are however
proved directly. This is the input for the construction of Stacks Tag 097D
(`def:modify-pi0-profinite` in the blueprint): modifying the connected components of
`Spec R` along a continuous map `T → π₀(Spec R)`, see
`WContractification.PullbackProfinite` in `Proetale.Algebra.WContractible`.

## Main declarations

* `LocallyConstant.toPrimeSpectrum`: the map `T × Spec R → Spec (LocallyConstant T R)`
  sending `(t, p)` to the prime of functions whose value at `t` lies in `p`.
* `LocallyConstant.homeomorphPrimeSpectrum`: for `T` profinite, `toPrimeSpectrum` is a
  homeomorphism.
* `LocallyConstant.instIndZariski`: `LocallyConstant T R` is ind-Zariski over `R`, being
  the filtered colimit of the finite products `LocallyConstant S R ≃ (S → R)` over the
  discrete quotients `S` of `T`.
-/

universe u

open PrimeSpectrum TopologicalSpace

namespace LocallyConstant

variable {T : Type*} [TopologicalSpace T] {R : Type*} [CommRing R]

/-!
### Characteristic functions of clopen subsets
-/

section CharFn

variable {U V : Set T}

lemma charFn_apply_of_mem (hU : IsClopen U) {t : T} (ht : t ∈ U) :
    charFn R hU t = 1 :=
  Set.indicator_of_mem ht 1

lemma charFn_apply_of_notMem (hU : IsClopen U) {t : T} (ht : t ∉ U) :
    charFn R hU t = 0 :=
  Set.indicator_of_notMem ht 1

lemma charFn_mul_charFn (hU : IsClopen U) (hV : IsClopen V) :
    charFn R hU * charFn R hV = charFn R (hU.inter hV) := by
  ext t
  by_cases htU : t ∈ U <;> by_cases htV : t ∈ V <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU, htV, Set.mem_inter_iff]

lemma charFn_mul_charFn_compl (hU : IsClopen U) :
    charFn R hU * charFn R hU.compl = 0 := by
  ext t
  by_cases htU : t ∈ U <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU]

lemma charFn_add_charFn_compl (hU : IsClopen U) :
    charFn R hU + charFn R hU.compl = 1 := by
  ext t
  by_cases htU : t ∈ U <;>
    simp [charFn_apply_of_mem, charFn_apply_of_notMem, htU]

end CharFn

/-!
### The prime spectrum of `LocallyConstant T R`
-/

variable (t : T) (p : PrimeSpectrum R)

/-- The prime of `LocallyConstant T R` associated to a point `t : T` and a prime `p` of
`R`: the ideal of functions whose value at `t` lies in `p`. For `T` profinite this
defines a homeomorphism `T × Spec R ≃ₜ Spec (LocallyConstant T R)`, see
`LocallyConstant.homeomorphPrimeSpectrum`. -/
def toPrimeSpectrum (tp : T × PrimeSpectrum R) :
    PrimeSpectrum (LocallyConstant T R) :=
  PrimeSpectrum.comap (evalRingHom tp.1) tp.2

lemma mem_toPrimeSpectrum_asIdeal {tp : T × PrimeSpectrum R} {f : LocallyConstant T R} :
    f ∈ (toPrimeSpectrum tp).asIdeal ↔ f tp.1 ∈ tp.2.asIdeal :=
  Iff.rfl

@[simp]
lemma algebraMap_apply_apply (r : R) (t : T) :
    algebraMap R (LocallyConstant T R) r t = r :=
  rfl

lemma comap_algebraMap_toPrimeSpectrum (tp : T × PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) (toPrimeSpectrum tp) = tp.2 := by
  ext x
  change algebraMap R (LocallyConstant T R) x tp.1 ∈ tp.2.asIdeal ↔ x ∈ tp.2.asIdeal
  simp

lemma toPrimeSpectrum_mem_basicOpen {tp : T × PrimeSpectrum R} {f : LocallyConstant T R} :
    toPrimeSpectrum tp ∈ basicOpen f ↔ f tp.1 ∉ tp.2.asIdeal :=
  Iff.rfl

lemma continuous_toPrimeSpectrum :
    Continuous (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  refine isTopologicalBasis_basic_opens.continuous_iff.mpr fun s hs ↦ ?_
  obtain ⟨f, rfl⟩ := hs
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨t, p⟩ (htp : toPrimeSpectrum (t, p) ∈ basicOpen f)
  rw [toPrimeSpectrum_mem_basicOpen] at htp
  refine ⟨(⇑f ⁻¹' {f t}) ×ˢ (basicOpen (f t) : Set (PrimeSpectrum R)), ?_, ?_, ?_⟩
  · rintro ⟨t', p'⟩ ⟨ht' : f t' = f t, hp'⟩
    change f t' ∉ p'.asIdeal
    rw [ht']
    exact hp'
  · exact ((f.isLocallyConstant.isClopen_fiber _).isOpen).prod (basicOpen (f t)).2
  · exact ⟨rfl, htp⟩

section Profinite

variable [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

omit [T2Space T] [TotallyDisconnectedSpace T] in
lemma toPrimeSpectrum_surjective :
    Function.Surjective (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  intro P
  -- `T` is nonempty since `LocallyConstant T R` has a prime ideal.
  have hT : Nonempty T := by
    by_contra h
    rw [not_nonempty_iff] at h
    refine P.isPrime.one_notMem ?_
    have : (1 : LocallyConstant T R) = 0 := by ext t; exact h.elim t
    rw [this]
    exact zero_mem _
  -- The collection of clopens whose characteristic function does not lie in `P`.
  set C : Set (Set T) := {U | ∃ hU : IsClopen U, charFn R hU ∉ P.asIdeal} with hC
  -- It is a filter base of closed nonempty sets, hence has nonempty intersection.
  have hUniv : Set.univ ∈ C :=
    ⟨isClopen_univ, by
      have h1 : charFn R isClopen_univ = (1 : LocallyConstant T R) := by
        ext t; exact charFn_apply_of_mem _ (Set.mem_univ t)
      rw [h1]
      exact P.isPrime.one_notMem⟩
  have hinter : ∀ U ∈ C, ∀ V ∈ C, U ∩ V ∈ C := by
    rintro U ⟨hU, hU'⟩ V ⟨hV, hV'⟩
    refine ⟨hU.inter hV, fun hmem ↦ ?_⟩
    rw [← charFn_mul_charFn hU hV] at hmem
    exact (P.isPrime.mem_or_mem hmem).elim hU' hV'
  have hne : ∀ U ∈ C, U.Nonempty := by
    rintro U ⟨hU, hU'⟩
    rcases Set.eq_empty_or_nonempty U with rfl | h
    · refine absurd ?_ hU'
      have : charFn R hU = (0 : LocallyConstant T R) := by
        ext t; exact charFn_apply_of_notMem _ (Set.notMem_empty t)
      rw [this]
      exact zero_mem _
    · exact h
  have hclosed : ∀ U ∈ C, IsClosed U := by
    rintro U ⟨hU, -⟩
    exact hU.isClosed
  haveI : Nonempty C := ⟨⟨Set.univ, hUniv⟩⟩
  obtain ⟨t₀, ht₀⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun U : C ↦ (U.1 : Set T))
    (fun U V ↦ ⟨⟨U.1 ∩ V.1, hinter _ U.2 _ V.2⟩, Set.inter_subset_left,
      Set.inter_subset_right⟩)
    (fun U ↦ hne _ U.2)
    (fun U ↦ (hclosed _ U.2).isCompact)
    (fun U ↦ hclosed _ U.2)
  have ht₀' : ∀ U ∈ C, t₀ ∈ U := fun U hU ↦ Set.mem_iInter.mp ht₀ ⟨U, hU⟩
  -- Key: the characteristic function of any clopen containing `t₀` is not in `P`.
  have hkey : ∀ (U : Set T) (hU : IsClopen U), t₀ ∈ U → charFn R hU ∉ P.asIdeal := by
    intro U hU htU hmem
    have hcompl : charFn R hU.compl ∉ P.asIdeal := fun hc ↦ by
      have h1 : (1 : LocallyConstant T R) ∈ P.asIdeal := by
        rw [← charFn_add_charFn_compl (R := R) hU]
        exact add_mem hmem hc
      exact P.isPrime.one_notMem h1
    exact (ht₀' _ ⟨hU.compl, hcompl⟩ : t₀ ∈ Uᶜ) htU
  -- Key: any function vanishing at `t₀` lies in `P`.
  have hvanish : ∀ f : LocallyConstant T R, f t₀ = 0 → f ∈ P.asIdeal := by
    intro f hf
    have hU : IsClopen (⇑f ⁻¹' {0}) := f.isLocallyConstant.isClopen_fiber 0
    have hcompl : charFn R hU.compl ∈ P.asIdeal := by
      have hmul : charFn R hU * charFn R hU.compl ∈ P.asIdeal := by
        rw [charFn_mul_charFn_compl]
        exact zero_mem _
      exact (P.isPrime.mem_or_mem hmul).resolve_left (hkey _ hU hf)
    have heq : f = f * charFn R hU.compl := by
      ext x
      by_cases hx : f x = 0
      · simp [hx]
      · simp [charFn_apply_of_mem hU.compl (by simpa using hx)]
    rw [heq]
    exact P.asIdeal.mul_mem_left _ hcompl
  refine ⟨(t₀, PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P), ?_⟩
  ext f
  change f t₀ ∈ (PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P).asIdeal ↔
    f ∈ P.asIdeal
  change algebraMap R (LocallyConstant T R) (f t₀) ∈ P.asIdeal ↔ f ∈ P.asIdeal
  have hsub : f - algebraMap R (LocallyConstant T R) (f t₀) ∈ P.asIdeal := by
    refine hvanish _ ?_
    change f t₀ - algebraMap R (LocallyConstant T R) (f t₀) t₀ = 0
    rw [algebraMap_apply_apply, sub_self]
  constructor
  · intro h
    simpa using add_mem hsub h
  · intro h
    simpa using sub_mem h hsub

lemma toPrimeSpectrum_injective :
    Function.Injective (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  rintro ⟨t, p⟩ ⟨t', p'⟩ h
  have hp : p = p' := by
    have := congrArg (PrimeSpectrum.comap (algebraMap R (LocallyConstant T R))) h
    rwa [comap_algebraMap_toPrimeSpectrum, comap_algebraMap_toPrimeSpectrum] at this
  subst hp
  suffices ht : t = t' by rw [ht]
  by_contra hne
  haveI : TotallySeparatedSpace T := loc_compact_t2_tot_disc_iff_tot_sep.mp ‹_›
  obtain ⟨U, hU, htU, ht'U⟩ := exists_isClopen_of_totally_separated hne
  have h1 : charFn R hU ∈ (toPrimeSpectrum (t', p)).asIdeal := by
    rw [mem_toPrimeSpectrum_asIdeal, charFn_apply_of_notMem hU ht'U]
    exact zero_mem _
  have h2 : charFn R hU ∉ (toPrimeSpectrum (t, p)).asIdeal := by
    rw [mem_toPrimeSpectrum_asIdeal, charFn_apply_of_mem hU htU]
    exact p.isPrime.one_notMem
  rw [h] at h2
  exact h2 h1

lemma isOpenMap_toPrimeSpectrum :
    IsOpenMap (toPrimeSpectrum : T × PrimeSpectrum R → _) := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro Q ⟨⟨t, p⟩, htp, rfl⟩
  obtain ⟨b, hb, htpb, hbW⟩ :=
    (isTopologicalBasis_isClopen.prod isTopologicalBasis_basic_opens).exists_subset_of_mem_open
      htp hW
  obtain ⟨U, hU, s, hs, rfl⟩ := hb
  obtain ⟨r, rfl⟩ := hs
  have hUclopen : IsClopen U := hU
  refine ⟨(basicOpen (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) :
      Set (PrimeSpectrum (LocallyConstant T R))), ?_, (basicOpen _).2, ?_⟩
  · intro Q' hQ'
    obtain ⟨⟨t', p'⟩, rfl⟩ := toPrimeSpectrum_surjective Q'
    rw [SetLike.mem_coe, toPrimeSpectrum_mem_basicOpen] at hQ'
    have hval : (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) t' =
        charFn R hUclopen t' * r := by simp
    rw [hval] at hQ'
    have ht'U : t' ∈ U := by
      by_contra ht'U
      rw [charFn_apply_of_notMem _ ht'U, zero_mul] at hQ'
      exact hQ' (zero_mem _)
    rw [charFn_apply_of_mem _ ht'U, one_mul] at hQ'
    exact ⟨(t', p'), hbW ⟨ht'U, hQ'⟩, rfl⟩
  · rw [SetLike.mem_coe, toPrimeSpectrum_mem_basicOpen]
    obtain ⟨htU, hpr⟩ := htpb
    have hval : (charFn R hUclopen * algebraMap R (LocallyConstant T R) r) t =
        charFn R hUclopen t * r := by simp
    rw [hval, charFn_apply_of_mem _ htU, one_mul]
    exact hpr

/-- For `T` profinite, the prime spectrum of `LocallyConstant T R` is `T × Spec R`.
This computes the Stacks 097D construction in one step: it is the topological
incarnation of `Spec (colim_S (S → R)) = lim_S (S × Spec R) = T × Spec R` over the
discrete quotients `S` of `T`, but is proved directly. -/
noncomputable def homeomorphPrimeSpectrum :
    T × PrimeSpectrum R ≃ₜ PrimeSpectrum (LocallyConstant T R) :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective _ ⟨toPrimeSpectrum_injective, toPrimeSpectrum_surjective⟩)
    continuous_toPrimeSpectrum isOpenMap_toPrimeSpectrum

@[simp]
lemma homeomorphPrimeSpectrum_apply (tp : T × PrimeSpectrum R) :
    homeomorphPrimeSpectrum tp = toPrimeSpectrum tp :=
  rfl

lemma homeomorphPrimeSpectrum_symm_snd (P : PrimeSpectrum (LocallyConstant T R)) :
    ((homeomorphPrimeSpectrum (T := T) (R := R)).symm P).2 =
      PrimeSpectrum.comap (algebraMap R (LocallyConstant T R)) P := by
  conv_rhs => rw [← (homeomorphPrimeSpectrum (T := T) (R := R)).apply_symm_apply P]
  rw [homeomorphPrimeSpectrum_apply, comap_algebraMap_toPrimeSpectrum]

end Profinite

/-!
### `LocallyConstant T R` is ind-Zariski over `R`

The ring of locally constant functions is the filtered colimit of the algebras
`LocallyConstant S R ≃ (S → R)` of functions on the (finite) discrete quotients `S`
of `T`. Since finite products of copies of `R` are ind-Zariski over `R`, so is the
colimit.
-/

section IndZariski

open CategoryTheory CategoryTheory.Limits

/-- For a discrete space, locally constant functions are just functions. -/
@[simps]
def algEquivPi (R : Type*) [CommRing R] (S : Type*) [TopologicalSpace S]
    [DiscreteTopology S] :
    LocallyConstant S R ≃ₐ[R] (S → R) where
  toFun f := ⇑f
  invFun g := ⟨g, IsLocallyConstant.of_discrete g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (R : Type u) [CommRing R] (T : Type u) [TopologicalSpace T] [CompactSpace T]

/-- The filtered diagram of the algebras of functions on the (finite) discrete
quotients of `T`. -/
@[simps]
noncomputable def discreteQuotientDiag : (DiscreteQuotient T)ᵒᵖ ⥤ CommAlgCat R where
  obj S := .of R (LocallyConstant S.unop R)
  map {S S'} h := CommAlgCat.ofHom <| comapₐ R
    ⟨DiscreteQuotient.ofLE h.unop.le, DiscreteQuotient.ofLE_continuous h.unop.le⟩
  map_id S := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro f
    ext x
    exact congrArg f (DiscreteQuotient.ofLE_refl_apply x)
  map_comp {S S' S''} h h' := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro f
    ext x
    exact congrArg f (DiscreteQuotient.ofLE_ofLE h'.unop.le h.unop.le x).symm

/-- The cocone over `discreteQuotientDiag` with apex `LocallyConstant T R`, given by
pulling back functions along the quotient projections. -/
@[simps]
noncomputable def discreteQuotientCocone : Cocone (discreteQuotientDiag R T) where
  pt := .of R (LocallyConstant T R)
  ι :=
    { app S := CommAlgCat.ofHom <| comapₐ R ⟨S.unop.proj, S.unop.proj_continuous⟩
      naturality {S S'} h := by
        dsimp only [discreteQuotientDiag]
        apply CommAlgCat.hom_ext
        apply AlgHom.ext
        intro f
        apply LocallyConstant.ext
        intro t
        exact congrArg (fun x ↦ f x) (DiscreteQuotient.ofLE_proj h.unop.le t) }

/-- The cocone `discreteQuotientCocone` is colimiting: every locally constant function
factors through a discrete quotient, and two functions on quotients agreeing on `T`
agree on a common refinement. -/
noncomputable def isColimitDiscreteQuotientCocone :
    IsColimit (discreteQuotientCocone R T) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient T)ᵒᵖ (forget (CommAlgCat R)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget (CommAlgCat R))
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro f
    refine ⟨Opposite.op f.discreteQuotient, f.lift, ?_⟩
    change f = comapₐ R ⟨f.discreteQuotient.proj, f.discreteQuotient.proj_continuous⟩ f.lift
    apply LocallyConstant.ext
    intro t
    exact (congrFun f.lift_comp_proj t).symm
  · intro S g₁ g₂ h
    refine ⟨S, 𝟙 S, ?_⟩
    suffices hg : g₁ = g₂ by rw [hg]
    refine comap_injective ⟨S.unop.proj, S.unop.proj_continuous⟩ S.unop.proj_surjective ?_
    exact h

/-- `LocallyConstant T R` as the filtered colimit of the algebras of functions on the
discrete quotients of `T`. -/
noncomputable def discreteQuotientColimitPresentation :
    ColimitPresentation (DiscreteQuotient T)ᵒᵖ (CommAlgCat.of R (LocallyConstant T R)) where
  diag := discreteQuotientDiag R T
  ι := (discreteQuotientCocone R T).ι
  isColimit := isColimitDiscreteQuotientCocone R T

instance (S : DiscreteQuotient T) : Algebra.IndZariski R (LocallyConstant S R) :=
  Algebra.IndZariski.of_equiv (R := R) (S := (S → R)) (T := LocallyConstant S R)
    (algEquivPi R S).symm

/-- The ring of locally constant functions on a compact space is ind-Zariski. This is
the algebra `A^S` of Stacks 097D (for `S = T` profinite), obtained as the filtered
colimit of the finite products `S → R` over the discrete quotients `S` of `T`. -/
instance instIndZariski : Algebra.IndZariski R (LocallyConstant T R) :=
  Algebra.IndZariski.of_colimitPresentation (R := R) (S := LocallyConstant T R)
    (discreteQuotientColimitPresentation R T) fun S ↦
    inferInstanceAs (Algebra.IndZariski R (LocallyConstant S.unop R))

end IndZariski

end LocallyConstant
