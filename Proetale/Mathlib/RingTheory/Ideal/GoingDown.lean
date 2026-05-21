import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Topology.JacobsonSpace

-- after `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
theorem Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (h : closedPoints (PrimeSpectrum R) ⊆ Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  rintro ⟨p, hp⟩
  obtain ⟨m, hm, hle⟩  := Ideal.exists_le_maximal _ hp.ne_top
  have : ⟨m, hm.isPrime⟩ ∈ closedPoints (PrimeSpectrum R) := by
    rwa [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  obtain ⟨⟨n, _⟩, hn⟩ := h this
  have : n.LiesOver m := ⟨PrimeSpectrum.ext_iff.mp hn.symm⟩
  obtain ⟨q, _, hq, hpq⟩ := Ideal.exists_ideal_le_liesOver_of_le n hle
  use ⟨q, hq⟩, PrimeSpectrum.ext hpq.over.symm

/-- Stacks 00EA, (1) + (2)(a): if `R → S` has going down and there is at most one prime of
`S` above every prime of `R`, then for every prime `q` of `S` lying over `p`, the natural map
`S_{pS} → S_q` is an isomorphism, i.e. `Localization.AtPrime q` is the localization of `S` at
the image of `R \ p`. -/
theorem Algebra.HasGoingDown.isLocalization_atPrime_of_subsingleton {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (h : ∀ (p : Ideal R) [p.IsPrime], Subsingleton {q : Ideal S // q.IsPrime ∧ q.LiesOver p}) :
    IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q) := by
  set T : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  have hover : p = Ideal.under R q := Ideal.LiesOver.over
  have hTle : T ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩ hmem
    exact hr (hover ▸ (hmem : r ∈ Ideal.under R q))
  have key : ∀ t ∈ q.primeCompl, IsUnit (algebraMap S (Localization T) t) := by
    intro t ht
    rw [IsLocalization.algebraMap_isUnit_iff T]
    by_contra hno
    have hdisj : Disjoint ((Ideal.span {t} : Ideal S) : Set S) (T : Set S) := by
      rw [Set.disjoint_left]
      intro m hm hmT
      rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hm
      exact hno ⟨m, hmT, hm⟩
    obtain ⟨q', hq', htq', hdisj'⟩ :=
      Ideal.exists_le_prime_disjoint (Ideal.span {t}) T hdisj
    have : q'.IsPrime := hq'
    have : q'.LiesOver (Ideal.under R q') := ⟨rfl⟩
    have hle : Ideal.under R q' ≤ p := by
      intro r hr
      by_contra hrp
      rw [Ideal.under_def, Ideal.mem_comap] at hr
      exact Set.disjoint_left.mp hdisj' hr ⟨r, hrp, rfl⟩
    obtain ⟨P, hPq, hPprime, hPover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.under R q') (q := p) q hle
    have hPq' : P = q' := congrArg Subtype.val <| Subsingleton.elim
      (⟨P, hPprime, hPover⟩ : {q'' : Ideal S // q''.IsPrime ∧ q''.LiesOver (Ideal.under R q')})
      ⟨q', hq', ⟨rfl⟩⟩
    subst hPq'
    exact ht (hPq (htq' (Ideal.mem_span_singleton_self t)))
  have : IsLocalization q.primeCompl (Localization T) :=
    IsLocalization.of_le T q.primeCompl hTle key
  exact (IsLocalization.isLocalization_iff_of_algEquiv T
    (IsLocalization.algEquiv q.primeCompl (Localization T) (Localization.AtPrime q))).mp
    inferInstance
