/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.Ideal

/-!
# General results on ring homomorphisms and localization

In this file we show:

- A ring homomorphism is injective if all stalk maps are injective and for every maximal
  ideal of `R`, there exists a prime of `S` mapping to it.
- A ring homomorphism is flat if the induced maps on localizations at each maximal ideal
  are flat.
- A ring homomorphism is surjective if and only if for every element and every maximal ideal,
  there exists an element outside the maximal ideal whose product with the given element
  is in the range.
-/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism is injective if all stalk maps at maximal ideals are injective and
`PrimeSpectrum.comap f` is surjective. -/
lemma RingHom.injective_of_injectiveOnStalks {f : R →+* S}
    (hf : ∀ (p : Ideal S) [p.IsMaximal],
        Function.Injective (Localization.localRingHom (p.comap f) p f rfl))
    (hb : Function.Surjective (PrimeSpectrum.comap f)) : Function.Injective f := by
  intro r₁ r₂ hr
  apply MaximalSpectrum.toPiLocalization_injective R
  ext ⟨q, hq⟩
  obtain ⟨⟨p, hp⟩, hpq⟩ := hb ⟨q, hq.isPrime⟩
  have hpq' : p.comap f = q := congr_arg PrimeSpectrum.asIdeal hpq
  obtain ⟨m, hm, hpm⟩ := p.exists_le_maximal hp.ne_top
  have hmcomap : m.comap f = q :=
    (hq.eq_of_le (Ideal.comap_ne_top f hm.ne_top)
      (hpq' ▸ Ideal.comap_mono hpm)).symm
  subst hmcomap
  haveI := hm
  apply hf m
  simp only [MaximalSpectrum.toPiLocalization, Pi.algebraMap_apply,
    Localization.localRingHom_to_map, hr]

/-- A ring homomorphism `f : R →+* S` is flat if the induced maps on localizations at each
maximal ideal are flat. -/
lemma RingHom.flat_of_localizations_flat {f : R →+* S}
    (h : ∀ (p : Ideal S) [p.IsMaximal],
        (Localization.localRingHom (p.comap f) p f rfl).Flat) :
    f.Flat := by
  algebraize [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap S _)
  intro P hPmax
  haveI : P.IsMaximal := hPmax
  algebraize [Localization.localRingHom (Ideal.comap f P) P f rfl]
  haveI : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  haveI : Module.Flat (Localization.AtPrime (Ideal.comap f P))
      (Localization.AtPrime P) := h P
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)

/-- A ring homomorphism `f : R →+* S` is surjective if for every `s : S` and every maximal
ideal `m` of `R`, there exists `r ∉ m` such that `f r * s ∈ f.range`. -/
lemma RingHom.surjective_of_forall_isMaximal_exists {f : R →+* S}
    (h : ∀ (s : S) (m : Ideal R), m.IsMaximal → ∃ r : R, r ∉ m ∧ f r * s ∈ f.range) :
    Function.Surjective f := by
  intro s
  by_contra hs
  have h1 : ¬(f 1 * s ∈ f.range) := by simpa only [map_one, one_mul]
  set J_s : Ideal R := {
    carrier := {r : R | f r * s ∈ f.range}
    add_mem' := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by rw [map_add, map_add, add_mul, hx, hy]⟩
    zero_mem' := ⟨0, by simp⟩
    smul_mem' := fun c _ ⟨x, hx⟩ ↦
      ⟨c * x, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hx]⟩
  }
  have hJ_ne_top : J_s ≠ ⊤ := fun heq ↦ h1 ((heq ▸ Submodule.mem_top : (1 : R) ∈ J_s))
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J_s hJ_ne_top
  obtain ⟨r, hrm, hr_range⟩ := h s m hm
  exact hrm (hJm hr_range)

/-- Converse of `RingHom.surjective_of_forall_isMaximal_exists`. -/
lemma RingHom.exists_mul_mem_range_of_surjective {f : R →+* S}
    (hf : Function.Surjective f) (s : S) (m : Ideal R) (hm : m.IsMaximal) :
    ∃ r : R, r ∉ m ∧ f r * s ∈ f.range := by
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨1, (Ideal.ne_top_iff_one m).mp hm.ne_top, r, by simp⟩
