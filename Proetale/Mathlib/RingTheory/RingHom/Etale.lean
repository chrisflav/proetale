/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Etale

/-!
# Étale ring homomorphisms cancel from the left

We show `RingHom.Etale.of_comp`: if `f : R →+* S` and `g ∘ f : R →+* T` are étale, then so
is `g : S →+* T`.
-/

namespace RingHom

/-- Étale ring maps cancel from the left: if `f : R →+* S` and `g ∘ f : R →+* T` are
étale, then so is `g : S →+* T`. -/
lemma Etale.of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.Etale) (hgf : (g.comp f).Etale) :
    g.Etale := by
  have hfp : g.FinitePresentation :=
    FinitePresentation.of_comp_finiteType f
      (Etale.iff_flat_and_formallyUnramified.mp hgf).2.2
      (FiniteType.of_finitePresentation (Etale.iff_flat_and_formallyUnramified.mp hf).2.2)
  algebraize [f, g, g.comp f]
  exact ⟨Algebra.FormallyEtale.of_restrictScalars (R := R), hfp⟩

end RingHom
