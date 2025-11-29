/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib

/-!
# Weakly contractible objects

In a (pre)topos, a weakly contractible object is an object `F` such that every epimorphism
`p : G ⟶ F` splits. In a (pre)topos, this is equivalent to being a projective object.
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C]

instance {X P : C} [Projective P] (f : X ⟶ P) [Epi f] : IsSplitEpi f :=
  ⟨⟨⟨Projective.factorThru (𝟙 P) f, by simp⟩⟩⟩

/-- If `C` has pullbacks and epimorphisms are stable under pullbacks, `P` is projective
if and only if every epimorphism to `P` splits.
The conditions hold for example in abelian categories and pretopoi. -/
lemma Projective.iff_forall_isSplitEpi_of_hasPullbacks [HasPullbacks C]
    (H : ∀ {X E S : C} (f : X ⟶ S) (e : E ⟶ S), Epi e → Epi (pullback.fst f e)) (P : C) :
    Projective P ↔ ∀ {X : C} (f : X ⟶ P), Epi f → IsSplitEpi f := by
  refine ⟨fun hP X f hf ↦ inferInstance, fun h ↦ ⟨fun {E X} f e he ↦ ?_⟩⟩
  obtain ⟨a, ha⟩ := h (pullback.fst f e) (H f e he)
  use a ≫ pullback.snd f e
  simp [← pullback.condition, reassoc_of% ha]

/-- An object `P` is weakly contractible if it is projective. -/
class abbrev WeaklyContractible (P : C) := Projective P

/-- If `C` has enough projectives, being an epimorphism can be detected on sections over
projective objects. -/
lemma EnoughProjectives.epi_iff_forall_projective [EnoughProjectives C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ (P : C), Projective P → Function.Surjective ((coyoneda.obj (op P)).map f) := by
  refine ⟨fun hf P hP ↦ ?_, fun H ↦ ?_⟩
  · exact (epi_iff_surjective _).mp <|
      (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj P).mp hP |>.1 f
  · obtain ⟨(g : Projective.over Y ⟶ X), (hg : g ≫ f = _)⟩ :=
      H (Projective.over Y) inferInstance (Projective.π Y)
    exact epi_of_epi_fac hg

end CategoryTheory
