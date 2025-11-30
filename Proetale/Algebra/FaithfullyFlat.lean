/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Proetale.Algebra.Ind

/-!
# Ind-(faithfully flat) is faithfully flat

-/

universe u v w

open CategoryTheory Limits

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} [CommRing S]

namespace Flat

-- `Do we need SmallCategory here?`
/-- A module is flat if it can be written as a filtered colimit of flat modules. -/
theorem of_colimitPresentation {ι : Type w} [Category ι] [IsFiltered ι]
    (P : ColimitPresentation ι (ModuleCat.of R M))
    (h : ∀ (i : ι), Module.Flat R (P.diag.obj i)) : Module.Flat R M := sorry

-- `Can we define ObjectPropert use Algebra/Module version instead of RingHom version?`
-- (RingHom not so compatible with the current setup since RingHom.toAlgebra is bad.
-- See IndZariski case.)
-- `Module.toObjectProperty` ?
/-- Flat is equivalent to ind-flat. -/
theorem iff_ind_flat [Algebra R S]: Module.Flat R S ↔ ObjectProperty.ind.{u}
    (RingHom.toObjectProperty RingHom.Flat R) (.of R S) := by
  sorry

end Flat

namespace FaithfullyFlat

-- `Do we need SmallCategory here?`
theorem of_colimitPresentation {ι : Type w} [Category ι] [IsFiltered ι]
    (P : ColimitPresentation ι (ModuleCat.of R M))
    (h : ∀ (i : ι), Module.FaithfullyFlat R (P.diag.obj i)) : Module.FaithfullyFlat R M := sorry

theorem iff_ind_faithfullyFlat [Algebra R S] : Module.FaithfullyFlat R S ↔ ObjectProperty.ind.{u}
    (RingHom.toObjectProperty RingHom.FaithfullyFlat R) (.of R S) := by
  sorry

end FaithfullyFlat

end Module

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

namespace Flat

/-- Flat is equivalent to ind-flat. -/
lemma iff_ind_flat (f : R →+* S) :
    f.Flat ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.Flat) (CommRingCat.ofHom f) := by
  algebraize [f]
  sorry

/-- A ring map is flat if it can be written as a filtered colimit of flat ring maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.Flat ∧ t.app i ≫ c.app i = f) : f.hom.Flat :=
  (iff_ind_flat _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

end Flat

namespace FaithfullyFlat

/-- Faithfully flat is equivalent to ind-(faithfully flat). -/
lemma iff_ind_faithfullyFlat (f : R →+* S) :
    f.FaithfullyFlat ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.FaithfullyFlat) (CommRingCat.ofHom f) := by
  algebraize [f]
  sorry

/-- A ring hom is faithfully flat if it can be written as a colimit of faithfully flat ring maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.FaithfullyFlat ∧ t.app i ≫ c.app i = f) : f.hom.FaithfullyFlat :=
  (iff_ind_faithfullyFlat _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

end FaithfullyFlat

end RingHom
