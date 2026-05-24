/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RingHom.Etale
import Proetale.Algebra.IndZariski
import Proetale.Algebra.Etale

/-!
# Ind-étale algebras

In this file we define ind-étale algebras and ring homomorphisms.
-/

universe u

open CategoryTheory Limits

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The object property on commutative `R`-algebras of being étale. -/
def CommAlgCat.etale : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.Etale R S

lemma CommAlgCat.etale_eq : etale R = RingHom.toObjectProperty RingHom.Etale R := by
  ext S
  exact RingHom.etale_algebraMap.symm

instance : (MorphismProperty.ind.{u} CommRingCat.etale.{u}).IsStableUnderComposition :=
  .ind_of_le_isFinitelyPresentable CommRingCat.etale_le_isFinitelyPresentable.{u}

/-- An algebra is ind-étale if it can be written as the filtered colimit of étale
algebras. -/
@[mk_iff]
class Algebra.IndEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.Etale R (P.diag.obj i)

namespace Algebra.IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma iff_ind_etale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u} (CommAlgCat.etale R) (.of R S) :=
  Algebra.indEtale_iff R S

/-- Étale `R`-algebras are finitely presented. -/
lemma etale_le_finitePresentation :
    CommAlgCat.etale R ≤ CommAlgCat.finitePresentation R := by
  intro S hS
  exact (RingHom.etale_algebraMap.mpr hS).2

/-- If every stage of a filtered colimit presentation of `S` over `R` is ind-étale,
then `S` is ind-étale over `R`. -/
theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndEtale R (P.diag.obj i)) : Algebra.IndEtale R S := by
  rw [iff_ind_etale, ← ObjectProperty.ind_ind (etale_le_finitePresentation R |>.trans
    (CommAlgCat.finitePresentation_le_isFinitelyPresentable R))]
  exact ⟨ι, ‹_›, ‹_›, P, fun i => (iff_ind_etale R _).mp (h i)⟩

lemma isLocalIso_le_etale (R : Type u) [CommRing R] :
    CommAlgCat.isLocalIso R ≤ CommAlgCat.etale R := fun X hX ↦
  have : Algebra.IsLocalIso R X := hX
  Algebra.IsLocalIso.etale R X

/-- An ind-Zariski algebra is ind-étale, since localizations are étale. -/
instance (priority := 100) of_indZariski [IndZariski R S] : IndEtale R S := by
  rw [iff_ind_etale]
  refine ObjectProperty.ind_mono (isLocalIso_le_etale R) _ ?_
  rwa [← Algebra.IndZariski.iff_ind_isLocalIso]

instance isSeparable (k : Type u) [Field k] [Algebra k R] [IndEtale k R] [IsLocalRing R] :
    Algebra.IsSeparable k R := by
  sorry

instance isSeparable_residueField [Algebra.IndEtale R S] (p : Ideal R) (q : Ideal S)
    [q.LiesOver p] [p.IsPrime] [q.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Algebra.IsSeparable p.ResidueField q.ResidueField :=
  sorry

end Algebra.IndEtale

/-- A ring hom is ind-étale if and only if it is an ind-étale algebra. -/
@[algebraize Algebra.IndEtale]
def RingHom.IndEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndEtale R S

namespace RingHom.IndEtale

variable (S) in
lemma algebraMap_iff : (algebraMap R S).IndEtale ↔ Algebra.IndEtale R S :=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

lemma iff_ind_etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u} CommRingCat.etale (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndEtale, Algebra.IndEtale.iff_ind_etale, ← f.algebraMap_toAlgebra,
    CommRingCat.etale, RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.etale_eq]

/-- A ring hom is ind-étale if and only if it can be written as a colimit of étale ring homs. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndEtale ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S) (_ : IsColimit (.mk _ c)),
      ∀ i, (t.app i).hom.Etale ∧ t.app i ≫ c.app i = f :=
  RingHom.IndEtale.iff_ind_etale _

variable {R S : Type u} [CommRing R] [CommRing S]

lemma comp {T : Type u} [CommRing T] {g : S →+* T} {f : R →+* S} (hg : g.IndEtale)
    (hf : f.IndEtale) : (g.comp f).IndEtale := by
  rw [iff_ind_etale] at hf hg ⊢
  rw [CommRingCat.ofHom_comp]
  exact (MorphismProperty.ind.{u} CommRingCat.etale).comp_mem _ _ hf hg

/-- Ind-étale ring homomorphisms are stable under base change. -/
lemma isStableUnderBaseChange : IsStableUnderBaseChange IndEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ hpush hRS
  rw [iff_ind_etale] at hRS ⊢
  rw [← CommRingCat.isPushout_iff_isPushout] at hpush
  exact (inferInstance : (MorphismProperty.ind CommRingCat.etale).IsStableUnderCobaseChange).1
    hpush.flip hRS

/-- Ind-étale is equivalent to ind-ind-étale. -/
lemma iff_ind_indEtale (f : R →+* S) :
    f.IndEtale ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndEtale) (CommRingCat.ofHom f) := by
  rw [iff_ind_etale]
  have heq : RingHom.toMorphismProperty RingHom.IndEtale =
      MorphismProperty.ind.{u} CommRingCat.etale := by
    ext X Y g
    exact iff_ind_etale g.hom
  rw [heq, MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable.{u}]

/-- A ring hom is ind-étale if it can be written as a filtered colimit of ind-étale maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndEtale ∧ t.app i ≫ c.app i = f) : f.hom.IndEtale :=
  (iff_ind_indEtale _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

/-- Ind-étale algebras are equivalent to ind-ind-étale algebras. -/
theorem _root_.Algebra.IndEtale.iff_ind_indEtale [Algebra R S] :
    Algebra.IndEtale R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndEtale R) (.of R S) :=
  have h := isStableUnderBaseChange.localizationPreserves.away.respectsIso
  (algebraMap_iff (R := R) S).symm.trans
    ((RingHom.IndEtale.iff_ind_indEtale _).trans
      h.ind_toMorphismProperty_iff_ind_toObjectProperty)

lemma _root_.RingHom.IndZariski.indEtale {f : R →+* S}
    (hf : f.IndZariski) : f.IndEtale := by
  algebraize [f]
  exact .of_indZariski R S

end RingHom.IndEtale

namespace Algebra.IndEtale

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T := by
  rw [← RingHom.IndEtale.algebraMap_iff R T, IsScalarTower.algebraMap_eq R S T]
  exact RingHom.IndEtale.comp
    ((RingHom.IndEtale.algebraMap_iff S T).mpr ‹_›)
    ((RingHom.IndEtale.algebraMap_iff R S).mpr ‹_›)

end Algebra.IndEtale
