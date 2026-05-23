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

/-- `Algebra.IndEtale` in terms of `MorphismProperty.ind` on the underlying ring map. -/
private lemma iff_ind_etale_algebraMap :
    Algebra.IndEtale R S ↔
      MorphismProperty.ind.{u} CommRingCat.etale (CommRingCat.ofHom (algebraMap R S)) := by
  rw [iff_ind_etale, CommAlgCat.etale_eq, CommRingCat.etale,
    RingHom.Etale.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]

/-- If `R → S` is ind-étale and `S → A` is étale, then `R → A` is ind-étale.

The proof descends the étale map `S → A` to a finite level via `PreIndSpreads`, then forms
pushouts along the filtered colimit diagram for `S` to recover `A` as a filtered colimit of
étale `R`-algebras. -/
private lemma of_indEtale_etale (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra.IndEtale R S] [Algebra.Etale S A] :
    Algebra.IndEtale R A := by
  rw [iff_ind_etale_algebraMap]
  obtain ⟨J, _, _, D, sR, tS, htS, hRS_data⟩ := (iff_ind_etale_algebraMap R S).mp ‹_›
  have hSA : CommRingCat.etale (CommRingCat.ofHom (algebraMap S A)) :=
    RingHom.etale_algebraMap.mpr ‹_›
  obtain ⟨j₀, T', f', g, hpush, hf'⟩ :=
    CommRingCat.etale.exists_isPushout_of_isFiltered htS
      (CommRingCat.ofHom (algebraMap S A)) hSA
  let D' : Under j₀ ⥤ CommRingCat.{u} :=
    (Under.post D ⋙ Under.pushout f') ⋙ Under.forget _
  let c'₀ : Cocone D' :=
    (Under.pushout f' ⋙ Under.forget _).mapCocone ((Cocone.mk _ tS).underPost j₀)
  let c' : Cocone D' := c'₀.extend hpush.isoPushout.inv
  let hc' : IsColimit c' :=
    IsColimit.extendIso _ (isColimitOfPreserves _ (htS.underPost j₀))
  let s' : (Functor.const (Under j₀)).obj (CommRingCat.of R) ⟶ D' :=
    { app k := sR.app k.right ≫ pushout.inl (D.map k.hom) f'
      naturality k l a := by
        have hnat := sR.naturality a.right
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hnat
        change 𝟙 _ ≫ sR.app l.right ≫ pushout.inl (D.map l.hom) f' =
          (sR.app k.right ≫ pushout.inl (D.map k.hom) f') ≫ _
        rw [Category.id_comp, Category.assoc]
        dsimp [D', Under.post, Under.pushout]
        rw [pushout.inl_desc, ← Category.assoc, ← hnat] }
  refine ⟨Under j₀, inferInstance, inferInstance, D', s', c'.ι, hc', fun k ↦ ⟨?_, ?_⟩⟩
  · exact CommRingCat.etale.comp_mem _ _ (hRS_data k.right).1
      (CommRingCat.etale.pushout_inl _ _ hf')
  · have hkey : pushout.inl (D.map k.hom) f' ≫ c'₀.ι.app k =
        tS.app k.right ≫ pushout.inl ((Cocone.mk (CommRingCat.of S) tS).ι.app j₀) f' := by
      dsimp only [c'₀, Functor.mapCocone_ι_app, Cocone.underPost_ι_app, Functor.comp_map,
        Under.forget_map, Under.pushout_map, Under.post_obj, Under.mk_hom, Under.homMk_right,
        Cocone.underPost_pt]
      exact pushout.inl_desc _ _ _
    have hcomp : pushout.inl (D.map k.hom) f' ≫ c'.ι.app k =
        tS.app k.right ≫ CommRingCat.ofHom (algebraMap S A) := by
      change pushout.inl (D.map k.hom) f' ≫ c'₀.ι.app k ≫ hpush.isoPushout.inv = _
      rw [← Category.assoc, hkey, Category.assoc, hpush.inl_isoPushout_inv]
    change (sR.app k.right ≫ pushout.inl (D.map k.hom) f') ≫ c'.ι.app k =
      CommRingCat.ofHom (algebraMap R A)
    rw [Category.assoc, hcomp, ← Category.assoc, (hRS_data k.right).2]
    ext x
    exact (IsScalarTower.algebraMap_apply R S A x).symm

lemma trans (T : Type u) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IndEtale R S] [Algebra.IndEtale S T] :
    Algebra.IndEtale R T := by
  rw [iff_ind_etale_algebraMap]
  obtain ⟨J, hJ, hFilt, D, s₂, t₂, ht₂, hst₂⟩ := (iff_ind_etale_algebraMap S T).mp ‹_›
  have hIndEtale_j : ∀ j, MorphismProperty.ind.{u} CommRingCat.etale
      (CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j) := fun j ↦ by
    letI : Algebra S (D.obj j) := (s₂.app j).hom.toAlgebra
    letI : Algebra R (D.obj j) :=
      ((CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j).hom).toAlgebra
    haveI : IsScalarTower R S (D.obj j) := .of_algebraMap_eq' rfl
    haveI : Algebra.Etale S (D.obj j) := RingHom.etale_algebraMap.mp (hst₂ j).1
    exact (iff_ind_etale_algebraMap R (D.obj j)).mp (of_indEtale_etale R S (D.obj j))
  rw [← MorphismProperty.ind_ind CommRingCat.etale_le_isFinitelyPresentable.{u}]
  refine ⟨J, hJ, hFilt, D,
    (Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂,
    t₂, ht₂, fun j ↦ ⟨hIndEtale_j j, ?_⟩⟩
  simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app, Category.assoc]
  ext x
  change (t₂.app j).hom ((s₂.app j).hom ((algebraMap R S) x)) = (algebraMap R T) x
  have h := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp (hst₂ j).2) ((algebraMap R S) x)
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  exact (IsScalarTower.algebraMap_apply R S T x).symm

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
  algebraize [f, g, (g.comp f)]
  exact Algebra.IndEtale.trans R S T

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
