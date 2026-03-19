/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Flat
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.Ind
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits

/-!
# Ind-Zariski algebras and ring homomorphisms

In this file we define ind-Zariski algebras.
-/
universe u

open CategoryTheory Limits

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

section Algebra

variable [Algebra R S] [Algebra R T]

/-- The object property on commutative `R`-algebras of being a local isomorphism. -/
def CommAlgCat.isLocalIso : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.IsLocalIso R S

lemma CommAlgCat.isLocalIso_eq : isLocalIso R = RingHom.toObjectProperty RingHom.IsLocalIso R := by
  ext S
  exact RingHom.isLocalIso_algebraMap.symm

instance : (CommAlgCat.isLocalIso R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.isLocalIso_eq]
  exact RingHom.IsLocalIso.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

private instance isClosedUnderLimitsOfShape_isLocalIso_aux (ι : Type u) [Finite ι] :
    (CommAlgCat.isLocalIso R).IsClosedUnderLimitsOfShape (Discrete ι) := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  let S : ι → CommAlgCat.{u} R := fun i ↦ F.obj ⟨i⟩
  let natIso : F ≅ Discrete.functor S := Discrete.natIso (fun i ↦ Iso.refl _)
  let isoPi : (CommAlgCat.piFan S).pt ≅ limit (Discrete.functor S) :=
    (limit.isoLimitCone ⟨CommAlgCat.piFan S, CommAlgCat.isLimitPiFan S⟩).symm
  let isoLim : limit (Discrete.functor S) ≅ limit F :=
    (HasLimit.isoOfNatIso natIso).symm
  apply (CommAlgCat.isLocalIso R).prop_of_iso (isoPi ≪≫ isoLim)
  have inst (i : ι) : Algebra.IsLocalIso R (S i) := hF ⟨i⟩
  exact Algebra.IsLocalIso.pi_of_finite R (fun i ↦ S i)

instance (ι : Type*) [Finite ι] :
    (CommAlgCat.isLocalIso R).IsClosedUnderLimitsOfShape (Discrete ι) := by
  have : Small.{u} ι := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact ⟨⟨ULift.{u} (Fin n), ⟨e.trans Equiv.ulift.symm⟩⟩⟩
  have : Finite (Shrink.{u} ι) := Finite.of_equiv ι (equivShrink ι)
  exact .of_equivalence (Discrete.equivalence (equivShrink.{u} ι).symm)

/-- An algebra is ind-Zariski if it can be written as the filtered colimit of locally isomorphic
algebras. -/
@[stacks 096N, mk_iff]
class Algebra.IndZariski (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.IsLocalIso R (P.diag.obj i)

namespace Algebra.IndZariski

lemma iff_ind_isLocalIso :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (.of R S) :=
  Algebra.indZariski_iff R S

lemma of_equiv (e : S ≃ₐ[R] T) [IndZariski R S] : IndZariski R T := by
  rwa [iff_ind_isLocalIso, (CommAlgCat.isLocalIso R).ind.prop_iff_of_iso (CommAlgCat.isoMk e.symm),
    ← iff_ind_isLocalIso]

lemma trans [Algebra S T] [IsScalarTower R S T] [Algebra.IndZariski R S] [Algebra.IndZariski S T] :
    Algebra.IndZariski R T :=
  sorry

instance pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.IndZariski R (S i)] : Algebra.IndZariski R (∀ i, S i) := by
  rw [iff_ind_isLocalIso]
  apply ObjectProperty.LimitOfShape.prop (J := Discrete ι)
  refine ⟨⟨Discrete.functor fun i ↦ .of R (S i),
      Discrete.natTrans fun i ↦ CommAlgCat.ofHom (Pi.evalAlgHom _ _ _), ?_⟩, ?_⟩
  · exact CommAlgCat.isLimitPiFan fun i ↦ .of R (S i)
  · intro j
    dsimp
    rw [← iff_ind_isLocalIso]
    infer_instance

private def prod_B (S T : Type u) : ULift.{u} Bool → Type u := fun i ↦ Bool.rec T S i.down

private noncomputable instance prod_instCR (S T : Type u) [CommRing S] [CommRing T] :
    ∀ i, CommRing (prod_B S T i) := fun ⟨b⟩ ↦
  Bool.rec (inferInstanceAs (CommRing T)) (inferInstanceAs (CommRing S)) b

private noncomputable instance prod_instAlg (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : ∀ i, Algebra R (prod_B S T i) := fun ⟨b⟩ ↦
  Bool.rec (inferInstanceAs (Algebra R T)) (inferInstanceAs (Algebra R S)) b

private noncomputable instance prod_instIZ (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IndZariski R S] [IndZariski R T] :
    ∀ i, IndZariski R (prod_B S T i) := fun ⟨b⟩ ↦
  Bool.rec (inferInstanceAs (IndZariski R T)) (inferInstanceAs (IndZariski R S)) b

private noncomputable def prod_equiv (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : (∀ i, prod_B S T i) ≃ₐ[R] S × T where
  toFun f := (f ⟨true⟩, f ⟨false⟩)
  invFun p := fun ⟨b⟩ ↦ @Bool.rec (fun b ↦ prod_B S T ⟨b⟩) p.2 p.1 b
  left_inv f := by
    ext ⟨b⟩
    cases b <;> rfl
  right_inv p := by obtain ⟨_, _⟩ := p; rfl
  map_mul' _ _ := Prod.ext rfl rfl
  map_add' _ _ := Prod.ext rfl rfl
  commutes' _ := Prod.ext rfl rfl

/-- The product of two ind-Zariski algebras is ind-Zariski. -/
instance prod [Algebra.IndZariski R S] [Algebra.IndZariski R T] :
    Algebra.IndZariski R (S × T) :=
  of_equiv (R := R) (S := ∀ i, prod_B S T i) (T := S × T) (prod_equiv R S T)

instance function {ι : Type u} [_root_.Finite ι] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.IndZariski R S] : Algebra.IndZariski R (ι → S) :=
  pi R (fun _ ↦ S)

variable {R}

instance (priority := 100) of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ObjectProperty.le_ind _ _ ‹_›

instance refl : Algebra.IndZariski R R :=
  Algebra.IndZariski.of_isLocalIso _

lemma of_isLocalization (M : Submonoid R) [IsLocalization M S] : Algebra.IndZariski R S :=
  sorry

instance localization (M : Submonoid R) : Algebra.IndZariski R (Localization M) :=
  of_isLocalization _ M

variable (R)

/-- A local isomorphism `R → X` is flat, since it is locally a localization. -/
private lemma isLocalIso_implies_flat {R : Type u} [CommRing R] (X : CommAlgCat.{u} R)
    (hX : Algebra.IsLocalIso R X) : Module.Flat R X := by
  have hflat : RingHom.Flat (algebraMap R X) :=
    RingHom.Flat.ofLocalizationSpanTarget (algebraMap R X)
      {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)} (by
        by_contra hne
        obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
        obtain ⟨g, hgm, hstd⟩ := hX.exists_notMem_isStandardOpenImmersion m
        exact hgm (hms (Ideal.subset_span hstd)))
      (fun ⟨g, hg⟩ ↦ by
        obtain ⟨r, hr⟩ := hg.exists_away
        have : (algebraMap X (Localization.Away g)).comp (algebraMap R X) =
            algebraMap R (Localization.Away g) := by
          ext x
          simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R X]
        rw [this]
        exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r)))
  exact RingHom.flat_algebraMap_iff.mp hflat

instance (priority := 100) _root_.Module.Flat.of_indZariski [Algebra.IndZariski R S] :
    Module.Flat R S := by
  rw [Module.Flat.iff_ind_flat]
  obtain ⟨J, _, _, pres, h⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  exact ⟨J, inferInstance, inferInstance, pres, fun i ↦ by
    rw [CommAlgCat.flat_iff]
    exact isLocalIso_implies_flat (pres.diag.obj i) (h i)⟩

@[stacks 096T]
theorem bijectiveOnStalks_algebraMap [Algebra.IndZariski R S] :
    (algebraMap R S).BijectiveOnStalks :=
  sorry

theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := sorry

end Algebra.IndZariski

end Algebra

section RingHom

/-- A ring hom is ind-Zariski if and only if it is an ind-Zariski algebra. -/
@[stacks 096N, algebraize Algebra.IndZariski]
def RingHom.IndZariski {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndZariski R S

namespace RingHom.IndZariski

lemma algebraMap_iff [Algebra R S] :
    (algebraMap R S).IndZariski ↔ Algebra.IndZariski R S:=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

variable {R S T}

lemma iff_ind_isLocalIso (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) (CommRingCat.ofHom f) := by
  algebraize [f]
  simp only [RingHom.IndZariski, Algebra.IndZariski.iff_ind_isLocalIso, ← f.algebraMap_toAlgebra,
    RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.isLocalIso_eq]

/-- A ring hom is ind-Zariski if and only if it can be written
as a colimit of local isomorphisms. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndZariski ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S)
      (_ : IsColimit (.mk _ c)), ∀ i, (t.app i).hom.IsLocalIso ∧ t.app i ≫ c.app i = f :=
  RingHom.IndZariski.iff_ind_isLocalIso _

lemma id : (RingHom.id R).IndZariski :=
  Algebra.IndZariski.refl

variable {f : R →+* S} {g : S →+* T}

lemma comp (hg : g.IndZariski) (hf : f.IndZariski) : (g.comp f).IndZariski := by
  algebraize [f, g, g.comp f]
  exact Algebra.IndZariski.trans R S T

lemma prod {g : R →+* T} (hf : f.IndZariski) (hg : g.IndZariski) : (f.prod g).IndZariski := by
  algebraize [f, g]
  exact Algebra.IndZariski.prod R S T

lemma pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* (S i)) (hf : ∀ i, (f i).IndZariski) : (Pi.ringHom f).IndZariski := by
  let (i : ι) : Algebra R (S i) := (f i).toAlgebra
  have (i : ι) : Algebra.IndZariski R (S i) := hf i
  exact Algebra.IndZariski.pi R S

lemma flat (h : f.IndZariski) : f.Flat := by
  algebraize [f]
  exact .of_indZariski R S

@[stacks 096T]
theorem bijectiveOnStalks (h : f.IndZariski) : f.BijectiveOnStalks := by
  algebraize [f]
  exact Algebra.IndZariski.bijectiveOnStalks_algebraMap R S

/-- Ind-Zariski is equivalent to ind-ind-Zariski. -/
lemma iff_ind_indZariski (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndZariski) (CommRingCat.ofHom f) := by
  algebraize [f]
  sorry

/-- A ring hom is ind-Zariski if it can be written as a filtered colimit of ind-Zariski maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndZariski ∧ t.app i ≫ c.app i = f) : f.hom.IndZariski :=
  (iff_ind_indZariski _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

theorem _root_.Algebra.IndZariski.iff_ind_indZariksi [Algebra R S] :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndZariski R) (.of R S) := by
  sorry

end RingHom.IndZariski

end RingHom
