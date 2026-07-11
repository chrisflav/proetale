/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Proetale.Mathlib.Algebra.Homology.DerivedCategoryPlus
import Proetale.Mathlib.AlgebraicGeometry.Sites.SmallBaseChange

/-!
# Derived pushforward on bounded below derived categories

For an additive functor `G : A ⥤ B` between abelian categories with enough injectives
we construct its total right derived functor on the bounded below derived categories

`G.rightDerivedPlus : DerivedCategoryPlus A ⥤ DerivedCategoryPlus B`

using the injective model structure on `CochainComplex.Plus A`
(`Mathlib.Algebra.Homology.ModelCategory.Injective`) and the Kahn–Maltsiniotis
derivability structure of fibrant objects: bounded below complexes of injectives are
K-injective, so quasi-isomorphisms between fibrant objects are homotopy equivalences,
which any additive functor inverts after localization
(`Functor.fibrantObject_derives_mapCochainComplexPlus`).

For an *exact* functor no derivation is necessary
(`Functor.mapDerivedCategoryPlus`).

We then specialize to the pushforward of abelian sheaves along a morphism of schemes
on small étale sites, and construct the **derived base change transformation**

`AlgebraicGeometry.Scheme.derivedBaseChangeNatTrans :
  Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*`

for a commutative square `g' ≫ f = f' ≫ g` of schemes, from the underived one
(`AlgebraicGeometry.Scheme.baseChangeNatTrans`) via the universal property of the
right derived functor. The proper base change theorem asserts that it is an
isomorphism on complexes with locally torsion cohomology when `f` is proper (see
`Proetale/Etale/ProperBaseChange.lean`).
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory

section General

variable {A : Type*} [Category* A] {B : Type*} [Category* B]

section MapComp

variable [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B]
  {E : Type*} [Category* E] [Limits.HasZeroMorphisms E]

/-- `Functor.mapCochainComplexPlus` is compatible with composition of functors. -/
def Functor.mapCochainComplexPlusComp (G : A ⥤ B) (H : B ⥤ E)
    [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms] :
    (G ⋙ H).mapCochainComplexPlus ≅
      G.mapCochainComplexPlus ⋙ H.mapCochainComplexPlus :=
  Iso.refl _

end MapComp

variable [Abelian A] [Abelian B]

open scoped CochainComplex.Plus.modelCategoryQuillen

section Derives

variable [EnoughInjectives A] [HasDerivedCategoryPlus.{w} B]

/-- Any additive functor, postcomposed with the localization to the bounded below
derived category, inverts quasi-isomorphisms between fibrant objects (= bounded below
complexes of injectives): such quasi-isomorphisms are homotopy equivalences because
bounded below complexes of injectives are K-injective. -/
lemma Functor.fibrantObject_derives_mapCochainComplexPlus (G : A ⥤ B) [G.Additive] :
    (FibrantObject.localizerMorphism (CochainComplex.Plus A)).Derives
      (G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B) := by
  intro X₁ Y₁ f hf
  -- The underlying complexes are bounded below complexes of injectives, hence
  -- K-injective.
  obtain ⟨dX, hdX⟩ := X₁.obj.2
  obtain ⟨dY, hdY⟩ := Y₁.obj.2
  haveI := hdX
  haveI := hdY
  haveI : ∀ n, Injective (X₁.obj.obj.X n) :=
    (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff _).mp X₁.2
  haveI : ∀ n, Injective (Y₁.obj.obj.X n) :=
    (CochainComplex.Plus.modelCategoryQuillen.isFibrant_iff _).mp Y₁.2
  haveI : X₁.obj.obj.IsKInjective := CochainComplex.isKInjective_of_injective _ dX
  haveI : Y₁.obj.obj.IsKInjective := CochainComplex.isKInjective_of_injective _ dY
  -- The weak equivalence `f` is a quasi-isomorphism of the underlying complexes,
  -- hence a homotopy equivalence.
  have hq : QuasiIso f.hom.hom := by
    rw [← CochainComplex.Plus.modelCategoryQuillen.weakEquivalence_iff]
    exact ⟨hf⟩
  rw [CochainComplex.IsKInjective.quasiIso_iff] at hq
  obtain ⟨e, he⟩ := hq
  -- Additive functors preserve homotopy equivalences, hence the image is again a
  -- quasi-isomorphism, which the localization functor inverts.
  refine Localization.inverts (DerivedCategoryPlus.Q B) (CochainComplex.Plus.quasiIso B)
    _ ?_
  have : HomologicalComplex.quasiIso B (ComplexShape.up ℤ)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom.hom) := by
    apply homotopyEquivalences_le_quasiIso
    exact ⟨G.mapHomotopyEquiv e, by rw [← he]; rfl⟩
  exact this

end Derives

section RightDerivedPlus

variable [EnoughInjectives A] [HasDerivedCategoryPlus.{w} A] [HasDerivedCategoryPlus.{w} B]

variable (G : A ⥤ B) [G.Additive]

instance : (G.mapCochainComplexPlus ⋙
    DerivedCategoryPlus.Q B).HasPointwiseRightDerivedFunctor
      (CochainComplex.Plus.quasiIso A) :=
  (G.fibrantObject_derives_mapCochainComplexPlus).hasPointwiseRightDerivedFunctor

/-- The total right derived functor of an additive functor between abelian categories
with enough injectives, on the bounded below derived categories. -/
noncomputable def Functor.rightDerivedPlus :
    DerivedCategoryPlus A ⥤ DerivedCategoryPlus B :=
  (G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B).totalRightDerived
    (DerivedCategoryPlus.Q A) (CochainComplex.Plus.quasiIso A)

/-- The unit of the total right derived functor. -/
noncomputable def Functor.rightDerivedPlusUnit :
    G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B ⟶
      DerivedCategoryPlus.Q A ⋙ G.rightDerivedPlus :=
  (G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B).totalRightDerivedUnit
    (DerivedCategoryPlus.Q A) (CochainComplex.Plus.quasiIso A)

instance : G.rightDerivedPlus.IsRightDerivedFunctor (G.rightDerivedPlusUnit)
    (CochainComplex.Plus.quasiIso A) := by
  dsimp [Functor.rightDerivedPlus, Functor.rightDerivedPlusUnit]
  infer_instance

/-- The unit of the total right derived functor is an isomorphism on bounded below
complexes of injectives. -/
lemma Functor.isIso_rightDerivedPlusUnit_app (X : FibrantObject (CochainComplex.Plus A)) :
    IsIso ((G.rightDerivedPlusUnit).app
      ((FibrantObject.localizerMorphism (CochainComplex.Plus A)).functor.obj X)) := by
  haveI : (DerivedCategoryPlus.Q A).IsLocalization
      (weakEquivalences (CochainComplex.Plus A)) :=
    inferInstanceAs ((DerivedCategoryPlus.Q A).IsLocalization
      (CochainComplex.Plus.quasiIso A))
  haveI : G.rightDerivedPlus.IsRightDerivedFunctor (G.rightDerivedPlusUnit)
      (weakEquivalences (CochainComplex.Plus A)) :=
    inferInstanceAs (G.rightDerivedPlus.IsRightDerivedFunctor (G.rightDerivedPlusUnit)
      (CochainComplex.Plus.quasiIso A))
  exact (G.fibrantObject_derives_mapCochainComplexPlus).isIso (G.rightDerivedPlusUnit) X

end RightDerivedPlus

section Exact

variable [HasDerivedCategoryPlus.{w} A] [HasDerivedCategoryPlus.{w} B]

variable (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategoryPlus A] in
/-- An exact functor preserves quasi-isomorphisms of bounded below complexes. -/
lemma Functor.mapCochainComplexPlus_inverts :
    (CochainComplex.Plus.quasiIso A).IsInvertedBy
      (G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B) := by
  intro K L f hf
  refine Localization.inverts (DerivedCategoryPlus.Q B) (CochainComplex.Plus.quasiIso B)
    _ ?_
  have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((CochainComplex.Plus.ι A).map f)) := by
    haveI : QuasiIso ((CochainComplex.Plus.ι A).map f) := hf
    infer_instance
  exact this

/-- The functor induced on bounded below derived categories by an exact functor. -/
noncomputable def Functor.mapDerivedCategoryPlus :
    DerivedCategoryPlus A ⥤ DerivedCategoryPlus B :=
  Localization.lift (G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B)
    (G.mapCochainComplexPlus_inverts) (DerivedCategoryPlus.Q A)

/-- The functor induced on bounded below derived categories by an exact functor
commutes with the localization functors. -/
noncomputable def Functor.mapDerivedCategoryPlusFactors :
    DerivedCategoryPlus.Q A ⋙ G.mapDerivedCategoryPlus ≅
      G.mapCochainComplexPlus ⋙ DerivedCategoryPlus.Q B :=
  Localization.fac _ (G.mapCochainComplexPlus_inverts) (DerivedCategoryPlus.Q A)

end Exact

end General

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory MorphismProperty

section DerivedPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The pushforward of abelian sheaves along a morphism of schemes, between the small
étale sites (with the `smallEtaleTopology`-spelled signature). -/
noncomputable abbrev etalePushforward :
    Sheaf X.smallEtaleTopology Ab.{u + 1} ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  smallPushforward f @Etale Ab.{u + 1}

/-- The pullback of abelian sheaves along a morphism of schemes, between the small
étale sites (with the `smallEtaleTopology`-spelled signature). -/
noncomputable abbrev etalePullback :
    Sheaf S.smallEtaleTopology Ab.{u + 1} ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  smallPullback f @Etale Ab.{u + 1}

instance : (etalePushforward f).Additive :=
  inferInstanceAs ((smallPushforward f @Etale Ab.{u + 1}).Additive)

instance : (etalePullback f).Additive :=
  inferInstanceAs ((smallPullback f @Etale Ab.{u + 1}).Additive)

instance : PreservesFiniteLimits (etalePullback f) :=
  inferInstanceAs (PreservesFiniteLimits (smallPullback f @Etale Ab.{u + 1}))

instance : PreservesFiniteColimits (etalePullback f) :=
  inferInstanceAs (PreservesFiniteColimits (smallPullback f @Etale Ab.{u + 1}))

variable [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]

/-- The derived pushforward of abelian sheaves along a morphism of schemes, on the
bounded below derived categories of the small étale sites. -/
noncomputable def derivedPushforward :
    DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}) ⥤
      DerivedCategoryPlus (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  (etalePushforward f).rightDerivedPlus

/-- The derived pullback of abelian sheaves along a morphism of schemes (no derivation
is necessary: the pullback is exact). -/
noncomputable def derivedPullback :
    DerivedCategoryPlus (Sheaf S.smallEtaleTopology Ab.{u + 1}) ⥤
      DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
  (etalePullback f).mapDerivedCategoryPlus

end DerivedPushforward

section DerivedBaseChange

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

open scoped CochainComplex.Plus.modelCategoryQuillen

/-- The base change transformation on abelian sheaves over the small étale sites, with
the `smallEtaleTopology`-spelled signature. -/
noncomputable abbrev etaleBaseChangeNatTrans :
    etalePushforward f ⋙ etalePullback g ⟶ etalePullback g' ⋙ etalePushforward f' :=
  baseChangeNatTrans f g f' g' w

/-- (Implementation) The canonical natural transformation exhibiting
`Rf_* ⋙ g^*` as a functor under `(f_* ⋙ g^*)` on complexes. -/
noncomputable def derivedBaseChangeUnitLeft :
    (etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus ⋙
        DerivedCategoryPlus.Q _ ⟶
      DerivedCategoryPlus.Q _ ⋙ (derivedPushforward f ⋙ derivedPullback g) :=
  Functor.whiskerRight (Functor.mapCochainComplexPlusComp
      (etalePushforward f) (etalePullback g)).hom (DerivedCategoryPlus.Q _) ≫
  Functor.whiskerLeft (etalePushforward f).mapCochainComplexPlus
    ((etalePullback g).mapDerivedCategoryPlusFactors).inv ≫
  Functor.whiskerRight ((etalePushforward f).rightDerivedPlusUnit) (derivedPullback g)

/-- (Implementation) The canonical natural transformation from `(f_* ⋙ g^*)` on
complexes to `g'^* ⋙ Rf'_*`, built from the underived base change transformation. -/
noncomputable def derivedBaseChangeUnitRight :
    (etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus ⋙
        DerivedCategoryPlus.Q _ ⟶
      DerivedCategoryPlus.Q _ ⋙ (derivedPullback g' ⋙ derivedPushforward f') :=
  Functor.whiskerRight (NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w))
    (DerivedCategoryPlus.Q _) ≫
  Functor.whiskerRight (Functor.mapCochainComplexPlusComp
      (etalePullback g') (etalePushforward f')).hom (DerivedCategoryPlus.Q _) ≫
  Functor.whiskerLeft (etalePullback g').mapCochainComplexPlus
    ((etalePushforward f').rightDerivedPlusUnit) ≫
  Functor.whiskerRight ((etalePullback g').mapDerivedCategoryPlusFactors).inv
    (derivedPushforward f')

instance : (derivedPushforward f ⋙ derivedPullback g).IsRightDerivedFunctor
    (derivedBaseChangeUnitLeft f g) (CochainComplex.Plus.quasiIso _) := by
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).IsLocalization
      (weakEquivalences (CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))) :=
    inferInstanceAs ((DerivedCategoryPlus.Q _).IsLocalization
      (CochainComplex.Plus.quasiIso (Sheaf X.smallEtaleTopology Ab.{u + 1})))
  refine ((etalePushforward f ⋙
    etalePullback g).fibrantObject_derives_mapCochainComplexPlus
      ).isRightDerivedFunctor_of_isIso _ (fun K ↦ ?_)
  dsimp only [derivedBaseChangeUnitLeft]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  haveI := (etalePushforward f).isIso_rightDerivedPlusUnit_app K
  infer_instance

/-- **The derived base change transformation** `Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` for a
commutative square `g' ≫ f = f' ≫ g` of schemes, on the bounded below derived
categories of abelian sheaves over the small étale sites. The proper base change
theorem asserts that it is an isomorphism on complexes with locally torsion cohomology
sheaves when `f` is proper. -/
noncomputable def derivedBaseChangeNatTrans :
    derivedPushforward f ⋙ derivedPullback g ⟶ derivedPullback g' ⋙ derivedPushforward f' :=
  (derivedPushforward f ⋙ derivedPullback g).rightDerivedDesc
    (derivedBaseChangeUnitLeft f g) (CochainComplex.Plus.quasiIso _)
    (derivedPullback g' ⋙ derivedPushforward f') (derivedBaseChangeUnitRight f g f' g' w)

end DerivedBaseChange

end AlgebraicGeometry.Scheme
