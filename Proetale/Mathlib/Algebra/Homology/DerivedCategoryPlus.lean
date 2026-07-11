/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Localization.HasLocalization

/-!
# The bounded below derived category

Mathlib's `DerivedCategory C` localizes all of `CochainComplex C ℤ` at the
quasi-isomorphisms, but there is currently no machinery to right-derive a non-exact
functor on it (this would require K-injective resolutions of unbounded complexes).
For bounded below complexes the injective model structure on `CochainComplex.Plus C`
(`Mathlib.Algebra.Homology.ModelCategory.Injective`) provides such resolutions, so we
introduce the corresponding localized category:

- `DerivedCategoryPlus C`: the localization of the category `CochainComplex.Plus C` of
  bounded below cochain complexes at the quasi-isomorphisms, available under a
  `[HasDerivedCategoryPlus.{w} C]` instance (`HasDerivedCategoryPlus.standard` always
  applies, with `w := max u v`).
- `DerivedCategoryPlus.Q`: the localization functor.
- `DerivedCategoryPlus.homologyFunctor`: the homology functors
  `DerivedCategoryPlus C ⥤ C`.
- `CategoryTheory.NatTrans.mapCochainComplexPlus`: functoriality of
  `Functor.mapCochainComplexPlus` in natural transformations.

This is intended as the home of the derived pushforward of abelian sheaves along a
morphism of sites (see `Proetale/Mathlib/AlgebraicGeometry/Sites/DerivedPushforward`),
in particular for the statement of the proper base change theorem.
-/

universe w v u

open CategoryTheory Limits

section

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The assumption that the quasi-isomorphisms between bounded below cochain complexes
admit a localized category with `w`-small hom types. The instance
`HasDerivedCategoryPlus.standard` always provides one with `w := max u v`. -/
abbrev HasDerivedCategoryPlus :=
  MorphismProperty.HasLocalization.{w} (CochainComplex.Plus.quasiIso C)

/-- The constructed localization of the category of bounded below cochain complexes at
the quasi-isomorphisms. -/
@[implicit_reducible]
noncomputable def HasDerivedCategoryPlus.standard : HasDerivedCategoryPlus.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategoryPlus.{w} C]

/-- The bounded below derived category of an abelian category: the localization of the
category of bounded below cochain complexes at the quasi-isomorphisms. -/
abbrev DerivedCategoryPlus :=
  (CochainComplex.Plus.quasiIso C).Localization'

namespace DerivedCategoryPlus

/-- The localization functor from bounded below cochain complexes to the bounded below
derived category. -/
abbrev Q : CochainComplex.Plus C ⥤ DerivedCategoryPlus C :=
  (CochainComplex.Plus.quasiIso C).Q'

omit [HasDerivedCategoryPlus.{w} C] in
/-- The homology functors on bounded below cochain complexes invert
quasi-isomorphisms. -/
lemma homologyFunctor_inverts (n : ℤ) :
    (CochainComplex.Plus.quasiIso C).IsInvertedBy (CochainComplex.Plus.ι C ⋙
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n) := fun _ _ f hf ↦
  HomologicalComplex.homologyFunctor_inverts_quasiIso C (ComplexShape.up ℤ) n
    ((CochainComplex.Plus.ι C).map f) hf

/-- The homology functors on the bounded below derived category. -/
noncomputable def homologyFunctor (n : ℤ) : DerivedCategoryPlus C ⥤ C :=
  Localization.lift _ (homologyFunctor_inverts C n) (Q C)

/-- The homology functors on the bounded below derived category are induced by the
homology functors on complexes. -/
noncomputable def homologyFunctorFactors (n : ℤ) :
    Q C ⋙ homologyFunctor C n ≅
      CochainComplex.Plus.ι C ⋙ HomologicalComplex.homologyFunctor C
        (ComplexShape.up ℤ) n :=
  Localization.fac _ (homologyFunctor_inverts C n) (Q C)

/-- An object of the abelian category, considered as an object of the bounded below
derived category concentrated in a single degree. -/
noncomputable def singleFunctor [HasZeroObject C] (n : ℤ) : C ⥤ DerivedCategoryPlus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (ComplexShape.up ℤ) n)
    (fun _ ↦ ⟨n, inferInstance⟩) ⋙ Q C

end DerivedCategoryPlus

end

namespace CategoryTheory.NatTrans

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]

/-- The natural transformation on categories of bounded below cochain complexes
induced by a natural transformation between functors preserving zero morphisms. -/
def mapCochainComplexPlus {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (τ : F ⟶ G) :
    F.mapCochainComplexPlus ⟶ G.mapCochainComplexPlus where
  app K := (CochainComplex.Plus.fullyFaithfulι D).preimage
    ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
      ((CochainComplex.Plus.ι C).obj K))
  naturality K L f := (CochainComplex.Plus.fullyFaithfulι D).map_injective (by
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
    exact (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).naturality
      ((CochainComplex.Plus.ι C).map f))

/-- The underlying morphism of complexes of `NatTrans.mapCochainComplexPlus`. -/
lemma mapCochainComplexPlus_app_ι {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (τ : F ⟶ G) (K : CochainComplex.Plus C) :
    (CochainComplex.Plus.ι D).map ((NatTrans.mapCochainComplexPlus τ).app K) =
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((CochainComplex.Plus.ι C).obj K) :=
  (CochainComplex.Plus.fullyFaithfulι D).map_preimage _

end CategoryTheory.NatTrans
