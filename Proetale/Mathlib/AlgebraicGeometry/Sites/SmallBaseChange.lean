/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Proetale.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Base change for abelian sheaves on small étale sites

For a morphism of schemes `f : X ⟶ S` we study the adjunction `f^* ⊣ f_*` between
abelian sheaves on the small étale sites (`smallPullback`/`smallPushforward`,
`Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean`):

- `AlgebraicGeometry.Scheme.preservesFiniteLimits_smallPullback`: `f^*` is exact.
- `AlgebraicGeometry.Scheme.baseChangeNatTrans`: for a commutative square
  `g' ≫ f = f' ≫ g` of schemes, the base change transformation
  `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*`, obtained as the mate of the canonical isomorphism
  `g^* ⋙ f'^* ≅ f^* ⋙ g'^*` (which in turn is conjugate to the equality
  `g'_* ⋙ f_* = f'_* ⋙ g_*` of pushforward functors).

This is the underived layer of the base change machinery for étale cohomology; the
derived version is in `Proetale/Mathlib/AlgebraicGeometry/Sites/DerivedPushforward`.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty

section LanEvaluation

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

-- TODO: this is duplicated from `Proetale/Topology/Comparison/CohomologyComparison`
-- (and `Comparator/Definitions.lean`); it should be unified upstream.
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved. -/
private noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (Y : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F Y) E] :
    F.lan ⋙ (CategoryTheory.evaluation D E).obj Y ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F Y) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ Y).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end LanEvaluation

namespace AlgebraicGeometry.Scheme

instance hasFilteredColimitsOfSizeAbBaseChange :
    HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance ab5OfSizeAbBaseChange : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

/-- The category of abelian sheaves on the small étale site is Grothendieck abelian.
(This duplicates the instance from `Proetale/Topology/Comparison/CohomologyComparison`
to keep this file independent of the comparison theory.) -/
instance isGrothendieckAbelianSheafSmallEtaleAbBaseChange (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance enoughInjectivesSheafSmallEtaleAbBaseChange (S : Scheme.{u}) :
    EnoughInjectives (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

section Exactness

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The left Kan extension of abelian presheaves along the base change functor of small
étale sites is exact, since the base change functor is representably flat. -/
noncomputable instance preservesFiniteLimits_lan_pullback :
    PreservesFiniteLimits ((Over.pullback @Etale ⊤ f).op.lan :
      (S.Etaleᵒᵖ ⥤ Ab.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ Ab.{u + 1}) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro K
  haveI : RepresentablyFlat (Over.pullback @Etale ⊤ f) := flat_of_preservesFiniteLimits _
  haveI : IsFiltered (CostructuredArrow (Over.pullback @Etale ⊤ f).op K) :=
    IsFiltered.of_equivalence
      (structuredArrowOpEquivalence (Over.pullback @Etale ⊤ f) (unop K))
  exact preservesLimitsOfShape_of_natIso
    (lanEvaluationIsoColim' (Over.pullback @Etale ⊤ f).op K).symm

/-- The pullback of abelian sheaves along a morphism of schemes is exact. -/
instance preservesFiniteLimits_smallPullback :
    PreservesFiniteLimits (smallPullback f @Etale Ab.{u + 1}) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (Over.pullback @Etale ⊤ f)
    Ab.{u + 1} (S.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

instance preservesFiniteColimits_smallPullback :
    PreservesFiniteColimits (smallPullback f @Etale Ab.{u + 1}) :=
  haveI : PreservesColimitsOfSize.{0, 0} (smallPullback f @Etale Ab.{u + 1}) :=
    (smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

instance additive_smallPullback : (smallPullback f @Etale Ab.{u + 1}).Additive := by
  haveI : (smallPullback f @Etale Ab.{u + 1}).IsLeftAdjoint :=
    (smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

instance additive_smallPushforward : (smallPushforward f @Etale Ab.{u + 1}).Additive := by
  haveI : PreservesLimitsOfSize.{0, 0} (smallPushforward f @Etale Ab.{u + 1}) :=
    (smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).rightAdjoint_preservesLimits
  exact Functor.additive_of_preserves_binary_products _

end Exactness

section BaseChange

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- The base change functors of small étale sites along a commutative square of schemes
commute up to a canonical natural isomorphism. -/
noncomputable def overPullbackSquareIso :
    Over.pullback @Etale ⊤ f ⋙ Over.pullback @Etale ⊤ g' ≅
      Over.pullback @Etale ⊤ g ⋙ Over.pullback @Etale ⊤ f' :=
  (MorphismProperty.Over.pullbackComp g' f).symm ≪≫ MorphismProperty.Over.pullbackCongr w ≪≫
    MorphismProperty.Over.pullbackComp f' g

/-- The pushforward functors of abelian sheaves on small étale sites along a
commutative square of schemes commute up to a canonical natural isomorphism. -/
noncomputable def pushforwardSquareIso :
    smallPushforward g' @Etale Ab.{u + 1} ⋙ smallPushforward f @Etale Ab.{u + 1} ≅
      smallPushforward f' @Etale Ab.{u + 1} ⋙ smallPushforward g @Etale Ab.{u + 1} :=
  haveI := Functor.isContinuous_comp (Over.pullback @Etale ⊤ f) (Over.pullback @Etale ⊤ g')
    (S.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
    (X'.smallGrothendieckTopology @Etale)
  haveI := Functor.isContinuous_comp (Over.pullback @Etale ⊤ g) (Over.pullback @Etale ⊤ f')
    (S.smallGrothendieckTopology @Etale) (S'.smallGrothendieckTopology @Etale)
    (X'.smallGrothendieckTopology @Etale)
  Functor.sheafPushforwardContinuousComp (Over.pullback @Etale ⊤ f)
      (Over.pullback @Etale ⊤ g') Ab.{u + 1} (S.smallGrothendieckTopology @Etale)
      (X.smallGrothendieckTopology @Etale) (X'.smallGrothendieckTopology @Etale) ≪≫
    Functor.sheafPushforwardContinuousIso (overPullbackSquareIso f g f' g' w) Ab.{u + 1}
      (S.smallGrothendieckTopology @Etale) (X'.smallGrothendieckTopology @Etale) ≪≫
    (Functor.sheafPushforwardContinuousComp (Over.pullback @Etale ⊤ g)
      (Over.pullback @Etale ⊤ f') Ab.{u + 1} (S.smallGrothendieckTopology @Etale)
      (S'.smallGrothendieckTopology @Etale) (X'.smallGrothendieckTopology @Etale)).symm

/-- The pullback functors of abelian sheaves on small étale sites along a commutative
square of schemes commute up to a canonical natural isomorphism, conjugate to
`pushforwardSquareIso`. -/
noncomputable def pullbackSquareIso :
    smallPullback g @Etale Ab.{u + 1} ⋙ smallPullback f' @Etale Ab.{u + 1} ≅
      smallPullback f @Etale Ab.{u + 1} ⋙ smallPullback g' @Etale Ab.{u + 1} :=
  (conjugateIsoEquiv
    ((smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).comp
      (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1}))
    ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).comp
      (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1}))).symm
    (pushforwardSquareIso f g f' g' w)

/-- **The base change transformation** `f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` for a commutative
square `g' ≫ f = f' ≫ g` of schemes, on abelian sheaves over the small étale sites:
the mate of the canonical isomorphism `pullbackSquareIso`. -/
noncomputable def baseChangeNatTrans :
    smallPushforward f @Etale Ab.{u + 1} ⋙ smallPullback g @Etale Ab.{u + 1} ⟶
      smallPullback g' @Etale Ab.{u + 1} ⋙ smallPushforward f' @Etale Ab.{u + 1} :=
  (mateEquiv (smallPullbackPushforwardAdj f @Etale Ab.{u + 1})
    (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1})
    (TwoSquare.mk _ _ _ _ (pullbackSquareIso f g f' g' w).hom)).natTrans

end BaseChange

end AlgebraicGeometry.Scheme
