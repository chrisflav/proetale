/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Topology.Comparison.Etale
import Proetale.Topology.Coherent.Affine
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.PresheafColimit

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : C ⥤ D) (R : D ⥤ C)
  {A : Type*} [Category A]

namespace MorphismProperty

variable {J : Type*} [Category* J] {C : Type*} [Category* C]
variable {P Q : MorphismProperty C} [Q.IsMultiplicative]

@[simps!]
def Over.lift' (D : J ⥤ C) {S : C} (s : D ⟶ (Functor.const J).obj S)
    (hs : ∀ j, P (s.app j)) (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f)) :
    J ⥤ P.Over Q S :=
  Over.lift (CategoryTheory.Over.lift D s) hs hD

@[simps]
def Over.iteratedLift {S : C} (D : J ⥤ P.Over Q S)
    {X : P.Over Q S}
    (s : D ⟶ (Functor.const J).obj X) (hs : ∀ j, P (s.app j).left)
    (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f).left := by cat_disch) :
    J ⥤ P.Over Q X.left where
  obj j := Over.mk _ (s.app j).left (hs j)
  map {i j} f := Over.homMk (D.map f).left
    (by simpa [-NatTrans.naturality] using congr($(s.naturality f).left)) (hD f)

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry.Scheme

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange]
variable (A : Type*) [Category* A]

instance :
    (Over.pullback P ⊤ f).PreservesOneHypercovers
      (T.smallGrothendieckTopology P)
      (S.smallGrothendieckTopology P) := by
  intro X E
  constructor
  · -- mem₀: Need (E.map (Over.pullback P ⊤ f)).sieve₀ ∈ S.smallGrothendieckTopology P.
    -- Since smallGrothendieckTopology P = (forget P ⊤ S).inducedTopology (overGrothendieckTopology P S),
    -- this reduces to showing the pushforward of the image sieve through Over.forget is in
    -- S.overGrothendieckTopology P. The original hypercover E gives a P-cover of X.left;
    -- base change along pullback.fst X.hom f gives a P-cover of pullback X.hom f
    -- (using P.IsStableUnderBaseChange). Missing: formal infrastructure for relating
    -- sieve operations across the induced topology and the pullback functor.
    rw [Functor.mem_inducedTopology_sieves_iff]
    sorry
  · -- mem₁: Similar argument for the fiber product sieves.
    intro i₁ i₂ W p₁ p₂ hw
    rw [Functor.mem_inducedTopology_sieves_iff]
    sorry

noncomputable
abbrev smallPushforward :
    Sheaf (S.smallGrothendieckTopology P) A ⥤ Sheaf (T.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPushforwardContinuous _ _ _

-- Requires IsContinuous (from PreservesOneHypercovers above) + existence of left adjoint
-- (HasWeakSheafify or HasLeftKanExtension for the small site categories).
instance :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology P)
      (smallGrothendieckTopology P)).IsRightAdjoint :=
  sorry

noncomputable
abbrev smallPullback :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPullback _ _ _

noncomputable
def smallPullbackPushforwardAdj :
    smallPullback f P A ⊣ smallPushforward f P A :=
  (Over.pullback P ⊤ f).sheafAdjunctionContinuous A _ _

-- IsContinuous for Over.map ⊤ hf between smallGrothendieckTopology.
-- Approach 1 (CoverPreserving + CompatiblePreserving): CoverPreserving follows from the
-- commutative diagram Over.map ⊤ hf ⋙ Over.forget P ⊤ T = Over.forget P ⊤ S ⋙ Over.map f
-- and over_map_coverPreserving. CompatiblePreserving is blocked: needs RepresentablyFlat
-- (hard to establish) or IsCoverDense+IsLocallyFaithful (Over.map is not cover dense).
-- Approach 2 (PreservesOneHypercovers): mem₀ works (same underlying cover). mem₁ is blocked:
-- needs to construct W' : P.Over ⊤ S from W : P.Over ⊤ T (requires HasOfPostcompProperty P).
-- Approach 3 (direct): use IsContinuous of Over.map f for over topologies and transfer through
-- the induced topology structure. Missing formal infrastructure for this transfer.
instance (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology P) (smallGrothendieckTopology P) := by
  sorry

def smallSheafRestrict (hf : P f) :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.map ⊤ hf).sheafPushforwardContinuous _ _ _

noncomputable def smallSheafRestrictAdj (hf : P f) :
    smallSheafRestrict f P A hf ⊣ smallPushforward f P A :=
  (Over.mapPullbackAdj P ⊤ f hf trivial).sheaf _ _

/-- If `f : S ⟶ T` satisfies `P` the pullback functor `Shv(T) ⥤ Shv(S)` is
naturally isomorphic to the restriction functor. -/
noncomputable def smallPullbackIsoRestrict (hf : P f) :
    smallPullback f P A ≅ smallSheafRestrict f P A hf :=
  (conjugateIsoEquiv (smallSheafRestrictAdj f P A hf) (smallPullbackPushforwardAdj f P A)).symm
    (Iso.refl _)

end

variable {S : Scheme.{u}}

/-- An object of the pro-étale site of `S` is pro-affine, if it can be written
as `limᵢ (Spec Aᵢ)` where `Spec Aᵢ` is an étale `S`-scheme. -/
def ProEt.proAffine (S : Scheme.{u}) : ObjectProperty S.ProEt :=
  fun X ↦ ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCofiltered J),
    Nonempty (RelativeLimitPresentation J (AffineEtale.Spec S ⋙ S.toProEtale) X)

/-- The pro-étale affine site is the full subcategory of the pro-étale site where every
object can be written as a cofiltered limit of affine étale schemes over `S`. -/
def AffineProEt (S : Scheme.{u}) : Type (u + 1) :=
  (ProEt.proAffine S).FullSubcategory

variable (S : Scheme.{u})
variable (A : Type*) [Category A]

noncomputable instance : Category S.AffineProEt :=
  inferInstanceAs <| Category <| ObjectProperty.FullSubcategory _

namespace AffineProEt

/-- The inclusion of the affine pro-étale site into the pro-étale site. -/
def toProEt (S : Scheme.{u}) : S.AffineProEt ⥤ S.ProEt :=
  (ProEt.proAffine S).ι

instance : (toProEt S).Full := inferInstanceAs <| (ProEt.proAffine S).ι.Full
instance : (toProEt S).Faithful := inferInstanceAs <| (ProEt.proAffine S).ι.Faithful

instance : (toProEt S).LocallyCoverDense (ProEt.topology S) :=
  sorry

instance : (toProEt S).LocallyCoverDense (ProEt.zariskiTopology S) :=
  sorry

noncomputable def topology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.topology S)

noncomputable def zariskiTopology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.zariskiTopology S)

instance : (toProEt S).IsCoverDense (ProEt.topology S) := by
  sorry

instance : (toProEt S).IsContinuous (topology S) (ProEt.topology S) := by
  change (toProEt S).IsContinuous ((toProEt S).inducedTopology (ProEt.topology S))
    (ProEt.topology S)
  infer_instance

/-- The restriction of sheafs on the pro-étale site to sheaf on the affine pro-étale site. -/
noncomputable
def sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (AffineProEt.topology S) A :=
  (toProEt S).sheafPushforwardContinuous _ _ _

instance : HasPullbacks (AffineProEt S) :=
  sorry

/-- To show a presheaf of types is a sheaf on the affine pro-étale site, it suffices to show
it is a Zariksi sheaf and satifies the sheaf condition for single surjective morphisms. -/
lemma isSheaf {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : Presheaf.IsSheaf (zariskiTopology S) F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.hom.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F :=
  sorry

end AffineProEt

noncomputable def ProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.ProEt ⥤ S.ProEt :=
  MorphismProperty.Over.pullback _ _ f

noncomputable def AffineProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.AffineProEt ⥤ S.AffineProEt :=
  ObjectProperty.lift _ (AffineProEt.toProEt _ ⋙ ProEt.baseChange f) sorry

/-- The inclusion of the affine étale site into the affine pro-étale site. -/
noncomputable def AffineEtale.toAffineProEt (S : Scheme.{u}) :
    S.AffineEtale ⥤ S.AffineProEt :=
  ObjectProperty.lift _ (AffineEtale.Spec S ⋙ S.toProEtale) <| fun _ ↦
    ⟨PUnit, inferInstance, inferInstance, ⟨.self _⟩⟩

/-- The topology on the affine pro-étale site is generated by limits
of `1`-hypercovers in the affine étale site. -/
instance :
    (GrothendieckTopology.oneHypercoverRelativelyRepresentable.{u}
      (AffineEtale.toAffineProEt S) (Type u)
      (AffineEtale.topology S) (AffineProEt.topology S)).IsGenerating :=
  sorry

end AlgebraicGeometry.Scheme
