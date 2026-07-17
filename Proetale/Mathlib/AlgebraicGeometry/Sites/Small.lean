import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.Sites.Grothendieck

universe u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

instance (hPQ : P ≤ Q) [P.HasOfPostcompProperty P] :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) := by
  have : PreservesFiniteLimits
      (Over.changeProp S hPQ le_rfl : P.Over ⊤ S ⥤ Q.Over ⊤ S) := by
    refine ⟨fun J _ _ ↦ ?_⟩
    have : PreservesLimitsOfShape J (Over.changeProp S hPQ le_rfl ⋙
        MorphismProperty.Over.forget Q ⊤ S) :=
      inferInstanceAs <| PreservesLimitsOfShape J (MorphismProperty.Over.forget P ⊤ S)
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (MorphismProperty.Over.forget Q ⊤ S)
  have : RepresentablyFlat (Over.changeProp S hPQ le_rfl : P.Over ⊤ S ⥤ Q.Over ⊤ S) :=
    flat_of_preservesFiniteLimits _
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) ⟨fun {U R} hR ↦ ?_⟩
  rw [Functor.mem_inducedTopology_sieves_iff, ← Sieve.functorPushforward_comp]
  -- `Over.changeProp S hPQ le_rfl ⋙ forget Q = forget P` definitionally
  have hmono : S.overGrothendieckTopology P ≤ S.overGrothendieckTopology Q := by
    intro Z T hT
    rw [GrothendieckTopology.mem_over_iff] at hT ⊢
    exact grothendieckTopology_monotone hPQ _ hT
  exact hmono _ ((Functor.mem_inducedTopology_sieves_iff _ _ _).mp hR)

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
variable (A : Type*) [Category* A]

/-- The base change functor along `f : S ⟶ T` is continuous for the small
Grothendieck topologies. -/
instance :
    (Over.pullback P ⊤ f).IsContinuous
      (T.smallGrothendieckTopology P)
      (S.smallGrothendieckTopology P) := by
  have : RepresentablyFlat (Over.pullback P ⊤ f) := flat_of_preservesFiniteLimits _
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (Over.pullback P ⊤ f)) ⟨fun {U R} hR ↦ ?_⟩
  rw [Functor.mem_inducedTopology_sieves_iff, ← Sieve.functorPushforward_comp]
  refine GrothendieckTopology.functorPushforward_mem_of_iso _
    (Over.pullbackCompForgetIso (P := P) (Q := ⊤) f).symm R ?_
  rw [Sieve.functorPushforward_comp]
  exact (GrothendieckTopology.coverPreserving_overPullback
    (J := Scheme.grothendieckTopology P) f).cover_preserve
    (by rwa [Functor.mem_inducedTopology_sieves_iff] at hR)

noncomputable
abbrev smallPushforward :
    Sheaf (S.smallGrothendieckTopology P) A ⥤ Sheaf (T.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPushforwardContinuous _ _ _

variable [HasWeakSheafify (S.smallGrothendieckTopology P) A]
  [∀ F : (P.Over ⊤ T)ᵒᵖ ⥤ A, (Over.pullback P ⊤ f).op.HasLeftKanExtension F]

instance :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology P)
      (smallGrothendieckTopology P)).IsRightAdjoint :=
  inferInstance

noncomputable
abbrev smallPullback :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPullback _ _ _

noncomputable
def smallPullbackPushforwardAdj :
    smallPullback f P A ⊣ smallPushforward f P A :=
  (Over.pullback P ⊤ f).sheafAdjunctionContinuous A _ _

/-- The functor `X/S ⥤ X/T` induced by postcomposition with `f : S ⟶ T` satisfying `P`
is continuous for the small Grothendieck topologies. -/
instance (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology P) (smallGrothendieckTopology P) := by
  refine Functor.isContinuous_of_coverPreserving ⟨?_⟩ ⟨fun {U R} hR ↦ ?_⟩
  · -- compatible preservation, mirroring `over_map_compatiblePreserving`: a cone over
    -- `(Over.map ⊤ hf).obj Y₁` and `(Over.map ⊤ hf).obj Y₂` lifts to `P.Over ⊤ S`,
    -- the property of the lifted structure morphism coming from `of_postcomp`.
    intro ℱ Z 𝒯 x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h
    have hW' : P (f₁.left ≫ Y₁.hom) := by
      refine P.of_postcomp (W' := P) _ f hf ?_
      have : f₁.left ≫ Y₁.hom ≫ f = W.hom := MorphismProperty.Over.w f₁
      rw [Category.assoc, this]
      exact W.prop
    let W' : P.Over ⊤ S := MorphismProperty.Over.mk ⊤ (f₁.left ≫ Y₁.hom) hW'
    have hleft : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      simpa using congrArg (fun q ↦ q.left) h
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl trivial
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left
      (by rw [← MorphismProperty.Over.w g₂, ← Category.assoc, ← hleft, Category.assoc,
        MorphismProperty.Over.w g₁]; simp [W']) trivial
    let e : (Over.map ⊤ hf).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _)
      (by simpa [W'] using (MorphismProperty.Over.w f₁).symm)
    have compat : ℱ.obj.map ((Over.map ⊤ hf).map g₁').op (x g₁ hg₁) =
        ℱ.obj.map ((Over.map ⊤ hf).map g₂').op (x g₂ hg₂) :=
      hx g₁' g₂' hg₁ hg₂ (by ext; simpa [g₁', g₂'] using hleft)
    have h1 : e.inv ≫ (Over.map ⊤ hf).map g₁' = f₁ := by
      ext
      simp [e, g₁', W']
    have h2 : e.inv ≫ (Over.map ⊤ hf).map g₂' = f₂ := by
      ext
      simp [e, g₂', W']
    calc ℱ.obj.map f₁.op (x g₁ hg₁)
        = ℱ.obj.map (e.inv ≫ (Over.map ⊤ hf).map g₁').op (x g₁ hg₁) := by rw [h1]
      _ = ℱ.obj.map e.inv.op (ℱ.obj.map ((Over.map ⊤ hf).map g₁').op (x g₁ hg₁)) := by
          rw [op_comp, ℱ.obj.map_comp]; rfl
      _ = ℱ.obj.map e.inv.op (ℱ.obj.map ((Over.map ⊤ hf).map g₂').op (x g₂ hg₂)) := by
          rw [compat]
      _ = ℱ.obj.map f₂.op (x g₂ hg₂) := by rw [← h2, op_comp, ℱ.obj.map_comp]; rfl
  · -- cover preservation, by transport to `over_map_coverPreserving` for the big sites
    rw [Functor.mem_inducedTopology_sieves_iff, ← Sieve.functorPushforward_comp]
    have e : MorphismProperty.Over.forget P ⊤ S ⋙ CategoryTheory.Over.map f ≅
        Over.map ⊤ hf ⋙ MorphismProperty.Over.forget P ⊤ T := Iso.refl _
    refine GrothendieckTopology.functorPushforward_mem_of_iso _ e R ?_
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.over_map_coverPreserving
      (J := Scheme.grothendieckTopology P) f).cover_preserve
      ((Functor.mem_inducedTopology_sieves_iff _ _ _).mp hR)

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

end AlgebraicGeometry.Scheme
