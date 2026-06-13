/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.Affine

/-!
# Sections of the pullback of an étale sheaf over affine pro-étale objects

Let `S` be a scheme and `F` an abelian sheaf on the small étale site of `S`. If `U` is an
object of the small affine pro-étale site of `S`, presented as a cofiltered limit
`U = limⱼ Uⱼ` of affine étale `S`-schemes (a `RelativeLimitPresentation`), then the sections
of the pullback of `F` to the small pro-étale site over `U` are the filtered colimit of the
sections `F(Uⱼ)` at the stages of the presentation. This is the underived form of
Bhatt–Scholze, Lemma 5.1.1.

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackSectionsι`: the canonical map
  `F(Uⱼ) ⟶ (ν^*F)(U)`, given by restriction along the projection `U ⟶ Uⱼ` combined with the
  identification of the pullback with the left Kan extension on the affine pro-étale site.
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackSectionsCocone`: the cocone over the diagram
  `j ↦ F(Uⱼ)` (indexed by `Jᵒᵖ`) with point `(ν^*F)(U)` and legs `sheafPullbackSectionsι`.
- `AlgebraicGeometry.Scheme.ProEt.isColimitSheafPullbackSectionsCocone`: this cocone is a
  colimit cocone, i.e. `(ν^*F)(U) = colimⱼ F(Uⱼ)`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace ProEt

/-- The restriction of the presheaf pullback of an étale presheaf `F` (i.e., the left Kan
extension along the inclusion of the small étale site into the small pro-étale site) to the
small affine étale site is canonically isomorphic to `F` itself, via the unit of the left
Kan extension. -/
noncomputable def lanToProEtaleRestrictIso (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) :
    (AffineEtale.toAffineProEt S).op ⋙ (AffineProEt.toProEt S).op ⋙
      (toProEtale S).op.lan.obj F ≅ (AffineEtale.Spec S).op ⋙ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
    Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
    Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso <| (toProEtale S).op.lanUnit.app F).symm

variable {S}
variable (F : Sheaf S.smallEtaleTopology Ab.{u + 1})

/-- Evaluated at an affine pro-étale object `U`, the sections of the sheaf pullback of an
étale sheaf `F` agree with the sections of the presheaf pullback (left Kan extension),
since the latter is already a sheaf on the small affine pro-étale site. -/
noncomputable def sheafPullbackSectionsIso (U : S.AffineProEt) :
    ((toProEtale S).op.lan.obj F.obj).obj (op ((AffineProEt.toProEt S).obj U)) ≅
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  ((sheafPullbackCompIso S).app F).symm.app (op U)

@[simp]
lemma sheafPullbackSectionsIso_hom (U : S.AffineProEt) :
    (sheafPullbackSectionsIso F U).hom = ((sheafPullbackCompIso S).inv.app F).app (op U) :=
  rfl

variable {J : Type u} [SmallCategory J] {U : S.AffineProEt}
  (pres : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) U)

/-- Given a presentation of an affine pro-étale object `U` as a cofiltered limit
`U = limⱼ Uⱼ` of affine étale `S`-schemes, the sections of `F` at the stages `Uⱼ` form a
cocone over the sections of the pullback of `F` at `U`: the legs are restriction along the
projections `U ⟶ Uⱼ`, combined with the identification of the pullback sheaf with the left
Kan extension on the small affine pro-étale site. -/
noncomputable def sheafPullbackSectionsCocone :
    Cocone ((pres.diag ⋙ AffineEtale.Spec S).op ⋙ (sheafToPresheaf _ _).obj F) :=
  Cocone.extend
    ((Cocone.precompose
        (Functor.isoWhiskerLeft pres.diag.op (lanToProEtaleRestrictIso S F.obj)).inv).obj
      (((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F.obj).mapCocone pres.cone.op))
    (sheafPullbackSectionsIso F U).hom

@[simp]
lemma sheafPullbackSectionsCocone_pt :
    (sheafPullbackSectionsCocone F pres).pt =
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  rfl

/-- The canonical map from the sections of an étale sheaf `F` at a stage `Uⱼ` of a
presentation `U = limⱼ Uⱼ` of an affine pro-étale object `U` to the sections of the
pullback of `F` at `U`. -/
noncomputable def sheafPullbackSectionsι (j : J) :
    F.obj.obj (op ((AffineEtale.Spec S).obj (pres.diag.obj j))) ⟶
      ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).obj
        (op ((AffineProEt.toProEt S).obj U)) :=
  (sheafPullbackSectionsCocone F pres).ι.app (op j)

@[simp]
lemma sheafPullbackSectionsCocone_ι_app (j : Jᵒᵖ) :
    (sheafPullbackSectionsCocone F pres).ι.app j = sheafPullbackSectionsι F pres j.unop :=
  rfl

/-- The legs of `sheafPullbackSectionsCocone`, explicitly: restrict from the stage to the
left Kan extension at `U` along the projection, then identify with the sections of the
sheaf pullback. -/
lemma sheafPullbackSectionsι_eq (j : J) :
    sheafPullbackSectionsι F pres j =
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres.diag.obj j)) ≫
        ((toProEtale S).op.lan.obj F.obj).map
          ((AffineProEt.toProEt S).map (pres.π.app j)).op ≫
        ((sheafPullbackCompIso S).inv.app F).app (op U) := by
  simp [sheafPullbackSectionsι, sheafPullbackSectionsCocone]

/-- The legs of `sheafPullbackSectionsCocone` are compatible with the transition maps of the
presentation. -/
@[reassoc (attr := simp)]
lemma map_sheafPullbackSectionsι {j j' : J} (f : j ⟶ j') :
    F.obj.map ((AffineEtale.Spec S).map (pres.diag.map f)).op ≫
        sheafPullbackSectionsι F pres j =
      sheafPullbackSectionsι F pres j' :=
  (sheafPullbackSectionsCocone F pres).w f.op

/-- **Bhatt–Scholze, Lemma 5.1.1.** The sections of the pullback of an étale sheaf `F` over
an affine pro-étale object `U` are the filtered colimit of the sections of `F` at the stages
of a relative limit presentation `U = limⱼ Uⱼ` by affine étale `S`-schemes. -/
noncomputable def isColimitSheafPullbackSectionsCocone [IsCofiltered J] :
    IsColimit (sheafPullbackSectionsCocone F pres) :=
  ((IsColimit.precomposeInvEquiv
      (Functor.isoWhiskerLeft pres.diag.op (lanToProEtaleRestrictIso S F.obj))
      (((AffineProEt.toProEt S).op ⋙ (toProEtale S).op.lan.obj F.obj).mapCocone
        pres.cone.op)).symm
    (Functor.PreservesRelativeFilteredColimits.nonempty_isColimit pres.cone
      pres.isLimit).some).ofIsoColimit
    (Cocone.ext (sheafPullbackSectionsIso F U) fun _ ↦ rfl)

/-- The legs of `sheafPullbackSectionsCocone` are compatible with morphisms of relative
limit presentations. -/
@[reassoc]
lemma sheafPullbackSectionsι_naturality {X Y : S.AffineProEt}
    {pres₁ : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) X}
    {pres₂ : RelativeLimitPresentation J (AffineEtale.toAffineProEt S) Y}
    (φ : pres₁.Hom pres₂) (j : J) :
    F.obj.map ((AffineEtale.Spec S).map (φ.natTrans.app j)).op ≫
        sheafPullbackSectionsι F pres₁ j =
      sheafPullbackSectionsι F pres₂ j ≫
        ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).map
          ((AffineProEt.toProEt S).map φ.map).op := by
  have h1 : F.obj.map ((AffineEtale.Spec S).map (φ.natTrans.app j)).op ≫
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres₁.diag.obj j)) =
      (lanToProEtaleRestrictIso S F.obj).inv.app (op (pres₂.diag.obj j)) ≫
        ((toProEtale S).op.lan.obj F.obj).map
          ((AffineProEt.toProEt S).map
            ((AffineEtale.toAffineProEt S).map (φ.natTrans.app j))).op :=
    (lanToProEtaleRestrictIso S F.obj).inv.naturality (φ.natTrans.app j).op
  have h2 : ((toProEtale S).op.lan.obj F.obj).map
        ((AffineProEt.toProEt S).map φ.map).op ≫
        ((sheafPullbackCompIso S).inv.app F).app (op X) =
      ((sheafPullbackCompIso S).inv.app F).app (op Y) ≫
        ((sheafToPresheaf _ _).obj ((sheafPullback S Ab.{u + 1}).obj F)).map
          ((AffineProEt.toProEt S).map φ.map).op :=
    ((sheafPullbackCompIso S).inv.app F).naturality (φ.map).op
  rw [sheafPullbackSectionsι_eq, sheafPullbackSectionsι_eq, reassoc_of% h1,
    ← Functor.map_comp_assoc, ← op_comp, ← Functor.map_comp,
    ← RelativeLimitPresentation.Hom.map_π φ j, Functor.map_comp, op_comp,
    Functor.map_comp_assoc, h2, Category.assoc, Category.assoc]

end ProEt

end AlgebraicGeometry.Scheme
