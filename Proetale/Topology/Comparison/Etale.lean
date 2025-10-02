/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Topology.Proetale.Sheafification
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Comparison with the étale site

-/

universe u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the étale site into the pro-étale site. -/
@[simps! obj_toComma]
def toProEtale (S : Scheme.{u}) : Etale S ⥤ ProEt S :=
  MorphismProperty.Over.changeProp _ isEtale_le_weaklyEtale le_rfl

variable (S : Scheme.{u})

instance : (toProEtale S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ isEtale_le_weaklyEtale le_rfl).Full

instance : (toProEtale S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ isEtale_le_weaklyEtale le_rfl).Faithful

/-- The inclusion of the étale site into the pro-étale site is continuous. -/
instance isContinuous_toProEtale :
    (toProEtale S).IsContinuous (smallEtaleTopology S) (ProEt.topology S) :=
  inferInstanceAs <| (Over.changeProp _ isEtale_le_weaklyEtale _).IsContinuous
    (smallGrothendieckTopology _) (smallGrothendieckTopology _)

namespace ProEt

/-- The direct image functor from pro-étale sheafs to étale sheafs. -/
abbrev sheafPushforward :
    Sheaf (ProEt.topology S) Ab.{u} ⥤ Sheaf (smallEtaleTopology S) Ab.{u} :=
  (toProEtale S).sheafPushforwardContinuous Ab.{u} (smallEtaleTopology S) (ProEt.topology S)

instance (F : S.Etaleᵒᵖ ⥤ Ab.{u}) : (toProEtale S).op.HasPointwiseLeftKanExtension F :=
  sorry

/-- The direct image functor from pro-étale sheafs to étale sheafs has a left-adjoint. -/
instance : (ProEt.sheafPushforward S).IsRightAdjoint := inferInstance

/-- The inverse image functor from étale sheafs to pro-étale sheafs. -/
noncomputable abbrev sheafPullback :
    Sheaf (smallEtaleTopology S) Ab.{u} ⥤ Sheaf (ProEt.topology S) Ab.{u} :=
  (toProEtale S).sheafPullback Ab.{u} (smallEtaleTopology S) (ProEt.topology S)

/-- The inverse image - direct image adjunction for the pro-étale site. -/
noncomputable abbrev sheafAdjunction :
    ProEt.sheafPullback S ⊣ ProEt.sheafPushforward S :=
  (toProEtale S).sheafAdjunctionContinuous Ab.{u} (smallEtaleTopology S) (ProEt.topology S)

instance preservesFilteredColimits_sheafPullback_obj (F : Sheaf (smallEtaleTopology S) Ab.{u}) :
    PreservesFilteredColimits ((sheafPullback S).obj F).val :=
  sorry

instance isIso_unit_sheafAdjunction : IsIso (sheafAdjunction S).unit :=
  sorry

instance faithful_sheafPullback : (sheafPullback S).Faithful :=
  (sheafAdjunction S).faithful_L_of_mono_unit_app

instance full_sheafPullback : (sheafPullback S).Full :=
  (sheafAdjunction S).full_L_of_isSplitEpi_unit_app

end ProEt

end AlgebraicGeometry.Scheme
