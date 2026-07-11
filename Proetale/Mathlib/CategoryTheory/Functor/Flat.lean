import Mathlib.CategoryTheory.Functor.Flat

/-!
# Evaluation of a pointwise left Kan extension as a colimit

Mathlib's `CategoryTheory.lanEvaluationIsoColim` expresses the evaluation of the left
Kan extension `F.lan` at an object `Y` as a colimit over the costructured arrows over
`Y`, but only for functors between *small* categories. We record here the variant
`lanEvaluationIsoColim'` without the smallness assumptions, phrased in terms of the
existence of pointwise left Kan extensions.
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.lanEvaluationIsoColim` without the smallness assumptions on
the categories involved. The evaluation of `F.lan` at `Y` is the colimit over the
costructured arrows over `Y`. -/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (Y : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F Y) E] :
    F.lan ⋙ (evaluation D E).obj Y ≅
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

end CategoryTheory
