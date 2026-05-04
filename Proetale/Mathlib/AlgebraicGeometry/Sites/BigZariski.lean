import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Proetale.Mathlib.AlgebraicGeometry.Sites.MorphismProperty

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory

@[simp]
lemma GrothendieckTopology.pullback_hom_mem_iff {C : Type*} [Category C] {J : GrothendieckTopology C}
    {X Y : C} {e : X ≅ Y} {S : Sieve Y} :
    S.pullback e.hom ∈ J X ↔ S ∈ J Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ J.pullback_stable e.hom h⟩
  simpa using J.pullback_stable e.inv h

end CategoryTheory

namespace AlgebraicGeometry

/--
The big Zariski site on the category of all `u`-schemes has sheafification in `Type u`.
This requires a refactor of sheafification in mathlib.
-/
proof_wanted hasSheafify_zariskiTopology : HasSheafify Scheme.zariskiTopology.{u} (Type u)

lemma preservesFiniteProducts_of_isSheaf_zariskiTopology {F : Scheme.{u}ᵒᵖ ⥤ Type*}
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) :
    PreservesFiniteProducts F := by
  apply Limits.preservesFiniteProducts_of_preservesLimitsOfShape.{0}
  intro ι _
  apply preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF

lemma Scheme.IsLocallyDirected.ofArrows_mem_grothendieckTopology {J : Type*} [Category J]
    (F : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F.comp Scheme.forget).IsLocallyDirected]
    [Quiver.IsThin J] [Small.{u} J] :
    Sieve.ofArrows _ (colimit.ι F) ∈ Scheme.zariskiTopology (colimit F) :=
  (Scheme.IsLocallyDirected.openCover F).generate_ofArrows_mem_grothendieckTopology

end AlgebraicGeometry
