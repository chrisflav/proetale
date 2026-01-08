import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Proetale.Mathlib.AlgebraicGeometry.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Sieves

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]

@[simp]
lemma Cover.pullbackArrows_ofArrows {X S : Scheme.{u}}
    (𝒰 : S.Cover (precoverage P)) (f : X ⟶ S) :
    (Presieve.ofArrows 𝒰.X 𝒰.f).pullbackArrows f =
      .ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f := by
  rw [← Presieve.ofArrows_pullback]
  rfl

variable [P.IsMultiplicative]

@[simp]
lemma Cover.generate_ofArrows_mem_grothendieckTopology {S : Scheme.{u}}
    (𝒰 : Cover.{v} (precoverage P) S) :
    .generate (.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.grothendieckTopology P S :=
  𝒰.mem_grothendieckTopology

lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] :
    ⊥ ∈ Scheme.grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  let 𝒰 : Cover.{u} (precoverage P) X :=
    { I₀ := PEmpty
      X := PEmpty.elim
      f i := i.elim
      mem₀ := by simp [ofArrows_mem_precoverage_iff] }
  have : Presieve.ofArrows 𝒰.X 𝒰.f = ⊥ := by
    rw [eq_bot_iff]
    rintro - - ⟨i⟩
    exact i.elim
  rw [← this]
  exact 𝒰.generate_ofArrows_mem_grothendieckTopology

lemma Cover.ofArrows_of_unique {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Unique 𝒰.I₀] :
    Presieve.ofArrows 𝒰.X 𝒰.f = Presieve.singleton (𝒰.f default) :=
  sorry

end AlgebraicGeometry.Scheme
