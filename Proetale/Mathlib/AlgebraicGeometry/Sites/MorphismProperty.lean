import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Proetale.Mathlib.AlgebraicGeometry.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Sieves

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

@[simp]
lemma Cover.pullbackArrows_ofArrows {X S : Scheme.{u}}
    (𝒰 : S.Cover P) (f : X ⟶ S) :
    (Presieve.ofArrows 𝒰.obj 𝒰.map).pullbackArrows f =
      .ofArrows (𝒰.pullbackCover' f).obj (𝒰.pullbackCover' f).map := by
  rw [← Presieve.ofArrows_pullback]
  rfl

variable [P.IsMultiplicative]

@[simp]
lemma Cover.generate_ofArrows_mem_grothendieckTopology {S : Scheme.{u}} (𝒰 : Cover.{u} P S) :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ Scheme.grothendieckTopology P S := by
  rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, rfl⟩, Sieve.le_generate _⟩

lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] :
    ⊥ ∈ Scheme.grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  let 𝒰 : Cover.{u} P X :=
    { J := PEmpty
      obj := PEmpty.elim
      map i := i.elim
      f x := (IsEmpty.false x).elim
      covers x := (IsEmpty.false x).elim
      map_prop x := x.elim }
  have : Presieve.ofArrows 𝒰.obj 𝒰.map = ⊥ := by
    rw [eq_bot_iff]
    rintro - - ⟨i⟩
    exact i.elim
  rw [← this]
  exact 𝒰.generate_ofArrows_mem_grothendieckTopology

lemma Cover.ofArrows_of_unique {S : Scheme.{u}} (𝒰 : S.Cover P) [Unique 𝒰.J] :
    Presieve.ofArrows 𝒰.obj 𝒰.map = Presieve.singleton (𝒰.map default) :=
  sorry

end AlgebraicGeometry.Scheme
