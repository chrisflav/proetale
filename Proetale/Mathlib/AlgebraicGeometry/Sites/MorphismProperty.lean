import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Proetale.Mathlib.AlgebraicGeometry.Limits
import Proetale.Mathlib.CategoryTheory.Sites.Sieves

universe v u

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
lemma Cover.generate_ofArrows_mem_grothendieckTopology {S : Scheme.{u}} (𝒰 : Cover.{v} P S) :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ Scheme.grothendieckTopology P S := by
  let 𝒱 : Cover.{u} P S := 𝒰.ulift
  apply GrothendieckTopology.superset_covering _ (S := Sieve.ofArrows _ 𝒱.map) _
  · rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
    exact ⟨.ofArrows 𝒱.obj 𝒱.map, ⟨𝒱, rfl⟩, Sieve.le_generate _⟩
  · rw [Sieve.ofArrows]
    apply Sieve.generate_mono
    rintro - - ⟨i⟩
    use 𝒰.f i

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
