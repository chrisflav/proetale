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
    (Presieve.ofArrows 𝒰.X 𝒰.f).pullbackArrows f =
      .ofArrows (𝒰.pullbackCover' f).X (𝒰.pullbackCover' f).f := by
  rw [← Presieve.ofArrows_pullback]
  rfl

variable [P.IsMultiplicative]

@[simp]
lemma Cover.generate_ofArrows_mem_grothendieckTopology {S : Scheme.{u}} (𝒰 : Cover.{v} P S) :
    .generate (.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.grothendieckTopology P S := by
  let 𝒱 : Cover.{u} P S := 𝒰.ulift
  apply GrothendieckTopology.superset_covering _ (S := Sieve.ofArrows _ 𝒱.f) _
  · rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
    exact ⟨.ofArrows 𝒱.X 𝒱.f, ⟨𝒱, rfl⟩, Sieve.le_generate _⟩
  · rw [Sieve.ofArrows]
    apply Sieve.generate_mono
    rintro - - ⟨i⟩
    use 𝒰.idx i

lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] :
    ⊥ ∈ Scheme.grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  let 𝒰 : Cover.{u} P X :=
    { I₀ := PEmpty
      X := PEmpty.elim
      f i := i.elim
      idx x := (IsEmpty.false x).elim
      covers x := (IsEmpty.false x).elim
      map_prop x := x.elim }
  have : Presieve.ofArrows 𝒰.X 𝒰.f = ⊥ := by
    rw [eq_bot_iff]
    rintro - - ⟨i⟩
    exact i.elim
  rw [← this]
  exact 𝒰.generate_ofArrows_mem_grothendieckTopology

lemma Cover.ofArrows_of_unique {S : Scheme.{u}} (𝒰 : S.Cover P) [Unique 𝒰.I₀] :
    Presieve.ofArrows 𝒰.X 𝒰.f = Presieve.singleton (𝒰.f default) :=
  sorry

end AlgebraicGeometry.Scheme
