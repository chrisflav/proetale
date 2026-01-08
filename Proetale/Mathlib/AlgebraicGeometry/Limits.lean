import Mathlib.AlgebraicGeometry.Limits

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry

instance : HasFiniteCoproducts Scheme.{u} where
  out := inferInstance

lemma isInitial_iff_isEmpty {X : Scheme.{u}} : Nonempty (IsInitial X) ↔ IsEmpty X :=
  ⟨fun ⟨h⟩ ↦ (h.uniqueUpToIso specPunitIsInitial).hom.homeomorph.isEmpty,
    fun _ ↦ ⟨isInitialOfIsEmpty⟩⟩

instance : IsEmpty (⊥_ Scheme) := by
  rw [← isInitial_iff_isEmpty]
  exact ⟨initialIsInitial⟩

private lemma isEmpty_of_commSq_sigmaι_of_ne_aux {ι : Type u} {X : ι → Scheme.{u}}
    {i j : ι} {Z : Scheme.{u}} {f : Z ⟶ X i} {g : Z ⟶ X j}
    (h : CommSq f g (Sigma.ι X i) (Sigma.ι X j)) (hij : i ≠ j) :
    IsEmpty Z := by
  refine ⟨fun z ↦ ?_⟩
  fapply eq_bot_iff.mp <| disjoint_iff.mp <| disjoint_opensRange_sigmaι X i j hij
  · exact (f ≫ Sigma.ι X i).base z
  · refine ⟨⟨f.base z, rfl⟩, ⟨g.base z, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, h.w]

lemma isEmpty_of_commSq_sigmaι_of_ne {ι : Type v} [Small.{u} ι] {X : ι → Scheme.{u}}
    {i j : ι} {Z : Scheme.{u}} {f : Z ⟶ X i} {g : Z ⟶ X j}
    (h : CommSq f g (Sigma.ι X i) (Sigma.ι X j)) (hij : i ≠ j) :
    IsEmpty Z := by
  let e := equivShrink ι
  refine isEmpty_of_commSq_sigmaι_of_ne_aux (X := X ∘ e.symm) (i := e i) (j := e j)
    (f := f ≫ eqToHom (by simp)) (g := g ≫ eqToHom (by simp)) ⟨?_⟩ (by simp [hij])
  simp [← Sigma.ι_reindex_inv, h.1]

lemma isEmpty_pullback_sigmaι_of_ne {ι : Type u} (X : ι → Scheme.{u})
    {i j : ι} (hij : i ≠ j) :
    IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) :=
  isEmpty_of_commSq_sigmaι_of_ne ⟨pullback.condition⟩ hij

/-- The cover of `∐ X` by the `Xᵢ`. -/
@[simps!]
noncomputable def sigmaOpenCover' {ι : Type*} [Small.{u} ι] (X : ι → Scheme.{u}) :
    (∐ X).OpenCover :=
  (Scheme.IsLocallyDirected.openCover (Discrete.functor X)).copy ι X (Sigma.ι _)
  (discreteEquiv.symm) (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

end AlgebraicGeometry
