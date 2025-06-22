import Mathlib.CategoryTheory.Extensive

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

-- in PR #26186
/-- If `C` has pullbacks and is finitary (pre-)extensive, pullbacks distribute over finite
coproducts, i.e., `∐ (Xᵢ ×[S] Xⱼ) ≅ (∐ Xᵢ) ×[S] (∐ Xⱼ)`. -/
instance FinitaryPreExtensive.isIso_sigmaDesc_map [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι → C} {Y : ι' → C}
    (f : ∀ i, X i ⟶ S) (g : ∀ i, Y i ⟶ S) :
    IsIso (Sigma.desc fun (p : ι × ι') ↦
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)) :=
  sorry

end CategoryTheory
