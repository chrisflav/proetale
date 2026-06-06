import Mathlib.CategoryTheory.Limits.HasLimits

namespace CategoryTheory
open Limits
variable {C : Type*} [Category* C]

class IsReplete (C : Type*) [Category* C] : Prop where
  epi_pi_app_of_forall_epi_map (F : ℕᵒᵖ ⥤ C)
    (hF : ∀ (n : ℕ), Epi <| F.map ((homOfLE (n.le_succ)).op))
    (c : Cone F) (hc : IsLimit c) (n : ℕ) : Epi (c.π.app (.op n))

end CategoryTheory
