import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

-- TODO: this file has the wrong name

namespace CategoryTheory.Limits

/-- The assumption on `X` is in particular satisfied if `X` is finitely presentable
and `J` is a small filtered category. -/
lemma exists_hom_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))] (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (.op X)) hc) f

lemma exists_eq_of_preservesColimit_coyoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (.op X)) hc)).mp h

lemma exists_eq_of_preservesColimit_coyoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C}
    [PreservesColimit D (coyoneda.obj (.op X))]
    {i : J} (f g : X ⟶ D.obj i) (h : f ≫ c.ι.app i = g ≫ c.ι.app i) :
    ∃ (j : J) (a : i ⟶ j), f ≫ D.map a = g ≫ D.map a := by
  obtain ⟨j, u, v, heq⟩ := exists_eq_of_preservesColimit_coyoneda hc f g h
  use IsFiltered.coeq u v, u ≫ IsFiltered.coeqHom u v
  rw [Functor.map_comp, reassoc_of% heq, ← Functor.map_comp, ← IsFiltered.coeq_condition]
  simp

lemma exists_hom_of_preservesColimit_yoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)] (f : c.pt ⟶ X) :
    ∃ (j : J) (p : D.obj j ⟶ X), c.π.app j ≫ p = f := by
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (yoneda.obj X) hc.op) f
  use j.unop, p, hp

lemma exists_eq_of_preservesColimit_yoneda {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsCofiltered J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)]
    {i j : J} (f : D.obj i ⟶ X) (g : D.obj j ⟶ X) (h : c.π.app i ≫ f = c.π.app j ≫ g) :
    ∃ (k : J) (u : k ⟶ i) (v : k ⟶ j), D.map u ≫ f = D.map v ≫ g := by
  obtain ⟨k, u, v, huv⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (yoneda.obj X) hc.op)).mp h
  use k.unop, u.unop, v.unop, huv

lemma exists_eq_of_preservesColimit_yoneda_self {C : Type*} [Category* C] {J : Type*}
    [Category* J] [IsCofiltered J] {D : J ⥤ C} {c : Cone D} (hc : IsLimit c) {X : C}
    [PreservesColimit D.op (yoneda.obj X)]
    {i : J} (f g : D.obj i ⟶ X) (h : c.π.app i ≫ f = c.π.app i ≫ g) :
    ∃ (j : J) (a : j ⟶ i), D.map a ≫ f = D.map a ≫ g := by
  obtain ⟨j, u, v, heq⟩ := exists_eq_of_preservesColimit_yoneda hc f g h
  use IsCofiltered.eq u v, IsCofiltered.eqHom u v ≫ u
  rw [Functor.map_comp, Category.assoc, heq, ← Functor.map_comp, IsCofiltered.eq_condition]
  simp

end CategoryTheory.Limits
