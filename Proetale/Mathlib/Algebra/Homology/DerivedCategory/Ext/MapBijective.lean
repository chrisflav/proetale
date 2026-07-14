/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Bijections between Ext groups without preservation of injective objects

In `Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean` it is shown that the maps
between `Ext`-groups induced by a fully faithful exact functor `F : C ⥤ D` between abelian
categories are bijective if `C` has enough injectives and `F` preserves injective objects.

In this file we relax the hypothesis that `F` preserves injective objects: it suffices that
images of injective objects are *relatively acyclic*, i.e. all higher `Ext`-groups out of
images of `F` into images of injective objects vanish
(`Functor.mapExt_bijective_of_subsingleton_ext_injective`). Moreover, by a dimension shifting
argument, this vanishing only needs to be checked on a class of objects admitting epimorphisms
onto every object of `C` (`Functor.mapExt_bijective_of_exists_epi`). This applies for example
to pullback functors of sites, which in general do not preserve injective objects.
-/

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

attribute [local instance] Ext.subsingleton_of_injective in
/-- Variant of `Functor.mapExt_bijective_of_preservesInjectiveObjects` where instead of
preservation of injectives one assumes that images of injective objects are "relatively
acyclic": all higher Ext groups out of images of `F` into them vanish. This applies e.g. to
pullback functors of sites which do not preserve injectives. -/
lemma Functor.mapExt_bijective_of_subsingleton_ext_injective
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    (hacyc : ∀ (X I : C), Injective I → ∀ (n : ℕ),
      Subsingleton (Ext (F.obj X) (F.obj I) (n + 1)))
    (X Y : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using ⟨Faithful.map_injective, Full.map_surjective⟩
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n) (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map F) y₁
        ((hacyc X I.J I.injective n).elim _ _) rfl)

/-- Variant of `Functor.mapExt_bijective_of_subsingleton_ext_injective` where relative
acyclicity of images of injective objects only needs to be checked against a class of
"relatively acyclic" objects admitting epimorphisms onto every object of `C`. -/
lemma Functor.mapExt_bijective_of_exists_epi
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Full] [F.Faithful] [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    (hP : ∀ X : C, ∃ (P : C) (π : P ⟶ X), Epi π ∧ ∀ (I : C), Injective I → ∀ (n : ℕ),
      Subsingleton (Ext (F.obj P) (F.obj I) (n + 1)))
    (X Y : C) (n : ℕ) : Function.Bijective (F.mapExtAddHom X Y n) := by
  refine F.mapExt_bijective_of_subsingleton_ext_injective ?_ X Y n
  intro X I hI n
  haveI := hI
  induction n generalizing X with
  | zero =>
    obtain ⟨P, π, hπ, hPacyc⟩ := hP X
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    let S := ShortComplex.mk (Limits.kernel.ι π) π (Limits.kernel.condition π)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_kernel π
        mono_f := inferInstanceAs (Mono (Limits.kernel.ι π))
        epi_g := hπ }
    obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ (hS.map F) (F.obj I) x
      ((hPacyc I hI 0).elim _ _) (add_comm 1 0)
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (F.obj (Limits.kernel π)) (F.obj I)).2 x₁
    obtain ⟨g', rfl⟩ := F.map_surjective g
    have hfac : Ext.mk₀ (F.map g') = (Ext.mk₀ (F.map (Limits.kernel.ι π))).comp
        (Ext.mk₀ (F.map (Injective.factorThru g' (Limits.kernel.ι π)))) (zero_add 0) := by
      rw [Ext.mk₀_comp_mk₀, ← F.map_comp, Injective.comp_factorThru]
    rw [← hx₁, hfac]
    exact (hS.map F).extClass_comp_assoc _
  | succ n hn =>
    obtain ⟨P, π, hπ, hPacyc⟩ := hP X
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    let S := ShortComplex.mk (Limits.kernel.ι π) π (Limits.kernel.condition π)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_kernel π
        mono_f := inferInstanceAs (Mono (Limits.kernel.ι π))
        epi_g := hπ }
    obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ (hS.map F) (F.obj I) x
      ((hPacyc I hI (n + 1)).elim _ _) (add_comm 1 (n + 1))
    rw [← hx₁, (hn (Limits.kernel π)).elim x₁ 0, Ext.comp_zero]

end CategoryTheory
