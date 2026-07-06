/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.ContinuousComparison
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.SequentialLimit

/-!
# The canonical map from cohomology of a limit to the limit of cohomologies

For `Z : A` and an inverse system `G : ℕᵒᵖ ⥤ A` in an abelian category with `Ext`-groups,
the limit projections induce a canonical map

`extLimitToLimit : Ext Z (limit G) m ⟶ limit (n ↦ Ext Z (Gₙ) m)`.

In degree `0` this map is bijective by the universal property of the limit
(`bijective_extLimitToLimit_zero`). In positive degrees it is in general neither
injective nor surjective (the failure is a `lim¹`-term, Jannsen); we prove that it *is*
bijective for the systems relevant to the `ℓ`-adic comparison: for
`G = F ⋙ ν^*` the pullback of a system `F` of abelian sheaves on the small étale site
of a scheme `S` with epimorphic transition maps, and `Z` the constant pro-étale sheaf
`ℤ`, the map is bijective in degree `i + 1` under the Mittag-Leffler condition for the
degree-`i` level system
(`AlgebraicGeometry.Scheme.ProEt.bijective_extLimitToLimit_of_isMittagLeffler`).

This is the canonical-map refinement of
`AlgebraicGeometry.Scheme.nonempty_continuousH_addEquiv_H_limit`
(`Proetale/Topology/Comparison/ContinuousComparison.lean`) combined with
`CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`
(`Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/SequentialLimit.lean`): instead
of comparing both sides abstractly with continuous étale cohomology `Ext (Δℤ) F`, we
compare them directly by a fused dimension-shifting argument, keeping track of the
canonical map. The connecting-map ladders on the source side are provided by
`ShortComplex.ShortExact.extClass_naturality` applied to the limit projections, which
constitute a morphism of short complexes from the limit sequence to each level sequence
(`extLimitToLimit_levelDelta`).
-/

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Abelian.Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

section Def

variable (Z : A) (G : ℕᵒᵖ ⥤ A) [HasLimit G]

/-- The canonical comparison map from the `Ext`-groups into a limit to the limit of the
levelwise `Ext`-groups, induced by the limit projections. -/
noncomputable def extLimitToLimit (m : ℕ) :
    AddCommGrpCat.of (Ext Z (limit G) m) ⟶ limit (levelSystem Z G m) :=
  limit.lift _ ((extFunctorObj Z m).mapCone (limit.cone G))

@[reassoc (attr := simp)]
lemma extLimitToLimit_π (m : ℕ) (k : ℕᵒᵖ) :
    extLimitToLimit Z G m ≫ limit.π (levelSystem Z G m) k =
      (extFunctorObj Z m).map (limit.π G k) :=
  limit.lift_π _ _

variable {Z G} in
/-- The components of the canonical comparison map are postcomposition with the limit
projections. -/
lemma π_extLimitToLimit_apply (m : ℕ) (k : ℕᵒᵖ) (x : Ext Z (limit G) m) :
    ConcreteCategory.hom (limit.π (levelSystem Z G m) k)
      (ConcreteCategory.hom (extLimitToLimit Z G m) x) =
      x.comp (Ext.mk₀ (limit.π G k)) (add_zero m) :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (extLimitToLimit_π Z G m k) x)

variable {G} in
/-- Naturality of the canonical comparison map: postcomposition with `limMap τ`
corresponds to the limit of the levelwise postcompositions. -/
lemma extLimitToLimit_limMap {G' : ℕᵒᵖ ⥤ A} [HasLimit G'] (τ : G ⟶ G')
    (m : ℕ) (x : Ext Z (limit G) m) :
    ConcreteCategory.hom (limMap (Functor.whiskerRight τ (extFunctorObj Z m)))
        (ConcreteCategory.hom (extLimitToLimit Z G m) x) =
      ConcreteCategory.hom (extLimitToLimit Z G' m)
        (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)) := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  have h1 : ConcreteCategory.hom (limit.π (G' ⋙ extFunctorObj Z m) k)
      (ConcreteCategory.hom (limMap (Functor.whiskerRight τ (extFunctorObj Z m)))
        (ConcreteCategory.hom (extLimitToLimit Z G m) x)) =
      ConcreteCategory.hom ((Functor.whiskerRight τ (extFunctorObj Z m)).app k)
        (ConcreteCategory.hom (limit.π (levelSystem Z G m) k)
          (ConcreteCategory.hom (extLimitToLimit Z G m) x)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom
        (limMap_π (Functor.whiskerRight τ (extFunctorObj Z m)) k) _).trans
        (ConcreteCategory.comp_apply _ _ _))
  have h2 : ConcreteCategory.hom (limit.π (G' ⋙ extFunctorObj Z m) k)
      (ConcreteCategory.hom (extLimitToLimit Z G' m)
        (x.comp (Ext.mk₀ (limMap τ)) (add_zero m))) =
      (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)).comp
        (Ext.mk₀ (limit.π G' k)) (add_zero m) :=
    π_extLimitToLimit_apply m k _
  rw [h1, h2, π_extLimitToLimit_apply]
  calc ConcreteCategory.hom ((Functor.whiskerRight τ (extFunctorObj Z m)).app k)
        (x.comp (Ext.mk₀ (limit.π G k)) (add_zero m))
      = (x.comp (Ext.mk₀ (limit.π G k)) (add_zero m)).comp
          (Ext.mk₀ (τ.app k)) (add_zero m) := rfl
    _ = x.comp ((Ext.mk₀ (limit.π G k)).comp (Ext.mk₀ (τ.app k)) (add_zero 0))
          (add_zero m) := Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = x.comp (Ext.mk₀ (limMap τ ≫ limit.π G' k)) (add_zero m) := by
        rw [Ext.mk₀_comp_mk₀, ← limMap_π]
    _ = x.comp ((Ext.mk₀ (limMap τ)).comp (Ext.mk₀ (limit.π G' k)) (add_zero 0))
          (add_zero m) := by rw [Ext.mk₀_comp_mk₀]
    _ = (x.comp (Ext.mk₀ (limMap τ)) (add_zero m)).comp
          (Ext.mk₀ (limit.π G' k)) (add_zero m) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

/-- The transition maps of the degree-zero level system of a system with split
epimorphic transition maps are surjective, by composing with the splittings. -/
lemma surjective_transition_levelSystem_of_isSplitEpi (G : ℕᵒᵖ ⥤ A)
    (hG : ∀ n, IsSplitEpi (SequentialSystem.transition G n)) (n : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      (SequentialSystem.transition (levelSystem Z G 0) n)) := by
  obtain ⟨σ⟩ := (hG n).exists_splitEpi
  intro y
  refine ⟨y.comp (Ext.mk₀ σ.section_) (add_zero 0), ?_⟩
  have h1 : ConcreteCategory.hom (SequentialSystem.transition (levelSystem Z G 0) n)
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)) =
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)).comp
        (Ext.mk₀ (SequentialSystem.transition G n)) (add_zero 0) := rfl
  rw [h1, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, σ.id, Ext.comp_mk₀_id]

end Def

section Zero

variable (Z : A) (G : ℕᵒᵖ ⥤ A) [HasLimit G]

/-- **In degree `0`, the canonical comparison map is bijective**: a compatible family of
morphisms `Z ⟶ Gₙ` is the same as a morphism into the limit. -/
lemma bijective_extLimitToLimit_zero :
    Function.Bijective (ConcreteCategory.hom (extLimitToLimit Z G 0)) := by
  constructor
  · intro x y hxy
    obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective Z (limit G)).2 x
    obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective Z (limit G)).2 y
    suffices h : φ = ψ by rw [h]
    apply limit.hom_ext
    intro k
    apply (Ext.mk₀_bijective Z (G.obj k)).1
    have hk := congrArg (ConcreteCategory.hom (limit.π (levelSystem Z G 0) k)) hxy
    rw [π_extLimitToLimit_apply, π_extLimitToLimit_apply, Ext.mk₀_comp_mk₀,
      Ext.mk₀_comp_mk₀] at hk
    exact hk
  · intro t
    set φ : ∀ k : ℕᵒᵖ, Z ⟶ G.obj k := fun k ↦
      Ext.homEquiv₀ (ConcreteCategory.hom (limit.π (levelSystem Z G 0) k) t)
      with hφdef
    have hmk : ∀ k : ℕᵒᵖ, Ext.mk₀ (φ k) =
        ConcreteCategory.hom (limit.π (levelSystem Z G 0) k) t := fun k ↦
      Ext.homEquiv₀.symm_apply_apply _
    have hφ : ∀ {k k' : ℕᵒᵖ} (f : k ⟶ k'), φ k ≫ G.map f = φ k' := by
      intro k k' f
      apply (Ext.mk₀_bijective Z (G.obj k')).1
      have hw := ConcreteCategory.congr_hom (limit.w (levelSystem Z G 0) f) t
      calc Ext.mk₀ (φ k ≫ G.map f)
          = (Ext.mk₀ (φ k)).comp (Ext.mk₀ (G.map f)) (add_zero 0) :=
            (Ext.mk₀_comp_mk₀ _ _).symm
        _ = ConcreteCategory.hom ((levelSystem Z G 0).map f)
              (ConcreteCategory.hom (limit.π (levelSystem Z G 0) k) t) := by
            rw [hmk k]; rfl
        _ = ConcreteCategory.hom (limit.π (levelSystem Z G 0) k ≫
              (levelSystem Z G 0).map f) t := (ConcreteCategory.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom (limit.π (levelSystem Z G 0) k') t := hw
        _ = Ext.mk₀ (φ k') := (hmk k').symm
    refine ⟨Ext.mk₀ (limit.lift G
      { pt := Z
        π := { app := φ, naturality := fun k k' f ↦ by simpa using (hφ f).symm } }), ?_⟩
    refine Concrete.limit_ext _ _ _ fun k ↦ ?_
    rw [π_extLimitToLimit_apply, Ext.mk₀_comp_mk₀, limit.lift_π]
    exact hmk k

end Zero

section Delta

variable [HasLimitsOfShape ℕᵒᵖ A]

variable (Z : A) {T : ShortComplex (ℕᵒᵖ ⥤ A)}

/-- The limit projections constitute a morphism of short complexes from the limit
sequence to each level sequence. -/
noncomputable def limitπShortComplexHom (T : ShortComplex (ℕᵒᵖ ⥤ A)) (k : ℕᵒᵖ) :
    T.map lim ⟶ T.map ((evaluation ℕᵒᵖ A).obj k) :=
  ShortComplex.homMk (limit.π T.X₁ k) (limit.π T.X₂ k) (limit.π T.X₃ k)
    (limMap_π T.f k).symm (limMap_π T.g k).symm

/-- **The canonical comparison map intertwines the connecting maps**: for a short exact
sequence `T` of inverse systems which is levelwise short exact and whose limit sequence
is short exact, postcomposition with the extension class of the limit sequence followed
by the canonical comparison map agrees with the canonical comparison map followed by
the limit of the levelwise connecting maps. -/
lemma extLimitToLimit_levelDelta
    (hTk : ∀ k : ℕᵒᵖ, (T.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact)
    (hTL : (T.map lim).ShortExact) (m : ℕ) (x : Ext Z (limit T.X₃) m) :
    ConcreteCategory.hom (limMap (levelDelta Z hTk m))
        (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x) =
      ConcreteCategory.hom (extLimitToLimit Z T.X₁ (m + 1))
        (x.comp hTL.extClass rfl) := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  have h1 : ConcreteCategory.hom (limit.π (levelSystem Z T.X₁ (m + 1)) k)
      (ConcreteCategory.hom (limMap (levelDelta Z hTk m))
        (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x)) =
      ConcreteCategory.hom ((levelDelta Z hTk m).app k)
        (ConcreteCategory.hom (limit.π (levelSystem Z T.X₃ m) k)
          (ConcreteCategory.hom (extLimitToLimit Z T.X₃ m) x)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom (limMap_π (levelDelta Z hTk m) k) _).trans
        (ConcreteCategory.comp_apply _ _ _))
  have hnat : hTL.extClass.comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero 1) =
      (Ext.mk₀ (limit.π T.X₃ k)).comp (hTk k).extClass (zero_add 1) :=
    ShortComplex.ShortExact.extClass_naturality hTL (hTk k) (limitπShortComplexHom T k)
  rw [h1, π_extLimitToLimit_apply, π_extLimitToLimit_apply]
  calc ConcreteCategory.hom ((levelDelta Z hTk m).app k)
        (x.comp (Ext.mk₀ (limit.π T.X₃ k)) (add_zero m))
      = (x.comp (Ext.mk₀ (limit.π T.X₃ k)) (add_zero m)).comp (hTk k).extClass rfl := rfl
    _ = x.comp ((Ext.mk₀ (limit.π T.X₃ k)).comp (hTk k).extClass (zero_add 1)) rfl :=
        Ext.comp_assoc_of_second_deg_zero _ _ _ _
    _ = x.comp (hTL.extClass.comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero 1)) rfl := by
        rw [hnat]
    _ = (x.comp hTL.extClass rfl).comp (Ext.mk₀ (limit.π T.X₁ k)) (add_zero (m + 1)) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

end Delta

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Scheme.ProEt

open CategoryTheory.Abelian

variable {S : Scheme.{u}}

/-- **`Ext` into the limit of a pulled-back system is the limit of the levelwise
`Ext`-groups, under a Mittag-Leffler hypothesis** (the `lim¹`-free case of Jannsen's
exact sequence, in its canonical-map form): for an inverse system `F` of abelian
sheaves on the small étale site of `S` with epimorphic transition maps, the canonical
map from the pro-étale cohomology of `lim ν^*Fₙ` in degree `i + 1` to the inverse limit
of the pro-étale cohomology groups of the `ν^*Fₙ` is bijective, provided the degree-`i`
level system satisfies the Mittag-Leffler condition. -/
theorem bijective_extLimitToLimit_of_isMittagLeffler
    (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (hF : ∀ n, Epi (SequentialSystem.transition F n)) (i : ℕ)
    (hML : (((F ⋙ ProEt.sheafPullback S Ab.{u + 1}) ⋙
      extFunctorObj (proetaleConstantUnit S) i) ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler) :
    Function.Bijective (ConcreteCategory.hom (Ext.extLimitToLimit
      (proetaleConstantUnit S) (F ⋙ ProEt.sheafPullback S Ab.{u + 1}) (i + 1))) := by
  -- Fused dimension shift: canonical-map refinement of
  -- `nonempty_continuousH_addEquiv_H_limit` composed with
  -- `Ext.nonempty_addEquiv_limit_levelSystem`. Dimension shifting along
  -- `0 → F → I → Q → 0`, with the connecting ladders on the source side provided by
  -- `Ext.extLimitToLimit_levelDelta` and on the target side by `Ext.levelDelta`.
  induction i generalizing F with
  | zero =>
    -- Setup: the short exact sequence `0 → F → I → Q → 0` and its pullback `T`.
    let SC : ShortComplex (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    let T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) :=
      SC.map ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1}))
    have hTk : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI := comp_preservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      haveI := comp_preservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      exact hSC.map_of_exact ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k ⋙ ProEt.sheafPullback S Ab.{u + 1})
    have hX₁ : ∀ n, Epi (SequentialSystem.transition T.X₁ n) := by
      intro n
      haveI : (ProEt.sheafPullback S Ab.{u + 1}).PreservesEpimorphisms :=
        Functor.preservesEpimorphisms_of_adjunction (ProEt.sheafAdjunction S Ab.{u + 1})
      exact SequentialSystem.epi_transition_whisker (ProEt.sheafPullback S Ab.{u + 1}) hF n
    have hTL : (T.map lim).ShortExact := shortExact_limMap hTk hX₁
    have hsplit : ∀ n, IsSplitEpi (SequentialSystem.transition T.X₂ n) := fun n ↦ by
      haveI := SequentialSystem.isSplitEpi_transition_of_injective SC.X₂ n
      exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
        (SequentialSystem.transition SC.X₂ n)))
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton
        (Ext (proetaleConstantUnit S) (T.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_H_sheafPullback_injective (SC.X₂.obj k) (q + 1) q.succ_pos
    have h₂lim : ∀ q, 0 < q → Subsingleton
        (Sheaf.H (limit (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})) q) := by
      refine subsingleton_H_limit_of_isSplitEpi _ (fun n ↦ ?_) (fun k q hq ↦ ?_)
      · haveI := SequentialSystem.isSplitEpi_transition_of_injective (Injective.under F) n
        exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
          (SequentialSystem.transition (Injective.under F) n)))
      · haveI : Injective ((Injective.under F).obj k) :=
          SequentialSystem.injective_obj_of_injective (Injective.under F) k.unop
        exact subsingleton_H_sheafPullback_injective ((Injective.under F).obj k) q hq
    -- The Mittag-Leffler exchange of limit and cokernel on the level systems.
    obtain ⟨hsurjL, hexactL⟩ := Ext.surjective_limMap_and_exact
      (Functor.whiskerRight T.g (extFunctorObj (proetaleConstantUnit S) 0))
      (Ext.levelDelta (proetaleConstantUnit S) hTk 0)
      (Ext.levelDelta_comp_app_zero (proetaleConstantUnit S) hTk 0)
      (Ext.exists_of_levelDelta_app_eq_zero (proetaleConstantUnit S) hTk 0)
      (fun k ↦ Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk 0 k (hsubk k 0))
      (Ext.surjective_transition_levelSystem_of_isSplitEpi
        (proetaleConstantUnit S) T.X₂ hsplit)
      (Ext.exists_transition_preimage_ker (proetaleConstantUnit S) hTk hML)
    constructor
    · -- Injectivity: a class killed by the canonical map is `δ` of a section which
      -- lifts to the middle object, hence vanishes.
      rw [injective_iff_map_eq_zero]
      intro ξ hξ
      obtain ⟨s, rfl⟩ := Ext.deltaZero_surjective hTL (proetaleConstantUnit S)
        (h₂lim 1 one_pos) ξ
      rw [Ext.deltaZero_apply] at hξ
      have h0 : ConcreteCategory.hom (limMap (Ext.levelDelta (proetaleConstantUnit S)
          hTk 0)) (ConcreteCategory.hom (Ext.extLimitToLimit (proetaleConstantUnit S)
            T.X₃ 0) (Ext.mk₀ s)) = 0 := by
        rw [Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL 0 (Ext.mk₀ s)]
        exact hξ
      obtain ⟨b, hb⟩ := hexactL _ h0
      obtain ⟨w', hw'⟩ := (Ext.bijective_extLimitToLimit_zero
        (proetaleConstantUnit S) T.X₂).2 b
      obtain ⟨w, rfl⟩ := (Ext.mk₀_bijective (proetaleConstantUnit S) (limit T.X₂)).2 w'
      rw [← hw', Ext.extLimitToLimit_limMap (proetaleConstantUnit S) T.g 0 (Ext.mk₀ w),
        Ext.mk₀_comp_mk₀] at hb
      have hs : w ≫ limMap T.g = s :=
        (Ext.mk₀_bijective _ _).1
          ((Ext.bijective_extLimitToLimit_zero (proetaleConstantUnit S) T.X₃).1 hb)
      exact (Ext.deltaZero_apply_eq_zero_iff hTL _ s).2 ⟨w, hs⟩
    · -- Surjectivity: lift through the surjection of limits and the degree-zero
      -- bijectivity, then apply the connecting ladder.
      intro t
      obtain ⟨c, hc⟩ := hsurjL t
      obtain ⟨x, hx⟩ := (Ext.bijective_extLimitToLimit_zero
        (proetaleConstantUnit S) T.X₃).2 c
      refine ⟨x.comp hTL.extClass rfl, ?_⟩
      exact Eq.trans
        (Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL 0 x).symm
        (Eq.trans (congrArg (ConcreteCategory.hom
          (limMap (Ext.levelDelta (proetaleConstantUnit S) hTk 0))) hx) hc)
  | succ i IH =>
    -- Setup as in the base case.
    let SC : ShortComplex (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    let T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) :=
      SC.map ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1}))
    have hTk : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
          (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      haveI := comp_preservesFiniteLimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      haveI := comp_preservesFiniteColimits ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k) (ProEt.sheafPullback S Ab.{u + 1})
      exact hSC.map_of_exact ((CategoryTheory.evaluation ℕᵒᵖ
        (Sheaf S.smallEtaleTopology Ab.{u + 1})).obj k ⋙ ProEt.sheafPullback S Ab.{u + 1})
    have hX₁ : ∀ n, Epi (SequentialSystem.transition T.X₁ n) := by
      intro n
      haveI : (ProEt.sheafPullback S Ab.{u + 1}).PreservesEpimorphisms :=
        Functor.preservesEpimorphisms_of_adjunction (ProEt.sheafAdjunction S Ab.{u + 1})
      exact SequentialSystem.epi_transition_whisker (ProEt.sheafPullback S Ab.{u + 1}) hF n
    have hTL : (T.map lim).ShortExact := shortExact_limMap hTk hX₁
    have hsplit : ∀ n, IsSplitEpi (SequentialSystem.transition T.X₂ n) := fun n ↦ by
      haveI := SequentialSystem.isSplitEpi_transition_of_injective SC.X₂ n
      exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
        (SequentialSystem.transition SC.X₂ n)))
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton
        (Ext (proetaleConstantUnit S) (T.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_H_sheafPullback_injective (SC.X₂.obj k) (q + 1) q.succ_pos
    have h₂lim : ∀ q, 0 < q → Subsingleton
        (Sheaf.H (limit (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})) q) := by
      refine subsingleton_H_limit_of_isSplitEpi _ (fun n ↦ ?_) (fun k q hq ↦ ?_)
      · haveI := SequentialSystem.isSplitEpi_transition_of_injective (Injective.under F) n
        exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
          (SequentialSystem.transition (Injective.under F) n)))
      · haveI : Injective ((Injective.under F).obj k) :=
          SequentialSystem.injective_obj_of_injective (Injective.under F) k.unop
        exact subsingleton_H_sheafPullback_injective ((Injective.under F).obj k) q hq
    -- Transport the Mittag-Leffler hypothesis to the cokernel system at degree `i`.
    have hMLQ : (Ext.levelSystem (proetaleConstantUnit S) T.X₃ i ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).IsMittagLeffler := by
      obtain _ | j := i
      · exact Ext.isMittagLeffler_of_exact
          (Functor.whiskerRight T.g (extFunctorObj (proetaleConstantUnit S) 0))
          (Ext.levelDelta (proetaleConstantUnit S) hTk 0)
          (Ext.exists_of_levelDelta_app_eq_zero (proetaleConstantUnit S) hTk 0)
          (fun k ↦ Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk 0 k
            (hsubk k 0))
          (Ext.surjective_transition_levelSystem_of_isSplitEpi
            (proetaleConstantUnit S) T.X₂ hsplit)
          hML
      · exact Ext.isMittagLeffler_forget_of_app_bijective
          (Ext.levelDelta (proetaleConstantUnit S) hTk (j + 1))
          (fun k ↦ ⟨Ext.injective_levelDelta_app (proetaleConstantUnit S) hTk j k
              (hsubk k j),
            Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk (j + 1) k
              (hsubk k (j + 1))⟩)
          hML
    -- The cokernel system has epimorphic transition maps.
    have hQepi : ∀ n, Epi (SequentialSystem.transition SC.X₃ n) := by
      have hIepi : ∀ n, Epi (SequentialSystem.transition SC.X₂ n) := fun n ↦
        haveI := SequentialSystem.isSplitEpi_transition_of_injective
          (Injective.under F) n
        inferInstanceAs (Epi (SequentialSystem.transition (Injective.under F) n))
      haveI : Epi SC.g := inferInstanceAs (Epi (cokernel.π (Injective.ι F)))
      exact SequentialSystem.epi_transition_of_epi_app SC.g (fun k ↦ inferInstance) hIepi
    have hbij3 := IH SC.X₃ hQepi hMLQ
    -- The connecting maps are bijective on both sides.
    have hconn : Function.Bijective (fun x : Ext (proetaleConstantUnit S)
        (limit T.X₃) (i + 1) ↦ x.comp hTL.extClass rfl) :=
      (Ext.connectingEquiv hTL (proetaleConstantUnit S) i
        (h₂lim (i + 1) i.succ_pos) (h₂lim (i + 2) (by omega))).bijective
    haveI : ∀ k, IsIso ((Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)).app k) := by
      intro k
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨Ext.injective_levelDelta_app (proetaleConstantUnit S) hTk i k (hsubk k i),
        Ext.surjective_levelDelta_app (proetaleConstantUnit S) hTk (i + 1) k
          (hsubk k (i + 1))⟩
    haveI : IsIso (Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)) :=
      NatIso.isIso_of_isIso_app _
    have hlimδ : Function.Bijective (ConcreteCategory.hom
        (limMap (Ext.levelDelta (proetaleConstantUnit S) hTk (i + 1)))) :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    -- Conclude via the commuting square `Ext.extLimitToLimit_levelDelta`.
    have hsq : (ConcreteCategory.hom (Ext.extLimitToLimit (proetaleConstantUnit S)
        T.X₁ (i + 2))) ∘ (fun x : Ext (proetaleConstantUnit S) (limit T.X₃) (i + 1) ↦
          x.comp hTL.extClass rfl) =
        (ConcreteCategory.hom (limMap (Ext.levelDelta (proetaleConstantUnit S)
          hTk (i + 1)))) ∘ (ConcreteCategory.hom (Ext.extLimitToLimit
            (proetaleConstantUnit S) T.X₃ (i + 1))) :=
      funext fun x ↦
        (Ext.extLimitToLimit_levelDelta (proetaleConstantUnit S) hTk hTL (i + 1) x).symm
    have hcomp : Function.Bijective ((ConcreteCategory.hom
        (Ext.extLimitToLimit (proetaleConstantUnit S) T.X₁ (i + 2))) ∘
        (fun x : Ext (proetaleConstantUnit S) (limit T.X₃) (i + 1) ↦
          x.comp hTL.extClass rfl)) := by
      rw [hsq]
      exact hlimδ.comp hbij3
    exact (Function.Bijective.of_comp_iff _ hconn).mp hcomp

end AlgebraicGeometry.Scheme.ProEt
