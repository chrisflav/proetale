/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.Product
import Proetale.Mathlib.CategoryTheory.Abelian.SequentialSystem
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.Limits

/-!
# `Ext` out of a constant system versus the limit of levelwise `Ext`-groups

Let `A` be an abelian category with enough injectives and countable products, and let
`Z : A`. For an inverse system `F : ℕᵒᵖ ⥤ A` we compare the `Ext`-groups
`Ext (Δ Z) F i` in the category of inverse systems (the right derived functors of
`F ↦ lim Hom(Z, Fₙ)`, e.g. continuous étale cohomology) with the inverse limit of the
levelwise `Ext`-groups `Ext Z Fₙ i`.

In general the two differ by a `lim¹`-term (Jannsen). We prove the comparison
isomorphism in degree `0` unconditionally, and in degree `i + 1` under the
Mittag-Leffler-type hypothesis that the transition maps of the degree-`i` levelwise
`Ext`-system are surjective (which forces the relevant `lim¹` to vanish):

- `CategoryTheory.Abelian.Ext.zeroAddEquivLimitLevelSystem`
- `CategoryTheory.Abelian.Ext.nonempty_addEquiv_limit_levelSystem`

The proof is by dimension shifting along `0 → F → I → Q → 0` with `I` injective: the
degree-one case is an explicit Mittag-Leffler correction argument for the four-term
exact sequences of systems `0 → Hom(Z,F•) → Hom(Z,I•) → Hom(Z,Q•) → Ext¹(Z,F•) → 0`
(using that the transition maps of `Hom(Z,I•)` are split surjections), and the
inductive step uses the connecting isomorphisms on both sides, with naturality in the
system direction provided by `ShortComplex.ShortExact.extClass_naturality`.
-/

universe w t v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Abelian.Ext

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A] [HasExt.{w} (ℕᵒᵖ ⥤ A)]

/-- Limits of `ℕᵒᵖ`-shaped diagrams of abelian groups, registered explicitly. -/
instance : HasLimitsOfShape ℕᵒᵖ AddCommGrpCat.{w} := inferInstance

section LevelSystem

variable (Z : A) (F : ℕᵒᵖ ⥤ A)

/-- The inverse system of levelwise `Ext`-groups `n ↦ Ext Z (F.obj (op n)) i`. -/
noncomputable def levelSystem (i : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{w} :=
  F ⋙ extFunctorObj Z i

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
lemma levelSystem_map_apply (i : ℕ) {k k' : ℕᵒᵖ} (f : k ⟶ k') (x : Ext Z (F.obj k) i) :
    ConcreteCategory.hom ((levelSystem Z F i).map f) x = x.comp (Ext.mk₀ (F.map f)) (add_zero i) :=
  rfl

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
/-- The componentwise `mk₀`-classes of a morphism of systems `Δ Z ⟶ F` form a section
of the degree-zero level system. -/
private lemma mk₀_app_mem_sections (φ : (Functor.const ℕᵒᵖ).obj Z ⟶ F) :
    (fun k : ℕᵒᵖ ↦ (Ext.mk₀ (φ.app k) : Ext Z (F.obj k) 0)) ∈
      (levelSystem Z F 0 ⋙ CategoryTheory.forget AddCommGrpCat.{w}).sections := by
  intro k k' f
  have h3 : φ.app k ≫ F.map f = φ.app k' := by
    simpa using (φ.naturality f).symm
  have h1 : ConcreteCategory.hom ((levelSystem Z F 0).map f) (Ext.mk₀ (φ.app k)) =
      (Ext.mk₀ (φ.app k)).comp (Ext.mk₀ (F.map f)) (add_zero 0) :=
    levelSystem_map_apply 0 f _
  have h2 : (Ext.mk₀ (φ.app k)).comp (Ext.mk₀ (F.map f)) (add_zero 0) =
      Ext.mk₀ (φ.app k ≫ F.map f) := Ext.mk₀_comp_mk₀ _ _
  exact h1.trans (h2.trans (by rw [h3]))

variable {Z F} in
/-- The element of the limit of the degree-zero level system associated to a morphism
of systems `Δ Z ⟶ F`. -/
private noncomputable def toLimitLevelZero (φ : (Functor.const ℕᵒᵖ).obj Z ⟶ F) :
    ToType (limit (levelSystem Z F 0)) :=
  (Types.isLimitEquivSections (isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w})
    (limit.isLimit (levelSystem Z F 0)))).symm ⟨_, mk₀_app_mem_sections φ⟩

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
private lemma π_toLimitLevelZero (φ : (Functor.const ℕᵒᵖ).obj Z ⟶ F) (k : ℕᵒᵖ) :
    ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero φ) =
      Ext.mk₀ (φ.app k) :=
  Types.isLimitEquivSections_symm_apply
    (isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w})
      (limit.isLimit (levelSystem Z F 0))) _ k

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
private lemma toLimitLevelZero_bijective :
    Function.Bijective (toLimitLevelZero (Z := Z) (F := F)) := by
  constructor
  · intro φ ψ hφψ
    ext k
    apply (Ext.mk₀_bijective Z (F.obj k)).1
    have h1 : ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero φ) =
        ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero ψ) := by
      rw [hφψ]
    exact (π_toLimitLevelZero φ k).symm.trans (h1.trans (π_toLimitLevelZero ψ k))
  · intro t
    set app : ∀ n : ℕ, Z ⟶ F.obj (op n) := fun n ↦
      Ext.addEquiv₀ (ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op n)) t) with happ
    have hcomp : ∀ n, app (n + 1) ≫ SequentialSystem.transition F n = app n := by
      intro n
      apply (Ext.mk₀_bijective Z (F.obj (op n))).1
      have e1 : Ext.mk₀ (app (n + 1)) =
          ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op (n + 1))) t :=
        Ext.mk₀_addEquiv₀_apply _
      have e2 : ConcreteCategory.hom
          ((levelSystem Z F 0).map (homOfLE (Nat.le_succ n)).op)
          (ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op (n + 1))) t) =
          ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op n)) t :=
        (ConcreteCategory.comp_apply _ _ _).symm.trans
          (ConcreteCategory.congr_hom
            (limit.w (levelSystem Z F 0) (homOfLE (Nat.le_succ n)).op) t)
      calc Ext.mk₀ (app (n + 1) ≫ SequentialSystem.transition F n)
          = (Ext.mk₀ (app (n + 1))).comp
              (Ext.mk₀ (SequentialSystem.transition F n)) (zero_add 0) :=
            (Ext.mk₀_comp_mk₀ _ _).symm
        _ = (ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op (n + 1))) t).comp
              (Ext.mk₀ (SequentialSystem.transition F n)) (zero_add 0) := by rw [e1]
        _ = ConcreteCategory.hom
              ((levelSystem Z F 0).map (homOfLE (Nat.le_succ n)).op)
              (ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op (n + 1))) t) :=
            (levelSystem_map_apply 0 _ _).symm
        _ = ConcreteCategory.hom (limit.π (levelSystem Z F 0) (op n)) t := e2
        _ = Ext.mk₀ (app n) := (Ext.mk₀_addEquiv₀_apply _).symm
    refine ⟨SequentialSystem.natTransOfSucc app hcomp, ?_⟩
    refine Concrete.limit_ext _ _ _ fun k ↦ ?_
    exact (π_toLimitLevelZero _ k).trans (Ext.mk₀_addEquiv₀_apply _)

variable {Z F} in
omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] in
private lemma toLimitLevelZero_add (φ ψ : (Functor.const ℕᵒᵖ).obj Z ⟶ F) :
    toLimitLevelZero (φ + ψ) = toLimitLevelZero φ + toLimitLevelZero ψ := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  calc ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero (φ + ψ))
      = Ext.mk₀ ((φ + ψ).app k) := π_toLimitLevelZero _ k
    _ = Ext.mk₀ (φ.app k) + Ext.mk₀ (ψ.app k) := by
        rw [NatTrans.app_add]; exact Ext.mk₀_add _ _
    _ = ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero φ) +
        ConcreteCategory.hom (limit.π (levelSystem Z F 0) k) (toLimitLevelZero ψ) := by
        rw [π_toLimitLevelZero, π_toLimitLevelZero]
    _ = ConcreteCategory.hom (limit.π (levelSystem Z F 0) k)
          (toLimitLevelZero φ + toLimitLevelZero ψ) := (map_add _ _ _).symm

/-- `Ext (Δ Z) F 0` is the limit of the levelwise `Hom`-groups: a morphism of systems
`Δ Z ⟶ F` is a compatible family of morphisms `Z ⟶ Fₙ`. -/
noncomputable def zeroAddEquivLimitLevelSystem :
    Ext ((Functor.const ℕᵒᵖ).obj Z) F 0 ≃+ ↥(limit (levelSystem Z F 0)) :=
  Ext.addEquiv₀.trans
    { Equiv.ofBijective _ toLimitLevelZero_bijective with
      map_add' := toLimitLevelZero_add }

variable {Z F} in
/-- The components of the image of `zeroAddEquivLimitLevelSystem` under the limit
projections are the `mk₀`-classes of the components of the underlying morphism of
systems. -/
@[simp]
lemma π_zeroAddEquivLimitLevelSystem (x : Ext ((Functor.const ℕᵒᵖ).obj Z) F 0) (k : ℕᵒᵖ) :
    ConcreteCategory.hom (limit.π (levelSystem Z F 0) k)
      (zeroAddEquivLimitLevelSystem Z F x) = Ext.mk₀ ((Ext.addEquiv₀ x).app k) :=
  π_toLimitLevelZero _ k

end LevelSystem

section AbChase

/-! ### Two Mittag-Leffler-type diagram chases for systems of abelian groups -/

variable {B C D : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (g : B ⟶ C) (h : C ⟶ D)

/-- A family of elements of an `ℕᵒᵖ`-indexed system of abelian groups which is
compatible with the successive transition maps assembles into an element of the limit
with the given components. -/
private lemma exists_limit_elem {F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (x : ∀ n : ℕ, ToType (F.obj (op n)))
    (hx : ∀ n, ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1)) = x n) :
    ∃ t : ToType ((limit F : AddCommGrpCat.{w})), ∀ k : ℕᵒᵖ,
      ConcreteCategory.hom (limit.π F k) t = x k.unop := by
  have hxall : ∀ (m n : ℕ) (hmn : m ≤ n),
      ConcreteCategory.hom (F.map (homOfLE hmn).op) (x n) = x m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
      have h1 : (homOfLE (le_refl m)).op = 𝟙 (op m) := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_refl m)).op) (x m)
          = ConcreteCategory.hom (F.map (𝟙 (op m))) (x m) := by rw [h1]
        _ = ConcreteCategory.hom (𝟙 (F.obj (op m))) (x m) := by rw [F.map_id]
        _ = x m := ConcreteCategory.id_apply _
    | succ n hmn ih =>
      have hsplit : (homOfLE (le_trans hmn (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_trans hmn (Nat.le_succ n))).op)
            (x (n + 1))
          = ConcreteCategory.hom
              (F.map ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op)) (x (n + 1)) := by
            rw [hsplit]
        _ = ConcreteCategory.hom
              (F.map (homOfLE (Nat.le_succ n)).op ≫ F.map (homOfLE hmn).op)
              (x (n + 1)) := by
            rw [Functor.map_comp]
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op)
              (ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1))) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op) (x n) := by rw [hx n]
        _ = x m := ih
  have hLF : IsLimit ((CategoryTheory.forget AddCommGrpCat.{w}).mapCone
      (limit.cone F)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w}) (limit.isLimit F)
  have hmemsec : (fun k : ℕᵒᵖ ↦ x k.unop) ∈
      (F ⋙ CategoryTheory.forget AddCommGrpCat.{w}).sections := by
    intro k k' f
    exact hxall k'.unop k.unop (leOfHom f.unop)
  exact ⟨(Types.isLimitEquivSections hLF).symm ⟨fun k ↦ x k.unop, hmemsec⟩,
    fun k ↦ Types.isLimitEquivSections_symm_apply hLF _ k⟩

/-- The components of an element of the limit are compatible with the successive
transition maps. -/
private lemma transition_π_apply {F : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : ToType ((limit F : AddCommGrpCat.{w}))) (n : ℕ) :
    ConcreteCategory.hom (SequentialSystem.transition F n)
      (ConcreteCategory.hom (limit.π F (op (n + 1))) t) =
      ConcreteCategory.hom (limit.π F (op n)) t :=
  (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (limit.w F (homOfLE (Nat.le_succ n)).op) t)

/-- To identify the image of an element under `limMap`, it suffices to identify all of
its components. -/
private lemma limMap_apply_eq {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G)
    (s : ToType ((limit F : AddCommGrpCat.{w})))
    (t : ToType ((limit G : AddCommGrpCat.{w})))
    (hst : ∀ k : ℕᵒᵖ, ConcreteCategory.hom (τ.app k)
      (ConcreteCategory.hom (limit.π F k) s) = ConcreteCategory.hom (limit.π G k) t) :
    ConcreteCategory.hom (limMap τ) s = t := by
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  calc ConcreteCategory.hom (limit.π G k) (ConcreteCategory.hom (limMap τ) s)
      = ConcreteCategory.hom (limMap τ ≫ limit.π G k) s :=
        (ConcreteCategory.comp_apply _ _ _).symm
    _ = ConcreteCategory.hom (limit.π F k ≫ τ.app k) s :=
        ConcreteCategory.congr_hom (limMap_π τ k) s
    _ = ConcreteCategory.hom (τ.app k) (ConcreteCategory.hom (limit.π F k) s) :=
        ConcreteCategory.comp_apply _ _ _
    _ = ConcreteCategory.hom (limit.π G k) t := hst k

/-- **Surjectivity of transitions of a quotient-like term.** Suppose `B ⟶ C ⟶ D` are
maps of inverse systems of abelian groups which are levelwise exact at `C`
(`range g = ker h`), `h` is levelwise surjective, and the transition maps of `B` and of
`D` are surjective. Then the transition maps of `C` are surjective. -/
lemma surjective_transition_of_exact
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hD : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition D n)))
    (n : ℕ) :
    Function.Surjective (ConcreteCategory.hom (SequentialSystem.transition C n)) := by
  intro c
  obtain ⟨d', hd'⟩ := hD n (ConcreteCategory.hom (h.app (op n)) c)
  obtain ⟨c', hc'⟩ := hsurj (op (n + 1)) d'
  have hnat : ConcreteCategory.hom (h.app (op n))
      (ConcreteCategory.hom (SequentialSystem.transition C n) c') =
      ConcreteCategory.hom (h.app (op n)) c := by
    calc ConcreteCategory.hom (h.app (op n))
          (ConcreteCategory.hom (SequentialSystem.transition C n) c')
        = ConcreteCategory.hom (SequentialSystem.transition C n ≫ h.app (op n)) c' :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (h.app (op (n + 1)) ≫ SequentialSystem.transition D n)
            c' :=
          ConcreteCategory.congr_hom (h.naturality (homOfLE (Nat.le_succ n)).op) c'
      _ = ConcreteCategory.hom (SequentialSystem.transition D n)
            (ConcreteCategory.hom (h.app (op (n + 1))) c') :=
          ConcreteCategory.comp_apply _ _ _
      _ = ConcreteCategory.hom (SequentialSystem.transition D n) d' := by rw [hc']
      _ = ConcreteCategory.hom (h.app (op n)) c := hd'
  have hzero : ConcreteCategory.hom (h.app (op n))
      (ConcreteCategory.hom (SequentialSystem.transition C n) c' - c) = 0 := by
    rw [map_sub, hnat, sub_self]
  obtain ⟨b, hb⟩ := hexact (op n) _ hzero
  obtain ⟨b', hb'⟩ := hB n b
  refine ⟨c' - ConcreteCategory.hom (g.app (op (n + 1))) b', ?_⟩
  have hgnat : ConcreteCategory.hom (SequentialSystem.transition C n)
      (ConcreteCategory.hom (g.app (op (n + 1))) b') =
      ConcreteCategory.hom (SequentialSystem.transition C n) c' - c := by
    calc ConcreteCategory.hom (SequentialSystem.transition C n)
          (ConcreteCategory.hom (g.app (op (n + 1))) b')
        = ConcreteCategory.hom (g.app (op (n + 1)) ≫ SequentialSystem.transition C n)
            b' :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (SequentialSystem.transition B n ≫ g.app (op n)) b' :=
          (ConcreteCategory.congr_hom (g.naturality (homOfLE (Nat.le_succ n)).op)
            b').symm
      _ = ConcreteCategory.hom (g.app (op n))
            (ConcreteCategory.hom (SequentialSystem.transition B n) b') :=
          ConcreteCategory.comp_apply _ _ _
      _ = ConcreteCategory.hom (g.app (op n)) b := by rw [hb']
      _ = ConcreteCategory.hom (SequentialSystem.transition C n) c' - c := hb
  rw [map_sub, hgnat]
  abel

/-- **Exchange of limit and cokernel under Mittag-Leffler hypotheses.** Suppose
`B ⟶ C ⟶ D` are maps of inverse systems of abelian groups which are levelwise exact at
`C`, `h` is levelwise surjective, the transition maps of `B` are surjective, and the
transition maps of `B` are surjective on the kernels of `g` (a relative Mittag-Leffler
condition). Then `limMap h` induces an isomorphism from the cokernel of `limMap g`:
every element of `limit D` lifts to `limit C`, and elements of `limit C` killed by
`limMap h` come from `limit B`. -/
lemma surjective_limMap_and_exact
    (hcomp : ∀ (k : ℕᵒᵖ) (b : B.obj k), ConcreteCategory.hom (h.app k)
      (ConcreteCategory.hom (g.app k) b) = 0)
    (hexact : ∀ (k : ℕᵒᵖ) (c : C.obj k), ConcreteCategory.hom (h.app k) c = 0 →
      ∃ b : B.obj k, ConcreteCategory.hom (g.app k) b = c)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (h.app k)))
    (hB : ∀ n, Function.Surjective
      (ConcreteCategory.hom (SequentialSystem.transition B n)))
    (hker : ∀ (n : ℕ) (b : B.obj (op n)), ConcreteCategory.hom (g.app (op n)) b = 0 →
      ∃ b' : B.obj (op (n + 1)), ConcreteCategory.hom (g.app (op (n + 1))) b' = 0 ∧
        ConcreteCategory.hom (SequentialSystem.transition B n) b' = b) :
    Function.Surjective (ConcreteCategory.hom (limMap h)) ∧
      ∀ c : (limit C : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap h) c = 0 →
        ∃ b : (limit B : AddCommGrpCat.{w}), ConcreteCategory.hom (limMap g) b = c := by
  constructor
  · -- Surjectivity of `limMap h`, by a Mittag-Leffler correction recursion.
    intro t
    let y : ∀ n : ℕ, ToType (D.obj (op n)) :=
      fun n ↦ ConcreteCategory.hom (limit.π D (op n)) t
    have step : ∀ (n : ℕ) (cn : ToType (C.obj (op n))),
        ConcreteCategory.hom (h.app (op n)) cn = y n →
        ∃ cs : ToType (C.obj (op (n + 1))),
          ConcreteCategory.hom (h.app (op (n + 1))) cs = y (n + 1) ∧
          ConcreteCategory.hom (SequentialSystem.transition C n) cs = cn := by
      intro n cn hcn
      obtain ⟨z, hz⟩ := hsurj (op (n + 1)) (y (n + 1))
      have hnatz : ConcreteCategory.hom (h.app (op n))
          (ConcreteCategory.hom (SequentialSystem.transition C n) z) = y n := by
        calc ConcreteCategory.hom (h.app (op n))
              (ConcreteCategory.hom (SequentialSystem.transition C n) z)
            = ConcreteCategory.hom (SequentialSystem.transition C n ≫ h.app (op n))
                z :=
              (ConcreteCategory.comp_apply _ _ _).symm
          _ = ConcreteCategory.hom
                (h.app (op (n + 1)) ≫ SequentialSystem.transition D n) z :=
              ConcreteCategory.congr_hom (h.naturality (homOfLE (Nat.le_succ n)).op) z
          _ = ConcreteCategory.hom (SequentialSystem.transition D n)
                (ConcreteCategory.hom (h.app (op (n + 1))) z) :=
              ConcreteCategory.comp_apply _ _ _
          _ = ConcreteCategory.hom (SequentialSystem.transition D n) (y (n + 1)) := by
              rw [hz]
          _ = y n := transition_π_apply t n
      have h0 : ConcreteCategory.hom (h.app (op n))
          (cn - ConcreteCategory.hom (SequentialSystem.transition C n) z) = 0 := by
        rw [map_sub, hcn, hnatz, sub_self]
      obtain ⟨b, hb⟩ := hexact (op n) _ h0
      obtain ⟨b', hb'⟩ := hB n b
      have hgb' : ConcreteCategory.hom (SequentialSystem.transition C n)
          (ConcreteCategory.hom (g.app (op (n + 1))) b') =
          cn - ConcreteCategory.hom (SequentialSystem.transition C n) z := by
        calc ConcreteCategory.hom (SequentialSystem.transition C n)
              (ConcreteCategory.hom (g.app (op (n + 1))) b')
            = ConcreteCategory.hom
                (g.app (op (n + 1)) ≫ SequentialSystem.transition C n) b' :=
              (ConcreteCategory.comp_apply _ _ _).symm
          _ = ConcreteCategory.hom (SequentialSystem.transition B n ≫ g.app (op n))
                b' :=
              (ConcreteCategory.congr_hom (g.naturality (homOfLE (Nat.le_succ n)).op)
                b').symm
          _ = ConcreteCategory.hom (g.app (op n))
                (ConcreteCategory.hom (SequentialSystem.transition B n) b') :=
              ConcreteCategory.comp_apply _ _ _
          _ = ConcreteCategory.hom (g.app (op n)) b := by rw [hb']
          _ = cn - ConcreteCategory.hom (SequentialSystem.transition C n) z := hb
      refine ⟨z + ConcreteCategory.hom (g.app (op (n + 1))) b', ?_, ?_⟩
      · rw [map_add, hz, hcomp, add_zero]
      · rw [map_add, hgb']
        abel
    obtain ⟨c0, hc0⟩ := hsurj (op 0) (y 0)
    let c : ∀ n, {v : ToType (C.obj (op n)) //
        ConcreteCategory.hom (h.app (op n)) v = y n} :=
      fun n ↦ Nat.rec ⟨c0, hc0⟩
        (fun m ih ↦ ⟨(step m ih.1 ih.2).choose, (step m ih.1 ih.2).choose_spec.1⟩) n
    have hcc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition C n)
        (c (n + 1)).1 = (c n).1 := fun n ↦ (step n (c n).1 (c n).2).choose_spec.2
    obtain ⟨s, hs⟩ := exists_limit_elem (fun n ↦ (c n).1) hcc
    refine ⟨s, limMap_apply_eq h s t fun k ↦ ?_⟩
    calc ConcreteCategory.hom (h.app k) (ConcreteCategory.hom (limit.π C k) s)
        = ConcreteCategory.hom (h.app k) (c k.unop).1 := by rw [hs k]
      _ = ConcreteCategory.hom (limit.π D k) t := (c k.unop).2
  · -- Exactness: elements of `limit C` killed by `limMap h` come from `limit B`.
    intro t ht
    have hc0 : ∀ n : ℕ, ConcreteCategory.hom (h.app (op n))
        (ConcreteCategory.hom (limit.π C (op n)) t) = 0 := by
      intro n
      calc ConcreteCategory.hom (h.app (op n))
            (ConcreteCategory.hom (limit.π C (op n)) t)
          = ConcreteCategory.hom (limit.π C (op n) ≫ h.app (op n)) t :=
            (ConcreteCategory.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom (limMap h ≫ limit.π D (op n)) t :=
            (ConcreteCategory.congr_hom (limMap_π h (op n)) t).symm
        _ = ConcreteCategory.hom (limit.π D (op n))
              (ConcreteCategory.hom (limMap h) t) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (limit.π D (op n)) 0 := by rw [ht]
        _ = 0 := map_zero _
    have step : ∀ (n : ℕ) (bn : ToType (B.obj (op n))),
        ConcreteCategory.hom (g.app (op n)) bn =
          ConcreteCategory.hom (limit.π C (op n)) t →
        ∃ bs : ToType (B.obj (op (n + 1))),
          ConcreteCategory.hom (g.app (op (n + 1))) bs =
            ConcreteCategory.hom (limit.π C (op (n + 1))) t ∧
          ConcreteCategory.hom (SequentialSystem.transition B n) bs = bn := by
      intro n bn hbn
      obtain ⟨b', hb'⟩ := hexact (op (n + 1)) _ (hc0 (n + 1))
      have hw : ConcreteCategory.hom (g.app (op n))
          (ConcreteCategory.hom (SequentialSystem.transition B n) b' - bn) = 0 := by
        have h1 : ConcreteCategory.hom (g.app (op n))
            (ConcreteCategory.hom (SequentialSystem.transition B n) b') =
            ConcreteCategory.hom (limit.π C (op n)) t := by
          calc ConcreteCategory.hom (g.app (op n))
                (ConcreteCategory.hom (SequentialSystem.transition B n) b')
              = ConcreteCategory.hom (SequentialSystem.transition B n ≫ g.app (op n))
                  b' :=
                (ConcreteCategory.comp_apply _ _ _).symm
            _ = ConcreteCategory.hom
                  (g.app (op (n + 1)) ≫ SequentialSystem.transition C n) b' :=
                ConcreteCategory.congr_hom
                  (g.naturality (homOfLE (Nat.le_succ n)).op) b'
            _ = ConcreteCategory.hom (SequentialSystem.transition C n)
                  (ConcreteCategory.hom (g.app (op (n + 1))) b') :=
                ConcreteCategory.comp_apply _ _ _
            _ = ConcreteCategory.hom (SequentialSystem.transition C n)
                  (ConcreteCategory.hom (limit.π C (op (n + 1))) t) := by rw [hb']
            _ = ConcreteCategory.hom (limit.π C (op n)) t := transition_π_apply t n
        rw [map_sub, h1, hbn, sub_self]
      obtain ⟨b'', hb''0, hb''t⟩ := hker n _ hw
      refine ⟨b' - b'', ?_, ?_⟩
      · rw [map_sub, hb', hb''0, sub_zero]
      · rw [map_sub, hb''t]
        abel
    obtain ⟨b0, hb0⟩ := hexact (op 0) _ (hc0 0)
    let b : ∀ n, {v : ToType (B.obj (op n)) //
        ConcreteCategory.hom (g.app (op n)) v =
          ConcreteCategory.hom (limit.π C (op n)) t} :=
      fun n ↦ Nat.rec ⟨b0, hb0⟩
        (fun m ih ↦ ⟨(step m ih.1 ih.2).choose, (step m ih.1 ih.2).choose_spec.1⟩) n
    have hbc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition B n)
        (b (n + 1)).1 = (b n).1 := fun n ↦ (step n (b n).1 (b n).2).choose_spec.2
    obtain ⟨s, hs⟩ := exists_limit_elem (fun n ↦ (b n).1) hbc
    refine ⟨s, limMap_apply_eq g s t fun k ↦ ?_⟩
    calc ConcreteCategory.hom (g.app k) (ConcreteCategory.hom (limit.π B k) s)
        = ConcreteCategory.hom (g.app k) (b k.unop).1 := by rw [hs k]
      _ = ConcreteCategory.hom (limit.π C k) t := (b k.unop).2

end AbChase

section Main

variable [EnoughInjectives A] [HasProductsOfShape ℕ A]

variable (Z : A)

/-- The connecting maps of the levelwise covariant long exact sequences assemble into a
morphism of systems. -/
noncomputable def levelDelta {SC : ShortComplex (ℕᵒᵖ ⥤ A)}
    (hSC : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) :
    levelSystem Z SC.X₃ i ⟶ levelSystem Z SC.X₁ (i + 1) where
  app k := AddCommGrpCat.ofHom ((hSC k).extClass.postcomp Z rfl)
  naturality {k k'} f := by
    have hnat : (hSC k).extClass.comp (Ext.mk₀ (SC.X₁.map f)) (add_zero 1) =
        (Ext.mk₀ (SC.X₃.map f)).comp (hSC k').extClass (zero_add 1) :=
      ShortComplex.ShortExact.extClass_naturality (hSC k) (hSC k')
        (ShortComplex.homMk (SC.X₁.map f) (SC.X₂.map f) (SC.X₃.map f)
          (SC.f.naturality f) (SC.g.naturality f))
    apply ConcreteCategory.hom_ext
    intro x
    refine (ConcreteCategory.comp_apply _ _ _).trans
      (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm)
    change (Ext.comp x (Ext.mk₀ (SC.X₃.map f)) (add_zero i)).comp (hSC k').extClass rfl =
      Ext.comp (Ext.comp x (hSC k).extClass rfl) (Ext.mk₀ (SC.X₁.map f))
        (add_zero (i + 1))
    calc (Ext.comp x (Ext.mk₀ (SC.X₃.map f)) (add_zero i)).comp (hSC k').extClass rfl
        = Ext.comp x ((Ext.mk₀ (SC.X₃.map f)).comp (hSC k').extClass (zero_add 1))
            rfl :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = Ext.comp x ((hSC k).extClass.comp (Ext.mk₀ (SC.X₁.map f)) (add_zero 1))
            rfl :=
          congrArg (fun e ↦ Ext.comp x e rfl) hnat.symm
      _ = Ext.comp (Ext.comp x (hSC k).extClass rfl) (Ext.mk₀ (SC.X₁.map f))
            (add_zero (i + 1)) :=
          (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

variable {SC : ShortComplex (ℕᵒᵖ ⥤ A)}

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Componentwise, `levelDelta` is postcomposition with the levelwise extension class. -/
private lemma levelDelta_app_apply
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (x : Ext Z (SC.X₃.obj k) i) :
    ConcreteCategory.hom ((levelDelta Z hSCk i).app k) x = x.comp (hSCk k).extClass rfl :=
  rfl

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Componentwise, whiskering `SC.g` with the `Ext`-functor is postcomposition with
`mk₀` of the corresponding component of `SC.g`. -/
private lemma whiskerRight_extFunctorObj_app_apply (i : ℕ) (k : ℕᵒᵖ)
    (x : Ext Z (SC.X₂.obj k) i) :
    ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) x =
      x.comp (Ext.mk₀ ((SC.map ((evaluation ℕᵒᵖ A).obj k)).g)) (add_zero i) :=
  rfl

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- The image of a levelwise `Hom`-class from the middle object dies under the
connecting map. -/
private lemma levelDelta_comp_app_zero
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (b : Ext Z (SC.X₂.obj k) i) :
    ConcreteCategory.hom ((levelDelta Z hSCk i).app k)
      (ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b) =
      0 := by
  have h1 : ConcreteCategory.hom ((levelDelta Z hSCk i).app k)
      (ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b) =
      (b.comp (Ext.mk₀ ((SC.map ((evaluation ℕᵒᵖ A).obj k)).g)) (add_zero i)).comp
        (hSCk k).extClass rfl := rfl
  rw [h1, Ext.comp_assoc_of_second_deg_zero, (hSCk k).comp_extClass, Ext.comp_zero]

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Levelwise exactness at the third object: classes killed by the connecting map come
from the middle object. -/
private lemma exists_of_levelDelta_app_eq_zero
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (c : Ext Z (SC.X₃.obj k) i)
    (hc : ConcreteCategory.hom ((levelDelta Z hSCk i).app k) c = 0) :
    ∃ b : Ext Z (SC.X₂.obj k) i,
      ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z i)).app k) b =
        c := by
  obtain ⟨b, hb⟩ := covariant_sequence_exact₃ Z (hSCk k) c rfl
    ((levelDelta_app_apply Z hSCk i k c).symm.trans hc)
  exact ⟨b, (whiskerRight_extFunctorObj_app_apply Z i k b).trans hb⟩

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- The connecting map is levelwise surjective when the positive `Ext`-groups of the
middle levels vanish. -/
private lemma surjective_levelDelta_app
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (i : ℕ) (k : ℕᵒᵖ)
    (h₂ : Subsingleton (Ext Z (SC.X₂.obj k) (i + 1))) :
    Function.Surjective (ConcreteCategory.hom ((levelDelta Z hSCk i).app k)) := by
  intro ξ
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z (hSCk k) ξ (h₂.elim _ _) rfl
  exact ⟨x₃, (levelDelta_app_apply Z hSCk i k x₃).trans hx₃⟩

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- The connecting map is levelwise injective in positive degrees when the `Ext`-groups
of the middle levels vanish there. -/
private lemma injective_levelDelta_app
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact) (j : ℕ) (k : ℕᵒᵖ)
    (h₂ : Subsingleton (Ext Z (SC.X₂.obj k) (j + 1))) :
    Function.Injective (ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app k)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z (hSCk k) x rfl
    ((levelDelta_app_apply Z hSCk (j + 1) k x).symm.trans hx)
  rw [← hx₂, h₂.elim x₂ 0, Ext.zero_comp]

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- The transition maps of the degree-zero level system of an injective system are
surjective, by composing with the splittings of the transition maps. -/
private lemma surjective_transition_levelSystem_of_injective
    (I : ℕᵒᵖ ⥤ A) [Injective I] (n : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      (SequentialSystem.transition (levelSystem Z I 0) n)) := by
  obtain ⟨σ⟩ := (SequentialSystem.isSplitEpi_transition_of_injective I n).exists_splitEpi
  intro y
  refine ⟨y.comp (Ext.mk₀ σ.section_) (add_zero 0), ?_⟩
  have h1 : ConcreteCategory.hom (SequentialSystem.transition (levelSystem Z I 0) n)
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)) =
      (y.comp (Ext.mk₀ σ.section_) (add_zero 0)).comp
        (Ext.mk₀ (SequentialSystem.transition I n)) (add_zero 0) := rfl
  rw [h1, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, σ.id, Ext.comp_mk₀_id]

omit [HasExt.{w} (ℕᵒᵖ ⥤ A)] [EnoughInjectives A] [HasProductsOfShape ℕ A] in
/-- Relative Mittag-Leffler input for `surjective_limMap_and_exact`: under the
Mittag-Leffler hypothesis on `Hom(Z, SC.X₁•)`, the transition maps of the level system
of the middle object surject onto the kernels of the level maps to the third object. -/
private lemma exists_transition_preimage_ker
    (hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact)
    (hML : ∀ n, Function.Surjective (ConcreteCategory.hom
      ((levelSystem Z SC.X₁ 0).map (homOfLE (Nat.le_succ n)).op)))
    (n : ℕ) (b : Ext Z (SC.X₂.obj (op n)) 0)
    (hb : ConcreteCategory.hom
      ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op n)) b = 0) :
    ∃ b' : Ext Z (SC.X₂.obj (op (n + 1))) 0,
      ConcreteCategory.hom
        ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op (n + 1))) b' = 0 ∧
      ConcreteCategory.hom
        (SequentialSystem.transition (levelSystem Z SC.X₂ 0) n) b' = b := by
  obtain ⟨w, hw⟩ := covariant_sequence_exact₂ Z (hSCk (op n)) b
    ((whiskerRight_extFunctorObj_app_apply Z 0 (op n) b).symm.trans hb)
  obtain ⟨w', hw'⟩ := hML n w
  refine ⟨w'.comp (Ext.mk₀ (SC.f.app (op (n + 1)))) (add_zero 0), ?_, ?_⟩
  · have h2 : SC.f.app (op (n + 1)) ≫ SC.g.app (op (n + 1)) = 0 := by
      rw [← NatTrans.comp_app, SC.zero, zero_app]
    calc ConcreteCategory.hom
          ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app (op (n + 1)))
          (w'.comp (Ext.mk₀ (SC.f.app (op (n + 1)))) (add_zero 0))
        = (w'.comp (Ext.mk₀ (SC.f.app (op (n + 1)))) (add_zero 0)).comp
            (Ext.mk₀ (SC.g.app (op (n + 1)))) (add_zero 0) := rfl
      _ = w'.comp ((Ext.mk₀ (SC.f.app (op (n + 1)))).comp
            (Ext.mk₀ (SC.g.app (op (n + 1)))) (zero_add 0)) (add_zero 0) :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = 0 := by rw [Ext.mk₀_comp_mk₀, h2, Ext.mk₀_zero, Ext.comp_zero]
  · calc ConcreteCategory.hom (SequentialSystem.transition (levelSystem Z SC.X₂ 0) n)
          (w'.comp (Ext.mk₀ (SC.f.app (op (n + 1)))) (add_zero 0))
        = (w'.comp (Ext.mk₀ (SC.f.app (op (n + 1)))) (add_zero 0)).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE (Nat.le_succ n)).op)) (add_zero 0) := rfl
      _ = w'.comp ((Ext.mk₀ (SC.f.app (op (n + 1)))).comp
            (Ext.mk₀ (SC.X₂.map (homOfLE (Nat.le_succ n)).op)) (zero_add 0))
            (add_zero 0) := Ext.comp_assoc_of_second_deg_zero _ _ _ _
      _ = w'.comp ((Ext.mk₀ (SC.X₁.map (homOfLE (Nat.le_succ n)).op)).comp
            (Ext.mk₀ (SC.f.app (op n))) (zero_add 0)) (add_zero 0) := by
          rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, SC.f.naturality]
      _ = (w'.comp (Ext.mk₀ (SC.X₁.map (homOfLE (Nat.le_succ n)).op)) (add_zero 0)).comp
            (Ext.mk₀ (SC.f.app (op n))) (add_zero 0) :=
          (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm
      _ = w.comp (Ext.mk₀ (SC.f.app (op n))) (add_zero 0) :=
          congrArg (fun t : Ext Z (SC.X₁.obj (op n)) 0 ↦
            t.comp (Ext.mk₀ (SC.f.app (op n))) (add_zero 0)) hw'
      _ = b := hw

/-- The composite identification `(Δ Z ⟶ G) ≃+ limit (levelSystem Z G 0)`. -/
private noncomputable def homAddEquivLimit (G : ℕᵒᵖ ⥤ A) :
    ((Functor.const ℕᵒᵖ).obj Z ⟶ G) ≃+ ↥(limit (levelSystem Z G 0)) :=
  (Ext.addEquiv₀ (X := (Functor.const ℕᵒᵖ).obj Z) (Y := G)).symm.trans
    (zeroAddEquivLimitLevelSystem Z G)

omit [EnoughInjectives A] [HasProductsOfShape ℕ A] in
private lemma π_homAddEquivLimit (G : ℕᵒᵖ ⥤ A)
    (s : (Functor.const ℕᵒᵖ).obj Z ⟶ G) (k : ℕᵒᵖ) :
    ConcreteCategory.hom (limit.π (levelSystem Z G 0) k) (homAddEquivLimit Z G s) =
      Ext.mk₀ (s.app k) := by
  have h1 := π_zeroAddEquivLimitLevelSystem (Z := Z) (F := G) (Ext.addEquiv₀.symm s) k
  rw [AddEquiv.apply_symm_apply] at h1
  exact h1

/-- **Comparison of `Ext` from a constant system with the limit of levelwise `Ext`,
under a Mittag-Leffler hypothesis** (the `lim¹`-free case of Jannsen's exact sequence):
if the transition maps of the degree-`i` levelwise `Ext`-system are surjective, then
`Ext (Δ Z) F (i + 1)` is the inverse limit of the levelwise `Ext`-groups in degree
`i + 1`. -/
theorem nonempty_addEquiv_limit_levelSystem (F : ℕᵒᵖ ⥤ A) (i : ℕ)
    (hML : ∀ n, Function.Surjective (ConcreteCategory.hom
      ((levelSystem Z F i).map (homOfLE (Nat.le_succ n)).op))) :
    Nonempty (Ext ((Functor.const ℕᵒᵖ).obj Z) F (i + 1) ≃+
      ↥(limit (levelSystem Z F (i + 1)))) := by
  -- Induction on `i`, generalizing `F` (as in
  -- `nonempty_continuousH_addEquiv_H_limit` in
  -- `Proetale/Topology/Comparison/ContinuousComparison.lean` — read it first; the
  -- structure here is parallel).
  --
  -- **Setup** (both cases). `SC := ShortComplex.mk (Injective.ι F)
  -- (cokernel.π (Injective.ι F)) (cokernel.condition _)`, `hSC : SC.ShortExact`,
  -- `I := SC.X₂ = Injective.under F` (injective system: split epimorphic transitions
  -- by `SequentialSystem.isSplitEpi_transition_of_injective`, injective levels by
  -- `SequentialSystem.injective_obj_of_injective`), `Q := SC.X₃`. Levelwise short
  -- exactness `hSCk k := hSC.map_of_exact ((evaluation ℕᵒᵖ A).obj k)`.
  -- Levelwise, `Ext Z (I.obj k) q = 0` for `q > 0` (`Ext.subsingleton_of_injective`),
  -- and `Ext (Δ Z) I q = 0` for `q > 0`.
  --
  -- **Base case `i = 0`.** Both sides are described by the four-term exact sequences
  -- `0 → Hom(Z,F•) → Hom(Z,I•) → Hom(Z,Q•) → Ext¹(Z,F•) → 0`:
  -- * `Ext (Δ Z) F 1 ≃+ (Δ Z ⟶ Q) ⧸ ker (deltaZero hSC (Δ Z))` via
  --   `QuotientAddGroup.quotientKerEquivOfSurjective` and `Ext.deltaZero_surjective`
  --   (`Ext (Δ Z) I 1 = 0`); the kernel is the image of `(Δ Z ⟶ I)` by
  --   `Ext.deltaZero_apply_eq_zero_iff`.
  -- * `(Δ Z ⟶ Q) ≃+ limit (levelSystem Z Q 0)` and similarly for `I` via
  --   `zeroAddEquivLimitLevelSystem` (composed with `Ext.addEquiv₀`), compatibly with
  --   the maps (naturality of the construction).
  -- * On the limit side apply `surjective_limMap_and_exact` with
  --   `B := levelSystem Z I 0`, `C := levelSystem Z Q 0`, `D := levelSystem Z F 1`,
  --   `g := ` postcomposition with `mk₀ SC.g` levelwise (a natural transformation;
  --   build it as `Functor.whiskerLeft`-style or by hand), `h := levelDelta Z hSCk 0`:
  --   - levelwise exactness and surjectivity of `h` come from the levelwise covariant
  --     LES (`Ext.covariant_sequence_exact₁/₃`, `Ext.deltaZero` lemmas, vanishing on
  --     injective levels);
  --   - transitions of `B` are surjective: `Hom(Z, -)` applied to the split
  --     epimorphisms `transition I n`;
  --   - `hker`: the kernel of `g` at level `n` is the image of `Hom(Z, Fₙ)` (LES
  --     exactness in degree 0: `Ext.covariant_sequence_exact₂` at `n = 0` through
  --     `mk₀`); surjectivity of the transitions on these kernels is exactly the
  --     hypothesis `hML` (transport through the identification, using naturality of
  --     `mk₀`-postcomposition and injectivity of `mk₀`).
  --   Conclude: `limMap h` identifies `limit (levelSystem Z F 1)` with
  --   `limit (levelSystem Z Q 0) ⧸ im (limMap g)`, and assemble the equivalence with
  --   the quotient description of `Ext (Δ Z) F 1` (use `QuotientAddGroup.congr` or an
  --   explicit `AddEquiv` built from the two surjections with equal kernels).
  --
  -- **Inductive step `i + 1` (target degree `i + 2`).**
  -- * `Q` satisfies the hypothesis at degree `i`: for `i ≥ 1`,
  --   `levelSystem Z Q i ≅ levelSystem Z F (i + 1)` via the levelwise connecting
  --   isomorphisms (`Ext.connectingEquiv` levelwise, assembled into a natural
  --   isomorphism using `levelDelta`-naturality — note `levelDelta Z hSCk i` is an
  --   isomorphism in each component when `i ≥ 1` since the adjacent `Ext`-groups of
  --   the injective levels vanish), so `hML` transports. For `i = 0`, the hypothesis
  --   `transitions of levelSystem Z Q 0 surjective` follows from
  --   `surjective_transition_of_exact` applied to
  --   `levelSystem Z I 0 ⟶ levelSystem Z Q 0 ⟶ levelSystem Z F 1`
  --   (with `hML` providing the `D`-surjectivity and split transitions of `I` the
  --   `B`-surjectivity).
  -- * Conclude:
  --   `Ext (Δ Z) F (i+2) ≃+ Ext (Δ Z) Q (i+1)` by `(Ext.connectingEquiv hSC _ i _ _).symm`
  --   (vanishing of `Ext (Δ Z) I` in degrees `i+1`, `i+2`),
  --   `≃+ limit (levelSystem Z Q (i+1))` by the induction hypothesis,
  --   `≃+ limit (levelSystem Z F (i+2))` by applying `lim.mapIso` to the natural
  --   isomorphism `levelSystem Z Q (i+1) ≅ levelSystem Z F (i+2)` given componentwise
  --   by `Ext.connectingEquiv` (naturality from
  --   `ShortComplex.ShortExact.extClass_naturality` — i.e. `levelDelta` is a natural
  --   isomorphism here), converted to an additive equivalence
  --   (`AddCommGrpCat`-isomorphisms are additive equivalences).
  induction i generalizing F with
  | zero =>
    let SC : ShortComplex (ℕᵒᵖ ⥤ A) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((evaluation ℕᵒᵖ A).obj k) := ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((evaluation ℕᵒᵖ A).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      exact hSC.map_of_exact ((evaluation ℕᵒᵖ A).obj k)
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton (Ext Z (SC.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_of_injective Z _ q
    obtain ⟨hsurjL, hexactL⟩ := surjective_limMap_and_exact
      (Functor.whiskerRight SC.g (extFunctorObj Z 0)) (levelDelta Z hSCk 0)
      (levelDelta_comp_app_zero Z hSCk 0)
      (exists_of_levelDelta_app_eq_zero Z hSCk 0)
      (fun k ↦ surjective_levelDelta_app Z hSCk 0 k (hsubk k 0))
      (surjective_transition_levelSystem_of_injective Z SC.X₂)
      (exists_transition_preimage_ker Z hSCk hML)
    have h₂ : Subsingleton (Ext ((Functor.const ℕᵒᵖ).obj Z) SC.X₂ 1) :=
      subsingleton_of_injective _ _ 0
    have hgapp : ∀ (k : ℕᵒᵖ) (t : (Functor.const ℕᵒᵖ).obj Z ⟶ SC.X₂),
        ConcreteCategory.hom ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app k)
          (Ext.mk₀ (t.app k)) = Ext.mk₀ ((t ≫ SC.g).app k) := fun k t ↦
      (whiskerRight_extFunctorObj_app_apply Z 0 k (Ext.mk₀ (t.app k))).trans
        (Ext.mk₀_comp_mk₀ _ _)
    have hker : AddSubgroup.map
        (homAddEquivLimit Z SC.X₃ :
          ((Functor.const ℕᵒᵖ).obj Z ⟶ SC.X₃) →+ ↥(limit (levelSystem Z SC.X₃ 0)))
        (AddMonoidHom.ker (deltaZero hSC ((Functor.const ℕᵒᵖ).obj Z))) =
        AddMonoidHom.ker (ConcreteCategory.hom (limMap (levelDelta Z hSCk 0)) :
          ↥(limit (levelSystem Z SC.X₃ 0)) →+ ↥(limit (levelSystem Z SC.X₁ 1))) := by
      ext y
      simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, AddMonoidHom.coe_coe]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨t, rfl⟩ := (deltaZero_apply_eq_zero_iff hSC _ x).1 hx
        refine limMap_apply_eq (levelDelta Z hSCk 0) _ 0 fun k ↦ ?_
        calc ConcreteCategory.hom ((levelDelta Z hSCk 0).app k)
              (ConcreteCategory.hom (limit.π (levelSystem Z SC.X₃ 0) k)
                (homAddEquivLimit Z SC.X₃ (t ≫ SC.g)))
            = ConcreteCategory.hom ((levelDelta Z hSCk 0).app k)
                (Ext.mk₀ ((t ≫ SC.g).app k)) := by rw [π_homAddEquivLimit]
          _ = ConcreteCategory.hom ((levelDelta Z hSCk 0).app k)
              (ConcreteCategory.hom
                ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app k)
                (Ext.mk₀ (t.app k))) := by rw [hgapp k t]
          _ = 0 := levelDelta_comp_app_zero Z hSCk 0 k _
          _ = ConcreteCategory.hom (limit.π (levelSystem Z SC.X₁ 1) k) 0 :=
            (map_zero _).symm
      · intro hy
        obtain ⟨b, hb⟩ := hexactL y hy
        have hbt : homAddEquivLimit Z SC.X₂ ((homAddEquivLimit Z SC.X₂).symm b) = b :=
          AddEquiv.apply_symm_apply _ b
        have hπb : ∀ k : ℕᵒᵖ, ConcreteCategory.hom (limit.π (levelSystem Z SC.X₂ 0) k) b =
            Ext.mk₀ (((homAddEquivLimit Z SC.X₂).symm b).app k) := by
          intro k
          conv_lhs => rw [← hbt]
          exact π_homAddEquivLimit Z SC.X₂ _ k
        refine ⟨(homAddEquivLimit Z SC.X₂).symm b ≫ SC.g,
          (deltaZero_apply_eq_zero_iff hSC _ _).2 ⟨_, rfl⟩, ?_⟩
        have h1 : ConcreteCategory.hom
            (limMap (Functor.whiskerRight SC.g (extFunctorObj Z 0))) b =
            homAddEquivLimit Z SC.X₃ ((homAddEquivLimit Z SC.X₂).symm b ≫ SC.g) := by
          refine limMap_apply_eq _ _ _ fun k ↦ ?_
          calc ConcreteCategory.hom
                ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app k)
                (ConcreteCategory.hom (limit.π (levelSystem Z SC.X₂ 0) k) b)
              = ConcreteCategory.hom
                  ((Functor.whiskerRight SC.g (extFunctorObj Z 0)).app k)
                  (Ext.mk₀ (((homAddEquivLimit Z SC.X₂).symm b).app k)) := by
                rw [hπb k]
            _ = Ext.mk₀ ((((homAddEquivLimit Z SC.X₂).symm b) ≫ SC.g).app k) :=
                hgapp k _
            _ = ConcreteCategory.hom (limit.π (levelSystem Z SC.X₃ 0) k)
                  (homAddEquivLimit Z SC.X₃
                    ((homAddEquivLimit Z SC.X₂).symm b ≫ SC.g)) :=
                (π_homAddEquivLimit Z SC.X₃ _ k).symm
        exact h1.symm.trans hb
    exact ⟨((QuotientAddGroup.quotientKerEquivOfSurjective _
          (deltaZero_surjective hSC _ h₂)).symm.trans
        (QuotientAddGroup.congr _ _ (homAddEquivLimit Z SC.X₃) hker)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurjL)⟩
  | succ i IH =>
    let SC : ShortComplex (ℕᵒᵖ ⥤ A) :=
      ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
    have hSCk : ∀ k : ℕᵒᵖ, (SC.map ((evaluation ℕᵒᵖ A).obj k)).ShortExact := by
      intro k
      haveI : PreservesFiniteLimits ((evaluation ℕᵒᵖ A).obj k) := ⟨fun _ _ _ ↦ inferInstance⟩
      haveI : PreservesFiniteColimits ((evaluation ℕᵒᵖ A).obj k) :=
        ⟨fun _ _ _ ↦ inferInstance⟩
      exact hSC.map_of_exact ((evaluation ℕᵒᵖ A).obj k)
    have hsubk : ∀ (k : ℕᵒᵖ) (q : ℕ), Subsingleton (Ext Z (SC.X₂.obj k) (q + 1)) := by
      intro k q
      haveI : Injective (SC.X₂.obj k) :=
        SequentialSystem.injective_obj_of_injective SC.X₂ k.unop
      exact subsingleton_of_injective Z _ q
    -- Transport the Mittag-Leffler hypothesis to the cokernel system at degree `i`.
    have hMLQ : ∀ n, Function.Surjective (ConcreteCategory.hom
        ((levelSystem Z SC.X₃ i).map (homOfLE (Nat.le_succ n)).op)) := by
      obtain _ | j := i
      · exact fun n ↦ surjective_transition_of_exact
          (Functor.whiskerRight SC.g (extFunctorObj Z 0)) (levelDelta Z hSCk 0)
          (exists_of_levelDelta_app_eq_zero Z hSCk 0)
          (fun k ↦ surjective_levelDelta_app Z hSCk 0 k (hsubk k 0))
          (surjective_transition_levelSystem_of_injective Z SC.X₂)
          hML n
      · intro n c
        obtain ⟨d', hd'⟩ := hML n (ConcreteCategory.hom
          ((levelDelta Z hSCk (j + 1)).app (op n)) c)
        obtain ⟨c', hc'⟩ := surjective_levelDelta_app Z hSCk (j + 1) (op (n + 1))
          (hsubk (op (n + 1)) (j + 1)) d'
        refine ⟨c', injective_levelDelta_app Z hSCk j (op n) (hsubk (op n) j) ?_⟩
        calc ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app (op n))
              (ConcreteCategory.hom ((levelSystem Z SC.X₃ (j + 1)).map
                (homOfLE (Nat.le_succ n)).op) c')
            = ConcreteCategory.hom
                ((levelSystem Z SC.X₃ (j + 1)).map (homOfLE (Nat.le_succ n)).op ≫
                  (levelDelta Z hSCk (j + 1)).app (op n)) c' :=
              (ConcreteCategory.comp_apply _ _ _).symm
          _ = ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app (op (n + 1)) ≫
                (levelSystem Z SC.X₁ (j + 2)).map (homOfLE (Nat.le_succ n)).op) c' :=
              ConcreteCategory.congr_hom
                ((levelDelta Z hSCk (j + 1)).naturality (homOfLE (Nat.le_succ n)).op) c'
          _ = ConcreteCategory.hom
                ((levelSystem Z SC.X₁ (j + 2)).map (homOfLE (Nat.le_succ n)).op)
                (ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app (op (n + 1)))
                  c') := ConcreteCategory.comp_apply _ _ _
          _ = ConcreteCategory.hom
                ((levelSystem Z SC.X₁ (j + 2)).map (homOfLE (Nat.le_succ n)).op) d' := by
              rw [hc']
          _ = ConcreteCategory.hom ((levelDelta Z hSCk (j + 1)).app (op n)) c := hd'
    obtain ⟨eQ⟩ := IH SC.X₃ hMLQ
    have h₂ : Subsingleton (Ext ((Functor.const ℕᵒᵖ).obj Z) SC.X₂ (i + 1)) :=
      subsingleton_of_injective _ _ i
    have h₂' : Subsingleton (Ext ((Functor.const ℕᵒᵖ).obj Z) SC.X₂ (i + 2)) :=
      subsingleton_of_injective _ _ (i + 1)
    haveI : ∀ k, IsIso ((levelDelta Z hSCk (i + 1)).app k) := by
      intro k
      rw [ConcreteCategory.isIso_iff_bijective]
      exact ⟨injective_levelDelta_app Z hSCk i k (hsubk k i),
        surjective_levelDelta_app Z hSCk (i + 1) k (hsubk k (i + 1))⟩
    haveI : IsIso (levelDelta Z hSCk (i + 1)) := NatIso.isIso_of_isIso_app _
    exact ⟨((connectingEquiv hSC ((Functor.const ℕᵒᵖ).obj Z) i h₂ h₂').symm.trans
        eQ).trans
      (asIso (limMap (levelDelta Z hSCk (i + 1)))).addCommGroupIsoToAddEquiv⟩

end Main

end CategoryTheory.Abelian.Ext
