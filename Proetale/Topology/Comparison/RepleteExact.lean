/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.WeaklyContractible
import Proetale.Mathlib.CategoryTheory.Abelian.SequentialSystem

/-!
# Exactness of sequential limits of pro-étale abelian sheaves

The topos of pro-étale sheaves on a scheme is replete: it has enough weakly contractible
objects (`Proetale.Topology.Comparison.WeaklyContractible`). We deduce the two exactness
statements needed for the comparison of continuous étale cohomology with pro-étale
cohomology (BS, Propositions 3.1.9 and 3.1.10; blueprint `prop:replete-products-exact`
and `prop:lim-exact-replete`):

- `AlgebraicGeometry.Scheme.ProEt.epi_piMap`: products of epimorphisms of abelian
  pro-étale sheaves are epimorphisms.
- `AlgebraicGeometry.Scheme.ProEt.shortExact_limMap`: the limit of a levelwise short
  exact sequence of inverse systems of abelian pro-étale sheaves is short exact, provided
  the first system has epimorphic transition maps (Mittag-Leffler).
- `AlgebraicGeometry.Scheme.ProEt.shortExact_telescope`: for an inverse system `G` with
  epimorphic transition maps, the Milnor sequence
  `0 → lim G → ∏ Gₙ → ∏ Gₙ → 0` (with second map `1 - shift`) is short exact.

All proofs proceed by evaluating on weakly contractible objects of the affine pro-étale
site, where the corresponding statements for abelian groups are elementary.
-/

universe w w' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- Limits of shape `ℕᵒᵖ` of abelian pro-étale sheaves. Registered explicitly: typeclass
search for limit shapes in sheaf categories is prohibitively slow. -/
instance : HasLimitsOfShape ℕᵒᵖ (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Sheaf.instHasLimitsOfShape

/-- Products indexed by a small type of abelian pro-étale sheaves, registered
explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

/-- Products indexed by a small type of abelian groups, registered explicitly. -/
instance (ι : Type w) [Small.{u + 1} ι] :
    HasLimitsOfShape (Discrete ι) Ab.{u + 1} :=
  hasLimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink ι)).symm

section Ab

/-! ### Elementary statements for abelian groups -/

/-- Subtraction of morphisms of abelian groups acts pointwise. -/
private lemma _root_.AddCommGrpCat.hom_sub_apply' {M N : AddCommGrpCat.{w}}
    (f g : M ⟶ N) (x : ToType M) :
    ConcreteCategory.hom (f - g) x =
      ConcreteCategory.hom f x - ConcreteCategory.hom g x :=
  rfl

/-- The zero morphism of abelian groups acts as zero. -/
private lemma _root_.AddCommGrpCat.hom_zero_apply' {M N : AddCommGrpCat.{w}}
    (x : ToType M) : ConcreteCategory.hom (0 : M ⟶ N) x = 0 :=
  rfl

/-- An element of a limit of abelian groups over a discrete diagram is determined by, and
can be assembled from, its components. -/
private lemma _root_.AddCommGrpCat.bijective_components_of_isLimit
    {ι : Type w} [Small.{w'} ι] {X : Discrete ι ⥤ AddCommGrpCat.{w'}} {c : Cone X}
    (hc : IsLimit c) :
    Function.Bijective (fun (t : ToType c.pt) (i : ι) ↦
      ConcreteCategory.hom (c.π.app ⟨i⟩) t) := by
  have hT : IsLimit ((CategoryTheory.forget AddCommGrpCat.{w'}).mapCone c) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w'}) hc
  -- Extracting the components of a section of the discrete diagram is bijective.
  have hsec : Function.Bijective
      (fun (s : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).sections) (i : ι) ↦ s.1 ⟨i⟩) := by
    constructor
    · intro s₁ s₂ h
      apply Subtype.ext
      funext k
      exact congrFun h k.as
    · intro g
      refine ⟨⟨fun k ↦ g k.as, ?_⟩, rfl⟩
      intro k k' f
      obtain ⟨i⟩ := k
      obtain ⟨j⟩ := k'
      obtain rfl : i = j := Discrete.eq_of_hom f
      have hf : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).map f = 𝟙 _ :=
        Discrete.functor_map_id _ f
      rw [hf]
      exact ConcreteCategory.id_apply _
  have key : (fun (t : ToType c.pt) (i : ι) ↦ ConcreteCategory.hom (c.π.app ⟨i⟩) t) =
      (fun (s : (X ⋙ CategoryTheory.forget AddCommGrpCat.{w'}).sections) (i : ι) ↦ s.1 ⟨i⟩) ∘
        (Types.isLimitEquivSections hT) := by
    funext t i
    exact (Types.isLimitEquivSections_apply hT ⟨i⟩ t).symm
  rw [key]
  exact hsec.comp (Types.isLimitEquivSections hT).bijective

/-- Mittag-Leffler for `ℕᵒᵖ`-indexed systems of abelian groups, kernel-free formulation:
if `τ : F ⟶ G` is levelwise surjective and the transition maps of `F` are surjective on
the kernels of `τ`, then `limMap τ` is surjective. -/
lemma _root_.AddCommGrpCat.surjective_limMap
    {F G : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G)
    (hsurj : ∀ k, Function.Surjective (ConcreteCategory.hom (τ.app k)))
    (hker : ∀ (n : ℕ) (x : F.obj (op n)), ConcreteCategory.hom (τ.app (op n)) x = 0 →
      ∃ y : F.obj (op (n + 1)), ConcreteCategory.hom (τ.app (op (n + 1))) y = 0 ∧
        ConcreteCategory.hom (SequentialSystem.transition F n) y = x) :
    Function.Surjective (ConcreteCategory.hom (limMap τ)) := by
  -- Identify elements of `limit F` and `limit G` with compatible sequences via
  -- `Types.limitEquivSections` and `isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat)`.
  -- Given a compatible sequence `(yₙ)` in `G`, construct `(xₙ)` in `F` by recursion:
  -- `x₀` is any `τ`-preimage of `y₀`; given `xₙ` with `τ xₙ = yₙ`, choose any preimage
  -- `z` of `yₙ₊₁`, observe `τ (xₙ - transition z) = 0` (compatibility of `(yₙ)` and
  -- naturality of `τ`), apply `hker` to obtain `w` with `τ w = 0` and
  -- `transition w = xₙ - transition z`, and set `xₙ₊₁ := z + w`.
  intro t
  let y : ∀ n : ℕ, ToType (G.obj (op n)) :=
    fun n ↦ ConcreteCategory.hom (limit.π G (op n)) t
  have hyc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition G n) (y (n + 1)) =
      y n := by
    intro n
    have h1 := ConcreteCategory.congr_hom (limit.w G (homOfLE (Nat.le_succ n)).op) t
    exact (ConcreteCategory.comp_apply _ _ _).symm.trans h1
  -- The successor step of the recursion.
  have step : ∀ (n : ℕ) (xn : ToType (F.obj (op n))),
      ConcreteCategory.hom (τ.app (op n)) xn = y n →
      ∃ xs : ToType (F.obj (op (n + 1))),
        ConcreteCategory.hom (τ.app (op (n + 1))) xs = y (n + 1) ∧
        ConcreteCategory.hom (SequentialSystem.transition F n) xs = xn := by
    intro n xn hxn
    obtain ⟨z, hz⟩ := hsurj (op (n + 1)) (y (n + 1))
    have hnatz : ConcreteCategory.hom (τ.app (op n))
        (ConcreteCategory.hom (SequentialSystem.transition F n) z) = y n :=
      calc ConcreteCategory.hom (τ.app (op n))
            (ConcreteCategory.hom (SequentialSystem.transition F n) z)
          = ConcreteCategory.hom (SequentialSystem.transition F n ≫ τ.app (op n)) z :=
            (ConcreteCategory.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom (τ.app (op (n + 1)) ≫ SequentialSystem.transition G n)
              z :=
            ConcreteCategory.congr_hom (τ.naturality (homOfLE (Nat.le_succ n)).op) z
        _ = ConcreteCategory.hom (SequentialSystem.transition G n)
              (ConcreteCategory.hom (τ.app (op (n + 1))) z) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (SequentialSystem.transition G n) (y (n + 1)) := by
            rw [hz]
        _ = y n := hyc n
    have hker0 : ConcreteCategory.hom (τ.app (op n))
        (xn - ConcreteCategory.hom (SequentialSystem.transition F n) z) = 0 := by
      rw [map_sub, hxn, hnatz, sub_self]
    obtain ⟨w', hw0, hwt⟩ := hker n _ hker0
    refine ⟨z + w', ?_, ?_⟩
    · rw [map_add, hz, hw0, add_zero]
    · rw [map_add, hwt]
      abel
  -- Construct the compatible lifting family by recursion with choice.
  obtain ⟨x0, hx0⟩ := hsurj (op 0) (y 0)
  let x : ∀ n, {v : ToType (F.obj (op n)) // ConcreteCategory.hom (τ.app (op n)) v = y n} :=
    fun n ↦ Nat.rec ⟨x0, hx0⟩
      (fun m ih ↦ ⟨(step m ih.1 ih.2).choose, (step m ih.1 ih.2).choose_spec.1⟩) n
  have hxc : ∀ n, ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1)).1 =
      (x n).1 :=
    fun n ↦ (step n (x n).1 (x n).2).choose_spec.2
  -- Compatibility for all `m ≤ n` follows from successive compatibility by induction.
  have hxall : ∀ (m n : ℕ) (h : m ≤ n),
      ConcreteCategory.hom (F.map (homOfLE h).op) (x n).1 = (x m).1 := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base =>
      have h1 : (homOfLE (le_refl m)).op = 𝟙 (op m) := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_refl m)).op) (x m).1
          = ConcreteCategory.hom (F.map (𝟙 (op m))) (x m).1 := by rw [h1]
        _ = ConcreteCategory.hom (𝟙 (F.obj (op m))) (x m).1 := by rw [F.map_id]
        _ = (x m).1 := ConcreteCategory.id_apply _
    | succ n hmn ih =>
      have hsplit : (homOfLE (le_trans hmn (Nat.le_succ n))).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := rfl
      calc ConcreteCategory.hom (F.map (homOfLE (le_trans hmn (Nat.le_succ n))).op)
            (x (n + 1)).1
          = ConcreteCategory.hom
              (F.map ((homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op)) (x (n + 1)).1 := by
            rw [hsplit]
        _ = ConcreteCategory.hom
              (F.map (homOfLE (Nat.le_succ n)).op ≫ F.map (homOfLE hmn).op)
              (x (n + 1)).1 := by
            rw [Functor.map_comp]
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op)
              (ConcreteCategory.hom (SequentialSystem.transition F n) (x (n + 1)).1) :=
            ConcreteCategory.comp_apply _ _ _
        _ = ConcreteCategory.hom (F.map (homOfLE hmn).op) (x n).1 := by rw [hxc n]
        _ = (x m).1 := ih
  -- Assemble the family into an element of the limit.
  have hLF : IsLimit ((CategoryTheory.forget AddCommGrpCat.{w}).mapCone (limit.cone F)) :=
    isLimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{w}) (limit.isLimit F)
  have hmemsec : (fun k : ℕᵒᵖ ↦ (x k.unop).1) ∈
      (F ⋙ CategoryTheory.forget AddCommGrpCat.{w}).sections := by
    intro k k' f
    exact hxall k'.unop k.unop (leOfHom f.unop)
  refine ⟨(Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩, ?_⟩
  have hπ : ∀ k : ℕᵒᵖ, ConcreteCategory.hom (limit.π F k)
      ((Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩) =
      (x k.unop).1 :=
    fun k ↦ Types.isLimitEquivSections_symm_apply hLF _ k
  refine Concrete.limit_ext _ _ _ fun k ↦ ?_
  calc ConcreteCategory.hom (limit.π G k) (ConcreteCategory.hom (limMap τ)
        ((Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩))
      = ConcreteCategory.hom (limMap τ ≫ limit.π G k)
          ((Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩) :=
        (ConcreteCategory.comp_apply _ _ _).symm
    _ = ConcreteCategory.hom (limit.π F k ≫ τ.app k)
          ((Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩) :=
        ConcreteCategory.congr_hom (limMap_π τ k) _
    _ = ConcreteCategory.hom (τ.app k) (ConcreteCategory.hom (limit.π F k)
          ((Types.isLimitEquivSections hLF).symm ⟨fun k ↦ (x k.unop).1, hmemsec⟩)) :=
        ConcreteCategory.comp_apply _ _ _
    _ = ConcreteCategory.hom (τ.app k) (x k.unop).1 := by rw [hπ k]
    _ = y k.unop := (x k.unop).2

/-- For a `ℕ`-indexed family of abelian groups with surjective maps
`f n : G (n + 1) → G n`, the "telescope" map `(xₙ)ₙ ↦ (xₙ - f n (xₙ₊₁))ₙ` on the product
is surjective. -/
lemma _root_.AddCommGroup.surjective_sub_shift {G : ℕ → Type w}
    [∀ n, AddCommGroup (G n)] (f : ∀ n, G (n + 1) →+ G n)
    (hf : ∀ n, Function.Surjective (f n)) :
    Function.Surjective (fun (x : ∀ n, G n) n ↦ x n - f n (x (n + 1))) := by
  -- Given `y`, define `x` by recursion: `x 0 := 0` and `x (n + 1)` any `f n`-preimage of
  -- `x n - y n`.
  intro y
  let x : ∀ n, G n := fun n ↦ Nat.rec 0 (fun m xm ↦ (hf m (xm - y m)).choose) n
  have hx : ∀ n, f n (x (n + 1)) = x n - y n := fun n ↦ (hf n (x n - y n)).choose_spec
  refine ⟨x, funext fun n ↦ ?_⟩
  change x n - f n (x (n + 1)) = y n
  rw [hx n, sub_sub_cancel]

end Ab

section Sheaf

variable (F G : Sheaf (ProEt.topology S) Ab.{u + 1})

/-- The sections functor of abelian pro-étale sheaves over (the image in the pro-étale
site of) an object of the affine pro-étale site. -/
private def secW (W : S.AffineProEt) :
    Sheaf (ProEt.topology S) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation (S.ProEt)ᵒᵖ Ab.{u + 1}).obj
      (op ((AffineProEt.toProEt S).obj W))

/-- The sections functor preserves all limits that exist in `Ab`: the forgetful functor
to presheaves creates them and evaluation preserves them. -/
private instance (W : S.AffineProEt) {J : Type w} [Category.{w'} J]
    [HasLimitsOfShape J Ab.{u + 1}] : PreservesLimitsOfShape J (secW W) :=
  inferInstanceAs (PreservesLimitsOfShape J (_ ⋙ _))

/-- The sections functor is additive: addition of morphisms of sheaves is sectionwise. -/
private instance (W : S.AffineProEt) : (secW W).Additive where
  map_add := rfl

/-- Products of epimorphisms of abelian pro-étale sheaves are epimorphisms
(BS, Proposition 3.1.9; the topos of pro-étale sheaves satisfies AB4*). -/
theorem epi_piMap {ι : Type w} [Small.{u + 1} ι]
    (A B : ι → Sheaf (ProEt.topology S) Ab.{u + 1}) (φ : ∀ i, A i ⟶ B i)
    [∀ i, Epi (φ i)] : Epi (Limits.Pi.map φ) := by
  -- By `AffineProEt.epi_of_forall_surjective_app` it suffices to prove surjectivity on
  -- sections over weakly contractible `W`. The sections functor `secW W` preserves
  -- limits, so `secW W (∏ᶜ A) ≅ ∏ (secW W (A i))` compatibly with `Pi.map φ` and the
  -- function-product map; each `secW W (φ i)` is surjective by
  -- `AffineProEt.surjective_app_of_epi`, and products of surjective maps of types are
  -- surjective.
  refine AffineProEt.epi_of_forall_surjective_app _ fun W hW ↦ ?_
  have hA : IsLimit ((secW W).mapCone (limit.cone (Discrete.functor A))) :=
    isLimitOfPreserves (secW W) (limit.isLimit (Discrete.functor A))
  have hB : IsLimit ((secW W).mapCone (limit.cone (Discrete.functor B))) :=
    isLimitOfPreserves (secW W) (limit.isLimit (Discrete.functor B))
  have hbijA := AddCommGrpCat.bijective_components_of_isLimit hA
  have hbijB := AddCommGrpCat.bijective_components_of_isLimit hB
  intro t
  -- Lift the components of `t` along the levelwise surjections.
  have hsec : ∀ i, ∃ u, ConcreteCategory.hom
      ((φ i).hom.app (op ((AffineProEt.toProEt S).obj W))) u =
      ConcreteCategory.hom ((secW W).map (Pi.π B i)) t :=
    fun i ↦ AffineProEt.surjective_app_of_epi (φ i) hW _
  choose u hu using hsec
  -- Reassemble the lifts into a section of the product.
  obtain ⟨s, hs⟩ := hbijA.2 u
  have hsi : ∀ i, ConcreteCategory.hom ((secW W).map (Pi.π A i)) s = u i :=
    fun i ↦ congrFun hs i
  refine ⟨s, hbijB.1 ?_⟩
  funext i
  have e1 : (secW W).map (Limits.Pi.map φ) ≫ (secW W).map (Pi.π B i) =
      (secW W).map (Pi.π A i) ≫ (secW W).map (φ i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Limits.Pi.map_π]
  calc ConcreteCategory.hom ((secW W).map (Pi.π B i))
        (ConcreteCategory.hom ((secW W).map (Limits.Pi.map φ)) s)
      = ConcreteCategory.hom ((secW W).map (Limits.Pi.map φ) ≫ (secW W).map (Pi.π B i))
          s := (ConcreteCategory.comp_apply _ _ _).symm
    _ = ConcreteCategory.hom ((secW W).map (Pi.π A i) ≫ (secW W).map (φ i)) s :=
        ConcreteCategory.congr_hom e1 s
    _ = ConcreteCategory.hom ((secW W).map (φ i))
          (ConcreteCategory.hom ((secW W).map (Pi.π A i)) s) :=
        ConcreteCategory.comp_apply _ _ _
    _ = ConcreteCategory.hom ((secW W).map (φ i)) (u i) := by rw [hsi i]
    _ = ConcreteCategory.hom ((secW W).map (Pi.π B i)) t := hu i

variable {T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1})}

/-- **Mittag-Leffler for pro-étale abelian sheaves** (BS, Proposition 3.1.10; blueprint
`prop:lim-exact-replete`): the limit of a levelwise short exact sequence of inverse
systems is short exact, provided the transition maps of the subobject system are
epimorphisms. -/
theorem shortExact_limMap
    (hT : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
      (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)).ShortExact)
    (h1 : ∀ n, Epi (SequentialSystem.transition T.X₁ n)) :
    (T.map lim).ShortExact := by
  -- * `Mono ((T.map lim).f)` and exactness: levelwise, `T.X₁` is the kernel of `T.g`;
  --   kernels in functor categories are pointwise, and `lim` preserves kernels, so
  --   `(T.map lim).f` is a kernel of `(T.map lim).g`.
  -- * `Epi ((T.map lim).g)`: by `AffineProEt.epi_of_forall_surjective_app` reduce to
  --   surjectivity on sections over weakly contractible `W` and apply
  --   `AddCommGrpCat.surjective_limMap` to the whiskered transformation.
  -- The kernel fork of `T.g` in the functor category, limiting because it is pointwise
  -- limiting.
  have hK : IsLimit (KernelFork.ofι T.f T.zero) := by
    refine evaluationJointlyReflectsLimits _ fun k ↦ ?_
    haveI := (hT k).mono_f
    exact (isLimitMapConeForkEquiv'
      ((CategoryTheory.evaluation ℕᵒᵖ (Sheaf (ProEt.topology S) Ab.{u + 1})).obj k)
      T.zero).symm ((hT k).exact.fIsKernel)
  -- `lim` preserves this kernel fork.
  haveI hpl : PreservesLimitsOfSize.{0, 0}
      (lim : (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) ⥤ _) :=
    Adjunction.rightAdjoint_preservesLimits constLimAdj
  haveI : PreservesLimit (parallelPair T.g 0)
      (lim : (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) ⥤ _) :=
    PreservesLimitsOfShape.preservesLimit
  have hK' : IsLimit (KernelFork.ofι ((T.map lim).f) ((T.map lim).zero)) :=
    isLimitForkMapOfIsLimit' lim T.zero hK
  haveI hmono : Mono ((T.map lim).f) := mono_of_isLimit_fork hK'
  have hexact : (T.map lim).Exact := ShortComplex.exact_of_f_is_kernel _ hK'
  -- The epimorphism part, via sections over weakly contractible objects.
  have hepi : Epi ((T.map lim).g) := by
    refine AffineProEt.epi_of_forall_surjective_app _ fun W hW ↦ ?_
    -- Surjectivity of the limit of the whiskered systems of sections.
    have hsurj : Function.Surjective
        (ConcreteCategory.hom (limMap (Functor.whiskerRight T.g (secW W)))) := by
      refine AddCommGrpCat.surjective_limMap (Functor.whiskerRight T.g (secW W)) ?_ ?_
      · intro k
        haveI : Epi (T.g.app k) := (hT k).epi_g
        exact AffineProEt.surjective_app_of_epi (T.g.app k) hW
      · intro n x hx
        -- Sections over `W` of the levelwise short exact sequence are exact.
        have hex : ((T.map ((CategoryTheory.evaluation ℕᵒᵖ
            (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (op n))).map (secW W)).Exact := by
          haveI := (hT (op n)).mono_f
          exact ShortComplex.Exact.map_of_mono_of_preservesKernel (hT (op n)).exact
            (secW W) (hT (op n)).mono_f inferInstance
        rw [ShortComplex.ab_exact_iff] at hex
        obtain ⟨a, ha⟩ := hex x hx
        -- Lift `a` along the transition of `T.X₁`, which is surjective on sections.
        haveI : Epi (SequentialSystem.transition T.X₁ n) := h1 n
        obtain ⟨a', ha'⟩ := AffineProEt.surjective_app_of_epi
          (SequentialSystem.transition T.X₁ n) hW a
        refine ⟨ConcreteCategory.hom ((secW W).map (T.f.app (op (n + 1)))) a', ?_, ?_⟩
        · have hzero : T.f.app (op (n + 1)) ≫ T.g.app (op (n + 1)) =
              (0 : T.X₁.obj (op (n + 1)) ⟶ T.X₃.obj (op (n + 1))) := by
            rw [← NatTrans.comp_app, T.zero]
            rfl
          calc ConcreteCategory.hom ((secW W).map (T.g.app (op (n + 1))))
                (ConcreteCategory.hom ((secW W).map (T.f.app (op (n + 1)))) a')
              = ConcreteCategory.hom ((secW W).map (T.f.app (op (n + 1))) ≫
                  (secW W).map (T.g.app (op (n + 1)))) a' :=
                (ConcreteCategory.comp_apply _ _ _).symm
            _ = ConcreteCategory.hom
                  ((secW W).map (T.f.app (op (n + 1)) ≫ T.g.app (op (n + 1)))) a' :=
                ConcreteCategory.congr_hom ((secW W).map_comp _ _).symm a'
            _ = ConcreteCategory.hom ((secW W).map
                  (0 : T.X₁.obj (op (n + 1)) ⟶ T.X₃.obj (op (n + 1)))) a' := by
                rw [hzero]
            _ = ConcreteCategory.hom
                  (0 : (secW W).obj (T.X₁.obj (op (n + 1))) ⟶
                    (secW W).obj (T.X₃.obj (op (n + 1)))) a' :=
                ConcreteCategory.congr_hom ((secW W).map_zero _ _) a'
            _ = 0 := AddCommGrpCat.hom_zero_apply' a'
        · have hnat : T.f.app (op (n + 1)) ≫ SequentialSystem.transition T.X₂ n =
              SequentialSystem.transition T.X₁ n ≫ T.f.app (op n) :=
            (T.f.naturality (homOfLE (Nat.le_succ n)).op).symm
          calc ConcreteCategory.hom (SequentialSystem.transition (T.X₂ ⋙ secW W) n)
                (ConcreteCategory.hom ((secW W).map (T.f.app (op (n + 1)))) a')
              = ConcreteCategory.hom ((secW W).map (T.f.app (op (n + 1))) ≫
                  (secW W).map (SequentialSystem.transition T.X₂ n)) a' :=
                (ConcreteCategory.comp_apply _ _ _).symm
            _ = ConcreteCategory.hom ((secW W).map
                  (T.f.app (op (n + 1)) ≫ SequentialSystem.transition T.X₂ n)) a' :=
                ConcreteCategory.congr_hom ((secW W).map_comp _ _).symm a'
            _ = ConcreteCategory.hom ((secW W).map
                  (SequentialSystem.transition T.X₁ n ≫ T.f.app (op n))) a' := by
                rw [hnat]
            _ = ConcreteCategory.hom ((secW W).map (SequentialSystem.transition T.X₁ n) ≫
                  (secW W).map (T.f.app (op n))) a' :=
                ConcreteCategory.congr_hom ((secW W).map_comp _ _) a'
            _ = ConcreteCategory.hom ((secW W).map (T.f.app (op n)))
                  (ConcreteCategory.hom
                    ((secW W).map (SequentialSystem.transition T.X₁ n)) a') :=
                ConcreteCategory.comp_apply _ _ _
            _ = ConcreteCategory.hom ((secW W).map (T.f.app (op n))) a :=
                congrArg (fun z ↦ ConcreteCategory.hom
                  ((secW W).map (T.f.app (op n))) z) ha'
            _ = x := ha
    -- Transfer surjectivity through the limit-comparison isomorphisms.
    intro t
    obtain ⟨v, hv⟩ := hsurj
      (ConcreteCategory.hom (preservesLimitIso (secW W) T.X₃).hom t)
    refine ⟨ConcreteCategory.hom (preservesLimitIso (secW W) T.X₂).inv v, ?_⟩
    have hsq : (secW W).map (limMap T.g) ≫ (preservesLimitIso (secW W) T.X₃).hom =
        (preservesLimitIso (secW W) T.X₂).hom ≫ limMap (Functor.whiskerRight T.g (secW W)) :=
      (preservesLimitNatIso (secW W)).hom.naturality T.g
    have hsq' : (preservesLimitIso (secW W) T.X₂).inv ≫ (secW W).map (limMap T.g) =
        limMap (Functor.whiskerRight T.g (secW W)) ≫ (preservesLimitIso (secW W) T.X₃).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    calc ConcreteCategory.hom ((secW W).map (limMap T.g))
          (ConcreteCategory.hom (preservesLimitIso (secW W) T.X₂).inv v)
        = ConcreteCategory.hom
            ((preservesLimitIso (secW W) T.X₂).inv ≫ (secW W).map (limMap T.g)) v :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (limMap (Functor.whiskerRight T.g (secW W)) ≫
            (preservesLimitIso (secW W) T.X₃).inv) v :=
          ConcreteCategory.congr_hom hsq' v
      _ = ConcreteCategory.hom (preservesLimitIso (secW W) T.X₃).inv
            (ConcreteCategory.hom (limMap (Functor.whiskerRight T.g (secW W))) v) :=
          ConcreteCategory.comp_apply _ _ _
      _ = ConcreteCategory.hom (preservesLimitIso (secW W) T.X₃).inv
            (ConcreteCategory.hom (preservesLimitIso (secW W) T.X₃).hom t) := by
          rw [hv]
      _ = ConcreteCategory.hom ((preservesLimitIso (secW W) T.X₃).hom ≫
            (preservesLimitIso (secW W) T.X₃).inv) t :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom (𝟙 ((secW W).obj (limit T.X₃))) t :=
          ConcreteCategory.congr_hom (Iso.hom_inv_id _) t
      _ = t := ConcreteCategory.id_apply t
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

variable (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1})

/-- The telescope endomorphism `1 - shift` of `∏ₙ G.obj (op n)`. -/
noncomputable def telescope :
    (∏ᶜ fun n : ℕ ↦ G.obj (op n)) ⟶ (∏ᶜ fun n : ℕ ↦ G.obj (op n)) :=
  𝟙 _ - Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ SequentialSystem.transition G n

/-- The canonical comparison from the sequential limit to the product. -/
noncomputable def limToPi : (lim.obj G : Sheaf (ProEt.topology S) Ab.{u + 1}) ⟶
    (∏ᶜ fun n : ℕ ↦ G.obj (op n)) :=
  Pi.lift fun n ↦ limit.π G (op n)

/-- The `n`-th component of the telescope morphism. -/
private lemma telescope_comp_π (n : ℕ) :
    telescope G ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n =
      Pi.π (fun n : ℕ ↦ G.obj (op n)) n -
        Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + 1) ≫ SequentialSystem.transition G n := by
  simp only [telescope, Preadditive.sub_comp, Category.id_comp, Pi.lift_π]

/-- The `n`-th component of the comparison morphism. -/
private lemma limToPi_π (n : ℕ) :
    limToPi G ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n = limit.π G (op n) := by
  simp only [limToPi, Pi.lift_π]

lemma limToPi_comp_telescope : limToPi G ≫ telescope G = 0 := by
  -- Check componentwise with `Limits.Pi.hom_ext`: the `n`-th component of the composite
  -- is `limit.π G (op n) - limit.π G (op (n+1)) ≫ transition`, which vanishes by
  -- `limit.w`.
  refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, telescope_comp_π, Preadditive.comp_sub, zero_comp, limToPi_π,
    ← Category.assoc, limToPi_π, sub_eq_zero]
  exact (limit.w G (homOfLE (Nat.le_succ n)).op).symm

/-- **The Milnor sequence** `0 → lim G → ∏ Gₙ → ∏ Gₙ → 0` for an inverse system of
abelian pro-étale sheaves with epimorphic transition maps. -/
theorem shortExact_telescope (hG : ∀ n, Epi (SequentialSystem.transition G n)) :
    (ShortComplex.mk (limToPi G) (telescope G) (limToPi_comp_telescope G)).ShortExact := by
  -- * `Mono (limToPi G)` and exactness: `limToPi G` is the kernel of `telescope G`.
  -- * `Epi (telescope G)`: reduce to sections over weakly contractible `W` and apply
  --   `AddCommGroup.surjective_sub_shift`.
  -- A morphism into the product killed by the telescope has successively compatible
  -- components.
  have hcompat : ∀ {Z : Sheaf (ProEt.topology S) Ab.{u + 1}}
      (h : Z ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n)), h ≫ telescope G = 0 → ∀ n,
      (h ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) (n + 1)) ≫ SequentialSystem.transition G n =
        h ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n := by
    intro Z h hh n
    have hc : h ≫ telescope G ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n = 0 := by
      rw [← Category.assoc, hh, zero_comp]
    rw [telescope_comp_π, Preadditive.comp_sub, sub_eq_zero] at hc
    rw [Category.assoc]
    exact hc.symm
  -- The kernel fork given by `limToPi G` is limiting.
  have hfork : IsLimit (KernelFork.ofι (limToPi G) (limToPi_comp_telescope G)) := by
    refine KernelFork.IsLimit.ofι _ _
      (fun {Z} h hh ↦ limit.lift G
        ⟨Z, SequentialSystem.natTransOfSucc
          (fun n ↦ h ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n) (hcompat h hh)⟩)
      (fun {Z} h hh ↦ ?_) (fun {Z} h hh m hm ↦ ?_)
    · refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
      rw [Category.assoc, limToPi_π, limit.lift_π]
      rfl
    · refine limit.hom_ext fun k ↦ ?_
      obtain ⟨n⟩ := k
      rw [limit.lift_π]
      change m ≫ limit.π G (op n) = h ≫ Pi.π (fun n : ℕ ↦ G.obj (op n)) n
      rw [← limToPi_π, ← Category.assoc, hm]
  haveI hmono : Mono (limToPi G) := mono_of_isLimit_fork hfork
  have hexact : (ShortComplex.mk (limToPi G) (telescope G)
      (limToPi_comp_telescope G)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ hfork
  -- The telescope is an epimorphism: check on sections over weakly contractible objects.
  have hepi : Epi (telescope G) := by
    refine AffineProEt.epi_of_forall_surjective_app _ fun W hW ↦ ?_
    have hP : IsLimit
        ((secW W).mapCone (limit.cone (Discrete.functor fun n : ℕ ↦ G.obj (op n)))) :=
      isLimitOfPreserves (secW W) (limit.isLimit _)
    have hbij := AddCommGrpCat.bijective_components_of_isLimit hP
    intro t
    have hstep : ∀ n, Function.Surjective
        (ConcreteCategory.hom ((secW W).map (SequentialSystem.transition G n))) := by
      intro n
      haveI : Epi (SequentialSystem.transition G n) := hG n
      exact AffineProEt.surjective_app_of_epi (SequentialSystem.transition G n) hW
    -- Solve the telescope equation on sections.
    obtain ⟨x, hx⟩ := AddCommGroup.surjective_sub_shift
      (G := fun n ↦ ToType ((secW W).obj (G.obj (op n))))
      (fun n ↦ ConcreteCategory.hom ((secW W).map (SequentialSystem.transition G n)))
      hstep
      (fun i ↦ ConcreteCategory.hom
        ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) t)
    obtain ⟨s, hs⟩ := hbij.2 x
    have hsi : ∀ i, ConcreteCategory.hom
        ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) s = x i :=
      fun i ↦ congrFun hs i
    have hxi : ∀ i, x i - ConcreteCategory.hom
        ((secW W).map (SequentialSystem.transition G i)) (x (i + 1)) =
        ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) t :=
      fun i ↦ congrFun hx i
    refine ⟨s, hbij.1 ?_⟩
    funext i
    have e1 : (secW W).map (telescope G) ≫
        (secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i) =
        (secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i) -
          (secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) (i + 1) ≫
            SequentialSystem.transition G i) := by
      rw [← Functor.map_comp, telescope_comp_π, Functor.map_sub]
    calc ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i))
          (ConcreteCategory.hom ((secW W).map (telescope G)) s)
        = ConcreteCategory.hom ((secW W).map (telescope G) ≫
            (secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) s :=
          (ConcreteCategory.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i) -
            (secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) (i + 1) ≫
              SequentialSystem.transition G i)) s :=
          ConcreteCategory.congr_hom e1 s
      _ = ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) s -
            ConcreteCategory.hom ((secW W).map
              (Pi.π (fun n : ℕ ↦ G.obj (op n)) (i + 1) ≫
                SequentialSystem.transition G i)) s :=
          AddCommGrpCat.hom_sub_apply' _ _ s
      _ = ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) s -
            ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) (i + 1)) ≫
              (secW W).map (SequentialSystem.transition G i)) s := by
          rw [Functor.map_comp]
      _ = ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) s -
            ConcreteCategory.hom ((secW W).map (SequentialSystem.transition G i))
              (ConcreteCategory.hom
                ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) (i + 1))) s) := by
          rw [ConcreteCategory.comp_apply]
      _ = x i - ConcreteCategory.hom ((secW W).map (SequentialSystem.transition G i))
            (x (i + 1)) := by
          rw [hsi i, hsi (i + 1)]
      _ = ConcreteCategory.hom ((secW W).map (Pi.π (fun n : ℕ ↦ G.obj (op n)) i)) t :=
          hxi i
  exact ShortComplex.ShortExact.mk' hexact hmono hepi

end Sheaf

end AlgebraicGeometry.Scheme.ProEt
