/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Proetale.Topology.Comparison.Acyclicity
import Proetale.Topology.Comparison.FreeSheaf

/-!
# Sheaves of continuous maps on the pro-étale site and constant sheaves

For a topological abelian group `M`, the presheaf `U ↦ C(U, M)` is a sheaf for the fpqc
topology (`AlgebraicGeometry.continuousMapPresheafAb`), hence restricts to a sheaf on the
pro-étale site of a scheme `X`; for `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ`. We define
this restriction in general (`AlgebraicGeometry.Scheme.ProEt.topologicalSheaf`) together
with its `ULift` to `Ab.{u + 1}` (`ProEt.topologicalSheafLifted`), and prove the key
comparison (BS, Lemma 4.2.12): for a *discrete* abelian group `M`, the canonical map
from the constant sheaf is an isomorphism

- `AlgebraicGeometry.Scheme.ProEt.constantToTopologicalSheafLifted`
- `AlgebraicGeometry.Scheme.ProEt.isIso_constantToTopologicalSheafLifted`
- `AlgebraicGeometry.Scheme.ProEt.sheafPullbackConstantTopologicalIso` (combination with
  the pullback of the constant sheaf from the étale site).

The point is that a continuous map `U → M` to a discrete group is locally constant: its
fibers form a clopen cover of `U`, which is a pro-étale cover, and on each piece the
section is constant. Injectivity is local as well (over the empty scheme the empty sieve
is a cover).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

namespace ProEt

section Topological

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- The sheaf `U ↦ C(U, M)` on the pro-étale site of `X`, for a topological abelian
group `M`. For `M = ℤ_[ℓ]` this is `X.ellAdicSheaf ℓ` (definitionally, see
`ellAdicSheaf_eq_topologicalSheaf`). -/
noncomputable def topologicalSheaf : Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb M, .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

lemma ellAdicSheaf_eq_topologicalSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    X.ellAdicSheaf ℓ = topologicalSheaf X ℤ_[ℓ] :=
  rfl

/-- The sections of `topologicalSheaf X M` over `U` are the continuous maps
`U.left → M`. -/
lemma topologicalSheaf_obj (U : X.ProEt) :
    (topologicalSheaf X M).obj.obj (op U) = AddCommGrpCat.of C(U.left, M) :=
  rfl

/-- The `ULift` of `topologicalSheaf X M` to `Ab.{u + 1}`. -/
noncomputable def topologicalSheafLifted : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (topologicalSheaf X M)

/-- Postcomposition with a continuous additive map, as a morphism of the lifted
sheaves of continuous maps. -/
noncomputable def topologicalSheafLiftedMap {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] (f : M →+ M') (hf : Continuous f) :
    topologicalSheafLifted X M ⟶ topologicalSheafLifted X M' where
  hom :=
    { app := fun U ↦ AddCommGrpCat.uliftFunctor.{u + 1}.map
        (AddCommGrpCat.ofHom
          (AddMonoidHom.mk' (fun g ↦ (ContinuousMap.mk f hf).comp g)
            (fun g₁ g₂ ↦ by ext x; exact map_add f _ _)))
      naturality := by
        -- Componentwise both composites send a continuous map `g : U.left → M` to
        -- `f ∘ g ∘ (restriction)`; this is associativity of composition.
        intro U V h
        apply ConcreteCategory.hom_ext
        intro g
        rfl }

end Topological

section Discrete

variable (M : Type) [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]
  [DiscreteTopology M]

/-- The canonical morphism from the constant sheaf with values `M` to the sheaf of
continuous `M`-valued maps, for a discrete abelian group `M`: it is the adjoint of the
map sending `m` to the constant function with value `m` on the terminal object. -/
noncomputable def constantToTopologicalSheafLifted :
    (constantSheaf (ProEt.topology X) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} M)) ⟶
      topologicalSheafLifted X M :=
  ((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
    (isTerminalMkIdProEt X)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })

/-- The presheaf-level constant-functions morphism: the transpose under the
constant-presheaf adjunction of the map sending `m` to the constant function with
value `m` on the terminal object. Its sheafification-transpose is
`constantToTopologicalSheafLifted`. -/
private noncomputable def constantToTopologicalPresheaf :
    (Functor.const (X.ProEt)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} M)) ⟶
      (topologicalSheafLifted X M).obj :=
  ((constantPresheafAdj Ab.{u + 1} (isTerminalMkIdProEt X)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      { toFun := fun m ↦ ULift.up ⟨fun _ ↦ m.down, continuous_const⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl })

omit [DiscreteTopology M] in
/-- The component of `constantToTopologicalPresheaf` at `V` sends `m` to the constant
function with value `m` on `V.left`: restricting a constant function along the unique
map to the terminal object yields a constant function, definitionally. -/
private lemma constantToTopologicalPresheaf_app (V : (X.ProEt)ᵒᵖ) (m : ULift.{u + 1} M) :
    (constantToTopologicalPresheaf X M).app V m =
      ULift.up (⟨fun _ ↦ m.down, continuous_const⟩ : C(V.unop.left, M)) :=
  rfl

omit [DiscreteTopology M] in
/-- `constantToTopologicalSheafLifted` is the sheafification-transpose of
`constantToTopologicalPresheaf`. -/
private lemma constantToTopologicalSheafLifted_eq :
    constantToTopologicalSheafLifted X M =
      (presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
          (constantToTopologicalPresheaf X M) ≫
        (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.app
          (topologicalSheafLifted X M) := by
  -- The right-hand side is, by definition of `Adjunction.homEquiv`, the transpose of
  -- `constantToTopologicalPresheaf` under the sheafification adjunction; the claim is
  -- then the compatibility of the hom-equivalence of a composite adjunction with the
  -- hom-equivalences of the factors (`Adjunction.comp_homEquiv`).
  have h1 : constantToTopologicalSheafLifted X M =
      ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).homEquiv
          ((Functor.const (X.ProEt)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} M)))
          (topologicalSheafLifted X M)).symm
        (constantToTopologicalPresheaf X M) := by
    unfold constantToTopologicalSheafLifted constantSheafAdj
    rw [Adjunction.comp_homEquiv]
    rfl
  exact h1

omit [DiscreteTopology M] in
/-- `constantToTopologicalPresheaf` is locally injective: two constants agreeing as
functions on a nonempty scheme are equal, and over the empty scheme the empty sieve
is covering. -/
private lemma isLocallyInjective_constantToTopologicalPresheaf :
    Presheaf.IsLocallyInjective (ProEt.topology X) (constantToTopologicalPresheaf X M) := by
  constructor
  intro V m₁ m₂ h
  by_cases hV : Nonempty V.unop.left
  · obtain ⟨v⟩ := hV
    have h1 := (constantToTopologicalPresheaf_app X M V m₁).symm.trans
      (h.trans (constantToTopologicalPresheaf_app X M V m₂))
    have h2 : m₁ = m₂ :=
      ULift.ext _ _ (ContinuousMap.congr_fun (congrArg ULift.down h1) v)
    rw [h2, Presheaf.equalizerSieve_self_eq_top]
    exact (ProEt.topology X).top_mem _
  · haveI : IsEmpty V.unop.left := not_nonempty_iff.mp hV
    exact (ProEt.topology X).superset_covering bot_le (ProEt.bot_mem_topology V.unop)

/-- `constantToTopologicalPresheaf` is locally surjective: a continuous map to the
discrete group `M` is locally constant; its clopen fibers form a pro-étale cover by
open immersions, on each piece of which the section is the image of a constant. -/
private lemma isLocallySurjective_constantToTopologicalPresheaf :
    Presheaf.IsLocallySurjective (ProEt.topology X) (constantToTopologicalPresheaf X M) := by
  constructor
  intro V s
  let g : C(V.left, M) := s.down
  -- The fibers of `g` are open (even clopen) since `M` is discrete.
  let O : M → V.left.Opens := fun m ↦
    ⟨g ⁻¹' {m}, (isOpen_discrete _).preimage g.continuous⟩
  -- The fibers as pro-étale objects over `X`: open immersions are étale, hence weakly
  -- étale, and weakly étale morphisms are stable under composition.
  let W : M → X.ProEt := fun m ↦ ProEt.mk ((O m).ι ≫ V.hom)
  let j : ∀ m : M, W m ⟶ V := fun m ↦
    MorphismProperty.Over.homMk (O m).ι rfl trivial
  have hoi : ∀ i : ULift.{u} M, IsOpenImmersion (j i.down).left := fun i ↦
    inferInstanceAs (IsOpenImmersion (O i.down).ι)
  have hsurj : ∀ x : V.left, ∃ i : ULift.{u} M,
      x ∈ Set.range ((j i.down).left.base) := fun x ↦
    ⟨ULift.up (g x), ⟨x, rfl⟩, rfl⟩
  have hcov : Sieve.generate (Presieve.ofArrows (fun i : ULift.{u} M ↦ W i.down)
      (fun i ↦ j i.down)) ∈ ProEt.topology X V :=
    ProEt.generate_ofArrows_mem_topology _ hoi hsurj
  refine (ProEt.topology X).superset_covering ?_ hcov
  rintro T f ⟨Z, h', l, ⟨k⟩, rfl⟩
  refine ⟨ULift.up k.down, ?_⟩
  -- On the fiber over `k.down`, the section `g` restricts to the constant `k.down`.
  have key : ∀ z : T.left, g ((h' ≫ j k.down).left.base z) = k.down := fun z ↦
    ((h'.left.base z).property : g (h'.left.base z).val ∈ ({k.down} : Set M))
  have e1 : (constantToTopologicalPresheaf X M).app (op T) (ULift.up k.down) =
      ULift.up (⟨fun _ ↦ k.down, continuous_const⟩ : C(T.left, M)) :=
    constantToTopologicalPresheaf_app X M (op T) (ULift.up k.down)
  have e2 : (ULift.up (⟨fun _ ↦ k.down, continuous_const⟩ : C(T.left, M)) :
        ULift.{u + 1} C(T.left, M)) =
      ULift.up (g.comp ((h' ≫ j k.down).left.base.hom)) :=
    congrArg ULift.up (ContinuousMap.ext fun z ↦ (key z).symm)
  have e3 : (topologicalSheafLifted X M).obj.map (h' ≫ j k.down).op s =
      ULift.up (g.comp ((h' ≫ j k.down).left.base.hom)) := rfl
  exact e1.trans (e2.trans e3.symm)

/-- **The constant sheaf on the pro-étale site is the sheaf of continuous maps**
(BS, Lemma 4.2.12) for a discrete abelian group `M`. -/
instance isIso_constantToTopologicalSheafLifted :
    IsIso (constantToTopologicalSheafLifted X M) := by
  -- The sheaf category is abelian, hence balanced; it suffices to prove that the map
  -- is a monomorphism and an epimorphism.
  --
  -- **Epi** (via `Sheaf.isLocallySurjective_iff_epi'`): let `U : X.ProEt` and let
  -- `g : C(U.left, M)` be a section of the target (after `ULift`). The fibers
  -- `g ⁻¹' {m}` are clopen (`IsOpen` since `M` is discrete and `g` continuous; closed
  -- as complement of the union of the others), so the open subschemes
  -- `V m := U.left ∣_ᵤ ⟨g ⁻¹' {m}, _⟩` (`Scheme.restrict`/`Scheme.Opens` API), as
  -- pro-étale objects over `X` via the composites with `U.hom` (open immersions are
  -- weakly étale: étale implies weakly étale, plus composition stability — see how the
  -- disjoint-union pieces are built in `exists_surjective_factorization_disjoint`,
  -- `Proetale/Topology/Comparison/Acyclicity.lean`), give a jointly surjective family
  -- of open immersions `V m ⟶ U`, hence a covering sieve by
  -- `ProEt.generate_ofArrows_mem_topology` (same file; index the family by
  -- `ULift.{u} M` if a `Type u` index is required). On each piece, `g` restricts to
  -- the constant function with value `m`, which is in the image of the map (factor
  -- the adjoint through `Presheaf.imageSieve` membership: the constant section over
  -- `V m` is the image of the global section `m` of the constant sheaf restricted to
  -- `V m`; relate the adjoint to the presheaf-level constant-functions map via
  -- `Adjunction.homEquiv` unfolding and `toSheafify`).
  --
  -- **Mono**: via local injectivity. The morphism is, up to the canonical isomorphism
  -- `presheafToSheaf`-image, the sheafification of the presheaf morphism
  -- `ψ : (constant presheaf) ⟶ (continuous maps presheaf)` given by constant
  -- functions. `ψ` is locally injective: if two constants `m₁, m₂` agree as functions
  -- on `U.left`, then either `U.left` is nonempty and `m₁ = m₂` (so the top sieve
  -- works), or `U.left` is empty and the empty sieve is covering
  -- (`ProEt.bot_mem_topology`, cf. its use in
  -- `Proetale/Topology/Comparison/Acyclicity.lean`). Local injectivity passes to the
  -- sheafification (`Presheaf.isLocallyInjective` API: `toSheafify` is locally
  -- bijective and local injectivity is stable under composition with locally
  -- injective maps — see `Mathlib.CategoryTheory.Sites.LocallyInjective`), and a
  -- locally injective morphism of sheaves is a monomorphism
  -- (`Sheaf.mono_of_isLocallyInjective` or the corresponding `iff`).
  --
  -- (Implementation note: instead of mono + epi + balanced, we directly observe that
  -- the presheaf morphism `constantToTopologicalPresheaf` is locally bijective by the
  -- two arguments above, hence a `J.W`-equivalence, so its sheafification is an
  -- isomorphism; the map in question is the sheafification composed with the counit
  -- of the sheafification adjunction at a sheaf, which is an isomorphism.)
  haveI := isLocallyInjective_constantToTopologicalPresheaf X M
  haveI := isLocallySurjective_constantToTopologicalPresheaf X M
  haveI : IsIso ((presheafToSheaf (ProEt.topology X) Ab.{u + 1}).map
      (constantToTopologicalPresheaf X M)) := by
    rw [← GrothendieckTopology.W_iff]
    exact (ProEt.topology X).W_of_isLocallyBijective _
  rw [constantToTopologicalSheafLifted_eq]
  infer_instance

/-- The pullback to the pro-étale site of the constant étale sheaf with values `M` is
the sheaf of continuous `M`-valued maps, for `M` discrete. -/
noncomputable def sheafPullbackConstantTopologicalIso :
    (ProEt.sheafPullback X Ab.{u + 1}).obj
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} M))) ≅
      topologicalSheafLifted X M :=
  sheafPullbackConstantIso X (AddCommGrpCat.of (ULift.{u + 1} M)) ≪≫
    asIso (constantToTopologicalSheafLifted X M)

/-- Naturality of `constantToTopologicalSheafLifted` in the coefficient group: for an
additive map `f : M →+ M'` of discrete groups, the square with the constant-sheaf
functor on the left and postcomposition on the right commutes. -/
lemma constantToTopologicalSheafLifted_naturality {M' : Type} [TopologicalSpace M']
    [AddCommGroup M'] [IsTopologicalAddGroup M'] [DiscreteTopology M'] (f : M →+ M') :
    constantToTopologicalSheafLifted X M ≫
        topologicalSheafLiftedMap X M (f := f) (continuous_of_discreteTopology) =
      (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f)) ≫
        constantToTopologicalSheafLifted X M' := by
  -- Both sides are adjoints (under `constantSheafAdj ... |>.homEquiv`) of the same map
  -- `ULift M ⟶ (sections of topologicalSheafLifted X M' over the terminal object)`,
  -- by naturality of the adjunction hom-equivalence
  -- (`Adjunction.homEquiv_naturality_left_symm` / `_right_symm`); compute both
  -- transposes on elements (`m ↦` constant function with value `f m`).
  unfold constantToTopologicalSheafLifted
  refine (((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
      (isTerminalMkIdProEt X)).homEquiv_naturality_right_symm _
        (topologicalSheafLiftedMap X M (f := f)
          continuous_of_discreteTopology)).symm.trans ?_).trans
    ((constantSheafAdj (ProEt.topology X) Ab.{u + 1}
      (isTerminalMkIdProEt X)).homEquiv_naturality_left_symm
        (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom f)) _)
  refine congrArg _ ?_
  apply ConcreteCategory.hom_ext
  intro m
  rfl

end Discrete

end ProEt

end AlgebraicGeometry.Scheme
