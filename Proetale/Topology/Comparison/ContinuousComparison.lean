/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.CohomologyComparison
import Proetale.Topology.Comparison.RepleteExact
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.Product
import Proetale.Mathlib.CategoryTheory.Abelian.SequentialSystem

/-!
# Comparison of continuous étale cohomology with pro-étale cohomology

Let `S` be a scheme and let `(Fₙ)ₙ` be an inverse system of abelian sheaves on the small
étale site of `S` with epimorphic transition maps. We compare the *continuous étale
cohomology* of `(Fₙ)ₙ` in the sense of Jannsen with the pro-étale cohomology of the
sheaf `lim ν^* Fₙ` on the pro-étale site (BS, Proposition 5.6.2; blueprint
`thm:comparison-continuous`).

## Definitions

- `AlgebraicGeometry.Scheme.continuousH F n`: continuous étale cohomology of the inverse
  system `F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab`, defined as the `Ext`-group
  `Ext (Δℤ) F n` in the abelian category of inverse systems, from the constant system on
  the constant sheaf `ℤ` (blueprint `def:continuous-etale-cohomology`). Since
  `Hom(Δℤ, F) ≅ Γ(X, lim Fₙ)` (see `continuousHZeroAddEquiv`), this `Ext`-group is the
  `n`-th right derived functor of `(Fₙ)ₙ ↦ Γ(X, lim Fₙ)` in the sense of Jannsen.

## Main result

- `AlgebraicGeometry.Scheme.nonempty_continuousH_addEquiv_H_limit`:
  `H^i_cont(X, (Fₙ)) ≅ H^i(X_proét, lim ν^* Fₙ)` for systems with epimorphic transition
  maps.

The proof is by dimension shifting. Embed `F` into an injective system `I` with quotient
`Q`. Injective systems have split epimorphic transitions and injective levels
(`Proetale.Mathlib.CategoryTheory.Abelian.SequentialSystem`), so `lim ν^* Iₙ` is acyclic:
by the Milnor sequence (`ProEt.shortExact_telescope`) this reduces to acyclicity of
countable products of the sheaves `ν^* Iₙ` (`Ext.subsingleton_pi`,
`ProEt.epi_piMap`), which in turn follows from the levelwise comparison with étale
cohomology (`ProEt.mapExt_bijective_sheafPullback`). The functor `lim ν^* (-)` sends the
short exact sequence `0 → F → I → Q → 0` to a short exact sequence
(`ProEt.shortExact_limMap`, using repleteness of the pro-étale topos via weakly
contractible objects). In degree `0` the comparison map is induced by the adjunction
`const ⊣ lim` and full faithfulness of `ν^*`; in degree `1` it is constructed from the
five-term exact sequences (`Ext.oneEquivOfHomEquiv`), and in higher degrees by the
connecting isomorphisms (`Ext.connectingEquiv`) and induction applied to `Q`.
-/

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

namespace ProEt

/-! ### Instances for the category of inverse systems -/

instance : HasProductsOfShape ℕ (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  Sheaf.instHasLimitsOfShape

instance : EnoughInjectives (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

instance : EnoughInjectives (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  inferInstance

instance : HasExt.{u + 1} (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  hasExt_of_enoughInjectives _

instance : EnoughInjectives (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  inferInstance

end ProEt

/-- The constant abelian sheaf `ℤ` on the small étale site (the unit for sheaf
cohomology, see `CategoryTheory.Sheaf.H`). -/
noncomputable abbrev etaleConstantUnit : Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  (constantSheaf S.smallEtaleTopology Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The constant abelian sheaf `ℤ` on the pro-étale site. -/
noncomputable abbrev proetaleConstantUnit : Sheaf (ProEt.topology S) Ab.{u + 1} :=
  (constantSheaf (ProEt.topology S) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **Continuous étale cohomology** (Jannsen; blueprint
`def:continuous-etale-cohomology`): for an inverse system `F` of abelian sheaves on the
small étale site of `S`, this is the `Ext`-group from the constant system on the constant
sheaf `ℤ` to `F` in the category of inverse systems. Since morphisms out of that object
compute `Γ(X, lim Fₙ)` (see `continuousHZeroAddEquiv`), these `Ext`-groups are the right
derived functors of `(Fₙ)ₙ ↦ Γ(X, lim Fₙ)`. -/
noncomputable abbrev continuousH (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (n : ℕ) : Type (u + 1) :=
  Ext ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F n

namespace ProEt

variable {S}

/-! ### Degree zero -/

/-- In degree zero, continuous cohomology is the sections of the limit sheaf:
`Hom(Δℤ, F) ≅ Hom(ℤ, lim F) = H⁰(X_ét, lim Fₙ)`. This justifies the definition of
`continuousH` against the blueprint definition. -/
noncomputable def continuousHZeroAddEquiv (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology
    Ab.{u + 1}) : continuousH S F 0 ≃+ Sheaf.H (limit F) 0 :=
  -- Compose `Ext.addEquiv₀ : continuousH S F 0 ≃+ (Δℤ ⟶ F)` with the additive hom-
  -- equivalence of the adjunction `Functor.const ℕᵒᵖ ⊣ lim` (`constLimAdj.homAddEquiv`)
  -- and `Ext.addEquiv₀.symm` (note that `limit F` and `lim.obj F` are definitionally
  -- equal).
  Ext.addEquiv₀.trans ((constLimAdj.homAddEquiv (etaleConstantUnit S) F).trans
    Ext.addEquiv₀.symm)

/-! ### Acyclicity inputs -/

/-- The pullback of an injective abelian sheaf along `ν` has vanishing positive
cohomology, by the levelwise comparison `ProEt.mapExt_bijective_sheafPullback`. -/
lemma subsingleton_H_sheafPullback_injective
    (K : Sheaf S.smallEtaleTopology Ab.{u + 1}) [Injective K] :
    ∀ q, 0 < q → Subsingleton (Sheaf.H ((ProEt.sheafPullback S Ab.{u + 1}).obj K) q) := by
  -- `Sheaf.H (ν^* K) q = Ext (proetaleConstantUnit S) (ν^* K) q`. The bijection
  -- `mapExt_bijective_sheafPullback` identifies `Ext (etaleConstantUnit S) K q` (which
  -- is a subsingleton since `K` is injective and `q > 0`) with
  -- `Ext (ν^* (etaleConstantUnit S)) (ν^* K) q`; transport along the isomorphism
  -- `ν^* (etaleConstantUnit S) ≅ proetaleConstantUnit S`
  -- (`ProEt.sheafPullbackConstantIso`) using `Ext.subsingleton_of_iso`.
  intro q hq
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  have h2 : Subsingleton (Ext ((ProEt.sheafPullback S Ab.{u + 1}).obj (etaleConstantUnit S))
      ((ProEt.sheafPullback S Ab.{u + 1}).obj K) (m + 1)) :=
    haveI h1 : Subsingleton (Ext (etaleConstantUnit S) K (m + 1)) :=
      Ext.subsingleton_of_injective _ _ m
    (AddEquiv.ofBijective ((ProEt.sheafPullback S Ab.{u + 1}).mapExtAddHom
      (etaleConstantUnit S) K (m + 1))
      (mapExt_bijective_sheafPullback (etaleConstantUnit S) K (m + 1))).symm.toEquiv.subsingleton
  exact Abelian.Ext.subsingleton_of_iso
    (sheafPullbackConstantIso S (AddCommGrpCat.of (ULift.{u + 1} ℤ))) (m + 1) h2

/-- The limit of an inverse system of acyclic abelian pro-étale sheaves with split
epimorphic transition maps is acyclic. -/
lemma subsingleton_H_limit_of_isSplitEpi
    (G : ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1})
    (hsplit : ∀ n, IsSplitEpi (SequentialSystem.transition G n))
    (hacyc : ∀ (k : ℕᵒᵖ) (q : ℕ), 0 < q → Subsingleton (Sheaf.H (G.obj k) q)) :
    ∀ q, 0 < q → Subsingleton (Sheaf.H (limit G) q) := by
  -- Apply `Ext.subsingleton_x₁_of_shortExact` to the Milnor sequence
  -- `ProEt.shortExact_telescope G (split epi ⇒ epi)` with `Z := proetaleConstantUnit S`:
  -- * vanishing for the middle and right objects `∏ᶜ (G.obj (op n))`: by
  --   `Ext.subsingleton_pi` with `hepi := fun A B φ h ↦ ProEt.epi_piMap A B φ` and the
  --   levelwise acyclicity `hacyc`;
  -- * surjectivity against the telescope: under `Pi.lift`/`Pi.π`, the telescope becomes
  --   the concrete telescope of the maps `Hom(Z, transition G n)`; those are surjective
  --   since the transitions are split epimorphisms; conclude with
  --   `AddCommGroup.surjective_sub_shift`.
  have hepi : ∀ n, Epi (SequentialSystem.transition G n) := fun n ↦
    haveI := hsplit n
    inferInstance
  have hML := shortExact_telescope G hepi
  have hprod : ∀ q, 0 < q → Subsingleton (Ext (proetaleConstantUnit S)
      (∏ᶜ fun n : ℕ ↦ G.obj (op n)) q) :=
    Ext.subsingleton_pi
      (fun A B φ h ↦ haveI := h; epi_piMap A B φ)
      (proetaleConstantUnit S) (fun n : ℕ ↦ G.obj (op n))
      (fun n q hq ↦ hacyc (op n) q hq)
  have hsurj : ∀ s : proetaleConstantUnit S ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n),
      ∃ t : proetaleConstantUnit S ⟶ ∏ᶜ fun n : ℕ ↦ G.obj (op n),
        t ≫ telescope G = s := by
    intro s
    obtain ⟨x, hx⟩ := AddCommGroup.surjective_sub_shift
      (G := fun n : ℕ ↦ (proetaleConstantUnit S ⟶ G.obj (op n)))
      (fun n ↦ Preadditive.rightComp (proetaleConstantUnit S)
        (SequentialSystem.transition G n))
      (fun n u ↦ by
        haveI := hsplit n
        refine ⟨u ≫ section_ (SequentialSystem.transition G n), ?_⟩
        have h : (u ≫ section_ (SequentialSystem.transition G n)) ≫
            SequentialSystem.transition G n = u := by
          rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
        exact h)
      (fun n ↦ s ≫ Pi.π (fun m : ℕ ↦ G.obj (op m)) n)
    refine ⟨Pi.lift x, Pi.hom_ext _ _ fun n ↦ ?_⟩
    have hn : x n - x (n + 1) ≫ SequentialSystem.transition G n =
        s ≫ Pi.π (fun m : ℕ ↦ G.obj (op m)) n := congrFun hx n
    rw [← hn]
    simp only [telescope, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc,
      Category.comp_id, Limits.Pi.lift_π, Limits.Pi.lift_π_assoc]
  exact Ext.subsingleton_x₁_of_shortExact hML (proetaleConstantUnit S) hsurj hprod hprod

/-! ### The degree-zero comparison equivalence -/

universe v₁ u₁

/-- Precomposition with an isomorphism, as an additive equivalence on hom-groups. -/
private def precompAddEquivOfIso {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {X X' W : C} (e : X ≅ X') : (X ⟶ W) ≃+ (X' ⟶ W) where
  toFun f := e.inv ≫ f
  invFun g := e.hom ≫ g
  left_inv f := Iso.hom_inv_id_assoc e f
  right_inv g := Iso.inv_hom_id_assoc e g
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

private lemma precompAddEquivOfIso_comp {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {X X' W W' : C} (e : X ≅ X') (f : X ⟶ W) (w : W ⟶ W') :
    precompAddEquivOfIso e (f ≫ w) = precompAddEquivOfIso e f ≫ w :=
  (Category.assoc _ _ _).symm

/-- Whiskering with the fully faithful pullback `ν^*`, as an additive equivalence on
hom-groups of inverse systems. -/
private noncomputable def whiskerAddEquiv
    (F G : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    (F ⟶ G) ≃+ (F ⋙ ProEt.sheafPullback S Ab.{u + 1} ⟶
      G ⋙ ProEt.sheafPullback S Ab.{u + 1}) :=
  AddEquiv.mk'
    ((((ProEt.sheafAdjunction S Ab.{u + 1}).fullyFaithfulLOfIsIsoUnit).whiskeringRight
      ℕᵒᵖ).homEquiv)
    fun _ _ ↦ ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
      (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1})).map_add

/-- The whiskering by `ν^*` of the constant system on `ℤ_ét` is the constant system on
`ℤ_proét`. -/
private noncomputable def constUnitIso :
    (Functor.const ℕᵒᵖ).obj (etaleConstantUnit S) ⋙ ProEt.sheafPullback S Ab.{u + 1} ≅
      (Functor.const ℕᵒᵖ).obj (proetaleConstantUnit S) :=
  Functor.constComp ℕᵒᵖ (etaleConstantUnit S) (ProEt.sheafPullback S Ab.{u + 1}) ≪≫
    (Functor.const ℕᵒᵖ).mapIso
      (sheafPullbackConstantIso S (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The natural identification `Hom(Δℤ_ét, F) ≃+ Hom(ℤ_proét, lim ν^* Fₙ)`:
combine full faithfulness of `ν^*` (from `isIso_unit_sheafAdjunction` via
`Adjunction.fullyFaithfulLOfIsIsoUnit`), the isomorphism
`ν^* ℤ_ét ≅ ℤ_proét` (`ProEt.sheafPullbackConstantIso`) and the adjunction
`const ⊣ lim`. -/
noncomputable def homEquivZero (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S) ⟶ F) ≃+
      (proetaleConstantUnit S ⟶ limit (F ⋙ ProEt.sheafPullback S Ab.{u + 1})) :=
  (whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F).trans
    ((precompAddEquivOfIso (constUnitIso (S := S))).trans
      (constLimAdj.homAddEquiv (proetaleConstantUnit S)
        (F ⋙ ProEt.sheafPullback S Ab.{u + 1})))

/-- Naturality of `homEquivZero`. -/
lemma homEquivZero_naturality {F G : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}}
    (τ : F ⟶ G) (φ : (Functor.const ℕᵒᵖ).obj (etaleConstantUnit S) ⟶ F) :
    homEquivZero G (φ ≫ τ) = homEquivZero F φ ≫
      limMap (Functor.whiskerRight τ (ProEt.sheafPullback S Ab.{u + 1})) := by
  -- Each of the three constituents of `homEquivZero` is natural in `F`:
  -- whiskering is functorial, precomposition commutes with postcomposition, and the
  -- adjunction hom-equivalence is natural (`Adjunction.homEquiv_naturality_right`).
  have h1 : whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) G (φ ≫ τ) =
      whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F φ ≫
        Functor.whiskerRight τ (ProEt.sheafPullback S Ab.{u + 1}) :=
    ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
      (Sheaf (ProEt.topology S) Ab.{u + 1})).obj
        (ProEt.sheafPullback S Ab.{u + 1})).map_comp φ τ
  calc homEquivZero G (φ ≫ τ)
      = constLimAdj.homAddEquiv (proetaleConstantUnit S)
          (G ⋙ ProEt.sheafPullback S Ab.{u + 1})
          (precompAddEquivOfIso (constUnitIso (S := S))
            (whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) G
              (φ ≫ τ))) := rfl
    _ = constLimAdj.homAddEquiv (proetaleConstantUnit S)
          (G ⋙ ProEt.sheafPullback S Ab.{u + 1})
          (precompAddEquivOfIso (constUnitIso (S := S))
            (whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F φ) ≫
              Functor.whiskerRight τ (ProEt.sheafPullback S Ab.{u + 1})) := by
        rw [h1, precompAddEquivOfIso_comp]
    _ = constLimAdj.homAddEquiv (proetaleConstantUnit S)
          (F ⋙ ProEt.sheafPullback S Ab.{u + 1})
          (precompAddEquivOfIso (constUnitIso (S := S))
            (whiskerAddEquiv ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) F φ)) ≫
          lim.map (Functor.whiskerRight τ (ProEt.sheafPullback S Ab.{u + 1})) :=
        constLimAdj.homEquiv_naturality_right _ _
    _ = homEquivZero F φ ≫
          limMap (Functor.whiskerRight τ (ProEt.sheafPullback S Ab.{u + 1})) := rfl

/-! ### Main theorem -/

/-- **Comparison of continuous étale and pro-étale cohomology** (BS, Proposition 5.6.2;
blueprint `thm:comparison-continuous`): for an inverse system `(Fₙ)ₙ` of abelian sheaves
on the small étale site of `S` with epimorphic transition maps, continuous étale
cohomology agrees with the pro-étale cohomology of `lim ν^* Fₙ`:
`H^i_cont(X, (Fₙ)) ≅ H^i(X_proét, lim ν^* Fₙ)`. -/
theorem nonempty_continuousH_addEquiv_H_limit
    (F : ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1})
    (hF : ∀ n, Epi (SequentialSystem.transition F n)) (i : ℕ) :
    Nonempty (continuousH S F i ≃+
      Sheaf.H (limit (F ⋙ ProEt.sheafPullback S Ab.{u + 1})) i) := by
  -- Strong induction on `i` (over all `F` with epimorphic transitions simultaneously,
  -- as in `Sheaf.ext_free_eq_zero_of_cech` in
  -- `Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/Cartan.lean`). The proof
  -- below follows the sketch in the remaining comments.
  --
  -- **Degree 0.** `Ext.addEquiv₀.trans ((homEquivZero F).trans Ext.addEquiv₀.symm)`.
  --
  -- **Setup for positive degrees.** Let `I := Injective.under F`,
  -- `SC := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
  -- (cokernel.condition _)` with `hSC : SC.ShortExact` (mono by `Injective.ι` instance,
  -- exact by `ShortComplex.exact_cokernel`). Write `Q := SC.X₃`.
  -- * `I` has split epimorphic transitions
  --   (`SequentialSystem.isSplitEpi_transition_of_injective`), so in particular `Q` has
  --   epimorphic transitions: `cokernel.π _` is an epimorphism in the functor category,
  --   hence levelwise (`NatTrans.epi_iff_app_epi`-style, see
  --   `Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono`), and
  --   `SequentialSystem.epi_transition_of_epi_app` applies.
  -- * `T := SC.map ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (ProEt.sheafPullback S Ab.{u+1}))`
  --   is levelwise short exact: for `k : ℕᵒᵖ`,
  --   `T.map ((evaluation _ _).obj k) = SC.map ((evaluation _ _).obj k ⋙ ν^*)` up to
  --   `rfl`/`ShortComplex.map_comp`-style identifications, and short exactness is
  --   preserved by the exact functor `(evaluation _ _).obj k ⋙ ν^*`
  --   (`ShortComplex.ShortExact.map_of_exact`; both factors are additive and preserve
  --   finite limits and colimits — for `ν^*` these instances are in
  --   `Proetale/Topology/Comparison/CohomologyComparison.lean`).
  -- * `hTL : (T.map lim).ShortExact` by `ProEt.shortExact_limMap` (the system
  --   `T.X₁ = F ⋙ ν^*` has epimorphic transitions by
  --   `SequentialSystem.epi_transition_whisker`, since `ν^*` preserves epimorphisms,
  --   having a right adjoint).
  -- * The objects of `T.map lim` are `lim.obj (F ⋙ ν^*) = limit (F ⋙ ν^*)` etc.
  -- * Acyclicity of the middle objects:
  --   - `∀ q, 0 < q → Subsingleton (continuousH S I q)`: `Ext.eq_zero_of_injective`.
  --   - `∀ q, 0 < q → Subsingleton (Sheaf.H (limit (I ⋙ ν^*)) q)`: by
  --     `subsingleton_H_limit_of_isSplitEpi`; the transitions of `I ⋙ ν^*` are split
  --     epimorphisms (functors preserve split epimorphisms, `IsSplitEpi.map`), and the
  --     levels `ν^* (I.obj k)` are acyclic by
  --     `subsingleton_H_sheafPullback_injective` since `I.obj k` is injective
  --     (`SequentialSystem.injective_obj_of_injective`).
  --
  -- **Degree 1.** Apply `Ext.oneEquivOfHomEquiv hSC _ hTL _` with
  -- `e₂ := homEquivZero I`, `e₃ := homEquivZero Q`, `hcomm` from
  -- `homEquivZero_naturality` applied to `τ := SC.g` (identify `(T.map lim).g` with
  -- `limMap (Functor.whiskerRight SC.g ν^*)` — this is `rfl` or a `ShortComplex.map`
  -- unfolding), and the degree-1 acyclicity of the middle objects.
  --
  -- **Degree `j + 2`.** `Q` is again a system with epimorphic transition maps, so the
  -- induction hypothesis at degree `j + 1` provides
  -- `e : continuousH S Q (j+1) ≃+ Sheaf.H (limit (Q ⋙ ν^*)) (j+1)`. Conclude with
  -- `((Ext.connectingEquiv hSC _ j _ _).symm.trans e).trans
  --   (Ext.connectingEquiv hTL _ j _ _)`
  -- where the two `connectingEquiv`s are the connecting isomorphisms of the covariant
  -- long exact sequences for `SC` and `T.map lim` (vanishing hypotheses from the
  -- acyclicity of the middle objects above).
  induction i using Nat.strong_induction_on generalizing F with
  | _ i IH =>
    obtain _ | i := i
    · -- Degree 0.
      exact ⟨Ext.addEquiv₀.trans ((homEquivZero F).trans Ext.addEquiv₀.symm)⟩
    · -- Setup for positive degrees.
      let SC : ShortComplex (ℕᵒᵖ ⥤ Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
      have hSC : SC.ShortExact := { exact := ShortComplex.exact_cokernel _ }
      haveI hinj : Injective SC.X₂ := inferInstanceAs (Injective (Injective.under F))
      let T : ShortComplex (ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) Ab.{u + 1}) :=
        SC.map ((Functor.whiskeringRight ℕᵒᵖ (Sheaf S.smallEtaleTopology Ab.{u + 1})
          (Sheaf (ProEt.topology S) Ab.{u + 1})).obj (ProEt.sheafPullback S Ab.{u + 1}))
      have hT : ∀ k : ℕᵒᵖ, (T.map ((CategoryTheory.evaluation ℕᵒᵖ
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
      have hTL : (T.map lim).ShortExact := shortExact_limMap hT hX₁
      -- Acyclicity of the middle objects.
      have h₂cont : ∀ q : ℕ, Subsingleton
          (Ext ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) SC.X₂ (q + 1)) :=
        fun q ↦ Ext.subsingleton_of_injective _ _ q
      have h₂proet : ∀ q, 0 < q → Subsingleton (Sheaf.H
          (limit (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})) q) := by
        refine subsingleton_H_limit_of_isSplitEpi
          (Injective.under F ⋙ ProEt.sheafPullback S Ab.{u + 1})
          (fun n ↦ ?_) (fun k q hq ↦ ?_)
        · haveI := SequentialSystem.isSplitEpi_transition_of_injective (Injective.under F) n
          exact inferInstanceAs (IsSplitEpi ((ProEt.sheafPullback S Ab.{u + 1}).map
            (SequentialSystem.transition (Injective.under F) n)))
        · haveI : Injective ((Injective.under F).obj k) :=
            SequentialSystem.injective_obj_of_injective (Injective.under F) k.unop
          exact subsingleton_H_sheafPullback_injective ((Injective.under F).obj k) q hq
      obtain _ | i := i
      · -- Degree 1.
        exact ⟨Ext.oneEquivOfHomEquiv hSC ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S))
          hTL (proetaleConstantUnit S) (homEquivZero SC.X₂) (homEquivZero SC.X₃)
          (fun t ↦ homEquivZero_naturality SC.g t) (h₂cont 0) (h₂proet 1 one_pos)⟩
      · -- Degree `i + 2`.
        have hQepi : ∀ n, Epi (SequentialSystem.transition SC.X₃ n) := by
          have hIepi : ∀ n, Epi (SequentialSystem.transition SC.X₂ n) := fun n ↦
            haveI := SequentialSystem.isSplitEpi_transition_of_injective
              (Injective.under F) n
            inferInstanceAs (Epi (SequentialSystem.transition (Injective.under F) n))
          haveI : Epi SC.g := inferInstanceAs (Epi (cokernel.π (Injective.ι F)))
          exact SequentialSystem.epi_transition_of_epi_app SC.g
            (fun k ↦ inferInstance) hIepi
        obtain ⟨e⟩ := IH (i + 1) (by omega) SC.X₃ hQepi
        exact ⟨((Ext.connectingEquiv hSC ((Functor.const ℕᵒᵖ).obj (etaleConstantUnit S)) i
            (h₂cont i) (h₂cont (i + 1))).symm.trans e).trans
          (Ext.connectingEquiv hTL (proetaleConstantUnit S) i
            (h₂proet (i + 1) i.succ_pos) (h₂proet (i + 2) (by omega)))⟩

end ProEt

end AlgebraicGeometry.Scheme
