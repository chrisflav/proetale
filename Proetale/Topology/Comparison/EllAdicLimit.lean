/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Comparison.ProetConstantSheaf
import Proetale.Topology.Comparison.RepleteExact

/-!
# The `ℓ`-adic sheaf as a limit of `ℤ/ℓⁿ`-sheaves

We identify the (`ULift`ed) `ℓ`-adic sheaf `X.ellAdicSheaf ℓ` on the pro-étale site of a
scheme `X` with the inverse limit of the pullbacks of the constant étale sheaves
`ℤ/ℓⁿℤ`:

- `AlgebraicGeometry.Scheme.ProEt.zmodSystem`: the inverse system
  `n ↦ (constant étale sheaf at ℤ/ℓⁿℤ)` with the reduction maps as transitions; its
  transition maps are epimorphisms.
- `AlgebraicGeometry.Scheme.ProEt.ellAdicSheafLimitIso`:
  `ULift (ellAdicSheaf) ≅ lim_n ν^*(ℤ/ℓⁿℤ)`.

Sectionwise this is the topological statement that `ℤ_[ℓ]` is the inverse limit of the
finite discrete groups `ℤ/ℓⁿℤ`: a continuous map `U → ℤ_[ℓ]` is the same as a compatible
family of continuous maps `U → ℤ/ℓⁿℤ` (`PadicInt.lift` and the fact that the topology of
`ℤ_[ℓ]` is detected by the quotients `toZModPow`).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace ProEt

section Padic

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The projections `ℤ_[ℓ] → ℤ/ℓⁿℤ` are continuous (they are "locally constant": their
fibers are unions of balls of radius `ℓ⁻ⁿ`). -/
lemma continuous_toZModPow (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  -- The fibers are open: if `toZModPow n x = a` and `‖y - x‖ ≤ ℓ⁻ⁿ`, then
  -- `y - x ∈ Ideal.span {(ℓ : ℤ_[ℓ])^n} = RingHom.ker (toZModPow n)`
  -- (`PadicInt.norm_le_pow_iff_mem_span_pow`, `PadicInt.ker_toZModPow`), so
  -- `toZModPow n y = a`. Hence the map is locally constant
  -- (`IsLocallyConstant.continuous`, or directly `continuous_discrete_rng`-style:
  -- preimages of singletons are open).
  have hℓ : (0 : ℝ) < (ℓ : ℝ) := by
    exact_mod_cast (Fact.out (p := ℓ.Prime)).pos
  refine continuous_def.mpr fun s _ => Metric.isOpen_iff.mpr fun x hx => ?_
  refine ⟨(ℓ : ℝ) ^ (-(n : ℤ) + 1), zpow_pos hℓ _, fun y hy => ?_⟩
  have h1 : ‖y - x‖ < (ℓ : ℝ) ^ (-(n : ℤ) + 1) := by
    rw [← dist_eq_norm]
    exact hy
  have h2 : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (y - x) (-(n : ℤ))).mpr h1
  have h3 : PadicInt.toZModPow (p := ℓ) n (y - x) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (y - x) n).mp h2
  have h4 : PadicInt.toZModPow (p := ℓ) n y = PadicInt.toZModPow (p := ℓ) n x := by
    rw [map_sub, sub_eq_zero] at h3
    exact h3
  change PadicInt.toZModPow (p := ℓ) n y ∈ s
  rw [h4]
  exact hx

/-- A map into `ℤ_[ℓ]` is continuous as soon as its compositions with all the
projections `toZModPow n` are continuous: the topology of `ℤ_[ℓ]` is the inverse limit
topology. -/
lemma continuous_of_forall_continuous_toZModPow {U : Type*} [TopologicalSpace U]
    (f : U → ℤ_[ℓ]) (hf : ∀ n, Continuous fun x => PadicInt.toZModPow n (f x)) :
    Continuous f := by
  -- Use the metric characterization: for `x₀` and `ε > 0` pick `n` with
  -- `(ℓ : ℝ)⁻¹ ^ n < ε`; on the open set
  -- `{x | toZModPow n (f x) = toZModPow n (f x₀)}` (open by `hf n`, discrete target)
  -- one has `f x - f x₀ ∈ ker (toZModPow n) = span {ℓ^n}`, hence
  -- `‖f x - f x₀‖ ≤ ℓ⁻ⁿ < ε` (`PadicInt.norm_le_pow_iff_mem_span_pow`,
  -- `PadicInt.ker_toZModPow`). Conclude with `Metric.continuous_iff`
  -- (mind `zpow` vs `pow` normalization for the radius).
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt ℓ hε
  have hopen : IsOpen {x : U | PadicInt.toZModPow n (f x) = PadicInt.toZModPow n (f x₀)} :=
    (isOpen_discrete {PadicInt.toZModPow n (f x₀)}).preimage (hf n)
  have hmem : {x : U | PadicInt.toZModPow n (f x) = PadicInt.toZModPow n (f x₀)} ∈
      nhds x₀ := hopen.mem_nhds rfl
  refine Filter.eventually_of_mem hmem fun x hx => ?_
  have h1 : PadicInt.toZModPow (p := ℓ) n (f x - f x₀) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hx
  have h2 : ‖f x - f x₀‖ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow (p := ℓ) n,
      RingHom.mem_ker]
    exact h1
  calc dist (f x) (f x₀) = ‖f x - f x₀‖ := dist_eq_norm _ _
    _ ≤ (ℓ : ℝ) ^ (-(n : ℤ)) := h2
    _ < ε := hn

/-- A compatible family of continuous maps `U → ℤ/ℓⁿℤ` arises from a unique continuous
map `U → ℤ_[ℓ]`. -/
theorem existsUnique_continuousMap_padicInt {U : Type*} [TopologicalSpace U]
    (g : ∀ n, C(U, ZMod (ℓ ^ n)))
    (hg : ∀ n, (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))) ∘
      (g (n + 1)) = g n) :
    ∃! f : C(U, ℤ_[ℓ]), ∀ n x, PadicInt.toZModPow n (f x) = g n x := by
  -- Existence: upgrade `hg` from successive indices to all pairs `m ≤ n` (induction);
  -- form the subring `R ≤ ∀ n, ZMod (ℓ ^ n)` of compatible families
  -- (`Subring` with carrier `{s | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow ℓ h) _
  -- (s n) = s m}`; closure under the ring operations is componentwise), with the
  -- projections `R →+* ZMod (ℓ ^ n)`; `PadicInt.lift` (with
  -- `PadicInt.lift_spec`) produces `R →+* ℤ_[ℓ]`. The map
  -- `f := fun x => lift ⟨fun n => g n x, _⟩` satisfies `toZModPow n ∘ f = g n`
  -- (`lift_spec` applied pointwise), and is continuous by
  -- `continuous_of_forall_continuous_toZModPow` since
  -- `toZModPow n ∘ f = g n` is continuous.
  -- Uniqueness: two such `f f'` agree pointwise since `toZModPow n (f x) = toZModPow n
  -- (f' x)` for all `n` implies `f x = f' x` (`PadicInt.ext_of_toZModPow` or
  -- `PadicInt.eq_of_forall_toZModPow_eq` — grep for the exact name; it follows from
  -- `PadicInt.dense_range_intCast`-style arguments or directly from
  -- `norm_le_pow_iff_mem_span_pow`: `‖f x - f' x‖ ≤ ℓ⁻ⁿ` for all `n` forces equality).
  -- Upgrade the compatibility from successive indices to all pairs `m ≤ n`.
  have hg' : ∀ (x : U) (m n : ℕ) (h : m ≤ n),
      ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (g n x) = g m x := by
    intro x m n h
    induction n, h using Nat.le_induction with
    | base =>
      rw [ZMod.castHom_apply, ZMod.cast_id]
    | succ n hmn ih =>
      have h1 : ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x) =
          g n x := congrFun (hg n) x
      have h2 : ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x)) =
          ZMod.castHom (pow_dvd_pow ℓ (hmn.trans (Nat.le_succ n))) (ZMod (ℓ ^ m))
            (g (n + 1) x) :=
        RingHom.congr_fun
          (ZMod.castHom_comp (pow_dvd_pow ℓ hmn) (pow_dvd_pow ℓ (Nat.le_succ n)))
          (g (n + 1) x)
      calc ZMod.castHom (pow_dvd_pow ℓ (hmn.trans (Nat.le_succ n))) (ZMod (ℓ ^ m))
            (g (n + 1) x)
          = ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n)) (g (n + 1) x)) :=
            h2.symm
        _ = ZMod.castHom (pow_dvd_pow ℓ hmn) (ZMod (ℓ ^ m)) (g n x) := by rw [h1]
        _ = g m x := ih
  -- The subring of compatible families in the product of the `ℤ/ℓⁿℤ`.
  let R : Subring (∀ n, ZMod (ℓ ^ n)) :=
    { carrier := {s | ∀ (m n : ℕ) (h : m ≤ n),
        ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (s n) = s m}
      one_mem' := fun m n h => by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) 1 = 1
        rw [map_one]
      mul_mem' := fun {a b} ha hb m n h => by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n * b n) = a m * b m
        rw [map_mul, ha m n h, hb m n h]
      zero_mem' := fun m n h => by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) 0 = 0
        rw [map_zero]
      add_mem' := fun {a b} ha hb m n h => by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (a n + b n) = a m + b m
        rw [map_add, ha m n h, hb m n h]
      neg_mem' := fun {a} ha m n h => by
        change ZMod.castHom (pow_dvd_pow ℓ h) (ZMod (ℓ ^ m)) (-(a n)) = -(a m)
        rw [map_neg, ha m n h] }
  -- The compatible projections out of `R`, in the shape required by `PadicInt.lift`.
  have compat : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))).comp
        ((Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) k2).comp R.subtype) =
      (Pi.evalRingHom (fun k => ZMod (ℓ ^ k)) k1).comp R.subtype := by
    intro k1 k2 hk
    refine RingHom.ext fun s => ?_
    exact s.2 k1 k2 hk
  have hmem : ∀ x : U, (fun n => g n x) ∈ R := fun x m n h => hg' x m n h
  -- The candidate map, via the universal property of `ℤ_[ℓ]`.
  have hφ : ∀ (n : ℕ) (x : U),
      PadicInt.toZModPow n (PadicInt.lift compat ⟨fun k => g k x, hmem x⟩) = g n x :=
    fun n x => RingHom.congr_fun (PadicInt.lift_spec compat n) ⟨fun k => g k x, hmem x⟩
  have hcont : Continuous fun x => PadicInt.lift compat ⟨fun k => g k x, hmem x⟩ :=
    continuous_of_forall_continuous_toZModPow ℓ _ fun n =>
      (g n).continuous.congr fun x => (hφ n x).symm
  refine ⟨⟨fun x => PadicInt.lift compat ⟨fun k => g k x, hmem x⟩, hcont⟩, hφ, ?_⟩
  intro f' hf'
  ext x
  exact PadicInt.ext_of_toZModPow.mp fun n => (hf' n x).trans (hφ n x).symm

end Padic

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse system `n ↦ ULift ℤ/ℓⁿℤ` of abelian groups, with the reduction maps as
transition maps. -/
noncomputable def zmodAbSystem : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Functor.ofSequence
    (X := fun n => op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
    (fun n => (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)).leftOp

set_option linter.unusedSectionVars false in
lemma zmodAbSystem_obj (n : ℕ) :
    (zmodAbSystem ℓ).obj (op n) = AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))) :=
  rfl

set_option linter.unusedSectionVars false in
/-- The transition maps of `zmodAbSystem` are the (`ULift`ed) reduction maps. -/
lemma zmodAbSystem_transition (n : ℕ) :
    SequentialSystem.transition (zmodAbSystem ℓ) n =
      AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom) := by
  -- `Functor.ofSequence_map_homOfLE_succ` (or the corresponding simp lemma) plus
  -- `leftOp`/`op` unfolding; morphisms in `ℕ` are subsingletons.
  exact congrArg Quiver.Hom.unop
    (Functor.ofSequence_map_homOfLE_succ
      (X := fun n => op (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (f := fun n => (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)).op)
      n)

lemma epi_transition_zmodAbSystem (n : ℕ) :
    Epi (SequentialSystem.transition (zmodAbSystem ℓ) n) := by
  -- By `zmodAbSystem_transition` and `AddCommGrpCat.epi_iff_surjective`: the reduction
  -- `ZMod.castHom : ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ` is surjective (`ZMod.castHom_surjective` or via
  -- `ZMod.natCast_self_eq_zero`/`ZMod.natCast_rightInverse`-style arguments; grep for
  -- the right lemma — `ZMod.castHom_surjective` exists for `m ∣ n`), and `ULift`
  -- preserves surjectivity.
  rw [zmodAbSystem_transition ℓ n, AddCommGrpCat.epi_iff_surjective]
  intro y
  obtain ⟨y⟩ := y
  obtain ⟨z, hz⟩ := ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ n)) y
  exact ⟨ULift.up z, congrArg ULift.up hz⟩

/-- The inverse system of constant étale sheaves `ℤ/ℓⁿℤ` on the small étale site. -/
noncomputable def zmodSystem : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology Ab.{u + 1} :=
  zmodAbSystem ℓ ⋙ constantSheaf X.smallEtaleTopology Ab.{u + 1}

lemma epi_transition_zmodSystem (n : ℕ) :
    Epi (SequentialSystem.transition (zmodSystem X ℓ) n) :=
  -- The constant sheaf functor is a left adjoint (`constantSheafAdj`), hence preserves
  -- epimorphisms.
  haveI : (constantSheaf X.smallEtaleTopology Ab.{u + 1}).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (constantSheafAdj X.smallEtaleTopology Ab.{u + 1} (isTerminalMkId X))
  SequentialSystem.epi_transition_whisker (constantSheaf X.smallEtaleTopology Ab.{u + 1})
    (epi_transition_zmodAbSystem ℓ) n

section LimitCone

/-- Functoriality of `topologicalSheafLiftedMap` in the coefficient map. -/
private lemma topologicalSheafLiftedMap_comp
    (M₁ M₂ M₃ : Type) [TopologicalSpace M₁] [AddCommGroup M₁] [IsTopologicalAddGroup M₁]
    [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    [TopologicalSpace M₃] [AddCommGroup M₃] [IsTopologicalAddGroup M₃]
    (f : M₁ →+ M₂) (hf : Continuous f) (g : M₂ →+ M₃) (hg : Continuous g) :
    topologicalSheafLiftedMap X M₁ f hf ≫ topologicalSheafLiftedMap X M₂ g hg =
      topologicalSheafLiftedMap X M₁ (g.comp f) (hg.comp hf) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- `topologicalSheafLiftedMap` only depends on the coefficient map. -/
private lemma topologicalSheafLiftedMap_congr (M₁ M₂ : Type)
    [TopologicalSpace M₁] [AddCommGroup M₁] [IsTopologicalAddGroup M₁]
    [TopologicalSpace M₂] [AddCommGroup M₂] [IsTopologicalAddGroup M₂]
    {f f' : M₁ →+ M₂} {hf : Continuous f} {hf' : Continuous f'} (h : f = f') :
    topologicalSheafLiftedMap X M₁ f hf = topologicalSheafLiftedMap X M₁ f' hf' := by
  subst h
  rfl

/-- The comparison isomorphism between the value of the pulled-back system at `n` and
the sheaf of continuous `ℤ/ℓⁿℤ`-valued maps. -/
private noncomputable def ellAdicIso (n : ℕ) :
    (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n) ≅
      topologicalSheafLifted X (ZMod (ℓ ^ n)) :=
  sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ n))

set_option linter.unusedSectionVars false in
/-- The comparison isomorphisms intertwine the transition maps of the pulled-back system
with postcomposition by the reduction maps. -/
private lemma ellAdicIso_inv_naturality (n : ℕ) :
    (ellAdicIso X ℓ (n + 1)).inv ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology ≫
        (ellAdicIso X ℓ n).inv := by
  -- Identify the transition map of the composed system.
  have h0 : SequentialSystem.transition
        (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) :=
    congrArg (fun f => (ProEt.sheafPullback X Ab.{u + 1}).map
      ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map f)) (zmodAbSystem_transition ℓ n)
  -- Naturality of the pullback-constant comparison in the coefficient group.
  have hnat1 : (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
        (sheafPullbackConstantIso X
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom =
      (sheafPullbackConstantIso X
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
        (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)) :=
    (sheafPullbackCompConstantIso X).hom.naturality
      (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
        (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))
  -- Naturality of the constant-to-continuous comparison in the coefficient group.
  have hnat2 : constantToTopologicalSheafLifted X (ZMod (ℓ ^ (n + 1))) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology =
      (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)) ≫
        constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
    constantToTopologicalSheafLifted_naturality X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
  -- The combined naturality square for the `hom` direction.
  have hsq : (ProEt.sheafPullback X Ab.{u + 1}).map
        ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
          (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
        (ellAdicIso X ℓ n).hom =
      (ellAdicIso X ℓ (n + 1)).hom ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology := by
    calc (ProEt.sheafPullback X Ab.{u + 1}).map
          ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
            (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
          (ellAdicIso X ℓ n).hom
        = ((ProEt.sheafPullback X Ab.{u + 1}).map
            ((constantSheaf X.smallEtaleTopology Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
            (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          (Category.assoc _ _ _).symm
      _ = ((sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom))) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          congrArg (fun h => h ≫ constantToTopologicalSheafLifted X (ZMod (ℓ ^ n))) hnat1
      _ = (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            (constantSheaf (ProEt.topology X) Ab.{u + 1}).map
              (AddCommGrpCat.uliftFunctor.{u + 1}.map (AddCommGrpCat.ofHom
                (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n))
                  (ZMod (ℓ ^ n))).toAddMonoidHom)) ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ n)) :=
          Category.assoc _ _ _
      _ = (sheafPullbackConstantIso X
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫
            constantToTopologicalSheafLifted X (ZMod (ℓ ^ (n + 1))) ≫
            topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
              continuous_of_discreteTopology :=
          congrArg (fun h => (sheafPullbackConstantIso X
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))).hom ≫ h) hnat2.symm
      _ = (ellAdicIso X ℓ (n + 1)).hom ≫
            topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
              (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
              continuous_of_discreteTopology :=
          (Category.assoc _ _ _).symm
  rw [h0, Iso.inv_comp_eq, ← Category.assoc, ← hsq, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The legs of the limit cone with apex the lifted `ℓ`-adic sheaf. -/
private noncomputable def ellAdicLeg (n : ℕ) :
    topologicalSheafLifted X ℤ_[ℓ] ⟶
      (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n) :=
  topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
      (continuous_toZModPow ℓ n) ≫ (ellAdicIso X ℓ n).inv

/-- The legs are compatible with the transition maps. -/
private lemma ellAdicLeg_succ (n : ℕ) :
    ellAdicLeg X ℓ (n + 1) ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n =
      ellAdicLeg X ℓ n := by
  have hcomp : topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
        (continuous_toZModPow ℓ (n + 1)) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology =
      topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
        (continuous_toZModPow ℓ n) := by
    refine (topologicalSheafLiftedMap_comp X _ _ _ _ _ _ _).trans
      (topologicalSheafLiftedMap_congr X _ _ ?_)
    refine AddMonoidHom.ext fun z => ?_
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) z
  calc ellAdicLeg X ℓ (n + 1) ≫
        SequentialSystem.transition (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n
      = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        ((ellAdicIso X ℓ (n + 1)).inv ≫
          SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n) :=
        Category.assoc _ _ _
    _ = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        (topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology ≫ (ellAdicIso X ℓ n).inv) :=
        congrArg (fun h => topologicalSheafLiftedMap X ℤ_[ℓ]
          (PadicInt.toZModPow (n + 1)).toAddMonoidHom (continuous_toZModPow ℓ (n + 1)) ≫ h)
          (ellAdicIso_inv_naturality X ℓ n)
    _ = (topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow (n + 1)).toAddMonoidHom
          (continuous_toZModPow ℓ (n + 1)) ≫
        topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology) ≫ (ellAdicIso X ℓ n).inv :=
        (Category.assoc _ _ _).symm
    _ = topologicalSheafLiftedMap X ℤ_[ℓ] (PadicInt.toZModPow n).toAddMonoidHom
          (continuous_toZModPow ℓ n) ≫ (ellAdicIso X ℓ n).inv :=
        congrArg (fun h => h ≫ (ellAdicIso X ℓ n).inv) hcomp
    _ = ellAdicLeg X ℓ n := rfl

/-- The cone over the pulled-back system with apex the lifted `ℓ`-adic sheaf. -/
private noncomputable def ellAdicCone :
    Cone (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) where
  pt := topologicalSheafLifted X ℤ_[ℓ]
  π := SequentialSystem.natTransOfSucc (fun n => ellAdicLeg X ℓ n) (ellAdicLeg_succ X ℓ)

/-- The cone `ellAdicCone` is a limit cone: sectionwise this is the statement that a
continuous map to `ℤ_[ℓ]` is the same as a compatible family of continuous maps to the
`ℤ/ℓⁿℤ`. -/
private noncomputable def isLimitEllAdicCone : IsLimit (ellAdicCone X ℓ) := by
  apply isLimitOfReflects (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})
  refine evaluationJointlyReflectsLimits _ fun U => ?_
  apply isLimitOfReflects (CategoryTheory.forget Ab.{u + 1})
  refine ((Types.isLimit_iff _).mpr ?_).some
  intro s hs
  -- The comparison isomorphisms are bijective on sections over `U`.
  have cancel1 : ∀ (n : ℕ)
      (t : ToType (((zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj
        (op n)).obj.obj U)),
      ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) t) = t := by
    intro n t
    have h1 : (ellAdicIso X ℓ n).hom.hom.app U ≫ (ellAdicIso X ℓ n).inv.hom.app U =
        𝟙 (((zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}).obj (op n)).obj.obj U) :=
      congrArg (fun f => f.hom.app U) (ellAdicIso X ℓ n).hom_inv_id
    exact ((ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom h1 t)).trans (ConcreteCategory.id_apply t)
  have cancel2 : ∀ (n : ℕ) (t : ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ n))),
      ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U) t) = t := by
    intro n t
    have h1 : (ellAdicIso X ℓ n).inv.hom.app U ≫ (ellAdicIso X ℓ n).hom.hom.app U =
        𝟙 ((topologicalSheafLifted X (ZMod (ℓ ^ n))).obj.obj U) :=
      congrArg (fun f => f.hom.app U) (ellAdicIso X ℓ n).inv_hom_id
    have h2 := ConcreteCategory.congr_hom h1 t
    have h3 := (ConcreteCategory.comp_apply ((ellAdicIso X ℓ n).inv.hom.app U)
      ((ellAdicIso X ℓ n).hom.hom.app U) t).symm
    have h4 := ConcreteCategory.id_apply
      (X := (topologicalSheafLifted X (ZMod (ℓ ^ n))).obj.obj U) t
    exact (h3.trans h2).trans h4
  -- The transition square on sections over `U`.
  have hBsq : ∀ (n : ℕ) (a : ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ (n + 1)))),
      ConcreteCategory.hom
          ((SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
          (ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) a) =
        ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
          (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U) a) := by
    intro n a
    have h1 : (ellAdicIso X ℓ (n + 1)).inv.hom.app U ≫
          (SequentialSystem.transition
            (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U =
        (topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U ≫
          (ellAdicIso X ℓ n).inv.hom.app U :=
      congrArg (fun f => f.hom.app U) (ellAdicIso_inv_naturality X ℓ n)
    have h2 := ConcreteCategory.congr_hom h1 a
    have h3 := (ConcreteCategory.comp_apply ((ellAdicIso X ℓ (n + 1)).inv.hom.app U)
      ((SequentialSystem.transition
        (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U) a).symm
    have h4 := ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) ((ellAdicIso X ℓ n).inv.hom.app U) a
    exact (h3.trans h2).trans h4
  -- The compatible family of continuous maps obtained from the section `s`.
  let g' : ∀ n : ℕ, ULift.{u + 1} C((unop U).left, ZMod (ℓ ^ n)) := fun n =>
    ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) (s (op n))
  let g : ∀ n : ℕ, C((unop U).left, ZMod (ℓ ^ n)) := fun n => (g' n).down
  have htrans : ∀ n : ℕ,
      ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
        (s (op (n + 1))) = s (op n) := fun n => hs ((homOfLE (Nat.le_succ n)).op)
  have hgc : ∀ n : ℕ, ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) (g' (n + 1)) = g' n := by
    intro n
    have e1 : ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) (g' (n + 1)) =
        s (op (n + 1)) := cancel1 (n + 1) (s (op (n + 1)))
    have e2 : ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ (n + 1)).inv.hom.app U) (g' (n + 1))) =
        s (op n) :=
      (congrArg (fun z => ConcreteCategory.hom
        ((SequentialSystem.transition
          (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n).hom.app U) z) e1).trans
        (htrans n)
    have e3 : ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
          (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
          continuous_of_discreteTopology).hom.app U) (g' (n + 1))) = s (op n) :=
      (hBsq n (g' (n + 1))).symm.trans e2
    have e4 : ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U)
        (ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
          (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
            (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
            continuous_of_discreteTopology).hom.app U) (g' (n + 1)))) =
        ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) (s (op n)) :=
      congrArg (fun z => ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) z) e3
    have e6 := cancel2 n (ConcreteCategory.hom ((topologicalSheafLiftedMap X (ZMod (ℓ ^ (n + 1)))
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom
      continuous_of_discreteTopology).hom.app U) (g' (n + 1)))
    exact e6.symm.trans e4
  have hgfun : ∀ n : ℕ, (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))) ∘
      (g (n + 1)) = g n := by
    intro n
    have e5 : ULift.up.{u + 1} ((ContinuousMap.mk
        ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).toAddMonoidHom)
        continuous_of_discreteTopology).comp (g (n + 1))) = g' n := hgc n
    funext x
    exact ContinuousMap.congr_fun (congrArg ULift.down e5) x
  obtain ⟨f, hf, huniq⟩ := existsUnique_continuousMap_padicInt ℓ g hgfun
  refine ⟨ULift.up f, fun k => ?_, fun y hy => ?_⟩
  · -- The element `ULift.up f` maps to the given section.
    obtain ⟨n⟩ := k
    have p2 : ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
        (ULift.up f) = g' n := by
      have p2a : (ContinuousMap.mk ((PadicInt.toZModPow (p := ℓ) n)).toAddMonoidHom
          (continuous_toZModPow ℓ n)).comp f = g n := ContinuousMap.ext fun x => hf n x
      exact congrArg ULift.up.{u + 1} p2a
    have p1 := ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X ℤ_[ℓ]
      (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
      ((ellAdicIso X ℓ n).inv.hom.app U) (ULift.up f)
    have p3 := congrArg
      (fun z => ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U) z) p2
    have p4 := cancel1 n (s (op n))
    exact p1.trans (p3.trans p4)
  · -- Uniqueness.
    let y' : ULift.{u + 1} C((unop U).left, ℤ_[ℓ]) := y
    have q1 : ∀ n : ℕ, ConcreteCategory.hom ((ellAdicIso X ℓ n).inv.hom.app U)
        (ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
          (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y') =
        s (op n) := by
      intro n
      have qa := (ConcreteCategory.comp_apply ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U)
        ((ellAdicIso X ℓ n).inv.hom.app U) y').symm
      exact qa.trans (hy (op n))
    have q2 : ∀ n : ℕ, ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y' =
        g' n := by
      intro n
      have qb := congrArg
        (fun z => ConcreteCategory.hom ((ellAdicIso X ℓ n).hom.hom.app U) z) (q1 n)
      have qc := cancel2 n (ConcreteCategory.hom ((topologicalSheafLiftedMap X ℤ_[ℓ]
        (PadicInt.toZModPow n).toAddMonoidHom (continuous_toZModPow ℓ n)).hom.app U) y')
      exact qc.symm.trans qb
    have q3 : ∀ (n : ℕ) (x : (unop U).left), PadicInt.toZModPow n (y'.down x) = g n x := by
      intro n x
      have q3a : (ContinuousMap.mk ((PadicInt.toZModPow (p := ℓ) n)).toAddMonoidHom
          (continuous_toZModPow ℓ n)).comp y'.down = g n := congrArg ULift.down (q2 n)
      exact ContinuousMap.congr_fun q3a x
    exact ULift.ext y' (ULift.up f) (huniq y'.down q3)

end LimitCone

/-- **The `ℓ`-adic sheaf is the limit of the `ℤ/ℓⁿℤ`-sheaves**: the `ULift`ed
`X.ellAdicSheaf ℓ` is the inverse limit over `n` of the pullbacks to the pro-étale site
of the constant étale sheaves `ℤ/ℓⁿℤ`. -/
noncomputable def ellAdicSheafLimitIso :
    (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ) ≅
      limit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) := by
  -- Step 1: identify the diagram. Construct a natural isomorphism
  -- `zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u+1} ≅ D` where
  -- `D : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) Ab.{u+1}` has `D.obj (op n) =
  -- topologicalSheafLifted X (ZMod (ℓ ^ n))` and transition maps
  -- `topologicalSheafLiftedMap` of the reductions: componentwise the isomorphism is
  -- `sheafPullbackConstantTopologicalIso X (ZMod (ℓ ^ n))`
  -- (`Proetale/Topology/Comparison/ProetConstantSheaf.lean`), and naturality is
  -- `constantToTopologicalSheafLifted_naturality` combined with the naturality of
  -- `sheafPullbackConstantIso` in the coefficient group (it is `.app` of the functor
  -- isomorphism `sheafPullbackCompConstantIso`, see
  -- `Proetale/Topology/Comparison/FreeSheaf.lean`). Define `D` itself with
  -- `Functor.ofSequence`/`leftOp` as for `zmodAbSystem`, or avoid naming `D` by
  -- building the limit cone for the original diagram directly with components passing
  -- through the isomorphisms.
  -- Step 2: build a cone on the diagram with apex the lifted `ellAdicSheaf`:
  -- the leg at `n` is `topologicalSheafLiftedMap X ℤ_[ℓ] ((PadicInt.toZModPow n).toAddMonoidHom)
  -- (continuous_toZModPow ℓ n)` composed with the step-1 isomorphism (inverted);
  -- cone compatibility from `PadicInt.zmod_cast_comp_toZModPow` and functoriality of
  -- `topologicalSheafLiftedMap` in the coefficient map (prove a small composition
  -- lemma `topologicalSheafLiftedMap_comp` first).
  -- Step 3: the cone is limiting; conclude with
  -- `(limit.isLimit _).conePointUniqueUpToIso` or `IsLimit.conePointUniqueUpToIso`.
  -- For the limiting property: `sheafToPresheaf` creates limits, presheaf limits are
  -- detected by evaluation (`evaluationJointlyReflectsLimits`), and limits in `Ab` are
  -- detected by `forget` (`isLimitOfReflects`); at each `U : X.ProEt` the underlying
  -- cone of types is `C(U.left, ℤ_[ℓ]) → (compatible families of C(U.left, ℤ/ℓⁿ))`
  -- (after `ULift`), which is a bijection onto the sections by
  -- `existsUnique_continuousMap_padicInt`; use `Types.isLimit_iff` or build the
  -- comparison with `Types.limitEquivSections` as in the `IsLimit` arguments of
  -- `Proetale/Topology/Comparison/RepleteExact.lean` (read `shortExact_telescope` and
  -- the helpers there for the established pattern).
  exact (isLimitEllAdicCone X ℓ).conePointUniqueUpToIso
    (limit.isLimit (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}))

/-- The transition maps of the pulled-back system are epimorphisms. -/
lemma epi_transition_zmodSystem_sheafPullback (n : ℕ) :
    Epi (SequentialSystem.transition
      (zmodSystem X ℓ ⋙ ProEt.sheafPullback X Ab.{u + 1}) n) := by
  haveI : (ProEt.sheafPullback X Ab.{u + 1}).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (ProEt.sheafAdjunction X Ab.{u + 1})
  exact SequentialSystem.epi_transition_whisker _ (epi_transition_zmodSystem X ℓ) n

end ProEt

end AlgebraicGeometry.Scheme
