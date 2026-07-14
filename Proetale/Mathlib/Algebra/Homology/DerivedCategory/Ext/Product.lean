/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Vanishing of `Ext` into products and dimension shifting

Let `C` be an abelian category with `HasExt`. We record elementary consequences of the
covariant long exact `Ext`-sequence:

- `CategoryTheory.Abelian.Ext.subsingleton_x₁_of_shortExact`: if `0 → X₁ → X₂ → X₃ → 0` is
  exact, `Hom(Z, X₂) → Hom(Z, X₃)` is surjective and the positive `Ext`-groups from `Z` to
  `X₂` and `X₃` vanish, then the positive `Ext`-groups from `Z` to `X₁` vanish.
- `CategoryTheory.Abelian.Ext.subsingleton_pi`: if products indexed by `ι` are exact
  (levelwise epimorphisms induce an epimorphism on products), then vanishing of the
  positive `Ext`-groups `Ext Z (G i)` implies vanishing of `Ext Z (∏ᶜ G)`.
  This is the product analogue of `CategoryTheory.subsingleton_ext_coproduct` and is proved
  by the same dimension shifting argument.
- `CategoryTheory.Abelian.Ext.connectingEquiv`: the connecting isomorphism
  `Ext Z X₃ (n+1) ≃+ Ext Z X₁ (n+2)` when the adjacent `Ext`-groups of `X₂` vanish.
- `CategoryTheory.Abelian.Ext.oneEquivOfHomEquiv`: a comparison of `Ext¹`-groups across two
  ambient abelian categories, given short exact sequences with vanishing `Ext¹` of the
  middle objects and compatible additive equivalences on `Hom`-level.
-/

universe w w' t v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Ext

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (Z : C)

include hS in
/-- If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence, every morphism `Z ⟶ X₃` lifts to
`X₂` and the positive `Ext`-groups from `Z` to `X₂` and to `X₃` vanish, then the positive
`Ext`-groups from `Z` to `X₁` vanish. -/
lemma subsingleton_x₁_of_shortExact
    (hsurj : ∀ s : Z ⟶ S.X₃, ∃ t : Z ⟶ S.X₂, t ≫ S.g = s)
    (h₂ : ∀ q, 0 < q → Subsingleton (Ext Z S.X₂ q))
    (h₃ : ∀ q, 0 < q → Subsingleton (Ext Z S.X₃ q)) :
    ∀ q, 0 < q → Subsingleton (Ext Z S.X₁ q) := by
  -- Let `ξ : Ext Z S.X₁ (m + 1)`. Its image in `Ext Z S.X₂ (m + 1)` vanishes by `h₂`,
  -- so by `Ext.covariant_sequence_exact₁` it is of the form `x₃.comp hS.extClass` with
  -- `x₃ : Ext Z S.X₃ m`. If `m > 0`, then `x₃ = 0` by `h₃`, so `ξ = 0`.
  -- If `m = 0`, write `x₃ = Ext.mk₀ s` (using `Ext.mk₀_homEquiv₀_apply`) and lift
  -- `s = t ≫ S.g` by `hsurj`; then
  -- `ξ = (mk₀ (t ≫ S.g)).comp hS.extClass = (mk₀ t).comp ((mk₀ S.g).comp hS.extClass) = 0`
  -- by `ShortComplex.ShortExact.comp_extClass` (use `Ext.mk₀_comp_mk₀` and associativity).
  intro q hq
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ
    ((h₂ (m + 1) m.succ_pos).elim _ _) rfl
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · obtain ⟨s, rfl⟩ : ∃ s, Ext.mk₀ s = x₃ := ⟨_, Ext.mk₀_homEquiv₀_apply x₃⟩
    obtain ⟨t, rfl⟩ := hsurj s
    rw [← hx₃, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]
  · rw [← hx₃, (h₃ m hm).elim x₃ 0, Ext.zero_comp]

/-- The degree-zero connecting homomorphism `(Z ⟶ S.X₃) →+ Ext Z S.X₁ 1` of the covariant
long exact sequence, sending `s` to `(Ext.mk₀ s).comp hS.extClass`. -/
noncomputable def deltaZero : (Z ⟶ S.X₃) →+ Ext Z S.X₁ 1 :=
  (hS.extClass.postcomp Z (zero_add 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom

@[simp]
lemma deltaZero_apply (s : Z ⟶ S.X₃) :
    deltaZero hS Z s = (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  have h : (Ext.addEquiv₀.symm s : Ext Z S.X₃ 0) = Ext.mk₀ s := by
    have h0 := Ext.mk₀_addEquiv₀_apply ((Ext.addEquiv₀ (X := Z) (Y := S.X₃)).symm s)
    rw [AddEquiv.apply_symm_apply] at h0
    exact h0.symm
  exact congrArg (fun t : Ext Z S.X₃ 0 ↦ t.comp hS.extClass (zero_add 1)) h

include hS in
lemma deltaZero_surjective (h₂ : Subsingleton (Ext Z S.X₂ 1)) :
    Function.Surjective (deltaZero hS Z) := by
  -- For `ξ : Ext Z S.X₁ 1`, the image in `Ext Z S.X₂ 1` vanishes, so
  -- `Ext.covariant_sequence_exact₁` provides `x₃ : Ext Z S.X₃ 0` with
  -- `x₃.comp hS.extClass = ξ`; conclude with `Ext.mk₀_homEquiv₀_apply`.
  intro ξ
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ (h₂.elim _ _) (zero_add 1)
  obtain ⟨s, rfl⟩ : ∃ s, Ext.mk₀ s = x₃ := ⟨_, Ext.mk₀_homEquiv₀_apply x₃⟩
  exact ⟨s, by rw [deltaZero_apply]; exact hx₃⟩

include hS in
lemma deltaZero_apply_eq_zero_iff (s : Z ⟶ S.X₃) :
    deltaZero hS Z s = 0 ↔ ∃ t : Z ⟶ S.X₂, t ≫ S.g = s := by
  -- `←`: `(mk₀ (t ≫ g)).comp extClass = (mk₀ t).comp ((mk₀ g).comp extClass) = 0` by
  --   `ShortComplex.ShortExact.comp_extClass`.
  -- `→`: by `Ext.covariant_sequence_exact₃` applied to `mk₀ s` (in degree 0), there is
  --   `x₂ : Ext Z S.X₂ 0` with `x₂.comp (mk₀ S.g) = mk₀ s`; write `x₂ = mk₀ t` and use
  --   `Ext.mk₀_comp_mk₀` plus injectivity of `mk₀` (`Ext.mk₀_bijective`).
  rw [deltaZero_apply]
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hS (Ext.mk₀ s) (zero_add 1) h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective Z S.X₂).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact ⟨t, (Ext.mk₀_bijective Z S.X₃).1 hx₂⟩
  · rintro ⟨t, rfl⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]

include hS in
/-- If `Hom(Z, S.X₂) → Hom(Z, S.X₃)` is surjective and `Ext Z S.X₂ 1` vanishes, then
`Ext Z S.X₁ 1` vanishes: the degree-zero connecting homomorphism is surjective with
full kernel. -/
private lemma subsingleton_x₁_one
    (hsurj : ∀ s : Z ⟶ S.X₃, ∃ t : Z ⟶ S.X₂, t ≫ S.g = s)
    (h₂ : Subsingleton (Ext Z S.X₂ 1)) :
    Subsingleton (Ext Z S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  obtain ⟨s, rfl⟩ := deltaZero_surjective hS Z h₂ ξ
  exact (deltaZero_apply_eq_zero_iff hS Z s).2 (hsurj s)

/-- The connecting isomorphism `Ext Z S.X₃ (n + 1) ≃+ Ext Z S.X₁ (n + 2)` of the covariant
long exact sequence, when the `Ext`-groups of the middle object in degrees `n + 1` and
`n + 2` vanish. -/
noncomputable def connectingEquiv (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) (h₂' : Subsingleton (Ext Z S.X₂ (n + 2))) :
    Ext Z S.X₃ (n + 1) ≃+ Ext Z S.X₁ (n + 2) := by
  -- The map is `hS.extClass.postcomp Z rfl : Ext Z S.X₃ (n+1) →+ Ext Z S.X₁ (n+2)`.
  -- Injectivity: if `x₃.comp hS.extClass = 0`, then by `Ext.covariant_sequence_exact₃`
  -- `x₃ = x₂.comp (mk₀ S.g)` with `x₂ : Ext Z S.X₂ (n+1) = 0`, so `x₃ = 0`.
  -- Surjectivity: for `ξ : Ext Z S.X₁ (n+2)`, its image in `Ext Z S.X₂ (n+2)` vanishes,
  -- so `Ext.covariant_sequence_exact₁` provides a preimage.
  -- Use `AddEquiv.ofBijective`.
  refine AddEquiv.ofBijective (hS.extClass.postcomp Z rfl) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x₃ hx₃
    have hx₃' : x₃.comp hS.extClass rfl = 0 := hx₃
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hS x₃ rfl hx₃'
    rw [← hx₂, h₂.elim x₂ 0, Ext.zero_comp]
  · intro ξ
    obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ (h₂'.elim _ _) rfl
    exact ⟨x₃, hx₃⟩

end ShortExact

section Pi

variable {ι : Type t} [HasProductsOfShape ι C] [EnoughInjectives C]

omit [HasExt.{w} C] in
private lemma pi_comp_zero (B : ι → C) :
    (Limits.Pi.map fun i ↦ Injective.ι (B i)) ≫
      (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) = 0 := by
  ext i
  simp

omit [HasExt.{w} C] in
/-- The product of the canonical short exact sequences
`0 ⟶ B i ⟶ Injective.under (B i) ⟶ cokernel (Injective.ι (B i)) ⟶ 0` is short exact,
provided that products of levelwise epimorphisms are epimorphisms: the product of the
monomorphisms is a monomorphism since products preserve limits, and exactness in the
middle holds since `Pi.map` of the inclusions is a kernel of `Pi.map` of the
projections (constructed componentwise). -/
private lemma pi_shortExact
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (B : ι → C) :
    (ShortComplex.mk _ _ (pi_comp_zero B)).ShortExact := by
  haveI : Epi (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) :=
    hepi _ _ _ fun i ↦ inferInstance
  refine { exact := ?_ }
  apply ShortComplex.exact_of_f_is_kernel
  refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk ↦ ?_
  have hki : ∀ i, (k ≫ Pi.π (fun j ↦ Injective.under (B j)) i) ≫
      cokernel.π (Injective.ι (B i)) = 0 := fun i ↦ by
    simpa using congrArg
      (fun u ↦ u ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i) hk
  choose l hl using fun i ↦
    (ShortComplex.exact_cokernel (Injective.ι (B i))).lift' _ (hki i)
  refine ⟨Pi.lift l, ?_⟩
  ext i
  simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
  exact hl i

/-- Every morphism into the product of the cokernels lifts to the product of the chosen
injectives, provided that `Ext Z (B i) 1` vanishes for all `i`: lift componentwise via
the covariant long exact sequence. -/
private lemma exists_pi_lift (Z : C) (B : ι → C)
    (hB : ∀ i, Subsingleton (Ext Z (B i) 1))
    (s : Z ⟶ ∏ᶜ fun i ↦ cokernel (Injective.ι (B i))) :
    ∃ t : Z ⟶ ∏ᶜ fun i ↦ Injective.under (B i),
      t ≫ (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) = s := by
  have hlift : ∀ i, ∃ tᵢ : Z ⟶ Injective.under (B i),
      tᵢ ≫ cokernel.π (Injective.ι (B i)) =
        s ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i := by
    intro i
    have hSi : (ShortComplex.mk (Injective.ι (B i)) (cokernel.π (Injective.ι (B i)))
        (cokernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_cokernel _ }
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hSi
      (Ext.mk₀ (s ≫ Pi.π (fun j ↦ cokernel (Injective.ι (B j))) i)) (zero_add 1)
      ((hB i).elim _ _)
    obtain ⟨tᵢ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact ⟨tᵢ, (Ext.mk₀_bijective _ _).1 hx₂⟩
  choose t ht using hlift
  refine ⟨Pi.lift t, ?_⟩
  ext i
  rw [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
  exact ht i

/-- Degree-one case of `CategoryTheory.Abelian.Ext.subsingleton_pi`. -/
private lemma subsingleton_ext_pi_one
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (Z : C) (B : ι → C) (hB : ∀ i, Subsingleton (Ext Z (B i) 1)) :
    Subsingleton (Ext Z (∏ᶜ B) 1) := by
  have hT := pi_shortExact hepi B
  haveI : Injective (∏ᶜ fun i ↦ Injective.under (B i)) := inferInstance
  exact subsingleton_x₁_one hT Z (fun s ↦ exists_pi_lift Z B hB s)
    (subsingleton_of_injective Z (∏ᶜ fun i ↦ Injective.under (B i)) 0)

/-- If levelwise epimorphisms of `ι`-indexed families induce epimorphisms on products,
then vanishing of the positive `Ext`-groups from `Z` to each member of a family `G`
implies vanishing of the positive `Ext`-groups from `Z` to `∏ᶜ G`.

This is the product analogue of `CategoryTheory.subsingleton_ext_coproduct`, proved by
dimension shifting: embed each `G i` into an injective `J i` with cokernel `Q i`; the
product `∏ᶜ J` is injective and `0 → ∏ᶜ G → ∏ᶜ J → ∏ᶜ Q → 0` is short exact by the
product-exactness hypothesis; in degree `1` lift morphisms `Z ⟶ ∏ᶜ Q` componentwise
(using `Ext.covariant_sequence_exact₃` levelwise and vanishing of `Ext Z (G i) 1`), and in
higher degrees use the connecting isomorphism and induction on the degree bound. -/
lemma subsingleton_pi
    (hepi : ∀ (A B : ι → C) (φ : ∀ i, A i ⟶ B i), (∀ i, Epi (φ i)) → Epi (Limits.Pi.map φ))
    (Z : C) (G : ι → C) (hG : ∀ i q, 0 < q → Subsingleton (Ext Z (G i) q)) :
    ∀ q, 0 < q → Subsingleton (Ext Z (∏ᶜ G) q) := by
  -- Structure the induction as in `CategoryTheory.subsingleton_ext_coproduct`
  -- (`Proetale/Topology/Comparison/CohomologyComparison.lean`): prove by induction on `n`
  -- the statement
  -- `∀ G, (∀ i q, 0 < q → q ≤ n → Subsingleton (Ext Z (G i) q)) →`
  -- `  ∀ q, 0 < q → q ≤ n → Subsingleton (Ext Z (∏ᶜ G) q)`,
  -- with the short exact sequences `Sᵢ = (G i ⟶ Injective.under (G i) ⟶ Qᵢ)` and their
  -- product. For the product short complex use:
  -- * mono: `Pi.map` of monomorphisms is a monomorphism (products preserve limits);
  -- * epi: the hypothesis `hepi`;
  -- * exactness: `Pi.map (ι ∘ Injective.ι)` is the kernel of `Pi.map (cokernel.π _)`
  --   since the product functor `Limits.piObjFunctor`/`lim` preserves kernels.
  -- The product of injectives is injective (instance in
  -- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`).
  suffices h : ∀ (n : ℕ) (B : ι → C),
      (∀ i q, 0 < q → q ≤ n + 1 → Subsingleton (Ext Z (B i) q)) →
      ∀ q, 0 < q → q ≤ n + 1 → Subsingleton (Ext Z (∏ᶜ B) q) by
    intro q hq
    exact h q G (fun i q' hq' _ ↦ hG i q' hq') q hq (Nat.le_succ q)
  intro n
  induction n with
  | zero =>
    intro B hB q hq hq'
    obtain rfl : q = 1 := le_antisymm hq' hq
    exact subsingleton_ext_pi_one hepi Z B fun i ↦ hB i 1 one_pos le_rfl
  | succ n IH =>
    intro B hB q hq hq'
    obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
    obtain rfl | hq0 := Nat.eq_zero_or_pos q
    · exact subsingleton_ext_pi_one hepi Z B fun i ↦ hB i 1 one_pos (by omega)
    · have hT := pi_shortExact hepi B
      -- The componentwise vanishing transfers to the cokernels with bound lowered by one.
      have hQ : ∀ (i : ι) (q' : ℕ), 0 < q' → q' ≤ n + 1 →
          Subsingleton (Ext Z (cokernel (Injective.ι (B i))) q') := by
        intro i q' hq'' hq'''
        have hSi : (ShortComplex.mk (Injective.ι (B i)) (cokernel.π (Injective.ι (B i)))
            (cokernel.condition _)).ShortExact :=
          { exact := ShortComplex.exact_cokernel _ }
        refine subsingleton_of_forall_eq 0 fun χ ↦ ?_
        obtain ⟨q', rfl⟩ : ∃ m, q' = m + 1 := ⟨q' - 1, (Nat.succ_pred_eq_of_pos hq'').symm⟩
        obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hSi χ rfl
          ((hB i (q' + 1 + 1) (by omega) (by omega)).elim _ _)
        rw [← hx₂, eq_zero_of_injective x₂, Ext.zero_comp]
      refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
      obtain ⟨η, hη⟩ := covariant_sequence_exact₁ Z hT ξ (eq_zero_of_injective _) rfl
      rw [← hη, (IH (fun i ↦ cokernel (Injective.ι (B i))) hQ q hq0 (by omega)).elim η 0,
        Ext.zero_comp]

end Pi

section OneEquiv

variable {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasExt.{w'} C']
variable {S : ShortComplex C} (hS : S.ShortExact) (Z : C)
variable {S' : ShortComplex C'} (hS' : S'.ShortExact) (Z' : C')

/-- Comparison of `Ext¹`-groups across two abelian categories. Given short exact sequences
`S` and `S'` whose middle objects have vanishing `Ext¹` from `Z` resp. `Z'`, and additive
equivalences on `Hom`-level intertwining the maps to the third objects, the `Ext¹`-groups
of the first objects are isomorphic.

Both sides are identified with the cokernel of `Hom(Z, X₂) → Hom(Z, X₃)` via the
degree-zero connecting homomorphism `Ext.deltaZero`. -/
noncomputable def oneEquivOfHomEquiv
    (e₂ : (Z ⟶ S.X₂) ≃+ (Z' ⟶ S'.X₂)) (e₃ : (Z ⟶ S.X₃) ≃+ (Z' ⟶ S'.X₃))
    (hcomm : ∀ t : Z ⟶ S.X₂, e₃ (t ≫ S.g) = e₂ t ≫ S'.g)
    (h₂ : Subsingleton (Ext Z S.X₂ 1)) (h₂' : Subsingleton (Ext Z' S'.X₂ 1)) :
    Ext Z S.X₁ 1 ≃+ Ext Z' S'.X₁ 1 := by
  -- Strategy: both `deltaZero hS Z` and `deltaZero hS' Z'` are surjective with kernels
  -- the images of `Hom(Z, X₂)` resp. `Hom(Z', X₂')` (by `deltaZero_surjective` and
  -- `deltaZero_apply_eq_zero_iff`). Define the forward map by
  -- `ξ ↦ deltaZero hS' Z' (e₃ s)` for any `s` with `deltaZero hS Z s = ξ`:
  -- well-definedness follows since for `s` in the kernel, `s = t ≫ S.g`, and then
  -- `e₃ s = e₂ t ≫ S'.g` lies in the kernel of `deltaZero hS' Z'` by `hcomm`.
  -- Implement either by lifting along the quotient
  -- `(Z ⟶ S.X₃) ⧸ (kernel of deltaZero)` using `QuotientAddGroup.lift` and
  -- `QuotientAddGroup.congr`, or directly via `AddEquiv.ofBijective` on a map defined
  -- with `Classical.choice`; the quotient route is preferred:
  -- 1. `e₁ : (Z ⟶ S.X₃) ⧸ (deltaZero hS Z).ker ≃+ Ext Z S.X₁ 1` from
  --    `QuotientAddGroup.quotientKerEquivOfSurjective`.
  -- 2. `(deltaZero hS Z).ker.map e₃ = (deltaZero hS' Z').ker` from
  --    `deltaZero_apply_eq_zero_iff`, `hcomm` and surjectivity of `e₂` (both inclusions).
  -- 3. Conclude with `QuotientAddGroup.congr`.
  have hker : AddSubgroup.map (e₃ : (Z ⟶ S.X₃) →+ (Z' ⟶ S'.X₃))
      (AddMonoidHom.ker (deltaZero hS Z)) = AddMonoidHom.ker (deltaZero hS' Z') := by
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, AddMonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := (deltaZero_apply_eq_zero_iff hS Z x).1 hx
      exact (deltaZero_apply_eq_zero_iff hS' Z' _).2 ⟨e₂ t, (hcomm t).symm⟩
    · intro hy
      obtain ⟨t', ht'⟩ := (deltaZero_apply_eq_zero_iff hS' Z' y).1 hy
      obtain ⟨t, rfl⟩ := e₂.surjective t'
      refine ⟨t ≫ S.g, (deltaZero_apply_eq_zero_iff hS Z _).2 ⟨t, rfl⟩, ?_⟩
      rw [hcomm t, ht']
  exact ((QuotientAddGroup.quotientKerEquivOfSurjective _
        (deltaZero_surjective hS Z h₂)).symm.trans
      (QuotientAddGroup.congr (AddMonoidHom.ker (deltaZero hS Z))
        (AddMonoidHom.ker (deltaZero hS' Z')) e₃ hker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (deltaZero_surjective hS' Z' h₂'))

end OneEquiv

end Ext

end CategoryTheory.Abelian
