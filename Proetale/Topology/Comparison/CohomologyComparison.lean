/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Proetale.Topology.Comparison.Acyclicity

/-!
# Comparison of étale and pro-étale cohomology

Let `S` be a scheme and `ν^* : Sheaf S.smallEtaleTopology Ab ⥤ Sheaf (ProEt.topology S) Ab`
the pullback functor along the inclusion of the small étale site into the pro-étale site.
We show:

- `AlgebraicGeometry.Scheme.ProEt.mapExt_bijective_sheafPullback`: `ν^*` induces bijections
  on all `Ext`-groups of abelian sheaves ([BS15, Corollary 5.1.8] in the abelian setting).
- `AlgebraicGeometry.Scheme.ProEt.sheafHAddEquiv`: for an abelian sheaf `K` on the small
  étale site, `H^n(S_proét, ν^*K) ≃+ H^n(S_ét, K)` ([BS15, Corollary 5.1.6]).

The proof applies `Functor.mapExt_bijective_of_exists_epi`: the functor `ν^*` is exact and
fully faithful, and every abelian sheaf on the small étale site admits an epimorphism from
a coproduct of free abelian sheaves on *affine* étale `S`-schemes. By the key acyclicity
result `ProEt.subsingleton_ext_sheafPullback_injective`, the pullbacks of injective sheaves
have no higher `Ext`s from pullbacks of such free sheaves; a dimension shifting argument
(`CategoryTheory.subsingleton_ext_coproduct`) extends this vanishing to the coproducts.
-/

universe w t v u u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory

section ExtTransport

variable {C : Type u₂} [Category.{v₂} C] [Abelian C] [HasExt.{w} C]

namespace Abelian.Ext

/-- `Subsingleton` of `Ext`-groups transports along isomorphisms in the first argument. -/
lemma subsingleton_of_iso {X X' Y : C} (e : X ≅ X') (n : ℕ)
    (h : Subsingleton (Ext X Y n)) : Subsingleton (Ext X' Y n) := by
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  have h0 : (mk₀ e.hom).comp ξ (zero_add n) = 0 := h.elim _ _
  calc ξ = (mk₀ (𝟙 X')).comp ξ (zero_add n) := (mk₀_id_comp ξ).symm
    _ = (mk₀ e.inv).comp ((mk₀ e.hom).comp ξ (zero_add n)) (zero_add n) := by
        rw [mk₀_comp_mk₀_assoc, Iso.inv_hom_id]
    _ = 0 := by rw [h0, comp_zero]

/-- Precomposition with (the degree zero class of) an isomorphism, as an additive
equivalence of `Ext`-groups. -/
noncomputable def precompAddEquiv {X X' : C} (e : X ≅ X') (Y : C) (n : ℕ) :
    Ext X' Y n ≃+ Ext X Y n where
  toFun ξ := (mk₀ e.hom).comp ξ (zero_add n)
  invFun ξ := (mk₀ e.inv).comp ξ (zero_add n)
  left_inv ξ := by dsimp only; rw [mk₀_comp_mk₀_assoc, Iso.inv_hom_id, mk₀_id_comp]
  right_inv ξ := by dsimp only; rw [mk₀_comp_mk₀_assoc, Iso.hom_inv_id, mk₀_id_comp]
  map_add' ξ ξ' := comp_add _ _ _ _

end Abelian.Ext

end ExtTransport

section ExtCoproduct

variable {C : Type u₂} [Category.{v₂} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]

/-- If all `Ext¹ (A i) B` vanish, then `Ext¹ (∐ A) B` vanishes. -/
lemma subsingleton_ext_coproduct_one {ι : Type t} (A : ι → C) [HasCoproduct A] (B : C)
    (h : ∀ i, Subsingleton (Ext (A i) B 1)) : Subsingleton (Ext (∐ A) B 1) := by
  let S : ShortComplex C := ShortComplex.mk (Injective.ι B) (cokernel.π (Injective.ι B))
    (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  haveI hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under B))
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  obtain ⟨η, hη⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (Ext.eq_zero_of_injective _) rfl
  obtain ⟨s, rfl⟩ : ∃ s, Ext.mk₀ s = η := ⟨_, Ext.mk₀_homEquiv₀_apply η⟩
  -- The degree zero class `s : ∐ A ⟶ S.X₃` lifts componentwise through `S.g`.
  have hlift : ∀ i, ∃ tᵢ : A i ⟶ S.X₂, tᵢ ≫ S.g = Limits.Sigma.ι A i ≫ s := by
    intro i
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS
      (Ext.mk₀ (Limits.Sigma.ι A i ≫ s)) rfl ((h i).elim _ _)
    obtain ⟨tᵢ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact ⟨tᵢ, (Ext.mk₀_bijective _ _).1 hx₂⟩
  choose lift hlift using hlift
  have hfac : s = Limits.Sigma.desc lift ≫ S.g :=
    Limits.Sigma.hom_ext _ _ fun i ↦ by rw [Limits.Sigma.ι_desc_assoc, hlift i]
  rw [← hη, hfac, ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_comp, hS.comp_extClass, Ext.comp_zero]

/-- Vanishing of `Ext`-groups out of the components of a coproduct in a range of positive
degrees implies vanishing of the `Ext`-groups out of the coproduct in the same range.
This is proved by a dimension shifting induction on the bound of the range. -/
lemma subsingleton_ext_coproduct {ι : Type t} (A : ι → C) [HasCoproduct A] (n : ℕ) :
    ∀ (B : C), (∀ (i : ι) (q : ℕ), 0 < q → q ≤ n + 1 → Subsingleton (Ext (A i) B q)) →
      ∀ (q : ℕ), 0 < q → q ≤ n + 1 → Subsingleton (Ext (∐ A) B q) := by
  induction n with
  | zero =>
    intro B hB q hq hq'
    obtain rfl : q = 1 := le_antisymm hq' hq
    exact subsingleton_ext_coproduct_one A B fun i ↦ hB i 1 one_pos le_rfl
  | succ n IH =>
    intro B hB q hq hq'
    obtain ⟨q, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
    obtain rfl | hq0 := Nat.eq_zero_or_pos q
    · exact subsingleton_ext_coproduct_one A B fun i ↦ hB i 1 one_pos (by omega)
    let S : ShortComplex C := ShortComplex.mk (Injective.ι B) (cokernel.π (Injective.ι B))
      (cokernel.condition _)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
    haveI hinj : Injective S.X₂ := inferInstanceAs (Injective (Injective.under B))
    -- The componentwise vanishing transfers to the cokernel `S.X₃` with bound lowered by one.
    have hQ : ∀ (i : ι) (q' : ℕ), 0 < q' → q' ≤ n + 1 → Subsingleton (Ext (A i) S.X₃ q') := by
      intro i q' hq' hq''
      refine subsingleton_of_forall_eq 0 fun χ ↦ ?_
      obtain ⟨q', rfl⟩ : ∃ m, q' = m + 1 := ⟨q' - 1, (Nat.succ_pred_eq_of_pos hq').symm⟩
      obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS χ rfl
        ((hB i (q' + 1 + 1) (by omega) (by omega)).elim _ _)
      rw [← hx₂, Ext.eq_zero_of_injective x₂, Ext.zero_comp]
    refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
    obtain ⟨η, hη⟩ := Ext.covariant_sequence_exact₁ _ hS ξ (Ext.eq_zero_of_injective _) rfl
    rw [← hη, (IH S.X₃ hQ q hq0 (by omega)).elim η 0, Ext.zero_comp]

end ExtCoproduct

section LanEvaluation

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]
  {E : Type u₁} [Category.{v₁} E]

set_option backward.isDefEq.respectTransparency false in
/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved. -/
noncomputable def Functor.lanEvaluationIsoColim' (F : C ⥤ D) (X : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end LanEvaluation

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

instance (ι : Type (u + 1)) :
    HasColimitsOfShape (Discrete ι) (Sheaf S.smallEtaleTopology Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

instance (ι : Type (u + 1)) :
    HasColimitsOfShape (Discrete ι) (Sheaf (ProEt.topology S) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

instance : HasFilteredColimitsOfSize.{u, u + 1} Ab.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

instance : AB5OfSize.{u, u + 1} Ab.{u + 1} :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} Ab.{u + 1}

/-- The category of abelian sheaves on the small étale site of `S : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. -/
instance : IsGrothendieckAbelian.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

namespace ProEt

/-- The left Kan extension of abelian presheaves along the inclusion of the étale site
into the pro-étale site is exact, since the inclusion is representably flat. -/
noncomputable instance preservesFiniteLimits_lan :
    PreservesFiniteLimits ((toProEtale S).op.lan :
      (S.Etaleᵒᵖ ⥤ Ab.{u + 1}) ⥤ S.ProEtᵒᵖ ⥤ Ab.{u + 1}) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro K
  haveI : IsFiltered (CostructuredArrow (toProEtale S).op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (toProEtale S) (unop K))
  exact preservesLimitsOfShape_of_natIso
    (Functor.lanEvaluationIsoColim' (toProEtale S).op K).symm

instance : PreservesFiniteLimits (ProEt.sheafPullback S Ab.{u + 1}) :=
  Functor.sheafPullbackConstruction.preservesFiniteLimits (toProEtale S) Ab.{u + 1}
    (smallEtaleTopology S) (ProEt.topology S)

instance : PreservesFiniteColimits (ProEt.sheafPullback S Ab.{u + 1}) :=
  haveI : PreservesColimitsOfSize.{0, 0} (ProEt.sheafPullback S Ab.{u + 1}) :=
    (ProEt.sheafAdjunction S Ab.{u + 1}).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

instance : (ProEt.sheafPullback S Ab.{u + 1}).Additive := by
  haveI : (ProEt.sheafPullback S Ab.{u + 1}).IsLeftAdjoint :=
    (ProEt.sheafAdjunction S Ab.{u + 1}).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _

section Generators

variable {S}

/-- The index type for the family of free abelian sheaves on affine étale `S`-schemes
mapping to an abelian sheaf `X` on the small étale site: pairs of an affine étale
`S`-scheme `V` and a section of `X` over `V`. -/
def GeneratorIndex (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) : Type (u + 1) :=
  (V : S.AffineEtale) ×
    ((sheafToPresheaf S.smallEtaleTopology Ab.{u + 1}).obj X ⋙
      CategoryTheory.forget Ab.{u + 1}).obj (op ((AffineEtale.Spec S).obj V))

variable (S) in
/-- The family of free abelian sheaves on affine étale `S`-schemes indexed by sections
of `X`. -/
noncomputable abbrev generatorFamily (X : Sheaf S.smallEtaleTopology Ab.{u + 1})
    (i : GeneratorIndex X) : Sheaf S.smallEtaleTopology Ab.{u + 1} :=
  (freeAbelianSheafFunctor S.smallEtaleTopology).obj ((AffineEtale.Spec S).obj i.1)

variable (S) in
/-- The canonical morphism from the coproduct of the free abelian sheaves on all affine
étale `S`-schemes with a section of `X` to `X`. It is an epimorphism since affine étale
`S`-schemes are cover dense in the small étale site. -/
noncomputable def generatorTo (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    ∐ generatorFamily S X ⟶ X :=
  Sigma.desc fun i ↦ freeAbelianSheafHomEquiv.symm i.2

lemma isLocallySurjective_generatorTo (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    Presheaf.IsLocallySurjective S.smallEtaleTopology (generatorTo S X).hom := by
  constructor
  intro U s
  refine S.smallEtaleTopology.superset_covering ?_
    ((AffineEtale.Spec S).is_cover_of_isCoverDense S.smallEtaleTopology U)
  rintro W g ⟨hg⟩
  -- The index given by the restriction of `s` along `hg.map`.
  let i : GeneratorIndex X := ⟨hg.obj,
    ((sheafToPresheaf S.smallEtaleTopology Ab.{u + 1}).obj X ⋙
      CategoryTheory.forget Ab.{u + 1}).map hg.map.op s⟩
  refine ⟨freeAbelianSheafHomEquiv
    ((freeAbelianSheafFunctor S.smallEtaleTopology).map hg.lift ≫
      Sigma.ι (generatorFamily S X) i), ?_⟩
  have h1 : ((freeAbelianSheafFunctor S.smallEtaleTopology).map hg.lift ≫
      Sigma.ι (generatorFamily S X) i) ≫ generatorTo S X =
      (freeAbelianSheafFunctor S.smallEtaleTopology).map hg.lift ≫
        freeAbelianSheafHomEquiv.symm i.2 := by
    rw [Category.assoc, generatorTo, Sigma.ι_desc]
  have h2 := freeAbelianSheafHomEquiv_naturality_right
    ((freeAbelianSheafFunctor S.smallEtaleTopology).map hg.lift ≫
      Sigma.ι (generatorFamily S X) i) (generatorTo S X)
  rw [h1] at h2
  have h3 := freeAbelianSheafHomEquiv_naturality_left hg.lift
    (freeAbelianSheafHomEquiv.symm i.2)
  rw [Equiv.apply_symm_apply] at h3
  rw [h3] at h2
  refine h2.symm.trans ?_
  change ((sheafToPresheaf S.smallEtaleTopology Ab.{u + 1}).obj X ⋙
      CategoryTheory.forget Ab.{u + 1}).map hg.lift.op
      (((sheafToPresheaf S.smallEtaleTopology Ab.{u + 1}).obj X ⋙
        CategoryTheory.forget Ab.{u + 1}).map hg.map.op s) = _
  rw [← Functor.map_comp_apply, ← op_comp, hg.fac]
  rfl

instance epi_generatorTo (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    Epi (generatorTo S X) :=
  haveI : Sheaf.IsLocallySurjective (generatorTo S X) := isLocallySurjective_generatorTo X
  Sheaf.epi_of_isLocallySurjective _

/-- The pullbacks of the free abelian sheaves in the generating family to the pro-étale
site are acyclic for pullbacks of injective sheaves: this is the content of
`ProEt.subsingleton_ext_sheafPullback_injective`, transported along the identification
of the pullback of a free abelian sheaf with the free abelian sheaf on the image. -/
lemma subsingleton_ext_sheafPullback_generatorFamily
    (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) (i : GeneratorIndex X)
    {I : Sheaf S.smallEtaleTopology Ab.{u + 1}} (hI : Injective I) (n : ℕ) :
    Subsingleton (Ext ((ProEt.sheafPullback S Ab.{u + 1}).obj (generatorFamily S X i))
      ((ProEt.sheafPullback S Ab.{u + 1}).obj I) (n + 1)) :=
  Abelian.Ext.subsingleton_of_iso
    ((freeAbelianSheafFunctor (ProEt.topology S)).mapIso
        ((AffineEtale.toAffineProEtCompToProEtIso S).app i.1) ≪≫
      (ProEt.sheafPullbackFreeIso S ((AffineEtale.Spec S).obj i.1)).symm) _
    (ProEt.subsingleton_ext_sheafPullback_injective S I hI
      ((AffineEtale.toAffineProEt S).obj i.1) n)

/-- Every abelian sheaf on the small étale site of `S` admits an epimorphism from an
object whose pullback to the pro-étale site is acyclic for pullbacks of injectives. -/
lemma exists_epi_acyclic (X : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    ∃ (P : Sheaf S.smallEtaleTopology Ab.{u + 1}) (π : P ⟶ X), Epi π ∧
      ∀ (I : Sheaf S.smallEtaleTopology Ab.{u + 1}), Injective I → ∀ (n : ℕ),
        Subsingleton (Ext ((ProEt.sheafPullback S Ab.{u + 1}).obj P)
          ((ProEt.sheafPullback S Ab.{u + 1}).obj I) (n + 1)) := by
  refine ⟨∐ generatorFamily S X, generatorTo S X, inferInstance, fun I hI n ↦ ?_⟩
  haveI : PreservesColimitsOfSize.{u + 1, u + 1} (ProEt.sheafPullback S Ab.{u + 1}) :=
    (ProEt.sheafAdjunction S Ab.{u + 1}).leftAdjoint_preservesColimits
  refine Abelian.Ext.subsingleton_of_iso
    (PreservesCoproduct.iso (ProEt.sheafPullback S Ab.{u + 1}) (generatorFamily S X)).symm _ ?_
  refine subsingleton_ext_coproduct
    (fun i ↦ (ProEt.sheafPullback S Ab.{u + 1}).obj (generatorFamily S X i)) n
    ((ProEt.sheafPullback S Ab.{u + 1}).obj I) (fun i q hq _ ↦ ?_) (n + 1) n.succ_pos le_rfl
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  exact subsingleton_ext_sheafPullback_generatorFamily X i hI m

end Generators

variable {S} in
/-- **Comparison of étale and pro-étale `Ext`-groups** ([BS15, Corollary 5.1.8]): the
pullback functor from abelian sheaves on the small étale site of `S` to abelian sheaves
on the pro-étale site of `S` induces bijections on all `Ext`-groups. -/
theorem mapExt_bijective_sheafPullback (F K : Sheaf S.smallEtaleTopology Ab.{u + 1}) (n : ℕ) :
    Function.Bijective ((ProEt.sheafPullback S Ab.{u + 1}).mapExtAddHom F K n) :=
  Functor.mapExt_bijective_of_exists_epi _ (fun X ↦ exists_epi_acyclic X) F K n

variable {S} in
/-- **Comparison of étale and pro-étale cohomology** ([BS15, Corollary 5.1.6] in the
abelian setting): for an abelian sheaf `K` on the small étale site of `S`, the cohomology
of its pullback to the pro-étale site agrees with its cohomology. -/
noncomputable def sheafHAddEquiv (K : Sheaf S.smallEtaleTopology Ab.{u + 1}) (n : ℕ) :
    Sheaf.H ((ProEt.sheafPullback S Ab.{u + 1}).obj K) n ≃+ Sheaf.H K n :=
  (Abelian.Ext.precompAddEquiv
      (ProEt.sheafPullbackConstantIso S (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((ProEt.sheafPullback S Ab.{u + 1}).obj K) n).trans
    (AddEquiv.ofBijective _ (mapExt_bijective_sheafPullback
      ((constantSheaf S.smallEtaleTopology Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) K n)).symm

end ProEt

end AlgebraicGeometry.Scheme
