/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Algebra.WLocalization.Ideal
import Proetale.Algebra.WStrictLocalization
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndZariski
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Proetale.Mathlib.RingTheory.Spectrum.Prime.Topology
import Proetale.Mathlib.Topology.Constructions

/-!
# w-contractible rings

A ring is w-contractible if it is w-strictly-local and the space of connected components of
its prime spectrum is extremally disconnected.

Every w-contractible ring is indeed contractible in the ind-étale topology in the following
sense: If `R` is w-contractible, then every ind-étale faithfully flat map `R →+* S`
has a retraction.

The ind-étale site has enough contractible objects, in the sense that every ring admits a
faithfully flat, ind-étale algebra that is w-contractible.
-/

universe u

/-- A ring `R` is w-contractible if it is w-strictly-local and the space of connected components
of `Spec R` is extremally disconnected. -/
class IsWContractibleRing (R : Type*) [CommRing R] extends IsWStrictlyLocalRing R where
  extremallyDisconnected_connectedComponents :
    ExtremallyDisconnected (ConnectedComponents <| PrimeSpectrum R)

open PrimeSpectrum TopologicalSpace

noncomputable section

namespace WContractification

variable {A : Type u} [CommRing A]

/-!
## The W-Contractification

In this section, we construct w-contractification of w-strictly local rings.
-/

def RestrictClopen (W : Clopens (PrimeSpectrum A)) : Type u :=
  Localization.Away (isIdempotentElemEquivClopens.symm W).val

namespace RestrictClopen

variable {W W₁ W₂ : Clopens (PrimeSpectrum A)}

instance commRing : CommRing (RestrictClopen W) := fast_instance%
  inferInstanceAs <| CommRing <| Localization.Away _

instance algebra : Algebra A (RestrictClopen W) := fast_instance%
  inferInstanceAs <| Algebra A <| Localization.Away _

instance away : IsLocalization.Away (isIdempotentElemEquivClopens.symm W).val
    (RestrictClopen W) :=
  inferInstanceAs <| IsLocalization.Away _ <| Localization.Away _

instance isStandardOpenImmersion : Algebra.IsStandardOpenImmersion A (RestrictClopen W) :=
  ⟨(isIdempotentElemEquivClopens.symm W).val, RestrictClopen.away⟩

lemma val_dvd {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    (isIdempotentElemEquivClopens.symm W₂).val ∣
    (isIdempotentElemEquivClopens.symm W₁).val := by
  use (isIdempotentElemEquivClopens.symm W₁).val
  nth_rw 1 [(isIdempotentElemEquivClopens.symm.monotone h).symm, mul_comm]

open IsLocalization Away in
def map {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    RestrictClopen W₂ →ₐ[A] RestrictClopen W₁ where
  toRingHom := lift (isIdempotentElemEquivClopens.symm W₂).val (isUnit_of_dvd _ (val_dvd h))
  commutes' r := by simp

/-- The range of `Spec`-side comap of the algebra map `A → RestrictClopen W` is `W`. -/
lemma range_comap (W : Clopens (PrimeSpectrum A)) :
    Set.range (PrimeSpectrum.comap (algebraMap A (RestrictClopen W))) =
      (W : Set (PrimeSpectrum A)) := by
  rw [localization_away_comap_range (RestrictClopen W) (isIdempotentElemEquivClopens.symm W).val]
  exact congr_arg Opens.carrier (basicOpen_isIdempotentElemEquivClopens_symm W)

end RestrictClopen

open scoped CategoryTheory
open CategoryTheory.Limits Topology PrimeSpectrum ConnectedComponents Continuous

section Restriction
variable (T : Set (ConnectedComponents (PrimeSpectrum A)))

def Restriction.diag :
    {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W}ᵒᵖ ⥤ CommAlgCat A where
  obj W := .of A (RestrictClopen W.unop.val)
  map {X Y} f := CommAlgCat.ofHom (RestrictClopen.map f.unop.le)
  map_id X := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _
  map_comp {X _ _} _ _ := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _

def Restriction : Type u :=
  colimit (C := CommAlgCat A) (Restriction.diag T)

namespace Restriction

instance commRing : CommRing (Restriction T) :=
  inferInstanceAs <| CommRing <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance algebra : Algebra A (Restriction T) :=
  inferInstanceAs <| Algebra A <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance nonempty_index :
    Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
  ⟨⟨⊤, le_top⟩⟩

instance isCofiltered_index : CategoryTheory.IsCofiltered
    {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} where
  cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ =>
    ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_left),
      CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_right), trivial⟩
  cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩

instance indZariski : Algebra.IndZariski A (Restriction T) := by
  rw [Algebra.IndZariski.iff_ind_isLocalIso]
  exact ⟨_, inferInstance, inferInstance, .colimit (Restriction.diag T),
    fun W => show Algebra.IsLocalIso A (RestrictClopen W.unop.val) from inferInstance⟩

lemma algebraMap_surjective : Function.Surjective (algebraMap A (Restriction T)) := by
  intro x
  -- The forgetful functor preserves filtered colimits, giving joint surjectivity.
  have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
  have hc' := CategoryTheory.Limits.isColimitOfPreserves
    (CategoryTheory.forget (CommAlgCat A)) hc
  obtain ⟨⟨j⟩, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc' x
  -- `algebraMap A (RestrictClopen j.val)` is surjective (localization at an idempotent).
  have hpiece : Function.Surjective (algebraMap A (RestrictClopen j.val)) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (isIdempotentElemEquivClopens.symm j.val).val
      (isIdempotentElemEquivClopens.symm j.val).prop
  obtain ⟨a, ha⟩ := hpiece y
  refine ⟨a, ?_⟩
  simp only [CategoryTheory.Functor.mapCocone_ι_app, colimit.cocone_ι,
    CategoryTheory.ConcreteCategory.hom_ofHom] at hy
  rw [← hy, ← ha]
  exact ((colimit.ι (Restriction.diag T) (Opposite.op j)).hom.commutes a).symm

variable {T}

/-- The zero locus of the kernel of `A → RestrictClopen W` equals `W`. -/
lemma zeroLocus_ker_restrictClopen_eq (W : Clopens (PrimeSpectrum A)) :
    zeroLocus (RingHom.ker (algebraMap A (RestrictClopen W)) : Set A) =
      (W : Set (PrimeSpectrum A)) := by
  rw [← range_comap_of_surjective (RestrictClopen W) (algebraMap A (RestrictClopen W))
        (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
          (isIdempotentElemEquivClopens.symm W).prop),
      RestrictClopen.range_comap]

/-- For `W` a clopen containing the preimage of `T`, the kernel of `A → RestrictClopen W`
is contained in the kernel of the algebra map into the colimit `Restriction T`. -/
lemma ker_algebraMap_restrictClopen_le
    {W : Clopens (PrimeSpectrum A)} (hW : ConnectedComponents.mk ⁻¹' T ≤ W) :
    RingHom.ker (algebraMap A (RestrictClopen W)) ≤
      RingHom.ker (algebraMap A (Restriction T)) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  let ι : RestrictClopen W →ₐ[A] Restriction T :=
    (colimit.ι (Restriction.diag T) (Opposite.op ⟨W, hW⟩)).hom
  calc algebraMap A (Restriction T) a
      = ι (algebraMap A (RestrictClopen W) a) := (ι.commutes a).symm
    _ = ι 0 := by rw [ha]
    _ = 0 := map_zero _

/-- The image of `Spec(Restriction T) → Spec A` is the preimage of `T` under the projection
`Spec A → π₀(Spec A)`, whenever `T` is closed. -/
lemma range_algebraMap_specComap (h : IsClosed T) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Restriction T)) =
      ConnectedComponents.mk ⁻¹' T := by
  rw [range_comap_of_surjective _ _ (algebraMap_surjective T)]
  refine Set.Subset.antisymm ?_ ?_
  · -- ⊆: any prime in `V(ker)` lies in every clopen containing the preimage of `T`,
    -- hence in the intersection of all such clopens, which is the preimage of `T`
    -- by Stacks 04PL.
    intro p hp
    have hp_mem_W : ∀ (W : Clopens (PrimeSpectrum A)),
        ConnectedComponents.mk ⁻¹' T ≤ W → p ∈ (W : Set (PrimeSpectrum A)) := fun W hW ↦ by
      rw [← zeroLocus_ker_restrictClopen_eq W]
      exact zeroLocus_anti_mono (ker_algebraMap_restrictClopen_le (T := T) hW) hp
    obtain ⟨J, hJ⟩ := isClosed_and_iUnion_connectedComponent_eq_iff.mp
      ⟨h.preimage ConnectedComponents.continuous_coe,
        _, ConnectedComponents.iUnion_connectedComponent_preimage_mk T⟩
    rw [← hJ]
    simp only [Set.iInter_coe_set, Set.mem_iInter, Subtype.forall]
    intro V hV hVJ
    refine hp_mem_W ⟨V, hV⟩ ?_
    rw [← hJ]
    exact Set.iInter_subset_of_subset ⟨⟨V, hV⟩, hVJ⟩ le_rfl
  · -- ⊇: given `a ∈ ker(A → Restriction T)`, the equality criterion for filtered colimits
    -- yields a clopen `W ⊇ T` at which `a` already vanishes. Then `p ∈ W` forces `a ∈ p`.
    intro p hp
    rw [mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, RingHom.mem_ker] at ha
    let ι_top := colimit.ι (Restriction.diag T) (Opposite.op ⟨(⊤ : Clopens _), le_top⟩)
    have heq_in_colim : ι_top.hom (algebraMap A (RestrictClopen ⊤) a) =
        ι_top.hom (0 : RestrictClopen ⊤) :=
      (ι_top.hom.commutes a).trans (ha.trans (map_zero ι_top.hom).symm)
    obtain ⟨k, f, g, hfg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff
        (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A))
        (isColimitOfPreserves (CategoryTheory.forget (CommAlgCat A))
          (colimit.isColimit (Restriction.diag T)))).mp heq_in_colim
    let W := k.unop.val
    have hW : ConnectedComponents.mk ⁻¹' T ≤ W := k.unop.property
    have hf_alg : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map f
        (algebraMap A (RestrictClopen ⊤) a) = algebraMap A (RestrictClopen W) a :=
      ((Restriction.diag T).map f).hom.commutes a
    have ha_zero : algebraMap A (RestrictClopen W) a = 0 := by
      rw [← hf_alg, hfg]
      exact map_zero ((Restriction.diag T).map g).hom
    have hker_le : RingHom.ker (algebraMap A (RestrictClopen W)) ≤ p.asIdeal := by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus]
      exact zeroLocus_ker_restrictClopen_eq W ▸ hW hp
    exact hker_le (RingHom.mem_ker.mpr ha_zero)

/-- The map `Spec(Restriction T) → Spec A` is a closed embedding. -/
lemma isClosedEmbedding_algebraMap_specComap :
    IsClosedEmbedding (PrimeSpectrum.comap <| algebraMap A (Restriction T)) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective (Restriction T)
    (algebraMap A (Restriction T)) (algebraMap_surjective T)

end Restriction

end Restriction

section Pullback

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

def Z := Set.range fun t ↦ connectedComponentsMap (PrimeSpectrum.continuous_sigmaToPi fun _ ↦ A) <|
  connectedComponentsMap Prod.continuous_toSigma (prodMap.symm (mkHomeomorph _ (S.proj t), f t))

def Pullback := Restriction (Z S f)

namespace Pullback

instance commRing : CommRing (Pullback S f) :=
  inferInstanceAs <| CommRing <| Restriction (Z S f)

instance algebra' : Algebra (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra (S → A) <| Restriction (Z S f)

instance algebra : Algebra A (Pullback S f) :=
  Algebra.compHom _ (Pi.ringHom fun _ : S ↦ RingHom.id A)

instance isScalarTower : IsScalarTower A (S → A) (Pullback S f) :=
  .of_algebraMap_eq' rfl

variable {T : Type u} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

instance indZariski' : Algebra.IndZariski (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra.IndZariski (S → A) <| Restriction (Z S f)

instance indZariski : Algebra.IndZariski A (Pullback S f) :=
  .trans A (S → A) (Pullback S f)

theorem bijectiveOnStalks_algebraMap : (algebraMap A (Pullback S f)).BijectiveOnStalks :=
  Algebra.IndZariski.bijectiveOnStalks_algebraMap _ _

-- Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting for 1.123

end Pullback

end Pullback

end WContractification

end

variable {R : Type u} [CommRing R]

/--
Let `R` be a w-contractible ring and `I` an ideal of `R` cutting out the set `X^c` of closed
points in `Spec R`. Then every faithfully flat ind-étale map `R →+* S` with `S` w-local and
whose closed points of `Spec S` are exactly `V(IB)` has a retraction.
-/
theorem IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints
    [IsWContractibleRing R]
    {I : Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R)) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S)) :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  sorry -- thm:ind-etale-plus-c-has-retraction-if-w-contractible

variable (R)

/-- If `R` is w-contractible, every faithfully flat, ind-étale map `R →+* S` has a retraction. -/
theorem IsWContractibleRing.exists_retraction [IsWContractibleRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  let I := vanishingIdeal (closedPoints (PrimeSpectrum R))
  have hI : zeroLocus I = closedPoints (PrimeSpectrum R) := by
    rw [zeroLocus_vanishingIdeal_eq_closure,
      IsClosed.closure_eq IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints]
  let S' := (I.map (algebraMap R S)).WLocalization
  have : Module.FaithfullyFlat R S' :=
    Ideal.WLocalization.faithfullyFlat_map_algebraMap hI (fun _ _ ↦ inferInstance)
  have : Algebra.IndEtale R S' := Algebra.IndEtale.trans R S S'
  have : zeroLocus (I.map (algebraMap R S')) = closedPoints (PrimeSpectrum S') :=
    Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq hI (fun _ _ ↦ inferInstance)
  obtain ⟨g, hg⟩ := IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints hI this
  use g.comp (algebraMap S S')
  simp only [RingHom.comp_assoc]
  exact hg

/-- Any w-strictly-local ring has an ind-Zariski, faithfully flat cover that is w-contractible. -/
lemma exists_isWContractibleRing_of_isWStrictlyLocal
    [IsWStrictlyLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndZariski R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S :=
  sorry

/-- Any ring has an ind-étale, faithfully flat cover that is w-contractible. -/
theorem exists_isWContractibleRing :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S := by
  obtain ⟨S, _, _, _, _, _⟩ :=
    exists_isWContractibleRing_of_isWStrictlyLocal (WStrictLocalization R)
  letI : Algebra R S := Algebra.compHom _ (algebraMap R (WStrictLocalization R))
  have : IsScalarTower R (WStrictLocalization R) S := .of_algebraMap_eq' rfl
  refine ⟨S, inferInstance, inferInstance, ?_, ?_, inferInstance⟩
  · exact Algebra.IndEtale.trans _ (WStrictLocalization R) _
  · exact Module.FaithfullyFlat.trans _ (WStrictLocalization R) _

/-- Any ring has an ind-étale, faithfully flat cover for which every ind-étale
faithfully flat cover splits. -/
theorem exists_forall_exists_retraction :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧
      ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.IndEtale S T] [Module.FaithfullyFlat S T],
        ∃ (f : T →+* S), f.comp (algebraMap S T) = RingHom.id S := by
  obtain ⟨S, _, _, _, _, _⟩ := exists_isWContractibleRing R
  use S, inferInstance, inferInstance, inferInstance, inferInstance
  intro T _ _ _ _
  obtain ⟨f, hf⟩ := IsWContractibleRing.exists_retraction S T
  use f, hf
