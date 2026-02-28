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
  Localization.isLocalization

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
  commutes' := fun r => by simp

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
  map_comp {X Y Z} f g := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _

def Restriction : Type u :=
  colimit (C := CommAlgCat A) (Restriction.diag T)

namespace Restriction

instance commRing : CommRing (Restriction T) := fast_instance%
  inferInstanceAs <| CommRing <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance algebra : Algebra A (Restriction T) := fast_instance%
  inferInstanceAs <| Algebra A <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance indZariski : Algebra.IndZariski A (Restriction T) := by
  rw [Algebra.IndZariski.iff_ind_isLocalIso]
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { }
  exact ⟨_, inferInstance, inferInstance, .colimit (Restriction.diag T),
    fun W => show Algebra.IsLocalIso A (RestrictClopen W.unop.val) from inferInstance⟩

lemma algebraMap_surjective : Function.Surjective (algebraMap A (Restriction T)) := by
  intro x
  -- The colimit is a filtered colimit since the indexing category is cofiltered
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} := { }
  -- Use that forget preserves filtered colimits to get jointly surjective
  have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
  have hc' := CategoryTheory.Limits.isColimitOfPreserves
    (CategoryTheory.forget (CommAlgCat A)) hc
  obtain ⟨⟨j⟩, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc' x
  -- y is in the underlying type of RestrictClopen j.val
  -- The algebraMap from A to RestrictClopen j.val is surjective (localization at idempotent)
  have hpiece : Function.Surjective (algebraMap A (RestrictClopen j.val)) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (isIdempotentElemEquivClopens.symm j.val).val
      (isIdempotentElemEquivClopens.symm j.val).prop
  obtain ⟨a, ha⟩ := hpiece y
  -- The cocone map sends algebraMap a to algebraMap a
  refine ⟨a, ?_⟩
  -- x = cocone.ι.app (op j) y, and y = algebraMap a, so x = cocone.ι.app (op j) (algebraMap a)
  -- algebraMap A (Restriction T) a = cocone.ι.app (op j) (algebraMap A (RestrictClopen j.val) a)
  -- since the algebra structure on Restriction T restricts through the cocone
  change (CategoryTheory.forget (CommAlgCat A)).map
    (colimit.ι (Restriction.diag T) (Opposite.op j)) y = x at hy
  rw [← ha] at hy
  -- Now need: algebraMap A (Restriction T) a = cocone map applied to (algebraMap A (RestrictClopen j.val) a)
  -- This holds by the fact that the cocone map is an algebra hom
  change algebraMap A (colimit (C := CommAlgCat A) (Restriction.diag T)) a = x
  rw [← hy]
  -- The cocone map is an AlgHom, so it commutes with algebraMap
  let ι_alg : RestrictClopen j.val →ₐ[A] colimit (C := CommAlgCat A) (Restriction.diag T) :=
    (colimit.ι (Restriction.diag T) (Opposite.op j)).hom
  exact (ι_alg.commutes a).symm

variable {T}

-- Helper: the range of Spec(RestrictClopen W) -> Spec(A) equals W as a set.
private lemma restrictClopen_range_eq (W : Clopens (PrimeSpectrum A)) :
    Set.range (PrimeSpectrum.comap (algebraMap A (RestrictClopen W))) =
      (W : Set (PrimeSpectrum A)) := by
  rw [localization_away_comap_range (RestrictClopen W) (isIdempotentElemEquivClopens.symm W).val]
  have h := basicOpen_isIdempotentElemEquivClopens_symm W
  -- h : basicOpen e_W = W.toOpens (as Opens)
  -- Need: (basicOpen e_W : Set _) = (W : Set _)
  -- W : Clopens _, coercion to Set goes through toOpens
  change (basicOpen (isIdempotentElemEquivClopens.symm W).val).carrier = W.toOpens.carrier
  exact congr_arg Opens.carrier h

-- Helper: for each W, ker(A -> A_W) ⊆ ker(A -> colim)
private lemma ker_algebraMap_restrictClopen_le
    {W : Clopens (PrimeSpectrum A)} (hW : ConnectedComponents.mk ⁻¹' T ≤ W) :
    RingHom.ker (algebraMap A (RestrictClopen W)) ≤
      RingHom.ker (algebraMap A (Restriction T)) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  let ι : RestrictClopen W →ₐ[A] Restriction T :=
    (colimit.ι (Restriction.diag T) (Opposite.op ⟨W, hW⟩)).hom
  calc algebraMap A (Restriction T) a = ι (algebraMap A (RestrictClopen W) a) :=
        (ι.commutes a).symm
    _ = ι 0 := by rw [ha]
    _ = 0 := map_zero _

lemma range_algebraMap_specComap (h : IsClosed T) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Restriction T)) =
      ConnectedComponents.mk ⁻¹' T := by
  -- Set up filtered indexing category instances
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} := { }
  -- Step 1: range = zeroLocus(ker) by surjectivity
  have hsr : Set.range (comap (algebraMap A (Restriction T))) =
      zeroLocus ↑(RingHom.ker (algebraMap A (Restriction T))) :=
    _root_.range_comap_of_surjective (Restriction T) (algebraMap A (Restriction T))
      (algebraMap_surjective T)
  rw [hsr]
  apply Set.Subset.antisymm
  · -- ⊆ direction: p ∈ zeroLocus(ker(A -> colim)) implies p ∈ mk⁻¹'T
    intro p hp
    -- For each clopen W ⊇ mk⁻¹'T, show p ∈ W
    have hp_in_W : ∀ (W : Clopens (PrimeSpectrum A)),
        ConnectedComponents.mk ⁻¹' T ≤ W → p ∈ (W : Set (PrimeSpectrum A)) := by
      intro W hW
      have hker : RingHom.ker (algebraMap A (RestrictClopen W)) ≤
          RingHom.ker (algebraMap A (Restriction T)) :=
        ker_algebraMap_restrictClopen_le (T := T) hW
      have hzl : zeroLocus (RingHom.ker (algebraMap A (Restriction T)) : Set A) ⊆
          zeroLocus (RingHom.ker (algebraMap A (RestrictClopen W)) : Set A) := by
        apply zeroLocus_anti_mono
        intro x hx
        exact hker hx
      have := hzl hp
      have hrW : Set.range (comap (algebraMap A (RestrictClopen W))) =
          zeroLocus ↑(RingHom.ker (algebraMap A (RestrictClopen W))) :=
        _root_.range_comap_of_surjective (RestrictClopen W) (algebraMap A (RestrictClopen W))
          (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
            (isIdempotentElemEquivClopens.symm W).prop)
      rw [← hrW, restrictClopen_range_eq] at this
      exact this
    -- mk⁻¹'T is closed and a union of connected components
    have hclosed : IsClosed (ConnectedComponents.mk ⁻¹' T : Set (PrimeSpectrum A)) :=
      h.preimage ConnectedComponents.continuous_coe
    have hunion : ∃ I : Set (PrimeSpectrum A),
        ⋃ x ∈ I, connectedComponent x = ConnectedComponents.mk ⁻¹' T := by
      refine ⟨ConnectedComponents.mk ⁻¹' T, ?_⟩
      ext x; simp only [Set.mem_iUnion, Set.mem_preimage]; constructor
      · rintro ⟨y, hy, hxy⟩
        have : (x : ConnectedComponents (PrimeSpectrum A)) =
            (y : ConnectedComponents (PrimeSpectrum A)) :=
          ConnectedComponents.coe_eq_coe'.mpr hxy
        rw [this]; exact hy
      · intro hx; exact ⟨x, hx, mem_connectedComponent⟩
    -- By the theorem, mk⁻¹'T = ⋂ of clopens containing it
    obtain ⟨J, hJ⟩ := isClosed_and_iUnion_connectedComponent_eq_iff.mp ⟨hclosed, hunion⟩
    rw [← hJ]
    simp only [Set.iInter_coe_set, Set.mem_iInter, Subtype.forall]
    intro V hV hVJ
    have hTsubV : ConnectedComponents.mk ⁻¹' T ≤
        (⟨V, hV⟩ : {U : Set (PrimeSpectrum A) // IsClopen U}).val := by
      rw [← hJ]
      exact Set.iInter_subset_of_subset ⟨⟨V, hV⟩, hVJ⟩ le_rfl
    exact hp_in_W ⟨V, hV⟩ hTsubV
  · -- ⊇ direction: p ∈ mk⁻¹'T implies p ∈ zeroLocus(ker(A -> colim))
    intro p hp
    rw [mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, RingHom.mem_ker] at ha
    -- ha : algebraMap A (Restriction T) a = 0
    -- We express algebraMap via the cocone map at ⊤
    let top_idx : {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
      ⟨⊤, le_top⟩
    let ι_top := colimit.ι (Restriction.diag T) (Opposite.op top_idx)
    -- ι_top.hom (algebraMap A (RestrictClopen ⊤) a) = ι_top.hom 0 in the colimit
    have heq_in_colim : ι_top.hom (algebraMap A (RestrictClopen ⊤) a) =
        ι_top.hom (0 : RestrictClopen ⊤) :=
      (ι_top.hom.commutes a).trans (ha.trans (map_zero ι_top.hom).symm)
    -- Use that this is a cocone in CommAlgCat, which is concrete.
    -- By filtered colimit property, there exists k and morphisms such that
    -- the images become equal at stage k.
    -- We use the underlying Types colimit.
    have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
    have hc' := CategoryTheory.Limits.isColimitOfPreserves
      (CategoryTheory.forget (CommAlgCat A)) hc
    -- Transfer the equality to the Types colimit
    have heq_types : (CategoryTheory.forget (CommAlgCat A)).map ι_top
        (algebraMap A (RestrictClopen ⊤) a) =
      (CategoryTheory.forget (CommAlgCat A)).map ι_top (0 : RestrictClopen ⊤) := heq_in_colim
    -- Use Types.FilteredColimit.isColimit_eq_iff
    have hexists := (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)) hc').mp heq_types
    obtain ⟨k, f_top_k, g_top_k, hfg⟩ := hexists
    -- f_top_k, g_top_k : op top_idx ⟶ k in the indexing category
    -- hfg : (diag T ⋙ forget).map f_top_k (algebraMap ...) = (diag T ⋙ forget).map g_top_k 0
    -- The map (diag T ⋙ forget).map g_top_k is the underlying function of an algebra hom,
    -- so it sends 0 to 0.
    -- The transition maps are algebra homs, so they preserve 0 and commute with algebraMap
    let W := k.unop.val
    have hW : ConnectedComponents.mk ⁻¹' T ≤ W := k.unop.property
    -- Extract the algebra hom underlying f_top_k
    let φ : RestrictClopen ⊤ →ₐ[A] RestrictClopen W :=
      ((Restriction.diag T).map f_top_k).hom
    -- hfg says: φ (algebraMap A (RestrictClopen ⊤) a) = ψ 0 where ψ is from g_top_k
    -- Since ψ is an algebra hom, ψ 0 = 0
    have hg0 : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map g_top_k
        (0 : RestrictClopen ⊤) = (0 : RestrictClopen W) := by
      show ((Restriction.diag T).map g_top_k).hom (0 : RestrictClopen ⊤) = 0
      exact map_zero _
    have hf_alg : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map f_top_k
        (algebraMap A (RestrictClopen ⊤) a) = algebraMap A (RestrictClopen W) a := by
      show φ (algebraMap A (RestrictClopen ⊤) a) = _
      exact φ.commutes a
    -- Combine: algebraMap A (RestrictClopen W) a = 0
    have ha_zero : algebraMap A (RestrictClopen W) a = 0 := by
      rw [← hf_alg, hfg, hg0]
    -- So a ∈ ker(A -> RestrictClopen W)
    have ha_ker : a ∈ RingHom.ker (algebraMap A (RestrictClopen W)) :=
      RingHom.mem_ker.mpr ha_zero
    -- zeroLocus(ker(A -> RestrictClopen W)) = W for any W
    have hzl_eq : zeroLocus ↑(RingHom.ker (algebraMap A (RestrictClopen W))) =
        (W : Set (PrimeSpectrum A)) := by
      rw [← _root_.range_comap_of_surjective (RestrictClopen W)
        (algebraMap A (RestrictClopen W))
        (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
          (isIdempotentElemEquivClopens.symm W).prop),
        restrictClopen_range_eq]
    -- p ∈ mk⁻¹'T ⊆ W
    have hp_in_W : p ∈ (W : Set (PrimeSpectrum A)) := hW hp
    -- So p ∈ zeroLocus(ker(A -> RestrictClopen W)), meaning ker ≤ p.asIdeal
    have hker_le : RingHom.ker (algebraMap A (RestrictClopen W)) ≤ p.asIdeal := by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus]
      exact hzl_eq ▸ hp_in_W
    exact SetLike.mem_coe.mp (hker_le ha_ker)

lemma isClosedEmbedding_algebraMap_specComap (h : IsClosed T) :
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

instance commRing : CommRing (Pullback S f) := fast_instance%
  inferInstanceAs <| CommRing <| Restriction (Z S f)

instance algebra' : Algebra (S → A) (Pullback S f) := fast_instance%
  inferInstanceAs <| Algebra (S → A) <| Restriction (Z S f)

instance algebra : Algebra A (Pullback S f) := Algebra.compHom _ (Pi.ringHom fun _ : S ↦ RingHom.id A)

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
-- An ind-etale map from a w-strictly-local ring to a w-local ring (with matching closed points)
-- is bijective on stalks. This corresponds to the first step of
-- thm:ind-etale-plus-c-has-retraction-if-w-contractible in the blueprint.
-- The proof uses thm:ind-etale-strictly-henselian-localization-isom: if A is a strictly
-- Henselian local ring and A -> B is ind-etale, then A -> B_n is an isomorphism for any
-- maximal ideal n lying over the maximal ideal of A.
private lemma bijectiveOnStalks_of_indEtale_wStrictlyLocal [IsWStrictlyLocalRing R]
    {I : Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R))
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.IndEtale R S]
    [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S)) :
    (algebraMap R S).BijectiveOnStalks := by
  -- For each prime q of S, need to show localRingHom (q.comap f) q f rfl is bijective.
  -- The key case is when q is maximal (lies in V(IS) = closedPoints).
  -- Then q.comap f lies in V(I) = closedPoints(Spec R), so q.comap f is maximal.
  -- Since R is w-strictly-local, R_(comap q) is strictly Henselian.
  -- Since R → S is ind-étale, the stalk map R_(comap q) → S_q is ind-étale
  -- and hence an isomorphism (thm:ind-etale-strictly-henselian-localization-isom).
  -- For non-maximal primes q, BijectiveOnStalks follows by passing through the
  -- unique closed point that q specializes to (using w-local structure).
  sorry

-- If R is w-local with extremally disconnected pi_0(Spec R) and R -> S is faithfully flat,
-- bijective on stalks, with S w-local and matching closed points, then R -> S has a retraction.
-- This corresponds to thm:ff-identifies-local-rings-plus-c-has-retraction-if in the blueprint.
-- The proof uses:
-- (1) ExtremallyDisconnected projectivity to get a section of closed points map
-- (2) WContractification.Restriction to restrict S to a quotient S_T
-- (3) RingHom.IsWLocal.bijective_of_bijective (sorry in WLocal.lean) to conclude A -> S_T is iso
private lemma exists_retraction_of_bijectiveOnStalks [IsWLocalRing R]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R)))
    {I : Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R))
    {S : Type u} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S))
    (hbij : (algebraMap R S).BijectiveOnStalks) :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  -- The closed points V(IS) map to V(I) via Spec(algebraMap R S).
  -- V(I) ≅ π₀(Spec R) is extremally disconnected (compact T2 projective).
  -- So the surjection π₀(Spec S) → π₀(Spec R) has a section, giving a retraction
  -- of S via the Restriction construction and the isomorphism theorem.
  -- The full proof requires:
  -- 1. Show V(IS) → V(I) is surjective (from faithfully flat)
  -- 2. Get section using extremally disconnected projectivity
  -- 3. Use Restriction construction to get S → S_T
  -- 4. Show R ≅ S_T using RingHom.IsWLocal.bijective_of_bijective
  -- 5. Compose to get retraction
  -- All steps except (4) use formalized infrastructure.
  -- Step (4) depends on the sorry'd RingHom.IsWLocal.bijective_of_bijective.
  -- Blueprint: thm:ff-identifies-local-rings-plus-c-has-retraction-if. Blocked on RingHom.IsWLocal.bijective_of_bijective.
  sorry

theorem IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints [IsWContractibleRing R]
    {I :Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R)) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S)) :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  -- Step 1: R → S is bijective on stalks (identifies local rings).
  -- This uses that R is w-strictly local (stalks at maximal ideals are strictly Henselian)
  -- and S is ind-étale over R with matching closed points.
  have hbij : (algebraMap R S).BijectiveOnStalks :=
    bijectiveOnStalks_of_indEtale_wStrictlyLocal hI hS
  -- Step 2: Apply the retraction theorem for faithfully flat maps that identify local rings,
  -- using that π₀(Spec R) is extremally disconnected.
  exact exists_retraction_of_bijectiveOnStalks
    (IsWContractibleRing.extremallyDisconnected_connectedComponents) hI hS hbij

variable (R)

/-- If `R` is w-contractible, every faithfully flat, ind-étale map `R →+* S` has a retraction. -/
theorem IsWContractibleRing.exists_retraction [IsWContractibleRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  let I := vanishingIdeal (closedPoints (PrimeSpectrum R))
  have hI : zeroLocus I = closedPoints (PrimeSpectrum R) := by
    rw [zeroLocus_vanishingIdeal_eq_closure, IsClosed.closure_eq (IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints)]
  let S' := (I.map (algebraMap R S)).WLocalization
  have : Module.FaithfullyFlat R S' :=
    Ideal.WLocalization.faithfullyFlat_map_algebraMap hI
  have : Algebra.IndEtale R S' := Algebra.IndEtale.trans R S S'
  have : zeroLocus (I.map (algebraMap R S')) = closedPoints (PrimeSpectrum S') :=
    Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq hI (fun _ _ ↦ inferInstance)
  obtain ⟨g, hg⟩ := IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints hI this
  use g.comp (algebraMap S S')
  simp only [RingHom.comp_assoc]
  exact hg

/-!
### The w-contractification of a w-strictly-local ring

The main result `exists_isWContractibleRing_of_isWStrictlyLocal` constructs an ind-Zariski,
faithfully flat, w-contractible cover of any w-strictly-local ring. The proof follows the
blueprint (thm:ind-etale-w-contractible-cover-of-w-strictly-local, Stacks 0983):

1. By Gleason's theorem (`StoneCech.projective` + `CompactT2.Projective.extremallyDisconnected`),
   choose an extremally disconnected profinite space `T` (= `Ultrafilter (pi_0(Spec R))`)
   with a surjection `T -> pi_0(Spec R)`.
2. By the Pullback construction (`WContractification.Pullback`), taking the colimit over
   all discrete quotients of `T`, we get a ring `D` that is ind-Zariski and faithfully flat
   over `R`, with `pi_0(Spec D) = T` (hence extremally disconnected).
3. The local rings of `D` at maximal ideals are isomorphic to the corresponding local rings
   of `R` (by `Algebra.IndZariski.bijectiveOnStalks_algebraMap`), hence strictly Henselian.
4. Therefore `D` is w-contractible.

The construction of the "profinite Pullback" (colimit of `WContractification.Pullback S f`
over `S : DiscreteQuotient T`) and verification of its properties (`pi_0(Spec D) = T`,
cartesian diagram, w-local structure, faithfully flat) requires substantial infrastructure
that is stated as an admitted helper lemma below.
-/

-- Helper: the existence of a w-contractible cover, with the detailed construction admitted.
-- This corresponds to `thm:ind-etale-w-contractible-cover-of-w-strictly-local` in the blueprint
-- and `Stacks 0983` (second half).
-- The construction uses:
-- (a) Gleason's theorem: Ultrafilter(pi_0(Spec A)) is extremally disconnected
--     (Mathlib: StoneCech.projective + CompactT2.Projective.extremallyDisconnected)
-- (b) The profinite Pullback: colimit of WContractification.Pullback S f over
--     S : DiscreteQuotient (Ultrafilter (pi_0(Spec A))), cf. def:modify-pi0-profinite
-- (c) Properties of the profinite Pullback (Stacks 097D):
--     * ind-Zariski over A (colimit of ind-Zariski is ind-Zariski)
--     * pi_0(Spec D) = T (from the cartesian diagram, Stacks 096C)
--     * D is w-local (from WLocal/Pullback.lean, fully proved)
--     * D is faithfully flat (from Module.Flat.of_indZariski + surjectivity of Spec.comap)
-- (d) Stalks at maximal ideals are strictly Henselian:
--     by bijectiveOnStalks_algebraMap (fully proved in IndZariski.lean) +
--     transfer of strictly Henselian property through ring isomorphism
-- Individual pieces (a), (c-w-local part), (d-bijectiveOnStalks) are fully proved.
-- Missing infrastructure: (b) profinite Pullback definition + (c-remaining) its properties.
private lemma exists_wContractibleCover (A : Type u) [CommRing A] [IsWStrictlyLocalRing A] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.IndZariski A D ∧ Module.FaithfullyFlat A D ∧ IsWContractibleRing D := by
  -- Blueprint: thm:ind-etale-w-contractible-cover-of-w-strictly-local (Stacks 0983).
  sorry

/-- Any w-strictly-local ring has an ind-Zariski, faithfully flat cover that is w-contractible. -/
lemma exists_isWContractibleRing_of_isWStrictlyLocal
    [IsWStrictlyLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndZariski R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S :=
  exists_wContractibleCover R

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
