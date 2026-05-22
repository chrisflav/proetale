/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Mathlib.RingTheory.Ideal.GoingDown
import Proetale.Mathlib.RingTheory.Spectrum.Prime.Topology
import Proetale.Topology.SpectralSpace.WLocal.Basic
import Proetale.Topology.SpectralSpace.WLocal.ConnectedComponents
import Proetale.Algebra.StalkIso

/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

attribute [instance] IsWLocalRing.wLocalSpace_primeSepectrum

variable {R S : Type*} [CommRing R] [CommRing S]

lemma IsWLocalRing.of_surjective {f : R →+* S} (hf : Function.Surjective f) [IsWLocalRing R] :
    IsWLocalRing S :=
  ⟨(PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hf).wLocalSpace⟩

/-- A ring homomorphism is w-local if the induced map on spectra is w-local. -/
def RingHom.IsWLocal {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

lemma RingHom.isWLocal_iff_isMaximal_of_isMaximal (f : R →+* S) :
    IsWLocal f ↔ ∀ (m : Ideal S) [m.IsMaximal], (m.comap f).IsMaximal := by
  rw [IsWLocal, isWLocalMap_iff, and_iff_right (PrimeSpectrum.isSpectralMap_comap f)]
  simp_rw [Set.subset_def, Set.mem_preimage, mem_closedPoints_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.comap_asIdeal]
  exact ⟨fun h m hm ↦ h ⟨m, hm.isPrime⟩ hm, fun h x hx ↦ @h x.asIdeal hx⟩

namespace RingHom.IsWLocal

/-- In any topological space, a specialization induces equality of connected components. -/
private lemma specializes_connectedComponents_mk_eq {X : Type*} [TopologicalSpace X] {a b : X}
    (hab : a ⤳ b) : ConnectedComponents.mk a = ConnectedComponents.mk b := by
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  have hb : b ∈ connectedComponent a :=
    isClosed_connectedComponent.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr mem_connectedComponent) hab.mem_closure
  rw [← connectedComponent_eq hb]
  exact mem_connectedComponent

/-- Two closed points in a w-local prime spectrum lying in the same connected component
are equal. -/
private lemma closedPoints_eq_of_mk_eq [IsWLocalRing R] {c₁ c₂ : PrimeSpectrum R}
    (hc₁ : c₁ ∈ closedPoints (PrimeSpectrum R))
    (hc₂ : c₂ ∈ closedPoints (PrimeSpectrum R))
    (hmk : ConnectedComponents.mk c₁ = ConnectedComponents.mk c₂) : c₁ = c₂ :=
  congrArg Subtype.val <|
    (WLocalSpace.isHomeomorph_connectedComponents_closedPoints _).bijective.1
      (a₁ := ⟨c₁, hc₁⟩) (a₂ := ⟨c₂, hc₂⟩) hmk

/-- A w-local ring map between w-local rings that is bijective on stalks and
bijective on connected components is bijective. -/
lemma bijective_of_bijective [IsWLocalRing R] [IsWLocalRing S] {f : R →+* S} (hw : f.IsWLocal)
    (hs : f.BijectiveOnStalks)
    (hb : (PrimeSpectrum.continuous_comap f).connectedComponentsMap.Bijective) :
    Function.Bijective f := by
  -- Reduce to bijectivity of `PrimeSpectrum.comap f` and then apply `BijectiveOnStalks`.
  refine hs.bijective_of_bijective ⟨?_, ?_⟩
  -- Injectivity of `PrimeSpectrum.comap f`.
  · intro q₁ q₂ heq
    -- Each `qᵢ` specializes to a unique closed point `nᵢ` in `Spec S`.
    obtain ⟨n₁, hn₁_cl, hq₁n₁⟩ := exists_isClosed_specializes q₁
    obtain ⟨n₂, hn₂_cl, hq₂n₂⟩ := exists_isClosed_specializes q₂
    have hn₁_cp := mem_closedPoints_iff.mpr hn₁_cl
    have hn₂_cp := mem_closedPoints_iff.mpr hn₂_cl
    -- `comap f` sends closed points of `Spec S` to closed points of `Spec R` (`hw`).
    have hcomap_n₁_cl : IsClosed ({PrimeSpectrum.comap f n₁} : Set (PrimeSpectrum R)) :=
      mem_closedPoints_iff.mp (hw.closedPoints_subset_preimage_closedPoints hn₁_cp)
    have hcomap_n₂_cl : IsClosed ({PrimeSpectrum.comap f n₂} : Set (PrimeSpectrum R)) :=
      mem_closedPoints_iff.mp (hw.closedPoints_subset_preimage_closedPoints hn₂_cp)
    -- Both `comap f n₁` and `comap f n₂` are closed specializations of `comap f q₁`.
    have h1 : PrimeSpectrum.comap f q₁ ⤳ PrimeSpectrum.comap f n₁ :=
      hq₁n₁.map (PrimeSpectrum.continuous_comap f)
    have h2 : PrimeSpectrum.comap f q₁ ⤳ PrimeSpectrum.comap f n₂ :=
      heq ▸ hq₂n₂.map (PrimeSpectrum.continuous_comap f)
    -- By w-local uniqueness in `Spec R`, they are equal.
    have hcomap_n_eq : PrimeSpectrum.comap f n₁ = PrimeSpectrum.comap f n₂ :=
      WLocalSpace.eq_of_specializes hcomap_n₁_cl hcomap_n₂_cl h1 h2
    -- Hence `n₁` and `n₂` lie in the same connected component of `Spec S`, and as
    -- closed points in a w-local space they coincide.
    obtain rfl : n₁ = n₂ :=
      closedPoints_eq_of_mk_eq hn₁_cp hn₂_cp <| hb.1 <| by
        simp [Continuous.connectedComponentsMap_mk, hcomap_n_eq]
    -- Now `q₁, q₂ ≤ n₁` correspond to primes of `S` localised at `n₁`, and the stalk
    -- map at `n₁` is bijective; transport injectivity from `Spec R` to the stalk side.
    have hq₁_le : q₁.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₁ n₁).mpr hq₁n₁
    have hq₂_le : q₂.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₂ n₁).mpr hq₂n₂
    set m := n₁.asIdeal.comap f
    have hφ_inj : Function.Injective
        (PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl)) :=
      PrimeSpectrum.comap_injective_of_surjective _ (hs n₁.asIdeal).2
    -- Commutativity of the four-square: `algR_R_m ∘ Spec(localRingHom) = comap f ∘ algS_S_n`.
    have hcomm : ∀ (q : PrimeSpectrum (Localization.AtPrime n₁.asIdeal)),
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))
          (PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) q) =
        PrimeSpectrum.comap f
          (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal)) q) := by
      intro q
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1
      ext x
      simp [Localization.localRingHom_to_map]
    -- Lift `q₁, q₂` to primes of `Localization.AtPrime n₁.asIdeal` via the order iso.
    set oS := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime n₁.asIdeal) n₁.asIdeal
    have hq₁'_val :
        PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal))
          (oS.symm ⟨q₁, hq₁_le⟩) = q₁ :=
      congr_arg Subtype.val (oS.apply_symm_apply ⟨q₁, hq₁_le⟩)
    have hq₂'_val :
        PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal))
          (oS.symm ⟨q₂, hq₂_le⟩) = q₂ :=
      congr_arg Subtype.val (oS.apply_symm_apply ⟨q₂, hq₂_le⟩)
    have hφ_eq :
        PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) (oS.symm ⟨q₁, hq₁_le⟩) =
        PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl)
          (oS.symm ⟨q₂, hq₂_le⟩) := by
      have hcomap_inj : Function.Injective
          (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) :=
        Subtype.val_injective.comp
          (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime m) m).injective
      exact hcomap_inj <| by rw [hcomm, hcomm, hq₁'_val, hq₂'_val, heq]
    rw [← hq₁'_val, hφ_inj hφ_eq, hq₂'_val]
  -- Surjectivity: via going-down, it suffices to hit every closed point of `Spec R`.
  · letI : Algebra R S := f.toAlgebra
    have : Module.Flat R S :=
      RingHom.flat_of_flat_localRingHom fun P _ ↦ .of_bijective (hs.localRingHom P)
    apply Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    intro pm hpm
    -- Lift `pm` through the connected-component bijection to a closed point `n₀` of `Spec S`.
    obtain ⟨d, hd⟩ := hb.2 (.mk pm)
    obtain ⟨q₀, rfl⟩ := ConnectedComponents.surjective_coe d
    obtain ⟨n₀, hn₀_cl, hq₀n₀⟩ := exists_isClosed_specializes q₀
    have hn₀_cp : n₀ ∈ closedPoints (PrimeSpectrum S) := mem_closedPoints_iff.mpr hn₀_cl
    have hmk_eq : ConnectedComponents.mk (PrimeSpectrum.comap f n₀) =
        ConnectedComponents.mk pm := by
      rwa [← specializes_connectedComponents_mk_eq
        (hq₀n₀.map (PrimeSpectrum.continuous_comap f))]
    exact ⟨n₀, closedPoints_eq_of_mk_eq
      (hw.closedPoints_subset_preimage_closedPoints hn₀_cp) hpm hmk_eq⟩

end RingHom.IsWLocal

/-- A w-strictly-local ring is a w-local ring whose stalks at maximal ideals are strictly Henselian
local rings. -/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where
  isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m)
