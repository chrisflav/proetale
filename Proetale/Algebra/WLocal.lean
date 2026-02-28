/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Topology.SpectralSpace.WLocal.Basic
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.RingTheory.Ideal.GoingDown

/-!
# w-local rings

In this file we define w-local rings. A ring is w-local if its prime spectrum is
a w-local topological space.
-/

/-- A ring is w-local if it has a w-local prime spectrum. -/
@[mk_iff]
class IsWLocalRing (R : Type*) [CommSemiring R] : Prop where
  wLocalSpace_primeSepectrum : WLocalSpace (PrimeSpectrum R)

instance (R : Type*) [CommSemiring R] [IsWLocalRing R] : WLocalSpace (PrimeSpectrum R) :=
  IsWLocalRing.wLocalSpace_primeSepectrum

variable {R S : Type*} [CommRing R] [CommRing S]

lemma IsWLocalRing.of_surjective {f : R →+* S} (hf : Function.Surjective f) [IsWLocalRing R] :
    IsWLocalRing S :=
  ⟨(PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hf).wLocalSpace⟩

/-- A ring homomorphism is w-local if the induced map on spectra is w-local. -/
def RingHom.IsWLocal {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

lemma RingHom.isWLocal_iff_isMaximal_of_isMaximal (f : R →+* S) :
    IsWLocal f ↔ ∀ (m : Ideal S) [m.IsMaximal], (m.comap f).IsMaximal := by
  rw [IsWLocal, isWLocalMap_iff]
  -- Blueprint: def:w-local-ring-map. w-local iff maximal ideals pull back to maximal ideals.
  refine ⟨fun ⟨_, h⟩ m hm ↦ ?_, ?_⟩
  · sorry
  · sorry

namespace RingHom.IsWLocal

-- Helper: in a w-local space, two closed points with the same connected component are equal.
-- This follows from closedPointsHomeomorph being injective.
private lemma closedPoints_eq_of_mk_eq [IsWLocalRing R]
    {c₁ c₂ : PrimeSpectrum R}
    (hc₁ : c₁ ∈ closedPoints (PrimeSpectrum R))
    (hc₂ : c₂ ∈ closedPoints (PrimeSpectrum R))
    (hmk : ConnectedComponents.mk c₁ = ConnectedComponents.mk c₂) : c₁ = c₂ := by
  have hinj : Function.Injective
      (ConnectedComponents.mk ∘ ((↑) : closedPoints (PrimeSpectrum R) → PrimeSpectrum R)) :=
    (WLocalSpace.isHomeomorph_connectedComponents_closedPoints _).bijective.1
  have h : (⟨c₁, hc₁⟩ : closedPoints (PrimeSpectrum R)) =
      (⟨c₂, hc₂⟩ : closedPoints (PrimeSpectrum R)) := by
    apply hinj
    show ConnectedComponents.mk c₁ = ConnectedComponents.mk c₂
    exact hmk
  exact congrArg Subtype.val h

-- Helper: specialization implies same connected component.
private lemma specializes_mk_eq' {X : Type*} [TopologicalSpace X] {a b : X} (hab : a ⤳ b) :
    ConnectedComponents.mk a = ConnectedComponents.mk b := by
  have hb_mem : b ∈ connectedComponent a :=
    isClosed_connectedComponent.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr mem_connectedComponent) hab.mem_closure
  exact ConnectedComponents.coe_eq_coe'.mpr
    (connectedComponent_eq hb_mem ▸ mem_connectedComponent)

/-- A w-local ring map between w-local rings that is bijective on stalks and
bijective on connected components is bijective. -/
lemma bijective_of_bijective [IsWLocalRing R] [IsWLocalRing S] {f : R →+* S} (hw : f.IsWLocal)
    (hs : f.BijectiveOnStalks)
    (hb : (PrimeSpectrum.continuous_comap f).connectedComponentsMap.Bijective) :
    Function.Bijective f := by
  -- Reduce to PrimeSpectrum.comap f bijective, then apply BijectiveOnStalks.bijective_of_bijective.
  apply hs.bijective_of_bijective
  constructor
  · -- Injectivity of Spec(f): if comap f q₁ = comap f q₂ then q₁ = q₂.
    intro q₁ q₂ heq
    -- Get the unique closed points that q₁ and q₂ specialize to.
    obtain ⟨n₁, hn₁_cl, h₁s⟩ := exists_isClosed_specializes q₁
    obtain ⟨n₂, hn₂_cl, h₂s⟩ := exists_isClosed_specializes q₂
    -- comap sends specializations to specializations
    have hcn₁ : PrimeSpectrum.comap f q₁ ⤳ PrimeSpectrum.comap f n₁ :=
      h₁s.map (PrimeSpectrum.continuous_comap f)
    have hcn₂ : PrimeSpectrum.comap f q₂ ⤳ PrimeSpectrum.comap f n₂ :=
      h₂s.map (PrimeSpectrum.continuous_comap f)
    -- n₁, n₂ are closed points of Spec S
    have hn₁_cp : n₁ ∈ closedPoints (PrimeSpectrum S) := mem_closedPoints_iff.mpr hn₁_cl
    have hn₂_cp : n₂ ∈ closedPoints (PrimeSpectrum S) := mem_closedPoints_iff.mpr hn₂_cl
    -- comap(n₁) and comap(n₂) are closed specializations of comap(q₁) = comap(q₂) in Spec R.
    -- Get closed specializations of comap(q₁) in Spec R.
    obtain ⟨m₁, hm₁_cl, hm₁s⟩ := exists_isClosed_specializes (PrimeSpectrum.comap f q₁)
    -- Both comap(n₁) (via hcn₁) and m₁ (via hm₁s) are closed specializations of comap(q₁).
    -- By w-local uniqueness in Spec R, they must be equal (if comap(n₁) is closed).
    -- But comap(n₁) might not be closed. However, it specializes to something closed.
    -- Let's get a closed point below comap(n₁):
    obtain ⟨m₁', hm₁'_cl, hm₁'s⟩ := exists_isClosed_specializes (PrimeSpectrum.comap f n₁)
    -- hcn₁.trans hm₁'s gives: comap f q₁ ⤳ m₁'
    -- hm₁s gives: comap f q₁ ⤳ m₁
    -- By w-local uniqueness: m₁ = m₁'
    have hm_eq₁ : m₁ = m₁' := WLocalSpace.eq_of_specializes hm₁_cl hm₁'_cl hm₁s
      (hcn₁.trans hm₁'s)
    -- Similarly for q₂: comap f q₂ ⤳ comap f n₂ ⤳ m₂'
    obtain ⟨m₂', hm₂'_cl, hm₂'s⟩ := exists_isClosed_specializes (PrimeSpectrum.comap f n₂)
    -- Since comap f q₁ = comap f q₂ (from heq):
    have heq' : PrimeSpectrum.comap f q₁ = PrimeSpectrum.comap f q₂ :=
      heq
    -- m₁ is a closed spec of comap f q₁ = comap f q₂, and
    -- m₂' is a closed spec of comap f q₂ (via hcn₂.trans hm₂'s)
    -- So m₁ = m₂' by w-local uniqueness.
    have hm_eq₂ : m₁ = m₂' :=
      WLocalSpace.eq_of_specializes hm₁_cl hm₂'_cl (heq' ▸ hm₁s) (hcn₂.trans hm₂'s)
    -- So comap f n₁ ⤳ m₁' = m₁ = m₂' ← comap f n₂
    -- i.e., both comap f n₁ and comap f n₂ specialize to the same closed point m₁.
    -- ConnectedComponents.mk (comap f n₁) = ConnectedComponents.mk m₁ = ConnectedComponents.mk (comap f n₂)
    -- The connectedComponentsMap sends mk(n_i) to mk(comap f n_i).
    -- So connectedComponentsMap(mk n₁) = mk(comap f n₁) which has mk = mk(m₁)
    -- and connectedComponentsMap(mk n₂) = mk(comap f n₂) which has mk = mk(m₁)
    -- So connectedComponentsMap(mk n₁) = connectedComponentsMap(mk n₂).
    -- By injectivity of connectedComponentsMap, mk n₁ = mk n₂.
    -- By closedPoints_eq_of_mk_eq, n₁ = n₂.
    have h_mk_n₁ : ConnectedComponents.mk (PrimeSpectrum.comap f n₁) =
        ConnectedComponents.mk m₁' := specializes_mk_eq' hm₁'s
    have h_mk_n₂ : ConnectedComponents.mk (PrimeSpectrum.comap f n₂) =
        ConnectedComponents.mk m₂' := specializes_mk_eq' hm₂'s
    have h_cmn_eq : (PrimeSpectrum.continuous_comap f).connectedComponentsMap
        (ConnectedComponents.mk n₁) =
        (PrimeSpectrum.continuous_comap f).connectedComponentsMap
        (ConnectedComponents.mk n₂) := by
      -- connectedComponentsMap(mk n_i) = mk(comap f n_i)
      show ConnectedComponents.mk (PrimeSpectrum.comap f n₁) =
        ConnectedComponents.mk (PrimeSpectrum.comap f n₂)
      rw [h_mk_n₁, h_mk_n₂, ← hm_eq₁, hm_eq₂]
    have hn_eq : n₁ = n₂ := by
      apply closedPoints_eq_of_mk_eq hn₁_cp hn₂_cp
      exact hb.1 h_cmn_eq
    -- Now n₁ = n₂ =: n. Both q₁ and q₂ specialize to n.
    -- The stalk map at n: localRingHom (n.asIdeal.comap f) n.asIdeal f rfl is bijective.
    -- q₁.asIdeal ≤ n.asIdeal (from specialization q₁ ⤳ n₁ = n)
    -- q₂.asIdeal ≤ n.asIdeal (from specialization q₂ ⤳ n₂ = n)
    -- The primes q₁, q₂ ⊆ n correspond to primes of S_n.
    -- Their images in R_{n.comap} are equal (since comap f q₁ = comap f q₂).
    -- By the bijectivity of the stalk map at n (on spectra), q₁ = q₂.
    subst hn_eq
    -- q₁.asIdeal ≤ n₁.asIdeal and q₂.asIdeal ≤ n₁.asIdeal
    have hq₁_le : q₁.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₁ n₁).mpr h₁s
    have hq₂_le : q₂.asIdeal ≤ n₁.asIdeal :=
      (PrimeSpectrum.le_iff_specializes q₂ n₁).mpr h₂s
    -- The stalk map φ : R_m → S_n₁ is bijective. Use this to show q₁ = q₂.
    -- Since φ is surjective, Spec(φ) is injective. We show q₁ and q₂ map to the
    -- same element under Spec(φ) (via localization), hence are equal.
    set m := n₁.asIdeal.comap f with hm_def
    have hstalk_bij : Function.Bijective (Localization.localRingHom m n₁.asIdeal f rfl) :=
      hs n₁.asIdeal
    -- Spec(φ) is injective since φ is surjective
    have hφ_inj : Function.Injective (PrimeSpectrum.comap
        (Localization.localRingHom m n₁.asIdeal f rfl)) :=
      PrimeSpectrum.comap_injective_of_surjective _ hstalk_bij.2
    -- The diagram commutes: localRingHom ∘ algebraMap R R_m = algebraMap S S_n ∘ f
    have hcomm : ∀ (q : PrimeSpectrum (Localization.AtPrime n₁.asIdeal)),
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))
          (PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) q) =
        PrimeSpectrum.comap f
          (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal)) q) := by
      intro q
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      congr 1; ext x; simp [Localization.localRingHom_to_map]
    -- Use the order iso to get q₁', q₂' and show their Spec(φ) images agree
    set oS := IsLocalization.AtPrime.primeSpectrumOrderIso
      (Localization.AtPrime n₁.asIdeal) n₁.asIdeal
    set q₁' := oS.symm ⟨q₁, hq₁_le⟩
    set q₂' := oS.symm ⟨q₂, hq₂_le⟩
    have hq₁'_val : (oS q₁').val = q₁ := congr_arg Subtype.val (oS.apply_symm_apply ⟨q₁, hq₁_le⟩)
    have hq₂'_val : (oS q₂').val = q₂ := congr_arg Subtype.val (oS.apply_symm_apply ⟨q₂, hq₂_le⟩)
    -- oS sends q' to ⟨comap(algebraMap S S_n)(q'), ...⟩, so:
    have hq₁'_comap : PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal)) q₁' = q₁ := hq₁'_val
    have hq₂'_comap : PrimeSpectrum.comap (algebraMap S (Localization.AtPrime n₁.asIdeal)) q₂' = q₂ := hq₂'_val
    -- Show Spec(φ)(q₁') = Spec(φ)(q₂') using diagram commutativity + heq
    have hφ_eq : PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) q₁' =
        PrimeSpectrum.comap (Localization.localRingHom m n₁.asIdeal f rfl) q₂' := by
      -- comap(algebraMap R R_m) is injective (via localization order iso)
      have h_comap_inj : Function.Injective
          (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime m))) :=
        Subtype.val_injective.comp
          (IsLocalization.AtPrime.primeSpectrumOrderIso
            (Localization.AtPrime m) m).injective
      apply h_comap_inj
      rw [hcomm q₁', hcomm q₂', hq₁'_comap, hq₂'_comap, heq]
    -- q₁' = q₂' by injectivity of Spec(φ)
    have hq'_eq : q₁' = q₂' := hφ_inj hφ_eq
    -- q₁ = q₂
    calc q₁ = PrimeSpectrum.comap (algebraMap S _) q₁' := hq₁'_comap.symm
      _ = PrimeSpectrum.comap (algebraMap S _) q₂' := congr_arg _ hq'_eq
      _ = q₂ := hq₂'_comap
  · -- Surjectivity of Spec(f): use w-local decomposition + stalk bijection.
    -- In a w-local space, Spec R = ∐_m Spec(R_m) (m running over closed points).
    -- Similarly Spec S = ∐_n Spec(S_n). The stalk bijection gives Spec(S_n) ≃ Spec(R_{comap f n}).
    -- The closed points bijection (from π₀ bijection) makes this a bijection of the whole space.
    -- However, this requires showing closed points of S map to closed points of R.
    -- Step 1: f is flat (from BijectiveOnStalks)
    letI := f.toAlgebra
    have hflat : Module.Flat R S := by
      apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
        (fun P ↦ Algebra.linearMap S _)
      intro P _
      letI := (Localization.localRingHom (Ideal.comap f P) P f rfl).toAlgebra
      have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
        .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
      have : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
        Module.Flat.of_linearEquiv
          (LinearEquiv.ofBijective (Algebra.linearMap _ _) (hs P)).symm
      exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)
    -- Step 2: Show every closed point of Spec R is in the image.
    -- For each maximal m of R, we need n with comap f n = m.
    -- By π₀ surjectivity, find q₀ with mk(comap f q₀) = mk(m).
    -- Let n₀ be the closed specialization of q₀. Show comap f n₀ = m by w-local uniqueness.
    have hclosed_in_image : closedPoints (PrimeSpectrum R) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
      intro pm hpm
      have hpm_max : IsClosed ({pm} : Set (PrimeSpectrum R)) := mem_closedPoints_iff.mp hpm
      -- By π₀ surjectivity, find d with connectedComponentsMap d = mk pm
      obtain ⟨d, hd⟩ := hb.2 (ConnectedComponents.mk pm)
      obtain ⟨q₀, rfl⟩ := ConnectedComponents.surjective_coe d
      -- mk(comap f q₀) = mk(pm)
      -- Let n₀ be the closed specialization of q₀ in Spec S
      obtain ⟨n₀, hn₀_cl, hq₀n₀⟩ := exists_isClosed_specializes q₀
      -- comap f n₀ is in the same connected component as pm
      -- (comap f q₀ ⤳ comap f n₀, so mk(comap f q₀) = mk(comap f n₀))
      -- and mk(comap f q₀) = mk(pm), so mk(comap f n₀) = mk(pm)
      have hmk_n₀ : ConnectedComponents.mk (PrimeSpectrum.comap f n₀) =
          ConnectedComponents.mk pm := by
        rw [← specializes_mk_eq' (hq₀n₀.map (PrimeSpectrum.continuous_comap f))]
        exact hd
      -- The closed specialization of comap f n₀ in Spec R equals pm
      -- (unique closed point in the connected component of pm)
      obtain ⟨m', hm'_cl, hn₀m'⟩ := exists_isClosed_specializes (PrimeSpectrum.comap f n₀)
      have hm'_eq : m' = pm := by
        have hmk_m' : ConnectedComponents.mk m' = ConnectedComponents.mk pm := by
          rw [← specializes_mk_eq' hn₀m']; exact hmk_n₀
        exact closedPoints_eq_of_mk_eq (mem_closedPoints_iff.mpr hm'_cl) hpm hmk_m'
      subst hm'_eq
      -- comap f n₀ ⤳ pm, i.e., (comap f n₀).asIdeal ≤ pm.asIdeal.
      -- We need: pm is in the image of comap f, i.e., ∃ n, comap f n = pm.
      -- This requires showing comap f n₀ = pm (since n₀ is the unique candidate
      -- in the connected component of pm by π₀ bijectivity).
      -- The stalk map at n₀ gives Spec(S_{n₀}) ≅ Spec(R_{comap f n₀}).
      -- If comap f n₀ < pm, then Spec(R_{comap f n₀}) ⊊ Spec(R_{pm}),
      -- and by π₀ bijection no other component covers the gap.
      -- To show comap f n₀ = pm, we note n₀ is maximal and the stalk map
      -- is bijective. This should yield comap f n₀ maximal via the w-local map
      -- condition (closed points map to closed points).
      -- Blueprint: thm:isom-of-identifies-local-rings-bijective (Stacks 097E).
      sorry
    -- Step 3: Apply going-down surjectivity.
    exact Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
      hclosed_in_image

end RingHom.IsWLocal

/-- A w-strictly-local ring is a w-local ring whose stalks at maximal ideals are strictly Henselian
local rings. -/
class IsWStrictlyLocalRing (R : Type*) [CommRing R] : Prop extends IsWLocalRing R where
  isStrictlyHenselianLocalRing_localization (m : Ideal R) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m)
