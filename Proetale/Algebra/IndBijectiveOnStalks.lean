/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.StalkIso
import Proetale.Algebra.IndZariski
import Proetale.Algebra.WLocal
import Proetale.Algebra.IdentifiesLocalRings
import Proetale.Algebra.WContractible

/-!
# Ring maps that identify local rings are ind-Zariski locally ind-Zariski

In this file we prove Stacks 097F: a w-local ring map between w-local rings that
identifies local rings is ind-Zariski.

The proof follows the Stacks project: let `f : R → S` be such a map and let
`T = π₀(Spec S)`. The profinite space `T` maps to `π₀(Spec R)`, and the ind-Zariski
`R`-algebra `A' = PullbackProfinite R T i` (Stacks 097D) realizes the topological
pullback `Spec R ×_{π₀(Spec R)} T`. By the universal property there is a continuous map
`Spec S → Spec A'` over `Spec R`, which by fully faithfulness (Stacks 096L,
`Algebra.BijectiveOnStalks.algHom_of_continuousMap`) comes from an `R`-algebra map
`g : A' → S`. The map `g` is a w-local map of w-local rings which identifies local
rings and is bijective on connected components, hence is bijective (Stacks 097E,
`RingHom.IsWLocal.bijective_of_bijective`). Thus `S ≅ A'` is ind-Zariski over `R`.
-/

universe u

open CategoryTheory TopCat PrimeSpectrum WContractification

variable {R S : Type u} [CommRing R] [CommRing S]

variable (R S) in
/-- **Stacks 097F**, algebra version: a w-local map of w-local rings that identifies
local rings is ind-Zariski. -/
@[stacks 097F]
lemma Algebra.BijectiveOnStalks.indZariski_of_isWLocal [Algebra R S] [IsWLocalRing R]
    [IsWLocalRing S] [Algebra.BijectiveOnStalks R S]
    (hw : (algebraMap R S).IsWLocal) :
    Algebra.IndZariski R S := by
  -- The profinite space of connected components of `Spec S` with its map to `π₀(Spec R)`.
  set T := _root_.ConnectedComponents (PrimeSpectrum S) with hT
  let i : C(T, _root_.ConnectedComponents (PrimeSpectrum R)) :=
    ⟨(PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap,
      (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_continuous⟩
  -- The ind-Zariski `R`-algebra realizing `Spec R ×_{π₀(Spec R)} T`.
  set A' := PullbackProfinite R T i with hA'
  have pb := PullbackProfinite.isPullback R T i
  -- The canonical map `Spec S → Spec A'` over `Spec R` via the pullback property.
  let a : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of T :=
    ofHom ⟨_root_.ConnectedComponents.mk, _root_.ConnectedComponents.continuous_coe⟩
  let b : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum R) :=
    ofHom ⟨PrimeSpectrum.comap (algebraMap R S), PrimeSpectrum.continuous_comap _⟩
  have w : a ≫ ofHom i =
      b ≫ ofHom ⟨_root_.ConnectedComponents.mk, _root_.ConnectedComponents.continuous_coe⟩ := by
    ext y
    exact (PrimeSpectrum.continuous_comap (algebraMap R S)).connectedComponentsMap_mk y
  let φ : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum A') := pb.lift a b w
  have hφT : ∀ y, PullbackProfinite.projT R T i (φ y) = _root_.ConnectedComponents.mk y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_fst a b w) y
  have hφR : ∀ y, PullbackProfinite.projSpec R T i (φ y) =
      PrimeSpectrum.comap (algebraMap R S) y := fun y ↦
    ConcreteCategory.congr_hom (pb.lift_snd a b w) y
  -- The continuous map `Spec S → Spec A'` over `Spec R` as a `HomOver`.
  haveI : Algebra.BijectiveOnStalks R A' :=
    RingHom.bijectiveOnStalks_algebraMap.mp <|
      RingHom.IndZariski.bijectiveOnStalks
        ((RingHom.IndZariski.algebraMap_iff (R := R) (S := A')).mpr inferInstance)
  let Φ : Algebra.BijectiveOnStalks.HomOver R A' S :=
    { toContinuousMap := φ.hom
      comp_comap_algebraMap := fun p ↦ hφR p }
  -- By fully faithfulness (Stacks 096L), `Φ` comes from an `R`-algebra map `g : A' → S`.
  let g : A' →ₐ[R] S := Algebra.BijectiveOnStalks.algHom_of_continuousMap R A' S Φ
  have hg : ∀ p, PrimeSpectrum.comap g.toRingHom p = φ p := fun p ↦
    DFunLike.congr_fun
      (Algebra.BijectiveOnStalks.continuousMap_of_algHom_algHom_of_continuousMap R A' S Φ) p
  -- `Spec A'` is w-local.
  haveI : IsWLocalRing A' := ⟨ConnectedComponents.wlocalSpace_of_isPullback pb⟩
  -- `g` is a w-local map.
  have hgw : RingHom.IsWLocal g.toRingHom := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap _, fun n hn ↦ ?_⟩
    rw [Set.mem_preimage, hg n,
      ← ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb,
      Set.mem_preimage, hφR n]
    exact hw.closedPoints_subset_preimage_closedPoints hn
  -- `g` identifies local rings.
  have hgs : g.toRingHom.BijectiveOnStalks := by
    have h1 : (algebraMap R A').BijectiveOnStalks :=
      RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    have h2 : (g.toRingHom.comp (algebraMap R A')).BijectiveOnStalks := by
      have heq : g.toRingHom.comp (algebraMap R A') = algebraMap R S :=
        RingHom.ext fun x ↦ g.commutes x
      rw [heq]
      exact RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    exact RingHom.BijectiveOnStalks.of_comp h1 h2
  -- `g` is bijective on connected components.
  have hb : (PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap.Bijective := by
    have hL := ConnectedComponents.lift_bijective_of_isPullback pb
    set L := Continuous.connectedComponentsLift (PullbackProfinite.projT R T i).2 with hLdef
    have hkey : ∀ c, L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c)
        = c := by
      intro c
      obtain ⟨y, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
      rw [Continuous.connectedComponentsMap_mk, hg y]
      exact hφT y
    constructor
    · intro c₁ c₂ h12
      calc c₁ = L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c₁) :=
            (hkey c₁).symm
        _ = L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c₂) := by
            rw [h12]
        _ = c₂ := hkey c₂
    · intro d
      exact ⟨L d, hL.injective (hkey (L d))⟩
  -- Hence `g` is bijective, and `S ≅ A'` is ind-Zariski over `R`.
  have hbij : Function.Bijective g.toRingHom :=
    RingHom.IsWLocal.bijective_of_bijective hgw hgs hb
  exact Algebra.IndZariski.of_equiv R A' S (AlgEquiv.ofBijective g hbij)

/-- **Stacks 097F**: a w-local ring map between w-local rings that is bijective on stalks
is ind-Zariski. -/
@[stacks 097F]
lemma RingHom.BijectiveOnStalks.indZariski_of_isWLocal {f : R →+* S} [IsWLocalRing R]
    [IsWLocalRing S] (hf : f.IsWLocal) (hf' : f.BijectiveOnStalks) :
    f.IndZariski := by
  algebraize [f]
  haveI : Algebra.BijectiveOnStalks R S := hf'.toAlgebra
  rw [← RingHom.algebraMap_toAlgebra f, RingHom.IndZariski.algebraMap_iff]
  exact Algebra.BijectiveOnStalks.indZariski_of_isWLocal R S
    (by rwa [RingHom.algebraMap_toAlgebra])

variable (R S) in
lemma Algebra.BijectiveOnStalks.exists_indZariski [Algebra R S] [Algebra.BijectiveOnStalks R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      IndZariski S T ∧ Module.FaithfullyFlat S T ∧ IndZariski R T :=
  sorry

/-- If `R → S` is bijective on stalks, ind-Zariski locally it is ind-Zariski. -/
lemma RingHom.BijectiveOnStalks.exists_indZariski {f : R →+* S} (hf : f.BijectiveOnStalks) :
    ∃ (T : Type u) (_ : CommRing T) (g : S →+* T),
      g.IndZariski ∧ g.FaithfullyFlat ∧ (g.comp f).IndZariski := by
  algebraize [f]
  obtain ⟨T, _, _, _, _, h₁, h₂, h₃⟩ := Algebra.BijectiveOnStalks.exists_indZariski R S
  refine ⟨T, inferInstance, algebraMap S T, ?_, ?_, ?_⟩
  · rwa [IndZariski.algebraMap_iff]
  · rwa [faithfullyFlat_algebraMap_iff]
  · rwa [← RingHom.algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq, IndZariski.algebraMap_iff]
