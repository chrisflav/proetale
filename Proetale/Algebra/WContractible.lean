/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Algebra.WLocalization.Ideal
import Proetale.Topology.SpectralSpace.WLocal.Pullback
import Proetale.Algebra.WStrictLocalization
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndZariski
import Proetale.Algebra.PullbackProfinite
import Mathlib.Topology.Category.Stonean.Basic
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
  inferInstanceAs <| IsLocalization.Away (isIdempotentElemEquivClopens.symm W).val <|
    Localization.Away (isIdempotentElemEquivClopens.symm W).val

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
  simp only [CategoryTheory.Functor.mapCocone_ι_app, colimit.cocone_ι] at hy
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

section PullbackProfinite

/-!
## Modifying the connected components along a profinite map (Stacks 097D)

Given a ring `R` and a continuous map `i : T → π₀(Spec R)` from a profinite space, we
construct an ind-Zariski `R`-algebra `PullbackProfinite R T i` realizing the cartesian
square
```
Spec D --→ T
  |        |
  ↓        ↓
Spec R --→ π₀(Spec R)
```
of topological spaces. Following the identification
`Spec (LocallyConstant T R) ≃ₜ T × Spec R` (see `Proetale.Algebra.PullbackProfinite`),
the ring is obtained as the `Restriction` of `LocallyConstant T R` to the closed subset
of connected components lying on the graph of `i`. This computes the Stacks 097D
colimit `A^f_{π₀} = colim_q A^f_q` in a single step.
-/

open LocallyConstant TopCat

variable (R : Type u) [CommRing R]
variable (T : Type u) [TopologicalSpace T] [CompactSpace T] [T2Space T]
  [TotallyDisconnectedSpace T]
variable (i : C(T, ConnectedComponents (PrimeSpectrum R)))

namespace PullbackProfinite

/-- The graph of `i` inside `T × Spec R`. -/
def graph : Set (T × PrimeSpectrum R) :=
  {q | i q.1 = ConnectedComponents.mk q.2}

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
lemma isClosed_graph : IsClosed (graph R T i) :=
  isClosed_eq (i.continuous.comp continuous_fst)
    (ConnectedComponents.continuous_coe.comp continuous_snd)

/-- The set of primes of `LocallyConstant T R` lying on the graph of `i`. -/
def specGraph : Set (PrimeSpectrum (LocallyConstant T R)) :=
  toPrimeSpectrum '' graph R T i

lemma isClosed_specGraph : IsClosed (specGraph R T i) :=
  (homeomorphPrimeSpectrum (T := T) (R := R)).isClosedMap _ (isClosed_graph R T i)

/-- `specGraph` is a union of connected components: connected components of
`T × Spec R` are of the form `{t} × C` and both `i ∘ fst` and `π₀ ∘ snd` are constant
on them. -/
lemma connectedComponent_subset_specGraph {P : PrimeSpectrum (LocallyConstant T R)}
    (hP : P ∈ specGraph R T i) :
    connectedComponent P ⊆ specGraph R T i := by
  obtain ⟨⟨t, x⟩, hq, rfl⟩ := hP
  intro P' hP'
  set e := homeomorphPrimeSpectrum (T := T) (R := R) with he
  have h1 : e.symm P' ∈ connectedComponent (e.symm (toPrimeSpectrum (t, x))) :=
    e.symm.continuous.image_connectedComponent_subset _ ⟨P', hP', rfl⟩
  have h2 : e.symm (toPrimeSpectrum (t, x)) = (t, x) := e.symm_apply_apply (t, x)
  rw [h2, connectedComponent.prod, connectedComponent_eq_singleton] at h1
  have hfst : (e.symm P').1 = t := Set.mem_singleton_iff.mp h1.1
  have hmk : ConnectedComponents.mk (e.symm P').2 = ConnectedComponents.mk x :=
    ConnectedComponents.coe_eq_coe'.mpr h1.2
  refine ⟨e.symm P', ?_, e.apply_symm_apply P'⟩
  change i (e.symm P').1 = ConnectedComponents.mk (e.symm P').2
  rw [hfst, hmk]
  exact hq

/-- The closed subset of `π₀(Spec (LocallyConstant T R))` of components lying on the
graph of `i`. -/
def Z : Set (ConnectedComponents (PrimeSpectrum (LocallyConstant T R))) :=
  ConnectedComponents.mk '' specGraph R T i

lemma preimage_mk_Z : ConnectedComponents.mk ⁻¹' Z R T i = specGraph R T i := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro P ⟨P', hP', hmk⟩
  exact connectedComponent_subset_specGraph R T i hP'
    (ConnectedComponents.coe_eq_coe'.mp hmk.symm)

lemma isClosed_Z : IsClosed (Z R T i) :=
  ConnectedComponents.continuous_coe.isClosedMap _ (isClosed_specGraph R T i)

end PullbackProfinite

/-- The modification of the connected components of `Spec R` along the continuous map
`i : T → π₀(Spec R)` from a profinite space: an ind-Zariski `R`-algebra `D` with
`Spec D = Spec R ×_{π₀(Spec R)} T`, see `PullbackProfinite.isPullback`. This is the
ring `A^f_{π₀}` of Stacks 097D, realized as the restriction of `LocallyConstant T R`
to the components on the graph of `i`. -/
def PullbackProfinite : Type u :=
  Restriction (PullbackProfinite.Z R T i)

namespace PullbackProfinite

instance commRing : CommRing (PullbackProfinite R T i) :=
  inferInstanceAs <| CommRing <| Restriction _

instance algebra' : Algebra (LocallyConstant T R) (PullbackProfinite R T i) :=
  inferInstanceAs <| Algebra _ <| Restriction _

instance algebra : Algebra R (PullbackProfinite R T i) :=
  Algebra.compHom _ (algebraMap R (LocallyConstant T R))

instance isScalarTower :
    IsScalarTower R (LocallyConstant T R) (PullbackProfinite R T i) :=
  .of_algebraMap_eq' rfl

instance indZariski' :
    Algebra.IndZariski (LocallyConstant T R) (PullbackProfinite R T i) :=
  inferInstanceAs <| Algebra.IndZariski _ <| Restriction _

instance indZariski : Algebra.IndZariski R (PullbackProfinite R T i) :=
  Algebra.IndZariski.trans R (LocallyConstant T R) (PullbackProfinite R T i)

lemma range_comap_algebraMap :
    Set.range (PrimeSpectrum.comap
      (algebraMap (LocallyConstant T R) (PullbackProfinite R T i))) = specGraph R T i :=
  (Restriction.range_algebraMap_specComap (isClosed_Z R T i)).trans
    (preimage_mk_Z R T i)

/-- The projection `Spec D → T`. -/
noncomputable def projT : C(PrimeSpectrum (PullbackProfinite R T i), T) :=
  ⟨fun y => ((homeomorphPrimeSpectrum (T := T) (R := R)).symm
      (PrimeSpectrum.comap (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y)).1,
    continuous_fst.comp ((homeomorphPrimeSpectrum (T := T) (R := R)).symm.continuous.comp
      (PrimeSpectrum.continuous_comap _))⟩

/-- The structure map `Spec D → Spec R`. -/
def projSpec : C(PrimeSpectrum (PullbackProfinite R T i), PrimeSpectrum R) :=
  ⟨PrimeSpectrum.comap (algebraMap R (PullbackProfinite R T i)),
    PrimeSpectrum.continuous_comap _⟩

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
lemma comap_algebraMap_comap (y : PrimeSpectrum (PullbackProfinite R T i)) :
    PrimeSpectrum.comap (algebraMap R (LocallyConstant T R))
      (PrimeSpectrum.comap
        (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y) =
      PrimeSpectrum.comap (algebraMap R (PullbackProfinite R T i)) y := by
  rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq]

/-- `Spec D` is homeomorphic to the fiber product of `i : T → π₀(Spec R)` and
`Spec R → π₀(Spec R)`, realized as a subspace of `T × Spec R`. -/
noncomputable def fiberHomeo :
    PrimeSpectrum (PullbackProfinite R T i) ≃ₜ
      {q : T × PrimeSpectrum R // i q.1 = ConnectedComponents.mk q.2} :=
  (((Restriction.isClosedEmbedding_algebraMap_specComap
      (T := Z R T i)).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_comap_algebraMap R T i))).trans
    ((homeomorphPrimeSpectrum (T := T) (R := R)).image (graph R T i)).symm)

lemma coe_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y : T × PrimeSpectrum R) =
      (homeomorphPrimeSpectrum (T := T) (R := R)).symm
        (PrimeSpectrum.comap
          (algebraMap (LocallyConstant T R) (PullbackProfinite R T i)) y) :=
  rfl

lemma fst_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y).1.1 = projT R T i y := by
  rw [coe_fiberHomeo]
  rfl

lemma snd_fiberHomeo (y : PrimeSpectrum (PullbackProfinite R T i)) :
    (fiberHomeo R T i y).1.2 = projSpec R T i y := by
  rw [coe_fiberHomeo, homeomorphPrimeSpectrum_symm_snd, comap_algebraMap_comap]
  rfl

/-- The square
```
Spec D --→ T
  |        |
  ↓        ↓
Spec R --→ π₀(Spec R)
```
is cartesian in the category of topological spaces. This is
`thm:modify-pi0-profinite-properties` (Stacks 097D) in the blueprint. -/
theorem isPullback :
    CategoryTheory.IsPullback (ofHom (projT R T i)) (ofHom (projSpec R T i)) (ofHom i)
      (ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) := by
  have hcomm : ofHom (projT R T i) ≫ ofHom i = ofHom (projSpec R T i) ≫
      ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    ext y
    change i (projT R T i y) = ConnectedComponents.mk (projSpec R T i y)
    rw [← fst_fiberHomeo, ← snd_fiberHomeo]
    exact (fiberHomeo R T i y).2
  refine CategoryTheory.IsPullback.of_iso_pullback ⟨hcomm⟩
    (isoOfHomeo (fiberHomeo R T i) ≪≫ (pullbackIsoProdSubtype _ _).symm) ?_ ?_
  · rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, CategoryTheory.Iso.symm_hom,
      pullbackIsoProdSubtype_inv_fst]
    ext y
    exact fst_fiberHomeo R T i y
  · rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, CategoryTheory.Iso.symm_hom,
      pullbackIsoProdSubtype_inv_snd]
    refine TopCat.hom_ext (ContinuousMap.ext fun y => ?_)
    exact snd_fiberHomeo R T i y

lemma projSpec_surjective (hi : Function.Surjective i) :
    Function.Surjective (projSpec R T i) := by
  intro x
  obtain ⟨t, ht⟩ := hi (ConnectedComponents.mk x)
  refine ⟨(fiberHomeo R T i).symm ⟨(t, x), ht⟩, ?_⟩
  have h := snd_fiberHomeo R T i ((fiberHomeo R T i).symm ⟨(t, x), ht⟩)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

lemma faithfullyFlat (hi : Function.Surjective i) :
    Module.FaithfullyFlat R (PullbackProfinite R T i) := by
  rw [← RingHom.faithfullyFlat_algebraMap_iff,
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, projSpec_surjective R T i hi⟩

end PullbackProfinite

end PullbackProfinite

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

/-- Any w-strictly-local ring has an ind-Zariski, faithfully flat cover that is
w-contractible.

Following the blueprint (`thm:ind-etale-w-contractible-cover-of-w-strictly-local`,
Stacks 0983): choose an extremally disconnected cover `T → π₀(Spec R)` (Gleason), let
`D` be the ind-Zariski `R`-algebra realizing `Spec D = Spec R ×_{π₀(Spec R)} T` from
`WContractification.PullbackProfinite` (Stacks 097D). Then `Spec D` is w-local with
closed points lying over closed points of `Spec R` (Stacks 096C), so the local rings
of `D` at maximal ideals are isomorphic to those of `R` (ind-Zariski maps identify
local rings) and hence strictly henselian; finally `π₀(Spec D) ≃ T` is extremally
disconnected. -/
lemma exists_isWContractibleRing_of_isWStrictlyLocal
    [IsWStrictlyLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndZariski R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S := by
  classical
  -- The extremally disconnected cover of `π₀(Spec R)`, by Gleason's theorem.
  let X₀ : CompHaus := CompHaus.of (ConnectedComponents (PrimeSpectrum R))
  let pres := CompHaus.projectivePresentation X₀
  haveI : CategoryTheory.Projective pres.p := pres.projective
  haveI hED : ExtremallyDisconnected pres.p := inferInstance
  let T : Type u := pres.p
  let i : C(T, ConnectedComponents (PrimeSpectrum R)) :=
    CategoryTheory.ConcreteCategory.hom pres.f
  have hi : Function.Surjective i :=
    (CompHaus.epi_iff_surjective pres.f).mp pres.epi
  -- The Stacks 097D modification of `Spec R` along `i`.
  let D := WContractification.PullbackProfinite R T i
  have pb := WContractification.PullbackProfinite.isPullback R T i
  -- `Spec D` is w-local (Stacks 096C).
  haveI : WLocalSpace (PrimeSpectrum D) :=
    ConnectedComponents.wlocalSpace_of_isPullback pb
  haveI : IsWLocalRing D := ⟨inferInstance⟩
  haveI hbos : Algebra.BijectiveOnStalks R D :=
    RingHom.bijectiveOnStalks_algebraMap.mp <|
      RingHom.IndZariski.bijectiveOnStalks
        ((RingHom.IndZariski.algebraMap_iff (R := R) (S := D)).mpr inferInstance)
  -- The local rings of `D` at maximal ideals are strictly henselian: maximal ideals
  -- of `D` lie over maximal ideals of `R` and `R → D` identifies local rings.
  haveI : IsWStrictlyLocalRing D := by
    refine ⟨fun m hm => ?_⟩
    haveI : m.IsPrime := hm.isPrime
    set y : PrimeSpectrum D := ⟨m, inferInstance⟩
    have hy : y ∈ closedPoints (PrimeSpectrum D) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
    have hpre :=
      ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb
    have hxc : WContractification.PullbackProfinite.projSpec R T i y ∈
        closedPoints (PrimeSpectrum R) := by
      rw [← hpre] at hy
      exact hy
    haveI hn : (m.comap (algebraMap R D)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hxc
    haveI := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization
      (R := R) (m.comap (algebraMap R D))
    exact IsStrictlyHenselianLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (hbos.bijective_localRingHom m))
  -- `π₀(Spec D) ≃ T` is extremally disconnected.
  haveI : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum D)) := by
    have hlift := ConnectedComponents.isHomeomorph_lift_of_isPullback pb
    exact extremallyDisconnected_of_homeo hlift.homeomorph.symm
  exact ⟨D, inferInstance, inferInstance, inferInstance,
    WContractification.PullbackProfinite.faithfullyFlat R T i hi,
    { extremallyDisconnected_connectedComponents := inferInstance }⟩

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
