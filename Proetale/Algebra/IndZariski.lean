/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Proetale.Algebra.Ind
import Proetale.Algebra.StalkIso
import Proetale.Algebra.FaithfullyFlat
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Algebra.Etale

/-!
# Ind-Zariski algebras and ring homomorphisms

In this file we define ind-Zariski algebras.
-/
universe u

open CategoryTheory Limits

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

section Algebra

variable [Algebra R S] [Algebra R T]

/-- The object property on commutative `R`-algebras of being a local isomorphism. -/
def CommAlgCat.isLocalIso : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.IsLocalIso R S

lemma CommAlgCat.isLocalIso_eq : isLocalIso R = RingHom.toObjectProperty RingHom.IsLocalIso R := by
  ext S
  exact RingHom.isLocalIso_algebraMap.symm

instance : (CommAlgCat.isLocalIso R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.isLocalIso_eq]
  exact RingHom.IsLocalIso.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

private instance isClosedUnderLimitsOfShape_isLocalIso_aux (ι : Type u) [Finite ι] :
    (CommAlgCat.isLocalIso R).IsClosedUnderLimitsOfShape (Discrete ι) := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  let S : ι → CommAlgCat.{u} R := fun i => F.obj ⟨i⟩
  let natIso : F ≅ Discrete.functor S := Discrete.natIso (fun i => Iso.refl _)
  let isoPi : (CommAlgCat.piFan S).pt ≅ limit (Discrete.functor S) :=
    (limit.isoLimitCone ⟨CommAlgCat.piFan S, CommAlgCat.isLimitPiFan S⟩).symm
  let isoLim : limit (Discrete.functor S) ≅ limit F :=
    (HasLimit.isoOfNatIso natIso).symm
  apply (CommAlgCat.isLocalIso R).prop_of_iso (isoPi ≪≫ isoLim)
  have inst (i : ι) : Algebra.IsLocalIso R (S i) := hF ⟨i⟩
  exact Algebra.IsLocalIso.pi_of_finite R (fun i => (S i))

instance (ι : Type*) [Finite ι] :
    (CommAlgCat.isLocalIso R).IsClosedUnderLimitsOfShape (Discrete ι) := by
  have : Small.{u} ι := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    exact ⟨⟨ULift.{u} (Fin n), ⟨e.trans Equiv.ulift.symm⟩⟩⟩
  haveI : Finite (Shrink.{u} ι) := Finite.of_equiv ι (equivShrink ι)
  exact .of_equivalence (Discrete.equivalence (equivShrink.{u} ι).symm)

/-- An algebra is ind-Zariski if it can be written as the filtered colimit of locally isomorphic
algebras. -/
@[stacks 096N, mk_iff]
class Algebra.IndZariski (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.IsLocalIso R (P.diag.obj i)

namespace Algebra.IndZariski

lemma iff_ind_isLocalIso :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (.of R S) :=
  Algebra.indZariski_iff R S

lemma of_equiv (e : S ≃ₐ[R] T) [IndZariski R S] : IndZariski R T := by
  rwa [iff_ind_isLocalIso, (CommAlgCat.isLocalIso R).ind.prop_iff_of_iso (CommAlgCat.isoMk e.symm),
    ← iff_ind_isLocalIso]

-- The MorphismProperty version of isLocalIso in CommRingCat.
private def CommRingCat.isLocalIso : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.IsLocalIso

private lemma isLocalIso_le_etale :
    CommRingCat.isLocalIso.{u} ≤ CommRingCat.etale.{u} := by
  intro R S f (hf : f.hom.IsLocalIso)
  show f.hom.Etale
  letI : Algebra R S := f.hom.toAlgebra
  have hiso : Algebra.IsLocalIso R S := hf
  let s : Set S := {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgm, hstd⟩ := hiso.exists_notMem_isStandardOpenImmersion m
    exact hgm (hms (Ideal.subset_span (show g ∈ s from hstd)))
  exact RingHom.Etale.ofLocalizationSpanTarget (algebraMap R S) s hs (fun ⟨g, hg⟩ => by
    obtain ⟨r, hr⟩ := hg.exists_away
    haveI : Algebra.Etale R (Localization.Away g) := Algebra.Etale.of_isLocalizationAway r
    rw [show (algebraMap S (Localization.Away g)).comp (algebraMap R S) =
      algebraMap R (Localization.Away g) from by
      ext x; simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R S]]
    exact RingHom.etale_algebraMap.mpr inferInstance)

/-- If R → S is ind-Zariski and S → A is a local isomorphism, then R → A is ind-Zariski.
This is the key technical step: ind(isLocalIso) ∘ isLocalIso ⊆ ind(isLocalIso).

The full proof requires `PreIndSpreads` for `isLocalIso`, which in turn needs a spreading-out
result for local isomorphisms (analogous to `Algebra.Etale.exists_subalgebra_fg` for étale maps).

See also Stacks Project Tag 096N for the definition of ind-Zariski and the expected transitivity
property. -/
private lemma of_indZariski_isLocalIso (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra.IndZariski R S] [Algebra.IsLocalIso S A] :
    Algebra.IndZariski R A := by
  -- Blueprint: thm:ind-Zariski-composition. Internal helper: ind-Zariski ∘ IsLocalIso ⊆ ind-Zariski.
  sorry

instance pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.IndZariski R (S i)] : Algebra.IndZariski R (∀ i, S i) := by
  rw [iff_ind_isLocalIso]
  apply ObjectProperty.LimitOfShape.prop (J := Discrete ι)
  refine ⟨⟨Discrete.functor fun i ↦ .of R (S i),
      Discrete.natTrans fun i ↦ CommAlgCat.ofHom (Pi.evalAlgHom _ _ _), ?_⟩, ?_⟩
  · exact CommAlgCat.isLimitPiFan fun i ↦ .of R (S i)
  · intro j
    dsimp
    rw [← iff_ind_isLocalIso]
    infer_instance

-- Auxiliary definitions for the `prod` proof: express S × T as a pi type
private def prod_B (S T : Type u) : ULift.{u} Bool → Type u := fun i => Bool.rec T S i.down

private noncomputable instance prod_instCR (S T : Type u) [CommRing S] [CommRing T] :
    ∀ i, CommRing (prod_B S T i) := fun ⟨b⟩ =>
  Bool.rec (inferInstanceAs (CommRing T)) (inferInstanceAs (CommRing S)) b

private noncomputable instance prod_instAlg (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : ∀ i, Algebra R (prod_B S T i) := fun ⟨b⟩ =>
  Bool.rec (inferInstanceAs (Algebra R T)) (inferInstanceAs (Algebra R S)) b

private noncomputable instance prod_instIZ (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IndZariski R S] [IndZariski R T] :
    ∀ i, IndZariski R (prod_B S T i) := fun ⟨b⟩ =>
  Bool.rec (inferInstanceAs (IndZariski R T)) (inferInstanceAs (IndZariski R S)) b

private noncomputable def prod_equiv (S T : Type u) [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : (∀ i, prod_B S T i) ≃ₐ[R] S × T where
  toFun f := (f ⟨true⟩, f ⟨false⟩)
  invFun p := fun ⟨b⟩ => @Bool.rec (fun b => prod_B S T ⟨b⟩) p.2 p.1 b
  left_inv f := by ext ⟨b⟩; cases b <;> rfl
  right_inv p := by obtain ⟨_, _⟩ := p; rfl
  map_mul' _ _ := Prod.ext rfl rfl
  map_add' _ _ := Prod.ext rfl rfl
  commutes' _ := Prod.ext rfl rfl

instance prod [Algebra.IndZariski R S] [Algebra.IndZariski R T] :
    Algebra.IndZariski R (S × T) :=
  of_equiv (R := R) (S := ∀ i, prod_B S T i) (T := S × T) (prod_equiv R S T)

instance function {ι : Type u} [_root_.Finite ι] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.IndZariski R S] : Algebra.IndZariski R (ι → S) :=
  pi R (fun _ ↦ S)

variable {R}

instance (priority := 100) of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ObjectProperty.le_ind _ _ ‹_›

instance refl : Algebra.IndZariski R R :=
  Algebra.IndZariski.of_isLocalIso _

/-- The divisibility preorder on a submonoid: `a ≤ b` iff `a.val ∣ b.val`. -/
private instance dvdPreorder (M : Submonoid R) : Preorder M where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

/-- The divisibility-ordered submonoid is directed: for any `a, b ∈ M`, the product `a*b` is
an upper bound under divisibility. -/
private instance dvdIsDirected (M : Submonoid R) :
    @IsDirectedOrder M (dvdPreorder M).toLE :=
  letI : Preorder M := dvdPreorder M
  { directed := fun a b => ⟨⟨a.val * b.val, M.mul_mem a.prop b.prop⟩,
      ⟨b.val, rfl⟩, ⟨a.val, mul_comm a.val b.val⟩⟩ }

/-- The divisibility-ordered submonoid is a filtered category. -/
private instance dvdIsFiltered (M : Submonoid R) :
    @IsFiltered M (@Preorder.smallCategory M (dvdPreorder M)) := by
  letI : Preorder M := dvdPreorder M
  haveI : Nonempty M := ⟨⟨1, M.one_mem⟩⟩
  exact isFiltered_of_directed_le_nonempty M

/-- For `a ∣ b` in a commutative ring, the unique R-algebra hom `R[1/a] →ₐ[R] R[1/b]`. -/
private noncomputable def locAwayAlgHom {a b : R} (h : a ∣ b) :
    Localization.Away a →ₐ[R] Localization.Away b :=
  IsLocalization.liftAlgHom
    (f := Algebra.ofId R (Localization.Away b))
    (hf := fun y => by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.prop
      simp only [Algebra.ofId_apply, ← hn, map_pow]
      exact IsUnit.pow n (IsLocalization.Away.isUnit_of_dvd b h))

/-- The functor from `M` (ordered by divisibility) to `CommAlgCat R` sending `m` to `R[1/m]`. -/
private noncomputable def localizationDiag (M : Submonoid R) :
    letI : SmallCategory M := @Preorder.smallCategory M (dvdPreorder M)
    M ⥤ CommAlgCat.{u} R where
  obj m := .of R (Localization.Away m.val)
  map {a b} _ := CommAlgCat.ofHom (locAwayAlgHom (leOfHom ‹_›))
  map_id a := by
    apply CommAlgCat.hom_ext
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_id]
    exact (IsLocalization.algHom_subsingleton (Submonoid.powers a.val)).elim _ _
  map_comp {a _ _} _ _ := by
    apply CommAlgCat.hom_ext
    simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp]
    exact (IsLocalization.algHom_subsingleton (Submonoid.powers a.val)).elim _ _

/-- The cocone maps from `R[1/m]` to `S = R_M`. -/
private noncomputable def localizationCoconeMap (M : Submonoid R) [IsLocalization M S] (m : M) :
    Localization.Away m.val →ₐ[R] S :=
  IsLocalization.liftAlgHom
    (f := Algebra.ofId R S)
    (hf := fun y => by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.val m.val).mp y.prop
      simp only [Algebra.ofId_apply, ← hn, map_pow]
      exact IsUnit.pow n (IsLocalization.map_units S ⟨m.val, m.prop⟩))

private noncomputable def localizationColimitDesc (M : Submonoid R) [IsLocalization M S] :
    letI : SmallCategory M := @Preorder.smallCategory M (dvdPreorder M)
    (s : Cocone (localizationDiag M)) → (CommAlgCat.of R S ⟶ s.pt) := by
  letI : SmallCategory M := @Preorder.smallCategory M (dvdPreorder M)
  intro s
  -- For each m ∈ M, algebraMap R s.pt m is a unit (from the cocone maps)
  have hunit : ∀ m : M, IsUnit (algebraMap R s.pt m.val) := fun m => by
    -- The cocone map s.ι.app m is an R-algebra hom from R[1/m] to s.pt
    -- Since (localizationDiag M).obj m = CommAlgCat.of R (Localization.Away m.val),
    -- the .hom field is an AlgHom from Localization.Away m.val to s.pt
    let φ : Localization.Away m.val →ₐ[R] s.pt := (s.ι.app m).hom
    have : IsUnit (φ (algebraMap R (Localization.Away m.val) m.val)) :=
      (IsLocalization.Away.algebraMap_isUnit m.val).map φ.toRingHom
    rwa [φ.commutes] at this
  exact CommAlgCat.ofHom (IsLocalization.liftAlgHom
    (M := M) (f := Algebra.ofId R s.pt)
    (hf := fun m => by simpa [Algebra.ofId_apply] using hunit m))

lemma of_isLocalization (M : Submonoid R) [IsLocalization M S] : Algebra.IndZariski R S := by
  letI : Preorder M := dvdPreorder M
  letI : SmallCategory M := Preorder.smallCategory M
  rw [iff_ind_isLocalIso]
  refine ⟨M, inferInstance, dvdIsFiltered M, ?_, fun m => ?_⟩
  · -- Construct the ColimitPresentation
    exact {
      diag := localizationDiag M
      ι := {
        app := fun m => CommAlgCat.ofHom (localizationCoconeMap (S := S) M m)
        naturality := fun a _ _ => by
          apply CommAlgCat.hom_ext
          exact @Subsingleton.elim (Localization.Away a.val →ₐ[R] S)
            (IsLocalization.algHom_subsingleton (Submonoid.powers a.val)) _ _
      }
      isColimit := {
        desc := localizationColimitDesc (S := S) M
        fac := fun s m => by
          apply CommAlgCat.hom_ext
          exact @Subsingleton.elim (Localization.Away m.val →ₐ[R] ↑s.pt)
            (IsLocalization.algHom_subsingleton (Submonoid.powers m.val)) _ _
        uniq := fun s φ _ => by
          apply CommAlgCat.hom_ext
          exact @Subsingleton.elim (S →ₐ[R] ↑s.pt)
            (IsLocalization.algHom_subsingleton M) _ _
      }
    }
  · -- Each R[1/m] is a standard open immersion, hence a local isomorphism
    show Algebra.IsLocalIso R (Localization.Away m.val)
    exact inferInstance

instance localization (M : Submonoid R) : Algebra.IndZariski R (Localization M) :=
  of_isLocalization _ M

variable (R)

/-- A local isomorphism is flat: the spanning set of standard open immersions
gives flatness at each localization, and flat is local on the target. -/
private lemma isLocalIso_implies_flat {R : Type u} [CommRing R] (X : CommAlgCat.{u} R)
    (hX : Algebra.IsLocalIso R X) : Module.Flat R X := by
  have hflat : RingHom.Flat (algebraMap R X) :=
    RingHom.Flat.ofLocalizationSpanTarget (algebraMap R X)
      {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)} (by
        by_contra hne
        obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
        obtain ⟨g, hgm, hstd⟩ := hX.exists_notMem_isStandardOpenImmersion m
        exact hgm (hms (Ideal.subset_span hstd)))
      (fun ⟨g, hg⟩ => by
        obtain ⟨r, hr⟩ := hg.exists_away
        rw [show (algebraMap X (Localization.Away g)).comp (algebraMap R X) =
          algebraMap R (Localization.Away g) from by
          ext x; simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R X]]
        exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r)))
  exact RingHom.flat_algebraMap_iff.mp hflat

instance (priority := 100) _root_.Module.Flat.of_indZariski [Algebra.IndZariski R S] :
    Module.Flat R S := by
  rw [Module.Flat.iff_ind_flat]
  obtain ⟨J, _, _, pres, h⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  exact ⟨J, inferInstance, inferInstance, pres, fun i => by
    rw [CommAlgCat.flat_iff]
    exact isLocalIso_implies_flat (pres.diag.obj i) (h i)⟩

set_option maxHeartbeats 400000 in
@[stacks 096T]
theorem bijectiveOnStalks_algebraMap [Algebra.IndZariski R S] :
    (algebraMap R S).BijectiveOnStalks := by
  -- S = colim S_i with each S_i a local isomorphism over R.
  -- Each local isomorphism is bijective on stalks (proven). We show the colimit preserves this.
  obtain ⟨J, hJ_cat, hJ_filt, P, hP⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  letI := hJ_cat; letI := hJ_filt
  have hBij : ∀ (i : J), (algebraMap R (P.diag.obj i)).BijectiveOnStalks :=
    fun i => (RingHom.isLocalIso_algebraMap.mpr (hP i)).bijectiveOnStalks
  have hcolim : IsColimit ((forget (CommAlgCat.{u} R)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} R)) P.isColimit
  intro p _
  set q := p.comap (algebraMap R S) with hq_def
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  -- Helper: for stage i, let ι_i be the cocone ring hom, p_i = p.comap ι_i, and q = p_i.comap alg_i.
  -- The stalk map factors: R_q → (S_i)_{p_i} → S_p via localRingHom_comp.
  constructor
  · -- Injectivity of R_q → S_p.
    -- Strategy: extract torsion in S, lift to a stage, use the unit trick in the stage
    -- localization to get torsion in R, then conclude in R_q.
    intro a b hab
    obtain ⟨⟨r₁, ⟨d₁, hd₁⟩⟩, ha⟩ := IsLocalization.surj q.primeCompl a
    obtain ⟨⟨r₂, ⟨d₂, hd₂⟩⟩, hb⟩ := IsLocalization.surj q.primeCompl b
    -- Simplify the projection forms in ha and hb
    simp only at ha hb
    -- ha : a * algebraMap R _ d₁ = algebraMap R _ r₁
    -- hb : b * algebraMap R _ d₂ = algebraMap R _ r₂
    -- From hab, derive: in S_p, algebraMap R S (d₂ * r₁ - d₁ * r₂) = 0.
    set fl := Localization.localRingHom q p (algebraMap R S) rfl
    have hzero_Sp : (algebraMap S (Localization.AtPrime p)) (algebraMap R S (d₂ * r₁ - d₁ * r₂)) = 0 := by
      -- fl sends algebraMap R _ x to algebraMap S S_p (algebraMap R S x).
      have hfl_comm : ∀ x : R, fl (algebraMap R _ x) =
          (algebraMap S (Localization.AtPrime p)) (algebraMap R S x) :=
        fun x => Localization.localRingHom_to_map q p (algebraMap R S) rfl x
      -- From ha: fl a * fl (algebraMap R _ d₁) = fl (algebraMap R _ r₁)
      have h1 : fl a * (algebraMap S (Localization.AtPrime p)) (algebraMap R S d₁) =
          (algebraMap S (Localization.AtPrime p)) (algebraMap R S r₁) := by
        rw [← hfl_comm, ← hfl_comm, ← map_mul fl, ha]
      -- From hb: fl b * (algebraMap S _) (algebraMap R S d₂) = (algebraMap S _) (algebraMap R S r₂)
      have h2 : fl b * (algebraMap S (Localization.AtPrime p)) (algebraMap R S d₂) =
          (algebraMap S (Localization.AtPrime p)) (algebraMap R S r₂) := by
        rw [← hfl_comm, ← hfl_comm, ← map_mul fl, hb]
      -- Now: d₂ * r₁ - d₁ * r₂ maps to 0 in S_p.
      -- Let's abbreviate the algebra maps for readability.
      set α := algebraMap S (Localization.AtPrime p)
      set D₁ := α (algebraMap R S d₁)
      set D₂ := α (algebraMap R S d₂)
      set R₁ := α (algebraMap R S r₁)
      set R₂ := α (algebraMap R S r₂)
      rw [map_sub (algebraMap R S), map_sub α, sub_eq_zero, map_mul (algebraMap R S),
          map_mul (algebraMap R S), map_mul α, map_mul α]
      -- Goal: D₂ * R₁ = D₁ * R₂
      -- From h1: fl a * D₁ = R₁, from h2: fl b * D₂ = R₂, from hab: fl a = fl b.
      have h1' : D₂ * R₁ = D₂ * (fl a * D₁) := by rw [← h1]
      have h2' : D₁ * R₂ = D₁ * (fl b * D₂) := by rw [← h2]
      rw [h1', h2', hab]; ring
    -- Extract torsion: ∃ c ∉ p, c * algebraMap R S (d₂ * r₁ - d₁ * r₂) = 0 in S.
    obtain ⟨⟨c, hc⟩, hcz⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp
      (show (algebraMap S _) (algebraMap R S (d₂ * r₁ - d₁ * r₂)) =
            (algebraMap S _) (0 : S) by rw [hzero_Sp, map_zero])
    simp only [mul_zero] at hcz
    -- Lift c to a stage j, lift the zero equation to a stage k.
    obtain ⟨j, c_j', hc_j⟩ := Types.jointly_surjective_of_isColimit hcolim c
    set c_j : (P.diag.obj j : Type u) := c_j'
    set z_j := c_j * algebraMap R (P.diag.obj j) (d₂ * r₁ - d₁ * r₂) with hz_j_def
    let z_j' : (P.diag ⋙ forget (CommAlgCat.{u} R)).obj j := z_j
    let zero_j' : (P.diag ⋙ forget (CommAlgCat.{u} R)).obj j := (0 : (P.diag.obj j : Type u))
    -- Key: (P.ι.app j).hom is the same as the forgetful cocone map.
    have hc_j' : (P.ι.app j).hom c_j = c := hc_j
    have hzero_colim :
        ((forget (CommAlgCat.{u} R)).mapCocone P.cocone).ι.app j z_j' =
        ((forget (CommAlgCat.{u} R)).mapCocone P.cocone).ι.app j zero_j' := by
      show (P.ι.app j).hom z_j = (P.ι.app j).hom 0
      simp only [hz_j_def, map_mul, map_zero, AlgHom.commutes, hc_j']
      exact hcz
    obtain ⟨k, f_jk, hf_jk⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcolim z_j' zero_j').mp hzero_colim
    -- Define the stage k ring and cocone map.
    set ι_k := (P.ι.app k).hom.toRingHom
    set p_k := p.comap ι_k
    set c_k := (P.diag.map f_jk).hom c_j
    have hf_jk' : c_k * algebraMap R (P.diag.obj k) (d₂ * r₁ - d₁ * r₂) = 0 := by
      have : (P.diag.map f_jk).hom z_j = (P.diag.map f_jk).hom 0 := hf_jk
      rw [hz_j_def, map_mul, map_zero, (P.diag.map f_jk).hom.commutes] at this
      exact this
    haveI hp_k : p_k.IsPrime := by
      simp only [p_k, ι_k]
      exact Ideal.IsPrime.comap _
    -- The cocone map at k sends c_k to c (by naturality + hc_j).
    have hc_k_map : (P.ι.app k).hom c_k = c := by
      -- c_k = (P.diag.map f_jk).hom c_j
      -- Use P.w: P.diag.map f_jk ≫ P.ι.app k = P.ι.app j (in CommAlgCat)
      have h := P.w f_jk
      have key : (P.ι.app k).hom ((P.diag.map f_jk).hom c_j) = (P.ι.app j).hom c_j :=
        congrFun (congrArg DFunLike.coe (congrArg CommAlgCat.Hom.hom h)) c_j
      -- Goal: (P.ι.app k).hom c_k = c; c_k is set-defined as (P.diag.map f_jk).hom c_j
      convert key.trans hc_j'
    have hc_k_nmem : c_k ∉ p_k := by
      intro hmem
      -- p_k = p.comap ι_k, so c_k ∈ p_k means ι_k c_k ∈ p, i.e., c ∈ p.
      exact hc (show c ∈ p from hc_k_map ▸ hmem)
    -- Key: c_k ∉ p_k and c_k * algebraMap R S_k (d₂ * r₁ - d₁ * r₂) = 0.
    -- In (S_k)_{p_k}, c_k becomes a unit, so algebraMap R S_k (d₂ * r₁ - d₁ * r₂) maps to 0.
    -- The stalk map R_{q_k} → (S_k)_{p_k} is injective (by hBij k),
    -- so algebraMap R R_{q_k} (d₂ * r₁ - d₁ * r₂) = 0.
    -- This gives ∃ e ∈ R \ q_k = R \ q, e * (d₂ * r₁ - d₁ * r₂) = 0, hence a = b in R_q.
    set q_k := p_k.comap (algebraMap R (P.diag.obj k))
    haveI : q_k.IsPrime := Ideal.IsPrime.comap _
    -- Show algebraMap S_k (S_k)_{p_k} (algebraMap R S_k (d₂ * r₁ - d₁ * r₂)) = 0.
    have hzero_Sk_loc : (algebraMap (P.diag.obj k) (Localization.AtPrime p_k))
        (algebraMap R _ (d₂ * r₁ - d₁ * r₂)) = 0 := by
      have hck_mem : c_k ∈ p_k.primeCompl := hc_k_nmem
      have hunit_ck : IsUnit ((algebraMap (P.diag.obj k) (Localization.AtPrime p_k)) c_k) :=
        IsLocalization.map_units (Localization.AtPrime p_k) ⟨c_k, hck_mem⟩
      have h0 : (algebraMap (P.diag.obj k) (Localization.AtPrime p_k))
          (c_k * algebraMap R _ (d₂ * r₁ - d₁ * r₂)) = 0 := by
        rw [hf_jk', map_zero]
      rw [map_mul] at h0
      -- h0 : unit * x = 0, where unit is a unit. So x = 0.
      rwa [IsUnit.mul_right_eq_zero hunit_ck] at h0
    -- The stalk map sends algebraMap R R_{q_k} x to algebraMap S_k (S_k)_{p_k} (algebraMap R S_k x).
    have hstalk_zero : Localization.localRingHom q_k p_k (algebraMap R _) rfl
        (algebraMap R (Localization.AtPrime q_k) (d₂ * r₁ - d₁ * r₂)) =
        Localization.localRingHom q_k p_k (algebraMap R _) rfl 0 := by
      rw [Localization.localRingHom_to_map, hzero_Sk_loc, map_zero]
    -- By injectivity at stage k:
    have hinj_k := (hBij k p_k).1 hstalk_zero
    -- hinj_k : algebraMap R R_{q_k} (d₂ * r₁ - d₁ * r₂) = 0
    -- Extract torsion witness in R: ∃ e ∉ q_k, e * (d₂ * r₁ - d₁ * r₂) = 0.
    rw [map_sub, sub_eq_zero] at hinj_k
    obtain ⟨⟨e, he⟩, heq⟩ := (IsLocalization.eq_iff_exists q_k.primeCompl _).mp hinj_k
    -- heq : e * (d₂ * r₁) = e * (d₁ * r₂)
    -- Since q = q_k, e ∉ q.
    have hcomap_eq_k : q = q_k := by
      ext r
      simp only [Ideal.mem_comap, hq_def, q_k, p_k, ι_k]
      -- Goal: algebraMap R S r ∈ p ↔ (P.ι.app k).hom.toRingHom (algebraMap R _ r) ∈ p
      -- (P.ι.app k).hom.toRingHom x = (P.ι.app k).hom x for all x
      -- Goal: ι_k (algebraMap R _ r) ∈ p ↔ algebraMap R S r ∈ p
      -- where ι_k = (P.ι.app k).hom.toRingHom
      -- Key: ι_k (algebraMap R _ r) = (P.ι.app k).hom (algebraMap R _ r) = algebraMap R S r
      suffices h : ι_k (algebraMap R _ r) = algebraMap R S r by
        exact h ▸ Iff.rfl
      show (P.ι.app k).hom (algebraMap R _ r) = algebraMap R S r
      exact (P.ι.app k).hom.commutes r
    have he_q : e ∉ q := hcomap_eq_k ▸ he
    -- Conclude a = b in R_q via IsLocalization.eq.
    have ha_mk : a = IsLocalization.mk' _ r₁ ⟨d₁, hd₁⟩ :=
      (IsLocalization.eq_mk'_iff_mul_eq (M := q.primeCompl)).mpr ha
    have hb_mk : b = IsLocalization.mk' _ r₂ ⟨d₂, hd₂⟩ :=
      (IsLocalization.eq_mk'_iff_mul_eq (M := q.primeCompl)).mpr hb
    rw [ha_mk, hb_mk, IsLocalization.eq (M := q.primeCompl)]
    exact ⟨⟨e, he_q⟩, heq⟩
  · -- Surjectivity of R_q → S_p.
    -- Strategy: lift element of S_p to a stage, find preimage via stage surjectivity,
    -- extract r, d from the preimage, construct the answer in R_q.
    intro x
    obtain ⟨⟨s, ⟨t, ht⟩⟩, hx⟩ := IsLocalization.surj p.primeCompl x
    -- hx : x * algebraMap S S_p t = algebraMap S S_p s.
    -- Lift s and t to a common stage i.
    obtain ⟨i, s_i', t_i', hs_i, ht_i⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hcolim s t
    set s_i : (P.diag.obj i : Type u) := s_i'
    set t_i : (P.diag.obj i : Type u) := t_i'
    have hs_i' : (P.ι.app i).hom s_i = s := hs_i
    have ht_i' : (P.ι.app i).hom t_i = t := ht_i
    set ι_i : (P.diag.obj i : Type u) →+* S := (P.ι.app i).hom.toRingHom
    set p_i := p.comap ι_i
    haveI : p_i.IsPrime := Ideal.IsPrime.comap ι_i
    have ht_i_nmem : t_i ∉ p_i := by
      intro hmem
      have : (P.ι.app i).hom t_i ∈ p := hmem
      rw [ht_i'] at this; exact ht this
    -- Stage surjectivity: find y_i : R_{q_i} mapping to mk'(s_i, t_i) in (S_i)_{p_i}.
    set q_i := p_i.comap (algebraMap R (P.diag.obj i))
    haveI : q_i.IsPrime := Ideal.IsPrime.comap _
    obtain ⟨y_i, hy_i⟩ := (hBij i p_i).2
      (IsLocalization.mk' (Localization.AtPrime p_i) s_i
        (⟨t_i, ht_i_nmem⟩ : p_i.primeCompl))
    -- Extract r, d from y_i.
    obtain ⟨⟨r, ⟨d, hd⟩⟩, hy_surj⟩ := IsLocalization.surj q_i.primeCompl y_i
    -- hy_surj : y_i * algebraMap R R_{q_i} d = algebraMap R R_{q_i} r
    -- hd : d ∉ q_i
    -- Since q = q_i (same argument as before), d ∉ q.
    have hcomap_eq_i : q = q_i := by
      ext r'; simp only [Ideal.mem_comap, p_i, ι_i, hq_def, q_i]
      constructor
      · intro h
        show (P.ι.app i).hom (algebraMap R _ r') ∈ p
        rw [(P.ι.app i).hom.commutes]; exact h
      · intro h
        show algebraMap R S r' ∈ p
        have h1 : (P.ι.app i).hom (algebraMap R _ r') ∈ p := h
        rwa [(P.ι.app i).hom.commutes] at h1
    have hd_q : d ∉ q := hcomap_eq_i ▸ hd
    -- Construct y = mk'(r, d) in R_q.
    let y := IsLocalization.mk' (Localization.AtPrime q) r (⟨d, hd_q⟩ : q.primeCompl)
    refine ⟨y, ?_⟩
    -- Show: localRingHom q p (algebraMap R S) rfl y = x.
    rw [Localization.localRingHom_mk']
    -- Goal: mk'(algebraMap R S r, algebraMap R S d) = x in S_p.
    -- Rewrite x as mk'(s, t).
    rw [show x = IsLocalization.mk' _ s ⟨t, ht⟩ from
      (IsLocalization.eq_mk'_iff_mul_eq (M := p.primeCompl)).mpr hx]
    -- Goal: mk'(algebraMap R S r, algebraMap R S d) = mk'(s, t) in S_p.
    -- From the stage-level equation:
    have hy_i' : y_i = IsLocalization.mk' _ r ⟨d, hd⟩ :=
      (IsLocalization.eq_mk'_iff_mul_eq (M := q_i.primeCompl)).mpr hy_surj
    rw [hy_i', Localization.localRingHom_mk'] at hy_i
    -- hy_i : mk'(algebraMap R S_i r, algebraMap R S_i d) = mk'(s_i, t_i) in (S_i)_{p_i}.
    -- Extract torsion witness in S_i.
    rw [IsLocalization.eq (M := p_i.primeCompl)] at hy_i
    obtain ⟨⟨e_i, he_i⟩, heq_i⟩ := hy_i
    -- Apply ι_i to get a torsion witness in S.
    have he_S : (ι_i e_i : S) ∉ p := fun h => he_i (show ι_i e_i ∈ p from h)
    have heq_S : ι_i e_i * (t * algebraMap R S r) = ι_i e_i * (algebraMap R S d * s) := by
      have := congr_arg ι_i heq_i
      simp only [map_mul] at this
      rw [show ι_i (algebraMap R _ r) = algebraMap R S r from (P.ι.app i).hom.commutes r,
          show ι_i (algebraMap R _ d) = algebraMap R S d from (P.ι.app i).hom.commutes d,
          show (ι_i s_i : S) = s from hs_i',
          show (ι_i t_i : S) = t from ht_i'] at this
      exact this
    -- Conclude: mk'(algebraMap R S r, algebraMap R S d) = mk'(s, t) in S_p.
    rw [IsLocalization.eq (M := p.primeCompl)]
    exact ⟨⟨ι_i e_i, he_S⟩, heq_S⟩

private lemma isLocalIso_le_isFinitelyPresentable :
    CommAlgCat.isLocalIso R ≤ ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := by
  intro S hS
  -- hS : Algebra.IsLocalIso R S, which implies algebraMap R S is FinitePresentation
  -- by Zariski descent for finite presentation.
  have hfp : RingHom.FinitePresentation (algebraMap R S) := by
    -- For every prime q of S, there's g ∉ q with IsStandardOpenImmersion R S[1/g].
    -- Standard open immersion means S[1/g] ≅ R[1/r], which is of finite presentation.
    -- By ofLocalizationSpanTarget, algebraMap R S is of finite presentation.
    let s : Set S := {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    have hs : Ideal.span s = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
      obtain ⟨g, hgm, hstd⟩ := hS.exists_notMem_isStandardOpenImmersion m
      exact hgm (hms (Ideal.subset_span (show g ∈ s from hstd)))
    apply RingHom.finitePresentation_ofLocalizationSpanTarget
      (algebraMap R S) s hs
    intro ⟨g, hg⟩
    -- hg : Algebra.IsStandardOpenImmersion R (Localization.Away g)
    -- Goal: RingHom.FinitePresentation ((algebraMap S (Localization.Away g)).comp (algebraMap R S))
    obtain ⟨r, hr⟩ := hg.exists_away
    -- hr : IsLocalization.Away r (Localization.Away g) as R-algebra
    haveI : Algebra.FinitePresentation R (Localization.Away g) :=
      Algebra.FinitePresentation.of_isLocalizationAway r
    rw [show (algebraMap S (Localization.Away g)).comp (algebraMap R S) =
      algebraMap R (Localization.Away g) from by
      ext x; simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R S]]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  -- Transfer via commAlgCatEquivUnder: Under version is finitely presentable.
  have hunder : IsFinitelyPresentable.{u}
      ((commAlgCatEquivUnder (.of R)).functor.obj S) :=
    CommRingCat.isFinitelyPresentable_under _ _ (by convert hfp using 1)
  -- Transfer back via the equivalence.
  haveI : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact (@isCardinalPresentable_iff_of_isEquivalence
    (CommAlgCat.{u} R) _ S (Cardinal.aleph0 : Cardinal.{u}) this
    (Under (CommRingCat.of.{u} R)) _
    (commAlgCatEquivUnder (.of R)).functor inferInstance).mp hunder

theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  have h' : ∀ (i : ι), ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (P.diag.obj i) :=
    fun i => (iff_ind_isLocalIso R (P.diag.obj i)).mp (h i)
  -- Each P.diag.obj i satisfies ind (isLocalIso R), so S satisfies ind (ind (isLocalIso R)).
  have hind_ind : ObjectProperty.ind.{u} (ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R))
      (.of R S) :=
    ⟨ι, ‹_›, ‹_›, P, h'⟩
  -- By ind_ind (isLocalIso R ≤ isFinitelyPresentable), ind (ind (isLocalIso R)) = ind (isLocalIso R).
  rwa [ObjectProperty.ind_ind (isLocalIso_le_isFinitelyPresentable R)] at hind_ind

-- isLocalIso is ≤ MorphismProperty.isFinitelyPresentable, derived from isLocalIso ≤ etale.
private lemma isLocalIso_le_mp_isFP :
    CommRingCat.isLocalIso.{u} ≤ MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} :=
  le_trans isLocalIso_le_etale CommRingCat.etale_le_isFinitelyPresentable

lemma trans [Algebra S T] [IsScalarTower R S T] [Algebra.IndZariski R S] [Algebra.IndZariski S T] :
    Algebra.IndZariski R T := by
  -- Strategy: T = colim D_j in CommRingCat (from IndZariski S T, each S → D_j isLocalIso).
  -- For each j, R → D_j is ind(isLocalIso) by of_indZariski_isLocalIso.
  -- Then R → T is ind(ind(isLocalIso)) = ind(isLocalIso) by ind_ind.
  -- Convert to MorphismProperty.ind level.
  suffices MorphismProperty.ind.{u} CommRingCat.isLocalIso
      (CommRingCat.ofHom (algebraMap R T)) by
    rw [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]
    exact this
  -- Convert IndZariski S T to MorphismProperty.ind form.
  have hST : MorphismProperty.ind.{u} CommRingCat.isLocalIso
      (CommRingCat.ofHom (algebraMap S T)) := by
    have : Algebra.IndZariski S T := inferInstance
    rwa [iff_ind_isLocalIso S, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  obtain ⟨J, hJ, hFilt, D, s₂, t₂, ht₂, hst₂⟩ := hST
  -- For each j, R → D_j is ind(isLocalIso) by of_indZariski_isLocalIso.
  have hInd_j : ∀ j, MorphismProperty.ind.{u} CommRingCat.isLocalIso
      (CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j) := by
    intro j
    have hLocalIso_j : (s₂.app j).hom.IsLocalIso := (hst₂ j).1
    letI : Algebra S (D.obj j) := (s₂.app j).hom.toAlgebra
    letI : Algebra R (D.obj j) :=
      ((CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j).hom).toAlgebra
    haveI : IsScalarTower R S (D.obj j) := .of_algebraMap_eq' rfl
    haveI : Algebra.IsLocalIso S (D.obj j) := RingHom.isLocalIso_algebraMap.mp hLocalIso_j
    have := of_indZariski_isLocalIso R S (D.obj j)
    rwa [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  -- R → T is ind(ind(isLocalIso)): T = colim D_j with each R → D_j being ind(isLocalIso).
  have hind_ind : MorphismProperty.ind.{u} (MorphismProperty.ind.{u} CommRingCat.isLocalIso)
      (CommRingCat.ofHom (algebraMap R T)) :=
    ⟨J, hJ, hFilt, D,
      (Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂,
      t₂, ht₂, fun j => ⟨hInd_j j, by
        -- Goal: ((const J).map (ofHom (algebraMap R S)) ≫ s₂).app j ≫ t₂.app j = ofHom (algebraMap R T)
        simp only [NatTrans.comp_app, Functor.const_map_app]
        -- Now: ofHom (algebraMap R S) ≫ s₂.app j ≫ t₂.app j = ofHom (algebraMap R T)
        rw [Category.assoc, (hst₂ j).2]
        -- Now: ofHom (algebraMap R S) ≫ ofHom (algebraMap S T) = ofHom (algebraMap R T)
        ext x; show (algebraMap S T) ((algebraMap R S) x) = (algebraMap R T) x
        exact (IsScalarTower.algebraMap_apply R S T x).symm⟩⟩
  -- By ind_ind: ind(ind(isLocalIso)) = ind(isLocalIso).
  have key : MorphismProperty.ind.{u} (MorphismProperty.ind.{u} CommRingCat.isLocalIso) =
      MorphismProperty.ind.{u} CommRingCat.isLocalIso :=
    MorphismProperty.ind_ind isLocalIso_le_mp_isFP
  rw [key] at hind_ind
  exact hind_ind

end Algebra.IndZariski

end Algebra

section RingHom

/-- A ring hom is ind-Zariski if and only if it is an ind-Zariski algebra. -/
@[stacks 096N, algebraize Algebra.IndZariski]
def RingHom.IndZariski {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndZariski R S

namespace RingHom.IndZariski

lemma algebraMap_iff [Algebra R S] :
    (algebraMap R S).IndZariski ↔ Algebra.IndZariski R S:=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

variable {R S T}

lemma iff_ind_isLocalIso (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) (CommRingCat.ofHom f) := by
  algebraize [f]
  simp only [RingHom.IndZariski, Algebra.IndZariski.iff_ind_isLocalIso, ← f.algebraMap_toAlgebra,
    RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.isLocalIso_eq]

/-- A ring hom is ind-Zariski if and only if it can be written
as a colimit of local isomorphisms. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndZariski ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S)
      (_ : IsColimit (.mk _ c)), ∀ i, (t.app i).hom.IsLocalIso ∧ t.app i ≫ c.app i = f :=
  RingHom.IndZariski.iff_ind_isLocalIso _

lemma id : (RingHom.id R).IndZariski :=
  Algebra.IndZariski.refl

variable {f : R →+* S} {g : S →+* T}

lemma comp (hg : g.IndZariski) (hf : f.IndZariski) : (g.comp f).IndZariski := by
  algebraize [f, g, g.comp f]
  exact Algebra.IndZariski.trans R S T

lemma prod {g : R →+* T} (hf : f.IndZariski) (hg : g.IndZariski) : (f.prod g).IndZariski := by
  algebraize [f, g]
  exact Algebra.IndZariski.prod R S T

lemma pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* (S i)) (hf : ∀ i, (f i).IndZariski) : (Pi.ringHom f).IndZariski := by
  let (i : ι) : Algebra R (S i) := (f i).toAlgebra
  have (i : ι) : Algebra.IndZariski R (S i) := hf i
  exact Algebra.IndZariski.pi R S

lemma flat (h : f.IndZariski) : f.Flat := by
  algebraize [f]
  exact .of_indZariski R S

-- lemma of_bijective (hf : Function.Bijective f) : f.IndZariski :=
--   sorry

-- lemma stableUnderComposition : StableUnderComposition IndZariski :=
--   fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

-- lemma respectsIso : RespectsIso IndZariski :=
--   stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

@[stacks 096T]
theorem bijectiveOnStalks (h : f.IndZariski) : f.BijectiveOnStalks := by
  algebraize [f]
  exact Algebra.IndZariski.bijectiveOnStalks_algebraMap R S

private lemma isLocalIso_le_morphismProperty_isFinitelyPresentable :
    RingHom.toMorphismProperty RingHom.IsLocalIso ≤
      MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} := by
  intro R S f (hf : f.hom.IsLocalIso)
  apply CommRingCat.isFinitelyPresentable_hom
  -- Need: f.hom.FinitePresentation from f.hom.IsLocalIso
  letI : Algebra R S := f.hom.toAlgebra
  have hiso : Algebra.IsLocalIso R S := hf
  let s : Set S := {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hgm, hstd⟩ := hiso.exists_notMem_isStandardOpenImmersion m
    exact hgm (hms (Ideal.subset_span (show g ∈ s from hstd)))
  apply RingHom.finitePresentation_ofLocalizationSpanTarget
    (algebraMap R S) s hs
  intro ⟨g, hg⟩
  obtain ⟨r, hr⟩ := hg.exists_away
  haveI : Algebra.FinitePresentation R (Localization.Away g) :=
    Algebra.FinitePresentation.of_isLocalizationAway r
  rw [show (algebraMap S (Localization.Away g)).comp (algebraMap R S) =
    algebraMap R (Localization.Away g) from by
    ext x; simp [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R S]]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

private lemma indZariski_respectsIso :
    RingHom.RespectsIso
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndZariski) := by
  rw [RingHom.toMorphismProperty_respectsIso_iff]
  have heq : RingHom.toMorphismProperty
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) ↦ f.IndZariski) =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
    ext X Y g
    exact iff_ind_isLocalIso g.hom
  rw [heq]
  haveI : (RingHom.toMorphismProperty RingHom.IsLocalIso).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.IsLocalIso.respectsIso
  infer_instance

/-- Ind-Zariski is equivalent to ind-ind-Zariski. -/
lemma iff_ind_indZariski (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndZariski) (CommRingCat.ofHom f) := by
  rw [iff_ind_isLocalIso]
  have heq : RingHom.toMorphismProperty RingHom.IndZariski =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
    ext X Y g
    exact iff_ind_isLocalIso g.hom
  rw [heq]; constructor
  · exact MorphismProperty.le_ind _ _
  · intro h
    have key : MorphismProperty.ind.{u}
        (MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso)) =
        MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) :=
      MorphismProperty.ind_ind isLocalIso_le_morphismProperty_isFinitelyPresentable
    rw [key] at h; exact h

/-- A ring hom is ind-Zariski if it can be written as a filtered colimit of ind-Zariski maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndZariski ∧ t.app i ≫ c.app i = f) : f.hom.IndZariski :=
  (iff_ind_indZariski _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

theorem _root_.Algebra.IndZariski.iff_ind_indZariksi [Algebra R S] :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndZariski R) (.of R S) :=
  (algebraMap_iff (R := R) S).symm.trans
    ((iff_ind_indZariski _).trans
      indZariski_respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty)

end RingHom.IndZariski

end RingHom
