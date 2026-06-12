/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WContractible
import Proetale.Topology.Comparison.Acyclicity

/-!
# Weakly contractible objects of the pro-étale site

An object `W` of the affine pro-étale site of a scheme `S` is *weakly contractible* if
every surjection onto `W` in the affine pro-étale site splits. We show:

- `AlgebraicGeometry.Scheme.AffineProEt.isWeaklyContractible_of_isWContractibleRing`:
  if the ring of global sections of `W` is w-contractible, then `W` is weakly
  contractible (every faithfully flat ind-étale algebra over a w-contractible ring has a
  retraction, `IsWContractibleRing.exists_retraction`).
- `AlgebraicGeometry.Scheme.AffineProEt.exists_isWeaklyContractible_cover`:
  every object of the affine pro-étale site admits a surjection from a weakly
  contractible object (BS, Proposition 4.2.8; blueprint `prop:proet-wc`). This follows
  from `exists_isWContractibleRing`.
- `AlgebraicGeometry.Scheme.AffineProEt.surjective_app_of_epi`: an epimorphism of abelian
  sheaves on the pro-étale site is surjective on sections over weakly contractible
  objects.
- `AlgebraicGeometry.Scheme.AffineProEt.epi_of_forall_surjective_app`: conversely, a
  morphism of abelian sheaves which is surjective on sections over all weakly
  contractible objects is an epimorphism.

In particular the topos of pro-étale sheaves on `S` has enough weakly contractible
objects, hence is replete.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

/-- An object `W` of the affine pro-étale site is weakly contractible if every surjection
onto `W` in the affine pro-étale site splits. -/
def IsWeaklyContractible (W : S.AffineProEt) : Prop :=
  ∀ ⦃V : S.AffineProEt⦄ (q : V ⟶ W), Surjective q.left → ∃ s : W ⟶ V, s ≫ q = 𝟙 W

/-- If the ring of global sections of `W` is w-contractible, then `W` is a weakly
contractible object of the affine pro-étale site. We allow an abstract w-contractible
ring `A` together with a ring isomorphism `Γ(W.left, ⊤) ≃+* A` to avoid transporting
`IsWContractibleRing` along ring isomorphisms. -/
theorem isWeaklyContractible_of_isWContractibleRing {W : S.AffineProEt}
    (A : Type u) [CommRing A] [IsWContractibleRing A] (e : Γ(W.left, ⊤) ≃+* A) :
    W.IsWeaklyContractible := by
  -- Let `q : V ⟶ W` with `q.left` surjective. The ring map
  -- `ρ := q.left.appTop : Γ(W.left, ⊤) ⟶ Γ(V.left, ⊤)` is ind-étale by
  -- `indEtale_appTop_of_proAffineEtale (proAffineEtale_hom q)`, flat (ind-étale maps are
  -- weakly étale, hence flat) and surjective on prime spectra (conjugate `q.left.base`
  -- by `isoSpec`), hence faithfully flat.
  -- Transfer along `e`: make `Γ(V.left, ⊤)` an `A`-algebra via `ρ.hom.comp e.symm`,
  -- which is again ind-étale and faithfully flat (composition with a ring isomorphism).
  -- `IsWContractibleRing.exists_retraction` provides `f : Γ(V.left, ⊤) →+* A` with
  -- `f.comp (ρ.hom.comp e.symm) = id`. Then `g := e.symm.toRingHom.comp f` satisfies
  -- `g.comp ρ.hom = RingHom.id`.
  -- The section of `q` is `s₀ := W.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g) ≫
  -- V.left.isoSpec.inv` (use `Scheme.isoSpec_hom_naturality` as in
  -- `exists_surjective_factorization_disjoint` in `Proetale/Topology/Comparison/`
  -- `Acyclicity.lean`), promoted to `s : W ⟶ V` by `MorphismProperty.Over.homMk` with
  -- the over-`S` compatibility from `MorphismProperty.Over.w q`, and `s ≫ q = 𝟙 W` is
  -- checked on `left` components via `MorphismProperty.Over.Hom.ext`.
  intro V q hq
  have hρInd : (q.left.appTop).hom.IndEtale :=
    indEtale_appTop_of_proAffineEtale (proAffineEtale_hom q)
  -- `q.left.appTop` is flat, being ind-étale.
  have hρFlat : (q.left.appTop).hom.Flat := by
    letI := (q.left.appTop).hom.toAlgebra
    haveI : Algebra.WeaklyEtale (Γ(W.left, ⊤)) (Γ(V.left, ⊤)) := hρInd.weaklyEtale
    exact inferInstanceAs (Module.Flat (Γ(W.left, ⊤)) (Γ(V.left, ⊤)))
  -- `q.left.appTop` is surjective on prime spectra: `Spec.map q.left.appTop` is conjugate
  -- to the surjective `q.left` via `isoSpec`.
  have hcomap : Function.Surjective (PrimeSpectrum.comap (q.left.appTop).hom) := by
    intro x
    obtain ⟨v, hv⟩ := hq.surj (W.left.isoSpec.inv.base x)
    have hv' : q.left.base v = W.left.isoSpec.inv.base x := hv
    refine ⟨V.left.isoSpec.hom.base v, ?_⟩
    have h1 : PrimeSpectrum.comap (q.left.appTop).hom (V.left.isoSpec.hom.base v) =
        (V.left.isoSpec.hom ≫ Spec.map q.left.appTop).base v := rfl
    have h2 : (V.left.isoSpec.hom ≫ Spec.map q.left.appTop).base v =
        (q.left ≫ W.left.isoSpec.hom).base v := by
      rw [Scheme.isoSpec_hom_naturality]
    have h3 : (q.left ≫ W.left.isoSpec.hom).base v =
        W.left.isoSpec.hom.base (q.left.base v) := rfl
    have h4 : W.left.isoSpec.hom.base (W.left.isoSpec.inv.base x) =
        (W.left.isoSpec.inv ≫ W.left.isoSpec.hom).base x := rfl
    have h5 : (W.left.isoSpec.inv ≫ W.left.isoSpec.hom).base x = x := by
      rw [Iso.inv_hom_id]
      simp
    rw [h1, h2, h3, hv', h4, h5]
  have hρFF : (q.left.appTop).hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hρFlat, hcomap⟩
  -- Transfer along `e` to the w-contractible ring `A`.
  have hbij : Function.Bijective e.symm.toRingHom := e.symm.bijective
  have heInd : e.symm.toRingHom.IndEtale := by
    letI := e.symm.toRingHom.toAlgebra
    haveI : Algebra.IsLocalIso A (Γ(W.left, ⊤)) := RingHom.IsLocalIso.of_bijective hbij
    exact inferInstanceAs (Algebra.IndEtale A (Γ(W.left, ⊤)))
  have heFF : e.symm.toRingHom.FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective hbij
  have hσInd : ((q.left.appTop).hom.comp e.symm.toRingHom).IndEtale :=
    RingHom.IndEtale.comp hρInd heInd
  have hσFF : ((q.left.appTop).hom.comp e.symm.toRingHom).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition _ _ heFF hρFF
  letI : Algebra A (Γ(V.left, ⊤)) := ((q.left.appTop).hom.comp e.symm.toRingHom).toAlgebra
  haveI : Algebra.IndEtale A (Γ(V.left, ⊤)) := hσInd
  haveI : Module.FaithfullyFlat A (Γ(V.left, ⊤)) := hσFF
  obtain ⟨f, hf⟩ := IsWContractibleRing.exists_retraction A (Γ(V.left, ⊤) : Type u)
  have hf' : f.comp ((q.left.appTop).hom.comp e.symm.toRingHom) = RingHom.id A := hf
  -- The retraction on global sections of `W`.
  have hretr : (e.symm.toRingHom.comp f).comp (q.left.appTop).hom =
      RingHom.id (Γ(W.left, ⊤)) := by
    ext x
    have h2 : ((q.left.appTop).hom.comp e.symm.toRingHom) (e x) = (q.left.appTop).hom x := by
      have h2a : e.symm.toRingHom (e x) = x := e.symm_apply_apply x
      calc ((q.left.appTop).hom.comp e.symm.toRingHom) (e x)
          = (q.left.appTop).hom (e.symm.toRingHom (e x)) := rfl
        _ = (q.left.appTop).hom x := by rw [h2a]
    have h1 : f (((q.left.appTop).hom.comp e.symm.toRingHom) (e x)) = e x :=
      RingHom.congr_fun hf' (e x)
    calc ((e.symm.toRingHom.comp f).comp (q.left.appTop).hom) x
        = e.symm.toRingHom (f ((q.left.appTop).hom x)) := rfl
      _ = e.symm.toRingHom (f (((q.left.appTop).hom.comp e.symm.toRingHom) (e x))) := by
          rw [h2]
      _ = e.symm.toRingHom (e x) := by rw [h1]
      _ = x := e.symm_apply_apply x
  have hgρ : q.left.appTop ≫ CommRingCat.ofHom (e.symm.toRingHom.comp f) =
      𝟙 (Γ(W.left, ⊤)) := by
    ext x
    exact RingHom.congr_fun hretr x
  -- The geometric section of `q.left`.
  have hqleft : q.left =
      V.left.isoSpec.hom ≫ Spec.map q.left.appTop ≫ W.left.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hs₀ : (W.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp f)) ≫
      V.left.isoSpec.inv) ≫ q.left = 𝟙 W.left := by
    rw [hqleft]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp_assoc, hgρ, Spec.map_id, Category.id_comp, Iso.hom_inv_id]
  have hw : (W.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp f)) ≫
      V.left.isoSpec.inv) ≫ V.hom = W.hom := by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, hs₀, Category.id_comp]
  refine ⟨MorphismProperty.Over.homMk
    (W.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp f)) ≫
      V.left.isoSpec.inv) hw trivial, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left]
  exact hs₀

/-- **The pro-étale site has enough weakly contractible objects** (BS, Proposition
4.2.8; blueprint `prop:proet-wc`, affine form): every object of the affine pro-étale
site of `S` admits a surjection from a weakly contractible object. -/
theorem exists_isWeaklyContractible_cover (U : S.AffineProEt) :
    ∃ (W : S.AffineProEt) (q : W ⟶ U), Surjective q.left ∧ W.IsWeaklyContractible := by
  -- Apply `exists_isWContractibleRing Γ(U.left, ⊤)` to obtain a faithfully flat
  -- ind-étale `A'` which is w-contractible. Let
  -- `q₀ := Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) A')) ≫ U.left.isoSpec.inv`
  -- and `W := AffineProEt.mk (q₀ ≫ U.hom) _` exactly as in the construction of the
  -- disjoint union in `exists_surjective_factorization_disjoint`
  -- (`Proetale/Topology/Comparison/Acyclicity.lean`, lines 60-70): `proAffineEtale q₀`
  -- via `proAffineEtale_Spec_iff` and the cancellation lemma for isomorphisms, and
  -- membership for the composite via `proAffineEtale.comp_mem`.
  -- `q := MorphismProperty.Over.homMk q₀ rfl trivial : W ⟶ U` is surjective since
  -- faithfully flat ring maps are surjective on prime spectra.
  -- `W` is weakly contractible by `isWeaklyContractible_of_isWContractibleRing` applied
  -- with the ring isomorphism `Γ(Spec A', ⊤) ≃+* A'` from `Scheme.ΓSpecIso`.
  obtain ⟨A', hCRA, hAlgA, hIndA, hFFA, hWCA⟩ :=
    exists_isWContractibleRing (Γ(U.left, ⊤) : Type u)
  letI := hCRA
  letI := hAlgA
  haveI := hIndA
  haveI := hFFA
  haveI := hWCA
  let φA : Γ(U.left, ⊤) ⟶ CommRingCat.of A' :=
    CommRingCat.ofHom (algebraMap (Γ(U.left, ⊤)) A')
  have hφA : φA.hom.IndEtale :=
    (RingHom.IndEtale.algebraMap_iff (R := (Γ(U.left, ⊤) : Type u)) A').mpr hIndA
  let q₀ : Spec (CommRingCat.of A') ⟶ U.left := Spec.map φA ≫ U.left.isoSpec.inv
  have hq₀ : proAffineEtale q₀ :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr hφA)
  let W : S.AffineProEt := mk (q₀ ≫ U.hom) (proAffineEtale.comp_mem _ _ hq₀ U.prop)
  let q : W ⟶ U := MorphismProperty.Over.homMk q₀ rfl trivial
  have hq₀surj : Function.Surjective q₀.base := by
    intro x
    obtain ⟨y, hy⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (B := A') (U.left.isoSpec.hom.base x)
    refine ⟨y, ?_⟩
    have h1 : q₀.base y = U.left.isoSpec.inv.base ((Spec.map φA).base y) := rfl
    have h2 : (Spec.map φA).base y =
        PrimeSpectrum.comap (algebraMap (Γ(U.left, ⊤)) A') y := rfl
    have h3 : U.left.isoSpec.inv.base (U.left.isoSpec.hom.base x) =
        (U.left.isoSpec.hom ≫ U.left.isoSpec.inv).base x := rfl
    have h4 : (U.left.isoSpec.hom ≫ U.left.isoSpec.inv).base x = x := by
      rw [Iso.hom_inv_id]
      simp
    rw [h1, h2, hy, h3, h4]
  exact ⟨W, q, ⟨hq₀surj⟩, isWeaklyContractible_of_isWContractibleRing A'
    ((Scheme.ΓSpecIso (CommRingCat.of A')).commRingCatIsoToRingEquiv)⟩

/-- Restriction of a section of an abelian sheaf along a composite is the composite of the
restrictions. -/
private lemma map_op_comp_apply (H : Sheaf (ProEt.topology S) Ab.{u + 1})
    {X Y Z : S.ProEt} (f : Y ⟶ X) (g : Z ⟶ Y) (t : H.obj.obj (op X)) :
    H.obj.map (g ≫ f).op t = H.obj.map g.op (H.obj.map f.op t) := by
  rw [op_comp, Functor.map_comp]
  exact ConcreteCategory.comp_apply _ _ _

variable (F : Sheaf (ProEt.topology S) Ab.{u + 1})

/-- Restriction to the pieces of a finite disjoint open decomposition is bijective on
sections of an abelian sheaf on the pro-étale site. This is a section-level reformulation
of `isIso_sigmaDesc_freeAbelianSheafFunctor_map`. -/
theorem bijective_sections_pi {W : S.AffineProEt}
    {ι : Type u} [Finite ι] (V : ι → S.AffineProEt) (j : ∀ k, V k ⟶ W)
    (hoi : ∀ k, IsOpenImmersion (j k).left)
    (hcov : ∀ x : W.left, ∃ k, x ∈ Set.range ((j k).left.base))
    (hdisj : Pairwise fun k l ↦ Disjoint (Set.range ((j k).left.base))
      (Set.range ((j l).left.base))) :
    Function.Bijective (fun (t : F.obj.obj (op ((AffineProEt.toProEt S).obj W))) k ↦
      F.obj.map ((AffineProEt.toProEt S).map (j k)).op t) := by
  -- By `isIso_sigmaDesc_freeAbelianSheafFunctor_map V j hoi hcov hdisj`
  -- (`Proetale/Topology/Comparison/Acyclicity.lean`), the canonical map
  -- `d : ∐ (fun k ↦ ℤ[V k]) ⟶ ℤ[W]` is an isomorphism, where `ℤ[-]` denotes
  -- `freeAbelianSheafFunctor (ProEt.topology S)` applied to the image in the pro-étale
  -- site. Precomposition with `d` is therefore a bijection
  -- `Hom(ℤ[W], F) ≃ Hom(∐ ℤ[V k], F)`, and `Hom(∐ ℤ[V k], F) ≃ ∀ k, Hom(ℤ[V k], F)` by
  -- the universal property of the coproduct (e.g. `Cofan.IsColimit.homEquiv` or a hand
  -- rolled equivalence via `Sigma.desc`/`Sigma.ι`). Translate both sides to sections via
  -- `freeAbelianSheafHomEquiv`
  -- (`Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/FreeAbelianSheaf.lean`) and
  -- identify the resulting map with restriction using
  -- `freeAbelianSheafHomEquiv_naturality_left`
  -- (`Proetale/Mathlib/CategoryTheory/Sites/SheafCohomology/LocallyVanish.lean`).
  classical
  haveI : IsIso (Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map (j k))) :=
    isIso_sigmaDesc_freeAbelianSheafFunctor_map V j hoi hcov hdisj
  let Fk : ι → Sheaf (ProEt.topology S) Ab.{u + 1} :=
    fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).obj ((AffineProEt.toProEt S).obj (V k))
  let d : (∐ Fk) ⟶
      (freeAbelianSheafFunctor (ProEt.topology S)).obj ((AffineProEt.toProEt S).obj W) :=
    Sigma.desc fun k ↦ (freeAbelianSheafFunctor (ProEt.topology S)).map
      ((AffineProEt.toProEt S).map (j k))
  haveI : IsIso d := by
    dsimp only [d]
    infer_instance
  -- Precomposition with the isomorphism `d` is a bijection on hom sets.
  have h1 : Function.Bijective (fun (s : (freeAbelianSheafFunctor (ProEt.topology S)).obj
      ((AffineProEt.toProEt S).obj W) ⟶ F) ↦ d ≫ s) := by
    constructor
    · intro s₁ s₂ hss
      exact (cancel_epi d).mp hss
    · intro r
      exact ⟨inv d ≫ r, by simp⟩
  -- Restriction of a hom from the coproduct to its components is a bijection onto
  -- families of sections, by the universal property and the sections equivalence.
  have h2 : Function.Bijective (fun (r : (∐ Fk) ⟶ F) k ↦
      freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)
        (Sigma.ι Fk k ≫ r)) := by
    constructor
    · intro r₁ r₂ hrr
      refine Sigma.hom_ext _ _ fun k ↦ ?_
      exact freeAbelianSheafHomEquiv.injective (congrFun hrr k)
    · intro p
      refine ⟨Sigma.desc fun k ↦
        (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)).symm
          (p k), ?_⟩
      funext k
      dsimp only
      rw [Sigma.ι_desc, Equiv.apply_symm_apply]
  -- The map of the statement is the composite of the three bijections.
  have key : (fun (t : F.obj.obj (op ((AffineProEt.toProEt S).obj W))) k ↦
        F.obj.map ((AffineProEt.toProEt S).map (j k)).op t) =
      (fun (r : (∐ Fk) ⟶ F) k ↦
          freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)
            (Sigma.ι Fk k ≫ r)) ∘
        (fun s ↦ d ≫ s) ∘
        (fun t ↦ (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W)
          (F := F)).symm t) := by
    funext t k
    have hι : Sigma.ι Fk k ≫ d =
        (freeAbelianSheafFunctor (ProEt.topology S)).map ((AffineProEt.toProEt S).map (j k)) :=
      Sigma.ι_desc _ k
    have hcompeq : Sigma.ι Fk k ≫ d ≫
        (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)).symm t =
        (freeAbelianSheafFunctor (ProEt.topology S)).map ((AffineProEt.toProEt S).map (j k)) ≫
          (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)).symm t := by
      rw [← Category.assoc, hι]
    have hnat : freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)
        ((freeAbelianSheafFunctor (ProEt.topology S)).map ((AffineProEt.toProEt S).map (j k)) ≫
          (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)).symm t) =
        F.obj.map ((AffineProEt.toProEt S).map (j k)).op
          (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)
            ((freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)).symm t)) :=
      freeAbelianSheafHomEquiv_naturality_left _ _
    rw [Equiv.apply_symm_apply] at hnat
    calc F.obj.map ((AffineProEt.toProEt S).map (j k)).op t
        = freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)
            ((freeAbelianSheafFunctor (ProEt.topology S)).map
              ((AffineProEt.toProEt S).map (j k)) ≫
              (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W)
                (F := F)).symm t) := hnat.symm
      _ = freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj (V k)) (F := F)
            (Sigma.ι Fk k ≫ d ≫
              (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W)
                (F := F)).symm t) := by rw [hcompeq]
  rw [key]
  exact (h2.comp h1).comp
    (freeAbelianSheafHomEquiv (U := (AffineProEt.toProEt S).obj W) (F := F)).symm.bijective

variable {F} {G : Sheaf (ProEt.topology S) Ab.{u + 1}}

/-- An epimorphism of abelian sheaves on the pro-étale site is surjective on sections
over weakly contractible objects. -/
theorem surjective_app_of_epi (φ : F ⟶ G) [Epi φ]
    {W : S.AffineProEt} (hW : W.IsWeaklyContractible) :
    Function.Surjective
      (ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W)))) := by
  -- `φ` is locally surjective by `Sheaf.isLocallySurjective_iff_epi'`. Let
  -- `t : G(W)`. The sieve `Presheaf.imageSieve φ.hom t` is covering, so by
  -- `exists_singleton_refinement` there are `q : W' ⟶ W` with `q.left` surjective and a
  -- finite disjoint open cover `j k : V k ⟶ W'` such that `t` restricted along
  -- `(toProEt S).map (j k ≫ q)` lifts to `u k : F(V k)`.
  -- Apply `exists_surjective_factorization_disjoint` to the jointly surjective family
  -- `(j k ≫ q : V k ⟶ W)` to obtain a single object `T`, a surjection `h : T ⟶ W`, and
  -- pieces `ĵ k : V k ⟶ T` with `ĵ k ≫ h = j k ≫ q`, open immersions, jointly
  -- surjective, pairwise disjoint.
  -- Since `W` is weakly contractible, `h` splits: `s : W ⟶ T`, `s ≫ h = 𝟙 W`.
  -- By `bijective_sections_pi F` over `T`, glue the `u k` to `u : F(T)` with
  -- `ĵ k`-restrictions `u k`. Then `φ(u) = h^* t` because both sides have equal
  -- restrictions to all pieces (`bijective_sections_pi G` injectivity; use naturality of
  -- `φ.hom`). Finally `t = (s ≫ h)^* t = s^* (h^* t) = s^* φ(u) = φ (s^* u)` (use
  -- `Functor.map_comp`, `op_comp` and naturality of `φ.hom`; beware of rewriting through
  -- `ConcreteCategory` coercions — use `ConcreteCategory.congr_hom` and `congrArg`
  -- chains instead of `rw` where needed).
  intro t
  haveI hls : Presheaf.IsLocallySurjective (ProEt.topology S) φ.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (A := Ab.{u + 1}) φ).2 inferInstance
  obtain ⟨W', q, ι, hfin, V, j, hq, hmem, hoi, hcov, hdisj⟩ :=
    exists_singleton_refinement W (hls.imageSieve_mem t)
  haveI := hfin
  -- Split the surjection `q` using weak contractibility of `W`.
  obtain ⟨s, hs⟩ := hW q hq
  -- Glue the local preimages of `t` over the pieces to a section of `F` over `W'`.
  obtain ⟨u, hu⟩ := (bijective_sections_pi F V j hoi hcov hdisj).2
    (fun k ↦ Presheaf.localPreimage φ.hom t ((AffineProEt.toProEt S).map (j k ≫ q)) (hmem k))
  have hu' : ∀ k, F.obj.map ((AffineProEt.toProEt S).map (j k)).op u =
      Presheaf.localPreimage φ.hom t ((AffineProEt.toProEt S).map (j k ≫ q)) (hmem k) :=
    fun k ↦ congrFun hu k
  -- `φ(u)` agrees with the restriction of `t` along `q`, since both restrict to the same
  -- sections on the pieces.
  have hφu : ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W'))) u =
      G.obj.map ((AffineProEt.toProEt S).map q).op t := by
    refine (bijective_sections_pi G V j hoi hcov hdisj).1 ?_
    funext k
    calc G.obj.map ((AffineProEt.toProEt S).map (j k)).op
          (ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W'))) u)
        = ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj (V k))))
            (F.obj.map ((AffineProEt.toProEt S).map (j k)).op u) :=
          (NatTrans.naturality_apply φ.hom ((AffineProEt.toProEt S).map (j k)).op u).symm
      _ = ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj (V k))))
            (Presheaf.localPreimage φ.hom t
              ((AffineProEt.toProEt S).map (j k ≫ q)) (hmem k)) := by rw [hu' k]
      _ = G.obj.map ((AffineProEt.toProEt S).map (j k ≫ q)).op t :=
          Presheaf.app_localPreimage φ.hom t _ (hmem k)
      _ = G.obj.map ((AffineProEt.toProEt S).map (j k) ≫ (AffineProEt.toProEt S).map q).op t :=
          by rw [Functor.map_comp]
      _ = G.obj.map ((AffineProEt.toProEt S).map (j k)).op
            (G.obj.map ((AffineProEt.toProEt S).map q).op t) :=
          map_op_comp_apply G _ _ t
  -- Conclude: `t` is the image of the restriction of `u` along the section `s`.
  refine ⟨F.obj.map ((AffineProEt.toProEt S).map s).op u, ?_⟩
  have h1 : ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W)))
      (F.obj.map ((AffineProEt.toProEt S).map s).op u) =
      G.obj.map ((AffineProEt.toProEt S).map s).op
        (ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W'))) u) :=
    NatTrans.naturality_apply φ.hom ((AffineProEt.toProEt S).map s).op u
  rw [h1, hφu]
  have h2 : G.obj.map ((AffineProEt.toProEt S).map s).op
      (G.obj.map ((AffineProEt.toProEt S).map q).op t) =
      G.obj.map ((AffineProEt.toProEt S).map s ≫ (AffineProEt.toProEt S).map q).op t :=
    (map_op_comp_apply G _ _ t).symm
  rw [h2, ← Functor.map_comp, hs, CategoryTheory.Functor.map_id, op_id,
    CategoryTheory.Functor.map_id]
  exact ConcreteCategory.id_apply t

/-- A morphism of abelian sheaves on the pro-étale site which is surjective on sections
over all weakly contractible objects is an epimorphism. -/
theorem epi_of_forall_surjective_app (φ : F ⟶ G)
    (h : ∀ (W : S.AffineProEt), W.IsWeaklyContractible →
      Function.Surjective
        (ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W))))) :
    Epi φ := by
  -- By `Sheaf.isLocallySurjective_iff_epi'` it suffices to show that `φ` is locally
  -- surjective. Fix `X : S.ProEt` and `t : G(X)`; we must show
  -- `Presheaf.imageSieve φ.hom t ∈ ProEt.topology S X`.
  -- The affine pro-étale site is a dense subsite (`AffineProEt.isCoverDense_toProEt`
  -- type results; see how `exists_singleton_refinement` uses
  -- `Functor.IsCoverDense.functorPullback_pushforward_covering` in
  -- `Proetale/Topology/Comparison/Acyclicity.lean`), so `X` admits a covering sieve
  -- generated by morphisms `f : (toProEt S).obj U ⟶ X` with `U : S.AffineProEt`. For
  -- each such `U` choose a weakly contractible cover `q : W ⟶ U`
  -- (`exists_isWeaklyContractible_cover`); the composites
  -- `(toProEt S).map q ≫ f` generate a covering sieve of `X` (use
  -- `GrothendieckTopology.bind`/transitivity, plus
  -- `generate_singleton_toProEt_map_mem` for the covering property of `q`).
  -- On each such composite the section `t` lifts by hypothesis `h`, so the image sieve
  -- contains this covering sieve and is itself covering
  -- (`GrothendieckTopology.superset_covering`).
  refine (Sheaf.isLocallySurjective_iff_epi' (A := Ab.{u + 1}) φ).1 ?_
  refine ⟨fun {X} t ↦ ?_⟩
  refine (ProEt.topology S).transitive
    (Functor.is_cover_of_isCoverDense (AffineProEt.toProEt S) (ProEt.topology S) X) _ ?_
  intro Y f hf
  obtain ⟨⟨U, lift, gmap, fac⟩⟩ := hf
  obtain ⟨W', qc, hqc, hW'⟩ := exists_isWeaklyContractible_cover U
  refine (ProEt.topology S).superset_covering ?_
    ((ProEt.topology S).pullback_stable lift (generate_singleton_toProEt_map_mem qc hqc))
  rintro Z gz ⟨Z', l, m, hm, hcomp⟩
  cases hm
  -- `t` restricted along the composite lifts to `F`, using surjectivity over the weakly
  -- contractible `W'`.
  obtain ⟨v, hv⟩ := h W' hW'
    (G.obj.map ((AffineProEt.toProEt S).map qc ≫ gmap).op t)
  refine ⟨F.obj.map l.op v, ?_⟩
  calc ConcreteCategory.hom (φ.hom.app (op Z)) (F.obj.map l.op v)
      = G.obj.map l.op
          (ConcreteCategory.hom (φ.hom.app (op ((AffineProEt.toProEt S).obj W'))) v) :=
        NatTrans.naturality_apply φ.hom l.op v
    _ = G.obj.map l.op
          (G.obj.map ((AffineProEt.toProEt S).map qc ≫ gmap).op t) := by rw [hv]
    _ = G.obj.map (l ≫ (AffineProEt.toProEt S).map qc ≫ gmap).op t :=
        (map_op_comp_apply G _ _ t).symm
    _ = G.obj.map (gz ≫ f).op t := by
        rw [← Category.assoc, hcomp, Category.assoc, fac]

end AlgebraicGeometry.Scheme.AffineProEt
