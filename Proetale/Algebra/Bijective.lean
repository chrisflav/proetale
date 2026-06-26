import Proetale.Algebra.WeaklyEtale
import Proetale.Mathlib.Logic.Function.Basic

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

open TensorProduct

namespace Algebra

/-- If all residue field extensions are trivial and the map on prime spectra is
bijective, the map `Spec S ⟶ Spec (S ⊗[R] S)` is bijective. -/
lemma bijective_comap_lmul'_of_bijective_of_bijective
    (hf : Function.Bijective (PrimeSpectrum.comap (algebraMap R S)))
    (h : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (PrimeSpectrum.comap <| (TensorProduct.lmul' (S := S) R).toRingHom) := by
  set μ : S ⊗[R] S →+* S := (TensorProduct.lmul' (S := S) R).toRingHom with hμdef
  set ι₁ : S →+* S ⊗[R] S :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).toRingHom with hι₁def
  set ι₂ : S →+* S ⊗[R] S :=
    (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom with hι₂def
  have hμsurj : Function.Surjective μ := fun s ↦ ⟨ι₁ s, by simp [hμdef, hι₁def]⟩
  have hcommfun : ∀ r : R, ι₁ (algebraMap R S r) = ι₂ (algebraMap R S r) := fun r ↦
    ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).commutes r).trans
      ((Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).commutes r).symm
  have hcomm : ι₁.comp (algebraMap R S) = ι₂.comp (algebraMap R S) :=
    RingHom.ext hcommfun
  -- `lmul'` is surjective (it has the section `includeLeft`), hence `Spec (lmul')` is injective.
  refine ⟨PrimeSpectrum.comap_injective_of_surjective μ hμsurj, fun P ↦ ?_⟩
  -- For surjectivity, let `P` be a prime of `S ⊗[R] S`. Its two pullbacks to `S` agree,
  -- since `Spec S → Spec R` is injective.
  set q : Ideal S := P.asIdeal.comap ι₁ with hq₁
  have hq₂ : q = P.asIdeal.comap ι₂ := by
    have heq : PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap ι₁ P) =
        PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap ι₂ P) := by
      apply PrimeSpectrum.ext
      simp [Ideal.comap_comap, hcomm]
    exact hq₁.trans (congrArg PrimeSpectrum.asIdeal (hf.injective heq))
  have hqprime : q.IsPrime := by
    rw [hq₁]
    infer_instance
  set p : Ideal R := q.comap (algebraMap R S) with hp
  have : q.LiesOver p := ⟨hp⟩
  -- The two induced maps `κ(q) → κ(P)` agree, since both restrict to the same map on
  -- `κ(p)` and `κ(p) → κ(q)` is surjective.
  have hρ : Function.Bijective (Ideal.ResidueField.map p q (algebraMap R S) hp) := h p q
  have hcomp : (Ideal.ResidueField.map q P.asIdeal ι₁ hq₁).comp
        (Ideal.ResidueField.map p q (algebraMap R S) hp) =
      (Ideal.ResidueField.map q P.asIdeal ι₂ hq₂).comp
        (Ideal.ResidueField.map p q (algebraMap R S) hp) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p))
    rw [← RingHom.cancel_right (Ideal.Quotient.mk_surjective (I := p))]
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply,
      Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap]
    rw [hcommfun r]
  have hψ : Ideal.ResidueField.map q P.asIdeal ι₁ hq₁ =
      Ideal.ResidueField.map q P.asIdeal ι₂ hq₂ := by
    refine RingHom.ext fun x ↦ ?_
    obtain ⟨y, rfl⟩ := hρ.surjective x
    exact congr($hcomp y)
  have hkey : ∀ s : S, algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ s) =
      algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₂ s) := by
    intro s
    rw [← Ideal.ResidueField.map_algebraMap q P.asIdeal ι₁ hq₁ s,
      ← Ideal.ResidueField.map_algebraMap q P.asIdeal ι₂ hq₂ s, hψ]
  -- Hence every element of `S ⊗[R] S` has the same image in `κ(P)` as the image of its
  -- product under `includeLeft`.
  have hχ : ∀ x : S ⊗[R] S, algebraMap (S ⊗[R] S) P.asIdeal.ResidueField x =
      algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ (μ x)) := by
    intro x
    induction x with
    | zero => simp
    | tmul s t =>
      calc algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (s ⊗ₜ[R] t)
          = algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ s) *
            algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₂ t) := by
            rw [← map_mul]
            congr 1
            simp [hι₁def, hι₂def]
        _ = algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ s) *
            algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ t) := by rw [hkey t]
        _ = algebraMap (S ⊗[R] S) P.asIdeal.ResidueField (ι₁ (μ (s ⊗ₜ[R] t))) := by
            rw [← map_mul, ← map_mul]
            congr 2
    | add x y hx hy => simp [hx, hy]
  -- Conclude that `P` is the pullback of `q` along `lmul'`.
  refine ⟨PrimeSpectrum.comap ι₁ P, PrimeSpectrum.ext ?_⟩
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  rw [← Ideal.algebraMap_residueField_eq_zero (I := P.asIdeal) (x := ι₁ (μ x)),
    ← Ideal.algebraMap_residueField_eq_zero (I := P.asIdeal) (x := x), ← hχ x]

/-- A flat surjective map `R → S` that is bijective on prime spectra is an isomorphism. -/
lemma bijective_of_bijective_of_flat [Module.Flat R S]
    (hf : Function.Bijective (PrimeSpectrum.comap (algebraMap R S)))
    (hf' : Function.Surjective (algebraMap R S)) :
    Function.Bijective (algebraMap R S) := by
  refine ⟨?_, hf'⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  have e : (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := (algebraMap R S).quotientKerEquivOfSurjective hf') fun _ ↦ rfl
  have hker : (RingHom.ker (algebraMap R S)).Pure := Module.Flat.of_linearEquiv e.toLinearEquiv
  have hbot : (⊥ : Ideal R).Pure := Module.Flat.of_linearEquiv (Submodule.quotEquivOfEqBot ⊥ rfl)
  rw [← Ideal.zeroLocus_inj_of_pure, PrimeSpectrum.zeroLocus_bot, Set.eq_univ_iff_forall]
  intro p
  obtain ⟨q, rfl⟩ := hf.surjective p
  rw [PrimeSpectrum.mem_zeroLocus]
  intro x hx
  rw [SetLike.mem_coe, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    RingHom.mem_ker.mp hx]
  exact q.asIdeal.zero_mem

/-- A faithfully flat epimorphism `R → S` is an isomorphism. -/
lemma bijective_of_faithfullyFlat_of_isEpi [Module.FaithfullyFlat R S] [Algebra.IsEpi R S] :
    Function.Bijective (algebraMap R S) :=
  sorry

lemma bijective_of_bijective_residueFieldMap [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (h : Function.Bijective (PrimeSpectrum.comap <| algebraMap R S))
    (h : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (algebraMap R S) :=
  sorry

/-- Let `R → S` be a weakly étale local homomorphism of local rings.  If for every prime
`p ⊂ R` there is a unique prime `q ⊂ S` lying over `p` and `κ(p) = κ(q)`, then `R → S` is
an isomorphism. -/
lemma WeaklyEtale.bijective_algebraMap_of_bijective_residueFieldMap
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.WeaklyEtale R S]
    (h : Function.Bijective (PrimeSpectrum.comap <| algebraMap R S))
    (hres : ∀ (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p],
      Function.Bijective
        (IsLocalRing.ResidueField.map (Localization.localRingHom p q (algebraMap R S)
          ‹q.LiesOver p›.over))) :
    Function.Bijective (algebraMap R S) := by
  have hff : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  -- The multiplication map `S ⊗[R] S → S` is flat, surjective and bijective on prime
  -- spectra, hence bijective.
  have hμ : Function.Bijective (TensorProduct.lmul' (S := S) R) := by
    have hflat := WeaklyEtale.flat_lmul' R S
    algebraize [(TensorProduct.lmul' (S := S) R).toRingHom]
    have halg : algebraMap (S ⊗[R] S) S = (TensorProduct.lmul' (S := S) R).toRingHom :=
      RingHom.algebraMap_toAlgebra _
    have hsurj : Function.Surjective (algebraMap (S ⊗[R] S) S) := by
      rw [halg]
      refine fun s ↦ ⟨s ⊗ₜ 1, ?_⟩
      simp [TensorProduct.lmul'_apply_tmul]
    have hbij : Function.Bijective (PrimeSpectrum.comap (algebraMap (S ⊗[R] S) S)) := by
      rw [halg]
      exact bijective_comap_lmul'_of_bijective_of_bijective h hres
    have := bijective_of_bijective_of_flat (R := S ⊗[R] S) (S := S) hbij hsurj
    rwa [halg] at this
  -- Hence `includeLeft : S → S ⊗[R] S` is bijective, being a section of `lmul'`.
  have hone : ∀ s : S, TensorProduct.lmul' (S := S) R (s ⊗ₜ[R] 1) = s := fun s ↦ by
    rw [TensorProduct.lmul'_apply_tmul, mul_one]
  have hinc : Function.Bijective fun s : S ↦ (s ⊗ₜ[R] 1 : S ⊗[R] S) :=
    Function.bijective_of_leftInverse_of_bijective hone hμ
  -- Faithfully flat descent of surjectivity: `S ⊗[R] R → S ⊗[R] S` is surjective, hence
  -- so is `R → S`.
  have hsurj : Function.Surjective (algebraMap R S) := by
    have hT : Function.Surjective ⇑(LinearMap.lTensor S (Algebra.linearMap R S)) := by
      intro y
      obtain ⟨s, rfl⟩ := hinc.surjective y
      refine ⟨s ⊗ₜ 1, ?_⟩
      simp
    exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S
      (Algebra.linearMap R S)).mp hT
  exact bijective_of_bijective_of_flat h hsurj

end Algebra
