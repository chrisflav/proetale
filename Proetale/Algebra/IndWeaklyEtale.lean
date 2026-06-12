import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.HenselianLocalRing
import Proetale.Mathlib.RingTheory.Flat.FilteredColimit

universe u

open CategoryTheory Limits

/-- Every ind-étale algebra is weakly étale: étale algebras are weakly étale and weak étaleness
is stable under filtered colimits. -/
instance {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IndEtale R S] :
    Algebra.WeaklyEtale R S := by
  obtain ⟨ι, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  have hflat (i : ι) : Module.Flat R (P.diag.obj i) := by
    haveI : Algebra.Etale R (P.diag.obj i) := hP i
    exact (inferInstance : Algebra.WeaklyEtale R (P.diag.obj i)).flat
  have hlmul (i : ι) : (Algebra.TensorProduct.lmul' R (S := P.diag.obj i)).Flat := by
    haveI : Algebra.Etale R (P.diag.obj i) := hP i
    exact Algebra.WeaklyEtale.flat_lmul' R (P.diag.obj i)
  refine ⟨?_, ?_⟩
  · -- `Module.Flat R S`: transfer the `CommAlgCat`-level presentation to `ModuleCat`.
    rw [← CommAlgCat.flat_iff (S := .of R S), CommAlgCat.flat,
        ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
        ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨ι, ‹_›, ‹_›, P, fun i ↦ ?_⟩
    exact CommAlgCat.flat_iff.mpr (hflat i)
  · exact RingHom.Flat.of_filteredColim_lmul' P hlmul

lemma RingHom.IndEtale.weaklyEtale {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IndEtale) :
    f.WeaklyEtale := by
  algebraize [f]
  rw [← RingHom.algebraMap_toAlgebra f, weaklyEtale_algebraMap_iff]
  infer_instance

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra. -/
theorem Algebra.WeaklyEtale.exists_indEtale (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [WeaklyEtale R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      IndEtale S T ∧ Module.FaithfullyFlat S T ∧ IndEtale R T :=
  sorry

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra. -/
theorem RingHom.WeaklyEtale.exists_indEtale_comp {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.WeaklyEtale) :
    ∃ (T : Type u) (_ : CommRing T) (g : S →+* T),
      g.IndEtale ∧ g.FaithfullyFlat ∧ (g.comp f).IndEtale := by
  algebraize [f]
  obtain ⟨T, _, _, _, _, h₁, h₂, h₃⟩ := Algebra.WeaklyEtale.exists_indEtale R S
  refine ⟨T, inferInstance, algebraMap S T, ?_, ?_, ?_⟩
  · rwa [IndEtale.algebraMap_iff]
  · rwa [faithfullyFlat_algebraMap_iff]
  · rwa [← RingHom.algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq, IndEtale.algebraMap_iff]
