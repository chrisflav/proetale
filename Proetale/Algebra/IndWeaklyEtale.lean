import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.HenselianLocalRing

universe u

instance {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IndEtale R S] :
    Algebra.WeaklyEtale R S :=
  sorry

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
