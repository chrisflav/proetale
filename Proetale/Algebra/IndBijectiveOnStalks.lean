import Proetale.Algebra.StalkIso
import Proetale.Algebra.IndZariski
import Proetale.Algebra.WLocal

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A w-local ring map between w-local spaces that is bijective on stalks is ind-Zariski. -/
lemma RingHom.BijectiveOnStalks.indZariski_of_isWLocal {f : R →+* S} [IsWLocalRing R]
    [IsWLocalRing S] (hf : f.IsWLocal) (hf' : f.BijectiveOnStalks) :
    f.IndZariski :=
  sorry

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
