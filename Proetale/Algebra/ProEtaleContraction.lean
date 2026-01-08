/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.Contraction.Covers
import Proetale.Algebra.IndEtale
import Proetale.FromPi1.Etale

/-!
# Constructing ind-étale algebras

In this file we construct for any ring `R` an ind-étale, faithfully flat `R`-algebra
`IndEtaleContraction R` such that any faithfully flat, étale ring homomorphism
`IndEtaleContraction R →+* S` has a retraction.
-/

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R]

-- local instance to speed up instance search
instance (R : CommRingCat.{u}ᵒᵖ) :
    Limits.HasLimitsOfShape
      (FiniteFamilies (SmallModel.{u}
      ((CommRingCat.etale.op ⊓ CommRingCat.faithfullyFlat.op).Over ⊤ R)))ᵒᵖ (Over R) :=
  inferInstance

/-- The étale ind-contraction of a ring. This is defined
to be the contraction wrt. to the morphism property of étale ring homomorphisms. -/
def IndEtaleContraction (R : Type u) [CommRing R] : Type u :=
  (MorphismProperty.contraction.{u}
    CommRingCat.etale.op
    CommRingCat.faithfullyFlat.op
    (op <| CommRingCat.of R) : CommRingCat.{u}ᵒᵖ).unop

noncomputable instance : CommRing (IndEtaleContraction R) := fast_instance%
  inferInstanceAs <| CommRing (_ : CommRingCat.{u})

noncomputable instance : Algebra R (IndEtaleContraction R) :=
  letI f : R →+* IndEtaleContraction R :=
    (MorphismProperty.Contraction.base _ _ (op <| CommRingCat.of R)).unop.hom
  f.toAlgebra

/-- The ind-contraction of `R` is ind-étale over `R`. -/
instance indEtale_indEtaleContraction : Algebra.IndEtale R (IndEtaleContraction R) := by
  rw [← RingHom.IndEtale.algebraMap_iff, RingHom.algebraMap_toAlgebra,
    RingHom.IndEtale.iff_ind_etale]
  dsimp only [CommRingCat.ofHom_hom]
  rw [MorphismProperty.ind_eq_unop_pro_op]
  dsimp only [MorphismProperty.unop.eq_1, Quiver.Hom.op_unop]
  apply MorphismProperty.pro_contractionBase
  grw [← MorphismProperty.op_isFinitelyPresentable, CommRingCat.etale_le_isFinitelyPresentable]

instance faithfullyFlat_indEtaleContraction : Module.FaithfullyFlat R (IndEtaleContraction R) := by
  rw [← RingHom.faithfullyFlat_algebraMap_iff, RingHom.algebraMap_toAlgebra]
  have heq : MorphismProperty.pro.{u} CommRingCat.faithfullyFlat.{u}.op =
      CommRingCat.faithfullyFlat.{u}.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  exact MorphismProperty.prop_contractionπ
    CommRingCat.etale.op CommRingCat.faithfullyFlat.op heq (op <| .of R) 0

/-- Any étale ring homomorphism `IndEtaleContraction R →+* S` has a retraction. -/
lemma RingHom.Etale.exists_comp_eq_id_indContraction {S : Type u} [CommRing S]
    (f : IndEtaleContraction R →+* S) (hf : f.Etale)
    (hf' : Function.Surjective (PrimeSpectrum.comap f)) :
    ∃ (g : S →+* IndEtaleContraction R), g.comp f = .id (IndEtaleContraction R) := by
  have : MorphismProperty.PreProSpreads.{0} CommRingCat.etale.op := by
    rw [MorphismProperty.PreProSpreads.op_iff]
    exact MorphismProperty.PreIndSpreads.of_univLE.{u} _
  have hf' : f.FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    exact ⟨hf.smooth.flat, hf'⟩
  have heq : MorphismProperty.pro.{u} CommRingCat.faithfullyFlat.{u}.op =
      CommRingCat.faithfullyFlat.{u}.op := by
    conv_rhs => rw [← CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat]
    rw [MorphismProperty.ind_eq_unop_pro_op, MorphismProperty.op_unop]
  obtain ⟨g, hg⟩ := MorphismProperty.exists_comp_eq_id_contraction
    CommRingCat.etale.op _ _ heq
    (fun {R S T} f g hfg hf hg ↦ by
      rw [CommRingCat.faithfullyFlat_eq] at ⊢ hfg
      refine ⟨?_, ?_⟩
      · exact hg.smooth.flat
      · apply Function.Surjective.of_comp (g := PrimeSpectrum.comap f.1.hom)
        exact hfg.2)
    (CommRingCat.ofHom f).op hf hf'
  use g.unop.hom
  exact congr($(hg).unop.hom)
