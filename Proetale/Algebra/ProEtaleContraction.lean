/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.Contraction.Covers
import Proetale.Algebra.Etale
import Proetale.Algebra.IndEtale

/-!

-/

universe u

open CategoryTheory Opposite

variable {R : Type u} [CommRing R]

-- local instance to speed up instance search
instance (R : CommRingCatᵒᵖ) :
    Limits.HasLimitsOfShape
      (FiniteFamilies (SmallModel.{u} (CommRingCat.etale.op.Over ⊤ R)))ᵒᵖ (Over R) :=
  inferInstance

-- TODO: replace étale by étale and surjective on prime spectra
-- right now this is the zero ring
/-- The étale ind-contraction of a ring. This is defined
to be the contraction wrt. to the morphism property of étale ring homomorphisms. -/
def EtaleIndContraction (R : Type u) [CommRing R] : Type u :=
  (MorphismProperty.contraction.{u} CommRingCat.etale.op
    (op <| CommRingCat.of R) : CommRingCat.{u}ᵒᵖ).unop

noncomputable instance : CommRing (EtaleIndContraction R) := fast_instance%
  inferInstanceAs <| CommRing (_ : CommRingCat.{u})

noncomputable instance : Algebra R (EtaleIndContraction R) :=
  letI f : R →+* EtaleIndContraction R :=
    (MorphismProperty.Contraction.base CommRingCat.etale.op (op <| CommRingCat.of R)).unop.hom
  f.toAlgebra

/-- The ind-contraction of `R` is ind-étale over `R`. -/
instance : Algebra.IndEtale R (EtaleIndContraction R) := by
  rw [← RingHom.IndEtale.algebraMap_iff, RingHom.algebraMap_toAlgebra,
    RingHom.IndEtale.iff_ind_etale]
  dsimp only [CommRingCat.ofHom_hom]
  rw [MorphismProperty.ind_eq_unop_pro_op]
  dsimp only [MorphismProperty.unop.eq_1, Quiver.Hom.op_unop]
  apply MorphismProperty.pro_contractionBase
  grw [← MorphismProperty.op_isFinitelyPresentable, CommRingCat.etale_le_isFinitelyPresentable]

/-- Any étale ring homomorphism `EtaleIndContraction R →+* S` has a retraction. -/
lemma RingHom.Etale.exists_comp_eq_id_indContraction {S : Type u} [CommRing S]
    (f : EtaleIndContraction R →+* S) (hf : f.Etale) :
    ∃ (g : S →+* EtaleIndContraction R), g.comp f = .id (EtaleIndContraction R) := by
  have : MorphismProperty.PreProSpreads.{0} CommRingCat.etale.op := by
    rw [MorphismProperty.PreProSpreads.op_iff]
    exact MorphismProperty.PreIndSpreads.of_univLE.{u} _
  obtain ⟨g, hg⟩ := MorphismProperty.exists_comp_eq_id_contraction CommRingCat.etale.op _
    (CommRingCat.ofHom f).op hf
  use g.unop.hom
  exact congr($(hg).unop.hom)
