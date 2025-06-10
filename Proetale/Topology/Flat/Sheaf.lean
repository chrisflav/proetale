/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Flat.QuasiCompactCover
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.CategoryTheory.EffectiveEpi.Basic
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# The fpqc topology is subcanonical

In this file we show that the fqpc topology of a scheme is subcanonical. This implies that
all coarser topologies, e.g., the (pro)étale topology, are subcanonical.
-/

universe v u

open CategoryTheory Limits

namespace CategoryTheory

instance {C : Type*} [Category C] : (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

variable {C : Type*} [Category C] {X : C}

lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Sieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.arrows.IsSheafFor (yoneda.obj Y) :=
  S.forallYonedaIsSheaf_iff_colimit.symm

lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda (S : Presieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.IsSheafFor (yoneda.obj Y) := by
  simp_rw [Presieve.isSheafFor_iff_generate S]
  rw [Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

-- TODO: this is almost in mathlib, with slightly less general universe assumptions on `F`
-- and with a wrong name
lemma Presieve.IsSheafFor.of_isSheafFor_pullback'' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Sieve X)
    (hF : Presieve.IsSheafFor F S.arrows)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F (S.pullback f).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Y Z f g hf
    refine (H (g ≫ f) (by simp [hf])).isSeparatedFor.ext fun U o ho ↦ ?_
    simp only [Sieve.pullback_apply] at ho
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hs _ _ _ ho, hs _ _ _ (by simpa)]
    congr 1
    simp
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp, ht' (g ≫ f) hg, ← t.comp_of_compatible _ ht]
    have := hs (g ≫ f) hg (𝟙 _)
    dsimp only [Presieve.FamilyOfElements.IsAmalgamation,
      Presieve.FamilyOfElements.pullback] at this
    simp only [Sieve.pullback_apply, Category.id_comp, op_id, FunctorToTypes.map_id_apply] at this
    rw [this]
    · congr 1
      simp
    · simp [hf]
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback
    (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S : Presieve X) (T : Sieve X) [S.hasPullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := hasPullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F (T.pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [pullbackCompatible_iff]
    intro Y Z f g hf hg
    haveI := hasPullbacks.has_pullbacks hf hg
    obtain ⟨R, hR, h⟩ := H' f g hf hg
    refine hR.ext fun W w hw ↦ (h w hw).ext fun U u hu ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, Category.assoc]
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [hs f hf (u ≫ w ≫ pullback.fst f g) (by simpa),
      hs g hg (u ≫ w ≫ pullback.snd f g) (by simpa [← pullback.condition])]
    congr 1
    simp [pullback.condition]
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [Sieve.pullback_apply, Sieve.generate_apply] at hg
    obtain ⟨W, w, u, hu, heq⟩ := hg
    simp only [← heq, op_comp, FunctorToTypes.map_comp_apply, ht' u hu]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ u) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    rw [← t.comp_of_compatible _ ht, this]
    apply hs
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Presieve X) [S.hasPullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := hasPullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F ((Sieve.generate T).pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F ((Sieve.generate T).pullback f).arrows) :
    Presieve.IsSheafFor F T := by
  rw [isSheafFor_iff_generate]
  apply Presieve.IsSheafFor.of_isSheafFor_pullback F S _ _ hF'
  · assumption
  · assumption
  · assumption

-- this needs more assumptions, but the proof will show which the correct ones are
lemma Presieve.isSheafFor_ofArrows_comp {F : Cᵒᵖ ⥤ Type*} {ι : Type*} {Y Z : ι → C}
    (f : ∀ i, Y i ⟶ X) (g : ∀ i, Z i ⟶ X)
    (e : ∀ i, Y i ≅ Z i) (H : Presieve.IsSheafFor F (.ofArrows _ g)) :
    Presieve.IsSheafFor F (.ofArrows _ (fun i ↦ (e i).hom ≫ g i)) := by
  let B (W : C) (w : W ⟶ X) (hw : Presieve.ofArrows _ g w) : Sieve W :=
    sorry
  have : .ofArrows _ (fun i ↦ (e i).hom ≫ g i) = Sieve.bind (.ofArrows _ g) B :=
    sorry
  rw [Presieve.isSheafFor_iff_generate, ← Sieve.ofArrows, this]
  sorry

end CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}}

@[simp]
lemma Scheme.Cover.pullbackArrows_ofArrows [P.IsStableUnderBaseChange] {X S : Scheme.{u}}
    (𝒰 : S.Cover P) (f : X ⟶ S) :
    (Presieve.ofArrows 𝒰.obj 𝒰.map).pullbackArrows f =
      .ofArrows (𝒰.pullbackCover' f).obj (𝒰.pullbackCover' f).map := by
  rw [← Presieve.ofArrows_pullback]
  rfl

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_grothendieckTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} P S) :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ Scheme.grothendieckTopology P S := by
  rw [grothendieckTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, rfl⟩, Sieve.le_generate _⟩

open Scheme

def qcPretopology (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : Pretopology Scheme.{u} where
  coverings Y S := ∃ (𝒰 : Cover.{u} P Y) (h : 𝒰.QuasiCompact), S = Presieve.ofArrows 𝒰.obj 𝒰.map
  has_isos _ _ f _ := ⟨coverOfIsIso f, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h𝒰, rfl⟩
    exact ⟨𝒰.pullbackCover' f, inferInstance, (Presieve.ofArrows_pullback _ _ _).symm⟩
  transitive := by
    rintro X _ T ⟨𝒰, h𝒰, rfl⟩ H
    choose 𝒱 hc𝒱 h𝒱 using H
    refine ⟨𝒰.bind (fun j ↦ 𝒱 (𝒰.map j) ⟨j⟩), inferInstance, ?_⟩
    simpa only [Cover.bind, ← h𝒱] using Presieve.ofArrows_bind 𝒰.obj 𝒰.map _
      (fun _ f H => (𝒱 f H).obj) (fun _ f H => (𝒱 f H).map)

abbrev fpqcPretopology : Pretopology Scheme.{u} := qcPretopology @Flat

abbrev qcTopology (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : GrothendieckTopology Scheme.{u} := (qcPretopology P).toGrothendieck

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_qcTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} P S) [𝒰.QuasiCompact] :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ qcTopology P S := by
  rw [qcTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, ‹_›, rfl⟩, Sieve.le_generate _⟩

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

/-- The fqpc-topology on the category of schemes is the Grothendieck topology associated
to the pretopology given by fqpc-covers. -/
abbrev fpqcTopology : GrothendieckTopology Scheme.{u} := fpqcPretopology.toGrothendieck

lemma zariskiTopology_le_qcTopology [IsLocalAtSource P] :
    zariskiTopology ≤ qcTopology P := by
  rw [qcTopology, zariskiTopology, (Pretopology.gi _).gc.le_iff_le]
  rintro S R ⟨𝒰, rfl⟩
  rw [Pretopology.mem_ofGrothendieck]
  let 𝒰' : Cover P S := 𝒰.changeProp P (fun j ↦ IsLocalAtSource.of_isOpenImmersion _)
  have : 𝒰'.QuasiCompact := ⟨(inferInstanceAs <| 𝒰.QuasiCompact).1⟩
  exact 𝒰'.generate_ofArrows_mem_qcTopology

variable {P} in
@[simps!]
noncomputable
def Scheme.Hom.cover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] : Cover.{v} P S :=
  .mkOfCovers PUnit.{v + 1} (fun _ ↦ X) (fun _ ↦ f) (fun x ↦ ⟨⟨⟩, f.surjective x⟩) (fun _ ↦ hf)

instance {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] [QuasiCompact f] :
    (f.cover hf).QuasiCompact :=
  sorry

lemma ofArrows_homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] :
    Presieve.ofArrows (f.cover hf).obj (f.cover hf).map = Presieve.singleton f :=
  sorry

open Opposite

@[simps!]
noncomputable
def Scheme.affineCover' (X : Scheme.{u}) : X.OpenCover :=
  .mkOfCovers X.affineOpens (fun i ↦ i.1) (fun i ↦ i.1.ι) fun x ↦ by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)
      (show x ∈ ⊤ from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

variable {P}

lemma Cover.QuasiCompact.exists_hom {S : Scheme.{u}} (𝒰 : S.Cover P)
    [CompactSpace S] [𝒰.QuasiCompact] :
    ∃ (𝒱 : S.AffineCover P) (f : 𝒱.cover ⟶ 𝒰), Finite 𝒱.J ∧ ∀ j, IsOpenImmersion (f.app j) :=
  sorry

lemma Scheme.Cover.Hom.isSheafFor {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S : Scheme.{u}} {𝒰 𝒱 : S.Cover P}
    (f : 𝒰 ⟶ 𝒱)
    (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.map))
    (H₂ : ∀ {X : Scheme.{u}} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullbackCover' f).obj (𝒰.pullbackCover' f).map)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.obj 𝒱.map) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.obj 𝒰.map))
  · show Sieve.generate _ ≤ Sieve.generate _
    rw [Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    rw [← f.w]
    exact ⟨_, f.app i, 𝒱.map _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
    rw [← Presieve.ofArrows_pullback]
    apply H₂

lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type*} [IsLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover P) :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.obj 𝒰.sigma.map) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.obj 𝒰.map) :=
  sorry

lemma Scheme.Cover.ofArrows_of_unique {S : Scheme.{u}} (𝒰 : S.Cover P) [Unique 𝒰.J] :
    Presieve.ofArrows 𝒰.obj 𝒰.map = Presieve.singleton (𝒰.map default) :=
  sorry

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.J] :
    𝒰.cover.QuasiCompact :=
  sorry

lemma isSheafFor_iff_of_iso {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (e : X ≅ Y) (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    (he : e.hom ≫ g = f) :
    Presieve.IsSheafFor F (.singleton f) ↔ Presieve.IsSheafFor F (.singleton g) := by
  subst he
  refine ⟨fun hf ↦ ?_, ?_⟩
  · sorry
  · sorry

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`.-/
@[stacks 022H]
nonrec lemma isSheaf_qcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) [IsLocalAtSource P] :
    Presieve.IsSheaf (qcTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_qcTopology P) hF
  · apply hF.isSheafFor
    rw [← ofArrows_homCover P _ hf]
    exact Cover.generate_ofArrows_mem_qcTopology _
  · rw [Presieve.isSheaf_pretopology]
    rintro T - ⟨𝒰, _, rfl⟩
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · let 𝒱 : T.OpenCover := T.affineCover
      have h (j : T.affineCover.J) : Presieve.IsSheafFor F
          (.ofArrows (𝒰.pullbackCover' (𝒱.map j)).obj (𝒰.pullbackCover' (𝒱.map j)).map) :=
        this _ inferInstance ⟨_, rfl⟩
      refine .of_isSheafFor_pullback' F (.ofArrows 𝒱.obj 𝒱.map) _ ?_ ?_ ?_ ?_
      · exact hzar.isSheafFor _ _ 𝒱.generate_ofArrows_mem_grothendieckTopology
      · intro Y f
        refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
        rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm, Cover.pullbackArrows_ofArrows]
        exact (Cover.pullbackCover' 𝒱 f).generate_ofArrows_mem_grothendieckTopology
      · rintro - - - - ⟨i⟩ ⟨j⟩
        use .ofArrows (pullback (𝒱.map i) (𝒱.map j)).affineCover.obj
          (pullback (𝒱.map i) (𝒱.map j)).affineCover.map
        refine ⟨(hzar.isSheafFor _ _ <|
            Cover.generate_ofArrows_mem_grothendieckTopology _).isSeparatedFor, ?_⟩
        · rintro - - ⟨k⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
          apply Presieve.IsSheafFor.isSeparatedFor
          rw [← Presieve.ofArrows_pullback]
          exact this (𝒰.pullbackCover' _) inferInstance ⟨_, rfl⟩
      · rintro - - ⟨i⟩
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullbackCover' (𝒱.map i)) inferInstance ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.obj i)) ∧ Finite 𝒰.J generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := Cover.QuasiCompact.exists_hom 𝒰
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullbackCover' f).obj (𝒱.cover.pullbackCover' f).map) := by
        let 𝒰V := V.affineCover
        refine .of_isSheafFor_pullback' F (.ofArrows 𝒰V.obj 𝒰V.map) _ ?_ ?_ ?_ ?_
        · exact hzar.isSheafFor _ _ 𝒰V.generate_ofArrows_mem_grothendieckTopology
        · intro Y f
          refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
          rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm, Cover.pullbackArrows_ofArrows]
          exact (Cover.pullbackCover' 𝒰V f).generate_ofArrows_mem_grothendieckTopology
        · rintro - - - - ⟨i⟩ ⟨j⟩
          refine ⟨.ofArrows _ (pullback (𝒰V.map i) (𝒰V.map j)).affineCover.map, ?_, ?_⟩
          · exact hzar.isSheafFor _ _
              (Cover.generate_ofArrows_mem_grothendieckTopology _) |>.isSeparatedFor
          · rintro - - ⟨k⟩
            rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
              ← Presieve.isSeparatedFor_iff_generate]
            refine (this _ ((𝒱.cover.pullbackCover' f).pullbackCover' _) inferInstance
              ⟨fun l ↦ ?_, hfin⟩).isSeparatedFor
            exact .of_isIso (pullbackLeftPullbackSndIso (𝒱.map l) f _).hom
        · rintro - - ⟨i⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullbackCover' f).pullbackCover' (𝒰V.map i)
          refine this _ 𝒰' inferInstance
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.map j) f (𝒰V.map i)).hom, hfin⟩
      refine f.isSheafFor ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ _ inferInstance ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.sigma
    rw [← Scheme.Cover.isSheafFor_sigma_iff hzar, Scheme.Cover.ofArrows_of_unique]
    have : IsAffine (𝒰.sigma.obj default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.sigma.obj default).isoSpec.inv ≫ 𝒰.sigma.map default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [isSheafFor_iff_of_iso _ (Spec.map φ) (𝒰.sigma.obj default).isoSpec hzar (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsLocalAtSource.comp (𝒰.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_J, PUnit.default_eq_unit, Cover.sigma_obj, Cover.sigma_map, f]
      infer_instance

lemma isSheaf_fpqcTopology_iff (F : Scheme.{u}ᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf fpqcTopology F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S) (_ : f.hom.Flat) (_ : Surjective (Spec.map f)),
          Presieve.IsSheafFor F (Presieve.singleton (Spec.map f)) := by
  rw [isSheaf_qcTopology_iff]
  congr!
  exact HasRingHomProperty.Spec_iff

lemma effectiveEpi_of_flat {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (hs : Surjective (Spec.map f)) :
    EffectiveEpi (Spec.map f) := by
  constructor
  constructor
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry

/-- The fpqc topology is subcanonical. -/
instance : fpqcTopology.Subcanonical := by
  refine .of_isSheaf_yoneda_obj _ fun X ↦ ?_
  rw [isSheaf_fpqcTopology_iff (yoneda.obj X)]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)
  · intro R S f hf hs
    revert X
    rw [← Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda,
      Sieve.effectiveEpimorphic_singleton]
    exact effectiveEpi_of_flat _ hf hs

/-- A quasi-compact flat cover is an effective epimorphism family. -/
lemma Scheme.Cover.effectiveEpiFamily_of_quasiCompact {X : Scheme.{u}} (𝒰 : X.Cover @Flat)
    [𝒰.QuasiCompact] : EffectiveEpiFamily 𝒰.obj 𝒰.map :=
  -- immediate consequence of fqpc subcanonical
  sorry

end AlgebraicGeometry
