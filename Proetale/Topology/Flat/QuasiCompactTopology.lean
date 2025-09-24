/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Finite
import Proetale.Mathlib.CategoryTheory.Sites.Sheaf
import Proetale.Mathlib.CategoryTheory.Sites.IsSheafFor
import Proetale.Topology.Flat.QuasiCompactCover
import Proetale.Mathlib.CategoryTheory.Extensive

/-!
# The quasi-compact topology of a scheme

The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`.

We show that a presheaf is a sheaf in this topology if and only if it is a sheaf
in the Zariski topology and a sheaf on single object `P`-coverings of affine schemes.
-/

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type*} [Category C] {X : C}

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

open Scheme

variable {P : MorphismProperty Scheme.{u}}

@[simp]
lemma Scheme.Cover.ofArrows_sigma {S : Scheme.{u}} (𝒰 : S.Cover P) [IsLocalAtSource P] :
    Presieve.ofArrows 𝒰.sigma.obj 𝒰.sigma.map = Presieve.singleton (Sigma.desc 𝒰.map) := by
  refine le_antisymm ?_ ?_
  · intro T g ⟨i⟩
    exact Presieve.singleton_self _
  · intro T g ⟨⟩
    exact ⟨⟨⟩⟩

/-- The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`. -/
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

abbrev qcTopology (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] : GrothendieckTopology Scheme.{u} := (qcPretopology P).toGrothendieck

@[simp]
lemma Scheme.Hom.singleton_mem_qcPretopology [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f] [QuasiCompact f] :
    Presieve.singleton f ∈ qcPretopology P Y := by
  refine ⟨f.cover hf, inferInstance, ?_⟩
  rw [ofArrows_homCover]

@[simp]
lemma Scheme.Hom.generate_singleton_mem_qcTopology [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f) [Surjective f] [QuasiCompact f] :
    Sieve.generate (Presieve.singleton f) ∈ qcTopology P Y := by
  refine ⟨Presieve.singleton f, ?_, ?_⟩
  · exact f.singleton_mem_qcPretopology hf
  · exact Sieve.le_generate _

@[simp]
lemma Scheme.Cover.generate_ofArrows_mem_qcTopology [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} (𝒰 : Cover.{u} P S) [𝒰.QuasiCompact] :
    .generate (.ofArrows 𝒰.obj 𝒰.map) ∈ qcTopology P S := by
  rw [qcTopology, Pretopology.mem_toGrothendieck]
  exact ⟨.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, ‹_›, rfl⟩, Sieve.le_generate _⟩

-- This holds more generally if `𝒰.J` is `u`-small, but we don't need that for now.
lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type*} [IsLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover P) [Finite 𝒰.J] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.obj 𝒰.sigma.map) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.obj 𝒰.map) := by
  have : PreservesFiniteProducts F := preservesFiniteProducts_of_isSheaf_zariskiTopology hF
  conv_rhs => rw [← Presieve.isSheafFor_sigmaDesc_iff]
  congr!
  rw [Scheme.Cover.ofArrows_sigma]

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

lemma zariskiTopology_le_qcTopology [IsLocalAtSource P] :
    zariskiTopology ≤ qcTopology P := by
  rw [qcTopology, zariskiTopology, (Pretopology.gi _).gc.le_iff_le]
  rintro S R ⟨𝒰, rfl⟩
  rw [Pretopology.mem_ofGrothendieck]
  let 𝒰' : Cover P S := 𝒰.changeProp P (fun j ↦ IsLocalAtSource.of_isOpenImmersion _)
  have : 𝒰'.QuasiCompact := ⟨(inferInstanceAs <| 𝒰.QuasiCompact).1⟩
  exact 𝒰'.generate_ofArrows_mem_qcTopology

open Opposite

@[simps!]
noncomputable
def Scheme.affineCover' (X : Scheme.{u}) : X.OpenCover :=
  .mkOfCovers X.affineOpens (fun i ↦ i.1) (fun i ↦ i.1.ι) fun x ↦ by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_affine_open X)
      (show x ∈ ⊤ from trivial)
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩

variable {P}

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
    rw [← ofArrows_homCover _ hf]
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

end AlgebraicGeometry
