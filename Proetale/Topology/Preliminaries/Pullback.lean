/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Proetale.Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Proetale.Mathlib.Topology.Spectral.Basic

universe u

open CategoryTheory TopCat Limits

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
variable (f : C(X, S)) (g : C(Y, S))

variable {P : Type u} [TopologicalSpace P] {f' : C(P, Y)} {g' : C(P, X)} (pb : IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g))

section pullback

instance T2Space.pullback [T2Space X] [T2Space Y]  :
    T2Space (pullback (ofHom f) (ofHom g) : TopCat) := (homeoOfIso (pullbackIsoProdSubtype (ofHom f) (ofHom g))).symm.t2Space

instance T0Space.pullback [T0Space X] [T0Space Y] (f : C(X, S)) (g : C(Y, S)) :
    T0Space (pullback (ofHom f) (ofHom g) : TopCat) := (homeoOfIso (pullbackIsoProdSubtype (ofHom f) (ofHom g))).symm.t0Space

instance QuasiSober.pullback [QuasiSober X] [QuasiSober Y] (f : C(X, S)) (g : C(Y, S)) :
    QuasiSober (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.quasiSober
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).quasiSober

instance QuasiSeparatedSpace.pullback [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    QuasiSeparatedSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.quasiSeparatedSpace
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).quasiSeparatedSpace

instance CompactSpace.pullback [CompactSpace X] [CompactSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    CompactSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.compactSpace
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).compactSpace

instance PrespectralSpace.pullback [PrespectralSpace X] [PrespectralSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    PrespectralSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.prespectralSpace
  PrespectralSpace.of_isClosedEmbedding _ (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g))

instance SpectralSpace.pullback [SpectralSpace X] [SpectralSpace Y] (f : C(X, S)) (g : C(Y, S)) :
    SpectralSpace (pullback (ofHom f) (ofHom g) : TopCat) :=
  let _ := (homeoOfIso (prodIsoProd (of X) (of Y))).symm.spectralSpace
  (isClosedEmbedding_pullback_to_prod (ofHom f) (ofHom g)).spectralSpace

end pullback

section IsPullback

variable {f g}

include f' g' pb

theorem CategoryTheory.IsPullback.t2Space [T2Space X] [T2Space Y] : T2Space P :=
  (homeoOfIso pb.isoPullback).symm.t2Space

theorem CategoryTheory.IsPullback.t0Space [T0Space X] [T0Space Y] : T0Space P :=
  (homeoOfIso pb.isoPullback).symm.t0Space

theorem CategoryTheory.IsPullback.quasiSober [QuasiSober X] [QuasiSober Y] : QuasiSober P :=
  (homeoOfIso pb.isoPullback).symm.quasiSober

theorem CategoryTheory.IsPullback.quasiSeparatedSpace [QuasiSeparatedSpace X] [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace P :=
  (homeoOfIso pb.isoPullback).symm.quasiSeparatedSpace

theorem CategoryTheory.IsPullback.compactSpace [CompactSpace X] [CompactSpace Y] : CompactSpace P :=
  (homeoOfIso pb.isoPullback).symm.compactSpace

theorem CategoryTheory.IsPullback.prespectralSpace [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace P :=
  (homeoOfIso pb.isoPullback).symm.prespectralSpace

theorem CategoryTheory.IsPullback.spectralSpace [SpectralSpace X] [SpectralSpace Y] : SpectralSpace P :=
  (homeoOfIso pb.isoPullback).symm.spectralSpace

end IsPullback
