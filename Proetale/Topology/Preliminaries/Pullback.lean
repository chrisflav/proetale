/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Proetale.Mathlib.Topology.Spectral.Basic

universe u

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]

open CategoryTheory TopCat Limits

instance T2Space.pullback [T2Space X] [T2Space Y] (f : C(X, S)) (g : C(Y, S)) :
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

