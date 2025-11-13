/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Proetale.Topology.SpectralSpace.WLocal.Basic
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Pullback of w-local spaces

Stacks Project 096C
-/

open CategoryTheory TopCat

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

@[stacks 096C "second part"]
theorem ConnectedComponents.wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y where
  __ := pb.spectralSpace
  eq_of_specializes := sorry
  isClosed_closedPoints := sorry

@[stacks 096C "second part"]
theorem ConnectedComponents.isWLocalMap_of_isPullback {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    IsWLocalMap f := sorry

@[stacks 096C "second part"]
theorem ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := sorry
