/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Topology.Proetale.Basic

/-!
# The pro-étale site has sheafification

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme.ProEt

/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Type (u + 1)`-valued sheafs. -/
instance (S : Scheme.{u}) : HasSheafify (ProEt.topology S) (Type (u + 1)) :=
  inferInstance

/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Ab.{u + 1}`-valued sheafs. -/
instance (S : Scheme.{u}) : HasSheafify (ProEt.topology S) Ab.{u + 1} :=
  inferInstance

end AlgebraicGeometry.Scheme.ProEt
