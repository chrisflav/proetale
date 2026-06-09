import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer

universe w w' v u

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

namespace Limits

variable {J : MulticospanShape.{w, w'}} (d : MulticospanIndex J C)
  (c : Multifork d) (F : C ⥤ D)

/-- The multicospan index obtained by applying a functor. -/
@[simps]
def MulticospanIndex.map : MulticospanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

/-- If `d : MulticospanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multicospan ≅ d.multicospan ⋙ F`. -/
@[simps!]
def MulticospanIndex.multicospanMapIso : (d.map F).multicospan ≅ d.multicospan ⋙ F :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

variable {d}

/-- If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
this is the induced multifork of `d.map F`. -/
@[simps!]
def Multifork.map : Multifork (d.map F) :=
  Multifork.ofι _ (F.obj c.pt) (fun i ↦ F.map (c.ι i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

/-- If `d : MulticospanIndex J C`, `c : Multifork d` and `F : C ⥤ D`,
the cone `F.mapCone c` is limiting iff the multifork `c.map F` is. -/
def Multifork.isLimitMapEquiv :
    IsLimit (F.mapCone c) ≃ IsLimit (c.map F) :=
  Equiv.trans (IsLimit.postcomposeInvEquiv (d.multicospanMapIso F) (F.mapCone c)).symm
    (IsLimit.equivIsoLimit
      (Multifork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multifork.ι]; simp)))

/-- If `d : MulticospanIndex J C`, `c : Multifork d` is a limit multifork,
and `F : C ⥤ D` is a functor which preserves the limit of `d.multicospan`,
then the multifork `c.map F` is limiting. -/
noncomputable def Multifork.isLimitMapOfPreserves
    [PreservesLimit d.multicospan F] (hc : IsLimit c) : IsLimit (c.map F) :=
  (isLimitMapEquiv c F) (isLimitOfPreserves F hc)

end Limits

end CategoryTheory
