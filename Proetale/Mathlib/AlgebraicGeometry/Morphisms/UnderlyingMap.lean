import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

universe v u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

@[simps!]
noncomputable
def Scheme.Hom.cover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] : Cover.{v} P S :=
  .mkOfCovers PUnit.{v + 1} (fun _ ↦ X) (fun _ ↦ f) (fun x ↦ ⟨⟨⟩, f.surjective x⟩) (fun _ ↦ hf)

lemma ofArrows_homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] :
    Presieve.ofArrows (f.cover hf).X (f.cover hf).f = Presieve.singleton f :=
  sorry

instance {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] : Unique (f.cover hf).I₀ :=
  inferInstanceAs <| Unique PUnit

end AlgebraicGeometry
