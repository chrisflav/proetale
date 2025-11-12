import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

universe u

open CategoryTheory Limits

-- after `TopCat.isEmbedding_pullback_to_prod`
theorem TopCat.isClosedEmbedding_pullback_to_prod {X Y Z : TopCat.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
Topology.IsClosedEmbedding ⇑(prod.lift (pullback.fst f g) (pullback.snd f g)) := sorry
