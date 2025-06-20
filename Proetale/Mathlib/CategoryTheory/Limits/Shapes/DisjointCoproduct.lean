import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

def CoproductDisjoint.of_binaryCofan_of_pullbackCone {X Y : C}
    (c : BinaryCofan X Y) (hc : IsColimit c)
    (d : PullbackCone c.inl c.inr) (hd : IsLimit d)
    (H : IsInitial d.pt) [Mono c.inl] [Mono c.inr] :
    CoproductDisjoint X Y where
  isInitialOfIsPullbackOfIsCoproduct {A B} p q f g h hsq hl := by
    let e := h.uniqueUpToIso hc
    have hp : p ≫ e.hom.hom = c.inl := e.hom.w ⟨.left⟩
    have hq : q ≫ e.hom.hom = c.inr := e.hom.w ⟨.right⟩
    let u : B ⟶ d.pt := by
      refine PullbackCone.IsLimit.lift hd f g ?_
      · rw [← hp, reassoc_of% hsq, reassoc_of% show q = c.inr ≫ e.inv.hom by simp]
        rw [CoconeMorphism.w_assoc, CoconeMorphism.w]
    have hu1 : u ≫ d.fst = f := by simp [u]
    have hu2 : u ≫ d.snd = g := by simp [u]
    refine H.ofIso ⟨H.to B, u, H.hom_ext _ _, PullbackCone.IsLimit.hom_ext hl ?_ ?_⟩
    · simp [← hu1, show H.to X = d.fst from H.hom_ext _ _]
    · simp [← hu2, show H.to Y = d.snd from H.hom_ext _ _]
  mono_inl B p q h := by
    rw [show p = c.inl ≫ (h.uniqueUpToIso hc).inv.hom by simp]
    infer_instance
  mono_inr B p q h := by
    rw [show q = c.inr ≫ (h.uniqueUpToIso hc).inv.hom by simp]
    infer_instance

end CategoryTheory.Limits
