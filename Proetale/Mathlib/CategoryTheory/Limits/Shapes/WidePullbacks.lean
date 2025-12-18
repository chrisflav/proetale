import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Proetale.Mathlib.Order.BooleanAlgebra.Set

namespace CategoryTheory.Limits

noncomputable
def WidePullback.reindex {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasWidePullback B X f]
    {g : (j : β) → Y j ⟶ B} [HasWidePullback B Y g]
    (e : α ≃ β) (s : ∀ a, X a ≅ Y (e a))
    (w : ∀ i, (s i).hom ≫ g (e i) = f _) :
    widePullback B X f ≅ widePullback B Y g where
  hom := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e.symm i) ≫ (s _).hom ≫ eqToHom (by simp))
    fun i ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i
      simp [w]
  inv := WidePullback.lift (WidePullback.base _)
    (fun i ↦ WidePullback.π _ (e i) ≫ (s _).inv)
    fun i ↦ by simp [← w]

noncomputable
def WidePullback.proj {α β : Type*} {C : Type*} [Category C] {B : C}
    {X : α ⊕ β → C}
    {f : (j : α ⊕ β) → X j ⟶ B} [HasWidePullback B X f]
    [HasWidePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j))] :
    widePullback B X f ⟶ widePullback B (X ∘ Sum.inl) (fun j ↦ f (.inl j)) :=
  WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp)

noncomputable
def WidePullback.mapOfSumEquiv {α β γ : Type*} {C : Type*} [Category C] {B : C}
    {X : α → C} {Y : β → C}
    {f : (j : α) → X j ⟶ B} [HasLimitsOfShape (WidePullbackShape α) C]
    {g : (j : β) → Y j ⟶ B} [HasLimitsOfShape (WidePullbackShape β) C]
    [HasLimitsOfShape (WidePullbackShape (β ⊕ γ)) C]
    (e : β ⊕ γ ≃ α) (s : ∀ (b : β), X (e (.inl b)) ⟶ Y b)
    (w : ∀ b, s b ≫ g b = f _) :
    widePullback B X f ⟶ widePullback B Y g :=
  (WidePullback.reindex (Y := X ∘ e) (g := fun i ↦ f (e i)) e.symm
    (fun a ↦ eqToIso (by simp)) (fun i ↦ by
      simp only [Function.comp_apply, eqToIso.hom]
      rw [← eqToHom_naturality, eqToHom_refl, Category.comp_id]
      rw [Equiv.apply_symm_apply])).hom ≫
    WidePullback.lift (objs := Sum.elim Y (X ∘ e ∘ .inr))
      (arrows := fun i ↦ match i with
        | .inl b => g b
        | .inr c => f _)
      (WidePullback.base _)
      (fun j ↦ match j with
        | .inl b => WidePullback.π _ _ ≫ s b
        | .inr b => WidePullback.π _ _)
      (by simp [w]) ≫
      WidePullback.proj

section

variable {C : Type*} [Category C]

@[simps!]
def WidePullbackShape.functorExt {ι : Type*}
    {F G : WidePullbackShape ι ⥤ C}
    (base : F.obj none ≅ G.obj none)
    (comp : ∀ i, F.obj (some i) ≅ G.obj (some i))
    (w : ∀ i, F.map (.term i) ≫ base.hom = (comp i).hom ≫ G.map (.term i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | none => base
      | some i => comp i)
    (fun f ↦ by rcases f <;> simp [w])

@[simp]
lemma WidePullbackShape.equivalenceOfEquiv_functor_obj_none
    {ι ι' : Type*} (e : ι ≃ ι') :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj none = none := rfl

@[simp]
lemma WidePullbackShape.equivalenceOfEquiv_functor_obj_some
    {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj (some i) = some (e i) := rfl

@[simp]
lemma WidePullbackShape.equivalenceOfEquiv_functor_map_term
    {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.map (.term i) = .term (e i) := rfl

abbrev WidePullbackCone {ι : Type*} {X : C} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :=
  Cone (WidePullbackShape.wideCospan X Y f)

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

abbrev π (s : WidePullbackCone f) (i : ι) : s.pt ⟶ Y i :=
  (Cone.π s).app (some i)

abbrev base (s : WidePullbackCone f) : s.pt ⟶ X :=
  (Cone.π s).app none

@[reassoc (attr := simp)]
lemma condition (s : WidePullbackCone f) (i : ι) : s.π i ≫ f i = s.base := by
  simpa using ((Cone.π s).naturality (.term i)).symm

@[simps! pt]
def mk {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    WidePullbackCone f :=
  WidePullbackShape.mkCone b π h

@[simp]
lemma mk_base {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    (WidePullbackCone.mk b π h).base = b := rfl

@[simp]
lemma mk_π {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) (i : ι) :
    (WidePullbackCone.mk b π h).π i = π i := rfl

def IsLimit.mk (s : WidePullbackCone f) (lift : ∀ t : WidePullbackCone f, t.pt ⟶ s.pt)
    (facbase : ∀ t, lift t ≫ s.base = t.base) (facπ : ∀ t i, lift t ≫ s.π i = t.π i)
    (uniq : ∀ (t) (m : t.pt ⟶ s.pt), m ≫ s.base = t.base → (∀ i, m ≫ s.π i = t.π i) → m = lift t) :
    IsLimit s where
  lift := lift
  fac t j := by
    cases j
    exact facbase t
    exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ ↦ hm (some _)

lemma IsLimit.hom_ext {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} {k l : W ⟶ s.pt} (hbase : k ≫ s.base = l ≫ s.base)
    (hπ : ∀ i, k ≫ s.π i = l ≫ s.π i) :
    k = l := by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j

def IsLimit.lift {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    W ⟶ s.pt :=
  hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]
lemma IsLimit.lift_base {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    IsLimit.lift hs b a w ≫ s.base = b := by
  simp [lift]

@[reassoc (attr := simp)]
lemma IsLimit.lift_π {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) (i : ι) :
    IsLimit.lift hs b a w ≫ s.π i = a i := by
  simp [lift]

@[simps! pt]
def reindex {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    WidePullbackCone (fun i ↦ f (e i)) :=
  .mk s.base (fun i ↦ s.π _) (by simp)

@[simp]
lemma reindex_base {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    (s.reindex e).base = s.base := rfl

@[simp]
lemma reindex_π {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) (i : ι') :
    (s.reindex e).π i = s.π (e i) := rfl

def ext {ι : Type*}
    {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {s t : WidePullbackCone f}
    (e : s.pt ≅ t.pt)
    (base : e.hom ≫ t.base = s.base)
    (π : ∀ i, e.hom ≫ t.π i = s.π i) :
    s ≅ t :=
  Cones.ext e <| by rintro (_ | _) <;> simp [base, π]

def reindexIsLimitEquiv {ι : Type*}
    {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) :
    IsLimit (s.reindex e) ≃ IsLimit s :=
  (IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans <|
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i ↦ eqToIso (by simp))
        fun i ↦ by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp [WidePullbackCone.base, WidePullbackCone.reindex])
        (fun i ↦ by
          simp [WidePullbackCone.π, WidePullbackCone.reindex,
            eqToHom_naturality (fun i ↦ (Cone.π s).app (some i)) (e.apply_symm_apply i)]))

def isPullback_sum {α β : Type*} {X : C} {Y : α ⊕ β → C}
    {f : ∀ i, Y i ⟶ X} (c : WidePullbackCone f)
    (cl : WidePullbackCone (fun i ↦ f (.inl i))) (cr : WidePullbackCone (fun i ↦ f (.inr i)))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun _ ↦ c.π _) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun _ ↦ c.π _) (by simp))
      cl.base cr.base := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_) ?_⟩⟩
  · refine WidePullbackCone.IsLimit.lift hc (s.fst ≫ cl.base) ?_ ?_
    · intro j
      match j with
      | .inl a => exact s.fst ≫ cl.π _
      | .inr a => exact s.snd ≫ cr.π _
    · rintro (_ | _) <;> simp [-PullbackCone.condition_one]
  · apply WidePullbackCone.IsLimit.hom_ext hcl <;> simp [-PullbackCone.condition_one]
  · apply WidePullbackCone.IsLimit.hom_ext hcr <;> simp [-PullbackCone.condition_one, s.condition]
  · intro s m h1 h2
    apply WidePullbackCone.IsLimit.hom_ext hc <;> simp [← h1, ← h2]

def isPullback_of_isCompl {α β γ : Type*} {X : C}
    {Y : γ → C} (f : ∀ i, Y i ⟶ X) (il : α → γ) (ir : β → γ)
    (hlr : IsCompl (Set.range il) (Set.range ir))
    (hil : il.Injective) (hir : ir.Injective)
    (c : WidePullbackCone f)
    (cl : WidePullbackCone fun i ↦ f (il i)) (cr : WidePullbackCone fun i ↦ f (ir i))
    (hc : IsLimit c) (hcl : IsLimit cl) (hcr : IsLimit cr) :
    IsPullback
      (WidePullbackCone.IsLimit.lift hcl c.base (fun i ↦ c.π (il i)) (by simp))
      (WidePullbackCone.IsLimit.lift hcr c.base (fun i ↦ c.π (ir i)) (by simp))
      cl.base cr.base := by
  have : Function.Surjective (Sum.elim il ir) := fun x ↦ by
    simp_rw [isCompl_iff, Set.codisjoint_iff, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
      forall_const] at hlr
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := hlr.2 x <;> simp
  let e : α ⊕ β ≃ γ :=
    .ofBijective (Sum.elim il ir) ⟨hil.sumElim hir (Set.disjoint_range_iff.mp hlr.1), this⟩
  let c' : WidePullbackCone (fun i ↦ f (e i)) := c.reindex e
  have hc' : IsLimit c' :=
    (WidePullbackCone.reindexIsLimitEquiv _ _).symm hc
  exact isPullback_sum c' cl cr hc' hcl hcr

lemma isPullback_of_isCompl' {α β : Type*} {X : C}
    {Y : β → C} (f : ∀ i, Y i ⟶ X) (l : α → β) (hl : Function.Injective l) (i : β)
    (H : IsCompl {i} (Set.range l)) (c : WidePullbackCone f) (hc : IsLimit c)
    (d : WidePullbackCone fun i ↦ f (l i)) (hd : IsLimit d) :
    IsPullback (c.π i)
      (WidePullbackCone.IsLimit.lift hd c.base (fun i ↦ c.π _) (by simp))
      (f i) d.base := by
  let γ := { j : β // i ≠ j }
  let cl : WidePullbackCone (fun _ : Unit ↦ f i) :=
    WidePullbackCone.mk (f i) (fun _ ↦ 𝟙 _) (by simp)
  have hcl : IsLimit cl := by
    refine WidePullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
    · intro t
      exact t.π ()
    · intro t
      simp [cl]
    · intro t
      simp [cl]
    · intro t m hm h
      simpa [cl] using h ()
  convert c.isPullback_of_isCompl _ _ _ (by simpa)
    (Function.injective_of_subsingleton _) hl cl d hc hcl hd
  apply WidePullbackCone.IsLimit.hom_ext hcl
  · simp only [WidePullbackCone.IsLimit.lift_base]
    simp [cl]
  · simp only [WidePullbackCone.IsLimit.lift_π]
    simp [cl]

lemma isPullback_ne {β : Type*} {X : C}
    {Y : β → C} (f : ∀ i, Y i ⟶ X) (i : β)
    [HasWidePullback X Y f] [HasWidePullback X (fun j : { j // i ≠ j } ↦ Y j) fun j ↦ f j] :
    IsPullback (WidePullback.π f _)
      (WidePullback.lift (WidePullback.base _) (fun j ↦ WidePullback.π _ _) (by simp))
      (f i) (WidePullback.base <| fun j : {j // i ≠ j } ↦ f j) := by
  apply isPullback_of_isCompl'
  · exact Subtype.val_injective
  · rw [isCompl_iff]
    simp [codisjoint_iff]
    grind
  · exact limit.isLimit _

end WidePullbackCone

end

end CategoryTheory.Limits
