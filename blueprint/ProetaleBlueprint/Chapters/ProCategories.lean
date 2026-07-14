import Verso
import VersoManual
import VersoBlueprint
import Proetale
import ProetaleBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pro-categories" =>

Let $`\mathcal{C}` be a category. The category $`\pro{\mathcal{C}}` is the full
subcategory of $`\mathrm{Fun}(\mathcal{C}, \mathrm{Set})^{\mathrm{op}}` on the
functors that are cofiltered limits of representable functors. This category
satisfies the following universal property:

:::group "pro-categories"
Pro-categories, precoherent categories, the coherent topology and generated
topologies, used to compare sites with their pro-completions.
:::

:::proposition "prop:pro-univ-prop" (parent := "pro-categories")
(Universal property of $`\pro{\mathcal{C}}`.) Let $`\mathcal{D}` be a category
with cofiltered limits. The restriction functor
$$`\mathrm{Fun}(\pro{\mathcal{C}}, \mathcal{D}) \to \mathrm{Fun}(\mathcal{C}, \mathcal{D})`
admits a left-adjoint that induces an equivalence on the full subcategory of
$`\mathrm{Fun}(\pro{\mathcal{C}}, \mathcal{D})` on functors preserving
cofiltered limits.
:::

:::proof "prop:pro-univ-prop"
The left-adjoint is the left Kan extension along the inclusion
$`\mathcal{C} \to \pro{\mathcal{C}}`.
:::

Let now $`\mathcal{K}` be a small category. The canonical functor
$`\mathcal{C} \to \pro{\mathcal{C}}` induces a functor
$`\mathrm{Fun}(\mathcal{K}, \mathcal{C}) \to \mathrm{Fun}(\mathcal{K}, \pro{\mathcal{C}})`.
Since the right hand side admits small cofiltered limits, the universal
property of $`\pro{\mathcal{C}}` induces a canonical functor
$$`\Phi_{\mathcal{K}}\colon \pro{\mathrm{Fun}(\mathcal{K}, \mathcal{C})} \longrightarrow \mathrm{Fun}(\mathcal{K}, \pro{\mathcal{C}}).`

:::proposition "prop:finite-diag-pro" (parent := "pro-categories") (uses := "prop:pro-univ-prop")
Suppose $`\mathcal{K}` is a finite category and every object of $`\mathcal{K}`
admits no non-trivial automorphisms. Then the natural functor
$`\Phi_{\mathcal{K}}` induces an equivalence of categories.
:::

:::proof "prop:finite-diag-pro"
See Kashiwara–Schapira, Theorem 6.4.3.
:::

:::lemma_ "ex:finite-diag-pro" (parent := "pro-categories") (uses := "prop:finite-diag-pro")
Note that {bpref "prop:finite-diag-pro"}[] in particular implies that if there
is a finite family of morphisms $`f_i \colon X_i \to X` in
$`\pro{\mathcal{C}}`, there exists a diagram $`\mathcal{J}` such that
$`X = \lim_{j \in \mathcal{J}} Y_j` and
$`X_i = \lim_{j \in \mathcal{J}} Y_{ij}` and
$`f_i = \lim_{j \in \mathcal{J}} f_{ij}` for morphisms
$`f_{ij}\colon Y_{ij} \to Y_j`.
:::

:::proposition "prop:pro-equiv-pro" (parent := "pro-categories")
Let $`\mathcal{A}` be a category with cofiltered limits and suppose there
exists a fully faithful functor $`i\colon \mathcal{C} \to \mathcal{A}` such
that $`i(X)` is cocompact for all $`X \in \mathcal{C}`. Then
$$`\lim_{\mathcal{A}} \circ \; \pro{i}\colon \pro{\mathcal{C}} \to \mathcal{A}`
is fully faithful.
:::

:::proof "prop:pro-equiv-pro"
See [nlab](https://ncatlab.org/nlab/show/pro-object#PropositionCategoriesEquivalentToProC).
:::

:::corollary "cor:pro-object-prop" (parent := "pro-categories")
Let $`P` be a property of objects of a category $`\mathcal{A}` that implies
finitely presented. Denote by $`\mathcal{A}_P` (resp.
$`\mathcal{A}_{\pro{P}}`) the full subcategory defined by $`P` (resp.
$`\pro{P}`). Suppose $`\mathcal{A}` has cofiltered limits, then
$`\lim_{\mathcal{A}}` induces an equivalence
$$`\pro{\mathcal{A}_{P}} \cong \mathcal{A}_{\pro{P}}.`
:::

:::proof "cor:pro-object-prop" (uses := "prop:pro-equiv-pro")
Follows from {bpref "prop:pro-equiv-pro"}[], because by definition
$`\mathcal{A}_{\pro{P}}` is the essential image of
$`\lim_{\mathcal{A}}(\pro{\mathcal{A}_{P}})`.
:::

Note that {bpref "cor:pro-object-prop"}[] does not apply to
$`\mathcal{A} = \mathrm{Scheme} / X` and $`P = \text{étale}`, because
$`\mathrm{Scheme} / X` does not have all cofiltered limits. It does apply in
the case of $`\mathcal{A} = \mathrm{AffScheme} / X` though, or in the case
$`\mathrm{CRing}^{\mathrm{op}} / R`.

Recall the following definition:

:::definition "def:precoherent" (parent := "pro-categories")
A category $`\mathcal{C}` is *precoherent* if given a finite effective
epimorphism family $`f\colon X_i \to X` and a morphism $`p\colon Y \to X`,
there exists a finite effective epimorphism family $`g\colon Y_j \to Y` that
factors through $`f`.
:::

:::lemma_ "lemma:et-effective-epi" (parent := "pro-categories") (lean := "AlgebraicGeometry.Scheme.Etale.effectiveEpi_of_surjective, AlgebraicGeometry.Scheme.Etale.surjective_of_epi")
A morphism $`f\colon X \to Y` in $`\et{S}` is an effective epimorphism if and
only if it is surjective.
:::

:::proof "lemma:et-effective-epi" (uses := "thm:fpqc-subcanonical")
One direction follows from the fact that the fpqc topology is subcanonical. The
converse holds, because étale morphisms are open: If $`f\colon X \to Y` is an
étale morphism we may glue two copies of $`Y` along the inclusion of the image
of $`f`. If $`f` is not surjective, the two inclusions of $`Y` into the
amalgamated sum are different, but by construction they agree on the image of
$`f`. Hence $`f` is not an epimorphism.
:::

:::lemma_ "lemma:scheme-finitaryextensive" (parent := "pro-categories") (tags := "mathlib")
The category of schemes is finitary extensive.
:::

:::proof "lemma:scheme-finitaryextensive"
Since the Zariski topology is subcanonical, the category of schemes embeds into
the big Zariski topos, which is finitary extensive. Since the Yoneda embedding
preserves finite coproducts, the claim follows.
:::

:::lemma_ "lemma:et-precoherent" (parent := "pro-categories") (lean := "AlgebraicGeometry.Scheme.Etale.precoherent")
The category $`\et{X}` is precoherent.
:::

:::proof "lemma:et-precoherent" (uses := "lemma:et-effective-epi, lemma:scheme-finitaryextensive")
The category of schemes is finitary extensive, so the same holds for
$`\et{X}`. By {bpref "lemma:et-effective-epi"}[] the effective epimorphisms in
$`\et{X}` are the surjective morphisms, hence being an effective epimorphism is
stable under base change. Thus $`\et{X}` is preregular and therefore
precoherent.
:::

:::proposition "prop:pro-precoherent" (parent := "pro-categories")
If $`\mathcal{C}` is precoherent, also $`\pro{\mathcal{C}}` is precoherent.
:::

# Coherent topology

Any precoherent category can be equipped with the coherent coverage, where
covering families are given by finite effective epimorphic families. The
coherent topology is the topology generated by the coherent coverage.

:::lemma_ "remark:et-not-precoherent-topology" (parent := "pro-categories")
One would hope that the topology on $`\et{X}` given by jointly surjective
families is the precoherent topology. Since effective epimorphisms are simply
surjective maps in $`\et{X}`, this would mean that every cover in $`\et{X}` can
be refined by a finite cover. This is not true though, because $`\et{X}` also
contains non-quasi-compact schemes.

The situation is slightly better if we instead consider the affine étale site
$`\affet{X}` of $`X`, the category of affine schemes étale over $`X`.
Unfortunately, it is not clear to the authors if effective epimorphisms in
$`\affet{X}` are still surjective.
:::

Let from now on $`\mathcal{C}` be precoherent equipped with the coherent
topology.

:::proposition "prop:sheaf-pro-restrict" (parent := "pro-categories")
Let $`F \colon \pro{\mathcal{C}}^{\mathrm{op}} \to \mathrm{Set}` be a sheaf.
Then $`F|_{\mathcal{C}^{\mathrm{op}}}` is a sheaf.
:::

By {bpref "prop:sheaf-pro-restrict"}[], the inclusion functor
$`\mathcal{C} \to \pro{\mathcal{C}}` induces a morphism on sites
$`\nu\colon \pro{\mathcal{C}} \to \mathcal{C}`. The direct image functor
$`\nu_{*}\colon \shv{\pro{\mathcal{C}}} \to \shv{\mathcal{C}}` agrees with the
restriction $`F \mapsto F|_{\mathcal{C}^{\mathrm{op}}}`.

:::proposition "prop:sheaf-pro" (parent := "pro-categories")
Let $`F \colon \pro{\mathcal{C}}^{\mathrm{op}} \to \mathrm{Set}` be a
presheaf. Suppose $`F|_{\mathcal{C}^{\mathrm{op}}}` is a sheaf and $`F`
preserves filtered colimits. Then $`F` is a sheaf.
:::

Combining {bpref "prop:pro-univ-prop"}[] and {bpref "prop:sheaf-pro"}[]
yields:

:::corollary "cor:pro-direct-image-unit-iso" (parent := "pro-categories")
Let $`F` be a sheaf on $`\mathcal{C}`. Then the unit
$`F \to \nu_{*} \nu^{-1} F` is an isomorphism.
:::

:::proof "cor:pro-direct-image-unit-iso" (uses := "prop:pro-univ-prop, prop:sheaf-pro")
Denote by $`\mathrm{res}` the restriction functor
$`\mathrm{PShv}(\pro{\mathcal{C}}) \to \mathrm{PShv}(\mathcal{C})` and by
$`\mathrm{ext}` the left-adjoint of {bpref "prop:pro-univ-prop"}[]. By
{bpref "prop:sheaf-pro"}[], $`\mathrm{ext}` restricts to a functor
$`\mathrm{Shv}(\mathcal{C}) \to \mathrm{Shv}(\pro{\mathcal{C}})` that is the
left-adjoint of $`\nu_*`. In particular it agrees with $`\nu^{-1}` and the
result follows.
:::

# Generated topologies

The previous section established a relationship between the coherent topologies
on $`\mathcal{C}` and $`\pro{\mathcal{C}}`. In the situations we are interested
in, the topologies don't necessarily agree with the coherent topologies though
(see {bpref "remark:et-not-precoherent-topology"}[]).

To remedy the situation, we make the following definitions:

:::definition "def:exact-one-hypercover" (parent := "pro-categories")
Let $`\mathcal{U}` be a one-hypercover in a site $`\mathcal{C}`. We say
$`\mathcal{U}` is *exact* if taking filtered colimits preserves the
multiequalizer diagram of $`\mathcal{U}`.
:::

Any finite one-hypercover is exact, because filtered colimits commute with
finite limits.

:::definition "def:one-cover-relatively-pro-prepresentable" (parent := "pro-categories") (uses := "def:exact-one-hypercover") (lean := "CategoryTheory.GrothendieckTopology.oneHypercoverRelativelyRepresentable")
Let $`F\colon \mathcal{C} \to \mathcal{D}` be a functor between sites. We say a
one-hypercover $`\mathcal{U}` of an object $`X` in $`\mathcal{D}` is
*relatively pro-representable* if it is exact and $`\mathcal{U}` can be written
as the componentwise cofiltered limit of one-hypercovers in $`\mathcal{C}`.
:::

Concretely, a one-hypercover
$`\mathcal{U} = (U_{\alpha}, U_{\alpha \beta \gamma})` is relatively
pro-representable if there exist

1. a cofiltered diagram $`\mathcal{I}`,
2. functors $`V_{\alpha}\colon \mathcal{I} \to \mathcal{C}` and
   $`V_{\alpha \beta \gamma}\colon \mathcal{I} \to \mathcal{C}`,
3. natural transformations $`p_1 \colon V_{\alpha \beta \gamma} \to V_{\alpha}`
   and $`p_2\colon V_{\alpha \beta \gamma} \to V_{\beta}`,

such that

1. $`U_{\alpha} = \lim_i V_{\alpha}(i)` and
   $`U_{\alpha \beta \gamma} = \lim_i V_{\alpha \beta \gamma}(i)`, and
2. for every $`i \in \mathcal{I}`, the induced pre-one-hypercover
   $`(V_{\alpha}(i), V_{\alpha \beta \gamma}(i))` is a one-hypercover.

Suppose $`\mathcal{C}` is coherent, $`\mathcal{D} = \pro{\mathcal{C}}` and
$`F \colon \mathcal{C} \to \pro{\mathcal{C}}` the inclusion. If both
$`\mathcal{C}` and $`\pro{\mathcal{C}}` are equipped with the coherent
topologies, the topology on $`\pro{\mathcal{C}}` is generated by relatively
pro-representable one-hypercovers.

The analogue of {bpref "prop:sheaf-pro"}[] is:

:::proposition "prop:sheaf-relatively-representable-generated" (parent := "pro-categories") (uses := "def:one-cover-relatively-pro-prepresentable") (lean := "CategoryTheory.Presheaf.IsSheaf.of_preservesFilteredColimitsOfSize")
Suppose the topology on $`\mathcal{D}` is generated by relatively
pro-representable one-hypercovers and let $`P` be a presheaf on
$`\mathcal{D}`. If $`P \circ F^{\mathrm{op}}` is a sheaf on $`\mathcal{C}` and
$`P` preserves filtered colimits, then $`P` is a sheaf on $`\mathcal{D}`.
:::

:::proof "prop:sheaf-relatively-representable-generated"
By the assumption, it suffices to check the sheaf condition for every
relatively pro-representable one-hypercover
$`\mathcal{U} = \lim F(\mathcal{V}_i)`. Because $`P` preserves filtered
colimits, one computes that the sheaf condition for $`\mathcal{U}` is the
filtered colimit of the sheaf conditions for $`\mathcal{V}_i`. But
$`P \circ F^{\mathrm{op}}` is a sheaf and filtered colimits preserve the
equalizers because $`\mathcal{U}` is exact.
:::
