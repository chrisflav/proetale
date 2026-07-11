import Verso
import VersoManual
import VersoBlueprint
import Proetale
import ProetaleBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Proper base change" =>

In this chapter we set up the base change machinery for abelian sheaves on small
étale sites and decompose the proof of the proper base change theorem
(SGA 4, Exposé XII). Throughout, consider a cartesian square of schemes

$$`\begin{array}{ccc} X' & \xrightarrow{g'} & X \\ \downarrow f' & & \downarrow f \\ S' & \xrightarrow{g} & S \end{array}`

with $`f` proper.

:::group "proper-base-change"
The base change formalism for étale cohomology and the proper base change theorem,
following SGA 4, Exposé XII.
:::

# The base change morphism

:::definition "def:etale-pushforward" (parent := "proper-base-change") (lean := "AlgebraicGeometry.Scheme.etalePushforward")
For a morphism of schemes $`f \colon X \to S`, base change of étale $`S`-schemes
induces a continuous morphism of small étale sites, and hence an adjunction
$`f^* \dashv f_*` between the categories of abelian sheaves on $`\et{X}` and
$`\et{S}`.
:::

:::lemma_ "lemma:etale-pullback-exact" (parent := "proper-base-change") (uses := "def:etale-pushforward") (lean := "AlgebraicGeometry.Scheme.preservesFiniteLimits_smallPullback")
The pullback functor $`f^*` on abelian étale sheaves is exact.
:::

:::proof "lemma:etale-pullback-exact"
$`f^*` is a left adjoint, hence right exact. For left exactness, the base change
functor on the small étale sites preserves finite limits, so it is representably
flat, so the left Kan extension on abelian presheaves is a filtered colimit
pointwise and therefore exact; sheafification is exact as well.
:::

:::definition "def:base-change-transformation" (parent := "proper-base-change") (uses := "def:etale-pushforward") (lean := "AlgebraicGeometry.Scheme.baseChangeNatTrans")
For a commutative square $`g' \circ f = f' \circ g` as above (not necessarily
cartesian), the *base change transformation*
$$`\tau \colon f_* \circ g^* \longrightarrow g'^* \circ f'_*`
is the mate of the canonical isomorphism $`g^* \circ f'^* \cong f^* \circ g'^*`,
which in turn is conjugate to the canonical isomorphism
$`g'_* \circ f_* \cong f'_* \circ g_*` of pushforward functors.
:::

:::definition "def:derived-category-plus" (parent := "proper-base-change") (lean := "DerivedCategoryPlus")
The *bounded below derived category* $`D^+(\mathcal{A})` of an abelian category
$`\mathcal{A}` is the localization of the category of bounded below cochain
complexes at the quasi-isomorphisms.
:::

:::lemma_ "lemma:fibrant-derives" (parent := "proper-base-change") (uses := "def:derived-category-plus") (lean := "CategoryTheory.Functor.fibrantObject_derives_mapCochainComplexPlus")
Let $`\mathcal{A}` be an abelian category with enough injectives. Bounded below
complexes of injectives are K-injective; consequently any quasi-isomorphism between
them is a homotopy equivalence and is inverted by $`G` followed by the localization,
for every additive functor $`G`.
:::

:::proof "lemma:fibrant-derives"
The fibrant objects of the injective model structure on bounded below complexes are
exactly the bounded below complexes of injectives. These are K-injective, so a
quasi-isomorphism between them is a homotopy equivalence; additive functors preserve
homotopy equivalences, and homotopy equivalences are quasi-isomorphisms.
:::

:::definition "def:derived-pushforward" (parent := "proper-base-change") (uses := "def:etale-pushforward, def:derived-category-plus, lemma:fibrant-derives") (lean := "AlgebraicGeometry.Scheme.derivedPushforward")
The *derived pushforward*
$`Rf_* \colon D^+(\mathrm{Ab}(\et{X})) \to D^+(\mathrm{Ab}(\et{S}))`
is the total right derived functor of $`f_*`, constructed via the derivability
structure of fibrant objects of the injective model structure on bounded below
complexes. Since $`g^*` is exact ({bpref "lemma:etale-pullback-exact"}[]), it descends
to the bounded below derived categories without derivation.
:::

:::definition "def:derived-base-change" (parent := "proper-base-change") (uses := "def:derived-pushforward, def:base-change-transformation") (lean := "AlgebraicGeometry.Scheme.derivedBaseChangeNatTrans")
The *derived base change transformation*
$$`Rf_* \circ g^* \longrightarrow g'^* \circ Rf'_*`
is obtained from the underived one ({bpref "def:base-change-transformation"}[]) by
the universal property of the total right derived functor: the composite
$`Rf_* \circ g^*` is itself a right derived functor of $`f_* \circ g^*` because
$`g^*` is exact.
:::

:::definition "def:locally-torsion" (parent := "proper-base-change") (lean := "CategoryTheory.Sheaf.IsLocallyTorsion")
An abelian sheaf $`F` on a site is *locally torsion* if every section is, locally on
a covering, killed by a positive integer.
:::

:::theorem "thm:proper-base-change" (parent := "proper-base-change") (uses := "def:derived-base-change, def:locally-torsion, thm:pbc-special-case") (lean := "AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app")
(Proper base change, SGA 4 XII 5.1.) If the square is cartesian and $`f` is proper,
the derived base change transformation is an isomorphism on every bounded below
complex with locally torsion cohomology sheaves.
:::

:::proof "thm:proper-base-change"
By dévissage (truncation triangles and the five lemma) reduce to a single locally
torsion sheaf $`F`. Writing $`F` as the filtered colimit of its $`n`-torsion
subsheaves and using that étale cohomology of the qcqs schemes involved commutes with
filtered colimits, reduce to sheaves of $`\mathbb{Z}/n`-modules. Isomorphy may be
checked on stalks at geometric points of $`S'`; the stalk of $`R^q f'_*` at a
geometric point is the cohomology of the base change of $`X` to the strict
henselization, which is the special case {bpref "thm:pbc-special-case"}[].
:::

# Reduction to the strictly henselian case

The following statements require infrastructure that is not yet available: strictly
henselian local rings, and the computation of stalks of higher direct images at
geometric points as cohomology over the strict henselization.

:::definition "def:strictly-henselian" (parent := "proper-base-change")
A local ring $`R` is *strictly henselian* if it is henselian with separably closed
residue field. For a geometric point $`\bar{s}` of a scheme $`S`, the *strict
localization* $`\operatorname{Spec} \mathcal{O}^{sh}_{S, \bar{s}}` is the limit of
the étale neighbourhoods of $`\bar{s}`.
:::

:::theorem "thm:pbc-special-case" (parent := "proper-base-change") (uses := "def:strictly-henselian, lemma:pbc-degree-zero, lemma:pbc-finite, thm:pbc-curves, lemma:pbc-devissage")
Let $`S` be the spectrum of a strictly henselian local ring with closed point $`s`,
let $`f \colon X \to S` be proper and let $`F` be a torsion abelian sheaf on
$`\et{X}`. Then restriction induces isomorphisms
$$`H^q(X, F) \xrightarrow{\ \sim\ } H^q(X_s, F|_{X_s})`
for all $`q \geq 0`.
:::

# Degree zero and finite morphisms

:::lemma_ "lemma:pbc-degree-zero" (parent := "proper-base-change") (uses := "def:strictly-henselian, lemma:pbc-finite")
In the situation of {bpref "thm:pbc-special-case"}[], the restriction
$`\Gamma(X, F) \to \Gamma(X_s, F|_{X_s})` is bijective.
:::

:::proof "lemma:pbc-degree-zero"
By Stein factorization and the finite case one reduces to the statement that the
connected components of $`X` and of the closed fiber $`X_s` correspond bijectively;
this is the lifting of idempotents along the finite $`\mathcal{O}_S`-algebra
$`f_* \mathcal{O}_X` over the henselian local base.
:::

:::lemma_ "lemma:pbc-finite" (parent := "proper-base-change") (uses := "def:etale-pushforward")
For a finite morphism $`f`, one has $`R^q f_* F = 0` for $`q > 0`, and the base
change transformation is an isomorphism for every abelian sheaf $`F`.
:::

:::proof "lemma:pbc-finite"
The stalk of $`f_* F` at a geometric point $`\bar{s}` is
$`\prod_{\bar{x} \mapsto \bar{s}} F_{\bar{x}}`, because a finite algebra over a
strictly henselian local ring decomposes as a finite product of strictly henselian
local algebras. Exactness of $`\prod` and the same computation after base change give
both claims.
:::

# Cohomology of curves

:::theorem "thm:pbc-curves" (parent := "proper-base-change")
Let $`C` be a proper curve over an algebraically closed field $`k` and let `n` be an
integer. Then $`H^q(C, \mathbb{Z}/n) = 0` for $`q > 2`, and for $`C` smooth connected
and $`n` invertible in $`k` there are canonical isomorphisms
$`H^0 = \mathbb{Z}/n`, $`H^1 = \operatorname{Pic}(C)[n]`, $`H^2 = \mathbb{Z}/n`.
:::

:::proof "thm:pbc-curves"
Via the Kummer sequence this reduces to the computation of
$`H^q(C, \mathbb{G}_m)`: $`H^1` is the Picard group, and $`H^q = 0` for
$`q \geq 2` by Tsen's theorem (the function field of $`C` is $`C_1`, so its Brauer
group and higher Galois cohomology vanish). This chapter of the formalization —
Kummer theory, Picard schemes, Tsen's theorem — is the deepest missing prerequisite
and deserves a blueprint chapter of its own.
:::

# Dévissage

:::lemma_ "lemma:pbc-devissage" (parent := "proper-base-change") (uses := "lemma:pbc-finite, thm:pbc-curves, lemma:pbc-degree-zero")
The special case {bpref "thm:pbc-special-case"}[] holds in general if it holds for
$`f` of relative dimension $`\leq 1`.
:::

:::proof "lemma:pbc-devissage"
Locally on $`X`, the morphism $`f` factors through a projective space over $`S`; by
the finite case and Čech arguments one reduces to $`f = \mathbb{P}^n_S \to S`, which
is an iterated fibration in curves. The Leray spectral sequence for a fibration in
curves, together with induction on the fiber dimension and
{bpref "thm:pbc-curves"}[] for the fibers, yields the general case.
:::

# Finiteness of étale cohomology

:::theorem "thm:pbc-finiteness" (parent := "proper-base-change") (uses := "thm:proper-base-change, thm:pbc-curves, lemma:pbc-finite") (lean := "AlgebraicGeometry.Scheme.finite_H_of_isProper")
(SGA 4 XIV.) Let $`X` be proper over a separably closed field and let $`M` be a
finite abelian group. Then the étale cohomology groups $`H^q(X, M)` are finite.
:::

:::proof "thm:pbc-finiteness"
Induction on the dimension. After reducing to projective $`X` by Chow's lemma and the
finite case ({bpref "lemma:pbc-finite"}[]), fiber $`X` in curves over a base of
smaller dimension. By proper base change ({bpref "thm:proper-base-change"}[]) the
stalks of the higher direct images along the fibration are the cohomologies of the
fibers, which are finite by the curve case ({bpref "thm:pbc-curves"}[]), and the
higher direct images are constructible; the Leray spectral sequence and the induction
hypothesis (extended from constant to constructible coefficients by dévissage)
conclude.
:::

:::theorem "thm:elladic-comparison-proper" (parent := "proper-base-change") (uses := "thm:pbc-finiteness") (lean := "AlgebraicGeometry.Scheme.existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper")
For $`X` proper over a separably closed field and $`\ell` prime, there is a unique
additive equivalence
$$`H^{i+1}(X_{\mathrm{pro\acute{e}t}}, \widehat{\mathbb{Z}}_\ell) \simeq
\varprojlim_n H^{i+1}(X_{\acute{e}t}, \mathbb{Z}/\ell^n)`
compatible with the canonical comparison maps — the finiteness hypothesis of the
general comparison theorem holds automatically by
{bpref "thm:pbc-finiteness"}[].
:::

:::proof "thm:elladic-comparison-proper"
Immediate from the general comparison theorem and
{bpref "thm:pbc-finiteness"}[] applied to $`M = \mathbb{Z}/\ell^n`. This deduction
is a complete Lean proof.
:::
