import Verso
import VersoManual
import VersoBlueprint
import Proetale
import ProetaleBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The pro-étale topology" =>

In this chapter we introduce the pro-étale site of a scheme and study its basic
properties.

:::group "proetale-topology"
The pro-étale site of a scheme and its basic properties, including the
comparison with étale cohomology, following Sections 4 and 5 of Bhatt–Scholze.
:::

# Preliminaries about the étale topology

Before going to the pro-étale case, we recall a few preliminary results about
the étale site that we will need in the sequel. Let $`X` be a scheme. By
$`\et{X}` we denote the étale site of $`X` and by $`\affet{X}` the affine étale
site. $`\affet{X}` consists of affine schemes étale over $`X`.

:::lemma_ "lemma:affet-gen-et" (parent := "proetale-topology")
The inclusion functor $`\affet{X} \to \et{X}` is cover dense, i.e. for every
$`Y` in $`\et{X}` there exists a cover $`\{U_i \to Y\}` with $`U_i` in
$`\affet{X}`.
:::

:::proof "lemma:affet-gen-et"
This is immediate, because open immersions are étale and étale is stable under
composition.
:::

# Weakly étale morphisms of schemes

:::definition "def:weakly-etale-morphism" (parent := "proetale-topology") (lean := "AlgebraicGeometry.WeaklyEtale")
A map $`f \colon Y \to X` is *weakly étale* if $`f` is flat and
$`\Delta_f\colon Y \to Y \times_{X} Y` is flat.
(Bhatt–Scholze, Definition 4.1.1)
:::

:::lemma_ "lemma:weakly-etale-hasringhomprop" (parent := "proetale-topology") (uses := "def:weakly-etale-algebra, def:weakly-etale-morphism") (lean := "AlgebraicGeometry.WeaklyEtale.hasRingHomProperty")
(Local property of weakly étale morphisms.) $`f \colon Y \to X` is weakly étale
if and only if for every affine open $`U` of $`Y` and every affine open $`V` of
$`X` with $`f(U) \subset V`, the induced ring homomorphism
$`\Gamma(X, V) \to \Gamma(Y, U)` is weakly étale.
:::

:::proof "lemma:weakly-etale-hasringhomprop"
Weakly étale morphisms of schemes are local on source and on target for the
Zariski topology, so the property descends to affine opens. There it matches
the ring-theoretic definition via the characterisation of weakly étale algebras
({bpref "def:weakly-etale-algebra"}[]).
:::

:::lemma_ "lemma:etale-weakly-etale" (parent := "proetale-topology") (uses := "def:weakly-etale-morphism") (tags := "mathlib")
Etale morphisms are weakly étale.
:::

:::proof "lemma:etale-weakly-etale"
Any étale morphism is flat and its diagonal is an open immersion, hence flat.
:::

:::lemma_ "lemma:weakly-etale-stable" (parent := "proetale-topology") (uses := "def:weakly-etale-morphism") (tags := "mathlib")
Weakly étale is stable under composition and base change.
(Bhatt–Scholze, Lemma 4.1.6)
:::

:::proof "lemma:weakly-etale-stable"
This follows because flat is stable under composition and base change.
:::

# The site

Before we define the pro-étale site, we recall a few standard definitions.

:::definition "def:qc-cover" (parent := "proetale-topology") (tags := "mathlib")
A jointly surjective family $`(f_i \colon Y_i \to X)_{i \in I}` of morphisms of
schemes is *quasi-compact* if for every affine open $`U` of $`X` there exist
quasi-compact opens $`V_i` in $`Y_i` such that
$`U = \bigcup_{i \in I} f_i(V_i)`.
:::

:::lemma_ "lemma:qc-cover-of-flat-fp" (parent := "proetale-topology") (uses := "def:qc-cover") (lean := "AlgebraicGeometry.QuasiCompactCover.of_flat_locallyOfFinitePresentation") (tags := "mathlib")
Let $`(f_i \colon Y_i \to X)_{i \in I}` be a jointly-surjective family of
morphisms of schemes. If $`f_i` is flat and locally of finite presentation for
every $`i \in I`, the family is quasi-compact.
:::

:::proof "lemma:qc-cover-of-flat-fp"
In this case, every $`f_i` is an open map, from which the claim easily follows.
:::

:::definition "def:small-P-site" (parent := "proetale-topology") (tags := "mathlib")
Let $`\mathcal{P}` be a morphism property of schemes and $`X` be a scheme. The
*small $`\mathcal{P}`-site of $`X`* is the category of $`X`-schemes with
structure morphism satisfying $`\mathcal{P}` and with covers given by
quasi-compact, jointly surjective families of morphisms satisfying
$`\mathcal{P}`.
:::

If we let $`\mathcal{P}` be flat morphisms of schemes, we obtain the fpqc site:

:::definition "def:fpqc-site" (parent := "proetale-topology") (uses := "def:small-P-site") (tags := "mathlib")
Let $`X` be a scheme. The *fpqc site of $`X`*, denoted by $`\fpqc{X}`, is the
$`\mathcal{P}`-site of $`X` with $`\mathcal{P} = \text{flat}`.
:::

For us, the main relevant property of the fpqc site is that it is subcanonical:

:::theorem "thm:fpqc-subcanonical" (parent := "proetale-topology") (uses := "def:fpqc-site") (tags := "mathlib")
The fpqc site is subcanonical, i.e., every representable presheaf is a sheaf.
:::

Analogous to the familiar criterion for fpqc sheaves, we have a generalization
for the small $`\mathcal{P}`-site of a scheme.

:::proposition "prop:fpqc-sheaf-iff" (parent := "proetale-topology") (uses := "def:small-P-site") (tags := "mathlib")
Let $`F` be a presheaf on the small $`\mathcal{P}`-site. Then $`F` is a sheaf
if and only if it is a sheaf in the Zariski topology and satisfies the sheaf
property for $`\{V \to U\}` with $`V`, $`U` affine and $`V \to U` satisfying
$`\mathcal{P}`.
:::

We can now define the main object of this chapter:

:::definition "def:proetale-site" (parent := "proetale-topology") (uses := "def:qc-cover, def:weakly-etale-morphism, def:small-P-site") (tags := "mathlib")
Let $`X` be a scheme. The *pro-étale site of $`X`*, denoted by $`\proet{X}`,
is the $`\mathcal{P}`-site of $`X` with
$`\mathcal{P} = \text{weakly étale}`.
(Bhatt–Scholze, Definition 4.1.1)
:::

Despite the name pro-étale, {bpref "def:proetale-site"}[] does not mention
pro-étale morphisms. The name is justified by
{bpref "thm:weakly-etale-ind-etale"}[] (see also
{bpref "lemma:affproet-gen-proet"}[]).

:::proposition "prop:proet-subcanonical" (parent := "proetale-topology") (tags := "mathlib")
The site $`\proet{X}` is subcanonical.
(Bhatt–Scholze, Lemma 4.2.4)
:::

:::proof "prop:proet-subcanonical" (uses := "thm:fpqc-subcanonical")
Follows from {bpref "thm:fpqc-subcanonical"}[], since every pro-étale sheaf is
an fpqc-sheaf.
:::

## Affine covers

:::definition "def:affproet" (parent := "proetale-topology") (lean := "AlgebraicGeometry.Scheme.AffineProEt")
An object $`U` of $`\proet{X}` is called a *pro-étale affine* if it can be
written as $`U = \lim U_i` over a small cofiltered diagram $`i \mapsto U_i` of
affine schemes étale over $`X`. The subcategory of pro-étale affines in
$`\proet{X}` is denoted by $`\affproet{X}`.
(Bhatt–Scholze, Definition 4.2.1)
:::

:::lemma_ "lemma:affproet-limits" (parent := "proetale-topology") (uses := "def:affproet")
The category $`\affproet{X}` admits limits indexed by a connected diagram and
the forgetful functor to $`\mathrm{Sch} / X` preserves them. If $`X` is affine,
$`\affproet{X}` has all small limits.
(Bhatt–Scholze, Remark 4.2.3)
:::

:::definition "def:affproet-site" (parent := "proetale-topology") (uses := "lemma:affproet-limits, def:affproet") (lean := "AlgebraicGeometry.Scheme.AffineProEt")
Let $`X` be affine. The *affine pro-étale site* of $`X` is the category
$`\affproet{X}`. The covering families are the quasi-compact covers.
:::

In other words, $`\affproet{X}` carries the topology induced by the inclusion
functor $`\affproet{X} \to \proet{X}`. Although the objects of $`\proet{X}` are
weakly étale $`X`-schemes, by {bpref "thm:weakly-etale-ind-etale"}[] the
topology of $`\proet{X}` is still generated by objects in $`\affproet{X}`:

:::proposition "lemma:affproet-gen-proet" (parent := "proetale-topology") (uses := "def:affproet-site") (lean := "AlgebraicGeometry.Scheme.AffineProEt.isCoverDense_toProEt")
The inclusion $`\affproet{X} \to \proet{X}` is cover dense, i.e. for every
object $`Y` of $`\proet{X}`, there exists a cover $`\{U_i \to Y\}_{i \in I}`
with $`U_i` in $`\affproet{X}`.
(Bhatt–Scholze, Lemma 4.2.4)
:::

:::proof "lemma:affproet-gen-proet" (uses := "thm:weakly-etale-ind-etale")
Let $`f\colon Y \to X` be a weakly étale morphism and let $`\{U_i \to X\}` be
an affine open cover of $`X`. If we prove the lemma for each $`U_i` and the
weakly étale morphism $`f^{-1}(U_i) \to U_i`, the lemma follows for $`f` by
taking the joint cover. Thus we may assume that $`X = \spec{A}` is affine.

Now let $`\{U_i \to Y\}` be an affine open cover. Again, if we prove the lemma
for each $`U_i` and the composition $`U_i \to Y \to X`, the claim follows by
joining the covers. Hence we may assume that $`Y = \spec{B}` is affine.

We now have $`A \to B` weakly étale, so by
{bpref "thm:weakly-etale-ind-etale"}[] there exists an ind-étale and faithfully
flat $`B \to B'` such that $`A \to B \to B'` is ind-étale. The cover
$`\{ \spec{B'} \to \spec{B} \}` concludes the proof.
:::

:::corollary "cor:affproet-equivalence" (parent := "proetale-topology") (uses := "def:affproet-site") (lean := "AlgebraicGeometry.Scheme.AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt")
Restriction along the inclusion $`\affproet{X} \to \proet{X}` induces an
equivalence of categories $`\shv{\proet{X}} \to \shv{\affproet{X}}`.
:::

:::proof "cor:affproet-equivalence" (uses := "lemma:affproet-gen-proet")
The functor $`\affproet{X} \to \proet{X}` is fully faithful and makes
$`\affproet{X}` a dense subsite of $`\proet{X}` by
{bpref "lemma:affproet-gen-proet"}[]. Thus the claim follows from the
comparison lemma for sites.
:::

:::corollary "cor:affproet-sheafification-commute" (parent := "proetale-topology") (uses := "def:affproet-site")
Restriction along the inclusion $`\affproet{X} \to \proet{X}` commutes with
sheafification.
:::

:::proof "cor:affproet-sheafification-commute" (uses := "cor:affproet-equivalence")
This follows immediately from {bpref "cor:affproet-equivalence"}[].
:::

We can also compare $`\affproet{X}` to $`\affet{X}`.

:::proposition "prop:pro-affet-equiv-affproet" (parent := "proetale-topology") (uses := "def:affproet-site")
The canonical functor $`\affet{X} \to \affproet{X}` induces an equivalence of
categories $`\pro{\affet{X}} \to \affproet{X}`.
:::

:::proof "prop:pro-affet-equiv-affproet" (uses := "prop:pro-equiv-pro")
By {bpref "prop:pro-equiv-pro"}[], it suffices to show that for every $`U` in
$`\affet{X}`, the image of $`U` in $`\affproet{X}` is co-finitely-presentable.
This follows from the fact that étale morphisms are finitely presented.
:::

## Repleteness

An important property of the pro-étale site is the following:

:::proposition "prop:proet-wc" (parent := "proetale-topology") (uses := "def:weakly-contractible, def:proetale-site")
The category of sheaves on $`\proet{X}` has enough weakly contractible
objects.
(Bhatt–Scholze, Proposition 4.2.8)
:::

:::proof "prop:proet-wc" (uses := "cor:ind-etale-retraction-cover-exists")
TBA.
:::

:::corollary "prop:proet-replete" (parent := "proetale-topology") (uses := "prop:proet-wc, prop:wc-replete")
The category of sheaves on $`\proet{X}` is replete.
:::

# Comparison with étale cohomology

Let $`X` be a scheme. Since an étale map is also weakly étale by
{bpref "lemma:etale-weakly-etale"}[] we may define:

:::definition "def:forget-proet" (parent := "proetale-topology") (uses := "lemma:etale-weakly-etale, def:proetale-site") (lean := "AlgebraicGeometry.Scheme.toProEtale")
We denote by $`\nu = \nu_X` the morphism of sites $`\proet{X} \to \et{X}`
induced by the functor from $`\et{X}` to $`\proet{X}` given by
$`(U \to X) \mapsto (U \to X)`.
:::

:::lemma_ "lemma:forget-proet-continuous" (parent := "proetale-topology") (uses := "def:forget-proet") (lean := "AlgebraicGeometry.Scheme.isContinuous_toProEtale")
The morphism of sites $`\nu` is continuous.
:::

:::proof "lemma:forget-proet-continuous" (uses := "lemma:qc-cover-of-flat-fp")
This follows from the definitions, because every étale covering is a
quasi-compact covering by {bpref "lemma:qc-cover-of-flat-fp"}[].
:::

We denote by $`\nu_{p}\colon \preshv{\proet{X}} \to \preshv{\et{X}}` and
$`\nu^{p}\colon \preshv{\et{X}} \to \preshv{\proet{X}}` the pushforward and
pullback functors on the level of presheaves.

:::lemma_ "lemma:affproet-pushforward-presheaf-filtered-colim" (parent := "proetale-topology") (lean := "AlgebraicGeometry.Scheme.ProEt.preservesRelativeFilteredColimits_lan_toProEtale")
Let $`F` be a presheaf on $`\et{X}`. Then $`(\nu^p F)|_{\affproet{X}}`
preserves filtered colimits.
:::

:::proof "lemma:affproet-pushforward-presheaf-filtered-colim"
Let $`U = \lim_{\lambda} U_{\lambda}` be a cofiltered limit. By definition of
$`\affproet{X}` and because pro-pro-étale is pro-étale, we may assume that the
$`U_{\lambda}` are étale over $`X`. Then
$$`(\nu^p F)|_{\affproet{X}}(\lim U_{\lambda}) = \colim_{\mu} F(V_{\mu}),`
where the $`V_{\mu}` run over factorisations
$`U = \lim U_{\lambda} \to V_{\mu} \to X` where $`V_{\mu} \to X` is étale.
Since the $`U_{\lambda}` are locally of finite presentation over $`X`, they
are finitely presented in the categorical sense. Hence, for every such
factorisation there exists a $`\lambda` such that
$`U = \lim U_{\lambda} \to V_{\mu}` factors via $`U_{\lambda}`. This shows
that the $`U_{\lambda}` lie cofinal in all $`V_{\mu}`, so we obtain
$$`\colim_{\mu} F(V_{\mu}) = \colim_{\lambda} F(U_{\lambda}) = \colim_{\lambda} (\nu^p F)|_{\affproet{X}}(U_{\lambda}).`
:::

:::lemma_ "lemma:affproet-relatively-pro-prepresentable" (parent := "proetale-topology") (uses := "def:one-cover-relatively-pro-prepresentable")
The topology on $`\affproet{X}` is generated by relatively pro-representable
one-hypercovers with respect to the inclusion $`\affet{X} \to \affproet{X}`.
:::

:::proof "lemma:affproet-relatively-pro-prepresentable" (uses := "prop:finite-diag-pro")
The topology on $`\affproet{X}` is generated by surjections $`V \to U` in
$`\affproet{X}` and finite standard Zariski coverings. Both of these can be
relatively pro-represented by {bpref "prop:finite-diag-pro"}[] (see also
{bpref "ex:finite-diag-pro"}[]).
:::

Further denote by $`\nu_{*} \colon \shv{\proet{X}} \to \shv{\et{X}}` and
$`\nu^* \colon \shv{\et{X}} \to \shv{\proet{X}}` the corresponding pushforward
and pullback functors. Since $`\nu^*` is exact, we have $`R \nu^* = \nu^*` by
abuse of notation and we simply write $`\nu^*` everywhere. In contrast to
Bhatt–Scholze, we write $`R \nu_{*}` for the derived functor of $`\nu_{*}`.

:::proposition "prop:presheaf-pushforward-sheaf-affproet" (parent := "proetale-topology") (lean := "AlgebraicGeometry.Scheme.isSheaf_lan_toProEtale, AlgebraicGeometry.Scheme.ProEt.sheafPullbackCompIso")
Let $`F` be a sheaf on $`\et{X}`. Then $`(\nu^p F)|_{\affproet{X}}` is a
sheaf. In particular,
$`(\nu^*F)|_{\affproet{X}} \cong (\nu^p F)|_{\affproet{X}}`.
:::

:::proof "prop:presheaf-pushforward-sheaf-affproet" (uses := "lemma:affproet-relatively-pro-prepresentable, prop:sheaf-relatively-representable-generated, lemma:affproet-pushforward-presheaf-filtered-colim, cor:affproet-sheafification-commute")
By {bpref "lemma:affproet-relatively-pro-prepresentable"}[] and
{bpref "lemma:affproet-pushforward-presheaf-filtered-colim"}[], this follows
from {bpref "prop:sheaf-relatively-representable-generated"}[]. Hence we have
the following chain of isomorphisms
$$`(\nu^*F)|_{\affproet{X}} \cong (\nu^pF)^{\#}|_{\affproet{X}} \cong ((\nu^pF)|_{\affproet{X}})^{\#} \cong (\nu^pF)|_{\affproet{X}}.`
The second isomorphism is {bpref "cor:affproet-sheafification-commute"}[] and
the last is the first part of this proposition.
:::

:::corollary "lemma:pullback-section-affproet" (parent := "proetale-topology") (uses := "lemma:forget-proet-continuous, def:affproet")
Let $`F` be a sheaf on $`\et{X}` and $`U = \lim_i U_i` in $`\affproet{X}`.
Then $`\nu^*F(U) = \colim_i F(U_i)`.
(Bhatt–Scholze, Lemma 5.1.1)
:::

:::proof "lemma:pullback-section-affproet" (uses := "prop:presheaf-pushforward-sheaf-affproet")
By {bpref "prop:presheaf-pushforward-sheaf-affproet"}[] we have
$`(\nu^*F)|_{\affproet{X}} \cong (\nu^p F)|_{\affproet{X}}`. The claim now
follows from {bpref "lemma:affproet-pushforward-presheaf-filtered-colim"}[].
:::

:::corollary "lemma:pullback-unit-iso" (parent := "proetale-topology") (lean := "AlgebraicGeometry.Scheme.ProEt.isIso_unit_sheafAdjunction")
For any $`F \in \shv{\et{X}}`, the unit $`F \to \nu_{*} \nu^{*} F` is an
isomorphism.
:::

:::proof "lemma:pullback-unit-iso" (uses := "lemma:affet-gen-et, lemma:pullback-section-affproet")
By {bpref "lemma:affet-gen-et"}[], we may check this on any affine $`U` étale
over $`X`. Since $`U = \lim U`, the formula of
{bpref "lemma:pullback-section-affproet"}[] shows the desired isomorphism.
:::

:::corollary "lemma:pullback-fully-faithful" (parent := "proetale-topology") (lean := "AlgebraicGeometry.Scheme.ProEt.faithful_sheafPullback, AlgebraicGeometry.Scheme.ProEt.full_sheafPullback")
$`\nu^*` is fully faithful.
(Bhatt–Scholze, Lemma 5.1.2, fully faithful part)
:::

:::proof "lemma:pullback-fully-faithful" (uses := "lemma:pullback-unit-iso")
Follows formally from {bpref "lemma:pullback-unit-iso"}[].
:::

:::definition "def:classical-sheaf" (parent := "proetale-topology") (uses := "def:forget-proet")
A sheaf $`F` in $`\shv{\proet{X}}` is called *classical* if it lies in the
essential image of $`\nu^{*}`.
:::

We can recognize the classical sheaves among all pro-étale sheaves by checking
if they preserve affine filtered colimits:

:::corollary "cor:classical-sheaf-iff-preserves" (parent := "proetale-topology") (uses := "def:classical-sheaf")
A sheaf $`F` in $`\shv{\proet{X}}` is classical if and only if for any
$`U \in \affproet{X}` with presentation $`U = \lim U_i`, it holds that
$`F(U) = \colim F(U_i)`.
(Bhatt–Scholze, Lemma 5.1.2, essential image part)
:::

:::proof "cor:classical-sheaf-iff-preserves" (uses := "lemma:pullback-section-affproet, cor:affproet-equivalence")
The only if part follows directly from
{bpref "lemma:pullback-section-affproet"}[]. Conversely, let $`F` be in
$`\shv{\proet{X}}` and suppose $`F` satisfies the formula in the statement.
Then $`\nu^* \nu_{*} F \to F` is an isomorphism. Indeed, by
{bpref "cor:affproet-equivalence"}[], it suffices to check this after
restricting to $`\affproet{X}`. Let $`U = \lim U_i` be in $`\affproet{X}`.
Then again by {bpref "lemma:pullback-section-affproet"}[]
$$`\nu^* \nu_{*} F (U) = \colim \nu_{*} F(U_i) = \colim F(U_i) = F(U).`
:::

:::lemma_ "lemma:derived-pullback-section-affproet" (parent := "proetale-topology") (uses := "lemma:forget-proet-continuous")
Let $`K` be in $`D^+(\et{X})` and $`U = \lim_i U_i` in $`\affproet{X}`. Then
$`R \Gamma(U, \nu^*K) = \colim_i R\Gamma(U_i, K)`.
(Bhatt–Scholze, Lemma 5.1.6)
:::

:::proof "lemma:derived-pullback-section-affproet" (uses := "lemma:pullback-section-affproet")
TBA.
:::

:::proposition "prop:proetale-etale-iso" (parent := "proetale-topology") (uses := "lemma:forget-proet-continuous")
For any $`K` in $`D^{+}(\et{X})` the unit $`K \to R \nu_{*} \nu^* K` is an
isomorphism.
(Bhatt–Scholze, Corollary 5.1.6)
:::

:::proof "prop:proetale-etale-iso" (uses := "lemma:derived-pullback-section-affproet, lemma:affproet-gen-proet")
TBA.
:::

:::corollary "cor:derived-sections-proetale-etale-iso" (parent := "proetale-topology") (uses := "lemma:forget-proet-continuous")
Let $`K` be in $`D^{+}(\et{X})`. Then
$$`R \Gamma(\et{X}, K) \cong R \Gamma(\proet{X}, \nu^{*} K).`
:::

:::proof "cor:derived-sections-proetale-etale-iso" (uses := "prop:proetale-etale-iso")
By {bpref "prop:proetale-etale-iso"}[], we have
$`R \Gamma(\et{X}, K) \cong R \Gamma(\et{X}, R \nu_{*}\nu^*K)`. Since
$`\nu_*` maps injective sheaves to acyclic ones by general theory, we have
$`R \Gamma(\et{X}, -) \circ R\nu_{*} = R (\Gamma(\et{X}, -) \circ \nu_*) = R \Gamma(\proet{X}, -)`.
So the claim follows.
:::

:::definition "def:continuous-etale-cohomology" (parent := "proetale-topology")
Denote by
$`\gammacont(X, -)\colon \mathrm{Ab}(\et{X})^{\N} \to \mathrm{Ab}` the functor
$$`\left( F_n \right)_{n \in \N} \mapsto \Gamma\left(X, \lim F_n\right).`
For an inverse system $`(F_n)_{n \in \N}`, we call the cohomology groups
$`H^i \mathrm{R} \gammacont\left(X, -\right)\left( \left( F_{n} \right)_{n \in \N} \right)`,
denoted by $`H^i_{\mathrm{cont}}(\et{X}, (F_{n})_{n \in \N})`, the
*continuous étale cohomology* of $`X` with coefficients in
$`\left( F_n \right)_{n \in \N}`.
(Jannsen, §3)
:::

:::theorem "thm:comparison-continuous" (parent := "proetale-topology") (uses := "def:continuous-etale-cohomology, lemma:forget-proet-continuous")
Let $`(F_n)_{n \in \N}` be an inverse system of abelian sheaves on $`\et{X}`
with epimorphic transition maps. Then there exists a canonical identification
$$`R \gammacont(X, (F_n)_n) \cong R \Gamma(\proet{X}, \lim \nu^* F_n).`
In particular, for every $`i \ge 0` we have
$$`H^i_{\mathrm{cont}}(\et{X}, (F_n)_n) \cong H^i(\proet{X}, \lim \nu^* F_n).`
(Bhatt–Scholze, Proposition 5.6.2)
:::

:::proof "thm:comparison-continuous" (uses := "prop:proet-replete, prop:lim-exact-replete, cor:derived-sections-proetale-etale-iso")
We repeatedly use the fact that $`\Gamma` commutes with inverse limits both on
$`\et{X}` and $`\proet{X}`. Then we have
$$`\begin{aligned} R \gammacont(X, (F_n)_n) &\cong R \left( \Gamma(\et{X}, -) \circ \lim \right) ( (F_n)_n ) \\ &\cong R \left( \lim \circ \Gamma(\et{X}, -) \right) ( (F_n)_n ) \\ &\cong R \lim ( R \Gamma(\et{X}, F_n)) \\ &\cong R \lim ( R \Gamma(\proet{X}, \nu^{*} F_n)) \\ &\cong R \left( \lim \circ \Gamma(\proet{X}, -) \right) ( (\nu^* F_n)_n ) \\ &\cong R \left( \Gamma(\proet{X}, -) \circ \lim \right) ( (\nu^* F_n)_n ) \\ &\cong R \Gamma(\proet{X}, R \lim \nu^* F_n) \\ &\cong R \Gamma(\proet{X}, \lim \nu^* F_n) \end{aligned}`
The fourth isomorphism is
{bpref "cor:derived-sections-proetale-etale-iso"}[] and the last is
{bpref "prop:lim-exact-replete"}[].
:::
