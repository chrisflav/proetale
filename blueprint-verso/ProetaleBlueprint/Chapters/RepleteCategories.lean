import Verso
import VersoManual
import VersoBlueprint
import Proetale.Replete.Basic
import Proetale.Replete.WeaklyContractible

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Replete categories" =>

Let $`\mathcal{C}` be a category with limits. By $`\mathrm{Ab}(\mathcal{C})`
we denote its abelian group objects.

:::group "replete"
Replete categories, coherent objects, and weakly contractible objects,
following Section 3 of Bhatt–Scholze.
:::

:::author "proetale_project" (name := "Proétale Project")
:::

:::definition "def:replete" (parent := "replete") (lean := "CategoryTheory.IsReplete")
We say $`\mathcal{C}` is *replete* if epimorphisms are stable under sequential
limits, i.e., if $`(F_n)_{n \in \mathbb{N}}` is an inverse system in
$`\mathcal{C}` such that $`F_{n+1} \to F_n` is an epimorphism for all
$`n \in \mathbb{N}`, then $`\lim F_n \to F_n` is an epimorphism for all
$`n \in \mathbb{N}`. (Bhatt–Scholze, Definition 3.1.1)
:::

The following examples are all not needed later, but are useful to gain some
intuition for {bpref "def:replete"}[repleteness].

* The category of sets is replete (Bhatt–Scholze, Example 3.1.4).
* Let $`k` be a field and $`\bar k` a separable closure of $`k`. Then the
  category of sheaves on the small étale site of $`\operatorname{Spec} k` is
  replete if and only if $`\bar k` is a finite extension of $`k`
  (Bhatt–Scholze, Example 3.1.5).
* The category of fpqc sheaves, i.e., sheaves on the big fpqc site, is replete
  (Bhatt–Scholze, Example 3.1.7).

:::lemma_ "lemma:replete-lim-lim-epi" (parent := "replete")
Let $`\mathcal{C}` be {uses "def:replete"}[replete] and let
$`(F_n)_{n \in \mathbb{N}} \to (G_n)_{n \in \mathbb{N}}` be a morphism of
inverse systems in $`\mathcal{C}`. If $`F_n \to G_n` and
$`F_{n+1} \to F_n \times_{G_n} G_{n+1}` are epimorphisms for each
$`n \in \mathbb{N}`, then $`\lim F_n \to \lim G_n` is an epimorphism.
(Bhatt–Scholze, Lemma 3.1.8)
:::

:::proposition "prop:replete-products-exact" (parent := "replete") (uses := "lemma:replete-lim-lim-epi")
If $`\mathcal{C}` is replete, countable products are exact.
(Bhatt–Scholze, Proposition 3.1.9)
:::

:::proposition "prop:lim-exact-replete" (parent := "replete") (uses := "prop:replete-products-exact, lemma:replete-lim-lim-epi")
Let $`\mathcal{C}` be replete. If $`(F_n)_{n \in \mathbb{N}}` is an inverse
system in $`\mathrm{Ab}(\mathcal{C})` with epimorphic transition maps, then
$`\lim F_n \cong \mathrm{R}\lim F_n`.
(Bhatt–Scholze, Proposition 3.1.10)
:::

# Coherent objects

:::definition "def:compact-object" (parent := "replete")
An object $`X` of $`\mathcal{C}` is *compact* if the top element of the poset
of subobjects of $`X` is a *compact element*.
:::

:::definition "def:stable-object" (parent := "replete")
An object $`X` of $`\mathcal{C}` is *stable* if for all compact $`Y` and
morphisms $`Y \to X`, the fiber product $`Y \times_X Y` is compact.
:::

:::definition "def:coherent-object" (parent := "replete") (uses := "def:stable-object, def:compact-object")
An object $`X` of $`\mathcal{C}` is *coherent* if it is compact and stable.
:::

# Weakly contractible categories

From now on, we assume that pullbacks in $`\mathcal{C}` preserve epimorphisms.
For example this holds in abelian categories and (pre)topoi.

:::definition "def:weakly-contractible" (parent := "replete") (lean := "CategoryTheory.WeaklyContractible")
An object $`F` of $`\mathcal{C}` is called *weakly contractible* if every
epimorphism $`G \to F` has a section. We say $`\mathcal{C}` has *enough weakly
contractible objects*, if every object admits an epimorphism from a weakly
contractible one. (Bhatt–Scholze, Definition 3.2.1)
:::

:::lemma_ "remark:wc-projective" (parent := "replete") (uses := "def:weakly-contractible") (lean := "CategoryTheory.Projective.iff_forall_isSplitEpi_of_hasPullbacks")
Under our assumptions on $`\mathcal{C}`, an object $`F` is weakly contractible
if and only if it is projective.
:::

:::definition "def:lwc" (parent := "replete") (uses := "def:coherent-object, def:weakly-contractible")
We say $`\mathcal{C}` is *locally weakly contractible*, if each $`X` in
$`\mathcal{C}` admits an epimorphism from the coproduct of $`Y_i`, where
$`Y_i` is coherent and weakly contractible.
(Bhatt–Scholze, Definition 3.2.1)
:::

If $`\mathcal{C}` is {bpref "def:lwc"}[locally weakly contractible], it has
enough weakly contractible objects: the coproduct of projective objects is
projective. For example, the category of sets is locally weakly contractible.

:::lemma_ "lemma:wc-epi-criterion" (parent := "replete") (uses := "def:weakly-contractible") (lean := "CategoryTheory.EnoughProjectives.epi_iff_forall_projective")
Let $`\mathcal{C}` have enough weakly contractible objects and $`F \to G` be a
morphism. Then $`F \to G` is an epimorphism if and only if for every weakly
contractible $`Y` in $`\mathcal{C}`, the induced map
$`F(Y) = \mathrm{Hom}(Y, F) \to \mathrm{Hom}(Y, G) = G(Y)` is surjective.
:::

:::proof "lemma:wc-epi-criterion"
Choose an epimorphism $`e \colon P \to G` where $`P` is weakly contractible
and lift that to $`P \to F`.
:::

:::proposition "prop:wc-replete" (parent := "replete") (uses := "def:weakly-contractible, def:replete")
If $`\mathcal{C}` has enough weakly contractible objects, it is replete.
:::

:::proof "prop:wc-replete"
This follows from {uses "lemma:wc-epi-criterion"}[], the fact that
$`\mathrm{Hom}(Y, -)` commutes with limits and the corresponding statement in
the category of sets.
:::
