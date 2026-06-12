import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ProetaleBlueprint.Chapters.RepleteCategories

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Pro-étale cohomology" =>

This blueprint tracks the formalisation of (pro)étale cohomology in Lean,
following the paper *The pro-étale topology for schemes* by Bhatt and Scholze.
A long-term goal of the project is Theorem 5.6.2 of that paper, comparing
étale and pro-étale cohomology with $`\overline{\mathbb{Q}}_\ell`-coefficients
for varieties over an algebraically closed field.

{include 0 ProetaleBlueprint.Chapters.RepleteCategories}

{blueprint_graph}
{blueprint_summary}
