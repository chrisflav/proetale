import VersoBlueprint

/-!
KaTeX macro prelude shared by all blueprint chapters. These mirror the macros
from the LaTeX blueprint (`blueprint/src/macros/common.tex`), adapted to
KaTeX-compatible definitions.
-/

open Informal

tex_prelude r#"\newcommand{\proet}[1]{#1_{\text{proét}}}"#
tex_prelude r#"\newcommand{\affproet}[1]{#1^{\text{aff}}_{\text{proét}}}"#
tex_prelude r#"\newcommand{\et}[1]{#1_{\text{ét}}}"#
tex_prelude r#"\newcommand{\affet}[1]{#1^{\text{aff}}_{\text{ét}}}"#
tex_prelude r#"\newcommand{\fpqc}[1]{#1_{\mathrm{fpqc}}}"#
tex_prelude r#"\newcommand{\preshv}[1]{\mathrm{PreShv}(#1)}"#
tex_prelude r#"\newcommand{\shv}[1]{\mathrm{Shv}(#1)}"#
tex_prelude r#"\newcommand{\spec}[1]{\mathrm{Spec}(#1)}"#
tex_prelude r#"\newcommand{\Spec}{\operatorname{Spec}}"#
tex_prelude r#"\newcommand{\gammacont}{\Gamma_{\mathrm{cont}}}"#
tex_prelude r#"\newcommand{\colim}{\operatorname{colim}}"#
tex_prelude r#"\newcommand{\pro}[1]{\mathrm{Pro}(#1)}"#
tex_prelude r#"\newcommand{\sep}{\mathrm{sep}}"#
tex_prelude r#"\newcommand{\Hom}{\operatorname{Hom}}"#
tex_prelude r#"\renewcommand{\N}{\mathbb{N}}"#
tex_prelude r#"\newcommand{\m}{\mathfrak{m}}"#
tex_prelude r#"\newcommand{\n}{\mathfrak{n}}"#
tex_prelude r#"\newcommand{\p}{\mathfrak{p}}"#
tex_prelude r#"\newcommand{\q}{\mathfrak{q}}"#
tex_prelude r#"\newcommand{\tildering}[3]{#1_{\widetilde{(#2, #3)}}}"#
tex_prelude r#"\newcommand{\tildeideal}[2]{\widetilde{(#1, #2)}}"#
