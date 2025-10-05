# Proétale cohomology in Lean

This repository contains a (WIP) formalisation of (pro)étale cohomology in Lean following
the paper [[BS13]](https://arxiv.org/abs/1309.1198) by Bhatt and Scholze.

A long-term goal of this project is to formalise Theorem 5.6.2 in [BS13], which implies the following theorem:
Let $X$ be a variety over an algebraically closed field $k$. Let $l$ be a prime different from the characteristic of $k$. One has
$H^i(X_{ét}, \overline{\mathbb{Q}}_l) = H^i(X_{proét}, \overline{\mathbb{Q}}_l),$
where the RHS is interpreted naively as cohomology of the proétale site of $X$, the LHS is defined as the inverse limit
$H^i(X_{ét}, \overline{\mathbb{Q}}_l) := (\varprojlim_{n} H^i(X_{ét}, \mathbb{Z}/l^n\mathbb{Z})) \otimes_{\mathbb{Z}_l} \overline{\mathbb{Q}}_l.$
