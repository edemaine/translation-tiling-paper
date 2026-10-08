---
title: Tiling 3D by Translates of a Single Polycube is Undecidable
author: >-
  [Erik D. Demaine](https://erikdemaine.org/) ·
  [Stefan Langerman](https://algo.ulb.be/sl/)
lang: en
---

Given a single polycube, can copies of it tile three-dimensional space using
only translations? We prove that this problem is undecidable, even when the
polycube is connected through faces. More precisely, the problem is co-RE
complete. Dimension three is optimal: the corresponding problem in two
dimensions is decidable.

## Read the paper

- **[Paper (PDF)](paper.pdf)** — Human-written overview of the results,
  proof ideas, and Lean formalization.
- **[Technical overview (PDF)](slop.pdf)** — LLM-written definitions,
  constructions, and proofs, intended to be read independently.

## Source and formalization

The [GitHub repository](https://github.com/edemaine/translation-tiling-paper)
contains the document sources, figures, finite verification code, and a
complete Lean formalization of the reduction and main results. See the
[formalization notes](https://github.com/edemaine/translation-tiling-paper/blob/main/lean/README.md)
for formal statements, checked proofs, and build instructions.
