# Reducing Reactive to Strong Bisimilarity

This repository contains all the files related to my [Bachelor's thesis](https://maxpohlmann.github.io/Reducing-Reactive-to-Strong-Bisimilarity/thesis.pdf). More information can be found in the thesis itself.

I am proud to say that my thesis has been cited by Rob van Glabbeek in the paper an earlier version of which my thesis is based on (van Glabbeek, R. Reactive bisimulation semantics for a process algebra with timeouts. Acta Informatica (2022). https://doi.org/10.1007/s00236-022-00417-1).

## Thesis Abstract

I show that it is possible to reduce the problem of checking strong reactive bisimilarity, as introduced by Rob van Glabbeek ([here](https://arxiv.org/abs/2008.11499)), to checking ordinary strong bisimilarity. I do this by specifying a mapping that effectively yields a model of the closed system consisting of the original reactive systemand its environment. I formalised all concepts discussed in this thesis, and conducted all the proofs, in the interactive proof assistant [Isabelle](https://isabelle.in.tum.de/).

## Files in Repo

- `thesis.pdf` is the thesis document
- `presentation.pdf` contains the slides from a presentation (/defense) of my thesis
- `index.html` is the index of the web presentation of the Isabelle theory files, \
available through the [GitHub Pages of this repo](https://maxpohlmann.github.io/Reducing-Reactive-to-Strong-Bisimilarity/)
- `web/` contains the files for these Pages
- `isabelle/` contains the Isabelle source code, from which both the web version as well as the thesis document were generated using the [Isabelle Document Preparation System](https://isabelle.in.tum.de/doc/system.pdf)
