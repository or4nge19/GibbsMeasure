---
# On main, CI copies README.md over this file for deployment.
---

# Gibbs Measures

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the book [Gibbs Measures and
Phase Transitions](https://doi.org/10.1515/9783110250329) by Hans-Otto Georgii.

The goal is to follow Georgii's four basic questions about the set `G(γ)` of Gibbs measures for a
specification `γ` (Section 1.2): (A) how to construct specifications, (B) when `G(γ)` is non-empty
(Chapter 4), (C) for which `γ` it is a singleton (Chapter 8), and (D) what its structure is when it
is not (Chapters 6, 7 and Parts II–IV). Non-uniqueness is the subject of the book: `|G(Φ)| > 1` is a
phase transition, so there is no global uniqueness theorem to prove.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed by the [Lean FRO](https://lean-lang.org/fro).

## Content of this project

See [README.md](https://github.com/or4nge19/GibbsMeasure/blob/main/README.md) for the chapter-by-chapter
inventory. The library has no `sorry`.

### Code organisation

The Lean code is contained in the directory `GibbsMeasure/`. The subdirectories are:
* `Mathlib`: Material missing from existing Mathlib developments
* `Prereqs`: New developments to be integrated to Mathlib

## What next?

On top of the new developments, there are many basic lemmas needed for this project that are
currently missing from Mathlib.

Here is the list of files that do not depend on any other GibbsMeasure file, indicating they are good
candidates for upstreaming to Mathlib:

{% include files_to_upstream.md %}

## Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://lean-lang.org/install/).
Alternatively, click on the button below to open an Ona workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/or4nge19/GibbsMeasure)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Build the blueprint

See instructions at https://github.com/PatrickMassot/leanblueprint/.

## Acknowledgements

Our project builds on Mathlib. We must therefore thank its numerous contributors without whom this
project couldn't even have started.

Much of the project infrastructure has been adapted from
* [sphere eversion](https://leanprover-community.github.io/sphere-eversion/)
* [liquid tensor experiment](https://github.com/leanprover-community/liquid/)
* [unit fractions](https://github.com/b-mehta/unit-fractions/)

## Source reference

`[G]` : https://doi.org/10.1515/9783110250329

[G]: https://doi.org/10.1515/9783110250329
