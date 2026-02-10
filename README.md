# Gibbs Measures

[![.github/workflows/push.yml](https://github.com/james18lpc/GibbsMeasure/actions/workflows/push.yml/badge.svg)](https://github.com/james18lpc/GibbsMeasure/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/james18lpc/GibbsMeasure)

The purpose of this repository is to *digitise* some mathematical definitions, theorem statements
and theorem proofs. Digitisation, or formalisation, is a process where the source material,
typically a mathematical textbook or a pdf file or website or video, is transformed into definitions
in a target system consisting of a computer implementation of a logical theory (such as set theory
or type theory).

## The source

The definitions, theorems and proofs in this repository are taken from the book [Gibbs Measures and
Phase Transitions](https://doi.org/10.1515/9783110250329) by Hans-Otto Georgii.

The goal is to prove existence and uniqueness of Gibbs measures.

## The target

The formal system which we are using as a target system is Lean's dependent type theory. Lean is a
project being developed by the [Lean FRO](https://lean-lang.org/fro).

## Content

This project currently contains a definition of Gibbs measures, but no construction yet.

### Code organisation

The Lean code is contained in the directory `GibbsMeasure/`. The subdirectories are:
* `Mathlib`: Material missing from existing Mathlib developments
* `Prereqs`: New developments to be integrated to Mathlib

## What next?

On top of the new developments, there are many basic lemmas needed for this project that are
currently missing from Mathlib.

See the [upstreaming dashboard](https://james18lpc.github.io/GibbsMeasure/upstreaming) for more information.

## Getting the project

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://lean-lang.org/install/).
Alternatively, click on the button below to open an Ona workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/james18lpc/GibbsMeasure)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Contributing

**This project is open to contribution.**

## Source reference

[G]: https://doi.org/10.1515/9783110250329
