# Gibbs Measures

[![.github/workflows/push.yml](https://github.com/or4nge19/GibbsMeasure/actions/workflows/push.yml/badge.svg)](https://github.com/or4nge19/GibbsMeasure/actions/workflows/push.yml)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/or4nge19/GibbsMeasure)

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

## Content

Chapter 1 is essentially complete: specifications (1.23), Gibbs measures and the DLR equation
(1.24), the independent specification with `G(λ_·) = {λ^S}` (1.25), λ-modifications and
Proposition (1.30). Remark (1.25) is a corollary of a general fact rather than a computation:
a specification with a **free measure** `μ₀` — `γ_Λ(A|η) = μ₀(A)` for `A ∈ 𝓕_Λ`, Georgii's
`λ_Λ(A|η) = λ^S(A)` — has at most one Gibbs probability measure, namely `μ₀`, and has one exactly
when `μ₀` makes `𝓕_Λ` and `𝓕_{Λᶜ}` independent for every finite `Λ`
(`Specification.eq_of_hasFreeMeasure`, `Specification.isGibbsMeasure_iff_indep_of_hasFreeMeasure`).
Remark **(1.28)(2)**: for positive densities the null events of `𝓕_Δ` are those of the reference
kernel, so all Gibbs measures of a λ-specification share them
(`IsGibbsMeasure.lambdaSpecification_null_iff`).

Chapter 2: potentials, Hamiltonians and the Boltzmann pre-modification (2.1)–(2.6); the space `ℬ` of
absolutely summable potentials (2.11)–(2.14) and the Gibbsian specification `γ^Φ` for `Φ ∈ ℬ` (2.9);
the quasilocal algebra (2.20)–(2.23); and Proposition (2.24)(a)(b) with Example (2.25), so `γ^Φ` is
quasilocal for every `Φ ∈ ℬ` — with (2.24)(b) at Georgii's hypotheses: measurable quasilocal
Hamiltonians, not assumed bounded, over a resampling reference specification or a σ-finite
a-priori measure (`Specification/Quasilocality.lean`).

Chapter 4: the topology of local convergence (4.2) with Hausdorffness (4.3)(1) and the
characterisation by local observables (4.3)(2); the necessary condition (4.4), equicontinuity
(4.5) and local equicontinuity (4.6); the cluster-point Proposition (4.9) via the Kolmogorov
extension theorem (ported from
[kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4)); compactness of
uniformly dominated sets (4.10) and of the whole space of random fields for a finite state space
(4.11)(2); the existence backbone: Theorem (4.17) (limit and cluster-point forms), Comment (4.18)
(thermodynamic limits of quasilocal specifications are Gibbs measures) and Theorem (4.22); and
**Theorem (4.23)(a)**: over a standard Borel state space, for every `Φ ∈ ℬ` the set `G(Φ)` is
non-empty and compact in the topology of local convergence (via the density bound
`ρ_Λ ≤ e^{2|β|‖Φ‖_Λ}` of (4.14)(1) and closedness of `G(γ)` from (4.17)).

Example (4.11)(1): relative compactness of `G(γ)` for bounded-density modifications of the
independent specification.

**First concrete model**: the nearest-neighbour pair potential on a locally finite graph
(`Potential.nearestNeighbourPair`) and the Ising model over `Bool` spins
(`GibbsMeasure/Model/Ising.lean`) — on any countable locally finite graph, in particular on the
lattice `ℤ^d`, the Ising model has a Gibbs measure at every coupling, external field and inverse
temperature, and its set of Gibbs measures is compact in the topology of local convergence
(`latticeIsingGibbsMeasure_nonempty`, `isCompact_setOf_latticeIsingGibbsMeasure`).

Proposition (4.19): uniform convergence `γ^{Φⁱ} → γ^Φ` of Gibbsian specifications from
convergence of the Hamiltonians, with Georgii's quantitative bound
`‖γ^{Φⁱ}_Λ f − γ^Φ_Λ f‖ ≤ 2‖f‖(e^{|β|‖H^{Φⁱ−Φ}_Λ‖} − 1)`; the general net results
**Theorem (4.12)** and **Corollary (4.13)** (eventually-bounded densities on a set of
eventually-full measure; confinement
boxes `K_ℓ^Δ`, in density and Hamiltonian forms) with the bounded-density Comment (4.14)(1)
derived as a corollary; Example (4.20)(1) **free boundary conditions** (the truncated potential
`Φ^Δ`, the tail estimate `‖H^{Φ^Δ−Φ}_Λ‖ ≤ ∑_{A∩Λ≠∅, A⊄Δ}‖Φ_A‖ → 0`, cluster points of the
free-boundary net are Gibbs, and — since the truncation densities are `Δ`-uniformly bounded —
free-boundary thermodynamic limits exist unconditionally over standard Borel state spaces; the
truncations `Φ^Δ` converge to `Φ` in the topology of `ℬ`);
Theorem (4.23)(b) in per-volume and Georgii's per-site forms; and **Theorem (4.23)(c)–(d)**:
the space `ℬ` of absolutely summable potentials (indexed, as in Georgii, by the nonempty finite
sets: `Φ ∅ = 0`) as a separated seminormed `ℝ`-module (per-site seminorms, `WithSeminorms`
topology, `T1`; for countable `S` metrizable and **complete** — Georgii's (2.11) Fréchet
space — with the measurable locus `BSpace` a closed, hence complete, subspace), the Gibbs correspondence
`𝒢 : ℬ → 𝒫(Ω,𝓕)` has closed graph, and `𝒢⁻¹(F)` is closed for every closed `F` — so
**Theorem (4.23) is complete** (throughout, for a probability a-priori measure: Georgii's
finite-`λ` case, WLOG by his Remark (1.28)(3)).

Remark (4.3)(3): for finite `E` (and countable `S`) the topology of local convergence is
metrizable — indeed `WithLocalConvergence S E` is compact metrizable, hence Polish
(`GibbsMeasure/Topology/Metrizable.lean`).

Example (4.16): a genuine (proper, consistent) specification — a single particle at a uniformly
random site — with **no Gibbs measure**; it is not quasilocal (`not_isQuasilocal_specification`),
so quasilocality cannot be dropped from (4.17)/(4.22).

Chapter 5, §5.1 and §5.2: everything in (5.1)–(5.13), (5.17)(1)–(2), (5.18) and (5.20)(1)–(3) is
formalised; Theorem **(5.19)**, Georgii's counterpart to the general
existence theorem (4.22) — a locally equicontinuous net of Cesàro averages of `I`-invariant
finite-volume distributions has a cluster point in `𝒢_I(γ)` — is
`GibbsMeasure/Specification/InvariantExistence.lean`, and the finite-`E` shift-invariant existence
of (5.17)(1)/(5.20)(1) is now derived from it rather than proved directly. Definition **(5.21)**,
broken symmetries, is `GibbsMeasure/Specification/BrokenSymmetry.lean`, with the two-dimensional
phase transition as an instance in `GibbsMeasure/Model/SymmetryBreaking.lean`: at `β ≥ log 3` the
spin flip is a symmetry of the zero-field specification and is broken, which by Georgii's remark
after (5.21) gives non-uniqueness without going through the two explicit phases. The abelian
branch of Theorem **(5.15)(ii)** and Corollary **(5.16)** — an `I`-invariant specification with
`𝒢(γ)` non-empty and compact and `I` abelian has an `I`-invariant Gibbs measure — is
`GibbsMeasure/Specification/InvariantExistenceGroup.lean`
(`exists_mem_GP_and_forall_measurePreserving_of_commute`), by Følner averaging over the abelian
group (`GibbsMeasure/Mathlib/GroupTheory/Foelner.lean` supplies the Følner sets Mathlib's
`IsFoelner` lacks a producer for). The other branch **(5.15)(i)** is proved in the same file at
the hypothesis its proof actually uses — a *left-invariant probability measure* on the acting
group, `exists_mem_GP_and_forall_measurePreserving_of_invariantWeight` — with the compact-group
case (`..._of_compactGroup`) as the corollary in which Haar measure supplies the weight; neither
needs `𝒢(γ)` compact. The two-subgroup `I₁ ∘ I₀` form of (5.15) is proved in both branches
(`exists_mem_GP_and_forall_measurePreserving_of_commute_of_measurePreserving`,
`exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq`), with the
(5.17)(2)-shaped Ising instance (shift- and spin-flip-invariant Gibbs measure at `h = 0`).
Georgii's (ii) is now proved at his own hypotheses — commutativity *modulo* `I₀`
(`τ₁ ∘ τ₂ = τ₂ ∘ τ₁ ∘ τ₀` with `τ₀ ∈ I₀`), `I₀` normalised by `I₁`, and `𝒢_{I₀}(γ)` compact rather
than `𝒢(γ)` (`exists_mem_GP_and_forall_measurePreserving_sup_of_commute_mod_of_measurePreserving`).
Georgii runs a Markov–Kakutani average over `ℤⁿ`; here the generators are adjoined one at a time,
each step a Følner average over the cyclic group `{τ^k}` — whose transport law is `zpow_add`, so
the commutation hypothesis is needed only to keep the previously gained invariance — and the
finite subsets of `I₁` are combined by the finite intersection property in the compact
`𝒢_{I₀}(γ)`. The Følner theorem was generalised in place for it: the composition law is required
only after transporting the starting measure (`map_transAverage_of_transportLaw`), which is what
"homomorphism modulo `I₀`" delivers. In detail: Georgii's
transformation group `T` of configuration space ((5.1),
`GibbsMeasure/Prereqs/Transformation.lean`), its action on potentials ((5.3), `Potential.map`,
with the Hamiltonian/norm/Boltzmann-factor transport of (5.6)(c)), on specifications ((5.4),
(5.5), `Specification.map`, `GibbsMeasure/Specification/Transformation.lean`) and on Gibbs
measures ((5.10), (5.11)); `τ`-invariant specifications ((5.7)); the independent specification
is invariant under `λ`-preserving transformations ((5.6)(a)); the invariant random fields and
the invariant Gibbs measures are `L`-closed ((5.12), (5.13),
`GibbsMeasure/Specification/InvariantFields.lean`); Proposition (5.6)(c) and Corollary (5.9)(b)
at the level of specifications — `γ^{τΦ} = τ(γ^Φ)` for `λ`-preserving `τ`, so a `τ`-invariant
potential has a `τ`-invariant Gibbsian specification (`GibbsMeasure/Potential/GibbsTransformation.lean`);
the Ising specification on `ℤ^d` is shift-invariant, and a unique Ising Gibbs measure is
shift-invariant ((5.11)); Proposition (5.18) (cluster points of averaged Gibbs distributions
are invariant, `GibbsMeasure/Specification/Average.lean`) and Example (5.20)(1) on `ℤ^d`
(`GibbsMeasure/Model/ShiftAverage.lean`): cube-averaged finite-volume Gibbs distributions with a
constant boundary condition cluster at **shift-invariant Gibbs measures**, which therefore exist
for every shift-invariant quasilocal specification over a finite state space — in particular
the Ising model on `ℤ^d` has a shift-invariant Gibbs measure at every coupling, field and
temperature (`exists_latticeIsing_mem_GP_forall_measurePreserving_shift`, Georgii (5.17)(1)); the shift `θ_j` on `ℤ^d`, shift-invariant
potentials and the closed subspace `ℬ_Θ` ((5.2)(1), (5.8)); the Ising potential on `ℤ^d` is
shift-invariant.

Proposition **(5.18)** is proved in Georgii's full generality, with the transformations `τ_α`
varying along the net — the form Example (5.20)(3) needs, since there `τ_N` is the
`Δ_N`-periodic modification of `τ`. Example **(5.17)(2)** adds a *finite* group of site
automorphisms to the shift invariance
(`exists_isGibbsMeasure_shift_and_siteEquiv_invariant`): Georgii's reflection group `R` does not
commute modulo the shifts, so this is branch (i) of (5.15), with the uniform measure on a finite
group as the invariant weight (Mathlib's `uniformOn Set.univ`, shown left invariant); the general fact behind it is that an
additive site bijection conjugates shifts into shifts, `τ_e ∘ θ_j = θ_{ej} ∘ τ_e`. Example
**(5.20)(2)**, free boundary conditions, is
`mem_GP_and_measurePreserving_of_mapClusterPt_truncation`: cluster points of the truncated-potential
net are `I`-invariant Gibbs measures whenever `Φ` is `I`-invariant and the spatial parts of `I`
fix the volumes, because truncation transports (`Potential.map_truncation`) and (5.18) applies
with the one-element family `{Δ_n}`, whose Følner ratio is zero. Example **(5.20)(3)**, periodic
boundary conditions (`GibbsMeasure/Model/PeriodicSymmetry.lean`), needed Georgii's periodic
modification `τ_N` of a *transformation*, `i ↦ π(τ_* π i) + (i − π i)` — a bijection whose
inverse is the periodic modification of `τ⁻¹` — and the identity `σ̃_Δ ∘ τ_N = τ ∘ σ̃_Δ`, from
which the periodic modification of a `τ`-invariant potential is `τ_N`-invariant; then (5.18)
with the varying `τ_N`. The boundary fields are arbitrary, as Georgii says; `I` need only be a
set; the reflection group `R` is replaced by all lattice automorphisms.

Prerequisites filled for Chapter 3 (uniqueness on `ℤ`, Theorem (3.5)), all absent from Mathlib:
the Perron–Frobenius theorem for positive matrices
(`GibbsMeasure/Mathlib/LinearAlgebra/Matrix/PerronFrobenius.lean`, Collatz–Wielandt), Doeblin's
ergodic theorem for positive stochastic matrices (`.../Doeblin.lean`) and Georgii's Theorem
(1.33) — a specification is determined by its singleton kernels
(`GibbsMeasure/Specification/Singleton.lean`).

Two further Mathlib shims: **Pratt's lemma** (dominated convergence against a *varying* `L¹`
bound) and **Scheffé's lemma**
(`GibbsMeasure/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`), used for (7.12)(c);
and **stochastic domination** of measures — `Measure.StochasticallyLE`, monotone observables
integrate monotonically, and two comparable measures of equal mass agreeing on a generating
family of upper sets are equal
(`GibbsMeasure/Mathlib/MeasureTheory/Order/StochasticDomination.lean`) — together with the form
of **Holley's inequality** in which correlation inequalities are applied to boundary conditions
(`GibbsMeasure/Mathlib/MeasureTheory/Order/Holley.lean`, `sum_indicator_le_of_holley`, built on
Mathlib's `holley` in `Mathlib/Combinatorics/SetFamily/FourFunctions.lean`).

**Theorem (7.26), the extreme decomposition**: over a standard Borel state space, every Gibbs
measure is the barycentre of a unique probability weight on the extreme Gibbs measures, and
`μ ↦ w_μ` is an affine bijection `𝒢(γ) ≃ 𝒫(ex 𝒢(γ))`
(`GibbsMeasure/Specification/ExtremeDecomposition.lean`: `exists_unique_weight_extremePoints`,
`extremeDecomposition`, `bijOn_weightOf`, `weightOf_add_smul`). Its ingredients: Georgii's
`(𝒫, 𝒜)`-kernels and the Dynkin uniqueness of the representing weight, Proposition (7.22)
(`GibbsMeasure/Specification/PAKernel.lean`); the `μ`-independent `(𝒢(γ), 𝒯)`-kernel of
Proposition (7.25), built from Lévy's downward theorem and Mathlib's CDF-to-kernel
disintegration (`GibbsMeasure/Specification/GibbsKernel.lean`); and Theorem (7.7)(a).
Its corollaries (`GibbsMeasure/Specification/ExtremeCorollaries.lean`): **(7.28)** every symmetry
of `γ` commutes with the decomposition (`w_{τ(μ)} = τ(w_μ)`, and `μ` is `τ`-invariant iff `w_μ`
is); **(7.7)(d)/(7.29)** distinct extreme Gibbs measures are mutually singular, and
`|ex 𝒢(γ)| ≥ N` iff `𝒢(γ)` contains `N` linearly independent measures; **(7.30)** for finite `E`
and quasilocal `γ`, `𝒢(γ)` is the closed convex hull of the limiting Gibbs measures `𝒢_lim(γ)`.
Georgii's abstract setting of Remark **(7.13)** is `GibbsMeasure/Specification/Abstract.lean` and
`GibbsMeasure/Specification/AbstractPAKernel.lean`: an `AbstractSpecification` is any consistent
family of proper probability kernels from a decreasing family of sub-σ-algebras, with (7.7)(a)/(b)
and the `(𝒫, 𝓣)`-kernel of (7.25) proved at that level. Its payoff is §7.2–7.3 on exchangeability
(`GibbsMeasure/Specification/HewittSavage.lean`, `GibbsMeasure/Specification/DeFinetti.lean`):
Example **(7.16)**, the exchangeable distributions as the invariant measures of the symmetrisation
kernels; the **Hewitt–Savage zero-one law** of Example (7.16) (`measure_symmetric_eq_zero_or_one`); the
identification `ex 𝒫_I` = i.i.d. product measures, Georgii's equation **(7.17)**
(`mem_extremePoints_exchangeable_iff`) — the
substantial half over an *arbitrary* state space, via a subtraction-free symmetrisation estimate
obtained from group translations alone, with no counting of injections; and **de Finetti's theorem
in the version of Dynkin (7.31)** (`existsUnique_mixing_of_isExchangeable`): over a standard Borel
state space every exchangeable probability measure on `E^ℕ` is `∫ λ^ℕ m(dλ)` for a unique
probability measure `m` on `𝒫(E, ℰ)`, the mixture taken as `Measure.bind`. Mathlib has neither
exchangeability nor de Finetti; the new Mathlib-facing prerequisite is
`Measure.measurable_infinitePi` (`GibbsMeasure/Mathlib/Probability/ProductMeasure.lean`), the
measurability of the infinite product measure in its parameters.

Examples **(7.14)** and **(7.15)** come with them. (7.14) is Kolmogorov's zero-one law: the tail
σ-algebra of `⨂ᵢ αᵢ` is trivial, proved from the cofinite-limsup description of `𝓣` and so with
**no countability assumption on `S`** (`forall_tail_measure_eq_zero_or_one_infinitePi`), together
with Georgii's own route — `𝒢(λ_·) = {λ^S}` and its inhomogeneous form `𝒢(isssdFamily ν) =
{⨂ᵢ νᵢ}` (`G_isssd_eq_singleton`, `G_isssdFamily_eq_singleton`), hence extremality. The general
independence input, `⨂ᵢ μᵢ` makes the coordinates inside a set independent of those outside it
for an arbitrary index type, is `ProbabilityTheory.indep_cylinderEvents_compl_infinitePi`.
(7.15): the stationary Markov chain is extreme in `𝒢(γ_P)` and trivial on `𝓣`
(`stationaryChain_mem_extremePoints_G`, `forall_tail_stationaryChain_eq_zero_or_one`).

Examples **(7.18)** and **(7.19)**, product specifications
(`GibbsMeasure/Specification/ProductSpecification.lean`): on the disjoint union `S₁ ⊕ S₂` of two
site sets, `γ¹ × γ²` is a specification with `γ_Λ(·|ω¹ω²) = γ¹_{Λ∩S₁}(·|ω¹) × γ²_{Λ∩S₂}(·|ω²)`,
products of Gibbs measures are Gibbs, and `ex 𝒢(γ¹ × γ²) = {μ¹ × μ² : μᵏ ∈ ex 𝒢(γᵏ)}` — a
bijection, so `|ex 𝒢|` multiplies and an iterated product prescribes the number of phases. Two
general facts came out of it: properness of a parallel composition of kernels with Fubini for
parallel binds, and the zero-one law for a product measure over a *double* intersection of
σ-algebras (`Measure.prod_apply_eq_zero_or_one_iInf`) — the product of the two tail σ-algebras is
strictly too small to contain the tail of `E^{S₁ ⊕ S₂}`, which is the trap in Georgii's one-line
"it follows from the definition of product σ-algebras".

**Theorem (7.12)**: for an extreme Gibbs measure `μ` the finite-volume distributions
`γ_{Λ_n}(·|ω)` converge to `μ` for `μ`-a.e. `ω` (setwise, and in the topology of local
convergence for finite `E`), so `ex 𝒢(γ) ⊆ 𝒢_lim(γ) ⊆ 𝒢(γ)` (`GibbsMeasure/Specification/LocalLimits.lean`).
**Theorem (7.12)(c)**, the uniform form, is proved too, over an arbitrary measurable state space
(`GibbsMeasure/Specification/UniformLocalLimits.lean`): for a λ-specification `γ = ρ λ` and
`μ ∈ ex 𝒢(γ)`, the convergence `γ_{Λ_n}(·|ω) → μ` holds for `μ`-a.e. `ω` **in total variation on
the events of each finite volume `Δ`**, `sup {|γ_{Λ_n}(A|ω) − μ(A)| : A ∈ 𝓕_Δ} → 0`
(`ae_tendsto_iSup_ofReal_abs_sub`,
`GibbsMeasure.ae_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G`, and
`ae_tendsto_iSup_ofReal_abs_sub_lambdaSpecification` for the λ-specifications of Definition
(1.27)) — Georgii's own argument, run through the densities via Lévy's downward theorem and
Scheffé's lemma.

**Theorem (6.9), the two-dimensional Ising phase transition** — the theorem the book is named
for. Both assertions of the numbered theorem are proved.

*Second assertion* (`GibbsMeasure/Model/PhaseTransition.lean`): for every `β ≥ 8 log 2` the
ferromagnetic Ising model on `ℤ²` with coupling `1` and no external field has two *distinct*
shift-invariant Gibbs measures `μ₊ ≠ μ₋ = τ(μ₊)` (`τ` the spin flip) with
`μ₊(σ₀ = -1) < 1/2 < μ₋(σ₀ = -1)`, hence `|𝒢(βΦ)| > 1`
(`exists_two_shiftInvariant_gibbs` with the explicit threshold,
`nontrivial_GP_isingSpecification_of_large_beta`), and spontaneous magnetisation
`∫ σ₀ dμ₋ < 0 < ∫ σ₀ dμ₊` (`exists_spontaneous_magnetisation`).

*First assertion* (`GibbsMeasure/Model/LowTemperatureLimit.lean`):
`lim_{β→∞} d(𝒢_Θ(βΦ), δ_±) = 0` (`tendsto_localDistSet_shiftInvariantGibbs_dirac`), where `d` is
the metric of Georgii Remark (4.3)(3) for the topology of local convergence — built here as a
genuine `MetricSpace` instance inducing that topology (`localDist`, `localMetricSpace`) — via
`tendsto_r_atTop` and Georgii's estimate `|μ₊(f) − δ₊(f)| ≤ 2‖f‖ |Λ| r(β)`
(`abs_integral_plusPhase_sub_le`).

Its Peierls prerequisites, all topology-free: the contour machinery on `ℤ²` (`GibbsMeasure/Model/Contours.lean`) — plaquette
adjacency of bonds (Georgii's dual bonds sharing a dual vertex), the unique infinite component
of a finite set's complement, and **Lemma (6.14)**: the outer edge boundary of a finite
connected set is connected in the plaquette-adjacency graph, proved by an explicit `ℤ/2`
coboundary argument (Timár's cycle-space step made elementary) instead of Georgii's appeal to
the Jordan curve theorem; and (`GibbsMeasure/Model/PeierlsEstimate.lean`) the Ising
energy–contour identity `H_Λ(ζ) = -(|B_Λ| - 2|B_Λ ∩ B*(ζ)|)`, the flip estimate (6.15) in
edge-boundary form `γ_Λ^{βΦ}(∂D ⊆ B*(·) | ω) ≤ e^{-2β|∂D|}` (for every real `β`), and the
contour counting (6.13).

Georgii's **own** contour count is proved in `GibbsMeasure/Model/SharpContours.lean`: the
degree-two property `n_c(u) = 2` for the outer boundary of a finite connected set — all four
cases, including the one Georgii settles with the Jordan curve theorem, here by a mod-2 argument
with no topology — the resulting circuit structure, and hence `ℓ · 3^{ℓ−1}` circuits of length
`ℓ` through a fixed bond, against the crude `4096^ℓ` for arbitrary plaquette-connected bond
sets. With it, `GibbsMeasure/Model/SharpPhaseTransition.lean` re-derives (6.9) at
**`β ≥ log 3 ≈ 1.099`** instead of `8 log 2 ≈ 5.545`
(`exists_two_shiftInvariant_gibbs_sharp`, `ising_two_dimensional_phase_transition_sharp`), the
two temperature ranges remaining disjoint since `1/4 < log 3`.

**Chapter 8, Dobrushin's uniqueness condition.** Dobrushin's interdependence matrix `C(γ)`
((8.5)) and his condition of weak dependence ((8.6)); the oscillation calculus (8.14)/(8.15),
the estimates (8.16)/(8.17) and Lemma (8.18); the **comparison theorem (8.20)**; and
**Theorem (8.7)** in full: under Dobrushin's condition `|𝒢(γ)| ≤ 1`, and `= 1` over a standard
Borel state space — the existence half coming from Georgii's conditioned specification (8.22) and
the Cauchy argument of (8.23) (`GibbsMeasure/Specification/DobrushinUniqueness.lean`:
`existsUnique_mem_GP_of_isDobrushin_of_standardBorel`). Dobrushin's condition is formalised as
Georgii states it in (8.6) — quasilocality *and* `c(γ) < 1`; his Example (2.27) — now formalised — has `C(γ) ≡ 0`
yet uncountably many Gibbs measures, so the first conjunct is not decorative:
`GibbsMeasure/Specification/GluedFamily.lean` builds Remark (2.26), the specification glued from a
measurable family along a tail-measurable parameter, and `GibbsMeasure/Model/Exchangeable.lean`
gives the Bernoulli instance with `interdep_gammaEx i j = 0`, `not_countable_gibbsMeasures` and
`not_isQuasilocal_gammaEx`, packaged as
`exists_not_countable_gibbsMeasures_of_tsum_interdep_lt_one`. Deleting quasilocality from (8.6)
would therefore make (8.7) false. The criterion **(8.8)** —
`sup_i ∑_{A ∋ i} (|A| − 1) δ(Φ_A) < 2` implies Dobrushin's condition, with Georgii's sharp
constant 2, proved at Georgii's hypotheses: a σ-finite non-zero a-priori measure and a merely
λ-admissible potential, with the self-potential unrestricted
(`Dobrushin.isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible`; the quasilocality input is
Proposition (2.24)(b) at Georgii's hypotheses — unbounded quasilocal Hamiltonians — in
`GibbsMeasure/Specification/Quasilocality.lean`) — and its instance for the
Ising model, `isDobrushin_isingSpecification`
(`GibbsMeasure/Model/IsingDobrushin.lean`). Together with (6.9) this brackets the critical
temperature of the two-dimensional Ising ferromagnet from both sides: uniqueness at high
temperature, non-uniqueness at low temperature. Griffiths' monotonicity — the GKS inequalities
(`GibbsMeasure/Model/GKSInequalities.lean`: `corr_nonneg`, `corr_mul_corr_le`, `corr_mono`,
`corr_mono_beta`, `plusMagnetisation_mono`) — turns the bracket into a critical inverse
temperature: `β_c := inf {β ≥ 0 : |𝒢(βΦ)| > 1}` is a well-defined real number with
`artanh(1/4) ≤ β_c ≤ log 3`, and **both** halves are unconditional: uniqueness for every
`0 ≤ β < β_c` and
non-uniqueness for every `β_c < β` (`GibbsMeasure/Model/SharpCriticalTemperature.lean`:
`isingBetaC`, `isingBetaC_mem_Icc`, `existsUnique_of_lt_isingBetaC`, `nontrivial_of_isingBetaC_lt`,
`ising_sharp_phase_transition`). What used to be the hypothesis `IsUpperSet isingNonUniqueness` is
now the theorem `isUpperSet_isingNonUniqueness`, because the **Lebowitz–Martin-Löf/Ruelle
equivalence** `|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` — which Georgii cites without proving it — is proved in
`GibbsMeasure/Model/LebowitzMartinLof.lean`
(`nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos`). Nothing is asserted at `β = β_c`.
Onsager's exact value `β_c = ½ log(1+√2)` is not proved here. Georgii states it in the remarks
after (6.9) without proof, referring to the Bibliographical Notes.

Two different senses of "sharp" occur in these names and should not be conflated. In
`ising_sharp_phase_transition` it means the *dichotomy* is sharp: a single threshold `β_c` with
uniqueness strictly below and non-uniqueness strictly above. In `SharpPhaseTransition.lean` and
`exists_two_shiftInvariant_gibbs_sharp` it means the *Peierls threshold* has been sharpened, from
`8 log 2` to `log 3`, by replacing the `4096^ℓ` contour count with Georgii's `ℓ·3^(ℓ-1)`. **`log 3`
is a sufficient contour-counting threshold, an upper bound for `β_c`, not the critical value.** The
proved bracket is `1/4 ≤ β_c ≤ log 3`; Onsager's `½ log(1+√2) ≈ 0.4407` lies inside it and is not
proved.

That equivalence rests on two new pieces. **Holley's inequality for the Ising ferromagnet**
(`GibbsMeasure/Model/IsingFKG.lean`): the finite-volume distribution is stochastically increasing
in the boundary condition, hence decreasing in the volume under the all-plus condition. It reduces
to submodularity of the Hamiltonian, `H_Λ(η ⊓ ζ) + H_Λ(η ⊔ ζ) ≤ H_Λ(η) + H_Λ(ζ)`, because
`juxt Λ ω ζ ⊓ juxt Λ ω' ξ = juxt Λ ω (ζ ⊓ ξ)` for `ω ≤ ω'` collapses the boundary bonds into the
interior ones. And the **plus state as a genuine monotone limit** — not a compactness cluster point
— with the sandwich `μ₋ ≼ μ ≼ μ₊` for every Gibbs measure (`GibbsMeasure/Model/PlusPhase.lean`:
`plusState`, `tendsto_measure_plusState`, `plusState_mem_GP`, `stochasticallyLE_plusState`). No
coupling theorem is used: two stochastically comparable measures of equal mass that agree on a
generating family of upper sets are equal
(`GibbsMeasure/Mathlib/MeasureTheory/Order/StochasticDomination.lean`), so Strassen's theorem —
absent from Mathlib — is not needed.

**Chapter 8 beyond Dobrushin.** Proposition **(8.38)** is a uniqueness criterion for an *arbitrary*
specification: if some `c > 0` makes every cylinder event `A` admit a volume `Λ` with
`γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all boundary conditions, then `|𝒢(γ)| ≤ 1`
(`GibbsMeasure/Specification/OneDimensionalUniqueness.lean`,
`subsingleton_G_of_isUniformlyDominated`). Theorem **(8.39)**, uniqueness in one dimension under
decay of the interaction, is its corollary, at Georgii's own hypotheses: Definition (2.2)
summability rather than absolute summability, any σ-finite non-zero λ-admissible a priori measure,
and both `S = ℤ` and `S = ℕ` — through `HasBoundedBoundary`, an abstraction of "exhausted by
intervals with a bounded number of boundary sites". Georgii's Comments (8.41) come with it, ending
in `subsingleton_G_lambdaSpecification_of_pair_rpow_le`: a shift-invariant pair potential on `ℤ`
with `δ(Φ_{0,n}) ≤ c n^{-p}`, `p > 2`, has at most one Gibbs measure — uniqueness far past the
nearest-neighbour Markov case of (3.5). The second half of (8.39), `|𝒢(Φ)| = 1` rather than
`≤ 1`, follows Georgii's own reduction and is proved at his hypotheses
(`existsUnique_mem_GP_lambdaSpecification_of_iSup_oscSpan_ne_top`). It needs three things that
were missing. §2.4, equivalence of potentials, is `GibbsMeasure/Potential/Equivalence.lean`, with
`isAbsolutelySummable_centre_iff`: the class of `Φ` meets `ℬ` exactly when `∑_{A ∋ i} δ(Φ_A) < ∞`
at every site — the sharp form of Georgii's normalisation `‖Φ_A‖ = δ(Φ_A)/2`. Under (8.40) that
holds for the many-body part, since a volume of at least two sites containing `i` spans `i` or its
predecessor. And the self-energies `Φ_{i}` are absorbed into per-site a priori measures
`λ_i = e^{-β Φ_{i}} λ`, over which (4.23)(a) is re-proved
(`GibbsMeasure/Potential/PerSiteExistence.lean`); their integrability is λ-admissibility at
`Λ = {i}`. Getting there generalised the existence machinery off the homogeneous reference
measure: `Specification.IsResampling` for quasilocality, `Specification.HasFreeMeasure` for local
equicontinuity. The a priori measure is any `λ ∈ 𝓜(E,ℰ)`, as in the book: Georgii's own (4.23)
assumes `λ` finite, and (8.39) reaches the σ-finite case because the measures `e^{-βΦ_{i}}λ` the
reduction produces are themselves finite — which is how it is done here too.

Chapter 4 is complete: Proposition **(4.15)** (a cluster point of a locally equicontinuous
sequence is a subsequential limit, `GibbsMeasure/Topology/Subsequence.lean`) and Example
**(4.20)(2)**, periodic boundary conditions — torus reduction, the periodic continuation
`σ̃_Δ`, `A*`, representatives, the periodic modification `Φ̃^Δ`, and the fact that cluster
points of the periodic finite-volume Gibbs distributions are Gibbs measures for `Φ`
(`GibbsMeasure/Potential/Periodic.lean`; the concrete instantiation is carried out for `S = ℤ`,
the general theory applies verbatim to `ℤ^d` once a torus reduction and anchor are supplied).

**Theorem (3.5)**: over a finite state space the positive homogeneous Markov specifications on
`ℤ` are exactly the Gibbsian specifications of the homogeneous nearest-neighbour potentials
`-log P` for a positive stochastic matrix `P`, and each has the stationary Markov chain `μ_P` as
its **unique** Gibbs measure — `𝒢(γ_P) = {μ_P}` (`GibbsMeasure/Model/MarkovChain.lean`:
`gibbsMeasure_eq_singleton`, `exists_matrix_eq_markovSpecification`). Corollary **(3.9)** is an
iff over the general homogeneous nearest-neighbour potential `Φ_{i} = φ₁(σ_i)`,
`Φ_{i,i+1} = φ₂(σ_i, σ_{i+1})` (`isPositiveHomogeneousMarkov_iff_exists_homogeneousNNSpecification`),
and Georgii's **(3.13)–(3.19)** come with it: the one-dimensional Ising potential is such a
potential, its determining function is (3.14), the Perron–Frobenius eigenvalue of the associated
matrix is `q_{J,h} = e^{-h}(cosh h + √(e^{-4J} + sinh²h))` (3.16), formula (3.7) produces the
transfer matrix (3.17), so `𝒢(βΦ^{J,h})` is the singleton `{μ_{βJ,βh}}` — **(3.15)**, no phase
transition in one dimension — with stationary distribution (3.18) and magnetisation
`sinh h / √(e^{-4J} + sinh²h)` (3.19). The correspondence `g ↔ P` uses the Perron–Frobenius
theorem and Doeblin's ergodic theorem, both of which had to be built
(`GibbsMeasure/Mathlib/LinearAlgebra/Matrix/`).

**Theorem (2.30), the Gibbs representation theorem** (`GibbsMeasure/Potential/GibbsRepresentation.lean`):
every positive quasilocal pre-modification is Gibbsian for a unique `a`-normalised gas potential,
so the DLR and Hamiltonian frameworks agree — and, when `log ρ_Λ` is bounded, for a unique
`α`-normalised potential for each `α ∈ 𝓟(E)`, its second assertion. The gas potential is built at
an arbitrary reference configuration and the `α`-normalised one is that potential averaged over
the reference configuration, so the second assertion integrates the first. Corollaries **(2.31)**
(finite `E`, counting measure) and **(2.32)** (a Markov premodifier is represented by a
nearest-neighbour potential, `Potential.IsNearestNeighbour`) come with it; (2.32) holds for the
vacuum potential too, with no boundedness hypothesis, which Georgii does not state.

**Chapter 14, ergodicity** (`GibbsMeasure/Specification/Ergodicity.lean`): Georgii's invariant
σ-algebra `𝓘` ((14.2), `MeasurableSpace.invariants` for any group action), Remark (14.3) — a
function is `𝓘`-measurable iff it is invariant, and an a.s.-invariant event has a strictly
invariant companion, its orbit — and **Theorem (14.5)** in full, (a)–(d), for any *countable*
subgroup of the transformation group, as Georgii's footnote licenses: ergodic ⟺ extreme in `𝓟_Θ`,
the density of an absolutely continuous invariant measure is `𝓘`-measurable, `μ ∈ 𝓟_Θ` is
determined by its restriction to `𝓘`, and distinct ergodic measures are singular *on `𝓘`*.
Ergodicity (14.6) is Mathlib's `ErgodicSMul`, not a second definition. Georgii's shift group is
`shiftGroup S E`, an honest `Subgroup`. **Proposition (14.9)**, `𝓘 ⊆ 𝓣` mod `μ` for any group of
transformations that moves every finite volume off itself (hence tail-trivial ⟹ ergodic), rests on
a Borel–Cantelli lemma for an *infimum* of σ-algebras now in the Mathlib layer; **(14.14)**
`𝒢_Θ(γ) = 𝒢(γ) ∩ 𝓟_Θ` and **Theorem (14.15)** follow in Georgii's own order — (c) `𝒢_Θ(γ)` is a
face of `𝓟_Θ`, then (a) `ex 𝒢_Θ(γ) = 𝒢_Θ(γ) ∩ ex 𝓟_Θ` and (b) — with no shift-invariance of `γ`
consumed by any proof (`GibbsMeasure/Specification/ErgodicGibbs.lean`). Of Appendix 14.A, the
**ergodic maximal inequality (14.A6)** is proved (`GibbsMeasure/Mathlib/Dynamics/Ergodic/MaximalInequality.lean`):
Georgii's `μ(sup_n |R_n f| > c) ≤ 3^d μ(|f|)/c` for increasing cubes in `ℤ^d`, as the instance of
a Tempelman-type inequality over any additive group acting by measure-preserving maps, with the
greedy Vitali selection a corollary of Mathlib's covering lemma. Mathlib has no pointwise ergodic
theorem at all — not even for a single transformation — so the mean and individual theorems
(14.A3), (14.A5), (14.A8) are being built on top of this.

Not yet done: the inhomogeneous Ising chains of §6.1, Shlosman's random staircases of §6.3
(Theorem (6.21)), Examples (5.17)(3)–(4) (instances of (5.15) recorded as such), Mermin–Wagner
(9.20), the rest of Chapter 14 — the mean and individual ergodic theorems (14.A3)/(14.A5)/(14.A8),
(14.7), (14.10)–(14.12), (14.16)–(14.25) — and Chapters 10–13 and 15–20 (Markov fields on trees,
Gaussian fields, the variational principle, the Poulsen simplex, reflection positivity, and the
infrared bound).

### Code organisation

The Lean code is contained in the directory `GibbsMeasure/`. The subdirectories are:
* `Mathlib`: Material missing from existing Mathlib developments
* `Prereqs`: New developments to be integrated to Mathlib

## What next?

On top of the new developments, there are many basic lemmas needed for this project that are
currently missing from Mathlib.

See the [upstreaming dashboard](https://or4nge19.github.io/GibbsMeasure/upstreaming) for more information.

## Getting the project

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://lean-lang.org/install/).
Alternatively, click on the button below to open an Ona workspace containing the project.

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/or4nge19/GibbsMeasure)

In either case, run `lake exe cache get` and then `lake build` to build the project.

## Contributing

**This project is open to contribution.**

## Source reference

[G]: https://doi.org/10.1515/9783110250329
