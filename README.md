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
Proposition (1.30).

Chapter 2: potentials, Hamiltonians and the Boltzmann pre-modification (2.1)–(2.6); the space `ℬ` of
absolutely summable potentials (2.11)–(2.14) and the Gibbsian specification `γ^Φ` for `Φ ∈ ℬ` (2.9);
the quasilocal algebra (2.20)–(2.23); and Proposition (2.24)(a)(b) with Example (2.25), so `γ^Φ` is
quasilocal for every `Φ ∈ ℬ`.

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

From Chapter 7: Theorem (7.7), extreme ⟺ tail-trivial.

Proposition (4.19): uniform convergence `γ^{Φⁱ} → γ^Φ` of Gibbsian specifications from
convergence of the Hamiltonians, with Georgii's quantitative bound
`‖γ^{Φⁱ}_Λ f − γ^Φ_Λ f‖ ≤ 2‖f‖(e^{|β|‖H^{Φⁱ−Φ}_Λ‖} − 1)`; the **general net Theorems
(4.12)–(4.13)** (eventually-bounded densities on a set of eventually-full measure; confinement
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

Chapter 5, §5.1 and most of §5.2: everything in (5.1)–(5.13) and (5.17)(1)/(5.18)/(5.20)(1) is
formalised; Theorem **(5.19)**, Georgii's counterpart to the general
existence theorem (4.22) — a locally equicontinuous net of Cesàro averages of `I`-invariant
finite-volume distributions has a cluster point in `𝒢_I(γ)` — is
`GibbsMeasure/Specification/InvariantExistence.lean`, and the finite-`E` shift-invariant existence
of (5.17)(1)/(5.20)(1) is now derived from it rather than proved directly. Definition **(5.21)**,
broken symmetries, is `GibbsMeasure/Specification/BrokenSymmetry.lean`, with the two-dimensional
phase transition as an instance in `GibbsMeasure/Model/SymmetryBreaking.lean`: at `β ≥ log 3` the
spin flip is a symmetry of the zero-field specification and is broken, which by Georgii's remark
after (5.21) gives non-uniqueness without going through the two explicit phases. Still missing are
Theorem (5.15) and its Corollary (5.16), which need a Følner net for an abelian group — Mathlib has
`IsFoelner` but no theorem producing one, and no amenability definition. In detail: Georgii's
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
constant 2 — and its instance for the Ising model, `isDobrushin_isingSpecification`
(`GibbsMeasure/Specification/Dobrushin.lean`). Together with (6.9) this brackets the critical
temperature of the two-dimensional Ising ferromagnet from both sides: uniqueness at high
temperature, non-uniqueness at low temperature. Griffiths' monotonicity — the GKS inequalities
(`GibbsMeasure/Model/GKSInequalities.lean`: `corr_nonneg`, `corr_mul_corr_le`, `corr_mono`,
`corr_mono_beta`, `plusMagnetisation_mono`) — turns the bracket into a critical inverse
temperature: `β_c := inf {β ≥ 0 : |𝒢(βΦ)| > 1}` is a well-defined real number with
`1/4 ≤ β_c ≤ log 3`, and **both** halves are unconditional: uniqueness for every `0 ≤ β < β_c` and
non-uniqueness for every `β_c < β` (`GibbsMeasure/Model/SharpCriticalTemperature.lean`:
`isingBetaC`, `isingBetaC_mem_Icc`, `existsUnique_of_lt_isingBetaC`, `nontrivial_of_isingBetaC_lt`,
`ising_sharp_phase_transition`). What used to be the hypothesis `IsUpperSet isingNonUniqueness` is
now the theorem `isUpperSet_isingNonUniqueness`, because the **Lebowitz–Martin-Löf/Ruelle
equivalence** `|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` — which Georgii cites without proving it — is proved in
`GibbsMeasure/Model/LebowitzMartinLof.lean`
(`nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos`). Nothing is asserted at `β = β_c`.
Onsager's exact value is not proved here, and Georgii does not prove it either — the digitised text
does not state it.

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
in `subsingleton_G_of_pair_rpow_le`: a shift-invariant pair potential on `ℤ` with
`δ(Φ_{0,n}) ≤ c n^{-p}`, `p > 2`, has at most one Gibbs measure — uniqueness far past the
nearest-neighbour Markov case of (3.5). The second half of (8.39), `|𝒢(Φ)| = 1` rather than `≤ 1`,
is proved only for an absolutely summable potential over a probability a priori measure, because
existence (4.23)(a) is available only there; that is the one place where a stated result is weaker
than the book.

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
`gibbsMeasure_eq_singleton`, `exists_matrix_eq_markovSpecification`), whence Georgii (3.15).
The correspondence `g ↔ P` uses the Perron–Frobenius theorem and Doeblin's ergodic theorem, both
of which had to be built (`GibbsMeasure/Mathlib/LinearAlgebra/Matrix/`).

**Theorem (2.30), the Gibbs representation theorem** (`GibbsMeasure/Potential/GibbsRepresentation.lean`):
every positive quasilocal pre-modification is Gibbsian for a unique `a`-normalised gas potential,
so the DLR and Hamiltonian frameworks agree.

Not yet done: the inhomogeneous Ising chains of §6.1, Shlosman's random staircases of §6.3
(Theorem (6.21)), the long-range 1D uniqueness theorem (8.39), Mermin–Wagner (9.20), and
Chapters 10–20 (Markov fields on trees, Gaussian fields, the variational principle, the Poulsen
simplex, reflection positivity, and the infrared bound).

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
