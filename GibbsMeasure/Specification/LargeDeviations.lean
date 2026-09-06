/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.StrictConvexSubgradient
public import GibbsMeasure.Mathlib.Probability.LargeDeviations.Legendre
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.UniformAverage
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.SetwiseConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import GibbsMeasure.Mathlib.Topology.Semicontinuity.EReal
public import GibbsMeasure.Specification.PhaseTransition

/-!
# Large deviations and the equivalence of ensembles (Georgii §15.5)

Throughout, `S = ℤ^d` is spelled `ι → ℤ` for a finite type `ι`, `λ` is an a priori *probability*
measure `ν` on `E`, and potentials live in Georgii's Banach space `ℬ_Θ`
(`Potential.BTheta (ι → ℤ) E`, `Specification/TangentFunctional.lean`). The inputs are §15.2
(`Specification/SpecificEntropy.lean`), §15.3 (`Specification/Pressure.lean`) and §15.4
(`Specification/VariationalPrinciple.lean`).

## The periodic empirical field, Georgii Definition (15.41)

`MeasureTheory.GibbsMeasure.periodicEmpiricalField E π Δ ω`, Georgii's `°R^ω_Δ` (15.42), is the
uniform average `|Δ|⁻¹ ∑_{i ∈ Δ} δ_{θ_{-i} ω^∘_Δ}` of the Dirac measures at the translates of the
periodic continuation `ω^∘_Δ = Potential.periodicExtend π ω` of `ω_Δ` along a torus reduction `π`
of the box `Δ` (Georgii Example (4.20)(2), `Potential.IsTorusReduction`, in
`GibbsMeasure/Potential/Periodic.lean`). It is stated for an arbitrary additive group of sites.

* `MeasureTheory.GibbsMeasure.integral_periodicEmpiricalField`: `°R^ω_Δ f` is the spatial average
  `|Δ|⁻¹ ∑_{i ∈ Δ} f(θ_{-i} ω^∘_Δ)`.
* `MeasureTheory.GibbsMeasure.map_shift_periodicEmpiricalField` and
  `MeasureTheory.GibbsMeasure.periodicEmpiricalField_mem_invariantFields`: **Georgii's remark
  after (15.41)**, `°R^ω_Δ ∈ 𝓟_Θ`. The shift `θ_j` permutes the translates through the bijection
  `i ↦ π (i − j)` of the torus `Δ`, since the periodic continuation only sees sites modulo the
  periods (`MeasureTheory.GibbsMeasure.shift_shift_periodicExtend`).
* `MeasureTheory.GibbsMeasure.apply_shift_periodicExtend_eq`,
  `MeasureTheory.GibbsMeasure.abs_sum_apply_shift_periodicExtend_sub_le` and
  `MeasureTheory.GibbsMeasure.abs_integral_periodicEmpiricalField_sub_le`: **Georgii Remark
  (15.43)(1)**, a `B`-local observable does not distinguish `θ_{-i} ω` from `θ_{-i} ω^∘_Δ` when
  `B + i ⊆ Δ`, so `‖°R_Δ f − R_Δ f‖ ≤ 2‖f‖ |T| / |Δ|` for any `T ⊇ {i ∈ Δ : B + i ⊄ Δ}`;
  `MeasureTheory.GibbsMeasure.tendsto_integral_periodicEmpiricalField_sub_zero` is Georgii's
  statement `‖°R_Δ f − R_Δ f‖ → 0`, the bound being independent of the configuration.
* `MeasureTheory.GibbsMeasure.specificEnergy_periodicEmpiricalField`: **Georgii Remark
  (15.43)(3)**, `⟨°R^ω_Δ, Φ⟩ = |Δ|⁻¹ ∑_{i ∈ Δ} f_Φ(θ_{-i} ω^∘_Δ)`, the identity behind Step 1 of
  the proof of (15.46).

## The empirical field of an ergodic random field, Georgii Remark (15.43)(2) and (15.44)

* `MeasureTheory.GibbsMeasure.ae_tendsto_integral_periodicEmpiricalField`: for an ergodic
  `μ ∈ 𝓟_Θ` — trivial on the invariant σ-algebra `𝓘`, which by (14.5)(a) is `μ ∈ ex 𝓟_Θ` — and a
  bounded local observable `f`, `°R^ω_{Λ_n}(f) → μ(f)` for `μ`-almost every `ω`, along any
  increasing sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` with `s_n → ∞` and *arbitrary* torus
  reductions `π_n`. This is Remark (15.43)(1) above together with the ergodic theorem (14.A8)
  (`MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp_cube`) applied along the reflected
  cubes `−Λ_n`, since `f ∘ θ_{-i} = f((-i) +ᵥ ·)`, and the Følner property of cubes
  (`MeasureTheory.GibbsMeasure.tendsto_card_filter_add_notMem_div_card`).
* `MeasureTheory.GibbsMeasure.tendsto_eLpNorm_integral_periodicEmpiricalField_sub_one`: the same
  convergence in `L¹(μ)`, `∫ |°R^ω_{Λ_n}(f) − μ(f)| dμ(ω) → 0`, along an **arbitrary** sequence of
  cubes with `s_n → ∞`. This uses only the *mean* ergodic theorem (14.A5)
  (`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one`), whose hypothesis on
  the volumes is the Følner property alone; Georgii's monotonicity of the cubes enters only
  through the individual ergodic theorem (14.A8), i.e. only in the almost sure statement above.
* `MeasureTheory.GibbsMeasure.tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt`:
  **(15.44)** itself, `μ(°R_{Λ_n} ∈ U) → 1` for a basic neighbourhood
  `U = {ν : |ν(f_j) − μ(f_j)| < ε, j = 1, …, k}` of `μ` in the topology of local convergence
  (Georgii (4.2)). Being a statement about convergence *in probability*, it follows from the `L¹`
  convergence by Markov's inequality and holds along an arbitrary sequence of cubes — which is
  how Georgii states it, and how he proves it (he refers to (14.A5), not to (14.A8)).

## The rate function, Georgii (15.48), (15.49)

* `Potential.BTheta.energyVec Ψ μ = ⟨μ, Ψ⟩ ∈ ℝ^k`, Georgii's continuous map `e_Ψ`, and
  `Potential.BTheta.dotPotential t Ψ = t · Ψ ∈ ℬ_Θ`.
* `Potential.BTheta.ldRate ν Φ Ψ x`, **Georgii (15.49)**:
  `J_Ψ(x|Φ) = inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ, ⟨ν, Ψ⟩ = x}`.
* `Potential.BTheta.specificRelativeEntropy_sub_dotPotential_add`, Georgii's identity in the proof
  of (15.49): for `μ ∈ 𝓟_Θ`, `𝓀(μ|Φ − t·Ψ) + (P(Φ) + t·⟨μ, Ψ⟩ − P(Φ − t·Ψ)) = 𝓀(μ|Φ)`. Everything
  below is a consequence of it. It is stated additively so that it holds also when `𝓀(μ) = −∞`.
* `Potential.BTheta.coe_le_ldRate`, **(15.49), the elementary half of the Legendre duality**:
  `t·x − P(Φ − t·Ψ) + P(Φ) ≤ J_Ψ(x|Φ)` for every `t ∈ ℝ^k`.
* `Potential.BTheta.ldRate_eq_iSup`, **Georgii (15.49) in full**:
  `J_Ψ(x|Φ) = sup_{t ∈ ℝ^k} [t·x − P(Φ − t·Ψ)] + P(Φ)`, and
  `Potential.BTheta.iSup_sub_ldRate_eq`, the dual identity
  `sup_x [t·x − J_Ψ(x|Φ)] = P(Φ − t·Ψ) − P(Φ)`: the rate function and the pressure difference are
  convex conjugates of each other. Georgii extends the functional `t·Ψ ↦ t·x` from the span of
  `Ψ¹, …, Ψᵏ` to `ℬ_Θ` by Hahn–Banach and identifies the extension with a random field by Theorem
  (16.13). The proof here stays in `ℝ^k`: it separates `(x, c)` from the closed convex epigraph of
  `J_Ψ(·|Φ)` (`Potential.BTheta.ldRateEpigraph`, `Potential.BTheta.convex_ldRateEpigraph`,
  `Potential.BTheta.isClosed_ldRateEpigraph`) by
  `eq_iSup_sub_of_isClosed_convex_epigraph` of
  `GibbsMeasure/Mathlib/Probability/LargeDeviations/Legendre.lean`, the Fenchel–Moreau theorem in
  the form a rate function needs, which Mathlib does not have. The conjugate of `J_Ψ(·|Φ)` is
  *attained*, at a shift-invariant Gibbs measure of the tilted potential
  (`Potential.BTheta.exists_specificRelativeEntropy_eq_pressure_sub`), and that is exactly the
  variational principle (15.39).
* `Potential.BTheta.ldRate_smul_add_smul_le`: **Corollary (15.48)**, `J_Ψ(·|Φ)` is *convex*, from
  the concavity half of Proposition (15.14)
  (`Potential.BTheta.specificRelativeEntropy_smul_add_smul_le`, which needs no shift
  invariance).
* `Potential.BTheta.isCompact_setOf_ldRate_le`, `Potential.BTheta.isClosed_setOf_ldRate_le` and
  `Potential.BTheta.lowerSemicontinuous_ldRate`: **Corollary (15.48)**, the level sets
  `{J_Ψ(·|Φ) ≤ c}` are *compact*, being the `e_Ψ`-images of the compact level sets of `𝓀(·|Φ)`.
* `Potential.BTheta.ldRate_nonneg`, `Potential.BTheta.exists_ldRate_eq_zero` and
  `Potential.BTheta.ldRate_eq_zero_iff` (the last two over a standard Borel `E`):
  `J_Ψ(·|Φ) ≥ 0`, `J_Ψ(·|Φ)` is not identically `+∞`, and `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`, the
  last assertion of **Corollary (15.48)**.
* `Potential.BTheta.iInf_specificRelativeEntropy_eq_iInf_ldRate`, Georgii's **contraction step**
  in the proof of (15.48): `inf {𝓀(ν|Φ) : ⟨ν, Ψ⟩ ∈ B} = inf_{x ∈ B} J_Ψ(x|Φ)`. It is the
  regrouping of an infimum over the `e_Ψ`-preimage of `B` by the fibres of `e_Ψ`, and is proved
  directly from `iInf₂_le` and `le_iInf₂`; no limit theorem enters.
* `Potential.BTheta.continuous_energyVec`: `e_Ψ` is continuous for the topology of local
  convergence — the input the contraction principle of Corollary (15.48) consumes on top of the
  regrouping above.

## The shape of `J_Ψ(·|Φ)` for `k = 1`, Georgii Example (15.50)

* `Potential.BTheta.ldRate_eq_zero_iff_mem_Icc`, **Example (15.50), first assertion**: over a
  standard Borel state space `J_Ψ(·|Φ)` attains its minimum `0` exactly on the interval
  `[∂⁻_{−Ψ}P(Φ), ∂⁺_{−Ψ}P(Φ)]` of the one-sided derivatives at `t = 0` of `t ↦ P(Φ − tΨ)`. This
  is Remark (16.6) and Theorem (16.14) of `GibbsMeasure/Specification/TangentFunctional.lean` and
  `GibbsMeasure/Specification/PhaseTransition.lean` applied to `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`.
* `Potential.BTheta.ldRate_le_ldRate_of_le`, **Example (15.50), second assertion**: `J_Ψ(·|Φ)` is
  monotone to the right of that interval, by convexity.
* `Potential.BTheta.ldRate_pos`: strictly above `a⁺` the rate function is strictly positive,
  Georgii's `0 < J_Ψ(a|Φ)`.
* `Potential.BTheta.iInf_ldRate_Ioi_eq`: `inf {J_Ψ(y|Φ) : y > a} = J_Ψ(a|Φ)` whenever
  `a ≥ ∂⁺_{−Ψ}P(Φ)` and `J_Ψ(·|Φ)` is finite somewhere above `a`. This is what makes the two
  inequalities of Corollary (15.48) meet on a half-line, i.e. what turns them into the
  asymptotics (15.51) of `GibbsMeasure/Specification/LargeDeviationsCorollaries.lean`.

## Compactness of the level sets, Georgii's remark after (15.45)

* `Potential.BTheta.isClosed_setOf_specificRelativeEntropy_le`,
  `Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le` (standard Borel `E`) and
  `Potential.BTheta.lowerSemicontinuous_specificRelativeEntropy`: the level sets
  `{𝓀(·|Φ) ≤ c}` are compact in the topology of local convergence, because `𝓀` is upper
  semicontinuous with compact level sets (Proposition (15.14)) and `⟨·, Φ⟩` is bounded and
  continuous.
* `Potential.BTheta.exists_specificRelativeEntropy_eq_ldRate` and its real form
  `Potential.BTheta.exists_specificRelativeEntropy_eq_coe_of_ldRate_le`: hence the infimum
  defining `J_Ψ(x|Φ)` is **attained** whenever it is finite — the remark Georgii makes about the
  right-hand side of (15.46).

## The equivalence of ensembles, Georgii (15.59), (15.60)

* `Potential.BTheta.iInf_ldRate_interior_eq_iInf_closure`, **Georgii (15.59)**: for a convex
  `B ⊆ ℝ^k` whose interior meets the essential domain of `J_Ψ(·|Φ)`,
  `inf_{B̄} J_Ψ(·|Φ) = inf_{B°} J_Ψ(·|Φ)`. This is hypothesis (15.56) of the minimum free energy
  principle, and it is what makes the microcanonical conditioning of Corollary (15.58)
  legitimate.
* `Potential.BTheta.mem_invariantG_sub_dotPotential_of_isMinOn` and its set form
  `Potential.BTheta.subset_invariantG_sub_dotPotential`, **Georgii (15.60)**: if `μ ∈ 𝓟_Θ`
  minimises `𝓀(·|Φ)` among the shift-invariant random fields with the same specific `Ψ`-energy
  `x = ⟨μ, Ψ⟩`, and if `t ∈ ℝ^k` is a subgradient of `J_Ψ(·|Φ)` at `x`, then
  `μ ∈ 𝒢_Θ(Φ − t·Ψ)`. This is the *minimum free energy principle*: the constrained
  (microcanonical) minimisers of the free energy are the unconstrained (grand canonical) Gibbs
  measures of the potential tilted by the Lagrange multiplier `t`.

  Georgii obtains `t` from the differentiability of `J_Ψ(·|Φ)` on the interior of its essential
  domain (Rockafellar), which he gets from the strict convexity of `t ↦ P(Φ + t·Ψ)`; here the
  differentiability is replaced by the subgradient inequality it produces, which is what the
  proof actually consumes.
* `Potential.BTheta.subgradient_ldRate_unique`, the **uniqueness half of that
  differentiability**, i.e. the convex-analytic input of **Corollary (15.58)**: if
  `t ↦ P(Φ − t·Ψ)` is strictly convex then `J_Ψ(·|Φ)` has at most one subgradient at each point of
  its essential domain. A subgradient `t` of `J_Ψ(·|Φ)` at `x` makes the supremum of
  `Potential.BTheta.iSup_sub_ldRate_eq` attained at `x`, so the functional `s ↦ s·x` supports
  `t ↦ P(Φ − t·Ψ)` at `t`, and a strictly convex function is supported by a given functional at
  one point at most (`StrictConvexOn.eq_of_mem_subgradientAt` of
  `GibbsMeasure/Mathlib/Analysis/Convex/StrictConvexSubgradient.lean`).

## Not proved here

Both halves of **Theorem (15.45)** are proved, but not at Georgii's generality:

* the **lower bound (15.47)**, with the "in particular" clause for the Gibbs measures, is
  `neg_iInf_specificRelativeEntropy_le_liminf_log_iInf_gibbsSpecification` (in
  `MeasureTheory.GibbsMeasure`) of `GibbsMeasure/Specification/LargeDeviationsLower.lean`, over an
  *arbitrary* measurable state space;
* the **upper bound (15.46)**, with its "in particular" clause, is
  `MeasureTheory.GibbsMeasure.limsup_log_iSup_gibbsSpecification_div_card_le_closedConvexHull` of
  `GibbsMeasure/Specification/LargeDeviationsUpper.lean`, over a **standard Borel** state space and
  under Georgii's hypothesis `C ∈ 𝓔(𝓟_Θ)`, but with his `cx̄ C` (the closed convex hull) on the
  right; with `C̄` on the right it is `…_of_convex` for a convex `C`, and
  `…limsup_log_iSup_gibbsSpecification_div_card_le` for an arbitrary `C` over a **finite** state
  space. Georgii's Step 3, the passage from `cx̄ C` to `C̄` for which he cites Phelps' Choquet
  theory, is `iInf_closedConvexHull_eq_iInf_closure_ereal` of
  `GibbsMeasure/Specification/InvariantFieldsBarycenter.lean`; it is the only step of his proof
  that is finite-only.

What §15.5 still lacks:

* **Georgii's `C̄` in (15.46) for a non-convex `C` over an infinite state space.** Steps 1, 2
  and 4 are formalised over a standard Borel state space, with the compactness of the sublevel
  sets `{𝓀(·|Φ) ≤ c}` (Proposition (15.14)) in place of the compactness of the whole space of
  random fields. Step 3 is not, and Georgii's change of topology — a countable core `𝒞 ⊆ 𝓕⁰`
  (Corollary (4.A13)) and the compact metrizability of `𝓟(Ω, 𝓕)` in the `𝒞`-topology (Comment
  (4.A10)(1)), both formalised in `GibbsMeasure/Topology/CountableCore.lean` — bounds the infimum
  over the `𝒞`-closure of `C`, not over its closure in the topology of local convergence, and the
  resulting bound is weaker than the `cx̄ C` bound already proved. See the module documentation of
  `GibbsMeasure/Specification/LargeDeviationsUpper.lean`.
* the **finiteness of `J_Ψ(·|Φ)` on `]a⁻_f, a⁺_f[`** asserted in **Example (15.50)** — `a^±_f`
  the infimum and supremum of the support of `f(λ)`. Georgii states it without proof; it is what
  supplies the point `b > a` at which the rate function is still finite in the hypotheses of
  `MeasureTheory.GibbsMeasure.tendsto_log_periodicBoundaryGibbs_setOf_le_spatialMean_div_card`,
  the asymptotics (15.51), which is otherwise complete. Its proof is the exponential tilt
  `ρ_t = e^{tf} λ / λ(e^{tf})`: the i.i.d. field `ρ_t^{⊗ℤ^d}` is shift invariant with specific
  `Ψ`-energy `∫ f dρ_t` and finite excess free energy, and `t ↦ ∫ f dρ_t` sweeps out
  `]a⁻_f, a⁺_f[`. That construction is not carried out here.
* the last sentence of **Example (15.50)**, **Cramér's theorem**: for `Φ = 0`,
  `°γ^0_Λ = λ^Λ` and `J_Ψ(a|0) = sup_t [ta − log λ(e^{tf})]`. What is missing is the pressure of a
  self-potential, `P(−tΨ) = log λ(e^{tf})`; the Legendre formula (15.49)
  (`Potential.BTheta.ldRate_eq_iSup`) would then give the displayed identity at once.
* the cluster-point half of **Corollary (15.58)**, i.e. `clust °γ^{Φ|Ψ,B}_Λ ≠ ∅` and the
  identification of `t` as the gradient of `J_Ψ(·|Φ)` on `B̄_min ∩ D°`. The other half — that
  every minimiser of the free energy under the constraint is Gibbsian for the tilted potential —
  is (15.60) below, `Potential.BTheta.subset_invariantG_sub_dotPotential`, and (15.59) is
  `Potential.BTheta.iInf_ldRate_interior_eq_iInf_closure`. Two ingredients are wanting: the
  compactness argument that produces a cluster point of the conditioned measures
  `°γ^{Φ|Ψ,B}_Λ` (available over a finite state space from the machinery of (15.46), Step 4 of
  `GibbsMeasure/Specification/LargeDeviationsUpper.lean`, together with
  `Potential.empiricalFieldAverage_periodicBoundaryGibbs_cond_apply`, Georgii's identity
  `σ_Λ(°γ^B_Λ °R_Λ) = °γ^B_Λ`), and the differentiability of `J_Ψ(·|Φ)` on the interior of its
  essential domain, which Georgii takes from Rockafellar (1970), p. 253. Of the latter the
  *uniqueness* half is proved — `Potential.BTheta.subgradient_ldRate_unique` — and what is still
  missing is the *existence* of a subgradient of `J_Ψ(·|Φ)` at a point of the interior of its
  essential domain, i.e. that the supremum in (15.49) is attained there; Mathlib has the
  subdifferential of a real-valued convex function on a normed space
  (`ConvexOn.subgradientAt_nonempty`) but nothing for an `EReal`-valued one.

Everything else that §15.5 asserts is proved here: **Corollary (15.48)** in full — the two
displayed inequalities for `°γ^Φ_Λ`
(`MeasureTheory.GibbsMeasure.limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le` and
`MeasureTheory.GibbsMeasure.neg_iInf_ldRate_le_liminf_log_periodicBoundaryGibbs_setOf_mem` of
`GibbsMeasure/Specification/LargeDeviationsCorollaries.lean`), the convexity of `J_Ψ(·|Φ)`, the
compactness of its level sets, `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))` and the Legendre formula (15.49) —
the Gibbs distributions with periodic boundary conditions themselves and Georgii's remark after
(15.47) that both inequalities of Theorem (15.45) hold for them
(`GibbsMeasure/Specification/PeriodicBoundaryGibbs.lean`), **Example (15.50)** apart from the two
items listed above (`Potential.BTheta.ldRate_eq_zero_iff_mem_Icc`,
`Potential.BTheta.ldRate_le_ldRate_of_le`, `Potential.BTheta.iInf_ldRate_Ioi_eq` and the
asymptotics (15.51)), and the minimum free energy principle (15.59), (15.60) that carries the
equivalence of ensembles.

The **theorem of McMillan** `ν(| |Λ|⁻¹ log f_Λ + 𝓀(ν)|) → 0`, which is what makes the event `A_Λ`
in the proof of (15.47) typical for `ν̃`, is **no longer an obstruction**. Georgii invokes it only
for the randomly shifted independent-block field `ν̃ = γ̃` of Proposition (15.52), whose density in
a volume that is a union of tiles factorises over the independent blocks; the statement is then the
`L¹` law of large numbers for the i.i.d. block variables, i.e. the mean ergodic theorem for a
Bernoulli field. That is proved for an *arbitrary* measurable state space and an arbitrary a priori
probability measure in `GibbsMeasure/Specification/BlockMcMillan.lean`
(`MeasureTheory.GibbsMeasure.tendsto_integral_abs_inv_card_sum_llr_sub`, and in the form the proof
of (15.47) consumes, `MeasureTheory.GibbsMeasure.tendsto_measure_setOf_prod_rnDeriv_le` and
`MeasureTheory.GibbsMeasure.tendsto_tileProduct_setOf_blockDensity_le_specificEntropy`). No
standard Borel hypothesis and no finiteness of `E` enters. The general Shannon–McMillan(–Breiman)
theorem of `GibbsMeasure/Specification/ShannonMcMillan.lean`, which is available only over a finite
state space (`blockProb` is the probability of an atom, the wrong object as soon as the single-site
marginals are diffuse), is *not* needed for (15.47).

The remaining inputs to (15.47) — the neighbourhood basis of the topology of local convergence,
(15.44) for an arbitrary open set, the finite-volume Gibbs lower bound
`γ^Φ_Λ(A | ω) ≥ e^{−b − log Z_Λ(ω)} λ^S(A)` and Georgii's estimate (15.25) in the form
`|H_Λ(y) − |Λ| ⟨°R^y_Λ, Φ⟩| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` — are in
`GibbsMeasure/Specification/LargeDeviationsLower.lean`, together with the assembly of (15.47)
itself. The combinatorial ingredient the assembly needs — for an *arbitrary* cube `Λ`, the union
`Δ` of the tiles of `Λ(m)` meeting `Λ` satisfies `|Δ| / |Λ| → 1`, and its tile-index set is
Følner in `p ℤ^d` — is `tendsto_card_tileHull_div_card` and
`tendsto_card_vadd_tileIdxImage_Icc_symmDiff_div_card` (in `MeasureTheory.GibbsMeasure`,
`GibbsMeasure/Specification/BlockMcMillan.lean`).

Another input, **Proposition (15.52)** (`𝓀` of the randomly shifted independent-block measure
`γ̄ = |Λ|⁻¹ ∑_{j ∈ Λ} θ_{-j}(∏_i θ_{-pi}(γ))` equals `|Λ|⁻¹ 𝓗_Λ(γ)`), is
`MeasureTheory.GibbsMeasure.specificEntropy_tileAverage` in
`GibbsMeasure/Specification/BlockEntropy.lean`, with the additivity of the relative entropy over
the independent blocks (`InformationTheory.klDiv_pi`) and the `|Λ|`-ary form of Proposition
(15.14) for measures invariant only under the block lattice; the measure is
`MeasureTheory.GibbsMeasure.tileAverage` of `GibbsMeasure/Specification/ErgodicDense.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Topology symmDiff

noncomputable section

/-! ### Georgii Definition (15.41): the periodic empirical field -/

namespace MeasureTheory.GibbsMeasure

section PeriodicEmpiricalField

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {G : AddSubgroup S} {Δ : Finset S} {π : S → S}

variable (E) in
/-- **Georgii Definition (15.41), (15.42).** The *periodic empirical field*
`°R^ω_Δ = |Δ|⁻¹ ∑_{i ∈ Δ} δ_{θ_{-i} ω^∘_Δ}` of a configuration `ω` in the box `Δ`, where
`ω^∘_Δ = Potential.periodicExtend π ω` is the periodic continuation of `ω_Δ` along a torus
reduction `π` of `Δ` (Georgii Example (4.20)(2), `Potential.IsTorusReduction`). It depends on
`ω` only through `ω_Δ`. -/
def periodicEmpiricalField (π : S → S) (Δ : Finset S) (ω : S → E) : Measure (S → E) :=
  uniformAverage (fun i ↦ Measure.dirac ((shift E (-i)).toFun (Potential.periodicExtend π ω))) Δ

lemma periodicEmpiricalField_apply (π : S → S) (Δ : Finset S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    periodicEmpiricalField E π Δ ω A = (#Δ : ℝ≥0∞)⁻¹ *
      ∑ i ∈ Δ, A.indicator 1 ((shift E (-i)).toFun (Potential.periodicExtend π ω)) := by
  rw [periodicEmpiricalField, uniformAverage_apply]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ Measure.dirac_apply' _ hA)

/-- The periodic empirical field is a probability measure. -/
instance isProbabilityMeasure_periodicEmpiricalField (π : S → S) {Δ : Finset S}
    [NeZero (#Δ)] (ω : S → E) : IsProbabilityMeasure (periodicEmpiricalField E π Δ ω) :=
  isProbabilityMeasure_uniformAverage _ (fun _ ↦ Measure.dirac.isProbabilityMeasure)
    (Finset.card_pos.1 (Nat.pos_of_ne_zero (NeZero.ne _)))

/-- **Georgii (15.42).** Integration against the periodic empirical field is the spatial average
over `Δ` of the translates of the periodic continuation. -/
theorem integral_periodicEmpiricalField (π : S → S) (Δ : Finset S) (ω : S → E)
    {f : (S → E) → ℝ} (hf : StronglyMeasurable f) :
    ∫ η, f η ∂(periodicEmpiricalField E π Δ ω)
      = (#Δ : ℝ)⁻¹ * ∑ i ∈ Δ, f ((shift E (-i)).toFun (Potential.periodicExtend π ω)) := by
  rw [periodicEmpiricalField, integral_uniformAverage_dirac _ _ hf, smul_eq_mul]

/-- The `Δ`-periodic continuation is what makes `θ_j (θ_{-i} ω^∘) = θ_{-π(i - j)} ω^∘`: the
periodic continuation only sees sites modulo the periods. -/
lemma shift_shift_periodicExtend (hπ : Potential.IsTorusReduction G Δ π) (ω : S → E) (i j : S) :
    (shift E j).toFun ((shift E (-i)).toFun (Potential.periodicExtend π ω))
      = (shift E (-π (i - j))).toFun (Potential.periodicExtend π ω) := by
  funext n
  simp only [shift_toFun_apply, Potential.periodicExtend]
  refine congrArg ω (hπ.reduce_eq _ _ ?_)
  have h : n - j - -i - (n - -π (i - j)) = (i - j) - π (i - j) := by abel
  rw [h]
  exact hπ.sub_mem _

/-- **Georgii, after (15.41).** The periodic empirical field is shift invariant: `θ_j` permutes
the translates `θ_{-i} ω^∘`, `i ∈ Δ`, through the bijection `i ↦ π (i − j)` of the torus `Δ`. -/
theorem map_shift_periodicEmpiricalField (hπ : Potential.IsTorusReduction G Δ π) (ω : S → E)
    (j : S) :
    (periodicEmpiricalField E π Δ ω).map (shift E j).toFun = periodicEmpiricalField E π Δ ω := by
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.map_apply (shift E j).measurable_toFun hA,
    periodicEmpiricalField_apply _ _ _ ((shift E j).measurable_toFun hA),
    periodicEmpiricalField_apply _ _ _ hA]
  refine congrArg _ (Finset.sum_nbij' (i := fun a ↦ π (a - j)) (j := fun b ↦ π (b + j))
    (fun a ha ↦ hπ.mapsTo _) (fun b hb ↦ hπ.mapsTo _) (fun a ha ↦ ?_) (fun b hb ↦ ?_)
    fun a ha ↦ ?_)
  · refine hπ.eq_of_mem_of_sub_mem ha ?_
    have h : π (a - j) + j - a = π (a - j) - (a - j) := by abel
    rw [h]
    exact hπ.sub_mem' _
  · refine hπ.eq_of_mem_of_sub_mem hb ?_
    have h : π (b + j) - j - b = π (b + j) - (b + j) := by abel
    rw [h]
    exact hπ.sub_mem' _
  · have h := shift_shift_periodicExtend hπ ω a j
    rw [← h]
    by_cases hm : (shift E j).toFun ((shift E (-a)).toFun (Potential.periodicExtend π ω)) ∈ A
    · have hm' : (shift E (-a)).toFun (Potential.periodicExtend π ω)
          ∈ (shift E j).toFun ⁻¹' A := hm
      rw [Set.indicator_of_mem hm', Set.indicator_of_mem hm, Pi.one_apply, Pi.one_apply]
    · have hm' : (shift E (-a)).toFun (Potential.periodicExtend π ω)
          ∉ (shift E j).toFun ⁻¹' A := hm
      rw [Set.indicator_of_notMem hm', Set.indicator_of_notMem hm]

/-- **Georgii, after (15.41).** `°R^ω_Δ ∈ 𝓟_Θ`. -/
theorem periodicEmpiricalField_mem_invariantFields (hπ : Potential.IsTorusReduction G Δ π)
    [NeZero (#Δ)] (ω : S → E) :
    periodicEmpiricalField E π Δ ω ∈ invariantFields (shiftGroup S E) :=
  mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦
    ⟨(shift E j).measurable_toFun, map_shift_periodicEmpiricalField hπ ω j⟩⟩

/-- **Georgii Remark (15.43)(1)**, pointwise form: a `B`-local observable does not see the
difference between `ω` and its periodic continuation at those `i ∈ Δ` for which `B + i ⊆ Δ`. -/
theorem apply_shift_periodicExtend_eq (hπ : Potential.IsTorusReduction G Δ π) {B : Set S}
    {β : Type*} {f : (S → E) → β} (hf : DependsOn f B) {i : S} (hi : ∀ n ∈ B, n + i ∈ Δ)
    (ω : S → E) :
    f ((shift E (-i)).toFun (Potential.periodicExtend π ω))
      = f ((shift E (-i)).toFun ω) := by
  refine hf fun n hn ↦ ?_
  simp only [shift_toFun_apply, sub_neg_eq_add, Potential.periodicExtend]
  exact congrArg ω (hπ.eq_self _ (hi n hn))

/-- **Georgii Remark (15.43)(1)**, finite-volume form: for a `B`-local observable bounded by `c`,
the periodic empirical average `°R_Δ f` and the plain spatial average `R_Δ f` differ by at most
`2 c |T| / |Δ|`, where `T` is any set of sites containing all `i ∈ Δ` with `B + i ⊄ Δ`. Georgii's
`T` is `{i ∈ Δ : B + i ⊄ Δ}`, whose relative size tends to `0` along cubes. -/
theorem abs_sum_apply_shift_periodicExtend_sub_le (hπ : Potential.IsTorusReduction G Δ π)
    {B : Set S} {f : (S → E) → ℝ} (hf : DependsOn f B) {c : ℝ} (hc : ∀ η, |f η| ≤ c)
    {T : Finset S} (hT : T ⊆ Δ) (hgood : ∀ i ∈ Δ, i ∉ T → ∀ n ∈ B, n + i ∈ Δ) (ω : S → E) :
    |(∑ i ∈ Δ, f ((shift E (-i)).toFun (Potential.periodicExtend π ω)))
        - ∑ i ∈ Δ, f ((shift E (-i)).toFun ω)| ≤ 2 * c * #T := by
  have hsum : (∑ i ∈ Δ, f ((shift E (-i)).toFun (Potential.periodicExtend π ω)))
      - ∑ i ∈ Δ, f ((shift E (-i)).toFun ω)
      = ∑ i ∈ T, (f ((shift E (-i)).toFun (Potential.periodicExtend π ω))
        - f ((shift E (-i)).toFun ω)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_subset hT fun i hi hiT ↦ ?_).symm
    rw [apply_shift_periodicExtend_eq hπ hf (hgood i hi hiT) ω, sub_self]
  rw [hsum]
  calc |∑ i ∈ T, (f ((shift E (-i)).toFun (Potential.periodicExtend π ω))
          - f ((shift E (-i)).toFun ω))|
      ≤ ∑ i ∈ T, |f ((shift E (-i)).toFun (Potential.periodicExtend π ω))
          - f ((shift E (-i)).toFun ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ T, 2 * c := by
        refine Finset.sum_le_sum fun i _ ↦ (abs_sub _ _).trans ?_
        have h1 := hc ((shift E (-i)).toFun (Potential.periodicExtend π ω))
        have h2 := hc ((shift E (-i)).toFun ω)
        linarith
    _ = 2 * c * #T := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Georgii Remark (15.43)(1), the estimate `‖°R_Δ f − R_Δ f‖ ≤ 2‖f‖ |T| / |Δ|`.** For a
`B`-local observable `f` bounded by `c`, the periodic empirical average `°R^ω_Δ f` and the plain
spatial average `R^ω_Δ f = |Δ|⁻¹ ∑_{i ∈ Δ} f(θ_{-i} ω)` differ by at most `2 c |T| / |Δ|`, where
`T` is any set of sites containing all `i ∈ Δ` with `B + i ⊄ Δ`. The bound does not depend on
`ω`, so it bounds Georgii's supremum norm. -/
theorem abs_integral_periodicEmpiricalField_sub_le (hπ : Potential.IsTorusReduction G Δ π)
    {B : Set S} {f : (S → E) → ℝ} (hf : DependsOn f B) (hfm : StronglyMeasurable f)
    {c : ℝ} (hc : ∀ η, |f η| ≤ c) {T : Finset S} (hT : T ⊆ Δ)
    (hgood : ∀ i ∈ Δ, i ∉ T → ∀ n ∈ B, n + i ∈ Δ) (ω : S → E) :
    |(∫ η, f η ∂(periodicEmpiricalField E π Δ ω))
        - (#Δ : ℝ)⁻¹ * ∑ i ∈ Δ, f ((shift E (-i)).toFun ω)|
      ≤ 2 * c * #T / #Δ := by
  rcases Δ.eq_empty_or_nonempty with rfl | hΔ
  · rw [integral_periodicEmpiricalField _ _ _ hfm]
    simp [Finset.subset_empty.1 hT]
  have hcard : (0 : ℝ) < #Δ := by exact_mod_cast hΔ.card_pos
  rw [integral_periodicEmpiricalField _ _ _ hfm, ← mul_sub, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hcard.le), div_eq_inv_mul _ (#Δ : ℝ)]
  exact mul_le_mul_of_nonneg_left
    (abs_sum_apply_shift_periodicExtend_sub_le hπ hf hc hT hgood ω) (inv_nonneg.2 hcard.le)

/-- **Georgii Remark (15.43)(1) as stated:** `‖°R_Δ f − R_Δ f‖ → 0` when `|Δ| → ∞`. Along a
sequence of volumes `Δ n` whose boundary layers `T n ⊇ {i ∈ Δ n : B + i ⊄ Δ n}` are of vanishing
relative size, the periodic empirical average of a bounded `B`-local observable is asymptotically
the plain spatial average, uniformly in the configuration. -/
theorem tendsto_integral_periodicEmpiricalField_sub_zero {κ : Type*} {l : Filter κ}
    {G' : κ → AddSubgroup S} {Δ' : κ → Finset S} {π' : κ → S → S}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Δ' n) (π' n))
    {B : Set S} {f : (S → E) → ℝ} (hf : DependsOn f B) (hfm : StronglyMeasurable f)
    {c : ℝ} (hc : ∀ η, |f η| ≤ c) {T : κ → Finset S} (hT : ∀ n, T n ⊆ Δ' n)
    (hgood : ∀ n, ∀ i ∈ Δ' n, i ∉ T n → ∀ b ∈ B, b + i ∈ Δ' n)
    (hsmall : Tendsto (fun n ↦ (#(T n) : ℝ) / #(Δ' n)) l (𝓝 0)) (ω : S → E) :
    Tendsto (fun n ↦ (∫ η, f η ∂(periodicEmpiricalField E (π' n) (Δ' n) ω))
      - (#(Δ' n) : ℝ)⁻¹ * ∑ i ∈ Δ' n, f ((shift E (-i)).toFun ω)) l (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ 2 * c * ((#(T n) : ℝ) / #(Δ' n))) l (𝓝 0) := by
    simpa using hsmall.const_mul (2 * c)
  refine squeeze_zero_norm' (Eventually.of_forall fun n ↦ ?_) hlim
  rw [Real.norm_eq_abs, ← mul_div_assoc]
  exact abs_integral_periodicEmpiricalField_sub_le (hπ n) hf hfm hc (hT n) (hgood n) ω

/-- **Georgii Remark (15.43)(3).** The specific energy of the periodic empirical field is the
spatial average of the site energies of the periodic continuation,
`⟨°R^ω_Δ, Φ⟩ = |Δ|⁻¹ ∑_{i ∈ Δ} f_Φ(θ_{-i} ω^∘_Δ)`. This is the identity Georgii uses to write
`|Δ|⁻¹ γ^C_{Δ|ω}(H^Φ_Δ) = ⟨γ^C_{Δ|ω} °R_Δ, Φ⟩ + o(1)` in Step 1 of the proof of (15.46). -/
theorem specificEnergy_periodicEmpiricalField [Countable S] {Φ : Potential S E}
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant)
    (π : S → S) (Δ : Finset S) (ω : S → E) :
    Φ.specificEnergy (periodicEmpiricalField E π Δ ω)
      = (#Δ : ℝ)⁻¹ * ∑ i ∈ Δ, Φ.siteEnergy i (Potential.periodicExtend π ω) := by
  rw [Potential.specificEnergy,
    integral_periodicEmpiricalField _ _ _ (Φ.measurable_siteEnergy 0).stronglyMeasurable]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ (hΦ.siteEnergy_eq i _).symm)

end PeriodicEmpiricalField

/-! ### Georgii Remark (15.43)(2) and (15.44): the empirical field of an ergodic random field -/

section ErgodicLimit

open scoped Pointwise

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

open scoped Classical in
/-- **The Følner property of cubes in the form Georgii Remark (15.43)(1) needs.** For a fixed
site `b`, the fraction of the cube `Λ_n = [m_n, m_n + s_n]^d` that the translation `i ↦ b + i`
pushes out of the cube vanishes as the side length grows. -/
theorem tendsto_card_filter_add_notMem_div_card {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (b : ι → ℤ) :
    Tendsto (fun n ↦ (#{i ∈ Finset.Icc (m n) fun k ↦ m n k + s n |
          b + i ∉ Finset.Icc (m n) fun k ↦ m n k + s n} : ℝ)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n)) atTop (𝓝 0) := by
  have hr : Tendsto (fun n ↦ s n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ (s n)) hs
  have hfol := tendsto_card_vadd_cube_symmDiff_div_card (ι := ι) m (r := fun n ↦ s n + 1) hr (-b)
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hfol
  set F : Finset (ι → ℤ) :=
    m n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ) with hF
  have hΛ : (Finset.Icc (m n) fun k ↦ m n k + s n) = F := Finset.Icc_cube_eq_vadd_piFinset_Ico _ _
  have hsub : {i ∈ F | b + i ∉ F} ⊆ ((-b) +ᵥ F) ∆ F := by
    intro i hi
    rw [Finset.mem_filter] at hi
    refine Finset.mem_symmDiff.2 (Or.inr ⟨hi.1, fun hmem ↦ hi.2 ?_⟩)
    obtain ⟨y, hy, hyi⟩ := Finset.mem_vadd_finset.1 hmem
    have hby : b + i = y := by
      rw [← hyi]
      funext k
      simp only [vadd_eq_add, Pi.add_apply, Pi.neg_apply]
      ring
    rw [hby]
    exact hy
  rw [hΛ]
  have hpos : (0 : ℝ) < #F := by
    refine Nat.cast_pos.2 (Finset.card_pos.2 ?_)
    rw [hF]
    exact (Finset.Nonempty.vadd_finset ⟨fun _ ↦ 0, Fintype.mem_piFinset.2 fun _ ↦ by
      simp only [Finset.mem_Ico, le_refl, true_and]; exact_mod_cast Nat.succ_pos (s n)⟩)
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hpos.le

variable {μ : Measure ((ι → ℤ) → E)}

open scoped Classical in
/-- **Georgii Remark (15.43)(2) and (15.44).** Let `μ` be a shift-invariant random field that is
*ergodic* — trivial on the σ-algebra `𝓘` of shift-invariant events, Georgii (14.6), which by
(14.5)(a) is what `μ ∈ ex 𝓟_Θ` means. Then for every bounded local observable `f` the periodic
empirical fields `°R^ω_{Λ_n}` of Definition (15.41), along an increasing sequence of cubes
`Λ_n = [m_n, m_n + s_n]^d` with side lengths tending to infinity and arbitrary torus reductions
`π_n`, satisfy `°R^ω_{Λ_n}(f) → μ(f)` for `μ`-almost every `ω`. In particular `°R_{Λ_n} → μ` in
`μ`-probability in the topology of local convergence, which is (15.44).

This is the ergodic theorem (14.A8) for the plain spatial averages `R_{Λ_n} f`, applied along the
reflected cubes `−Λ_n` because `f ∘ θ_{-i} = f((-i) +ᵥ ·)`, together with Remark (15.43)(1)
(`tendsto_integral_periodicEmpiricalField_sub_zero`): the periodization changes the average by at
most `2‖f‖` times the relative size of the boundary layer `{i ∈ Λ_n : B + i ⊄ Λ_n}`, which
vanishes by the Følner property of the cubes. -/
theorem ae_tendsto_integral_periodicEmpiricalField
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hmono : Monotone fun n ↦ Finset.Icc (m n) fun k ↦ m n k + s n)
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    {B : Finset (ι → ℤ)} {f : ((ι → ℤ) → E) → ℝ} (hf : DependsOn f (B : Set (ι → ℤ)))
    (hfm : StronglyMeasurable f) {c : ℝ} (hc : ∀ η, |f η| ≤ c) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ η, f η ∂(periodicEmpiricalField E (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) atTop (𝓝 (∫ η, f η ∂μ)) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hvadd := vaddInvariantMeasure_of_forall_measurePreserving_shift hpres
  have hint : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable c
      (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact hc η)
  set Λ : ℕ → Finset (ι → ℤ) := fun n ↦ Finset.Icc (m n) fun k ↦ m n k + s n with hΛdef
  -- the ergodic theorem along the reflected cubes
  have hr : Tendsto (fun n ↦ s n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ (s n)) hs
  have hcube : ∀ n, (fun k ↦ -(m n k + s n)) +ᵥ
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ)) = -(Λ n) :=
    fun n ↦ (Finset.neg_Icc_cube_eq_vadd_piFinset_Ico (m n) (s n)).symm
  have hmono' : Monotone fun n ↦ (fun k ↦ -(m n k + s n)) +ᵥ
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ)) := by
    intro a b hab
    simp only [hcube]
    exact Finset.neg_subset_neg (hmono hab)
  have herg := ae_tendsto_inv_card_smul_sum_vadd_condExp_cube (μ := μ)
    (fun n k ↦ -(m n k + s n)) (r := fun n ↦ s n + 1) (fun n ↦ Nat.succ_pos _) hr hmono' hint
  have htriv' : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ))
      ((ι → ℤ) → E)] A → μ A = 0 ∨ μ A = 1 := by
    rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
    exact htriv
  -- the boundary layer of the cubes
  set T : ℕ → Finset (ι → ℤ) := fun n ↦ B.biUnion fun b ↦ {i ∈ Λ n | b + i ∉ Λ n} with hT
  have hTsub : ∀ n, T n ⊆ Λ n := fun n ↦
    Finset.biUnion_subset.2 fun b _ ↦ Finset.filter_subset _ _
  have hgood : ∀ n, ∀ i ∈ Λ n, i ∉ T n → ∀ b ∈ (B : Set (ι → ℤ)), b + i ∈ Λ n := by
    intro n i hi hiT b hb
    by_contra hbi
    exact hiT (Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_filter.2 ⟨hi, hbi⟩⟩)
  have hsmall : Tendsto (fun n ↦ (#(T n) : ℝ) / #(Λ n)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦ ∑ b ∈ B, (#{i ∈ Λ n | b + i ∉ Λ n} : ℝ) / #(Λ n)) atTop
        (𝓝 0) := by
      simpa using tendsto_finsetSum B fun b _ ↦ tendsto_card_filter_add_notMem_div_card hs b
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hbound
    rw [← Finset.sum_div]
    have hpos : (0 : ℝ) < #(Λ n) := by
      refine Nat.cast_pos.2 (Finset.card_pos.2 ?_)
      exact Finset.nonempty_Icc.2 fun k ↦ by simp
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_biUnion_le) hpos.le
  -- assemble
  filter_upwards [herg,
    condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      (MeasurableSpace.smulInvariants_le (M := Multiplicative (ι → ℤ))) htriv' f]
    with ω hω hconst
  rw [hconst] at hω
  have hsum : ∀ n, ∑ i ∈ -(Λ n), f ((shift E i).toFun ω)
      = ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) := fun n ↦ by
    rw [← Finset.image_neg_eq_neg, Finset.sum_image neg_injective.injOn]
  simp only [hcube, Finset.card_neg, smul_eq_mul, shift_vadd, hsum] at hω
  have hcorr := tendsto_integral_periodicEmpiricalField_sub_zero
    (Δ' := Λ) hπ hf hfm hc hTsub hgood hsmall ω
  simpa using hcorr.add hω

open scoped Classical in
/-- **Georgii Remark (15.43)(2), in `L¹`.** Let `μ` be an ergodic shift-invariant random field.
Then for every bounded local observable `f` the periodic empirical averages converge to `μ(f)` in
`L¹(μ)`,
`∫ |°R^ω_{Λ_n}(f) − μ(f)| dμ(ω) → 0`,
along **any** sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` whose side lengths tend to infinity,
with arbitrary torus reductions `π_n`. The cubes are *not* required to be increasing.

This is Georgii's own argument for (15.44): Remark (15.43)(1)
(`abs_integral_periodicEmpiricalField_sub_le`, a bound uniform in `ω`) together with the **mean**
ergodic theorem (14.A5) (`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one`)
applied along the reflected cubes `−Λ_n`, whose only hypothesis on the volumes is the Følner
property (`MeasureTheory.tendsto_card_vadd_cube_symmDiff_div_card`). The *individual* ergodic
theorem (14.A8) is not needed here, and with it goes the monotonicity of the cubes that Georgii
imposes in Section 14.A and that `ae_tendsto_integral_periodicEmpiricalField` inherits. -/
theorem tendsto_eLpNorm_integral_periodicEmpiricalField_sub_one
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    {B : Finset (ι → ℤ)} {f : ((ι → ℤ) → E) → ℝ} (hf : DependsOn f (B : Set (ι → ℤ)))
    (hfm : StronglyMeasurable f) {c : ℝ} (hc : ∀ η, |f η| ≤ c) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) - ∫ η, f η ∂μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hvadd := vaddInvariantMeasure_of_forall_measurePreserving_shift hpres
  have hint : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable c
      (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact hc η)
  set Λ : ℕ → Finset (ι → ℤ) := fun n ↦ Finset.Icc (m n) fun k ↦ m n k + s n with hΛdef
  have hΛne : ∀ n, (Λ n).Nonempty := fun n ↦ Finset.nonempty_Icc.2 fun k ↦ by simp
  have hr : Tendsto (fun n ↦ s n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_succ (s n)) hs
  have hcube : ∀ n, (fun k ↦ -(m n k + s n)) +ᵥ
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ)) = -(Λ n) :=
    fun n ↦ (Finset.neg_Icc_cube_eq_vadd_piFinset_Ico (m n) (s n)).symm
  have hFne : ∀ n, ((fun k ↦ -(m n k + s n)) +ᵥ
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ))).Nonempty := fun n ↦
    ⟨fun k ↦ -(m n k + s n), Finset.mem_vadd_finset.2 ⟨0, Fintype.mem_piFinset.2 fun i ↦ by
      simp only [Pi.zero_apply, Finset.mem_Ico, le_refl, true_and]
      exact_mod_cast Nat.succ_pos (s n), by simp⟩⟩
  -- the mean ergodic theorem (14.A5) along the reflected cubes
  have hmean := tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one (μ := μ)
    (F := fun n ↦ (fun k ↦ -(m n k + s n)) +ᵥ
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((s n + 1 : ℕ) : ℤ)))
    (Eventually.of_forall hFne)
    (tendsto_card_vadd_cube_symmDiff_div_card (fun n k ↦ -(m n k + s n))
      (r := fun n ↦ s n + 1) hr) hint
  -- ergodicity: the conditional expectation is the constant `μ(f)`
  have htriv' : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ))
      ((ι → ℤ) → E)] A → μ A = 0 ∨ μ A = 1 := by
    rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
    exact htriv
  have hconst := condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
    (MeasurableSpace.smulInvariants_le (M := Multiplicative (ι → ℤ))) htriv' f
  have hmean' : Tendsto (fun n ↦ eLpNorm (fun ω ↦ (#(Λ n) : ℝ)⁻¹ *
      ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) - ∫ η, f η ∂μ) 1 μ) atTop (𝓝 0) := by
    refine hmean.congr fun n ↦ eLpNorm_congr_ae ?_
    filter_upwards [hconst] with ω hω
    rw [hω]
    have hsum : ∑ i ∈ -(Λ n), f (i +ᵥ ω) = ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) := by
      rw [← Finset.image_neg_eq_neg, Finset.sum_image neg_injective.injOn]
      rfl
    rw [hcube n, Finset.card_neg, smul_eq_mul, hsum]
  -- Remark (15.43)(1): the boundary layer of the cubes
  set T : ℕ → Finset (ι → ℤ) := fun n ↦ B.biUnion fun b ↦ {i ∈ Λ n | b + i ∉ Λ n} with hT
  have hTsub : ∀ n, T n ⊆ Λ n := fun n ↦
    Finset.biUnion_subset.2 fun b _ ↦ Finset.filter_subset _ _
  have hgood : ∀ n, ∀ i ∈ Λ n, i ∉ T n → ∀ b ∈ (B : Set (ι → ℤ)), b + i ∈ Λ n := by
    intro n i hi hiT b hb
    by_contra hbi
    exact hiT (Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_filter.2 ⟨hi, hbi⟩⟩)
  have hsmall : Tendsto (fun n ↦ (#(T n) : ℝ) / #(Λ n)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦ ∑ b ∈ B, (#{i ∈ Λ n | b + i ∉ Λ n} : ℝ) / #(Λ n)) atTop
        (𝓝 0) := by
      simpa using tendsto_finsetSum B fun b _ ↦ tendsto_card_filter_add_notMem_div_card hs b
    refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hbound
    rw [← Finset.sum_div]
    have hpos : (0 : ℝ) < #(Λ n) := by exact_mod_cast (hΛne n).card_pos
    exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_biUnion_le) hpos.le
  -- the two estimates add up
  have hXm : ∀ n, Measurable fun ω ↦ ∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω) := by
    intro n
    have hrw : (fun ω ↦ ∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
        = fun ω ↦ (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n,
            f ((shift E (-i)).toFun (Potential.periodicExtend (π n) ω)) :=
      funext fun ω ↦ integral_periodicEmpiricalField _ _ _ hfm
    rw [hrw]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      hfm.measurable.comp ((shift E (-i)).measurable_toFun.comp
        (Potential.measurable_periodicExtend (π n))))
  have hYm : ∀ n, Measurable fun ω : (ι → ℤ) → E ↦
      (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) := fun n ↦
    measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      hfm.measurable.comp (shift E (-i)).measurable_toFun)
  have hsplit : ∀ n, eLpNorm (fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
        - ∫ η, f η ∂μ) 1 μ
      ≤ ENNReal.ofReal (2 * c * #(T n) / #(Λ n))
        + eLpNorm (fun ω ↦ (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω)
            - ∫ η, f η ∂μ) 1 μ := by
    intro n
    have hbd : eLpNorm (fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
        - (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω)) 1 μ
        ≤ ENNReal.ofReal (2 * c * #(T n) / #(Λ n)) := by
      have h := eLpNorm_le_of_ae_bound (μ := μ) (p := 1)
        (f := fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
          - (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω))
        (C := 2 * c * #(T n) / #(Λ n)) (.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact abs_integral_periodicEmpiricalField_sub_le (hπ n) hf hfm hc (hTsub n) (hgood n) ω)
      simpa using h
    have hstep := eLpNorm_add_le (μ := μ) (p := 1)
      (f := fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
        - (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω))
      (g := fun ω ↦ (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) - ∫ η, f η ∂μ)
      ((hXm n).sub (hYm n)).aestronglyMeasurable
      ((hYm n).sub measurable_const).aestronglyMeasurable le_rfl
    have hd : ((fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
          - (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω))
        + fun ω ↦ (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n, f ((shift E (-i)).toFun ω) - ∫ η, f η ∂μ)
        = fun ω ↦ (∫ η, f η ∂(periodicEmpiricalField E (π n) (Λ n) ω)) - ∫ η, f η ∂μ := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hd] at hstep
    exact hstep.trans (add_le_add hbd le_rfl)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (.of_forall fun _ ↦ bot_le) (.of_forall hsplit)
  have h1 : Tendsto (fun n ↦ ENNReal.ofReal (2 * c * #(T n) / #(Λ n))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n ↦ 2 * c * ((#(T n) : ℝ) / #(Λ n))) atTop (𝓝 0) := by
      simpa using hsmall.const_mul (2 * c)
    simpa [mul_div_assoc] using ENNReal.tendsto_ofReal h2
  simpa using h1.add hmean'

open scoped Classical in
/-- **Georgii (15.44).** For an ergodic shift-invariant random field `μ`, the periodic empirical
fields converge to `μ` in `μ`-probability in the topology of local convergence: for a *basic*
neighbourhood `U = {ν : |ν(f_j) − μ(f_j)| < ε for all j}` of `μ` — Georgii (4.2), with finitely
many bounded local observables `f_j` — one has `μ(°R_{Λ_n} ∈ U) → 1`.

The cubes `Λ_n` are an arbitrary sequence with side lengths tending to infinity: (15.44) is
convergence *in probability*, so Markov's inequality reduces it to the `L¹` convergence
`tendsto_eLpNorm_integral_periodicEmpiricalField_sub_one`, i.e. to the mean ergodic theorem
(14.A5). The increasing cubes of the individual ergodic theorem (14.A8), which
`ae_tendsto_integral_periodicEmpiricalField` needs, are not required here. -/
theorem tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    {κ : Type*} [Fintype κ] {B : κ → Finset (ι → ℤ)} {f : κ → ((ι → ℤ) → E) → ℝ}
    (hf : ∀ j, DependsOn (f j) (B j : Set (ι → ℤ))) (hfm : ∀ j, StronglyMeasurable (f j))
    {c : κ → ℝ} (hc : ∀ j η, |f j η| ≤ c j) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ μ {ω | ∀ j : κ, |(∫ η, f j η ∂(periodicEmpiricalField E (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) - ∫ η, f j η ∂μ| < ε}) atTop (𝓝 1) := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  set Λ : ℕ → Finset (ι → ℤ) := fun n ↦ Finset.Icc (m n) fun k ↦ m n k + s n with hΛdef
  have hmeas : ∀ (n : ℕ) (j : κ), Measurable fun ω ↦
      ∫ η, f j η ∂(periodicEmpiricalField E (π n) (Λ n) ω) := by
    intro n j
    have hrw : (fun ω ↦ ∫ η, f j η ∂(periodicEmpiricalField E (π n) (Λ n) ω))
        = fun ω ↦ (#(Λ n) : ℝ)⁻¹ * ∑ i ∈ Λ n,
            f j ((shift E (-i)).toFun (Potential.periodicExtend (π n) ω)) :=
      funext fun ω ↦ integral_periodicEmpiricalField _ _ _ (hfm j)
    rw [hrw]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
      (hfm j).measurable.comp ((shift E (-i)).measurable_toFun.comp
        (Potential.measurable_periodicExtend (π n))))
  set A : ℕ → Set ((ι → ℤ) → E) := fun n ↦ {ω | ∀ j : κ,
    |(∫ η, f j η ∂(periodicEmpiricalField E (π n) (Λ n) ω)) - ∫ η, f j η ∂μ| < ε} with hAdef
  have hA : ∀ n, MeasurableSet (A n) := by
    intro n
    have hrw : A n = ⋂ j : κ,
        (fun ω ↦ ∫ η, f j η ∂(periodicEmpiricalField E (π n) (Λ n) ω)) ⁻¹'
          Set.Ioo ((∫ η, f j η ∂μ) - ε) ((∫ η, f j η ∂μ) + ε) := by
      ext ω
      simp only [hAdef, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo,
        abs_lt]
      exact forall_congr' fun j ↦ by
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    rw [hrw]
    exact MeasurableSet.iInter fun j ↦ (hmeas n j) measurableSet_Ioo
  -- each of the finitely many observables converges in `μ`-probability, by Markov's inequality
  have hbad : ∀ j : κ, Tendsto (fun n ↦ μ {ω | ε ≤ |(∫ η, f j η ∂(periodicEmpiricalField E (π n)
      (Λ n) ω)) - ∫ η, f j η ∂μ|}) atTop (𝓝 0) := by
    intro j
    have hL1 := tendsto_eLpNorm_integral_periodicEmpiricalField_sub_one hμ htriv hs hπ
      (hf j) (hfm j) (hc j)
    have hdiv : Tendsto (fun n ↦ eLpNorm (fun ω ↦ (∫ η, f j η ∂(periodicEmpiricalField E (π n)
        (Λ n) ω)) - ∫ η, f j η ∂μ) 1 μ / ENNReal.ofReal ε) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.div_const hL1 (Or.inr (ENNReal.ofReal_pos.2 hε).ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
      (.of_forall fun _ ↦ bot_le) (.of_forall fun n ↦ ?_)
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine le_trans (measure_mono ?_) (meas_ge_le_lintegral_div
      (((hmeas n j).sub measurable_const).enorm.aemeasurable)
      (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top)
    intro ω hω
    rw [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal hω
  have hcompl : ∀ n, μ (A n)ᶜ ≤ ∑ j : κ, μ {ω | ε ≤ |(∫ η, f j η ∂(periodicEmpiricalField E (π n)
      (Λ n) ω)) - ∫ η, f j η ∂μ|} := by
    intro n
    refine le_trans (measure_mono ?_) (measure_iUnion_fintype_le μ _)
    intro ω hω
    simp only [hAdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨j, hj⟩ := hω
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hlim0 : Tendsto (fun n ↦ μ (A n)ᶜ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (.of_forall fun _ ↦ bot_le) (.of_forall hcompl)
    simpa using tendsto_finsetSum Finset.univ fun j _ ↦ hbad j
  have hfinal : Tendsto (fun n ↦ 1 - μ (A n)ᶜ) atTop (𝓝 1) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds hlim0 (Or.inl ENNReal.one_ne_top)
  refine hfinal.congr fun n ↦ ?_
  rw [← prob_compl_eq_one_sub (hA n).compl, compl_compl, hAdef]

end ErgodicLimit

end MeasureTheory.GibbsMeasure

namespace Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {K : Type*} [Fintype K]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-! ### Georgii (15.48): the vector-valued specific energy `e_Ψ` -/

/-- **Georgii, before (15.48).** The continuous map `e_Ψ : ν ↦ ⟨ν, Ψ⟩` from `𝓟_Θ` to `ℝ^k`
attached to a vector-valued potential `Ψ = (Ψ¹, …, Ψᵏ) ∈ ℬ_Θ^k`. -/
def energyVec (Ψ : K → BTheta (ι → ℤ) E) (μ : Measure ((ι → ℤ) → E)) : K → ℝ :=
  fun j ↦ (Ψ j : Potential (ι → ℤ) E).specificEnergy μ

/-- **Georgii, before (15.48).** The inner product `t · Ψ = ∑ⱼ tⱼ Ψʲ ∈ ℬ_Θ`. -/
def dotPotential (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E) : BTheta (ι → ℤ) E := ∑ j, t j • Ψ j

variable {ν}

omit [Fintype ι] [DecidableEq ι] [Fintype K] in
lemma energyVec_apply (Ψ : K → BTheta (ι → ℤ) E) (μ : Measure ((ι → ℤ) → E)) (j : K) :
    energyVec Ψ μ j = (Ψ j : Potential (ι → ℤ) E).specificEnergy μ := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype K] in
/-- **Georgii, before (15.48): `e_Ψ` is continuous.** The vector-valued specific energy
`μ ↦ ⟨μ, Ψ⟩` is continuous for the topology of local convergence, each coordinate being
`Potential.continuous_specificEnergy` (Georgii (4.3)(2)). This is the continuity of `e_Ψ` that
the contraction principle of Corollary (15.48) consumes. -/
theorem continuous_energyVec (Ψ : K → BTheta (ι → ℤ) E) :
    Continuous fun μ : WithLocalConvergence (ι → ℤ) E ↦
      energyVec Ψ (μ.toMeasure : Measure ((ι → ℤ) → E)) :=
  continuous_pi fun j ↦ Potential.continuous_specificEnergy (Φ := (Ψ j : Potential (ι → ℤ) E))

omit [DecidableEq ι] [Fintype K] in
/-- The specific energy of a finite linear combination of potentials. -/
lemma specificEnergy_sum (s : Finset K) (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E)
    (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    ((∑ j ∈ s, t j • Ψ j : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = ∑ j ∈ s, t j * (Ψ j : Potential (ι → ℤ) E).specificEnergy μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, Submodule.coe_zero]
      simp [Potential.specificEnergy, Potential.energyDensity, Potential.siteEnergy,
        Potential.siteEnergyTerms]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Submodule.coe_add, specificEnergy_add,
        Submodule.coe_smul, specificEnergy_smul, ih]

omit [DecidableEq ι] in
/-- `⟨μ, t·Ψ⟩ = ∑ⱼ tⱼ ⟨μ, Ψʲ⟩`. -/
lemma specificEnergy_dotPotential (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E)
    (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    ((dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = ∑ j, t j * energyVec Ψ μ j :=
  specificEnergy_sum Finset.univ t Ψ μ

/-! ### The identity behind (15.49) -/

variable (ν) in
/-- **Georgii, first display of the proof of (15.49).** For a shift-invariant random field `μ`
with `⟨μ, Ψ⟩ = x`, `𝓀(μ|Φ) = 𝓀(μ|Φ − t·Ψ) + t·x − P(Φ − t·Ψ) + P(Φ)`. Written additively so that
it holds also when `𝓀(μ) = −∞`, i.e. when both specific relative entropies are `+∞`. -/
theorem specificRelativeEntropy_sub_dotPotential_add (Φ : BTheta (ι → ℤ) E)
    (Ψ : K → BTheta (ι → ℤ) E) (t : K → ℝ) {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ] :
    ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + (((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * energyVec Ψ μ j
          - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
              Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      = (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ := by
  set Φ' : BTheta (ι → ℤ) E := Φ - dotPotential t Ψ with hΦ'
  have hcoe : ((Φ' : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)
      = (Φ : Potential (ι → ℤ) E) - ((dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E) := by rw [hΦ', Submodule.coe_sub]
  have henergy : ((Φ' : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = (Φ : Potential (ι → ℤ) E).specificEnergy μ - ∑ j, t j * energyVec Ψ μ j := by
    rw [hcoe, specificEnergy_sub, specificEnergy_dotPotential]
  have key : ∀ (a b : ℝ) (h : EReal),
      (a : EReal) - h + (b : EReal) = ((a + b : ℝ) : EReal) - h := by
    intro a b h
    rw [sub_eq_add_neg, sub_eq_add_neg, EReal.coe_add, add_right_comm]
  rw [specificRelativeEntropy, specificRelativeEntropy, key, henergy]
  congr 2
  ring

/-! ### Georgii (15.49): the rate function `J_Ψ(·|Φ)` -/

variable (ν) in
/-- **Georgii (15.49).** The rate function of the vector-valued potential `Ψ` for the potential
`Φ`: `J_Ψ(x|Φ) = inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ, ⟨ν, Ψ⟩ = x}`, the contraction of the excess free energy
functional `𝓀(·|Φ)` along `e_Ψ`. -/
def ldRate (Φ : BTheta (ι → ℤ) E) (Ψ : K → BTheta (ι → ℤ) E) (x : K → ℝ) : EReal :=
  ⨅ μ ∈ {μ : Measure ((ι → ℤ) → E) | μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      energyVec Ψ μ = x}, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ

variable {Φ : BTheta (ι → ℤ) E} {Ψ : K → BTheta (ι → ℤ) E} {x : K → ℝ}

omit [Fintype K] in
lemma ldRate_le {μ : Measure ((ι → ℤ) → E)} (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hx : energyVec Ψ μ = x) :
    ldRate ν Φ Ψ x ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ :=
  iInf₂_le μ ⟨hμ, hx⟩

omit [Fintype K] in
/-- **Georgii Corollary (15.35)** contracted: the rate function is nonnegative. -/
theorem ldRate_nonneg : 0 ≤ ldRate ν Φ Ψ x := by
  refine le_iInf₂ fun μ hμ ↦ ?_
  have : IsProbabilityMeasure μ := hμ.1.1
  exact specificRelativeEntropy_nonneg ν (isShiftInvariant Φ) hμ.1

/-- **Georgii (15.49), the elementary inequality.** For every `t ∈ ℝ^k`,
`t·x − P(Φ − t·Ψ) + P(Φ) ≤ J_Ψ(x|Φ)`: the Legendre–Fenchel transform of `t ↦ P(Φ − t·Ψ)` is a
lower bound for the rate function. -/
theorem coe_le_ldRate (t : K → ℝ) :
    (((∑ j, t j * x j) - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      ≤ ldRate ν Φ Ψ x := by
  refine le_iInf₂ fun μ hμ ↦ ?_
  have : IsProbabilityMeasure μ := hμ.1.1
  have hid := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := μ)
  rw [hμ.2] at hid
  rw [← hid]
  have hnn : 0 ≤ ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
      Potential (ι → ℤ) E).specificRelativeEntropy ν μ :=
    specificRelativeEntropy_nonneg ν (isShiftInvariant (Φ - dotPotential t Ψ)) hμ.1
  calc (((∑ j, t j * x j) - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
          Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      = 0 + (((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * x j
          - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
            Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := by
        rw [zero_add]; congr 1; ring
    _ ≤ _ := by gcongr

omit [Fintype K] in
/-- **Georgii Corollary (15.35)** contracted: if a shift-invariant Gibbs measure has
`⟨μ, Ψ⟩ = x`, then `J_Ψ(x|Φ) = 0`. -/
theorem ldRate_eq_zero_of_mem_invariantG {μ : Measure ((ι → ℤ) → E)}
    (hμ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E))
    (hx : energyVec Ψ μ = x) :
    ldRate ν Φ Ψ x = 0 :=
  le_antisymm
    ((ldRate_le hμ.2 hx).trans_eq
      (specificRelativeEntropy_eq_zero_of_mem_invariantG ν (isShiftInvariant Φ) hμ))
    ldRate_nonneg

omit [Fintype K] in
variable (ν Φ Ψ) in
/-- **Georgii Corollary (15.48)**, the half of `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))` that makes the
rate function nonvacuous: over a standard Borel state space `J_Ψ(·|Φ)` is not identically `+∞`,
because `𝒢_Θ(Φ) ≠ ∅` (Theorem (4.23)(a) and Corollary (5.16),
`Potential.invariantG_gibbsSpecification_shiftGroup_nonempty`) and `J_Ψ` vanishes at the specific
`Ψ`-energy of any shift-invariant Gibbs measure of `Φ`. -/
theorem exists_ldRate_eq_zero [StandardBorelSpace E] : ∃ x : K → ℝ, ldRate ν Φ Ψ x = 0 := by
  obtain ⟨μ, hμ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant Φ)
  exact ⟨_, ldRate_eq_zero_of_mem_invariantG hμ rfl⟩

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii's contraction step in the proof of Corollary (15.48).** For any `B ⊆ ℝ^k`,
`inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ, ⟨ν, Ψ⟩ ∈ B} = inf {J_Ψ(x|Φ) : x ∈ B}`: the rate function of the image of
`𝓀(·|Φ)` under `e_Ψ` is `J_Ψ(·|Φ)`. Both inequalities are immediate from `iInf₂_le` and
`le_iInf₂`: an infimum over `{μ ∈ 𝓟_Θ : e_Ψ μ ∈ B}` regroups by the fibres of `e_Ψ`. -/
theorem iInf_specificRelativeEntropy_eq_iInf_ldRate (B : Set (K → ℝ)) :
    (⨅ μ ∈ {μ : Measure ((ι → ℤ) → E) | μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
        energyVec Ψ μ ∈ B}, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ)
      = ⨅ y ∈ B, ldRate ν Φ Ψ y := by
  refine le_antisymm (le_iInf₂ fun y hy ↦ le_iInf₂ fun μ hμ ↦ ?_)
    (le_iInf₂ fun μ hμ ↦ le_trans (iInf₂_le _ hμ.2) (ldRate_le hμ.1 rfl))
  exact iInf₂_le μ ⟨hμ.1, hμ.2 ▸ hy⟩

/-! ### Georgii's remark after (15.45): the level sets of `𝓀(·|Φ)` are compact -/

omit [Fintype K] in
/-- `𝓀(μ|Φ) ≤ c` is `P(Φ) + ⟨μ, Φ⟩ − c ≤ 𝓀(μ)`, written without `EReal` subtraction. -/
lemma specificRelativeEntropy_le_coe_iff {μ : Measure ((ι → ℤ) → E)} {c : ℝ} :
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ ≤ (c : EReal) ↔
      (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ - c
        : ℝ) : EReal) ≤ specificEntropy ν μ := by
  rw [specificRelativeEntropy]
  set a : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ
  have hne : specificEntropy ν μ ≠ ⊤ := specificEntropy_ne_top ν
  induction h : specificEntropy ν μ using EReal.rec with
  | bot =>
      simp only [EReal.sub_bot (EReal.coe_ne_bot _), le_bot_iff, top_le_iff]
      exact iff_of_false (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  | coe r =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro <;> linarith
  | top => exact absurd h hne

omit [Fintype K] in
/-- The excess free energy is never `−∞`: it is at least `P(Φ) + ⟨μ, Φ⟩`, because `𝓀(μ) ≤ 0`. -/
lemma coe_le_specificRelativeEntropy (μ : Measure ((ι → ℤ) → E)) :
    (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ : ℝ)
        : EReal) ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ := by
  rw [specificRelativeEntropy, sub_eq_add_neg]
  nth_rewrite 1 [← add_zero (((Φ : Potential (ι → ℤ) E).pressure ν
    + (Φ : Potential (ι → ℤ) E).specificEnergy μ : ℝ) : EReal)]
  gcongr
  simpa using EReal.neg_le_neg_iff.2 (specificEntropy_nonpos ν (μ := μ))

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** The sublevel sets `{𝓀(·|Φ) ≤ c}` of the excess
free energy functional are closed in the topology of local convergence: `𝓀` is upper
semicontinuous (15.14) and `⟨·, Φ⟩` is continuous. -/
theorem isClosed_setOf_specificRelativeEntropy_le (c : ℝ) :
    IsClosed {μ : WithLocalConvergence (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)} := by
  have hset : {μ : WithLocalConvergence (ι → ℤ) E |
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)}
      = {μ : WithLocalConvergence (ι → ℤ) E |
        (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy
            (μ.toMeasure : Measure ((ι → ℤ) → E)) - c : ℝ) : EReal)
          ≤ specificEntropy ν (μ.toMeasure : Measure ((ι → ℤ) → E))} := by
    ext μ; exact specificRelativeEntropy_le_coe_iff
  rw [hset]
  exact UpperSemicontinuous.isClosed_setOf_coe_le
    (((continuous_specificEnergy (Φ := (Φ : Potential (ι → ℤ) E))).const_add _).sub
      continuous_const)
    (upperSemicontinuous_specificEntropy ν)

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** Over a standard Borel state space the sublevel
sets `{𝓀(·|Φ) ≤ c}` are compact: they are closed, and contained in the compact level set
`{𝓀 ≥ P(Φ) − ‖Φ‖₀ − c}` of the specific entropy (Proposition (15.14)). -/
theorem isCompact_setOf_specificRelativeEntropy_le [StandardBorelSpace E] (c : ℝ) :
    IsCompact {μ : WithLocalConvergence (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)} := by
  refine IsCompact.of_isClosed_subset
    (isCompact_setOf_le_specificEntropy ν ((Φ : Potential (ι → ℤ) E).pressure ν
      - (((Φ : Potential (ι → ℤ) E)).normAt 0).toReal - c))
    (isClosed_setOf_specificRelativeEntropy_le ν Φ c) fun μ hμ ↦ ?_
  have h1 : (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy
      (μ.toMeasure : Measure ((ι → ℤ) → E)) - c : ℝ) : EReal)
      ≤ specificEntropy ν (μ.toMeasure : Measure ((ι → ℤ) → E)) :=
    specificRelativeEntropy_le_coe_iff.1 hμ
  have h2 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (ι → ℤ) E))
    (μ.toMeasure : Measure ((ι → ℤ) → E)))
  exact le_trans (EReal.coe_le_coe_iff.2 (by linarith [h2.1])) h1

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** The excess free energy functional `𝓀(·|Φ)` is
lower semicontinuous for the topology of local convergence. -/
theorem lowerSemicontinuous_specificRelativeEntropy :
    LowerSemicontinuous fun μ : WithLocalConvergence (ι → ℤ) E ↦
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot =>
      convert isClosed_empty
      ext μ
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, le_bot_iff]
      intro hcon
      exact absurd (hcon ▸ coe_le_specificRelativeEntropy
        (Φ := Φ) (μ.toMeasure : Measure ((ι → ℤ) → E))) (by simp)
  | coe c => exact isClosed_setOf_specificRelativeEntropy_le ν Φ c
  | top => simp

/-! ### Georgii, remark after (15.45): the infimum of `𝓀(·|Φ)` is attained -/

variable (Ψ x) in
/-- The index set of the rate function `J_Ψ(x|Φ)`, as a subset of the space of random fields with
the topology of local convergence. -/
def constraintSet : Set (WithLocalConvergence (ι → ℤ) E) :=
  {μ | (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
    energyVec Ψ (μ.toMeasure : Measure ((ι → ℤ) → E)) = x}

omit [Fintype ι] [DecidableEq ι] [Fintype K] in
variable (Ψ x) in
/-- `e_Ψ` is continuous and `𝓟_Θ` is closed, so the constraint set of (15.49) is closed. -/
theorem isClosed_constraintSet : IsClosed (constraintSet Ψ x) := by
  have hset : constraintSet (ι := ι) (E := E) Ψ x
      = {μ : WithLocalConvergence (ι → ℤ) E | ∀ τ ∈ shiftGroup (ι → ℤ) E,
          MeasurePreserving τ.toFun (μ.toMeasure : Measure ((ι → ℤ) → E)) μ.toMeasure}
        ∩ ⋂ j : K, {μ : WithLocalConvergence (ι → ℤ) E |
          (Ψ j : Potential (ι → ℤ) E).specificEnergy
            (μ.toMeasure : Measure ((ι → ℤ) → E)) = x j} := by
    ext μ
    simp only [constraintSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      mem_invariantFields_iff, funext_iff, energyVec]
    exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨inferInstance, h.1⟩, h.2⟩⟩
  rw [hset]
  refine (isClosed_setOf_forall_measurePreserving _).inter (isClosed_iInter fun j ↦ ?_)
  exact isClosed_eq (continuous_specificEnergy (Φ := (Ψ j : Potential (ι → ℤ) E)))
    continuous_const

omit [Fintype K] in
variable (Φ Ψ x) in
/-- The rate function (15.49) as an infimum over the constraint set inside the space of random
fields with the topology of local convergence. -/
theorem ldRate_eq_iInf_constraintSet :
    ldRate ν Φ Ψ x = ⨅ μ ∈ constraintSet (ι := ι) (E := E) Ψ x,
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ldRate_le hμ.1 hμ.2) (le_iInf₂ fun μ hμ ↦ ?_)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  set μ' : WithLocalConvergence (ι → ℤ) E := WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩ with hμ'def
  have hcoe : (μ'.toMeasure : Measure ((ι → ℤ) → E)) = μ := rfl
  have hmemC : μ' ∈ constraintSet (ι := ι) (E := E) Ψ x := by
    refine ⟨?_, ?_⟩ <;> rw [hcoe]
    exacts [hμ.1, hμ.2]
  exact (iInf₂_le μ' hmemC).trans_eq (by rw [hcoe])

variable [StandardBorelSpace E]

omit [Fintype K] in
variable (Φ Ψ x) in
/-- **Georgii, remark after Theorem (15.45).** The infimum defining the rate function
`J_Ψ(x|Φ)` is attained as soon as it is finite, because the sublevel sets of `𝓀(·|Φ)` are compact
and `𝓀(·|Φ)` is lower semicontinuous. -/
theorem exists_specificRelativeEntropy_eq_ldRate (hfin : ldRate ν Φ Ψ x ≠ ⊤) :
    ∃ μ : Measure ((ι → ℤ) → E), μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      energyVec Ψ μ = x ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = ldRate ν Φ Ψ x := by
  set F : WithLocalConvergence (ι → ℤ) E → EReal := fun μ ↦
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (μ.toMeasure : Measure ((ι → ℤ) → E)) with hF
  set C : Set (WithLocalConvergence (ι → ℤ) E) := constraintSet (ι := ι) (E := E) Ψ x with hC
  have hJ : ldRate ν Φ Ψ x = ⨅ μ ∈ C, F μ := ldRate_eq_iInf_constraintSet Φ Ψ x
  -- a real level strictly above the infimum
  obtain ⟨q, hq1, -⟩ := EReal.lt_iff_exists_rat_btwn.1 (lt_top_iff_ne_top.2 hfin)
  set c : ℝ := (q : ℝ) with hc
  rw [hJ] at hq1
  obtain ⟨μ₀, hμ₀⟩ := iInf_lt_iff.1 hq1
  obtain ⟨hμ₀C, hμ₀c⟩ := iInf_lt_iff.1 hμ₀
  -- the compact piece of the constraint set below that level
  set K : Set (WithLocalConvergence (ι → ℤ) E) := {μ | F μ ≤ (c : EReal)} ∩ C with hK
  have hKcompact : IsCompact K :=
    (isCompact_setOf_specificRelativeEntropy_le ν Φ c).inter_right (isClosed_constraintSet Ψ x)
  have hKne : K.Nonempty := ⟨μ₀, hμ₀c.le, hμ₀C⟩
  obtain ⟨μ₁, hμ₁K, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hKne hKcompact
    ((lowerSemicontinuous_specificRelativeEntropy ν Φ).lowerSemicontinuousOn K)
  refine ⟨(μ₁.toMeasure : Measure ((ι → ℤ) → E)), hμ₁K.2.1, hμ₁K.2.2, ?_⟩
  rw [hJ]
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ?_) (iInf₂_le μ₁ hμ₁K.2)
  by_cases hle : F μ ≤ (c : EReal)
  · exact hmin ⟨hle, hμ⟩
  · exact le_trans hμ₁K.1 (le_of_lt (not_le.1 hle))

omit [Fintype K] in
variable (Φ Ψ x) in
/-- **Georgii Corollary (15.48), last assertion**: `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`. The rate
function vanishes at `x` exactly when some shift-invariant Gibbs measure has specific
`Ψ`-energy `x`; this is the variational principle (15.39) together with the attainment of the
infimum. -/
theorem ldRate_eq_zero_iff :
    ldRate ν Φ Ψ x = 0 ↔ ∃ μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E), energyVec Ψ μ = x := by
  refine ⟨fun h ↦ ?_, fun ⟨μ, hμ, hx⟩ ↦ ldRate_eq_zero_of_mem_invariantG hμ hx⟩
  obtain ⟨μ, hμinv, hμx, hμ0⟩ := exists_specificRelativeEntropy_eq_ldRate Φ Ψ x
    (by rw [h]; exact EReal.zero_ne_top)
  have : IsProbabilityMeasure μ := hμinv.1
  rw [h] at hμ0
  exact ⟨μ, mem_invariantG_of_specificRelativeEntropy_eq_zero' ν (isShiftInvariant Φ) hμinv hμ0,
    hμx⟩

omit [Fintype K] in
variable (Φ Ψ x) in
/-- **Georgii Example (15.50), first assertion**, for an arbitrary single potential `Ψ ∈ ℬ_Θ`
(Georgii's `k = 1`). Over a standard Borel state space, the rate function `J_Ψ(·|Φ)` attains its
minimum `0` exactly on the closed interval `[a⁻, a⁺]` whose endpoints are the left- and
right-sided derivatives at `t = 0` of the convex function `t ↦ P(Φ − tΨ)`, i.e. the one-sided
directional derivatives of the pressure at `Φ` in the direction `−Ψ`.

This is `Potential.BTheta.ldRate_eq_zero_iff` (`{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`, the last assertion
of Corollary (15.48)) together with Theorem (16.14)
(`Potential.BTheta.mem_subgradientAt_pressure_of_mem_invariantG` and
`Potential.BTheta.exists_mem_fieldsOf_mem_invariantG`: `j(𝒢_Θ(Φ)) = ∂P(Φ)`) and Remark (16.6)
(`Potential.BTheta.leftDirDeriv_le_and_le_rightDirDeriv_pressure` and
`Potential.BTheta.exists_mem_subgradientAt_pressure_apply_eq`: the values `L(−Ψ)`, `L ∈ ∂P(Φ)`,
fill out `[∂⁻_{−Ψ}P(Φ), ∂⁺_{−Ψ}P(Φ)]`), since `⟨μ, Ψ⟩ = j(μ)(−Ψ)`. -/
theorem ldRate_eq_zero_iff_mem_Icc [Unique K] :
    ldRate ν Φ Ψ x = 0 ↔
      x default ∈ Set.Icc (leftDirDeriv (pressure ν) Φ (-Ψ default))
        (rightDirDeriv (pressure ν) Φ (-Ψ default)) := by
  rw [ldRate_eq_zero_iff]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    have hprob : IsProbabilityMeasure μ := hμ.1.1
    have hval : specificEnergyFunctional μ (-Ψ default) = energyVec Ψ μ default := by
      rw [map_neg, specificEnergyFunctional_apply, neg_neg, energyVec_apply]
    have h := leftDirDeriv_le_and_le_rightDirDeriv_pressure ν
      (mem_subgradientAt_pressure_of_mem_invariantG ν hμ) (-Ψ default)
    rw [hval] at h
    exact Set.mem_Icc.2 h
  · intro hx
    obtain ⟨L, hL, hLx⟩ := exists_mem_subgradientAt_pressure_apply_eq ν Φ (-Ψ default) hx
    obtain ⟨μ, hμf, hμG⟩ := exists_mem_fieldsOf_mem_invariantG ν hL
    have hprob : IsProbabilityMeasure μ := hμG.1.1
    refine ⟨μ, hμG, funext fun j ↦ ?_⟩
    obtain rfl : j = default := Subsingleton.elim _ _
    rw [energyVec_apply, hμf.2 (Ψ default), ← map_neg, hLx]

/-! ### Georgii (15.60): the minimum free energy principle and the equivalence of ensembles -/

/-- **Georgii (15.60).** Let `μ ∈ 𝓟_Θ` minimise the excess free energy `𝓀(·|Φ)` among the
shift-invariant random fields with the same specific `Ψ`-energy `x = ⟨μ, Ψ⟩`, i.e.
`𝓀(μ|Φ) = J_Ψ(x|Φ)`, and let `t ∈ ℝ^k` be a subgradient of the convex rate function
`J_Ψ(·|Φ)` at `x`. Then `μ ∈ 𝒢_Θ(Φ − t·Ψ)`.

This is the *equivalence of ensembles*: the constrained (microcanonical) minimisers of the free
energy are the unconstrained (grand canonical) Gibbs measures of the potential tilted by the
Lagrange multiplier `t`. Combined with Georgii's Theorem (15.45) — not available here — every
cluster point of `°γ^{Φ|Ψ,B}_Λ` is such a minimiser, which is his Corollary (15.58).

The proof is Georgii's, with the differentiability of `J_Ψ(·|Φ)` at `x` replaced by the
subgradient inequality it produces: for a Gibbs measure `ρ ∈ 𝒢_Θ(Φ − t·Ψ)`, which exists over a
standard Borel state space, the subgradient inequality at `y = ⟨ρ, Ψ⟩` and the identity
`𝓀(·|Φ) = 𝓀(·|Φ − t·Ψ) + t·⟨·, Ψ⟩ − P(Φ − t·Ψ) + P(Φ)` give
`𝓀(μ|Φ − t·Ψ) ≤ 𝓀(ρ|Φ − t·Ψ) = 0`; the variational principle (15.39) then puts `μ` in
`𝒢_Θ(Φ − t·Ψ)`. -/
theorem mem_invariantG_sub_dotPotential_of_isMinOn {μ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) (t : K → ℝ)
    (hmin : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      = ldRate ν Φ Ψ (energyVec Ψ μ))
    (ht : ∀ y : K → ℝ, ldRate ν Φ Ψ (energyVec Ψ μ)
      + ((∑ j, t j * (y j - energyVec Ψ μ j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν 1)
      (shiftGroup (ι → ℤ) E) := by
  set Φ' : BTheta (ι → ℤ) E := Φ - dotPotential t Ψ with hΦ'
  set x : K → ℝ := energyVec Ψ μ with hx
  -- a shift-invariant Gibbs measure for the tilted potential exists
  obtain ⟨ρ, hρ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := (Φ' : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant Φ')
  have hρprob : IsProbabilityMeasure ρ := hρ.1.1
  set y : K → ℝ := energyVec Ψ ρ with hy
  -- Georgii's identity for `μ` and for `ρ`
  have hidμ := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := μ)
  have hidρ := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := ρ)
  have hρ0 : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν ρ = 0 :=
    specificRelativeEntropy_eq_zero_of_mem_invariantG ν (isShiftInvariant Φ') hρ
  -- the subgradient inequality at `y`, together with the minimality of `μ`
  have hsub : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + ((∑ j, t j * (y j - x j) : ℝ) : EReal)
      ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν ρ := by
    rw [hmin]
    exact (ht y).trans (ldRate_le hρ.2 rfl)
  rw [← hidμ, ← hidρ, hρ0, zero_add] at hsub
  -- cancel the real constants
  have hsum : (∑ j, t j * (y j - x j) : ℝ) = (∑ j, t j * y j) - ∑ j, t j * x j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  set P : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν with hP
  set P' : ℝ := (Φ' : Potential (ι → ℤ) E).pressure ν with hP'
  have hcollapse : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + ((P + ∑ j, t j * y j - P' : ℝ) : EReal)
      ≤ (0 : EReal) + ((P + ∑ j, t j * y j - P' : ℝ) : EReal) := by
    rw [zero_add]
    refine le_trans (le_of_eq ?_) hsub
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    rw [hsum]
    ring
  have h0 : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ ≤ 0 :=
    (EReal.addLECancellable_coe _).add_le_add_iff_right.1 hcollapse
  have h0' : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = 0 :=
    le_antisymm h0 (specificRelativeEntropy_nonneg ν (isShiftInvariant Φ') hμ)
  exact mem_invariantG_of_specificRelativeEntropy_eq_zero' ν (isShiftInvariant Φ') hμ h0'

variable (Φ Ψ) in
/-- **Georgii (15.60)**, in his set form `𝓜_{C,Φ} = e_Ψ⁻¹(B̄_min) ⊆ 𝒢_Θ(Φ − t·Ψ)`: every
shift-invariant random field whose specific `Ψ`-energy lies in a set `D` on which `t` is a
subgradient of `J_Ψ(·|Φ)`, and which minimises `𝓀(·|Φ)` under that constraint, is a Gibbs measure
for the tilted potential `Φ − t·Ψ`. -/
theorem subset_invariantG_sub_dotPotential {D : Set (K → ℝ)} (t : K → ℝ)
    (ht : ∀ y₀ ∈ D, ∀ y : K → ℝ,
      ldRate ν Φ Ψ y₀ + ((∑ j, t j * (y j - y₀ j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y) :
    {μ : Measure ((ι → ℤ) → E) | μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
        energyVec Ψ μ ∈ D ∧
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = ldRate ν Φ Ψ (energyVec Ψ μ)}
      ⊆ invariantG (gibbsSpecificationOfAbsolutelySummable
        (Φ := ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν 1)
        (shiftGroup (ι → ℤ) E) := by
  rintro μ ⟨hμinv, hμD, hμmin⟩
  have : IsProbabilityMeasure μ := hμinv.1
  exact mem_invariantG_sub_dotPotential_of_isMinOn hμinv t hμmin (ht _ hμD)


/-! ### Georgii Corollary (15.48): the rate function is convex with compact level sets -/

omit [Fintype K] [StandardBorelSpace E] in
/-- If the excess free energy of `μ` is the *real* number `r`, then the specific entropy of `μ`
is the real number `P(Φ) + ⟨μ, Φ⟩ − r`. -/
lemma specificEntropy_eq_of_specificRelativeEntropy_eq_coe {μ : Measure ((ι → ℤ) → E)} {r : ℝ}
    (h : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = (r : EReal)) :
    specificEntropy ν μ
      = (((Φ : Potential (ι → ℤ) E).pressure ν
          + (Φ : Potential (ι → ℤ) E).specificEnergy μ - r : ℝ) : EReal) := by
  rw [specificRelativeEntropy] at h
  set a : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ
    with ha
  have hne : specificEntropy ν μ ≠ ⊤ := specificEntropy_ne_top ν
  have hbot : specificEntropy ν μ ≠ ⊥ := by
    intro hb
    rw [hb, EReal.sub_bot (EReal.coe_ne_bot _)] at h
    exact EReal.top_ne_coe _ h
  have hk : ((specificEntropy ν μ).toReal : EReal) = specificEntropy ν μ :=
    EReal.coe_toReal hne hbot
  rw [← hk, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
  rw [← hk, EReal.coe_eq_coe_iff]
  linarith

omit [Fintype K] [StandardBorelSpace E] in
/-- **Georgii Proposition (15.14), the convexity half, transported to the excess free energy.**
If `𝓀(μ₁|Φ) = r₁` and `𝓀(μ₂|Φ) = r₂` are real, then `𝓀(s μ₁ + t μ₂|Φ) ≤ s r₁ + t r₂` for
`s + t = 1`. Only the *concavity* of the specific entropy is used, which holds for arbitrary
finite measures; no shift invariance is needed. -/
lemma specificRelativeEntropy_smul_add_smul_le {μ₁ μ₂ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {r₁ r₂ : ℝ}
    (h₁ : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ₁ = (r₁ : EReal))
    (h₂ : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ₂ = (r₂ : EReal))
    {s t : ℝ≥0} (hst : s + t = 1) :
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν (s • μ₁ + t • μ₂)
      ≤ (((s : ℝ) * r₁ + (t : ℝ) * r₂ : ℝ) : EReal) := by
  set P : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν with hP
  set a₁ : ℝ := (Φ : Potential (ι → ℤ) E).specificEnergy μ₁ with ha₁
  set a₂ : ℝ := (Φ : Potential (ι → ℤ) E).specificEnergy μ₂ with ha₂
  have hstR : (s : ℝ) + (t : ℝ) = 1 := by
    rw [← NNReal.coe_add, hst, NNReal.coe_one]
  have henergy : (Φ : Potential (ι → ℤ) E).specificEnergy (s • μ₁ + t • μ₂)
      = (s : ℝ) * a₁ + (t : ℝ) * a₂ := specificEnergy_smul_add_smul μ₁ μ₂ s t
  have hlow : (((s : ℝ) * (P + a₁ - r₁) + (t : ℝ) * (P + a₂ - r₂) : ℝ) : EReal)
      ≤ specificEntropy ν (s • μ₁ + t • μ₂) := by
    refine le_trans (le_of_eq ?_) (smul_specificEntropy_add_smul_specificEntropy_le ν hst)
    rw [specificEntropy_eq_of_specificRelativeEntropy_eq_coe h₁,
      specificEntropy_eq_of_specificRelativeEntropy_eq_coe h₂, ← EReal.coe_mul, ← EReal.coe_mul,
      ← EReal.coe_add]
  calc (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν (s • μ₁ + t • μ₂)
      = ((P + ((s : ℝ) * a₁ + (t : ℝ) * a₂) : ℝ) : EReal)
        - specificEntropy ν (s • μ₁ + t • μ₂) := by
        rw [specificRelativeEntropy, henergy]
    _ ≤ ((P + ((s : ℝ) * a₁ + (t : ℝ) * a₂) : ℝ) : EReal)
        - (((s : ℝ) * (P + a₁ - r₁) + (t : ℝ) * (P + a₂ - r₂) : ℝ) : EReal) :=
        EReal.sub_le_sub le_rfl hlow
    _ = (((s : ℝ) * r₁ + (t : ℝ) * r₂ : ℝ) : EReal) := by
        rw [← EReal.coe_sub, EReal.coe_eq_coe_iff]
        linear_combination (-P) * hstR

omit [Fintype K] in
variable (Φ Ψ) in
/-- The attainment of the infimum defining `J_Ψ(x|Φ)`, in real form: below any real level `r` the
infimum is attained at a shift-invariant random field whose excess free energy is a real number
`≤ r`. -/
theorem exists_specificRelativeEntropy_eq_coe_of_ldRate_le {r : ℝ}
    (h : ldRate ν Φ Ψ x ≤ (r : EReal)) :
    ∃ (μ : Measure ((ι → ℤ) → E)) (ρ : ℝ), μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      energyVec Ψ μ = x ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = (ρ : EReal) ∧ ρ ≤ r := by
  have hne : ldRate ν Φ Ψ x ≠ ⊤ := (h.trans_lt (EReal.coe_lt_top r)).ne
  obtain ⟨μ, hμinv, hμx, hμ⟩ := exists_specificRelativeEntropy_eq_ldRate Φ Ψ x hne
  have hbot : ldRate ν Φ Ψ x ≠ ⊥ :=
    fun hb ↦ absurd (hb ▸ ldRate_nonneg (ν := ν) (Φ := Φ) (Ψ := Ψ) (x := x)) (by simp)
  refine ⟨μ, (ldRate ν Φ Ψ x).toReal, hμinv, hμx, ?_, ?_⟩
  · rw [hμ, EReal.coe_toReal hne hbot]
  · exact EReal.coe_le_coe_iff.1 ((EReal.coe_toReal hne hbot).symm ▸ h)

omit [Fintype K] in
/-- **Georgii Corollary (15.48), the convexity of the rate function.** `J_Ψ(·|Φ)` is convex: the
excess free energy is affine and the constraint `⟨·, Ψ⟩ = x` is linear, so a convex combination of
(almost) minimisers is admissible for the combined constraint. -/
theorem ldRate_smul_add_smul_le {x₁ x₂ : K → ℝ} {r₁ r₂ : ℝ}
    (h₁ : ldRate ν Φ Ψ x₁ ≤ (r₁ : EReal)) (h₂ : ldRate ν Φ Ψ x₂ ≤ (r₂ : EReal))
    {s t : ℝ≥0} (hst : s + t = 1) :
    ldRate ν Φ Ψ (fun j ↦ (s : ℝ) * x₁ j + (t : ℝ) * x₂ j)
      ≤ (((s : ℝ) * r₁ + (t : ℝ) * r₂ : ℝ) : EReal) := by
  obtain ⟨μ₁, ρ₁, hμ₁, hx₁, hρ₁, hr₁⟩ := exists_specificRelativeEntropy_eq_coe_of_ldRate_le Φ Ψ h₁
  obtain ⟨μ₂, ρ₂, hμ₂, hx₂, hρ₂, hr₂⟩ := exists_specificRelativeEntropy_eq_coe_of_ldRate_le Φ Ψ h₂
  have hp₁ : IsProbabilityMeasure μ₁ := hμ₁.1
  have hp₂ : IsProbabilityMeasure μ₂ := hμ₂.1
  have henergy : energyVec Ψ (s • μ₁ + t • μ₂) = fun j ↦ (s : ℝ) * x₁ j + (t : ℝ) * x₂ j := by
    funext j
    rw [energyVec_apply, specificEnergy_smul_add_smul μ₁ μ₂ s t, ← hx₁, ← hx₂]
    rfl
  refine le_trans (ldRate_le (smul_add_smul_mem_invariantFields_shiftGroup hμ₁ hμ₂ hst) henergy)
    (le_trans (specificRelativeEntropy_smul_add_smul_le hρ₁ hρ₂ hst) ?_)
  exact EReal.coe_le_coe_iff.2 (by gcongr)

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii Corollary (15.48).** The level sets `{J_Ψ(·|Φ) ≤ c}` of the rate function are
compact: they are the `e_Ψ`-images of the compact level sets `{𝓀(·|Φ) ≤ c} ∩ 𝓟_Θ`. -/
theorem isCompact_setOf_ldRate_le (c : ℝ) :
    IsCompact {x : K → ℝ | ldRate ν Φ Ψ x ≤ (c : EReal)} := by
  set L : Set (WithLocalConvergence (ι → ℤ) E) :=
    {μ : WithLocalConvergence (ι → ℤ) E |
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)} ∩
      {μ : WithLocalConvergence (ι → ℤ) E | ∀ τ ∈ shiftGroup (ι → ℤ) E,
        MeasurePreserving τ.toFun (μ.toMeasure : Measure ((ι → ℤ) → E))
          (μ.toMeasure : Measure ((ι → ℤ) → E))} with hLdef
  have hLcompact : IsCompact L :=
    (isCompact_setOf_specificRelativeEntropy_le ν Φ c).inter_right
      (isClosed_setOf_forall_measurePreserving _)
  have himage : {x : K → ℝ | ldRate ν Φ Ψ x ≤ (c : EReal)}
      = (fun μ : WithLocalConvergence (ι → ℤ) E ↦
          energyVec Ψ (μ.toMeasure : Measure ((ι → ℤ) → E))) '' L := by
    ext y
    constructor
    · intro hy
      obtain ⟨μ, ρ, hμinv, hμy, hμρ, hρ⟩ :=
        exists_specificRelativeEntropy_eq_coe_of_ldRate_le Φ Ψ hy
      have hprob : IsProbabilityMeasure μ := hμinv.1
      obtain ⟨-, hshift⟩ := mem_invariantFields_shiftGroup.1 hμinv
      refine ⟨WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩, ⟨?_, ?_⟩, hμy⟩
      · show (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ ≤ (c : EReal)
        rw [hμρ]
        exact EReal.coe_le_coe_iff.2 hρ
      · rintro τ ⟨j, rfl⟩
        exact hshift j
    · rintro ⟨μ, ⟨hkμ, hshift⟩, rfl⟩
      have hinv : (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) :=
        mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦ hshift _ (shift_mem_shiftGroup j)⟩
      exact (ldRate_le hinv rfl).trans hkμ
  rw [himage]
  exact hLcompact.image (continuous_pi fun j ↦ continuous_specificEnergy)

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii Corollary (15.48).** The level sets of the rate function are closed. -/
theorem isClosed_setOf_ldRate_le (c : ℝ) :
    IsClosed {x : K → ℝ | ldRate ν Φ Ψ x ≤ (c : EReal)} :=
  (isCompact_setOf_ldRate_le Φ Ψ c).isClosed

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii Corollary (15.48).** The rate function is lower semicontinuous. -/
theorem lowerSemicontinuous_ldRate : LowerSemicontinuous (ldRate ν Φ Ψ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot =>
      convert isClosed_empty
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, le_bot_iff]
      intro hcon
      exact absurd (hcon ▸ ldRate_nonneg (ν := ν) (Φ := Φ) (Ψ := Ψ) (x := y)) (by simp)
  | coe c => exact isClosed_setOf_ldRate_le Φ Ψ c
  | top => simp


/-! ### Georgii (15.49): the rate function is the Legendre transform of the pressure -/

omit [Fintype ι] [DecidableEq ι] [StandardBorelSpace E] in
@[simp] lemma dotPotential_zero : dotPotential (0 : K → ℝ) Ψ = 0 := by
  simp [dotPotential]

variable (Φ Ψ) in
/-- **Georgii, in the proof of (15.49).** The dual quantity `P(Φ − t·Ψ) − P(Φ)` is *attained*: a
shift-invariant Gibbs measure `μ` of the tilted potential `Φ − t·Ψ` — which exists over a standard
Borel state space — satisfies `𝓀(μ|Φ) = P(Φ) + t·⟨μ, Ψ⟩ − P(Φ − t·Ψ)`. Together with
`Potential.BTheta.coe_le_ldRate` this says that `t ↦ P(Φ − t·Ψ) − P(Φ)` is the convex conjugate of
`J_Ψ(·|Φ)`. -/
theorem exists_specificRelativeEntropy_eq_pressure_sub (t : K → ℝ) :
    ∃ μ : Measure ((ι → ℤ) → E), μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
        = (((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * energyVec Ψ μ j
            - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
              Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := by
  obtain ⟨μ, hμ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν 1
    (isShiftInvariant _)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  refine ⟨μ, hμ.2, ?_⟩
  have hid := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := μ)
  rw [specificRelativeEntropy_eq_zero_of_mem_invariantG ν (isShiftInvariant _) hμ,
    zero_add] at hid
  exact hid.symm

variable (ν Φ Ψ) in
/-- The epigraph `{(x, r) : J_Ψ(x|Φ) ≤ r}` of the rate function, the convex closed set that
Georgii separates from `(x, c)` by the Hahn–Banach theorem in the proof of (15.49). -/
def ldRateEpigraph : Set ((K → ℝ) × ℝ) := {p | ldRate ν Φ Ψ p.1 ≤ (p.2 : EReal)}

omit [Fintype K] [StandardBorelSpace E] in
lemma mem_ldRateEpigraph_iff {p : (K → ℝ) × ℝ} :
    p ∈ ldRateEpigraph ν Φ Ψ ↔ ldRate ν Φ Ψ p.1 ≤ (p.2 : EReal) := Iff.rfl

omit [Fintype K] in
variable (ν Φ Ψ) in
/-- The epigraph of `J_Ψ(·|Φ)` is convex, because `J_Ψ(·|Φ)` is convex. -/
theorem convex_ldRateEpigraph : Convex ℝ (ldRateEpigraph ν Φ Ψ) := by
  rintro ⟨x₁, r₁⟩ h₁ ⟨x₂, r₂⟩ h₂ a b ha hb hab
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = b := ⟨⟨b, hb⟩, rfl⟩
  have hst : s + t = 1 := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_add, NNReal.coe_one, hs, ht]
    exact hab
  have hfun : a • x₁ + b • x₂ = fun j ↦ (s : ℝ) * x₁ j + (t : ℝ) * x₂ j := by
    funext j
    simp [hs, ht]
  show ldRate ν Φ Ψ (a • x₁ + b • x₂) ≤ ((a * r₁ + b * r₂ : ℝ) : EReal)
  rw [hfun, ← hs, ← ht]
  exact ldRate_smul_add_smul_le h₁ h₂ hst

omit [Fintype K] in
variable (ν Φ Ψ) in
/-- The epigraph of `J_Ψ(·|Φ)` is closed, because `J_Ψ(·|Φ)` is lower semicontinuous. -/
theorem isClosed_ldRateEpigraph : IsClosed (ldRateEpigraph ν Φ Ψ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨y, r⟩ h
  have hlt : ((r : ℝ) : EReal) < ldRate ν Φ Ψ y := not_le.1 h
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
  refine mem_nhds_iff.2 ⟨{z : K → ℝ | ¬ ldRate ν Φ Ψ z ≤ ((q : ℝ) : EReal)} ×ˢ
    Set.Iio ((q : ℝ)), ?_, ?_, ?_⟩
  · rintro ⟨z, w⟩ ⟨hz, hw⟩ hmem
    exact hz (le_trans hmem (EReal.coe_le_coe_iff.2 (le_of_lt hw)))
  · exact ((isClosed_setOf_ldRate_le Φ Ψ (q : ℝ)).isOpen_compl).prod isOpen_Iio
  · exact ⟨not_le.2 hq2, EReal.coe_lt_coe_iff.1 hq1⟩

variable (Φ Ψ x) in
/-- **Georgii (15.49).** The rate function is, up to the additive constant `P(Φ)`, the
Legendre–Fenchel transform of the convex function `t ↦ P(Φ − t·Ψ)`:
`J_Ψ(x|Φ) = sup_{t ∈ ℝ^k} [t·x − P(Φ − t·Ψ)] + P(Φ)`.

`≥` is `Potential.BTheta.coe_le_ldRate`, which is the nonnegativity of `𝓀(·|Φ − t·Ψ)`. For `≤`,
Georgii extends the linear functional `t·Ψ ↦ t·x` from the span of `Ψ¹, …, Ψᵏ` to `ℬ_Θ` by
Hahn–Banach and identifies the extension by Theorem (16.13). The proof here separates the point
`(x, c)` from the closed convex epigraph of `J_Ψ(·|Φ)` inside `ℝ^k × ℝ`, which needs no
representation theorem: the level sets of `J_Ψ(·|Φ)` are compact
(`Potential.BTheta.isCompact_setOf_ldRate_le`), so the epigraph is closed, and the conjugate of
`J_Ψ(·|Φ)` is attained at a Gibbs measure of the tilted potential
(`Potential.BTheta.exists_specificRelativeEntropy_eq_pressure_sub`). A vertical separating
hyperplane is excluded by letting the multiplier tend to infinity. -/
theorem ldRate_eq_iSup :
    ldRate ν Φ Ψ x = ⨆ t : K → ℝ, (((∑ j, t j * x j)
        - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
        + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := by
  have h := eq_iSup_sub_of_isClosed_convex_epigraph (J := ldRate ν Φ Ψ)
    (g := fun t : K → ℝ ↦
      ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
        - (Φ : Potential (ι → ℤ) E).pressure ν)
    (convex_ldRateEpigraph ν Φ Ψ) (isClosed_ldRateEpigraph ν Φ Ψ) ?_ ?_ x
  · rw [h]
    refine iSup_congr fun t ↦ ?_
    rw [EReal.coe_eq_coe_iff]
    ring
  · intro t y
    refine le_trans (le_of_eq ?_) (coe_le_ldRate (ν := ν) (Φ := Φ) (Ψ := Ψ) (x := y) t)
    rw [EReal.coe_eq_coe_iff]
    ring
  · intro t
    obtain ⟨μ, hμinv, hμeq⟩ := exists_specificRelativeEntropy_eq_pressure_sub (ν := ν) Φ Ψ t
    have hprob : IsProbabilityMeasure μ := hμinv.1
    have heq : ((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * energyVec Ψ μ j
          - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν)
        = (∑ j, t j * energyVec Ψ μ j)
          - (((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
            - (Φ : Potential (ι → ℤ) E).pressure ν) := by ring
    refine ⟨energyVec Ψ μ, (∑ j, t j * energyVec Ψ μ j)
      - (((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
        - (Φ : Potential (ι → ℤ) E).pressure ν), ?_, ?_, rfl⟩
    · rw [← heq, ← hμeq]
      exact ldRate_le hμinv rfl
    · have hnn := specificRelativeEntropy_nonneg (Φ := (Φ : Potential (ι → ℤ) E)) (μ := μ) ν
        (isShiftInvariant Φ) hμinv
      rw [hμeq] at hnn
      rw [← heq]
      exact_mod_cast hnn

variable (Φ Ψ) in
/-- **Georgii (15.49), the dual identity.** The convex conjugate of the rate function is the
pressure difference: `sup_x [t·x − J_Ψ(x|Φ)] = P(Φ − t·Ψ) − P(Φ)`. The supremum is attained at the
specific `Ψ`-energy of any shift-invariant Gibbs measure of the tilted potential `Φ − t·Ψ`, by
the variational principle (15.39). Together with `Potential.BTheta.ldRate_eq_iSup` this says that
`J_Ψ(·|Φ)` and `t ↦ P(Φ − t·Ψ) − P(Φ)` are convex conjugates of each other. -/
theorem iSup_sub_ldRate_eq (t : K → ℝ) :
    (⨆ y : K → ℝ, (((∑ j, t j * y j : ℝ) : EReal) - ldRate ν Φ Ψ y))
      = ((((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
          - (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := by
  refine le_antisymm (iSup_le fun y ↦ ?_) ?_
  · refine le_trans (EReal.sub_le_sub le_rfl (coe_le_ldRate (x := y) t)) (le_of_eq ?_)
    rw [← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring
  · obtain ⟨μ, hμinv, hμeq⟩ := exists_specificRelativeEntropy_eq_pressure_sub (ν := ν) Φ Ψ t
    refine le_trans ?_ (le_iSup
      (fun y : K → ℝ ↦ (((∑ j, t j * y j : ℝ) : EReal) - ldRate ν Φ Ψ y)) (energyVec Ψ μ))
    refine le_trans (le_of_eq ?_) (EReal.sub_le_sub le_rfl
      ((ldRate_le hμinv rfl).trans (le_of_eq hμeq)))
    rw [← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring

omit [Fintype K] [StandardBorelSpace E] in
/-- A finite value of the rate function is a real number: `J_Ψ(·|Φ)` never takes the value
`−∞`. -/
lemma exists_ldRate_eq_coe (h : ldRate ν Φ Ψ x ≠ ⊤) : ∃ r : ℝ, ldRate ν Φ Ψ x = (r : EReal) := by
  refine ⟨(ldRate ν Φ Ψ x).toReal, (EReal.coe_toReal h ?_).symm⟩
  exact fun hb ↦ absurd (hb ▸ ldRate_nonneg (ν := ν) (Φ := Φ) (Ψ := Ψ) (x := x)) (by simp)

/-! ### Georgii Corollary (15.58): the Lagrange multiplier is unique -/

variable (Φ Ψ) in
/-- **The convex-analytic input of Georgii's Corollary (15.58)**, Georgii's reference to
Rockafellar (1970), p. 253, reduced to what his proof consumes. If the convex function
`t ↦ P(Φ − t·Ψ)` — whose Legendre transform is `J_Ψ(·|Φ) − P(Φ)` by (15.49) — is *strictly*
convex, then `J_Ψ(·|Φ)` has **at most one** subgradient at each point of its essential domain.
(Georgii writes the hypothesis as strict convexity of `t ↦ P(Φ + t·Ψ)`; the two functions differ
by the substitution `t ↦ −t`, since `dotPotential (−t) Ψ = −dotPotential t Ψ`.)

The proof is the elementary half of the Legendre correspondence: a subgradient `t` of `J_Ψ(·|Φ)`
at `x` makes the supremum `sup_y [t·y − J_Ψ(y|Φ)] = P(Φ − t·Ψ) − P(Φ)` of
`Potential.BTheta.iSup_sub_ldRate_eq` attained at `y = x`, which says exactly that the linear
functional `s ↦ s·x` is a subgradient of `t ↦ P(Φ − t·Ψ)` at `t`; and a strictly convex function
is supported by a given linear functional at one point at most
(`StrictConvexOn.eq_of_mem_subgradientAt`).

Georgii uses the resulting uniqueness twice in the proof of (15.58): to identify `t' = J'(x')`
with `t* = J'(x*)`, and to conclude that `J'` is constant on `B̄_min ∩ D°`. -/
theorem subgradient_ldRate_unique
    (hP : StrictConvexOn ℝ Set.univ fun t : K → ℝ ↦
      ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν)
    {x : K → ℝ} (hx : ldRate ν Φ Ψ x ≠ ⊤) {t₁ t₂ : K → ℝ}
    (h₁ : ∀ y : K → ℝ,
      ldRate ν Φ Ψ x + ((∑ j, t₁ j * (y j - x j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y)
    (h₂ : ∀ y : K → ℝ,
      ldRate ν Φ Ψ x + ((∑ j, t₂ j * (y j - x j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y) :
    t₁ = t₂ := by
  classical
  obtain ⟨r, hr⟩ := exists_ldRate_eq_coe hx
  set L : (K → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun s ↦ ∑ j, x j * s j
      map_add' := fun s₁ s₂ ↦ by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by simp [mul_add]
      map_smul' := fun c s ↦ by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by simp [mul_left_comm] } with hLdef
  have key : ∀ t : K → ℝ,
      (∀ y : K → ℝ, ldRate ν Φ Ψ x + ((∑ j, t j * (y j - x j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y) →
      L ∈ subgradientAt (fun t : K → ℝ ↦
        ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν) t := by
    intro t ht z
    -- the supremum of (15.49) is attained at `y = x`
    have hupper : ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
        - (Φ : Potential (ι → ℤ) E).pressure ν ≤ (∑ j, t j * x j) - r := by
      have hsup : (⨆ y : K → ℝ, (((∑ j, t j * y j : ℝ) : EReal) - ldRate ν Φ Ψ y))
          ≤ ((((∑ j, t j * x j) - r : ℝ)) : EReal) := by
        refine iSup_le fun y ↦ ?_
        by_cases hy : ldRate ν Φ Ψ y = ⊤
        · rw [hy]
          simp
        · obtain ⟨r', hr'⟩ := exists_ldRate_eq_coe hy
          rw [hr', ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have hty := ht y
          rw [hr, hr', ← EReal.coe_add, EReal.coe_le_coe_iff] at hty
          have hsum : (∑ j, t j * (y j - x j)) = (∑ j, t j * y j) - ∑ j, t j * x j := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
          rw [hsum] at hty
          linarith
      rw [iSup_sub_ldRate_eq] at hsup
      exact EReal.coe_le_coe_iff.1 hsup
    have hlower : ∀ s : K → ℝ, (∑ j, s j * x j) - r
        ≤ ((Φ - dotPotential s Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
          - (Φ : Potential (ι → ℤ) E).pressure ν := by
      intro s
      have h := le_iSup (fun y : K → ℝ ↦ (((∑ j, s j * y j : ℝ) : EReal) - ldRate ν Φ Ψ y)) x
      rw [iSup_sub_ldRate_eq, hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
      exact h
    have hz := hlower (t + z)
    have hsum : (∑ j, (t + z) j * x j) = (∑ j, t j * x j) + ∑ j, z j * x j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by simp [add_mul]
    have hcomm : (∑ j, z j * x j) = ∑ j, x j * z j :=
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
    rw [hsum, hcomm] at hz
    have hLz : L z = ∑ j, x j * z j := rfl
    change L z ≤ ((Φ - dotPotential (t + z) Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E).pressure ν
      - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν
    rw [hLz]
    linarith
  exact hP.eq_of_mem_subgradientAt (key t₁ h₁) (key t₂ h₂)

/-! ### Georgii (15.59): the infimum of the rate function over a convex set -/

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii Example (15.50), second assertion.** `J_Ψ(·|Φ)` is nondecreasing on
`[a⁺, ∞)`, where `a⁺ = ∂⁺_{−Ψ}P(Φ)` is the right endpoint of the interval on which it vanishes:
if `a⁺ ≤ u ≤ v` then `u` is a convex combination of `a⁺` and `v`, `J_Ψ(a⁺|Φ) = 0`, and `J_Ψ` is
convex and nonnegative. (Georgii's "by convexity, `J_Ψ(·|Φ)` is monotone on either side of this
interval".) -/
theorem ldRate_le_ldRate_of_le [Unique K] {x y : K → ℝ}
    (hx : rightDirDeriv (pressure ν) Φ (-Ψ default) ≤ x default)
    (hxy : x default ≤ y default) :
    ldRate ν Φ Ψ x ≤ ldRate ν Φ Ψ y := by
  by_cases htop : ldRate ν Φ Ψ y = ⊤
  · rw [htop]; exact le_top
  obtain ⟨r, hr⟩ := exists_ldRate_eq_coe htop
  have hr0 : 0 ≤ r := by
    have h := ldRate_nonneg (ν := ν) (Φ := Φ) (Ψ := Ψ) (x := y)
    rw [hr] at h
    exact_mod_cast h
  set p : ℝ := rightDirDeriv (pressure ν) Φ (-Ψ default) with hp
  have hc0 : ldRate ν Φ Ψ (fun _ ↦ p) = 0 := by
    rw [ldRate_eq_zero_iff_mem_Icc]
    exact Set.mem_Icc.2 ⟨leftDirDeriv_le_rightDirDeriv_pressure ν Φ (-Ψ default), le_rfl⟩
  rcases eq_or_lt_of_le hxy with heq | hlt
  · have hxy' : x = y := funext fun j ↦ by
      obtain rfl : j = default := Subsingleton.elim _ _
      exact heq
    rw [hxy']
  -- `x = (1 − σ) a⁺ + σ y` with `σ = (x − a⁺)/(y − a⁺) ∈ [0, 1]`
  have hpy : p < y default := lt_of_le_of_lt hx hlt
  set σ : ℝ := (x default - p) / (y default - p) with hσ
  have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
  have hσ1 : σ ≤ 1 := by
    rw [hσ, div_le_one (by linarith)]
    linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = σ := ⟨⟨σ, hσ0⟩, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ≥0, (u : ℝ) = 1 - σ := ⟨⟨1 - σ, by linarith⟩, rfl⟩
  have hut : u + t = 1 := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_add, NNReal.coe_one, hu, ht]
    ring
  have hne : y default - p ≠ 0 := by linarith
  have hcombo : (fun j ↦ (u : ℝ) * (fun _ : K ↦ p) j + (t : ℝ) * y j) = x := by
    funext j
    obtain rfl : j = default := Subsingleton.elim _ _
    change (u : ℝ) * p + (t : ℝ) * y default = x default
    rw [hu, ht, hσ]
    field_simp
    ring
  have hmain := ldRate_smul_add_smul_le (ν := ν) (Φ := Φ) (Ψ := Ψ)
    (x₁ := fun _ : K ↦ p) (x₂ := y) (r₁ := 0) (r₂ := r) (le_of_eq hc0) (le_of_eq hr) hut
  rw [hcombo] at hmain
  rw [hr]
  refine hmain.trans (EReal.coe_le_coe_iff.2 ?_)
  rw [mul_zero, zero_add, ht]
  nlinarith

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii Example (15.50):** strictly to the right of `a⁺ = ∂⁺_{−Ψ}P(Φ)` the rate function is
strictly positive, since it vanishes exactly on `[a⁻, a⁺]` and is nonnegative. Together with the
finiteness hypothesis of `Potential.BTheta.iInf_ldRate_Ioi_eq` this is Georgii's
`0 < J_Ψ(a|Φ) < ∞` for `a⁺_{f,Φ} < a < a⁺_f`. -/
theorem ldRate_pos [Unique K] {x : K → ℝ}
    (hx : rightDirDeriv (pressure ν) Φ (-Ψ default) < x default) : 0 < ldRate ν Φ Ψ x :=
  lt_of_le_of_ne ldRate_nonneg fun h ↦
    absurd ((ldRate_eq_zero_iff_mem_Icc Φ Ψ x).1 h.symm).2 (not_le.2 hx)

omit [Fintype K] in
variable (Φ Ψ) in
/-- **The right-hand limit of `J_Ψ(·|Φ)` at a point of `[a⁺, ∞)`.** If `J_Ψ(·|Φ)` is finite
somewhere strictly to the right of `a ≥ a⁺`, then `inf {J_Ψ(y|Φ) : y > a} = J_Ψ(a|Φ)`: the
infimum is `≥` by monotonicity and `≤` by convexity along the segment from `a` to that point.
This is what makes the two bounds of Corollary (15.48) meet for the half-line `[a, ∞)`, i.e.
what turns them into Georgii's asymptotics (15.51). -/
theorem iInf_ldRate_Ioi_eq [Unique K] {a b : ℝ}
    (ha : rightDirDeriv (pressure ν) Φ (-Ψ default) ≤ a) (hab : a < b)
    (hb : ldRate ν Φ Ψ (fun _ ↦ b) ≠ ⊤) :
    ⨅ y ∈ {y : K → ℝ | a < y default}, ldRate ν Φ Ψ y = ldRate ν Φ Ψ fun _ ↦ a := by
  have hmono : ∀ u v : ℝ, a ≤ u → u ≤ v →
      ldRate ν Φ Ψ (fun _ : K ↦ u) ≤ ldRate ν Φ Ψ fun _ : K ↦ v := fun u v hu huv ↦
    ldRate_le_ldRate_of_le Φ Ψ (ha.trans hu) huv
  refine le_antisymm ?_ (le_iInf₂ fun y hy ↦ ?_)
  · have hafin : ldRate ν Φ Ψ (fun _ : K ↦ a) ≠ ⊤ :=
      ne_top_of_le_ne_top hb (hmono a b le_rfl hab.le)
    obtain ⟨ra, hra⟩ := exists_ldRate_eq_coe hafin
    obtain ⟨rb, hrb⟩ := exists_ldRate_eq_coe hb
    rw [hra]
    have hstep : ∀ n : ℕ, (⨅ y ∈ {y : K → ℝ | a < y default}, ldRate ν Φ Ψ y)
        ≤ ((((1 - 1 / ((n : ℝ) + 1)) * ra + (1 / ((n : ℝ) + 1)) * rb : ℝ)) : EReal) := by
      intro n
      set c : ℝ := 1 / ((n : ℝ) + 1) with hc
      have hcpos : 0 < c := by positivity
      have hcle : c ≤ 1 := by
        rw [hc, div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = c := ⟨⟨c, hcpos.le⟩, rfl⟩
      obtain ⟨u, hu⟩ : ∃ u : ℝ≥0, (u : ℝ) = 1 - c := ⟨⟨1 - c, by linarith⟩, rfl⟩
      have hut : u + t = 1 := by
        refine NNReal.coe_injective ?_
        rw [NNReal.coe_add, NNReal.coe_one, hu, ht]
        ring
      have hmem : (fun j ↦ (u : ℝ) * (fun _ : K ↦ a) j + (t : ℝ) * (fun _ : K ↦ b) j)
          ∈ {y : K → ℝ | a < y default} := by
        change a < (u : ℝ) * a + (t : ℝ) * b
        rw [hu, ht]
        nlinarith
      refine (iInf₂_le _ hmem).trans (le_of_le_of_eq
        (ldRate_smul_add_smul_le (le_of_eq hra) (le_of_eq hrb) hut) ?_)
      rw [EReal.coe_eq_coe_iff, hu, ht]
    have hten : Tendsto (fun n : ℕ ↦
        ((((1 - 1 / ((n : ℝ) + 1)) * ra + (1 / ((n : ℝ) + 1)) * rb : ℝ)) : EReal)) atTop
        (𝓝 ((ra : ℝ) : EReal)) := by
      refine EReal.tendsto_coe.2 ?_
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Tendsto (fun n : ℕ ↦ (1 - 1 / ((n : ℝ) + 1)) * ra + (1 / ((n : ℝ) + 1)) * rb)
          atTop (𝓝 ((1 - 0) * ra + 0 * rb)) :=
        ((tendsto_const_nhds.sub h0).mul tendsto_const_nhds).add (h0.mul tendsto_const_nhds)
      simpa using h1
    exact ge_of_tendsto hten (.of_forall hstep)
  · have hy' : (fun _ : K ↦ y default) = y := funext fun j ↦ by
      obtain rfl : j = default := Subsingleton.elim _ _
      rfl
    exact hy' ▸ hmono a (y default) le_rfl hy.le

omit [Fintype K] in
variable (Φ Ψ) in
/-- **Georgii (15.59).** For a convex set `B ⊆ ℝ^k` whose interior meets the essential domain of
the rate function, the infimum of `J_Ψ(·|Φ)` over the closure of `B` is already attained over its
interior. This is the hypothesis (15.56) of the minimum free energy principle, and it is what
makes the microcanonical conditioning of Corollary (15.58) legitimate.

Georgii's proof: if `x* ∈ B° ∩ D` and `x ∈ B̄`, then `a x* + (1 − a) x ∈ B°` for `0 < a < 1`
(`Convex.combo_interior_closure_mem_interior`), and the convexity of `J_Ψ(·|Φ)` gives
`inf_{B°} J ≤ a J(x*) + (1 − a) J(x) → J(x)` as `a ↓ 0`. -/
theorem iInf_ldRate_interior_eq_iInf_closure {B : Set (K → ℝ)} (hB : Convex ℝ B)
    {x₀ : K → ℝ} (hx₀ : x₀ ∈ interior B) (hfin : ldRate ν Φ Ψ x₀ ≠ ⊤) :
    ⨅ y ∈ interior B, ldRate ν Φ Ψ y = ⨅ y ∈ closure B, ldRate ν Φ Ψ y := by
  refine le_antisymm ?_ (le_iInf₂ fun y hy ↦ iInf₂_le y (interior_subset.trans subset_closure hy))
  refine le_iInf₂ fun y hy ↦ ?_
  by_cases hytop : ldRate ν Φ Ψ y = ⊤
  · rw [hytop]; exact le_top
  obtain ⟨r₀, hr₀⟩ := exists_ldRate_eq_coe hfin
  obtain ⟨r, hr⟩ := exists_ldRate_eq_coe hytop
  rw [hr]
  have hstep : ∀ n : ℕ, (⨅ z ∈ interior B, ldRate ν Φ Ψ z)
      ≤ (((1 / ((n : ℝ) + 1)) * r₀ + (1 - 1 / ((n : ℝ) + 1)) * r : ℝ) : EReal) := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with ha
    have hapos : 0 < a := by positivity
    have hale : a ≤ 1 := by
      rw [ha, div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = a := ⟨⟨a, hapos.le⟩, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = 1 - a := ⟨⟨1 - a, by linarith⟩, rfl⟩
    have hst : s + t = 1 := by
      refine NNReal.coe_injective ?_
      rw [NNReal.coe_add, NNReal.coe_one, hs, ht]
      ring
    have hmem : a • x₀ + (1 - a) • y ∈ interior B :=
      hB.combo_interior_closure_mem_interior hx₀ hy hapos (by linarith) (by ring)
    have hfun : (fun j ↦ (s : ℝ) * x₀ j + (t : ℝ) * y j) = a • x₀ + (1 - a) • y := by
      funext j
      simp [hs, ht]
    have hmem' : (fun j ↦ (s : ℝ) * x₀ j + (t : ℝ) * y j) ∈ interior B := by
      rw [hfun]; exact hmem
    refine le_trans (iInf₂_le _ hmem') (le_of_le_of_eq
      (ldRate_smul_add_smul_le (le_of_eq hr₀) (le_of_eq hr) hst) ?_)
    rw [EReal.coe_eq_coe_iff, hs, ht]
  have hten : Tendsto (fun n : ℕ ↦
      (((1 / ((n : ℝ) + 1)) * r₀ + (1 - 1 / ((n : ℝ) + 1)) * r : ℝ) : EReal)) atTop
      (𝓝 ((r : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.2 ?_
    have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) * r₀ + (1 - 1 / ((n : ℝ) + 1)) * r)
        atTop (𝓝 (0 * r₀ + (1 - 0) * r)) :=
      (h0.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub h0).mul tendsto_const_nhds)
    simpa using h1
  exact ge_of_tendsto hten (.of_forall hstep)


end Potential.BTheta
