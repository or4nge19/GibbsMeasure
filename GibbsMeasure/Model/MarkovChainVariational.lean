/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.CountWithDensity
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PerronStochastic
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import GibbsMeasure.Model.MarkovChainReindex
public import GibbsMeasure.Specification.VariationalPrinciple

/-!
# Georgii Example (15.40): the variational principle for a Markov chain

Let `E` be finite, `Q` a positive stochastic matrix on `E` and `μ_Q` the stationary Markov chain
with transition matrix `Q`, the unique Gibbs measure of the nearest-neighbour potential
`Φ_{i-1,i}(ω) = -log Q(ω_{i-1}, ω_i)` (`Model/MarkovChain.lean`, Georgii (3.5), (3.9)).
Georgii computes the three ingredients `P(Φ)`, `⟨μ, Φ⟩`, `𝓀(μ)` of the specific relative entropy
`𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ - 𝓀(μ)` of Chapter 15 explicitly, rewrites `𝓀(μ|Φ)` as a mean relative
entropy and reads off the variational principle `𝓀(μ|Φ) = 0 ↔ μ = μ_Q` directly.

The thermodynamic formalism of Chapter 15 is stated on `ℤ^d = (ι → ℤ)`; the identification
`ℤ ≃ ℤ^1` is `(Equiv.funUnique Unit ℤ).symm`, and the Chapter 15 quantities below are stated for
the transported potential `Φ = (markovPotential Q).reindex (Equiv.funUnique Unit ℤ).symm` on the
site set `Unit → ℤ` and for the transported chain `μ_Q ∘ (· ∘ e.symm)⁻¹`
(`Model/MarkovChainReindex.lean`). Georgii's past `𝓕_{]-∞,0[}` of the origin is the
lexicographic past `V*(0) = lexPast 0 \ {0}` of `Specification/SpecificEntropy.lean`
(`lexPast_zero_diff_singleton_funUnique`), and `μ(σ_0 = x | 𝓕_{]-∞,0[})` is Mathlib's
conditional expectation `μ[1_{σ_0 = x} | cylinderEvents (lexPast 0 \ {0})]`.

## Normalisation

Georgii takes the a priori measure `λ` to be counting measure on `E` and, "without loss"
(Theorem (2.35)(b)), replaces `Φ` by an equivalent gas potential `Φ^a` with vacuum state `a`. In
the tree, `pressure`, `specificEntropy` and `specificRelativeEntropy` take a *probability*
a priori measure, here the uniform measure `ν = |E|⁻¹ ∑_x δ_x`, and the potential is `Φ` itself.
Passing from `λ` to `ν` shifts `P` and `𝓀(·)` by the same constant `-log |E|` (Georgii (15.19):
`specificEntropy_uniformOn_eq_neg_integral_sum_mul_log`); passing from `Φ` to `Φ^a` shifts
`P(·)` and `⟨μ, ·⟩` by the same constant `-log Q(a, a)` (the vacuum block
`γ_Λ(σ_Λ ≡ a | ω^a) = 1/Z^{Φ^a}_Λ(ω^a)`). Both constants cancel in `𝓀(μ|Φ)`, which is the same
extended real in Georgii's normalisation and in the tree's. Concretely, Georgii's three numbers
`P(Φ^a) = -log Q(a, a)`, `⟨μ, Φ^a⟩ = μ(log Q(a,a)/Q(σ_{-1}, σ_0))`, `𝓀^λ(μ)` correspond to
`P^ν(Φ) = -log |E|`, `⟨μ, Φ⟩ = μ(-log Q(σ_{-1}, σ_0))`, `𝓀^ν(μ) = 𝓀^λ(μ) - log |E|`.

## Main results

* `pressure_markovPotential_reindex_eq_log_perronRoot`: the general fact behind Georgii's
  computation, for any positive matrix `Q` (Georgii (3.16)–(3.17)): `P(Φ) = log r_Q - log |E|`
  with `r_Q` the Perron root of `Q` (`Mathlib/LinearAlgebra/Matrix/PerronStochastic.lean`);
  `pressure_markovPotential_reindex`: `P(Φ) = -log |E|` for a stochastic `Q` (Perron root `1`).
* `markovSpecification_Icc_apply_cyl_const`,
  `tendsto_neg_log_markovSpecification_Icc_apply_cyl_const_div` and
  `hamiltonian_Icc_sub_hamiltonian_const`: Georgii's intermediate displays on `ℤ`,
  `γ_{[1,n]}(σ_{[1,n]} ≡ a | ω^a) = Q(a,a)^{n+1}/Q^{n+1}(a,a)`,
  `-lim n⁻¹ log γ_{[1,n]}(σ_{[1,n]} ≡ a | ω^a) = -log Q(a, a)` (his value of `P(Φ^a)`), and
  `H_{[1,n]}(ω) - H_{[1,n]}(ω^a) = log ∏_{i=0}^n Q(a,a)/Q(ω_i, ω_{i+1})`.
* `specificEnergy_markovPotential_reindex`: `⟨μ, Φ⟩ = μ(-log Q(σ_{-1}, σ_0))` for `μ ∈ 𝓟_Θ`, from
  the energy density `f_Φ = ½(-log Q(σ_{-1}, σ_0) - log Q(σ_0, σ_1))`
  (`siteEnergy_markovPotential_reindex`) and shift-invariance.
* `specificRelativeEntropy_markovPotential_reindex`: Georgii's first display,
  `𝓀(μ|Φ) = μ(-log Q(σ_{-1}, σ_0) + ∑_x μ(σ_0 = x | 𝓕_{<0}) log μ(σ_0 = x | 𝓕_{<0}))`;
  `specificRelativeEntropy_markovPotential_reindex_eq_integral_sum_mul_log_div` and
  `specificRelativeEntropy_markovPotential_reindex_eq_lintegral_klDiv`: the second display,
  `𝓀(μ|Φ) = ∫ 𝓗(μ(σ_0 = · | 𝓕_{<0})(ω) | Q(ω_{-1}, ·)) μ(dω)`, with the relative entropy of two
  probability vectors written as `∑_x p_x log (p_x / q_x)` and as Mathlib's `klDiv` of the
  measures with these densities with respect to counting measure. In particular `𝓀(μ|Φ)` is a
  finite real for every `μ ∈ 𝓟_Θ`.
* `specificRelativeEntropy_markovPotential_reindex_eq_zero_iff`: the variational principle
  `𝓀(μ|Φ) = 0 ↔ μ = μ_Q` on `𝓟_Θ`, from Theorem (15.39) and `𝒢(Φ) = {μ_Q}`;
  `specificRelativeEntropy_markovPotential_reindex_eq_zero_iff_condExp`: Georgii's direct proof,
  `𝓀(μ|Φ) = 0 ↔ μ(σ_0 = x | 𝓕_{<0}) = Q(σ_{-1}, x)` a.s. for all `x` (Proposition (15.5));
  `condExp_ae_eq_iff_eq_stationaryChain_map`: hence, on `𝓟_Θ`, the latter condition holds if and
  only if `μ = μ_Q` ("since `μ` is shift-invariant, the latter condition just means `μ = μ_Q`").
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Topology
open InformationTheory Real
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

/-! ### The interval `[m, n] ⊆ ℤ^1` is the interval `[m(), n()] ⊆ ℤ` -/

/-- Along `ℤ^1 ≃ ℤ`, the box `[m, n]` of `ℤ^1` is the interval `[m (), n ()]` of `ℤ`. -/
lemma map_Icc_funUnique (m n : Unit → ℤ) :
    (Finset.Icc m n).map (Equiv.funUnique Unit ℤ).toEmbedding = Finset.Icc (m ()) (n ()) := by
  ext i
  simp only [Finset.mem_map_equiv, Finset.mem_Icc, Pi.le_def, Equiv.funUnique_symm_apply]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁ (), h₂ ()⟩, fun ⟨h₁, h₂⟩ ↦ ⟨fun _ ↦ h₁, fun _ ↦ h₂⟩⟩

/-- The cardinality of the box `[0, N] ⊆ ℤ^1` is `N + 1`. -/
lemma card_Icc_zero_funUnique (N : ℕ) :
    #(Finset.Icc (0 : Unit → ℤ) fun _ ↦ (N : ℤ)) = N + 1 := by
  rw [← Finset.card_map (Equiv.funUnique Unit ℤ).toEmbedding, map_Icc_funUnique, Int.card_Icc]
  simp

/-! ### The pressure (Georgii: `P(Φ) = -log Q(a, a)` for the gas transform) -/

variable (P : Matrix E E ℝ)

/-- The finite-volume pressure of the reindexed Markov potential on the box `[0, N] ⊆ ℤ^1` with
the constant boundary condition `a`: `log Z_{[0,N]}(a) = -(N+1) log |E| + log Q^{N+2}(a, a)`
(Georgii: `γ_{[1,n]}(σ_{[1,n]} ≡ a | ω^a) = Q(a,a)^{n+1}/Q^{n+1}(a,a)`). -/
lemma logZ_markovPotential_reindex_Icc (hpos : ∀ x y, 0 < P x y) (N : ℕ) (a : E) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).logZ (uniformOn Set.univ)
        (Finset.Icc (0 : Unit → ℤ) fun _ ↦ (N : ℤ)) (fun _ ↦ a)
      = -((N : ℝ) + 1) * log (Fintype.card E) + log ((P ^ (N + 2)) a a) := by
  rw [Potential.logZ, Potential.premodifierZ_boltzmannFactor_reindex, Equiv.symm_symm,
    map_Icc_funUnique]
  have hb : (N : ℤ) = (0 : Unit → ℤ) () + (N : ℕ) := by simp
  have hconst : (MeasurableEquiv.arrowCongr' (Equiv.funUnique Unit ℤ).symm
      (MeasurableEquiv.refl E)).symm (fun _ : Unit → ℤ ↦ a) = fun _ : ℤ ↦ a := rfl
  rw [hconst, premodifierZ_Icc hpos hb]
  have hcard : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hpow : 0 < (P ^ (N + 2)) a a := pow_apply_pos hpos (N + 1) a a
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hpow.le, log_mul (by positivity) hpow.ne', log_pow, log_inv]
  push_cast
  ring

/-- **The pressure of a positive transfer matrix is the logarithm of its Perron root.** For any
positive matrix `Q` on the finite set `E` (not necessarily stochastic), the pressure of the
reindexed nearest-neighbour potential `Φ = -log Q` with respect to the uniform a priori measure
is `P(Φ) = log r_Q - log |E|`, with `r_Q` the Perron root of `Q`; with respect to counting
measure it is `log r_Q`. Georgii's argument for (15.40): along the boxes `[0, N]` with the
constant boundary condition `a`, `log Z_{[0,N]}(a) = -(N+1) log |E| + log Q^{N+2}(a, a)`, and
`Q^{N+2}(a, a) = r_Q^{N+2} P^{N+2}(a, a)` for the stochastic matrix `P` of `Q`
(`Matrix.pow_apply_self_eq_perronRoot_pow_mul`), whose diagonal entries tend to the positive
stationary probability `α_P(a)` (Doeblin, Theorem (3.A3)). -/
theorem pressure_markovPotential_reindex_eq_log_perronRoot (hpos : ∀ x y, 0 < P x y) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).pressure (uniformOn Set.univ)
      = log (Matrix.perronRoot P hpos) - log (Fintype.card E) := by
  obtain ⟨a⟩ := ‹Nonempty E›
  set S := Matrix.perronStochastic P hpos with hS
  have hSpos : ∀ x y, 0 < S x y := Matrix.perronStochastic_pos P hpos
  have hSst : S ∈ Matrix.rowStochastic ℝ E := Matrix.perronStochastic_mem_rowStochastic P hpos
  have hr : 0 < Matrix.perronRoot P hpos := Matrix.perronRoot_pos P hpos
  obtain ⟨α, hα, hαS⟩ := Matrix.exists_stationary S hSst hSpos
  have hΦ := isShiftInvariant_markovPotential_reindex P
  have hlim := Potential.tendsto_logZ_div_card_pressure (uniformOn (Set.univ : Set E)) hΦ
    (m := fun _ : ℕ ↦ (0 : Unit → ℤ)) (n := fun N : ℕ ↦ fun _ : Unit ↦ (N : ℤ))
    (Potential.tendsto_sub_atTop_cube) (fun _ _ ↦ a)
  refine tendsto_nhds_unique hlim ?_
  have heq : (fun N : ℕ ↦ ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).logZ
        (uniformOn Set.univ) (Finset.Icc (0 : Unit → ℤ) fun _ ↦ (N : ℤ)) (fun _ ↦ a)
        / #(Finset.Icc (0 : Unit → ℤ) fun _ ↦ (N : ℤ)))
      = fun N : ℕ ↦ log (Matrix.perronRoot P hpos) - log (Fintype.card E)
          + (log (Matrix.perronRoot P hpos) + log ((S ^ (N + 2)) a a)) / ((N : ℝ) + 1) := by
    funext N
    rw [logZ_markovPotential_reindex_Icc P hpos, card_Icc_zero_funUnique,
      Matrix.pow_apply_self_eq_perronRoot_pow_mul P hpos, log_mul (pow_pos hr _).ne'
        (pow_apply_pos hSpos (N + 1) a a).ne', log_pow]
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [heq]
  have hαa : 0 < α a := Matrix.pos_of_vecMul_eq_self S hSpos hα hαS a
  have h1 : Tendsto (fun N : ℕ ↦ log (Matrix.perronRoot P hpos) + log ((S ^ (N + 2)) a a)) atTop
      (𝓝 (log (Matrix.perronRoot P hpos) + log (α a))) :=
    tendsto_const_nhds.add
      (((Matrix.tendsto_pow_apply S hSst hSpos hα hαS a a).comp (tendsto_add_atTop_nat 2)).log
        hαa.ne')
  have h2 : Tendsto (fun N : ℕ ↦ (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h3 : Tendsto (fun N : ℕ ↦ (log (Matrix.perronRoot P hpos) + log ((S ^ (N + 2)) a a))
      / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have := h1.mul h2
    rw [mul_zero] at this
    exact this.congr fun N ↦ mul_one_div _ _
  simpa using
    (tendsto_const_nhds (x := log (Matrix.perronRoot P hpos) - log (Fintype.card E))).add h3

/-- **Georgii (15.40), the pressure.** For a positive stochastic matrix `Q` the pressure of the
reindexed Markov potential `Φ = -log Q` with respect to the uniform a priori measure is
`P(Φ) = -log |E|`: with respect to counting measure it is `0 = log 1`, `log` of the Perron root
of the stochastic matrix `Q` (`pressure_markovPotential_reindex_eq_log_perronRoot`,
`Matrix.perronRoot_eq_one_of_mem_rowStochastic`). Georgii's `P(Φ^gas) = -log Q(a, a)` is this
value for the gas transform of `Φ` with vacuum `a`, whose bonds are `Φ_{i-1,i} + log Q(a, a)`. -/
theorem pressure_markovPotential_reindex (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).pressure (uniformOn Set.univ)
      = -log (Fintype.card E) := by
  rw [pressure_markovPotential_reindex_eq_log_perronRoot P hpos,
    Matrix.perronRoot_eq_one_of_mem_rowStochastic P hpos hP, log_one, zero_sub]

/-! ### Georgii's intermediate displays on `ℤ`: the vacuum block and the Hamiltonian -/

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The path weight of the constant configuration `ω^c` along `[a, b]` is `Q(c, c)^{b - a}`. -/
lemma pathWeight_const (a b : ℤ) (c : E) :
    pathWeight P a b (fun _ ↦ c) = P c c ^ (b - a).toNat := by
  rw [pathWeight, Finset.prod_const, Int.card_Ico]

/-- **Georgii (15.40), the vacuum block** (notation (10.1)): for `b = a + n`,
`γ_{[a,b]}(σ_{[a,b]} ≡ c | ω^c) = Q(c, c)^{n+2} / Q^{n+2}(c, c)`; Georgii's
`γ_{[1,n]}(σ_{[1,n]} ≡ a | ω^a) = Q(a,a)^{n+1}/Q^{n+1}(a,a)`. -/
lemma markovSpecification_Icc_apply_cyl_const (hpos : ∀ x y, 0 < P x y) {n : ℕ} {a b : ℤ}
    (hb : b = a + n) (c : E) :
    markovSpecification P (Finset.Icc a b) (fun _ ↦ c) (cyl (Finset.Icc a b) fun _ ↦ c)
      = ENNReal.ofReal (P c c ^ (n + 2) / (P ^ (n + 2)) c c) := by
  rw [markovSpecification_Icc_apply_cyl hpos hb _ _ (fun _ _ ↦ rfl), pathWeight_const,
    show b + 1 - (a - 1) = ((n + 2 : ℕ) : ℤ) by push_cast; omega, Int.toNat_natCast]

/-- **Georgii (15.40), the first line of the pressure display.** Under `γ_{[0,N]}(· | ω^a)` the
probability that the block `[0, N]` is in the vacuum state `a` decays exponentially at rate
`-log Q(a, a)`: `-lim_N (N+1)⁻¹ log γ_{[0,N]}(σ_{[0,N]} ≡ a | ω^a) = -log Q(a, a)`, because
`γ_{[0,N]}(σ_{[0,N]} ≡ a | ω^a) = Q(a,a)^{N+2}/Q^{N+2}(a,a)` and `Q^{N+2}(a, a)` tends to the
positive stationary probability `α_Q(a)` (Doeblin, Theorem (3.A3)). For the gas transform `Φ^a`
of `Φ` with vacuum `a` (Theorem (2.35)(b)) one has `γ_Λ(σ_Λ ≡ a | ω^a) = 1/Z_Λ(ω^a)` with respect
to counting measure, so this limit is Georgii's `P(Φ^a) = -log Q(a, a)`. -/
theorem tendsto_neg_log_markovSpecification_Icc_apply_cyl_const_div
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) (a : E) :
    Tendsto (fun N : ℕ ↦ -(log (markovSpecification P (Finset.Icc (0 : ℤ) N) (fun _ ↦ a)
        (cyl (Finset.Icc (0 : ℤ) N) fun _ ↦ a)).toReal / ((N : ℝ) + 1)))
      atTop (𝓝 (-log (P a a))) := by
  obtain ⟨α, hα, hαP⟩ := Matrix.exists_stationary P hP hpos
  have hαa : 0 < α a := Matrix.pos_of_vecMul_eq_self P hpos hα hαP a
  have heq : (fun N : ℕ ↦ -(log (markovSpecification P (Finset.Icc (0 : ℤ) N) (fun _ ↦ a)
        (cyl (Finset.Icc (0 : ℤ) N) fun _ ↦ a)).toReal / ((N : ℝ) + 1)))
      = fun N : ℕ ↦ -log (P a a) + (log ((P ^ (N + 2)) a a) - log (P a a)) / ((N : ℝ) + 1) := by
    funext N
    have hpow : 0 < (P ^ (N + 2)) a a := pow_apply_pos hpos (N + 1) a a
    rw [markovSpecification_Icc_apply_cyl_const P hpos (zero_add (N : ℤ)).symm a,
      ENNReal.toReal_ofReal (div_pos (pow_pos (hpos a a) _) hpow).le,
      log_div (pow_pos (hpos a a) _).ne' hpow.ne', log_pow]
    have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [heq]
  have h1 : Tendsto (fun N : ℕ ↦ log ((P ^ (N + 2)) a a) - log (P a a)) atTop
      (𝓝 (log (α a) - log (P a a))) :=
    (((Matrix.tendsto_pow_apply P hP hpos hα hαP a a).comp (tendsto_add_atTop_nat 2)).log
      hαa.ne').sub tendsto_const_nhds
  have h2 : Tendsto (fun N : ℕ ↦ (log ((P ^ (N + 2)) a a) - log (P a a)) / ((N : ℝ) + 1)) atTop
      (𝓝 0) := by
    have := h1.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at this
    exact this.congr fun N ↦ mul_one_div _ _
  simpa using (tendsto_const_nhds (x := -log (P a a))).add h2

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- **Georgii (15.40), the Hamiltonian display.** On the interval `[a, a + n]`, for every
configuration `ω`,
`H_{[a,a+n]}(ω) - H_{[a,a+n]}(ω^c) = log ∏_{j=a-1}^{a+n} Q(c, c) / Q(ω_j, ω_{j+1})`.
Georgii states this for the gas transform `Φ^c`, for which `H^{Φ^c}(ω^c) = 0` and the left side
is `H^{Φ^c}_{[1,n]}(ω)` whenever `ω ≡ c` off `[1, n]`. -/
lemma hamiltonian_Icc_sub_hamiltonian_const (hpos : ∀ x y, 0 < P x y) (a : ℤ) (n : ℕ) (c : E)
    (ω : ℤ → E) :
    (markovPotential P).hamiltonian (Finset.Icc a (a + n)) ω
        - (markovPotential P).hamiltonian (Finset.Icc a (a + n)) (fun _ ↦ c)
      = log (∏ j ∈ Finset.Ico (a - 1) (a + n + 1), P c c / P (ω j) (ω (j + 1))) := by
  rw [hamiltonian_Icc, hamiltonian_Icc, ← Finset.sum_sub_distrib,
    Real.log_prod fun j _ ↦ (div_pos (hpos c c) (hpos _ _)).ne']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [log_div (hpos c c).ne' (hpos _ _).ne']
  ring

/-! ### The specific energy
(Georgii: `⟨μ, Φ⟩ = μ(log Q(a,a)/Q(σ_{-1}, σ_0))` for the gas transform) -/

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The site `i ∈ ℤ` corresponds to the constant site `(i) ∈ ℤ^1`. -/
lemma funUnique_symm_apply_eq (i : ℤ) : (Equiv.funUnique Unit ℤ).symm i = fun _ ↦ i := rfl

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The energy density terms of the reindexed Markov potential vanish off the two bonds
`{-1, 0}` and `{0, 1}` containing the origin. -/
lemma siteEnergyTerms_markovPotential_reindex_of_ne (η : (Unit → ℤ) → E)
    {A : Finset (Unit → ℤ)} (h₁ : A ≠ {fun _ ↦ -1, 0}) (h₂ : A ≠ {0, fun _ ↦ 1}) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).siteEnergyTerms 0 η A = 0 := by
  by_cases h0 : (0 : Unit → ℤ) ∈ A
  · rw [Potential.siteEnergyTerms_of_mem h0, Potential.reindex_apply, Equiv.symm_symm]
    by_cases hpair : ∃ i : ℤ, A.map (Equiv.funUnique Unit ℤ).toEmbedding = {i, i + 1}
    · exfalso
      obtain ⟨i, hi⟩ := hpair
      have hA : A = ({i, i + 1} : Finset ℤ).map (Equiv.funUnique Unit ℤ).symm.toEmbedding := by
        rw [← hi, Finset.map_symm_map]
      have h0' : (0 : ℤ) ∈ ({i, i + 1} : Finset ℤ) := by
        rw [← hi, Finset.mem_map_equiv]
        exact h0
      rw [Finset.mem_insert, Finset.mem_singleton] at h0'
      rw [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding,
        funUnique_symm_apply_eq, funUnique_symm_apply_eq] at hA
      rcases h0' with h | h
      · subst h
        rw [zero_add] at hA
        exact h₂ hA
      · obtain rfl : i = -1 := by omega
        rw [show (-1 : ℤ) + 1 = 0 by norm_num] at hA
        exact h₁ hA
    · rw [markovPotential_of_not_pair P hpair, mul_zero]
  · exact Potential.siteEnergyTerms_of_not_mem h0 η

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- **The energy density of the reindexed Markov potential**, Georgii (15.22):
`f_Φ(η) = ½(-log Q(η_{-1}, η_0) - log Q(η_0, η_1))`, the two bonds at the origin each counted with
weight `|A|⁻¹ = ½`. -/
lemma siteEnergy_markovPotential_reindex (η : (Unit → ℤ) → E) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).siteEnergy 0 η
      = (-log (P (η fun _ ↦ -1) (η 0)) + -log (P (η 0) (η fun _ ↦ 1))) / 2 := by
  have hne : ({fun _ ↦ -1, 0} : Finset (Unit → ℤ)) ≠ {0, fun _ ↦ 1} := by
    intro h
    have : (fun _ : Unit ↦ (-1 : ℤ)) ∈ ({0, fun _ ↦ 1} : Finset (Unit → ℤ)) := by
      rw [← h]; exact Finset.mem_insert_self _ _
    rw [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h' | h' <;> exact absurd (congrFun h' ()) (by norm_num)
  have h₁ : (fun _ : Unit ↦ (-1 : ℤ)) ≠ 0 := fun h ↦ absurd (congrFun h ()) (by norm_num)
  have h₂ : (0 : Unit → ℤ) ≠ fun _ ↦ 1 := fun h ↦ absurd (congrFun h ()) (by norm_num)
  rw [Potential.siteEnergy, tsum_eq_sum (s := {{fun _ ↦ -1, 0}, {0, fun _ ↦ 1}}) (fun A hA ↦ by
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hA
      exact siteEnergyTerms_markovPotential_reindex_of_ne P η hA.1 hA.2),
    Finset.sum_pair hne, Potential.siteEnergyTerms_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_singleton_self _)), Potential.siteEnergyTerms_of_mem (Finset.mem_insert_self _ _),
    Finset.card_pair h₁, Finset.card_pair h₂, Potential.reindex_apply, Potential.reindex_apply,
    Equiv.symm_symm, Finset.map_insert, Finset.map_singleton, Finset.map_insert,
    Finset.map_singleton, Equiv.coe_toEmbedding, Equiv.funUnique_apply]
  beta_reduce
  have hm1 : markovPotential P {-1, 0} (η ∘ (Equiv.funUnique Unit ℤ).symm)
      = -log (P (η fun _ ↦ -1) (η 0)) := by
    have := markovPotential_pair P (-1) (η ∘ (Equiv.funUnique Unit ℤ).symm)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at this
    exact this
  have hm0 : markovPotential P {0, 1} (η ∘ (Equiv.funUnique Unit ℤ).symm)
      = -log (P (η 0) (η fun _ ↦ 1)) := by
    have := markovPotential_pair P 0 (η ∘ (Equiv.funUnique Unit ℤ).symm)
    rw [zero_add] at this
    exact this
  rw [Pi.zero_apply, hm1, hm0]
  push_cast
  ring

omit [DecidableEq E] [Nonempty E] in
/-- `η ↦ -log Q(η_i, η_j)` is bounded, hence integrable for every probability measure on the
configuration space. -/
lemma integrable_neg_log_apply_apply (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ]
    (i j : Unit → ℤ) : Integrable (fun η : (Unit → ℤ) → E ↦ -log (P (η i) (η j))) μ := by
  have hmeas : Measurable fun η : (Unit → ℤ) → E ↦ -log (P (η i) (η j)) :=
    Measurable.comp (g := fun p : E × E ↦ -log (P p.1 p.2))
      (f := fun η : (Unit → ℤ) → E ↦ (η i, η j)) (measurable_of_countable _)
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  refine Integrable.of_bound hmeas.aestronglyMeasurable (∑ x, ∑ y, |log (P x y)|)
    (.of_forall fun η ↦ ?_)
  rw [Real.norm_eq_abs, abs_neg]
  calc |log (P (η i) (η j))|
      ≤ ∑ y, |log (P (η i) y)| :=
        Finset.single_le_sum (f := fun y ↦ |log (P (η i) y)|) (fun _ _ ↦ abs_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ x, ∑ y, |log (P x y)| :=
        Finset.single_le_sum (f := fun x ↦ ∑ y, |log (P x y)|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)

omit [DecidableEq E] [Nonempty E] in
/-- **Georgii (15.40), the specific energy.** For `μ ∈ 𝓟_Θ` on `ℤ^1`, the specific energy of the
reindexed Markov potential is `⟨μ, Φ⟩ = μ(-log Q(σ_{-1}, σ_0))`. Georgii's
`⟨μ, Φ^gas⟩ = μ(log Q(a,a)/Q(σ_{-1}, σ_0))` is this value shifted by the constant `log Q(a, a)`
of the gas transform. -/
theorem specificEnergy_markovPotential_reindex {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificEnergy μ
      = ∫ η, -log (P (η fun _ ↦ -1) (η 0)) ∂μ := by
  obtain ⟨hprob, hshift⟩ := mem_invariantFields_shiftGroup.1 hμ
  rw [Potential.specificEnergy]
  simp_rw [Potential.energyDensity, siteEnergy_markovPotential_reindex]
  rw [integral_div, integral_add (integrable_neg_log_apply_apply P μ _ _)
    (integrable_neg_log_apply_apply P μ _ _)]
  have hT := (hshift (fun _ : Unit ↦ (-1 : ℤ))).integral_comp'
    (f := (shift E (fun _ : Unit ↦ (-1 : ℤ))).toMeasurableEquiv)
    (fun η ↦ -log (P (η fun _ ↦ -1) (η 0)))
  have hT' : ∀ η : (Unit → ℤ) → E, (shift E (fun _ : Unit ↦ (-1 : ℤ))).toMeasurableEquiv η
      = fun i ↦ η (i - fun _ ↦ -1) := fun η ↦ funext fun i ↦ shift_toFun_apply _ η i
  have e1 : ((fun _ : Unit ↦ (-1 : ℤ)) - fun _ ↦ -1) = 0 := by funext; simp
  have e2 : ((0 : Unit → ℤ) - fun _ ↦ -1) = fun _ ↦ 1 := by funext; simp
  simp only [hT', e1, e2] at hT
  rw [hT]
  ring

/-! ### The specific relative entropy (Georgii's first display for `𝓀(μ|Φ)`) -/

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Georgii's past `𝓕_{]-∞, 0[}` of the origin of `ℤ`, as the lexicographic past `V*(0)` of the
origin of `ℤ^1`: `{i : ℤ^1 | i () < 0}`. -/
lemma lexPast_zero_diff_singleton_funUnique :
    lexPast (0 : Unit → ℤ) \ {0} = {i : Unit → ℤ | i () < 0} := by
  rw [lexPast_diff_singleton]
  ext i
  exact Pi.Lex.lt_iff_of_unique

omit [Fintype E] [DecidableEq E] [Nonempty E] in
/-- The event `{σ_0 = x}` is measurable. -/
lemma measurableSet_apply_zero_eq (x : E) : MeasurableSet {ω : (Unit → ℤ) → E | ω 0 = x} :=
  (measurable_pi_apply 0 : Measurable fun ω : (Unit → ℤ) → E ↦ ω 0) (measurableSet_singleton x)

omit [DecidableEq E] [Nonempty E] in
/-- The conditional Shannon entropy integrand `∑_x μ(σ_0 = x | 𝓕_{<0}) log μ(σ_0 = x | 𝓕_{<0})`
is integrable. -/
lemma integrable_sum_condExp_mul_log (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    Integrable (fun ω ↦ ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
      * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω)) μ :=
  integrable_finsetSum _ fun x _ ↦
    integrable_condExp_indicator_one_mul_log (measurableSet_apply_zero_eq x)

/-- **Georgii (15.40), the first display for `𝓀(μ|Φ)`.** For `μ ∈ 𝓟_Θ` on `ℤ^1`,
`𝓀(μ|Φ) = μ(-log Q(σ_{-1}, σ_0) + ∑_x μ(σ_0 = x | 𝓕_{<0}) log μ(σ_0 = x | 𝓕_{<0}))`, where
`𝓕_{<0} = 𝓕_{]-∞,0[}` is the σ-algebra of the past of the origin
(`lexPast_zero_diff_singleton_funUnique`). This is `P(Φ) + ⟨μ, Φ⟩ - 𝓀(μ)` with the three
ingredients `pressure_markovPotential_reindex`, `specificEnergy_markovPotential_reindex` and
Georgii (15.19) (`specificEntropy_uniformOn_eq_neg_integral_sum_mul_log`); the normalisation
constants `∓ log |E|` of the uniform a priori measure cancel. In particular `𝓀(μ|Φ)` is finite. -/
theorem specificRelativeEntropy_markovPotential_reindex (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificRelativeEntropy
        (uniformOn Set.univ) μ
      = ((∫ ω, (-log (P (ω fun _ ↦ -1) (ω 0))
          + ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
              cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
            * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
              cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω)) ∂μ : ℝ)
          : EReal) := by
  have hprob : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  have h1519 := specificEntropy_uniformOn_eq_neg_integral_sum_mul_log hμ
  rw [Potential.specificRelativeEntropy, pressure_markovPotential_reindex P hP hpos,
    specificEnergy_markovPotential_reindex P hμ]
  -- `specificEntropy` is stated for `[DecidableEq ι]`, (15.19) for `[LinearOrder ι]`
  rw [show (instDecidableEqPUnit : DecidableEq Unit)
      = fun a b ↦ @LinearOrder.toDecidableEq Unit PUnit.instLinearOrder a b from
      Subsingleton.elim _ _, h1519, ← EReal.coe_sub, EReal.coe_eq_coe_iff,
    integral_add (integrable_neg_log_apply_apply P μ _ _) (integrable_sum_condExp_mul_log μ)]
  ring

/-! ### The specific relative entropy as a mean relative entropy (Georgii's second display) -/

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The site `-1 ∈ ℤ^1` lies in the past of the origin. -/
lemma neg_one_mem_lexPast_zero_diff_singleton :
    (fun _ : Unit ↦ (-1 : ℤ)) ∈ lexPast (0 : Unit → ℤ) \ {0} := by
  rw [lexPast_zero_diff_singleton_funUnique]
  show (-1 : ℤ) < 0
  norm_num

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `|log Q(y, x)| ≤ ∑_{y', x'} |log Q(y', x')|`, Georgii's bound `logBound Q` on the Markov
potential. -/
lemma norm_neg_log_apply_le (y x : E) : ‖-log (P y x)‖ ≤ logBound P := by
  rw [Real.norm_eq_abs, abs_neg, logBound]
  calc |log (P y x)|
      ≤ ∑ x', |log (P y x')| :=
        Finset.single_le_sum (f := fun x' ↦ |log (P y x')|) (fun _ _ ↦ abs_nonneg _)
          (Finset.mem_univ _)
    _ ≤ ∑ y', ∑ x', |log (P y' x')| :=
        Finset.single_le_sum (f := fun y' ↦ ∑ x', |log (P y' x')|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)

omit [DecidableEq E] [Nonempty E] in
/-- `ω ↦ -log Q(ω_{-1}, x)` is measurable with respect to the past `𝓕_{<0}` of the origin. -/
lemma stronglyMeasurable_neg_log_apply_neg_one (x : E) :
    StronglyMeasurable[cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]
      fun ω : (Unit → ℤ) → E ↦ -log (P (ω fun _ ↦ -1) x) :=
  ((measurable_of_countable fun y ↦ -log (P y x)).comp
    (measurable_cylinderEvent_apply (X := fun _ : Unit → ℤ ↦ E)
      neg_one_mem_lexPast_zero_diff_singleton)).stronglyMeasurable

omit [DecidableEq E] [Nonempty E] in
/-- **Conditioning `-log Q(σ_{-1}, σ_0)` on the past.** For a probability measure `μ`,
`μ(-log Q(σ_{-1}, σ_0)) = μ(∑_x μ(σ_0 = x | 𝓕_{<0}) (-log Q(σ_{-1}, x)))`: write
`-log Q(σ_{-1}, σ_0) = ∑_x 1_{σ_0 = x} (-log Q(σ_{-1}, x))`, condition on `𝓕_{<0}` and pull out
the `𝓕_{<0}`-measurable factor `-log Q(σ_{-1}, x)`. -/
lemma integral_neg_log_apply_apply_eq (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    ∫ ω, -log (P (ω fun _ ↦ -1) (ω 0)) ∂μ
      = ∫ ω, ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
          cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
        * -log (P (ω fun _ ↦ -1) x) ∂μ := by
  classical
  have hm : cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0}) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hpt : ∀ ω : (Unit → ℤ) → E, -log (P (ω fun _ ↦ -1) (ω 0))
      = ∑ x, ({ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ)) ω * -log (P (ω fun _ ↦ -1) x) := by
    intro ω
    rw [Finset.sum_eq_single (ω 0)]
    · simp
    · intro x _ hx
      rw [Set.indicator_of_notMem (fun h ↦ hx (Set.mem_ofPred_eq ▸ h).symm), zero_mul]
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  simp_rw [hpt]
  have hmeas : ∀ x : E, AEStronglyMeasurable (fun ω : (Unit → ℤ) → E ↦ -log (P (ω fun _ ↦ -1) x))
      μ := fun x ↦ ((stronglyMeasurable_neg_log_apply_neg_one P x).mono hm).aestronglyMeasurable
  have hbd : ∀ x : E, ∀ᵐ ω ∂μ, ‖-log (P (ω fun _ ↦ -1) x)‖ ≤ logBound P :=
    fun x ↦ .of_forall fun ω ↦ norm_neg_log_apply_le P _ x
  have hint : ∀ x : E, Integrable
      (fun ω ↦ ({ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ)) ω * -log (P (ω fun _ ↦ -1) x)) μ :=
    fun x ↦ ((integrable_const _).indicator (measurableSet_apply_zero_eq x)).mul_bdd (hmeas x)
      (hbd x)
  rw [integral_finsetSum _ fun x _ ↦ hint x,
    integral_finsetSum _ fun x _ ↦ integrable_condExp.mul_bdd (hmeas x) (hbd x)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← integral_condExp hm (f := fun ω ↦ ({ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ)) ω
    * -log (P (ω fun _ ↦ -1) x))]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_right
    (stronglyMeasurable_neg_log_apply_neg_one P x) (hint x)
    ((integrable_const _).indicator (measurableSet_apply_zero_eq x)))

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `p log p - p log q = p log (p / q)` for `q > 0` (both sides vanish when `p = 0`). -/
lemma mul_log_add_mul_neg_log_eq {p q : ℝ} (hq : 0 < q) :
    p * log p + p * -log q = p * log (p / q) := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [log_div hp hq.ne']
    ring

omit [DecidableEq E] [Nonempty E] in
/-- The integrand `∑_x μ(σ_0 = x | 𝓕_{<0}) (-log Q(σ_{-1}, x))` is integrable. -/
lemma integrable_sum_condExp_mul_neg_log (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    Integrable (fun ω ↦ ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
      * -log (P (ω fun _ ↦ -1) x)) μ :=
  integrable_finsetSum _ fun x _ ↦ integrable_condExp.mul_bdd
    (((stronglyMeasurable_neg_log_apply_neg_one P x).mono
      cylinderEvents_le_pi).aestronglyMeasurable)
    (.of_forall fun ω ↦ norm_neg_log_apply_le P (ω fun _ ↦ -1) x)

/-- **Georgii (15.40), the second display for `𝓀(μ|Φ)`.** For `μ ∈ 𝓟_Θ` on `ℤ^1`,
`𝓀(μ|Φ) = ∫ 𝓗(μ(σ_0 = · | 𝓕_{<0})(ω) | Q(ω_{-1}, ·)) μ(dω)`, the mean over `μ` of the relative
entropy `𝓗(p | q) = ∑_x p_x log (p_x / q_x)` (Georgii (15.7) on the finite set `E`) of the
conditional distribution of `σ_0` given the past with respect to the transition row
`Q(ω_{-1}, ·)`. From the first display, conditioning `-log Q(σ_{-1}, σ_0)` on `𝓕_{<0}`
(`integral_neg_log_apply_apply_eq`). -/
theorem specificRelativeEntropy_markovPotential_reindex_eq_integral_sum_mul_log_div
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificRelativeEntropy
        (uniformOn Set.univ) μ
      = ((∫ ω, ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
            cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
          * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
            cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
              / P (ω fun _ ↦ -1) x) ∂μ : ℝ) : EReal) := by
  have hprob : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  rw [specificRelativeEntropy_markovPotential_reindex P hP hpos hμ, EReal.coe_eq_coe_iff,
    integral_add (integrable_neg_log_apply_apply P μ _ _) (integrable_sum_condExp_mul_log μ),
    integral_neg_log_apply_apply_eq P μ, ← integral_add (integrable_sum_condExp_mul_neg_log P μ)
      (integrable_sum_condExp_mul_log μ)]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [add_comm, mul_log_add_mul_neg_log_eq (hpos _ _)]

/-! ### The variational principle `𝓀(μ|Φ) = 0 ↔ μ = μ_Q` -/

/-- **Georgii (15.40), the variational principle for `μ_Q`.** For `μ ∈ 𝓟_Θ` on `ℤ^1`,
`𝓀(μ|Φ) = 0` if and only if `μ` is the (reindexed) stationary chain `μ_Q`. This is Theorem
(15.39) combined with `𝒢(Φ) = {μ_Q}` (Theorem (3.5), `gibbsMeasure_reindex_eq_singleton`), through
the general mechanism `specificRelativeEntropy_eq_zero_iff_eq_of_G_eq_singleton`. -/
theorem specificRelativeEntropy_markovPotential_reindex_eq_zero_iff
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificRelativeEntropy
        (uniformOn Set.univ) μ = 0
      ↔ μ = (stationaryChain P hP hpos).map
          (MeasurableEquiv.arrowCongr' (Equiv.funUnique Unit ℤ).symm (MeasurableEquiv.refl E)) :=
  have : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  Potential.specificRelativeEntropy_eq_zero_iff_eq_of_G_eq_singleton _
    (isShiftInvariant_markovPotential_reindex P) hμ (gibbsMeasure_reindex_eq_singleton P hP hpos)

omit [DecidableEq E] [Nonempty E] in
/-- The conditional probabilities `μ(σ_0 = x | 𝓕_{<0})`, `x ∈ E`, sum to `1` almost surely. -/
lemma ae_sum_condExp_eq_one (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂μ, ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
      cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω = 1 := by
  classical
  have hm : cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0}) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hpt : ∑ x, ({ω : (Unit → ℤ) → E | ω 0 = x}.indicator fun _ ↦ (1 : ℝ))
      = fun _ ↦ (1 : ℝ) := by
    funext ω
    rw [Finset.sum_apply, Finset.sum_eq_single (ω 0)]
    · simp
    · intro x _ hx
      exact Set.indicator_of_notMem (fun h ↦ hx (Set.mem_ofPred_eq ▸ h).symm) _
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  have h := condExp_finsetSum (μ := μ) (s := Finset.univ)
    (f := fun x ↦ {ω : (Unit → ℤ) → E | ω 0 = x}.indicator fun _ ↦ (1 : ℝ))
    (fun x _ ↦ (integrable_const _).indicator (measurableSet_apply_zero_eq x))
    (cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0}))
  rw [hpt, condExp_const hm] at h
  filter_upwards [h] with ω hω
  rw [← Finset.sum_apply, ← hω]

omit [Nonempty E] in
/-- For a.e. `ω`, `μ(σ_0 = · | 𝓕_{<0})(ω)` is a nonnegative vector of the same total mass `1` as
the transition row `Q(ω_{-1}, ·)`. -/
lemma ae_condExp_nonneg_and_sum_eq_sum (hP : P ∈ Matrix.rowStochastic ℝ E)
    (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂μ, (∀ x, 0 ≤ (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω)
      ∧ ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
          cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
        = ∑ x, P (ω fun _ ↦ -1) x := by
  have h0 : ∀ᵐ ω ∂μ, ∀ x, 0 ≤ (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
      cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω :=
    ae_all_iff.2 fun x ↦ condExp_indicator_one_nonneg (μ := μ) (m := _) _
  filter_upwards [h0, ae_sum_condExp_eq_one μ] with ω h0 h1
  exact ⟨h0, by rw [h1, Matrix.sum_row_of_mem_rowStochastic hP]⟩

omit [Nonempty E] in
/-- The relative entropy integrand `𝓗(μ(σ_0 = · | 𝓕_{<0}) | Q(σ_{-1}, ·))` is nonnegative
almost surely (Gibbs' inequality). -/
lemma ae_nonneg_sum_condExp_mul_log_div (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    0 ≤ᵐ[μ] fun ω ↦ ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
      * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω / P (ω fun _ ↦ -1) x) := by
  filter_upwards [ae_condExp_nonneg_and_sum_eq_sum P hP μ] with ω hω
  exact InformationTheory.sum_mul_log_div_nonneg (fun x _ ↦ hω.1 x) (fun x _ ↦ hpos _ _) hω.2

omit [DecidableEq E] [Nonempty E] in
/-- The relative entropy integrand `𝓗(μ(σ_0 = · | 𝓕_{<0}) | Q(σ_{-1}, ·))` is integrable. -/
lemma integrable_sum_condExp_mul_log_div (hpos : ∀ x y, 0 < P x y)
    (μ : Measure ((Unit → ℤ) → E)) [IsProbabilityMeasure μ] :
    Integrable (fun ω ↦ ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω
      * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω / P (ω fun _ ↦ -1) x))
      μ := by
  refine ((integrable_sum_condExp_mul_neg_log P μ).add (integrable_sum_condExp_mul_log μ)).congr
    (.of_forall fun ω ↦ ?_)
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ by rw [add_comm, mul_log_add_mul_neg_log_eq (hpos _ _)]

/-- **Georgii (15.40), the second display for `𝓀(μ|Φ)`, with Mathlib's relative entropy.** For
`μ ∈ 𝓟_Θ` on `ℤ^1`, `𝓀(μ|Φ) = ∫ 𝓗(μ(σ_0 = · | 𝓕_{<0})(ω) | Q(ω_{-1}, ·)) μ(dω)`, where
`μ(σ_0 = · | 𝓕_{<0})(ω)` is the probability measure on `E` with density
`x ↦ μ(σ_0 = x | 𝓕_{<0})(ω)` with respect to counting measure, `Q(ω_{-1}, ·)` is the row
`ω_{-1}` of the transition kernel `Kernel.ofMatrix Q`, and `𝓗(· | ·) = klDiv` is the relative
entropy of Georgii (15.1). -/
theorem specificRelativeEntropy_markovPotential_reindex_eq_lintegral_klDiv
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificRelativeEntropy
        (uniformOn Set.univ) μ
      = ((∫⁻ ω, klDiv (Measure.count.withDensity fun x ↦ ENNReal.ofReal
            ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
              cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]) ω))
          (Kernel.ofMatrix (fun x y ↦ ENNReal.ofReal (P x y)) (ω fun _ ↦ -1)) ∂μ : ℝ≥0∞)
          : EReal) := by
  have hprob : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  rw [specificRelativeEntropy_markovPotential_reindex_eq_integral_sum_mul_log_div P hP hpos hμ,
    ← max_eq_left (integral_nonneg_of_ae (ae_nonneg_sum_condExp_mul_log_div P hP hpos μ)),
    ← EReal.coe_ennreal_ofReal, ofReal_integral_eq_lintegral_ofReal
      (integrable_sum_condExp_mul_log_div P hpos μ) (ae_nonneg_sum_condExp_mul_log_div P hP hpos μ)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [ae_condExp_nonneg_and_sum_eq_sum P hP μ] with ω hω
  rw [Kernel.ofMatrix_apply, InformationTheory.klDiv_count_withDensity_ofReal hω.1
    (fun x ↦ hpos _ x) hω.2]

/-- **Georgii (15.40), the direct proof of the variational principle, first half.** For
`μ ∈ 𝓟_Θ` on `ℤ^1`, `𝓀(μ|Φ) = 0` if and only if `μ(σ_0 = x | 𝓕_{<0}) = Q(σ_{-1}, x)` `μ`-a.s. for
every `x ∈ E`: by the second display `𝓀(μ|Φ)` is the mean of the relative entropy
`𝓗(μ(σ_0 = · | 𝓕_{<0}) | Q(σ_{-1}, ·)) ≥ 0`, which vanishes exactly when the two probability
vectors agree (Proposition (15.5), `InformationTheory.sum_mul_log_div_eq_zero_iff`). -/
theorem specificRelativeEntropy_markovPotential_reindex_eq_zero_iff_condExp
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).specificRelativeEntropy
        (uniformOn Set.univ) μ = 0
      ↔ ∀ x, μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
            cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]
          =ᵐ[μ] fun ω ↦ P (ω fun _ ↦ -1) x := by
  have hprob : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  rw [specificRelativeEntropy_markovPotential_reindex_eq_integral_sum_mul_log_div P hP hpos hμ,
    EReal.coe_eq_zero, integral_eq_zero_iff_of_nonneg_ae
      (ae_nonneg_sum_condExp_mul_log_div P hP hpos μ) (integrable_sum_condExp_mul_log_div P hpos μ)]
  simp only [Filter.EventuallyEq, ← ae_all_iff]
  refine eventually_congr ?_
  filter_upwards [ae_condExp_nonneg_and_sum_eq_sum P hP μ] with ω hω
  rw [Pi.zero_apply]
  exact (InformationTheory.sum_mul_log_div_eq_zero_iff (fun x _ ↦ hω.1 x) (fun x _ ↦ hpos _ _)
    hω.2).trans ⟨fun h x ↦ h x (Finset.mem_univ _), fun h x _ ↦ h x⟩

/-- **Georgii (15.40), the direct proof of the variational principle, second half** ("since `μ`
is shift-invariant, the latter condition just means that `μ = μ_Q`"): a shift-invariant random
field `μ ∈ 𝓟_Θ` on `ℤ^1` satisfies `μ(σ_0 = x | 𝓕_{<0}) = Q(σ_{-1}, x)` `μ`-a.s. for every `x`
if and only if it is the stationary chain `μ_Q`. Here this is read off from the two
characterisations of `𝓀(μ|Φ) = 0`, `specificRelativeEntropy_markovPotential_reindex_eq_zero_iff`
and `specificRelativeEntropy_markovPotential_reindex_eq_zero_iff_condExp`. -/
theorem condExp_ae_eq_iff_eq_stationaryChain_map (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) {μ : Measure ((Unit → ℤ) → E)}
    (hμ : μ ∈ invariantFields (shiftGroup (Unit → ℤ) E)) :
    (∀ x, μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : Unit → ℤ ↦ E) (lexPast 0 \ {0})]
      =ᵐ[μ] fun ω ↦ P (ω fun _ ↦ -1) x)
      ↔ μ = (stationaryChain P hP hpos).map
          (MeasurableEquiv.arrowCongr' (Equiv.funUnique Unit ℤ).symm (MeasurableEquiv.refl E)) := by
  rw [← specificRelativeEntropy_markovPotential_reindex_eq_zero_iff_condExp P hP hpos hμ,
    specificRelativeEntropy_markovPotential_reindex_eq_zero_iff P hP hpos hμ]

end MeasureTheory.GibbsMeasure.Markov

end
