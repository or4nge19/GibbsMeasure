/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.HeisenbergPeriodicModification
public import GibbsMeasure.Specification.HeisenbergSpecification

/-!
# Georgii §20.1: the fields `μ_n^Φ`, Lemma (20.6), and `𝒢₀(Φ)` for an `N`-vector model

`GibbsMeasure.Specification.InfraredBound` proves Georgii's tail estimate

`°γ_Λ^Φ(|σ_i|² ≥ t) ≤ b(a) e^{-a t}`

on the *torus*, and derives Lemma (20.6)(i)–(iii) from it for any probability measure on a
configuration space satisfying such a bound.  This file carries the bound across to `ℤ^d`, where
Georgii states (20.6): to his fields

`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_{0_{S∖Λ(n)}}`

and to the set `𝒢₀(Φ)` of their cluster points in the topology of local convergence.

## Main results

* `MeasureTheory.GibbsMeasure.heisenbergPeriodicField` — **Georgii's `°γ_{Λ(N)}^Φ × δ_ω`** of
  Example (5.20)(3) for a Heisenberg potential; `μ_n^Φ` is the case `ω = 0`.  By
  `heisenbergPeriodicGibbsSpec_latticeBox` it is the finite-volume Gibbs kernel of the periodic
  modification `Φ^n` in the cube, which is how Georgii introduces it in the proof of (20.7).
* `heisenbergPeriodicField_zero_tail_le` — **step (a) of the proof of (20.7)**: the torus tail
  estimate of the proof of (20.6) holds for `μ_n^Φ`, at *every* site of `ℤ^d` and uniformly in
  the cube.  Off the cube the spins of `μ_n^Φ` are `0`, and the estimate holds there because
  Georgii's `b(a) ≥ 1` (`one_le_expSqRatio`).
* `heisenbergGZero` — **Georgii's `𝒢₀(Φ)`** of §20.1: the cluster points of `(μ_n^Φ)_{n ≥ 1}`.
  `exists_forall_tail_le_of_mem_heisenbergGZero` is Georgii's "by continuity" step, transporting
  the tail estimate to them: the tail event is a local event and the bound a closed condition
  (`eval_le_of_mapClusterPt`).
* `exists_lemma_20_6_heisenbergPeriodicField` and `exists_lemma_20_6_heisenbergGZero` —
  **Lemma (20.6) as Georgii states it**, for every `μ ∈ {μ_n^Φ : n ≥ 1} ∪ 𝒢₀(Φ)`: for each
  `a > 0` there are `b₁(a), b₂(a), b₃(a) > 0` with (i), (ii) and (iii).  The passage from the
  tail estimate to the three assertions is `exists_lemma_20_6_of_tail` in
  `GibbsMeasure.Specification.InfraredBound`, where it is proved for an arbitrary probability
  measure with the tail bound.
* `measurePreserving_shift_of_mem_heisenbergGZero` — **the shift invariance of `𝒢₀(Φ)`**, the
  half of Georgii's Example (5.20)(3) used in (20.7): `𝒢₀(Φ) ⊆ 𝒫_Θ(Ω, 𝓕)`.
* `sum_abs_periodizedCoupling_mul_slowGrowth_le` — **Georgii's "`J_{Λ(n)}` is dominated using
  (20.4)"** in the proof of (20.7): `∑_{j ∈ Λ(N)} |J_{Λ(N)}(i-j)| α(j) ≤ ∑_k |J(i-k)| α(k)`,
  uniformly in the cube, because the representative of a torus site in `Λ(N)` is the shortest
  point of its fibre (`norm_le_norm_of_latticeToTorus_eq`).

## The rest of (20.7)

Georgii's Proposition (20.7) is `∅ ≠ 𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`.  Of its four steps, (a) the tail estimate
for `μ_n^Φ` and (d) the shift invariance of the cluster points are proved above, and the analytic
input of (b) — the uniform-in-`n` domination of `J_{Λ(n)}` by (20.4) — is
`sum_abs_periodizedCoupling_mul_slowGrowth_le`.

**(b) `𝒢₀(Φ) ≠ ∅` is proved** in `GibbsMeasure.Specification.HeisenbergExistence`
(`heisenbergGZero_nonempty`), together with the density bound
`μ_n^Φ(A ∩ Ω_t) ≤ c(Λ, t) λ^Λ(A_Λ)` uniform in the cube
(`heisenbergPeriodicField_inter_slowGrowthSet_le`) that feeds Theorem (4.12).  Georgii's `ρ_Λ^n`
is not constructed: the bound is read off the explicit density (17.24) by resampling the block
`Λ mod 2N` of the torus, and Theorem (4.12) is used in the form
`locallyEquicontinuous_of_eventually_measure_inter_le`, which takes that bound as its hypothesis.

**(c) `𝒢₀(Φ) ⊆ 𝒢(Φ) is proved** in `GibbsMeasure.Specification.HeisenbergGibbsInclusion`
(`heisenbergGZero_subset_heisenbergGibbsMeasures`), together with Georgii's statement
`∅ ≠ 𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)` (`heisenbergGZero_nonempty_and_subset`).  Georgii's
`μ_n(γ_Λ^n f) → μ(γ_Λ^Φ f)` goes through `‖(γ_Λ^n f - γ_Λ^Φ f) 1_{Ω_t}‖ → 0` (Proposition (4.19)
restricted to `Ω_t`).  The tree's (4.17), `mem_GP_of_mapClusterPt` in
`GibbsMeasure.Specification.Existence`, assumes the limit specification quasilocal, which `γ^Φ` of
(20.5) is not; Georgii's "a glance at the proof of (4.17)" is therefore carried out separately.
Its model-specific inputs are proved in `GibbsMeasure.Specification.HeisenbergExistence`:
`H_Λ^{Φ^n}` is the block energy of the torus
(`hamiltonian_heisenbergPeriodicPotential_eq_sub`), `Φ^n` is `λ`-admissible so that `γ^n` is a
genuine specification and `μ_n^Φ γ_Λ^n = μ_n^Φ`
(`isSigmaFiniteLambdaAdmissible_heisenbergPeriodicPotential`), and Georgii's estimate
`sup_{ω ∈ Ω_t} |H_Λ^{Φ^n - Φ}| ≤ δ_n ∑_{i∈Λ}[1 + |ζ_i|²]` holds with the explicit null sequence
`δ_n` of `tendsto_sum_couplingTail`
(`abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le`).

## Two general lemmas about the periodic continuation

`map_periodicJuxt_apply_of_cylinderEvents` and `measurePreserving_shift_map_periodicPullback` are
stated here for an **arbitrary** law `κ` on the torus.  They are the general forms of
`periodicGibbsField_apply_of_cylinderEvents` and
`measurePreserving_shift_periodicGibbsPeriodicField` of
`GibbsMeasure.Specification.PeriodicGibbsLimits`, which are the same statements for the
`C`-potential family only; those two should be re-derived from these, and are not, only because
that file is not touched here.

## Deviations from Georgii

* Georgii's `Λ(n) = ]-n, n]^d`; the cube here is `Potential.latticeBox d L = [-N, N)^d` with
  `N = L + 1`, a translate of his and the same fundamental domain of `2N ℤ^d`.  The index is `L`,
  not `N`, so that `latticeToTorus L` and the torus `(ℤ/2(L+1))^d` agree on the nose.
* Georgii's standing hypothesis `°Z_Λ^Φ < ∞` is not assumed: over an unbounded spin space it
  follows from (20.2) and (20.3) (`integrable_exp_heisenbergExponent`).
* The a priori measure `λ` is a finite non-zero measure, as in Georgii; it is *not* assumed to be
  a probability measure, and no normalisation of it is used.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The periodic continuation of an arbitrary law on the torus -/

section PeriodicTransfer

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-- **The boundary condition is invisible inside the cube.**  On an event of the cube `Λ(N)` the
law of the configuration which is the periodic continuation of `ζ` inside `Λ(N)` and `ω` outside
does not depend on `ω`: it is the law of the full periodic continuation.

This is the general form of `periodicGibbsField_apply_of_cylinderEvents`, which is the same
statement for the periodic Gibbs distribution of a `C`-potential. -/
theorem map_periodicJuxt_apply_of_cylinderEvents (L : ℕ)
    (κ : Measure ((Fin d → ZMod (2 * (L + 1))) → E)) (ω : (Fin d → ℤ) → E)
    {A : Set ((Fin d → ℤ) → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((periodicCube d L : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] A) :
    (κ.map (periodicJuxt E L ω)) A = (κ.map (periodicPullback L)) A := by
  have hpre : periodicJuxt E L ω ⁻¹' A = periodicPullback L ⁻¹' A := by
    ext ζ
    exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
      periodicJuxt_apply_of_mem ζ (by simpa using hi)
  rw [Measure.map_apply (measurable_periodicJuxt L ω) (cylinderEvents_le_pi _ hA),
    Measure.map_apply (measurable_periodicPullback (E := E) (d := d) (n := L))
      (cylinderEvents_le_pi _ hA), hpre]

/-- **The periodic continuation of a shift-invariant law on the torus is shift invariant.**  This
is the general form of `measurePreserving_shift_periodicGibbsPeriodicField`. -/
theorem measurePreserving_shift_map_periodicPullback {L : ℕ}
    {κ : Measure ((Fin d → ZMod (2 * (L + 1))) → E)} (a : Fin d → ℤ)
    (hκ : MeasurePreserving (shift E (latticeToTorus L a)).toFun κ κ) :
    MeasurePreserving (shift E a).toFun (κ.map (periodicPullback L))
      (κ.map (periodicPullback L)) := by
  refine ⟨(shift E a).measurable_toFun, ?_⟩
  rw [Measure.map_map (shift E a).measurable_toFun
    (measurable_periodicPullback (E := E) (d := d) (n := L))]
  have hcomp : (shift E a).toFun ∘ periodicPullback (E := E) (d := d) L
      = periodicPullback L ∘ (shift E (latticeToTorus L a)).toFun :=
    funext fun ζ ↦ (periodicPullback_shift a ζ).symm
  rw [hcomp, ← Measure.map_map (measurable_periodicPullback (E := E) (d := d) (n := L))
    (shift E (latticeToTorus L a)).measurable_toFun, hκ.map_eq]

end PeriodicTransfer

/-! ### Georgii's fields `μ_n^Φ` -/

section Fields

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

variable (J ν) in
/-- **Georgii's `°γ_{Λ(N)}^Φ × δ_ω`** (Example (5.20)(3), §20.1) for a Heisenberg potential: the
Gibbs distribution in the cube `Λ(N)` with periodic boundary condition, read as a random field on
`Ω = ((ℝ^n)^{ℤ^d})` by freezing the configuration outside `Λ(N)` to `ω`.  Georgii's

`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_{0_{S∖Λ(n)}}`

is the case `ω = 0`.  By `heisenbergPeriodicGibbsSpec_latticeBox` this is the finite-volume Gibbs
kernel `γ^n_{Λ(n)}(·|ω)` of the periodic modification `Φ^n`, which is Georgii's own description of
it in the proof of (20.7). -/
def heisenbergPeriodicField (L : ℕ) (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    Measure ((Fin d → ℤ) → (Fin n → ℝ)) :=
  (heisenbergPeriodicGibbsDist (L + 1) n J ν).map (periodicJuxt (Fin n → ℝ) L ω)

theorem heisenbergPeriodicField_apply (L : ℕ) (ω : (Fin d → ℤ) → (Fin n → ℝ))
    {A : Set ((Fin d → ℤ) → (Fin n → ℝ))} (hA : MeasurableSet A) :
    heisenbergPeriodicField J ν L ω A
      = heisenbergPeriodicGibbsDist (L + 1) n J ν (periodicJuxt (Fin n → ℝ) L ω ⁻¹' A) :=
  Measure.map_apply (measurable_periodicJuxt L ω) hA

theorem isProbabilityMeasure_heisenbergPeriodicField [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (L : ℕ)
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    IsProbabilityMeasure (heisenbergPeriodicField J ν L ω) := by
  have := isProbabilityMeasure_heisenbergPeriodicGibbsDist (N := L + 1) (d := d) (ν := ν) hν
    (integrable_exp_heisenbergExponent hexp hsum)
  exact Measure.isProbabilityMeasure_map (measurable_periodicJuxt L ω).aemeasurable

/-- Georgii's `μ_n^Φ` has all its spins outside the cube equal to zero. -/
theorem heisenbergPeriodicField_zero_apply_of_notMem (L : ℕ) {i : Fin d → ℤ}
    (hi : i ∉ periodicCube d L) {A : Set ((Fin d → ℤ) → (Fin n → ℝ))} (hA : MeasurableSet A)
    (hA0 : ∀ ω : (Fin d → ℤ) → (Fin n → ℝ), ω i = 0 → ω ∉ A) :
    heisenbergPeriodicField J ν L 0 A = 0 := by
  rw [heisenbergPeriodicField_apply L 0 hA]
  convert measure_empty (μ := heisenbergPeriodicGibbsDist (L + 1) n J ν)
  refine Set.eq_empty_iff_forall_notMem.2 fun ζ hζ ↦ ?_
  exact hA0 _ (periodicJuxt_apply_of_notMem ζ hi) hζ

end Fields

/-! ### Step (a) of Georgii's proof of (20.7): the tail estimate on `ℤ^d` -/

section TailTransfer

variable {n : ℕ} {ν : Measure (Fin n → ℝ)}

/-- **Georgii's `b(a) ≥ 1`.**  The constant `b(a) = (∫λ e^{(a+c)|x|²})/(∫λ e^{-c|x|²})` of the
proof of (20.6) is at least `1` for `a, c ≥ 0`: its numerator is at least `λ(E)` and its
denominator at most `λ(E)`.  This is what makes the tail estimate hold trivially at the sites
where the spin is deterministic. -/
theorem one_le_expSqRatio [IsFiniteMeasure ν] (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    1 ≤ (∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν) / (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) := by
  have hden_int : Integrable (fun x : Fin n → ℝ ↦ Real.exp (-(c * (x ⬝ᵥ x)))) ν := by
    have h := hexp (-c)
    simpa only [neg_mul] using h
  have hνpos : 0 < ν.real Set.univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_pos.2 hν).ne' (measure_ne_top _ _)
  have hden_le : (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) ≤ ν.real Set.univ := by
    have h : (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) ≤ ∫ _x : Fin n → ℝ, (1 : ℝ) ∂ν :=
      integral_mono hden_int (integrable_const 1) fun x ↦
        Real.exp_le_one_iff.2 (by nlinarith [Matrix.dotProduct_self_nonneg x])
    simpa using h
  have hnum_ge : ν.real Set.univ ≤ ∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν := by
    have h : (∫ _x : Fin n → ℝ, (1 : ℝ) ∂ν) ≤ ∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν :=
      integral_mono (integrable_const 1) (hexp (a + c)) fun x ↦
        Real.one_le_exp (by nlinarith [Matrix.dotProduct_self_nonneg x])
    simpa using h
  have hden_pos : 0 < ∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun x ↦ Real.exp_nonneg _) hden_int]
    have hsupp : Function.support (fun x : Fin n → ℝ ↦ Real.exp (-(c * (x ⬝ᵥ x)))) = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ (Real.exp_pos _).ne'
    rw [hsupp]
    exact Measure.measure_univ_pos.2 hν
  rw [le_div_iff₀ hden_pos]
  linarith

variable {d : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ}

/-- **Step (a) of Georgii's proof of (20.7).**  The tail estimate

`°γ_Λ^Φ(|σ_i|² ≥ t) ≤ b(a) e^{-a t}`

of the proof of Lemma (20.6), proved on the torus in
`MeasureTheory.GibbsMeasure.heisenbergPeriodicGibbsDist_tail_le`, holds for Georgii's field
`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_{0_{S∖Λ(n)}}` on `ℤ^d`, at **every** site of `ℤ^d`, with the same
constant and uniformly in the cube.  Inside the cube this is the torus estimate read through the
coupling map; outside it the spin of `μ_n^Φ` is deterministically `0`, and the estimate holds
there because `b(a) ≥ 1` (`one_le_expSqRatio`).

This is Georgii's "By continuity, we can conclude that `μ(|σ_i|² ≥ t) ≤ b(a) e^{-at}` … for
`μ ∈ {μ_n^Φ : n ≥ 1}`", which for the fields themselves is not a continuity argument at all. -/
theorem heisenbergPeriodicField_zero_tail_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {a : ℝ} (ha : 0 < a) (L : ℕ)
    (i : Fin (d + 1) → ℤ) (t : ℝ) :
    heisenbergPeriodicField J ν L 0 {ω | t ≤ ω i ⬝ᵥ ω i}
      ≤ ENNReal.ofReal
        ((∫ x, Real.exp ((a + (∑' m, |J m|) / 2) * (x ⬝ᵥ x)) ∂ν)
            / (∫ x, Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) ∂ν)
          * Real.exp (-(a * t))) := by
  classical
  set c : ℝ := (∑' m, |J m|) / 2 with hc
  have hc0 : 0 ≤ c := by
    have h : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
    rw [hc]; linarith
  set B : ℝ := (∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν)
      / (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) with hB
  have hB1 : 1 ≤ B := one_le_expSqRatio hν hexp ha.le hc0
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hint := integrable_exp_heisenbergExponent (N := L + 1) (d := d + 1) (J := J) hexp hsum
  have hprob := isProbabilityMeasure_heisenbergPeriodicField hν hexp hsum L
    (0 : (Fin (d + 1) → ℤ) → (Fin n → ℝ))
  have hAmeas : MeasurableSet {ω : (Fin (d + 1) → ℤ) → (Fin n → ℝ) | t ≤ ω i ⬝ᵥ ω i} :=
    measurableSet_le measurable_const ((measurable_pi_apply i).dotProduct (measurable_pi_apply i))
  rcases le_or_gt t 0 with ht | ht
  · -- `t ≤ 0`: the bound exceeds `1`, and every measure of a probability measure is at most `1`.
    have hexp1 : (1 : ℝ) ≤ Real.exp (-(a * t)) :=
      Real.one_le_exp (by nlinarith)
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    rw [measure_univ]
    exact ENNReal.one_le_ofReal.2 (by nlinarith)
  · by_cases hi : i ∈ periodicCube (d + 1) L
    · -- inside the cube: the torus estimate, read through `periodicJuxt`
      have hpre : periodicJuxt (Fin n → ℝ) L (0 : (Fin (d + 1) → ℤ) → (Fin n → ℝ)) ⁻¹'
            {ω | t ≤ ω i ⬝ᵥ ω i}
          = {ζ | t ≤ ζ (latticeToTorus L i) ⬝ᵥ ζ (latticeToTorus L i)} := by
        ext ζ
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, periodicJuxt_apply_of_mem ζ hi]
      have hprobT : IsProbabilityMeasure (heisenbergPeriodicGibbsDist (L + 1) n J ν) :=
        isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
      have htorus := heisenbergPeriodicGibbsDist_tail_le (N := L + 1) hν hexp hsum heven hnd hint
        ha t (latticeToTorus L i)
      rw [heisenbergPeriodicField_apply L _ hAmeas, hpre]
      refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
        (by positivity)).2 (le_trans htorus ?_)
      rw [← hB]
    · -- outside the cube: the spin vanishes and `t > 0`
      rw [heisenbergPeriodicField_zero_apply_of_notMem L hi hAmeas ?_]
      · exact zero_le
      · intro ω hω hmem
        rw [Set.mem_ofPred_eq, hω, zero_dotProduct] at hmem
        exact absurd hmem (not_le.2 ht)

/-- The one-site tail event `{|σ_i|² ≥ t}` is a local event: it reads the single spin at `i`. -/
theorem dotProduct_self_ge_mem_localEvents {S : Type*} (i : S) (t : ℝ) :
    {ω : S → (Fin n → ℝ) | t ≤ ω i ⬝ᵥ ω i} ∈ localEvents S (Fin n → ℝ) := by
  classical
  refine mem_localEvents_of_cylinderEvents {i} ?_
  have hmeas : Measurable fun ω : S → (Fin n → ℝ) ↦ (ω i ⬝ᵥ ω i) :=
    (measurable_pi_apply i).dotProduct (measurable_pi_apply i)
  have hdep : DependsOn (fun ω : S → (Fin n → ℝ) ↦ (ω i ⬝ᵥ ω i))
      (({i} : Finset S) : Set S) := fun _ _ h ↦ by simp only [h i (by simp)]
  exact (hmeas.cylinderEvents_of_dependsOn hdep) measurableSet_Ici

/-- **The uniform tail estimate for `μ_n^Φ`**, in the form Lemma (20.6) takes as input: for every
rate `a > 0` there is one constant, uniform in the cube, in the site, and in `t`. -/
theorem exists_forall_heisenbergPeriodicField_zero_tail_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {a : ℝ} (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ ∀ (L : ℕ) (i : Fin (d + 1) → ℤ) (t : ℝ),
      heisenbergPeriodicField J ν L 0 {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(a * t))) := by
  have hc0 : (0 : ℝ) ≤ (∑' m, |J m|) / 2 := by
    have h : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
    linarith
  exact ⟨_, lt_of_lt_of_le zero_lt_one (one_le_expSqRatio hν hexp ha.le hc0),
    fun L i t ↦ heisenbergPeriodicField_zero_tail_le hν hexp hsum heven hnd ha L i t⟩

/-- **Georgii, Lemma (20.6) for the fields `μ_n^Φ`.** -/
theorem exists_lemma_20_6_heisenbergPeriodicField [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (L : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ b₁ b₂ b₃ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧
      (∀ i : Fin (d + 1) → ℤ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (ω i ⬝ᵥ ω i)))
          ∂(heisenbergPeriodicField J ν L 0) ≤ ENNReal.ofReal b₁) ∧
      (∀ (i j : Fin (d + 1) → ℤ) (t : ℝ),
        ∫⁻ ω, Set.indicator {ω : (Fin (d + 1) → ℤ) → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
            (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω ∂(heisenbergPeriodicField J ν L 0)
          ≤ ENNReal.ofReal (b₂ * Real.exp (-(a * t)))) ∧
      (∀ t : ℝ, 1 ≤ t → heisenbergPeriodicField J ν L 0 (slowGrowthSet (d + 1) n t)ᶜ
          ≤ ENNReal.ofReal (b₃ * Real.exp (-(a * t ^ 2)))) := by
  have := isProbabilityMeasure_heisenbergPeriodicField hν hexp hsum L
    (0 : (Fin (d + 1) → ℤ) → (Fin n → ℝ))
  refine exists_lemma_20_6_of_tail (fun a' ha' ↦ ?_) ha
  obtain ⟨b, hb0, hb⟩ :=
    exists_forall_heisenbergPeriodicField_zero_tail_le hν hexp hsum heven hnd ha'
  exact ⟨b, hb0, fun i t ↦ hb L i t⟩

end TailTransfer

/-! ### Georgii's `𝒢₀(Φ)` -/

section GZero

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

variable (J ν) in
/-- **Georgii's `𝒢₀(Φ)`** of §20.1 (Example (5.20)(3)): the set of cluster points, in the topology
of local convergence, of the sequence of fields

`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_{0_{S∖Λ(n)}}`,

the Gibbs distributions in the cubes with periodic boundary condition, embedded in `ℤ^d` by
freezing the exterior spins to `0`.  Unlike Georgii's `𝒢₀` of §18.1 the boundary condition here
is *not* arbitrary: it is the zero configuration, which is what makes the tail estimate of (20.6)
available at the sites outside the cube. -/
def heisenbergGZero : Set (ProbabilityMeasure ((Fin d → ℤ) → (Fin n → ℝ))) :=
  {μ | ∃ μs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → (Fin n → ℝ)),
    (∀ L, (μs L : Measure ((Fin d → ℤ) → (Fin n → ℝ))) = heisenbergPeriodicField J ν L 0) ∧
    MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) (Fin n → ℝ))
      atTop fun L ↦ WithSetwiseTopology.ofMeasure (μs L)}

end GZero

section GZeroTail

variable {d n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **Georgii's "By continuity, we can conclude that `μ(|σ_i|² ≥ t) ≤ b(a) e^{-at}` … for
`μ ∈ 𝒢₀(Φ)`."**  The tail event is a local event and the bound is a closed condition, so it passes
to the cluster points (`eval_le_of_mapClusterPt`). -/
theorem exists_forall_tail_le_of_mem_heisenbergGZero [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {a : ℝ} (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ ∀ μ ∈ heisenbergGZero J ν, ∀ (i : Fin (d + 1) → ℤ) (t : ℝ),
      (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) {ω | t ≤ ω i ⬝ᵥ ω i}
        ≤ ENNReal.ofReal (b * Real.exp (-(a * t))) := by
  obtain ⟨b, hb0, hb⟩ :=
    exists_forall_heisenbergPeriodicField_zero_tail_le hν hexp hsum heven hnd ha
  refine ⟨b, hb0, fun μ hμ i t ↦ ?_⟩
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine eval_le_of_mapClusterPt (dotProduct_self_ge_mem_localEvents i t) hcp
    (Filter.Eventually.of_forall fun L ↦ ?_)
  rw [hμs L]
  exact hb L i t

/-- **Georgii, Lemma (20.6) for `𝒢₀(Φ)`.**  Together with
`exists_lemma_20_6_heisenbergPeriodicField` this is Lemma (20.6) as stated: the estimates hold for
all `μ ∈ {μ_n^Φ : n ≥ 1} ∪ 𝒢₀(Φ)`, with constants depending only on `a`. -/
theorem exists_lemma_20_6_heisenbergGZero [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {μ : ProbabilityMeasure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))}
    (hμ : μ ∈ heisenbergGZero J ν) {a : ℝ} (ha : 0 < a) :
    ∃ b₁ b₂ b₃ : ℝ, 0 < b₁ ∧ 0 < b₂ ∧ 0 < b₃ ∧
      (∀ i : Fin (d + 1) → ℤ, ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (ω i ⬝ᵥ ω i)))
          ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) ≤ ENNReal.ofReal b₁) ∧
      (∀ (i j : Fin (d + 1) → ℤ) (t : ℝ),
        ∫⁻ ω, Set.indicator {ω : (Fin (d + 1) → ℤ) → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
            (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω
            ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
          ≤ ENNReal.ofReal (b₂ * Real.exp (-(a * t)))) ∧
      (∀ t : ℝ, 1 ≤ t →
        (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) (slowGrowthSet (d + 1) n t)ᶜ
          ≤ ENNReal.ofReal (b₃ * Real.exp (-(a * t ^ 2)))) := by
  have := μ.2
  refine exists_lemma_20_6_of_tail (fun a' ha' ↦ ?_) ha
  obtain ⟨b, hb0, hb⟩ :=
    exists_forall_tail_le_of_mem_heisenbergGZero hν hexp hsum heven hnd ha'
  exact ⟨b, hb0, fun i t ↦ hb μ hμ i t⟩

end GZeroTail

/-! ### Shift invariance: the half of Example (5.20)(3) used in (20.7) -/

section ShiftInvariance

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **`𝒢₀(Φ) ⊆ 𝒫_Θ(Ω, 𝓕)`**, the shift-invariance half of Georgii's Example (5.20)(3), quoted in
the proof of (20.7) as "It is clear that `μ` is shift-invariant".

The periodic Gibbs distribution `°γ_{Λ(N)}^Φ` is invariant under the shifts of the *torus*
(`measurePreserving_shift_heisenbergPeriodicGibbsDist`), so its periodic continuation to `ℤ^d` is
exactly shift invariant (`measurePreserving_shift_map_periodicPullback`); the boundary condition
`0` is invisible on any fixed local event once the cube contains it and its shift
(`map_periodicJuxt_apply_of_cylinderEvents`), and invariance is a closed condition on the values
at the local events (`eq_of_mapClusterPt_of_eventually_eq`). -/
theorem measurePreserving_shift_of_mem_heisenbergGZero [IsFiniteMeasure ν]
    {μ : ProbabilityMeasure ((Fin d → ℤ) → (Fin n → ℝ))} (hμ : μ ∈ heisenbergGZero J ν)
    (a : Fin d → ℤ) :
    MeasurePreserving (shift (Fin n → ℝ) a).toFun
      (μ : Measure ((Fin d → ℤ) → (Fin n → ℝ))) μ := by
  classical
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine ⟨(shift (Fin n → ℝ) a).measurable_toFun, ?_⟩
  have hprob : IsProbabilityMeasure
      ((μ : Measure ((Fin d → ℤ) → (Fin n → ℝ))).map (shift (Fin n → ℝ) a).toFun) :=
    Measure.isProbabilityMeasure_map (shift (Fin n → ℝ) a).measurable_toFun.aemeasurable
  refine separatesOn_localEvents hprob inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  rw [Measure.map_apply (shift (Fin n → ℝ) a).measurable_toFun hAm]
  refine eq_of_mapClusterPt_of_eventually_eq hcp
    ((shift (Fin n → ℝ) a).preimage_mem_localEvents hA) hA ?_
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  set Λ' : Finset (Fin d → ℤ) :=
    Λ.preimage (shift (Fin n → ℝ) a).sites (shift (Fin n → ℝ) a).sites.injective.injOn with hΛ'
  have hshiftA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
      (Λ' : Set (Fin d → ℤ))] ((shift (Fin n → ℝ) a).toFun ⁻¹' A) := by
    rw [hΛ', Finset.coe_preimage]
    exact (shift (Fin n → ℝ) a).measurable_toFun_cylinderEvents (Λ : Set (Fin d → ℤ)) hΛ
  filter_upwards [Potential.tendsto_latticeBox_atTop.eventually
    (eventually_ge_atTop (Λ ∪ Λ'))] with L hL
  have hsub : Λ ∪ Λ' ⊆ periodicCube d L := hL
  have hAsub : (Λ : Set (Fin d → ℤ)) ⊆ (periodicCube d L : Set (Fin d → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_left hsub
  have hA'sub : (Λ' : Set (Fin d → ℤ)) ⊆ (periodicCube d L : Set (Fin d → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_right hsub
  rw [hμs L, heisenbergPeriodicField,
    map_periodicJuxt_apply_of_cylinderEvents L _ _ ((cylinderEvents_mono hA'sub) _ hshiftA),
    map_periodicJuxt_apply_of_cylinderEvents L _ _ ((cylinderEvents_mono hAsub) _ hΛ),
    ← Measure.map_apply (shift (Fin n → ℝ) a).measurable_toFun hAm,
    (measurePreserving_shift_map_periodicPullback a
      (measurePreserving_shift_heisenbergPeriodicGibbsDist (N := L + 1) (J := J) ν
        (latticeToTorus L a))).map_eq]

end ShiftInvariance

/-! ### Georgii: the coupling `J_{Λ(n)}` is dominated using (20.4) -/

section PeriodizedDomination

variable {D : ℕ} {J : (Fin D → ℤ) → ℝ}

/-- Sites of the cube `Λ(N) = [-N, N)^D`, `N = L + 1`, have sup norm at most `N`. -/
theorem norm_le_of_mem_latticeBox {L : ℕ} {j : Fin D → ℤ}
    (hj : j ∈ Potential.latticeBox D L) : ‖j‖ ≤ (L : ℝ) + 1 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun c ↦ ?_
  have h := Potential.mem_latticeBox.1 hj c
  rw [Finset.mem_Ico, Potential.intBoxLeft, Potential.intBoxLen] at h
  have habs : |j c| ≤ (L : ℤ) + 1 := abs_le.2 ⟨by omega, by omega⟩
  rw [Int.norm_eq_abs]
  exact_mod_cast habs

/-- **The fundamental domain consists of the shortest representatives.**  If `k` reduces to the
same torus site as a point `j` of the cube `Λ(N)`, then `‖j‖ ≤ ‖k‖`: either `k = j`, or `k`
differs from `j` by a non-zero multiple of the period `2N`, and then some coordinate of `k` has
modulus at least `2N - N = N ≥ ‖j‖`. -/
theorem norm_le_norm_of_latticeToTorus_eq {L : ℕ} {j k : Fin D → ℤ}
    (hj : j ∈ Potential.latticeBox D L) (h : latticeToTorus L k = latticeToTorus L j) :
    ‖j‖ ≤ ‖k‖ := by
  obtain ⟨r, hr⟩ := Potential.mem_piPeriods_const_iff.1 ((latticeToTorus_eq_iff k j).1 h)
  by_cases hr0 : r = 0
  · have hkj : k = j := by
      rw [hr0, smul_zero] at hr
      exact sub_eq_zero.1 hr
    rw [hkj]
  · obtain ⟨c, hc⟩ : ∃ c, r c ≠ 0 := by
      by_contra hcon
      exact hr0 (funext fun c ↦ by simpa using not_exists.1 hcon c)
    have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
    have hkc : k c - j c = 2 * ((L : ℤ) + 1) * r c := by
      have hcf := congrFun hr c
      simpa [Potential.intBoxLen] using hcf
    have hjc : |j c| ≤ (L : ℤ) + 1 := by
      have h1 := Potential.mem_latticeBox.1 hj c
      rw [Finset.mem_Ico, Potential.intBoxLeft, Potential.intBoxLen] at h1
      exact abs_le.2 ⟨by omega, by omega⟩
    have hrc : (1 : ℤ) ≤ |r c| := Int.one_le_abs hc
    have h1 : 2 * ((L : ℤ) + 1) ≤ 2 * ((L : ℤ) + 1) * |r c| := by nlinarith
    have h2 : |2 * ((L : ℤ) + 1) * r c| = 2 * ((L : ℤ) + 1) * |r c| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * ((L : ℤ) + 1))]
    have h3 : |2 * ((L : ℤ) + 1) * r c| - |j c| ≤ |k c| := by
      have hsub := abs_sub_abs_le_abs_sub (2 * ((L : ℤ) + 1) * r c) (-(j c))
      rw [abs_neg, show 2 * ((L : ℤ) + 1) * r c - -(j c) = k c by omega] at hsub
      exact hsub
    rw [h2] at h3
    have hbig : (L : ℤ) + 1 ≤ |k c| := by linarith
    calc ‖j‖ ≤ (L : ℝ) + 1 := norm_le_of_mem_latticeBox hj
      _ ≤ ‖k c‖ := by rw [Int.norm_eq_abs]; exact_mod_cast hbig
      _ ≤ ‖k‖ := norm_le_pi_norm k c

/-- **Georgii's "the coupling `J_{Λ(n)}` is dominated using (20.4)"** in the proof of (20.7).
The `α`-weighted row sums of the periodised coupling (17.25) over the cube are bounded by the
`α`-weighted row sums of `J` itself, **uniformly in the cube**:

`∑_{j ∈ Λ(N)} |J_{Λ(N)}(i - j)| α(j) ≤ ∑_{k ∈ ℤ^D} |J(i - k)| α(k) < ∞`.

The proof is the fibrewise decomposition of `ℤ^D` over the torus (`sum_tsum_ite_torus`) together
with `norm_le_norm_of_latticeToTorus_eq`: on the fibre of a torus site the representative in the
cube is the shortest, so `α` is smallest there.  This is the estimate in Georgii's "straightforward
calculation" of the proof of (20.7) which is not uniform in `n` for free, and the only place where
(20.4) — rather than (20.2) — is needed for the periodic modification `Φ^n`. -/
theorem sum_abs_periodizedCoupling_mul_slowGrowth_le (hJ : IsSlowlySummable J) (L : ℕ)
    (i : Fin D → ℤ) :
    ∑ v : Fin D → ZMod (2 * (L + 1)),
        |periodizedCoupling (L + 1) J (latticeToTorus L i - v)| * slowGrowth (torusToLattice L v)
      ≤ ∑' k : Fin D → ℤ, |J (i - k)| * slowGrowth k := by
  classical
  set g : (Fin D → ℤ) → ℝ := fun k ↦ |J (i - k)| * slowGrowth k with hg
  have hgsum : Summable g := hJ.summable_sub' i
  have hgnn : ∀ k, 0 ≤ g k := fun k ↦ mul_nonneg (abs_nonneg _) (slowGrowth_pos k).le
  have hfib : ∀ v : Fin D → ZMod (2 * (L + 1)), Summable fun k : Fin D → ℤ ↦
      (if latticeToTorus L k = v then g k else 0) := fun v ↦
    Summable.of_nonneg_of_le (fun k ↦ by by_cases h : latticeToTorus L k = v <;> simp [h, hgnn k])
      (fun k ↦ by by_cases h : latticeToTorus L k = v <;> simp [h, hgnn k]) hgsum
  -- `α` at the representative in the cube is the smallest on the fibre
  have hα : ∀ (v : Fin D → ZMod (2 * (L + 1))) (k : Fin D → ℤ), latticeToTorus L k = v →
      slowGrowth (torusToLattice L v) ≤ slowGrowth k := by
    intro v k hk
    refine slowGrowth_le_slowGrowth (norm_le_norm_of_latticeToTorus_eq (torusToLattice_mem v) ?_)
    rw [hk, latticeToTorus_torusToLattice]
  -- the pointwise estimate at one torus site
  have hstep : ∀ v : Fin D → ZMod (2 * (L + 1)),
      |periodizedCoupling (L + 1) J (latticeToTorus L i - v)| * slowGrowth (torusToLattice L v)
        ≤ ∑' k : Fin D → ℤ, (if latticeToTorus L k = v then g k else 0) := by
    intro v
    -- the periodised coupling as a sum over the fibre, reindexed by `k ↦ i - k`
    have hJre : periodizedCoupling (L + 1) J (latticeToTorus L i - v)
        = ∑' k : Fin D → ℤ, (if latticeToTorus L k = v then J (i - k) else 0) := by
      rw [periodizedCoupling_eq_tsum_ite,
        ← (Equiv.subLeft i).tsum_eq (fun m : Fin D → ℤ ↦
          if (fun c ↦ ((m c : ℤ) : ZMod (2 * (L + 1)))) = latticeToTorus L i - v then J m else 0)]
      refine tsum_congr fun k ↦ ?_
      have hb : (fun c ↦ (((i - k) c : ℤ) : ZMod (2 * (L + 1)))) = latticeToTorus L (i - k) := rfl
      rw [Equiv.subLeft_apply, hb, latticeToTorus_sub]
      exact if_congr sub_right_inj rfl rfl
    have habs : |periodizedCoupling (L + 1) J (latticeToTorus L i - v)|
        ≤ ∑' k : Fin D → ℤ, (if latticeToTorus L k = v then |J (i - k)| else 0) := by
      have hs : Summable fun k : Fin D → ℤ ↦
          ‖(if latticeToTorus L k = v then J (i - k) else 0)‖ := by
        refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_)
          (hJ.summable.abs.comp_injective (Equiv.subLeft i).injective)
        by_cases h : latticeToTorus L k = v <;> simp [h]
      rw [hJre, ← Real.norm_eq_abs]
      refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr fun k ↦ ?_))
      by_cases h : latticeToTorus L k = v <;> simp [h]
    have hnn : (0 : ℝ) ≤ slowGrowth (torusToLattice L v) := (slowGrowth_pos _).le
    calc |periodizedCoupling (L + 1) J (latticeToTorus L i - v)|
            * slowGrowth (torusToLattice L v)
        ≤ (∑' k : Fin D → ℤ, (if latticeToTorus L k = v then |J (i - k)| else 0))
            * slowGrowth (torusToLattice L v) := mul_le_mul_of_nonneg_right habs hnn
      _ = ∑' k : Fin D → ℤ,
            (if latticeToTorus L k = v then |J (i - k)| else 0) * slowGrowth (torusToLattice L v) :=
          (tsum_mul_right).symm
      _ ≤ ∑' k : Fin D → ℤ, (if latticeToTorus L k = v then g k else 0) := by
          refine Summable.tsum_le_tsum (fun k ↦ ?_) ?_ (hfib v)
          · by_cases h : latticeToTorus L k = v
            · simp only [h, ite_true, hg]
              exact mul_le_mul_of_nonneg_left (hα v k h) (abs_nonneg _)
            · simp [h]
          · refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) (hfib v)
            · by_cases h : latticeToTorus L k = v <;> simp [h, mul_nonneg (abs_nonneg _) hnn]
            · by_cases h : latticeToTorus L k = v
              · simp only [h, ite_true, hg]
                exact mul_le_mul_of_nonneg_left (hα v k h) (abs_nonneg _)
              · simp [h]
  refine le_trans (Finset.sum_le_sum fun v _ ↦ hstep v) (le_of_eq ?_)
  exact sum_tsum_ite_torus (L + 1) hgsum

end PeriodizedDomination

end MeasureTheory.GibbsMeasure

end

end
