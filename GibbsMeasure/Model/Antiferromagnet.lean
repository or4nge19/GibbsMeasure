/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.ExtremeDecomposition
public import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# Georgii, Example (14.16): the one-dimensional zero-temperature Ising antiferromagnet

Georgii, §14.2. Let `S = ℤ`, `E = {-1, 1}` (here `Bool`, `true ↔ 1`, `false ↔ -1`), `λ` counting
measure, and
```
p_j(x, y) = 1 if x ≠ y, 0 if x = y      (x, y ∈ E, j ∈ ℤ).
```
As in Example (10.3), these functions define a shift-invariant `λ`-specification `γ`: the zero
temperature limit of the Ising antiferromagnet without external field (§3.2, Case 2). Let
`ω^{+-}, ω^{-+}` be the two alternating configurations, `ω_i^{+-} = ω_{i+1}^{-+} = 1` if `i` is
even, `-1` if `i` is odd. Georgii states: `δ_{ω^{+-}}, δ_{ω^{-+}} ∈ ex 𝒢(γ)` and
`(δ_{ω^{+-}} + δ_{ω^{-+}})/2 ∈ ex 𝒢_Θ(γ)`; hence `ex 𝒢_Θ(γ) \ ex 𝒢(γ) ≠ ∅`.

## Why this is not built through `transferSpecification` or `lambdaSpecification`

The determining functions `p_j(x, y) = 1_{x ≠ y}` form a matrix with **zero diagonal entries**:
`Q(x, x) = 0`. This is not a `IsTransferMatrix` (Georgii (11.1) demands `Q` entrywise *positive*),
so `Model/BoundaryLaw.lean`'s `transferSpecification` does not apply. Nor does the general
`Specification.lambdaSpecification` builder: its admissibility hypothesis
`IsSigmaFiniteLambdaAdmissible` demands the partition function `Z_Λ(ω) ≠ 0` for *every* boundary
condition `ω`, and here `Z_{]i,k[}(ω)` is **zero** exactly when `ω_i, ω_k` have the wrong parity for
an alternating fill of length `k - i` — precisely the case Georgii's Example (10.3) singles out with
its `Z_{i,k} = 0` fallback branch `ρ_{]i,k[} = g_{i,k-1}`.

Reducing the two branches of (10.3) at this `p_j` shows they **coincide**: fixing the boundary
spin `ω_i` forces every interior spin by strict alternation, and (crucially) `g_{i,k-1}` does not
read `ω_k` at all, so the `Z = 0` fallback returns exactly the same Dirac mass as the `Z > 0`
branch would if the parity matched. Consequently `γ_Λ(\cdot \mid \omega)` is *deterministic*: it
is the Dirac mass at the configuration obtained from `ω` by continuing the alternation, on each
maximal run of `Λ`, from the boundary spin immediately to its left. This is the route taken
below: `γ` is built directly as a family of proper deterministic (`Kernel.deterministic`) Markov
kernels, along the pattern of `Specification.NoGibbsMeasure`'s `Example416.kernel`, and Example
(10.3)'s general (non-deterministic, case-split) construction is not re-derived.

## Contents

* Two general facts, about `Finset ℤ` and about alternating Boolean sequences: every finite
  `Λ : Finset ℤ` and `j : ℤ` have a greatest site `runStart Λ j ≤ j` outside `Λ` (a `sSup` in
  `ℤ`), and (`parityFlip`, `alternating_add`) a Boolean sequence with `σ (n + 1) = !σ n` for all
  `n` is determined by any one value via parity: `σ (n + d) = parityFlip d (σ n)`.
* `altFill Λ ω`: the deterministic resampling map of the specification, and its properties
  (`altFill_apply_of_notMem`, `altFill_of_alternating`, `altFill_altFill_of_subset`).
* `antiferromagnetSpecification`: the specification `γ` itself.
* `altPM`, `altMP`: the alternating configurations `ω^{+-}, ω^{-+}`;
  `dirac_altPM_mem_extremePoints_G`, `dirac_altMP_mem_extremePoints_G`:
  **`δ_{ω^{+-}}, δ_{ω^{-+}} ∈ ex 𝒢(γ)`**, via tail-triviality of Dirac measures
  (`mem_extremePoints_G_of_isTailTrivial`); no case analysis on the shape of `𝒢(γ)` is needed.
* `altMidpoint`: `(δ_{ω^{+-}} + δ_{ω^{-+}})/2`; `altMidpoint_mem_G` (convexity,
  `add_smul_mem_G`), `altMidpoint_notMem_extremePoints_G` (`altMidpoint` is an interior point of
  the segment between two *distinct* elements of `𝒢(γ)`), and
  `altMidpoint_mem_extremePoints_invariantG` — **`(δ_{ω^{+-}} + δ_{ω^{-+}})/2 ∈ ex 𝒢_Θ(γ)`** —
  proved by showing `altMidpoint` is trivial on the invariant σ-algebra of the **full** shift
  group (shift by `1` already swaps the two atoms of its support, so every invariant event has
  probability `0` or `1`), then invoking Georgii's Theorem (14.15)(a)
  (`ErgodicGibbs.mem_extremePoints_invariantG_iff_mem_trivialOn`).
* `georgii_14_16`: the packaged conclusion, `ex 𝒢_Θ(γ) \ ex 𝒢(γ) ≠ ∅`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Convex

noncomputable section

namespace MeasureTheory.GibbsMeasure.Antiferromagnet

/-! ## General: the nearest exterior site, and parity flips of an alternating sequence -/

section General

/-- Every finite `Λ : Finset ℤ` and `j : ℤ` admit some `i ≤ j` with `i ∉ Λ`: take `j` itself if
`Λ` is empty, or anything below `Λ.min' - 1` otherwise. -/
lemma exists_le_notMem (Λ : Finset ℤ) (j : ℤ) : ∃ i : ℤ, i ≤ j ∧ i ∉ Λ := by
  classical
  rcases Λ.eq_empty_or_nonempty with rfl | hne
  · exact ⟨j, le_refl j, by simp⟩
  · refine ⟨min j (Λ.min' hne - 1), min_le_left _ _, fun hmem ↦ ?_⟩
    have h1 : min j (Λ.min' hne - 1) ≤ Λ.min' hne - 1 := min_le_right _ _
    have h2 : Λ.min' hne ≤ min j (Λ.min' hne - 1) := Λ.min'_le _ hmem
    omega

/-- The nearest site to (and including) `j`, outside `Λ`, looking leftward: the greatest `i ≤ j`
with `i ∉ Λ`. If `j ∉ Λ` this is `j` itself; if `j ∈ Λ`, this is one step outside the maximal run
of `Λ` containing `j`, to its left. -/
def runStart (Λ : Finset ℤ) (j : ℤ) : ℤ := sSup {i : ℤ | i ≤ j ∧ i ∉ Λ}

lemma bddAbove_setOf_le_notMem (Λ : Finset ℤ) (j : ℤ) : BddAbove {i : ℤ | i ≤ j ∧ i ∉ Λ} :=
  ⟨j, fun _ hz ↦ hz.1⟩

lemma runStart_spec (Λ : Finset ℤ) (j : ℤ) :
    (runStart Λ j ≤ j ∧ runStart Λ j ∉ Λ) ∧
      ∀ z : ℤ, (z ≤ j ∧ z ∉ Λ) → z ≤ runStart Λ j :=
  ⟨Int.csSup_mem (exists_le_notMem Λ j) (bddAbove_setOf_le_notMem Λ j),
    fun _ hz ↦ le_csSup (bddAbove_setOf_le_notMem Λ j) hz⟩

lemma runStart_le (Λ : Finset ℤ) (j : ℤ) : runStart Λ j ≤ j := (runStart_spec Λ j).1.1

lemma runStart_notMem (Λ : Finset ℤ) (j : ℤ) : runStart Λ j ∉ Λ := (runStart_spec Λ j).1.2

lemma le_runStart_of_le_of_notMem {Λ : Finset ℤ} {j z : ℤ} (h1 : z ≤ j) (h2 : z ∉ Λ) :
    z ≤ runStart Λ j := (runStart_spec Λ j).2 z ⟨h1, h2⟩

lemma runStart_eq_self_of_notMem {Λ : Finset ℤ} {j : ℤ} (h : j ∉ Λ) : runStart Λ j = j :=
  le_antisymm (runStart_le Λ j) (le_runStart_of_le_of_notMem le_rfl h)

/-- `runStart` is idempotent under restriction to any window between it and its base point. -/
lemma runStart_eq_of_le_of_le {Λ : Finset ℤ} {j i : ℤ} (h1 : runStart Λ j ≤ i) (h2 : i ≤ j) :
    runStart Λ i = runStart Λ j := by
  have ha1 : runStart Λ j ≤ runStart Λ i := le_runStart_of_le_of_notMem h1 (runStart_notMem Λ j)
  have ha2 : runStart Λ i ≤ runStart Λ j :=
    le_runStart_of_le_of_notMem ((runStart_le Λ i).trans h2) (runStart_notMem Λ i)
  exact le_antisymm ha2 ha1

/-- Shrinking `Λ` moves `runStart` closer to `j` (or leaves it fixed). -/
lemma runStart_le_runStart_of_subset {Λ1 Λ2 : Finset ℤ} (h : Λ1 ⊆ Λ2) (j : ℤ) :
    runStart Λ2 j ≤ runStart Λ1 j :=
  le_runStart_of_le_of_notMem (runStart_le Λ2 j) fun hmem ↦ runStart_notMem Λ2 j (h hmem)

/-- Flip `b : Bool` according to the parity of `n : ℤ`. -/
def parityFlip (n : ℤ) (b : Bool) : Bool := if Even n then b else !b

@[simp] lemma parityFlip_zero (b : Bool) : parityFlip 0 b = b := by simp [parityFlip]

lemma parityFlip_one (b : Bool) : parityFlip 1 b = !b := by simp [parityFlip, Int.not_even_one]

lemma parityFlip_neg_one (b : Bool) : parityFlip (-1 : ℤ) b = !b := by
  simp [parityFlip, even_neg, Int.not_even_one]

lemma parityFlip_add (m n : ℤ) (b : Bool) :
    parityFlip (m + n) b = parityFlip m (parityFlip n b) := by
  unfold parityFlip
  by_cases hm : Even m <;> by_cases hn : Even n <;> simp [hm, hn, Int.even_add, Bool.not_not]

/-- A Boolean sequence alternating at every step is determined, at any point, by its value at any
other point together with the parity of their distance. -/
lemma alternating_add {σ : ℤ → Bool} (hσ : ∀ n : ℤ, σ (n + 1) = !σ n) (n d : ℤ) :
    σ (n + d) = parityFlip d (σ n) := by
  induction d using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hkey : n + ((k : ℤ) + 1) = (n + (k : ℤ)) + 1 := by ring
      have hpar : parityFlip ((k : ℤ) + 1) (σ n) = !(parityFlip (k : ℤ) (σ n)) := by
        rw [show (k : ℤ) + 1 = 1 + (k : ℤ) by ring, parityFlip_add, parityFlip_one]
      rw [hkey, hσ, ih, hpar]
  | pred k ih =>
      have hstep : σ ((n + (-(k : ℤ) - 1)) + 1) = !σ (n + (-(k : ℤ) - 1)) := hσ _
      have heq : (n + (-(k : ℤ) - 1)) + 1 = n + -(k : ℤ) := by ring
      rw [heq] at hstep
      have hval : σ (n + (-(k : ℤ) - 1)) = !σ (n + -(k : ℤ)) := by
        have h2 := congrArg Bool.not hstep
        simpa using h2.symm
      have hpar : parityFlip (-(k : ℤ) - 1) (σ n) = !(parityFlip (-(k : ℤ)) (σ n)) := by
        rw [show -(k : ℤ) - 1 = (-1) + (-(k : ℤ)) by ring, parityFlip_add, parityFlip_neg_one]
      rw [hval, ih, hpar]

end General

/-! ## The deterministic resampling map -/

/-- The deterministic resampling map of Georgii's Example (14.16): continue the alternation, on
each maximal run of `Λ`, from the boundary spin immediately to its left. -/
def altFill (Λ : Finset ℤ) (ω : ℤ → Bool) (j : ℤ) : Bool :=
  parityFlip (j - runStart Λ j) (ω (runStart Λ j))

lemma altFill_apply (Λ : Finset ℤ) (ω : ℤ → Bool) (j : ℤ) :
    altFill Λ ω j = parityFlip (j - runStart Λ j) (ω (runStart Λ j)) := rfl

/-- `altFill Λ ω` agrees with `ω` off `Λ`: this is what makes the kernel proper. -/
lemma altFill_apply_of_notMem {Λ : Finset ℤ} {j : ℤ} (hj : j ∉ Λ) (ω : ℤ → Bool) :
    altFill Λ ω j = ω j := by
  rw [altFill_apply, runStart_eq_self_of_notMem hj, sub_self, parityFlip_zero]

/-- A globally alternating configuration is a fixed point of every resampling. -/
lemma altFill_of_alternating {σ : ℤ → Bool} (hσ : ∀ n : ℤ, σ (n + 1) = !σ n) (Λ : Finset ℤ) :
    altFill Λ σ = σ := by
  funext j
  rw [altFill_apply]
  have h := alternating_add hσ (runStart Λ j) (j - runStart Λ j)
  rw [show runStart Λ j + (j - runStart Λ j) = j by ring] at h
  exact h.symm

/-- The resampling maps are consistent: resampling a subvolume of an already-resampled
configuration changes nothing. This is the content of Georgii's Example (10.3) that a Markovian
`λ`-modification is genuinely consistent, specialised to this deterministic case. -/
lemma altFill_altFill_of_subset {Λ1 Λ2 : Finset ℤ} (h : Λ1 ⊆ Λ2) (ω : ℤ → Bool) :
    altFill Λ1 (altFill Λ2 ω) = altFill Λ2 ω := by
  funext j
  have hle : runStart Λ2 j ≤ runStart Λ1 j := runStart_le_runStart_of_subset h j
  have hle' : runStart Λ1 j ≤ j := runStart_le Λ1 j
  have hrun : runStart Λ2 (runStart Λ1 j) = runStart Λ2 j := runStart_eq_of_le_of_le hle hle'
  rw [altFill_apply, altFill_apply, altFill_apply, hrun, ← parityFlip_add,
    show (j - runStart Λ1 j) + (runStart Λ1 j - runStart Λ2 j) = j - runStart Λ2 j by ring]

/-- Measurability, as a function of the boundary condition, of `altFill Λ`. -/
lemma measurable_altFill (Λ : Finset ℤ) :
    Measurable[cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)] (altFill Λ) := by
  let _ : MeasurableSpace (ℤ → Bool) := cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)
  refine measurable_pi_lambda _ fun j ↦ ?_
  have hj : runStart Λ j ∈ ((Λ : Set ℤ)ᶜ) := runStart_notMem Λ j
  have hproj : Measurable[cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)]
      (fun ω : ℤ → Bool ↦ ω (runStart Λ j)) := measurable_cylinderEvent_apply hj
  exact (measurable_of_finite (fun b : Bool ↦ parityFlip (j - runStart Λ j) b)).comp hproj

/-! ## The kernel and the specification -/

/-- The kernels of Georgii's Example (14.16): the Dirac mass at the alternation-continuing
resampling `altFill Λ`. -/
def antiferroKer (Λ : Finset ℤ) :
    Kernel[cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)] (ℤ → Bool) (ℤ → Bool) :=
  letI : MeasurableSpace (ℤ → Bool) := cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)
  Kernel.deterministic (altFill Λ) (measurable_altFill Λ)

lemma antiferroKer_apply (Λ : Finset ℤ) (x : ℤ → Bool) :
    antiferroKer Λ x = Measure.dirac (altFill Λ x) := by
  unfold antiferroKer
  rw [Kernel.deterministic_apply]

instance isMarkovKernel_antiferroKer (Λ : Finset ℤ) : IsMarkovKernel (antiferroKer Λ) := by
  unfold antiferroKer
  infer_instance

/-- A `cylinderEvents Λᶜ`-measurable indicator has the same value at configurations agreeing off
`Λ`; the elementary fact underlying properness of `antiferroKer`. -/
lemma indicator_eq_of_eqOn_compl {Λ : Finset ℤ} {B : Set (ℤ → Bool)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ Bool) ((Λ : Set ℤ)ᶜ)] B)
    {ω ω' : ℤ → Bool} (h : ∀ i, i ∉ Λ → ω' i = ω i) :
    B.indicator (1 : (ℤ → Bool) → ℝ≥0∞) ω' = B.indicator 1 ω := by
  have hiff : ω' ∈ B ↔ ω ∈ B :=
    mem_congr_of_measurableSet_cylinderEvents hB fun i hi ↦ h i (by simpa using hi)
  by_cases hmem : ω ∈ B
  · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
    rfl
  · rw [Set.indicator_of_notMem (fun hc ↦ hmem (hiff.1 hc)), Set.indicator_of_notMem hmem]

lemma isProper_antiferroKer (Λ : Finset ℤ) : (antiferroKer Λ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB x
  have hAB : MeasurableSet (A ∩ B) := hA.inter (cylinderEvents_le_pi _ hB)
  rw [antiferroKer_apply, Measure.dirac_apply' _ hAB, Measure.dirac_apply' _ hA,
    Set.inter_indicator_one, Pi.mul_apply,
    indicator_eq_of_eqOn_compl hB (fun i hi ↦ altFill_apply_of_notMem hi x), mul_comm]

lemma isConsistent_antiferroKer : IsConsistent antiferroKer := by
  intro Λ1 Λ2 h
  refine Kernel.ext fun x ↦ Measure.ext fun s hs ↦ ?_
  rw [Kernel.comp_apply' _ _ _ hs]
  change ∫⁻ b, antiferroKer Λ1 b s ∂(antiferroKer Λ2 x) = antiferroKer Λ2 x s
  have hmeas : Measurable fun b ↦ antiferroKer Λ1 b s :=
    ((antiferroKer Λ1).measurable_coe hs).mono cylinderEvents_le_pi le_rfl
  rw [antiferroKer_apply Λ2 x, lintegral_dirac' _ hmeas, antiferroKer_apply Λ1 (altFill Λ2 x),
    altFill_altFill_of_subset h]

/-- **Georgii, Example (14.16), the specification.** The zero-temperature limit of the Ising
antiferromagnet without external field on `S = ℤ`, `E = {-1, 1}`, built directly as a family of
proper deterministic Markov kernels (see the module docstring for why the general
`transferSpecification`/`lambdaSpecification` builders do not apply here). -/
def antiferromagnetSpecification : Specification ℤ Bool where
  toPreSpecification := { toFun := antiferroKer, isConsistent' := isConsistent_antiferroKer }
  isMarkovKernel' := fun Λ ↦ isMarkovKernel_antiferroKer Λ
  isProper' := isProper_antiferroKer

/-! ## The two alternating configurations -/

/-- `1` at even sites, `-1` (i.e. `false`) at odd sites. -/
def evenConfig : ℤ → Bool := fun j ↦ decide (Even j)

lemma evenConfig_succ (n : ℤ) : evenConfig (n + 1) = !evenConfig n := by
  unfold evenConfig
  by_cases h : Even n
  · have hn1 : ¬ Even (n + 1) := by rw [Int.even_add_one]; exact not_not_intro h
    simp [h, hn1]
  · have hn1 : Even (n + 1) := Int.even_add_one.2 h
    simp [h, hn1]

/-- Georgii's `ω^{+-}`: `1` (true) at even sites, `-1` (false) at odd sites. -/
def altPM : ℤ → Bool := evenConfig

/-- Georgii's `ω^{-+}`: `-1` at even sites, `1` at odd sites, i.e. `ω^{-+} = ω^{+-}` shifted by
one: `ω_i^{+-} = ω_{i+1}^{-+}`. -/
def altMP : ℤ → Bool := fun j ↦ !evenConfig j

lemma altPM_succ (n : ℤ) : altPM (n + 1) = !altPM n := evenConfig_succ n

lemma altMP_succ (n : ℤ) : altMP (n + 1) = !altMP n := by
  simp [altMP, evenConfig_succ n, Bool.not_not]

/-! ## `δ_{ω^{+-}}, δ_{ω^{-+}} ∈ ex 𝒢(γ)` -/

lemma isGibbsMeasure_dirac_of_alternating {σ : ℤ → Bool} (hσ : ∀ n : ℤ, σ (n + 1) = !σ n) :
    antiferromagnetSpecification.IsGibbsMeasure (Measure.dirac σ) := by
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have hmeas : Measurable (⇑(antiferromagnetSpecification Λ) : (ℤ → Bool) → Measure (ℤ → Bool)) :=
    (antiferromagnetSpecification Λ).measurable.mono cylinderEvents_le_pi le_rfl
  rw [MeasureTheory.Measure.dirac_bind hmeas]
  change antiferroKer Λ σ = Measure.dirac σ
  rw [antiferroKer_apply, altFill_of_alternating hσ Λ]

lemma isGibbsMeasure_dirac_altPM :
    antiferromagnetSpecification.IsGibbsMeasure (Measure.dirac altPM) :=
  isGibbsMeasure_dirac_of_alternating altPM_succ

lemma isGibbsMeasure_dirac_altMP :
    antiferromagnetSpecification.IsGibbsMeasure (Measure.dirac altMP) :=
  isGibbsMeasure_dirac_of_alternating altMP_succ

lemma dirac_altPM_mem_G : Measure.dirac altPM ∈ G antiferromagnetSpecification :=
  ⟨inferInstance, isGibbsMeasure_dirac_altPM⟩

lemma dirac_altMP_mem_G : Measure.dirac altMP ∈ G antiferromagnetSpecification :=
  ⟨inferInstance, isGibbsMeasure_dirac_altMP⟩

lemma dirac_tail_trivial (x : ℤ → Bool) {A : Set (ℤ → Bool)}
    (hA : MeasurableSet[tailSigmaAlgebra ℤ Bool] A) :
    (Measure.dirac x) A = 0 ∨ (Measure.dirac x) A = 1 := by
  have hAm : MeasurableSet A := tailSigmaAlgebra_le_pi _ hA
  rw [Measure.dirac_apply' _ hAm]
  by_cases h : x ∈ A <;> simp [h]

/-- **Georgii (14.16): `δ_{ω^{+-}} ∈ ex 𝒢(γ)`.** -/
theorem dirac_altPM_mem_extremePoints_G :
    Measure.dirac altPM ∈ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ :=
  mem_extremePoints_G_of_isTailTrivial dirac_altPM_mem_G fun _A hA ↦ dirac_tail_trivial altPM hA

/-- **Georgii (14.16): `δ_{ω^{-+}} ∈ ex 𝒢(γ)`.** -/
theorem dirac_altMP_mem_extremePoints_G :
    Measure.dirac altMP ∈ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ :=
  mem_extremePoints_G_of_isTailTrivial dirac_altMP_mem_G fun _A hA ↦ dirac_tail_trivial altMP hA

/-! ## The altMidpoint `(δ_{ω^{+-}} + δ_{ω^{-+}})/2` -/

/-- Georgii's `(δ_{ω^{+-}} + δ_{ω^{-+}})/2`. -/
def altMidpoint : Measure (ℤ → Bool) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac altPM + (2 : ℝ≥0∞)⁻¹ • Measure.dirac altMP

lemma two_inv_add_two_inv : (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
  rw [← two_mul, ENNReal.mul_inv_cancel two_ne_zero (by norm_num)]

/-- `altMidpoint ∈ 𝒢(γ)`: a convex combination of two Gibbs measures. -/
theorem altMidpoint_mem_G : altMidpoint ∈ G antiferromagnetSpecification :=
  add_smul_mem_G dirac_altPM_mem_G dirac_altMP_mem_G two_inv_add_two_inv

/-- A single-site cylinder distinguishing `altPM` from `altMP`, used to certify that `altMidpoint`
is a genuine (proper) convex combination of two *distinct* points of `𝒢(γ)`. -/
private lemma altPM_ne_altMP_witness : altPM 1 ≠ altMP 1 := by
  simp [altPM, altMP, evenConfig, Int.not_even_one]

theorem dirac_altPM_ne_dirac_altMP : Measure.dirac altPM ≠ Measure.dirac altMP := by
  intro h
  have hB : MeasurableSet {ω : ℤ → Bool | ω 1 = altPM 1} :=
    measurable_pi_apply 1 (measurableSet_singleton _)
  have h1 : (Measure.dirac altPM) {ω : ℤ → Bool | ω 1 = altPM 1} = 1 := by
    rw [Measure.dirac_apply' _ hB]; simp
  have h2 : (Measure.dirac altMP) {ω : ℤ → Bool | ω 1 = altPM 1} = 0 := by
    rw [Measure.dirac_apply' _ hB]
    simp [altPM_ne_altMP_witness.symm]
  rw [h] at h1
  rw [h2] at h1
  exact (zero_ne_one (α := ℝ≥0∞)) h1

/-- **Georgii (14.16): the altMidpoint is not extreme in `𝒢(γ)`.** -/
theorem altMidpoint_notMem_extremePoints_G :
    altMidpoint ∉ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ := by
  intro hextreme
  have hopen : altMidpoint ∈ openSegment ℝ≥0∞ (Measure.dirac altPM) (Measure.dirac altMP) :=
    ⟨(2 : ℝ≥0∞)⁻¹, (2 : ℝ≥0∞)⁻¹, ENNReal.inv_pos.2 (by norm_num), ENNReal.inv_pos.2 (by norm_num),
      two_inv_add_two_inv, rfl⟩
  have heq := (mem_extremePoints_iff_left.1 hextreme).2 (Measure.dirac altPM) dirac_altPM_mem_G
    (Measure.dirac altMP) dirac_altMP_mem_G hopen
  have heq' := (mem_extremePoints_iff_left.1 hextreme).2 (Measure.dirac altMP) dirac_altMP_mem_G
    (Measure.dirac altPM) dirac_altPM_mem_G (by rwa [openSegment_symm])
  exact dirac_altPM_ne_dirac_altMP (heq.trans heq'.symm)

/-! ## The altMidpoint is shift-invariant, and ergodic for the full shift group -/

lemma shift_toFun_altPM (j : ℤ) :
    (shift Bool j).toFun altPM = if Even j then altPM else altMP := by
  by_cases hj : Even j
  · simp only [hj, ite_true]
    funext i
    rw [shift_toFun_apply]
    have h := alternating_add altPM_succ i (-j)
    rw [show i - j = i + -j by ring, h]
    simp [parityFlip, even_neg, hj]
  · simp only [hj, ite_false]
    funext i
    rw [shift_toFun_apply]
    have h := alternating_add altPM_succ i (-j)
    rw [show i - j = i + -j by ring, h]
    simp [parityFlip, even_neg, hj, altMP, altPM]

lemma shift_toFun_altMP (j : ℤ) :
    (shift Bool j).toFun altMP = if Even j then altMP else altPM := by
  by_cases hj : Even j
  · simp only [hj, ite_true]
    funext i
    rw [shift_toFun_apply]
    have h := alternating_add altMP_succ i (-j)
    rw [show i - j = i + -j by ring, h]
    simp [parityFlip, even_neg, hj]
  · simp only [hj, ite_false]
    funext i
    rw [shift_toFun_apply]
    have h := alternating_add altMP_succ i (-j)
    rw [show i - j = i + -j by ring, h]
    simp [parityFlip, even_neg, hj, altMP, altPM]

theorem measurePreserving_shift_altMidpoint (j : ℤ) :
    MeasurePreserving (shift Bool j).toFun altMidpoint altMidpoint := by
  refine ⟨(shift Bool j).measurable_toFun, ?_⟩
  unfold altMidpoint
  rw [Measure.map_add _ _ (shift Bool j).measurable_toFun, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac' (shift Bool j).measurable_toFun,
    Measure.map_dirac' (shift Bool j).measurable_toFun, shift_toFun_altPM,
    shift_toFun_altMP]
  by_cases hj : Even j
  · simp [hj]
  · simp only [hj, ite_false]
    rw [add_comm]

theorem altMidpoint_mem_invariantFields_shiftGroup :
    altMidpoint ∈ invariantFields (shiftGroup ℤ Bool) := by
  have hprob : IsProbabilityMeasure altMidpoint := altMidpoint_mem_G.1
  exact mem_invariantFields_shiftGroup.2 ⟨hprob, measurePreserving_shift_altMidpoint⟩

theorem altMidpoint_mem_invariantG :
    altMidpoint ∈ invariantG antiferromagnetSpecification (shiftGroup ℤ Bool) :=
  ⟨altMidpoint_mem_G, altMidpoint_mem_invariantFields_shiftGroup⟩

/-- Shifting by `1` swaps `altPM` and `altMP`, so every `Θ`-invariant event contains both or
neither: `altMidpoint` is trivial on the invariant σ-algebra of the *full* shift group. -/
theorem altMidpoint_mem_trivialOn_invariantEvents_shiftGroup :
    altMidpoint ∈ trivialOn (invariantEvents (shiftGroup ℤ Bool)) := by
  intro A hA
  obtain ⟨hAm, hAinv⟩ := measurableSet_invariantEvents.1 hA
  have hswap : altMP ∈ A ↔ altPM ∈ A := by
    have h1 : (shift Bool 1).toFun ⁻¹' A = A :=
      hAinv (shift Bool 1) (shift_mem_shiftGroup 1)
    have h2 : (shift Bool 1).toFun altPM = altMP := by
      rw [shift_toFun_altPM]; simp [Int.not_even_one]
    have h3 := Set.ext_iff.1 h1 altPM
    rwa [Set.mem_preimage, h2] at h3
  have hcompute : altMidpoint A =
      (2 : ℝ≥0∞)⁻¹ * (Measure.dirac altPM A) + (2 : ℝ≥0∞)⁻¹ * (Measure.dirac altMP A) := by
    unfold altMidpoint
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hcompute, Measure.dirac_apply' _ hAm, Measure.dirac_apply' _ hAm]
  by_cases h : altPM ∈ A
  · have hMP : altMP ∈ A := hswap.mpr h
    right
    simp [h, hMP, two_inv_add_two_inv]
  · have hMP : altMP ∉ A := fun hmem ↦ h (hswap.mp hmem)
    left
    simp [h, hMP]

/-- **Georgii (14.16): the altMidpoint is extreme in `𝒢_Θ(γ)`, i.e. ergodic.** -/
theorem altMidpoint_mem_extremePoints_invariantG :
    altMidpoint ∈ (invariantG antiferromagnetSpecification (shiftGroup ℤ Bool)).extremePoints
      ℝ≥0∞ :=
  (mem_extremePoints_invariantG_iff_mem_trivialOn
      (shiftGroup_exists_disjoint_sites_preimage (E := Bool)) altMidpoint_mem_invariantG).2
    altMidpoint_mem_trivialOn_invariantEvents_shiftGroup

/-- **Georgii (14.16): the altMidpoint is ergodic for the shift.** -/
theorem ergodicSMul_altMidpoint : ErgodicSMul (shiftGroup ℤ Bool) (ℤ → Bool) altMidpoint :=
  (mem_extremePoints_invariantG_shiftGroup_iff_ergodicSMul altMidpoint_mem_invariantG).1
    altMidpoint_mem_extremePoints_invariantG

/-! ## Georgii (14.16), packaged -/

/-- **Georgii, Example (14.16).** `δ_{ω^{+-}}, δ_{ω^{-+}} ∈ ex 𝒢(γ)`, the altMidpoint
`(δ_{ω^{+-}} + δ_{ω^{-+}})/2` lies in `ex 𝒢_Θ(γ)` (it is a shift-invariant, ergodic Gibbs measure)
but is *not* extreme in `𝒢(γ)`. In particular `ex 𝒢_Θ(γ) \ ex 𝒢(γ) ≠ ∅`. -/
theorem georgii_14_16 :
    Measure.dirac altPM ∈ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ ∧
    Measure.dirac altMP ∈ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ ∧
    altMidpoint ∈ (invariantG antiferromagnetSpecification (shiftGroup ℤ Bool)).extremePoints
      ℝ≥0∞ ∧
    altMidpoint ∉ (G antiferromagnetSpecification).extremePoints ℝ≥0∞ :=
  ⟨dirac_altPM_mem_extremePoints_G, dirac_altMP_mem_extremePoints_G,
    altMidpoint_mem_extremePoints_invariantG, altMidpoint_notMem_extremePoints_G⟩

end MeasureTheory.GibbsMeasure.Antiferromagnet
