/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Kalikow

/-!
# Georgii §11.3, Theorem (11.39): Step 3, and the classification of `ex 𝒢(Q)`

For Kalikow's matrix `Q` (Georgii (11.37)) the classification `ex 𝒢(Q) = {μ_Q} ∪ {μ_j : j ∈ ℤ}`
of Theorem (11.39) is directed by the boundary limit `Z = lim_{i → -∞} (σ_i + i) ∈ {-∞} ∪ ℤ`.
Step 3 of Georgii's proof computes the distribution of `Z` under the two kinds of candidates:

* `μ_Q(Z = -∞) = 1`, by the Borel–Cantelli lemma, because for every `k ∈ ℤ`
  `∑_{i<k} μ_Q(σ_i + i ≥ k) = ∑_{i<k} ∑_{x ≥ k-i} α(x) < a(1-p)^{-1} ∑_{i<k} p^{k-i} < ∞`;
* `μ_j(Z = j) = 1` for every `j ∈ ℤ`, likewise, because
  `∑_{i<j} μ_j(σ_i + i ≠ j) = ∑_{i<j} ∑_{x ≠ j-i} α_{i-j}(x) ≤ ∑_{i<j} s^{1-i+j} < ∞`.

Since `ℤ` is discrete, a `ℤ`-valued sequence converges to `j` iff it is eventually equal to `j`,
so `{Z = j}` is the event `{σ_i + i = j for all sufficiently small i}`, and `{Z = -∞}` is
`{σ_i + i → -∞}`.

## Main declarations

* `escapeEvent`, `limitEvent`, `existsLimit` — the events `{Z = -∞}`, `{Z = j}` and
  `{Z exists in {-∞} ∪ ℤ}`, with `measurableSet_escapeEvent`, `measurableSet_limitEvent`,
  `measurableSet_existsLimit`, and the disjointness lemmas `disjoint_escapeEvent_limitEvent`,
  `disjoint_limitEvent`, `eq_of_mem_limitEvent`.
* `stationary_tsum_indicator_Ici_le`, `entrance_tsum_indicator_compl_le` — the two summability
  estimates of Step 3: `∑_{x ≥ m} α(x) ≤ a p^m/(1-p)` (from `α(x) ≤ a p^x`,
  `alpha_le_aCoeff_mul_pow`) and `∑_{x ≠ m} α_{-m}(x) ≤ s^{m+1}` (the `δ_m` part of `α_{-m}`
  has mass `1 - s^{m+1}`).
* `tendsto_atBot_ae_invariantChain`, `eventually_eq_ae_shiftedChain` — **Georgii (11.39),
  Step 3**: `Z = -∞` `μ_Q`-almost surely, and `Z = j` `μ_j`-almost surely.
* `invariantChain_escapeEvent`, `shiftedChain_limitEvent` (`μ_Q(Z = -∞) = 1`, `μ_j(Z = j) = 1`),
  `invariantChain_existsLimit`, `shiftedChain_existsLimit`, and the vanishing statements
  `invariantChain_limitEvent`, `shiftedChain_escapeEvent`, `shiftedChain_limitEvent_of_ne`.
* `invariantChain_ne_shiftedChain`, `shiftedChain_ne` — `μ_Q ≠ μ_j` and `μ_j ≠ μ_{j'}` for
  `j ≠ j'`, read off from the masses of the limit events. (The second statement is also
  `injective_map_shift_chain`, obtained there from the failure of shift invariance of `μ_0`.)

The section *Theorem (11.39)* combines Step 3 with Step 2 (`exists_eq_of_mem_extremePoints`,
`GibbsMeasure/Model/Kalikow.lean`: every extreme Gibbs measure for `Q` is `μ_Q` or some `μ_j`)
into Georgii's theorem. The reverse inclusion — `μ_Q` and every `μ_j` are extreme — is his first
argument (the pattern of Step 4 of Theorem (11.31)): the extreme decomposition (7.26) of `μ_j` is
carried by extreme points `ν` with `ν(Z = j) = 1`, and by Steps 2–3 the only such `ν` is `μ_j`.
The decomposition `μ = μ(Z = -∞) μ_Q + ∑_j μ(Z = j) μ_j` of an arbitrary `μ ∈ 𝒢(Q)` is obtained by
integrating `ν(A) = ν(Z = -∞) μ_Q(A) + ∑_j ν(Z = j) μ_j(A)` (valid for every extreme `ν`) against
the weight `w_μ` of (7.26); its uniqueness is Theorem (7.26) itself (`eq_weightOf_of_join_eq`).
Georgii's last sentence, "each `μ ∈ 𝒢(Q)` is a Markov chain", is proved in the stronger form
that every `μ ∈ 𝒢(Q)` is a Markov chain *with transition matrix `Q`*: all `μ_Q`, `μ_j` are
(their boundary laws have `r ≡ 1`, so (11.11) gives `P_i = Q`), and the one-step recursion of the
cylinder probabilities is linear in the measure.

* `nonempty_G`, `mem_G_invariantChain`, `mem_G_shiftedChain`.
* `shiftedChain_mem_extremePoints_G`, `invariantChain_mem_extremePoints_G`,
  `extremePoints_G_eq` — **Georgii Theorem (11.39)**: `ex 𝒢(Q) = {μ_Q} ∪ {μ_j : j ∈ ℤ}`.
* `measure_existsLimit_eq_one_of_mem_G` — **Georgii Theorem (11.39)**: `Z` exists in
  `{-∞} ∪ ℤ` `μ`-almost surely, for every `μ ∈ 𝒢(Q)`.
* `measure_eq_add_tsum_of_mem_G`, `eq_add_sum_of_mem_G`,
  `measure_escapeEvent_add_tsum_measure_limitEvent` — **Georgii Theorem (11.39)**: the extreme
  decomposition `μ = μ(Z = -∞) μ_Q + ∑_j μ(Z = j) μ_j`, whose weights sum to `1`.
* `measure_intervalCylinder_of_mem_G`, `isMarkovChain_of_mem_G` — **Georgii Theorem (11.39),
  the final sentence**: `μ ∈ 𝒢(Q)` has the cylinder probabilities (11.10) of the boundary law
  `ℓ_i = μ(Z = -∞) α + ∑_j μ(Z = j) α_{i-j}`, `r_i = 1`, and is a Markov chain with transition
  matrix `Q`.

The helper `measure_preimage_eq_tsum_indicator` (the mass of a coordinate event `{σ_i ∈ S}` is
the sum over `S` of the one-site marginal) is Mathlib's `tsum_measure_preimage_singleton` read
through `tsum_subtype`, specialised to the coordinate projections of `ℤ → ℕ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov.Kalikow

/-! ## The events `{Z = -∞}` and `{Z = j}` -/

/-- Georgii's event `{Z = -∞}`, where `Z = lim_{i → -∞} (σ_i + i)`: the configurations along
which `σ_i + i → -∞` as `i → -∞`. -/
def escapeEvent : Set (ℤ → ℕ) :=
  {ω | Tendsto (fun i : ℤ ↦ (ω i : ℤ) + i) atBot atBot}

/-- Georgii's event `{Z = j}`, where `Z = lim_{i → -∞} (σ_i + i)`: since `ℤ` is discrete, a
`ℤ`-valued sequence converges to `j` iff it is eventually equal to `j` (`limitEvent_eq`). -/
def limitEvent (j : ℤ) : Set (ℤ → ℕ) :=
  {ω | ∀ᶠ i in atBot, (ω i : ℤ) + i = j}

/-- The event that the limit `Z = lim_{i → -∞} (σ_i + i)` exists in `{-∞} ∪ ℤ`. -/
def existsLimit : Set (ℤ → ℕ) := escapeEvent ∪ ⋃ j : ℤ, limitEvent j

lemma mem_escapeEvent {ω : ℤ → ℕ} :
    ω ∈ escapeEvent ↔ Tendsto (fun i : ℤ ↦ (ω i : ℤ) + i) atBot atBot :=
  Iff.rfl

lemma mem_limitEvent {ω : ℤ → ℕ} {j : ℤ} :
    ω ∈ limitEvent j ↔ ∀ᶠ i in atBot, (ω i : ℤ) + i = j :=
  Iff.rfl

/-- `{Z = j}` is the set of configurations along which `σ_i + i → j` as `i → -∞`, for the
discrete topology on `ℤ`. -/
lemma limitEvent_eq (j : ℤ) :
    limitEvent j = {ω | Tendsto (fun i : ℤ ↦ (ω i : ℤ) + i) atBot (𝓝 j)} := by
  ext ω
  simp only [limitEvent, mem_ofPred_eq, nhds_discrete, tendsto_pure]

lemma escapeEvent_subset_existsLimit : escapeEvent ⊆ existsLimit := subset_union_left

lemma limitEvent_subset_existsLimit (j : ℤ) : limitEvent j ⊆ existsLimit :=
  subset_union_right.trans' (subset_iUnion limitEvent j)

/-- The coordinate functional `ω ↦ σ_i + i` is measurable. -/
lemma measurable_coordinate_add (i : ℤ) : Measurable fun ω : ℤ → ℕ ↦ (ω i : ℤ) + i :=
  (measurable_of_countable fun k : ℕ ↦ (k : ℤ) + i).comp (measurable_pi_apply i)

lemma measurableSet_escapeEvent : MeasurableSet escapeEvent :=
  measurableSet_tendsto atBot measurable_coordinate_add

lemma measurableSet_limitEvent (j : ℤ) : MeasurableSet (limitEvent j) := by
  rw [limitEvent_eq]
  exact measurableSet_tendsto (𝓝 j) measurable_coordinate_add

lemma measurableSet_existsLimit : MeasurableSet existsLimit :=
  measurableSet_escapeEvent.union (MeasurableSet.iUnion measurableSet_limitEvent)

/-- A sequence that is eventually `j` and eventually `j'` forces `j = j'`. -/
lemma eq_of_mem_limitEvent {ω : ℤ → ℕ} {j j' : ℤ} (h : ω ∈ limitEvent j)
    (h' : ω ∈ limitEvent j') : j = j' := by
  obtain ⟨i, hi, hi'⟩ := (h.and h').exists
  exact hi.symm.trans hi'

/-- The events `{Z = j}`, `j ∈ ℤ`, are pairwise disjoint. -/
lemma disjoint_limitEvent {j j' : ℤ} (h : j ≠ j') : Disjoint (limitEvent j) (limitEvent j') :=
  Set.disjoint_left.2 fun _ hω hω' ↦ h (eq_of_mem_limitEvent hω hω')

/-- `{Z = -∞}` and `{Z = j}` are disjoint: a sequence tending to `-∞` is eventually below `j`. -/
lemma disjoint_escapeEvent_limitEvent (j : ℤ) : Disjoint escapeEvent (limitEvent j) := by
  refine Set.disjoint_left.2 fun ω hω hω' ↦ ?_
  obtain ⟨i, hi, hi'⟩ := ((tendsto_atBot.1 hω (j - 1)).and hω').exists
  omega

/-! ## Coordinate events and one-site marginals -/

/-- The mass of a coordinate event `{σ_i ∈ S}` is the sum over `S` of the one-site marginal
`x ↦ μ(σ_i = x)`: Mathlib's `tsum_measure_preimage_singleton` for the coordinate projections of
`ℤ → ℕ`, with the sum over the subtype `S` written as a sum of an indicator. -/
lemma measure_preimage_eq_tsum_indicator (μ : Measure (ℤ → ℕ)) (i : ℤ) (S : Set ℕ) :
    μ ((fun ω : ℤ → ℕ ↦ ω i) ⁻¹' S)
      = ∑' x : ℕ, S.indicator (fun x ↦ μ ((fun ω : ℤ → ℕ ↦ ω i) ⁻¹' {x})) x := by
  rw [← tsum_measure_preimage_singleton (μ := μ) S.to_countable
    (fun y _ ↦ measurable_pi_apply i (measurableSet_singleton y))]
  exact tsum_subtype S fun x ↦ μ ((fun ω : ℤ → ℕ ↦ ω i) ⁻¹' {x})

/-- Off `x = m`, Kalikow's entrance vector `α_{-m} = (1 - s^{m+1}) δ_m + s^{m+1} α` is
`s^{m+1} α`. -/
lemma entrance_neg_natCast_of_ne {p q : ℝ} {m x : ℕ} (hx : x ≠ m) :
    entrance p q (-(m : ℤ)) x = ENNReal.ofReal (sRatio p q ^ (m + 1) * alpha p q x) := by
  have h1 : ¬ ((1 : ℤ) ≤ -(m : ℤ)) := by omega
  simp [entrance, entranceReal, entranceNat, h1, hx]

/-! ## The two summability estimates of Step 3 -/

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p) (hp : p < 1)
include hq hqp hp

/-- `α(x) ≤ a p^x`, since `b q^x ≥ 0`: the estimate behind Georgii's
`∑_{x ≥ k-i} α(x) < a(1-p)^{-1} p^{k-i}` in Step 3. -/
lemma alpha_le_aCoeff_mul_pow (x : ℕ) : alpha p q x ≤ aCoeff p q * p ^ x := by
  have := mul_nonneg (bCoeff_pos hq hqp hp).le (pow_nonneg hq.le x)
  simp only [alpha]
  linarith

/-- **Georgii (11.39), Step 3, first estimate.** `∑_{x ≥ m} α(x) ≤ a p^m/(1-p)`: the geometric
tail of `α(x) ≤ a p^x`. -/
lemma stationary_tsum_indicator_Ici_le (m : ℕ) :
    ∑' x : ℕ, (Ici m).indicator (stationary p q) x
      ≤ ENNReal.ofReal (aCoeff p q * p ^ m / (1 - p)) := by
  have hp0 : 0 ≤ p := (p_pos hq hqp).le
  have ha : 0 ≤ aCoeff p q := (aCoeff_pos hq hqp hp).le
  have hs : Summable fun y : ℕ ↦ aCoeff p q * p ^ (y + m) :=
    ((summable_geometric_of_lt_one hp0 hp).mul_left (aCoeff p q * p ^ m)).congr fun y ↦ by ring
  calc ∑' x : ℕ, (Ici m).indicator (stationary p q) x
      = ∑' y : ℕ, stationary p q (y + m) := by
        rw [← (add_left_injective m).tsum_eq (f := (Ici m).indicator (stationary p q))]
        · exact tsum_congr fun y ↦ indicator_of_mem (by simp) _
        · intro x hx
          have hxm : m ≤ x := by
            by_contra hxm
            exact hx (indicator_of_notMem (by simpa [mem_Ici] using hxm) _)
          exact ⟨x - m, Nat.sub_add_cancel hxm⟩
    _ ≤ ∑' y : ℕ, ENNReal.ofReal (aCoeff p q * p ^ (y + m)) :=
        ENNReal.tsum_le_tsum fun y ↦ ENNReal.ofReal_le_ofReal (alpha_le_aCoeff_mul_pow hq hqp hp _)
    _ = ENNReal.ofReal (∑' y : ℕ, aCoeff p q * p ^ (y + m)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun y ↦ mul_nonneg ha (pow_nonneg hp0 _)) hs).symm
    _ = ENNReal.ofReal (aCoeff p q * p ^ m / (1 - p)) := by
        congr 1
        calc ∑' y : ℕ, aCoeff p q * p ^ (y + m)
            = ∑' y : ℕ, aCoeff p q * p ^ m * p ^ y := tsum_congr fun y ↦ by ring
          _ = aCoeff p q * p ^ m * (1 - p)⁻¹ := by
              rw [tsum_mul_left, tsum_geometric_of_lt_one hp0 hp]
          _ = aCoeff p q * p ^ m / (1 - p) := (div_eq_mul_inv _ _).symm

/-- **Georgii (11.39), Step 3, second estimate.** `∑_{x ≠ m} α_{-m}(x) ≤ s^{m+1}`: under `μ_j`
the site `i = j - m` carries the entrance vector `α_{i-j} = α_{-m}`, whose `δ_m` part has mass
`1 - s^{m+1}`, so `μ_j(σ_i + i ≠ j) = μ_j(σ_i ≠ m) ≤ s^{m+1}`. -/
lemma entrance_tsum_indicator_compl_le (m : ℕ) :
    ∑' x : ℕ, ({m}ᶜ : Set ℕ).indicator (entrance p q (-(m : ℤ))) x
      ≤ ENNReal.ofReal (sRatio p q ^ (m + 1)) := by
  have hs0 : 0 ≤ sRatio p q ^ (m + 1) := pow_nonneg (sRatio_pos hq hqp).le _
  calc ∑' x : ℕ, ({m}ᶜ : Set ℕ).indicator (entrance p q (-(m : ℤ))) x
      ≤ ∑' x : ℕ, ENNReal.ofReal (sRatio p q ^ (m + 1) * alpha p q x) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        by_cases hx : x = m
        · simp [hx]
        · rw [indicator_of_mem (by simpa using hx), entrance_neg_natCast_of_ne hx]
    _ = ENNReal.ofReal (sRatio p q ^ (m + 1)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ mul_nonneg hs0 (alpha_pos hq hqp hp x).le)
          ((summable_alpha hq hqp hp).mul_left _), tsum_mul_left, tsum_alpha hq hqp hp, mul_one]

/-! ## Step 3: the boundary limit `Z` under `μ_Q` and under `μ_j` -/

/-- `μ_j = θ_j(μ_0)` is a probability measure. -/
instance isProbabilityMeasure_shiftedChain (j : ℤ) :
    IsProbabilityMeasure (shiftedChain hq hqp hp j) := by
  rw [shiftedChain_eq_boundaryLawMeasure]
  infer_instance

/-- **Georgii (11.39), Step 3, for `μ_Q`.** `Z = lim_{i → -∞} (σ_i + i) = -∞` `μ_Q`-almost
surely. For each `k ∈ ℤ` the events `{σ_i + i > k}` at the sites `i = k - n`, `n ∈ ℕ`, have
`μ_Q`-masses `∑_{x ≥ n+1} α(x) ≤ a p^{n+1}/(1-p)`, summable in `n`; by the Borel–Cantelli lemma
`σ_i + i ≤ k` for all sufficiently small `i`, and the countably many `k` are handled at once. -/
theorem tendsto_atBot_ae_invariantChain :
    ∀ᵐ ω ∂(invariantChain hq hqp hp), Tendsto (fun i : ℤ ↦ (ω i : ℤ) + i) atBot atBot := by
  have hp0 : 0 ≤ p := (p_pos hq hqp).le
  have hk : ∀ k : ℤ, ∀ᵐ ω ∂(invariantChain hq hqp hp),
      ∀ᶠ n : ℕ in atTop, (ω (k - n) : ℤ) + (k - n) ≤ k := by
    intro k
    have hA : ∀ n : ℕ, invariantChain hq hqp hp ((fun ω : ℤ → ℕ ↦ ω (k - n)) ⁻¹' Ici (n + 1))
        ≤ ENNReal.ofReal (aCoeff p q * p ^ (n + 1) / (1 - p)) := fun n ↦ by
      rw [measure_preimage_eq_tsum_indicator]
      simp only [invariantChain_preimage_singleton]
      exact stationary_tsum_indicator_Ici_le hq hqp hp (n + 1)
    have hsum : (∑' n : ℕ,
        invariantChain hq hqp hp ((fun ω : ℤ → ℕ ↦ ω (k - n)) ⁻¹' Ici (n + 1))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
      have hs : Summable fun n : ℕ ↦ aCoeff p q * p ^ (n + 1) / (1 - p) :=
        (((summable_geometric_of_lt_one hp0 hp).mul_left (aCoeff p q * p)).div_const
          (1 - p)).congr fun n ↦ by ring
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ div_nonneg
        (mul_nonneg (aCoeff_pos hq hqp hp).le (pow_nonneg hp0 _)) (by linarith)) hs]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    filter_upwards [hω] with n hn
    simp only [mem_preimage, mem_Ici, not_le] at hn
    omega
  filter_upwards [ae_all_iff.2 hk] with ω hω
  refine tendsto_atBot_atBot.2 fun k ↦ ?_
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hω k)
  refine ⟨k - M, fun i hi ↦ ?_⟩
  have h := hM (k - i).toNat (by omega)
  rw [show k - ((k - i).toNat : ℤ) = i by omega] at h
  exact h

/-- **Georgii (11.39), Step 3, for `μ_j`.** `Z = lim_{i → -∞} (σ_i + i) = j` `μ_j`-almost surely.
The events `{σ_i + i ≠ j}` at the sites `i = j - (n+1)`, `n ∈ ℕ`, have `μ_j`-masses
`∑_{x ≠ n+1} α_{-(n+1)}(x) ≤ s^{n+2}`, summable in `n`; by the Borel–Cantelli lemma
`σ_i + i = j` for all sufficiently small `i`. -/
theorem eventually_eq_ae_shiftedChain (j : ℤ) :
    ∀ᵐ ω ∂(shiftedChain hq hqp hp j), ∀ᶠ i in atBot, (ω i : ℤ) + i = j := by
  have hs0 : 0 ≤ sRatio p q := (sRatio_pos hq hqp).le
  have hB : ∀ n : ℕ, shiftedChain hq hqp hp j
      ((fun ω : ℤ → ℕ ↦ ω (j - (n + 1 : ℕ))) ⁻¹' ({n + 1}ᶜ : Set ℕ))
        ≤ ENNReal.ofReal (sRatio p q ^ (n + 1 + 1)) := fun n ↦ by
    rw [measure_preimage_eq_tsum_indicator]
    simp only [shiftedChain_preimage_singleton, sub_sub_cancel_left]
    exact entrance_tsum_indicator_compl_le hq hqp hp (n + 1)
  have hsum : (∑' n : ℕ, shiftedChain hq hqp hp j
      ((fun ω : ℤ → ℕ ↦ ω (j - (n + 1 : ℕ))) ⁻¹' ({n + 1}ᶜ : Set ℕ))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hB)
    have hs : Summable fun n : ℕ ↦ sRatio p q ^ (n + 1 + 1) :=
      ((summable_geometric_of_lt_one hs0 (sRatio_lt_one hq hqp)).mul_left
        (sRatio p q ^ 2)).congr fun n ↦ by ring
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ pow_nonneg hs0 _) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨M, hM⟩ := eventually_atTop.1 hω
  refine eventually_atBot.2 ⟨j - (M + 1), fun i hi ↦ ?_⟩
  have h := hM (j - 1 - i).toNat (by omega)
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, not_not] at h
  rw [show j - (((j - 1 - i).toNat + 1 : ℕ) : ℤ) = i by omega] at h
  omega

/-- **Georgii (11.39), Step 3:** `μ_Q(Z = -∞) = 1`. -/
theorem invariantChain_escapeEvent : invariantChain hq hqp hp escapeEvent = 1 :=
  (prob_compl_eq_zero_iff measurableSet_escapeEvent).1
    (ae_iff.1 (tendsto_atBot_ae_invariantChain hq hqp hp))

/-- **Georgii (11.39), Step 3:** `μ_j(Z = j) = 1`. -/
theorem shiftedChain_limitEvent (j : ℤ) : shiftedChain hq hqp hp j (limitEvent j) = 1 :=
  (prob_compl_eq_zero_iff (measurableSet_limitEvent j)).1
    (ae_iff.1 (eventually_eq_ae_shiftedChain hq hqp hp j))

/-- The limit `Z` exists `μ_Q`-almost surely. -/
theorem invariantChain_existsLimit : invariantChain hq hqp hp existsLimit = 1 :=
  le_antisymm prob_le_one <| (invariantChain_escapeEvent hq hqp hp).symm.le.trans
    (measure_mono escapeEvent_subset_existsLimit)

/-- The limit `Z` exists `μ_j`-almost surely. -/
theorem shiftedChain_existsLimit (j : ℤ) : shiftedChain hq hqp hp j existsLimit = 1 :=
  le_antisymm prob_le_one <| (shiftedChain_limitEvent hq hqp hp j).symm.le.trans
    (measure_mono (limitEvent_subset_existsLimit j))

/-- `μ_Q(Z = j) = 0` for every `j ∈ ℤ`. -/
theorem invariantChain_limitEvent (j : ℤ) : invariantChain hq hqp hp (limitEvent j) = 0 :=
  measure_mono_null (disjoint_escapeEvent_limitEvent j).subset_compl_left
    ((prob_compl_eq_zero_iff measurableSet_escapeEvent).2 (invariantChain_escapeEvent hq hqp hp))

/-- `μ_j(Z = -∞) = 0`. -/
theorem shiftedChain_escapeEvent (j : ℤ) : shiftedChain hq hqp hp j escapeEvent = 0 :=
  measure_mono_null (disjoint_escapeEvent_limitEvent j).subset_compl_right
    ((prob_compl_eq_zero_iff (measurableSet_limitEvent j)).2
      (shiftedChain_limitEvent hq hqp hp j))

/-- `μ_j(Z = j') = 0` for `j' ≠ j`. -/
theorem shiftedChain_limitEvent_of_ne {j j' : ℤ} (h : j ≠ j') :
    shiftedChain hq hqp hp j (limitEvent j') = 0 :=
  measure_mono_null (disjoint_limitEvent h).subset_compl_left
    ((prob_compl_eq_zero_iff (measurableSet_limitEvent j)).2
      (shiftedChain_limitEvent hq hqp hp j))

/-- `μ_Q ≠ μ_j`: the event `{Z = j}` has `μ_Q`-mass `0` and `μ_j`-mass `1`. -/
theorem invariantChain_ne_shiftedChain (j : ℤ) :
    invariantChain hq hqp hp ≠ shiftedChain hq hqp hp j := by
  intro h
  have h1 := shiftedChain_limitEvent hq hqp hp j
  rw [← h, invariantChain_limitEvent hq hqp hp j] at h1
  exact zero_ne_one h1

/-- `μ_j ≠ μ_{j'}` for `j ≠ j'` (Georgii, before Theorem (11.39); compare
`injective_map_shift_chain`): the event `{Z = j'}` has `μ_j`-mass `0` and `μ_{j'}`-mass `1`. -/
theorem shiftedChain_ne {j j' : ℤ} (h : j ≠ j') :
    shiftedChain hq hqp hp j ≠ shiftedChain hq hqp hp j' := by
  intro heq
  have h1 := shiftedChain_limitEvent hq hqp hp j'
  rw [← heq, shiftedChain_limitEvent_of_ne hq hqp hp h] at h1
  exact zero_ne_one h1

/-! ## Theorem (11.39): the classification of `ex 𝒢(Q)` and the extreme decomposition -/

lemma nonempty_G :
    (G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))).Nonempty :=
  ⟨_, inferInstance, isGibbsMeasure_chain hq hqp hp⟩

lemma mem_G_invariantChain :
    invariantChain hq hqp hp
      ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)) :=
  ⟨inferInstance, isGibbsMeasure_invariantChain hq hqp hp⟩

lemma mem_G_shiftedChain (j : ℤ) :
    shiftedChain hq hqp hp j
      ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)) :=
  ⟨inferInstance, isGibbsMeasure_shiftedChain hq hqp hp j⟩

/-- **Georgii Theorem (11.39): `μ_j` is extreme.** The extreme decomposition (7.26) of `μ_j` is
carried by the extreme points `ν` with `ν(Z = j) = 1` (Step 3); by Step 2 such a `ν` is `μ_Q` or
some `μ_{j'}`, and `μ_Q(Z = j) = 0 = μ_{j'}(Z = j)` for `j' ≠ j` leave only `ν = μ_j`. -/
theorem shiftedChain_mem_extremePoints_G (j : ℤ) :
    shiftedChain hq hqp hp j
      ∈ (G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))).extremePoints
        ℝ≥0∞ := by
  classical
  have hG := nonempty_G hq hqp hp
  have hμG := mem_G_shiftedChain hq hqp hp j
  have hTmeas := measurableSet_limitEvent j
  have hzero : ∫⁻ ν, ν (limitEvent j)ᶜ ∂(weightOf hG (shiftedChain hq hqp hp j)) = 0 := by
    rw [← Measure.join_apply hTmeas.compl, join_weightOf hG hμG]
    exact (prob_compl_eq_zero_iff hTmeas).2 (shiftedChain_limitEvent hq hqp hp j)
  have hae : ∀ᵐ ν ∂(weightOf hG (shiftedChain hq hqp hp j)), ν (limitEvent j)ᶜ = 0 :=
    (lintegral_eq_zero_iff (Measure.measurable_coe hTmeas.compl)).1 hzero
  have haeex : ∀ᵐ ν ∂(weightOf hG (shiftedChain hq hqp hp j)),
      ν ∈ (G (transferSpecification (matrix p q)
        (isTransferMatrix hq hqp hp))).extremePoints ℝ≥0∞ :=
    ae_iff.2 (weightOf_extremePoints_compl hG hμG)
  obtain ⟨ν, hνT, hνex⟩ := (hae.and haeex).exists
  have hνprob : IsProbabilityMeasure ν := hνex.1.1
  have hν1 : ν (limitEvent j) = 1 := (prob_compl_eq_zero_iff hTmeas).1 hνT
  rcases exists_eq_of_mem_extremePoints hq hqp hp hνex with hνQ | ⟨j', hνj'⟩
  · rw [hνQ, invariantChain_limitEvent] at hν1
    exact absurd hν1 zero_ne_one
  · by_cases hjj : j' = j
    · subst hjj
      rwa [← hνj']
    · rw [hνj', shiftedChain_limitEvent_of_ne hq hqp hp hjj] at hν1
      exact absurd hν1 zero_ne_one

/-- **Georgii Theorem (11.39): `μ_Q` is extreme.** The extreme decomposition of `μ_Q` is carried
by the extreme points `ν` with `ν(Z = -∞) = 1`; by Step 2 and Step 3 the only such `ν` is
`μ_Q`. -/
theorem invariantChain_mem_extremePoints_G :
    invariantChain hq hqp hp
      ∈ (G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))).extremePoints
        ℝ≥0∞ := by
  classical
  have hG := nonempty_G hq hqp hp
  have hμG := mem_G_invariantChain hq hqp hp
  have hTmeas := measurableSet_escapeEvent
  have hzero : ∫⁻ ν, ν escapeEventᶜ ∂(weightOf hG (invariantChain hq hqp hp)) = 0 := by
    rw [← Measure.join_apply hTmeas.compl, join_weightOf hG hμG]
    exact (prob_compl_eq_zero_iff hTmeas).2 (invariantChain_escapeEvent hq hqp hp)
  have hae : ∀ᵐ ν ∂(weightOf hG (invariantChain hq hqp hp)), ν escapeEventᶜ = 0 :=
    (lintegral_eq_zero_iff (Measure.measurable_coe hTmeas.compl)).1 hzero
  have haeex : ∀ᵐ ν ∂(weightOf hG (invariantChain hq hqp hp)),
      ν ∈ (G (transferSpecification (matrix p q)
        (isTransferMatrix hq hqp hp))).extremePoints ℝ≥0∞ :=
    ae_iff.2 (weightOf_extremePoints_compl hG hμG)
  obtain ⟨ν, hνT, hνex⟩ := (hae.and haeex).exists
  have hνprob : IsProbabilityMeasure ν := hνex.1.1
  have hν1 : ν escapeEvent = 1 := (prob_compl_eq_zero_iff hTmeas).1 hνT
  rcases exists_eq_of_mem_extremePoints hq hqp hp hνex with hνQ | ⟨j, hνj⟩
  · rwa [← hνQ]
  · rw [hνj, shiftedChain_escapeEvent] at hν1
    exact absurd hν1 zero_ne_one

/-- **Georgii Theorem (11.39), the classification.** `ex 𝒢(Q) = {μ_Q} ∪ {μ_j : j ∈ ℤ}`. -/
theorem extremePoints_G_eq :
    (G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))).extremePoints ℝ≥0∞
      = insert (invariantChain hq hqp hp) (Set.range (shiftedChain hq hqp hp)) := by
  ext μ
  constructor
  · intro hμ
    have : IsProbabilityMeasure μ := hμ.1.1
    rcases exists_eq_of_mem_extremePoints hq hqp hp hμ with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact invariantChain_mem_extremePoints_G hq hqp hp
    · exact shiftedChain_mem_extremePoints_G hq hqp hp j

/-- **Georgii Theorem (11.39): the limit `Z = lim_{i → -∞} (σ_i + i)` exists in `{-∞} ∪ ℤ`
`μ`-almost surely, for every `μ ∈ 𝒢(Q)`.** By the extreme decomposition (7.26) it suffices to know
this for the extreme points, which are `μ_Q` and the `μ_j` (Step 2), for which it is Step 3. -/
theorem measure_existsLimit_eq_one_of_mem_G {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))) :
    μ existsLimit = 1 := by
  have hG := nonempty_G hq hqp hp
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hcompl : μ existsLimitᶜ = 0 := by
    rw [← join_weightOf hG hμ, Measure.join_apply measurableSet_existsLimit.compl]
    refine (lintegral_eq_zero_iff (Measure.measurable_coe measurableSet_existsLimit.compl)).2 ?_
    filter_upwards [ae_iff.2 (weightOf_extremePoints_compl hG hμ)] with ν hν
    have hνprob : IsProbabilityMeasure ν := hν.1.1
    rcases exists_eq_of_mem_extremePoints hq hqp hp hν with h | ⟨j, h⟩
    · rw [h]
      exact (prob_compl_eq_zero_iff measurableSet_existsLimit).2
        (invariantChain_existsLimit hq hqp hp)
    · rw [h]
      exact (prob_compl_eq_zero_iff measurableSet_existsLimit).2
        (shiftedChain_existsLimit hq hqp hp j)
  exact (prob_compl_eq_zero_iff measurableSet_existsLimit).1 hcompl

/-- **Georgii Theorem (11.39), the extreme decomposition, setwise.** For `μ ∈ 𝒢(Q)` and every
measurable `A`, `μ(A) = μ(Z = -∞) μ_Q(A) + ∑_j μ(Z = j) μ_j(A)`. The weight `w_μ` of (7.26) is
carried by the extreme points, each of which is `μ_Q` or some `μ_j` (Step 2); for such a `ν` the
value `ν(A)` is `ν(Z = -∞) μ_Q(A) + ∑_j ν(Z = j) μ_j(A)` by Step 3, and integrating against `w_μ`
turns `ν(Z = -∞)`, `ν(Z = j)` into `μ(Z = -∞)`, `μ(Z = j)`. -/
theorem measure_eq_add_tsum_of_mem_G {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)))
    {A : Set (ℤ → ℕ)} (hA : MeasurableSet A) :
    μ A = μ escapeEvent * invariantChain hq hqp hp A
      + ∑' j : ℤ, μ (limitEvent j) * shiftedChain hq hqp hp j A := by
  classical
  have hG := nonempty_G hq hqp hp
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hFν : ∀ ν ∈ (G (transferSpecification (matrix p q)
      (isTransferMatrix hq hqp hp))).extremePoints ℝ≥0∞,
      ν A = ν escapeEvent * invariantChain hq hqp hp A
        + ∑' j : ℤ, ν (limitEvent j) * shiftedChain hq hqp hp j A := by
    intro ν hν
    have hνprob : IsProbabilityMeasure ν := hν.1.1
    rcases exists_eq_of_mem_extremePoints hq hqp hp hν with h | ⟨j, h⟩
    · rw [h]
      simp only [invariantChain_escapeEvent, invariantChain_limitEvent, one_mul, zero_mul,
        tsum_zero, add_zero]
    · rw [h, shiftedChain_escapeEvent, zero_mul, zero_add,
        tsum_eq_single j fun j' hj' ↦ by
          rw [shiftedChain_limitEvent_of_ne hq hqp hp (Ne.symm hj'), zero_mul],
        shiftedChain_limitEvent, one_mul]
  have hjoin : ∀ B : Set (ℤ → ℕ), MeasurableSet B → μ B = ∫⁻ ν, ν B ∂(weightOf hG μ) :=
    fun B hB ↦ by rw [← Measure.join_apply hB, join_weightOf hG hμ]
  have hmeasE : Measurable fun ν : Measure (ℤ → ℕ) ↦ ν escapeEvent * invariantChain hq hqp hp A :=
    (Measure.measurable_coe measurableSet_escapeEvent).mul_const _
  have hmeasJ : ∀ j : ℤ,
      Measurable fun ν : Measure (ℤ → ℕ) ↦ ν (limitEvent j) * shiftedChain hq hqp hp j A :=
    fun j ↦ (Measure.measurable_coe (measurableSet_limitEvent j)).mul_const _
  rw [hjoin A hA, hjoin _ measurableSet_escapeEvent]
  simp_rw [hjoin _ (measurableSet_limitEvent _)]
  calc ∫⁻ ν, ν A ∂(weightOf hG μ)
      = ∫⁻ ν, ν escapeEvent * invariantChain hq hqp hp A
          + ∑' j : ℤ, ν (limitEvent j) * shiftedChain hq hqp hp j A ∂(weightOf hG μ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_iff.2 (weightOf_extremePoints_compl hG hμ)] with ν hν
        exact hFν ν hν
    _ = _ := by
        rw [lintegral_add_left hmeasE, lintegral_mul_const _
          (Measure.measurable_coe measurableSet_escapeEvent),
          lintegral_tsum fun j ↦ (hmeasJ j).aemeasurable]
        congr 1
        exact tsum_congr fun j ↦
          lintegral_mul_const _ (Measure.measurable_coe (measurableSet_limitEvent j))

/-- **Georgii Theorem (11.39), the extreme decomposition.** For every `μ ∈ 𝒢(Q)`,
`μ = μ(Z = -∞) μ_Q + ∑_{j ∈ ℤ} μ(Z = j) μ_j`. -/
theorem eq_add_sum_of_mem_G {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))) :
    μ = μ escapeEvent • invariantChain hq hqp hp
      + Measure.sum fun j : ℤ ↦ μ (limitEvent j) • shiftedChain hq hqp hp j := by
  ext A hA
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ hA,
    measure_eq_add_tsum_of_mem_G hq hqp hp hμ hA]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- The weights of the extreme decomposition sum to one: `μ(Z = -∞) + ∑_j μ(Z = j) = 1`, since
the limit `Z` exists `μ`-almost surely and the events `{Z = -∞}`, `{Z = j}` are pairwise
disjoint. -/
theorem measure_escapeEvent_add_tsum_measure_limitEvent {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))) :
    μ escapeEvent + ∑' j : ℤ, μ (limitEvent j) = 1 := by
  rw [← measure_iUnion (fun j j' h ↦ disjoint_limitEvent h) measurableSet_limitEvent,
    ← measure_union (Set.disjoint_iUnion_right.2 disjoint_escapeEvent_limitEvent)
      (MeasurableSet.iUnion measurableSet_limitEvent)]
  exact measure_existsLimit_eq_one_of_mem_G hq hqp hp hμ

/-- **Georgii's representation (11.10) of an arbitrary `μ ∈ 𝒢(Q)`**: the cylinder probabilities
are those of the boundary law `ℓ_i = μ(Z = -∞) α + ∑_j μ(Z = j) α_{i-j}`, `r_i = 1`. -/
theorem measure_intervalCylinder_of_mem_G {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)))
    {a b : ℤ} (hab : a ≤ b) (σ : ℤ → ℕ) :
    μ (intervalCylinder a b σ)
      = (μ escapeEvent * stationary p q (σ a)
          + ∑' j : ℤ, μ (limitEvent j) * entrance p q (a - j) (σ a))
        * pathProd (matrix p q) a b σ := by
  rw [measure_eq_add_tsum_of_mem_G hq hqp hp hμ (measurableSet_intervalCylinder a b σ), add_mul,
    ← ENNReal.tsum_mul_right]
  congr 1
  · rw [(isBoundaryLaw_const (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
      (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
      (tsum_stationary_mul_matrix hq hqp hp)).boundaryLawMeasure_intervalCylinder hab σ, mul_one]
    ring
  · refine tsum_congr fun j ↦ ?_
    rw [shiftedChain_eq_boundaryLawMeasure,
      ((isBoundaryLaw hq hqp hp).shift j).boundaryLawMeasure_intervalCylinder hab σ, mul_one]
    ring

/-- **Georgii Theorem (11.39), the final sentence: every `μ ∈ 𝒢(Q)` is a Markov chain** — with
transition matrix `Q` itself. Each `μ_Q` and `μ_j` is the measure (11.10) of a boundary law with
`r ≡ 1`, hence a Markov chain with transition matrix `Q` (Theorem (11.9)(a), (11.11)), and the
one-step recursion of the cylinder probabilities is linear in the measure, so it survives the
extreme decomposition. -/
theorem isMarkovChain_of_mem_G {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))) :
    IsMarkovChain (fun _ ↦ Kernel.ofMatrix (matrix p q)) μ := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  refine isMarkovChain_ofMatrix_of_forall_intervalCylinder (p := fun _ ↦ matrix p q)
    (fun _ x ↦ tsum_matrix hq hqp hp x) fun a b hab σ ↦ ?_
  have hstep : ∀ ν : Measure (ℤ → ℕ), (∃ (ℓ : ℤ → ℕ → ℝ≥0∞)
      (hbl : IsBoundaryLaw (matrix p q) ℓ fun _ _ ↦ 1), ν = boundaryLawMeasure hbl) →
      ν (intervalCylinder a (b + 1) σ)
        = ν (intervalCylinder a b σ) * matrix p q (σ b) (σ (b + 1)) := by
    rintro ν ⟨ℓ, hbl, rfl⟩
    rw [hbl.boundaryLawMeasure_intervalCylinder_succ hab σ, transitionMatrix_one]
  have hQstep := hstep (invariantChain hq hqp hp) ⟨fun _ ↦ stationary p q,
    isBoundaryLaw_const (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
      (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
      (tsum_stationary_mul_matrix hq hqp hp), rfl⟩
  have hjstep : ∀ j : ℤ, shiftedChain hq hqp hp j (intervalCylinder a (b + 1) σ)
      = shiftedChain hq hqp hp j (intervalCylinder a b σ) * matrix p q (σ b) (σ (b + 1)) :=
    fun j ↦ hstep _ ⟨_, _, shiftedChain_eq_boundaryLawMeasure hq hqp hp j⟩
  rw [measure_eq_add_tsum_of_mem_G hq hqp hp hμ (measurableSet_intervalCylinder a (b + 1) σ),
    measure_eq_add_tsum_of_mem_G hq hqp hp hμ (measurableSet_intervalCylinder a b σ), hQstep]
  simp_rw [hjstep]
  rw [add_mul, ← ENNReal.tsum_mul_right]
  congr 1
  · ring
  · exact tsum_congr fun j ↦ by ring

end MeasureTheory.GibbsMeasure.Markov.Kalikow

end
