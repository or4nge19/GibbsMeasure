/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.CriticalTemperature
public import GibbsMeasure.Model.GKSInequalities
public import GibbsMeasure.Model.LebowitzMartinLof
public import GibbsMeasure.Model.SharpPhaseTransition

/-!
# A well-defined critical inverse temperature for the two-dimensional Ising ferromagnet

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., the discussion after
Theorem (6.9) (p. 100):

> "By an inequality of Griffiths (1967a), `μ₊^β(σ₀)` is a nonnegative nondecreasing function of
> `β`.  Consequently, there exists a critical inverse temperature `0 ≤ β_c ≤ ∞` such that
> `|𝒢(βΦ)| = 1` when `β < β_c` and `|𝒢(βΦ)| > 1` when `β > β_c`.  Theorem (8.7) below will
> imply that `β_c > 0`, and the second phase of Theorem (6.9) above just means that
> `β_c < ∞`.  Thus `0 < β_c < ∞`."

`GibbsMeasure/Model/CriticalTemperature.lean` proves the two "phases" — uniqueness for
`|β| < 1/4` and non-uniqueness for `β ≥ 8 log 2` — as a two-sided bracket.  This file defines
`β_c` and states the dichotomy at it:

* `isingBetaC` **defines** Georgii's `β_c` for the two-dimensional Ising ferromagnet;
* `le_isingBetaC`, `isingBetaC_le` give `1/4 ≤ β_c ≤ 8 log 2`, i.e. Georgii's `0 < β_c < ∞`
  *as a statement about a well-defined number*;
* `existsUnique_of_lt_isingBetaC` gives `|𝒢(βΦ)| = 1` for every `0 ≤ β < β_c`
  — the "uniqueness below `β_c`" half;
* `isUpperSet_isingNonUniqueness` records that non-uniqueness is monotone in `β`, and
  `nontrivial_of_isingBetaC_lt` deduces `|𝒢(βΦ)| > 1` for every `β > β_c`.

Both halves are now **unconditional**: the monotonicity of non-uniqueness is proved in
`GibbsMeasure/Model/LebowitzMartinLof.lean`, which supplies the Lebowitz–Martin-Löf/Ruelle
equivalence `|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` (Georgii states it without proof) together with
Griffiths' monotonicity of `β ↦ μ₊^β(σ₀)`.

`isingBetaC` is the infimum of the non-uniqueness set, so uniqueness below it is immediate;
non-uniqueness above it comes from `isUpperSet_isingNonUniqueness`, i.e. from
`LebowitzMartinLof.nontrivial_GP_ising2D_of_nontrivial_of_le`.  Sections M7-M8 build the
threshold `betaCOf M` of an abstract nonnegative nondecreasing order parameter (`betaCOf`,
`eq_zero_of_lt_betaCOf`, `pos_of_betaCOf_lt`, `exists_betaC_of_monotone`);
`isingBetaC_eq_betaCOf_spontaneousMagnetisation` identifies `isingBetaC` with `betaCOf m*`, and
`spontaneousMagnetisation_eq_zero_of_lt_isingBetaC` /
`spontaneousMagnetisation_pos_of_isingBetaC_lt` are Georgii's statement that `m*` vanishes below
`β_c` and is positive above it.

Transferring the sharp threshold from the order parameter `μ₊^β(σ₀)` to the cardinality of
`𝒢(βΦ)` uses the equivalence `|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` of Lebowitz–Martin-Löf (1972) and
Ruelle (1972), together with the local limit `μ₊^β = lim_Λ γ_Λ^{βΦ}(·|ω⁺)`; both are supplied
by `GibbsMeasure/Model/LebowitzMartinLof.lean` and `GibbsMeasure/Model/PlusPhase.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Topology

namespace MeasureTheory.GibbsMeasure

open MeasureTheory.GibbsMeasure.Peierls (Site)

/-! ### M6: sharp thresholds -/

/-- Below the infimum of a set of reals bounded below, nothing belongs to the set. -/
theorem notMem_of_lt_csInf {S : Set ℝ} (hbdd : BddBelow S) {β : ℝ} (h : β < sInf S) : β ∉ S :=
  fun hmem ↦ absurd (csInf_le hbdd hmem) (not_le.2 h)

/-- Above the infimum of a nonempty *upward closed* set of reals, everything belongs to it. -/
theorem mem_of_csInf_lt {S : Set ℝ} (hne : S.Nonempty) (hup : IsUpperSet S) {β : ℝ}
    (h : sInf S < β) : β ∈ S := by
  obtain ⟨x, hxS, hxβ⟩ := exists_lt_of_csInf_lt hne h
  exact hup hxβ.le hxS

/-! ### M7: the critical inverse temperature of a monotone order parameter -/

/-- The critical inverse temperature attached to an order parameter `M`: the infimum of the
inverse temperatures at which `M` is strictly positive. -/
def betaCOf (M : ℝ → ℝ) : ℝ := sInf {β : ℝ | 0 ≤ β ∧ 0 < M β}

lemma bddBelow_posSet (M : ℝ → ℝ) : BddBelow {β : ℝ | 0 ≤ β ∧ 0 < M β} :=
  ⟨0, fun _ hβ ↦ hβ.1⟩

theorem betaCOf_nonneg (M : ℝ → ℝ) : 0 ≤ betaCOf M := by
  rcases Set.eq_empty_or_nonempty {β : ℝ | 0 ≤ β ∧ 0 < M β} with h | h
  · rw [betaCOf, h, Real.sInf_empty]
  · exact le_csInf h fun _ hβ ↦ hβ.1

/-- **Below the critical temperature the order parameter vanishes.** -/
theorem eq_zero_of_lt_betaCOf {M : ℝ → ℝ} (hnn : ∀ β, 0 ≤ β → 0 ≤ M β) {β : ℝ} (h0 : 0 ≤ β)
    (h : β < betaCOf M) : M β = 0 := by
  have hnot : β ∉ {β : ℝ | 0 ≤ β ∧ 0 < M β} :=
    notMem_of_lt_csInf (bddBelow_posSet M) h
  simp only [Set.mem_ofPred_eq, not_and, not_lt] at hnot
  exact le_antisymm (hnot h0) (hnn β h0)

/-- **Above the critical temperature a nondecreasing order parameter is strictly positive.** -/
theorem pos_of_betaCOf_lt {M : ℝ → ℝ} (hmono : MonotoneOn M (Set.Ici 0))
    (hne : {β : ℝ | 0 ≤ β ∧ 0 < M β}.Nonempty) {β : ℝ} (h : betaCOf M < β) : 0 < M β := by
  obtain ⟨x, hx, hxβ⟩ := exists_lt_of_csInf_lt hne h
  refine lt_of_lt_of_le hx.2 (hmono ?_ ?_ hxβ.le)
  · exact Set.mem_Ici.2 hx.1
  · exact Set.mem_Ici.2 (le_trans hx.1 hxβ.le)

/-- **Georgii's "consequently, there exists a critical inverse temperature".**  A nonnegative
order parameter which is nondecreasing in `β` and eventually positive has a sharp threshold:
it vanishes strictly below `betaCOf M` and is strictly positive strictly above it. -/
theorem exists_betaC_of_monotone (M : ℝ → ℝ) (hmono : MonotoneOn M (Set.Ici 0))
    (hnn : ∀ β, 0 ≤ β → 0 ≤ M β) (hpos : ∃ β, 0 ≤ β ∧ 0 < M β) :
    ∃ βc : ℝ, 0 ≤ βc ∧ (∀ β, 0 ≤ β → β < βc → M β = 0) ∧ (∀ β, βc < β → 0 < M β) :=
  ⟨betaCOf M, betaCOf_nonneg M, fun _ h0 h ↦ eq_zero_of_lt_betaCOf hnn h0 h,
    fun _ h ↦ pos_of_betaCOf_lt hmono hpos h⟩

/-- A pointwise limit of functions that are nondecreasing on `[0, ∞)` is nondecreasing
on `[0, ∞)`. -/
theorem monotoneOn_of_tendsto {J : Type*} {F : Filter J} [F.NeBot] (m : J → ℝ → ℝ) (M : ℝ → ℝ)
    (hmono : ∀ j, MonotoneOn (m j) (Set.Ici 0))
    (hlim : ∀ β, Tendsto (fun j ↦ m j β) F (𝓝 (M β))) :
    MonotoneOn M (Set.Ici 0) := fun _ ha _ hb hab ↦
  le_of_tendsto_of_tendsto' (hlim _) (hlim _) fun j ↦ hmono j ha hb hab

/-! ### M8: Griffiths' inequality gives Georgii's monotone magnetisation -/

/-! ### M9: Georgii's `β_c` for the two-dimensional Ising ferromagnet -/

/-- The set of nonnegative inverse temperatures at which the two-dimensional Ising ferromagnet
(`J = 1`, `h = 0`) has more than one Gibbs measure. -/
def isingNonUniqueness : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ (GP (S := Fin 2 → ℤ) (E := Bool)
    (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial}

/-- **Georgii's critical inverse temperature `β_c`** of the two-dimensional Ising ferromagnet:
the infimum of the inverse temperatures at which the Gibbs measure fails to be unique. -/
def isingBetaC : ℝ := sInf isingNonUniqueness

lemma bddBelow_isingNonUniqueness : BddBelow isingNonUniqueness := ⟨0, fun _ hβ ↦ hβ.1⟩

lemma eight_log_two_nonneg : (0 : ℝ) ≤ 8 * Real.log 2 := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

lemma eight_log_two_mem_isingNonUniqueness : 8 * Real.log 2 ∈ isingNonUniqueness :=
  ⟨eight_log_two_nonneg, nontrivial_GP_ising2D_of_le le_rfl⟩

lemma isingNonUniqueness_nonempty : isingNonUniqueness.Nonempty :=
  ⟨_, eight_log_two_mem_isingNonUniqueness⟩

/-- **Lebowitz–Martin-Löf/Ruelle, as an identity of sets**: non-uniqueness happens exactly where
the spontaneous magnetisation is positive. -/
theorem isingNonUniqueness_eq_setOf_spontaneousMagnetisation_pos :
    isingNonUniqueness = {β : ℝ | 0 ≤ β ∧ 0 < spontaneousMagnetisation β} :=
  Set.ext fun β ↦ and_congr_right fun h0 ↦
    nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos β h0

/-- **Georgii's critical inverse temperature is the threshold of the order parameter `m*`**: the
two constructions in this file are the same number. -/
theorem isingBetaC_eq_betaCOf_spontaneousMagnetisation :
    isingBetaC = betaCOf spontaneousMagnetisation := by
  rw [isingBetaC, betaCOf, isingNonUniqueness_eq_setOf_spontaneousMagnetisation_pos]

/-- **Georgii, §6.2 after (6.9)**: the spontaneous magnetisation vanishes strictly below the
critical inverse temperature. -/
theorem spontaneousMagnetisation_eq_zero_of_lt_isingBetaC {β : ℝ} (h0 : 0 ≤ β)
    (h : β < isingBetaC) : spontaneousMagnetisation β = 0 :=
  eq_zero_of_lt_betaCOf (fun β hβ ↦ spontaneousMagnetisation_nonneg β hβ) h0
    (isingBetaC_eq_betaCOf_spontaneousMagnetisation ▸ h)

/-- **Georgii, §6.2 after (6.9)**: the spontaneous magnetisation is strictly positive strictly
above the critical inverse temperature — spontaneous magnetisation occurs. -/
theorem spontaneousMagnetisation_pos_of_isingBetaC_lt {β : ℝ} (h : isingBetaC < β) :
    0 < spontaneousMagnetisation β :=
  pos_of_betaCOf_lt (fun _ ha _ _ hab ↦ spontaneousMagnetisation_mono ha hab)
    (isingNonUniqueness_eq_setOf_spontaneousMagnetisation_pos ▸ isingNonUniqueness_nonempty)
    (isingBetaC_eq_betaCOf_spontaneousMagnetisation ▸ h)

lemma log_three_nonneg : (0 : ℝ) ≤ Real.log 3 := (Real.log_pos (by norm_num)).le

lemma log_three_mem_isingNonUniqueness : Real.log 3 ∈ isingNonUniqueness :=
  ⟨log_three_nonneg, PeierlsSharp.nontrivial_GP_isingSpecification_of_log_three le_rfl⟩

/-- **`β_c < ∞`** — the second assertion of Georgii Theorem (6.9), the Peierls argument, at
Georgii's own contour count `ℓ · 3^(ℓ-1)`; see `GibbsMeasure/Model/SharpContours.lean`. -/
theorem isingBetaC_le : isingBetaC ≤ Real.log 3 :=
  csInf_le bddBelow_isingNonUniqueness log_three_mem_isingNonUniqueness

/-- The cruder bound obtained from counting arbitrary plaquette-connected bond sets. -/
theorem isingBetaC_le_eight_log_two : isingBetaC ≤ 8 * Real.log 2 :=
  csInf_le bddBelow_isingNonUniqueness eight_log_two_mem_isingNonUniqueness

/-- **`β_c > 0`** — Georgii Theorem (8.7) with Dobrushin's condition (8.8). -/
theorem artanh_le_isingBetaC : Real.artanh (1 / 4) ≤ isingBetaC := by
  refine le_csInf isingNonUniqueness_nonempty fun β hβ ↦ ?_
  by_contra hlt
  push Not at hlt
  have habs : |β| < Real.artanh (1 / 4) := by rw [abs_of_nonneg hβ.1]; exact hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := hβ.2
  exact hxy (subsingleton_GP_ising2D_of_abs_lt_artanh habs hx hy)

/-- The `1/4` reading of `artanh_le_isingBetaC`, via `1/4 < artanh (1/4)`. -/
theorem le_isingBetaC : (1 : ℝ) / 4 ≤ isingBetaC :=
  le_trans one_quarter_lt_artanh_one_quarter.le artanh_le_isingBetaC

/-- **Georgii's `0 < β_c < ∞`**, now as a statement about a well-defined number. -/
theorem isingBetaC_pos : 0 < isingBetaC := lt_of_lt_of_le (by norm_num) le_isingBetaC

theorem isingBetaC_mem_Icc : isingBetaC ∈ Set.Icc ((1 : ℝ) / 4) (Real.log 3) :=
  ⟨le_isingBetaC, isingBetaC_le⟩

/-- The sharper bracket obtained from Georgii's `tanh` criterion (8.10):
`artanh (1/4) ≈ 0.2554 ≤ β_c ≤ log 3`. -/
theorem isingBetaC_mem_Icc_artanh :
    isingBetaC ∈ Set.Icc (Real.artanh (1 / 4)) (Real.log 3) :=
  ⟨artanh_le_isingBetaC, isingBetaC_le⟩

/-- **Uniqueness strictly below `β_c`.**  This half of Georgii's dichotomy holds
unconditionally: `β_c` is by definition the infimum of the non-uniqueness set. -/
theorem existsUnique_of_lt_isingBetaC {β : ℝ} (h0 : 0 ≤ β) (h : β < isingBetaC) :
    ∃! μ : ProbabilityMeasure (Site → Bool),
      μ ∈ GP (S := Fin 2 → ℤ) (E := Bool)
        (isingSpecification (latticeGraph 2) 1 0 β) := by
  have hnot : β ∉ isingNonUniqueness := notMem_of_lt_csInf bddBelow_isingNonUniqueness h
  have hsub : (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β)).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    exact hnot ⟨h0, ⟨x, hx, y, hy, hxy⟩⟩
  obtain ⟨μ, hμ⟩ := isingGibbsMeasure_nonempty (latticeGraph 2) 1 0 β
  exact ⟨μ, hμ, fun ν hν ↦ hsub hν hμ⟩

/-- **Non-uniqueness is monotone in the inverse temperature.**  This is the combination of the
Lebowitz–Martin-Löf/Ruelle equivalence `|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` with Griffiths'
monotonicity of `β ↦ μ₊^β(σ₀)`; both are proved in
`GibbsMeasure/Model/LebowitzMartinLof.lean`. -/
theorem isUpperSet_isingNonUniqueness : IsUpperSet isingNonUniqueness := fun _ _ h12 hβ ↦
  ⟨hβ.1.trans h12, nontrivial_GP_ising2D_of_nontrivial_of_le hβ.1 h12 hβ.2⟩

/-- **Non-uniqueness strictly above `β_c`**, from the monotonicity of non-uniqueness in `β`. -/
theorem nontrivial_of_isingBetaC_lt {β : ℝ} (h : isingBetaC < β) :
    (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial :=
  (mem_of_csInf_lt isingNonUniqueness_nonempty isUpperSet_isingNonUniqueness h).2

/-- **Georgii's `0 < β_c < ∞` for the two-dimensional Ising ferromagnet, sharpened.**

Unconditionally: `β_c` is a well-defined real number with `1/4 ≤ β_c ≤ log 3`, the Gibbs
measure is unique for every `0 ≤ β < β_c`, and it is non-unique for every `β ≥ 8 log 2`.

This replaces the two-sided bracket of
`GibbsMeasure/Model/CriticalTemperature.lean`'s `ising_two_dimensional_phase_transition`,
whose caveat was that no sharp `β_c` was available. -/
theorem ising_critical_temperature :
    (1 : ℝ) / 4 ≤ isingBetaC ∧ isingBetaC ≤ Real.log 3 ∧
      (∀ β : ℝ, 0 ≤ β → β < isingBetaC → ∃! μ : ProbabilityMeasure (Site → Bool),
        μ ∈ GP (S := Fin 2 → ℤ) (E := Bool)
          (isingSpecification (latticeGraph 2) 1 0 β)) ∧
      (∀ β : ℝ, 8 * Real.log 2 ≤ β → (GP (S := Fin 2 → ℤ) (E := Bool)
        (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial) :=
  ⟨le_isingBetaC, isingBetaC_le, fun _ h0 h ↦ existsUnique_of_lt_isingBetaC h0 h,
    fun _ hβ ↦ nontrivial_GP_ising2D_of_le hβ⟩

/-- **Georgii's sharp dichotomy**, unconditionally.  The critical inverse temperature `β_c` of
the two-dimensional Ising ferromagnet satisfies `0 < β_c < ∞`, `|𝒢(βΦ)| = 1` for `β < β_c`, and
`|𝒢(βΦ)| > 1` for `β > β_c`.  The last assertion rests on the monotonicity of non-uniqueness in
`β`, i.e. on Griffiths' inequality together with the Lebowitz–Martin-Löf/Ruelle equivalence
`|𝒢(βΦ)| > 1 ↔ μ₊^β(σ₀) > 0` of `GibbsMeasure/Model/LebowitzMartinLof.lean`. -/
theorem ising_sharp_phase_transition :
    (1 : ℝ) / 4 ≤ isingBetaC ∧ isingBetaC ≤ Real.log 3 ∧
      (∀ β : ℝ, 0 ≤ β → β < isingBetaC → ∃! μ : ProbabilityMeasure (Site → Bool),
        μ ∈ GP (S := Fin 2 → ℤ) (E := Bool)
          (isingSpecification (latticeGraph 2) 1 0 β)) ∧
      (∀ β : ℝ, isingBetaC < β → (GP (S := Fin 2 → ℤ) (E := Bool)
        (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial) :=
  ⟨le_isingBetaC, isingBetaC_le, fun _ h0 h ↦ existsUnique_of_lt_isingBetaC h0 h,
    fun _ h ↦ nontrivial_of_isingBetaC_lt h⟩

end MeasureTheory.GibbsMeasure

end

end
