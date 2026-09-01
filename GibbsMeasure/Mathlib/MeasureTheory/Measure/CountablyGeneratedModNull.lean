/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Sub-σ-algebras of a separable measure space are countably generated modulo null sets

A sub-σ-algebra of a countably generated σ-algebra need not be countably generated: the tail
σ-algebra of `ℕ → Bool` under a product measure is the standard counterexample, since its atoms are
the classes of the non-smooth equivalence relation `E₀`. Modulo null sets, however, no such
obstruction exists:

`exists_countable_generateFrom_le_ae_of_isSeparable`: if `μ` is a finite separable measure on
`(X, m)` — for instance any finite measure on a countably generated `m`, so any finite measure on a
standard Borel space — and `m₀ ≤ m` is *any* sub-σ-algebra, then there is a **countable**
`D ⊆ m₀` with `generateFrom D ≤ m₀` such that every `m₀`-measurable set agrees with some
`generateFrom D`-measurable set up to a `μ`-null set.

The argument is the separability of `L¹`: constant indicators of `m₀`-sets form a subset of
`Lp ℝ 1 μ`, which is second-countable, and second-countability passes to subsets. A countable dense
subset of that family gives approximation in the pseudo-metric `μ (s ∆ t)`, and Borel–Cantelli
upgrades approximation to equality modulo null sets.

## Main statements

* `MeasureTheory.exists_countable_measure_symmDiff_lt_of_le`: the `L¹`-separability step.
* `MeasureTheory.exists_measurableSet_measure_symmDiff_eq_zero`: the Borel–Cantelli step.
* `MeasureTheory.exists_countable_generateFrom_le_ae_of_isSeparable`,
  `MeasureTheory.exists_countablyGenerated_le_ae_of_isSeparable`: the conclusion.
-/

@[expose] public section

open Filter MeasurableSpace Set
open scoped ENNReal Topology symmDiff

namespace MeasureTheory

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}

/-- **`L¹`-separability of a sub-σ-algebra.** For a finite separable measure, the sets of any
sub-σ-algebra `m₀` can be approximated in measure by members of a single countable subfamily. -/
theorem exists_countable_measure_symmDiff_lt_of_le [IsFiniteMeasure μ] [IsSeparable μ]
    {m₀ : MeasurableSpace X} (hm₀ : m₀ ≤ m) :
    ∃ D : Set (Set X), D.Countable ∧ (∀ t ∈ D, MeasurableSet[m₀] t) ∧
      ∀ s, MeasurableSet[m₀] s → ∀ ε : ℝ, 0 < ε → ∃ t ∈ D, μ (s ∆ t) < ENNReal.ofReal ε := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  -- The constant-one indicators of `m₀`-measurable sets, viewed inside `L¹(μ)`.
  set ind : {s : Set X // MeasurableSet[m₀] s} → Lp ℝ 1 μ :=
    fun s ↦ indicatorConstLp 1 (hm₀ _ s.2) (measure_ne_top μ _) (1 : ℝ) with hind
  -- `dist` of two such indicators is the measure of the symmetric difference.
  have hdist : ∀ s t : {s : Set X // MeasurableSet[m₀] s},
      dist (ind s) (ind t) = μ.real ((s : Set X) ∆ (t : Set X)) := by
    intro s t
    rw [hind, dist_indicatorConstLp_eq_norm,
      norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
    simp
  -- `L¹(μ)` is second-countable, hence every subset of it is separable.
  obtain ⟨c, hcT, hcc, hTc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range ind)).exists_countable_dense_subset
  -- Pick an `m₀`-measurable set behind each element of the countable dense subset.
  have hchoice : ∀ f : c, ∃ s : {s : Set X // MeasurableSet[m₀] s}, ind s = (f : Lp ℝ 1 μ) :=
    fun f ↦ hcT f.2
  choose g hg using hchoice
  have := hcc.to_subtype
  refine ⟨Set.range fun f : c ↦ ((g f : {s : Set X // MeasurableSet[m₀] s}) : Set X),
    countable_range _, ?_, ?_⟩
  · rintro t ⟨f, rfl⟩
    exact (g f).2
  · intro s hs ε hε
    obtain ⟨f, hfc, hf⟩ := Metric.mem_closure_iff.1 (hTc ⟨⟨s, hs⟩, rfl⟩) ε hε
    refine ⟨((g ⟨f, hfc⟩ : {s : Set X // MeasurableSet[m₀] s}) : Set X), ⟨⟨f, hfc⟩, rfl⟩, ?_⟩
    have hlt : μ.real (s ∆ ((g ⟨f, hfc⟩ : {s : Set X // MeasurableSet[m₀] s}) : Set X)) < ε := by
      rw [← hdist ⟨s, hs⟩ (g ⟨f, hfc⟩), hg ⟨f, hfc⟩]
      exact hf
    rwa [measureReal_def, ← ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ _)] at hlt

/-- **Borel–Cantelli upgrade.** If a set can be approximated arbitrarily well in measure by sets of
a σ-algebra `m'`, then it agrees with an `m'`-measurable set up to a null set: take the `limsup` of
approximants of error `2⁻ⁿ`. -/
theorem exists_measurableSet_measure_symmDiff_eq_zero {m' : MeasurableSpace X} {s : Set X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ t, MeasurableSet[m'] t ∧ μ (s ∆ t) < ENNReal.ofReal ε) :
    ∃ t, MeasurableSet[m'] t ∧ μ (s ∆ t) = 0 := by
  choose f hfm hfle using fun n : ℕ ↦ h ((1 : ℝ) / 2 ^ n) (by positivity)
  refine ⟨limsup f atTop, ?_, ?_⟩
  · rw [limsup_eq_iInf_iSup_of_nat']
    simpa only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion] using
      MeasurableSet.iInter fun n ↦ MeasurableSet.iUnion fun i ↦ hfm (i + n)
  -- `s ∆ limsup f ⊆ limsup (fun n ↦ s ∆ f n)`, whose measure vanishes by Borel–Cantelli.
  · refine measure_mono_null (fun x hx ↦ ?_)
      (measure_limsup_atTop_eq_zero (s := fun n ↦ s ∆ f n) ?_)
    · rw [Filter.mem_limsup_iff_frequently_mem]
      rcases hx with ⟨hxs, hxA⟩ | ⟨hxA, hxs⟩
      · rw [Filter.mem_limsup_iff_frequently_mem, Filter.not_frequently] at hxA
        exact (hxA.mono fun n hn ↦ Or.inl ⟨hxs, hn⟩).frequently
      · rw [Filter.mem_limsup_iff_frequently_mem] at hxA
        exact hxA.mono fun n hn ↦ Or.inr ⟨hn, hxs⟩
    · have hb : ∀ n : ℕ, μ (s ∆ f n) ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
        intro n
        refine (hfle n).le.trans ?_
        rw [show (1 : ℝ) / 2 ^ n = ((1 : ℝ) / 2) ^ n by rw [div_pow, one_pow],
          ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
        norm_num
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]
      simp

/-- **Every sub-σ-algebra of a separable finite measure space is countably generated modulo null
sets.** No countability hypothesis is placed on `m₀`; the tail σ-algebra of a product space is a
sub-σ-algebra that is *not* countably generated, yet is covered here. -/
theorem exists_countable_generateFrom_le_ae_of_isSeparable [IsFiniteMeasure μ] [IsSeparable μ]
    {m₀ : MeasurableSpace X} (hm₀ : m₀ ≤ m) :
    ∃ D : Set (Set X), D.Countable ∧ generateFrom D ≤ m₀ ∧
      ∀ s, MeasurableSet[m₀] s → ∃ t, MeasurableSet[generateFrom D] t ∧ μ (s ∆ t) = 0 := by
  obtain ⟨D, hDc, hDm, hDapprox⟩ := exists_countable_measure_symmDiff_lt_of_le (μ := μ) hm₀
  refine ⟨D, hDc, generateFrom_le hDm, fun s hs ↦
    exists_measurableSet_measure_symmDiff_eq_zero fun ε hε ↦ ?_⟩
  obtain ⟨t, htD, ht⟩ := hDapprox s hs ε hε
  exact ⟨t, measurableSet_generateFrom htD, ht⟩

/-- `exists_countable_generateFrom_le_ae_of_isSeparable` packaged with the `CountablyGenerated`
class. -/
theorem exists_countablyGenerated_le_ae_of_isSeparable [IsFiniteMeasure μ] [IsSeparable μ]
    {m₀ : MeasurableSpace X} (hm₀ : m₀ ≤ m) :
    ∃ m' : MeasurableSpace X, m' ≤ m₀ ∧ @CountablyGenerated X m' ∧
      ∀ s, MeasurableSet[m₀] s → ∃ t, MeasurableSet[m'] t ∧ μ (s ∆ t) = 0 := by
  obtain ⟨D, hDc, hDle, hD⟩ := exists_countable_generateFrom_le_ae_of_isSeparable (μ := μ) hm₀
  exact ⟨generateFrom D, hDle, @CountablyGenerated.mk X (generateFrom D) ⟨D, hDc, rfl⟩, hD⟩

/-- Specialisation to a countably generated ambient σ-algebra — in particular to any standard Borel
space — where separability of a finite measure is automatic. -/
theorem exists_countablyGenerated_le_ae [CountablyGenerated X] [IsFiniteMeasure μ]
    {m₀ : MeasurableSpace X} (hm₀ : m₀ ≤ m) :
    ∃ m' : MeasurableSpace X, m' ≤ m₀ ∧ @CountablyGenerated X m' ∧
      ∀ s, MeasurableSet[m₀] s → ∃ t, MeasurableSet[m'] t ∧ μ (s ∆ t) = 0 :=
  exists_countablyGenerated_le_ae_of_isSeparable hm₀

end MeasureTheory
