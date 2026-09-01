/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Topology.MetricSpace.DependsOn
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Georgii's oscillations (8.2) and (8.14)

The third layer of the library's single oscillation ontology (see CLAUDE-level docs):
`Dobrushin.osc f = oscOutside ∅ f` (total oscillation, Georgii (8.2)) and
`Dobrushin.oscAt f j = oscOutside {j}ᶜ f` (oscillation at a site, Georgii (8.14)), with the
`ofReal |·|` API both `Dobrushin.lean` and `OneDimensionalUniqueness.lean` consume. Split into its
own file so that one-dimensional uniqueness does not import the Dobrushin theory.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.GibbsMeasure.Dobrushin

variable {S E : Type*} {f : (S → E) → ℝ} {c : ℝ≥0∞} {j : S}

/-- The oscillation `δ(f) = sup_{ζ,η} |f(ζ) − f(η)|` of a function on the configuration space
(Georgii, the unnumbered display before Proposition (8.8), "in analogy with (8.2)"; (8.2) itself
is the oscillation of a function on the state space `E`).

It is the oscillation `oscOutside ∅ f` of `f` under variation of *all* coordinates; the two
agree because the `ℝ≥0∞`-valued distance of `ℝ` is `edist a b = ENNReal.ofReal |a − b|`
(`le_osc`, `osc_le`). -/
noncomputable def osc (f : (S → E) → ℝ) : ℝ≥0∞ := _root_.oscOutside (∅ : Set S) f

/-- Georgii (8.14): the single-site oscillation `δ_j(f)`, the oscillation of `f` under variation
of the coordinate `j` alone, i.e. `oscOutside {j}ᶜ f`. -/
noncomputable def oscAt (f : (S → E) → ℝ) (j : S) : ℝ≥0∞ := _root_.oscOutside ({j}ᶜ : Set S) f

/-! ### Georgii (8.2), (8.14): the basic oscillation API

`osc` and `oscAt` are the two instances `∅` and `{j}ᶜ` of the general `oscOutside` of
`GibbsMeasure/Mathlib/Topology/MetricSpace/DependsOn.lean`, so everything below is one line of
that API together with the bridge `edist_ofReal_abs_sub` between the `edist` of `ℝ` and
`ENNReal.ofReal |·|`. -/


lemma osc_eq_oscOutside_empty (f : (S → E) → ℝ) :
    osc f = _root_.oscOutside (∅ : Set S) f := rfl

lemma oscAt_eq_oscOutside_compl (f : (S → E) → ℝ) (j : S) :
    oscAt f j = _root_.oscOutside ({j}ᶜ : Set S) f := rfl

/-- The bridge between the value type of `oscOutside` on `ℝ` and Georgii's `|f(ζ) − f(η)|`: the
extended distance of two reals is `ENNReal.ofReal` of their absolute difference. -/
lemma edist_ofReal_abs_sub (a b : ℝ) : edist a b = ENNReal.ofReal |a - b| := by
  rw [edist_dist, Real.dist_eq]

lemma le_osc (f : (S → E) → ℝ) (ζ η : S → E) : ENNReal.ofReal |f ζ - f η| ≤ osc f := by
  rw [← edist_ofReal_abs_sub]
  exact _root_.le_oscOutside (by simp)

lemma osc_le (h : ∀ ζ η : S → E, ENNReal.ofReal |f ζ - f η| ≤ c) : osc f ≤ c :=
  _root_.oscOutside_le fun ζ η _ ↦ (edist_ofReal_abs_sub (f ζ) (f η)).trans_le (h ζ η)

lemma le_oscAt {ζ η : S → E} (h : ∀ k, k ≠ j → ζ k = η k) :
    ENNReal.ofReal |f ζ - f η| ≤ oscAt f j := by
  rw [← edist_ofReal_abs_sub]
  exact _root_.le_oscOutside fun k hk ↦ h k (by simpa using hk)

lemma oscAt_le (h : ∀ ζ η : S → E, (∀ k, k ≠ j → ζ k = η k) → ENNReal.ofReal |f ζ - f η| ≤ c) :
    oscAt f j ≤ c :=
  _root_.oscOutside_le fun ζ η hζη ↦
    (edist_ofReal_abs_sub (f ζ) (f η)).trans_le (h ζ η fun k hk ↦ hζη k (by simpa using hk))

/-- Georgii (8.14): the single-site oscillation is dominated by the global oscillation. More
generally `oscOutside s f ≤ osc f` for every `s`, by `oscOutside_antitone`. -/
lemma oscAt_le_osc : oscAt f j ≤ osc f := _root_.oscOutside_antitone (Set.empty_subset _)

@[simp] lemma osc_const (r : ℝ) : osc (fun _ : S → E ↦ r) = 0 :=
  _root_.DependsOn.oscOutside_eq_zero (dependsOn_const r)

@[simp] lemma oscAt_const (r : ℝ) (j : S) : oscAt (fun _ : S → E ↦ r) j = 0 :=
  _root_.DependsOn.oscOutside_eq_zero ((dependsOn_const r).mono (Set.empty_subset _))

/-- A function that only depends on the coordinates in `Δ` has no oscillation at sites off `Δ`. -/
lemma oscAt_eq_zero_of_dependsOn {Δ : Set S} (hf : DependsOn f Δ) (hj : j ∉ Δ) :
    oscAt f j = 0 :=
  _root_.DependsOn.oscOutside_eq_zero <| hf.mono fun k hk ↦ by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hj hk

end MeasureTheory.GibbsMeasure.Dobrushin
