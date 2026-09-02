/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.GroupTheory.Foelner
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The ergodic maximal inequality for actions of abelian groups

Let an abelian group `G` act on a measure space `(Ω, μ)` by measure-preserving maps
`ω ↦ g +ᵥ ω`, and let `F : ℕ → Finset G` be a sequence of finite non-empty sets. The **ergodic
maximal function** of `f : Ω → ℝ≥0∞` is
`ergodicMaximalFunction F f ω = ⨆ n, |F n|⁻¹ ∑_{j ∈ F n} f (j +ᵥ ω)`.

The main theorem `MeasureTheory.mul_measure_lt_ergodicMaximalFunction_le` is the weak-type
`(1,1)` bound
`c * μ {ω | c < ergodicMaximalFunction F f ω} ≤ C * ∫⁻ f`
under a *Vitali regularity* hypothesis on the sequence: there are finite sets `E n` with
`|E n| ≤ C |F n|` such that every translate `i' +ᵥ F m` with `m ≤ n` meeting `i +ᵥ F n` is
contained in `i +ᵥ E n` (`Finset.IsTranslateEnlargement F E`), and `0 ∈ F n`. This is
Georgii, *Gibbs Measures and Phase Transitions*, Lemma (14.A6), for cubes `Λ_n ⊆ ℤ^d`, where
`E n` is the concentric cube of triple side and `C = 3 ^ d`; in that form it is
`MeasureTheory.mul_measure_lt_ergodicMaximalFunction_le_cube`. The general statement is
Tempelman's maximal inequality for regular sequences: for an increasing sequence `F` with
`|F n - F n + F n| ≤ C |F n|` it is
`MeasureTheory.mul_measure_lt_ergodicMaximalFunction_le_of_monotone`.

The proof is Georgii's covering argument. Fix a configuration `ω`, a truncation level `N` and a
finite window `Δ ⊆ G`. Each site `i ∈ Δ` at which some truncated average exceeds `c` carries a
witness `i +ᵥ F n` on which `∑ f (· +ᵥ ω) > c |F n|`. The finite Vitali lemma
`Finset.exists_subset_pairwiseDisjoint_subset_biUnion` (greedy selection, largest `n` first)
extracts pairwise disjoint witnesses whose enlargements cover all such sites, so
`c |Δ_ω| ≤ C ∑_{j ∈ Δ + S} f (j +ᵥ ω)` with `S = ⋃_{n ≤ N} F n`
(`Finset.mul_card_le_mul_sum_of_forall_exists_lt_sum_vadd`). Integrating in `ω` and using
invariance gives `c |Δ| μ(A_N) ≤ C |Δ + S| ∫⁻ f`
(`MeasureTheory.mul_card_mul_measure_le_mul_card_add_mul_lintegral`). Letting `Δ` run through
Følner sets of the abelian group `G` (`AddCommGroup.exists_finset_transDist_le`) makes
`|Δ + S| / |Δ| → 1`, and `N → ∞` is monotone convergence.

## Hypotheses actually used

* `AddCommGroup G`: only to identify `{j + i : j ∈ F}` with `i +ᵥ F`, and for the Følner
  property of `G` (every abelian group is amenable). No countability of `G` is needed: the
  supremum in the maximal function is over `ℕ`, and all sums are over finite sets.
* `Measurable f`: for the measurability of the level sets and of `ω ↦ f (j +ᵥ ω)`. No
  integrability: if `∫⁻ f = ∞` the inequality is trivial.
* `μ` is any measure; only invariance under the action is used, not finiteness.
* `0 ∈ F n`: used twice in the covering argument (a site lies in its own witness), exactly as in
  Georgii's reduction to `0 ∈ Λ_1`. For an increasing sequence it is removed by translation
  (`MeasureTheory.ergodicMaximalFunction_vadd`).
-/

@[expose] public section

open Filter Finset Set
open scoped ENNReal Pointwise symmDiff

/-! ### The finite Vitali covering lemma -/

namespace Finset
variable {α : Type*} [DecidableEq α]

/-- **Finite Vitali covering lemma**, with exact comparison of sizes. Let `U i`, `i ∈ D`, be a
finite family of finite sets, each containing its index, with ranks `rk i` and enlargements
`V i` such that every `U i'` of rank at most `rk i` meeting `U i` is contained in `V i`. Then
some subfamily `W ⊆ D` has pairwise disjoint sets `U i` whose enlargements `V i` cover `D`.

The subfamily is chosen greedily, largest rank first. This is the finite, exact-comparison form
of `Vitali.exists_disjoint_subfamily_covering_enlargement`. -/
theorem exists_subset_pairwiseDisjoint_subset_biUnion (U V : α → Finset α) (rk : α → ℕ) :
    ∀ D : Finset α, (∀ i ∈ D, i ∈ U i) →
      (∀ i ∈ D, ∀ i' ∈ D, rk i' ≤ rk i → (U i' ∩ U i).Nonempty → U i' ⊆ V i) →
      ∃ W ⊆ D, (W : Set α).PairwiseDisjoint U ∧ D ⊆ W.biUnion V := by
  intro D
  induction D using Finset.strongInduction with
  | H D ih =>
  intro hU hV
  rcases D.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, Subset.rfl, by simp, by simp⟩
  obtain ⟨i₀, hi₀, hmax⟩ := D.exists_max_image rk hne
  have hi₀V : i₀ ∈ V i₀ :=
    hV i₀ hi₀ i₀ hi₀ le_rfl ⟨i₀, Finset.mem_inter.2 ⟨hU i₀ hi₀, hU i₀ hi₀⟩⟩ (hU i₀ hi₀)
  have hss : D.filter (fun i ↦ i ∉ V i₀) ⊂ D :=
    Finset.filter_ssubset.2 ⟨i₀, hi₀, not_not.2 hi₀V⟩
  obtain ⟨W', hW'D, hdisj, hcov⟩ := ih _ hss (fun i hi ↦ hU i (Finset.mem_of_mem_filter i hi))
    fun i hi i' hi' ↦ hV i (Finset.mem_of_mem_filter i hi) i' (Finset.mem_of_mem_filter i' hi')
  refine ⟨insert i₀ W', Finset.insert_subset hi₀ (hW'D.trans (Finset.filter_subset _ _)), ?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hdisj.insert fun i hi _ ↦ ?_
    obtain ⟨hiD, hiV⟩ := Finset.mem_filter.1 (hW'D hi)
    rw [Finset.disjoint_left]
    intro a ha₀ ha
    exact hiV (hV i₀ hi₀ i hiD (hmax i hiD) ⟨a, Finset.mem_inter.2 ⟨ha, ha₀⟩⟩ (hU i hiD))
  · intro i hi
    by_cases h : i ∈ V i₀
    · exact Finset.mem_biUnion.2 ⟨i₀, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.1 (hcov (Finset.mem_filter.2 ⟨hi, h⟩))
      exact Finset.mem_biUnion.2 ⟨j, Finset.mem_insert_of_mem hj, hij⟩

end Finset

/-! ### Regular sequences of finite sets in an abelian group -/

namespace Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {F E : ℕ → Finset G}

/-- `E` is a sequence of **enlargements** of `F`: every translate `i' +ᵥ F m` with `m ≤ n` that
meets `i +ᵥ F n` is contained in `i +ᵥ E n`. For cubes `F n = [0, r_n)^d ⊆ ℤ^d` the concentric
cubes `E n = [-r_n, 2 r_n)^d` will do; for any increasing sequence, `E n = F n - F n + F n` does
(`Monotone.isTranslateEnlargement_sub_add`). -/
def IsTranslateEnlargement (F E : ℕ → Finset G) : Prop :=
  ∀ ⦃m n⦄, m ≤ n → ∀ i i' : G, ((i' +ᵥ F m) ∩ (i +ᵥ F n)).Nonempty → i' +ᵥ F m ⊆ i +ᵥ E n

lemma IsTranslateEnlargement.vadd (hE : IsTranslateEnlargement F E) (a : G) :
    IsTranslateEnlargement (fun n ↦ a +ᵥ F n) fun n ↦ a +ᵥ E n := by
  intro m n hmn i i' h
  simp only [vadd_vadd] at h ⊢
  exact hE hmn _ _ h

/-- For an increasing sequence, `F n - F n + F n` enlarges `F n`: a smaller translate meeting
`i +ᵥ F n` lies in `i +ᵥ (F n - F n + F n)`. -/
lemma _root_.Monotone.isTranslateEnlargement_sub_add (hF : Monotone F) :
    IsTranslateEnlargement F fun n ↦ F n - F n + F n := by
  intro m n hmn i i' ⟨x, hx⟩
  rw [Finset.mem_inter, Finset.mem_vadd_finset, Finset.mem_vadd_finset] at hx
  obtain ⟨⟨b, hb, rfl⟩, ⟨a, ha, hab⟩⟩ := hx
  intro y hy
  obtain ⟨b', hb', rfl⟩ := Finset.mem_vadd_finset.1 hy
  refine Finset.mem_vadd_finset.2 ⟨a - b + b', Finset.mem_add.2
    ⟨a - b, Finset.mem_sub.2 ⟨a, ha, b, hF hmn hb, rfl⟩, b', hF hmn hb', rfl⟩, ?_⟩
  simp only [vadd_eq_add] at hab ⊢
  calc i + (a - b + b') = (i + a) + (b' - b) := by abel
    _ = (i' + b) + (b' - b) := by rw [hab]
    _ = i' + b' := by abel

lemma sum_vadd_finset {M : Type*} [AddCommMonoid M] (a : G) (s : Finset G) (g : G → M) :
    ∑ j ∈ a +ᵥ s, g j = ∑ j ∈ s, g (a + j) := by
  rw [Finset.vadd_finset_def, Finset.sum_image]
  · rfl
  · intro x _ y _ h
    simpa [vadd_eq_add] using h

/-- The **covering inequality** behind Georgii (14.A6), for a fixed configuration. If every site
`i ∈ D` carries a witness `i +ᵥ F n`, `n ≤ N`, on which the sum of `g` exceeds `c |F n|`, then
`c |D| ≤ C ∑_{k ∈ D + S} g k` for any `S` containing all `F n`, `n ≤ N`. -/
theorem mul_card_le_mul_sum_of_forall_exists_lt_sum_vadd (hE : IsTranslateEnlargement F E)
    (h0 : ∀ n, 0 ∈ F n) {C : ℝ≥0∞} (hC : ∀ n, ((E n).card : ℝ≥0∞) ≤ C * (F n).card)
    {g : G → ℝ≥0∞} {D S : Finset G} {N : ℕ} (hS : ∀ n ≤ N, F n ⊆ S) (c : ℝ≥0∞)
    (hD : ∀ i ∈ D, ∃ n ≤ N, c * (F n).card < ∑ k ∈ i +ᵥ F n, g k) :
    c * D.card ≤ C * ∑ k ∈ D + S, g k := by
  have : ∀ i, ∃ n, i ∈ D → n ≤ N ∧ c * (F n).card < ∑ k ∈ i +ᵥ F n, g k := fun i ↦ by
    by_cases hi : i ∈ D
    · obtain ⟨n, hn, h⟩ := hD i hi
      exact ⟨n, fun _ ↦ ⟨hn, h⟩⟩
    · exact ⟨0, fun h ↦ (hi h).elim⟩
  choose nn hnn using this
  obtain ⟨W, hWD, hdisj, hcov⟩ := exists_subset_pairwiseDisjoint_subset_biUnion
    (fun i ↦ i +ᵥ F (nn i)) (fun i ↦ i +ᵥ E (nn i)) nn D
    (fun i _ ↦ Finset.mem_vadd_finset.2 ⟨0, h0 _, by simp⟩)
    (fun i _ i' _ hle hne ↦ hE hle i i' hne)
  have h1 : (D.card : ℝ≥0∞) ≤ ∑ i ∈ W, ((E (nn i)).card : ℝ≥0∞) := by
    have := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    simp only [Finset.card_vadd_finset] at this
    exact_mod_cast this
  have h2 : ∑ i ∈ W, ((E (nn i)).card : ℝ≥0∞) ≤ C * ∑ i ∈ W, ((F (nn i)).card : ℝ≥0∞) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hC _
  have h3 : c * ∑ i ∈ W, ((F (nn i)).card : ℝ≥0∞) ≤ ∑ k ∈ D + S, g k := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ W, c * ((F (nn i)).card : ℝ≥0∞)
        ≤ ∑ i ∈ W, ∑ k ∈ i +ᵥ F (nn i), g k :=
          Finset.sum_le_sum fun i hi ↦ (hnn i (hWD hi)).2.le
      _ = ∑ k ∈ W.biUnion (fun i ↦ i +ᵥ F (nn i)), g k := (Finset.sum_biUnion hdisj).symm
      _ ≤ ∑ k ∈ D + S, g k :=
          Finset.sum_le_sum_of_subset <| Finset.biUnion_subset.2 fun i hi ↦
            (Finset.vadd_finset_subset_vadd_finset (hS _ (hnn i (hWD hi)).1)).trans
              (Finset.vadd_finset_subset_add (hWD hi))
  calc c * (D.card : ℝ≥0∞) ≤ c * (C * ∑ i ∈ W, ((F (nn i)).card : ℝ≥0∞)) := by
        gcongr; exact h1.trans h2
    _ = C * (c * ∑ i ∈ W, ((F (nn i)).card : ℝ≥0∞)) := by ring
    _ ≤ C * ∑ k ∈ D + S, g k := by gcongr

/-- `|Δ + S| ≤ |Δ| + ∑_{s ∈ S} |(s +ᵥ Δ) ∆ Δ|`: the sumset exceeds the window by at most the
Følner boundary terms. -/
lemma card_add_le_card_add_sum_transDist (Δ S : Finset G) :
    (Δ + S).card ≤ Δ.card + ∑ s ∈ S, Δ.transDist s := by
  have hsub : Δ + S ⊆ Δ ∪ S.biUnion fun s ↦ (s +ᵥ Δ) \ Δ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.1 hx
    by_cases h : y + z ∈ Δ
    · exact Finset.mem_union_left _ h
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_sdiff.2 ⟨?_, h⟩⟩)
      exact Finset.mem_vadd_finset.2 ⟨y, hy, by rw [vadd_eq_add, add_comm]⟩
  have hbd : ∀ s ∈ S, ((s +ᵥ Δ) \ Δ).card ≤ Δ.transDist s := fun s _ ↦ by
    rw [Finset.transDist_def, symmDiff_def]
    exact Finset.card_le_card le_sup_left
  calc (Δ + S).card ≤ (Δ ∪ S.biUnion fun s ↦ (s +ᵥ Δ) \ Δ).card := Finset.card_le_card hsub
    _ ≤ Δ.card + (S.biUnion fun s ↦ (s +ᵥ Δ) \ Δ).card := Finset.card_union_le _ _
    _ ≤ Δ.card + ∑ s ∈ S, ((s +ᵥ Δ) \ Δ).card := by gcongr; exact Finset.card_biUnion_le
    _ ≤ Δ.card + ∑ s ∈ S, Δ.transDist s := by gcongr with s hs; exact hbd s hs

end Finset

/-! ### The ergodic maximal function -/

namespace MeasureTheory

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] {F E : ℕ → Finset G} {f : Ω → ℝ≥0∞}
  {ω : Ω} {C c : ℝ≥0∞}

/-- The **ergodic maximal function** `sup_n |F n|⁻¹ ∑_{j ∈ F n} f (j +ᵥ ω)` of `f` along the
sequence of finite sets `F`, for an action of `G` on `Ω`. Georgii (14.A6) bounds
`μ {sup_n R_n f > c}` for the averages `R_n f = |Λ_n|⁻¹ ∑_{j ∈ Λ_n} f ∘ θ_j`. -/
noncomputable def ergodicMaximalFunction (F : ℕ → Finset G) (f : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ⨆ n, (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card

lemma lt_ergodicMaximalFunction_iff :
    c < ergodicMaximalFunction F f ω ↔ ∃ n, c < (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card :=
  lt_iSup_iff

lemma measurable_ergodicMaximalFunction [MeasurableSpace Ω]
    (hθ : ∀ g : G, Measurable (g +ᵥ · : Ω → Ω))
    (hf : Measurable f) : Measurable (ergodicMaximalFunction F f) :=
  Measurable.iSup fun _ ↦ (Finset.measurable_sum _ fun j _ ↦ hf.comp (hθ j)).div_const _

variable [DecidableEq G]

/-- Translating the averaging sets translates the configuration. -/
lemma ergodicMaximalFunction_vadd (a : G) :
    ergodicMaximalFunction (fun n ↦ a +ᵥ F n) f ω = ergodicMaximalFunction F f (a +ᵥ ω) := by
  refine iSup_congr fun n ↦ ?_
  rw [Finset.card_vadd_finset, Finset.sum_vadd_finset]
  exact congrArg (· / _) (Finset.sum_congr rfl fun j _ ↦ by rw [vadd_vadd, add_comm])

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Georgii (14.A6), finite-window form.** For the truncated level set
`A_N = {ω | ∃ n ≤ N, c < |F n|⁻¹ ∑_{j ∈ F n} f (j +ᵥ ω)}` and any finite window `Δ ⊆ G`,
`c |Δ| μ(A_N) ≤ C |Δ + S| ∫⁻ f`, where `S ⊇ F n` for all `n ≤ N`. -/
theorem mul_card_mul_measure_le_mul_card_add_mul_lintegral
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hE : Finset.IsTranslateEnlargement F E)
    (h0 : ∀ n, 0 ∈ F n) (hC : ∀ n, ((E n).card : ℝ≥0∞) ≤ C * (F n).card) (hf : Measurable f)
    (c : ℝ≥0∞) {N : ℕ} (Δ : Finset G) {S : Finset G} (hS : ∀ n ≤ N, F n ⊆ S) :
    c * Δ.card * μ {ω | ∃ n ≤ N, c < (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card} ≤
      C * (Δ + S).card * ∫⁻ ω, f ω ∂μ := by
  classical
  set A := {ω | ∃ n ≤ N, c < (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card} with hA
  have hfj : ∀ j : G, Measurable fun ω ↦ f (j +ᵥ ω) := fun j ↦ hf.comp (hθ j).measurable
  have hAm : MeasurableSet A := by
    have : A = ⋃ n ∈ Set.Iic N, {ω | c < (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun n _ ↦
      measurableSet_lt measurable_const ((Finset.measurable_sum _ fun j _ ↦ hfj j).div_const _)
  have h1 : Measurable (A.indicator (1 : Ω → ℝ≥0∞)) := measurable_one.indicator hAm
  -- The pointwise covering inequality.
  have hpt : ∀ ω, c * ∑ i ∈ Δ, A.indicator 1 (i +ᵥ ω) ≤ C * ∑ k ∈ Δ + S, f (k +ᵥ ω) := by
    intro ω
    have hcard : ∑ i ∈ Δ, A.indicator (1 : Ω → ℝ≥0∞) (i +ᵥ ω) =
        ((Δ.filter fun i ↦ i +ᵥ ω ∈ A).card : ℝ≥0∞) := by
      rw [← Finset.sum_boole]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [Set.indicator_apply]
    rw [hcard]
    refine (Finset.mul_card_le_mul_sum_of_forall_exists_lt_sum_vadd hE h0 hC
      (g := fun k ↦ f (k +ᵥ ω)) (D := Δ.filter fun i ↦ i +ᵥ ω ∈ A) hS c fun i hi ↦ ?_).trans
      (mul_le_mul_right (Finset.sum_le_sum_of_subset
        (Finset.add_subset_add_right (Finset.filter_subset _ _))) _)
    obtain ⟨n, hn, hlt⟩ := (Finset.mem_filter.1 hi).2
    refine ⟨n, hn, ?_⟩
    have hcard0 : ((F n).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.2 ⟨0, h0 n⟩).ne'
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hcard0) (Or.inl (ENNReal.natCast_ne_top _))] at hlt
    calc c * (F n).card < ∑ j ∈ F n, f (j +ᵥ (i +ᵥ ω)) := hlt
      _ = ∑ k ∈ i +ᵥ F n, f (k +ᵥ ω) := by
        rw [Finset.sum_vadd_finset]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [vadd_vadd, add_comm]
  -- Integrate both sides, using invariance.
  have hL : ∫⁻ ω, c * ∑ i ∈ Δ, A.indicator 1 (i +ᵥ ω) ∂μ = c * Δ.card * μ A := by
    have hm : ∀ i : G, Measurable fun ω ↦ A.indicator (1 : Ω → ℝ≥0∞) (i +ᵥ ω) := fun i ↦
      h1.comp (hθ i).measurable
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ ↦ hm i),
      lintegral_finsetSum _ fun i _ ↦ hm i,
      Finset.sum_congr rfl fun i _ ↦ (hθ i).lintegral_comp h1, lintegral_indicator_one hAm,
      Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hR : ∫⁻ ω, C * ∑ k ∈ Δ + S, f (k +ᵥ ω) ∂μ = C * (Δ + S).card * ∫⁻ ω, f ω ∂μ := by
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ ↦ hfj k),
      lintegral_finsetSum _ fun k _ ↦ hfj k,
      Finset.sum_congr rfl fun k _ ↦ (hθ k).lintegral_comp hf, Finset.sum_const, nsmul_eq_mul,
      mul_assoc]
  rw [← hL, ← hR]
  exact lintegral_mono hpt

/-- `a ≤ b` as soon as `a ≤ b (1 + η)` for every `η > 0`. -/
lemma _root_.ENNReal.le_of_forall_le_mul_ofReal_one_add {a b : ℝ≥0∞}
    (h : ∀ η : ℝ, 0 < η → a ≤ b * ENNReal.ofReal (1 + η)) : a ≤ b := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb ↦ ?_
  rcases eq_or_ne b 0 with rfl | hb0
  · exact (h 1 one_pos).trans (by simp)
  · have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb0 hb.ne
    refine (h (ε / b.toReal) (by positivity)).trans ?_
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, mul_add, mul_one,
      ENNReal.ofReal_div_of_pos hbpos, ENNReal.ofReal_toReal hb.ne, ENNReal.ofReal_coe_nnreal,
      ENNReal.mul_div_cancel hb0 hb.ne]

/-- **Georgii, Lemma (14.A6); Tempelman's maximal inequality.** Let an abelian group `G` act on
`(Ω, μ)` by measure-preserving maps and let `F : ℕ → Finset G` be a sequence of finite sets
containing `0` with enlargements `E n` of size `|E n| ≤ C |F n|`. Then for every measurable
`f : Ω → ℝ≥0∞` and every level `c`,
`c * μ {ω | c < sup_n |F n|⁻¹ ∑_{j ∈ F n} f (j +ᵥ ω)} ≤ C * ∫⁻ f`. -/
theorem mul_measure_lt_ergodicMaximalFunction_le
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hE : Finset.IsTranslateEnlargement F E)
    (h0 : ∀ n, 0 ∈ F n) (hC : ∀ n, ((E n).card : ℝ≥0∞) ≤ C * (F n).card) (hf : Measurable f)
    (c : ℝ≥0∞) :
    c * μ {ω | c < ergodicMaximalFunction F f ω} ≤ C * ∫⁻ ω, f ω ∂μ := by
  classical
  -- Truncate: the level set is the increasing union of the truncated level sets.
  set A : ℕ → Set Ω := fun N ↦ {ω | ∃ n ≤ N, c < (∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card} with hA
  have hAmono : Monotone A := fun N M hNM ω ⟨n, hn, h⟩ ↦ ⟨n, hn.trans hNM, h⟩
  have hAU : {ω | c < ergodicMaximalFunction F f ω} = ⋃ N, A N := by
    ext ω
    rw [Set.mem_iUnion]
    change c < _ ↔ ∃ N, ∃ n ≤ N, _
    rw [lt_ergodicMaximalFunction_iff]
    exact ⟨fun ⟨n, h⟩ ↦ ⟨n, n, le_rfl, h⟩, fun ⟨_, n, _, h⟩ ↦ ⟨n, h⟩⟩
  rw [hAU, hAmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun N ↦ ?_
  set S := (Finset.range (N + 1)).biUnion F with hSdef
  have hS : ∀ n ≤ N, F n ⊆ S := fun n hn ↦
    Finset.subset_biUnion_of_mem F (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  -- Følner windows `Δ` with `|Δ + S| ≤ (1 + η) |Δ|`.
  refine ENNReal.le_of_forall_le_mul_ofReal_one_add fun η hη ↦ ?_
  obtain ⟨Δ, hΔne, -, hΔ⟩ :=
    AddCommGroup.exists_finset_transDist_le S (η / (S.card + 1)) (by positivity)
  have hΔpos : (0 : ℝ) < Δ.card := by exact_mod_cast hΔne.card_pos
  have hbd : ((Δ + S).card : ℝ) ≤ (1 + η) * Δ.card := by
    have h2 : ∑ s ∈ S, (Δ.transDist s : ℝ) ≤ η * Δ.card := by
      have hq : (S.card : ℝ) * (η / (S.card + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      calc ∑ s ∈ S, (Δ.transDist s : ℝ) ≤ ∑ s ∈ S, η / (S.card + 1) * Δ.card :=
            Finset.sum_le_sum fun s hs ↦ hΔ s hs
        _ = (S.card * (η / (S.card + 1))) * Δ.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ η * Δ.card := by gcongr
    calc ((Δ + S).card : ℝ) ≤ Δ.card + ∑ s ∈ S, (Δ.transDist s : ℝ) := by
          exact_mod_cast Finset.card_add_le_card_add_sum_transDist Δ S
      _ ≤ Δ.card + η * Δ.card := by gcongr
      _ = (1 + η) * Δ.card := by ring
  have hbd' : ((Δ + S).card : ℝ≥0∞) ≤ ENNReal.ofReal (1 + η) * Δ.card := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (Δ.card),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hbd
  have hkey := mul_card_mul_measure_le_mul_card_add_mul_lintegral hθ hE h0 hC hf c Δ hS
  have hΔ0 : (Δ.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hΔne.card_pos.ne'
  rw [← ENNReal.mul_div_cancel_right (a := c * μ (A N)) hΔ0 (ENNReal.natCast_ne_top _),
    ENNReal.div_le_iff hΔ0 (ENNReal.natCast_ne_top _)]
  calc c * μ (A N) * Δ.card = c * Δ.card * μ (A N) := by ring
    _ ≤ C * (Δ + S).card * ∫⁻ ω, f ω ∂μ := hkey
    _ ≤ C * (ENNReal.ofReal (1 + η) * Δ.card) * ∫⁻ ω, f ω ∂μ := by gcongr
    _ = C * (∫⁻ ω, f ω ∂μ) * ENNReal.ofReal (1 + η) * Δ.card := by ring

/-- **Tempelman's maximal inequality** for an increasing sequence of finite sets `F` in an abelian
group with `|F n - F n + F n| ≤ C |F n|` (Georgii (14.A6) without the cube geometry). -/
theorem mul_measure_lt_ergodicMaximalFunction_le_of_monotone
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hf : Measurable f) (c : ℝ≥0∞) :
    c * μ {ω | c < ergodicMaximalFunction F f ω} ≤ C * ∫⁻ ω, f ω ∂μ := by
  obtain ⟨a, ha⟩ := hne
  have h0 : ∀ n, 0 ∈ (-a) +ᵥ F n := fun n ↦
    Finset.mem_vadd_finset.2 ⟨a, hF (Nat.zero_le n) ha, by simp⟩
  have hC' : ∀ n, (((-a) +ᵥ (F n - F n + F n)).card : ℝ≥0∞) ≤ C * ((-a) +ᵥ F n).card := by
    simpa only [Finset.card_vadd_finset] using hC
  have h := mul_measure_lt_ergodicMaximalFunction_le hθ
    (hF.isTranslateEnlargement_sub_add.vadd (-a)) h0 hC' hf c
  have hset : {ω | c < ergodicMaximalFunction (fun n ↦ (-a) +ᵥ F n) f ω} =
      (fun ω ↦ (-a) +ᵥ ω) ⁻¹' {ω | c < ergodicMaximalFunction F f ω} := by
    ext ω; simp [ergodicMaximalFunction_vadd]
  rwa [hset, (hθ (-a)).measure_preimage (measurableSet_lt measurable_const
    (measurable_ergodicMaximalFunction (fun g ↦ (hθ g).measurable) hf)).nullMeasurableSet] at h

/-- **Georgii (14.A6) for real-valued `f`**: `μ(sup_n |R_n f| > c) ≤ C μ(|f|) / c`, in the
weak-type form with `μ(|f|) = ∫⁻ ‖f‖ₑ`. Only measurability of `f` is needed. -/
theorem measure_exists_lt_abs_div_card_le
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hE : Finset.IsTranslateEnlargement F E)
    (h0 : ∀ n, 0 ∈ F n) (hC : ∀ n, ((E n).card : ℝ≥0∞) ≤ C * (F n).card) {f : Ω → ℝ}
    (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ≤
      C * (∫⁻ ω, ‖f ω‖ₑ ∂μ) / ENNReal.ofReal c := by
  have hsub : {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ⊆
      {ω | ENNReal.ofReal c < ergodicMaximalFunction F (fun ω ↦ ‖f ω‖ₑ) ω} := by
    intro ω ⟨n, hn⟩
    refine lt_ergodicMaximalFunction_iff.2 ⟨n, ?_⟩
    have hcard : (0 : ℝ) < (F n).card := by exact_mod_cast Finset.card_pos.2 ⟨0, h0 n⟩
    rw [abs_div, Nat.abs_cast, lt_div_iff₀ hcard] at hn
    have hn' : c * (F n).card < ∑ j ∈ F n, |f (j +ᵥ ω)| :=
      hn.trans_le (Finset.abs_sum_le_sum_abs _ _)
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hcard.ne'))
      (Or.inl (ENNReal.natCast_ne_top _))]
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hc.le]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hc hcard).trans hn')).2 hn'
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact (mul_le_mul_right (measure_mono hsub) _).trans
    (mul_measure_lt_ergodicMaximalFunction_le hθ hE h0 hC hf.enorm _)

/-! ### Cubes in `ℤ^d`: Georgii's constant `3 ^ d` -/

section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The translate of the cube `[0, r)^d` is `3 ^ d`-regular: `Λ - Λ + Λ` lies in the concentric
cube `[-r, 2r)^d`, of cardinality `3 ^ d |Λ|`. -/
lemma card_sub_add_cube_le (x : ι → ℤ) (r : ℕ) :
    let Λ : Finset (ι → ℤ) := x +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r
    (Λ - Λ + Λ).card ≤ 3 ^ Fintype.card ι * Λ.card := by
  intro Λ
  have hsub : Λ - Λ + Λ ⊆ x +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (-(r : ℤ)) (2 * r) := by
    intro y hy
    obtain ⟨w, hw, u, hu, rfl⟩ := Finset.mem_add.1 hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Finset.mem_sub.1 hw
    obtain ⟨p, hp', rfl⟩ := Finset.mem_vadd_finset.1 hp
    obtain ⟨q, hq', rfl⟩ := Finset.mem_vadd_finset.1 hq
    obtain ⟨u, hu', rfl⟩ := Finset.mem_vadd_finset.1 hu
    refine Finset.mem_vadd_finset.2 ⟨p - q + u, Fintype.mem_piFinset.2 fun i ↦ ?_, ?_⟩
    · have hp := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hp' i)
      have hq := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hq' i)
      have hu := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hu' i)
      simp only [Pi.add_apply, Pi.sub_apply, Finset.mem_Ico]
      omega
    · simp only [vadd_eq_add]; abel
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  simp only [Λ, Finset.card_vadd_finset, Fintype.card_piFinset, Int.card_Ico, Finset.prod_const,
    Finset.card_univ, sub_zero, Int.toNat_natCast]
  rw [show (2 * (r : ℤ) - -(r : ℤ)) = ((3 * r : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast,
    mul_pow]

/-- **Georgii, Lemma (14.A6)**: for an increasing sequence of cubes `Λ_n = x_n + [0, r_n)^d` in
`ℤ^d` and a `ℤ^d`-action by measure-preserving maps,
`c * μ {sup_n |Λ_n|⁻¹ ∑_{j ∈ Λ_n} f (j +ᵥ ω) > c} ≤ 3 ^ d ∫⁻ f`. The cubes need not exhaust
`ℤ^d`, nor contain `0`. -/
theorem mul_measure_lt_ergodicMaximalFunction_le_cube {Ω : Type*} [AddAction (ι → ℤ) Ω]
    [MeasurableSpace Ω] {μ : Measure Ω} (hθ : ∀ g : ι → ℤ, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ)
    (x : ℕ → ι → ℤ) (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (hF : Monotone fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (c : ℝ≥0∞) :
    c * μ {ω | c < ergodicMaximalFunction
        (fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)) f ω} ≤
      3 ^ Fintype.card ι * ∫⁻ ω, f ω ∂μ := by
  refine mul_measure_lt_ergodicMaximalFunction_le_of_monotone hθ hF ?_ (fun n ↦ ?_) hf c
  · exact ⟨x 0, Finset.mem_vadd_finset.2 ⟨0, Fintype.mem_piFinset.2 fun i ↦ by
      simp only [Pi.zero_apply, Finset.mem_Ico, le_refl, true_and]; exact_mod_cast hr 0, by simp⟩⟩
  · have := card_sub_add_cube_le (x n) (r n)
    exact_mod_cast this

/-- **Georgii, Lemma (14.A6)** in the book's form: `μ(sup_n |R_n f| > c) ≤ 3 ^ d μ(|f|) / c` for
an increasing sequence of cubes `Λ_n = x_n + [0, r_n)^d` in `ℤ^d`, a `ℤ^d`-action by
measure-preserving maps, measurable `f : Ω → ℝ` and `c > 0`, with `μ(|f|) = ∫⁻ ‖f‖ₑ`. -/
theorem measure_exists_lt_abs_div_card_le_cube {Ω : Type*} [AddAction (ι → ℤ) Ω]
    [MeasurableSpace Ω] {μ : Measure Ω} (hθ : ∀ g : ι → ℤ, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ)
    (x : ℕ → ι → ℤ) (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (hF : Monotone fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))
    {f : Ω → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c < |(∑ j ∈ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n),
        f (j +ᵥ ω)) / (r n ^ Fintype.card ι : ℕ)|} ≤
      3 ^ Fintype.card ι * (∫⁻ ω, ‖f ω‖ₑ ∂μ) / ENNReal.ofReal c := by
  set Λ : ℕ → Finset (ι → ℤ) := fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)
    with hΛ
  have hcard : ∀ n, (Λ n).card = r n ^ Fintype.card ι := fun n ↦ by
    simp [hΛ, Finset.card_vadd_finset, Fintype.card_piFinset, Int.card_Ico]
  have hsub : {ω | ∃ n, c < |(∑ j ∈ Λ n, f (j +ᵥ ω)) / (r n ^ Fintype.card ι : ℕ)|} ⊆
      {ω | ENNReal.ofReal c < ergodicMaximalFunction Λ (fun ω ↦ ‖f ω‖ₑ) ω} := by
    intro ω ⟨n, hn⟩
    refine lt_ergodicMaximalFunction_iff.2 ⟨n, ?_⟩
    have hcardpos : (0 : ℝ) < (Λ n).card := by
      rw [hcard]; exact_mod_cast pow_pos (hr n) _
    rw [← hcard, abs_div, Nat.abs_cast, lt_div_iff₀ hcardpos] at hn
    have hn' : c * (Λ n).card < ∑ j ∈ Λ n, |f (j +ᵥ ω)| :=
      hn.trans_le (Finset.abs_sum_le_sum_abs _ _)
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hcardpos.ne'))
      (Or.inl (ENNReal.natCast_ne_top _))]
    simp_rw [Real.enorm_eq_ofReal_abs]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hc.le]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hc hcardpos).trans hn')).2 hn'
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact (mul_le_mul_right (measure_mono hsub) _).trans
    (mul_measure_lt_ergodicMaximalFunction_le_cube hθ x r hr hF hf.enorm _)

end Cube

end MeasureTheory
