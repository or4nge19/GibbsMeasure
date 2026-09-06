/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLawChains
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.TreeGeodesic
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.Doeblin
public import GibbsMeasure.Specification.ErgodicGibbs

/-!
# Mixing of a completely homogeneous Markov chain on a tree

Georgii, proof of Theorem (12.31), step 5. A completely homogeneous Markov chain `μ` on a tree,
with transition matrix `P` and one-dimensional marginal `α`, satisfies the two-block estimate

  `|μ(A ∩ C) - μ(A) μ(C)| ≤ max_x ∑_y |P^n(x, y) - α(y)|`

whenever `A` and `C` are events on the two sides of a chain of `n` consecutive bonds
(`IsMarkovChain.measure_inter_le_add` / `..._le_measure_inter_add`). By Theorem (3.A3)
(`Matrix.sum_abs_vecMul_pow_sub_le`) the right-hand side tends to `0`, so a graph automorphism
group that moves a fixed finite volume arbitrarily far away forces `μ` to be trivial on the
almost surely invariant events, i.e. `μ ∈ ex 𝓟_{I(B)}(Ω, 𝓕)`.

## Main results

* `IsMarkovChain.measure_inter_eq_setLIntegral`, `..._eq_tsum` — the conditional independence of
  the two sides of a bond given the spin at its near endpoint, for *arbitrary* events on the two
  sides (Comment (12.3)(1) in finite-dimensional form).
* `measure_inter_preimage_eq_pow` — the `n`-step conditional law along a chain of bonds is `P^n`.
* `measure_inter_le_add`, `le_measure_inter_add` — Georgii's two-block estimate.
* `ergodicSMul_of_forall_exists_dist_le` — a completely homogeneous Markov chain whose graph is
  moved arbitrarily far by its automorphisms is ergodic for those automorphisms, hence an extreme
  point of the invariant probability measures (`mem_extremePoints_invariantFields`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure.Tree

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

/-! ## Conditional independence of the two sides of a bond

Georgii's Comment (12.3)(1) states `μ(A | 𝓕_{]-∞, ij[}) = μ(A | 𝓕_i)` for `A ∈ 𝓕_{]ij, ∞[}`.
Integrating that identity over an event `B ∈ 𝓕_{]-∞, ij[}` gives the form used below, in which
both events are arbitrary. -/

section CondIndep

variable {G : SimpleGraph S} [G.LocallyFinite] {μ : Measure (S → E)}

omit [DecidableEq S] in
/-- Integrating a function of the single spin `σ i` over an event: a sum over the state space. -/
lemma setLIntegral_apply_eq_tsum (μ : Measure (S → E)) (i : S) (F : E → ℝ≥0∞)
    (B : Set (S → E)) :
    ∫⁻ σ in B, F (σ i) ∂μ
      = ∑' x : E, F x * μ ((fun σ : S → E ↦ σ i) ⁻¹' {x} ∩ B) := by
  rw [← lintegral_map (measurable_of_countable F) (measurable_pi_apply i),
    lintegral_countable' (μ := (μ.restrict B).map fun σ : S → E ↦ σ i)]
  refine tsum_congr fun x ↦ ?_
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton x),
    Measure.restrict_apply (measurable_pi_apply i (measurableSet_singleton x))]

omit [DecidableEq S] in
/-- **Comment (12.3)(1), integrated form.** For a Markov chain on a tree, an event `A` on the far
side of a bond `ij` and an event `B` on the near side,
`μ(A ∩ B) = ∫_B μ(A | σ_i) dμ`. This is the two-sided conditional independence: `A` and `B` are
independent given the spin at `i`. -/
theorem IsMarkovChain.measure_inter_eq_setLIntegral [Nonempty E] (hμ : IsMarkovChain G μ)
    (hG : G.IsTree) {i j : S} (hij : G.Adj i j) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past j i)] A)
    {B : Set (S → E)} (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past i j)] B) :
    μ (A ∩ B)
      = ∫⁻ σ in B, μ (A ∩ cyl ({i} : Finset S) σ) / μ (cyl ({i} : Finset S) σ) ∂μ := by
  classical
  have hprob := hμ.isProbabilityMeasure
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hiP : i ∈ G.past i j := SimpleGraph.mem_past_self_of_adj hij
  set g : (S → E) → ℝ≥0∞ := fun ξ ↦ (μ.restrict A) (cyl {i} ξ) / μ (cyl {i} ξ) with hgdef
  have hgm : Measurable g := (measurable_measure_cyl _ _).div (measurable_measure_cyl μ _)
  have hgdep : DependsOn g ({i} : Set S) := fun ξ ξ' h ↦ by
    simp only [hgdef]
    rw [cyl_congr (Λ := ({i} : Finset S)) fun m hm ↦
      h m (Set.mem_singleton_iff.2 (Finset.mem_singleton.1 hm))]
  have hgle : ∀ ξ, g ξ ≤ 1 := fun ξ ↦
    ENNReal.div_le_of_le_mul (by rw [one_mul]; exact Measure.restrict_le_self _)
  have hfin : IsFiniteMeasure (μ.withDensity g) :=
    isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
      ((lintegral_mono hgle).trans_eq lintegral_one))
  have hcyl : ∀ (W : Finset S) (ω : S → E), (W : Set S) ⊆ G.past i j →
      (μ.restrict A) (cyl W ω) = (μ.withDensity g) (cyl W ω) := by
    intro W ω hWp
    have hdisj : Disjoint W (insert i W \ W) := Finset.disjoint_sdiff
    have hunion : W ∪ (insert i W \ W) = insert i W :=
      Finset.union_sdiff_of_subset (Finset.subset_insert i W)
    rw [measure_cyl_eq_lintegral_lambdaCount _ hdisj ω,
      measure_cyl_eq_lintegral_lambdaCount _ hdisj ω, hunion]
    refine lintegral_congr fun ξ ↦ ?_
    have hW' : ∀ k ∈ insert i W, k ∈ G.past i j := by
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact hiP
      · exact hWp (Finset.mem_coe.2 hk)
    have hkey := hμ.measure_inter_cyl_mul_measure_cyl_singleton hG hij hA hW'
      (Finset.mem_insert_self i W) ξ
    have hgξ : g ξ = μ (A ∩ cyl ({i} : Finset S) ξ) / μ (cyl ({i} : Finset S) ξ) := by
      simp only [hgdef]
      rw [Measure.restrict_apply (measurableSet_cyl _ _),
        Set.inter_comm (cyl ({i} : Finset S) ξ) A]
    rw [Measure.restrict_apply (measurableSet_cyl _ _), Set.inter_comm,
      withDensity_apply _ (measurableSet_cyl _ _),
      setLIntegral_congr_fun (measurableSet_cyl _ _) (g := fun _ ↦ g ξ) (fun σ hσ ↦
        hgdep fun m hm ↦ mem_cyl.1 hσ m (by
          rw [Set.mem_singleton_iff.1 hm]
          exact Finset.mem_insert_self i W)),
      setLIntegral_const, hgξ]
    by_cases h0 : μ (cyl ({i} : Finset S) ξ) = 0
    · have hsub : cyl (insert i W) ξ ⊆ cyl ({i} : Finset S) ξ :=
        cyl_mono (Finset.singleton_subset_iff.2 (Finset.mem_insert_self i W)) ξ
      rw [measure_mono_null (Set.inter_subset_right.trans hsub) h0,
        measure_mono_null (Set.inter_subset_right (s := A)) h0, ENNReal.zero_div, zero_mul]
    · rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, ← hkey,
        ENNReal.mul_div_cancel_right h0 (measure_ne_top _ _)]
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hgξ' : ∀ ξ : S → E,
      g ξ = μ (A ∩ cyl ({i} : Finset S) ξ) / μ (cyl ({i} : Finset S) ξ) := fun ξ ↦ by
    simp only [hgdef]
    rw [Measure.restrict_apply (measurableSet_cyl _ _),
      Set.inter_comm (cyl ({i} : Finset S) ξ) A]
  calc μ (A ∩ B) = (μ.restrict A) B := by
        rw [Measure.restrict_apply hBm, Set.inter_comm]
    _ = (μ.withDensity g) B := measure_eq_of_forall_cyl hcyl hB
    _ = ∫⁻ σ in B, g σ ∂μ := withDensity_apply _ hBm
    _ = ∫⁻ σ in B, μ (A ∩ cyl ({i} : Finset S) σ) / μ (cyl ({i} : Finset S) σ) ∂μ := by
        simp_rw [hgξ']

omit [DecidableEq S] in
/-- **Comment (12.3)(1), integrated form, as a sum over the state space.** -/
theorem IsMarkovChain.measure_inter_eq_tsum [Nonempty E] (hμ : IsMarkovChain G μ)
    (hG : G.IsTree) {i j : S} (hij : G.Adj i j) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past j i)] A)
    {B : Set (S → E)} (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past i j)] B) :
    μ (A ∩ B) = ∑' x : E,
      μ (A ∩ (fun σ : S → E ↦ σ i) ⁻¹' {x}) / μ ((fun σ : S → E ↦ σ i) ⁻¹' {x})
        * μ ((fun σ : S → E ↦ σ i) ⁻¹' {x} ∩ B) := by
  classical
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  set F : E → ℝ≥0∞ := fun x ↦ μ (A ∩ (fun σ : S → E ↦ σ i) ⁻¹' {x})
    / μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) with hFdef
  have hrw : ∀ σ : S → E,
      μ (A ∩ cyl ({i} : Finset S) σ) / μ (cyl ({i} : Finset S) σ) = F (σ i) := by
    intro σ
    have hpre : (fun σ' : S → E ↦ σ' i) ⁻¹' {σ i} = cyl ({i} : Finset S) σ := by
      rw [preimage_singleton_eq_cyl i (σ i) σ, Function.update_eq_self]
    rw [hFdef]
    simp only [hpre]
  rw [hμ.measure_inter_eq_setLIntegral hG hij hA hB, lintegral_congr hrw,
    setLIntegral_apply_eq_tsum μ i F B]

end CondIndep

/-! ## The `n`-step conditional law along a chain of bonds

For a completely homogeneous Markov chain, conditioning the far event `A` on the spin at a site
`v₀` and moving that site one bond towards `A` multiplies the conditional law by the transition
matrix `P`; iterating along a chain of `n` bonds gives `P ^ n`. -/

section Chain

variable {G : SimpleGraph S} [G.LocallyFinite] {μ : Measure (S → E)} [Fintype E] [DecidableEq E]
  {P : Matrix E E ℝ≥0∞} {α : E → ℝ≥0∞} {A : Set (S → E)}

omit [DecidableEq S] in
/-- A measure is the sum of its restrictions to the level sets of a single spin. -/
lemma measure_eq_tsum_inter_preimage (μ : Measure (S → E)) (k : S) {C : Set (S → E)}
    (hC : MeasurableSet C) :
    μ C = ∑' z : E, μ (C ∩ (fun σ : S → E ↦ σ k) ⁻¹' {z}) := by
  have hUnion : C = ⋃ z : E, C ∩ (fun σ : S → E ↦ σ k) ⁻¹' {z} := by
    ext σ; simp
  have hdisj :
      Pairwise (Function.onFun Disjoint fun z : E ↦ C ∩ (fun σ : S → E ↦ σ k) ⁻¹' {z}) :=
    fun z z' hzz' ↦ Set.disjoint_left.2 (by
      rintro σ ⟨-, hz⟩ ⟨-, hz'⟩; exact hzz' (hz.symm.trans hz'))
  conv_lhs => rw [hUnion]
  exact measure_iUnion hdisj fun z ↦ hC.inter (measurable_pi_apply k (measurableSet_singleton z))

omit [DecidableEq S] in
/-- **One step of the chain.** For a completely homogeneous Markov chain, if `A` is an event
beyond the bond `(v₁, v₂)` whose conditional law given the spin at `v₁` is `f`, then its
conditional law given the spin at the previous site `v₀` is `P f`. -/
theorem measure_inter_preimage_step [Nonempty E] (hμ : IsMarkovChain G μ) (hG : G.IsTree)
    (hmarg : ∀ (k : S) (x : E), μ ((fun σ : S → E ↦ σ k) ⁻¹' {x}) = α x)
    (htr : ∀ ⦃i j : S⦄, G.Adj i j → ∀ x y : E, transitionProb μ i j x y = P x y)
    (hαpos : ∀ x : E, 0 < α x)
    {v₀ v₁ v₂ : S} (h01 : G.Adj v₀ v₁) (h12 : G.Adj v₁ v₂) (h0 : v₀ ∈ G.past v₁ v₂)
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past v₂ v₁)] A)
    {f : E → ℝ≥0∞} (hf : ∀ y : E, μ (A ∩ (fun σ : S → E ↦ σ v₁) ⁻¹' {y}) = f y * α y) (x : E) :
    μ (A ∩ (fun σ : S → E ↦ σ v₀) ⁻¹' {x}) = α x * ∑ z, P x z * f z := by
  classical
  have hprob := hμ.isProbabilityMeasure
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hαtop : ∀ z : E, α z ≠ ⊤ := fun z ↦ by rw [← hmarg v₀ z]; exact measure_ne_top _ _
  have hne : v₀ ≠ v₁ := h01.ne
  obtain ⟨ω⟩ : Nonempty (S → E) := ⟨fun _ ↦ Classical.arbitrary E⟩
  have key : ∀ z : E,
      μ (A ∩ (fun σ : S → E ↦ σ v₀) ⁻¹' {x} ∩ (fun σ : S → E ↦ σ v₁) ⁻¹' {z})
        = α x * (P x z * f z) := by
    intro z
    have hcylW : cyl ({v₀, v₁} : Finset S)
        (Function.update (Function.update ω v₀ x) v₁ z)
        = (fun σ : S → E ↦ σ v₀) ⁻¹' {x} ∩ (fun σ : S → E ↦ σ v₁) ⁻¹' {z} :=
      (preimage_inter_preimage_eq_cyl hne x z ω).symm
    have hcyl1 : cyl ({v₁} : Finset S) (Function.update (Function.update ω v₀ x) v₁ z)
        = (fun σ : S → E ↦ σ v₁) ⁻¹' {z} :=
      (preimage_singleton_eq_cyl v₁ z (Function.update ω v₀ x)).symm
    have hW : ∀ k ∈ ({v₀, v₁} : Finset S), k ∈ G.past v₁ v₂ := by
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact h0
      · rw [Finset.mem_singleton.1 hk]; exact SimpleGraph.mem_past_self_of_adj h12
    have hkey := hμ.measure_inter_cyl_mul_measure_cyl_singleton hG h12 hA hW (by simp)
      (Function.update (Function.update ω v₀ x) v₁ z)
    rw [hcylW, hcyl1, hf z, hmarg v₁ z] at hkey
    have hprod : μ ((fun σ : S → E ↦ σ v₀) ⁻¹' {x} ∩ (fun σ : S → E ↦ σ v₁) ⁻¹' {z})
        = α x * P x z := by
      rw [← transitionProb_mul_measure_eq v₀ v₁ x z, hmarg v₀ x, htr h01 x z]
    rw [hprod] at hkey
    rw [Set.inter_assoc]
    refine (ENNReal.mul_left_inj (hαpos z).ne' (hαtop z)).1 ?_
    rw [hkey]
    ring
  rw [measure_eq_tsum_inter_preimage μ v₁
    (hAm.inter (measurable_pi_apply v₀ (measurableSet_singleton x)))]
  simp_rw [key]
  rw [ENNReal.tsum_mul_left, tsum_fintype]

omit [DecidableEq S] in
/-- **The `n`-step conditional law along a chain of bonds.** Let `w 0, …, w (n + 1)` be a chain of
consecutive vertices which never backtracks, and let `A` be an event lying beyond every one of its
bonds, with conditional law `f` given the spin at `w n`. Then the conditional law of `A` given the
spin at `w 0` is `P ^ n` applied to `f`. This is Georgii's (12.4) in the form needed by the proof
of Theorem (12.31), step 5. -/
theorem measure_inter_preimage_eq_pow [Nonempty E] (hμ : IsMarkovChain G μ) (hG : G.IsTree)
    (hmarg : ∀ (k : S) (x : E), μ ((fun σ : S → E ↦ σ k) ⁻¹' {x}) = α x)
    (htr : ∀ ⦃i j : S⦄, G.Adj i j → ∀ x y : E, transitionProb μ i j x y = P x y)
    (hαpos : ∀ x : E, 0 < α x) :
    ∀ (n : ℕ) (w : ℕ → S), (∀ l ≤ n, G.Adj (w l) (w (l + 1))) →
      (∀ l < n, w l ∈ G.past (w (l + 1)) (w (l + 2))) →
      (∀ l ≤ n, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past (w (l + 1)) (w l))] A) →
      ∀ f : E → ℝ≥0∞, (∀ y : E, μ (A ∩ (fun σ : S → E ↦ σ (w n)) ⁻¹' {y}) = f y * α y) →
      ∀ x : E, μ (A ∩ (fun σ : S → E ↦ σ (w 0)) ⁻¹' {x}) = α x * ∑ y, (P ^ n) x y * f y := by
  intro n
  induction n with
  | zero =>
    intro w _ _ _ f hf x
    rw [hf x, pow_zero]
    simp [Matrix.one_apply, Finset.sum_ite_eq, mul_comm]
  | succ n ih =>
    intro w hadj hpast hAmeas f hf x
    have hg : ∀ z : E, μ (A ∩ (fun σ : S → E ↦ σ (w 1)) ⁻¹' {z})
        = (∑ y, (P ^ n) z y * f y) * α z := by
      intro z
      rw [ih (fun l ↦ w (l + 1)) (fun l hl ↦ hadj (l + 1) (by omega))
        (fun l hl ↦ hpast (l + 1) (by omega)) (fun l hl ↦ hAmeas (l + 1) (by omega)) f hf z,
        mul_comm]
    have hstep := measure_inter_preimage_step hμ hG hmarg htr hαpos (hadj 0 (by omega))
      (hadj 1 (by omega)) (hpast 0 (by omega)) (hAmeas 1 (by omega)) hg x
    rw [hstep, pow_succ']
    congr 1
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

end Chain

/-! ## Georgii's two-block estimate

`|μ(A ∩ C) - μ(A) μ(C)| ≤ max_x ∑_y |P^n(x, y) - α(y)|` for events `A`, `C` separated by a chain
of `n` bonds. Over `ℝ≥0∞` the absolute value is spelled out as the two inequalities below. -/

section TwoBlock

variable {G : SimpleGraph S} [G.LocallyFinite] {μ : Measure (S → E)} [Fintype E] [DecidableEq E]
  {P : Matrix E E ℝ≥0∞} {α : E → ℝ≥0∞} {A B : Set (S → E)}

omit [DecidableEq S] in
/-- **Georgii's two-block estimate** (proof of Theorem (12.31), step 5). If `A` lies beyond every
bond of a non-backtracking chain `w 0, …, w (n + 1)` and `B` lies on the near side of its first
bond, then `μ(A ∩ B)` and `μ(A) μ(B)` differ by at most
`ε ≥ max_x ∑_y |P^n(x, y) - α(y)|`. -/
theorem measure_inter_sub_mul_measure_le [Nonempty E] (hμ : IsMarkovChain G μ) (hG : G.IsTree)
    (hmarg : ∀ (k : S) (x : E), μ ((fun σ : S → E ↦ σ k) ⁻¹' {x}) = α x)
    (htr : ∀ ⦃i j : S⦄, G.Adj i j → ∀ x y : E, transitionProb μ i j x y = P x y)
    (hαpos : ∀ x : E, 0 < α x) (n : ℕ) (w : ℕ → S) (hadj : ∀ l ≤ n, G.Adj (w l) (w (l + 1)))
    (hpast : ∀ l < n, w l ∈ G.past (w (l + 1)) (w (l + 2)))
    (hAmeas : ∀ l ≤ n,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past (w (l + 1)) (w l))] A)
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (G.past (w 0) (w 1))] B)
    {ε : ℝ≥0∞} (hε : ∀ x : E, ∑ y, ((P ^ n) x y - α y) ≤ ε)
    (hε' : ∀ x : E, ∑ y, (α y - (P ^ n) x y) ≤ ε) :
    μ (A ∩ B) ≤ μ A * μ B + ε ∧ μ A * μ B ≤ μ (A ∩ B) + ε := by
  classical
  have hprob := hμ.isProbabilityMeasure
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ (hAmeas 0 (Nat.zero_le n))
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hαtop : ∀ z : E, α z ≠ ⊤ := fun z ↦ by rw [← hmarg (w 0) z]; exact measure_ne_top _ _
  set f : E → ℝ≥0∞ := fun y ↦ μ (A ∩ (fun σ : S → E ↦ σ (w n)) ⁻¹' {y}) / α y with hfdef
  have hf : ∀ y : E, μ (A ∩ (fun σ : S → E ↦ σ (w n)) ⁻¹' {y}) = f y * α y := fun y ↦
    (ENNReal.div_mul_cancel (hαpos y).ne' (hαtop y)).symm
  have hf1 : ∀ y : E, f y ≤ 1 := fun y ↦ by
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul, ← hmarg (w n) y]
    exact measure_mono Set.inter_subset_right
  set g : E → ℝ≥0∞ := fun x ↦ ∑ y, (P ^ n) x y * f y with hgdef
  have hkey : ∀ x : E, μ (A ∩ (fun σ : S → E ↦ σ (w 0)) ⁻¹' {x}) = α x * g x := fun x ↦
    measure_inter_preimage_eq_pow hμ hG hmarg htr hαpos n w hadj hpast hAmeas f hf x
  have hμA : μ A = ∑ y, α y * f y := by
    rw [measure_eq_tsum_inter_preimage μ (w n) hAm, tsum_fintype]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [hf y, mul_comm]
  have hgle : ∀ x : E, g x ≤ μ A + ε := fun x ↦ by
    have h1 : ∑ y, ((P ^ n) x y - α y) * f y ≤ ε :=
      (Finset.sum_le_sum fun y _ ↦ mul_le_of_le_one_right' (hf1 y)).trans (hε x)
    calc g x ≤ ∑ y, (α y + ((P ^ n) x y - α y)) * f y :=
          Finset.sum_le_sum fun y _ ↦ by gcongr; exact le_add_tsub
      _ = (∑ y, α y * f y) + ∑ y, ((P ^ n) x y - α y) * f y := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ ↦ add_mul _ _ _
      _ ≤ μ A + ε := by rw [← hμA]; exact add_le_add le_rfl h1
  have hgge : ∀ x : E, μ A ≤ g x + ε := fun x ↦ by
    have h1 : ∑ y, (α y - (P ^ n) x y) * f y ≤ ε :=
      (Finset.sum_le_sum fun y _ ↦ mul_le_of_le_one_right' (hf1 y)).trans (hε' x)
    calc μ A = ∑ y, α y * f y := hμA
      _ ≤ ∑ y, ((P ^ n) x y + (α y - (P ^ n) x y)) * f y :=
          Finset.sum_le_sum fun y _ ↦ by gcongr; exact le_add_tsub
      _ = g x + ∑ y, (α y - (P ^ n) x y) * f y := by
          rw [hgdef, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ ↦ add_mul _ _ _
      _ ≤ g x + ε := add_le_add le_rfl h1
  have hmB : μ B = ∑ x, μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) := by
    rw [measure_eq_tsum_inter_preimage μ (w 0) hBm, tsum_fintype]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [Set.inter_comm]
  have hmAB : μ (A ∩ B) = ∑ x, g x * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) := by
    rw [hμ.measure_inter_eq_tsum hG (hadj 0 (Nat.zero_le n)) (hAmeas 0 (Nat.zero_le n)) hB,
      tsum_fintype]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hkey x, hmarg (w 0) x, mul_comm (α x) (g x),
      ENNReal.mul_div_cancel_right (hαpos x).ne' (hαtop x)]
  constructor
  · calc μ (A ∩ B) = ∑ x, g x * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) := hmAB
      _ ≤ ∑ x, (μ A + ε) * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) :=
          Finset.sum_le_sum fun x _ ↦ by gcongr; exact hgle x
      _ = (μ A + ε) * μ B := by rw [hmB, Finset.mul_sum]
      _ = μ A * μ B + ε * μ B := by rw [add_mul]
      _ ≤ μ A * μ B + ε := add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)
  · calc μ A * μ B = ∑ x, μ A * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) := by
          rw [hmB, Finset.mul_sum]
      _ ≤ ∑ x, (g x + ε) * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) :=
          Finset.sum_le_sum fun x _ ↦ by gcongr; exact hgge x
      _ = (∑ x, g x * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B))
            + ∑ x, ε * μ ((fun σ : S → E ↦ σ (w 0)) ⁻¹' {x} ∩ B) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ ↦ add_mul _ _ _
      _ = μ (A ∩ B) + ε * μ B := by rw [← hmAB, ← Finset.mul_sum, ← hmB]
      _ ≤ μ (A ∩ B) + ε := add_le_add le_rfl (mul_le_of_le_one_right' prob_le_one)

end TwoBlock

end MeasureTheory.GibbsMeasure.Tree

end
