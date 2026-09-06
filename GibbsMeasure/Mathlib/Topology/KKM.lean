/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.Sperner
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# The Knaster–Kuratowski–Mazurkiewicz lemma

If the standard simplex `stdSimplex ℝ (Fin N)` is covered by closed sets `K_1, …, K_N`, each of
which avoids the face where its own coordinate vanishes, then the `K_n` have a common point.

This is the topological consequence of Sperner's lemma (`Sperner.exists_isPanchromatic`), and it
is Lemma (19.12) of Georgii, *Gibbs Measures and Phase Transitions*, whose proof (his 19.A4) is
the one carried out here: for every mesh `ℓ` an admissible colouring of the grid of `ℓ⁻¹ℤ^N ∩ 𝒫_N`
is obtained by painting a grid point with an index of a member of the cover containing it, a
panchromatic cell provides `N` points of the simplex within `2/ℓ` of one another with the `n`-th
in `K_n`, and a cluster point of these as `ℓ → ∞` lies in every `K_n` by closedness.

## Main results

* `Sperner.bary` — the barycentric coordinates of a staircase grid point, the bridge from the
  combinatorial statement to the simplex; `Sperner.bary_mem_stdSimplex` puts them in the simplex,
  `Sperner.isAdmissibleAt_of_bary_ne_zero` turns "the `n`-th coordinate is nonzero" into
  admissibility of the colour `n`, and `Sperner.abs_bary_vertex_sub_le` is the mesh bound
  `|α_n - α'_n| ≤ 2/ℓ` for two vertices of one cell.
* `nonempty_iInter_of_isClosed_of_stdSimplex_subset_iUnion` — **the KKM lemma**, Georgii (19.12).
* `exists_mem_stdSimplex_forall_exists` — the selection principle it is used through in Georgii's
  Proposition (19.13): if `Γ` assigns a non-empty set of states to each `α` of the simplex,
  `q_0, …, q_d` sum to `1` on every state, the parameters admitting a state with
  `q_n ≥ (d+1)⁻¹` form a closed set, and no such state exists when `α_n = 0`, then some `α`
  admits such a state for *every* `n` at once.

-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Sperner

variable {d ℓ : ℕ}

/-! ### From staircase coordinates to the simplex -/

/-- The barycentric coordinates of a staircase point of mesh `ℓ`: the successive increments of
its profile, divided by `ℓ`. -/
noncomputable def bary (ℓ : ℕ) {d : ℕ} (y : Fin d → ℤ) : Fin (d + 1) → ℝ :=
  fun n ↦ ((profile ℓ y ((n : ℕ) + 1) - profile ℓ y (n : ℕ) : ℤ) : ℝ) / (ℓ : ℝ)

lemma bary_nonneg {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (n : Fin (d + 1)) : 0 ≤ bary ℓ y n := by
  refine div_nonneg ?_ (Nat.cast_nonneg ℓ)
  have := hy.profile_mono (m := (n : ℕ)) (n := (n : ℕ) + 1) (Nat.le_succ _)
  exact_mod_cast sub_nonneg.2 this

lemma sum_bary (hℓ : 1 ≤ ℓ) (y : Fin d → ℤ) : ∑ n, bary ℓ y n = 1 := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hg : ∀ n : Fin (d + 1), bary ℓ y n
      = (((profile ℓ y ((n : ℕ) + 1) : ℤ) : ℝ) - ((profile ℓ y (n : ℕ) : ℤ) : ℝ)) / (ℓ : ℝ) := by
    intro n; simp only [bary]; push_cast; ring
  rw [Finset.sum_congr rfl fun n _ ↦ hg n,
    Fin.sum_univ_eq_sum_range
      (fun n ↦ (((profile ℓ y (n + 1) : ℤ) : ℝ) - ((profile ℓ y n : ℤ) : ℝ)) / (ℓ : ℝ)) (d + 1),
    ← Finset.sum_div, Finset.sum_range_sub (fun n ↦ ((profile ℓ y n : ℤ) : ℝ)) (d + 1),
    profile_zero, profile_succ_of_le y le_rfl]
  push_cast
  rw [sub_zero, div_self hℓ0.ne']

lemma bary_mem_stdSimplex (hℓ : 1 ≤ ℓ) {y : Fin d → ℤ} (hy : IsGridPt ℓ y) :
    bary ℓ y ∈ stdSimplex ℝ (Fin (d + 1)) :=
  ⟨bary_nonneg hy, sum_bary hℓ y⟩

lemma isAdmissibleAt_of_bary_ne_zero (hℓ : 1 ≤ ℓ) {y : Fin d → ℤ} (hy : IsGridPt ℓ y)
    {n : Fin (d + 1)} (hn : bary ℓ y n ≠ 0) : IsAdmissibleAt ℓ y (n : ℕ) := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hle := hy.profile_mono (m := (n : ℕ)) (n := (n : ℕ) + 1) (Nat.le_succ _)
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact absurd (by simp [bary, ← heq]) hn
  · exact hlt

/-- Two vertices of the same cell have profiles differing by at most one. -/
lemma abs_profile_vertex_sub_le (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k k' n : ℕ) :
    |profile ℓ (vertex y σ k) n - profile ℓ (vertex y σ k') n| ≤ 1 := by
  cases n with
  | zero => simp
  | succ m =>
    by_cases h : m < d
    · rw [profile_succ_of_lt _ h, profile_succ_of_lt _ h]
      simp only [vertex]
      rw [abs_le]
      constructor <;> (split_ifs <;> omega)
    · rw [profile_succ_of_le _ (Nat.not_lt.1 h), profile_succ_of_le _ (Nat.not_lt.1 h)]
      simp

lemma abs_bary_vertex_sub_le (hℓ : 1 ≤ ℓ) (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k k' : ℕ)
    (m : Fin (d + 1)) :
    |bary ℓ (vertex y σ k) m - bary ℓ (vertex y σ k') m| ≤ 2 / (ℓ : ℝ) := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have h1 := abs_profile_vertex_sub_le (ℓ := ℓ) y σ k k' ((m : ℕ) + 1)
  have h2 := abs_profile_vertex_sub_le (ℓ := ℓ) y σ k k' (m : ℕ)
  rw [abs_le] at h1 h2
  set A : ℤ := profile ℓ (vertex y σ k) ((m : ℕ) + 1) - profile ℓ (vertex y σ k) (m : ℕ) with hA
  set B : ℤ := profile ℓ (vertex y σ k') ((m : ℕ) + 1) - profile ℓ (vertex y σ k') (m : ℕ) with hB
  have hAB : |A - B| ≤ 2 := by rw [abs_le]; omega
  have hnum : |((A : ℝ)) - ((B : ℝ))| ≤ 2 := by
    have : |((A - B : ℤ) : ℝ)| ≤ ((2 : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hAB
    push_cast at this
    exact this
  have heq : bary ℓ (vertex y σ k) m - bary ℓ (vertex y σ k') m
      = ((A : ℝ) - (B : ℝ)) / (ℓ : ℝ) := by
    simp only [bary, hA, hB]
    push_cast
    ring
  rw [heq, abs_div, abs_of_pos hℓ0]
  exact div_le_div_of_nonneg_right hnum hℓ0.le

end Sperner

/-! ### The Knaster–Kuratowski–Mazurkiewicz lemma -/

/-- **The Knaster–Kuratowski–Mazurkiewicz lemma**, Georgii (19.12).  Let `K_0, …, K_d` be closed
subsets of the standard simplex `𝒫_{d+1} = stdSimplex ℝ (Fin (d+1))` which cover it and are such
that `K_n` misses the face `{α : α_n = 0}`.  Then `⋂_n K_n ≠ ∅`.

The proof is Georgii's (19.A4): for each mesh `ℓ` paint every grid point with an index of a
member of the cover containing it — this is admissible exactly because `K_n` misses the `n`-th
face — read off a panchromatic cell from Sperner's lemma, and pass to a cluster point of its
vertices as `ℓ → ∞`. -/
theorem nonempty_iInter_of_isClosed_of_stdSimplex_subset_iUnion {d : ℕ}
    {K : Fin (d + 1) → Set (Fin (d + 1) → ℝ)} (hKcl : ∀ n, IsClosed (K n))
    (hKsub : ∀ n, K n ⊆ stdSimplex ℝ (Fin (d + 1)))
    (hcover : stdSimplex ℝ (Fin (d + 1)) ⊆ ⋃ n, K n)
    (hface : ∀ n, ∀ α ∈ K n, α n ≠ 0) :
    (⋂ n, K n).Nonempty := by
  classical
  have key : ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ a : Fin (d + 1) → (Fin (d + 1) → ℝ),
      (∀ n, a n ∈ K n) ∧ ∀ n n' (m : Fin (d + 1)), |a n m - a n' m| ≤ 2 / (ℓ : ℝ) := by
    intro ℓ hℓ
    have hex : ∀ y : Fin d → ℤ, Sperner.IsGridPt ℓ y →
        ∃ n : Fin (d + 1), Sperner.bary ℓ y ∈ K n := by
      intro y hy
      simpa using hcover (Sperner.bary_mem_stdSimplex hℓ hy)
    set φ : (Fin d → ℤ) → ℕ := fun y ↦
      if h : ∃ n : Fin (d + 1), Sperner.bary ℓ y ∈ K n then ((h.choose : Fin (d + 1)) : ℕ) else 0
      with hφdef
    have hval : ∀ y : Fin d → ℤ, ∀ h : ∃ n : Fin (d + 1), Sperner.bary ℓ y ∈ K n,
        φ y = ((h.choose : Fin (d + 1)) : ℕ) := by
      intro y h
      rw [hφdef]
      simp only [dif_pos h]
    have hφadm : Sperner.IsAdmissible ℓ φ := by
      intro y hy
      rw [hval y (hex y hy)]
      exact Sperner.isAdmissibleAt_of_bary_ne_zero hℓ hy
        (hface _ _ (hex y hy).choose_spec)
    obtain ⟨y, σ, hcell, hpan⟩ := Sperner.exists_isPanchromatic hℓ d φ hφadm
    choose j hj using fun n : Fin (d + 1) ↦ hpan (n : ℕ) (Nat.lt_succ_iff.1 n.isLt)
    refine ⟨fun n ↦ Sperner.bary ℓ (Sperner.vertex y σ ((j n : Fin (d + 1)) : ℕ)),
      fun n ↦ ?_, fun n n' m ↦ Sperner.abs_bary_vertex_sub_le hℓ y σ _ _ m⟩
    change Sperner.bary ℓ (Sperner.vertex y σ ((j n : Fin (d + 1)) : ℕ)) ∈ K n
    have hgrid := hcell.isGridPt_vertex ((j n : Fin (d + 1)) : ℕ)
    have h := hex _ hgrid
    have heq : h.choose = n := Fin.ext (by rw [← hval _ h, hj n])
    have hs := h.choose_spec
    rwa [heq] at hs
  choose a ha hdist using fun ℓ : ℕ ↦ key (ℓ + 1) (Nat.le_add_left 1 ℓ)
  have hcpt : IsCompact (stdSimplex ℝ (Fin (d + 1))) := isCompact_stdSimplex ℝ (Fin (d + 1))
  obtain ⟨α, -, ψ, hψ, hlim⟩ := hcpt.tendsto_subseq (x := fun ℓ ↦ a ℓ 0)
    (fun ℓ ↦ hKsub 0 (ha ℓ 0))
  refine ⟨α, Set.mem_iInter.2 fun n ↦ ?_⟩
  refine (hKcl n).mem_of_tendsto (f := fun k ↦ a (ψ k) n)
    (b := (Filter.atTop : Filter ℕ)) ?_ (Filter.Eventually.of_forall fun k ↦ ha (ψ k) n)
  rw [tendsto_pi_nhds]
  intro m
  have h0 : Filter.Tendsto (fun k ↦ a (ψ k) 0 m) Filter.atTop (𝓝 (α m)) :=
    (tendsto_pi_nhds.1 hlim) m
  have hbnd : Filter.Tendsto (fun k : ℕ ↦ (2 : ℝ) / ((ψ k + 1 : ℕ) : ℝ)) Filter.atTop (𝓝 0) := by
    refine (tendsto_const_div_atTop_nhds_zero_nat 2).comp ?_
    refine Filter.tendsto_atTop_mono (fun k ↦ ?_) Filter.tendsto_id
    exact le_trans hψ.le_apply (Nat.le_succ _)
  have hdiff : Filter.Tendsto (fun k : ℕ ↦ a (ψ k) n m - a (ψ k) 0 m) Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ ↦ -((2 : ℝ) /
      ((ψ k + 1 : ℕ) : ℝ))) (h := fun k : ℕ ↦ (2 : ℝ) / ((ψ k + 1 : ℕ) : ℝ))
      (by simpa using hbnd.neg) hbnd (fun k ↦ ?_) (fun k ↦ ?_)
    · have := hdist (ψ k) n 0 m
      rw [abs_le] at this
      exact this.1
    · have := hdist (ψ k) n 0 m
      rw [abs_le] at this
      exact this.2
  simpa using hdiff.add h0

/-- **The selection principle behind Georgii's Proposition (19.13), Step 1.**

Let `Γ` assign to each point `α` of the simplex a non-empty set of *states*, and let
`q_0, …, q_d` be quantities summing to `1` on every state.  Suppose that for each `n` the set of
parameters `α` admitting a state with `q_n ≥ (d+1)⁻¹` is closed, and that no such state exists
when `α_n = 0`.  Then some parameter `α` admits, *simultaneously for every `n`*, a state with
`q_n ≥ (d+1)⁻¹`.

Georgii applies this with `Γ(α)` a set of Gibbs measures for the potential `Ψ^α` and
`q_n(μ) = μ(0 ∈ V(G_n, ·) | 0 ∈ V(G, ·))`; the closedness is his hypothesis (19.13)(i)
(countable compactness of `Γ` in the topology of local convergence, which makes each `q_n` upper
semicontinuous along `Γ` because it is defined by local events), and the boundary condition is
his hypothesis (19.13)(iii). -/
theorem exists_mem_stdSimplex_forall_exists {d : ℕ} {X : Type*}
    {Γ : (Fin (d + 1) → ℝ) → Set X} {q : Fin (d + 1) → X → ℝ}
    (hΓ : ∀ α ∈ stdSimplex ℝ (Fin (d + 1)), (Γ α).Nonempty)
    (hsum : ∀ α ∈ stdSimplex ℝ (Fin (d + 1)), ∀ μ ∈ Γ α, ∑ n, q n μ = 1)
    (hclosed : ∀ n : Fin (d + 1), IsClosed {α ∈ stdSimplex ℝ (Fin (d + 1)) |
      ∃ μ ∈ Γ α, ((d : ℝ) + 1)⁻¹ ≤ q n μ})
    (hface : ∀ (n : Fin (d + 1)) (α : Fin (d + 1) → ℝ), α ∈ stdSimplex ℝ (Fin (d + 1)) →
      α n = 0 → ∀ μ ∈ Γ α, q n μ < ((d : ℝ) + 1)⁻¹) :
    ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∀ n, ∃ μ ∈ Γ α, ((d : ℝ) + 1)⁻¹ ≤ q n μ := by
  classical
  set K : Fin (d + 1) → Set (Fin (d + 1) → ℝ) := fun n ↦
    {α ∈ stdSimplex ℝ (Fin (d + 1)) | ∃ μ ∈ Γ α, ((d : ℝ) + 1)⁻¹ ≤ q n μ} with hK
  have hpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hKsub : ∀ n, K n ⊆ stdSimplex ℝ (Fin (d + 1)) := fun n α hα ↦ hα.1
  have hcover : stdSimplex ℝ (Fin (d + 1)) ⊆ ⋃ n, K n := by
    intro α hα
    obtain ⟨μ, hμ⟩ := hΓ α hα
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hlt : ∀ n : Fin (d + 1), q n μ < ((d : ℝ) + 1)⁻¹ := by
      intro n
      by_contra hle
      exact hcon n ⟨hα, μ, hμ, not_lt.1 hle⟩
    have hsum' : ∑ n : Fin (d + 1), q n μ < ∑ _n : Fin (d + 1), ((d : ℝ) + 1)⁻¹ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun n _ ↦ hlt n
    rw [hsum α hα μ hμ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum'
    rw [Nat.cast_add, Nat.cast_one, mul_inv_cancel₀ hpos.ne'] at hsum'
    exact absurd hsum' (lt_irrefl 1)
  have hfaceK : ∀ n, ∀ α ∈ K n, α n ≠ 0 := by
    intro n α hα hn
    obtain ⟨hmem, μ, hμ, hle⟩ := hα
    exact absurd (hface n α hmem hn μ hμ) (not_lt.2 hle)
  obtain ⟨α, hα⟩ :=
    nonempty_iInter_of_isClosed_of_stdSimplex_subset_iUnion hclosed hKsub hcover hfaceK
  rw [Set.mem_iInter] at hα
  exact ⟨α, (hα 0).1, fun n ↦ (hα n).2⟩
