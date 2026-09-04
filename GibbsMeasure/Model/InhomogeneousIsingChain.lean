/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Tanh.InfiniteProd
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Potential.Pair
public import GibbsMeasure.Specification.ExtremeCorollaries
public import GibbsMeasure.Topology.LocalMetric
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Georgii §6.1: inhomogeneous Ising chains

Sites `S = ℕ`, spins `E = Bool` (`spin true = 1`, `spin false = -1`), a priori measure the
uniform (equivalently, up to normalisation, the counting) measure, and the *inhomogeneous*
nearest-neighbour potential of Georgii (6.2)

`Φ_{n, n+1}(σ) = -J n · σ_n σ_{n+1}`, `Φ_A = 0` otherwise,

with couplings `J n > 0` satisfying Georgii (6.1), `∑_n e^{-2 J n} < ∞`.

The potential is the existing general pair potential `Potential.pair` of Georgii (9.10)
(`GibbsMeasure/Potential/Pair.lean`) — *not* `isingPotential`, whose coupling is a single
constant, and not Chapter 11's `transferSpecification`, which is homogeneous, lives on `ℤ`
and would give a second (matrix-shaped) copy of the model. `Potential.pair` is the only object
in the tree that carries a site-dependent coupling.  The specification is the general Gibbsian
`gibbsSpecificationOfAbsolutelySummable` at inverse temperature `1`; `γ^{βΦ}` is the chain with
couplings `βJ`, so no separate `β` is carried.

Georgii's volumes `Λ_N = {1, …, N}` are `Finset.range N = {0, …, N-1}` here, with `N` as the
adjacent boundary site; Georgii's `∏_{i=n}^N tanh J_i` is `∏ i ∈ Finset.Ico n N, tanh (J i)`.

## Main results

* `isingChainPotential`, `isingChainSpecification`: Georgii (6.2) and Definition (2.9) for it.
* `hamiltonian_isingChainPotential_range`: `H_{Λ_N} = -∑_{i<N} J_i σ_i σ_{i+1}`.
* `chainZ_eq_prod`, `chainMag_eq`: the finite-volume partition function `Z_N = ∏_{i<N} 2 cosh J_i`
  and the (unnormalised) magnetisation `∑_ζ σ_n e^{-H} = ω_N ∏_{n ≤ i < N} tanh J_i · Z_N`.
* `isingChainSpecification_range_apply_setOf_eq`: **Lemma (6.5)**.
* `isingChainSpecification_range_apply_eq_sum`, `isingChainSpecification_range_apply_eq`:
  **(6.6)**, the decomposition over the spin at the site `n`.
* `chainFlip`, `map_chainFlip_isingChainPotential`, `isInvariant_chainFlip`: **(6.3)**.
* `exists_G_isingChainSpecification_eq`: **Theorem (6.4)**, `𝒢(Φ) = [μ₋, μ₊]` with
  `μ₋ = τ(μ₊)`, `μ₊(σ_n) > 0 > μ₋(σ_n)` and `μ₊ ≠ μ₋`, in both directions.
* `exists_G_eq_singleton_of_not_summable`: **Comment (6.7)(2)**, `|𝒢(Φ)| = 1` when (6.1) fails,
  so (6.1) is necessary as well as sufficient.
* `plusPhase`, `minusPhase`: Georgii's `μ₊ = lim_N γ_{Λ_N}(· | ω⁺)` and `μ₋ = τ(μ₊)` as named
  objects, with `G_isingChainSpecification_eq` (Theorem (6.4) in terms of them) and
  `integral_spin_plusPhase`: `μ₊(σ_n) = ∏_{i ≥ n} tanh J_i`.
* **Comment (6.7)(1)**: `isingChainPotential_constConfig_le` (`ω^±` are ground states),
  `exists_G_gibbsSpecification_smul_eq` (`𝒢(βΦ) = [μ₋^β, μ₊^β]` for `β ≥ 1`),
  `tendsto_tprod_tanh_smul_atTop` and `tendsto_integral_spin_plusPhase_smul_atTop`
  (`μ₊^β(σ_n) = ∏_{i ≥ n} tanh βJ_i → 1`), `tendsto_localDist_plusPhase_smul_atTop` and
  `tendsto_localDist_minusPhase_smul_atTop` (`μ₊^β → δ₊`, `μ₋^β → δ₋` locally), and
  `lim_{β → ∞} 𝒢(βΦ) = [δ₋, δ₊]` in three forms: the endpoints
  (`tendsto_localDistSet_GP_gibbsSpecification_dirac`), the whole segment pointwise
  (`tendsto_smul_plusPhase_add_smul_minusPhase_atTop`), and the reverse inclusion — every local
  limit of Gibbs measures `μ^β ∈ 𝒢(βΦ)` lies in `[δ₋, δ₊]`
  (`exists_eq_smul_dirac_add_smul_dirac_of_tendsto`).
* **Comment (6.7)(3)**: `measurableSet_tail_eventuallyConst` (`A₊`, `A₋` are tail events),
  `plusPhase_apply_eventuallyConst_true`, `minusPhase_apply_eventuallyConst_false`
  (`μ₊(A₊) = μ₋(A₋) = 1`), `plusPhase_mem_extremePoints_G`, `minusPhase_mem_extremePoints_G`
  (`μ₊`, `μ₋` are the extreme points), the random graph `chainGraph` with its two descriptions
  (`chainGraph_adj_iff_forall_le`), the percolation characterisation
  `mem_eventuallyConst_union_iff_existsUnique_infinite_supp` of `A₊ ∪ A₋`, and
  `apply_setOf_exists_infinite_supp_eq_one`: every Gibbs measure percolates.

The analysis of the tail products `∏_{i ≥ n} tanh J_i` under (6.1) lives in
`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/Tanh/InfiniteProd.lean`.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure Potential ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable (J : ℕ → ℝ)

/-! ### The potential (6.2) -/

/-- The pair interaction of Georgii (6.2): `φ_{n,n+1}(x, y) = -J n · spin x · spin y`, and `0`
for every other pair of sites. -/
def isingChainPair (i j : ℕ) (x y : Bool) : ℝ :=
  if j = i + 1 then -J i * (spin x * spin y) else 0

variable {J}

lemma isingChainPair_succ (i : ℕ) (x y : Bool) :
    isingChainPair J i (i + 1) x y = -J i * (spin x * spin y) := by
  simp [isingChainPair]

lemma isingChainPair_of_ne {i j : ℕ} (hj : j ≠ i + 1) (x y : Bool) :
    isingChainPair J i j x y = 0 := by
  simp [isingChainPair, hj]

lemma abs_isingChainPair_le (i j : ℕ) (x y : Bool) : |isingChainPair J i j x y| ≤ |J i| := by
  unfold isingChainPair
  split_ifs with h
  · rw [abs_mul, abs_neg, abs_mul]
    calc |J i| * (|spin x| * |spin y|) ≤ |J i| * (1 * 1) := by
          gcongr <;> [exact abs_spin_le x; exact abs_spin_le y]
      _ = |J i| := by ring
  · simp [abs_nonneg]

variable (J)

/-- **Georgii (6.2).** The inhomogeneous nearest-neighbour Ising potential on `ℕ`. -/
def isingChainPotential : Potential ℕ Bool := Potential.pair (isingChainPair J)

instance isPotential_isingChainPotential : IsPotential (isingChainPotential J) :=
  isPotential_pair _ fun _ _ ↦ Measurable.of_discrete

instance isFiniteRange_isingChainPotential : IsFiniteRange (isingChainPotential J) :=
  isFiniteRange_pair (fun i ↦ Finset.Icc (i - 1) (i + 1)) (fun i ↦ by simp)
    fun i j _ ⟨x, y, hxy⟩ ↦ by
      have hj : j = i + 1 := by
        by_contra h
        exact hxy (isingChainPair_of_ne h x y)
      subst hj
      simp only [Finset.mem_Icc]
      omega

instance isAbsolutelySummable_isingChainPotential :
    IsAbsolutelySummable (isingChainPotential J) :=
  IsAbsolutelySummable.of_isFiniteRange (iSup_enorm_pair_ne_top fun i j _ ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup₂_le fun x y ↦ by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_isingChainPair_le i j x y)))

/-- **Scaling the couplings scales the potential**: `Φ^{βJ} = β Φ^J`, so the inhomogeneous
chain at inverse temperature `β` is the chain with couplings `βJ` at `β = 1`
(`Potential.gibbsSpecificationOfAbsolutelySummable_smul`). -/
lemma isingChainPotential_smul (β : ℝ) :
    isingChainPotential (β • J) = β • isingChainPotential J := by
  rw [isingChainPotential, isingChainPotential, ← Potential.pair_smul]
  congr 1
  funext i j x y
  simp only [isingChainPair, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-! ### The Hamiltonian of an initial interval

Georgii's volumes are `Λ_N = {1, …, N}`; with `ℕ` indexed from `0` they are `Finset.range N`,
and the boundary site adjacent to `Λ_N` is `N`.  The bonds meeting `Λ_N` are exactly
`{i, i+1}` for `i < N`. -/

lemma not_disjoint_pair_range {i N : ℕ} (hi : i < N) :
    ¬ Disjoint ({i, i + 1} : Finset ℕ) (Finset.range N) :=
  Finset.not_disjoint_iff.2 ⟨i, Finset.mem_insert_self _ _, Finset.mem_range.2 hi⟩

/-- **The Hamiltonian of the inhomogeneous Ising chain in an initial interval.**
`H_{Λ_N}(σ) = -∑_{i < N} J_i σ_i σ_{i+1}`; the bond `{N, N+1}` and all later ones do not meet
`Λ_N = {0, …, N-1}`, whereas the boundary bond `{N-1, N}` does. -/
theorem hamiltonian_isingChainPotential_range (N : ℕ) (σ : ℕ → Bool) :
    (isingChainPotential J).hamiltonian (Finset.range N) σ
      = -∑ i ∈ Finset.range N, J i * (spin (σ i) * spin (σ (i + 1))) := by
  classical
  set g : ℕ → ℕ → ℝ := fun i j ↦
    if ¬ Disjoint ({i, j} : Finset ℕ) (Finset.range N) then isingChainPair J i j (σ i) (σ j)
      else 0 with hg
  have hterms : ∀ A : Finset ℕ,
      (isingChainPotential J).hamiltonianTerms (Finset.range N) σ A = pairTerms g A :=
    fun A ↦ hamiltonianTerms_pair (isingChainPair J) (Finset.range N) σ A
  rw [hamiltonian_eq_tsum, tsum_congr hterms, tsum_pairTerms]
  have hzero : ∀ q : ℕ × ℕ, q ∉ (Finset.range N).image (fun i ↦ (i, i + 1)) →
      (if q.1 < q.2 then g q.1 q.2 else 0) = 0 := by
    rintro ⟨a, b⟩ hq
    simp only
    split_ifs with hab
    · rw [hg]
      simp only
      by_cases hd : Disjoint ({a, b} : Finset ℕ) (Finset.range N)
      · rw [ite_eq_right (not_not.2 hd)]
      · rw [ite_eq_left hd]
        by_cases hb : b = a + 1
        · subst hb
          refine absurd (Finset.mem_image.2 ⟨a, Finset.mem_range.2 ?_, rfl⟩) hq
          obtain ⟨x, hx, hxN⟩ := Finset.not_disjoint_iff.1 hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_range] at hxN
          rcases hx with rfl | rfl <;> omega
        · exact isingChainPair_of_ne hb _ _
    · rfl
  rw [tsum_eq_sum hzero, Finset.sum_image (by intro i _ j _ h; simpa using h),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [hg]
  rw [ite_eq_left (Nat.lt_succ_self i),
    ite_eq_left (not_disjoint_pair_range (Finset.mem_range.1 hi)), isingChainPair_succ]
  ring

/-! ### The finite-volume weights and their transfer recursion

The Boltzmann weight of the bonds inside `Λ_N = {0, …, N-1}` is `exp(∑_{i<N} J_i σ_i σ_{i+1})`;
it depends on `σ` only through `σ_0, …, σ_N`. Summing it over the spins in `Λ_N` with the
boundary spin `b` at the site `N` gives the partition function `Z_N(b)`, and inserting a factor
`σ_n` gives the (unnormalised) magnetisation `M_N(n, b)`. Both are computed by peeling off the
site `N`, which is Georgii's transfer-matrix step. -/

/-- `exp(∑_{i<N} J_i σ_i σ_{i+1})`, the Boltzmann factor of the volume `Λ_N = {0, …, N-1}`. -/
def chainWeight (N : ℕ) (σ : ℕ → Bool) : ℝ :=
  Real.exp (∑ i ∈ Finset.range N, J i * (spin (σ i) * spin (σ (i + 1))))

variable {J}

lemma chainWeight_pos (N : ℕ) (σ : ℕ → Bool) : 0 < chainWeight J N σ := Real.exp_pos _

lemma chainWeight_congr {N : ℕ} {σ τ : ℕ → Bool} (h : ∀ i ≤ N, σ i = τ i) :
    chainWeight J N σ = chainWeight J N τ := by
  unfold chainWeight
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [h i hi.le, h (i + 1) hi]

/-- `exp(-H_{Λ_N})` is the chain weight: the Boltzmann factor at inverse temperature `1`. -/
lemma exp_neg_hamiltonian_range (N : ℕ) (σ : ℕ → Bool) :
    Real.exp (-(isingChainPotential J).hamiltonian (Finset.range N) σ) = chainWeight J N σ := by
  rw [hamiltonian_isingChainPotential_range, neg_neg, chainWeight]

variable (J)

/-- The partition function of `Λ_N` with constant boundary spin `b` (only the spin at the site
`N` enters, see `sum_chainWeight_juxt`). -/
def chainZ (N : ℕ) (b : Bool) : ℝ :=
  ∑ ζ : (Finset.range N) → Bool,
    chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) (fun _ ↦ b) ζ)

/-- The unnormalised magnetisation at the site `n` in the volume `Λ_N` with boundary spin `b`. -/
def chainMag (N n : ℕ) (b : Bool) : ℝ :=
  ∑ ζ : (Finset.range N) → Bool,
    spin (juxt ((Finset.range N : Finset ℕ) : Set ℕ) (fun _ ↦ b) ζ n) *
      chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) (fun _ ↦ b) ζ)

variable {J}

/-! #### Peeling off the site `N` -/

/-- A configuration on `{0, …, N-1}` together with a spin at `N`, as a configuration on
`{0, …, N}`. -/
def chainSnoc (N : ℕ) (x : Bool) (v : (Finset.range N) → Bool)
    (i : (Finset.range (N + 1))) : Bool :=
  if h : (i : ℕ) < N then v ⟨(i : ℕ), Finset.mem_range.2 h⟩ else x

lemma chainSnoc_of_lt {N : ℕ} (x : Bool) (v : (Finset.range N) → Bool)
    {i : (Finset.range (N + 1))} (h : (i : ℕ) < N) :
    chainSnoc N x v i = v ⟨(i : ℕ), Finset.mem_range.2 h⟩ := dite_eq_left h

lemma chainSnoc_of_not_lt {N : ℕ} (x : Bool) (v : (Finset.range N) → Bool)
    {i : (Finset.range (N + 1))} (h : ¬ (i : ℕ) < N) : chainSnoc N x v i = x := dite_eq_right h

/-- Configurations on `{0, …, N}` are a spin at `N` together with a configuration on
`{0, …, N-1}`. -/
def chainSnocEquiv (N : ℕ) :
    Bool × ((Finset.range N) → Bool) ≃ ((Finset.range (N + 1)) → Bool) where
  toFun p := chainSnoc N p.1 p.2
  invFun u := (u ⟨N, Finset.mem_range.2 (Nat.lt_succ_self N)⟩,
    fun i ↦ u ⟨(i : ℕ), Finset.mem_range.2 (by
      have := Finset.mem_range.1 i.2; omega)⟩)
  left_inv := by
    rintro ⟨x, v⟩
    rw [Prod.mk.injEq]
    exact ⟨chainSnoc_of_not_lt x v (lt_irrefl N),
      funext fun i ↦ chainSnoc_of_lt x v (Finset.mem_range.1 i.2)⟩
  right_inv u := by
    funext i
    change chainSnoc N _ _ i = u i
    by_cases h : (i : ℕ) < N
    · exact chainSnoc_of_lt _ _ h
    · rw [chainSnoc_of_not_lt _ _ h]
      have := Finset.mem_range.1 i.2
      refine congrArg u (Subtype.ext ?_)
      simp only []
      omega

lemma sum_chainSnoc (N : ℕ) (f : ((Finset.range (N + 1)) → Bool) → ℝ) :
    ∑ u : (Finset.range (N + 1)) → Bool, f u
      = ∑ x : Bool, ∑ v : (Finset.range N) → Bool, f (chainSnoc N x v) :=
  ((chainSnocEquiv N).sum_comp f).symm.trans (Fintype.sum_prod_type _)

lemma juxt_chainSnoc_of_le {N : ℕ} (b x : Bool) (v : (Finset.range N) → Bool) {i : ℕ}
    (hi : i ≤ N) :
    juxt ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) (fun _ ↦ b) (chainSnoc N x v) i
      = juxt ((Finset.range N : Finset ℕ) : Set ℕ) (fun _ ↦ x) v i := by
  rcases lt_or_eq_of_le hi with hi' | rfl
  · rw [juxt_apply_of_mem (by simpa using hi'.trans (Nat.lt_succ_self N)),
      juxt_apply_of_mem (by simpa using hi')]
    exact chainSnoc_of_lt _ _ hi'
  · rw [juxt_apply_of_mem (by simp), juxt_apply_of_not_mem (by simp)]
    exact chainSnoc_of_not_lt _ _ (lt_irrefl i)

lemma juxt_chainSnoc_succ {N : ℕ} (b x : Bool) (v : (Finset.range N) → Bool) :
    juxt ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) (fun _ ↦ b) (chainSnoc N x v) (N + 1) = b :=
  juxt_apply_of_not_mem (by simp) _

lemma chainWeight_juxt_chainSnoc {N : ℕ} (b x : Bool) (v : (Finset.range N) → Bool) :
    chainWeight J (N + 1)
        (juxt ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) (fun _ ↦ b) (chainSnoc N x v))
      = Real.exp (J N * (spin x * spin b)) *
          chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) (fun _ ↦ x) v) := by
  unfold chainWeight
  rw [Finset.sum_range_succ, ← Real.exp_add, add_comm]
  congr 2
  · rw [juxt_chainSnoc_of_le b x v le_rfl, juxt_chainSnoc_succ b x v,
      juxt_apply_of_not_mem (by simp)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [juxt_chainSnoc_of_le b x v hi.le, juxt_chainSnoc_of_le b x v hi]

/-! #### The two Bool sums -/

lemma sum_bool_exp (t : ℝ) (b : Bool) :
    ∑ x : Bool, Real.exp (t * (spin x * spin b)) = 2 * Real.cosh t := by
  rw [Fintype.sum_bool, Real.cosh_eq]
  cases b <;> simp [spin] <;> ring

lemma sum_bool_spin_exp (t : ℝ) (b : Bool) :
    ∑ x : Bool, spin x * Real.exp (t * (spin x * spin b)) = spin b * (2 * Real.sinh t) := by
  rw [Fintype.sum_bool, Real.sinh_eq]
  cases b <;> simp [spin] <;> ring

/-! #### The transfer recursions and their closed forms -/

lemma chainZ_succ (N : ℕ) (b : Bool) :
    chainZ J (N + 1) b = ∑ x : Bool, Real.exp (J N * (spin x * spin b)) * chainZ J N x := by
  rw [chainZ, sum_chainSnoc]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [chainZ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ ↦ chainWeight_juxt_chainSnoc b x v

lemma chainMag_succ_of_lt {N n : ℕ} (hn : n < N) (b : Bool) :
    chainMag J (N + 1) n b
      = ∑ x : Bool, Real.exp (J N * (spin x * spin b)) * chainMag J N n x := by
  rw [chainMag, sum_chainSnoc]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [chainMag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [chainWeight_juxt_chainSnoc b x v, juxt_chainSnoc_of_le b x v hn.le]
  ring

lemma chainMag_succ_self (N : ℕ) (b : Bool) :
    chainMag J (N + 1) N b
      = ∑ x : Bool, spin x * Real.exp (J N * (spin x * spin b)) * chainZ J N x := by
  rw [chainMag, sum_chainSnoc]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [chainZ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [chainWeight_juxt_chainSnoc b x v, juxt_chainSnoc_of_le b x v le_rfl,
    juxt_apply_of_not_mem (by simp)]
  ring

/-- **The partition function of an initial interval**: `Z_N(b) = ∏_{i<N} 2 cosh J_i`, in
particular independent of the boundary spin `b` (Georgii, the "similar but simpler computation"
in the proof of Lemma (6.5)). -/
theorem chainZ_eq_prod (N : ℕ) (b : Bool) :
    chainZ J N b = ∏ i ∈ Finset.range N, (2 * Real.cosh (J i)) := by
  induction N generalizing b with
  | zero =>
    have : IsEmpty ((Finset.range 0 : Finset ℕ)) := ⟨fun i ↦ by simpa using i.2⟩
    rw [chainZ, Fintype.sum_unique]
    simp [chainWeight]
  | succ N ih =>
    rw [chainZ_succ, Finset.prod_range_succ]
    simp only [ih]
    rw [← Finset.sum_mul, sum_bool_exp]
    ring

lemma chainZ_pos (N : ℕ) (b : Bool) : 0 < chainZ J N b := by
  rw [chainZ_eq_prod]
  exact Finset.prod_pos fun i _ ↦ by positivity

/-- **The unnormalised magnetisation of an initial interval** (the identity at the heart of
Georgii's Lemma (6.5)): `∑_ζ σ_n e^{-H} = b ∏_{n ≤ i < N} tanh J_i · Z_N`. -/
theorem chainMag_eq {N n : ℕ} (hn : n < N) (b : Bool) :
    chainMag J N n b
      = spin b * (∏ i ∈ Finset.Ico n N, Real.tanh (J i)) * chainZ J N b := by
  have hcosh : ∀ i : ℕ, Real.tanh (J i) * (2 * Real.cosh (J i)) = 2 * Real.sinh (J i) := by
    intro i
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  induction N generalizing b with
  | zero => exact absurd hn (Nat.not_lt_zero n)
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn' | rfl
    · rw [chainMag_succ_of_lt hn' b, Finset.prod_Ico_succ_top hn'.le]
      simp only [ih hn', chainZ_eq_prod, Finset.prod_range_succ]
      set P := ∏ i ∈ Finset.Ico n N, Real.tanh (J i) with hP
      set C := ∏ i ∈ Finset.range N, (2 * Real.cosh (J i)) with hC
      have hstep : ∀ x : Bool, Real.exp (J N * (spin x * spin b)) * (spin x * P * C)
          = (P * C) * (spin x * Real.exp (J N * (spin x * spin b))) := fun x ↦ by ring
      rw [Finset.sum_congr rfl fun x _ ↦ hstep x, ← Finset.mul_sum, sum_bool_spin_exp,
        ← hcosh N]
      ring
    · rw [chainMag_succ_self, Nat.Ico_succ_singleton, Finset.prod_singleton]
      simp only [chainZ_eq_prod, Finset.prod_range_succ]
      set C := ∏ i ∈ Finset.range n, (2 * Real.cosh (J i)) with hC
      have hstep : ∀ x : Bool, spin x * Real.exp (J n * (spin x * spin b)) * C
          = C * (spin x * Real.exp (J n * (spin x * spin b))) := fun x ↦ by ring
      rw [Finset.sum_congr rfl fun x _ ↦ hstep x, ← Finset.mul_sum, sum_bool_spin_exp,
        ← hcosh n]
      ring

/-! ### The Gibbsian specification and its finite-volume form -/

variable (J)

/-- **Georgii Definition (2.9) for the potential (6.2).** The Gibbsian specification `γ^Φ` of the
inhomogeneous Ising chain, with the uniform a priori spin measure. The inverse temperature is
absorbed into the couplings: `γ^{βΦ}` is the chain with couplings `βJ`. -/
def isingChainSpecification : Specification ℕ Bool :=
  gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J) uniformSpinMeasure 1

/-- **The inverse temperature is absorbed into the couplings**: the chain with couplings `βJ` is
the chain with couplings `J` at inverse temperature `β`. -/
lemma isingChainSpecification_smul (β : ℝ) :
    isingChainSpecification (β • J)
      = gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
          uniformSpinMeasure β := by
  rw [isingChainSpecification,
    Potential.gibbsSpecification_congr uniformSpinMeasure 1 (isingChainPotential_smul J β),
    Potential.gibbsSpecificationOfAbsolutelySummable_smul, one_mul]

variable {J}

lemma sum_chainWeight_juxt (N : ℕ) (ω : ℕ → Bool) :
    ∑ ζ : ((Finset.range N) → Bool),
        chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ)
      = chainZ J N (ω N) := by
  refine Finset.sum_congr rfl fun ζ _ ↦ chainWeight_congr fun i hi ↦ ?_
  by_cases h : i ∈ Finset.range N
  · rw [juxt_apply_of_mem (by simpa using h), juxt_apply_of_mem (by simpa using h)]
  · have hiN : i = N := by
      rw [Finset.mem_range] at h
      omega
    subst hiN
    rw [juxt_apply_of_not_mem (by simp), juxt_apply_of_not_mem (by simp)]

lemma sum_spin_chainWeight_juxt {N n : ℕ} (hn : n < N) (ω : ℕ → Bool) :
    ∑ ζ : ((Finset.range N) → Bool),
        spin (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ n) *
          chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ)
      = chainMag J N n (ω N) := by
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  have hmem : n ∈ ((Finset.range N : Finset ℕ) : Set ℕ) := by simpa using hn
  rw [juxt_apply_of_mem hmem, juxt_apply_of_mem hmem]
  congr 1
  refine chainWeight_congr fun i hi ↦ ?_
  by_cases h : i ∈ Finset.range N
  · rw [juxt_apply_of_mem (by simpa using h), juxt_apply_of_mem (by simpa using h)]
  · have hiN : i = N := by
      rw [Finset.mem_range] at h
      omega
    subst hiN
    rw [juxt_apply_of_not_mem (by simp), juxt_apply_of_not_mem (by simp)]

lemma relZ_isingChain (N : ℕ) (ω : ℕ → Bool) (ζ : ((Finset.range N) → Bool)) :
    Specification.relZ (Specification.isssd (S := ℕ) (E := Bool) uniformSpinMeasure)
        ((isingChainPotential J).boltzmannFactor 1) (Finset.range N)
        (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ)
      = ENNReal.ofReal (chainZ J N (ω N)) *
          (2 : ℝ≥0∞)⁻¹ ^ Fintype.card (Finset.range N) := by
  rw [Specification.relZ, MeasureTheory.GibbsMeasure.lintegral_isssd_uniformSpinMeasure _ _
    (Potential.measurable_boltzmannFactor (Φ := isingChainPotential J) 1 _)]
  congr 1
  rw [← sum_chainWeight_juxt N ω, ENNReal.ofReal_sum_of_nonneg
    (fun ξ _ ↦ (chainWeight_pos N _).le)]
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  rw [juxt_juxt, Potential.boltzmannFactor, neg_one_mul, exp_neg_hamiltonian_range]

/-- **The finite-volume Gibbs distribution of the chain in closed form.** For a measurable `A`,
`γ_{Λ_N}(A | ω) = ∑_ζ e^{-H_N(ζ ω)} 1_A(ζ ω) / Z_N(ω_N)`. -/
theorem isingChainSpecification_range_apply (N : ℕ) (ω : ℕ → Bool) {A : Set (ℕ → Bool)}
    (hA : MeasurableSet A) :
    isingChainSpecification J (Finset.range N) ω A
      = ENNReal.ofReal ((∑ ζ : ((Finset.range N) → Bool),
            chainWeight J N (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ) *
              A.indicator (1 : (ℕ → Bool) → ℝ)
                (juxt ((Finset.range N : Finset ℕ) : Set ℕ) ω ζ))
          / chainZ J N (ω N)) := by
  set Λ : Finset ℕ := Finset.range N with hΛ
  set ρ := Specification.premodifierNorm (S := ℕ) (E := Bool) uniformSpinMeasure
    ((isingChainPotential J).boltzmannFactor 1) with hρdef
  have hρmeas : Measurable (ρ Λ) :=
    Specification.measurable_relNorm (γ := Specification.isssd uniformSpinMeasure)
      (Potential.isPremodifier_boltzmannFactor (Φ := isingChainPotential J) 1).measurable Λ
  have hmod : isingChainSpecification J Λ ω
      = (Specification.isssd (S := ℕ) (E := Bool) uniformSpinMeasure Λ ω).withDensity (ρ Λ) := rfl
  set c : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ with hcdef
  have hc0 : c ≠ 0 := by simp [hcdef]
  have hct : c ≠ ⊤ := by simp [hcdef]
  set W : ℝ := chainZ J N (ω N) with hWdef
  have hWpos : 0 < W := chainZ_pos N (ω N)
  have hterm : ∀ ζ : (Λ → Bool), A.indicator (ρ Λ) (juxt (Λ : Set ℕ) ω ζ) * c
      = ENNReal.ofReal (chainWeight J N (juxt (Λ : Set ℕ) ω ζ) *
          A.indicator (1 : (ℕ → Bool) → ℝ) (juxt (Λ : Set ℕ) ω ζ) / W) := by
    intro ζ
    by_cases hmem : juxt (Λ : Set ℕ) ω ζ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hρval : ρ Λ (juxt (Λ : Set ℕ) ω ζ)
          = ENNReal.ofReal (chainWeight J N (juxt (Λ : Set ℕ) ω ζ)) / (ENNReal.ofReal W * c) := by
        rw [hρdef, Specification.premodifierNorm, Specification.relNorm, relZ_isingChain N ω ζ,
          Potential.boltzmannFactor, neg_one_mul, exp_neg_hamiltonian_range]
      rw [hρval, ENNReal.div_mul _ (Or.inr hc0) (Or.inr hct),
        ENNReal.mul_div_cancel_right hc0 hct, Pi.one_apply, mul_one,
        ENNReal.ofReal_div_of_pos hWpos]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      simp
  rw [hmod, withDensity_apply _ hA, ← lintegral_indicator hA (ρ Λ),
    MeasureTheory.GibbsMeasure.lintegral_isssd_uniformSpinMeasure Λ ω (hρmeas.indicator hA),
        Finset.sum_mul,
    ← hcdef, Finset.sum_congr rfl fun ζ _ ↦ hterm ζ, ← ENNReal.ofReal_sum_of_nonneg,
    ← Finset.sum_div]
  intro ζ _
  exact div_nonneg (mul_nonneg (chainWeight_pos N _).le
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)) hWpos.le

/-! ### Georgii Lemma (6.5) -/

lemma measurableSet_setOf_apply_eq (n : ℕ) (x : Bool) :
    MeasurableSet {σ : ℕ → Bool | σ n = x} :=
  measurable_pi_apply (X := fun _ : ℕ ↦ Bool) n (measurableSet_singleton x)

/-- **Georgii Lemma (6.5).** For `n ∈ Λ_N = {0, …, N-1}`, `x` a spin and `ω` a boundary
configuration,
`γ^Φ_{Λ_N}(σ_n = x | ω) = (1 + x ω_N ∏_{n ≤ i < N} tanh J_i) / 2`. -/
theorem isingChainSpecification_range_apply_setOf_eq {N n : ℕ} (hn : n < N) (x : Bool)
    (ω : ℕ → Bool) :
    isingChainSpecification J (Finset.range N) ω {σ : ℕ → Bool | σ n = x}
      = ENNReal.ofReal
          ((1 + spin x * spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2) := by
  set Λ : Set ℕ := ((Finset.range N : Finset ℕ) : Set ℕ) with hΛ
  rw [isingChainSpecification_range_apply N ω (measurableSet_setOf_apply_eq n x)]
  congr 1
  have hind : ∀ ζ : ((Finset.range N) → Bool),
      ({σ : ℕ → Bool | σ n = x}).indicator (1 : (ℕ → Bool) → ℝ) (juxt Λ ω ζ)
        = (1 + spin x * spin (juxt Λ ω ζ n)) / 2 := by
    intro ζ
    by_cases h : juxt Λ ω ζ n = x
    · rw [Set.indicator_of_mem (show juxt Λ ω ζ ∈ {σ : ℕ → Bool | σ n = x} from h), Pi.one_apply,
        h, spin_mul_self]
      norm_num
    · rw [Set.indicator_of_notMem (show juxt Λ ω ζ ∉ {σ : ℕ → Bool | σ n = x} from h),
        spin_mul_spin_of_ne h]
      norm_num
  have hsum : ∑ ζ : ((Finset.range N) → Bool),
        chainWeight J N (juxt Λ ω ζ) *
          ({σ : ℕ → Bool | σ n = x}).indicator (1 : (ℕ → Bool) → ℝ) (juxt Λ ω ζ)
      = (chainZ J N (ω N) + spin x * chainMag J N n (ω N)) / 2 := by
    have hstep : ∀ ζ : ((Finset.range N) → Bool),
        chainWeight J N (juxt Λ ω ζ) *
            ({σ : ℕ → Bool | σ n = x}).indicator (1 : (ℕ → Bool) → ℝ) (juxt Λ ω ζ)
          = (chainWeight J N (juxt Λ ω ζ) +
              spin x * (spin (juxt Λ ω ζ n) * chainWeight J N (juxt Λ ω ζ))) / 2 := by
      intro ζ
      rw [hind ζ]
      ring
    rw [Finset.sum_congr rfl fun ζ _ ↦ hstep ζ, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_chainWeight_juxt N ω, sum_spin_chainWeight_juxt hn ω]
  rw [hsum, chainMag_eq hn]
  have hZ : chainZ J N (ω N) ≠ 0 := (chainZ_pos N (ω N)).ne'
  field_simp

/-! ### Step 1 of Georgii (6.4): the plus phase

Along the volumes `Λ_N` with the constant `+` boundary condition, every local event has a limit
(Lemma (6.5) computes it on the events `{σ_n = x}`), and a cluster point of the finite-volume
Gibbs distributions is a Gibbs measure by Theorem (4.17). -/

/-- `{σ_n = x}` is a local event. -/
lemma setOf_apply_eq_mem_localEvents (n : ℕ) (x : Bool) :
    {σ : ℕ → Bool | σ n = x} ∈ localEvents ℕ Bool :=
  mem_localEvents_iff_exists_finsetRestrict_preimage.2
    ⟨{n}, {y : (({n} : Finset ℕ)) → Bool | y ⟨n, Finset.mem_singleton_self n⟩ = x},
      MeasurableSet.of_discrete, rfl⟩

/-- The constant configuration `ω ≡ x`; Georgii's `ω⁺` is `constConfig true` and his `ω⁻` is
`constConfig false`. -/
def constConfig (x : Bool) : ℕ → Bool := fun _ ↦ x

@[simp] lemma constConfig_apply (x : Bool) (i : ℕ) : constConfig x i = x := rfl

/-- Georgii's `A_x = {σ_n = x for all sufficiently large n}`: `A₊` for `x = true` and `A₋` for
`x = false`. -/
def eventuallyConst (x : Bool) : Set (ℕ → Bool) := {σ : ℕ → Bool | ∀ᶠ n in atTop, σ n = x}

lemma mem_eventuallyConst_iff {x : Bool} {σ : ℕ → Bool} :
    σ ∈ eventuallyConst x ↔ ∀ᶠ n in atTop, σ n = x := Iff.rfl

lemma constConfig_mem_eventuallyConst (x : Bool) : constConfig x ∈ eventuallyConst x :=
  Filter.Eventually.of_forall fun _ ↦ rfl

lemma measurableSet_eventuallyConst (x : Bool) : MeasurableSet (eventuallyConst x) := by
  have : eventuallyConst x = ⋃ m : ℕ, ⋂ n ∈ Set.Ici m, {σ : ℕ → Bool | σ n = x} := by
    ext σ
    simp [eventuallyConst, Filter.eventually_atTop]
  rw [this]
  exact MeasurableSet.iUnion fun m ↦
    MeasurableSet.biInter (Set.to_countable _) fun n _ ↦ measurableSet_setOf_apply_eq n x

lemma isQuasilocal_isingChainSpecification : (isingChainSpecification J).IsQuasilocal :=
  Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable
    (Φ := isingChainPotential J) uniformSpinMeasure 1

/-! #### Georgii (6.6): the Markov decomposition over the boundary spin -/

/-- **The Markov property of the nearest-neighbour potential (6.2).** On an event `A` that
depends only on the sites `{0, …, n-1}` *inside* the volume `Λ_n`, the finite-volume Gibbs
distribution `γ_{Λ_n}(A | ·)` is a function of the boundary spin at the site `n` alone. -/
lemma isingChainSpecification_range_apply_congr {n : ℕ} {A : Set (ℕ → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool)
      ((Finset.range n : Finset ℕ) : Set ℕ)] A) {η η' : ℕ → Bool} (h : η n = η' n) :
    isingChainSpecification J (Finset.range n) η A
      = isingChainSpecification J (Finset.range n) η' A := by
  have hAm : MeasurableSet A := cylinderEvents_le_pi (X := fun _ : ℕ ↦ Bool) _ hA
  set Λ : Set ℕ := ((Finset.range n : Finset ℕ) : Set ℕ) with hΛ
  have hagree : ∀ ζ : ((Finset.range n) → Bool), ∀ i ≤ n, juxt Λ η ζ i = juxt Λ η' ζ i := by
    intro ζ i hi
    rcases lt_or_eq_of_le hi with hi' | rfl
    · rw [juxt_apply_of_mem (show i ∈ Λ by simpa [hΛ] using hi'),
        juxt_apply_of_mem (show i ∈ Λ by simpa [hΛ] using hi')]
    · rw [juxt_apply_of_not_mem (by simp [hΛ]), juxt_apply_of_not_mem (by simp [hΛ])]
      exact h
  have hmemA : ∀ ζ : ((Finset.range n) → Bool), juxt Λ η ζ ∈ A ↔ juxt Λ η' ζ ∈ A := fun ζ ↦
    mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
      hagree ζ i (le_of_lt (by simpa [hΛ] using hi))
  have hsum : ∑ ζ : ((Finset.range n) → Bool),
        chainWeight J n (juxt Λ η ζ) * A.indicator (1 : (ℕ → Bool) → ℝ) (juxt Λ η ζ)
      = ∑ ζ : ((Finset.range n) → Bool),
        chainWeight J n (juxt Λ η' ζ) * A.indicator (1 : (ℕ → Bool) → ℝ) (juxt Λ η' ζ) := by
    refine Finset.sum_congr rfl fun ζ _ ↦ ?_
    rw [chainWeight_congr (hagree ζ)]
    congr 1
    by_cases hmem : juxt Λ η ζ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hmemA ζ).1 hmem), Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem fun hc ↦ hmem ((hmemA ζ).2 hc)]
  rw [isingChainSpecification_range_apply n η hAm, isingChainSpecification_range_apply n η' hAm,
    h, hsum]

/-- **Georgii (6.6).** Let `A` depend only on the sites `{0, …, n-1}` and let `n ≤ N`. Writing
`ω^{n,x}` for any configuration with spin `x` at the site `n` (Georgii's notation; here the
constant configuration `≡ x`),
`γ_{Λ_N}(A | ω) = ∑_x γ_{Λ_n}(A | ω^{n,x}) · γ_{Λ_N}(σ_n = x | ω)`.
This is consistency `γ_{Λ_N} γ_{Λ_n} = γ_{Λ_N}` together with the Markov property
`isingChainSpecification_range_apply_congr`. -/
theorem isingChainSpecification_range_apply_eq_sum {n N : ℕ} (hnN : n ≤ N) {A : Set (ℕ → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool)
      ((Finset.range n : Finset ℕ) : Set ℕ)] A) (ω : ℕ → Bool) :
    isingChainSpecification J (Finset.range N) ω A
      = ∑ x : Bool, isingChainSpecification J (Finset.range n) (constConfig x) A *
          isingChainSpecification J (Finset.range N) ω {σ : ℕ → Bool | σ n = x} := by
  set γ := isingChainSpecification J with hγ
  have hAm : MeasurableSet A := cylinderEvents_le_pi (X := fun _ : ℕ ↦ Bool) _ hA
  have hsub : Finset.range n ⊆ Finset.range N := fun i hi ↦
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hnN)
  have hmap : ∫⁻ x, γ (Finset.range n) (constConfig x) A
        ∂((γ (Finset.range N) ω).map fun η : ℕ → Bool ↦ η n)
      = ∫⁻ η, γ (Finset.range n) (constConfig (η n)) A ∂(γ (Finset.range N) ω) :=
    lintegral_map (f := fun x : Bool ↦ γ (Finset.range n) (constConfig x) A)
      Measurable.of_discrete (measurable_pi_apply n)
  have hstep : ∫⁻ η, γ (Finset.range n) η A ∂(γ (Finset.range N) ω)
      = ∫⁻ η, γ (Finset.range n) (constConfig (η n)) A ∂(γ (Finset.range N) ω) :=
    lintegral_congr fun η ↦ isingChainSpecification_range_apply_congr hA rfl
  have hbind : γ (Finset.range N) ω A = ∫⁻ η, γ (Finset.range n) η A ∂(γ (Finset.range N) ω) := by
    conv_lhs => rw [← Specification.bind hsub ω]
    exact Measure.bind_apply hAm (γ.measurable_kernel_toMeasure _).aemeasurable
  rw [hbind, hstep, ← hmap, lintegral_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton x)]
  rfl

/-! #### The boundary-independent limit of `γ_{Λ_N}(A|ω)` -/

/-- Every local event of `ℕ → Bool` depends only on an initial interval `{0, …, n-1}`. -/
lemma exists_measurableSet_cylinderEvents_range {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    ∃ n : ℕ, MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool)
      ((Finset.range n : Finset ℕ) : Set ℕ)] A := by
  obtain ⟨Λ, hAΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  obtain ⟨n, hn⟩ := Λ.exists_nat_subset_range
  exact ⟨n, cylinderEvents_mono (X := fun _ : ℕ ↦ Bool) (by exact_mod_cast hn) _ hAΛ⟩

/-- **Georgii (6.6) together with Lemma (6.5).** For an event `A` depending only on the sites
`{0, …, n-1}` and any `N > n`,
`γ_{Λ_N}(A|ω) = γ_{Λ_n}(A|ω⁺) (1 + ω_N P)/2 + γ_{Λ_n}(A|ω⁻) (1 - ω_N P)/2`,
`P = ∏_{n ≤ i < N} tanh J_i`: the entire dependence on the boundary condition is through the
single spin `ω_N`, and it is carried by the product `P`. -/
theorem isingChainSpecification_range_apply_eq {n N : ℕ} (hN : n < N) {A : Set (ℕ → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool)
      ((Finset.range n : Finset ℕ) : Set ℕ)] A) (ω : ℕ → Bool) :
    isingChainSpecification J (Finset.range N) ω A
      = isingChainSpecification J (Finset.range n) (constConfig true) A
          * ENNReal.ofReal ((1 + spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)
        + isingChainSpecification J (Finset.range n) (constConfig false) A
          * ENNReal.ofReal ((1 - spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2) := by
  have e1 : (1 + spin true * spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2
      = (1 + spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2 := by
    rw [show spin true = 1 from rfl]; ring
  have e2 : (1 + spin false * spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2
      = (1 - spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2 := by
    rw [show spin false = -1 from rfl]; ring
  rw [isingChainSpecification_range_apply_eq_sum hN.le hA ω, Fintype.sum_bool,
    isingChainSpecification_range_apply_setOf_eq hN true ω,
    isingChainSpecification_range_apply_setOf_eq hN false ω, e1, e2]

/-- **Georgii (6.4), step 1.** Under (6.1) the finite-volume Gibbs distributions of the initial
intervals converge, on every local event `A`, to a limit that is the *same* for all boundary
conditions `ω` that are eventually equal to the constant spin `x`.  This is Georgii's (6.6)
combined with Lemma (6.5) and the convergence of the tail products `∏_{i ≥ n} tanh J_i`; the
convergence (not the positivity) of the tail products needs only (6.1), not `J_n > 0`. -/
theorem exists_tendsto_isingChainSpecification_range_apply
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (x : Bool) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    ∃ a : ℝ≥0∞, ∀ ω ∈ eventuallyConst x,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 a) := by
  classical
  obtain ⟨n, hAn⟩ := exists_measurableSet_cylinderEvents_range hA
  set aT := isingChainSpecification J (Finset.range n) (constConfig true) A with haT
  set aF := isingChainSpecification J (Finset.range n) (constConfig false) A with haF
  have haTtop : aT ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have haFtop : aF ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  obtain ⟨T, hTend⟩ : ∃ T : ℝ,
      Tendsto (fun N ↦ ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) atTop (𝓝 T) :=
    ⟨_, Multipliable.tendsto_prod_Ico_nat (f := fun i ↦ Real.tanh (J i))
      (Real.multipliable_tanh (h61.comp_injective (add_left_injective n)))⟩
  refine ⟨aT * ENNReal.ofReal ((1 + spin x * T) / 2)
    + aF * ENNReal.ofReal ((1 - spin x * T) / 2), fun ω hω ↦ ?_⟩
  have hlim : Tendsto (fun N ↦
      aT * ENNReal.ofReal ((1 + spin x * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)
        + aF * ENNReal.ofReal ((1 - spin x * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2))
      atTop (𝓝 (aT * ENNReal.ofReal ((1 + spin x * T) / 2)
        + aF * ENNReal.ofReal ((1 - spin x * T) / 2))) := by
    refine Filter.Tendsto.add (ENNReal.Tendsto.const_mul ?_ (Or.inr haTtop))
      (ENNReal.Tendsto.const_mul ?_ (Or.inr haFtop))
    · exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds.add (hTend.const_mul (spin x))).div_const 2)
    · exact (ENNReal.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds.sub (hTend.const_mul (spin x))).div_const 2)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop n, mem_eventuallyConst_iff.1 hω] with N hN hωN
  rw [isingChainSpecification_range_apply_eq hN hAn ω, hωN, ← haT, ← haF]

/-- **Georgii (6.5) in the limit.** With the `+` boundary condition, the finite-volume
probabilities of `{σ_n = true}` converge to `(1 + ∏_{i ≥ n} tanh J_i)/2 > 1/2`. -/
theorem tendsto_isingChainSpecification_setOf_true (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    ∃ T : ℝ, 0 < T ∧ Filter.Tendsto
      (fun N ↦ isingChainSpecification J (Finset.range N) (constConfig true)
        {σ : ℕ → Bool | σ n = true}) atTop (𝓝 (ENNReal.ofReal ((1 + T) / 2))) := by
  have h61n : Summable fun k ↦ Real.exp (-2 * J (k + n)) :=
    h61.comp_injective (add_left_injective n)
  refine ⟨∏' k, Real.tanh (J (k + n)), Real.tprod_tanh_pos (fun k ↦ hJ (k + n)) h61n, ?_⟩
  have hTend : Tendsto (fun N ↦ ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) atTop
      (𝓝 (∏' k, Real.tanh (J (k + n)))) :=
    Multipliable.tendsto_prod_Ico_nat (f := fun i ↦ Real.tanh (J i))
      (Real.multipliable_tanh h61n)
  have hcont : Filter.Tendsto
      (fun N ↦ ENNReal.ofReal ((1 + ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)) atTop
      (𝓝 (ENNReal.ofReal ((1 + ∏' k, Real.tanh (J (k + n))) / 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (((tendsto_const_nhds).add hTend).div_const 2)
  refine hcont.congr' ?_
  filter_upwards [eventually_gt_atTop n] with N hN
  rw [isingChainSpecification_range_apply_setOf_eq hN true (constConfig true)]
  norm_num [constConfig, spin]

/-- **Georgii, Theorem (4.17), for the chain.** There is a Gibbs measure `μ` of the chain which
is a cluster point, in the topology of local convergence, of the finite-volume Gibbs
distributions with the constant boundary condition `ω ≡ x`; on every local event on which that
sequence converges, `μ` takes the limit value. -/
theorem exists_mem_GP_eq_of_tendsto (x : Bool) :
    ∃ μ ∈ GP (isingChainSpecification J), ∀ A ∈ localEvents ℕ Bool, ∀ a : ℝ≥0∞,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) (constConfig x) A) atTop
          (𝓝 a) →
        (μ : Measure (ℕ → Bool)) A = a := by
  classical
  set γ := isingChainSpecification J with hγ
  set ν : ProbabilityMeasure (ℕ → Bool) :=
    ⟨Measure.dirac (constConfig x), inferInstance⟩ with hν
  have hdirac : ∀ Λ : Finset ℕ, γ.bindPM Λ ν = finiteVolumeDistributions γ (constConfig x) Λ :=
    fun Λ ↦ Subtype.ext (Measure.dirac_bind (γ.measurable_kernel_toMeasure Λ) (constConfig x))
  have hle : LocallyEquicontinuous atTop
      (fun N : ℕ ↦ γ.bindPM (Finset.range N) ν) := by
    have hcomp : (fun N : ℕ ↦ γ.bindPM (Finset.range N) ν)
        = (finiteVolumeDistributions γ (constConfig x)) ∘ Finset.range :=
      funext fun N ↦ hdirac (Finset.range N)
    rw [hcomp]
    exact (Potential.locallyEquicontinuous_finiteVolumeDistributions (Φ := isingChainPotential J)
      uniformSpinMeasure 1 (constConfig x)).comp Filter.tendsto_finset_range
  obtain ⟨μ, hμGP, hcp⟩ := exists_mem_GP_mapClusterPt (γ := γ)
    (isQuasilocal_isingChainSpecification (J := J)) (γs := fun _ : ℕ ↦ γ)
    (Λs := Finset.range) (νs := fun _ ↦ ν) Filter.tendsto_finset_range
    (fun Λ f _ ↦ by simp) hle
  refine ⟨μ, hμGP, fun A hA a ha ↦ ?_⟩
  obtain ⟨U, hU, hUconv⟩ := mapClusterPt_iff_ultrafilter.1 hcp
  have h1 := tendsto_withLocalConvergence_iff.1 hUconv _ hA
  have h2 : Tendsto (fun N : ℕ ↦ ((γ.bindPM (Finset.range N) ν :
      ProbabilityMeasure (ℕ → Bool)) : Measure (ℕ → Bool)) A) atTop (𝓝 a) := by
    refine ha.congr fun N ↦ ?_
    rw [hdirac (Finset.range N)]
    rfl
  exact tendsto_nhds_unique h1 (h2.mono_left hU)

/-- **Georgii (6.4), step 1: the plus phase `μ₊`.** Under (6.1) there is a Gibbs measure `μ₊`
of the inhomogeneous Ising chain which is the local limit `lim_{N} γ_{Λ_N}(· | ω)` for *every*
boundary condition `ω ∈ A₊`.  A cluster point of `γ_{Λ_N}(· | ω⁺)` is a Gibbs measure by
Theorem (4.17); `exists_tendsto_isingChainSpecification_range_apply` shows that the whole
sequence converges to it, and that the limit does not depend on `ω ∈ A₊`. -/
theorem exists_mem_GP_tendsto (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μ ∈ GP (isingChainSpecification J), ∀ A ∈ localEvents ℕ Bool, ∀ ω ∈ eventuallyConst true,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop
        (𝓝 ((μ : Measure (ℕ → Bool)) A)) := by
  obtain ⟨μ, hμGP, hμ⟩ := exists_mem_GP_eq_of_tendsto (J := J) true
  refine ⟨μ, hμGP, fun A hA ω hω ↦ ?_⟩
  obtain ⟨a, ha⟩ := exists_tendsto_isingChainSpecification_range_apply h61 true hA
  rw [hμ A hA a (ha _ (constConfig_mem_eventuallyConst true))]
  exact ha ω hω

/-- **Georgii (6.4): the magnetisation of the plus phase.** Any measure that is the local limit
of `γ_{Λ_N}(· | ω)` along `A₊` satisfies `μ(σ_n = +1) = (1 + ∏_{i ≥ n} tanh J_i)/2`, and the
tail product is strictly positive by (6.1). -/
theorem exists_apply_setOf_true_of_tendsto (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {μ : Measure (ℕ → Bool)}
    (hμ : ∀ A ∈ localEvents ℕ Bool, ∀ ω ∈ eventuallyConst true,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 (μ A)))
    (n : ℕ) :
    ∃ T : ℝ, 0 < T ∧ μ {σ : ℕ → Bool | σ n = true} = ENNReal.ofReal ((1 + T) / 2) := by
  obtain ⟨T, hT, hTend⟩ := tendsto_isingChainSpecification_setOf_true hJ h61 n
  exact ⟨T, hT, tendsto_nhds_unique
    (hμ _ (setOf_apply_eq_mem_localEvents n true) _ (constConfig_mem_eventuallyConst true)) hTend⟩

/-- **Georgii (6.4), step 1.** Under (6.1) there is a Gibbs measure `μ₊` for the inhomogeneous
Ising chain with `μ₊(σ_n = +1) = (1 + ∏_{i ≥ n} tanh J_i)/2 > 1/2` at every site. -/
theorem exists_mem_GP_apply_setOf_true (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μ ∈ GP (isingChainSpecification J), ∀ n : ℕ,
      ∃ T : ℝ, 0 < T ∧
        (μ : Measure (ℕ → Bool)) {σ : ℕ → Bool | σ n = true} = ENNReal.ofReal ((1 + T) / 2) := by
  obtain ⟨μ, hμGP, hμ⟩ := exists_mem_GP_tendsto h61
  exact ⟨μ, hμGP, exists_apply_setOf_true_of_tendsto hJ h61 hμ⟩

/-! ### Spontaneous magnetisation

`μ(σ_n) = 2 μ(σ_n = +1) - 1`, so the plus phase has strictly positive magnetisation at every
site — Georgii's `μ₊(σ_i) > 0`. -/

lemma integral_spin_apply (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ ω, spin (ω n) ∂μ = 2 * (μ {σ : ℕ → Bool | σ n = true}).toReal - 1 := by
  have hA := measurableSet_setOf_apply_eq n true
  have heq : ∀ ω : ℕ → Bool,
      spin (ω n) = 2 * ({σ : ℕ → Bool | σ n = true}).indicator (1 : (ℕ → Bool) → ℝ) ω - 1 := by
    intro ω
    by_cases h : ω n = true
    · rw [Set.indicator_of_mem (show ω ∈ {σ : ℕ → Bool | σ n = true} from h), Pi.one_apply, h]
      norm_num [spin]
    · have hf : ω n = false := by
        cases hb : ω n
        · rfl
        · exact absurd hb h
      rw [Set.indicator_of_notMem (show ω ∉ {σ : ℕ → Bool | σ n = true} from h), hf]
      norm_num [spin]
  have hint : Integrable
      (fun ω ↦ ({σ : ℕ → Bool | σ n = true}).indicator (1 : (ℕ → Bool) → ℝ) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  rw [integral_congr_ae (Filter.Eventually.of_forall heq),
    integral_sub (hint.const_mul 2) (integrable_const 1), integral_const_mul,
    integral_indicator_one hA, integral_const]
  simp [measureReal_def]

/-- **Georgii (6.4): the plus phase has positive magnetisation.** Under (6.1) there is a Gibbs
measure for the inhomogeneous Ising chain with `μ(σ_n) > 0` at every site `n`. -/
theorem exists_mem_G_integral_spin_pos (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μ ∈ G (isingChainSpecification J), ∀ n : ℕ, 0 < ∫ ω, spin (ω n) ∂μ := by
  obtain ⟨μ, hμGP, hμ⟩ := exists_mem_GP_apply_setOf_true hJ h61
  refine ⟨(μ : Measure (ℕ → Bool)), ⟨μ.2, hμGP⟩, fun n ↦ ?_⟩
  obtain ⟨T, hT, hTeq⟩ := hμ n
  have := μ.2
  rw [integral_spin_apply _ n, hTeq, ENNReal.toReal_ofReal (by positivity)]
  linarith

/-! ### Georgii (6.3): the spin flip, and step 2 of (6.4)

`τ : ω ↦ -ω` is a symmetry of `Φ`, hence of `γ^Φ` (Georgii (5.9)); it carries `μ₊` to a Gibbs
measure `μ₋` with the opposite magnetisation, so `μ₋ ≠ μ₊` and `|𝒢(Φ)| > 1`. -/

/-- **Georgii (6.3).** The spin flip `(τω)_i = -ω_i` on the chain. -/
def chainFlip : Transformation ℕ Bool where
  sites := Equiv.refl ℕ
  spin _ := boolNot

lemma isPureSpin_chainFlip : chainFlip.IsPureSpin := rfl

@[simp] lemma chainFlip_spin_apply (i : ℕ) (b : Bool) : chainFlip.spin i b = !b := rfl

@[simp] lemma chainFlip_toFun_apply (ω : ℕ → Bool) (i : ℕ) : chainFlip.toFun ω i = !(ω i) := rfl

/-- **Georgii (6.3).** The spin flip is a symmetry of the potential (6.2). -/
theorem map_chainFlip_isingChainPotential :
    Potential.map chainFlip (isingChainPotential J) = isingChainPotential J :=
  (map_pair_eq_iff _ isPureSpin_chainFlip).2 fun i j _ x y ↦ by
    simp only [isingChainPair, chainFlip_spin_apply, spin_not]
    split_ifs <;> ring

/-- **Georgii (5.9)(b) for the chain.** `γ^Φ` is invariant under the spin flip. -/
theorem isInvariant_chainFlip :
    Specification.IsInvariant chainFlip (isingChainSpecification J) :=
  Potential.isInvariant_gibbsSpecification chainFlip (isingChainPotential J) uniformSpinMeasure 1
    (fun _ ↦ measurePreserving_boolNot_uniformSpinMeasure) map_chainFlip_isingChainPotential

lemma chainFlip_toFun_involutive : Function.Involutive chainFlip.toFun :=
  fun ω ↦ funext fun i ↦ by simp

lemma chainFlip_mem_eventuallyConst {x : Bool} {ω : ℕ → Bool} (hω : ω ∈ eventuallyConst x) :
    chainFlip.toFun ω ∈ eventuallyConst (!x) := by
  filter_upwards [mem_eventuallyConst_iff.1 hω] with n hn
  rw [chainFlip_toFun_apply, hn]

/-- The spin flip maps local events to local events. -/
lemma preimage_chainFlip_mem_localEvents {A : Set (ℕ → Bool)} (hA : A ∈ localEvents ℕ Bool) :
    chainFlip.toFun ⁻¹' A ∈ localEvents ℕ Bool := by
  obtain ⟨Λ, hAΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  refine mem_localEvents_of_cylinderEvents Λ ?_
  refine (measurable_cylinderEvents_iff (X := fun _ : ℕ ↦ Bool)).2 (fun i hi ↦ ?_) hAΛ
  exact (Measurable.of_discrete (f := fun b : Bool ↦ !b)).comp
    (measurable_cylinderEvent_apply (X := fun _ : ℕ ↦ Bool) hi)

/-- **Georgii (5.9) for the chain, displayed form.** `γ_{Λ}(τ⁻¹B | ω) = γ_{Λ}(B | τω)`. -/
lemma isingChainSpecification_preimage_chainFlip (Λ : Finset ℕ) (ω : ℕ → Bool)
    {B : Set (ℕ → Bool)} (hB : MeasurableSet B) :
    isingChainSpecification J Λ ω (chainFlip.toFun ⁻¹' B)
      = isingChainSpecification J Λ (chainFlip.toFun ω) B := by
  have hmapΛ : Λ.map chainFlip.sites.toEmbedding = Λ :=
    Finset.ext fun i ↦ by simp [chainFlip]
  have h := Specification.isInvariant_iff.1 (isInvariant_chainFlip (J := J)) Λ ω
  rw [hmapΛ] at h
  rw [← h, Measure.map_apply chainFlip.measurable_toFun hB]

/-- **Georgii (6.4), step 2: the minus phase `μ₋ = τ(μ₊)`.** If `μ` is the local limit of
`γ_{Λ_N}(· | ω)` along `A₊`, then the image `τ(μ)` under the spin flip is the local limit along
`A₋`.  This is the symmetry `τ(γ^Φ) = γ^Φ` of Corollary (5.9). -/
theorem tendsto_map_chainFlip_of_tendsto {μ : Measure (ℕ → Bool)}
    (hμ : ∀ A ∈ localEvents ℕ Bool, ∀ ω ∈ eventuallyConst true,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 (μ A)))
    {A : Set (ℕ → Bool)} (hA : A ∈ localEvents ℕ Bool) {ω : ℕ → Bool}
    (hω : ω ∈ eventuallyConst false) :
    Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop
      (𝓝 ((μ.map chainFlip.toFun) A)) := by
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  have hpp : chainFlip.toFun ⁻¹' (chainFlip.toFun ⁻¹' A) = A :=
    Set.ext fun η ↦ by simp only [Set.mem_preimage, chainFlip_toFun_involutive η]
  have hflip : ∀ N : ℕ, isingChainSpecification J (Finset.range N) ω A
      = isingChainSpecification J (Finset.range N) (chainFlip.toFun ω)
          (chainFlip.toFun ⁻¹' A) := fun N ↦ by
    have h := isingChainSpecification_preimage_chainFlip (J := J) (Finset.range N) ω
      (chainFlip.measurable_toFun hAm)
    rwa [hpp] at h
  rw [Measure.map_apply chainFlip.measurable_toFun hAm]
  exact (hμ _ (preimage_chainFlip_mem_localEvents hA) _
    (chainFlip_mem_eventuallyConst hω)).congr fun N ↦ (hflip N).symm

lemma integral_spin_map_chainFlip {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ] (n : ℕ) :
    ∫ ω, spin (ω n) ∂(μ.map chainFlip.toFun) = -∫ ω, spin (ω n) ∂μ := by
  have hmap := integral_map (μ := μ) (φ := chainFlip.toFun)
    (f := fun ω : ℕ → Bool ↦ spin (ω n)) chainFlip.measurable_toFun.aemeasurable
    ((measurable_spin.comp (measurable_pi_apply n)).aestronglyMeasurable)
  rw [hmap]
  simp only [chainFlip_toFun_apply, spin_not]
  exact integral_neg _

/-- **Georgii (6.4), step 2: the phase transition.** Under (6.1) the inhomogeneous Ising chain
has two distinct Gibbs measures, `μ₊` and `μ₋ = τ(μ₊)`, with opposite (nonzero) magnetisations
at every site. -/
theorem exists_ne_mem_G (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μplus ∈ G (isingChainSpecification J), ∃ μminus ∈ G (isingChainSpecification J),
      μplus ≠ μminus ∧ ∀ n : ℕ,
        0 < ∫ ω, spin (ω n) ∂μplus ∧ ∫ ω, spin (ω n) ∂μminus < 0 := by
  obtain ⟨μ, ⟨hprob, hμG⟩, hpos⟩ := exists_mem_G_integral_spin_pos hJ h61
  have := hprob
  refine ⟨μ, ⟨hprob, hμG⟩, μ.map chainFlip.toFun,
    ⟨Measure.isProbabilityMeasure_map chainFlip.measurable_toFun.aemeasurable,
      (isInvariant_chainFlip (J := J)).map_isGibbsMeasure hμG⟩, ?_,
    fun n ↦ ⟨hpos n, ?_⟩⟩
  · intro hcon
    have h0 := hpos 0
    rw [hcon, integral_spin_map_chainFlip 0] at h0
    linarith [hpos 0]
  · rw [integral_spin_map_chainFlip n]
    linarith [hpos n]

/-! ### Step 3 of Georgii (6.4): every Gibbs measure lives on `A₊ ∪ A₋`

The single-bond disagreement probability is the same for *every* Gibbs measure, and is summable
by (6.1); Borel–Cantelli then puts all the mass on the configurations that are eventually
constant. -/

/-- **Georgii (6.4), step 3.** For every Gibbs measure of the chain,
`μ(σ_n ≠ σ_{n+1}) = (1 - tanh J_n)/2 = 1/(1 + e^{2J_n})` — a quantity that does not depend on
`μ`. -/
theorem apply_setOf_ne_of_isGibbsMeasure {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) (n : ℕ) :
    μ {σ : ℕ → Bool | σ n ≠ σ (n + 1)} = ENNReal.ofReal ((1 - Real.tanh (J n)) / 2) := by
  classical
  set γ := isingChainSpecification J with hγ
  set Λ : Finset ℕ := Finset.range (n + 1) with hΛ
  have hbind : μ.bind (γ Λ) = μ := (Specification.isGibbsMeasure_iff_forall_bind_eq).1 hμ Λ
  have hmemc : (n + 1) ∈ ((Λ : Set ℕ))ᶜ := by simp [hΛ]
  -- the two pieces of `{σ_n ≠ σ_{n+1}}`
  have key : ∀ z : Bool,
      μ ({σ : ℕ → Bool | σ n = !z} ∩ {σ : ℕ → Bool | σ (n + 1) = z})
        = ENNReal.ofReal ((1 - Real.tanh (J n)) / 2) * μ {σ : ℕ → Bool | σ (n + 1) = z} := by
    intro z
    have hA : MeasurableSet {σ : ℕ → Bool | σ n = !z} := measurableSet_setOf_apply_eq n (!z)
    have hB : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool) ((Λ : Set ℕ))ᶜ]
        {σ : ℕ → Bool | σ (n + 1) = z} :=
      measurable_cylinderEvent_apply (X := fun _ : ℕ ↦ Bool) hmemc (measurableSet_singleton z)
    have hcomp := (γ.isProper Λ).setLIntegral_eq_comp
      (fun t ht ↦ cylinderEvents_le_pi (X := fun _ : ℕ ↦ Bool) t ht) (μ := μ) hA hB
    have hval : ∀ ω ∈ {σ : ℕ → Bool | σ (n + 1) = z}, γ Λ ω {σ : ℕ → Bool | σ n = !z}
        = ENNReal.ofReal ((1 - Real.tanh (J n)) / 2) := by
      intro ω hω
      rw [hγ, hΛ, isingChainSpecification_range_apply_setOf_eq (Nat.lt_succ_self n) (!z) ω,
        Nat.Ico_succ_singleton, Finset.prod_singleton, show ω (n + 1) = z from hω,
        spin_mul_spin_of_ne (show z ≠ !z by cases z <;> simp)]
      ring_nf
    have hcomp' : ∫⁻ a in {σ : ℕ → Bool | σ (n + 1) = z}, γ Λ a {σ : ℕ → Bool | σ n = !z} ∂μ
        = μ ({σ : ℕ → Bool | σ n = !z} ∩ {σ : ℕ → Bool | σ (n + 1) = z}) := by
      rw [hcomp, hbind]
    rw [← hcomp', setLIntegral_congr_fun (measurableSet_setOf_apply_eq (n + 1) z) hval,
      setLIntegral_const]
  -- put the two pieces together
  have hdisj : Disjoint ({σ : ℕ → Bool | σ n = !true} ∩ {σ : ℕ → Bool | σ (n + 1) = true})
      ({σ : ℕ → Bool | σ n = !false} ∩ {σ : ℕ → Bool | σ (n + 1) = false}) :=
    Set.disjoint_left.2 fun σ h1 h2 ↦ by simp_all
  have hone : μ {σ : ℕ → Bool | σ (n + 1) = true} + μ {σ : ℕ → Bool | σ (n + 1) = false} = 1 := by
    rw [← measure_union (Set.disjoint_left.2 fun σ h1 h2 ↦ by simp_all)
      (measurableSet_setOf_apply_eq (n + 1) false),
      show ({σ : ℕ → Bool | σ (n + 1) = true} ∪ {σ : ℕ → Bool | σ (n + 1) = false})
        = Set.univ by ext σ; cases h : σ (n + 1) <;> simp [h],
      measure_univ]
  have hsplit : {σ : ℕ → Bool | σ n ≠ σ (n + 1)}
      = ({σ : ℕ → Bool | σ n = !true} ∩ {σ : ℕ → Bool | σ (n + 1) = true}) ∪
        ({σ : ℕ → Bool | σ n = !false} ∩ {σ : ℕ → Bool | σ (n + 1) = false}) := by
    ext σ
    cases h1 : σ n <;> cases h2 : σ (n + 1) <;> simp [h1, h2]
  rw [hsplit, measure_union hdisj
    ((measurableSet_setOf_apply_eq n (!false)).inter (measurableSet_setOf_apply_eq (n + 1) false)),
    key true, key false, ← mul_add, hone, mul_one]

lemma mem_eventuallyConst_union_of_eventually_eq {σ : ℕ → Bool}
    (h : ∀ᶠ n in atTop, σ n = σ (n + 1)) :
    σ ∈ eventuallyConst true ∪ eventuallyConst false := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨m, hm⟩ := h
  have hconst : ∀ n, m ≤ n → σ n = σ m := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ k hk ih => exact (hm k hk).symm.trans ih
  cases hσm : σ m with
  | true =>
    exact Or.inl (Filter.eventually_atTop.2 ⟨m, fun n hn ↦ (hconst n hn).trans hσm⟩)
  | false =>
    exact Or.inr (Filter.eventually_atTop.2 ⟨m, fun n hn ↦ (hconst n hn).trans hσm⟩)

/-- **Georgii (6.4), step 3, conclusion.** Under (6.1), `∑_n μ(σ_n ≠ σ_{n+1}) < ∞` for every
Gibbs measure `μ`, so by Borel–Cantelli `μ(A₋ ∪ A₊) = 1`: every Gibbs measure of the chain is
carried by the eventually-constant configurations. -/
theorem apply_eventuallyConst_union_eq_one
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) :
    μ (eventuallyConst true ∪ eventuallyConst false) = 1 := by
  have hnonneg : ∀ n, (0 : ℝ) ≤ (1 - Real.tanh (J n)) / 2 := fun n ↦ by
    have := Real.tanh_lt_one (J n)
    linarith
  have hsummable : Summable fun n ↦ (1 - Real.tanh (J n)) / 2 :=
    Summable.of_nonneg_of_le hnonneg
      (fun n ↦ by linarith [Real.one_sub_tanh_le_two_mul_exp (J n)]) h61
  have htsum : (∑' n, μ {σ : ℕ → Bool | σ n ≠ σ (n + 1)}) ≠ ⊤ := by
    rw [tsum_congr fun n ↦ apply_setOf_ne_of_isGibbsMeasure hμ n,
      ← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
    exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ σ ∂μ, σ ∈ eventuallyConst true ∪ eventuallyConst false := by
    filter_upwards [ae_finite_setOfPred_mem (μ := μ)
      (s := fun n ↦ {σ : ℕ → Bool | σ n ≠ σ (n + 1)}) htsum] with σ hσ
    refine mem_eventuallyConst_union_of_eventually_eq (Filter.eventually_atTop.2 ?_)
    obtain ⟨M, hM⟩ := hσ.bddAbove
    refine ⟨M + 1, fun n hn ↦ ?_⟩
    by_contra hne
    exact absurd (hM (show n ∈ {i | σ i ≠ σ (i + 1)} from hne)) (by omega)
  rw [← prob_compl_eq_zero_iff
    ((measurableSet_eventuallyConst true).union (measurableSet_eventuallyConst false))]
  exact ae_iff.1 hae

/-! ### Step 3 of Georgii (6.4), conclusion: `𝒢(Φ) = [μ₋, μ₊]` -/

lemma disjoint_eventuallyConst : Disjoint (eventuallyConst true) (eventuallyConst false) := by
  refine Set.disjoint_left.2 fun σ h1 h2 ↦ ?_
  have h : ∀ᶠ _n : ℕ in atTop, (true : Bool) = false := by
    filter_upwards [mem_eventuallyConst_iff.1 h1, mem_eventuallyConst_iff.1 h2] with n ha hb
    rw [← ha, hb]
  obtain ⟨-, hn⟩ := h.exists
  exact Bool.noConfusion hn

/-- Under (6.1) the two tail events `A₊` and `A₋` partition the configuration space up to a
`μ`-null set, for every Gibbs measure `μ` of the chain. -/
lemma apply_eventuallyConst_true_add_false (h61 : Summable fun n ↦ Real.exp (-2 * J n))
    {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) :
    μ (eventuallyConst true) + μ (eventuallyConst false) = 1 := by
  rw [← measure_union disjoint_eventuallyConst (measurableSet_eventuallyConst false)]
  exact apply_eventuallyConst_union_eq_one h61 hμ

/-- **Georgii (6.4), step 3, on a local event.** With `μ₊` the local limit of `γ_{Λ_N}(·|ω)`
along `A₊` and `μ₋ = τ(μ₊)`, every Gibbs measure `μ` of the chain satisfies
`μ(A) = μ(A₊) μ₊(A) + μ(A₋) μ₋(A)` for every local event `A`.  Proof: the DLR equation gives
`μ(A) = ∫ μ(dω) γ_{Λ_N}(A|ω)` for every `N`; by (6.1) the integrand converges `μ`-a.e. to
`1_{A₊} μ₊(A) + 1_{A₋} μ₋(A)`, and dominated convergence (the integrand is bounded by `1`)
concludes. -/
theorem apply_eq_of_isGibbsMeasure (h61 : Summable fun n ↦ Real.exp (-2 * J n))
    {μplus : Measure (ℕ → Bool)}
    (hplus : ∀ A ∈ localEvents ℕ Bool, ∀ ω ∈ eventuallyConst true,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 (μplus A)))
    {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ)
    {A : Set (ℕ → Bool)} (hA : A ∈ localEvents ℕ Bool) :
    μ A = μ (eventuallyConst true) * μplus A
      + μ (eventuallyConst false) * (μplus.map chainFlip.toFun) A := by
  classical
  set γ := isingChainSpecification J with hγ
  set μminus := μplus.map chainFlip.toFun with hμminus
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  set F : ℕ → (ℕ → Bool) → ℝ≥0∞ := fun N ω ↦ γ (Finset.range N) ω A with hF
  set f : (ℕ → Bool) → ℝ≥0∞ := fun ω ↦
    (eventuallyConst true).indicator (fun _ ↦ μplus A) ω
      + (eventuallyConst false).indicator (fun _ ↦ μminus A) ω with hf
  have hFmeas : ∀ N, Measurable (F N) := fun N ↦ Specification.measurable_apply_kernel γ _ hAm
  have hconst : ∀ N, ∫⁻ ω, F N ω ∂μ = μ A := fun N ↦ by
    rw [hF, ← Measure.bind_apply hAm (γ.measurable_kernel_toMeasure _).aemeasurable,
      Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμ (Finset.range N)]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun N ↦ F N ω) atTop (𝓝 (f ω)) := by
    have hfull : μ (eventuallyConst true ∪ eventuallyConst false)ᶜ = 0 :=
      (prob_compl_eq_zero_iff ((measurableSet_eventuallyConst true).union
        (measurableSet_eventuallyConst false))).2 (apply_eventuallyConst_union_eq_one h61 hμ)
    filter_upwards [(ae_iff (μ := μ)).2 hfull] with ω hω
    rcases hω with hω | hω
    · have hval : f ω = μplus A := by
        rw [hf]
        simp only
        rw [Set.indicator_of_mem hω,
          Set.indicator_of_notMem (Set.disjoint_left.1 disjoint_eventuallyConst hω), add_zero]
      rw [hval]
      exact hplus A hA ω hω
    · have hval : f ω = μminus A := by
        rw [hf]
        simp only
        rw [Set.indicator_of_notMem
          (fun h ↦ Set.disjoint_left.1 disjoint_eventuallyConst h hω),
          Set.indicator_of_mem hω, zero_add]
      rw [hval]
      exact tendsto_map_chainFlip_of_tendsto hplus hA hω
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ) (F := F) (f := f)
    (fun _ ↦ 1) hFmeas (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ prob_le_one)
    (by simp) hlim
  have hcv : Tendsto (fun N : ℕ ↦ ∫⁻ ω, F N ω ∂μ) atTop (𝓝 (μ A)) := by
    simp only [hconst]
    exact tendsto_const_nhds
  have hint : ∫⁻ ω, f ω ∂μ
      = μ (eventuallyConst true) * μplus A + μ (eventuallyConst false) * μminus A := by
    rw [hf]
    rw [lintegral_add_left (measurable_const.indicator (measurableSet_eventuallyConst true)),
      lintegral_indicator (measurableSet_eventuallyConst true),
      lintegral_indicator (measurableSet_eventuallyConst false), setLIntegral_const,
      setLIntegral_const]
    ring
  exact (tendsto_nhds_unique hcv hdom).trans hint

/-- **Georgii (6.4), step 3.** Every Gibbs measure of the inhomogeneous Ising chain is the
mixture `μ = μ(A₊) μ₊ + μ(A₋) μ₋` of the two phases. -/
theorem eq_smul_add_smul_of_isGibbsMeasure (h61 : Summable fun n ↦ Real.exp (-2 * J n))
    {μplus : Measure (ℕ → Bool)}
    (hplus : ∀ A ∈ localEvents ℕ Bool, ∀ ω ∈ eventuallyConst true,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 (μplus A)))
    {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) :
    μ = μ (eventuallyConst true) • μplus
      + μ (eventuallyConst false) • (μplus.map chainFlip.toFun) := by
  refine Measure.ext_of_generateFrom_of_iUnion_univ (localEvents ℕ Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders _) (by simp) fun A hA ↦ ?_
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact apply_eq_of_isGibbsMeasure h61 hplus hμ hA

/-! ### Georgii, Theorem (6.4) -/

/-- **Georgii, Theorem (6.4).** For the inhomogeneous nearest-neighbour Ising chain (6.2) on
`S = ℕ` with couplings `J_n > 0` satisfying (6.1) `∑_n e^{-2J_n} < ∞`,
`𝒢(Φ) = [μ₋, μ₊] = {s μ₊ + (1-s) μ₋ : 0 ≤ s ≤ 1}`,
where `μ₋ = τ(μ₊)` is the image of `μ₊` under the spin flip (6.3), `μ₊(σ_n) > 0` for every site
`n` (so that `μ₊(σ_n) > 0 > μ₋(σ_n)`), and consequently `μ₊ ≠ μ₋`: the chain exhibits a phase
transition with breaking of the spin-flip symmetry. -/
theorem exists_G_isingChainSpecification_eq (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μplus ∈ G (isingChainSpecification J), ∃ μminus ∈ G (isingChainSpecification J),
      μminus = μplus.map chainFlip.toFun ∧
        (∀ n : ℕ, 0 < ∫ ω, spin (ω n) ∂μplus) ∧
        (∀ n : ℕ, ∫ ω, spin (ω n) ∂μminus < 0) ∧
        μplus ≠ μminus ∧
        G (isingChainSpecification J)
          = {μ | ∃ s : ℝ≥0∞, s ≤ 1 ∧ μ = s • μplus + (1 - s) • μminus} := by
  classical
  obtain ⟨μp, hμpGP, hlim⟩ := exists_mem_GP_tendsto h61
  set μplus : Measure (ℕ → Bool) := (μp : Measure (ℕ → Bool)) with hμplus
  have hprobP : IsProbabilityMeasure μplus := μp.2
  set μminus : Measure (ℕ → Bool) := μplus.map chainFlip.toFun with hμminus
  have hprobM : IsProbabilityMeasure μminus :=
    Measure.isProbabilityMeasure_map chainFlip.measurable_toFun.aemeasurable
  have hplusG : μplus ∈ G (isingChainSpecification J) := ⟨hprobP, hμpGP⟩
  have hminusG : μminus ∈ G (isingChainSpecification J) :=
    ⟨hprobM, (isInvariant_chainFlip (J := J)).map_isGibbsMeasure hμpGP⟩
  have hmagP : ∀ n : ℕ, 0 < ∫ ω, spin (ω n) ∂μplus := by
    intro n
    obtain ⟨T, hT, hTeq⟩ := exists_apply_setOf_true_of_tendsto hJ h61 hlim n
    rw [integral_spin_apply _ n, hTeq, ENNReal.toReal_ofReal (by positivity)]
    linarith
  have hmagM : ∀ n : ℕ, ∫ ω, spin (ω n) ∂μminus < 0 := fun n ↦ by
    rw [hμminus, integral_spin_map_chainFlip n]
    linarith [hmagP n]
  refine ⟨μplus, hplusG, μminus, hminusG, rfl, hmagP, hmagM, ?_, ?_⟩
  · intro hcon
    have h0 := hmagP 0
    rw [hcon] at h0
    linarith [hmagM 0]
  refine Set.ext fun μ ↦ ⟨?_, ?_⟩
  · rintro ⟨hprob, hG⟩
    have := hprob
    refine ⟨μ (eventuallyConst true), prob_le_one, ?_⟩
    have hcompl : μ (eventuallyConst false) = 1 - μ (eventuallyConst true) :=
      ENNReal.eq_sub_of_add_eq (measure_ne_top μ _)
        (by rw [add_comm]; exact apply_eventuallyConst_true_add_false h61 hG)
    rw [← hcompl]
    exact eq_smul_add_smul_of_isGibbsMeasure h61 hlim hG
  · rintro ⟨s, hs, rfl⟩
    have hν : ∀ i : Fin 2, ![μplus, μminus] i ∈ G (isingChainSpecification J) := by
      intro i
      fin_cases i
      · exact hplusG
      · exact hminusG
    have hc : ∑ i : Fin 2, ![s, 1 - s] i = 1 := by
      simp [Fin.sum_univ_two, add_tsub_cancel_of_le hs]
    simpa [Fin.sum_univ_two] using sum_smul_mem_G hν hc

/-! ### Georgii, Comment (6.7)(2): condition (6.1) is also necessary

If `∑_n e^{-2 J_n} = ∞` then `∏_{i ≥ n} tanh J_i = 0` for every `n`, so by (6.6) the limit of
`γ_{Λ_N}(·|ω)` exists and does not depend on the boundary condition `ω` *at all*; the dominated
convergence argument of step 3 then gives `|𝒢(Φ)| = 1`.  Together with Theorem (6.4) this says
that (6.1) is necessary as well as sufficient for a phase transition. -/

/-- **Georgii, Comment (6.7)(2).** If (6.1) fails then, for every local event `A`, the
finite-volume Gibbs distributions `γ_{Λ_N}(A|ω)` converge to a limit that does not depend on the
boundary condition `ω` at all. -/
theorem exists_tendsto_isingChainSpecification_range_apply_of_not_summable (hJ : ∀ n, 0 < J n)
    (h61 : ¬ Summable fun n ↦ Real.exp (-2 * J n)) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    ∃ a : ℝ≥0∞, ∀ ω : ℕ → Bool,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 a) := by
  classical
  obtain ⟨n, hAn⟩ := exists_measurableSet_cylinderEvents_range hA
  set aT := isingChainSpecification J (Finset.range n) (constConfig true) A with haT
  set aF := isingChainSpecification J (Finset.range n) (constConfig false) A with haF
  have haTtop : aT ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have haFtop : aF ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
  have hP := Real.tendsto_prod_Ico_tanh_nhds_zero (fun i ↦ (hJ i).le) h61 n
  refine ⟨aT * ENNReal.ofReal ((1 : ℝ) / 2) + aF * ENNReal.ofReal ((1 : ℝ) / 2), fun ω ↦ ?_⟩
  have hQ : Tendsto (fun N ↦ spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N ↦ ?_) (by simpa using hP.abs)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_spin_le (ω N))
  have hc : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hnum : Tendsto (fun N ↦ (1 + spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)
      atTop (𝓝 ((1 : ℝ) / 2)) := by simpa using (hc.add hQ).div_const 2
  have hden : Tendsto (fun N ↦ (1 - spin (ω N) * ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)
      atTop (𝓝 ((1 : ℝ) / 2)) := by simpa using (hc.sub hQ).div_const 2
  have h1 := (ENNReal.continuous_ofReal.tendsto ((1 : ℝ) / 2)).comp hnum
  have h2 := (ENNReal.continuous_ofReal.tendsto ((1 : ℝ) / 2)).comp hden
  refine (Filter.Tendsto.add (ENNReal.Tendsto.const_mul h1 (Or.inr haTtop))
    (ENNReal.Tendsto.const_mul h2 (Or.inr haFtop))).congr' ?_
  filter_upwards [eventually_gt_atTop n] with N hN
  rw [isingChainSpecification_range_apply_eq hN hAn ω, ← haT, ← haF]
  rfl

/-- If the finite-volume Gibbs distributions converge on a local event `A` to a value `a` that
does not depend on the boundary condition, then every Gibbs measure gives `A` the mass `a`.
This is the dominated convergence step of Georgii's proof of (6.4)(3). -/
lemma apply_eq_of_tendsto_of_isGibbsMeasure {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) {a : ℝ≥0∞}
    (ha : ∀ ω : ℕ → Bool,
      Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop (𝓝 a)) :
    μ A = a := by
  set γ := isingChainSpecification J with hγ
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  have hconst : ∀ N, ∫⁻ ω, γ (Finset.range N) ω A ∂μ = μ A := fun N ↦ by
    rw [← Measure.bind_apply hAm (γ.measurable_kernel_toMeasure _).aemeasurable,
      Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμ (Finset.range N)]
  have hdom := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun N ω ↦ γ (Finset.range N) ω A) (f := fun _ ↦ a) (fun _ ↦ 1)
    (fun _ ↦ Specification.measurable_apply_kernel γ _ hAm)
    (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ prob_le_one) (by simp)
    (Filter.Eventually.of_forall ha)
  have hcv : Tendsto (fun N : ℕ ↦ ∫⁻ ω, γ (Finset.range N) ω A ∂μ) atTop (𝓝 (μ A)) := by
    simp only [hconst]
    exact tendsto_const_nhds
  simpa using tendsto_nhds_unique hcv hdom

/-- **Georgii, Comment (6.7)(2).** If (6.1) fails then the inhomogeneous Ising chain has
*exactly one* Gibbs measure: `|𝒢(Φ)| = 1`.  Hence (6.1) is necessary as well as sufficient for
the phase transition of Theorem (6.4). -/
theorem exists_G_eq_singleton_of_not_summable (hJ : ∀ n, 0 < J n)
    (h61 : ¬ Summable fun n ↦ Real.exp (-2 * J n)) :
    ∃ μ : Measure (ℕ → Bool), G (isingChainSpecification J) = {μ} := by
  obtain ⟨μ, hμGP, -⟩ := exists_mem_GP_eq_of_tendsto (J := J) true
  refine ⟨(μ : Measure (ℕ → Bool)),
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨μ.2, hμGP⟩, fun ν hν ↦ ?_⟩⟩
  obtain ⟨hνp, hνG⟩ := hν
  have := hνp
  refine Measure.ext_of_generateFrom_of_iUnion_univ (localEvents ℕ Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders _) (by simp) fun A hA ↦ ?_
  obtain ⟨a, ha⟩ :=
    exists_tendsto_isingChainSpecification_range_apply_of_not_summable hJ h61 hA
  rw [apply_eq_of_tendsto_of_isGibbsMeasure hνG hA ha,
    apply_eq_of_tendsto_of_isGibbsMeasure (μ := (μ : Measure (ℕ → Bool))) hμGP hA ha]

/-! ### Georgii, Comment (6.7)(1): ground states and the zero-temperature limit

The constant configurations `ω⁺`, `ω⁻` minimise every `Φ_A`, so they are the ground states of
`Φ`.  Since `γ^{βΦ}` is the chain with couplings `βJ` and (6.1) is inherited by `βJ` for
`β ≥ 1`, Theorem (6.4) gives `𝒢(βΦ) = [μ₋^β, μ₊^β]` for all `β ≥ 1`, and Lemma (6.5) gives
`μ₊^β(σ_n) = ∏_{i ≥ n} tanh βJ_i → 1` as `β → ∞`; hence `μ₊^β → δ₊`, `μ₋^β → δ₋` in the
topology of local convergence, and `𝒢(βΦ) → [δ₋, δ₊]`. -/

/-- **Georgii (6.7)(1): `ω⁺` and `ω⁻` are ground states.** For ferromagnetic couplings
`J_n ≥ 0` the constant configurations minimise `Φ_A` for every finite set of sites `A`. -/
theorem isingChainPotential_constConfig_le (hJ : ∀ n, 0 ≤ J n) (A : Finset ℕ) (x : Bool)
    (σ : ℕ → Bool) : isingChainPotential J A (constConfig x) ≤ isingChainPotential J A σ := by
  refine Potential.pairTerms_le_pairTerms (fun i j _ ↦ ?_) A
  simp only [isingChainPair, constConfig_apply]
  split_ifs with h
  · rw [spin_mul_self]
    have : spin (σ i) * spin (σ j) ≤ 1 := by cases σ i <;> cases σ j <;> norm_num [spin]
    nlinarith [hJ i]
  · exact le_rfl

lemma smul_pos_of_pos (hJ : ∀ n, 0 < J n) {β : ℝ} (hβ : 0 < β) (n : ℕ) : 0 < (β • J) n :=
  mul_pos hβ (hJ n)

/-- Under (6.1), the couplings `βJ` satisfy (6.1) for every `β ≥ 1`. -/
lemma summable_exp_neg_two_mul_smul (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {β : ℝ} (hβ : 1 ≤ β) :
    Summable fun n ↦ Real.exp (-2 * (β • J) n) :=
  h61.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) fun n ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Real.exp_le_exp.2 (by nlinarith [hJ n])

/-- **Georgii (6.7)(1): `𝒢(βΦ) = [μ₋^β, μ₊^β]` for `β ≥ 1`.** Theorem (6.4) at inverse
temperature `β ≥ 1`, for the Gibbsian specification `γ^{βΦ}` of the potential (6.2). -/
theorem exists_G_gibbsSpecification_smul_eq (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {β : ℝ} (hβ : 1 ≤ β) :
    ∃ μplus ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
        uniformSpinMeasure β),
      ∃ μminus ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
        uniformSpinMeasure β),
      μminus = μplus.map chainFlip.toFun ∧
        (∀ n : ℕ, 0 < ∫ ω, spin (ω n) ∂μplus) ∧
        (∀ n : ℕ, ∫ ω, spin (ω n) ∂μminus < 0) ∧
        μplus ≠ μminus ∧
        G (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
          uniformSpinMeasure β)
          = {μ | ∃ s : ℝ≥0∞, s ≤ 1 ∧ μ = s • μplus + (1 - s) • μminus} := by
  rw [← isingChainSpecification_smul]
  exact exists_G_isingChainSpecification_eq (smul_pos_of_pos hJ (by linarith))
    (summable_exp_neg_two_mul_smul hJ h61 hβ)

/-! #### The phases `μ₊` and `μ₋ = τ(μ₊)` as named objects -/

variable (J) in
/-- **Georgii's plus phase `μ₊`.** A Gibbs measure of the chain which is a cluster point, in the
topology of local convergence, of `γ_{Λ_N}(· | ω⁺)`, and which takes the limit value on every
local event on which that sequence converges (`exists_mem_GP_eq_of_tendsto`).  For `J_n > 0` the
sequence converges on every local event (`exists_tendsto_isingChainSpecification_range_apply`
under (6.1), `exists_tendsto_isingChainSpecification_range_apply_of_not_summable` otherwise),
so `μ₊ = lim_N γ_{Λ_N}(· | ω⁺)` is then uniquely determined: it is Georgii's `μ₊` of
Theorem (6.4) (`tendsto_isingChainSpecification_range_plusPhase`). -/
def plusPhase : ProbabilityMeasure (ℕ → Bool) :=
  (exists_mem_GP_eq_of_tendsto (J := J) true).choose

lemma plusPhase_mem_GP : plusPhase J ∈ GP (isingChainSpecification J) :=
  (exists_mem_GP_eq_of_tendsto (J := J) true).choose_spec.1

lemma isGibbsMeasure_plusPhase :
    (isingChainSpecification J).IsGibbsMeasure (plusPhase J : Measure (ℕ → Bool)) :=
  plusPhase_mem_GP

lemma plusPhase_apply_eq_of_tendsto {A : Set (ℕ → Bool)} (hA : A ∈ localEvents ℕ Bool)
    {a : ℝ≥0∞}
    (ha : Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) (constConfig true) A)
      atTop (𝓝 a)) :
    (plusPhase J : Measure (ℕ → Bool)) A = a :=
  (exists_mem_GP_eq_of_tendsto (J := J) true).choose_spec.2 A hA a ha

/-- **Georgii (6.4), step 1, for `μ₊`.** Under (6.1), `μ₊ = lim_N γ_{Λ_N}(· | ω)` on every
local event, for every boundary condition `ω ∈ A₊`. -/
theorem tendsto_isingChainSpecification_range_plusPhase
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) {ω : ℕ → Bool} (hω : ω ∈ eventuallyConst true) :
    Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop
      (𝓝 ((plusPhase J : Measure (ℕ → Bool)) A)) := by
  obtain ⟨a, ha⟩ := exists_tendsto_isingChainSpecification_range_apply h61 true hA
  rw [plusPhase_apply_eq_of_tendsto hA (ha _ (constConfig_mem_eventuallyConst true))]
  exact ha ω hω

/-- **Lemma (6.5) in the limit, for `μ₊`.** Under (6.1),
`μ₊(σ_n = +1) = (1 + ∏_{i ≥ n} tanh J_i)/2`. -/
theorem plusPhase_apply_setOf_true (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    (plusPhase J : Measure (ℕ → Bool)) {σ : ℕ → Bool | σ n = true}
      = ENNReal.ofReal ((1 + ∏' k, Real.tanh (J (k + n))) / 2) := by
  obtain ⟨T, hT0, hTend⟩ := tendsto_isingChainSpecification_setOf_true hJ h61 n
  have h61n : Summable fun k ↦ Real.exp (-2 * J (k + n)) :=
    h61.comp_injective (add_left_injective n)
  have hT'pos : 0 < ∏' k, Real.tanh (J (k + n)) := Real.tprod_tanh_pos (fun k ↦ hJ (k + n)) h61n
  have hTend' : Tendsto (fun N ↦ ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) atTop
      (𝓝 (∏' k, Real.tanh (J (k + n)))) :=
    Multipliable.tendsto_prod_Ico_nat (f := fun i ↦ Real.tanh (J i))
      (Real.multipliable_tanh h61n)
  have hT : T = ∏' k, Real.tanh (J (k + n)) := by
    have h2 : Tendsto
        (fun N ↦ isingChainSpecification J (Finset.range N) (constConfig true)
          {σ : ℕ → Bool | σ n = true}) atTop
        (𝓝 (ENNReal.ofReal ((1 + ∏' k, Real.tanh (J (k + n))) / 2))) := by
      have hcont : Tendsto
          (fun N ↦ ENNReal.ofReal ((1 + ∏ i ∈ Finset.Ico n N, Real.tanh (J i)) / 2)) atTop
          (𝓝 (ENNReal.ofReal ((1 + ∏' k, Real.tanh (J (k + n))) / 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((tendsto_const_nhds.add hTend').div_const 2)
      refine hcont.congr' ?_
      filter_upwards [eventually_gt_atTop n] with N hN
      rw [isingChainSpecification_range_apply_setOf_eq hN true (constConfig true)]
      norm_num [constConfig, spin]
    have h3 := tendsto_nhds_unique hTend h2
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)] at h3
    linarith
  rw [← hT]
  exact plusPhase_apply_eq_of_tendsto (setOf_apply_eq_mem_localEvents n true) hTend

/-- **Georgii (6.4)/(6.7)(1): the magnetisation of the plus phase**,
`μ₊(σ_n) = ∏_{i ≥ n} tanh J_i`. -/
theorem integral_spin_plusPhase (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    ∫ ω, spin (ω n) ∂(plusPhase J : Measure (ℕ → Bool)) = ∏' k, Real.tanh (J (k + n)) := by
  have hpos : 0 < ∏' k, Real.tanh (J (k + n)) :=
    Real.tprod_tanh_pos (fun k ↦ hJ (k + n)) (h61.comp_injective (add_left_injective n))
  rw [integral_spin_apply _ n, plusPhase_apply_setOf_true hJ h61 n,
    ENNReal.toReal_ofReal (by linarith)]
  ring


variable (J) in
/-- **Georgii's minus phase `μ₋ = τ(μ₊)`**, the spin-flip image of the plus phase. -/
def minusPhase : ProbabilityMeasure (ℕ → Bool) :=
  (plusPhase J).map chainFlip.measurable_toFun.aemeasurable

lemma minusPhase_toMeasure :
    (minusPhase J : Measure (ℕ → Bool))
      = (plusPhase J : Measure (ℕ → Bool)).map chainFlip.toFun :=
  ProbabilityMeasure.toMeasure_map _ _

lemma minusPhase_mem_GP : minusPhase J ∈ GP (isingChainSpecification J) :=
  (isInvariant_chainFlip (J := J)).map_mem_GP plusPhase_mem_GP

lemma isGibbsMeasure_minusPhase :
    (isingChainSpecification J).IsGibbsMeasure (minusPhase J : Measure (ℕ → Bool)) :=
  minusPhase_mem_GP

/-- **Georgii (6.4), step 2, for `μ₋`.** Under (6.1), `μ₋ = lim_N γ_{Λ_N}(· | ω)` on every
local event, for every boundary condition `ω ∈ A₋`. -/
theorem tendsto_isingChainSpecification_range_minusPhase
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) {ω : ℕ → Bool} (hω : ω ∈ eventuallyConst false) :
    Tendsto (fun N ↦ isingChainSpecification J (Finset.range N) ω A) atTop
      (𝓝 ((minusPhase J : Measure (ℕ → Bool)) A)) := by
  rw [minusPhase_toMeasure]
  exact tendsto_map_chainFlip_of_tendsto
    (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61 hA hω) hA hω

/-- `μ₋(σ_n) = -∏_{i ≥ n} tanh J_i`. -/
theorem integral_spin_minusPhase (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    ∫ ω, spin (ω n) ∂(minusPhase J : Measure (ℕ → Bool)) = -∏' k, Real.tanh (J (k + n)) := by
  rw [minusPhase_toMeasure, integral_spin_map_chainFlip, integral_spin_plusPhase hJ h61]

/-- **Georgii, Theorem (6.4), with the named phases.** Under (6.1),
`𝒢(Φ) = [μ₋, μ₊] = {s μ₊ + (1 - s) μ₋ : 0 ≤ s ≤ 1}`. -/
theorem G_isingChainSpecification_eq
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    G (isingChainSpecification J)
      = {μ | ∃ s : ℝ≥0∞, s ≤ 1 ∧ μ = s • (plusPhase J : Measure (ℕ → Bool))
          + (1 - s) • (minusPhase J : Measure (ℕ → Bool))} := by
  refine Set.ext fun μ ↦ ⟨?_, ?_⟩
  · rintro ⟨hprob, hG⟩
    have := hprob
    refine ⟨μ (eventuallyConst true), prob_le_one, ?_⟩
    have hcompl : μ (eventuallyConst false) = 1 - μ (eventuallyConst true) :=
      ENNReal.eq_sub_of_add_eq (measure_ne_top μ _)
        (by rw [add_comm]; exact apply_eventuallyConst_true_add_false h61 hG)
    rw [← hcompl, minusPhase_toMeasure]
    exact eq_smul_add_smul_of_isGibbsMeasure h61
      (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61 hA hω) hG
  · rintro ⟨s, hs, rfl⟩
    have hν : ∀ i : Fin 2, ![(plusPhase J : Measure (ℕ → Bool)),
        (minusPhase J : Measure (ℕ → Bool))] i ∈ G (isingChainSpecification J) := by
      intro i
      fin_cases i
      · exact ⟨(plusPhase J).2, plusPhase_mem_GP⟩
      · exact ⟨(minusPhase J).2, minusPhase_mem_GP⟩
    have hc : ∑ i : Fin 2, ![s, 1 - s] i = 1 := by
      simp [Fin.sum_univ_two, add_tsub_cancel_of_le hs]
    simpa [Fin.sum_univ_two] using sum_smul_mem_G hν hc

/-! #### The zero-temperature limit `β → ∞` -/

/-- **Georgii (6.7)(1), the analytic input.** Under (6.1), `∑_i e^{-2βJ_i} → 0` as `β → ∞`
(dominated convergence for series, the bound being `e^{-2J_i}` for `β ≥ 1`). -/
theorem tendsto_tsum_exp_neg_two_mul_smul_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    Tendsto (fun β : ℝ ↦ ∑' i, Real.exp (-2 * (β • J) i)) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (β : ℝ) (i : ℕ) ↦ Real.exp (-2 * (β • J) i)) (g := fun _ ↦ (0 : ℝ)) h61
    (fun i ↦ ?_) ?_
  · simpa using h
  · simp only [Pi.smul_apply, smul_eq_mul]
    refine Real.tendsto_exp_atBot.comp ?_
    have : Tendsto (fun β : ℝ ↦ β * (-2 * J i)) atTop atBot :=
      Tendsto.atTop_mul_const_of_neg (by linarith [hJ i]) tendsto_id
    exact this.congr fun β ↦ by ring
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ i
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Real.exp_le_exp.2 (by nlinarith [hJ i])

/-- **Georgii (6.7)(1): `lim_{β → ∞} ∏_{i ≥ n} tanh βJ_i = 1`.** -/
theorem tendsto_tprod_tanh_smul_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    Tendsto (fun β : ℝ ↦ ∏' k, Real.tanh ((β • J) (k + n))) atTop (𝓝 1) := by
  have hc := tendsto_tsum_exp_neg_two_mul_smul_atTop hJ h61
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun β ↦ 1 - 2 * ∑' i,
    Real.exp (-2 * (β • J) i)) (h := fun _ ↦ 1) ?_ tendsto_const_nhds ?_ ?_
  · simpa using (hc.const_mul 2).const_sub 1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    have hβJ := summable_exp_neg_two_mul_smul hJ h61 hβ
    have h1 : 1 - ∏' k, Real.tanh ((β • J) (k + n)) ≤ 2 * ∑' k, Real.exp (-2 * (β • J) (k + n)) :=
      Real.one_sub_tprod_tanh_le (fun k ↦ (smul_pos_of_pos hJ (by linarith) (k + n)).le)
        (hβJ.comp_injective (add_left_injective n))
    have h2 : ∑' k, Real.exp (-2 * (β • J) (k + n)) ≤ ∑' i, Real.exp (-2 * (β • J) i) :=
      tsum_comp_le_tsum_of_inj hβJ (fun _ ↦ (Real.exp_pos _).le) (add_left_injective n)
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact tprod_le_one₀ (fun k ↦ Real.tanh_nonneg (smul_pos_of_pos hJ (by linarith) (k + n)).le)
      fun _ ↦ (Real.tanh_lt_one _).le

/-- **Georgii (6.7)(1): `lim_{β → ∞} μ₊^β(σ_n) = 1`** for every site `n`. -/
theorem tendsto_integral_spin_plusPhase_smul_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (n : ℕ) :
    Tendsto (fun β : ℝ ↦ ∫ ω, spin (ω n) ∂(plusPhase (β • J) : Measure (ℕ → Bool))) atTop
      (𝓝 1) := by
  refine (tendsto_tprod_tanh_smul_atTop hJ h61 n).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
  exact (integral_spin_plusPhase (smul_pos_of_pos hJ (by linarith))
    (summable_exp_neg_two_mul_smul hJ h61 hβ) n).symm

/-- The per-site estimate behind the zero-temperature limit: under (6.1),
`μ₊(σ_a ≠ +1) = (1 - ∏_{i ≥ a} tanh J_i)/2 ≤ ∑_i e^{-2J_i}`, uniformly in the site `a`. -/
theorem plusPhase_real_ne_le (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (a : ℕ) :
    (plusPhase J : Measure (ℕ → Bool)).real {ζ : ℕ → Bool | ζ a ≠ constConfig true a}
      ≤ ∑' i, Real.exp (-2 * J i) := by
  have hprob : IsProbabilityMeasure (plusPhase J : Measure (ℕ → Bool)) := (plusPhase J).2
  have hset : {ζ : ℕ → Bool | ζ a ≠ constConfig true a} = {ζ : ℕ → Bool | ζ a = true}ᶜ := by
    ext ζ; simp
  have h61a : Summable fun k ↦ Real.exp (-2 * J (k + a)) :=
    h61.comp_injective (add_left_injective a)
  have hpos : 0 < ∏' k, Real.tanh (J (k + a)) := Real.tprod_tanh_pos (fun k ↦ hJ (k + a)) h61a
  have hle : ∏' k, Real.tanh (J (k + a)) ≤ 1 :=
    tprod_le_one₀ (fun k ↦ Real.tanh_nonneg (hJ (k + a)).le) fun _ ↦ (Real.tanh_lt_one _).le
  have h1 : 1 - ∏' k, Real.tanh (J (k + a)) ≤ 2 * ∑' k, Real.exp (-2 * J (k + a)) :=
    Real.one_sub_tprod_tanh_le (fun k ↦ (hJ (k + a)).le) h61a
  have h2 : ∑' k, Real.exp (-2 * J (k + a)) ≤ ∑' i, Real.exp (-2 * J i) :=
    tsum_comp_le_tsum_of_inj h61 (fun _ ↦ (Real.exp_pos _).le) (add_left_injective a)
  rw [hset, measureReal_def, prob_compl_eq_one_sub (measurableSet_setOf_apply_eq a true),
    plusPhase_apply_setOf_true hJ h61 a,
    ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 (by linarith)) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith)]
  linarith

/-- The same estimate for the minus phase: `μ₋(σ_a ≠ -1) ≤ ∑_i e^{-2J_i}`. -/
theorem minusPhase_real_ne_le (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) (a : ℕ) :
    (minusPhase J : Measure (ℕ → Bool)).real {ζ : ℕ → Bool | ζ a ≠ constConfig false a}
      ≤ ∑' i, Real.exp (-2 * J i) := by
  have hmeas : MeasurableSet {ζ : ℕ → Bool | ζ a ≠ constConfig false a} :=
    measurableSet_ne_apply _ a
  rw [minusPhase_toMeasure, measureReal_def, Measure.map_apply chainFlip.measurable_toFun hmeas,
    ← measureReal_def]
  refine le_of_eq_of_le ?_ (plusPhase_real_ne_le hJ h61 a)
  congr 1
  ext ζ
  simp

/-- **Georgii (6.7)(1): `lim_{β → ∞} μ₊^β = δ₊`** in the topology of local convergence, measured
by the metric `localDist` of Remark (4.3)(3). -/
theorem tendsto_localDist_plusPhase_smul_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    Tendsto (fun β : ℝ ↦ localDist (plusPhase (β • J)) (diracProb (constConfig true))) atTop
      (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun β ↦ ∑' i, Real.exp (-2 * (β • J) i))
    (tendsto_tsum_exp_neg_two_mul_smul_atTop hJ h61) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ a
  exact plusPhase_real_ne_le (smul_pos_of_pos hJ (by linarith))
    (summable_exp_neg_two_mul_smul hJ h61 hβ) a

/-- **Georgii (6.7)(1): `lim_{β → ∞} μ₋^β = δ₋`** in the topology of local convergence. -/
theorem tendsto_localDist_minusPhase_smul_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    Tendsto (fun β : ℝ ↦ localDist (minusPhase (β • J)) (diracProb (constConfig false))) atTop
      (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun β ↦ ∑' i, Real.exp (-2 * (β • J) i))
    (tendsto_tsum_exp_neg_two_mul_smul_atTop hJ h61) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ a
  exact minusPhase_real_ne_le (smul_pos_of_pos hJ (by linarith))
    (summable_exp_neg_two_mul_smul hJ h61 hβ) a


/-- Local convergence `μ₊^β → δ₊`, evaluated on a local event. -/
theorem tendsto_plusPhase_smul_apply_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    Tendsto (fun β : ℝ ↦ (plusPhase (β • J) : Measure (ℕ → Bool)) A) atTop
      (𝓝 (Measure.dirac (constConfig true) A)) :=
  tendsto_withLocalConvergence_iff.1
    (tendsto_withLocalConvergence_iff_tendsto_localDist.2
      (tendsto_localDist_plusPhase_smul_atTop hJ h61)) A hA

/-- Local convergence `μ₋^β → δ₋`, evaluated on a local event. -/
theorem tendsto_minusPhase_smul_apply_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    Tendsto (fun β : ℝ ↦ (minusPhase (β • J) : Measure (ℕ → Bool)) A) atTop
      (𝓝 (Measure.dirac (constConfig false) A)) :=
  tendsto_withLocalConvergence_iff.1
    (tendsto_withLocalConvergence_iff_tendsto_localDist.2
      (tendsto_localDist_minusPhase_smul_atTop hJ h61)) A hA

/-- **Georgii (6.7)(1): `lim_{β → ∞} 𝒢(βΦ) = [δ₋, δ₊]`, the segment converges.** Every point
`s μ₊^β + (1 - s) μ₋^β` of `𝒢(βΦ) = [μ₋^β, μ₊^β]` converges locally, as `β → ∞`, to the
corresponding point `s δ₊ + (1 - s) δ₋` of `[δ₋, δ₊]`. -/
theorem tendsto_smul_plusPhase_add_smul_minusPhase_atTop (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {s : ℝ≥0∞} (hs : s ≤ 1) {A : Set (ℕ → Bool)}
    (hA : A ∈ localEvents ℕ Bool) :
    Tendsto (fun β : ℝ ↦ (s • (plusPhase (β • J) : Measure (ℕ → Bool))
        + (1 - s) • (minusPhase (β • J) : Measure (ℕ → Bool))) A) atTop
      (𝓝 ((s • Measure.dirac (constConfig true)
        + (1 - s) • Measure.dirac (constConfig false)) A)) := by
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (ENNReal.Tendsto.const_mul (tendsto_plusPhase_smul_apply_atTop hJ h61 hA)
      (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top hs))).add
    (ENNReal.Tendsto.const_mul (tendsto_minusPhase_smul_apply_atTop hJ h61 hA)
      (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)))

/-- **Georgii (6.7)(1): `lim_{β → ∞} 𝒢(βΦ) = [δ₋, δ₊]`, the endpoints.** In Georgii's distance
`d(F, μ) = inf_{ν ∈ F} d(ν, μ)` from a set of random fields (as in Theorem (6.9)),
`d(𝒢(βΦ), δ₊) → 0` and `d(𝒢(βΦ), δ₋) → 0` as `β → ∞`. -/
theorem tendsto_localDistSet_GP_gibbsSpecification_dirac (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    Tendsto (fun β : ℝ ↦ localDistSet
      (GP (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
        uniformSpinMeasure β)) (diracProb (constConfig true))) atTop (𝓝 0) ∧
    Tendsto (fun β : ℝ ↦ localDistSet
      (GP (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
        uniformSpinMeasure β)) (diracProb (constConfig false))) atTop (𝓝 0) := by
  constructor
  · refine tendsto_localDistSet_diracProb (μs := fun β ↦ plusPhase (β • J))
      (fun β ↦ isingChainSpecification_smul J β ▸ plusPhase_mem_GP)
      (c := fun β ↦ ∑' i, Real.exp (-2 * (β • J) i))
      (tendsto_tsum_exp_neg_two_mul_smul_atTop hJ h61) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ a
    exact plusPhase_real_ne_le (smul_pos_of_pos hJ (by linarith))
      (summable_exp_neg_two_mul_smul hJ h61 hβ) a
  · refine tendsto_localDistSet_diracProb (μs := fun β ↦ minusPhase (β • J))
      (fun β ↦ isingChainSpecification_smul J β ▸ minusPhase_mem_GP)
      (c := fun β ↦ ∑' i, Real.exp (-2 * (β • J) i))
      (tendsto_tsum_exp_neg_two_mul_smul_atTop hJ h61) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ a
    exact minusPhase_real_ne_le (smul_pos_of_pos hJ (by linarith))
      (summable_exp_neg_two_mul_smul hJ h61 hβ) a


/-- **Georgii (6.4), step 3, at inverse temperature `β ≥ 1`.** Every Gibbs measure of `γ^{βΦ}`
is the mixture `μ = μ(A₊) μ₊^β + μ(A₋) μ₋^β`, with `μ(A₊) + μ(A₋) = 1`. -/
theorem eq_smul_plusPhase_add_smul_minusPhase_of_mem_G (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {β : ℝ} (hβ : 1 ≤ β) {μ : Measure (ℕ → Bool)}
    (hμ : μ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
      uniformSpinMeasure β)) :
    μ = μ (eventuallyConst true) • (plusPhase (β • J) : Measure (ℕ → Bool))
        + μ (eventuallyConst false) • (minusPhase (β • J) : Measure (ℕ → Bool))
      ∧ μ (eventuallyConst true) + μ (eventuallyConst false) = 1 := by
  rw [← isingChainSpecification_smul] at hμ
  obtain ⟨hprob, hG⟩ := hμ
  have hJ' := smul_pos_of_pos hJ (show (0 : ℝ) < β by linarith)
  have h61' := summable_exp_neg_two_mul_smul hJ h61 hβ
  refine ⟨?_, apply_eventuallyConst_true_add_false h61' hG⟩
  rw [minusPhase_toMeasure]
  exact eq_smul_add_smul_of_isGibbsMeasure h61'
    (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61' hA hω) hG

/-- **Georgii (6.7)(1): `lim_{β → ∞} 𝒢(βΦ) ⊆ [δ₋, δ₊]`.** If `μ^β ∈ 𝒢(βΦ)` for all `β ≥ 1`
and `μ^β → ν` in the topology of local convergence as `β → ∞`, then `ν ∈ [δ₋, δ₊]`. Together
with `tendsto_smul_plusPhase_add_smul_minusPhase_atTop` (every point of `[δ₋, δ₊]` is such a
limit) this is Georgii's `lim_{β → ∞} 𝒢(βΦ) = [δ₋, δ₊]`. -/
theorem exists_eq_smul_dirac_add_smul_dirac_of_tendsto (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {μ : ℝ → Measure (ℕ → Bool)}
    (hμ : ∀ β : ℝ, 1 ≤ β → μ β ∈ G (gibbsSpecificationOfAbsolutelySummable
      (Φ := isingChainPotential J) uniformSpinMeasure β))
    {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hlim : ∀ A ∈ localEvents ℕ Bool, Tendsto (fun β ↦ μ β A) atTop (𝓝 (ν A))) :
    ∃ s : ℝ≥0∞, s ≤ 1 ∧ ν = s • Measure.dirac (constConfig true)
      + (1 - s) • Measure.dirac (constConfig false) := by
  set A₀ : Set (ℕ → Bool) := {σ | σ 0 = true} with hA₀
  have hA₀m : MeasurableSet A₀ := measurableSet_setOf_apply_eq 0 true
  have hA₀l : A₀ ∈ localEvents ℕ Bool := setOf_apply_eq_mem_localEvents 0 true
  set p : ℝ → ℝ≥0∞ := fun β ↦ μ β (eventuallyConst true) with hp
  set q : ℝ → ℝ≥0∞ := fun β ↦ μ β (eventuallyConst false) with hq
  set s : ℝ≥0∞ := ν A₀ with hs
  have hs1 : s ≤ 1 := prob_le_one
  have hmix : ∀ β : ℝ, 1 ≤ β → ∀ A, MeasurableSet A →
      μ β A = p β * (plusPhase (β • J) : Measure (ℕ → Bool)) A
        + q β * (minusPhase (β • J) : Measure (ℕ → Bool)) A := fun β hβ A _ ↦ by
    have h := (eq_smul_plusPhase_add_smul_minusPhase_of_mem_G hJ h61 hβ (hμ β hβ)).1
    conv_lhs => rw [h]
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rfl
  have hpq : ∀ β : ℝ, 1 ≤ β → p β + q β = 1 := fun β hβ ↦
    (eq_smul_plusPhase_add_smul_minusPhase_of_mem_G hJ h61 hβ (hμ β hβ)).2
  have hp1 : ∀ β : ℝ, 1 ≤ β → p β ≤ 1 := fun β hβ ↦ (hpq β hβ) ▸ le_self_add
  have hq1 : ∀ β : ℝ, 1 ≤ β → q β ≤ 1 := fun β hβ ↦ (hpq β hβ) ▸ le_add_self
  -- the limits of the phases on `A₀`
  have hplus : Tendsto (fun β : ℝ ↦ (plusPhase (β • J) : Measure (ℕ → Bool)) A₀) atTop (𝓝 1) := by
    have := tendsto_plusPhase_smul_apply_atTop hJ h61 hA₀l
    rwa [Measure.dirac_apply_of_mem (show constConfig true ∈ A₀ from rfl)] at this
  have hminus : Tendsto (fun β : ℝ ↦ (minusPhase (β • J) : Measure (ℕ → Bool)) A₀) atTop
      (𝓝 0) := by
    have := tendsto_minusPhase_smul_apply_atTop hJ h61 hA₀l
    rwa [Measure.dirac_apply' _ hA₀m,
      Set.indicator_of_notMem (show constConfig false ∉ A₀ by simp [A₀, constConfig])] at this
  -- `p β → s`, by a sandwich
  have hptend : Tendsto p atTop (𝓝 s) := by
    have hlow : Tendsto (fun β ↦ μ β A₀ - (minusPhase (β • J) : Measure (ℕ → Bool)) A₀) atTop
        (𝓝 s) := by
      have := ENNReal.Tendsto.sub (hlim A₀ hA₀l) hminus (Or.inr ENNReal.zero_ne_top)
      rwa [tsub_zero] at this
    have hup : Tendsto (fun β ↦ μ β A₀ + (1 - (plusPhase (β • J) : Measure (ℕ → Bool)) A₀))
        atTop (𝓝 s) := by
      have := (hlim A₀ hA₀l).add (ENNReal.Tendsto.sub tendsto_const_nhds hplus
        (Or.inl ENNReal.one_ne_top))
      rwa [tsub_self, add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      rw [tsub_le_iff_right, hmix β hβ A₀ hA₀m]
      calc p β * (plusPhase (β • J) : Measure (ℕ → Bool)) A₀
            + q β * (minusPhase (β • J) : Measure (ℕ → Bool)) A₀
          ≤ p β * 1 + 1 * (minusPhase (β • J) : Measure (ℕ → Bool)) A₀ := by
            gcongr
            · exact prob_le_one
            · exact hq1 β hβ
        _ = p β + (minusPhase (β • J) : Measure (ℕ → Bool)) A₀ := by rw [mul_one, one_mul]
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      rw [hmix β hβ A₀ hA₀m]
      calc p β = p β * ((plusPhase (β • J) : Measure (ℕ → Bool)) A₀
            + (1 - (plusPhase (β • J) : Measure (ℕ → Bool)) A₀)) := by
            rw [add_tsub_cancel_of_le prob_le_one, mul_one]
        _ = p β * (plusPhase (β • J) : Measure (ℕ → Bool)) A₀
            + p β * (1 - (plusPhase (β • J) : Measure (ℕ → Bool)) A₀) := mul_add _ _ _
        _ ≤ (p β * (plusPhase (β • J) : Measure (ℕ → Bool)) A₀
            + q β * (minusPhase (β • J) : Measure (ℕ → Bool)) A₀)
            + 1 * (1 - (plusPhase (β • J) : Measure (ℕ → Bool)) A₀) := by
            gcongr
            · exact le_self_add
            · exact hp1 β hβ
        _ = _ := by rw [one_mul]
  have hqtend : Tendsto q atTop (𝓝 (1 - s)) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hptend
      (Or.inl ENNReal.one_ne_top)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact (ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hp1 β hβ))
      (by rw [add_comm]; exact hpq β hβ)).symm
  -- identify `ν` on the local events
  refine ⟨s, hs1, Measure.ext_of_generateFrom_of_iUnion_univ (localEvents ℕ Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders _) (by simp) fun A hA ↦ ?_⟩
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  have h1 : Tendsto (fun β ↦ μ β A) atTop
      (𝓝 (s * Measure.dirac (constConfig true) A
        + (1 - s) * Measure.dirac (constConfig false) A)) := by
    have hconv := (ENNReal.Tendsto.mul hptend (Or.inr (measure_ne_top _ _))
        (tendsto_plusPhase_smul_apply_atTop hJ h61 hA)
        (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top hs1))).add
      (ENNReal.Tendsto.mul hqtend (Or.inr (measure_ne_top _ _))
        (tendsto_minusPhase_smul_apply_atTop hJ h61 hA)
        (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)))
    refine hconv.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
    exact (hmix β hβ A hAm).symm
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact tendsto_nhds_unique (hlim A hA) h1

/-! ### Georgii, Comment (6.7)(3): disjoint tail supports, and percolation

Step 3 of (6.4) also gives `μ₊(A₊) = μ₋(A₋) = 1`: the two extreme points `μ₊`, `μ₋` are carried
by the disjoint tail events `A₊`, `A₋`, which the spin flip `τ` exchanges.  Moreover
`ω ∈ A₊ ∪ A₋` iff the random graph `G(ω)` on `ℕ` with the bonds `{i, i+1}` satisfying
`ω_i = ω_{i+1}` — the bonds on which `Φ_{{i,i+1}}` attains its minimum — has an (automatically
unique) infinite connected component; so every Gibbs measure percolates. -/

/-- The spin flip exchanges `A₊` and `A₋`. -/
lemma preimage_chainFlip_eventuallyConst (x : Bool) :
    chainFlip.toFun ⁻¹' eventuallyConst x = eventuallyConst (!x) := by
  ext σ
  simp only [Set.mem_preimage, mem_eventuallyConst_iff, chainFlip_toFun_apply]
  exact Filter.eventually_congr
    (Filter.Eventually.of_forall fun n ↦ by cases σ n <;> cases x <;> simp)

lemma eventuallyConst_eq_iUnion_iInter (x : Bool) (M : ℕ) :
    eventuallyConst x = ⋃ m ∈ Set.Ici M, ⋂ n ∈ Set.Ici m, {σ : ℕ → Bool | σ n = x} := by
  ext σ
  simp only [eventuallyConst, Set.mem_ofPred_eq, Filter.eventually_atTop, Set.mem_iUnion,
    Set.mem_iInter, Set.mem_Ici, exists_prop]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨max m M, le_max_right _ _, fun n hn ↦ hm n ((le_max_left _ _).trans hn)⟩
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm⟩

/-- **Georgii (6.7)(3): `A₊` and `A₋` are tail events.** -/
lemma measurableSet_tail_eventuallyConst (x : Bool) :
    MeasurableSet[@tailSigmaAlgebra ℕ Bool _] (eventuallyConst x) := by
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ ?_
  rw [eventuallyConst_eq_iUnion_iInter x (Λ.sup id + 1)]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦
    MeasurableSet.biInter (Set.to_countable _) fun n hn ↦ ?_
  have hn' : n ∈ ((Λ : Set ℕ))ᶜ := by
    intro hnΛ
    have := Finset.le_sup (f := id) hnΛ
    simp only [id_eq, Set.mem_Ici] at this hm hn
    omega
  exact measurable_cylinderEvent_apply (X := fun _ : ℕ ↦ Bool) hn' (measurableSet_singleton x)

/-- **Georgii (6.7)(3): `μ₊(A₊) = 1`.** The plus phase is carried by the tail event `A₊`. -/
theorem plusPhase_apply_eventuallyConst_true (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (plusPhase J : Measure (ℕ → Bool)) (eventuallyConst true) = 1 := by
  set μ : Measure (ℕ → Bool) := (plusPhase J : Measure (ℕ → Bool)) with hμdef
  have hprob : IsProbabilityMeasure μ := (plusPhase J).2
  have hG : (isingChainSpecification J).IsGibbsMeasure μ := plusPhase_mem_GP
  set A : Set (ℕ → Bool) := {σ | σ 0 = true} with hAdef
  have hAm : MeasurableSet A := measurableSet_setOf_apply_eq 0 true
  have hmix := apply_eq_of_isGibbsMeasure h61 (μplus := μ)
    (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61 hA hω) hG
    (setOf_apply_eq_mem_localEvents 0 true)
  have hflip : (μ.map chainFlip.toFun) A = 1 - μ A := by
    rw [Measure.map_apply chainFlip.measurable_toFun hAm, ← prob_compl_eq_one_sub hAm]
    congr 1
    ext σ
    simp [A]
  have hsum := apply_eventuallyConst_true_add_false h61 hG
  have hA : μ A = ENNReal.ofReal ((1 + ∏' k, Real.tanh (J (k + 0))) / 2) :=
    plusPhase_apply_setOf_true hJ h61 0
  have hT : 0 < ∏' k, Real.tanh (J (k + 0)) :=
    Real.tprod_tanh_pos (fun k ↦ hJ (k + 0)) (h61.comp_injective (add_left_injective 0))
  -- pass to real numbers
  set p := μ (eventuallyConst true) with hp
  set q := μ (eventuallyConst false) with hq
  have hp1 : p ≤ 1 := prob_le_one
  have hq1 : q ≤ 1 := prob_le_one
  have hA1 : μ A ≤ 1 := prob_le_one
  rw [hflip] at hmix
  have hreal := congrArg ENNReal.toReal hmix
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
      (ne_top_of_le_ne_top ENNReal.one_ne_top hA1))
      (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hq1)
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hA1 ENNReal.one_ne_top,
    ENNReal.toReal_one] at hreal
  have hsumr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hq1), ENNReal.toReal_one] at hsumr
  have hAr : (μ A).toReal = (1 + ∏' k, Real.tanh (J (k + 0))) / 2 := by
    rw [hA, ENNReal.toReal_ofReal (by linarith)]
  rw [hAr] at hreal
  have hpr : p.toReal = 1 := by nlinarith [ENNReal.toReal_nonneg (a := p)]
  exact (ENNReal.toReal_eq_one_iff p).1 hpr

/-- **Georgii (6.7)(3): `μ₊(A₋) = 0`.** -/
theorem plusPhase_apply_eventuallyConst_false (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (plusPhase J : Measure (ℕ → Bool)) (eventuallyConst false) = 0 := by
  have h := apply_eventuallyConst_true_add_false h61 (isGibbsMeasure_plusPhase (J := J))
  rw [plusPhase_apply_eventuallyConst_true hJ h61] at h
  calc (plusPhase J : Measure (ℕ → Bool)) (eventuallyConst false)
      = 1 + (plusPhase J : Measure (ℕ → Bool)) (eventuallyConst false) - 1 :=
        (ENNReal.add_sub_cancel_left ENNReal.one_ne_top).symm
    _ = 0 := by rw [h, tsub_self]

/-- **Georgii (6.7)(3): `μ₋(A₋) = 1`.** The minus phase is carried by the tail event `A₋`. -/
theorem minusPhase_apply_eventuallyConst_false (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (minusPhase J : Measure (ℕ → Bool)) (eventuallyConst false) = 1 := by
  rw [minusPhase_toMeasure, Measure.map_apply chainFlip.measurable_toFun
    (measurableSet_eventuallyConst false), preimage_chainFlip_eventuallyConst]
  exact plusPhase_apply_eventuallyConst_true hJ h61

/-- **Georgii (6.7)(3): `μ₋(A₊) = 0`.** -/
theorem minusPhase_apply_eventuallyConst_true (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (minusPhase J : Measure (ℕ → Bool)) (eventuallyConst true) = 0 := by
  rw [minusPhase_toMeasure, Measure.map_apply chainFlip.measurable_toFun
    (measurableSet_eventuallyConst true), preimage_chainFlip_eventuallyConst]
  exact plusPhase_apply_eventuallyConst_false hJ h61


/-- **A Gibbs measure carried by `A₊` is `μ₊`.** -/
theorem eq_plusPhase_of_apply_eventuallyConst_true_eq_one
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {μ : Measure (ℕ → Bool)}
    (hμ : μ ∈ G (isingChainSpecification J)) (h1 : μ (eventuallyConst true) = 1) :
    μ = plusPhase J := by
  obtain ⟨hprob, hG⟩ := hμ
  have h0 : μ (eventuallyConst false) = 0 := by
    have h := apply_eventuallyConst_true_add_false h61 hG
    rw [h1] at h
    calc μ (eventuallyConst false) = 1 + μ (eventuallyConst false) - 1 :=
          (ENNReal.add_sub_cancel_left ENNReal.one_ne_top).symm
      _ = 0 := by rw [h, tsub_self]
  refine (eq_smul_add_smul_of_isGibbsMeasure h61 (μplus := plusPhase J)
    (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61 hA hω) hG).trans ?_
  rw [h1, h0, one_smul, zero_smul, add_zero]

/-- **A Gibbs measure carried by `A₋` is `μ₋`.** -/
theorem eq_minusPhase_of_apply_eventuallyConst_false_eq_one
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) {μ : Measure (ℕ → Bool)}
    (hμ : μ ∈ G (isingChainSpecification J)) (h1 : μ (eventuallyConst false) = 1) :
    μ = minusPhase J := by
  obtain ⟨hprob, hG⟩ := hμ
  have h0 : μ (eventuallyConst true) = 0 := by
    have h := apply_eventuallyConst_true_add_false h61 hG
    rw [h1, add_comm] at h
    calc μ (eventuallyConst true) = 1 + μ (eventuallyConst true) - 1 :=
          (ENNReal.add_sub_cancel_left ENNReal.one_ne_top).symm
      _ = 0 := by rw [h, tsub_self]
  refine (eq_smul_add_smul_of_isGibbsMeasure h61 (μplus := plusPhase J)
    (fun A hA ω hω ↦ tendsto_isingChainSpecification_range_plusPhase h61 hA hω) hG).trans ?_
  rw [h1, h0, one_smul, zero_smul, zero_add, minusPhase_toMeasure]

/-- **Georgii (6.7)(3): `μ₊` is an extreme point of `𝒢(Φ)`.** -/
theorem plusPhase_mem_extremePoints_G (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (plusPhase J : Measure (ℕ → Bool)) ∈ (G (isingChainSpecification J)).extremePoints ℝ≥0∞ := by
  refine ⟨⟨(plusPhase J).2, plusPhase_mem_GP⟩, fun μ₁ hμ₁ μ₂ hμ₂ hseg ↦ ?_⟩
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  have ha1 : a ≤ 1 := hab ▸ le_self_add
  have hb1 : b ≤ 1 := hab ▸ le_add_self
  have hp₁ := hμ₁.1
  have hp₂ := hμ₂.1
  have hsumA : μ₁ (eventuallyConst true) * a + μ₂ (eventuallyConst true) * b = 1 := by
    have := congrArg (fun m : Measure (ℕ → Bool) ↦ m (eventuallyConst true)) hsum
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at this
    rw [mul_comm, mul_comm _ b, this]
    exact plusPhase_apply_eventuallyConst_true hJ h61
  refine eq_plusPhase_of_apply_eventuallyConst_true_eq_one h61 hμ₁ ?_
  by_contra hne
  have hlt : μ₁ (eventuallyConst true) < 1 := lt_of_le_of_ne prob_le_one hne
  have key : μ₁ (eventuallyConst true) * a + μ₂ (eventuallyConst true) * b < 1 * a + 1 * b :=
    ENNReal.add_lt_add_of_lt_of_le
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ne_top_of_le_ne_top ENNReal.one_ne_top hb1))
      (ENNReal.mul_lt_mul_left ha.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top ha1) hlt)
      (mul_le_mul_left prob_le_one b)
  rw [one_mul, one_mul, hab, hsumA] at key
  exact lt_irrefl _ key

/-- **Georgii (6.7)(3): `μ₋` is an extreme point of `𝒢(Φ)`.** -/
theorem minusPhase_mem_extremePoints_G (hJ : ∀ n, 0 < J n)
    (h61 : Summable fun n ↦ Real.exp (-2 * J n)) :
    (minusPhase J : Measure (ℕ → Bool)) ∈ (G (isingChainSpecification J)).extremePoints ℝ≥0∞ := by
  refine ⟨⟨(minusPhase J).2, minusPhase_mem_GP⟩, fun μ₁ hμ₁ μ₂ hμ₂ hseg ↦ ?_⟩
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := hseg
  have ha1 : a ≤ 1 := hab ▸ le_self_add
  have hb1 : b ≤ 1 := hab ▸ le_add_self
  have hp₁ := hμ₁.1
  have hp₂ := hμ₂.1
  have hsumA : μ₁ (eventuallyConst false) * a + μ₂ (eventuallyConst false) * b = 1 := by
    have := congrArg (fun m : Measure (ℕ → Bool) ↦ m (eventuallyConst false)) hsum
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at this
    rw [mul_comm, mul_comm _ b, this]
    exact minusPhase_apply_eventuallyConst_false hJ h61
  refine eq_minusPhase_of_apply_eventuallyConst_false_eq_one h61 hμ₁ ?_
  by_contra hne
  have hlt : μ₁ (eventuallyConst false) < 1 := lt_of_le_of_ne prob_le_one hne
  have key : μ₁ (eventuallyConst false) * a + μ₂ (eventuallyConst false) * b < 1 * a + 1 * b :=
    ENNReal.add_lt_add_of_lt_of_le
      (ENNReal.mul_ne_top (measure_ne_top _ _) (ne_top_of_le_ne_top ENNReal.one_ne_top hb1))
      (ENNReal.mul_lt_mul_left ha.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top ha1) hlt)
      (mul_le_mul_left prob_le_one b)
  rw [one_mul, one_mul, hab, hsumA] at key
  exact lt_irrefl _ key

/-! #### The random graph `G(ω)` and percolation -/

variable (ω : ℕ → Bool) in
/-- **Georgii (6.7)(3): the random graph `G(ω)`.** The subgraph of the half-line `hasse ℕ`
whose bonds are the `{i, i+1}` with `ω_i = ω_{i+1}`; equivalently
(`chainGraph_adj_iff_forall_le`) the nearest-neighbour bonds `A` on which `Φ_A(ω) = min Φ_A`. -/
def chainGraph : SimpleGraph ℕ :=
  SimpleGraph.hasse ℕ ⊓ SimpleGraph.fromRel fun i j ↦ ω i = ω j

lemma chainGraph_adj {ω : ℕ → Bool} {i j : ℕ} :
    (chainGraph ω).Adj i j ↔ (SimpleGraph.hasse ℕ).Adj i j ∧ ω i = ω j := by
  simp only [chainGraph, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, -, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.symm⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, h.ne, Or.inl h'⟩

lemma chainGraph_adj_succ {ω : ℕ → Bool} (i : ℕ) :
    (chainGraph ω).Adj i (i + 1) ↔ ω i = ω (i + 1) := by
  rw [chainGraph_adj, SimpleGraph.hasse_nat_adj]
  simp

lemma chainGraph_le_hasse (ω : ℕ → Bool) : chainGraph ω ≤ SimpleGraph.hasse ℕ := inf_le_left

lemma isingChainPotential_pair_succ (i : ℕ) (σ : ℕ → Bool) :
    isingChainPotential J {i, i + 1} σ = -J i * (spin (σ i) * spin (σ (i + 1))) := by
  rw [isingChainPotential, Potential.pair_pair _ (Nat.lt_succ_self i), isingChainPair_succ]

/-- On a nearest-neighbour bond `{i, i+1}`, `Φ_{{i,i+1}}(ω) = min Φ_{{i,i+1}}` iff
`ω_i = ω_{i+1}` (for `J_i > 0`). -/
lemma isingChainPotential_pair_succ_le_iff (hJ : ∀ n, 0 < J n) (i : ℕ) (ω : ℕ → Bool) :
    (∀ σ, isingChainPotential J {i, i + 1} ω ≤ isingChainPotential J {i, i + 1} σ)
      ↔ ω i = ω (i + 1) := by
  simp only [isingChainPotential_pair_succ]
  constructor
  · intro h
    have := h (constConfig true)
    simp only [constConfig_apply, spin_mul_self, mul_one] at this
    by_contra hne
    rw [spin_mul_spin_of_ne (Ne.symm hne)] at this
    linarith [hJ i]
  · intro h σ
    rw [h, spin_mul_self]
    have : spin (σ i) * spin (σ (i + 1)) ≤ 1 := by
      cases σ i <;> cases σ (i + 1) <;> norm_num [spin]
    nlinarith [hJ i]

/-- **Georgii (6.7)(3): the two descriptions of `G(ω)` agree.** The bonds of `G(ω)` are the
nearest-neighbour pairs `A = {i, j}` on which `Φ_A(ω) = min Φ_A`. -/
theorem chainGraph_adj_iff_forall_le (hJ : ∀ n, 0 < J n) {ω : ℕ → Bool} {i j : ℕ} :
    (chainGraph ω).Adj i j ↔ (SimpleGraph.hasse ℕ).Adj i j ∧
      ∀ σ, isingChainPotential J {i, j} ω ≤ isingChainPotential J {i, j} σ := by
  rw [chainGraph_adj]
  refine and_congr_right fun hij ↦ ?_
  rcases (SimpleGraph.hasse_nat_adj i j).1 hij with rfl | rfl
  · exact (isingChainPotential_pair_succ_le_iff hJ i ω).symm
  · rw [Finset.pair_comm, eq_comm]
    exact (isingChainPotential_pair_succ_le_iff hJ j ω).symm

/-- **Georgii (6.7)(3): `A₊ ∪ A₋` is the percolation event.** A configuration `ω` is eventually
constant iff the random graph `G(ω)` has an infinite connected component. -/
theorem mem_eventuallyConst_union_iff_exists_infinite_supp {ω : ℕ → Bool} :
    ω ∈ eventuallyConst true ∪ eventuallyConst false
      ↔ ∃ C : (chainGraph ω).ConnectedComponent, C.supp.Infinite := by
  rw [SimpleGraph.exists_infinite_supp_iff (chainGraph_le_hasse ω)]
  simp only [chainGraph_adj_succ]
  constructor
  · intro h
    have h' : ∃ x : Bool, ω ∈ eventuallyConst x := by
      rcases h with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    obtain ⟨x, hx⟩ := h'
    obtain ⟨v, hv⟩ := Filter.eventually_atTop.1 (mem_eventuallyConst_iff.1 hx)
    exact ⟨v, fun i hi ↦ by rw [hv i hi, hv (i + 1) (by omega)]⟩
  · rintro ⟨v, hv⟩
    exact mem_eventuallyConst_union_of_eventually_eq (Filter.eventually_atTop.2 ⟨v, hv⟩)

/-- **Georgii (6.7)(3)**, with the uniqueness: `ω ∈ A₊ ∪ A₋` iff `G(ω)` has a *unique* infinite
connected component. -/
theorem mem_eventuallyConst_union_iff_existsUnique_infinite_supp {ω : ℕ → Bool} :
    ω ∈ eventuallyConst true ∪ eventuallyConst false
      ↔ ∃! C : (chainGraph ω).ConnectedComponent, C.supp.Infinite := by
  rw [mem_eventuallyConst_union_iff_exists_infinite_supp]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, hC, fun D hD ↦
      SimpleGraph.ConnectedComponent.eq_of_infinite_supp (chainGraph_le_hasse ω) hD hC⟩
  · rintro ⟨C, hC, -⟩
    exact ⟨C, hC⟩

/-- **Georgii (6.7)(3): every Gibbs measure percolates.** Under (6.1), for every Gibbs measure
`μ` of the chain, the random graph `G(·)` has an infinite connected component `μ`-a.s. -/
theorem apply_setOf_exists_infinite_supp_eq_one (h61 : Summable fun n ↦ Real.exp (-2 * J n))
    {μ : Measure (ℕ → Bool)} [IsProbabilityMeasure μ]
    (hμ : (isingChainSpecification J).IsGibbsMeasure μ) :
    μ {ω : ℕ → Bool | ∃ C : (chainGraph ω).ConnectedComponent, C.supp.Infinite} = 1 := by
  have h : {ω : ℕ → Bool | ∃ C : (chainGraph ω).ConnectedComponent, C.supp.Infinite}
      = eventuallyConst true ∪ eventuallyConst false :=
    Set.ext fun _ ↦ mem_eventuallyConst_union_iff_exists_infinite_supp.symm
  rw [h]
  exact apply_eventuallyConst_union_eq_one h61 hμ

end MeasureTheory.GibbsMeasure

end

end
