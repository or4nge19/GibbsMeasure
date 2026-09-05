/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable
public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Nearest-neighbour pair potentials on a graph

The nearest-neighbour pair potential (Georgii (2.16)/(2.17), with the coefficients of formula
(3.13)) of a graph `G` with coupling `J`, external field `h` and
spin observable `σ : E → ℝ`: `Φ_{i} = -h·σ(η i)`, `Φ_{i,j} = -J·σ(η i)·σ(η j)` on edges, and `0`
otherwise. For a measurable bounded `σ` and a locally finite graph it is an absolutely summable
potential, so the whole Gibbsian theory of `ℬ` applies (Ising models are the instance
`σ = ±1` over `E = Bool`, see `GibbsMeasure/Model/Ising.lean`).

The second family is the symmetrised bond potential `Potential.nearestNeighbourSym G φ` of an
arbitrary bond interaction `φ : E → E → ℝ`: `Φ_{i,j} = ½ (φ(η i, η j) + φ(η j, η i))` on the
edges of `G` and `0` elsewhere, together with its measurability, finite range and the symmetry
theorem `map_nearestNeighbourSym_eq` (a graph automorphism with a common spin map preserving
`φ` preserves `Φ`).  The *gradient* potentials `nearestNeighbourDiff G g`, `φ(x, y) = g(x - y)`,
are Georgii (6.16) for a general even weight; `discreteGaussian G` is (6.16) itself,
`g = (·)²`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section


namespace Potential

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (2.17).** A potential is a *nearest-neighbour* (or Markov) potential for the graph
`G` when `Φ_A = 0` unless `A` is a complete subgraph of `G`.  Georgii's Corollary (2.32) says that
the potential representing a quasilocal Markov specification is of this form. -/
def IsNearestNeighbour (G : SimpleGraph S) (Φ : Potential S E) : Prop :=
  ∀ A : Finset S, ¬ G.IsClique (A : Set S) → Φ A = 0

/-! ### The nearest-neighbour pair potential on a graph -/

open Classical in
/-- The nearest-neighbour pair potential of a graph `G` with coupling `J`, external field `h`
and spin observable `σ`:
`Φ_{i} = -h·σ(η i)`, `Φ_{i,j} = -J·σ(η i)·σ(η j)` on edges `{i, j}` of `G`, and `0` otherwise.
The sum/product over `A` make the definition independent of any enumeration of `A`. -/
noncomputable def nearestNeighbourPair (G : SimpleGraph S) (J h : ℝ) (σ : E → ℝ) :
    Potential S E := fun A η ↦
  if A.card = 1 then -h * ∑ i ∈ A, σ (η i)
  else if A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j then -J * ∏ i ∈ A, σ (η i)
  else 0

lemma nearestNeighbourPair_apply_card_one {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h1 : A.card = 1) (η : S → E) :
    nearestNeighbourPair G J h σ A η = -h * ∑ i ∈ A, σ (η i) := by
  simp only [nearestNeighbourPair, ite_eq_left h1]

lemma nearestNeighbourPair_apply_pair {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j) (η : S → E) :
    nearestNeighbourPair G J h σ A η = -J * ∏ i ∈ A, σ (η i) := by
  have h1 : ¬ A.card = 1 := by omega
  simp only [nearestNeighbourPair, ite_eq_right h1, ite_eq_left h2]

lemma nearestNeighbourPair_apply_eq_zero {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h1 : ¬ A.card = 1)
    (h2 : ¬ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j)) (η : S → E) :
    nearestNeighbourPair G J h σ A η = 0 := by
  simp only [nearestNeighbourPair, ite_eq_right h1, ite_eq_right h2]

/-- Nearest-neighbour potentials have no `∅`-interaction (Georgii indexes potentials by nonempty
sets). -/
@[simp] lemma nearestNeighbourPair_empty (G : SimpleGraph S) (J h : ℝ) (σ : E → ℝ) :
    nearestNeighbourPair G J h σ ∅ = 0 :=
  funext fun η ↦ nearestNeighbourPair_apply_eq_zero (by simp) (by simp) η

/-! ### Measurability (`IsPotential`) -/

lemma isPotential_nearestNeighbourPair (G : SimpleGraph S) (J h : ℝ) {σ : E → ℝ}
    (hσ : Measurable σ) : IsPotential (nearestNeighbourPair G J h σ) := by
  constructor
  intro Δ
  by_cases h1 : Δ.card = 1
  · have hval : nearestNeighbourPair G J h σ Δ = fun η ↦ -h * ∑ i ∈ Δ, σ (η i) :=
      funext fun η ↦ nearestNeighbourPair_apply_card_one h1 η
    rw [hval]
    exact (Finset.measurable_sum Δ fun i hi ↦
      hσ.comp (measurable_cylinderEvent_apply (Finset.mem_coe.2 hi))).const_mul (-h)
  · by_cases h2 : Δ.card = 2 ∧ ∃ i ∈ Δ, ∃ j ∈ Δ, G.Adj i j
    · have hval : nearestNeighbourPair G J h σ Δ = fun η ↦ -J * ∏ i ∈ Δ, σ (η i) :=
        funext fun η ↦ nearestNeighbourPair_apply_pair h2 η
      rw [hval]
      exact (Finset.measurable_prod Δ fun i hi ↦
        hσ.comp (measurable_cylinderEvent_apply (Finset.mem_coe.2 hi))).const_mul (-J)
    · have hval : nearestNeighbourPair G J h σ Δ = fun _ ↦ 0 :=
        funext fun η ↦ nearestNeighbourPair_apply_eq_zero h1 h2 η
      rw [hval]
      exact measurable_const

/-! ### Finite range (`IsFiniteRange`) -/

/-- On a locally finite graph, a nonzero interaction support containing `i` is either `{i}`
or an edge at `i`; in both cases it lies in `insert i (G.neighborFinset i)`. -/
lemma subset_of_nearestNeighbourPair_ne_zero [DecidableEq S] (G : SimpleGraph S)
    [G.LocallyFinite] {J h : ℝ} {σ : E → ℝ} {i : S} {A : Finset S}
    (hiA : i ∈ A) (hΦ : nearestNeighbourPair G J h σ A ≠ 0) :
    A ⊆ insert i (G.neighborFinset i) := by
  by_cases h1 : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
    rw [Finset.mem_singleton] at hiA
    subst hiA
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_insert_self _ _
  · by_cases h2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
    · obtain ⟨hcard, a, haA, b, hbA, hab⟩ := h2
      have hAab : ({a, b} : Finset S) = A := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact haA
          · rw [Finset.mem_singleton] at hx
            subst hx
            exact hbA
        · exact le_of_eq (by rw [hcard, Finset.card_pair hab.ne])
      intro x hx
      rw [← hAab] at hx hiA
      rcases Finset.mem_insert.1 hiA with rfl | hi'
      · -- `i = a`
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact Finset.mem_insert_of_mem (by simpa using hab)
      · -- `i = b`
        rw [Finset.mem_singleton] at hi'
        subst hi'
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact Finset.mem_insert_of_mem (by simpa using hab.symm)
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact Finset.mem_insert_self _ _
    · exact absurd (funext fun η ↦ by
        simpa using nearestNeighbourPair_apply_eq_zero (G := G) (J := J) (h := h) (σ := σ)
          h1 h2 η) hΦ

lemma isFiniteRange_nearestNeighbourPair (G : SimpleGraph S) [G.LocallyFinite]
    (J h : ℝ) (σ : E → ℝ) : IsFiniteRange (nearestNeighbourPair G J h σ) := by
  classical
  exact ⟨fun i ↦ ⟨insert i (G.neighborFinset i),
    fun A hiA hΦ ↦ subset_of_nearestNeighbourPair_ne_zero G hiA hΦ⟩⟩

/-! ### B4: absolute summability (`IsAbsolutelySummable`) from a bounded spin observable -/

/-- A uniform bound on all interaction terms of the pair potential, from a bound on the spin
observable. The `|c|`s make the bound valid without a nonnegativity hypothesis on `c`. -/
lemma abs_nearestNeighbourPair_apply_le (G : SimpleGraph S) (J h : ℝ) {σ : E → ℝ} {c : ℝ}
    (hb : ∀ x, |σ x| ≤ c) (A : Finset S) (η : S → E) :
    |nearestNeighbourPair G J h σ A η| ≤ |h| * |c| + |J| * (c * c) := by
  have hcc : 0 ≤ c * c := mul_self_nonneg c
  by_cases h1 : A.card = 1
  · rw [nearestNeighbourPair_apply_card_one h1, abs_mul, abs_neg]
    have hsum : |∑ i ∈ A, σ (η i)| ≤ |c| := by
      calc |∑ i ∈ A, σ (η i)| ≤ ∑ i ∈ A, |σ (η i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ A, |c| := Finset.sum_le_sum fun i _ ↦ (hb (η i)).trans (le_abs_self c)
        _ = |c| := by rw [Finset.sum_const, h1, one_smul]
    calc |h| * |∑ i ∈ A, σ (η i)| ≤ |h| * |c| :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg h)
      _ ≤ |h| * |c| + |J| * (c * c) :=
          le_add_of_nonneg_right (mul_nonneg (abs_nonneg J) hcc)
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
    · rw [nearestNeighbourPair_apply_pair h2, abs_mul, abs_neg]
      have hprod : |∏ i ∈ A, σ (η i)| ≤ c * c := by
        calc |∏ i ∈ A, σ (η i)| = ∏ i ∈ A, |σ (η i)| := Finset.abs_prod _ _
          _ ≤ ∏ _i ∈ A, |c| := Finset.prod_le_prod (fun i _ ↦ abs_nonneg _)
              (fun i _ ↦ (hb (η i)).trans (le_abs_self c))
          _ = |c| ^ A.card := Finset.prod_const _
          _ = |c| * |c| := by rw [h2.1, pow_two]
          _ = c * c := abs_mul_abs_self c
      calc |J| * |∏ i ∈ A, σ (η i)| ≤ |J| * (c * c) :=
            mul_le_mul_of_nonneg_left hprod (abs_nonneg J)
        _ ≤ |h| * |c| + |J| * (c * c) :=
            le_add_of_nonneg_left (mul_nonneg (abs_nonneg h) (abs_nonneg c))
    · rw [nearestNeighbourPair_apply_eq_zero h1 h2, abs_zero]
      exact add_nonneg (mul_nonneg (abs_nonneg h) (abs_nonneg c))
        (mul_nonneg (abs_nonneg J) hcc)

lemma isAbsolutelySummable_nearestNeighbourPair (G : SimpleGraph S) [G.LocallyFinite]
    (J h : ℝ) {σ : E → ℝ} {c : ℝ} (hb : ∀ x, |σ x| ≤ c) :
    IsAbsolutelySummable (nearestNeighbourPair G J h σ) := by
  classical
  refine ⟨fun i ↦ ?_⟩
  -- Only supports inside `insert i (G.neighborFinset i)` contribute.
  have hsupp : ∀ A : Finset S, A ∉ (insert i (G.neighborFinset i)).powerset →
      ({A : Finset S | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A = 0 := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
      have hΦ0 : nearestNeighbourPair G J h σ A = 0 := by
        by_contra hΦ
        exact hA (subset_of_nearestNeighbourPair_ne_zero G hiA hΦ)
      refine le_antisymm (iSup_le fun η ↦ ?_) zero_le
      simp [hΦ0]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA) _
  have htsum : (nearestNeighbourPair G J h σ).normAt i =
      ∑ A ∈ (insert i (G.neighborFinset i)).powerset,
        ({A : Finset S | i ∈ A}.indicator
          (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A :=
    tsum_eq_sum hsupp
  rw [htsum]
  refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
  calc ({A : Finset S | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A
      ≤ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ := Set.indicator_le_self _ _ A
    _ ≤ ENNReal.ofReal (|h| * |c| + |J| * (c * c)) := iSup_le fun η ↦ by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_nearestNeighbourPair_apply_le G J h hb A η)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-! ### The symmetrised bond potential of a graph -/

section Sym

variable {G : SimpleGraph S} {φ : E → E → ℝ}

open Classical in
/-- The nearest-neighbour pair potential of a graph `G` with bond interaction `φ : E → E → ℝ`:
`Φ_{i,j} = ½ (φ(η i, η j) + φ(η j, η i))` on the edges `{i, j}` of `G` and `0` on every other
interaction support.  The half-sum over `A.offDiag` makes the definition independent of any
enumeration of `A`; for symmetric `φ` it is `φ(η i, η j)` (`nearestNeighbourSym_pair_of_symm`). -/
noncomputable def nearestNeighbourSym (G : SimpleGraph S) (φ : E → E → ℝ) : Potential S E :=
  fun A η ↦
    if A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j then
      (2 : ℝ)⁻¹ * ∑ p ∈ A.offDiag, φ (η p.1) (η p.2)
    else 0

open Classical in
lemma nearestNeighbourSym_apply_of_not {A : Finset S}
    (hA : ¬ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j)) (η : S → E) :
    nearestNeighbourSym G φ A η = 0 := by
  simp only [nearestNeighbourSym, ite_eq_right hA]

open Classical in
/-- The symmetrised bond potential on an interaction support carrying an edge. -/
lemma nearestNeighbourSym_apply_of {A : Finset S}
    (hA : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j) (η : S → E) :
    nearestNeighbourSym G φ A η = (2 : ℝ)⁻¹ * ∑ p ∈ A.offDiag, φ (η p.1) (η p.2) := by
  simp only [nearestNeighbourSym, ite_eq_left hA]

/-- The value of the symmetrised bond potential on an edge. -/
lemma nearestNeighbourSym_pair [DecidableEq S] {i j : S} (hij : G.Adj i j) (η : S → E) :
    nearestNeighbourSym G φ {i, j} η = (2 : ℝ)⁻¹ * (φ (η i) (η j) + φ (η j) (η i)) := by
  classical
  have hcard : ({i, j} : Finset S).card = 2 := Finset.card_pair hij.ne
  have hmem : ({i, j} : Finset S).card = 2 ∧ ∃ a ∈ ({i, j} : Finset S),
      ∃ b ∈ ({i, j} : Finset S), G.Adj a b :=
    ⟨hcard, i, by simp, j, by simp, hij⟩
  have hoff : ({i, j} : Finset S).offDiag = {(i, j), (j, i)} := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> simp_all [hij.ne, hij.ne']
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hij.ne, hij.ne']
  rw [nearestNeighbourSym_apply_of hmem, hoff,
    Finset.sum_pair (by simp [Prod.ext_iff, hij.ne])]

/-- For a symmetric bond interaction, the value on an edge is the bond interaction itself:
`Φ_{i,j}(η) = φ(η i, η j)`. -/
lemma nearestNeighbourSym_pair_of_symm [DecidableEq S] (hsymm : ∀ x y, φ x y = φ y x)
    {i j : S} (hij : G.Adj i j) (η : S → E) :
    nearestNeighbourSym G φ {i, j} η = φ (η i) (η j) := by
  rw [nearestNeighbourSym_pair hij, hsymm (η j) (η i)]
  ring

/-- Nearest-neighbour potentials have no `∅`-interaction. -/
@[simp] lemma nearestNeighbourSym_empty (G : SimpleGraph S) (φ : E → E → ℝ) :
    nearestNeighbourSym G φ ∅ = 0 :=
  funext fun η ↦ nearestNeighbourSym_apply_of_not (by simp) η

/-- **Georgii (2.2)(i)** for the symmetrised bond potential: each interaction term is a
measurable function of finitely many coordinates, as soon as the bond interaction is jointly
measurable. -/
lemma isPotential_nearestNeighbourSym (G : SimpleGraph S) {φ : E → E → ℝ}
    (hφ : Measurable (Function.uncurry φ)) : IsPotential (nearestNeighbourSym G φ) := by
  classical
  refine ⟨fun Δ ↦ ?_⟩
  by_cases hΔ : Δ.card = 2 ∧ ∃ i ∈ Δ, ∃ j ∈ Δ, G.Adj i j
  · have hval : nearestNeighbourSym G φ Δ
        = fun η ↦ (2 : ℝ)⁻¹ * ∑ p ∈ Δ.offDiag, φ (η p.1) (η p.2) :=
      funext fun η ↦ nearestNeighbourSym_apply_of hΔ η
    rw [hval]
    refine Measurable.const_mul (Finset.measurable_sum _ fun p hp ↦ ?_) _
    obtain ⟨hp1, hp2, -⟩ := Finset.mem_offDiag.1 hp
    have m1 : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] fun η : S → E ↦ η p.1 :=
      measurable_cylinderEvent_apply (Finset.mem_coe.2 hp1)
    have m2 : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] fun η : S → E ↦ η p.2 :=
      measurable_cylinderEvent_apply (Finset.mem_coe.2 hp2)
    exact hφ.comp (m1.prodMk m2)
  · have hval : nearestNeighbourSym G φ Δ = fun _ ↦ 0 :=
      funext fun η ↦ nearestNeighbourSym_apply_of_not hΔ η
    rw [hval]
    exact measurable_const

/-- Over a countable state space with measurable singletons (`ℤ`, `Bool`, …) every bond
interaction is measurable, so the symmetrised bond potential is a potential. -/
instance isPotential_nearestNeighbourSym_of_countable [Countable E] [MeasurableSingletonClass E]
    (G : SimpleGraph S) (φ : E → E → ℝ) : IsPotential (nearestNeighbourSym G φ) :=
  isPotential_nearestNeighbourSym G Measurable.of_discrete

/-- A nonzero interaction support of the symmetrised bond potential containing `i` is an edge
at `i`. -/
lemma subset_of_nearestNeighbourSym_ne_zero [DecidableEq S] (G : SimpleGraph S)
    [G.LocallyFinite] {i : S} {A : Finset S} (hiA : i ∈ A)
    (hΦ : nearestNeighbourSym G φ A ≠ 0) :
    A ⊆ insert i (G.neighborFinset i) := by
  by_contra hsub
  by_cases hA : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
  · obtain ⟨hcard, a, haA, b, hbA, hab⟩ := hA
    obtain ⟨x, hxA, hx⟩ := Finset.not_subset.1 hsub
    have hxi : x ≠ i := fun h ↦ hx (by simp [h])
    have hAxi : ({i, x} : Finset S) = A :=
      Finset.eq_of_subset_of_card_le (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hiA
        · rw [Finset.mem_singleton] at hy; exact hy ▸ hxA)
        (le_of_eq (by rw [hcard, Finset.card_pair (Ne.symm hxi)]))
    -- the only adjacency inside `A = {i, x}` is `i ~ x`
    rw [← hAxi] at haA hbA
    simp only [Finset.mem_insert, Finset.mem_singleton] at haA hbA
    have hix : G.Adj i x := by
      rcases haA with rfl | rfl <;> rcases hbA with rfl | rfl <;>
        simp_all [SimpleGraph.Adj.symm]
    exact hx (Finset.mem_insert_of_mem (by simpa using hix))
  · exact hΦ (funext fun η ↦ nearestNeighbourSym_apply_of_not hA η)

/-- **Georgii (2.15)** for the symmetrised bond potential on a locally finite graph. -/
instance isFiniteRange_nearestNeighbourSym (G : SimpleGraph S) [G.LocallyFinite]
    (φ : E → E → ℝ) : IsFiniteRange (nearestNeighbourSym G φ) := by
  classical
  exact ⟨fun i ↦ ⟨insert i (G.neighborFinset i),
    fun A hiA hΦ ↦ subset_of_nearestNeighbourSym_ne_zero G hiA hΦ⟩⟩

open MeasureTheory.GibbsMeasure in
/-- **The symmetries of a symmetrised bond potential.** If the site map of `τ` is an
automorphism of `G` and all its spin maps are one and the same `f` whose inverse preserves the
bond interaction, then `τ` preserves `Φ` (Georgii (5.3): `τ(Φ) = Φ`).

Georgii's Remark (6.17) is five instances of this for the gradient potential: the lattice
translations, the two lattice reflections and the lattice rotation (`f = id`), the spin
reflection (`f = -·`, `g` even) and the spin translation (`f = · - 1`). -/
theorem map_nearestNeighbourSym_eq {τ : Transformation S E} {f : E ≃ᵐ E}
    (hspin : ∀ i, τ.spin i = f)
    (hsites : ∀ i j, G.Adj (τ.sites i) (τ.sites j) ↔ G.Adj i j)
    (hφ : ∀ x y, φ (f.symm x) (f.symm y) = φ x y) :
    Potential.map τ (nearestNeighbourSym G φ) = nearestNeighbourSym G φ := by
  classical
  funext A η
  set A' : Finset S := A.map τ.sites.symm.toEmbedding with hA'
  have hmemA' : ∀ i : S, i ∈ A' ↔ τ.sites i ∈ A := by
    intro i
    simp [hA', Finset.mem_map_equiv]
  have hη' : ∀ i : S, τ.inv.toFun η i = f.symm (η (τ.sites i)) := by
    intro i
    simp [Transformation.inv, Transformation.toFun, hspin]
  have hcond : (A'.card = 2 ∧ ∃ i ∈ A', ∃ j ∈ A', G.Adj i j)
      ↔ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j) := by
    rw [hA', Finset.card_map]
    refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
    · rintro ⟨i, hi, j, hj, hij⟩
      exact ⟨τ.sites i, (hmemA' i).1 hi, τ.sites j, (hmemA' j).1 hj, (hsites i j).2 hij⟩
    · rintro ⟨i, hi, j, hj, hij⟩
      refine ⟨τ.sites.symm i, (hmemA' _).2 (by simpa using hi),
        τ.sites.symm j, (hmemA' _).2 (by simpa using hj), ?_⟩
      rw [← hsites (τ.sites.symm i) (τ.sites.symm j)]
      simpa using hij
  by_cases hA : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
  · rw [Potential.map_apply, nearestNeighbourSym_apply_of hA,
      nearestNeighbourSym_apply_of (hcond.2 hA)]
    congr 1
    refine Finset.sum_nbij' (i := fun p ↦ (τ.sites p.1, τ.sites p.2))
      (j := fun q ↦ (τ.sites.symm q.1, τ.sites.symm q.2)) ?_ ?_ ?_ ?_ ?_
    · rintro p hp
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.1 hp
      exact Finset.mem_offDiag.2 ⟨(hmemA' _).1 h1, (hmemA' _).1 h2,
        fun h ↦ h3 (τ.sites.injective h)⟩
    · rintro q hq
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.1 hq
      exact Finset.mem_offDiag.2 ⟨(hmemA' _).2 (by simpa using h1),
        (hmemA' _).2 (by simpa using h2), fun h ↦ h3 (τ.sites.symm.injective h)⟩
    · rintro p -; simp
    · rintro q -; simp
    · rintro p -
      rw [hη', hη']
      simpa using hφ (η (τ.sites p.1)) (η (τ.sites p.2))
  · rw [Potential.map_apply, nearestNeighbourSym_apply_of_not (fun h ↦ hA (hcond.1 h)),
      nearestNeighbourSym_apply_of_not hA]

end Sym

/-! ### Gradient potentials: Georgii (6.16) for a general even weight -/

section Diff

variable [AddGroup E]

/-- **Georgii (6.16), for a general even weight.** The nearest-neighbour *gradient* potential of a
graph `G` and a weight `g : E → ℝ`: the symmetrised bond potential of `φ(x, y) = g(x - y)`, so
`Φ_{i,j} = ½ (g(η i - η j) + g(η j - η i))` on the edges `{i, j}` of `G` and `0` elsewhere; for
even `g` it is `g(η i - η j)` (`nearestNeighbourDiff_pair_of_even`).

Georgii's potential (6.16) is the case `E = ℤ`, `g = (·)²`, `Potential.discreteGaussian`. -/
abbrev nearestNeighbourDiff (G : SimpleGraph S) (g : E → ℝ) : Potential S E :=
  nearestNeighbourSym G fun x y ↦ g (x - y)

/-- **Georgii (6.16)** on an edge, for even `g`: `Φ_{i,j}(η) = g(η i - η j)`. -/
lemma nearestNeighbourDiff_pair_of_even [DecidableEq S] {G : SimpleGraph S} {g : E → ℝ}
    (heven : ∀ x, g (-x) = g x) {i j : S} (hij : G.Adj i j) (η : S → E) :
    nearestNeighbourDiff G g {i, j} η = g (η i - η j) :=
  nearestNeighbourSym_pair_of_symm (fun x y ↦ by rw [← heven (x - y), neg_sub]) hij η

end Diff

/-- **Georgii (6.16).** The discrete Gaussian potential of a graph:
`Φ_{i,j} = (σ_i - σ_j)²` on edges, `0` elsewhere. -/
abbrev discreteGaussian (G : SimpleGraph S) : Potential S ℤ :=
  nearestNeighbourDiff G fun x ↦ (x : ℝ) ^ 2

/-- **Georgii (6.16)** on an edge: `Φ_{i,j}(η) = (η i - η j)²`. -/
lemma discreteGaussian_pair [DecidableEq S] {G : SimpleGraph S} {i j : S} (hij : G.Adj i j)
    (η : S → ℤ) :
    discreteGaussian G {i, j} η = ((η i - η j : ℤ) : ℝ) ^ 2 :=
  nearestNeighbourDiff_pair_of_even (fun x ↦ by push_cast; ring) hij η

/-- A nearest-neighbour potential on a locally finite graph has finite range: an interaction
support containing `i` is a clique, hence lies in `{i} ∪ ∂i`. -/
lemma IsNearestNeighbour.isFiniteRange {G : SimpleGraph S} [G.LocallyFinite] {Φ : Potential S E}
    (h : IsNearestNeighbour G Φ) : IsFiniteRange Φ := by
  classical
  refine ⟨fun i ↦ ⟨insert i (G.neighborFinset i), fun A hiA hΦ ↦ ?_⟩⟩
  have hcl : G.IsClique (A : Set S) := by_contra fun hc ↦ hΦ (h A hc)
  intro j hj
  by_cases hij : j = i
  · exact hij ▸ Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset i j).2
      (hcl (by simpa using hiA) (by simpa using hj) (Ne.symm hij)))

/-- The Hamiltonian of a single site `i` for a nearest-neighbour potential on `ℤ`: the self-energy
`Φ_{i}` and the two bond energies `Φ_{i-1,i}`, `Φ_{i,i+1}` (the only cliques of `hasse ℤ` through
`i`). -/
lemma hamiltonian_singleton_of_isNearestNeighbour_hasse_int {Φ : Potential ℤ E}
    (hΦ : IsNearestNeighbour (SimpleGraph.hasse ℤ) Φ) (i : ℤ) (η : ℤ → E) :
    Φ.hamiltonian {i} η = Φ {i} η + Φ {i - 1, i} η + Φ {i, i + 1} η := by
  classical
  have hne1 : ({i} : Finset ℤ) ∉ ({{i - 1, i}, {i, i + 1}} : Finset (Finset ℤ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro h
      have := Finset.ext_iff.1 h (i - 1)
      simp at this
    · intro h
      have := Finset.ext_iff.1 h (i + 1)
      simp at this
  have hne2 : ({i - 1, i} : Finset ℤ) ∉ ({{i, i + 1}} : Finset (Finset ℤ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have := Finset.ext_iff.1 h (i - 1)
    simp at this
    omega
  have hsum : HasSum (Φ.hamiltonianTerms {i} η)
      (∑ A ∈ ({{i}, {i - 1, i}, {i, i + 1}} : Finset (Finset ℤ)), Φ.hamiltonianTerms {i} η A) := by
    refine hasSum_sum_of_ne_finset_zero fun A hA ↦ ?_
    by_cases hdisj : Disjoint A {i}
    · exact hamiltonianTerms_of_disjoint hdisj η
    · rw [hamiltonianTerms_of_not_disjoint hdisj η]
      have hiA : i ∈ A := by rwa [Finset.disjoint_singleton_right, not_not] at hdisj
      have hnc : ¬ (SimpleGraph.hasse ℤ).IsClique (A : Set ℤ) := by
        intro hcl
        apply hA
        have hmem : ∀ a ∈ A, a = i - 1 ∨ a = i ∨ a = i + 1 := fun a ha ↦ by
          by_cases hai : a = i
          · exact Or.inr (Or.inl hai)
          · have := (SimpleGraph.hasse_int_adj i a).1
              (hcl (by simpa using hiA) (by simpa using ha) (Ne.symm hai))
            omega
        have hnot : ¬ (i - 1 ∈ A ∧ i + 1 ∈ A) := fun ⟨h1, h2⟩ ↦ by
          have := (SimpleGraph.hasse_int_adj (i - 1) (i + 1)).1
            (hcl (by simpa using h1) (by simpa using h2) (by omega))
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : i - 1 ∈ A <;> by_cases h2 : i + 1 ∈ A
        · exact absurd ⟨h1, h2⟩ hnot
        · refine Or.inr (Or.inl (Finset.ext fun a ↦ ?_))
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro ha
            rcases hmem a ha with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd (h ▸ ha) h2
          · rintro (rfl | rfl)
            · exact h1
            · exact hiA
        · refine Or.inr (Or.inr (Finset.ext fun a ↦ ?_))
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro ha
            rcases hmem a ha with h | h | h
            · exact absurd (h ▸ ha) h1
            · exact Or.inl h
            · exact Or.inr h
          · rintro (rfl | rfl)
            · exact hiA
            · exact h2
        · refine Or.inl (Finset.ext fun a ↦ ?_)
          simp only [Finset.mem_singleton]
          constructor
          · intro ha
            rcases hmem a ha with h | h | h
            · exact absurd (h ▸ ha) h1
            · exact h
            · exact absurd (h ▸ ha) h2
          · rintro rfl
            exact hiA
      rw [hΦ A hnc]
      rfl
  rw [hamiltonian, hsum.volume.tsum_eq, Finset.sum_insert hne1, Finset.sum_insert hne2,
    Finset.sum_singleton, hamiltonianTerms_of_not_disjoint (by simp) η,
    hamiltonianTerms_of_not_disjoint (by simp) η, hamiltonianTerms_of_not_disjoint (by simp) η,
    add_assoc]

end Potential
end
