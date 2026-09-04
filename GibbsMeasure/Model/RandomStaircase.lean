/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SharpContours
public import GibbsMeasure.Model.SharpPhaseTransition
public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Mathlib.Data.Set.CardTranslate
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ExpNegSq
public import GibbsMeasure.Mathlib.Data.ENNReal.TsumPi
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix

/-!
# Georgii §6.3: Shlosman's random staircases

`S = ℤ²`, `E = ℤ`, `λ` counting measure, and the *discrete Gaussian* potential (6.16)

`Φ_A = (σ_i - σ_j)²` if `A = {i, j}` with `|i - j| = 1`, `Φ_A = 0` otherwise.

The contour machinery of §6.2 (`GibbsMeasure/Model/Contours.lean`,
`GibbsMeasure/Model/PeierlsEstimate.lean`, `GibbsMeasure/Model/SharpContours.lean` and the
anchored-circuit count of `GibbsMeasure/Model/SharpPhaseTransition.lean`) is reused verbatim: the
sites, the lattice graph, the "infinite outside" `outside D` of a finite `D ⊆ ℤ²`, the outer
boundary, the fact that it is a circuit, and Georgii's count `ℓ · 3^{ℓ-1}` of the circuits of
length `ℓ` anchored at a site (Lemma (6.13)).  Only the *state space* and the *contour weight*
change.

## Contents

* `Potential.discreteGaussian`, `Shlosman.dgPotential` — **(6.16)**;
  `Shlosman.isSigmaFiniteLambdaAdmissible_dgPotential` — the `λ`-admissibility of `βΦ`;
  `Shlosman.dgSpecification` — the Gibbsian specification `γ^{βΦ}` over counting measure.
* `Shlosman.map_dgPotential_eq` — **Remark (6.17)(i)–(v)**: the five symmetries preserve `Φ`.
* `Potential.IsGroundState` — **Definition (6.18)**; `Shlosman.staircase` — **(6.19)**;
  `Shlosman.isGroundState_staircase` — **Remark (6.20)**.
* `Shlosman.exists_circuit_contour_dg` — **Lemma (6.22)**; `Shlosman.stepDown` — **(6.23)**;
  `Shlosman.card_bdIdx_le_hamiltonian_sub_stepDown` — **Lemma (6.24)**.
* `Shlosman.dgSpecification_abs_excess_le` — **Lemma (6.25)**, in the sharpened form
  `γ_{Λ_N}(|σ_a - ω^z_a| ≥ k | ω^z) ≤ 2 r'(β/2)^k` with `r'` the circuit series of
  `MeasureTheory.GibbsMeasure.PeierlsSharp.r'` (Georgii's `r(β) = 1 ∧ 6 r'(β/2)`).
* `Shlosman.staircasePhase`, `Shlosman.staircasePhase_spec`,
  `Shlosman.infinite_GP_dgSpecification_of_log_twelve` and the five
  `Shlosman.map_*_staircasePhase_ne` — **Theorem (6.21)**: the random staircases, their
  concentration on `ω^z`, their pairwise distinctness, and the breaking of `t`, `τ`, `θ_j`, `r₀`
  and `r₁`.

Not formalised here: the *invariance* half of (6.21)(ii) (`μ_z^β` invariant under `θ_{(0,1)}`,
`t^{-z} ∘ θ_{(1,0)}`, `r₁ ∘ τ`, `r₂`, and `τ(μ_z^β) = r₁(μ_z^β) = μ_{-z}^β`), which in Georgii
comes from Example (5.20)(1) applied to the *shift-averaged* sequence
`ν_{N,z} = |Λ_N|^{-1} ∑_{i ∈ Λ_N} γ_{Λ_N + i}(· | ω^z)` and to an equivariant choice of cluster
point; and the `ℓ¹` linear independence of (6.21)(iii), which needs signed measures.  What is
proved instead of (iii) is the pairwise separation `staircasePhase_ne` (and the `map_*_ne`
lemmas), which already gives `|𝒢(βΦ)| = ∞` and the symmetry breaking Georgii emphasises.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Potential

variable {S : Type*}

open Classical in
/-- **Georgii (6.16), for a general even weight.** The nearest-neighbour *gradient* potential of a
graph `G` and a function `g : ℤ → ℝ`:
`Φ_{i,j} = ½ (g(η i - η j) + g(η j - η i))` on the edges `{i, j}` of `G`, and `0` on every other
interaction support.  The half-sum over `A.offDiag` makes the definition independent of any
enumeration of `A`; for even `g` it is `g(η i - η j)` (`nearestNeighbourDiff_pair_of_even`).

Georgii's potential (6.16) is the case `g = (·)²`, `Potential.discreteGaussian`. -/
def nearestNeighbourDiff (G : SimpleGraph S) (g : ℤ → ℝ) : Potential S ℤ := fun A η ↦
  if A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j then
    (2 : ℝ)⁻¹ * ∑ p ∈ A.offDiag, g (η p.1 - η p.2)
  else 0

variable [DecidableEq S] {G : SimpleGraph S} {g : ℤ → ℝ}

open Classical in
omit [DecidableEq S] in
lemma nearestNeighbourDiff_apply_of_not {A : Finset S}
    (hA : ¬ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j)) (η : S → ℤ) :
    nearestNeighbourDiff G g A η = 0 := by
  simp only [nearestNeighbourDiff, ite_eq_right hA]

open Classical in
omit [DecidableEq S] in
/-- The gradient potential on an interaction support carrying an edge. -/
lemma nearestNeighbourDiff_apply_of {A : Finset S}
    (hA : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j) (η : S → ℤ) :
    nearestNeighbourDiff G g A η = (2 : ℝ)⁻¹ * ∑ p ∈ A.offDiag, g (η p.1 - η p.2) := by
  simp only [nearestNeighbourDiff, ite_eq_left hA]

/-- The value of the gradient potential on an edge. -/
lemma nearestNeighbourDiff_pair {i j : S} (hij : G.Adj i j) (η : S → ℤ) :
    nearestNeighbourDiff G g {i, j} η
      = (2 : ℝ)⁻¹ * (g (η i - η j) + g (η j - η i)) := by
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
  rw [nearestNeighbourDiff, ite_eq_left hmem, hoff,
    Finset.sum_pair (by simp [Prod.ext_iff, hij.ne])]

/-- **Georgii (6.16)** on an edge, for even `g`: `Φ_{i,j}(η) = g(η i - η j)`. -/
lemma nearestNeighbourDiff_pair_of_even (heven : ∀ x : ℤ, g (-x) = g x) {i j : S}
    (hij : G.Adj i j) (η : S → ℤ) :
    nearestNeighbourDiff G g {i, j} η = g (η i - η j) := by
  rw [nearestNeighbourDiff_pair hij, show η j - η i = -(η i - η j) by ring, heven]
  ring

omit [DecidableEq S] in
@[simp] lemma nearestNeighbourDiff_empty (G : SimpleGraph S) (g : ℤ → ℝ) :
    nearestNeighbourDiff G g ∅ = 0 :=
  funext fun η ↦ nearestNeighbourDiff_apply_of_not (by simp) η

/-- **Georgii (2.2)(i)** for the gradient potential: each interaction term is a function of
finitely many coordinates. -/
instance isPotential_nearestNeighbourDiff (G : SimpleGraph S) (g : ℤ → ℝ) :
    IsPotential (nearestNeighbourDiff G g) := by
  classical
  refine ⟨fun Δ ↦ ?_⟩
  by_cases hΔ : Δ.card = 2 ∧ ∃ i ∈ Δ, ∃ j ∈ Δ, G.Adj i j
  · have hval : nearestNeighbourDiff G g Δ
        = fun η ↦ (2 : ℝ)⁻¹ * ∑ p ∈ Δ.offDiag, g (η p.1 - η p.2) := by
      funext η; simp only [nearestNeighbourDiff, ite_eq_left hΔ]
    rw [hval]
    refine Measurable.const_mul (Finset.measurable_sum _ fun p hp ↦ ?_) _
    obtain ⟨hp1, hp2, -⟩ := Finset.mem_offDiag.1 hp
    have m1 : Measurable[cylinderEvents (X := fun _ : S ↦ ℤ) (Δ : Set S)] fun η : S → ℤ ↦ η p.1 :=
      measurable_cylinderEvent_apply (Finset.mem_coe.2 hp1)
    have m2 : Measurable[cylinderEvents (X := fun _ : S ↦ ℤ) (Δ : Set S)] fun η : S → ℤ ↦ η p.2 :=
      measurable_cylinderEvent_apply (Finset.mem_coe.2 hp2)
    exact Measurable.of_discrete.comp (m1.sub m2)
  · have hval : nearestNeighbourDiff G g Δ = fun _ ↦ 0 :=
      funext fun η ↦ nearestNeighbourDiff_apply_of_not hΔ η
    rw [hval]
    exact measurable_const

omit [DecidableEq S] in
/-- A nonzero interaction support of the gradient potential containing `i` is an edge at `i`. -/
lemma subset_of_nearestNeighbourDiff_ne_zero (G : SimpleGraph S)
    [G.LocallyFinite] [DecidableEq S] {i : S} {A : Finset S} (hiA : i ∈ A)
    (hΦ : nearestNeighbourDiff G g A ≠ 0) :
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
  · exact hΦ (funext fun η ↦ nearestNeighbourDiff_apply_of_not hA η)

/-- **Georgii (2.15)** for the gradient potential on a locally finite graph. -/
instance isFiniteRange_nearestNeighbourDiff (G : SimpleGraph S) [G.LocallyFinite] (g : ℤ → ℝ) :
    IsFiniteRange (nearestNeighbourDiff G g) := by
  classical
  exact ⟨fun i ↦ ⟨insert i (G.neighborFinset i),
    fun A hiA hΦ ↦ subset_of_nearestNeighbourDiff_ne_zero G hiA hΦ⟩⟩

/-- **Georgii (6.16).** The discrete Gaussian potential of a graph:
`Φ_{i,j} = (σ_i - σ_j)²` on edges, `0` elsewhere. -/
abbrev discreteGaussian (G : SimpleGraph S) : Potential S ℤ :=
  nearestNeighbourDiff G fun x ↦ (x : ℝ) ^ 2

/-- **Georgii (6.16)** on an edge: `Φ_{i,j}(η) = (η i - η j)²`. -/
lemma discreteGaussian_pair {i j : S} (hij : G.Adj i j) (η : S → ℤ) :
    discreteGaussian G {i, j} η = ((η i - η j : ℤ) : ℝ) ^ 2 := by
  rw [discreteGaussian, nearestNeighbourDiff_pair_of_even (fun x ↦ by push_cast; ring) hij]

end Potential

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-- **Georgii (6.16).** The discrete Gaussian potential on the square lattice `ℤ²`. -/
abbrev dgPotential : Potential Site ℤ := Potential.discreteGaussian (latticeGraph 2)

lemma dgPotential_toFinset {i j : Site} (hij : (latticeGraph 2).Adj i j) (ζ : Site → ℤ) :
    dgPotential (s(i, j)).toFinset ζ = ((ζ i - ζ j : ℤ) : ℝ) ^ 2 := by
  rw [Sym2.toFinset_mk_eq]
  exact discreteGaussian_pair hij ζ

/-! ### Ordered bonds

Every sum over the (unordered) bonds meeting `Λ` is half a sum over the ordered adjacent pairs
whose bond meets `Λ`. Working with ordered pairs is what makes the contour bookkeeping of
(6.20) and (6.24) — which distinguishes the site *inside* a contour from the one outside —
a sum manipulation rather than a case split. -/

/-- The ordered adjacent pairs whose bond meets `Λ` (Georgii's `B` of (6.11), oriented). -/
def dirBonds (Λ : Finset Site) : Finset (Site × Site) :=
  (bondsMeeting Λ).biUnion fun e ↦ e.toFinset.offDiag

lemma mem_dirBonds {Λ : Finset Site} {p : Site × Site} :
    p ∈ dirBonds Λ ↔ (latticeGraph 2).Adj p.1 p.2 ∧ (p.1 ∈ Λ ∨ p.2 ∈ Λ) := by
  simp only [dirBonds, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, he, hp⟩
    induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨hab, hΛ⟩ := mem_bondsMeeting_mk.1 he
    rw [Sym2.toFinset_mk_eq] at hp
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.1 hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> simp_all [SimpleGraph.Adj.symm, or_comm]
  · rintro ⟨hadj, hΛ⟩
    refine ⟨s(p.1, p.2), mem_bondsMeeting_mk.2 ⟨hadj, hΛ⟩, ?_⟩
    rw [Sym2.toFinset_mk_eq]
    exact Finset.mem_offDiag.2 ⟨by simp, by simp, hadj.ne⟩

lemma swap_mem_dirBonds {Λ : Finset Site} {p : Site × Site} (hp : p ∈ dirBonds Λ) :
    p.swap ∈ dirBonds Λ := by
  obtain ⟨hadj, hΛ⟩ := mem_dirBonds.1 hp
  exact mem_dirBonds.2 ⟨hadj.symm, hΛ.symm⟩

/-- The `offDiag`s of distinct bonds are disjoint: an ordered pair determines its bond. -/
lemma disjoint_offDiag_toFinset {e f : Sym2 Site} (he : e ∈ (latticeGraph 2).edgeSet)
    (hf : f ∈ (latticeGraph 2).edgeSet) (hef : e ≠ f) :
    Disjoint e.toFinset.offDiag f.toFinset.offDiag := by
  rw [Finset.disjoint_left]
  rintro p hp hp'
  refine hef ?_
  have key : ∀ {c : Sym2 Site}, c ∈ (latticeGraph 2).edgeSet →
      p ∈ c.toFinset.offDiag → c = s(p.1, p.2) := by
    intro c hc hpc
    induction c using Sym2.ind with
    | _ a b =>
    rw [Sym2.toFinset_mk_eq] at hpc
    obtain ⟨h1, h2, hne⟩ := Finset.mem_offDiag.1 hpc
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> simp_all [Sym2.eq_swap]
  rw [key he hp, key hf hp']

/-- A sum over the bonds meeting `Λ` of a symmetric bond quantity is half the sum over the
ordered pairs. -/
lemma sum_dirBonds_eq (Λ : Finset Site) (F : Site → Site → ℝ) :
    ∑ p ∈ dirBonds Λ, F p.1 p.2
      = ∑ e ∈ bondsMeeting Λ, ∑ p ∈ e.toFinset.offDiag, F p.1 p.2 := by
  rw [dirBonds]
  refine Finset.sum_biUnion ?_
  intro e he f hf hef
  exact disjoint_offDiag_toFinset (mem_bondsMeeting.1 (Finset.mem_coe.1 he)).1
    (mem_bondsMeeting.1 (Finset.mem_coe.1 hf)).1 hef

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-! ### The finite-volume Hamiltonian as a bond sum -/

lemma dgPotential_eq_zero {A : Finset Site} (ζ : Site → ℤ)
    (hA : ¬ ∃ i j, (latticeGraph 2).Adj i j ∧ A = {i, j}) :
    dgPotential A ζ = 0 := by
  refine nearestNeighbourDiff_apply_of_not (fun h ↦ hA ?_) ζ
  obtain ⟨hcard, i, hi, j, hj, hij⟩ := h
  refine ⟨i, j, hij, ?_⟩
  symm
  refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_)
    (le_of_eq (by rw [hcard, Finset.card_pair hij.ne]))
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact hi
  · rw [Finset.mem_singleton] at hx; exact hx ▸ hj

lemma dgPotential_hamiltonianTerms_eq_zero_of_notMem {Λ : Finset Site} (ζ : Site → ℤ)
    {A : Finset Site} (hA : A ∉ (bondsMeeting Λ).image Sym2.toFinset) :
    dgPotential.hamiltonianTerms Λ ζ A = 0 := by
  by_cases hdisj : Disjoint A Λ
  · exact Potential.hamiltonianTerms_of_disjoint hdisj ζ
  rw [Potential.hamiltonianTerms_of_not_disjoint hdisj]
  refine dgPotential_eq_zero ζ ?_
  rintro ⟨i, j, hij, rfl⟩
  refine hA (Finset.mem_image.2 ⟨s(i, j), ?_, Sym2.toFinset_mk_eq⟩)
  obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hdisj
  refine mem_bondsMeeting_mk.2 ⟨hij, ?_⟩
  rcases Finset.mem_insert.1 hxA with rfl | hx
  · exact Or.inl hxΛ
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact Or.inr hxΛ

/-- The finite-volume Hamiltonian of the discrete Gaussian potential is the sum of its bond
energies over the bonds meeting `Λ`. -/
theorem dgPotential_hamiltonian_eq_sum_bonds (Λ : Finset Site) (ζ : Site → ℤ) :
    dgPotential.hamiltonian Λ ζ = ∑ e ∈ bondsMeeting Λ, dgPotential e.toFinset ζ := by
  have hsum : HasSum (dgPotential.hamiltonianTerms Λ ζ)
      (∑ A ∈ (bondsMeeting Λ).image Sym2.toFinset, dgPotential.hamiltonianTerms Λ ζ A) :=
    hasSum_sum_of_ne_finset_zero fun A hA ↦
      dgPotential_hamiltonianTerms_eq_zero_of_notMem ζ hA
  rw [Potential.hamiltonian, hsum.volume.tsum_eq,
    Finset.sum_image (toFinset_injOn_bondsMeeting Λ)]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  refine Potential.hamiltonianTerms_of_not_disjoint ?_ ζ
  obtain ⟨-, i, hiΛ, hie⟩ := mem_bondsMeeting.1 he
  exact Finset.not_disjoint_iff.2 ⟨i, by simpa using hie, hiΛ⟩

/-- **The finite-volume Hamiltonian (6.16) as an ordered bond sum**:
`H_Λ(ζ) = ½ ∑_{(i,j)} (ζ_i - ζ_j)²`, the sum running over the ordered adjacent pairs whose bond
meets `Λ`. -/
theorem dgPotential_hamiltonian_eq (Λ : Finset Site) (ζ : Site → ℤ) :
    dgPotential.hamiltonian Λ ζ
      = (2 : ℝ)⁻¹ * ∑ p ∈ dirBonds Λ, ((ζ p.1 - ζ p.2 : ℤ) : ℝ) ^ 2 := by
  rw [dgPotential_hamiltonian_eq_sum_bonds,
    sum_dirBonds_eq Λ fun a b ↦ ((ζ a - ζ b : ℤ) : ℝ) ^ 2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨hab, -⟩ := mem_bondsMeeting_mk.1 he
  rw [Sym2.toFinset_mk_eq]
  exact nearestNeighbourDiff_apply_of ⟨Finset.card_pair hab.ne, a, by simp, b, by simp, hab⟩ ζ

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-! ### The four lattice directions, and site-indexed bond sums -/

/-- The four unit directions of `ℤ²`. -/
def dirs : Finset Site := {e0, -e0, e1, -e1}

lemma mem_dirs {v : Site} : v ∈ dirs ↔ v = e0 ∨ v = -e0 ∨ v = e1 ∨ v = -e1 := by
  simp [dirs]

lemma neg_mem_dirs {v : Site} (hv : v ∈ dirs) : -v ∈ dirs := by
  rcases mem_dirs.1 hv with rfl | rfl | rfl | rfl <;> simp [mem_dirs]

lemma adj_iff_sub_mem_dirs {i j : Site} : (latticeGraph 2).Adj i j ↔ j - i ∈ dirs := by
  rw [latticeGraph_two_adj_iff, mem_dirs]
  simp only [site_ext_iff, Pi.sub_apply, Pi.neg_apply, e0_zero, e0_one, e1_zero, e1_one]
  omega

lemma adj_add_dir {i v : Site} (hv : v ∈ dirs) : (latticeGraph 2).Adj i (i + v) :=
  adj_iff_sub_mem_dirs.2 (by simpa using hv)

/-- The sites within one step of `Λ`: the endpoints of every bond meeting `Λ`. -/
def halo (Λ : Finset Site) : Finset Site := Λ ∪ dirs.biUnion fun v ↦ Λ.image (· + v)

lemma subset_halo (Λ : Finset Site) : Λ ⊆ halo Λ := Finset.subset_union_left

lemma add_mem_halo {Λ : Finset Site} {i : Site} (hi : i ∈ Λ) {v : Site} (hv : v ∈ dirs) :
    i + v ∈ halo Λ :=
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_image.2 ⟨i, hi, rfl⟩⟩)

lemma fst_mem_halo {Λ : Finset Site} {p : Site × Site} (hp : p ∈ dirBonds Λ) :
    p.1 ∈ halo Λ := by
  obtain ⟨hadj, hΛ⟩ := mem_dirBonds.1 hp
  rcases hΛ with h | h
  · exact subset_halo Λ h
  · have : p.1 = p.2 + -(p.2 - p.1) := by abel
    rw [this]
    exact add_mem_halo h (neg_mem_dirs (adj_iff_sub_mem_dirs.1 hadj))

/-- **Ordered bond sums as site sums.** A sum over the ordered bonds meeting `Λ` of a quantity
that vanishes on bonds avoiding `Λ` is the double sum over sites of the halo and the four
directions. -/
theorem sum_dirBonds_eq_sum_halo (Λ : Finset Site) {F : Site → Site → ℝ}
    (hF : ∀ i j, i ∉ Λ → j ∉ Λ → F i j = 0) :
    ∑ p ∈ dirBonds Λ, F p.1 p.2 = ∑ i ∈ halo Λ, ∑ v ∈ dirs, F i (i + v) := by
  classical
  have hinj : Set.InjOn (fun q : Site × Site ↦ (q.1, q.1 + q.2))
      ((halo Λ ×ˢ dirs : Finset (Site × Site)) : Set (Site × Site)) := by
    rintro ⟨i, v⟩ - ⟨j, w⟩ - h
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.1 h
    simpa using h2
  have hprod : ∑ i ∈ halo Λ, ∑ v ∈ dirs, F i (i + v)
      = ∑ q ∈ (halo Λ ×ˢ dirs : Finset (Site × Site)), F q.1 (q.1 + q.2) :=
    (Finset.sum_product (s := halo Λ) (t := dirs)
      (f := fun q : Site × Site ↦ F q.1 (q.1 + q.2))).symm
  rw [hprod, ← Finset.sum_image (g := fun q : Site × Site ↦ (q.1, q.1 + q.2))
    (f := fun p : Site × Site ↦ F p.1 p.2) hinj]
  refine Finset.sum_subset ?_ ?_
  · rintro p hp
    obtain ⟨hadj, hΛ⟩ := mem_dirBonds.1 hp
    refine Finset.mem_image.2 ⟨(p.1, p.2 - p.1), Finset.mem_product.2
      ⟨fst_mem_halo (p := p) hp, adj_iff_sub_mem_dirs.1 hadj⟩, ?_⟩
    simp
  · rintro p hp hpn
    obtain ⟨⟨i, v⟩, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨-, hv⟩ := Finset.mem_product.1 hq
    refine hF _ _ (fun hi ↦ hpn ?_) (fun hj ↦ hpn ?_)
    · exact mem_dirBonds.2 ⟨adj_add_dir hv, Or.inl hi⟩
    · exact mem_dirBonds.2 ⟨adj_add_dir hv, Or.inr hj⟩

/-- **Telescoping.** For a function supported in `Λ`, the sum of `u i - u (i + v)` over the halo
of `Λ` vanishes. -/
theorem sum_sub_translate_eq_zero {u : Site → ℝ} {Λ : Finset Site} (hu : ∀ i ∉ Λ, u i = 0)
    {v : Site} (hv : v ∈ dirs) :
    ∑ i ∈ halo Λ, (u i - u (i + v)) = 0 := by
  classical
  have h1 : ∑ i ∈ halo Λ, u i = ∑ i ∈ Λ, u i :=
    (Finset.sum_subset (subset_halo Λ) fun x _ hx ↦ hu x hx).symm
  have hinj : Set.InjOn (· + v) ((halo Λ : Finset Site) : Set Site) := fun a _ b _ h ↦ by
    simpa using h
  have h2 : ∑ i ∈ halo Λ, u (i + v) = ∑ j ∈ (halo Λ).image (· + v), u j :=
    (Finset.sum_image hinj).symm
  have hsub : Λ ⊆ (halo Λ).image (· + v) := by
    intro i hi
    exact Finset.mem_image.2 ⟨i + -v, add_mem_halo hi (neg_mem_dirs hv), by abel⟩
  have h3 : ∑ j ∈ (halo Λ).image (· + v), u j = ∑ i ∈ Λ, u i :=
    (Finset.sum_subset hsub fun x _ hx ↦ hu x hx).symm
  rw [Finset.sum_sub_distrib, h1, h2, h3, sub_self]

end MeasureTheory.GibbsMeasure.Shlosman

namespace Potential

/-- **Georgii Definition (6.18).** A configuration `ω` is a *ground state* of the potential `Ψ`
when every finite perturbation of `ω` has at least the energy of `ω`: `H_Λ^Ψ(ζ) ≥ H_Λ^Ψ(ω)`
whenever `Λ` is finite and `ζ = ω` off `Λ`.

This is weaker than minimising every interaction term `Ψ_A`; Georgii's staircases (6.19) are
ground states in this sense without being constant. -/
def IsGroundState {S E : Type*} [MeasurableSpace E] (Ψ : Potential S E) (ω : S → E) : Prop :=
  ∀ (Λ : Finset S) (ζ : S → E), (∀ i ∉ Λ, ζ i = ω i) → Ψ.hamiltonian Λ ω ≤ Ψ.hamiltonian Λ ζ

end Potential

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-! ### Georgii (6.19): the staircase configurations, and (6.20): they are ground states -/

/-- **Georgii (6.19).** The staircase configuration `ω^z_i = z · i₁`, `i = (i₁, i₂) ∈ ℤ²`.
For `z ≠ 0` it is an infinite staircase of slope `z` in the first lattice direction. -/
def staircase (z : ℤ) : Site → ℤ := fun i ↦ z * i 0

@[simp] lemma staircase_apply (z : ℤ) (i : Site) : staircase z i = z * i 0 := rfl

@[simp] lemma staircase_zero : staircase 0 = fun _ ↦ 0 := by
  funext i; simp [staircase]

/-- Georgii: `τ ω^z = ω^{-z}`, the spin reflection maps the staircase of slope `z` to the one of
slope `-z`. -/
lemma neg_staircase (z : ℤ) : (fun i ↦ -staircase z i) = staircase (-z) := by
  funext i; simp [staircase]

/-- The staircase increment across a bond: `ω^z_i - ω^z_{i+v} = -z v₁`. -/
lemma staircase_sub_add (z : ℤ) (i v : Site) :
    staircase z i - staircase z (i + v) = -(z * v 0) := by
  simp only [staircase_apply, Pi.add_apply]
  ring

/-- **Georgii Remark (6.20).** Every staircase `ω^z` — indeed every shift `ω^z + n` of it, the
image under Georgii's spin translation `t^{-n}` — is a ground state of the discrete Gaussian
potential (6.16).

Georgii's proof takes `Λ` to be a rectangle and telescopes each row; here the bonds meeting an
*arbitrary* finite `Λ` are summed at once, `s² - z² ≥ 2z(s - z)` is applied bond by bond, and the
resulting linear term telescopes because `ζ - ω^z` is finitely supported
(`sum_sub_translate_eq_zero`). -/
theorem isGroundState_staircase (z n : ℤ) :
    dgPotential.IsGroundState (fun i ↦ staircase z i + n) := by
  classical
  intro Λ ζ hζ
  set ω : Site → ℤ := fun i ↦ staircase z i + n with hω
  -- the real-valued difference `u = ζ - ω`, supported in `Λ`
  set u : Site → ℝ := fun i ↦ ((ζ i : ℤ) : ℝ) - ((ω i : ℤ) : ℝ) with hu
  have husupp : ∀ i ∉ Λ, u i = 0 := fun i hi ↦ by simp [hu, hζ i hi]
  set F : Site → Site → ℝ :=
    fun i j ↦ ((ζ i - ζ j : ℤ) : ℝ) ^ 2 - ((ω i - ω j : ℤ) : ℝ) ^ 2 with hF
  have hFvanish : ∀ i j, i ∉ Λ → j ∉ Λ → F i j = 0 := by
    intro i j hi hj
    simp [hF, hζ i hi, hζ j hj]
  have hdiff : dgPotential.hamiltonian Λ ζ - dgPotential.hamiltonian Λ ω
      = (2 : ℝ)⁻¹ * ∑ i ∈ halo Λ, ∑ v ∈ dirs, F i (i + v) := by
    rw [dgPotential_hamiltonian_eq, dgPotential_hamiltonian_eq, ← mul_sub,
      ← Finset.sum_sub_distrib, ← sum_dirBonds_eq_sum_halo Λ hFvanish]
  -- bond-by-bond bound `s² - w² ≥ 2w(s - w)`
  have hbond : ∀ i v : Site, 2 * (-((z : ℝ) * (v 0 : ℤ))) * (u i - u (i + v)) ≤ F i (i + v) := by
    intro i v
    have hw : ((ω i - ω (i + v) : ℤ) : ℝ) = -((z : ℝ) * ((v 0 : ℤ) : ℝ)) := by
      have : ω i - ω (i + v) = -(z * v 0) := by
        simp only [hω, staircase_apply, Pi.add_apply]; ring
      rw [this]; push_cast; ring
    have hs : ((ζ i - ζ (i + v) : ℤ) : ℝ)
        = (u i - u (i + v)) + ((ω i - ω (i + v) : ℤ) : ℝ) := by
      simp only [hu]; push_cast; ring
    rw [hF]
    simp only [hs, ← hw]
    nlinarith [sq_nonneg (u i - u (i + v))]
  have hle : ∑ i ∈ halo Λ, ∑ v ∈ dirs, 2 * (-((z : ℝ) * (v 0 : ℤ))) * (u i - u (i + v))
      ≤ ∑ i ∈ halo Λ, ∑ v ∈ dirs, F i (i + v) :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun v _ ↦ hbond i v
  have hzero : ∑ i ∈ halo Λ, ∑ v ∈ dirs, 2 * (-((z : ℝ) * (v 0 : ℤ))) * (u i - u (i + v)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun v hv ↦ ?_
    rw [← Finset.mul_sum, sum_sub_translate_eq_zero husupp hv, mul_zero]
  have hnn : (0 : ℝ) ≤ ∑ i ∈ halo Λ, ∑ v ∈ dirs, F i (i + v) := hzero ▸ hle
  have : (0 : ℝ) ≤ dgPotential.hamiltonian Λ ζ - dgPotential.hamiltonian Λ ω := by
    rw [hdiff]
    linarith
  linarith

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-! ### Georgii (6.23): lowering the spins inside a contour, and (6.24): the energy gain -/

/-- **Georgii (6.23).** `t_c ζ`: Georgii's spin translation `t` applied in the interior of a
contour, i.e. on the set `D` of sites surrounded by it, and the identity outside. -/
noncomputable def stepDown (D : Set Site) (ζ : Site → ℤ) : Site → ℤ :=
  open Classical in fun i ↦ if i ∈ D then ζ i - 1 else ζ i

lemma stepDown_of_mem {D : Set Site} {ζ : Site → ℤ} {i : Site} (hi : i ∈ D) :
    stepDown D ζ i = ζ i - 1 := by
  classical
  simp [stepDown, hi]

lemma stepDown_of_notMem {D : Set Site} {ζ : Site → ℤ} {i : Site} (hi : i ∉ D) :
    stepDown D ζ i = ζ i := by
  classical
  simp [stepDown, hi]

/-- The pairs `(i, v)` with `i ∈ D`, `v` one of the four lattice directions and `i + v ∉ D`:
Georgii's contour `c`, indexed by the endpoint of each of its bonds that lies inside. -/
def bdIdx (D : Finset Site) : Finset (Site × Site) :=
  (D ×ˢ dirs).filter fun q ↦ q.1 + q.2 ∉ D

lemma mem_bdIdx {D : Finset Site} {q : Site × Site} :
    q ∈ bdIdx D ↔ q.1 ∈ D ∧ q.2 ∈ dirs ∧ q.1 + q.2 ∉ D := by
  simp only [bdIdx, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The oriented boundary bonds of `D` inside `Λ`: ordered adjacent pairs whose first entry is in
`D` and second is not. -/
def dirBd (Λ D : Finset Site) : Finset (Site × Site) :=
  (dirBonds Λ).filter fun p ↦ p.1 ∈ D ∧ p.2 ∉ D

lemma mem_dirBd {Λ D : Finset Site} {p : Site × Site} :
    p ∈ dirBd Λ D ↔ p ∈ dirBonds Λ ∧ p.1 ∈ D ∧ p.2 ∉ D := by
  simp only [dirBd, Finset.mem_filter]

/-- Sums over the oriented boundary bonds are sums over `bdIdx D`: a boundary bond is determined
by its inner endpoint and its direction. -/
theorem sum_dirBd_eq_sum_bdIdx {Λ D : Finset Site} (hDΛ : D ⊆ Λ) (f : Site → Site → ℝ) :
    ∑ p ∈ dirBd Λ D, f p.1 p.2 = ∑ q ∈ bdIdx D, f q.1 (q.1 + q.2) := by
  refine Finset.sum_nbij' (i := fun p ↦ (p.1, p.2 - p.1)) (j := fun q ↦ (q.1, q.1 + q.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro p hp
    obtain ⟨hp1, hp2, hp3⟩ := mem_dirBd.1 hp
    exact mem_bdIdx.2 ⟨hp2, adj_iff_sub_mem_dirs.1 (mem_dirBonds.1 hp1).1,
      by simpa using hp3⟩
  · rintro q hq
    obtain ⟨hq1, hq2, hq3⟩ := mem_bdIdx.1 hq
    exact mem_dirBd.2 ⟨mem_dirBonds.2 ⟨adj_add_dir hq2, Or.inl (hDΛ hq1)⟩, hq1, hq3⟩
  · rintro p -; simp
  · rintro q -; simp
  · rintro p -; simp

/-- **Translation parity along the first lattice direction**: a finite `D ⊆ ℤ²` has as many
boundary bonds pointing in the `+e₀` direction as in the `-e₀` direction, so the horizontal
staircase increments cancel over the boundary of `D`. -/
theorem sum_bdIdx_fst_dir_eq_zero (D : Finset Site) :
    ∑ q ∈ bdIdx D, (q.2 0 : ℤ) = 0 := by
  classical
  have hcount : ∀ v : Site, ∑ i ∈ D, (if i + v ∉ D then (v 0 : ℤ) else 0)
      = (v 0) * ((D.filter fun i ↦ i + v ∉ D).card : ℤ) := by
    intro v
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsplit : ∑ q ∈ bdIdx D, (q.2 0 : ℤ)
      = ∑ v ∈ dirs, (v 0) * ((D.filter fun i ↦ i + v ∉ D).card : ℤ) := by
    rw [bdIdx, Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ ↦ hcount v
  -- the two vertical directions contribute `0`, the two horizontal ones cancel
  have hparity : ((D.filter fun i ↦ i + e0 ∉ D).card : ℤ)
      = ((D.filter fun i ↦ i + -e0 ∉ D).card : ℤ) := by
    have h1 : {x ∈ (D : Set Site) | x + e0 ∉ (D : Set Site)}
        = ((D.filter fun i ↦ i + e0 ∉ D : Finset Site) : Set Site) := by
      ext x; simp
    have h2 : {x ∈ (D : Set Site) | x - e0 ∉ (D : Set Site)}
        = ((D.filter fun i ↦ i + -e0 ∉ D : Finset Site) : Set Site) := by
      ext x; simp [sub_eq_add_neg]
    have := Set.ncard_sep_add_notMem_eq (s := (D : Set Site)) D.finite_toSet e0
    rw [h1, h2, Set.ncard_coe_finset, Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hd : dirs = {e0, -e0, e1, -e1} := rfl
  have h0 : e0 ≠ -e0 := fun h ↦ by simpa using congrFun h 0
  have h1 : e0 ≠ e1 := fun h ↦ by simpa using congrFun h 0
  have h2 : e0 ≠ -e1 := fun h ↦ by simpa using congrFun h 0
  have h3 : (-e0 : Site) ≠ e1 := fun h ↦ by simpa using congrFun h 0
  have h4 : (-e0 : Site) ≠ -e1 := fun h ↦ by simpa using congrFun h 0
  have h5 : (e1 : Site) ≠ -e1 := fun h ↦ by simpa using congrFun h 1
  rw [hsplit, hd, Finset.sum_insert (by simp [h0, h1, h2]),
    Finset.sum_insert (by simp [h3, h4]), Finset.sum_insert (by simp [h5]),
    Finset.sum_singleton]
  simp only [e0_zero, e1_zero, Pi.neg_apply]
  rw [← hparity]
  ring

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-- The oriented boundary bonds of `D` traversed the other way. -/
def dirBd' (Λ D : Finset Site) : Finset (Site × Site) :=
  (dirBonds Λ).filter fun p ↦ p.2 ∈ D ∧ p.1 ∉ D

lemma mem_dirBd' {Λ D : Finset Site} {p : Site × Site} :
    p ∈ dirBd' Λ D ↔ p ∈ dirBonds Λ ∧ p.2 ∈ D ∧ p.1 ∉ D := by
  simp only [dirBd', Finset.mem_filter]

/-- Swapping the two endpoints matches the two orientations of the boundary of `D`. -/
theorem sum_dirBd'_eq_sum_dirBd {Λ D : Finset Site} {f : Site → Site → ℝ}
    (hf : ∀ i j, f i j = f j i) :
    ∑ p ∈ dirBd' Λ D, f p.1 p.2 = ∑ p ∈ dirBd Λ D, f p.1 p.2 := by
  refine Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) ?_ ?_ ?_ ?_ ?_
  · rintro p hp
    obtain ⟨h1, h2, h3⟩ := mem_dirBd'.1 hp
    exact mem_dirBd.2 ⟨swap_mem_dirBonds h1, h2, h3⟩
  · rintro p hp
    obtain ⟨h1, h2, h3⟩ := mem_dirBd.1 hp
    exact mem_dirBd'.2 ⟨swap_mem_dirBonds h1, h2, h3⟩
  · rintro p -; simp
  · rintro p -; simp
  · rintro p -; exact hf p.1 p.2

/-- **Georgii Lemma (6.24).** Let `z, k ∈ ℤ`, let `D ⊆ Λ` be the set of sites surrounded by a
`(z, k)`-contour `c` for `ζ` — so that across every bond of `c` the inner spin has
`ζ - ω^z ≥ k` and the outer one has `ζ - ω^z < k`, which is Georgii's definition of a
`(z, k)`-contour — and let `t_c ζ` lower the spins on `D` by one. Then

`H_Λ^Φ(ζ) - H_Λ^Φ(t_c ζ) ≥ |c|`,

`|c| = |bdIdx D|` being the number of bonds of the contour.

The vertical bonds of the contour each contribute at least `1`; the horizontal ones contribute at
least `1 ∓ 2z`, and the two horizontal orientations occur equally often
(`sum_bdIdx_fst_dir_eq_zero`), so the `z`-terms cancel. -/
theorem card_bdIdx_le_hamiltonian_sub_stepDown (z k : ℤ)
    {Λ D : Finset Site} (hDΛ : D ⊆ Λ) {ζ : Site → ℤ}
    (hc : ∀ i ∈ D, ∀ j ∉ D, (latticeGraph 2).Adj i j →
      k ≤ ζ i - staircase z i ∧ ζ j - staircase z j < k) :
    ((bdIdx D).card : ℝ)
      ≤ dgPotential.hamiltonian Λ ζ - dgPotential.hamiltonian Λ (stepDown ↑D ζ) := by
  classical
  set t : Site → ℤ := stepDown (↑D : Set Site) ζ with ht
  set F : Site → Site → ℝ :=
    fun i j ↦ ((ζ i - ζ j : ℤ) : ℝ) ^ 2 - ((t i - t j : ℤ) : ℝ) ^ 2 with hFdef
  have hFsymm : ∀ i j, F i j = F j i := by
    intro i j
    simp only [hFdef]
    rw [show ζ j - ζ i = -(ζ i - ζ j) by ring, show t j - t i = -(t i - t j) by ring]
    push_cast
    ring
  have hFzero : ∀ i j : Site, (i ∈ D ↔ j ∈ D) → F i j = 0 := by
    intro i j hij
    by_cases hi : i ∈ D
    · have hj : j ∈ D := hij.1 hi
      simp only [hFdef, ht, stepDown_of_mem (D := (↑D : Set Site)) (by simpa using hi),
        stepDown_of_mem (D := (↑D : Set Site)) (by simpa using hj)]
      ring_nf
    · have hj : j ∉ D := fun h ↦ hi (hij.2 h)
      simp only [hFdef, ht, stepDown_of_notMem (D := (↑D : Set Site)) (by simpa using hi),
        stepDown_of_notMem (D := (↑D : Set Site)) (by simpa using hj)]
      ring_nf
  have hFbd : ∀ i j : Site, i ∈ D → j ∉ D → F i j = 2 * ((ζ i - ζ j : ℤ) : ℝ) - 1 := by
    intro i j hi hj
    simp only [hFdef, ht, stepDown_of_mem (D := (↑D : Set Site)) (by simpa using hi),
      stepDown_of_notMem (D := (↑D : Set Site)) (by simpa using hj)]
    have : ζ i - 1 - ζ j = (ζ i - ζ j) - 1 := by ring
    rw [this]
    push_cast
    ring
  -- the energy difference is half the sum of `F` over the ordered bonds meeting `Λ`
  have hdiff : dgPotential.hamiltonian Λ ζ - dgPotential.hamiltonian Λ t
      = (2 : ℝ)⁻¹ * ∑ p ∈ dirBonds Λ, F p.1 p.2 := by
    rw [dgPotential_hamiltonian_eq, dgPotential_hamiltonian_eq, ← mul_sub,
      ← Finset.sum_sub_distrib]
  -- only the boundary bonds contribute, and each unoriented one twice
  have hsplit : ∑ p ∈ dirBonds Λ, F p.1 p.2 = 2 * ∑ p ∈ dirBd Λ D, F p.1 p.2 := by
    have hpn := Finset.sum_filter_add_sum_filter_not (dirBonds Λ)
      (fun p ↦ p.1 ∈ D ∧ p.2 ∉ D) (fun p ↦ F p.1 p.2)
    have hrest : ∑ p ∈ dirBd' Λ D, F p.1 p.2
        = ∑ p ∈ (dirBonds Λ).filter (fun p ↦ ¬ (p.1 ∈ D ∧ p.2 ∉ D)), F p.1 p.2 := by
      refine Finset.sum_subset (fun p hp ↦ ?_) (fun p hp hpn' ↦ ?_)
      · obtain ⟨h1, h2, h3⟩ := mem_dirBd'.1 hp
        exact Finset.mem_filter.2 ⟨h1, fun h ↦ h3 h.1⟩
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
        refine hFzero _ _ ⟨fun hd ↦ ?_, fun hd ↦ ?_⟩
        · by_contra hnd
          exact h2 ⟨hd, hnd⟩
        · by_contra hnd
          exact hpn' (mem_dirBd'.2 ⟨h1, hd, hnd⟩)
      -- (the two branches above cover `p.1 ∈ D` and `p.2 ∈ D`)
    rw [← hpn, ← hrest, sum_dirBd'_eq_sum_dirBd hFsymm, dirBd]
    ring
  -- the boundary sum, indexed by the inner endpoints
  have hbd : ∑ p ∈ dirBd Λ D, F p.1 p.2
      = ∑ q ∈ bdIdx D, (2 * ((ζ q.1 - ζ (q.1 + q.2) : ℤ) : ℝ) - 1) := by
    rw [sum_dirBd_eq_sum_bdIdx hDΛ]
    refine Finset.sum_congr rfl fun q hq ↦ ?_
    obtain ⟨h1, h2, h3⟩ := mem_bdIdx.1 hq
    exact hFbd _ _ h1 h3
  -- the contour bound, bond by bond
  have hterm : ∀ q ∈ bdIdx D,
      ((1 : ℝ) - 2 * (z : ℝ) * ((q.2 0 : ℤ) : ℝ))
        ≤ 2 * ((ζ q.1 - ζ (q.1 + q.2) : ℤ) : ℝ) - 1 := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := mem_bdIdx.1 hq
    have hz : (1 : ℤ) - z * q.2 0 ≤ ζ q.1 - ζ (q.1 + q.2) := by
      obtain ⟨hA, hB⟩ := hc q.1 h1 (q.1 + q.2) h3 (adj_add_dir h2)
      have hC : staircase z q.1 - staircase z (q.1 + q.2) = -(z * q.2 0) :=
        staircase_sub_add z q.1 q.2
      omega
    have := (Int.cast_le (R := ℝ)).2 hz
    push_cast at this ⊢
    linarith
  have hsum : ((bdIdx D).card : ℝ)
      ≤ ∑ q ∈ bdIdx D, (2 * ((ζ q.1 - ζ (q.1 + q.2) : ℤ) : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum]
    have : ∑ q ∈ bdIdx D, ((q.2 0 : ℤ) : ℝ) = ((∑ q ∈ bdIdx D, (q.2 0 : ℤ) : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [this, sum_bdIdx_fst_dir_eq_zero D]
    simp
  rw [hdiff, hsplit, hbd]
  linarith [hsum]

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-! ### λ-admissibility of `βΦ` for counting measure (Georgii, first display of §6.3) -/

/-- Georgii's first energy bound: `H_Λ^Φ(ξ) ≥ ∑_{i ∈ Λ} (ξ_i - ξ_{i - (1,0)})²`, the horizontal
bonds entering `Λ` from the left being pairwise distinct bonds meeting `Λ` and every bond energy
being nonnegative. -/
theorem sum_sq_horiz_le_hamiltonian (Λ : Finset Site) (ξ : Site → ℤ) :
    ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2 ≤ dgPotential.hamiltonian Λ ξ := by
  classical
  set g : Site × Site → ℝ := fun p ↦ ((ξ p.1 - ξ p.2 : ℤ) : ℝ) ^ 2 with hg
  set P : Finset (Site × Site) := Λ.image fun i ↦ (i, i - e0) with hP
  set P' : Finset (Site × Site) := Λ.image fun i ↦ (i - e0, i) with hP'
  have hinj : Set.InjOn (fun i : Site ↦ (i, i - e0)) (Λ : Set Site) := fun a _ b _ h ↦ by
    simpa using (Prod.ext_iff.1 h).1
  have hinj' : Set.InjOn (fun i : Site ↦ (i - e0, i)) (Λ : Set Site) := fun a _ b _ h ↦ by
    simpa using (Prod.ext_iff.1 h).2
  have hPd : P ⊆ dirBonds Λ := by
    rintro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact mem_dirBonds.2 ⟨adj_iff_sub_mem_dirs.2 (by simp [mem_dirs]), Or.inl hi⟩
  have hP'd : P' ⊆ dirBonds Λ := by
    rintro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
    exact mem_dirBonds.2 ⟨adj_iff_sub_mem_dirs.2 (by simp [mem_dirs]), Or.inr hi⟩
  have hdisj : Disjoint P P' := by
    rw [Finset.disjoint_left]
    rintro p hp hp'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hp'
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hj
    simp only at h1 h2
    subst h2
    have := congrFun h1 0
    simp only [Pi.sub_apply, e0_zero] at this
    omega
  have hnonneg : ∀ p ∈ dirBonds Λ, 0 ≤ g p := fun p _ ↦ by positivity
  have hstep : ∑ p ∈ P ∪ P', g p ≤ ∑ p ∈ dirBonds Λ, g p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hPd hP'd)
      fun p hp _ ↦ hnonneg p hp
  have hsplit : ∑ p ∈ P ∪ P', g p = 2 * ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2 := by
    rw [Finset.sum_union hdisj, hP, hP', Finset.sum_image hinj, Finset.sum_image hinj']
    have hsw : ∀ i : Site, g (i - e0, i) = g (i, i - e0) := fun i ↦ by
      show ((ξ (i - e0) - ξ i : ℤ) : ℝ) ^ 2 = ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2
      rw [show ξ (i - e0) - ξ i = -(ξ i - ξ (i - e0)) by ring]
      push_cast
      ring
    simp only [hsw]
    show (∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2) + ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2
      = 2 * ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2
    ring
  rw [dgPotential_hamiltonian_eq]
  have := hsplit ▸ hstep
  linarith

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-- The horizontal increments inside `Λ` of a configuration with a fixed boundary condition:
Georgii's substitution `ζ ↦ (ζ_i - ζ_{i - (1,0)})_{i ∈ Λ}`. -/
def horizGrad (Λ : Finset Site) (η : Site → ℤ) (ζ : ↥Λ → ℤ) : ↥Λ → ℤ :=
  fun i ↦ juxt (Λ : Set Site) η ζ (i : Site)
    - juxt (Λ : Set Site) η ζ ((i : Site) - e0)

/-- **Georgii's injection.** A configuration agreeing with `η` off `Λ` is determined by its
horizontal increments inside `Λ`: walking left along a row one leaves `Λ`, where the configuration
is prescribed. -/
theorem horizGrad_injective (Λ : Finset Site) (η : Site → ℤ) :
    Function.Injective (horizGrad Λ η) := by
  classical
  intro ζ ζ' h
  set ξ := juxt (Λ : Set Site) η ζ with hξ
  set ξ' := juxt (Λ : Set Site) η ζ' with hξ'
  have hout : ∀ x : Site, x ∉ Λ → ξ x = ξ' x := fun x hx ↦ by
    have hx' : x ∉ (Λ : Set Site) := by simpa using hx
    rw [hξ, hξ', juxt_apply_of_not_mem hx', juxt_apply_of_not_mem hx']
  have hstep : ∀ x : Site, x ∈ Λ → ξ x - ξ ((x : Site) - e0) = ξ' x - ξ' ((x : Site) - e0) := by
    intro x hx
    exact congrFun h ⟨x, by simpa using hx⟩
  have hall : ∀ x : Site, ξ x = ξ' x := by
    by_contra hcon
    obtain ⟨x₀, hx₀⟩ : ∃ x : Site, ξ x ≠ ξ' x := by
      by_contra h'
      exact hcon fun x ↦ not_not.1 fun hne ↦ h' ⟨x, hne⟩
    set T : Finset Site := Λ.filter fun i ↦ ξ i ≠ ξ' i with hT
    have hx₀Λ : x₀ ∈ Λ := by
      by_contra hx
      exact hx₀ (hout x₀ hx)
    have hTne : T.Nonempty := ⟨x₀, Finset.mem_filter.2 ⟨hx₀Λ, hx₀⟩⟩
    obtain ⟨i, hiT, hmin⟩ := T.exists_min_image (fun i ↦ i 0) hTne
    obtain ⟨hiΛ, hine⟩ := Finset.mem_filter.1 hiT
    have hprev : ξ ((i : Site) - e0) ≠ ξ' ((i : Site) - e0) := by
      have := hstep i hiΛ
      omega
    have hprevΛ : (i : Site) - e0 ∈ Λ := by
      by_contra hx
      exact hprev (hout _ hx)
    have := hmin _ (Finset.mem_filter.2 ⟨hprevΛ, hprev⟩)
    simp only [Pi.sub_apply, e0_zero] at this
    omega
  funext i
  have hi : (i : Site) ∈ (Λ : Set Site) := by simp
  have h2 := hall (i : Site)
  rwa [hξ, hξ', juxt_apply_of_mem hi, juxt_apply_of_mem hi] at h2

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-- The single-spin Gaussian weight `e^{-βx²}` of Georgii's admissibility bound. -/
def spinWeight (β : ℝ) (x : ℤ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β * (x : ℝ) ^ 2))

lemma tsum_spinWeight_ne_top {β : ℝ} (hβ : 0 < β) : (∑' x : ℤ, spinWeight β x) ≠ ⊤ :=
  ENNReal.tsum_ofReal_exp_neg_mul_sq_ne_top hβ

/-- **Georgii's admissibility bound, bond by bond.** The Boltzmann factor of a configuration with
boundary condition `η` is at most the product of the Gaussian weights of its horizontal
increments. -/
theorem boltzmannFactor_le_prod_spinWeight {β : ℝ} (hβ : 0 ≤ β) (Λ : Finset Site) (η : Site → ℤ)
    (ζ : ↥Λ → ℤ) :
    dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) η ζ)
      ≤ ∏ i : ↥Λ, spinWeight β (horizGrad Λ η ζ i) := by
  classical
  set ξ := juxt (Λ : Set Site) η ζ with hξ
  have hsum : ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2 ≤ dgPotential.hamiltonian Λ ξ :=
    sum_sq_horiz_le_hamiltonian Λ ξ
  have hexp : Real.exp (-β * dgPotential.hamiltonian Λ ξ)
      ≤ Real.exp (-β * ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith
  have hprod : Real.exp (-β * ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2)
      = ∏ i ∈ Λ, Real.exp (-β * ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2) := by
    rw [Finset.mul_sum, Real.exp_sum]
  have hcast : ∏ i ∈ Λ, ENNReal.ofReal (Real.exp (-β * ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2))
      = ∏ i : ↥Λ, spinWeight β (horizGrad Λ η ζ i) := by
    rw [← Finset.prod_coe_sort Λ
      (fun i ↦ ENNReal.ofReal (Real.exp (-β * ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2)))]
    rfl
  calc dgPotential.boltzmannFactor β Λ ξ
      = ENNReal.ofReal (Real.exp (-β * dgPotential.hamiltonian Λ ξ)) := rfl
    _ ≤ ENNReal.ofReal (Real.exp (-β * ∑ i ∈ Λ, ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hexp
    _ = ENNReal.ofReal (∏ i ∈ Λ, Real.exp (-β * ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2)) := by
        rw [hprod]
    _ = ∏ i ∈ Λ, ENNReal.ofReal (Real.exp (-β * ((ξ i - ξ (i - e0) : ℤ) : ℝ) ^ 2)) :=
        ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le
    _ = ∏ i : ↥Λ, spinWeight β (horizGrad Λ η ζ i) := hcast

/-- The partition function of the discrete Gaussian potential over counting measure is the sum of
the Boltzmann factors over the configurations inside `Λ`. -/
theorem sigmaFiniteLambdaZ_dgPotential (β : ℝ) (Λ : Finset Site) (η : Site → ℤ) :
    Specification.sigmaFiniteLambdaZ (S := Site) (E := ℤ) Measure.count
        (dgPotential.boltzmannFactor β) Λ η
      = ∑' ζ : ↥Λ → ℤ, dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) η ζ) := by
  have hpi : (Measure.pi fun _ : ↥Λ ↦ (Measure.count : Measure ℤ)) = Measure.count :=
    Measure.pi_count
  rw [Specification.sigmaFiniteLambdaZ,
    Specification.sigmaFiniteLambdaFun_apply_eq_map Measure.count Λ η,
    lintegral_map (Potential.measurable_boltzmannFactor β Λ) Measurable.juxt, hpi,
    lintegral_count]
  rfl

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

/-- **Georgii §6.3, first display.** Every positive multiple `βΦ` of the discrete Gaussian
potential (6.16) is `λ`-admissible for counting measure `λ` on `ℤ`:

`Z_Λ^{βΦ}(ω) = ∑_{ζ : ζ_{S∖Λ} = ω_{S∖Λ}} e^{-βH_Λ^Φ(ζ)} ≤ (∑_{x ∈ ℤ} e^{-βx²})^{|Λ|} < ∞`,

and it is nonzero because the Boltzmann factor is strictly positive.  The middle inequality is
Georgii's: the map `ζ ↦ (ζ_i - ζ_{i-(1,0)})_{i ∈ Λ}` is injective on the configurations with the
given boundary condition (`horizGrad_injective`). -/
theorem isSigmaFiniteLambdaAdmissible_dgPotential {β : ℝ} (hβ : 0 < β) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := Site) (E := ℤ) Measure.count
      (dgPotential.boltzmannFactor β) := by
  intro Λ η
  rw [sigmaFiniteLambdaZ_dgPotential]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 := (ENNReal.tsum_eq_zero.1 h) (fun _ ↦ 0)
    exact absurd h0 (Potential.boltzmannFactor_pos (Φ := dgPotential) β Λ _).ne'
  · have h1 : ∑' ζ : ↥Λ → ℤ, dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) η ζ)
        ≤ ∑' ζ : ↥Λ → ℤ, ∏ i : ↥Λ, spinWeight β (horizGrad Λ η ζ i) :=
      ENNReal.tsum_le_tsum fun ζ ↦ boltzmannFactor_le_prod_spinWeight hβ.le Λ η ζ
    have h2 : ∑' ζ : ↥Λ → ℤ, ∏ i : ↥Λ, spinWeight β (horizGrad Λ η ζ i)
        ≤ ∑' d : ↥Λ → ℤ, ∏ i : ↥Λ, spinWeight β (d i) :=
      ENNReal.tsum_comp_le_tsum_of_injective (horizGrad_injective Λ η)
        (fun d : ↥Λ → ℤ ↦ ∏ i : ↥Λ, spinWeight β (d i))
    have h3 : ∑' d : ↥Λ → ℤ, ∏ i : ↥Λ, spinWeight β (d i)
        ≤ (∑' x : ℤ, spinWeight β x) ^ Fintype.card ↥Λ :=
      ENNReal.tsum_pi_prod_le (spinWeight β)
    exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (tsum_spinWeight_ne_top hβ))
      (h1.trans (h2.trans h3))

instance : NeZero (Measure.count : Measure ℤ) :=
  ⟨fun h ↦ by simpa [h] using (Measure.count_singleton (0 : ℤ))⟩

/-- **Georgii §6.3.** The Gibbsian specification `γ^{βΦ}` of the discrete Gaussian potential
(6.16) on `ℤ²`, over counting measure on the state space `E = ℤ`, at inverse temperature
`β > 0`. -/
noncomputable def dgSpecification {β : ℝ} (hβ : 0 < β) : Specification Site ℤ :=
  Potential.gibbsSpecificationOfSigmaFiniteAdmissible dgPotential Measure.count β
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)

/-- Georgii (2.9) for the discrete Gaussian model: `γ_Λ(A|η) = Z_Λ(η)⁻¹ ∫_A e^{-βH_Λ} dλ_Λ(·|η)`.
-/
theorem dgSpecification_apply_set {β : ℝ} (hβ : 0 < β) (Λ : Finset Site) (η : Site → ℤ)
    {A : Set (Site → ℤ)} (hA : MeasurableSet A) :
    dgSpecification hβ Λ η A
      = (Specification.sigmaFiniteLambdaZ (S := Site) (E := ℤ) Measure.count
          (dgPotential.boltzmannFactor β) Λ η)⁻¹ *
        ∫⁻ ω in A, dgPotential.boltzmannFactor β Λ ω
          ∂(Specification.sigmaFiniteLambdaFun (S := Site) (E := ℤ) Measure.count Λ η) :=
  Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set dgPotential Measure.count β
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ) Λ η hA

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

/-! ### Georgii Lemma (6.22): existence of a `(z, k)`-contour around an excess site -/

/-- The set of sites where `ζ` exceeds the staircase `ω^z` by at least `k`. -/
def excess (z k : ℤ) (ζ : Site → ℤ) : Set Site := {i | k ≤ ζ i - staircase z i}

/-- The connected cluster of `a` inside the `k`-excess sites of `ζ`: Georgii's set `D` in the
proof of (6.14), used again for (6.22). -/
def excessCluster (z k : ℤ) (ζ : Site → ℤ) (a : Site) : Set Site :=
  {i | ReachIn (latticeGraph 2) (excess z k ζ) a i}

lemma mem_excessCluster_self {z k : ℤ} {ζ : Site → ℤ} {a : Site} (ha : a ∈ excess z k ζ) :
    a ∈ excessCluster z k ζ a := ReachIn.refl ha

lemma excessCluster_subset {z k : ℤ} {ζ : Site → ℤ} {a : Site} :
    excessCluster z k ζ a ⊆ excess z k ζ := fun _ h ↦ h.mem_right

lemma mem_excessCluster_of_adj {z k : ℤ} {ζ : Site → ℤ} {a i j : Site}
    (hi : i ∈ excessCluster z k ζ a) (hadj : (latticeGraph 2).Adj i j) (hj : j ∈ excess z k ζ) :
    j ∈ excessCluster z k ζ a :=
  hi.trans (ReachIn.of_adj (excessCluster_subset hi) hj hadj)

/-- A reachability cluster is connected in the induced graph. -/
lemma cluster_connected {A : Set Site} {a : Site} (ha : a ∈ A) :
    ((latticeGraph 2).induce {i | ReachIn (latticeGraph 2) A a i}).Connected := by
  refine induce_connected_iff.2 ⟨⟨a, ReachIn.refl ha⟩, fun u v hu hv ↦ ?_⟩
  have huv : ReachIn (latticeGraph 2) A u v := hu.symm.trans hv
  refine huv.induction (P := fun x ↦ ReachIn (latticeGraph 2)
    {i | ReachIn (latticeGraph 2) A a i} u x) (ReachIn.refl hu) ?_
  intro p q _ hq hpq hup
  exact hup.trans (ReachIn.of_adj hup.mem_right
    (hup.mem_right.trans (ReachIn.of_adj hup.mem_right.mem_right hq hpq)) hpq)

lemma excessCluster_connected {z k : ℤ} {ζ : Site → ℤ} {a : Site} (ha : a ∈ excess z k ζ) :
    ((latticeGraph 2).induce (excessCluster z k ζ a)).Connected := cluster_connected ha

/-- Off the box, a configuration equal to the staircase has no `k`-excess (`k ≥ 1`). -/
lemma excess_subset_box {z k : ℤ} (hk : 1 ≤ k) {N : ℕ} {ζ : Site → ℤ}
    (hout : ∀ i ∉ cube 2 N, ζ i = staircase z i) : excess z k ζ ⊆ box N := by
  intro i hi
  by_contra hib
  have heq : ζ i = staircase z i := hout i (by rwa [← Finset.mem_coe, coe_cube_eq_box])
  have hi' : k ≤ ζ i - staircase z i := hi
  rw [heq, sub_self] at hi'
  omega

/-- **Georgii Lemma (6.22).** If `ζ` agrees with the staircase `ω^z` outside the box `Λ_N` and
`ζ_a - ω^z_a ≥ k ≥ 1`, then there is a `(z, k)`-contour for `ζ` surrounding `a`: a circuit `C` of
dual bonds, anchored on the horizontal half-line from `a`, whose interior contains `a`, lies in
`Λ_N`, and across every bond of which the inner spin satisfies `ζ - ω^z ≥ k` and the outer one
`ζ - ω^z < k`.

The proof is Georgii's proof of (6.14), reused verbatim: `C` is the outer boundary of the
connected cluster of `a` in `{ζ - ω^z ≥ k}`. -/
theorem exists_circuit_contour_dg (z : ℤ) {k : ℤ} (hk : 1 ≤ k) (N : ℕ) (a : Site) {ζ : Site → ℤ}
    (ha : k ≤ ζ a - staircase z a) (hout : ∀ i ∉ cube 2 N, ζ i = staircase z i) :
    ∃ C : Finset (Sym2 Site), IsCircuit C ∧ 0 < C.card ∧
      (∃ m < C.card, s(a + m • e0, a + (m + 1) • e0) ∈ C) ∧
      a ∈ interiorOf (C : Set (Sym2 Site)) ∧
      interiorOf (C : Set (Sym2 Site)) ⊆ box N ∧
      edgeBoundary (interiorOf (C : Set (Sym2 Site))) = (C : Set (Sym2 Site)) ∧
      ∀ i ∈ interiorOf (C : Set (Sym2 Site)), ∀ j ∉ interiorOf (C : Set (Sym2 Site)),
        (latticeGraph 2).Adj i j → k ≤ ζ i - staircase z i ∧ ζ j - staircase z j < k := by
  classical
  have haE : a ∈ excess z k ζ := ha
  set D : Set Site := excessCluster z k ζ a with hD
  have haD : a ∈ D := mem_excessCluster_self haE
  have hDbox : D ⊆ box N :=
    excessCluster_subset.trans (excess_subset_box hk hout)
  have hDfin : D.Finite := (box_finite N).subset hDbox
  have hOBfin : (outerBoundary D).Finite := outerBoundary_finite hDfin
  have hcoe : (↑(hOBfin.toFinset) : Set (Sym2 Site)) = outerBoundary D := Set.Finite.coe_toFinset _
  have hcard : hOBfin.toFinset.card = (outerBoundary D).ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  refine ⟨hOBfin.toFinset, isCircuit_outerBoundary hDfin ⟨a, haD⟩ (excessCluster_connected haE),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_pos, Set.Finite.toFinset_nonempty]
    exact outerBoundary_nonempty hDfin ⟨a, haD⟩
  · obtain ⟨m, hm, hbond⟩ := exists_anchor_bond hDfin haD
    exact ⟨m, by rw [hcard]; exact hm, (Set.Finite.mem_toFinset _).2 hbond⟩
  · rw [hcoe]; exact subset_interiorOf_outerBoundary hDfin haD
  · rw [hcoe]; exact interiorOf_outerBoundary_subset_box hDbox
  · rw [hcoe]; exact edgeBoundary_interiorOf_outerBoundary hDfin
  · rw [hcoe]
    intro i hi j hj hadj
    have hedge : s(i, j) ∈ edgeBoundary (interiorOf (outerBoundary D)) := ⟨i, hi, j, hj, hadj, rfl⟩
    rw [edgeBoundary_interiorOf_outerBoundary hDfin] at hedge
    rcases (mem_outerBoundary_iff hadj).1 hedge with ⟨hiD, hjout⟩ | ⟨hjD, -⟩
    · refine ⟨excessCluster_subset hiD, ?_⟩
      by_contra hcon
      exact notMem_of_mem_outside hjout
        (mem_excessCluster_of_adj hiD hadj (by simpa [excess] using not_lt.1 hcon))
    · exact absurd (subset_interiorOf_outerBoundary hDfin hjD) hj

end MeasureTheory.GibbsMeasure.Shlosman

namespace Potential

variable {S : Type*} {G : SimpleGraph S} {g : ℤ → ℝ}

open MeasureTheory.GibbsMeasure Transformation

/-- **The symmetries of a gradient potential.** If the site map of `τ` is an automorphism of `G`
and all its spin maps are one and the same `f` whose inverse preserves `g` on differences, then
`τ` preserves `Φ` (Georgii (5.3): `τ(Φ) = Φ`).

Georgii's Remark (6.17) is five instances of this: the lattice translations, the two lattice
reflections and the lattice rotation (`f = id`), the spin reflection (`f = -·`, `g` even) and the
spin translation (`f = · - 1`). -/
theorem map_nearestNeighbourDiff_eq {τ : Transformation S ℤ} {f : ℤ ≃ᵐ ℤ}
    [DecidableEq S]
    (hspin : ∀ i, τ.spin i = f)
    (hsites : ∀ i j, G.Adj (τ.sites i) (τ.sites j) ↔ G.Adj i j)
    (hg : ∀ x y : ℤ, g (f.symm x - f.symm y) = g (x - y)) :
    Potential.map τ (nearestNeighbourDiff G g) = nearestNeighbourDiff G g := by
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
  · rw [Potential.map_apply, nearestNeighbourDiff_apply_of hA,
      nearestNeighbourDiff_apply_of (hcond.2 hA)]
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
      simpa using hg (η (τ.sites p.1)) (η (τ.sites p.2))
  · rw [Potential.map_apply, nearestNeighbourDiff_apply_of_not (fun h ↦ hA (hcond.1 h)),
      nearestNeighbourDiff_apply_of_not hA]

end Potential

namespace Potential

open MeasureTheory.GibbsMeasure Transformation

/-- Negation of the spin variable, as a measurable equivalence of `ℤ`. -/
def intNeg : ℤ ≃ᵐ ℤ where
  toEquiv := Equiv.neg ℤ
  measurable_toFun := Measurable.of_discrete
  measurable_invFun := Measurable.of_discrete

@[simp] lemma intNeg_symm_apply (x : ℤ) : intNeg.symm x = -x := rfl

/-- **Georgii (6.17)(i).** The gradient potential of the lattice `ℤ^d` is shift-invariant
(Georgii (5.2)(1)). -/
theorem isShiftInvariant_nearestNeighbourDiff {d : ℕ} (g : ℤ → ℝ) :
    (nearestNeighbourDiff (latticeGraph d) g).IsShiftInvariant := by
  intro j
  refine map_nearestNeighbourDiff_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) (fun a b ↦ ?_)
    (fun x y ↦ rfl)
  have : (shift ℤ j).sites = Equiv.addRight j := rfl
  rw [this]
  change (latticeGraph d).Adj (a + j) (b + j) ↔ (latticeGraph d).Adj a b
  rw [← latticeGraph_adj_sub_iff j (a := a + j) (b := b + j)]
  simp

/-- **Georgii (6.17)(iv).** The spin reflection `τ : ω ↦ -ω` preserves the gradient potential of
an even `g` (Georgii (5.2)(2)). -/
def spinReflection (S : Type*) : Transformation S ℤ where
  sites := Equiv.refl S
  spin _ := intNeg

/-- **Georgii (6.17)(v).** The spin translation `t : ω ↦ ω - 1`: the constant case `m = -1` of
`MeasureTheory.GibbsMeasure.spinTranslation`. -/
abbrev staircaseShift (S : Type*) : Transformation S ℤ :=
  MeasureTheory.GibbsMeasure.spinTranslation fun _ : S ↦ (-1 : ℤ)

@[simp] lemma spinReflection_toFun {S : Type*} (ω : S → ℤ) (i : S) :
    (spinReflection S).toFun ω i = -ω i := rfl

@[simp] lemma staircaseShift_toFun_apply {S : Type*} (ω : S → ℤ) (i : S) :
    (staircaseShift S).toFun ω i = ω i - 1 := by
  simp [staircaseShift, sub_eq_add_neg]

variable {S : Type*} [DecidableEq S] {G : SimpleGraph S} {g : ℤ → ℝ}

/-- **Georgii (6.17)(iv).** `τ(Φ) = Φ` for the spin reflection, when `g` is even. -/
theorem map_spinReflection_nearestNeighbourDiff (heven : ∀ x : ℤ, g (-x) = g x) :
    Potential.map (spinReflection S) (nearestNeighbourDiff G g) = nearestNeighbourDiff G g := by
  refine map_nearestNeighbourDiff_eq (f := intNeg) (fun _ ↦ rfl) (fun a b ↦ Iff.rfl) fun x y ↦ ?_
  rw [intNeg_symm_apply, intNeg_symm_apply, show -x - -y = -(x - y) by ring, heven]

/-- **Georgii (6.17)(v).** `t(Φ) = Φ` for the spin translation. -/
theorem map_spinTranslation_nearestNeighbourDiff :
    Potential.map (staircaseShift S) (nearestNeighbourDiff G g) = nearestNeighbourDiff G g := by
  refine map_nearestNeighbourDiff_eq (f := MeasurableEquiv.addRight (-1 : ℤ)) (fun _ ↦ rfl)
    (fun a b ↦ Iff.rfl) fun x y ↦ ?_
  have hsymm : ∀ w : ℤ, (MeasurableEquiv.addRight (-1 : ℤ)).symm w = w + 1 := fun w ↦ by
    simp [MeasurableEquiv.addRight]
  rw [hsymm, hsymm]
  ring_nf

end Potential

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls MeasureTheory.GibbsMeasure Transformation

/-! ### Georgii Remark (6.17)(ii)–(iii): the lattice reflections and the lattice rotation -/

/-- The lattice reflection in the second axis, `(i₁, i₂) ↦ (-i₁, i₂)`. -/
def reflectFst : Site ≃ Site :=
  Function.Involutive.toPerm (fun x ↦ mk (-(x 0)) (x 1)) fun x ↦ by
    rw [site_ext_iff]; simp

/-- The lattice reflection in the first axis, `(i₁, i₂) ↦ (i₁, -i₂)`. -/
def reflectSnd : Site ≃ Site :=
  Function.Involutive.toPerm (fun x ↦ mk (x 0) (-(x 1))) fun x ↦ by
    rw [site_ext_iff]; simp

/-- The quarter-turn of the lattice: its inverse is Georgii's `i ↦ (i₂, -i₁)`. -/
def rotateSite : Site ≃ Site where
  toFun x := mk (-(x 1)) (x 0)
  invFun x := mk (x 1) (-(x 0))
  left_inv x := by rw [site_ext_iff]; simp
  right_inv x := by rw [site_ext_iff]; simp

@[simp] lemma reflectFst_apply (x : Site) : reflectFst x = mk (-(x 0)) (x 1) := rfl
@[simp] lemma reflectSnd_apply (x : Site) : reflectSnd x = mk (x 0) (-(x 1)) := rfl
@[simp] lemma rotateSite_apply (x : Site) : rotateSite x = mk (-(x 1)) (x 0) := rfl
@[simp] lemma rotateSite_symm_apply (x : Site) : rotateSite.symm x = mk (x 1) (-(x 0)) := rfl

lemma adj_reflectFst (x y : Site) :
    (latticeGraph 2).Adj (reflectFst x) (reflectFst y) ↔ (latticeGraph 2).Adj x y := by
  rw [latticeGraph_two_adj_iff, latticeGraph_two_adj_iff]
  simp only [reflectFst_apply, Peierls.mk_zero, Peierls.mk_one]
  omega

lemma adj_reflectSnd (x y : Site) :
    (latticeGraph 2).Adj (reflectSnd x) (reflectSnd y) ↔ (latticeGraph 2).Adj x y := by
  rw [latticeGraph_two_adj_iff, latticeGraph_two_adj_iff]
  simp only [reflectSnd_apply, Peierls.mk_zero, Peierls.mk_one]
  omega

lemma adj_rotateSite (x y : Site) :
    (latticeGraph 2).Adj (rotateSite x) (rotateSite y) ↔ (latticeGraph 2).Adj x y := by
  rw [latticeGraph_two_adj_iff, latticeGraph_two_adj_iff]
  simp only [rotateSite_apply, Peierls.mk_zero, Peierls.mk_one]
  omega

/-- **Georgii (6.17)(ii).** The lattice reflection `r₁`, `(r₁ω)_i = ω_{(-i₁, i₂)}`. -/
def latticeReflFst : Transformation Site ℤ where
  sites := reflectFst
  spin _ := MeasurableEquiv.refl ℤ

/-- **Georgii (6.17)(ii).** The lattice reflection `r₂`, `(r₂ω)_i = ω_{(i₁, -i₂)}`. -/
def latticeReflSnd : Transformation Site ℤ where
  sites := reflectSnd
  spin _ := MeasurableEquiv.refl ℤ

/-- **Georgii (6.17)(iii).** The lattice rotation `r₀`, `(r₀ω)_i = ω_{(i₂, -i₁)}`. -/
def latticeRot : Transformation Site ℤ where
  sites := rotateSite
  spin _ := MeasurableEquiv.refl ℤ

@[simp] lemma latticeReflFst_toFun (ω : Site → ℤ) (i : Site) :
    latticeReflFst.toFun ω i = ω (mk (-(i 0)) (i 1)) := by
  simp [latticeReflFst, Transformation.toFun, reflectFst, Function.Involutive.toPerm]

@[simp] lemma latticeReflSnd_toFun (ω : Site → ℤ) (i : Site) :
    latticeReflSnd.toFun ω i = ω (mk (i 0) (-(i 1))) := by
  simp [latticeReflSnd, Transformation.toFun, reflectSnd, Function.Involutive.toPerm]

@[simp] lemma latticeRot_toFun (ω : Site → ℤ) (i : Site) :
    latticeRot.toFun ω i = ω (mk (i 1) (-(i 0))) := by
  simp [latticeRot, Transformation.toFun]

/-- **Georgii Remark (6.17)(ii).** `r₁` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeReflFst_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeReflFst (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourDiff_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_reflectFst
    (fun _ _ ↦ rfl)

/-- **Georgii Remark (6.17)(ii).** `r₂` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeReflSnd_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeReflSnd (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourDiff_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_reflectSnd
    (fun _ _ ↦ rfl)

/-- **Georgii Remark (6.17)(iii).** `r₀` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeRot_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeRot (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourDiff_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_rotateSite
    (fun _ _ ↦ rfl)

/-- **Georgii Remark (6.17).** The five families of transformations of `Ω = ℤ^{ℤ²}` listed by
Georgii all preserve the discrete Gaussian potential (6.16): the lattice translations `θ_i`, the
lattice reflections `r₁` and `r₂`, the lattice rotation `r₀`, the spin reflection `τ : ω ↦ -ω`
and the spin translation `t : ω ↦ ω - 1`. -/
theorem map_dgPotential_eq :
    (∀ j : Site, Potential.map (shift ℤ j) dgPotential = dgPotential) ∧
      Potential.map latticeReflFst dgPotential = dgPotential ∧
      Potential.map latticeReflSnd dgPotential = dgPotential ∧
      Potential.map latticeRot dgPotential = dgPotential ∧
      Potential.map (spinReflection Site) dgPotential = dgPotential ∧
      Potential.map (staircaseShift Site) dgPotential = dgPotential :=
  ⟨isShiftInvariant_nearestNeighbourDiff _,
    map_latticeReflFst_nearestNeighbourDiff _,
    map_latticeReflSnd_nearestNeighbourDiff _,
    map_latticeRot_nearestNeighbourDiff _,
    map_spinReflection_nearestNeighbourDiff (fun x ↦ by push_cast; ring),
    map_spinTranslation_nearestNeighbourDiff⟩

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory

/-- **Counting measure is preserved by every measurable automorphism** of the state space.
Mathlib has the inequality `Function.Injective.map_count_le`; applying it to `e` and to `e.symm`
turns it into an equality. -/
lemma measurePreserving_count_of_measurableEquiv {α : Type*} [MeasurableSpace α] (e : α ≃ᵐ α) :
    MeasurePreserving e (Measure.count : Measure α) Measure.count := by
  refine ⟨e.measurable, le_antisymm (e.injective.map_count_le e.measurable) ?_⟩
  have h1 : (Measure.count : Measure α).map e.symm ≤ Measure.count :=
    e.symm.injective.map_count_le e.symm.measurable
  have h2 := Measure.map_mono h1 e.measurable
  rwa [Measure.map_map e.measurable e.symm.measurable,
    show (e ∘ e.symm) = id from funext fun x ↦ e.apply_symm_apply x, Measure.map_id] at h2

end MeasureTheory

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

variable {β : ℝ}

/-! ### The finite-volume kernel as a ratio of sums over the configurations inside `Λ` -/

/-- Every event depending on one coordinate is measurable, the state space `ℤ` being discrete. -/
lemma measurableSet_apply_mem (a : Site) (A : Set ℤ) :
    MeasurableSet {ζ : Site → ℤ | ζ a ∈ A} :=
  measurable_pi_apply a MeasurableSet.of_discrete

/-- **Georgii (2.9) over counting measure.** The reference kernel `λ_Λ(·|η)` is the image of
counting measure on `ℤ^Λ` under `juxt`, so `γ_Λ(A|η)` is a ratio of two sums over the
configurations inside `Λ`. -/
theorem dgSpecification_apply_eq_tsum (hβ : 0 < β) (Λ : Finset Site) (η : Site → ℤ)
    {A : Set (Site → ℤ)} (hA : MeasurableSet A) :
    dgSpecification hβ Λ η A
      = (∑' ζ : ↥Λ → ℤ, dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) η ζ))⁻¹
        * ∑' ζ : ↥Λ → ℤ,
            A.indicator (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) η ζ) := by
  have hpi : (Measure.pi fun _ : ↥Λ ↦ (Measure.count : Measure ℤ)) = Measure.count :=
    Measure.pi_count
  rw [dgSpecification_apply_set hβ Λ η hA, sigmaFiniteLambdaZ_dgPotential]
  congr 1
  rw [← lintegral_indicator hA,
    Specification.sigmaFiniteLambdaFun_apply_eq_map Measure.count Λ η,
    lintegral_map ((Potential.measurable_boltzmannFactor β Λ).indicator hA) Measurable.juxt,
    hpi, lintegral_count]
  rfl

/-- The configurations that fail to agree with `η` off `Λ` form a measurable set. -/
lemma measurableSet_not_boundary (Λ : Finset Site) (η : Site → ℤ) :
    MeasurableSet {ζ : Site → ℤ | ¬ ∀ i ∉ Λ, ζ i = η i} := by
  have hset : {ζ : Site → ℤ | ¬ ∀ i ∉ Λ, ζ i = η i}
      = ⋃ i : {i : Site // i ∉ Λ}, {ζ : Site → ℤ | ζ (i : Site) ≠ η i} := by
    ext ζ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, not_forall, Subtype.exists]
  rw [hset]
  exact MeasurableSet.iUnion fun i ↦
    measurableSet_apply_mem (i : Site) {x : ℤ | x ≠ η (i : Site)}

/-- **Properness of `γ^{βΦ}`, concretely.** The kernel `γ_Λ(·|η)` is carried by the
configurations agreeing with `η` off `Λ`. -/
lemma dgSpecification_boundary_null (hβ : 0 < β) (Λ : Finset Site) (η : Site → ℤ) :
    dgSpecification hβ Λ η {ζ : Site → ℤ | ¬ ∀ i ∉ Λ, ζ i = η i} = 0 := by
  rw [dgSpecification_apply_eq_tsum hβ Λ η (measurableSet_not_boundary Λ η)]
  refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.2 fun ζ ↦ ?_)
  refine Set.indicator_of_notMem (fun hmem ↦ ?_) _
  exact hmem fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi) ζ

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls

variable {β : ℝ}

/-! ### Georgii's contour events, and the injection `t_c` of (6.23) -/

/-- **Georgii's `(z, k)`-contour condition**, indexed by the finite set `D` of sites surrounded
by the contour: across every boundary bond of `D` the inner spin exceeds the staircase `ω^z` by
at least `k`, the outer one by less than `k`.  `bdIdx D` indexes the boundary bonds of `D` by
their inner endpoint and their direction. -/
def contourEvent (z k : ℤ) (D : Finset Site) : Set (Site → ℤ) :=
  ⋂ q ∈ bdIdx D, {ζ : Site → ℤ | k ≤ ζ q.1 - staircase z q.1 ∧
    ζ (q.1 + q.2) - staircase z (q.1 + q.2) < k}

lemma measurableSet_contourEvent (z k : ℤ) (D : Finset Site) :
    MeasurableSet (contourEvent z k D) := by
  refine MeasurableSet.iInter fun q ↦ MeasurableSet.iInter fun _ ↦ ?_
  have hsplit : {ζ : Site → ℤ | k ≤ ζ q.1 - staircase z q.1 ∧
        ζ (q.1 + q.2) - staircase z (q.1 + q.2) < k}
      = {ζ : Site → ℤ | ζ q.1 ∈ {x : ℤ | k ≤ x - staircase z q.1}} ∩
        {ζ : Site → ℤ | ζ (q.1 + q.2) ∈
          {x : ℤ | x - staircase z (q.1 + q.2) < k}} := rfl
  rw [hsplit]
  exact (measurableSet_apply_mem _ _).inter (measurableSet_apply_mem _ _)

/-- Membership in `contourEvent` in Georgii's own phrasing: the condition across every bond with
one endpoint inside `D` and one outside. -/
lemma contourEvent_spec {z k : ℤ} {D : Finset Site} {ζ : Site → ℤ}
    (hζ : ζ ∈ contourEvent z k D) :
    ∀ i ∈ D, ∀ j ∉ D, (latticeGraph 2).Adj i j →
      k ≤ ζ i - staircase z i ∧ ζ j - staircase z j < k := by
  intro i hi j hj hadj
  have hv : j - i ∈ dirs := adj_iff_sub_mem_dirs.1 hadj
  have hij : i + (j - i) = j := by abel
  have hq : (i, j - i) ∈ bdIdx D := mem_bdIdx.2 ⟨hi, hv, by rwa [hij]⟩
  have := Set.mem_iInter₂.1 hζ (i, j - i) hq
  simpa [hij] using this

open Classical in
/-- **Georgii (6.23) inside `Λ`.** `t_c` lowers by one the spins on `D`; on the configurations of
the finite volume `Λ` it is a bijection, which is Georgii's "injection from `A₁` into `A₂`". -/
def stepDownRestrict (Λ D : Finset Site) : (↥Λ → ℤ) ≃ (↥Λ → ℤ) where
  toFun ζ i := if (i : Site) ∈ D then ζ i - 1 else ζ i
  invFun ζ i := if (i : Site) ∈ D then ζ i + 1 else ζ i
  left_inv ζ := by funext i; by_cases h : (i : Site) ∈ D <;> simp [h]
  right_inv ζ := by funext i; by_cases h : (i : Site) ∈ D <;> simp [h]

open Classical in
/-- `t_c` commutes with the boundary condition: lowering the spins of `Λ` on `D ⊆ Λ` is
`stepDown D` on the full configuration. -/
lemma juxt_stepDownRestrict {Λ D : Finset Site} (hDΛ : D ⊆ Λ) (η : Site → ℤ) (ζ : ↥Λ → ℤ) :
    juxt (Λ : Set Site) η (stepDownRestrict Λ D ζ)
      = stepDown (↑D : Set Site) (juxt (Λ : Set Site) η ζ) := by
  funext x
  by_cases hx : x ∈ Λ
  · by_cases hxD : x ∈ D
    · rw [juxt_apply_of_mem (by simpa using hx), stepDown_of_mem (by simpa using hxD),
        juxt_apply_of_mem (by simpa using hx)]
      simp [stepDownRestrict, hxD]
    · rw [juxt_apply_of_mem (by simpa using hx), stepDown_of_notMem (by simpa using hxD),
        juxt_apply_of_mem (by simpa using hx)]
      simp [stepDownRestrict, hxD]
  · have hxD : x ∉ D := fun h ↦ hx (hDΛ h)
    rw [juxt_apply_of_not_mem (by simpa using hx), stepDown_of_notMem (by simpa using hxD),
      juxt_apply_of_not_mem (by simpa using hx)]

/-- **Georgii's contour estimate, unnormalised.** The Boltzmann sum over the configurations
which have an excess `≥ k` at `a` and for which `D` is the interior of a `(z, k)`-contour is at
most `e^{-β|c|}` times the Boltzmann sum over the configurations with excess `≥ k - 1` at `a`.
This is Lemma (6.24) fed through the injection `t_c` of (6.23). -/
theorem tsum_indicator_contour_le (hβ : 0 < β) (z k : ℤ) (a : Site) {Λ D : Finset Site}
    (hDΛ : D ⊆ Λ) :
    ∑' ζ : ↥Λ → ℤ, ({ω : Site → ℤ | k ≤ ω a - staircase z a} ∩ contourEvent z k D).indicator
        (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)
      ≤ ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ)))
        * ∑' ζ : ↥Λ → ℤ, {ω : Site → ℤ | k - 1 ≤ ω a - staircase z a}.indicator
            (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ) := by
  classical
  set c := ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ))) with hc
  set g : (↥Λ → ℤ) → ℝ≥0∞ := fun ζ ↦ {ω : Site → ℤ | k - 1 ≤ ω a - staircase z a}.indicator
    (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ) with hg
  have key : ∀ ζ : ↥Λ → ℤ,
      ({ω : Site → ℤ | k ≤ ω a - staircase z a} ∩ contourEvent z k D).indicator
        (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)
        ≤ c * g (stepDownRestrict Λ D ζ) := by
    intro ζ
    set ω : Site → ℤ := juxt (Λ : Set Site) (staircase z) ζ with hω
    by_cases hmem : ω ∈ {ω : Site → ℤ | k ≤ ω a - staircase z a} ∩ contourEvent z k D
    · obtain ⟨hexc, hcont⟩ := hmem
      have hcc := contourEvent_spec hcont
      have hE : (((bdIdx D).card : ℕ) : ℝ)
          ≤ dgPotential.hamiltonian Λ ω - dgPotential.hamiltonian Λ (stepDown (↑D : Set Site) ω) :=
        card_bdIdx_le_hamiltonian_sub_stepDown z k hDΛ hcc
      -- the image is in `A₂`
      have hdown : stepDown (↑D : Set Site) ω ∈ {ω : Site → ℤ | k - 1 ≤ ω a - staircase z a} := by
        by_cases haD : a ∈ (↑D : Set Site)
        · rw [Set.mem_ofPred_eq, stepDown_of_mem haD]
          have : k ≤ ω a - staircase z a := hexc
          omega
        · rw [Set.mem_ofPred_eq, stepDown_of_notMem haD]
          have : k ≤ ω a - staircase z a := hexc
          omega
      have hgval : g (stepDownRestrict Λ D ζ)
          = dgPotential.boltzmannFactor β Λ (stepDown (↑D : Set Site) ω) := by
        rw [hg]
        simp only
        rw [juxt_stepDownRestrict hDΛ, ← hω, Set.indicator_of_mem hdown]
      -- the energy bound
      have hexp : Real.exp (-β * dgPotential.hamiltonian Λ ω)
          ≤ Real.exp (-β * ((bdIdx D).card : ℝ))
            * Real.exp (-β * dgPotential.hamiltonian Λ (stepDown (↑D : Set Site) ω)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith [hE, hβ]
      rw [Set.indicator_of_mem
        (show ω ∈ {ω : Site → ℤ | k ≤ ω a - staircase z a} ∩ contourEvent z k D from
          ⟨hexc, hcont⟩), hgval, hc]
      calc dgPotential.boltzmannFactor β Λ ω
          = ENNReal.ofReal (Real.exp (-β * dgPotential.hamiltonian Λ ω)) := rfl
        _ ≤ ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ))
              * Real.exp (-β * dgPotential.hamiltonian Λ (stepDown (↑D : Set Site) ω))) :=
            ENNReal.ofReal_le_ofReal hexp
        _ = ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ)))
              * dgPotential.boltzmannFactor β Λ (stepDown (↑D : Set Site) ω) :=
            ENNReal.ofReal_mul (Real.exp_nonneg _)
    · rw [Set.indicator_of_notMem hmem]
      exact zero_le
  calc ∑' ζ : ↥Λ → ℤ,
        ({ω : Site → ℤ | k ≤ ω a - staircase z a} ∩ contourEvent z k D).indicator
          (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)
      ≤ ∑' ζ : ↥Λ → ℤ, c * g (stepDownRestrict Λ D ζ) := ENNReal.tsum_le_tsum key
    _ = c * ∑' ζ : ↥Λ → ℤ, g (stepDownRestrict Λ D ζ) := ENNReal.tsum_mul_left
    _ = c * ∑' ζ : ↥Λ → ℤ, g ζ := by rw [(stepDownRestrict Λ D).tsum_eq g]

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

variable {β : ℝ}

/-! ### From circuits to the sets they surround -/

open Classical in
/-- The set of sites surrounded by a contour candidate `C`, as a `Finset` of the finite volume
`Λ` (the candidates used below have their interior inside `Λ`). -/
def contourInterior (Λ : Finset Site) (C : Finset (Sym2 Site)) : Finset Site :=
  Λ.filter (· ∈ interiorOf (↑C : Set (Sym2 Site)))

lemma contourInterior_subset (Λ : Finset Site) (C : Finset (Sym2 Site)) :
    contourInterior Λ C ⊆ Λ := by
  classical
  exact Finset.filter_subset _ _

lemma coe_contourInterior {Λ : Finset Site} {C : Finset (Sym2 Site)}
    (hsub : interiorOf (↑C : Set (Sym2 Site)) ⊆ (↑Λ : Set Site)) :
    (↑(contourInterior Λ C) : Set Site) = interiorOf (↑C : Set (Sym2 Site)) := by
  classical
  ext x
  simp only [contourInterior, Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by simpa using hsub h, h⟩⟩

/-- **Georgii's `|c|`.** The boundary bonds of `D`, indexed by their inner endpoint and their
direction, are in bijection with the bonds of the edge boundary of `D`; so when `D` is the
interior of a contour `C` the number `|bdIdx D|` entering Lemma (6.24) is the length `|C|` of the
contour. -/
theorem card_bdIdx_eq_card {D : Finset Site} {C : Finset (Sym2 Site)}
    (h : edgeBoundary (↑D : Set Site) = (↑C : Set (Sym2 Site))) :
    (bdIdx D).card = C.card := by
  classical
  refine Finset.card_bij (fun q _ ↦ s(q.1, q.1 + q.2)) ?_ ?_ ?_
  · rintro q hq
    obtain ⟨h1, h2, h3⟩ := mem_bdIdx.1 hq
    have hmem : s(q.1, q.1 + q.2) ∈ edgeBoundary (↑D : Set Site) :=
      ⟨q.1, by simpa using h1, q.1 + q.2, by simpa using h3, adj_add_dir h2, rfl⟩
    rw [h] at hmem
    exact hmem
  · rintro ⟨i, v⟩ hq ⟨i', v'⟩ hq' heq
    obtain ⟨h1, h2, h3⟩ := mem_bdIdx.1 hq
    obtain ⟨h1', h2', h3'⟩ := mem_bdIdx.1 hq'
    simp only at h1 h3 h1' h3' heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, hb⟩ | ⟨ha, hb⟩
    · have : v = v' := by
        have := hb
        simpa using this
      simp [this]
    · exact absurd (ha ▸ h1) h3'
  · rintro e he
    have he' : e ∈ edgeBoundary (↑D : Set Site) := by rw [h]; exact he
    obtain ⟨i, hi, j, hj, hadj, rfl⟩ := he'
    refine ⟨(i, j - i), mem_bdIdx.2 ⟨by simpa using hi, adj_iff_sub_mem_dirs.1 hadj, ?_⟩, ?_⟩
    · have : i + (j - i) = j := by abel
      rw [this]
      simpa using hj
    · have : i + (j - i) = j := by abel
      rw [this]

/-! ### Georgii Lemma (6.22) as a covering of the excess event -/

/-- **Georgii Lemma (6.22), as a covering.** A configuration equal to the staircase `ω^z` off the
box `Λ_N` and with an excess `≥ k ≥ 1` at `a` carries a `(z, k)`-contour surrounding `a`: it lies
in the contour event of the interior of one of the anchored circuit candidates. -/
theorem excess_subset_iUnion_contourEvent (z : ℤ) {k : ℤ} (hk : 1 ≤ k) (N : ℕ) (a : Site) :
    {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
        {ζ : Site → ℤ | ∀ i ∉ cube 2 N, ζ i = staircase z i} ⊆
      ⋃ l : ℕ, ⋃ C ∈ sharpContourFinset (cube 2 N) a (l + 1),
        {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
          contourEvent z k (contourInterior (cube 2 N) C) := by
  classical
  rintro ζ ⟨ha, hout⟩
  obtain ⟨C, hcirc, hpos, ⟨m, hm, hbond⟩, haC, hbox, hbdeq, hcont⟩ :=
    exists_circuit_contour_dg z hk N a ha hout
  have hsub : interiorOf (↑C : Set (Sym2 Site)) ⊆ (↑(cube 2 N) : Set Site) := by
    rw [coe_cube_eq_box]; exact hbox
  have hsucc : C.card - 1 + 1 = C.card := by omega
  refine Set.mem_iUnion.2 ⟨C.card - 1, ?_⟩
  refine Set.mem_iUnion₂.2 ⟨C, ?_, ?_⟩
  · rw [mem_sharpContourFinset, hsucc]
    exact ⟨mem_anchoredCircuitFinset hcirc rfl hm hbond, hbdeq, hsub⟩
  refine ⟨ha, ?_⟩
  · refine Set.mem_iInter₂.2 fun q hq ↦ ?_
    obtain ⟨h1, h2, h3⟩ := mem_bdIdx.1 hq
    rw [← Finset.mem_coe, coe_contourInterior hsub] at h1
    have h3' : q.1 + q.2 ∉ interiorOf (↑C : Set (Sym2 Site)) := by
      rw [← coe_contourInterior hsub, Finset.mem_coe]
      exact h3
    exact hcont _ h1 _ h3' (adj_add_dir h2)

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

variable {β : ℝ}

/-! ### Georgii Lemma (6.25): the excess of the discrete Gaussian model decays geometrically -/

/-- **Georgii's contour estimate at the level of the specification.** -/
theorem dgSpecification_contourEvent_le (hβ : 0 < β) (z k : ℤ) (a : Site) {Λ D : Finset Site}
    (hDΛ : D ⊆ Λ) :
    dgSpecification hβ Λ (staircase z)
        ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩ contourEvent z k D)
      ≤ ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ)))
        * dgSpecification hβ Λ (staircase z)
            {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} := by
  have hA1 : MeasurableSet ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩ contourEvent z k D) :=
    (measurableSet_apply_mem a {x : ℤ | k ≤ x - staircase z a}).inter
      (measurableSet_contourEvent z k D)
  have hA2 : MeasurableSet {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} :=
    measurableSet_apply_mem a {x : ℤ | k - 1 ≤ x - staircase z a}
  rw [dgSpecification_apply_eq_tsum hβ Λ _ hA1, dgSpecification_apply_eq_tsum hβ Λ _ hA2]
  calc (∑' ζ : ↥Λ → ℤ,
          dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) (staircase z) ζ))⁻¹
        * ∑' ζ : ↥Λ → ℤ,
            ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩ contourEvent z k D).indicator
              (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)
      ≤ (∑' ζ : ↥Λ → ℤ,
            dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) (staircase z) ζ))⁻¹
          * (ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ)))
            * ∑' ζ : ↥Λ → ℤ, {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a}.indicator
                (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)) :=
        mul_le_mul' le_rfl (tsum_indicator_contour_le hβ z k a hDΛ)
    _ = ENNReal.ofReal (Real.exp (-β * ((bdIdx D).card : ℝ)))
          * ((∑' ζ : ↥Λ → ℤ,
              dgPotential.boltzmannFactor β Λ (juxt (Λ : Set Site) (staircase z) ζ))⁻¹
            * ∑' ζ : ↥Λ → ℤ, {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a}.indicator
                (dgPotential.boltzmannFactor β Λ) (juxt (Λ : Set Site) (staircase z) ζ)) :=
        mul_left_comm _ _ _

/-- **The Peierls sum over the contours of one length**, Georgii's `∑_{ℓ} ℓ 3^{ℓ-1} e^{-βℓ}` term
by term: the contours of `ℓ = l + 1` bonds anchored at `a` are at most `(l+1) 3^l` in number
(Lemma (6.13), `card_sharpContourFinset_le`) and each contributes at most `e^{-β(l+1)}` times
the probability of an excess `≥ k - 1`. -/
theorem dgSpecification_contourUnion_le (hβ : 0 < β) (z k : ℤ) (N : ℕ) (a : Site) (l : ℕ) :
    dgSpecification hβ (cube 2 N) (staircase z)
        (⋃ C ∈ sharpContourFinset (cube 2 N) a (l + 1),
          {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
            contourEvent z k (contourInterior (cube 2 N) C))
      ≤ ((l : ℝ≥0∞) + 1) * 3 ^ l * ENNReal.ofReal (Real.exp (-β * ((l : ℝ) + 1)))
        * dgSpecification hβ (cube 2 N) (staircase z)
            {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} := by
  classical
  set G := dgSpecification hβ (cube 2 N) (staircase z)
    {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} with hG
  set X := ENNReal.ofReal (Real.exp (-β * ((l : ℝ) + 1))) * G with hX
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ X fun C hC ↦ ?_) ?_
  · obtain ⟨hCanch, hbd, hsub⟩ := mem_sharpContourFinset.1 hC
    have hcard : C.card = l + 1 := card_eq_of_mem_anchoredCircuitFinset hCanch
    have hDcoe : (↑(contourInterior (cube 2 N) C) : Set Site) = interiorOf (↑C : Set (Sym2 Site))
        := coe_contourInterior hsub
    have hbdD : edgeBoundary (↑(contourInterior (cube 2 N) C) : Set Site)
        = (↑C : Set (Sym2 Site)) := by rw [hDcoe, hbd]
    have hbdcard : (bdIdx (contourInterior (cube 2 N) C)).card = l + 1 := by
      rw [card_bdIdx_eq_card hbdD, hcard]
    have h := dgSpecification_contourEvent_le hβ z k a
      (contourInterior_subset (cube 2 N) C)
    rw [hbdcard] at h
    refine le_trans h (le_of_eq ?_)
    rw [hX, hG]
    congr 2
    push_cast
    ring
  · rw [nsmul_eq_mul, hX, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    have hle : ((sharpContourFinset (cube 2 N) a (l + 1)).card : ℝ≥0∞)
        ≤ ((l : ℝ≥0∞) + 1) * 3 ^ l := by
      have h := card_sharpContourFinset_le (cube 2 N) a (l + 1)
      simp only [Nat.add_sub_cancel] at h
      have h' : (((sharpContourFinset (cube 2 N) a (l + 1)).card : ℕ) : ℝ≥0∞)
          ≤ (((l + 1) * 3 ^ l : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h
      push_cast at h'
      exact h'
    exact mul_le_mul' hle le_rfl

/-- **Georgii Lemma (6.25), the induction step.** For `k ≥ 1`, `β > 0` and the staircase boundary
condition `ω^z` in the box `Λ_N`,

`γ_{Λ_N}(σ_a - ω^z_a ≥ k | ω^z) ≤ r'(β/2) · γ_{Λ_N}(σ_a - ω^z_a ≥ k - 1 | ω^z)`,

where `r'(β/2) = ∑_{ℓ ≥ 1} ℓ 3^{ℓ-1} e^{-βℓ}` is Georgii's Peierls series `PeierlsSharp.r'`
evaluated at `β/2` (its bond weight is `e^{-2b}`, and here Lemma (6.24) gives only `e^{-β}` per
bond).  Georgii writes the series as `r(β)/2 = ∑_{ℓ≥1} ℓ 3^ℓ e^{-βℓ}`, three times as large,
because he does not use his own `ℓ 3^{ℓ-1}` count at this point. -/
theorem dgSpecification_excess_le_mul (hβ : 0 < β) (z : ℤ) {k : ℤ} (hk : 1 ≤ k) (N : ℕ)
    (a : Site) :
    dgSpecification hβ (cube 2 N) (staircase z) {ζ : Site → ℤ | k ≤ ζ a - staircase z a}
      ≤ r' (β / 2)
        * dgSpecification hβ (cube 2 N) (staircase z)
            {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} := by
  classical
  set G := dgSpecification hβ (cube 2 N) (staircase z)
    {ζ : Site → ℤ | k - 1 ≤ ζ a - staircase z a} with hG
  have hr : r' (β / 2)
      = ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * 3 ^ l
          * ENNReal.ofReal (Real.exp (-β * ((l : ℝ) + 1))) := by
    rw [r']
    refine tsum_congr fun l ↦ ?_
    rw [show -2 * (β / 2) * ((l : ℝ) + 1) = -β * ((l : ℝ) + 1) from by ring]
  have hsplit : {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ⊆
      ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
        {ζ : Site → ℤ | ∀ i ∉ cube 2 N, ζ i = staircase z i}) ∪
      {ζ : Site → ℤ | ¬ ∀ i ∉ cube 2 N, ζ i = staircase z i} := by
    intro ζ hζ
    by_cases h : ∀ i ∉ cube 2 N, ζ i = staircase z i
    · exact Or.inl ⟨hζ, h⟩
    · exact Or.inr h
  calc dgSpecification hβ (cube 2 N) (staircase z)
        {ζ : Site → ℤ | k ≤ ζ a - staircase z a}
      ≤ dgSpecification hβ (cube 2 N) (staircase z)
          (({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
            {ζ : Site → ℤ | ∀ i ∉ cube 2 N, ζ i = staircase z i}) ∪
            {ζ : Site → ℤ | ¬ ∀ i ∉ cube 2 N, ζ i = staircase z i}) := measure_mono hsplit
    _ ≤ dgSpecification hβ (cube 2 N) (staircase z)
          ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
            {ζ : Site → ℤ | ∀ i ∉ cube 2 N, ζ i = staircase z i})
        + dgSpecification hβ (cube 2 N) (staircase z)
          {ζ : Site → ℤ | ¬ ∀ i ∉ cube 2 N, ζ i = staircase z i} := measure_union_le _ _
    _ = dgSpecification hβ (cube 2 N) (staircase z)
          ({ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
            {ζ : Site → ℤ | ∀ i ∉ cube 2 N, ζ i = staircase z i}) := by
        rw [dgSpecification_boundary_null hβ (cube 2 N) (staircase z), add_zero]
    _ ≤ dgSpecification hβ (cube 2 N) (staircase z)
          (⋃ l : ℕ, ⋃ C ∈ sharpContourFinset (cube 2 N) a (l + 1),
            {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
              contourEvent z k (contourInterior (cube 2 N) C)) :=
        measure_mono (excess_subset_iUnion_contourEvent z hk N a)
    _ ≤ ∑' l : ℕ, dgSpecification hβ (cube 2 N) (staircase z)
          (⋃ C ∈ sharpContourFinset (cube 2 N) a (l + 1),
            {ζ : Site → ℤ | k ≤ ζ a - staircase z a} ∩
              contourEvent z k (contourInterior (cube 2 N) C)) := measure_iUnion_le _
    _ ≤ ∑' l : ℕ, (((l : ℝ≥0∞) + 1) * 3 ^ l
          * ENNReal.ofReal (Real.exp (-β * ((l : ℝ) + 1)))) * G :=
        ENNReal.tsum_le_tsum fun l ↦ dgSpecification_contourUnion_le hβ z k N a l
    _ = (∑' l : ℕ, ((l : ℝ≥0∞) + 1) * 3 ^ l
          * ENNReal.ofReal (Real.exp (-β * ((l : ℝ) + 1)))) * G := ENNReal.tsum_mul_right
    _ = r' (β / 2) * G := by rw [hr]

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

variable {β : ℝ}

/-! ### Georgii Lemma (6.25) -/

/-- **Georgii's iteration in the proof of (6.25)**: `γ_{Λ_N}(σ_a - ω^z_a ≥ k | ω^z) ≤ r'(β/2)^k`
for every `k ≥ 0`, by induction on `k` from `dgSpecification_excess_le_mul`. -/
theorem dgSpecification_excess_le_pow (hβ : 0 < β) (z : ℤ) (N : ℕ) (a : Site) (k : ℕ) :
    dgSpecification hβ (cube 2 N) (staircase z)
        {ζ : Site → ℤ | (k : ℤ) ≤ ζ a - staircase z a} ≤ r' (β / 2) ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    have h := dgSpecification_excess_le_mul hβ z (k := (k : ℤ) + 1) (by omega) N a
    rw [add_sub_cancel_right] at h
    calc dgSpecification hβ (cube 2 N) (staircase z)
          {ζ : Site → ℤ | ((k + 1 : ℕ) : ℤ) ≤ ζ a - staircase z a}
        = dgSpecification hβ (cube 2 N) (staircase z)
            {ζ : Site → ℤ | (k : ℤ) + 1 ≤ ζ a - staircase z a} := by push_cast; rfl
      _ ≤ r' (β / 2) * dgSpecification hβ (cube 2 N) (staircase z)
            {ζ : Site → ℤ | (k : ℤ) ≤ ζ a - staircase z a} := h
      _ ≤ r' (β / 2) * r' (β / 2) ^ k := mul_le_mul' le_rfl ih
      _ = r' (β / 2) ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- **Georgii Remark (6.17)(iv) applied to the specification.** The spin reflection `τ : ω ↦ -ω`
leaves `γ^{βΦ}` invariant. -/
theorem isInvariant_spinReflection_dgSpecification (hβ : 0 < β) :
    Specification.IsInvariant (spinReflection Site) (dgSpecification hβ) :=
  Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential β
    (spinReflection Site) Measure.count
    (fun _ ↦ measurePreserving_count_of_measurableEquiv intNeg)
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    (map_spinReflection_nearestNeighbourDiff fun x ↦ by push_cast; ring)

/-- **Georgii's `τ`-step in the proof of (6.25)**: reflecting the spins turns a deficit below the
staircase `ω^z` into an excess above the staircase `ω^{-z}`. -/
theorem dgSpecification_deficit_eq (hβ : 0 < β) (z k : ℤ) (Λ : Finset Site) (a : Site) :
    dgSpecification hβ Λ (staircase z) {ζ : Site → ℤ | ζ a - staircase z a ≤ -k}
      = dgSpecification hβ Λ (staircase (-z)) {ζ : Site → ℤ | k ≤ ζ a - staircase (-z) a} := by
  have hA : MeasurableSet {ζ : Site → ℤ | ζ a - staircase z a ≤ -k} :=
    measurableSet_apply_mem a {x : ℤ | x - staircase z a ≤ -k}
  have hinv : (dgSpecification hβ).map (spinReflection Site) = dgSpecification hβ :=
    isInvariant_spinReflection_dgSpecification hβ
  have hΛ : Λ.map (spinReflection Site).sites.symm.toEmbedding = Λ := by
    simp [spinReflection]
  have hη : (spinReflection Site).inv.toFun (staircase z) = staircase (-z) := by
    funext i
    simp [spinReflection, Transformation.inv, Transformation.toFun, staircase]
  have hset : (spinReflection Site).toFun ⁻¹' {ζ : Site → ℤ | ζ a - staircase z a ≤ -k}
      = {ζ : Site → ℤ | k ≤ ζ a - staircase (-z) a} := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, spinReflection_toFun, staircase_apply,
      neg_mul]
    omega
  conv_lhs => rw [← hinv]
  rw [Specification.map_apply' _ _ _ _ hA, hΛ, hη, hset]

/-- **Georgii Lemma (6.25).** In the box `Λ_N` with the staircase boundary condition `ω^z`, the
spin at `a` differs from `ω^z_a` by at least `k` with probability at most `2 r'(β/2)^k`:

`γ_{Λ_N}^{βΦ}(|σ_a - ω^z_a| ≥ k | ω^z) ≤ 2 r'(β/2)^k`,

`r'(β/2) = ∑_{ℓ ≥ 1} ℓ 3^{ℓ-1} e^{-βℓ}`.  Georgii states it as `≤ r(β)^k` with
`r(β) = 1 ∧ 2 ∑_{ℓ≥1} ℓ (3e^{-β})^ℓ = 1 ∧ 6 r'(β/2)`; the bound proved here is sharper (and, for
`k = 0`, weaker only in that `2 ≥ 1`).  The two halves are Georgii's: an excess is controlled by
`dgSpecification_excess_le_pow`, a deficit is an excess for `ω^{-z}` by the spin reflection. -/
theorem dgSpecification_abs_excess_le (hβ : 0 < β) (z : ℤ) (N : ℕ) (a : Site) (k : ℕ) :
    dgSpecification hβ (cube 2 N) (staircase z)
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k := by
  have hsub : {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ⊆
      {ζ : Site → ℤ | (k : ℤ) ≤ ζ a - staircase z a} ∪
        {ζ : Site → ℤ | ζ a - staircase z a ≤ -(k : ℤ)} := by
    intro ζ hζ
    have : (k : ℤ) ≤ |ζ a - staircase z a| := hζ
    rcases lt_or_ge (ζ a - staircase z a) 0 with h | h
    · rw [abs_of_neg h] at this
      exact Or.inr (show ζ a - staircase z a ≤ -(k : ℤ) by omega)
    · rw [abs_of_nonneg h] at this
      exact Or.inl this
  have h2 : dgSpecification hβ (cube 2 N) (staircase z)
      {ζ : Site → ℤ | ζ a - staircase z a ≤ -(k : ℤ)} ≤ r' (β / 2) ^ k := by
    rw [dgSpecification_deficit_eq hβ z (k : ℤ) (cube 2 N) a]
    exact dgSpecification_excess_le_pow hβ (-z) N a k
  calc dgSpecification hβ (cube 2 N) (staircase z)
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|}
      ≤ dgSpecification hβ (cube 2 N) (staircase z)
          ({ζ : Site → ℤ | (k : ℤ) ≤ ζ a - staircase z a} ∪
            {ζ : Site → ℤ | ζ a - staircase z a ≤ -(k : ℤ)}) := measure_mono hsub
    _ ≤ dgSpecification hβ (cube 2 N) (staircase z)
          {ζ : Site → ℤ | (k : ℤ) ≤ ζ a - staircase z a}
        + dgSpecification hβ (cube 2 N) (staircase z)
          {ζ : Site → ℤ | ζ a - staircase z a ≤ -(k : ℤ)} := measure_union_le _ _
    _ ≤ r' (β / 2) ^ k + r' (β / 2) ^ k :=
        add_le_add (dgSpecification_excess_le_pow hβ z N a k) h2
    _ = 2 * r' (β / 2) ^ k := by rw [two_mul]

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure

/-- **Georgii Corollary (4.13)** in the form the discrete Gaussian model needs: a family of random
fields whose single-spin distributions are *uniformly tight* — for every site `i` and every
`ε > 0` one finite window `F ⊆ E` carries all of them up to `ε` — is locally equicontinuous, and
hence (Proposition (4.9)) has a cluster point in the topology of local convergence.

Georgii states (4.13) for a Polish `E` and compact windows; over the countable `E = ℤ` of §6.3
the compact windows are the finite ones, and the proof is the one below: outside a finite window
in each of the finitely many coordinates of `Λ` there is mass at most `ε`, and inside it only
finitely many `Λ`-configurations occur, so an antitone sequence of `𝓕_Λ`-events with empty
intersection eventually misses the window entirely.

This is a statement about `LocallyEquicontinuous` and belongs beside it in
`GibbsMeasure/Topology/ClusterPoints.lean`. -/
theorem locallyEquicontinuous_of_uniformlyTight {S E ι : Type*} [MeasurableSpace E] [Nonempty E]
    {l : Filter ι} {μs : ι → ProbabilityMeasure (S → E)}
    (htight : ∀ (i : S) (ε : ℝ≥0∞), 0 < ε → ∃ F : Finset E,
      ∀ n, (μs n : Measure (S → E)) {ω : S → E | ω i ∉ F} ≤ ε) :
    LocallyEquicontinuous l μs := by
  classical
  intro Λ A hmeas hanti hempty
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  set ε' : ℝ≥0∞ := ε / ((Λ.card : ℝ≥0∞) + 1) with hε'def
  have hne : ((Λ.card : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hnt : ((Λ.card : ℝ≥0∞) + 1) ≠ ⊤ := by simp
  have hε' : 0 < ε' := ENNReal.div_pos hε.ne' hnt
  have hsum : (Λ.card : ℝ≥0∞) * ε' ≤ ε := by
    calc (Λ.card : ℝ≥0∞) * ε' ≤ ((Λ.card : ℝ≥0∞) + 1) * ε' := by
          exact mul_le_mul' le_self_add le_rfl
      _ = ε := by rw [hε'def, ENNReal.mul_div_cancel' (fun h ↦ absurd h hne) (fun h ↦ absurd h hnt)]
  choose F hF using fun i : S ↦ htight i ε' hε'
  set K : Set (S → E) := {ω : S → E | ∀ i ∈ Λ, ω i ∈ F i} with hK
  have hKc : ∀ n, (μs n : Measure (S → E)) Kᶜ ≤ ε := by
    intro n
    have hsub : (Kᶜ : Set (S → E)) ⊆ ⋃ i ∈ Λ, {ω : S → E | ω i ∉ F i} := by
      intro ω hω
      simp only [hK, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
      obtain ⟨i, hi, hωi⟩ := hω
      exact Set.mem_biUnion hi hωi
    calc (μs n : Measure (S → E)) Kᶜ
        ≤ (μs n : Measure (S → E)) (⋃ i ∈ Λ, {ω : S → E | ω i ∉ F i}) := measure_mono hsub
      _ ≤ ∑ i ∈ Λ, (μs n : Measure (S → E)) {ω : S → E | ω i ∉ F i} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ Λ, ε' := Finset.sum_le_sum fun i _ ↦ hF i n
      _ = (Λ.card : ℝ≥0∞) * ε' := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ε := hsum
  set sec : (↥Λ → E) → (S → E) :=
    fun x j ↦ if hj : j ∈ Λ then x ⟨j, hj⟩ else Classical.arbitrary E with hsec
  have hex : ∀ x : ↥Λ → E, ∃ m : ℕ, sec x ∉ A m := by
    intro x
    by_contra hcon
    push Not at hcon
    have hmem : sec x ∈ ⋂ m, A m := Set.mem_iInter.2 hcon
    rw [hempty] at hmem
    exact hmem
  choose mfun hmfun using hex
  set T : Finset (↥Λ → E) := Fintype.piFinset fun i : ↥Λ ↦ F (i : S) with hT
  refine ⟨T.sup mfun, fun m hm ↦ ?_⟩
  have hAsub : A m ⊆ Kᶜ := by
    intro ω hωA hωK
    set x : ↥Λ → E := fun i ↦ ω (i : S) with hx
    have hxT : x ∈ T := Fintype.mem_piFinset.2 fun i ↦ hωK (i : S) i.2
    have hle : mfun x ≤ m := le_trans (Finset.le_sup hxT) hm
    have hωm : ω ∈ A (mfun x) := hanti hle hωA
    have hagree : ∀ i ∈ (Λ : Set S), sec x i = ω i := by
      intro i hi
      have hiΛ : i ∈ Λ := by simpa using hi
      simp [hsec, hiΛ, hx]
    exact hmfun x ((mem_congr_of_measurableSet_cylinderEvents (hmeas (mfun x)) hagree).2 hωm)
  exact Filter.limsup_le_of_le (h := Filter.Eventually.of_forall fun n ↦
    le_trans (measure_mono hAsub) (hKc n))

end MeasureTheory.GibbsMeasure

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp Filter Topology

variable {β : ℝ}

/-! ### Quasilocality of `γ^{βΦ}` -/

/-- The finite-volume Hamiltonian of the discrete Gaussian potential depends only on the halo of
`Λ`: it is a finite sum of bond energies over the bonds meeting `Λ`. -/
lemma dgPotential_hamiltonian_congr (Λ : Finset Site) {ζ η : Site → ℤ}
    (h : ∀ i ∈ halo Λ, ζ i = η i) :
    dgPotential.hamiltonian Λ ζ = dgPotential.hamiltonian Λ η := by
  rw [dgPotential_hamiltonian_eq, dgPotential_hamiltonian_eq]
  congr 1
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [h p.1 (fst_mem_halo hp), h p.2 (by simpa using fst_mem_halo (swap_mem_dirBonds hp))]

/-- **Georgii Proposition (2.24)(b) for the discrete Gaussian model.** `γ^{βΦ}` is quasilocal:
its Hamiltonians are local functions (they involve only the bonds meeting `Λ`). -/
theorem isQuasilocal_dgSpecification (hβ : 0 < β) : (dgSpecification hβ).IsQuasilocal :=
  Potential.isQuasilocal_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential Measure.count β
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    fun Λ ε hε ↦ ⟨halo Λ, fun ζ η hagree ↦ by
      show |β * dgPotential.hamiltonian Λ ζ - β * dgPotential.hamiltonian Λ η| ≤ ε
      rw [dgPotential_hamiltonian_congr Λ hagree, sub_self, abs_zero]
      exact hε.le⟩

/-! ### Georgii Theorem (6.21): the random staircases -/

/-- The one-site event `{|σ_a - ω^z_a| ≥ k}` is a local event. -/
lemma absExcess_mem_localEvents (z : ℤ) (a : Site) (k : ℕ) :
    {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ∈ localEvents Site ℤ := by
  refine mem_localEvents_of_cylinderEvents {a} ?_
  have hmem : a ∈ (({a} : Finset Site) : Set Site) := by simp
  exact measurable_cylinderEvent_apply (X := fun _ : Site ↦ ℤ) hmem
    (MeasurableSet.of_discrete (s := {x : ℤ | (k : ℤ) ≤ |x - staircase z a|}))

/-- **Uniform tightness of the finite-volume distributions with staircase boundary condition**,
Georgii's `lim_{k→∞} sup_N ν_{N,z}(|σ_a| ≥ k) = 0`: the input to Corollary (4.13). -/
theorem locallyEquicontinuous_dg_cube (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    LocallyEquicontinuous atTop
      (fun N : ℕ ↦ finiteVolumeDistributions (dgSpecification hβ) (staircase z) (cube 2 N)) := by
  classical
  have hpow : Tendsto (fun k : ℕ ↦ 2 * r' (β / 2) ^ k) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by simp))
  refine locallyEquicontinuous_of_uniformlyTight fun a ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop_zero.1 hpow) ε hε
  refine ⟨Finset.Icc (staircase z a - (k : ℤ) + 1) (staircase z a + (k : ℤ) - 1), fun N ↦ ?_⟩
  refine le_trans (measure_mono ?_) (le_trans
    (dgSpecification_abs_excess_le hβ z N a k) (hk k le_rfl))
  intro ω hω
  have hω' : ω a ∉ Finset.Icc (staircase z a - (k : ℤ) + 1) (staircase z a + (k : ℤ) - 1) := hω
  rw [Finset.mem_Icc] at hω'
  have hcase : ω a < staircase z a - (k : ℤ) + 1 ∨ staircase z a + (k : ℤ) - 1 < ω a := by
    omega
  show (k : ℤ) ≤ |ω a - staircase z a|
  rcases hcase with h | h
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

/-- **Georgii Theorem (6.21), the construction.** For every `z ∈ ℤ` and every `β > 0` at which
Georgii's Peierls series converges (`r'(β/2) < 1`), the finite-volume Gibbs distributions in the
boxes `Λ_N` with the staircase boundary condition `ω^z` have a cluster point `μ_z^β`; it is a
Gibbs measure for `βΦ` and inherits the estimate of Lemma (6.25):

`μ_z^β(|σ_a - ω^z_a| ≥ k) ≤ 2 r'(β/2)^k`  for all `a ∈ S`, `k ≥ 0`.

Georgii's `ν_{N,z}` are the *shift averages* of these distributions over the translates of `Λ_N`;
he averages only in order to get the invariance statement (ii) out of Example (5.20)(1). -/
theorem exists_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    ∃ μ : ProbabilityMeasure (Site → ℤ),
      μ ∈ GP (S := Site) (E := ℤ) (dgSpecification hβ) ∧
        ∀ (a : Site) (k : ℕ),
          (μ : Measure (Site → ℤ)) {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|}
            ≤ 2 * r' (β / 2) ^ k := by
  classical
  set μs : ℕ → ProbabilityMeasure (Site → ℤ) :=
    fun N ↦ finiteVolumeDistributions (dgSpecification hβ) (staircase z) (cube 2 N) with hμs
  obtain ⟨μ, hcp⟩ := exists_mapClusterPt_of_locallyEquicontinuous
    (μs := fun N : ℕ ↦ (WithSetwiseTopology.ofMeasure (μs N) : WithLocalConvergence Site ℤ))
    (locallyEquicontinuous_dg_cube hβ hr z)
  have hbind : ∀ N : ℕ, (dgSpecification hβ).bindPM (cube 2 N)
      ⟨Measure.dirac (staircase z), inferInstance⟩ = μs N := by
    intro N
    exact Subtype.ext
      (Measure.dirac_bind ((dgSpecification hβ).measurable_kernel_toMeasure (cube 2 N))
        (staircase z))
  refine ⟨μ.toMeasure, ?_, fun a k ↦ ?_⟩
  · refine mem_GP_of_mapClusterPt (l := (atTop : Filter ℕ)) (isQuasilocal_dgSpecification hβ)
      (γs := fun _ ↦ dgSpecification hβ) (Λs := fun N ↦ cube 2 N)
      (νs := fun _ ↦ ⟨Measure.dirac (staircase z), inferInstance⟩)
      tendsto_cube_atTop (fun Λ f _ ↦ by simp) ?_
    have hfun : (fun N : ℕ ↦ (WithSetwiseTopology.ofMeasure
          ((dgSpecification hβ).bindPM (cube 2 N)
            (⟨Measure.dirac (staircase z), inferInstance⟩ : ProbabilityMeasure (Site → ℤ))) :
          WithLocalConvergence Site ℤ))
        = fun N : ℕ ↦ (WithSetwiseTopology.ofMeasure (μs N) : WithLocalConvergence Site ℤ) :=
      funext fun N ↦ congrArg _ (hbind N)
    rw [hfun]
    exact hcp
  · exact eval_le_of_mapClusterPt (absExcess_mem_localEvents z a k) hcp
      (.of_forall fun N ↦ dgSpecification_abs_excess_le hβ z N a k)

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.PeierlsSharp

/-- **A strict version of `PeierlsSharp.r'_le_quarter`**, needed for the strict inequality
`μ_z^β(σ_a = ω^z_a) > 1/2` of Georgii (6.21)(i): `r' b ≤ 4/27 < 1/4` as soon as
`b ≥ (1/2) log 12 ≈ 1.242`.  (This belongs beside `r'_le_quarter` in
`GibbsMeasure/Model/SharpContours.lean`.) -/
theorem r'_lt_quarter {b : ℝ} (hb : Real.log 12 ≤ 2 * b) : r' b < 4⁻¹ := by
  set y := ENNReal.ofReal (Real.exp (-2 * b)) with hy
  have hexp : Real.exp (-2 * b) ≤ 1 / 12 := by
    have h1 : Real.exp (-2 * b) ≤ Real.exp (-Real.log 12) := Real.exp_le_exp.2 (by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 12), ← one_div] at h1
  have hy12 : y ≤ ENNReal.ofReal (1 / 12) := ENNReal.ofReal_le_ofReal hexp
  have h3y : 3 * y ≤ ENNReal.ofReal (1 / 4) := by
    calc 3 * y ≤ 3 * ENNReal.ofReal (1 / 12) := by gcongr
      _ = ENNReal.ofReal (1 / 4) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          norm_num
  have hsubl : ENNReal.ofReal (3 / 4) ≤ 1 - 3 * y := by
    refine le_trans (le_of_eq ?_) (tsub_le_tsub_left h3y 1)
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub _ (by norm_num : (0:ℝ) ≤ 1 / 4)]
    norm_num
  have hinv : (1 - 3 * y)⁻¹ ≤ ENNReal.ofReal (4 / 3) := by
    refine le_trans (ENNReal.inv_le_inv.2 hsubl) (le_of_eq ?_)
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 3 / 4)]
    norm_num
  rw [r'_eq]
  refine lt_of_le_of_lt (mul_le_mul' hy12 (mul_le_mul' hinv hinv)) ?_
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4 / 3),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 12),
    show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) from by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ from by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
      norm_num]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end MeasureTheory.GibbsMeasure.PeierlsSharp

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp Filter Topology Transformation

variable {β : ℝ}

/-! ### Georgii Theorem (6.21): the family `(μ_z^β)_{z ∈ ℤ}` -/

/-- **Georgii Theorem (6.21): the random staircase `μ_z^β`**, a Gibbs measure for `βΦ` obtained
as a cluster point of the finite-volume distributions in the boxes `Λ_N` with the staircase
boundary condition `ω^z`. -/
noncomputable def staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    ProbabilityMeasure (Site → ℤ) :=
  (exists_staircasePhase hβ hr z).choose

/-- `μ_z^β ∈ 𝒢(βΦ)`. -/
theorem staircasePhase_mem_GP (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    staircasePhase hβ hr z ∈ GP (S := Site) (E := ℤ) (dgSpecification hβ) :=
  (exists_staircasePhase hβ hr z).choose_spec.1

/-- **Georgii (6.21)(i), the estimate**: `μ_z^β(|σ_a - ω^z_a| ≥ k) ≤ 2 r'(β/2)^k`. -/
theorem staircasePhase_absExcess_le (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) (a : Site)
    (k : ℕ) :
    (staircasePhase hβ hr z : Measure (Site → ℤ))
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k :=
  (exists_staircasePhase hβ hr z).choose_spec.2 a k

lemma compl_spin_eq_staircase (z : ℤ) (a : Site) :
    {ζ : Site → ℤ | ζ a = staircase z a}ᶜ
      = {ζ : Site → ℤ | (1 : ℤ) ≤ |ζ a - staircase z a|} := by
  ext ζ
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    have h0 : ζ a - staircase z a ≠ 0 := sub_ne_zero.2 h
    have := abs_pos.2 h0
    omega
  · intro h heq
    rw [heq, sub_self, abs_zero] at h
    omega

/-- **Georgii Theorem (6.21)(i).** If `2 r'(β/2) < 1/2` — Georgii's `r(β) < 1/2` — then the
random staircase carries more than half of its mass on the staircase value at every site:
`μ_z^β(σ_a = ω^z_a) > 1/2`. -/
theorem half_lt_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1)
    (hq : 2 * r' (β / 2) < 2⁻¹) (z : ℤ) (a : Site) :
    2⁻¹ < (staircasePhase hβ hr z : Measure (Site → ℤ))
      {ζ : Site → ℤ | ζ a = staircase z a} := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  have hA : MeasurableSet {ζ : Site → ℤ | ζ a = staircase z a} :=
    measurableSet_apply_mem a {x : ℤ | x = staircase z a}
  have hcompl : μ {ζ : Site → ℤ | ζ a = staircase z a}ᶜ < 2⁻¹ := by
    rw [compl_spin_eq_staircase]
    refine lt_of_le_of_lt ?_ hq
    simpa using staircasePhase_absExcess_le hβ hr z a 1
  have hsum : μ {ζ : Site → ℤ | ζ a = staircase z a}
      + μ {ζ : Site → ℤ | ζ a = staircase z a}ᶜ = 1 := by
    rw [measure_add_measure_compl hA]
    simp
  by_contra hcon
  push Not at hcon
  have : (1 : ℝ≥0∞) < 2⁻¹ + 2⁻¹ := by
    calc (1 : ℝ≥0∞) = μ {ζ : Site → ℤ | ζ a = staircase z a}
          + μ {ζ : Site → ℤ | ζ a = staircase z a}ᶜ := hsum.symm
      _ < 2⁻¹ + 2⁻¹ := by
          exact ENNReal.add_lt_add_of_le_of_lt (by finiteness) hcon hcompl
  rw [ENNReal.inv_two_add_inv_two] at this
  exact absurd this (lt_irrefl 1)

/-- Two probability measures each putting more than half of its mass on a *different* value of
the same spin are different: this is the separation argument behind Georgii (6.21)(iii). -/
lemma ne_of_half_lt {μ ν : Measure (Site → ℤ)} [IsProbabilityMeasure μ]
    {a : Site} {c d : ℤ} (hcd : c ≠ d)
    (hμ : 2⁻¹ < μ {ζ : Site → ℤ | ζ a = c}) (hν : 2⁻¹ < ν {ζ : Site → ℤ | ζ a = d}) :
    μ ≠ ν := by
  rintro rfl
  have hdisj : Disjoint {ζ : Site → ℤ | ζ a = c} {ζ : Site → ℤ | ζ a = d} := by
    rw [Set.disjoint_left]
    intro ζ h1 h2
    exact hcd (h1.symm.trans h2)
  have hmd : MeasurableSet {ζ : Site → ℤ | ζ a = d} :=
    measurableSet_apply_mem a {x : ℤ | x = d}
  have hle : μ {ζ : Site → ℤ | ζ a = c} + μ {ζ : Site → ℤ | ζ a = d} ≤ 1 := by
    rw [← measure_union hdisj hmd]
    exact prob_le_one
  have hgt : (1 : ℝ≥0∞) < μ {ζ : Site → ℤ | ζ a = c} + μ {ζ : Site → ℤ | ζ a = d} := by
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := (ENNReal.inv_two_add_inv_two).symm
      _ < _ := ENNReal.add_lt_add_of_lt_of_le (by finiteness) hμ hν.le
  exact absurd hle (not_le.2 hgt)

/-- **Georgii Theorem (6.21)(iii), the separation of the `μ_z^β`.** Distinct slopes give
distinct Gibbs measures. -/
theorem staircasePhase_ne (hβ : 0 < β) (hr : r' (β / 2) < 1) (hq : 2 * r' (β / 2) < 2⁻¹)
    {z w : ℤ} (hzw : z ≠ w) : staircasePhase hβ hr z ≠ staircasePhase hβ hr w := by
  intro h
  refine ne_of_half_lt (μ := (staircasePhase hβ hr z : Measure (Site → ℤ)))
    (ν := (staircasePhase hβ hr w : Measure (Site → ℤ))) (a := e0) (c := z) (d := w) hzw ?_ ?_ ?_
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq z e0
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq w e0
  · exact congrArg (fun m : ProbabilityMeasure (Site → ℤ) ↦ (m : Measure (Site → ℤ))) h

/-- **Georgii Theorem (6.21), the punchline**: at low temperature the discrete Gaussian model on
`ℤ²` has infinitely many Gibbs measures. -/
theorem infinite_GP_dgSpecification (hβ : 0 < β) (hr : r' (β / 2) < 1)
    (hq : 2 * r' (β / 2) < 2⁻¹) :
    (GP (S := Site) (E := ℤ) (dgSpecification hβ)).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun z : ℤ ↦ staircasePhase hβ hr z)
    (fun z w h ↦ ?_) (fun z ↦ staircasePhase_mem_GP hβ hr z)
  by_contra hzw
  exact staircasePhase_ne hβ hr hq hzw h

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp Filter Topology Transformation

variable {β : ℝ}

/-! ### Georgii Theorem (6.21): the broken symmetries -/

lemma map_toFun_spin_eq (τ : Transformation Site ℤ) (μ : Measure (Site → ℤ))
    (a : Site) (d : ℤ) :
    (μ.map τ.toFun) {ζ : Site → ℤ | ζ a = d} = μ {ω : Site → ℤ | τ.toFun ω a = d} :=
  Measure.map_apply τ.measurable_toFun (measurableSet_apply_mem a {x : ℤ | x = d})

variable (hβ : 0 < β) (hr : r' (β / 2) < 1) (hq : 2 * r' (β / 2) < 2⁻¹)
include hβ hr hq

/-- **Georgii Theorem (6.21): the spin translation `t` is broken.** `t(μ_z^β) ≠ μ_z^β` for every
`z`; equivalently `μ_z^β` and `t^n(μ_z^β)` are distinct Gibbs measures. -/
theorem map_spinTranslation_staircasePhase_ne (z : ℤ) :
    Measure.map (staircaseShift Site).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map (staircaseShift Site).toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map (staircaseShift Site).measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := (0 : Site)) (c := -1) (d := 0) (by omega) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | (staircaseShift Site).toFun ω (0 : Site) = -1}
        = {ζ : Site → ℤ | ζ (0 : Site) = staircase z (0 : Site)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, staircaseShift_toFun_apply, staircase_apply, Pi.zero_apply,
        mul_zero]
      omega
    rw [hset]
    exact half_lt_staircasePhase hβ hr hq z 0
  · have h0 : staircase z (0 : Site) = 0 := by simp [staircase]
    simpa [h0] using half_lt_staircasePhase hβ hr hq z 0

/-- **Georgii Theorem (6.21): the spin reflection `τ` is broken** for `z ≠ 0`. -/
theorem map_spinReflection_staircasePhase_ne {z : ℤ} (hz : z ≠ 0) :
    Measure.map (spinReflection Site).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map (spinReflection Site).toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map (spinReflection Site).measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := e0) (c := -z) (d := z) (by omega) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | (spinReflection Site).toFun ω e0 = -z}
        = {ζ : Site → ℤ | ζ e0 = staircase z e0} := by
      ext ω
      simp only [Set.mem_ofPred_eq, spinReflection_toFun, staircase_apply, e0_zero, mul_one]
      omega
    rw [hset]
    exact half_lt_staircasePhase hβ hr hq z e0
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq z e0

/-- **Georgii Theorem (6.21): the lattice translation `θ_j` is broken** whenever it moves the
staircase, i.e. whenever `z · j₁ ≠ 0`. -/
theorem map_shift_staircasePhase_ne {z : ℤ} {j : Site} (hzj : z * j 0 ≠ 0) :
    Measure.map (shift ℤ j).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map (shift ℤ j).toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map (shift ℤ j).measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := j) (c := 0) (d := z * j 0) (Ne.symm hzj) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | (shift ℤ j).toFun ω j = 0}
        = {ζ : Site → ℤ | ζ (0 : Site) = staircase z (0 : Site)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, shift_toFun_apply, sub_self, staircase_apply, Pi.zero_apply,
        mul_zero]
    rw [hset]
    exact half_lt_staircasePhase hβ hr hq z 0
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq z j

/-- **Georgii Theorem (6.21): the lattice rotation `r₀` is broken** for `z ≠ 0`. -/
theorem map_latticeRot_staircasePhase_ne {z : ℤ} (hz : z ≠ 0) :
    Measure.map latticeRot.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map latticeRot.toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map latticeRot.measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := e1) (c := z) (d := 0) hz ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | latticeRot.toFun ω e1 = z}
        = {ζ : Site → ℤ | ζ (mk 1 0) = staircase z (mk 1 0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, latticeRot_toFun, e1_zero, e1_one, neg_zero,
        staircase_apply, Peierls.mk_zero, mul_one]
    rw [hset]
    exact half_lt_staircasePhase hβ hr hq z (mk 1 0)
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq z e1

/-- **Georgii Theorem (6.21): the lattice reflection `r₁` is broken** for `z ≠ 0`. -/
theorem map_latticeReflFst_staircasePhase_ne {z : ℤ} (hz : z ≠ 0) :
    Measure.map latticeReflFst.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map latticeReflFst.toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map latticeReflFst.measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := e0) (c := -z) (d := z) (by omega) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | latticeReflFst.toFun ω e0 = -z}
        = {ζ : Site → ℤ | ζ (mk (-1) 0) = staircase z (mk (-1) 0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, latticeReflFst_toFun, e0_zero, e0_one,
        staircase_apply, Peierls.mk_zero]
      omega
    rw [hset]
    exact half_lt_staircasePhase hβ hr hq z (mk (-1) 0)
  · simpa [staircase] using half_lt_staircasePhase hβ hr hq z e0

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

/-! ### Georgii Theorem (6.21) at an explicit temperature threshold -/

/-- `log 12 ≤ β` forces `β > 0`. -/
lemma pos_of_log_twelve {β : ℝ} (hlog : Real.log 12 ≤ β) : 0 < β :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog

/-- **Georgii's requirement `r(β) < 1/2`**, in the sharpened form `2 r'(β/2) < 1/2`, holds as
soon as `β ≥ log 12 ≈ 2.4849`. -/
lemma two_mul_r'_half_lt {β : ℝ} (hlog : Real.log 12 ≤ β) : 2 * r' (β / 2) < 2⁻¹ := by
  have h : r' (β / 2) < 4⁻¹ := by
    refine r'_lt_quarter ?_
    rw [show 2 * (β / 2) = β from by ring]
    exact hlog
  calc (2 : ℝ≥0∞) * r' (β / 2) < 2 * 4⁻¹ := by
        rw [mul_comm (2 : ℝ≥0∞) (r' (β / 2)), mul_comm (2 : ℝ≥0∞) ((4 : ℝ≥0∞)⁻¹)]
        exact ENNReal.mul_lt_mul_left (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) h
    _ = 2⁻¹ := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 from by norm_num,
          ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The Peierls series converges at `β ≥ log 12`. -/
lemma r'_half_lt_one {β : ℝ} (hlog : Real.log 12 ≤ β) : r' (β / 2) < 1 := by
  have h : r' (β / 2) < 4⁻¹ := by
    refine r'_lt_quarter ?_
    rw [show 2 * (β / 2) = β from by ring]
    exact hlog
  exact lt_trans h (ENNReal.inv_lt_one.2 (by norm_num))

/-- **Georgii Theorem (6.21), the phase-transition conclusion at an explicit threshold.**
For `β ≥ log 12 ≈ 2.4849` the discrete Gaussian model (6.16) on `ℤ²` has infinitely many Gibbs
measures: the random staircases `μ_z^β`, `z ∈ ℤ`, are pairwise distinct. -/
theorem infinite_GP_dgSpecification_of_log_twelve {β : ℝ} (hlog : Real.log 12 ≤ β) :
    (GP (S := Site) (E := ℤ) (dgSpecification (pos_of_log_twelve hlog))).Infinite :=
  infinite_GP_dgSpecification (pos_of_log_twelve hlog) (r'_half_lt_one hlog)
    (two_mul_r'_half_lt hlog)

/-- **Georgii Theorem (6.21), packaged at the explicit threshold `β ≥ log 12`.**  For every
`z ∈ ℤ` the random staircase `μ_z^β` is a Gibbs measure for `βΦ` which

* is a random perturbation of the staircase `ω^z`: `μ_z^β(|σ_a - ω^z_a| ≥ k) ≤ 2 r'(β/2)^k`
  for every site `a` and every `k` (Lemma (6.25));
* satisfies `μ_z^β(σ_a = ω^z_a) > 1/2` at every site — Georgii (6.21)(i);
* is distinct from `μ_w^β` for `w ≠ z` — part of Georgii (6.21)(iii).

The symmetry breaking of (6.21) is `map_spinTranslation_staircasePhase_ne`,
`map_spinReflection_staircasePhase_ne`, `map_shift_staircasePhase_ne`,
`map_latticeRot_staircasePhase_ne` and `map_latticeReflFst_staircasePhase_ne`. -/
theorem staircasePhase_spec {β : ℝ} (hlog : Real.log 12 ≤ β) (z : ℤ) :
    staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z
        ∈ GP (S := Site) (E := ℤ) (dgSpecification (pos_of_log_twelve hlog)) ∧
      (∀ (a : Site) (k : ℕ),
        (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z :
            Measure (Site → ℤ)) {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|}
          ≤ 2 * r' (β / 2) ^ k) ∧
      (∀ a : Site, 2⁻¹ < (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z :
          Measure (Site → ℤ)) {ζ : Site → ℤ | ζ a = staircase z a}) ∧
      (∀ w : ℤ, w ≠ z → staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) w
        ≠ staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z) :=
  ⟨staircasePhase_mem_GP _ _ z,
    staircasePhase_absExcess_le _ _ z,
    half_lt_staircasePhase _ _ (two_mul_r'_half_lt hlog) z,
    fun _ hw ↦ staircasePhase_ne _ _ (two_mul_r'_half_lt hlog) hw⟩

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

variable {β : ℝ} (hβ : 0 < β) (hr : r' (β / 2) < 1)
include hβ hr

/-- **Georgii Theorem (6.21)(i), the low-temperature limit, in finite volume.**  On every finite
volume `Λ` the random staircase agrees with the staircase `ω^z` with probability at least
`1 - 2 |Λ| r'(β/2)`.  Since `r'(β/2) → 0` as `β → ∞`, this is Georgii's statement that
`μ_z^β → δ_{ω^z}`: the Gibbs measure is a random perturbation of the staircase which freezes
onto it at low temperature. -/
theorem staircasePhase_agree_ge (z : ℤ) (Λ : Finset Site) :
    1 - (Λ.card : ℝ≥0∞) * (2 * r' (β / 2))
      ≤ (staircasePhase hβ hr z : Measure (Site → ℤ))
          {ζ : Site → ℤ | ∀ i ∈ Λ, ζ i = staircase z i} := by
  classical
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  set A : Set (Site → ℤ) := {ζ : Site → ℤ | ∀ i ∈ Λ, ζ i = staircase z i} with hAdef
  have hmeas : MeasurableSet A := by
    have hiInter : A = ⋂ i ∈ Λ, {ζ : Site → ℤ | ζ i = staircase z i} := by
      ext ζ
      simp only [hAdef, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hiInter]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_apply_mem i {x : ℤ | x = staircase z i}
  have hcompl : μ Aᶜ ≤ (Λ.card : ℝ≥0∞) * (2 * r' (β / 2)) := by
    have hsub : Aᶜ ⊆ ⋃ i ∈ Λ, {ζ : Site → ℤ | (1 : ℤ) ≤ |ζ i - staircase z i|} := by
      intro ζ hζ
      have hζ' : ¬ ∀ i ∈ Λ, ζ i = staircase z i := hζ
      push Not at hζ'
      obtain ⟨i, hi, hne⟩ := hζ'
      refine Set.mem_biUnion hi ?_
      have h0 : ζ i - staircase z i ≠ 0 := sub_ne_zero.2 hne
      have hpos := abs_pos.2 h0
      show (1 : ℤ) ≤ |ζ i - staircase z i|
      omega
    calc μ Aᶜ ≤ μ (⋃ i ∈ Λ, {ζ : Site → ℤ | (1 : ℤ) ≤ |ζ i - staircase z i|}) :=
          measure_mono hsub
      _ ≤ ∑ i ∈ Λ, μ {ζ : Site → ℤ | (1 : ℤ) ≤ |ζ i - staircase z i|} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ Λ, 2 * r' (β / 2) := Finset.sum_le_sum fun i _ ↦ by
            simpa using staircasePhase_absExcess_le hβ hr z i 1
      _ = (Λ.card : ℝ≥0∞) * (2 * r' (β / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ A + μ Aᶜ := by rw [measure_add_measure_compl hmeas]; simp
    _ ≤ μ A + (Λ.card : ℝ≥0∞) * (2 * r' (β / 2)) := add_le_add le_rfl hcompl

end MeasureTheory.GibbsMeasure.Shlosman
