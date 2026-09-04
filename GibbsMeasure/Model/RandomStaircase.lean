/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PeierlsEstimate
public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Mathlib.Data.Set.CardTranslate
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ExpNegSq

/-!
# Georgii §6.3: Shlosman's random staircases

`S = ℤ²`, `E = ℤ`, `λ` counting measure, and the *discrete Gaussian* potential (6.16)

`Φ_A = (σ_i - σ_j)²` if `A = {i, j}` with `|i - j| = 1`, `Φ_A = 0` otherwise.

The contour machinery of §6.2 (`GibbsMeasure/Model/Contours.lean`,
`GibbsMeasure/Model/PeierlsEstimate.lean`) is reused verbatim: the sites, the lattice graph, the
"infinite outside" `outside D` of a finite `D ⊆ ℤ²`, the outer boundary and the fact that it is a
circuit. Only the *state space* and the *contour weight* change.
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
    (hc : ∀ i ∈ D, ∀ v ∈ dirs, i + v ∉ D →
      k ≤ ζ i - staircase z i ∧ ζ (i + v) - staircase z (i + v) < k) :
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
      obtain ⟨hA, hB⟩ := hc q.1 h1 q.2 h2 h3
      have hC : staircase z q.1 - staircase z (q.1 + q.2) = -(z * q.2 0) :=
        staircase_sub_add z q.1 q.2
      omega
    have := (Int.cast_le (R := ℝ)).2 hz
    push_cast at this ⊢
    linarith
  have hsum : ((bdIdx D).card : ℝ) ≤ ∑ q ∈ bdIdx D, (2 * ((ζ q.1 - ζ (q.1 + q.2) : ℤ) : ℝ) - 1) := by
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
