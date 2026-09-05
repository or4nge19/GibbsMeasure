/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SharpContours
public import GibbsMeasure.Model.SharpPhaseTransition
public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Potential.GroundState
public import GibbsMeasure.Potential.NearestNeighbour
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Count
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

* `Shlosman.staircaseAverage` — Georgii's shift averages
  `ν_{N,z} = |Λ_N|^{-1} ∑_{i ∈ Λ_N} γ_{Λ_N + i}(· | ω^z)`;
  `Shlosman.glide`, `Shlosman.reflFstSpin`, `Shlosman.staircaseSymmetries` — the `Φ`-symmetries
  preserving `ω^z`; `Shlosman.measurePreserving_staircasePhase`,
  `Shlosman.map_spinReflection_staircasePhase`, `Shlosman.map_latticeReflFst_staircasePhase`,
  `Shlosman.integral_spin_staircasePhase` — **Theorem (6.21)(ii)** and the mean statement of
  (6.21)(i).

`μ_z^β` is constructed as the limit of `ν_{N,z}` along one fixed ultrafilter
(`Shlosman.staircaseUltrafilter`), the same for every `z`: this is Georgii's equivariant choice of
cluster point, and it is what makes `τ(μ_z^β) = μ_{-z}^β`.

## Not formalised here

* The `ℓ¹` linear independence of (6.21)(iii), which needs signed measures.  What is proved
  instead of (iii) is the pairwise separation `staircasePhase_ne` (and the `map_*_ne` lemmas),
  which already gives `|𝒢(βΦ)| = ∞` and the symmetry breaking Georgii emphasises.
* The low-temperature limit `μ_z^β → δ_{ω^z}` of (6.21)(i): only the finite-volume bound
  `staircasePhase_agree_ge` is proved, at fixed `β`.
* `r₀(μ_0^β) = μ_0^β` of (6.21)(ii).
* Lemma (6.25) is proved for the squares `Λ_N` of `Λ_N + i`, not for Georgii's arbitrary
  rectangles (6.10); that is all Theorem (6.21) uses.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Finset
open scoped ENNReal

noncomputable section

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
  refine nearestNeighbourSym_apply_of_not (fun h ↦ hA ?_) ζ
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
  exact nearestNeighbourSym_apply_of ⟨Finset.card_pair hab.ne, a, by simp, b, by simp, hab⟩ ζ

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

open MeasureTheory.GibbsMeasure Transformation

/-- **Georgii (6.17)(i).** The gradient potential of the lattice `ℤ^d` is shift-invariant
(Georgii (5.2)(1)). -/
theorem isShiftInvariant_nearestNeighbourDiff {d : ℕ} (g : ℤ → ℝ) :
    (nearestNeighbourDiff (latticeGraph d) g).IsShiftInvariant := by
  intro j
  refine map_nearestNeighbourSym_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) (fun a b ↦ ?_)
    (fun x y ↦ rfl)
  have : (shift ℤ j).sites = Equiv.addRight j := rfl
  rw [this]
  change (latticeGraph d).Adj (a + j) (b + j) ↔ (latticeGraph d).Adj a b
  rw [← latticeGraph_adj_sub_iff j (a := a + j) (b := b + j)]
  simp

variable {S : Type*} {G : SimpleGraph S} {g : ℤ → ℝ}

/-- **Georgii (6.17)(iv).** `τ(Φ) = Φ` for the spin reflection
`MeasureTheory.GibbsMeasure.spinReflection`, when `g` is even. -/
theorem map_spinReflection_nearestNeighbourDiff (heven : ∀ x : ℤ, g (-x) = g x) :
    Potential.map (spinReflection S ℤ) (nearestNeighbourDiff G g) = nearestNeighbourDiff G g := by
  refine map_nearestNeighbourSym_eq (f := MeasurableEquiv.neg ℤ) (fun _ ↦ rfl) (fun a b ↦ Iff.rfl)
    fun x y ↦ ?_
  show g (-x - -y) = g (x - y)
  rw [show -x - -y = -(x - y) by ring, heven]

/-- **Georgii (6.17)(v).** `t(Φ) = Φ` for the spin translation. -/
theorem map_spinTranslation_nearestNeighbourDiff :
    Potential.map (staircaseShift S ℤ) (nearestNeighbourDiff G g) = nearestNeighbourDiff G g := by
  refine map_nearestNeighbourSym_eq (f := MeasurableEquiv.addRight (-1 : ℤ)) (fun _ ↦ rfl)
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

/-! ### Georgii (6.21)(ii): the symmetries of the staircase `ω^z`

The subgroup of `Φ`-symmetries generated by `θ_{(0,1)}` and `t^{-z} ∘ θ_{(1,0)}` consists of the
*glides* `g^z_i = t^{-z i₁} ∘ θ_i`, the composites of a lattice translation with the spin
translation that repairs the height of the staircase; and `ω^z` is also fixed by `r₁ ∘ τ` and by
`r₂`. -/

/-- **Georgii (6.21)(ii).** The *staircase glide* `g^z_i = t^{-z i₁} ∘ θ_i`, acting by
`(g^z_i ζ)_m = ζ_{m - i} + z i₁`.  Its spatial part is the translation by `i` and its spin part
the translation of `ℤ` by `z i₁`.  Georgii's two generators are `g^z_{(0,1)} = θ_{(0,1)}` and
`g^z_{(1,0)} = t^{-z} ∘ θ_{(1,0)}`, and `g^z_i` is exactly the composite of translations that
fixes the staircase `ω^z` (`glide_toFun_staircase`). -/
def glide (z : ℤ) (i : Site) : Transformation Site ℤ where
  sites := Equiv.addRight i
  spin _ := MeasurableEquiv.addRight (z * i 0)

@[simp] lemma glide_sites (z : ℤ) (i : Site) : (glide z i).sites = Equiv.addRight i := rfl

@[simp] lemma glide_spin (z : ℤ) (i m : Site) :
    (glide z i).spin m = MeasurableEquiv.addRight (z * i 0) := rfl

@[simp] lemma glide_toFun_apply (z : ℤ) (i : Site) (ω : Site → ℤ) (m : Site) :
    (glide z i).toFun ω m = ω (m - i) + z * i 0 := by
  simp [glide, Transformation.toFun, sub_eq_add_neg]

@[simp] lemma glide_inv_toFun_apply (z : ℤ) (i : Site) (ω : Site → ℤ) (m : Site) :
    (glide z i).inv.toFun ω m = ω (m + i) - z * i 0 := by
  simp [glide, Transformation.inv, Transformation.toFun, sub_eq_add_neg]

/-- `g^z_{(0,1)}` is the lattice translation `θ_{(0,1)}`: its spin part is trivial. -/
lemma glide_e1 (z : ℤ) : glide z e1 = shift ℤ e1 := by
  refine Transformation.ext rfl (funext fun _ ↦ MeasurableEquiv.ext (funext fun x ↦ ?_))
  simp [glide, shift]

/-- `g^z_{(1,0)} = t^{-z} ∘ θ_{(1,0)}` is Georgii's second generator: the spin translation by `z`
composed with the lattice translation `θ_{(1,0)}`. -/
lemma glide_e0 (z : ℤ) :
    glide z e0 = spinTranslation (fun _ : Site ↦ z) * shift ℤ e0 := by
  refine Transformation.ext (Equiv.ext fun _ ↦ rfl)
    (funext fun _ ↦ MeasurableEquiv.ext (funext fun x ↦ ?_))
  simp [glide, spinTranslation, shift, Transformation.comp]

/-- **The glides fix the staircase `ω^z`** (Georgii (6.21)(ii): the listed symmetries "preserve
`ω^z`"): `g^z_i ω^z = ω^z`, because `ω^z_{m - i} + z i₁ = z(m₁ - i₁) + z i₁ = ω^z_m`. -/
@[simp] lemma glide_toFun_staircase (z : ℤ) (i : Site) :
    (glide z i).toFun (staircase z) = staircase z := by
  funext m
  simp only [glide_toFun_apply, staircase_apply, Pi.sub_apply]
  ring

@[simp] lemma glide_inv_toFun_staircase (z : ℤ) (i : Site) :
    (glide z i).inv.toFun (staircase z) = staircase z := by
  funext m
  simp only [glide_inv_toFun_apply, staircase_apply, Pi.add_apply]
  ring

/-- **Georgii (6.17)(i)+(v) for the glide.** `g^z_i` preserves the gradient potential on `ℤ²`:
its spatial part is a lattice translation and its (constant) spin part cancels in differences. -/
theorem map_glide_nearestNeighbourDiff (z : ℤ) (i : Site) (g : ℤ → ℝ) :
    Potential.map (glide z i) (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g := by
  refine map_nearestNeighbourSym_eq (f := MeasurableEquiv.addRight (z * i 0)) (fun _ ↦ rfl)
    (fun a b ↦ ?_) (fun x y ↦ ?_)
  · show (latticeGraph 2).Adj (a + i) (b + i) ↔ (latticeGraph 2).Adj a b
    rw [← latticeGraph_adj_sub_iff i (a := a + i) (b := b + i)]
    simp
  · have hsymm : ∀ w : ℤ, (MeasurableEquiv.addRight (z * i 0)).symm w = w - z * i 0 :=
      fun w ↦ by simp [MeasurableEquiv.addRight, sub_eq_add_neg]
    rw [hsymm, hsymm, sub_sub_sub_cancel_right]

/-- **Georgii (6.21)(ii): `r₁ ∘ τ`,** the lattice reflection in the second axis composed with the
spin reflection, `(r₁ τ ω)_i = -ω_{(-i₁, i₂)}`.  It fixes the staircase `ω^z`. -/
def reflFstSpin : Transformation Site ℤ where
  sites := reflectFst
  spin _ := MeasurableEquiv.neg ℤ

@[simp] lemma reflFstSpin_sites : reflFstSpin.sites = reflectFst := rfl

@[simp] lemma reflFstSpin_toFun (ω : Site → ℤ) (i : Site) :
    reflFstSpin.toFun ω i = -ω (mk (-(i 0)) (i 1)) := by
  simp [reflFstSpin, Transformation.toFun, reflectFst, Function.Involutive.toPerm]

@[simp] lemma reflFstSpin_toFun_staircase (z : ℤ) :
    reflFstSpin.toFun (staircase z) = staircase z := by
  funext m
  simp only [reflFstSpin_toFun, staircase_apply, Peierls.mk_zero]
  ring

@[simp] lemma latticeReflSnd_toFun_staircase (z : ℤ) :
    latticeReflSnd.toFun (staircase z) = staircase z := by
  funext m
  simp [latticeReflSnd, Transformation.toFun, reflectSnd, Function.Involutive.toPerm, staircase]

/-- **Georgii Remark (6.17)(ii)+(iv).** `r₁ ∘ τ` preserves the gradient potential of an even `g`
on `ℤ²`. -/
theorem map_reflFstSpin_nearestNeighbourDiff {g : ℤ → ℝ} (heven : ∀ x : ℤ, g (-x) = g x) :
    Potential.map reflFstSpin (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g := by
  refine map_nearestNeighbourSym_eq (f := MeasurableEquiv.neg ℤ) (fun _ ↦ rfl) adj_reflectFst
    fun x y ↦ ?_
  show g (-x - -y) = g (x - y)
  rw [show -x - -y = -(x - y) by ring, heven]

@[simp] lemma reflectFst_symm_apply (x : Site) : reflectFst.symm x = mk (-(x 0)) (x 1) := rfl

@[simp] lemma reflectSnd_symm_apply (x : Site) : reflectSnd.symm x = mk (x 0) (-(x 1)) := rfl

/-- The lattice reflection `r₁` is additive. -/
lemma reflectFst_add (x y : Site) : reflectFst (x + y) = reflectFst x + reflectFst y := by
  rw [site_ext_iff]; simp; ring

/-- The lattice reflection `r₂` is additive. -/
lemma reflectSnd_add (x y : Site) : reflectSnd (x + y) = reflectSnd x + reflectSnd y := by
  rw [site_ext_iff]; simp; ring

/-- The cubes `Λ_n = ℤ² ∩ [-n, n]²` are invariant under `r₁`. -/
lemma map_cube_reflectFst (n : ℕ) : (cube 2 n).map reflectFst.toEmbedding = cube 2 n := by
  ext x
  rw [Finset.mem_map_equiv, mem_cube, mem_cube]
  refine forall_congr' fun k ↦ ?_
  fin_cases k <;> simp

/-- The cubes `Λ_n = ℤ² ∩ [-n, n]²` are invariant under `r₂`. -/
lemma map_cube_reflectSnd (n : ℕ) : (cube 2 n).map reflectSnd.toEmbedding = cube 2 n := by
  ext x
  rw [Finset.mem_map_equiv, mem_cube, mem_cube]
  refine forall_congr' fun k ↦ ?_
  fin_cases k <;> simp

/-- **Georgii Remark (6.17)(ii).** `r₁` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeReflFst_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeReflFst (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourSym_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_reflectFst
    (fun _ _ ↦ rfl)

/-- **Georgii Remark (6.17)(ii).** `r₂` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeReflSnd_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeReflSnd (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourSym_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_reflectSnd
    (fun _ _ ↦ rfl)

/-- **Georgii Remark (6.17)(iii).** `r₀` preserves the gradient potential on `ℤ²`. -/
theorem map_latticeRot_nearestNeighbourDiff (g : ℤ → ℝ) :
    Potential.map latticeRot (nearestNeighbourDiff (latticeGraph 2) g)
      = nearestNeighbourDiff (latticeGraph 2) g :=
  map_nearestNeighbourSym_eq (f := MeasurableEquiv.refl ℤ) (fun _ ↦ rfl) adj_rotateSite
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
      Potential.map (spinReflection Site ℤ) dgPotential = dgPotential ∧
      Potential.map (staircaseShift Site ℤ) dgPotential = dgPotential :=
  ⟨isShiftInvariant_nearestNeighbourDiff (fun x ↦ (x : ℝ) ^ 2),
    map_latticeReflFst_nearestNeighbourDiff (fun x ↦ (x : ℝ) ^ 2),
    map_latticeReflSnd_nearestNeighbourDiff (fun x ↦ (x : ℝ) ^ 2),
    map_latticeRot_nearestNeighbourDiff (fun x ↦ (x : ℝ) ^ 2),
    map_spinReflection_nearestNeighbourDiff (g := fun x ↦ (x : ℝ) ^ 2) (fun x ↦ by push_cast; ring),
    map_spinTranslation_nearestNeighbourDiff (g := fun x ↦ (x : ℝ) ^ 2)⟩

end MeasureTheory.GibbsMeasure.Shlosman

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
    Specification.IsInvariant (spinReflection Site ℤ) (dgSpecification hβ) :=
  Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential β
    (spinReflection Site ℤ) Measure.count
    (fun _ ↦ (MeasurableEquiv.neg ℤ).measurePreserving_count)
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    (map_spinReflection_nearestNeighbourDiff (g := fun x ↦ (x : ℝ) ^ 2) fun x ↦ by push_cast; ring)

/-- **Georgii (6.21)(ii) at the specification level.** Every staircase glide `g^z_i` leaves
`γ^{βΦ}` invariant: it preserves `Φ` (`map_glide_nearestNeighbourDiff`) and its spin part, a
translation of `ℤ`, preserves counting measure. -/
theorem isInvariant_glide_dgSpecification (hβ : 0 < β) (z : ℤ) (i : Site) :
    Specification.IsInvariant (glide z i) (dgSpecification hβ) :=
  Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential β
    (glide z i) Measure.count
    (fun _ ↦ (MeasurableEquiv.addRight (z * i 0)).measurePreserving_count)
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    (map_glide_nearestNeighbourDiff z i (fun x ↦ (x : ℝ) ^ 2))

/-- **Georgii (6.21)(ii) at the specification level.** `r₁ ∘ τ` leaves `γ^{βΦ}` invariant. -/
theorem isInvariant_reflFstSpin_dgSpecification (hβ : 0 < β) :
    Specification.IsInvariant reflFstSpin (dgSpecification hβ) :=
  Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential β
    reflFstSpin Measure.count
    (fun _ ↦ (MeasurableEquiv.neg ℤ).measurePreserving_count)
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    (map_reflFstSpin_nearestNeighbourDiff (g := fun x ↦ (x : ℝ) ^ 2) fun x ↦ by push_cast; ring)

/-- **Georgii (6.21)(ii) at the specification level.** `r₂` leaves `γ^{βΦ}` invariant. -/
theorem isInvariant_latticeReflSnd_dgSpecification (hβ : 0 < β) :
    Specification.IsInvariant latticeReflSnd (dgSpecification hβ) :=
  Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible dgPotential β
    latticeReflSnd Measure.count
    (fun _ ↦ (MeasurableEquiv.refl ℤ).measurePreserving_count)
    (isSigmaFiniteLambdaAdmissible_dgPotential hβ)
    (map_latticeReflSnd_nearestNeighbourDiff (fun x ↦ (x : ℝ) ^ 2))

/-- **Georgii's `τ`-step in the proof of (6.25)**: reflecting the spins turns a deficit below the
staircase `ω^z` into an excess above the staircase `ω^{-z}`. -/
theorem dgSpecification_deficit_eq (hβ : 0 < β) (z k : ℤ) (Λ : Finset Site) (a : Site) :
    dgSpecification hβ Λ (staircase z) {ζ : Site → ℤ | ζ a - staircase z a ≤ -k}
      = dgSpecification hβ Λ (staircase (-z)) {ζ : Site → ℤ | k ≤ ζ a - staircase (-z) a} := by
  have hA : MeasurableSet {ζ : Site → ℤ | ζ a - staircase z a ≤ -k} :=
    measurableSet_apply_mem a {x : ℤ | x - staircase z a ≤ -k}
  have hinv : (dgSpecification hβ).map (spinReflection Site ℤ) = dgSpecification hβ :=
    isInvariant_spinReflection_dgSpecification hβ
  have hΛ : Λ.map (spinReflection Site ℤ).sites.symm.toEmbedding = Λ := by
    simp [spinReflection, pureSpin]
  have hη : (spinReflection Site ℤ).inv.toFun (staircase z) = staircase (-z) := by
    funext i
    simp [staircase]
  have hset : (spinReflection Site ℤ).toFun ⁻¹' {ζ : Site → ℤ | ζ a - staircase z a ≤ -k}
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
`r(β) = 1 ∧ 2 ∑_{ℓ≥1} ℓ (3e^{-β})^ℓ = 1 ∧ 6 r'(β/2)`, whose truncation at `1` makes it vacuous
for small `β`.  Against Georgii's own iterate `2 (r(β)/2)^k = 2 (3 r'(β/2))^k` the bound proved
here is sharper by `3^k`, the factor his `r(β)` loses by using `ℓ 3^ℓ` where his Lemma (6.13)
gives `ℓ 3^{ℓ-1}`.  Against the *stated* `r(β)^k` it is sharper whenever `2 r'(β/2)^k ≤ 1` — in
particular throughout the regime `r(β) < 1` in which (6.25) has content, by a factor `6^k/2` —
but not below `β ≈ 1.894`, where `2 r'(β/2) > 1 = r(β)`.  The two halves are Georgii's: an
excess is controlled by
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

/-- **Georgii Lemma (6.25) in a translated box.** The glide `g^z_i` carries the box `Λ_N` onto
`Λ_N + i` and fixes the staircase `ω^z`, so (6.25) holds verbatim in every translate of `Λ_N`,
the site `a` being carried back to `a - i`:

`γ_{Λ_N + i}^{βΦ}(|σ_a - ω^z_a| ≥ k | ω^z) ≤ 2 r'(β/2)^k`.

This is what makes Georgii's shift-averaged sequence `ν_{N,z}` obey the same estimate as the
single box. -/
theorem dgSpecification_abs_excess_translate_le (hβ : 0 < β) (z : ℤ) (N : ℕ) (i a : Site)
    (k : ℕ) :
    dgSpecification hβ ((cube 2 N).map (Equiv.addRight i).toEmbedding) (staircase z)
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k := by
  have hA : MeasurableSet {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} :=
    measurableSet_apply_mem a {x : ℤ | (k : ℤ) ≤ |x - staircase z a|}
  have hinv : (dgSpecification hβ).map (glide z i) = dgSpecification hβ :=
    isInvariant_glide_dgSpecification hβ z i
  have hΛ : ((cube 2 N).map (Equiv.addRight i).toEmbedding).map
      (glide z i).sites.symm.toEmbedding = cube 2 N := by
    rw [glide_sites, Finset.map_map]
    convert Finset.map_refl (s := cube 2 N) using 2
    exact Function.Embedding.ext fun x ↦ by simp
  have hset : (glide z i).toFun ⁻¹' {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|}
      = {ζ : Site → ℤ | (k : ℤ) ≤ |ζ (a - i) - staircase z (a - i)|} := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, glide_toFun_apply, staircase_apply,
      Pi.sub_apply]
    ring_nf
  conv_lhs => rw [← hinv]
  rw [Specification.map_apply' _ _ _ _ hA, hΛ, glide_inv_toFun_staircase, hset]
  exact dgSpecification_abs_excess_le hβ z N (a - i) k

/-! ### Georgii's shift-averaged finite-volume distributions -/

/-- **Georgii's `ν_{N,z}`** in the proof of Theorem (6.21): the average of the finite-volume Gibbs
distributions with staircase boundary condition over the translates of the box `Λ_N`,

`ν_{N,z} = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ_{Λ_N + i}^{βΦ}(· | ω^z)`.

Georgii averages in order to obtain the invariance statement (6.21)(ii) from Example
(5.20)(1). -/
def staircaseAverage (hβ : 0 < β) (z : ℤ) (N : ℕ) : ProbabilityMeasure (Site → ℤ) :=
  ⟨(dgSpecification hβ).average (Measure.dirac (staircase z)) (cubeTranslates 2 N N),
    Specification.isProbabilityMeasure_average _ _ (cubeTranslates_nonempty 2 N N)⟩

@[simp] lemma coe_staircaseAverage (hβ : 0 < β) (z : ℤ) (N : ℕ) :
    (staircaseAverage hβ z N : Measure (Site → ℤ))
      = (dgSpecification hβ).average (Measure.dirac (staircase z)) (cubeTranslates 2 N N) := rfl

/-- **Georgii Lemma (6.25) for the shift averages**: `ν_{N,z}(|σ_a - ω^z_a| ≥ k) ≤ 2 r'(β/2)^k`
for *every* site `a` and every `N`, since each term of the average obeys the estimate
(`dgSpecification_abs_excess_translate_le`). -/
theorem staircaseAverage_absExcess_le (hβ : 0 < β) (z : ℤ) (N : ℕ) (a : Site) (k : ℕ) :
    (staircaseAverage hβ z N : Measure (Site → ℤ))
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k := by
  classical
  set R : Finset (Finset Site) := cubeTranslates 2 N N with hR
  set c : ℝ≥0∞ := 2 * r' (β / 2) ^ k with hc
  set A : Set (Site → ℤ) := {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} with hA
  have hne : R.Nonempty := cubeTranslates_nonempty 2 N N
  have hterm : ∀ Λ ∈ R, (Measure.dirac (staircase z)).bind (dgSpecification hβ Λ) A ≤ c := by
    intro Λ hΛ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hΛ
    rw [Measure.dirac_bind ((dgSpecification hβ).measurable_kernel_toMeasure _) (staircase z)]
    exact dgSpecification_abs_excess_translate_le hβ z N i a k
  rw [coe_staircaseAverage, Specification.average_apply]
  calc (R.card : ℝ≥0∞)⁻¹ * ∑ Λ ∈ R, (Measure.dirac (staircase z)).bind (dgSpecification hβ Λ) A
      ≤ (R.card : ℝ≥0∞)⁻¹ * ∑ _Λ ∈ R, c :=
        mul_le_mul' le_rfl (Finset.sum_le_sum hterm)
    _ = (R.card : ℝ≥0∞)⁻¹ * ((R.card : ℝ≥0∞) * c) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = c := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hne.card_pos.ne') (by simp),
          one_mul]

end MeasureTheory.GibbsMeasure.Shlosman

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

/-- **Uniform tightness around a staircase gives local equicontinuity.**  A family of random
fields obeying the estimate of Lemma (6.25) around `ω^z` satisfies Georgii's
`lim_{k→∞} sup_N ν_N(|σ_a| ≥ k) = 0`, and is therefore locally equicontinuous by Corollary
(4.13) (`locallyEquicontinuous_of_uniformlyTight`). -/
theorem locallyEquicontinuous_of_absExcess_le (hr : r' (β / 2) < 1) (z : ℤ)
    {μs : ℕ → ProbabilityMeasure (Site → ℤ)}
    (h : ∀ (N : ℕ) (a : Site) (k : ℕ), (μs N : Measure (Site → ℤ))
      {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k) :
    LocallyEquicontinuous atTop μs := by
  classical
  have hpow : Tendsto (fun k : ℕ ↦ 2 * r' (β / 2) ^ k) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by simp))
  refine locallyEquicontinuous_of_uniformlyTight fun a ε hε ↦ ?_
  obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop_zero.1 hpow) ε hε
  refine ⟨Finset.Icc (staircase z a - (k : ℤ) + 1) (staircase z a + (k : ℤ) - 1), fun N ↦ ?_⟩
  refine le_trans (measure_mono ?_) (le_trans (h N a k) (hk k le_rfl))
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

/-- **Uniform tightness of the finite-volume distributions with staircase boundary condition**:
the input to Corollary (4.13) for the single boxes `Λ_N`. -/
theorem locallyEquicontinuous_dg_cube (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    LocallyEquicontinuous atTop
      (fun N : ℕ ↦ finiteVolumeDistributions (dgSpecification hβ) (staircase z) (cube 2 N)) :=
  locallyEquicontinuous_of_absExcess_le hr z fun N a k ↦
    dgSpecification_abs_excess_le hβ z N a k

/-- **Uniform tightness of Georgii's shift averages `ν_{N,z}`**: the input to Corollary (4.13) in
the proof of Theorem (6.21). -/
theorem locallyEquicontinuous_staircaseAverage (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    LocallyEquicontinuous atTop (staircaseAverage hβ z) :=
  locallyEquicontinuous_of_absExcess_le hr z (staircaseAverage_absExcess_le hβ z)

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp Filter Topology Transformation

variable {β : ℝ}

/-! ### Georgii Theorem (6.21): the family `(μ_z^β)_{z ∈ ℤ}`

Georgii extracts `μ_z^β` as a cluster point of `ν_{N,z}`.  The cluster point is chosen *along one
fixed ultrafilter*, the same for every `z`: this is Georgii's equivariant choice, and it is what
makes `τ(μ_z^β) = μ_{-z}^β` in (6.21)(ii) — a symmetry carrying the sequence `(ν_{N,z})_N` to
`(ν_{N,-z})_N` carries the limit along that ultrafilter to the limit along that ultrafilter. -/

/-- The ultrafilter along which every random staircase is extracted.  Any ultrafilter refining
`atTop` would do; fixing one makes the family `(μ_z^β)_{z ∈ ℤ}` equivariant under the symmetries
of `Φ` that permute the staircases. -/
def staircaseUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

lemma staircaseUltrafilter_le : ↑staircaseUltrafilter ≤ (atTop : Filter ℕ) :=
  Ultrafilter.of_le atTop

/-- **Georgii Theorem (6.21), the construction.** The shift averages `ν_{N,z}` converge along
`staircaseUltrafilter` in the topology of local convergence, by Corollary (4.13) and Proposition
(4.9). -/
theorem exists_tendsto_staircaseAverage (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    ∃ μ : WithLocalConvergence Site ℤ,
      Tendsto (fun N : ℕ ↦ (WithSetwiseTopology.ofMeasure (staircaseAverage hβ z N) :
        WithLocalConvergence Site ℤ)) staircaseUltrafilter (𝓝 μ) :=
  exists_tendsto_of_locallyEquicontinuous staircaseUltrafilter staircaseUltrafilter_le
    (locallyEquicontinuous_staircaseAverage hβ hr z)

/-- **Georgii Theorem (6.21): the random staircase `μ_z^β`**, the limit along
`staircaseUltrafilter` of Georgii's shift averages
`ν_{N,z} = |Λ_N|⁻¹ ∑_{i ∈ Λ_N} γ_{Λ_N + i}^{βΦ}(· | ω^z)`. -/
noncomputable def staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    ProbabilityMeasure (Site → ℤ) :=
  (exists_tendsto_staircaseAverage hβ hr z).choose.toMeasure

/-- `μ_z^β` is the limit of the shift averages along `staircaseUltrafilter`. -/
theorem tendsto_staircaseAverage (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    Tendsto (fun N : ℕ ↦ (WithSetwiseTopology.ofMeasure (staircaseAverage hβ z N) :
        WithLocalConvergence Site ℤ)) staircaseUltrafilter
      (𝓝 (WithSetwiseTopology.ofMeasure (staircasePhase hβ hr z))) :=
  (exists_tendsto_staircaseAverage hβ hr z).choose_spec

/-- `μ_z^β` is a cluster point of the shift averages, as in Georgii's proof of (6.21). -/
theorem mapClusterPt_staircaseAverage (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    MapClusterPt (WithSetwiseTopology.ofMeasure (staircasePhase hβ hr z) :
        WithLocalConvergence Site ℤ) atTop
      fun N : ℕ ↦ WithSetwiseTopology.ofMeasure (staircaseAverage hβ z N) :=
  mapClusterPt_iff_ultrafilter.2
    ⟨staircaseUltrafilter, staircaseUltrafilter_le, tendsto_staircaseAverage hβ hr z⟩

/-- The evaluation of `μ_z^β` at a local event is the limit along `staircaseUltrafilter` of the
evaluations of the shift averages. -/
theorem tendsto_staircaseAverage_apply (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ)
    {A : Set (Site → ℤ)} (hA : A ∈ localEvents Site ℤ) :
    Tendsto (fun N : ℕ ↦ (staircaseAverage hβ z N : Measure (Site → ℤ)) A)
      staircaseUltrafilter (𝓝 ((staircasePhase hβ hr z : Measure (Site → ℤ)) A)) :=
  tendsto_withLocalConvergence_iff.1 (tendsto_staircaseAverage hβ hr z) A hA

/-- **Georgii Theorem (6.21): `μ_z^β ∈ 𝒢(βΦ)`.**  Comment (4.18) applied to the shift averages,
which are fixed by `γ_{Λ}` for every `Λ ⊆ ⋂_{i ∈ Λ_{k}} (Λ_N + i)` (Example (5.20)(1)). -/
theorem staircasePhase_mem_GP (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    staircasePhase hβ hr z ∈ GP (S := Site) (E := ℤ) (dgSpecification hβ) :=
  mem_GP_of_mapClusterPt_average_cubeTranslates (isQuasilocal_dgSpecification hβ)
    (fun _ ↦ rfl) (mapClusterPt_staircaseAverage hβ hr z)

/-- **Georgii (6.21)(i), the estimate**: `μ_z^β(|σ_a - ω^z_a| ≥ k) ≤ 2 r'(β/2)^k`. -/
theorem staircasePhase_absExcess_le (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) (a : Site)
    (k : ℕ) :
    (staircasePhase hβ hr z : Measure (Site → ℤ))
        {ζ : Site → ℤ | (k : ℤ) ≤ |ζ a - staircase z a|} ≤ 2 * r' (β / 2) ^ k :=
  eval_le_of_mapClusterPt (absExcess_mem_localEvents z a k)
    (mapClusterPt_staircaseAverage hβ hr z)
    (.of_forall fun N ↦ staircaseAverage_absExcess_le hβ z N a k)

/-! ### Georgii Theorem (6.21)(ii): the symmetries of `μ_z^β` -/

/-- A transformation fixing the configuration `η` preserves the Dirac measure at `η`; this is the
`τ`-invariance of Georgii's boundary condition `ω^z` in Example (5.20)(1). -/
lemma measurePreserving_dirac_of_toFun_eq {τ : Transformation Site ℤ} {η : Site → ℤ}
    (h : τ.toFun η = η) :
    MeasurePreserving τ.toFun (Measure.dirac η) (Measure.dirac η) :=
  ⟨τ.measurable_toFun, by rw [Measure.map_dirac' τ.measurable_toFun, h]⟩

/-- **Georgii (6.21)(ii): the symmetries of `ω^z`.**  The glides `g^z_i`, the composite `r₁ ∘ τ`
and the reflection `r₂` are exactly the `Φ`-symmetries Georgii lists as preserving `ω^z`.  For
each of them the averaging family `R_N = {Λ_N + i : i ∈ Λ_N}` is Følner: for a glide because its
spatial part is a translation, for `r₁ ∘ τ` and `r₂` because their spatial parts fix `R_N`. -/
def staircaseSymmetries (z : ℤ) : Set (Transformation Site ℤ) :=
  Set.range (glide z) ∪ {reflFstSpin, latticeReflSnd}

lemma glide_mem_staircaseSymmetries (z : ℤ) (i : Site) : glide z i ∈ staircaseSymmetries z :=
  Or.inl ⟨i, rfl⟩

lemma reflFstSpin_mem_staircaseSymmetries (z : ℤ) : reflFstSpin ∈ staircaseSymmetries z :=
  Or.inr (by simp)

lemma latticeReflSnd_mem_staircaseSymmetries (z : ℤ) :
    latticeReflSnd ∈ staircaseSymmetries z :=
  Or.inr (by simp)

/-- **Georgii Theorem (6.21)(ii), the invariance half.**  Every symmetry of `ω^z` in
`staircaseSymmetries z` — and hence every element of the group it generates, which contains
Georgii's generators `θ_{(0,1)} = g^z_{(0,1)}` and `t^{-z} ∘ θ_{(1,0)} = g^z_{(1,0)}` — preserves
the random staircase `μ_z^β`.  This is Example (5.20)(1) applied to the shift averages
`ν_{N,z}`. -/
theorem measurePreserving_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ)
    {τ : Transformation Site ℤ} (hτ : τ ∈ Subgroup.closure (staircaseSymmetries z)) :
    MeasurePreserving τ.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      (staircasePhase hβ hr z) := by
  refine (mem_GP_and_measurePreserving_of_mapClusterPt_average_cubeTranslates
    (isQuasilocal_dgSpecification hβ) (I := staircaseSymmetries z) ?_ ?_ ?_ (fun _ ↦ rfl)
    (mapClusterPt_staircaseAverage hβ hr z)).2 τ hτ
  · rintro σ (⟨i, rfl⟩ | hσ)
    · exact tendsto_card_symmDiff_map_cubeTranslates_div_of_sites_eq_addRight (glide_sites z i)
    · rcases hσ with rfl | rfl
      · exact tendsto_card_symmDiff_map_cubeTranslates_div_of_map_eq fun N ↦
          map_cubeTranslates_of_additive reflectFst_add map_cube_reflectFst N N
      · exact tendsto_card_symmDiff_map_cubeTranslates_div_of_map_eq fun N ↦
          map_cubeTranslates_of_additive reflectSnd_add map_cube_reflectSnd N N
  · rintro σ (⟨i, rfl⟩ | hσ)
    · exact isInvariant_glide_dgSpecification hβ z i
    · rcases hσ with rfl | rfl
      · exact isInvariant_reflFstSpin_dgSpecification hβ
      · exact isInvariant_latticeReflSnd_dgSpecification hβ
  · rintro σ (⟨i, rfl⟩ | hσ)
    · exact measurePreserving_dirac_of_toFun_eq (glide_toFun_staircase z i)
    · rcases hσ with rfl | rfl
      · exact measurePreserving_dirac_of_toFun_eq (reflFstSpin_toFun_staircase z)
      · exact measurePreserving_dirac_of_toFun_eq (latticeReflSnd_toFun_staircase z)

/-- **Georgii (6.21)(ii)**: `μ_z^β` is invariant under every staircase glide `g^z_i`, in
particular under `θ_{(0,1)}` (`i = (0,1)`) and `t^{-z} ∘ θ_{(1,0)}` (`i = (1,0)`). -/
theorem measurePreserving_glide_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ)
    (i : Site) :
    MeasurePreserving (glide z i).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      (staircasePhase hβ hr z) :=
  measurePreserving_staircasePhase hβ hr z
    (Subgroup.subset_closure (glide_mem_staircaseSymmetries z i))

/-- **Georgii (6.21)(ii)**: `μ_z^β` is invariant under the group generated by Georgii's two
generators `θ_{(0,1)}` and `t^{-z} ∘ θ_{(1,0)}`. -/
theorem measurePreserving_staircasePhase_of_mem_closure_generators (hβ : 0 < β)
    (hr : r' (β / 2) < 1) (z : ℤ) {τ : Transformation Site ℤ}
    (hτ : τ ∈ Subgroup.closure ({shift ℤ e1, glide z e0} : Set (Transformation Site ℤ))) :
    MeasurePreserving τ.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      (staircasePhase hβ hr z) := by
  refine measurePreserving_staircasePhase hβ hr z (Subgroup.closure_mono ?_ hτ)
  rintro σ (rfl | rfl)
  · exact glide_e1 z ▸ glide_mem_staircaseSymmetries z e1
  · exact glide_mem_staircaseSymmetries z e0

/-- **Georgii (6.21)(ii)**: `μ_z^β` is invariant under `r₁ ∘ τ`. -/
theorem measurePreserving_reflFstSpin_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1)
    (z : ℤ) :
    MeasurePreserving reflFstSpin.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      (staircasePhase hβ hr z) :=
  measurePreserving_staircasePhase hβ hr z
    (Subgroup.subset_closure (reflFstSpin_mem_staircaseSymmetries z))

/-- **Georgii (6.21)(ii)**: `μ_z^β` is invariant under `r₂`. -/
theorem measurePreserving_latticeReflSnd_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1)
    (z : ℤ) :
    MeasurePreserving latticeReflSnd.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      (staircasePhase hβ hr z) :=
  measurePreserving_staircasePhase hβ hr z
    (Subgroup.subset_closure (latticeReflSnd_mem_staircaseSymmetries z))

/-! ### Georgii Theorem (6.21)(ii): `τ(μ_z^β) = r₁(μ_z^β) = μ_{-z}^β` -/

/-- **The spin reflection carries Georgii's shift averages for `z` to those for `-z`.**  Its
spatial part is the identity, so it does not move the boxes, and it carries the boundary
condition `ω^z` to `ω^{-z}`. -/
theorem map_spinReflection_staircaseAverage (hβ : 0 < β) (z : ℤ) (N : ℕ) :
    Measure.map (spinReflection Site ℤ).toFun (staircaseAverage hβ z N : Measure (Site → ℤ))
      = (staircaseAverage hβ (-z) N : Measure (Site → ℤ)) := by
  classical
  have hinv : (dgSpecification hβ).map (spinReflection Site ℤ) = dgSpecification hβ :=
    isInvariant_spinReflection_dgSpecification hβ
  refine Measure.ext fun A hA ↦ ?_
  have hterm : ∀ Λ : Finset Site,
      dgSpecification hβ Λ (staircase z) ((spinReflection Site ℤ).toFun ⁻¹' A)
        = dgSpecification hβ Λ (staircase (-z)) A := by
    intro Λ
    have hΛ : Λ.map (spinReflection Site ℤ).sites.symm.toEmbedding = Λ := by
      simp [spinReflection, pureSpin]
    have hη : (spinReflection Site ℤ).inv.toFun (staircase (-z)) = staircase z := by
      funext i
      simp [staircase]
    conv_rhs => rw [← hinv]
    rw [Specification.map_apply' _ _ _ _ hA, hΛ, hη]
  rw [Measure.map_apply (spinReflection Site ℤ).measurable_toFun hA, coe_staircaseAverage,
    coe_staircaseAverage, Specification.average_apply, Specification.average_apply]
  refine congrArg _ (Finset.sum_congr rfl fun Λ _ ↦ ?_)
  rw [Measure.dirac_bind ((dgSpecification hβ).measurable_kernel_toMeasure Λ) (staircase z),
    Measure.dirac_bind ((dgSpecification hβ).measurable_kernel_toMeasure Λ) (staircase (-z)),
    hterm Λ]

/-- **The equivariance of the choice of cluster point.**  A transformation carrying the shift
averages of `z` to those of `w` for every `N` carries `μ_z^β` to `μ_w^β`, because both are limits
along the *same* ultrafilter `staircaseUltrafilter`. -/
theorem map_staircasePhase_of_map_staircaseAverage (hβ : 0 < β) (hr : r' (β / 2) < 1)
    {z w : ℤ} {τ : Transformation Site ℤ}
    (h : ∀ N : ℕ, Measure.map τ.toFun (staircaseAverage hβ z N : Measure (Site → ℤ))
      = (staircaseAverage hβ w N : Measure (Site → ℤ))) :
    Measure.map τ.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      = (staircasePhase hβ hr w : Measure (Site → ℤ)) := by
  have hmap : IsProbabilityMeasure
      (Measure.map τ.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map τ.measurable_toFun.aemeasurable
  refine separatesOn_localEvents hmap inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  have h1 := tendsto_staircaseAverage_apply hβ hr z (τ.preimage_mem_localEvents hA)
  have h2 := tendsto_staircaseAverage_apply hβ hr w hA
  have heq : ∀ N : ℕ,
      (staircaseAverage hβ z N : Measure (Site → ℤ)) (τ.toFun ⁻¹' A)
        = (staircaseAverage hβ w N : Measure (Site → ℤ)) A := fun N ↦ by
    rw [← Measure.map_apply τ.measurable_toFun hAm, h N]
  rw [Measure.map_apply τ.measurable_toFun hAm]
  exact tendsto_nhds_unique (h1.congr heq) h2

/-- **Georgii Theorem (6.21)(ii): `τ(μ_z^β) = μ_{-z}^β`.**  The spin reflection carries the random
staircase of slope `z` to the one of slope `-z`. -/
theorem map_spinReflection_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    Measure.map (spinReflection Site ℤ).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      = (staircasePhase hβ hr (-z) : Measure (Site → ℤ)) :=
  map_staircasePhase_of_map_staircaseAverage hβ hr (map_spinReflection_staircaseAverage hβ z)

/-- `r₁ ∘ τ` is the composite of the lattice reflection `r₁` and the spin reflection `τ`. -/
lemma reflFstSpin_toFun_eq :
    reflFstSpin.toFun = latticeReflFst.toFun ∘ (spinReflection Site ℤ).toFun := by
  funext ω i
  simp

/-- The lattice reflection `r₁` is an involution of configuration space. -/
lemma latticeReflFst_toFun_comp_self :
    latticeReflFst.toFun ∘ latticeReflFst.toFun = _root_.id := by
  funext ω i
  simp

/-- **Georgii Theorem (6.21)(ii): `r₁(μ_z^β) = τ(μ_z^β)`.**  Immediate from the `r₁ ∘ τ`-invariance
of `μ_z^β` and the fact that `r₁` is an involution. -/
theorem map_latticeReflFst_eq_map_spinReflection_staircasePhase (hβ : 0 < β)
    (hr : r' (β / 2) < 1) (z : ℤ) :
    Measure.map latticeReflFst.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      = Measure.map (spinReflection Site ℤ).toFun (staircasePhase hβ hr z) := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  have hfix : Measure.map reflFstSpin.toFun μ = μ :=
    (measurePreserving_reflFstSpin_staircasePhase hβ hr z).map_eq
  calc Measure.map latticeReflFst.toFun μ
      = Measure.map latticeReflFst.toFun (Measure.map reflFstSpin.toFun μ) := by rw [hfix]
    _ = Measure.map (spinReflection Site ℤ).toFun μ := by
        rw [reflFstSpin_toFun_eq,
          ← Measure.map_map latticeReflFst.measurable_toFun
            ((spinReflection Site ℤ).measurable_toFun),
          Measure.map_map latticeReflFst.measurable_toFun latticeReflFst.measurable_toFun,
          latticeReflFst_toFun_comp_self, Measure.map_id]

/-- **Georgii Theorem (6.21)(ii): `r₁(μ_z^β) = μ_{-z}^β`.** -/
theorem map_latticeReflFst_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    Measure.map latticeReflFst.toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      = (staircasePhase hβ hr (-z) : Measure (Site → ℤ)) := by
  rw [map_latticeReflFst_eq_map_spinReflection_staircasePhase hβ hr z,
    map_spinReflection_staircasePhase hβ hr z]

/-! ### Georgii Theorem (6.21)(i): the mean of the spin -/

/-- The layer-cake identity in `ℝ≥0∞`: a natural number is the sum of the indicators of the
conditions `k < n`, `k ∈ ℕ`.  It turns `μ(|σ_a - ω^z_a|)` into `∑_{k ≥ 1} μ(|σ_a - ω^z_a| ≥ k)`,
which the geometric estimate of Lemma (6.25) controls. -/
lemma tsum_ite_lt (n : ℕ) : ∑' k : ℕ, (if k < n then (1 : ℝ≥0∞) else 0) = n := by
  rw [tsum_eq_sum (s := Finset.range n) fun k hk ↦ ite_eq_right (by simpa using hk),
    Finset.sum_ite_of_true fun k hk ↦ Finset.mem_range.1 hk]
  simp

/-- The Euclidean norm of an integer, in `ℝ≥0∞`. -/
lemma enorm_intCast (m : ℤ) : ‖(m : ℝ)‖ₑ = (m.natAbs : ℝ≥0∞) := by
  rw [Real.enorm_eq_ofReal_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast,
    ENNReal.ofReal_natCast]

variable {β : ℝ}

/-- **Georgii Theorem (6.21)(i): `μ_z^β(|σ_a - ω^z_a|) < ∞`.**  The geometric tail estimate of
Lemma (6.25) makes the excess over the staircase integrable at every site. -/
theorem lintegral_absExcess_ne_top (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) (a : Site) :
    ∫⁻ ω, ((|ω a - staircase z a|).toNat : ℝ≥0∞)
        ∂(staircasePhase hβ hr z : Measure (Site → ℤ)) ≠ ⊤ := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  set c := staircase z a with hc
  set f : (Site → ℤ) → ℕ := fun ω ↦ (|ω a - c|).toNat with hf
  have hmeasf : ∀ k : ℕ, MeasurableSet {ω : Site → ℤ | k < f ω} := fun k ↦
    measurableSet_apply_mem a {x : ℤ | k < (|x - c|).toNat}
  have hind : ∀ ω : Site → ℤ, (f ω : ℝ≥0∞)
      = ∑' k : ℕ, Set.indicator {ω : Site → ℤ | k < f ω} (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [← tsum_ite_lt (f ω)]
    exact tsum_congr fun k ↦ by by_cases h : k < f ω <;> simp [h]
  have hgeom : ∑' k : ℕ, 2 * r' (β / 2) ^ (k + 1) ≠ ⊤ := by
    have h1 : ∀ k : ℕ, 2 * r' (β / 2) ^ (k + 1) = (2 * r' (β / 2)) * r' (β / 2) ^ k := fun k ↦ by
      rw [pow_succ, mul_comm (r' (β / 2) ^ k), ← mul_assoc]
    have h : ∑' k : ℕ, 2 * r' (β / 2) ^ (k + 1)
        = (2 * r' (β / 2)) * ∑' k : ℕ, r' (β / 2) ^ k := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr h1
    rw [h, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hr.ne_top)
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')
  refine ne_top_of_le_ne_top hgeom ?_
  calc ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ
      = ∑' k : ℕ, ∫⁻ ω, Set.indicator {ω : Site → ℤ | k < f ω} (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ := by
        rw [← lintegral_tsum fun k ↦ (measurable_const.indicator (hmeasf k)).aemeasurable]
        exact lintegral_congr hind
    _ = ∑' k : ℕ, μ {ω : Site → ℤ | k < f ω} :=
        tsum_congr fun k ↦ lintegral_indicator_one (hmeasf k)
    _ ≤ ∑' k : ℕ, 2 * r' (β / 2) ^ (k + 1) := by
        refine ENNReal.tsum_le_tsum fun k ↦ ?_
        have hs : {ω : Site → ℤ | k < f ω}
            = {ζ : Site → ℤ | ((k + 1 : ℕ) : ℤ) ≤ |ζ a - staircase z a|} := by
          ext ω
          simp only [hf, hc, Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one]
          omega
        rw [hs]
        exact staircasePhase_absExcess_le hβ hr z a (k + 1)

/-- **Georgii Theorem (6.21)(i): `μ_z^β(|σ_a|) < ∞`.**  The spin at every site is `μ_z^β`-
integrable, by the geometric estimate of Lemma (6.25). -/
theorem integrable_spin_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) (a : Site) :
    Integrable (fun ω : Site → ℤ ↦ (ω a : ℝ))
      (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  set c := staircase z a with hc
  have hmeas : Measurable (fun ω : Site → ℤ ↦ (ω a : ℝ)) :=
    (Measurable.of_discrete (f := fun m : ℤ ↦ (m : ℝ))).comp (measurable_pi_apply a)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound : ∀ ω : Site → ℤ,
      ‖(ω a : ℝ)‖ₑ ≤ (c.natAbs : ℝ≥0∞) + ((|ω a - c|).toNat : ℝ≥0∞) := by
    intro ω
    have h1 : ω a - c ≤ |ω a - c| := le_abs_self _
    have h2 : -(ω a - c) ≤ |ω a - c| := neg_le_abs _
    rw [enorm_intCast, ← Nat.cast_add]
    exact Nat.cast_le.2 (by omega)
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_add_left measurable_const]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  · exact lt_top_iff_ne_top.2 (lintegral_absExcess_ne_top hβ hr z a)

/-- The integral of the spin at `a` is unchanged by a symmetry `τ` of `μ_z^β`. -/
lemma integral_comp_of_measurePreserving {μ : Measure (Site → ℤ)}
    {τ : Transformation Site ℤ} (hτ : MeasurePreserving τ.toFun μ μ) (g : (Site → ℤ) → ℝ) :
    ∫ ω, g (τ.toFun ω) ∂μ = ∫ ω, g ω ∂μ :=
  hτ.integral_comp τ.toMeasurableEquiv.measurableEmbedding g

/-- **Georgii Theorem (6.21)(i): `μ_z^β(σ_0) = 0`.**  The symmetry `r₁ ∘ τ` of `ω^z` sends `σ_0`
to `-σ_0`, so the mean of the spin at the origin vanishes. -/
theorem integral_spin_zero_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) :
    ∫ ω, (ω (0 : Site) : ℝ) ∂(staircasePhase hβ hr z : Measure (Site → ℤ)) = 0 := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  set I := ∫ ω, (ω (0 : Site) : ℝ) ∂μ with hI
  have hcomp := integral_comp_of_measurePreserving
    (measurePreserving_reflFstSpin_staircasePhase hβ hr z)
    (fun ω : Site → ℤ ↦ (ω (0 : Site) : ℝ))
  have hfun : ∀ ω : Site → ℤ, ((reflFstSpin.toFun ω (0 : Site) : ℤ) : ℝ)
      = -((ω (0 : Site) : ℤ) : ℝ) := by
    intro ω
    rw [reflFstSpin_toFun]
    have h0 : mk (-((0 : Site) 0)) ((0 : Site) 1) = (0 : Site) := by
      rw [site_ext_iff]; simp
    rw [h0, Int.cast_neg]
  have h : (∫ ω : Site → ℤ, ((reflFstSpin.toFun ω (0 : Site) : ℤ) : ℝ) ∂μ) = -I := by
    simp only [hfun]
    rw [hI, integral_neg]
  rw [h] at hcomp
  linarith

/-- **Georgii Theorem (6.21)(i): `μ_z^β(σ_a) = ω^z_a`.**  The glide `g^z_a` carries `σ_a` to
`σ_0 + z a₁`, so the mean of the spin at `a` is the height of the staircase there.  Together with
`half_lt_staircasePhase` this is Georgii's statement that `μ_z^β` is a random perturbation of
`ω^z`. -/
theorem integral_spin_staircasePhase (hβ : 0 < β) (hr : r' (β / 2) < 1) (z : ℤ) (a : Site) :
    ∫ ω, (ω a : ℝ) ∂(staircasePhase hβ hr z : Measure (Site → ℤ))
      = (staircase z a : ℝ) := by
  set μ := (staircasePhase hβ hr z : Measure (Site → ℤ)) with hμ
  have hcomp := integral_comp_of_measurePreserving
    (measurePreserving_glide_staircasePhase hβ hr z a) (fun ω : Site → ℤ ↦ (ω a : ℝ))
  have hfun : ∀ ω : Site → ℤ, (((glide z a).toFun ω a : ℤ) : ℝ)
      = ((ω (0 : Site) : ℤ) : ℝ) + ((z * a 0 : ℤ) : ℝ) := by
    intro ω
    rw [glide_toFun_apply, sub_self, Int.cast_add]
  rw [← hcomp]
  simp only [hfun]
  rw [integral_add (integrable_spin_staircasePhase hβ hr z 0) (integrable_const _),
    integral_spin_zero_staircasePhase hβ hr z, zero_add, integral_const]
  simp [staircase]

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
    Measure.map (staircaseShift Site ℤ).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map (staircaseShift Site ℤ).toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map (staircaseShift Site ℤ).measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := (0 : Site)) (c := -1) (d := 0) (by omega) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | (staircaseShift Site ℤ).toFun ω (0 : Site) = -1}
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
    Measure.map (spinReflection Site ℤ).toFun (staircasePhase hβ hr z : Measure (Site → ℤ))
      ≠ (staircasePhase hβ hr z : Measure (Site → ℤ)) := by
  have : IsProbabilityMeasure (Measure.map (spinReflection Site ℤ).toFun
      (staircasePhase hβ hr z : Measure (Site → ℤ))) :=
    Measure.isProbabilityMeasure_map (spinReflection Site ℤ).measurable_toFun.aemeasurable
  refine ne_of_half_lt (a := e0) (c := -z) (d := z) (by omega) ?_ ?_
  · rw [map_toFun_spin_eq]
    have hset : {ω : Site → ℤ | (spinReflection Site ℤ).toFun ω e0 = -z}
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
* is distinct from `μ_w^β` for `w ≠ z` — part of Georgii (6.21)(iii);
* has mean `μ_z^β(σ_a) = ω^z_a` at every site — Georgii (6.21)(i);
* is invariant under the group generated by `θ_{(0,1)}`, `t^{-z} ∘ θ_{(1,0)}`, `r₁ ∘ τ` and `r₂`,
  and satisfies `τ(μ_z^β) = r₁(μ_z^β) = μ_{-z}^β` — Georgii (6.21)(ii).

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
        ≠ staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z) ∧
      (∀ a : Site, ∫ ω, (ω a : ℝ)
        ∂(staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z :
          Measure (Site → ℤ)) = (staircase z a : ℝ)) ∧
      (∀ τ ∈ Subgroup.closure (staircaseSymmetries z), MeasurePreserving τ.toFun
        (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z : Measure (Site → ℤ))
        (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z)) ∧
      Measure.map (spinReflection Site ℤ).toFun
          (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z :
            Measure (Site → ℤ))
        = (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) (-z) :
            Measure (Site → ℤ)) ∧
      Measure.map latticeReflFst.toFun
          (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) z :
            Measure (Site → ℤ))
        = (staircasePhase (pos_of_log_twelve hlog) (r'_half_lt_one hlog) (-z) :
            Measure (Site → ℤ)) :=
  ⟨staircasePhase_mem_GP _ _ z,
    staircasePhase_absExcess_le _ _ z,
    half_lt_staircasePhase _ _ (two_mul_r'_half_lt hlog) z,
    fun _ hw ↦ staircasePhase_ne _ _ (two_mul_r'_half_lt hlog) hw,
    integral_spin_staircasePhase _ _ z,
    fun _ hτ ↦ measurePreserving_staircasePhase _ _ z hτ,
    map_spinReflection_staircasePhase _ _ z,
    map_latticeReflFst_staircasePhase _ _ z⟩

end MeasureTheory.GibbsMeasure.Shlosman

namespace MeasureTheory.GibbsMeasure.Shlosman

open Potential Peierls PeierlsSharp

variable {β : ℝ} (hβ : 0 < β) (hr : r' (β / 2) < 1)
include hβ hr

/-- **Georgii Theorem (6.21)(i), the low-temperature limit, in finite volume.**  On every finite
volume `Λ` the random staircase agrees with the staircase `ω^z` with probability at least
`1 - 2 |Λ| r'(β/2)`, and `r'(β/2) → 0` as `β → ∞`: the Gibbs measure is a random perturbation
of the staircase which freezes onto it at low temperature.  Georgii's actual limit statement in
(6.21)(i), `μ_z^β → δ_{ω^z}` as `β → ∞`, is *not* proved here; only this bound at fixed `β`
is. -/
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
