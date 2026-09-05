/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Potential.NearestNeighbour
public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Potential.GibbsTransformation
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The Ising model, and existence of its Gibbs measures

The Ising potential over `Bool` spins on a graph — the nearest-neighbour pair potential of
Georgii (2.16)/(2.17) with the coefficients of formula (3.13): `Φ_{i} = -h σ_i`,
`Φ_{i,j} = -J σ_i σ_j` on edges (wiki: `ising_potential`) — its Gibbsian specification with
uniform a-priori spin measure, and, as instances of Georgii Theorem (4.23)(a), **existence** and
**compactness** of the set of Ising Gibbs measures on any countable locally finite graph, in
particular on the lattice `ℤ^d`.

Non-uniqueness at low temperature on `ℤ²` (Georgii Theorem (6.9)) is proved in
`GibbsMeasure/Model/PhaseTransition.lean`, uniqueness at high temperature (Dobrushin's condition,
Georgii (8.7)/(8.8)) in `GibbsMeasure/Model/IsingDobrushin.lean`, and the simplex structure
(Georgii (7.26)) in `GibbsMeasure/Specification/ExtremeDecomposition.lean`.

Also here, for an arbitrary locally finite graph, the decomposition of the Hamiltonian
`hamiltonian_isingPotential`: `H_Λ(σ) = -J ∑_{b ∩ Λ ≠ ∅} σ_i σ_j - h ∑_{i ∈ Λ} σ_i`, the bond
energies over `SimpleGraph.bondsOf Λ` (`spinBond`) and the field energies over `Λ`.  Its
specialisations are the two-dimensional Peierls estimate (`Model/PeierlsEstimate.lean`) and the
Cayley tree (`Model/IsingCayleyTree.lean`).

What is *not* proved here: uniqueness on `ℤ` (Georgii (3.15), from Theorem (3.5)).
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### B5: the Ising model over `Bool` spins -/

/-- The `±1` spin observable on `Bool`. -/
def spin : Bool → ℝ := fun b ↦ if b then 1 else -1

lemma measurable_spin : Measurable spin := Measurable.of_discrete

lemma abs_spin_le (b : Bool) : |spin b| ≤ 1 := by cases b <;> simp [spin]

lemma spin_not (b : Bool) : spin (!b) = -spin b := by cases b <;> simp [spin]

lemma spin_mul_self (b : Bool) : spin b * spin b = 1 := by cases b <;> norm_num [spin]

lemma spin_mul_spin_of_ne {x y : Bool} (h : y ≠ x) : spin x * spin y = -1 := by
  cases x <;> cases y <;> simp_all [spin]

lemma spin_mul_spin (a b : Bool) : spin a * spin b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [spin]

/-- The Ising potential on a graph `G` with coupling `J` and external field `h`. -/
noncomputable def isingPotential {S : Type*} (G : SimpleGraph S) (J h : ℝ) :
    Potential S Bool :=
  Potential.nearestNeighbourPair G J h spin

instance {S : Type*} (G : SimpleGraph S) (J h : ℝ) :
    Potential.IsPotential (isingPotential G J h) :=
  Potential.isPotential_nearestNeighbourPair G J h measurable_spin

instance {S : Type*} (G : SimpleGraph S) [G.LocallyFinite] (J h : ℝ) :
    Potential.IsFiniteRange (isingPotential G J h) :=
  Potential.isFiniteRange_nearestNeighbourPair G J h spin

instance {S : Type*} (G : SimpleGraph S) [G.LocallyFinite] (J h : ℝ) :
    Potential.IsAbsolutelySummable (isingPotential G J h) :=
  Potential.isAbsolutelySummable_nearestNeighbourPair G J h abs_spin_le

/-- **The external field is a direction in potential space.** Adding `t` times the pure external
field `Φ^{0,1}` — the Ising potential with coupling `0` and field `1`, i.e. `Φ_{i} = −σ_i` — to
the Ising potential moves the field from `h` to `h + t` and leaves the coupling `J` alone: the
bond terms of `Φ^{0,1}` carry the factor `0`. -/
lemma isingPotential_add_smul_field {S : Type*} (G : SimpleGraph S) (J h t : ℝ) :
    isingPotential G J h + t • isingPotential G 0 1 = isingPotential G J (h + t) := by
  funext A η
  change isingPotential G J h A η + t * isingPotential G 0 1 A η
    = isingPotential G J (h + t) A η
  by_cases h1 : A.card = 1
  · simp only [isingPotential, Potential.nearestNeighbourPair_apply_card_one h1]
    ring
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
    · simp only [isingPotential, Potential.nearestNeighbourPair_apply_pair h2]
      ring
    · simp only [isingPotential, Potential.nearestNeighbourPair_apply_eq_zero h1 h2]
      ring

/-! ### The Hamiltonian of the Ising potential

On an arbitrary locally finite graph, `H_Λ^{Φ^{J,h}}(σ) = -J ∑_{b ∩ Λ ≠ ∅} σ_i σ_j
- h ∑_{i ∈ Λ} σ_i`: the bond energies of the bonds meeting `Λ` (`SimpleGraph.bondsOf`) and the
field energies of the sites of `Λ`. -/

section Spins
variable {S : Type*}

/-- The product `σ_i σ_j` of the two spins on a bond `b = {i, j}`. -/
def spinBond (σ : S → Bool) : Sym2 S → ℝ :=
  Sym2.lift ⟨fun i j ↦ spin (σ i) * spin (σ j), fun _ _ ↦ mul_comm _ _⟩

@[simp] lemma spinBond_mk (σ : S → Bool) (i j : S) :
    spinBond σ s(i, j) = spin (σ i) * spin (σ j) := rfl

/-- The sum `σ_i + σ_j` of the two spins on a bond `b = {i, j}`. -/
def spinSum (σ : S → Bool) : Sym2 S → ℝ :=
  Sym2.lift ⟨fun i j ↦ spin (σ i) + spin (σ j), fun _ _ ↦ add_comm _ _⟩

@[simp] lemma spinSum_mk (σ : S → Bool) (i j : S) :
    spinSum σ s(i, j) = spin (σ i) + spin (σ j) := rfl

end Spins

section Hamiltonian
variable {S : Type*} [DecidableEq S] {G : SimpleGraph S} [G.LocallyFinite] {J h : ℝ}

/-- Two bonds with the same pair of endpoints are equal: a bond is not a loop. -/
lemma toFinset_injOn_bondsOf (Λ : Finset S) :
    ∀ e ∈ G.bondsOf Λ, ∀ f ∈ G.bondsOf Λ, e.toFinset = f.toFinset → e = f := by
  intro e he f hf hef
  revert he hf hef
  refine Sym2.inductionOn e fun a b ↦ Sym2.inductionOn f fun c d he hf hef ↦ ?_
  have hab : a ≠ b := (SimpleGraph.mk_mem_bondsOf.1 he).1.ne
  have hcd : c ≠ d := (SimpleGraph.mk_mem_bondsOf.1 hf).1.ne
  rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at hef
  have hc : c ∈ ({a, b} : Finset S) := hef ▸ Finset.mem_insert_self c {d}
  have hd : d ∈ ({a, b} : Finset S) :=
    hef ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self d)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact absurd rfl hcd
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hcd

/-- The interactions of the Ising potential that meet `Λ` are the sites of `Λ` and the bonds
meeting `Λ`; every other interaction meeting `Λ` vanishes. -/
lemma isingPotential_eq_zero_of_notMem {Λ A : Finset S} (σ : S → Bool)
    (hd : ¬ Disjoint A Λ) (h1 : A ∉ Λ.image (fun i ↦ ({i} : Finset S)))
    (h2 : A ∉ (G.bondsOf Λ).image Sym2.toFinset) : isingPotential G J h A σ = 0 := by
  classical
  by_cases hc1 : A.card = 1
  · exfalso
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hc1
    obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hd
    rw [Finset.mem_singleton] at hxA
    subst hxA
    exact h1 (Finset.mem_image.2 ⟨x, hxΛ, rfl⟩)
  by_cases hc2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
  · exfalso
    obtain ⟨hcard, i, hi, j, hj, hij⟩ := hc2
    have hA : A = {i, j} := by
      refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hi
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact hj
      · rw [hcard, Finset.card_pair hij.ne]
    obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hd
    rw [hA, Finset.mem_insert, Finset.mem_singleton] at hxA
    refine h2 (Finset.mem_image.2 ⟨s(i, j), SimpleGraph.mk_mem_bondsOf.2 ⟨hij, ?_⟩, ?_⟩)
    · rcases hxA with rfl | rfl
      · exact Or.inl hxΛ
      · exact Or.inr hxΛ
    · rw [Sym2.toFinset_mk_eq, hA]
  · rw [isingPotential]
    exact Potential.nearestNeighbourPair_apply_eq_zero hc1 hc2 σ

/-- **The Ising Hamiltonian.**
`H_Λ^{Φ^{J,h}}(σ) = -J ∑_{b ∩ Λ ≠ ∅} σ_i σ_j - h ∑_{i ∈ Λ} σ_i`: the bond energies of the bonds
meeting `Λ` and the field energies of the sites of `Λ`. -/
theorem hamiltonian_isingPotential (Λ : Finset S) (σ : S → Bool) :
    (isingPotential G J h).hamiltonian Λ σ
      = -J * ∑ b ∈ G.bondsOf Λ, spinBond σ b - h * ∑ i ∈ Λ, spin (σ i) := by
  classical
  have hsing : ∀ i ∈ Λ, (isingPotential G J h).hamiltonianTerms Λ σ {i} = -h * spin (σ i) := by
    intro i hi
    rw [Potential.hamiltonianTerms_of_not_disjoint
        (Finset.not_disjoint_iff.2 ⟨i, Finset.mem_singleton_self i, hi⟩),
      isingPotential, Potential.nearestNeighbourPair_apply_card_one (Finset.card_singleton i),
      Finset.sum_singleton]
  have hbond : ∀ b ∈ G.bondsOf Λ,
      (isingPotential G J h).hamiltonianTerms Λ σ b.toFinset = -J * spinBond σ b := by
    intro b hb
    revert hb
    refine Sym2.inductionOn b fun i j hb ↦ ?_
    obtain ⟨hij, hmem⟩ := SimpleGraph.mk_mem_bondsOf.1 hb
    have hnd : ¬ Disjoint (s(i, j).toFinset) Λ := by
      rw [Sym2.toFinset_mk_eq, Finset.not_disjoint_iff]
      rcases hmem with hi | hj
      · exact ⟨i, by simp, hi⟩
      · exact ⟨j, by simp, hj⟩
    rw [Potential.hamiltonianTerms_of_not_disjoint hnd, Sym2.toFinset_mk_eq, isingPotential,
      Potential.nearestNeighbourPair_apply_pair
        ⟨Finset.card_pair hij.ne, i, by simp, j, by simp, hij⟩,
      Finset.prod_pair hij.ne, spinBond_mk]
  have hdisjT : Disjoint (Λ.image (fun i ↦ ({i} : Finset S)))
      ((G.bondsOf Λ).image Sym2.toFinset) := by
    rw [Finset.disjoint_left]
    rintro A hA hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨b, hb, hbA⟩ := Finset.mem_image.1 hB
    revert hb hbA
    refine Sym2.inductionOn b fun x y hb hbA ↦ ?_
    have hxy : x ≠ y := (SimpleGraph.mk_mem_bondsOf.1 hb).1.ne
    rw [Sym2.toFinset_mk_eq] at hbA
    have hcard := congrArg Finset.card hbA
    rw [Finset.card_pair hxy, Finset.card_singleton] at hcard
    omega
  have hzero : ∀ A ∉ Λ.image (fun i ↦ ({i} : Finset S)) ∪ (G.bondsOf Λ).image Sym2.toFinset,
      (isingPotential G J h).hamiltonianTerms Λ σ A = 0 := by
    intro A hA
    rw [Finset.mem_union, not_or] at hA
    by_cases hdisj : Disjoint A Λ
    · exact Potential.hamiltonianTerms_of_disjoint hdisj σ
    · rw [Potential.hamiltonianTerms_of_not_disjoint hdisj]
      exact isingPotential_eq_zero_of_notMem σ hdisj hA.1 hA.2
  have hone : ∑ A ∈ Λ.image (fun i ↦ ({i} : Finset S)),
      (isingPotential G J h).hamiltonianTerms Λ σ A = -h * ∑ i ∈ Λ, spin (σ i) := by
    rw [Finset.sum_image (fun i _ j _ hij ↦ by simpa using hij), Finset.mul_sum]
    exact Finset.sum_congr rfl hsing
  have htwo : ∑ A ∈ (G.bondsOf Λ).image Sym2.toFinset,
      (isingPotential G J h).hamiltonianTerms Λ σ A
        = -J * ∑ b ∈ G.bondsOf Λ, spinBond σ b := by
    rw [Finset.sum_image (toFinset_injOn_bondsOf Λ), Finset.mul_sum]
    exact Finset.sum_congr rfl hbond
  rw [Potential.hamiltonian_eq_tsum, tsum_eq_sum hzero, Finset.sum_union hdisjT, hone, htwo]
  ring

end Hamiltonian

/-- The uniform a-priori single-spin measure on `Bool`. -/
noncomputable def uniformSpinMeasure : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniformSpinMeasure := by
  refine ⟨?_⟩
  have hcount : Measure.count (Set.univ : Set Bool) = 2 := by
    rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
    norm_num
  change ((2 : ℝ≥0∞)⁻¹ • Measure.count) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul, hcount,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- `uniformSpinMeasure` is Mathlib's uniform distribution on `Bool`. -/
lemma uniformSpinMeasure_eq_uniformOn :
    uniformSpinMeasure = ProbabilityTheory.uniformOn (Set.univ : Set Bool) := by
  rw [ProbabilityTheory.uniformOn, ProbabilityTheory.cond, Measure.restrict_univ,
    uniformSpinMeasure]
  congr 1
  rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
  norm_num

/-! ### B6: the Ising Gibbsian specification and Georgii (4.23)(a) -/

/-- The Ising Gibbsian specification of a locally finite graph at inverse temperature `β`,
with uniform a-priori spin measure. -/
noncomputable def isingSpecification {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) : Specification S Bool :=
  Potential.gibbsSpecificationOfAbsolutelySummable (Φ := isingPotential G J h)
    uniformSpinMeasure β

/-- **Existence of Ising Gibbs measures** (Georgii (4.23)(a) for the Ising model):
on any countable, locally finite graph, at every coupling, external field and inverse
temperature, the set of Gibbs measures for the Ising specification is nonempty. -/
theorem isingGibbsMeasure_nonempty {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) :
    (GP (S := S) (E := Bool) (isingSpecification G J h β)).Nonempty :=
  Potential.GP_gibbsSpecification_nonempty (Φ := isingPotential G J h) uniformSpinMeasure β

/-- **Compactness of the set of Ising Gibbs measures** in the topology of local convergence. -/
theorem isCompact_setOf_isingGibbsMeasure {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) :
    IsCompact {μ : WithLocalConvergence S Bool |
      μ.toMeasure ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)} :=
  Potential.isCompact_setOf_mem_GP_gibbsSpecification uniformSpinMeasure β

/-! ### B7: the `ℤ^d` lattice -/

/-- The nearest-neighbour graph on `ℤ^d`: two points are adjacent iff their `ℓ¹` distance
is `1`. (This forces `x ≠ y`.) -/
def latticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj x y := ∑ i, (x i - y i).natAbs = 1
  symm := ⟨fun x y hxy ↦ by
    rw [← hxy]
    exact Finset.sum_congr rfl fun i _ ↦ by omega⟩
  loopless := ⟨fun x hx ↦ by simp at hx⟩

/-- An `ℓ¹`-neighbour of `x` in `ℤ^d` is `x` shifted by `±1` in exactly one coordinate. -/
lemma latticeGraph_adj_decomp {d : ℕ} {x y : Fin d → ℤ}
    (hxy : (latticeGraph d).Adj x y) :
    ∃ (j : Fin d) (s : ℤ), (s = 1 ∨ s = -1) ∧ y = Function.update x j (x j + s) := by
  classical
  have h1 : ∑ i, (x i - y i).natAbs = 1 := hxy
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [h1]; exact one_ne_zero)
  have hj1 : (x j - y j).natAbs = 1 := by
    have hle : (x j - y j).natAbs ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun i ↦ (x i - y i).natAbs)
        (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have herase : ∑ i ∈ Finset.univ.erase j, (x i - y i).natAbs = 0 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun i ↦ (x i - y i).natAbs)
      (Finset.mem_univ j)
    omega
  have hrest : ∀ k, k ≠ j → y k = x k := by
    intro k hk
    have hle : (x k - y k).natAbs ≤ ∑ i ∈ Finset.univ.erase j, (x i - y i).natAbs :=
      Finset.single_le_sum (f := fun i ↦ (x i - y i).natAbs)
        (fun i _ ↦ Nat.zero_le _) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    omega
  refine ⟨j, y j - x j, by omega, funext fun k ↦ ?_⟩
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self]
    ring
  · rw [Function.update_of_ne hk]
    exact hrest k hk

/-- `ℤ^d` is locally finite: each point has (at most) `2d` neighbours. -/
noncomputable instance (d : ℕ) : (latticeGraph d).LocallyFinite := fun v ↦
  Set.Finite.fintype <| (Set.finite_range
      (fun p : Fin d × Bool ↦
        Function.update v p.1 (v p.1 + if p.2 then (1 : ℤ) else -1))).subset <| by
    rintro y hy
    obtain ⟨j, s, hs, rfl⟩ := latticeGraph_adj_decomp hy
    rcases hs with rfl | rfl
    · exact ⟨(j, true), by simp⟩
    · exact ⟨(j, false), by simp⟩

/-- **`ℤ^d` is `2d`-regular.** The neighbours of `v` are exactly the `2d` points
`v ± e_j`, `j ∈ Fin d`, which are pairwise distinct. (For `d = 0` the graph is a single
isolated point and both sides are `0`.) -/
lemma card_neighborFinset_latticeGraph (d : ℕ) (v : Fin d → ℤ) :
    ((latticeGraph d).neighborFinset v).card = 2 * d := by
  classical
  have hone : ∀ b : Bool, (if b then (1 : ℤ) else -1).natAbs = 1 := by decide
  have hne0 : ∀ b : Bool, (if b then (1 : ℤ) else -1) ≠ 0 := by decide
  have hbinj : ∀ b b' : Bool, (if b then (1 : ℤ) else -1) = (if b' then (1 : ℤ) else -1) →
      b = b' := by decide
  set g : Fin d × Bool → (Fin d → ℤ) :=
    fun p ↦ Function.update v p.1 (v p.1 + if p.2 then (1 : ℤ) else -1) with hgdef
  -- every `v ± e_j` is a neighbour of `v`
  have hstep : ∀ (j : Fin d) (s : ℤ), s.natAbs = 1 →
      (latticeGraph d).Adj v (Function.update v j (v j + s)) := by
    intro j s hs
    change ∑ i, (v i - Function.update v j (v j + s) i).natAbs = 1
    rw [Finset.sum_eq_single j]
    · rw [Function.update_self]; omega
    · intro i _ hi
      rw [Function.update_of_ne hi]
      simp
    · intro h
      exact absurd (Finset.mem_univ j) h
  -- the `2d` shifts are pairwise distinct
  have hinj : Function.Injective g := by
    rintro ⟨j, b⟩ ⟨j', b'⟩ hpq
    have hjj : j = j' := by
      by_contra hne
      have h1 := congrFun hpq j
      rw [hgdef] at h1
      simp only [Function.update_self, Function.update_of_ne hne] at h1
      exact hne0 b (by omega)
    subst hjj
    have h2 := congrFun hpq j
    rw [hgdef] at h2
    simp only [Function.update_self, add_right_inj] at h2
    rw [hbinj b b' h2]
  have hset : (latticeGraph d).neighborFinset v = Finset.image g Finset.univ := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hy
      obtain ⟨j, s, hs, rfl⟩ := latticeGraph_adj_decomp hy
      rcases hs with rfl | rfl
      · exact ⟨(j, true), Finset.mem_univ _, by simp [hgdef]⟩
      · exact ⟨(j, false), Finset.mem_univ _, by simp [hgdef]⟩
    · rintro ⟨⟨j, b⟩, -, rfl⟩
      exact hstep j _ (hone b)
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, mul_comm]

/-- **Existence of Gibbs measures for the `ℤ^d` Ising model**, for every coupling, external
field and inverse temperature. -/
theorem latticeIsingGibbsMeasure_nonempty (d : ℕ) (J h β : ℝ) :
    (GP (S := Fin d → ℤ) (E := Bool)
      (isingSpecification (latticeGraph d) J h β)).Nonempty :=
  isingGibbsMeasure_nonempty (latticeGraph d) J h β

/-- **Compactness of the set of `ℤ^d` Ising Gibbs measures** in the topology of local
convergence. -/
theorem isCompact_setOf_latticeIsingGibbsMeasure (d : ℕ) (J h β : ℝ) :
    IsCompact {μ : WithLocalConvergence (Fin d → ℤ) Bool |
      μ.toMeasure ∈ GP (S := Fin d → ℤ) (E := Bool)
        (isingSpecification (latticeGraph d) J h β)} :=
  isCompact_setOf_isingGibbsMeasure (latticeGraph d) J h β

/-! ### Shift-invariance (Georgii (5.8)) -/

section Shift
variable {d : ℕ}

lemma latticeGraph_adj_sub_iff (j : Fin d → ℤ) {a b : Fin d → ℤ} :
    (latticeGraph d).Adj (a - j) (b - j) ↔ (latticeGraph d).Adj a b := by
  change (∑ i, ((a - j) i - (b - j) i).natAbs = 1) ↔ (∑ i, (a i - b i).natAbs = 1)
  simp only [Pi.sub_apply, sub_sub_sub_cancel_right]

/-- **Georgii (5.8) for the Ising model**: the Ising potential on `ℤ^d` is shift-invariant. -/
theorem isingPotential_isShiftInvariant (J h : ℝ) :
    (isingPotential (latticeGraph d) J h).IsShiftInvariant := by
  classical
  intro j
  funext A η
  rw [Potential.map_apply]
  simp only [isingPotential, Potential.nearestNeighbourPair]
  have hcard : (A.map (shift Bool j).sites.symm.toEmbedding).card = A.card :=
    Finset.card_map _
  have hadj : (∃ a ∈ A.map (shift Bool j).sites.symm.toEmbedding,
        ∃ b ∈ A.map (shift Bool j).sites.symm.toEmbedding, (latticeGraph d).Adj a b)
      ↔ ∃ a ∈ A, ∃ b ∈ A, (latticeGraph d).Adj a b := by
    simp only [Finset.mem_map_equiv]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨(shift Bool j).sites.symm.symm a, ha, (shift Bool j).sites.symm.symm b,
        hb, ?_⟩
      have : (shift Bool j).sites.symm.symm a - j = a := by
        simp [shift, Equiv.coe_addRight]
      have h2 : (shift Bool j).sites.symm.symm b - j = b := by
        simp [shift, Equiv.coe_addRight]
      rw [← latticeGraph_adj_sub_iff j, this, h2]; exact hab
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨(shift Bool j).sites.symm a, by simpa using ha,
        (shift Bool j).sites.symm b, by simpa using hb, ?_⟩
      have : (shift Bool j).sites.symm a = a - j := by
        simp [shift, Equiv.addRight_symm, Equiv.coe_addRight, sub_eq_add_neg]
      have h2 : (shift Bool j).sites.symm b = b - j := by
        simp [shift, Equiv.addRight_symm, Equiv.coe_addRight, sub_eq_add_neg]
      rw [this, h2, latticeGraph_adj_sub_iff]; exact hab
  have hsum : ∑ i ∈ A.map (shift Bool j).sites.symm.toEmbedding,
      spin ((shift Bool j).inv.toFun η i) = ∑ i ∈ A, spin (η i) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [shift, Transformation.inv, Transformation.toFun, Equiv.addRight_symm, Equiv.coe_addRight]
  have hprod : ∏ i ∈ A.map (shift Bool j).sites.symm.toEmbedding,
      spin ((shift Bool j).inv.toFun η i) = ∏ i ∈ A, spin (η i) := by
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [shift, Transformation.inv, Transformation.toFun, Equiv.addRight_symm, Equiv.coe_addRight]
  simp only [hcard, hadj, hsum, hprod]

end Shift

/-! ### Shift-invariance of the Ising specification (Georgii (5.8), (5.9)(b), (5.11)) -/

section ShiftSpecification
variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-- **Georgii (5.9)(b) for the shift.** The Gibbsian specification of a shift-invariant `Φ ∈ ℬ`
on `ℤ^d` is shift-invariant (Georgii (5.8)). -/
theorem isInvariant_shift_gibbsSpecification {Φ : Potential (Fin d → ℤ) E}
    [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant)
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) (j : Fin d → ℤ) :
    Specification.IsInvariant (shift E j)
      (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  Potential.isInvariant_shift_gibbsSpecification hΦ ν β j

/-- **The Ising specification on `ℤ^d` is shift-invariant** (Georgii (5.8), (5.9)(b)). -/
theorem isInvariant_shift_isingSpecification (d : ℕ) (J h β : ℝ) (j : Fin d → ℤ) :
    Specification.IsInvariant (shift Bool j) (isingSpecification (latticeGraph d) J h β) :=
  isInvariant_shift_gibbsSpecification (isingPotential_isShiftInvariant J h) uniformSpinMeasure
    β j

/-- **Georgii (5.11) for the Ising model.** A unique Ising Gibbs measure on `ℤ^d` is
shift-invariant. -/
theorem measurePreserving_shift_of_GP_isingSpecification_eq_singleton (d : ℕ) (J h β : ℝ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → Bool)}
    (hGP : GP (isingSpecification (latticeGraph d) J h β) = {μ}) (j : Fin d → ℤ) :
    MeasurePreserving (shift Bool j).toFun (μ : Measure ((Fin d → ℤ) → Bool)) μ :=
  (isInvariant_shift_isingSpecification d J h β j).measurePreserving_of_GP_eq_singleton hGP

end ShiftSpecification

/-- The spin flip preserves the uniform a-priori spin measure. This generalises
`Peierls.measurePreserving_boolNot`. -/
lemma measurePreserving_boolNot_uniformSpinMeasure :
    MeasurePreserving ⇑boolNot uniformSpinMeasure uniformSpinMeasure := by
  refine ⟨boolNot.measurable, ?_⟩
  have hsingle : ∀ c : Bool, uniformSpinMeasure {c} = 2⁻¹ := by
    intro c
    rw [uniformSpinMeasure, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
  refine Measure.ext_of_singleton fun c ↦ ?_
  rw [Measure.map_apply boolNot.measurable (measurableSet_singleton c)]
  have hpre : (⇑boolNot ⁻¹' {c}) = {!c} := by
    ext d
    cases c <;> cases d <;> simp
  rw [hpre, hsingle, hsingle]

/-- The uniform-spin case of `Specification.lintegral_isssd_fintype`: the `2^{-|Λ|}` weights are
constant. -/
lemma lintegral_isssd_uniformSpinMeasure {S : Type*} [DecidableEq S] (Λ : Finset S)
    (η : S → Bool) {F : (S → Bool) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(Specification.isssd (S := S) (E := Bool) uniformSpinMeasure Λ η)
      = (∑ ζ : (Λ → Bool), F (juxt (Λ : Set S) η ζ)) * (2 : ℝ≥0∞)⁻¹ ^ Fintype.card Λ := by
  have hsingle : ∀ b : Bool, uniformSpinMeasure {b} = (2 : ℝ≥0∞)⁻¹ := fun b ↦ by
    change ((2 : ℝ≥0∞)⁻¹ • Measure.count) {b} = _
    rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  rw [Specification.lintegral_isssd_fintype uniformSpinMeasure Λ η hF, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  simp only [hsingle, Finset.prod_const, Finset.card_univ]

end MeasureTheory.GibbsMeasure
