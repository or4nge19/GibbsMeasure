import Mathlib
import GibbsMeasure

/-!
# Comparator solution: the two-dimensional Ising phase transition (Georgii, Theorem (6.9))

This is the *solution* file matching `Comparator/Challenge.lean`.  Every declaration of the
challenge file is reproduced **verbatim**; the only differences are the extra
`import GibbsMeasure`, this module docstring, an auxiliary `namespace Bridge` block translating
between the challenge's from-scratch definitions and the `GibbsMeasure` library, and the proof
terms of the two final theorems.

The bridge establishes, for every inverse temperature `β`, that the challenge's explicitly written
finite-volume Gibbs distribution `gibbsMeasure β Λ ω` is *literally the same measure* as the
`Λ`-kernel of the library's `isingSpecification (latticeGraph 2) 1 0 β`, whence
`IsGibbs β μ ↔ μ ∈ GP (isingSpecification (latticeGraph 2) 1 0 β)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace IsingChallenge

/-! ### The lattice and the configuration space -/

/-- The sites of the two-dimensional lattice `ℤ²`. -/
abbrev Site : Type := Fin 2 → ℤ

/-- A spin configuration: a `Bool`, i.e. a sign, attached to every site of `ℤ²`. Being a product
of copies of the discrete space `Bool`, this carries the product σ-algebra. -/
abbrev Config : Type := Site → Bool

/-- The `±1`-valued spin attached to a `Bool`: `true ↦ +1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The `k`-th unit vector of the lattice `ℤ²`. -/
def e (k : Fin 2) : Site := fun l ↦ if l = k then 1 else 0

/-! ### The nearest-neighbour bonds meeting a finite volume

A nearest-neighbour bond of `ℤ²` is an unordered pair `{i, i + e k}` with `k : Fin 2`; we encode
it by the ordered pair `(i, k)`, so that each bond has exactly one encoding. -/

/-- An auxiliary finite set of sites containing every left endpoint of a bond meeting `Λ`: the
volume `Λ` itself together with all of its translates by `-e k`. -/
def bondBase (Λ : Finset Site) : Finset Site :=
  Λ ∪ (Finset.univ : Finset (Fin 2)).biUnion fun k ↦ Λ.image fun i ↦ i - e k

/-- The set of nearest-neighbour bonds `{i, i + e k}` of `ℤ²` that *meet* the finite volume `Λ`,
encoded as ordered pairs `(i, k)`. It is finite because the left endpoint `i` of such a bond lies
either in `Λ` or in one of the two translates `Λ - e k`. -/
def bonds (Λ : Finset Site) : Finset (Site × Fin 2) :=
  (bondBase Λ ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p ↦ p.1 ∈ Λ ∨ p.1 + e p.2 ∈ Λ

/-- The promised characterisation: `(i, k)` belongs to `bonds Λ` exactly when the nearest-neighbour
bond `{i, i + e k}` meets `Λ`. -/
theorem mem_bonds (Λ : Finset Site) (i : Site) (k : Fin 2) :
    (i, k) ∈ bonds Λ ↔ (i ∈ Λ ∨ i + e k ∈ Λ) := by
  refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨?_, h⟩⟩
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
  rcases h with h | h
  · exact Finset.mem_union_left _ h
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ?_⟩)
    exact Finset.mem_image.mpr ⟨i + e k, h, by simp⟩

/-! ### The Ising Hamiltonian -/

/-- The energy of the configuration `σ` in the finite volume `Λ`: minus the sum of the products of
neighbouring spins, over all nearest-neighbour bonds meeting `Λ`. This is the ferromagnetic Ising
Hamiltonian with coupling constant `1` and zero external field. -/
def hamiltonian (Λ : Finset Site) (σ : Config) : ℝ :=
  -∑ p ∈ bonds Λ, spin (σ p.1) * spin (σ (p.1 + e p.2))

/-! ### The finite-volume Gibbs distribution -/

/-- `glue Λ ζ ω` follows `ζ` inside `Λ` and the boundary condition `ω` outside `Λ`. -/
def glue (Λ : Finset Site) (ζ ω : Config) : Config := fun i ↦ if i ∈ Λ then ζ i else ω i

/-- Extend an inner configuration `ζ : Λ → Bool` to all of `ℤ²`, using `ω` outside `Λ`. -/
def extend (Λ : Finset Site) (ζ : Λ → Bool) (ω : Config) : Config :=
  fun i ↦ if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

/-- The unnormalised Boltzmann weight `exp (-β * H)` of the inner configuration `ζ` in the volume
`Λ` with boundary condition `ω`. -/
def weight (β : ℝ) (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) : ℝ :=
  Real.exp (-β * hamiltonian Λ (glue Λ (extend Λ ζ ω) ω))

/-- The partition function in the volume `Λ` with boundary condition `ω`: the sum of the Boltzmann
weights over the `2 ^ #Λ` inner configurations. -/
def partitionFunction (β : ℝ) (Λ : Finset Site) (ω : Config) : ℝ :=
  ∑ ζ : Λ → Bool, weight β Λ ω ζ

/-- The finite-volume Gibbs distribution in `Λ` at inverse temperature `β` with boundary condition
`ω`, written out explicitly as a normalised finite sum of Dirac measures: the configuration that
agrees with `ζ` on `Λ` and with `ω` off `Λ` gets probability `exp (-β * H) / Z`. -/
def gibbsMeasure (β : ℝ) (Λ : Finset Site) (ω : Config) : Measure Config :=
  (ENNReal.ofReal (partitionFunction β Λ ω))⁻¹ •
    ∑ ζ : Λ → Bool,
      ENNReal.ofReal (weight β Λ ω ζ) • Measure.dirac (glue Λ (extend Λ ζ ω) ω)

/-! ### Gibbs measures (the DLR equation) -/

/-- `μ` is a Gibbs measure for the two-dimensional Ising model at inverse temperature `β`: it is a
probability measure on `Config` whose conditional distribution in every finite volume `Λ`, given
the configuration outside `Λ`, is the finite-volume Gibbs distribution. This is the
Dobrushin–Lanford–Ruelle equation, written in the elementary integrated form
`μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ` for measurable `A`. -/
def IsGibbs (β : ℝ) (μ : Measure Config) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ Λ : Finset Site, ∀ A : Set Config, MeasurableSet A →
      μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ

/-- Translation of a configuration by the lattice vector `j`. -/
def shift (j : Site) (σ : Config) : Config := fun i ↦ σ (i - j)

/-! ### The bridge to the `GibbsMeasure` library

Everything in this namespace is auxiliary: it identifies the definitions above with those of the
`GibbsMeasure` library.  None of the statements of the challenge is touched. -/

namespace Bridge

open scoped ENNReal
open MeasureTheory.GibbsMeasure (isingPotential latticeGraph isingSpecification
  uniformSpinMeasure GP)

/-- The library's Ising potential on `ℤ²` with coupling `1` and no external field. -/
abbrev P : Potential Site Bool := isingPotential (latticeGraph 2) 1 0

lemma P_eq : P = Potential.nearestNeighbourPair (latticeGraph 2) 1 0
    MeasureTheory.GibbsMeasure.spin := rfl

lemma spin_eq : spin = MeasureTheory.GibbsMeasure.spin := rfl

/-! #### Unit vectors and nearest-neighbour bonds -/

lemma e_self (k : Fin 2) : e k k = 1 := by simp [e]

lemma e_of_ne {k l : Fin 2} (h : l ≠ k) : e k l = 0 := by simp [e, h]

lemma add_e_ne_self (i : Site) (k : Fin 2) : i + e k ≠ i := by
  intro h
  have h1 := congrFun h k
  rw [Pi.add_apply, e_self] at h1
  omega

lemma e_inj {k m : Fin 2} (h : e k = e m) : k = m := by
  by_contra hkm
  have h1 := congrFun h k
  rw [e_self, e_of_ne hkm] at h1
  exact one_ne_zero h1

lemma adj_add_e (i : Site) (k : Fin 2) : (latticeGraph 2).Adj i (i + e k) := by
  show ∑ l, (i l - (i + e k) l).natAbs = 1
  rw [Finset.sum_eq_single k]
  · have h1 : i k - (i + e k) k = -1 := by rw [Pi.add_apply, e_self]; ring
    rw [h1]
    rfl
  · intro l _ hl
    have h1 : i l - (i + e k) l = 0 := by rw [Pi.add_apply, e_of_ne hl]; ring
    rw [h1]
    rfl
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma adj_decomp {i j : Site} (h : (latticeGraph 2).Adj i j) :
    ∃ k : Fin 2, j = i + e k ∨ i = j + e k := by
  classical
  have h1 : ∑ l, (i l - j l).natAbs = 1 := h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [h1]; exact one_ne_zero)
  have hk1 : (i k - j k).natAbs = 1 := by
    have hle : (i k - j k).natAbs ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun l ↦ (i l - j l).natAbs)
        (fun l _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    omega
  have herase : ∑ l ∈ Finset.univ.erase k, (i l - j l).natAbs = 0 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun l ↦ (i l - j l).natAbs) (Finset.mem_univ k)
    omega
  have hrest : ∀ l, l ≠ k → j l = i l := by
    intro l hl
    have hle : (i l - j l).natAbs ≤ ∑ m ∈ Finset.univ.erase k, (i m - j m).natAbs :=
      Finset.single_le_sum (f := fun m ↦ (i m - j m).natAbs) (fun m _ ↦ Nat.zero_le _)
        (Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩)
    omega
  refine ⟨k, ?_⟩
  rcases (by omega : j k = i k + 1 ∨ i k = j k + 1) with hjk | hjk
  · refine Or.inl (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl
      rw [Pi.add_apply, e_self, hjk]
    · rw [Pi.add_apply, e_of_ne hl, add_zero, hrest l hl]
  · refine Or.inr (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl
      rw [Pi.add_apply, e_self, hjk]
    · rw [Pi.add_apply, e_of_ne hl, add_zero, (hrest l hl).symm]

lemma pair_eq_pair {a b : Site} {k m : Fin 2}
    (h : ({a, a + e k} : Finset Site) = {b, b + e m}) : a = b ∧ k = m := by
  have ha : a ∈ ({b, b + e m} : Finset Site) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hak : a + e k ∈ ({b, b + e m} : Finset Site) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.1 ha with rfl | ha'
  · rcases Finset.mem_insert.1 hak with h1 | h1
    · exact absurd h1 (add_e_ne_self a k)
    · rw [Finset.mem_singleton] at h1
      exact ⟨rfl, e_inj (add_left_cancel h1)⟩
  · rw [Finset.mem_singleton] at ha'
    rcases Finset.mem_insert.1 hak with h1 | h1
    · exfalso
      have hz : e m + e k = 0 := by
        have h2 : b + (e m + e k) = b + 0 := by
          rw [← add_assoc, ← ha', h1, add_zero]
        exact add_left_cancel h2
      have h3 := congrFun hz k
      rw [Pi.add_apply, Pi.zero_apply, e_self] at h3
      rcases eq_or_ne k m with rfl | hkm
      · rw [e_self] at h3; omega
      · rw [e_of_ne hkm] at h3; omega
    · rw [Finset.mem_singleton] at h1
      exact absurd (h1.trans ha'.symm) (add_e_ne_self a k)

/-! #### The Hamiltonian -/

lemma P_pair (a : Site) (k : Fin 2) (σ : Config) :
    P {a, a + e k} σ = -(spin (σ a) * spin (σ (a + e k))) := by
  have hne : a ≠ a + e k := (add_e_ne_self a k).symm
  have hcard : ({a, a + e k} : Finset Site).card = 2 := Finset.card_pair hne
  have hadj : ∃ x ∈ ({a, a + e k} : Finset Site), ∃ y ∈ ({a, a + e k} : Finset Site),
      (latticeGraph 2).Adj x y :=
    ⟨a, Finset.mem_insert_self _ _, a + e k,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), adj_add_e a k⟩
  rw [P_eq, Potential.nearestNeighbourPair_apply_pair ⟨hcard, hadj⟩, Finset.prod_pair hne,
    ← spin_eq]
  ring

lemma exists_pair_of_P_ne_zero {Δ : Finset Site} (h : P Δ ≠ 0) :
    ∃ (a : Site) (k : Fin 2), Δ = {a, a + e k} := by
  classical
  by_cases h1 : Δ.card = 1
  · exact absurd (funext fun η ↦ by
      rw [P_eq, Potential.nearestNeighbourPair_apply_card_one h1]
      simp) h
  by_cases h2 : Δ.card = 2 ∧ ∃ x ∈ Δ, ∃ y ∈ Δ, (latticeGraph 2).Adj x y
  · obtain ⟨hcard, x, hx, y, hy, hxy⟩ := h2
    have hne : x ≠ y := (latticeGraph 2).ne_of_adj hxy
    have hsub : ({x, y} : Finset Site) ⊆ Δ := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
    have hΔ : Δ = {x, y} :=
      (Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (by rw [hcard, Finset.card_pair hne]))).symm
    obtain ⟨k, hk | hk⟩ := adj_decomp hxy
    · exact ⟨x, k, by rw [hΔ, hk]⟩
    · exact ⟨y, k, by rw [hΔ, hk, Finset.pair_comm]⟩
  · exact absurd (funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero (G := latticeGraph 2)
      (J := 1) (h := 0) (σ := MeasureTheory.GibbsMeasure.spin) h1 h2 η) h

lemma hamiltonian_P_eq (Λ : Finset Site) (σ : Config) :
    P.hamiltonian Λ σ = hamiltonian Λ σ := by
  classical
  have hmem : ∀ Δ ∈ (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)),
      ((Δ : Set Site) ∩ (Λ : Set Site)).Nonempty := by
    intro Δ hΔ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hΔ
    rcases (mem_bonds Λ p.1 p.2).1 hp with hp' | hp'
    · exact ⟨p.1, by simp, by simpa using hp'⟩
    · exact ⟨p.1 + e p.2, by simp, by simpa using hp'⟩
  have hsub : Potential.interactingSupport (Φ := P) Λ ⊆
      (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)) := by
    intro Δ hΔ
    obtain ⟨hne, hΦ⟩ := Potential.mem_interactingSupport.1 hΔ
    obtain ⟨a, k, rfl⟩ := exists_pair_of_P_ne_zero hΦ
    refine Finset.mem_image.2 ⟨(a, k), ?_, rfl⟩
    rw [mem_bonds]
    obtain ⟨x, hxΔ, hxΛ⟩ := hne
    have hxΔ' : x = a ∨ x = a + e k := by
      simpa using hxΔ
    rcases hxΔ' with rfl | rfl
    · exact Or.inl (by simpa using hxΛ)
    · exact Or.inr (by simpa using hxΛ)
  have hzero : ∀ Δ ∈ (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)),
      Δ ∉ Potential.interactingSupport (Φ := P) Λ → P Δ σ = 0 := by
    intro Δ hΔ hΔ'
    have := Potential.mem_interactingSupport (Φ := P) (Λ := Λ) (Δ := Δ)
    have hPz : P Δ = 0 := by
      by_contra hc
      exact hΔ' (this.2 ⟨hmem Δ hΔ, hc⟩)
    exact congrFun hPz σ
  have hinj : ∀ p ∈ bonds Λ, ∀ q ∈ bonds Λ,
      ({p.1, p.1 + e p.2} : Finset Site) = {q.1, q.1 + e q.2} → p = q := by
    intro p _ q _ hpq
    obtain ⟨h1, h2⟩ := pair_eq_pair hpq
    exact Prod.ext h1 h2
  rw [Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian,
    Finset.sum_subset hsub hzero, Finset.sum_image hinj, hamiltonian,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ P_pair p.1 p.2 σ

/-! #### The independent specification over the uniform spin measure -/

lemma glue_extend (Λ : Finset Site) (ζ : Λ → Bool) (ω : Config) :
    glue Λ (extend Λ ζ ω) ω = extend Λ ζ ω := by
  funext i
  by_cases h : i ∈ Λ <;> simp [glue, extend, h]

lemma juxt_eq_extend (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) :
    juxt (Λ : Set Site) ω ζ = extend Λ ζ ω := by
  funext i
  by_cases h : i ∈ Λ <;> simp [juxt, extend, h]

lemma uniformSpinMeasure_singleton (c : Bool) : uniformSpinMeasure {c} = 2⁻¹ := by
  show ((2 : ℝ≥0∞)⁻¹ • Measure.count) {c} = 2⁻¹
  rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

lemma pi_uniform_singleton (Λ : Finset Site) (ζ : Λ → Bool) :
    (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) {ζ} = (2 ^ Λ.card : ℝ≥0∞)⁻¹ := by
  rw [← Set.univ_pi_singleton ζ, Measure.pi_pi]
  simp only [uniformSpinMeasure_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [← ENNReal.inv_pow]

lemma isssd_eq (Λ : Finset Site) (ω : Config) :
    Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω
      = Measure.map (juxt (Λ : Set Site) ω) (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) := rfl

lemma lintegral_isssd (Λ : Finset Site) (ω : Config) {f : Config → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω)
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ * ∑ ζ : Λ → Bool, f (extend Λ ζ ω) := by
  rw [isssd_eq, lintegral_map hf Measurable.juxt, lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [pi_uniform_singleton, juxt_eq_extend, mul_comm]

/-! #### Identification of the finite-volume kernels -/

lemma inv_mul_cancel_aux {c s x : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹ s⁻¹, mul_assoc,
    ← mul_assoc c⁻¹ c x, ENNReal.inv_mul_cancel hc0 hct, one_mul]

lemma boltzmann_extend (β : ℝ) (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) :
    P.boltzmannFactor β Λ (extend Λ ζ ω) = ENNReal.ofReal (weight β Λ ω ζ) := by
  rw [Potential.boltzmannFactor, hamiltonian_P_eq, weight, glue_extend]

lemma gibbsMeasure_apply (β : ℝ) (Λ : Finset Site) (ω : Config) {A : Set Config}
    (hA : MeasurableSet A) :
    gibbsMeasure β Λ ω A
      = (∑ ζ : Λ → Bool, ENNReal.ofReal (weight β Λ ω ζ))⁻¹ *
        ∑ ζ : Λ → Bool,
          A.indicator (fun _ ↦ ENNReal.ofReal (weight β Λ ω ζ)) (extend Λ ζ ω) := by
  rw [gibbsMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, partitionFunction,
    ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun ζ : Λ → Bool ↦ weight β Λ ω ζ) (fun ζ _ ↦ (Real.exp_pos _).le)]
  refine congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, glue_extend]
  by_cases hx : extend Λ ζ ω ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

lemma spec_apply (β : ℝ) (Λ : Finset Site) (ω : Config) {A : Set Config} (hA : MeasurableSet A) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω A = gibbsMeasure β Λ ω A := by
  classical
  have hc0 : (2 ^ Λ.card : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hct : (2 ^ Λ.card : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hZ : Specification.premodifierZ (S := Site) (E := Bool) uniformSpinMeasure
      (P.boltzmannFactor β) Λ ω
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ * ∑ ζ : Λ → Bool, ENNReal.ofReal (weight β Λ ω ζ) := by
    rw [Specification.premodifierZ,
      lintegral_isssd Λ ω (Potential.measurable_boltzmannFactor (Φ := P) β Λ)]
    exact congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ boltzmann_extend β Λ ω ζ)
  have hnum : ∫⁻ y in A, P.boltzmannFactor β Λ y
        ∂(Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω)
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ *
        ∑ ζ : Λ → Bool,
          A.indicator (fun _ ↦ ENNReal.ofReal (weight β Λ ω ζ)) (extend Λ ζ ω) := by
    rw [← lintegral_indicator hA,
      lintegral_isssd Λ ω
        ((Potential.measurable_boltzmannFactor (Φ := P) β Λ).indicator hA)]
    refine congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ ?_)
    by_cases hx : extend Λ ζ ω ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact boltzmann_extend β Λ ω ζ
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [isingSpecification, Potential.gibbsSpecificationOfAbsolutelySummable,
    Specification.modification_apply,
    Specification.withDensity_premodifierNorm_apply uniformSpinMeasure
      (Potential.isPremodifier_boltzmannFactor (Φ := P) β) hA ω,
    hZ, hnum, gibbsMeasure_apply β Λ ω hA]
  exact inv_mul_cancel_aux hc0 hct

lemma spec_eq (β : ℝ) (Λ : Finset Site) (ω : Config) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω = gibbsMeasure β Λ ω :=
  Measure.ext fun _ hA ↦ spec_apply β Λ ω hA

/-! #### The DLR equation -/

lemma dlr_iff (β : ℝ) (μ : Measure Config) [IsProbabilityMeasure μ] :
    (∀ Λ : Finset Site, ∀ A : Set Config, MeasurableSet A →
        μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ)
      ↔ Specification.IsGibbsMeasure (isingSpecification (latticeGraph 2) 1 0 β) μ := by
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  constructor
  · intro h Λ
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA
      (((isingSpecification (latticeGraph 2) 1 0 β Λ).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable)]
    calc ∫⁻ a, (isingSpecification (latticeGraph 2) 1 0 β Λ a) A ∂μ
        = ∫⁻ a, gibbsMeasure β Λ a A ∂μ := lintegral_congr fun a ↦ spec_apply β Λ a hA
      _ = μ A := (h Λ A hA).symm
  · intro h Λ A hA
    have h1 : μ.bind (isingSpecification (latticeGraph 2) 1 0 β Λ) A = μ A := by rw [h Λ]
    rw [Measure.bind_apply hA
      (((isingSpecification (latticeGraph 2) 1 0 β Λ).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable)] at h1
    calc μ A = ∫⁻ a, (isingSpecification (latticeGraph 2) 1 0 β Λ a) A ∂μ := h1.symm
      _ = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ := lintegral_congr fun a ↦ spec_apply β Λ a hA

lemma isGibbs_of_mem_GP (β : ℝ) (m : ProbabilityMeasure Config)
    (hm : m ∈ GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β)) :
    IsGibbs β (m : Measure Config) :=
  ⟨inferInstance, (dlr_iff β (m : Measure Config)).2 hm⟩

lemma mem_GP_of_isGibbs (β : ℝ) (μ : Measure Config) (h : IsGibbs β μ) :
    (⟨μ, h.1⟩ : ProbabilityMeasure Config) ∈
      GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β) := by
  have := h.1
  exact (dlr_iff β μ).1 h.2

/-! #### The lattice shifts and the spin flip -/

lemma shift_eq (j : Site) : (MeasureTheory.GibbsMeasure.shift Bool j).toFun = shift j :=
  funext fun ω ↦ funext fun i ↦ MeasureTheory.GibbsMeasure.shift_toFun_apply j ω i

lemma spinFlip_eq :
    MeasureTheory.GibbsMeasure.Peierls.spinFlip.toFun = fun (σ : Config) (i : Site) ↦ !σ i := rfl

end Bridge

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), the "in particular" half: the two-dimensional Ising phase
transition.** There is an inverse temperature `β₀` such that for every `β ≥ β₀` the two-dimensional
Ising ferromagnet admits two *distinct* Gibbs measures `μ₊` and `μ₋`, both invariant under all
lattice translations, exchanged by the global spin flip, and exhibiting spontaneous magnetisation:
the expected spin at the origin is strictly negative under `μ₋` and strictly positive under `μ₊`. -/
theorem ising_phase_transition :
    ∃ β₀ : ℝ, ∀ β ≥ β₀, ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      μp ≠ μm ∧
      (∀ j : Site, μp.map (shift j) = μp) ∧
      (∀ j : Site, μm.map (shift j) = μm) ∧
      μm = μp.map (fun σ i ↦ !σ i) ∧
      ∫ σ, spin (σ 0) ∂μm < 0 ∧
      0 < ∫ σ, spin (σ 0) ∂μp := by
  obtain ⟨b₀, h⟩ := MeasureTheory.GibbsMeasure.Peierls.exists_spontaneous_magnetisation
  refine ⟨b₀, fun β hβ ↦ ?_⟩
  obtain ⟨mp, mm, hne, hp, hm, hsp, hsm, hmap, hlt, hgt⟩ := h β hβ
  refine ⟨(mp : Measure Config), (mm : Measure Config),
    Bridge.isGibbs_of_mem_GP β mp hp, Bridge.isGibbs_of_mem_GP β mm hm,
    fun hcon ↦ hne (ProbabilityMeasure.toMeasure_injective hcon), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [← Bridge.shift_eq j]
    exact (hsp j).map_eq
  · intro j
    rw [← Bridge.shift_eq j]
    exact (hsm j).map_eq
  · rw [hmap, ← Bridge.spinFlip_eq]
  · exact hlt
  · exact hgt

/-- **The Dobrushin half: uniqueness at high temperature.** When the inverse temperature is small
enough — Dobrushin's condition holds for the two-dimensional Ising model as soon as `β < 1 / 4`,
since every site has four neighbours — the Gibbs measure is unique. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν := by
  intro β hβ0 hβ μ ν hμ hν
  have habs : |β| < 1 / 4 := by rwa [abs_of_nonneg hβ0]
  have h := MeasureTheory.GibbsMeasure.subsingleton_GP_ising2D_of_abs_lt habs
    (Bridge.mem_GP_of_isGibbs β μ hμ) (Bridge.mem_GP_of_isGibbs β ν hν)
  exact congrArg (fun m : ProbabilityMeasure Config ↦ (m : Measure Config)) h

end IsingChallenge

end
