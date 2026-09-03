/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.InvariantExistenceGroup
public import GibbsMeasure.Specification.Pressure
public import GibbsMeasure.Specification.SpecificEntropy
public import GibbsMeasure.Mathlib.Topology.Instances.EReal
public import GibbsMeasure.Mathlib.Data.Finset.Map

/-!
# The variational principle (Georgii §15.3 end, §15.4)

Throughout, `S = ℤ^d` is spelled `ι → ℤ` for a finite type `ι`, `λ` is an a priori *probability*
measure `ν` on `E` (Georgii normalises his finite `λ` in every proof of this section), and `Φ` is
an absolutely summable potential (`Potential.IsAbsolutelySummable`, Georgii's `ℬ`), shift
invariant (`Potential.IsShiftInvariant`) for the lattice statements: Georgii's `ℬ_Θ`.

The two inputs are §15.2 (`Specification/SpecificEntropy.lean`: `relativeEntropyIn`, `entropyIn`,
`specificEntropy`, Theorem (15.12)) and §15.3 (`Specification/Pressure.lean`: `specificEnergy`,
`logZ`, `pressure`, Theorems (15.23) and (15.30)(a)).

## Main definitions

* `Potential.gibbsDensityIn Φ ν Λ ω`, Georgii's `ρ^Φ_Λ(σ_Λ ω_{S∖Λ}) = e^{−H^Φ_Λ}/Z^Φ_Λ(ω)`: the
  density of `γ^Φ_Λ(·|ω)` with respect to `λ^S` on the cylinder σ-algebra `𝓕_Λ`.
* `Potential.specificRelativeEntropy Φ ν μ`, **Georgii (15.32)**: the specific relative entropy
  `𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)`, an `EReal`.

## Main results

* `Potential.relativeEntropyIn_gibbsSpecification_eq`, **Georgii (15.34)**:
  `𝓗_Λ(μ | γ^Φ_Λ(·|ω)) = −𝓗_Λ(μ) + μ(H^Φ_Λ(σ_Λ ω_{S∖Λ})) + log Z^Φ_Λ(ω)`.
* `Potential.relativeEntropyIn_bind_le_add`, **Georgii Lemma (15.28)**, quantitative form:
  `𝓗_Λ(μ | ρ γ^Φ_Λ) ≤ 𝓗_Λ(μ | ρ' γ^Φ_Λ) + 2 r(Λ, Φ)` for any two probability measures `ρ, ρ'`;
  `Potential.tendsto_relativeEntropyIn_bind_div_card_congr` is Lemma (15.28) as stated (the two
  limits exist together and agree). Georgii's `r(Λ, Φ)` is sharpened throughout to
  `2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` (`Potential.tail`).
* `Potential.tendsto_relativeEntropyIn_gibbsSpecification_div_card_zero`, **Georgii (15.33)**:
  `|Λ_j|⁻¹ 𝓗_{Λ_j}(μ | γ^Φ_{Λ_j}(·|ω_j)) → 0` for `μ ∈ 𝒢(Φ)` — shift invariance of `μ` is not
  needed, Georgii uses it only to produce a Gibbs measure in `𝒢_Θ(Φ)`.
* `Potential.tendsto_relativeEntropyIn_div_card`, **Georgii Theorem (15.30)(b)**: for `μ ∈ 𝓟_Θ`
  and *any* `ρ ∈ 𝒢(Φ)`, `|Λ_j|⁻¹ 𝓗_{Λ_j}(μ | ρ) → 𝓀(μ|Φ)`.
* `Potential.specificRelativeEntropy_nonneg` and `Potential.specificRelativeEntropy_eq_zero`,
  **Georgii Corollary (15.35)**: `𝓀(·|Φ) ≥ 0` on `𝓟_Θ`, with equality on `𝒢_Θ(Φ)`.
* `MeasureTheory.GibbsMeasure.isGibbsMeasure_of_tendsto_relativeEntropyIn_div_card`,
  **Georgii Theorem (15.37)**: a shift-invariant `μ` whose finite-volume relative entropies with
  respect to a shift-invariant `ν ∈ 𝒢(γ)` are `o(|Λ_j|)` is itself a Gibbs measure for the
  quasilocal specification `γ`.
* `Potential.specificRelativeEntropy_eq_zero_iff_mem_invariantG`, **Georgii Theorem (15.39)**,
  the variational principle: `𝓀(μ|Φ) = 0 ↔ μ ∈ 𝒢_Θ(Φ)`; equivalently
  (`Potential.specificEntropy_le_specificEnergy_add_pressure`,
  `Potential.specificEntropy_eq_specificEnergy_add_pressure`) the specific free energy
  `⟨·, Φ⟩ − 𝓀(·)` attains its minimum `−P(Φ)` exactly on `𝒢_Θ(Φ)`.
* `Potential.invariantG_gibbsSpecification_shiftGroup_nonempty` (**Georgii Theorem (4.23)(a) and
  Corollary (5.16)**, proved in `GibbsMeasure/Specification/InvariantExistenceGroup.lean`) gives
  `𝒢_Θ(Φ) ≠ ∅` over a standard Borel state space, so
  `Potential.specificRelativeEntropy_eq_zero_iff_mem_invariantG'` and
  `Potential.specificEntropy_eq_specificEnergy_add_pressure_iff_mem_invariantG` are (15.39) and
  its free-energy form with no hypothesis beyond `[StandardBorelSpace E]`.

## Hypotheses of the two directions of (15.39)

`←` (`Potential.specificRelativeEntropy_eq_zero_of_mem_invariantG`, Corollary (15.35)) needs only
`Φ` shift invariant and absolutely summable and `μ ∈ 𝒢_Θ(Φ)`. Nothing is assumed on `(E, ℰ)`.

`→` (`Potential.mem_invariantG_of_specificRelativeEntropy_eq_zero`) needs, in addition, that
**`𝒢_Θ(Φ)` be nonempty**: a shift-invariant Gibbs measure `ρ` is a hypothesis of the theorem.
No other hypothesis on `E` is used, so that form applies whenever a shift-invariant Gibbs measure
is known by other means. Georgii produces `ρ` from Theorem (4.23) and Corollary (5.16), which need
`(E, ℰ)` to be standard Borel; that is
`Potential.invariantG_gibbsSpecification_shiftGroup_nonempty`, and it turns the primed
statements `Potential.mem_invariantG_of_specificRelativeEntropy_eq_zero'`,
`Potential.specificRelativeEntropy_eq_zero_iff_mem_invariantG'` and
`Potential.specificEntropy_eq_specificEnergy_add_pressure_iff_mem_invariantG` into unconditional
theorems over a standard Borel `E`.

## Proof of (15.37)

Georgii's three steps are three separate theorems, at the level of an arbitrary quasilocal
specification wherever possible.

* Step 1 is `MeasureTheory.GibbsMeasure.exists_subset_relativeEntropyIn_sub_le`: for a cube
  `C = [−R, R]^d ⊇ Λ` and `δ > 0` there is a `Δ ⊇ C` with
  `𝓗_Δ(μ|ν) − 𝓗_{Δ∖Λ}(μ|ν) ≤ δ`. The box `Λ_N = [0, N(2R+1) − 1]^d` is tiled *exactly* by the
  `N^d` translates of `C`; the increments telescope by monotonicity (15.5)(c)
  (`exists_sub_le_div_of_pairwise_disjoint`), so one of them is at most `𝓗_{Λ_N}(μ|ν)/N^d`, and
  the shift invariance of `μ` and `ν` translates it back to `Δ`.
* Step 2 is `MeasureTheory.GibbsMeasure.exists_density_of_relativeEntropyIn_sub_le`: with
  `g = dμ/dν` on `𝓕_{Δ∖Λ}`, the chain rule `klDiv_withDensity_rnDeriv_add_klDiv_trim`
  (Georgii (15.38)) identifies `𝓗_Δ(μ|ν) − 𝓗_{Δ∖Λ}(μ|ν)` with `𝓗_Δ(μ | g ν)`, and
  `abs_measureReal_sub_measureReal_le_of_klDiv` turns a small relative entropy into a small total
  variation. Georgii's modulus is used, not Csiszár's `‖p − q‖₁² ≤ 2 𝓗(p|q)`: for each `ε > 0`
  there is `r` with `|x − 1| ≤ r ψ(x) + ε` on `[0, ∞)`
  (`InformationTheory.exists_abs_sub_one_le_mul_klFun_add`).
* Step 3 is `MeasureTheory.GibbsMeasure.isGibbsMeasure_of_forall_exists_density`, stated over an
  arbitrary site set: it only needs the conclusion of Steps 1–2 as a hypothesis. Georgii's local
  approximant of `γ_Λ 1_A` is made `𝓕_{S∖Λ}`-measurable by freezing the spins inside `Λ`
  (`exists_measurable_cylinderEvents_sdiff_of_isQuasilocal`), and the whole estimate is run on
  measurable cylinders in `ℝ≥0∞`, so that the Gibbs property of `ν` enters through the properness
  identity `Specification.lintegral_mul`.

## General lemmas that belong in Mathlib

`EReal.tendsto_of_le_add_coe` (`Mathlib/Topology/Instances/EReal/Lemmas.lean`);
`Finset.map_addRightEmbedding_map`, `Finset.map_addRightEmbedding_neg`
(`Mathlib/Data/Finset/Image.lean`); `MeasureTheory.Measure.rnDeriv_le_of_le_smul`
(`Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`);
`InformationTheory.klDiv_withDensity_add_integral_log`,
`InformationTheory.klDiv_le_klDiv_add_ofReal_log_of_le_smul`,
`InformationTheory.klDiv_le_ofReal_log_of_le_smul`,
`InformationTheory.abs_measureReal_sub_measureReal_le_of_klDiv`
(`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`),
`InformationTheory.exists_abs_sub_one_le_mul_klFun_add`
(`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`),
`InformationTheory.klDiv_withDensity_rnDeriv_add_klDiv_trim`
(`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`); and, inside this library,
`MeasureTheory.measurable_cylinderEvents_juxt_restrict`,
`MeasureTheory.preimage_juxt_restrict_eq` (`GibbsMeasure/Prereqs/Juxt.lean`) and
`MeasureTheory.isssd_eq_map_juxt_restrict` (`GibbsMeasure/Specification.lean`, next to
`Specification.isssd_apply_of_mem_cylinderEvents`).

## Not in this file

Georgii's Example (15.40) (the variational characterisation of a homogeneous Markov chain on `ℤ`,
which needs Proposition (15.16) and formula (15.19)), and the consequences drawn at the end of
§15.4 from Theorem (15.20), Proposition (16.1) and (4.23).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Topology
open InformationTheory Real
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Missing general lemmas -/

/-- **The averaging step in Georgii's proof of Theorem (15.37), Step 1.** Let `h` be a monotone
set function vanishing on `∅`, let `C i` be pairwise disjoint finite volumes and `Λ i ⊆ C i`. With
`W j = C 0 ∪ … ∪ C (j-1)`, the increments `h (W (i+1)) − h (W (i+1) ∖ Λ i)` are dominated by the
telescoping increments `h (W (i+1)) − h (W i)`, whose sum is `h (W p)`; so one of the `p`
increments is at most the average `h (W p) / p`. -/
private lemma exists_sub_le_div_of_pairwise_disjoint {S : Type*} [DecidableEq S]
    {h : Finset S → ℝ} (hmono : Monotone h) (hempty : h ∅ = 0)
    {p : ℕ} (hp : 0 < p) {C Λ : ℕ → Finset S} (hΛC : ∀ i, Λ i ⊆ C i)
    (hdisj : Pairwise fun i j ↦ Disjoint (C i) (C j)) :
    ∃ i < p, h ((range (i + 1)).biUnion C) - h ((range (i + 1)).biUnion C \ Λ i)
      ≤ h ((range p).biUnion C) / p := by
  set W : ℕ → Finset S := fun j ↦ (range j).biUnion C with hW
  have hWmono : Monotone W := fun a b hab ↦
    biUnion_subset_biUnion_of_subset_left _ (Finset.range_subset_range.2 hab)
  have hdisjW : ∀ i, Disjoint (W i) (C i) := fun i ↦ by
    rw [hW]
    exact (Finset.disjoint_biUnion_left _ _ _).2 fun j hj ↦
      hdisj (Nat.ne_of_lt (Finset.mem_range.1 hj))
  have hkey : ∀ i, W i ⊆ W (i + 1) \ Λ i := fun i ↦ by
    intro x hx
    refine Finset.mem_sdiff.2 ⟨hWmono (Nat.le_succ i) hx, fun hxΛ ↦ ?_⟩
    exact (Finset.disjoint_left.1 (hdisjW i) hx) (hΛC i hxΛ)
  set x : ℕ → ℝ := fun i ↦ h (W (i + 1)) - h (W (i + 1) \ Λ i) with hx
  have hxle : ∀ i, x i ≤ h (W (i + 1)) - h (W i) := fun i ↦ by
    simp only [hx]
    exact sub_le_sub_left (hmono (hkey i)) _
  have hsum : ∑ i ∈ range p, x i ≤ h (W p) := by
    calc ∑ i ∈ range p, x i ≤ ∑ i ∈ range p, (h (W (i + 1)) - h (W i)) :=
          Finset.sum_le_sum fun i _ ↦ hxle i
      _ = h (W p) - h (W 0) := Finset.sum_range_sub (fun j ↦ h (W j)) p
      _ = h (W p) := by simp [hW, hempty]
  obtain ⟨i, hi, hile⟩ := Finset.exists_le_of_sum_le ⟨0, mem_range.2 hp⟩
    (f := x) (g := fun _ ↦ h (W p) / p) (by
      rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ (by positivity)]
      exact hsum)
  exact ⟨i, mem_range.1 hi, hile⟩

/-! ### Resampling inside a finite volume -/

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

end MeasureTheory


/-! ### Georgii Theorem (15.37): Steps 1 and 2 -/

namespace MeasureTheory.GibbsMeasure

section Step1

variable {E : Type*} [MeasurableSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ ν : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Georgii, Step 1 in the proof of Theorem (15.37).** -/
theorem exists_subset_relativeEntropyIn_sub_le
    (hμ : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun μ μ)
    (hν : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun ν ν)
    (hfin : ∀ D : Finset (ι → ℤ), relativeEntropyIn (D : Set (ι → ℤ)) μ ν ≠ ∞)
    (Λ : Finset (ι → ℤ)) (R : ℕ)
    (hΛ : Λ ⊆ Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)))
    {δ : ℝ} {N : ℕ} (hN : 0 < N)
    (hB : (relativeEntropyIn
        (↑(Icc (0 : ι → ℤ) fun _ ↦ (N : ℤ) * (2 * (R : ℤ) + 1) - 1) : Set (ι → ℤ)) μ ν).toReal
      ≤ δ * (N : ℝ) ^ Fintype.card ι) :
    ∃ Δ : Finset (ι → ℤ), Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) ⊆ Δ ∧
      (relativeEntropyIn (Δ : Set (ι → ℤ)) μ ν).toReal
        - (relativeEntropyIn ((Δ \ Λ : Finset (ι → ℤ)) : Set (ι → ℤ)) μ ν).toReal ≤ δ := by
  classical
  set c : ℤ := 2 * (R : ℤ) + 1 with hcdef
  have hcpos : 0 < c := by positivity
  set C₀ : Finset (ι → ℤ) := Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) with hC₀
  set T : Finset (ι → ℤ) := Icc (0 : ι → ℤ) (fun _ ↦ (N : ℤ) - 1) with hT
  set B : Finset (ι → ℤ) := Icc (0 : ι → ℤ) (fun _ ↦ (N : ℤ) * c - 1) with hBdef
  set p : ℕ := #T with hp
  have hpN : p = N ^ Fintype.card ι := by rw [hp, hT, Pi.card_Icc]; simp [Int.card_Icc]
  have hppos : 0 < p := by rw [hpN]; positivity
  set h : Finset (ι → ℤ) → ℝ := fun D ↦ (relativeEntropyIn (D : Set (ι → ℤ)) μ ν).toReal with hh
  have hmono : Monotone h := fun D D' hDD' ↦
    ENNReal.toReal_mono (hfin D') (relativeEntropyIn_mono (by exact_mod_cast hDD'))
  have hempty : h ∅ = 0 := by simp [hh]
  have hshift : ∀ (D : Finset (ι → ℤ)) (i : ι → ℤ),
      h (D.map (addRightEmbedding i)) = h D := by
    intro D i
    simp only [hh]
    congr 1
    rw [Finset.coe_map]
    have : ⇑(addRightEmbedding i) = fun x : ι → ℤ ↦ x + i := rfl
    rw [this]
    exact relativeEntropyIn_image_add hμ hν _ i
  -- the enumeration of the translation vectors
  set ee : Fin p ≃ {x // x ∈ T} := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm with hee
  set vv : ℕ → (ι → ℤ) := fun i ↦ if hi : i < p then ((ee ⟨i, hi⟩ : {x // x ∈ T}) : ι → ℤ) else 0
    with hvv
  have hvT : ∀ i, i < p → vv i ∈ T := by
    intro i hi; simp only [hvv, hi, ↓reduceDIte]; exact (ee ⟨i, hi⟩).2
  have hvinj : ∀ i j, i < p → j < p → vv i = vv j → i = j := by
    intro i j hi hj hij
    simp only [hvv, hi, hj, ↓reduceDIte] at hij
    have := ee.injective (Subtype.ext hij)
    exact congrArg Fin.val this
  set w : ℕ → (ι → ℤ) := fun i ↦ fun k ↦ c * vv i k + (R : ℤ) with hw
  set Cf : ℕ → Finset (ι → ℤ) := fun i ↦ if i < p then C₀.map (addRightEmbedding (w i)) else ∅
    with hCf
  set Lf : ℕ → Finset (ι → ℤ) := fun i ↦ if i < p then Λ.map (addRightEmbedding (w i)) else ∅
    with hLf
  have hCfmem : ∀ i, i < p → Cf i = Icc (fun k ↦ c * vv i k) (fun k ↦ c * vv i k + c - 1) := by
    intro i hi
    simp only [hCf, hi, ↓reduceIte, hC₀, Finset.map_add_right_Icc]
    congr 1 <;> (funext k; simp only [hw, hcdef, Pi.add_apply]; ring)
  have hΛC : ∀ i, Lf i ⊆ Cf i := by
    intro i
    by_cases hi : i < p
    · simp only [hCf, hLf, hi, ↓reduceIte]
      exact Finset.map_subset_map.2 hΛ
    · simp [hCf, hLf, hi]
  have hdisj : Pairwise fun i j ↦ Disjoint (Cf i) (Cf j) := by
    intro i j hij
    by_cases hi : i < p
    swap; · simp [hCf, hi]
    by_cases hj : j < p
    swap; · simp [hCf, hj]
    rw [hCfmem i hi, hCfmem j hj]
    have hne : vv i ≠ vv j := fun hc ↦ hij (hvinj i j hi hj hc)
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx hx'
    have h1 : c * vv i k ≤ x k := Pi.le_def.1 hx.1 k
    have h2 : x k ≤ c * vv i k + c - 1 := Pi.le_def.1 hx.2 k
    have h3 : c * vv j k ≤ x k := Pi.le_def.1 hx'.1 k
    have h4 : x k ≤ c * vv j k + c - 1 := Pi.le_def.1 hx'.2 k
    rcases lt_trichotomy (vv i k) (vv j k) with hlt | heq | hgt
    · have h5 : vv i k + 1 ≤ vv j k := hlt
      nlinarith
    · exact hk heq
    · have h5 : vv j k + 1 ≤ vv i k := hgt
      nlinarith
  have hCB : ∀ i, i < p → Cf i ⊆ B := by
    intro i hi
    rw [hCfmem i hi, hBdef]
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    have hvi := hvT i hi
    rw [hT, Finset.mem_Icc] at hvi
    refine ⟨Pi.le_def.2 fun k ↦ ?_, Pi.le_def.2 fun k ↦ ?_⟩
    · have hb1 : (0 : ℤ) ≤ vv i k := Pi.le_def.1 hvi.1 k
      have hb2 := Pi.le_def.1 hx.1 k
      have : (0 : ι → ℤ) k = 0 := rfl
      rw [this]
      nlinarith
    · have hb1 : vv i k ≤ (N : ℤ) - 1 := Pi.le_def.1 hvi.2 k
      have hb2 := Pi.le_def.1 hx.2 k
      nlinarith
  obtain ⟨i, hip, hile⟩ := exists_sub_le_div_of_pairwise_disjoint hmono hempty hppos hΛC hdisj
  set W : Finset (ι → ℤ) := (range (i + 1)).biUnion Cf with hWdef
  have hWB : (range p).biUnion Cf ⊆ B :=
    Finset.biUnion_subset.2 fun j hj ↦ hCB j (mem_range.1 hj)
  have hbound : h ((range p).biUnion Cf) / p ≤ δ := by
    have h1 : h ((range p).biUnion Cf) ≤ h B := hmono hWB
    have h2 : h B ≤ δ * p := by
      rw [hpN]; push_cast; exact hB
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < p)]
    linarith
  refine ⟨W.map (addRightEmbedding (-(w i))), ?_, ?_⟩
  · have h1 : Cf i ⊆ W := Finset.subset_biUnion_of_mem Cf (mem_range.2 (Nat.lt_succ_self i))
    have h2 : (Cf i).map (addRightEmbedding (-(w i))) = C₀ := by
      simp only [hCf, hip, ↓reduceIte]
      exact Finset.map_addRightEmbedding_neg _ _
    rw [← h2]
    exact Finset.map_subset_map.2 h1
  · have hLmap : (Lf i).map (addRightEmbedding (-(w i))) = Λ := by
      simp only [hLf, hip, ↓reduceIte]
      exact Finset.map_addRightEmbedding_neg _ _
    have hsd : W.map (addRightEmbedding (-(w i))) \ Λ
        = (W \ Lf i).map (addRightEmbedding (-(w i))) := by
      rw [Finset.map_sdiff, hLmap]
    change h (W.map (addRightEmbedding (-(w i))))
      - h (W.map (addRightEmbedding (-(w i))) \ Λ) ≤ δ
    rw [hsd, hshift, hshift]
    exact hile.trans hbound

end Step1

section Step2

variable {S E : Type*} [MeasurableSpace E] {μ ν : Measure (S → E)}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Georgii, Step 2 in the proof of Theorem (15.37).** -/
theorem exists_density_of_relativeEntropyIn_sub_le (Λ Δ : Set S)
    (hfin : relativeEntropyIn Δ μ ν ≠ ∞)
    {r ε δ : ℝ} (hr : ∀ x : ℝ, 0 ≤ x → |x - 1| ≤ r * klFun x + ε) (hr0 : 0 ≤ r)
    (hδ : (relativeEntropyIn Δ μ ν).toReal - (relativeEntropyIn (Δ \ Λ) μ ν).toReal ≤ δ) :
    ∃ g : (S → E) → ℝ≥0∞, Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ \ Λ)] g ∧
      IsProbabilityMeasure (ν.withDensity g) ∧
      (ν.withDensity g).trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Δ \ Λ))
        = μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Δ \ Λ)) ∧
      (∀ A, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Δ] A →
        |μ.real A - (ν.withDensity g).real A| ≤ r * δ + ε) := by
  have hsub : cylinderEvents (X := fun _ : S ↦ E) (Δ \ Λ)
      ≤ cylinderEvents (X := fun _ : S ↦ E) Δ := cylinderEvents_mono Set.sdiff_subset
  set hleΔ := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Δ) with hleΔdef
  set hleD := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Δ \ Λ) with hleDdef
  have hfinD : relativeEntropyIn (Δ \ Λ) μ ν ≠ ∞ :=
    ne_top_of_le_ne_top hfin (relativeEntropyIn_mono Set.sdiff_subset)
  have hac : μ.trim hleD ≪ ν.trim hleD := by
    by_contra hc
    exact hfinD (klDiv_of_not_ac hc)
  set g : (S → E) → ℝ≥0∞ := (μ.trim hleD).rnDeriv (ν.trim hleD) with hgdef
  have hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ \ Λ)] g :=
    (μ.trim hleD).measurable_rnDeriv (ν.trim hleD)
  have htrimD : (ν.withDensity g).trim hleD = μ.trim hleD := by
    rw [trim_withDensity hleD hg, hgdef, Measure.withDensity_rnDeriv_eq _ _ hac]
  have hprob : IsProbabilityMeasure (ν.withDensity g) := by
    refine ⟨?_⟩
    rw [← trim_measurableSet_eq hleD MeasurableSet.univ, htrimD,
      trim_measurableSet_eq hleD MeasurableSet.univ, measure_univ]
  refine ⟨g, hg, hprob, htrimD, fun A hA ↦ ?_⟩
  · have hgΔ : Measurable[cylinderEvents (X := fun _ : S ↦ E) Δ] g := hg.mono hsub le_rfl
    have htt : ∀ ρ : Measure (S → E), (ρ.trim hleΔ).trim hsub = ρ.trim hleD :=
      fun ρ ↦ trim_trim
    have hchain : klDiv (μ.trim hleΔ) ((ν.trim hleΔ).withDensity g)
        + relativeEntropyIn (Δ \ Λ) μ ν = relativeEntropyIn Δ μ ν := by
      have hac2 : (μ.trim hleΔ).trim hsub ≪ (ν.trim hleΔ).trim hsub := by
        rw [htt, htt]; exact hac
      have hkey := klDiv_withDensity_rnDeriv_add_klDiv_trim (μ := μ.trim hleΔ)
        (ν := ν.trim hleΔ) hsub hac2
      rw [htt, htt] at hkey
      exact hkey
    set a := klDiv (μ.trim hleΔ) ((ν.trim hleΔ).withDensity g) with hadef
    have hane : a ≠ ∞ := by
      refine ne_top_of_le_ne_top hfin ?_
      rw [← hchain]
      exact le_self_add
    have hale : a.toReal ≤ δ := by
      have h1 : a.toReal + (relativeEntropyIn (Δ \ Λ) μ ν).toReal
          = (relativeEntropyIn Δ μ ν).toReal := by
        rw [← ENNReal.toReal_add hane hfinD, hchain]
      linarith
    have hprobwd : IsProbabilityMeasure ((ν.trim hleΔ).withDensity g) := by
      rw [← trim_withDensity hleΔ hgΔ]
      exact isProbabilityMeasure_trim hleΔ
    have hbound := abs_measureReal_sub_measureReal_le_of_klDiv (p := μ.trim hleΔ)
      (q := (ν.trim hleΔ).withDensity g) hr hane A
    have hμA : (μ.trim hleΔ).real A = μ.real A := by
      simp only [measureReal_def, trim_measurableSet_eq hleΔ hA]
    have hqA : ((ν.trim hleΔ).withDensity g).real A = (ν.withDensity g).real A := by
      rw [← trim_withDensity hleΔ hgΔ]
      simp only [measureReal_def, trim_measurableSet_eq hleΔ hA]
    rw [hμA, hqA] at hbound
    refine hbound.trans ?_
    have : r * a.toReal ≤ r * δ := mul_le_mul_of_nonneg_left hale hr0
    linarith

end Step2

section Step3

variable {S E : Type*} [MeasurableSpace E]

/-- The indicator of a set is `𝓕_D`-measurable as soon as the set is. -/
lemma measurable_coeFn_indicatorLp {m : MeasurableSpace (S → E)} {A : Set (S → E)}
    (hA : MeasurableSet[m] A) : Measurable[m] (indicatorLp (S := S) (E := E) A) := by
  rw [coeFn_indicatorLp]
  exact (measurable_const (a := (1 : ℝ))).indicator hA

lemma indicatorLp_mem_localFunctionsOn {D : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (D : Set S)] A) :
    indicatorLp A ∈ localFunctionsOn S E D :=
  measurable_coeFn_indicatorLp hA

lemma action_indicatorLp_apply (γ : Specification S E) (Λ : Finset S) {A : Set (S → E)}
    (hA : MeasurableSet A) (ω : S → E) :
    (Specification.action γ Λ (indicatorLp A) : (S → E) → ℝ) ω = (γ Λ ω A).toReal := by
  rw [Specification.action_apply, coeFn_indicatorLp]
  rw [show (fun _ : S → E ↦ (1 : ℝ)) = (1 : (S → E) → ℝ) from rfl,
    MeasureTheory.integral_indicator_one hA, measureReal_def]

/-- **Georgii, in Step 3 of the proof of (15.37).** For a quasilocal specification, the function
`γ_Λ 1_A` is uniformly approximated, within any `ε > 0`, by a bounded observable measurable for
the cylinder σ-algebra of `C ∖ Λ` for some finite `C`. Georgii takes a local approximant `g̃` of
`γ_Λ g` and notes that it may be taken `𝓕_{S∖Λ}`-measurable; here this is arranged by freezing the
spins inside `Λ` at a fixed configuration, which changes nothing because `γ_Λ 1_A` is itself
`𝓕_{S∖Λ}`-measurable. -/
theorem exists_measurable_cylinderEvents_sdiff_of_isQuasilocal [Nonempty E]
    {γ : Specification S E} (hγ : γ.IsQuasilocal) (Λ D : Finset S)
    {A : Set (S → E)} (hAmeas : MeasurableSet A)
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (D : Set S)] A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (C : Finset S) (F : (S → E) → ℝ),
      Measurable[cylinderEvents (X := fun _ : S ↦ E) ((C : Set S) \ (Λ : Set S))] F ∧
      ∀ ω, |(γ Λ ω A).toReal - F ω| ≤ ε := by
  classical
  set f : lp (fun _ : S → E ↦ ℝ) ∞ := indicatorLp A with hf
  have hfmeas : Measurable (⇑f) := measurable_coeFn_indicatorLp hAmeas
  have hfloc : f ∈ localFunctions S E :=
    mem_localFunctions.2 ⟨D, indicatorLp_mem_localFunctionsOn hA⟩
  have hq : Specification.action γ Λ f ∈ quasilocalFunctions S E :=
    hγ Λ f (localFunctions_le_quasilocalFunctions hfloc)
  obtain ⟨g, hgloc, hgdist⟩ :=
    Metric.mem_closure_iff.1 (mem_quasilocalFunctions_iff_mem_closure.1 hq) ε hε
  obtain ⟨C, hC⟩ := mem_localFunctions.1 hgloc
  have hgmeasC : Measurable[cylinderEvents (X := fun _ : S ↦ E) (C : Set S)] (⇑g) := hC
  have hgdep : DependsOn (⇑g) (C : Set S) := hgmeasC.dependsOn_of_cylinderEvents
  set o : S → E := fun _ ↦ Classical.arbitrary E with ho
  set φ : (S → E) → (S → E) := fun ω i ↦ if i ∈ Λ then o i else ω i with hφ
  have hφmeas : Measurable φ := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    by_cases hi : i ∈ Λ
    · simpa only [hφ, hi, ↓reduceIte] using measurable_const
    · simpa only [hφ, hi, ↓reduceIte] using measurable_pi_apply i
  have hφout : ∀ (ω : S → E) (i : S), i ∈ ((Λ : Set S)ᶜ) → φ ω i = ω i := by
    intro ω i hi
    have hi' : i ∉ Λ := by simpa using hi
    simp only [hφ, hi', ↓reduceIte]
  refine ⟨C, fun ω ↦ (g : (S → E) → ℝ) (φ ω), ?_, fun ω ↦ ?_⟩
  · refine Measurable.cylinderEvents_of_dependsOn
      ((measurable_of_mem_quasilocalFunctions
        (localFunctions_le_quasilocalFunctions hgloc)).comp hφmeas) ?_
    intro x y hxy
    refine hgdep fun i hi ↦ ?_
    by_cases hiΛ : i ∈ Λ
    · simp only [hφ, hiΛ, ↓reduceIte]
    · simp only [hφ, hiΛ, ↓reduceIte]
      exact hxy i ⟨hi, by simpa using hiΛ⟩
  · have hactdep : DependsOn ((Specification.action γ Λ f : (S → E) → ℝ)) ((Λ : Set S)ᶜ) :=
      (Specification.action_mem_localFunctionsOn_compl (γ := γ) (Λ := Λ)
        hfmeas).dependsOn_of_cylinderEvents
    have hactφ : (Specification.action γ Λ f : (S → E) → ℝ) (φ ω)
        = (Specification.action γ Λ f : (S → E) → ℝ) ω :=
      hactdep fun i hi ↦ hφout ω i hi
    have hpt : ‖(Specification.action γ Λ f : (S → E) → ℝ) (φ ω)
        - (g : (S → E) → ℝ) (φ ω)‖ ≤ ‖Specification.action γ Λ f - g‖ := by
      have := lp.norm_apply_le_norm ENNReal.top_ne_zero (Specification.action γ Λ f - g) (φ ω)
      rwa [lp.coeFn_sub, Pi.sub_apply] at this
    rw [← action_indicatorLp_apply γ Λ hAmeas ω, ← hf, ← hactφ]
    rw [← Real.norm_eq_abs]
    refine hpt.trans ?_
    rw [← dist_eq_norm]
    exact hgdist.le

/-- **Georgii, Step 3 in the proof of Theorem (15.37).** -/
theorem isGibbsMeasure_of_forall_exists_density [Nonempty E]
    {γ : Specification S E} (hγ : γ.IsQuasilocal)
    {μ ν : Measure (S → E)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : γ.IsGibbsMeasure ν)
    (hstep : ∀ (Λ D : Finset S) (η : ℝ), 0 < η →
      ∃ (Δ : Finset S) (g : (S → E) → ℝ≥0∞), D ⊆ Δ ∧
        Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S) \ (Λ : Set S))] g ∧
        IsProbabilityMeasure (ν.withDensity g) ∧
        (ν.withDensity g).trim (cylinderEvents_le_pi (X := fun _ : S ↦ E)
            (Δ := ((Δ : Set S) \ (Λ : Set S))))
          = μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E)
            (Δ := ((Δ : Set S) \ (Λ : Set S)))) ∧
        ∀ A, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A →
          |μ.real A - (ν.withDensity g).real A| ≤ η) :
    γ.IsGibbsMeasure μ := by
  classical
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq]
  intro Λ
  have hker0 : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have : IsProbabilityMeasure (μ.bind (γ Λ)) :=
    isProbabilityMeasure_bind hker0 (.of_forall fun _ ↦ inferInstance)
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : S ↦ E)
    (generateFrom_measurableCylinders (α := fun _ : S ↦ E)).symm
    isPiSystem_measurableCylinders (fun A hA ↦ ?_) (by simp)
  obtain ⟨D, hD⟩ := Specification.exists_measurableSet_cylinderEvents_of_mem_measurableCylinders hA
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  have hker : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hkerν : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) ν :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hHmeas : Measurable fun ω : S → E ↦ γ Λ ω A :=
    ((γ Λ).measurable_coe hAmeas).mono cylinderEvents_le_pi le_rfl
  have hbindA : (μ.bind (γ Λ)) A = ∫⁻ ω, γ Λ ω A ∂μ := Measure.bind_apply hAmeas hker
  have hνbind : ν.bind (γ Λ) = ν :=
    (Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := ν)).1 hν Λ
  have hind : Measurable (A.indicator (1 : (S → E) → ℝ≥0∞)) :=
    measurable_one.indicator hAmeas
  have key : ∀ η : ℝ, 0 < η →
      (∫⁻ ω, γ Λ ω A ∂μ) ≤ μ A + ENNReal.ofReal η ∧
        μ A ≤ (∫⁻ ω, γ Λ ω A ∂μ) + ENNReal.ofReal η := by
    intro η hη
    set ε : ℝ := η / 4 with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨C, F₀, hF₀meas, hF₀close⟩ :=
      exists_measurable_cylinderEvents_sdiff_of_isQuasilocal hγ Λ D hAmeas hD hε
    obtain ⟨Δ, g, hDΔ, hg, hqprob, htrim, hTV⟩ := hstep Λ (D ∪ C ∪ Λ) (η / 2) (by positivity)
    set q : Measure (S → E) := ν.withDensity g with hqdef
    have hDsub : (D : Set S) ⊆ (Δ : Set S) := by
      exact_mod_cast (Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_left
        Finset.subset_union_left) hDΔ)
    have hCsub : (C : Set S) ⊆ (Δ : Set S) := by
      exact_mod_cast (Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_right
        Finset.subset_union_left) hDΔ)
    have hAΔ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A :=
      cylinderEvents_mono hDsub A hD
    have hFmeasΔ : Measurable[cylinderEvents (X := fun _ : S ↦ E)
        ((Δ : Set S) \ (Λ : Set S))] F₀ :=
      hF₀meas.mono (cylinderEvents_mono (Set.sdiff_subset_sdiff_left hCsub)) le_rfl
    set F : (S → E) → ℝ≥0∞ := fun ω ↦ ENNReal.ofReal (F₀ ω) with hFdef
    have hFm : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S) \ (Λ : Set S))] F :=
      ENNReal.measurable_ofReal.comp hFmeasΔ
    have hFm' : Measurable F := hFm.mono cylinderEvents_le_pi le_rfl
    -- the pointwise two-sided bound
    have htoReal : ∀ ω, γ Λ ω A = ENNReal.ofReal (γ Λ ω A).toReal := fun ω ↦
      (ENNReal.ofReal_toReal (measure_ne_top (γ Λ ω) A)).symm
    have hp1 : ∀ ω, γ Λ ω A ≤ F ω + ENNReal.ofReal ε := by
      intro ω
      have habs := abs_le.1 (hF₀close ω)
      rcases le_or_gt 0 (F₀ ω) with h0 | h0
      · rw [htoReal ω, hFdef]
        calc ENNReal.ofReal (γ Λ ω A).toReal ≤ ENNReal.ofReal (F₀ ω + ε) :=
              ENNReal.ofReal_le_ofReal (by linarith [habs.2])
          _ = ENNReal.ofReal (F₀ ω) + ENNReal.ofReal ε := ENNReal.ofReal_add h0 hε.le
      · have : (γ Λ ω A).toReal ≤ ε := by linarith [habs.2]
        calc γ Λ ω A = ENNReal.ofReal (γ Λ ω A).toReal := htoReal ω
          _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal this
          _ ≤ F ω + ENNReal.ofReal ε := le_add_self
    have hp2 : ∀ ω, F ω ≤ γ Λ ω A + ENNReal.ofReal ε := by
      intro ω
      have habs := abs_le.1 (hF₀close ω)
      rcases le_or_gt 0 (F₀ ω) with h0 | h0
      · rw [htoReal ω, hFdef]
        calc ENNReal.ofReal (F₀ ω) ≤ ENNReal.ofReal ((γ Λ ω A).toReal + ε) :=
              ENNReal.ofReal_le_ofReal (by linarith [habs.1])
          _ = ENNReal.ofReal (γ Λ ω A).toReal + ENNReal.ofReal ε :=
              ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le
      · have : F ω = 0 := by simp [hFdef, ENNReal.ofReal_eq_zero.2 h0.le]
        rw [this]
        exact zero_le
    -- integrating
    have hint1 : (∫⁻ ω, γ Λ ω A ∂μ) ≤ (∫⁻ ω, F ω ∂μ) + ENNReal.ofReal ε := by
      calc (∫⁻ ω, γ Λ ω A ∂μ) ≤ ∫⁻ ω, (F ω + ENNReal.ofReal ε) ∂μ := lintegral_mono hp1
        _ = (∫⁻ ω, F ω ∂μ) + ENNReal.ofReal ε := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    have hint2 : (∫⁻ ω, F ω ∂q) ≤ (∫⁻ ω, γ Λ ω A ∂q) + ENNReal.ofReal ε := by
      have := hqprob
      calc (∫⁻ ω, F ω ∂q) ≤ ∫⁻ ω, (γ Λ ω A + ENNReal.ofReal ε) ∂q := lintegral_mono hp2
        _ = (∫⁻ ω, γ Λ ω A ∂q) + ENNReal.ofReal ε := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    have hint4 : (∫⁻ ω, γ Λ ω A ∂q) ≤ (∫⁻ ω, F ω ∂q) + ENNReal.ofReal ε := by
      have := hqprob
      calc (∫⁻ ω, γ Λ ω A ∂q) ≤ ∫⁻ ω, (F ω + ENNReal.ofReal ε) ∂q := lintegral_mono hp1
        _ = (∫⁻ ω, F ω ∂q) + ENNReal.ofReal ε := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    have hint5 : (∫⁻ ω, F ω ∂μ) ≤ (∫⁻ ω, γ Λ ω A ∂μ) + ENNReal.ofReal ε := by
      calc (∫⁻ ω, F ω ∂μ) ≤ ∫⁻ ω, (γ Λ ω A + ENNReal.ofReal ε) ∂μ := lintegral_mono hp2
        _ = (∫⁻ ω, γ Λ ω A ∂μ) + ENNReal.ofReal ε := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    have hFμq : (∫⁻ ω, F ω ∂μ) = ∫⁻ ω, F ω ∂q := by
      rw [← lintegral_trim cylinderEvents_le_pi hFm, ← htrim,
        lintegral_trim cylinderEvents_le_pi hFm]
    -- the Gibbs property of `ν`
    have hgΛc : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] g :=
      hg.mono (cylinderEvents_mono (Set.sdiff_subset_compl _ _)) le_rfl
    have hgm : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
    have hqA : (∫⁻ ω, γ Λ ω A ∂q) = q A := by
      have hmul : Measurable fun x : S → E ↦ g x * A.indicator 1 x := hgm.mul hind
      calc (∫⁻ ω, γ Λ ω A ∂q)
          = ∫⁻ ω, g ω * γ Λ ω A ∂ν := by
            rw [hqdef, lintegral_withDensity_eq_lintegral_mul _ hgm hHmeas]; rfl
        _ = ∫⁻ ω, (∫⁻ x, g x * A.indicator 1 x ∂(γ Λ ω)) ∂ν := by
            refine lintegral_congr fun ω ↦ ?_
            rw [Specification.lintegral_mul γ Λ hind hgΛc, lintegral_indicator_one hAmeas]
        _ = ∫⁻ x, g x * A.indicator 1 x ∂(ν.bind (γ Λ)) :=
            (Measure.lintegral_bind hkerν hmul.aemeasurable).symm
        _ = ∫⁻ x, g x * A.indicator 1 x ∂ν := by rw [hνbind]
        _ = q A := by
            rw [hqdef, withDensity_apply _ hAmeas, ← lintegral_indicator hAmeas]
            exact lintegral_congr fun x ↦ by
              by_cases hx : x ∈ A <;> simp [hx]
    -- Step 2's total-variation bound
    have := hqprob
    have htv := abs_le.1 (hTV A hAΔ)
    have hqμ : q A ≤ μ A + ENNReal.ofReal (η / 2) := by
      have h1 : q.real A ≤ μ.real A + η / 2 := by linarith [htv.2]
      calc q A = ENNReal.ofReal (q.real A) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top q A)]
        _ ≤ ENNReal.ofReal (μ.real A + η / 2) := ENNReal.ofReal_le_ofReal h1
        _ = μ A + ENNReal.ofReal (η / 2) := by
            rw [ENNReal.ofReal_add measureReal_nonneg (by positivity), measureReal_def,
              ENNReal.ofReal_toReal (measure_ne_top μ A)]
    have hμq : μ A ≤ q A + ENNReal.ofReal (η / 2) := by
      have h1 : μ.real A ≤ q.real A + η / 2 := by linarith [htv.1]
      calc μ A = ENNReal.ofReal (μ.real A) := by
            rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ A)]
        _ ≤ ENNReal.ofReal (q.real A + η / 2) := ENNReal.ofReal_le_ofReal h1
        _ = q A + ENNReal.ofReal (η / 2) := by
            rw [ENNReal.ofReal_add measureReal_nonneg (by positivity), measureReal_def,
              ENNReal.ofReal_toReal (measure_ne_top q A)]
    have hsum : ENNReal.ofReal (η / 2) + (ENNReal.ofReal ε + ENNReal.ofReal ε)
        = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      rw [hεdef]; ring
    constructor
    · calc (∫⁻ ω, γ Λ ω A ∂μ) ≤ (∫⁻ ω, F ω ∂μ) + ENNReal.ofReal ε := hint1
        _ = (∫⁻ ω, F ω ∂q) + ENNReal.ofReal ε := by rw [hFμq]
        _ ≤ ((∫⁻ ω, γ Λ ω A ∂q) + ENNReal.ofReal ε) + ENNReal.ofReal ε := by gcongr
        _ = q A + ENNReal.ofReal ε + ENNReal.ofReal ε := by rw [hqA]
        _ ≤ (μ A + ENNReal.ofReal (η / 2)) + ENNReal.ofReal ε + ENNReal.ofReal ε := by gcongr
        _ = μ A + ENNReal.ofReal η := by rw [add_assoc, add_assoc, hsum]
    · calc μ A ≤ q A + ENNReal.ofReal (η / 2) := hμq
        _ = (∫⁻ ω, γ Λ ω A ∂q) + ENNReal.ofReal (η / 2) := by rw [hqA]
        _ ≤ ((∫⁻ ω, F ω ∂q) + ENNReal.ofReal ε) + ENNReal.ofReal (η / 2) := by gcongr
        _ = ((∫⁻ ω, F ω ∂μ) + ENNReal.ofReal ε) + ENNReal.ofReal (η / 2) := by rw [hFμq]
        _ ≤ (((∫⁻ ω, γ Λ ω A ∂μ) + ENNReal.ofReal ε) + ENNReal.ofReal ε)
              + ENNReal.ofReal (η / 2) := by gcongr
        _ = (∫⁻ ω, γ Λ ω A ∂μ) + (ENNReal.ofReal (η / 2)
              + (ENNReal.ofReal ε + ENNReal.ofReal ε)) := by ring
        _ = (∫⁻ ω, γ Λ ω A ∂μ) + ENNReal.ofReal η := by rw [hsum]
  rw [hbindA]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun e he _ ↦ ?_)
    (ENNReal.le_of_forall_pos_le_add fun e he _ ↦ ?_)
  · have := (key e (by exact_mod_cast he)).1
    rwa [ENNReal.ofReal_coe_nnreal] at this
  · have := (key e (by exact_mod_cast he)).2
    rwa [ENNReal.ofReal_coe_nnreal] at this

end Step3

end MeasureTheory.GibbsMeasure

/-! ### Georgii Theorem (15.37) on `ℤ^d` -/

namespace MeasureTheory.GibbsMeasure

section Georgii1537

variable {E : Type*} [MeasurableSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ ν : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Turning an `EReal` bound on `a / N` into a real bound on `a`. -/
private lemma toReal_lt_of_ereal_div_lt {a : ℝ≥0∞} {N t : ℝ} (hN : 0 < N)
    (h : ((a : ℝ≥0∞) : EReal) / (N : EReal) < (t : EReal)) : a ≠ ∞ ∧ a.toReal < t * N := by
  rw [EReal.div_lt_iff (by exact_mod_cast hN) (EReal.coe_ne_top _), ← EReal.coe_mul] at h
  have hane : a ≠ ∞ := by rintro rfl; simp at h
  exact ⟨hane, EReal.coe_lt_coe_iff.1 (by rwa [← EReal.coe_ennreal_toReal hane] at h)⟩

private lemma card_Icc_zero_mul_sub_one (j R : ℕ) :
    #(Icc (0 : ι → ℤ) fun _ ↦ (j : ℤ) * (2 * (R : ℤ) + 1) - 1)
      = (j * (2 * R + 1)) ^ Fintype.card ι := by
  rw [Pi.card_Icc]
  simp only [Int.card_Icc, Pi.zero_apply]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  have : (j : ℤ) * (2 * (R : ℤ) + 1) - 1 + 1 - 0 = ((j * (2 * R + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

/-- **Georgii Theorem (15.37).** Let `γ` be a quasilocal specification on `ℤ^d`, let `ν` be a
shift-invariant Gibbs measure for `γ` and let `μ` be a shift-invariant random field whose
finite-volume relative entropies with respect to `ν` are `o(|Λ_j|)` along every sequence of boxes
all of whose sides tend to infinity. Then `μ` is itself a Gibbs measure for `γ`.

Georgii assumes only `liminf |Λ_n|⁻¹ 𝓗_{Λ_n}(μ|ν) = 0` along one sequence of cubes with
`|Λ_n| → ∞`; the hypothesis here is the limit along all boxes, which is what Theorem (15.30)(b)
supplies in the application to the variational principle (15.39), and which is what makes the
packing of Step 1 exact (the boxes `Λ_N` are tiled by `N^d` translates of the cube `C`). -/
theorem isGibbsMeasure_of_tendsto_relativeEntropyIn_div_card [Nonempty E]
    {γ : Specification (ι → ℤ) E} (hγ : γ.IsQuasilocal)
    (hμs : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun μ μ)
    (hνs : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun ν ν)
    (hνG : γ.IsGibbsMeasure ν)
    (hlim : ∀ m n : ℕ → ι → ℤ, (∀ k, Tendsto (fun j ↦ n j k - m j k) atTop atTop) →
      Tendsto (fun j ↦ ((relativeEntropyIn (↑(Icc (m j) (n j)) : Set (ι → ℤ)) μ ν : ℝ≥0∞) : EReal)
        / (#(Icc (m j) (n j)) : EReal)) atTop (𝓝 0)) :
    γ.IsGibbsMeasure μ := by
  classical
  -- (A) every finite-volume relative entropy is finite
  have hfin : ∀ D : Finset (ι → ℤ), relativeEntropyIn (D : Set (ι → ℤ)) μ ν ≠ ∞ := by
    intro D
    obtain ⟨R, hR⟩ := Potential.exists_subset_Icc_const D
    have hcube := hlim (fun _ ↦ 0) (fun j _ ↦ (j : ℤ))
      (fun k ↦ by simpa using tendsto_natCast_atTop_atTop (R := ℤ))
    have hev := hcube.eventually (gt_mem_nhds (show (0 : EReal) < ((1 : ℝ) : EReal) by
      exact_mod_cast zero_lt_one))
    obtain ⟨j, hj1, hj2⟩ := ((eventually_ge_atTop (2 * R)).and hev).exists
    have hcardpos : (0 : ℝ) < #(Icc (0 : ι → ℤ) fun _ ↦ (j : ℤ)) := by
      have : (Icc (0 : ι → ℤ) fun _ ↦ (j : ℤ)).Nonempty :=
        nonempty_Icc.2 (Pi.le_def.2 fun _ ↦ by positivity)
      exact_mod_cast this.card_pos
    have hne := (toReal_lt_of_ereal_div_lt hcardpos hj2).1
    refine ne_top_of_le_ne_top hne ?_
    have himg : ((· + fun _ : ι ↦ (R : ℤ)) '' (D : Set (ι → ℤ)))
        ⊆ ((Icc (0 : ι → ℤ) fun _ ↦ (j : ℤ)) : Finset (ι → ℤ)) := by
      rintro _ ⟨x, hx, rfl⟩
      have hxR := (Finset.mem_Icc.1 (hR (by exact_mod_cast hx)))
      refine Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨Pi.le_def.2 fun k ↦ ?_, Pi.le_def.2 fun k ↦ ?_⟩)
      · have := Pi.le_def.1 hxR.1 k
        simp only [Pi.add_apply, Pi.zero_apply]
        omega
      · have h1 := Pi.le_def.1 hxR.2 k
        have h2 : (2 * R : ℕ) ≤ j := hj1
        have h3 : (2 * (R : ℤ)) ≤ (j : ℤ) := by exact_mod_cast h2
        simp only [Pi.add_apply]
        omega
    calc relativeEntropyIn (D : Set (ι → ℤ)) μ ν
        = relativeEntropyIn ((· + fun _ : ι ↦ (R : ℤ)) '' (D : Set (ι → ℤ))) μ ν :=
          (relativeEntropyIn_image_add hμs hνs _ _).symm
      _ ≤ _ := relativeEntropyIn_mono himg
  -- (B) Steps 1 and 2 supply the data needed by Step 3
  refine isGibbsMeasure_of_forall_exists_density hγ hνG ?_
  intro Λ D η hη
  obtain ⟨r, hr0, hr⟩ := InformationTheory.exists_abs_sub_one_le_mul_klFun_add
    (show (0 : ℝ) < η / 2 by positivity)
  set δ : ℝ := η / (2 * r) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨R, hR⟩ := Potential.exists_subset_Icc_const (D ∪ Λ)
  set d : ℕ := Fintype.card ι with hd
  set K : ℝ := ((2 * R + 1 : ℕ) : ℝ) ^ d with hK
  have hKpos : 0 < K := by
    have : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) := by positivity
    exact pow_pos this d
  -- find a box along which the relative entropy is at most `δ |Λ_N|`
  have hbox := hlim (fun _ ↦ 0) (fun j _ ↦ (j : ℤ) * (2 * (R : ℤ) + 1) - 1) (fun k ↦ by
    refine tendsto_atTop_mono (fun j : ℕ ↦ ?_)
      (Filter.tendsto_atTop_add_const_right atTop (-1)
        (tendsto_natCast_atTop_atTop (R := ℤ)))
    have h1 : (1 : ℤ) ≤ 2 * (R : ℤ) + 1 := by omega
    have h2 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    simp only [Pi.zero_apply, sub_zero]
    nlinarith)
  have hev := hbox.eventually (gt_mem_nhds (show (0 : EReal) < ((δ / K : ℝ) : EReal) by
    exact_mod_cast div_pos hδ hKpos))
  obtain ⟨N, hN1, hN2⟩ := ((eventually_ge_atTop 1).and hev).exists
  have hNpos : 0 < N := hN1
  have hcardN : (#(Icc (0 : ι → ℤ) fun _ ↦ (N : ℤ) * (2 * (R : ℤ) + 1) - 1) : ℝ)
      = (N : ℝ) ^ d * K := by
    rw [card_Icc_zero_mul_sub_one, hK]
    push_cast
    rw [mul_pow]
  have hcardpos : (0 : ℝ) < #(Icc (0 : ι → ℤ) fun _ ↦ (N : ℤ) * (2 * (R : ℤ) + 1) - 1) := by
    rw [hcardN]
    have : (0 : ℝ) < (N : ℝ) ^ d := by positivity
    positivity
  obtain ⟨-, hNlt⟩ := toReal_lt_of_ereal_div_lt hcardpos hN2
  have hB : (relativeEntropyIn
      (↑(Icc (0 : ι → ℤ) fun _ ↦ (N : ℤ) * (2 * (R : ℤ) + 1) - 1) : Set (ι → ℤ)) μ ν).toReal
      ≤ δ * (N : ℝ) ^ d := by
    refine hNlt.le.trans (le_of_eq ?_)
    rw [hcardN]
    field_simp
  -- Step 1
  have hΛR : Λ ⊆ Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) :=
    Finset.Subset.trans Finset.subset_union_right hR
  obtain ⟨Δ, hΔC, hΔle⟩ :=
    exists_subset_relativeEntropyIn_sub_le hμs hνs hfin Λ R hΛR hNpos hB
  -- Step 2
  have hΔle' : (relativeEntropyIn (Δ : Set (ι → ℤ)) μ ν).toReal
      - (relativeEntropyIn ((Δ : Set (ι → ℤ)) \ (Λ : Set (ι → ℤ))) μ ν).toReal ≤ δ := by
    rwa [← Finset.coe_sdiff]
  obtain ⟨g, hg, hgprob, htrim, hTV⟩ :=
    exists_density_of_relativeEntropyIn_sub_le (Λ : Set (ι → ℤ)) (Δ : Set (ι → ℤ)) (hfin Δ)
      hr hr0.le hΔle'
  refine ⟨Δ, g, ?_, hg, hgprob, htrim, fun A hA ↦ (hTV A hA).trans (le_of_eq ?_)⟩
  · exact Finset.Subset.trans (Finset.Subset.trans Finset.subset_union_left hR) hΔC
  · rw [hδdef]
    field_simp
    ring

end Georgii1537

end MeasureTheory.GibbsMeasure

/-! ### Georgii (15.29): the Gibbs distribution as a density on `𝓕_Λ` -/

namespace Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]

variable (Φ) in
/-- Georgii's density `ρ^Φ_Λ(σ_Λ ω_{S∖Λ}) = e^{−H^Φ_Λ(σ_Λ ω_{S∖Λ})} / Z^Φ_Λ(ω)` of the Gibbs
distribution `γ^Φ_Λ(·|ω)` with respect to the a priori product measure `λ^S` on the cylinder
σ-algebra `𝓕_Λ`; it is the function `ρ^{Φ,ν}_Λ` in Georgii's proof of Lemma (15.28), taken at
the Dirac boundary condition `ν = δ_ω`. -/
def gibbsDensityIn (Λ : Finset S) (ω σ : S → E) : ℝ≥0∞ :=
  Φ.boltzmannFactor 1 Λ (juxt (Λ : Set S) ω fun i ↦ σ i)
    / Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω

lemma measurable_cylinderEvents_gibbsDensityIn (Λ : Finset S) (ω : S → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (Φ.gibbsDensityIn ν Λ ω) :=
  Measurable.div ((measurable_boltzmannFactor (Φ := Φ) 1 Λ).comp
    (measurable_cylinderEvents_juxt_restrict (Λ : Set S) ω)) measurable_const

lemma measurable_gibbsDensityIn (Λ : Finset S) (ω : S → E) :
    Measurable (Φ.gibbsDensityIn ν Λ ω) :=
  (measurable_cylinderEvents_gibbsDensityIn ν Λ ω).mono cylinderEvents_le_pi le_rfl

/-- **Georgii, in the proof of (15.28)/(15.29).** On the cylinder σ-algebra `𝓕_Λ`, the Gibbs
distribution `γ^Φ_Λ(·|ω)` has the density `ρ^Φ_Λ(σ_Λ ω_{S∖Λ})` with respect to the a priori
product measure `λ^S`. -/
theorem trim_gibbsSpecification_eq_withDensity (Λ : Finset S) (ω : S → E) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω).trim
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))
      = ((Measure.infinitePi fun _ : S ↦ ν).trim
          (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))).withDensity
            (Φ.gibbsDensityIn ν Λ ω) := by
  have hZ0 : Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω ≠ 0 :=
    (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν 1 Λ ω).1
  have hZt : Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω ≠ ⊤ :=
    (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν 1 Λ ω).2
  refine @Measure.ext _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) _ _ fun A hA ↦ ?_
  rw [trim_measurableSet_eq _ hA, withDensity_apply _ hA,
    restrict_trim _ _ hA,
    lintegral_trim _ (measurable_cylinderEvents_gibbsDensityIn ν Λ ω),
    gibbsSpecificationOfAbsolutelySummable, Specification.modification_apply,
    Specification.withDensity_premodifierNorm_apply ν (isPremodifier_boltzmannFactor (Φ := Φ) 1)
      (cylinderEvents_le_pi _ hA),
    Specification.isssd_eq_map_juxt_restrict ν Λ ω,
    setLIntegral_map (cylinderEvents_le_pi _ hA) (measurable_boltzmannFactor (Φ := Φ) 1 Λ)
      ((measurable_cylinderEvents_juxt_restrict (Λ : Set S) ω).mono cylinderEvents_le_pi le_rfl),
    preimage_juxt_restrict_eq (Λ : Set S) ω hA]
  simp only [gibbsDensityIn, ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hZ0)]

omit [Countable S] [IsPotential Φ] in
lemma gibbsDensityIn_ne_zero (Λ : Finset S) (ω σ : S → E) : Φ.gibbsDensityIn ν Λ ω σ ≠ 0 := by
  rw [gibbsDensityIn, Ne, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨(boltzmannFactor_pos (Φ := Φ) 1 Λ _).ne',
    (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν 1 Λ ω).2⟩

omit [Countable S] [IsPotential Φ] in
lemma gibbsDensityIn_ne_top (Λ : Finset S) (ω σ : S → E) : Φ.gibbsDensityIn ν Λ ω σ ≠ ⊤ := by
  rw [gibbsDensityIn, Ne, ENNReal.div_eq_top, not_or, not_and_or, not_and_or]
  exact ⟨Or.inr (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν 1 Λ ω).1,
    Or.inl (boltzmannFactor_ne_top (Φ := Φ) 1 Λ _)⟩

omit [Countable S] [IsPotential Φ] in
/-- The logarithm of Georgii's density: `log ρ^Φ_Λ(σ_Λ ω_{S∖Λ}) = −H^Φ_Λ(σ_Λ ω_{S∖Λ}) − log Z_Λ(ω)`.
-/
lemma log_toReal_gibbsDensityIn (Λ : Finset S) (ω σ : S → E) :
    log (Φ.gibbsDensityIn ν Λ ω σ).toReal
      = -Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) - Φ.logZ ν Λ ω := by
  rw [gibbsDensityIn, ENNReal.toReal_div, boltzmannFactor,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_div (Real.exp_ne_zero _)
      (toReal_premodifierZ_boltzmannFactor_pos ν (Φ := Φ) 1 Λ ω).ne',
    Real.log_exp, logZ]
  ring

omit [Countable S] [IsPotential Φ] in
lemma abs_log_toReal_gibbsDensityIn_le (Λ : Finset S) (ω σ : S → E) :
    |log (Φ.gibbsDensityIn ν Λ ω σ).toReal| ≤ Φ.hamiltonianBound Λ + |Φ.logZ ν Λ ω| := by
  rw [log_toReal_gibbsDensityIn]
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  rw [abs_neg]
  exact abs_hamiltonian_le Λ _

/-- **Georgii (15.34).** The relative entropy of `μ` with respect to the Gibbs distribution in `Λ`
with boundary condition `ω`, on the cylinder σ-algebra `𝓕_Λ`:
`𝓗_Λ(μ | γ^Φ_Λ(·|ω)) = −𝓗_Λ(μ) + μ(H^Φ_Λ(σ_Λ ω_{S∖Λ})) + log Z^Φ_Λ(ω)`. -/
theorem relativeEntropyIn_gibbsSpecification_eq {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (Λ : Finset S) (ω : S → E) :
    ((relativeEntropyIn (Λ : Set S) μ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω) : ℝ≥0∞) : EReal)
      = -entropyIn ν (Λ : Set S) μ
        + ((((∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂μ) + Φ.logZ ν Λ ω : ℝ)) :
            EReal) := by
  have hgm := measurable_cylinderEvents_gibbsDensityIn (Φ := Φ) ν Λ ω
  have hden := trim_gibbsSpecification_eq_withDensity (Φ := Φ) ν Λ ω
  have hprob : IsProbabilityMeasure
      (((Measure.infinitePi fun _ : S ↦ ν).trim
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))).withDensity
          (Φ.gibbsDensityIn ν Λ ω)) := by
    rw [← hden]; infer_instance
  have hsm : StronglyMeasurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      fun σ ↦ log (Φ.gibbsDensityIn ν Λ ω σ).toReal :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hgm)).stronglyMeasurable
  have hint : Integrable (fun σ ↦ log (Φ.gibbsDensityIn ν Λ ω σ).toReal)
      (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))) :=
    Integrable.mono' (integrable_const (Φ.hamiltonianBound Λ + |Φ.logZ ν Λ ω|))
      hsm.aestronglyMeasurable
      (.of_forall fun σ ↦ by
        simpa only [Real.norm_eq_abs] using abs_log_toReal_gibbsDensityIn_le ν Λ ω σ)
  have key := klDiv_withDensity_add_integral_log
    (μ := μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))))
    (lam := (Measure.infinitePi fun _ : S ↦ ν).trim cylinderEvents_le_pi)
    hgm (.of_forall fun σ ↦ gibbsDensityIn_ne_zero ν Λ ω σ)
    (.of_forall fun σ ↦ gibbsDensityIn_ne_top ν Λ ω σ) hprob hint
  rw [← hden] at key
  -- rewrite the integral of `log ρ` as `−μ(H_Λ) − log Z_Λ(ω)`
  have hI : ∫ σ, log (Φ.gibbsDensityIn ν Λ ω σ).toReal
      ∂(μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))))
      = -((∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂μ) + Φ.logZ ν Λ ω) := by
    rw [← integral_trim _ hsm]
    have hlog : ∀ σ : S → E, log (Φ.gibbsDensityIn ν Λ ω σ).toReal
        = -(Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) + Φ.logZ ν Λ ω) := fun σ ↦ by
      rw [log_toReal_gibbsDensityIn]; ring
    simp only [hlog]
    rw [integral_neg, integral_add (integrable_hamiltonian_juxt Λ ω μ) (integrable_const _),
      integral_const]
    simp
  rw [hI] at key
  rw [entropyIn, neg_neg, ← key, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
    add_zero]

/-! ### Georgii (15.28): the boundary condition only matters up to `r(Λ, Φ)` -/

/-- **Georgii, in the proof of (15.28).** `log Z^Φ_Λ(η) − log Z^Φ_Λ(ω) ≤ r(Λ, Φ)`, with Georgii's
`r(Λ, Φ)` sharpened to `2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
lemma logZ_sub_logZ_le_two_mul_tail (Λ : Finset S) (η ω : S → E) :
    Φ.logZ ν Λ η - Φ.logZ ν Λ ω ≤ 2 * Φ.tail Λ Λ := by
  have h := (logZ_le_logSupZ ν (Φ := Φ) Λ η).trans (logSupZ_le_logZ_add ν (Φ := Φ) Λ ω)
  linarith

/-- **Georgii, in the proof of (15.28).**
`log ρ^Φ_Λ(σ_Λ η_{S∖Λ}) − log ρ^Φ_Λ(σ_Λ ω_{S∖Λ}) ≤ 2 r(Λ, Φ)`. -/
lemma log_toReal_gibbsDensityIn_sub_le (Λ : Finset S) (η ω σ : S → E) :
    log (Φ.gibbsDensityIn ν Λ η σ).toReal - log (Φ.gibbsDensityIn ν Λ ω σ).toReal
      ≤ 4 * Φ.tail Λ Λ := by
  rw [log_toReal_gibbsDensityIn, log_toReal_gibbsDensityIn]
  have h1 := (abs_le.1 (abs_hamiltonian_sub_le_of_eqOn (Φ := Φ) Λ
    (η := juxt (Λ : Set S) ω fun i ↦ σ i) (ζ := juxt (Λ : Set S) η fun i ↦ σ i)
    fun i hi ↦ by rw [juxt_apply_of_mem hi, juxt_apply_of_mem hi])).2
  have h2 := logZ_sub_logZ_le_two_mul_tail ν (Φ := Φ) Λ ω η
  linarith

/-- **Georgii, in the proof of (15.28).** The Gibbs densities on `𝓕_Λ` for two boundary conditions
are within `e^{2 r(Λ, Φ)}` of each other. -/
lemma gibbsDensityIn_le_mul (Λ : Finset S) (η ω σ : S → E) :
    Φ.gibbsDensityIn ν Λ η σ
      ≤ ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ)) * Φ.gibbsDensityIn ν Λ ω σ := by
  have hat := gibbsDensityIn_ne_top ν (Φ := Φ) Λ η σ
  have hbt := gibbsDensityIn_ne_top ν (Φ := Φ) Λ ω σ
  have hap : 0 < (Φ.gibbsDensityIn ν Λ η σ).toReal :=
    ENNReal.toReal_pos (gibbsDensityIn_ne_zero ν (Φ := Φ) Λ η σ) hat
  have hbp : 0 < (Φ.gibbsDensityIn ν Λ ω σ).toReal :=
    ENNReal.toReal_pos (gibbsDensityIn_ne_zero ν (Φ := Φ) Λ ω σ) hbt
  have hlog := log_toReal_gibbsDensityIn_sub_le ν (Φ := Φ) Λ η ω σ
  have hle : (Φ.gibbsDensityIn ν Λ η σ).toReal
      ≤ Real.exp (4 * Φ.tail Λ Λ) * (Φ.gibbsDensityIn ν Λ ω σ).toReal := by
    rw [← Real.log_le_log_iff hap (by positivity), Real.log_mul (Real.exp_ne_zero _) hbp.ne',
      Real.log_exp]
    linarith
  calc Φ.gibbsDensityIn ν Λ η σ = ENNReal.ofReal (Φ.gibbsDensityIn ν Λ η σ).toReal :=
        (ENNReal.ofReal_toReal hat).symm
    _ ≤ ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ) * (Φ.gibbsDensityIn ν Λ ω σ).toReal) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ)) * Φ.gibbsDensityIn ν Λ ω σ := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hbt]

/-- **Georgii, in the proof of (15.28).** On the cylinder σ-algebra `𝓕_Λ`, the Gibbs distributions
with boundary conditions `η` and `ω` are within `e^{2 r(Λ, Φ)}` of each other. -/
theorem gibbsSpecification_apply_le_mul (Λ : Finset S) (η ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ η A
      ≤ ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ))
        * gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A := by
  have hval : ∀ ρ : S → E, gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ρ A
      = ∫⁻ σ in A, Φ.gibbsDensityIn ν Λ ρ σ
          ∂((Measure.infinitePi fun _ : S ↦ ν).trim
            (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))) := fun ρ ↦ by
    rw [← trim_measurableSet_eq (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))) hA,
      trim_gibbsSpecification_eq_withDensity (Φ := Φ) ν Λ ρ, withDensity_apply _ hA]
  rw [hval η, hval ω, ← lintegral_const_mul _ (measurable_cylinderEvents_gibbsDensityIn ν Λ ω)]
  exact lintegral_mono fun σ ↦ gibbsDensityIn_le_mul ν Λ η ω σ

omit [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] in
/-- `log e^{2 r(Λ, Φ)} = 2 r(Λ, Φ)`, for the `ℝ≥0`-valued constant used below. -/
lemma log_coe_toNNReal_exp_tail (Λ : Finset S) :
    log (((Real.exp (4 * Φ.tail Λ Λ)).toNNReal : ℝ≥0) : ℝ) = 4 * Φ.tail Λ Λ := by
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, Real.log_exp]

/-- **Georgii Lemma (15.28), the estimate on which it rests.** For any two probability measures
`ρ, ρ'` on `Ω`, the measures `ρ γ^Φ_Λ` and `ρ' γ^Φ_Λ` are within a factor `e^{2 r(Λ, Φ)}` of each
other on the cylinder σ-algebra `𝓕_Λ`; `ρ^{Φ,ρ}_Λ / ρ^{Φ,ρ'}_Λ ∈ [e^{-2r}, e^{2r}]` in Georgii's
notation. -/
theorem trim_bind_gibbsSpecification_le_smul (Λ : Finset S) (ρ ρ' : Measure (S → E))
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ'] :
    (ρ.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)).trim
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))
      ≤ (Real.exp (4 * Φ.tail Λ Λ)).toNNReal •
          (ρ'.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)).trim
            (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))) := by
  refine Measure.le_iff.2 fun A hA ↦ ?_
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hker : ∀ σ : Measure (S → E),
      AEMeasurable (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ :
        (S → E) → Measure (S → E)) σ :=
    fun σ ↦ (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable).mono
      cylinderEvents_le_pi le_rfl).aemeasurable
  have hmeas : Measurable fun ω : S → E ↦
      gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A :=
    (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable_coe hAm)).mono
      cylinderEvents_le_pi le_rfl
  rw [trim_measurableSet_eq _ hA, Measure.smul_apply, trim_measurableSet_eq _ hA,
    Measure.bind_apply hAm (hker ρ), Measure.bind_apply hAm (hker ρ'), ENNReal.smul_def,
    smul_eq_mul]
  have key : ∀ ω : S → E,
      (∫⁻ η, gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ η A ∂ρ)
        ≤ ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ))
            * gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A := fun ω ↦ by
    calc ∫⁻ η, gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ η A ∂ρ
        ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ))
            * gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A ∂ρ :=
          lintegral_mono fun η ↦ gibbsSpecification_apply_le_mul ν Λ η ω hA
      _ = _ := by simp
  calc ∫⁻ η, gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ η A ∂ρ
      = ∫⁻ _, (∫⁻ η, gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ η A ∂ρ) ∂ρ' := by simp
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (4 * Φ.tail Λ Λ))
          * gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A ∂ρ' := lintegral_mono key
    _ = _ := lintegral_const_mul _ hmeas

instance isProbabilityMeasure_bind_gibbsSpecification (Λ : Finset S) (ρ : Measure (S → E))
    [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (ρ.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)) :=
  isProbabilityMeasure_bind
    (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable).mono
      cylinderEvents_le_pi le_rfl).aemeasurable (.of_forall fun _ ↦ inferInstance)

/-- **Georgii Lemma (15.28), quantitative form.** For any `μ ∈ 𝓟(Ω, 𝓕)` and any two probability
measures `ρ, ρ'` on `Ω`,
`𝓗_Λ(μ | ρ γ^Φ_Λ) ≤ 𝓗_Λ(μ | ρ' γ^Φ_Λ) + 2 r(Λ, Φ)`,
Georgii's `‖log ρ^{Φ,ρ'}_Λ / ρ^{Φ,ρ}_Λ‖ ≤ 2 r(Λ, Φ)` inserted into (15.29). Georgii's `r(Λ, Φ)` is
sharpened here to `2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` (`Potential.tail`). -/
theorem relativeEntropyIn_bind_le_add {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (Λ : Finset S) (ρ ρ' : Measure (S → E)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ'] :
    relativeEntropyIn (Λ : Set S) μ
        (ρ.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ))
      ≤ relativeEntropyIn (Λ : Set S) μ
          (ρ'.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ))
        + ENNReal.ofReal (4 * Φ.tail Λ Λ) := by
  have h := klDiv_le_klDiv_add_ofReal_log_of_le_smul
    (μ := μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))))
    (ν₁ := (ρ'.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)).trim
      cylinderEvents_le_pi)
    (ν₂ := (ρ.bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)).trim
      cylinderEvents_le_pi)
    (trim_bind_gibbsSpecification_le_smul ν Λ ρ' ρ) (trim_bind_gibbsSpecification_le_smul ν Λ ρ ρ')
  rwa [log_coe_toNNReal_exp_tail] at h

/-- **Georgii (15.33), finite-volume form.** If `μ` is a Gibbs measure for `γ^Φ`, then for every
boundary condition `ω`, `𝓗_Λ(μ | γ^Φ_Λ(·|ω)) ≤ 2 r(Λ, Φ)`: taking `ν = μ` and `ν̃ = δ_ω` in
Lemma (15.28), `𝓗_Λ(μ | μ γ^Φ_Λ) = 𝓗_Λ(μ | μ) = 0`. -/
theorem relativeEntropyIn_gibbsSpecification_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure μ)
    (Λ : Finset S) (ω : S → E) :
    relativeEntropyIn (Λ : Set S) μ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)
      ≤ ENNReal.ofReal (4 * Φ.tail Λ Λ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq
    (γ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1) (μ := μ)).1 hμ Λ
  have hdirac : (Measure.dirac ω).bind
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω :=
    Measure.dirac_bind
      (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable).mono
        cylinderEvents_le_pi le_rfl) ω
  have h := relativeEntropyIn_bind_le_add (Φ := Φ) ν (μ := μ) Λ (Measure.dirac ω) μ
  rw [hdirac, hbind] at h
  simpa using h

/-- **Georgii Lemma (15.28)**, one half of the comparison with a Dirac boundary condition: for a
Gibbs measure `ρ ∈ 𝒢(γ^Φ)` and any boundary condition `ω`,
`𝓗_Λ(μ | ρ) ≤ 𝓗_Λ(μ | γ^Φ_Λ(·|ω)) + 2 r(Λ, Φ)`. -/
theorem relativeEntropyIn_le_relativeEntropyIn_gibbsSpecification_add {μ ρ : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (hρ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure ρ)
    (Λ : Finset S) (ω : S → E) :
    relativeEntropyIn (Λ : Set S) μ ρ
      ≤ relativeEntropyIn (Λ : Set S) μ
          (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)
        + ENNReal.ofReal (4 * Φ.tail Λ Λ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq
    (γ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1) (μ := ρ)).1 hρ Λ
  have hdirac : (Measure.dirac ω).bind
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω :=
    Measure.dirac_bind
      (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable).mono
        cylinderEvents_le_pi le_rfl) ω
  have h := relativeEntropyIn_bind_le_add (Φ := Φ) ν (μ := μ) Λ ρ (Measure.dirac ω)
  rwa [hdirac, hbind] at h

/-- **Georgii Lemma (15.28)**, the other half: `𝓗_Λ(μ | γ^Φ_Λ(·|ω)) ≤ 𝓗_Λ(μ | ρ) + 2 r(Λ, Φ)`. -/
theorem relativeEntropyIn_gibbsSpecification_le_relativeEntropyIn_add {μ ρ : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    (hρ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure ρ)
    (Λ : Finset S) (ω : S → E) :
    relativeEntropyIn (Λ : Set S) μ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω)
      ≤ relativeEntropyIn (Λ : Set S) μ ρ + ENNReal.ofReal (4 * Φ.tail Λ Λ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq
    (γ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1) (μ := ρ)).1 hρ Λ
  have hdirac : (Measure.dirac ω).bind
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ)
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω :=
    Measure.dirac_bind
      (((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ).measurable).mono
        cylinderEvents_le_pi le_rfl) ω
  have h := relativeEntropyIn_bind_le_add (Φ := Φ) ν (μ := μ) Λ (Measure.dirac ω) ρ
  rwa [hdirac, hbind] at h

end Potential

/-! ### Georgii (15.30)(b), (15.32)–(15.35): the specific relative entropy on `ℤ^d` -/

namespace Potential

variable {E : Type*} [MeasurableSpace E] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Φ : Potential (ι → ℤ) E} (ν : Measure E) [IsProbabilityMeasure ν]
  {μ : Measure ((ι → ℤ) → E)}

variable (Φ) in
/-- **Georgii (15.32).** The *specific relative entropy* `𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)` of a
random field `μ` on `ℤ^d` relative to an absolutely summable shift-invariant potential `Φ`, an
extended real. By **Corollary (15.35)** (`Potential.specificRelativeEntropy_nonneg`) it lies in
`[0, +∞]`, and by **Theorem (15.30)(b)** it is the limit `lim |Λ_n|⁻¹ 𝓗_{Λ_n}(μ | ν)` for every
`ν ∈ 𝒢(Φ)`. Georgii's `−𝓀(μ|Φ) + P(Φ)` is the specific free energy `⟨μ, Φ⟩ − 𝓀(μ)`. -/
def specificRelativeEntropy (μ : Measure ((ι → ℤ) → E)) : EReal :=
  ((Φ.pressure ν + Φ.specificEnergy μ : ℝ) : EReal) - specificEntropy ν μ

lemma specificRelativeEntropy_eq_neg_specificEntropy_add :
    Φ.specificRelativeEntropy ν μ
      = -specificEntropy ν μ + ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal) := by
  rw [specificRelativeEntropy, sub_eq_add_neg, add_comm (Φ.pressure ν), add_comm]

/-- `(-x) / N = -(x / N)` in `EReal`. -/
private lemma ereal_neg_div (x y : EReal) : (-x) / y = -(x / y) := by
  rw [EReal.div_eq_inv_mul, EReal.div_eq_inv_mul, EReal.mul_comm, EReal.neg_mul, EReal.mul_comm]

/-- Dividing an `ℝ≥0∞` estimate `x ≤ y + t` by `|Λ|`. -/
private lemma ereal_div_le_add_of_le_add {x y : ℝ≥0∞} {t N : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (h : x ≤ y + ENNReal.ofReal t) :
    ((x : ℝ≥0∞) : EReal) / (N : EReal)
      ≤ ((y : ℝ≥0∞) : EReal) / (N : EReal) + ((t / N : ℝ) : EReal) := by
  have hN' : (0 : EReal) ≤ (N : EReal) := EReal.coe_nonneg.2 hN
  have h1 : ((x : ℝ≥0∞) : EReal) ≤ ((y : ℝ≥0∞) : EReal) + (t : EReal) := by
    have := EReal.coe_ennreal_le_coe_ennreal_iff.2 h
    rwa [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left ht] at this
  calc ((x : ℝ≥0∞) : EReal) / (N : EReal)
      ≤ (((y : ℝ≥0∞) : EReal) + (t : EReal)) / (N : EReal) :=
        EReal.div_le_div_right_of_nonneg hN' h1
    _ = ((y : ℝ≥0∞) : EReal) / (N : EReal) + (t : EReal) / (N : EReal) :=
        EReal.add_div_of_nonneg_right hN'
    _ = _ := by rw [EReal.coe_div]

variable [IsPotential Φ] [IsAbsolutelySummable Φ] {κ : Type*} {l : Filter κ} {m n : κ → ι → ℤ}

/-- **Georgii, the limit of (15.34).** For `μ ∈ 𝓟_Θ`, boxes `Λ_j` all of whose sides tend to
infinity and arbitrary boundary conditions `ω_j`,
`|Λ_j|⁻¹ 𝓗_{Λ_j}(μ | γ^Φ_{Λ_j}(·|ω_j)) → 𝓀(μ|Φ)`.
This is (15.34) divided by `|Λ_j|`, combined with Theorem (15.12) (`𝓗_{Λ_j}(μ)/|Λ_j| → 𝓀(μ)`),
Theorem (15.23) (`μ(H_{Λ_j}(σ ω_j))/|Λ_j| → ⟨μ, Φ⟩`) and Theorem (15.30)(a)
(`log Z_{Λ_j}(ω_j)/|Λ_j| → P(Φ)`). Georgii's (15.33) is the special case `μ ∈ 𝒢_Θ(Φ)`, where the
limit is `0`. -/
theorem tendsto_relativeEntropyIn_gibbsSpecification_div_card [IsProbabilityMeasure μ]
    (hΦ : Φ.IsShiftInvariant) (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) (ω : κ → (ι → ℤ) → E) :
    Tendsto (fun j ↦ ((relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 (Icc (m j) (n j)) (ω j)) :
          ℝ≥0∞) : EReal) / (#(Icc (m j) (n j)) : EReal))
      l (𝓝 (Φ.specificRelativeEntropy ν μ)) := by
  obtain ⟨_, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  -- the entropy term
  have hA : Tendsto (fun j ↦ (-entropyIn ν (Icc (m j) (n j) : Set (ι → ℤ)) μ)
      / (#(Icc (m j) (n j)) : EReal)) l (𝓝 (-specificEntropy ν μ)) :=
    Filter.Tendsto.congr (fun j ↦ (ereal_neg_div _ _).symm)
      ((tendsto_entropyIn_div_card ν hμ h).neg)
  -- the energy and pressure terms
  have hB : Tendsto (fun j ↦ ((((∫ σ, Φ.hamiltonian (Icc (m j) (n j))
        (juxt (Icc (m j) (n j) : Set (ι → ℤ)) (ω j) fun i ↦ σ i) ∂μ)
          + Φ.logZ ν (Icc (m j) (n j)) (ω j)) / #(Icc (m j) (n j)) : ℝ) : EReal)) l
      (𝓝 ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.2 ?_
    simp only [add_div]
    exact (tendsto_integral_hamiltonian_juxt_div_card hΦ hμ h ω).add
      (tendsto_logZ_div_card_pressure ν hΦ h ω)
  have hlim := (EReal.continuousAt_add (p := (-specificEntropy ν μ,
      ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal)))
    (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).tendsto.comp (hA.prodMk_nhds hB)
  rw [specificRelativeEntropy_eq_neg_specificEntropy_add]
  refine hlim.congr fun j ↦ ?_
  rw [Function.comp_apply, relativeEntropyIn_gibbsSpecification_eq ν _ (ω j),
    EReal.add_div_of_nonneg_right (Nat.cast_nonneg' _), EReal.coe_div, EReal.coe_natCast]

/-! ### Georgii Lemma (15.28), Theorem (15.30)(b), (15.33), Corollary (15.35): the limits -/

/-- **Squeezing two `ℝ≥0∞`-valued volume functionals that differ by `o(|Λ_j|)`.** If
`|x_j − y_j| ≤ t_j` with `t_j / N_j → 0` and `y_j / N_j → a`, then `x_j / N_j → a`. -/
private lemma tendsto_ereal_div_of_le_add {x y : κ → ℝ≥0∞} {t N : κ → ℝ} {a : EReal}
    (hN : ∀ j, 0 ≤ N j) (ht0 : ∀ j, 0 ≤ t j)
    (ht : Tendsto (fun j ↦ t j / N j) l (𝓝 0))
    (h₁ : ∀ j, x j ≤ y j + ENNReal.ofReal (t j))
    (h₂ : ∀ j, y j ≤ x j + ENNReal.ofReal (t j))
    (hy : Tendsto (fun j ↦ ((y j : ℝ≥0∞) : EReal) / ((N j : ℝ) : EReal)) l (𝓝 a)) :
    Tendsto (fun j ↦ ((x j : ℝ≥0∞) : EReal) / ((N j : ℝ) : EReal)) l (𝓝 a) :=
  EReal.tendsto_of_le_add_coe hy ht
    (.of_forall fun j ↦ EReal.bot_lt_zero.trans_le
      (EReal.div_nonneg (EReal.coe_ennreal_nonneg _) (EReal.coe_nonneg.2 (hN j))))
    (.of_forall fun j ↦ ereal_div_le_add_of_le_add (hN j) (ht0 j) (h₁ j))
    (.of_forall fun j ↦ ereal_div_le_add_of_le_add (hN j) (ht0 j) (h₂ j))

omit [IsPotential Φ] in
/-- Georgii's `2 r(Λ_j, Φ)` is `o(|Λ_j|)`; here in the sharpened form
`4 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
private lemma tendsto_four_mul_tail_div_card (hΦ : Φ.IsShiftInvariant)
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ 4 * Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j))
      / (#(Icc (m j) (n j)) : ℝ)) l (𝓝 0) := by
  simpa [mul_div_assoc] using (tendsto_tail_div_card hΦ h).const_mul 4

omit [Fintype ι] [DecidableEq ι] [IsPotential Φ] [IsAbsolutelySummable Φ] in
private lemma four_mul_tail_nonneg (Λ : Finset (ι → ℤ)) : 0 ≤ 4 * Φ.tail Λ Λ :=
  mul_nonneg (by norm_num) (tail_nonneg _ _)

/-- **Georgii Lemma (15.28).** For any `μ ∈ 𝓟(Ω, 𝓕)`, any two sequences `(ρ_j)`, `(ρ'_j)` of
probability measures on `Ω` and boxes `Λ_j` all of whose sides tend to infinity, the limits
`lim |Λ_j|⁻¹ 𝓗_{Λ_j}(μ | ρ_j γ^Φ_{Λ_j})` and `lim |Λ_j|⁻¹ 𝓗_{Λ_j}(μ | ρ'_j γ^Φ_{Λ_j})` exist
simultaneously and are then equal: the boundary condition of the Gibbs distribution is felt only
through `2 r(Λ_j, Φ) = o(|Λ_j|)`. Georgii's statement is for cubes with `|Λ_n| → ∞`; the boxes here
are more general. -/
theorem tendsto_relativeEntropyIn_bind_div_card_congr [IsProbabilityMeasure μ]
    (hΦ : Φ.IsShiftInvariant) (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop)
    (ρ ρ' : κ → Measure ((ι → ℤ) → E)) (hρ : ∀ j, IsProbabilityMeasure (ρ j))
    (hρ' : ∀ j, IsProbabilityMeasure (ρ' j)) {a : EReal}
    (ha : Tendsto (fun j ↦ ((relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ
        ((ρ' j).bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
          (Icc (m j) (n j)))) : ℝ≥0∞) : EReal) / (#(Icc (m j) (n j)) : EReal)) l (𝓝 a)) :
    Tendsto (fun j ↦ ((relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ
        ((ρ j).bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1
          (Icc (m j) (n j)))) : ℝ≥0∞) : EReal) / (#(Icc (m j) (n j)) : EReal)) l (𝓝 a) := by
  refine tendsto_ereal_div_of_le_add (t := fun j ↦ 4 * Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j)))
    (fun j ↦ Nat.cast_nonneg _) (fun j ↦ four_mul_tail_nonneg _)
    (tendsto_four_mul_tail_div_card hΦ h) (fun j ↦ ?_) (fun j ↦ ?_) ha
  · have := hρ j; have := hρ' j
    exact relativeEntropyIn_bind_le_add ν _ (ρ j) (ρ' j)
  · have := hρ j; have := hρ' j
    exact relativeEntropyIn_bind_le_add ν _ (ρ' j) (ρ j)

/-- **Georgii (15.33).** For a Gibbs measure `μ ∈ 𝒢(Φ)`, boxes `Λ_j` all of whose sides tend to
infinity and arbitrary boundary conditions `ω_j`,
`|Λ_j|⁻¹ 𝓗_{Λ_j}(μ | γ^Φ_{Λ_j}(·|ω_j)) → 0`. Shift invariance of `μ` is *not* needed: Georgii uses
it only to produce a Gibbs measure in `𝒢_Θ(Φ)` in the first place. -/
theorem tendsto_relativeEntropyIn_gibbsSpecification_div_card_zero [IsProbabilityMeasure μ]
    (hΦ : Φ.IsShiftInvariant)
    (hμ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure μ)
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) (ω : κ → (ι → ℤ) → E) :
    Tendsto (fun j ↦ ((relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 (Icc (m j) (n j)) (ω j)) :
          ℝ≥0∞) : EReal) / (#(Icc (m j) (n j)) : EReal)) l (𝓝 0) := by
  refine tendsto_ereal_div_of_le_add
    (x := fun j ↦ relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 (Icc (m j) (n j)) (ω j)))
    (y := fun _ ↦ 0) (N := fun j ↦ (#(Icc (m j) (n j)) : ℝ))
    (t := fun j ↦ 4 * Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j)))
    (fun j ↦ Nat.cast_nonneg _) (fun j ↦ four_mul_tail_nonneg _)
    (tendsto_four_mul_tail_div_card hΦ h)
    (fun j ↦ (zero_add (ENNReal.ofReal _)).ge.trans'
      (relativeEntropyIn_gibbsSpecification_le ν hμ _ (ω j)))
    (fun _ ↦ _root_.zero_le) ?_
  simpa using tendsto_const_nhds (x := (0 : EReal)) (f := l)

/-- **Georgii Theorem (15.30)(b).** For a shift-invariant random field `μ ∈ 𝓟_Θ`, *any* Gibbs
measure `ρ ∈ 𝒢(Φ)` and boxes `Λ_j` all of whose sides tend to infinity, the limit
`lim |Λ_j|⁻¹ 𝓗_{Λ_j}(μ | ρ)` exists and equals the specific relative entropy
`𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)` of (15.32); in particular it does not depend on `ρ`. -/
theorem tendsto_relativeEntropyIn_div_card [IsProbabilityMeasure μ] {ρ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure ρ] (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hρ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure ρ)
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ ((relativeEntropyIn (Icc (m j) (n j) : Set (ι → ℤ)) μ ρ : ℝ≥0∞) : EReal)
      / (#(Icc (m j) (n j)) : EReal)) l (𝓝 (Φ.specificRelativeEntropy ν μ)) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  refine tendsto_ereal_div_of_le_add (t := fun j ↦ 4 * Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j)))
    (fun j ↦ Nat.cast_nonneg _) (fun j ↦ four_mul_tail_nonneg _)
    (tendsto_four_mul_tail_div_card hΦ h)
    (fun j ↦ relativeEntropyIn_le_relativeEntropyIn_gibbsSpecification_add ν hρ _ _)
    (fun j ↦ relativeEntropyIn_gibbsSpecification_le_relativeEntropyIn_add ν hρ _ _)
    (tendsto_relativeEntropyIn_gibbsSpecification_div_card ν hΦ hμ h
      (fun _ ↦ Classical.arbitrary _))

/-- **Georgii Corollary (15.35), second half.** A shift-invariant Gibbs measure has specific
relative entropy zero: `𝓀(μ|Φ) = 0` for `μ ∈ 𝒢_Θ(Φ)`. Equivalently, `⟨μ, Φ⟩ − 𝓀(μ) = −P(Φ)`:
the specific free energy of every `μ ∈ 𝒢_Θ(Φ)` is `−P(Φ)`. -/
theorem specificRelativeEntropy_eq_zero [IsProbabilityMeasure μ] (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hg : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure μ) :
    Φ.specificRelativeEntropy ν μ = 0 := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  exact tendsto_nhds_unique
    (tendsto_relativeEntropyIn_gibbsSpecification_div_card (Φ := Φ) ν hΦ hμ
      (m := fun _ : ℕ ↦ fun _ : ι ↦ (0 : ℤ)) (n := fun N : ℕ ↦ fun _ : ι ↦ (N : ℤ))
      tendsto_sub_atTop_cube (fun _ ↦ Classical.arbitrary _))
    (tendsto_relativeEntropyIn_gibbsSpecification_div_card_zero (Φ := Φ) ν hΦ hg
      (m := fun _ : ℕ ↦ fun _ : ι ↦ (0 : ℤ)) (n := fun N : ℕ ↦ fun _ : ι ↦ (N : ℤ))
      tendsto_sub_atTop_cube (fun _ ↦ Classical.arbitrary _))

/-- **Georgii Corollary (15.35), second half**, for `μ ∈ 𝒢_Θ(Φ)` in the notation (14.14). -/
theorem specificRelativeEntropy_eq_zero_of_mem_invariantG (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
      (shiftGroup (ι → ℤ) E)) :
    Φ.specificRelativeEntropy ν μ = 0 := by
  obtain ⟨⟨hprob, hgibbs⟩, hinv⟩ := hμ
  exact specificRelativeEntropy_eq_zero ν hΦ hinv hgibbs

/-- **Georgii Corollary (15.35), first half.** `𝓀(μ|Φ) ≥ 0` for every shift-invariant random
field `μ`: the finite-volume relative entropies are nonnegative (Proposition (15.5)(a)), and
`𝓀(μ|Φ)` is their limit. -/
theorem specificRelativeEntropy_nonneg [IsProbabilityMeasure μ] (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) : 0 ≤ Φ.specificRelativeEntropy ν μ := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hlim := tendsto_relativeEntropyIn_gibbsSpecification_div_card (Φ := Φ) ν hΦ hμ
    (m := fun _ : ℕ ↦ fun _ : ι ↦ (0 : ℤ)) (n := fun N : ℕ ↦ fun _ : ι ↦ (N : ℤ))
    tendsto_sub_atTop_cube (fun _ ↦ Classical.arbitrary _)
  exact ge_of_tendsto' hlim fun _ ↦
    EReal.div_nonneg (EReal.coe_ennreal_nonneg _) (Nat.cast_nonneg' _)

/-! ### Georgii Theorem (15.39): the variational principle -/

/-- **Georgii Theorem (15.39), free-energy form, the inequality.** For every shift-invariant
random field `μ ∈ 𝓟_Θ` the specific free energy `⟨μ, Φ⟩ − 𝓀(μ)` is at least `−P(Φ)`, i.e.
`𝓀(μ) ≤ ⟨μ, Φ⟩ + P(Φ)`. This is `𝓀(μ|Φ) ≥ 0` written without `EReal` subtraction. -/
theorem specificEntropy_le_specificEnergy_add_pressure [IsProbabilityMeasure μ]
    (hΦ : Φ.IsShiftInvariant) (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy ν μ ≤ ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal) := by
  have h := specificRelativeEntropy_nonneg (Φ := Φ) ν hΦ hμ
  rw [specificRelativeEntropy, add_comm (Φ.pressure ν),
    EReal.sub_nonneg (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))] at h
  exact h

/-- **Georgii Theorem (15.39), free-energy form, the equality on `𝒢_Θ(Φ)`.** Every shift-invariant
Gibbs measure attains the minimum `−P(Φ)` of the specific free energy: `𝓀(μ) = ⟨μ, Φ⟩ + P(Φ)`. -/
theorem specificEntropy_eq_specificEnergy_add_pressure [IsProbabilityMeasure μ]
    (hΦ : Φ.IsShiftInvariant) (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hg : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure μ) :
    specificEntropy ν μ = ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal) := by
  have h := specificRelativeEntropy_eq_zero (Φ := Φ) ν hΦ hμ hg
  rw [specificRelativeEntropy, add_comm (Φ.pressure ν)] at h
  refine le_antisymm (specificEntropy_le_specificEnergy_add_pressure ν hΦ hμ) ?_
  exact EReal.sub_nonpos.1 h.le

/-- **Georgii Theorem (15.39), the converse direction** (Theorem (15.37) applied to the quasilocal
Gibbsian specification `γ^Φ` of Example (2.25)): a shift-invariant random field with vanishing
specific relative entropy is a shift-invariant Gibbs measure.

Besides shift invariance of `μ` and of `Φ`, the direction needs a **shift-invariant Gibbs measure
`ρ ∈ 𝒢_Θ(Φ)` to exist**: Georgii gets it from Theorem (4.23) and Corollary (5.16) (which need `E`
to be standard Borel, resp. compact); it is a hypothesis here. -/
theorem mem_invariantG_of_specificRelativeEntropy_eq_zero (hΦ : Φ.IsShiftInvariant)
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    {ρ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure ρ]
    (hρ : ρ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
      (shiftGroup (ι → ℤ) E))
    (h0 : Φ.specificRelativeEntropy ν μ = 0) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
      (shiftGroup (ι → ℤ) E) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  obtain ⟨-, hμshift⟩ := mem_invariantFields_shiftGroup.1 hμ
  obtain ⟨-, hρshift⟩ := mem_invariantFields_shiftGroup.1 hρ.2
  refine ⟨⟨inferInstance, ?_⟩, hμ⟩
  refine isGibbsMeasure_of_tendsto_relativeEntropyIn_div_card
    (isQuasilocal_gibbsSpecificationOfAbsolutelySummable ν 1) hμshift hρshift hρ.1.2
    fun m n hmn ↦ ?_
  have h := tendsto_relativeEntropyIn_div_card (Φ := Φ) ν hΦ hμ hρ.1.2 hmn
  rwa [h0] at h

/-- **Georgii Theorem (15.39), the variational principle.** For a shift-invariant absolutely
summable potential `Φ` and a shift-invariant random field `μ ∈ 𝓟_Θ`, the specific relative entropy
`𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)` is nonnegative (`specificRelativeEntropy_nonneg`), and it vanishes
exactly on `𝒢_Θ(Φ)`. Equivalently, `𝒢_Θ(Φ)` is where the specific free energy `⟨·, Φ⟩ − 𝓀(·)`
attains its minimum `−P(Φ)`.

The `←` direction is Corollary (15.35); the `→` direction is Theorem (15.37) and needs a
shift-invariant Gibbs measure `ρ` to exist. -/
theorem specificRelativeEntropy_eq_zero_iff_mem_invariantG (hΦ : Φ.IsShiftInvariant)
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    {ρ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure ρ]
    (hρ : ρ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
      (shiftGroup (ι → ℤ) E)) :
    Φ.specificRelativeEntropy ν μ = 0 ↔
      μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
        (shiftGroup (ι → ℤ) E) :=
  ⟨fun h ↦ mem_invariantG_of_specificRelativeEntropy_eq_zero ν hΦ hμ hρ h,
    fun h ↦ specificRelativeEntropy_eq_zero_of_mem_invariantG ν hΦ h⟩

/-! ### Georgii Theorem (15.39) over a standard Borel state space -/

section StandardBorel

variable [StandardBorelSpace E]

/-- **Georgii Theorem (15.39), the converse direction, unconditional.** Over a standard Borel
state space the shift-invariant Gibbs measure that
`Potential.mem_invariantG_of_specificRelativeEntropy_eq_zero` takes as a hypothesis is supplied by
Theorem (4.23) and Corollary (5.16)
(`Potential.invariantG_gibbsSpecification_shiftGroup_nonempty`): a shift-invariant random field
with vanishing specific relative entropy is a shift-invariant Gibbs measure. -/
theorem mem_invariantG_of_specificRelativeEntropy_eq_zero' (hΦ : Φ.IsShiftInvariant)
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h0 : Φ.specificRelativeEntropy ν μ = 0) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
      (shiftGroup (ι → ℤ) E) := by
  obtain ⟨ρ, hρ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty (Φ := Φ) ν 1 hΦ
  have : IsProbabilityMeasure ρ := hρ.1.1
  exact mem_invariantG_of_specificRelativeEntropy_eq_zero ν hΦ hμ hρ h0

/-- **Georgii Theorem (15.39), the variational principle**, unconditional over a standard Borel
state space: for a shift-invariant absolutely summable potential `Φ` and a shift-invariant random
field `μ ∈ 𝓟_Θ`, the specific relative entropy `𝓀(μ|Φ) = P(Φ) + ⟨μ, Φ⟩ − 𝓀(μ)` vanishes exactly
on `𝒢_Θ(Φ)`. This is `Potential.specificRelativeEntropy_eq_zero_iff_mem_invariantG` with the
hypothesis `𝒢_Θ(Φ) ≠ ∅` discharged by Theorem (4.23) and Corollary (5.16). -/
theorem specificRelativeEntropy_eq_zero_iff_mem_invariantG' (hΦ : Φ.IsShiftInvariant)
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    Φ.specificRelativeEntropy ν μ = 0 ↔
      μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
        (shiftGroup (ι → ℤ) E) :=
  ⟨fun h ↦ mem_invariantG_of_specificRelativeEntropy_eq_zero' ν hΦ hμ h,
    fun h ↦ specificRelativeEntropy_eq_zero_of_mem_invariantG ν hΦ h⟩

/-- **Georgii Theorem (15.39), free-energy form.** Over a standard Borel state space, a
shift-invariant random field `μ ∈ 𝓟_Θ` attains the minimum `−P(Φ)` of the specific free energy
`⟨·, Φ⟩ − 𝓀(·)` — equivalently `𝓀(μ) = ⟨μ, Φ⟩ + P(Φ)` — if and only if `μ ∈ 𝒢_Θ(Φ)`. The
inequality `𝓀(μ) ≤ ⟨μ, Φ⟩ + P(Φ)` on all of `𝓟_Θ` is
`Potential.specificEntropy_le_specificEnergy_add_pressure` and needs no hypothesis on `E`. -/
theorem specificEntropy_eq_specificEnergy_add_pressure_iff_mem_invariantG
    (hΦ : Φ.IsShiftInvariant) [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy ν μ = ((Φ.specificEnergy μ + Φ.pressure ν : ℝ) : EReal) ↔
      μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1)
        (shiftGroup (ι → ℤ) E) := by
  refine ⟨fun h ↦ mem_invariantG_of_specificRelativeEntropy_eq_zero' ν hΦ hμ ?_,
    fun h ↦ specificEntropy_eq_specificEnergy_add_pressure ν hΦ hμ h.1.2⟩
  rw [specificRelativeEntropy, add_comm (Φ.pressure ν), h, ← EReal.coe_sub, sub_self,
    EReal.coe_zero]

end StandardBorel

end Potential
