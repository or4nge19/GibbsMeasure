/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.KernelDomination
public import GibbsMeasure.Specification.PeriodicGibbsLimits

/-!
# The single-site Hamiltonian and single-site kernel of a `C`-potential

For Georgii's `C`-potential (17.18) with cube interaction `Φ_C = φ` on `ℤ^d`, the Hamiltonian in
a single site `{i}` is the sum of the `2^d` cube interactions of the elementary cubes containing
`i`.  Consequently its oscillation in the spin at `i` is at most `2^d` times the oscillation of
`φ` in a single corner, and the single-site Gibbs kernel is dominated by the a priori measure with
that Boltzmann constant.

* `MeasureTheory.GibbsMeasure.hamiltonian_cubePotential_singleton`:
  `H_{\{i\}} = ∑_{c ∈ C} Φ_C ∘ θ_{-(i - c)}`.
* `MeasureTheory.GibbsMeasure.hamiltonian_cubePotential_singleton_sub_le`: the oscillation bound
  `H_{\{i\}}(σ) - H_{\{i\}}(σ') ≤ 2^d κ` for `σ, σ'` differing only at `i`, from a one-corner
  oscillation bound `κ` for `φ`.
* `MeasureTheory.GibbsMeasure.cubeGibbsSpec_singleton_apply_le` and
  `MeasureTheory.GibbsMeasure.cubeGibbsSpec_singleton_apply_preimage_eval_le`: the resulting
  bound `γ^Φ_{\{i\}}(A|η) ≤ e^{2^d κ} λ_{\{i\}}(A|η)`, and its form for an event `{σ_i ∈ B}`,
  `γ^Φ_{\{i\}}(σ_i ∈ B|η) ≤ e^{2^d κ} λ(B)`, which uses
  `Specification.sigmaFiniteLambdaFun_singleton_apply_preimage_eval`: the a priori kernel at a
  single site is the a priori measure of the spin there.

The inverse temperature is carried by `φ` itself (`βΦ` is the `C`-potential of `β φ`), as
everywhere in `GibbsMeasure/Specification/PeriodicGibbsLimits.lean` and
`GibbsMeasure/Model/LowEnergyOceans.lean`, so no `β` appears below.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Specification

/-! ### The single-site a priori kernel -/

variable {S E : Type*} [MeasurableSpace E]

/-- **The a priori kernel at a single site reads off the a priori measure**: for a probability
a priori measure `λ`, `λ_{\{i\}}(σ_i ∈ B | η) = λ(B)`.  All the other coordinates of
`λ_{\{i\}}(·|η)` are frozen at `η`, so the product measure collapses to its `i`-th factor. -/
lemma sigmaFiniteLambdaFun_singleton_apply_preimage_eval (ν : Measure E) [IsProbabilityMeasure ν]
    (i : S) (η : S → E) {B : Set E} (hB : MeasurableSet B) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν {i} η ((fun σ : S → E ↦ σ i) ⁻¹' B) = ν B := by
  classical
  have hi : i ∈ ((({i} : Finset S) : Set S)) := by simp
  have hjuxt : Measurable (juxt (Λ := ((({i} : Finset S)) : Set S)) η) :=
    Measurable.juxt (Λ := ((({i} : Finset S)) : Set S)) (η := η) (𝓔 := ‹MeasurableSpace E›)
  have hpre : (juxt ((({i} : Finset S)) : Set S) η) ⁻¹' ((fun σ : S → E ↦ σ i) ⁻¹' B)
      = Function.eval (⟨i, hi⟩ : ((({i} : Finset S)) : Set S)) ⁻¹' B := by
    ext x
    simp [Function.eval]
  rw [sigmaFiniteLambdaFun_apply_eq_map, Measure.map_apply hjuxt ((measurable_pi_apply i) hB),
    hpre]
  exact (measurePreserving_eval (μ := fun _ : ((({i} : Finset S)) : Set S) ↦ ν)
    ⟨i, hi⟩).measure_preimage hB.nullMeasurableSet

end Specification

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d : ℕ} {φ : ((Fin d → Fin 2) → E) → ℝ}

/-! ### The corners of the cubes containing a site -/

lemma intCubeCast_injective : Function.Injective (intCubeCast (d := d)) := by
  intro c c' h
  funext k
  have := congrFun h k
  simp only [intCubeCast] at this
  exact Fin.val_injective (Nat.cast_injective this)

/-- The elementary cubes containing the site `i` are the `2^d` cubes `C + (i - c)`, `c ∈ C`, and
they are pairwise distinct. -/
lemma latticeCube_sub_intCubeCast_injective (i : Fin d → ℤ) :
    Function.Injective fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c) := fun c c' h ↦
  intCubeCast_injective (by simpa using latticeCube_injective h)

lemma mem_latticeCube_sub_intCubeCast (i : Fin d → ℤ) (c : Fin d → Fin 2) :
    i ∈ latticeCube (i - intCubeCast c) :=
  mem_latticeCube_iff.2 ⟨c, by ring⟩

/-- A cube containing `i` is one of the `2^d` cubes `C + (i - c)`. -/
lemma exists_eq_latticeCube_sub_intCubeCast {i j : Fin d → ℤ} (h : i ∈ latticeCube j) :
    ∃ c : Fin d → Fin 2, j = i - intCubeCast c := by
  obtain ⟨c, hc⟩ := mem_latticeCube_iff.1 h
  exact ⟨c, by rw [← hc]; ring⟩

/-! ### The single-site Hamiltonian -/

/-- **The single-site Hamiltonian of a `C`-potential.**  `H_{\{i\}}` is the sum of the cube
interactions of the `2^d` elementary cubes containing `i`; these are the only sets on which the
potential is both nonzero and meets `{i}`. -/
theorem hamiltonian_cubePotential_singleton (i : Fin d → ℤ) (σ : (Fin d → ℤ) → E) :
    (cubePotential E φ).hamiltonian {i} σ
      = ∑ c : Fin d → Fin 2, φ (latticeCubeView σ (i - intCubeCast c)) := by
  classical
  have hzero : ∀ A ∉ Finset.univ.image fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c),
      (cubePotential E φ).hamiltonianTerms {i} σ A = 0 := by
    intro A hA
    by_cases hd : Disjoint A ({i} : Finset (Fin d → ℤ))
    · exact Potential.hamiltonianTerms_of_disjoint hd σ
    · rw [Potential.hamiltonianTerms_of_not_disjoint hd σ]
      have hi : i ∈ A := by
        obtain ⟨x, hxA, hx⟩ := Finset.not_disjoint_iff.1 hd
        rwa [Finset.mem_singleton.1 hx] at hxA
      refine congrFun (cubePotential_eq_zero_of_forall fun j hj ↦ ?_) σ
      obtain ⟨c, rfl⟩ :=
        exists_eq_latticeCube_sub_intCubeCast (show i ∈ latticeCube j by rw [hj]; exact hi)
      exact hA (hj ▸ Finset.mem_image_of_mem
        (fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c)) (Finset.mem_univ c))
  have hsum : HasSum ((cubePotential E φ).hamiltonianTerms {i} σ)
      (∑ A ∈ Finset.univ.image fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c),
        (cubePotential E φ).hamiltonianTerms {i} σ A) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [Potential.hamiltonian, hsum.volume.tsum_eq,
    Finset.sum_image fun c _ c' _ h ↦ latticeCube_sub_intCubeCast_injective i h]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Potential.hamiltonianTerms_of_not_disjoint
      (Finset.not_disjoint_iff.2 ⟨i, mem_latticeCube_sub_intCubeCast i c,
        Finset.mem_singleton_self i⟩) σ,
    cubePotential_latticeCube]

omit [MeasurableSpace E] in
/-- Two configurations differing only at `i` give, in each of the `2^d` cubes containing `i`,
views that differ only at the corresponding corner. -/
lemma latticeCubeView_sub_intCubeCast_congr {i : Fin d → ℤ} {σ σ' : (Fin d → ℤ) → E}
    (h : ∀ j, j ≠ i → σ j = σ' j) (c c' : Fin d → Fin 2) (hc' : c' ≠ c) :
    latticeCubeView σ (i - intCubeCast c) c' = latticeCubeView σ' (i - intCubeCast c) c' := by
  refine h _ fun hj ↦ hc' (intCubeCast_injective (funext fun k ↦ ?_))
  have hk := congrFun hj k
  simp only [Pi.add_apply, Pi.sub_apply] at hk
  omega

/-- **The oscillation of the single-site Hamiltonian of a `C`-potential.**  If the cube
interaction `φ` changes by at most `κ` when a single corner of the cube is changed, then
`H_{\{i\}}` changes by at most `2^d κ` when the spin at `i` is changed: the site `i` lies in `2^d`
cubes, and in each of them it is one corner. -/
theorem hamiltonian_cubePotential_singleton_sub_le {κ : ℝ}
    (hκ : ∀ (ζ ζ' : (Fin d → Fin 2) → E) (c : Fin d → Fin 2),
      (∀ c', c' ≠ c → ζ c' = ζ' c') → φ ζ - φ ζ' ≤ κ)
    (i : Fin d → ℤ) {σ σ' : (Fin d → ℤ) → E} (h : ∀ j, j ≠ i → σ j = σ' j) :
    (cubePotential E φ).hamiltonian {i} σ - (cubePotential E φ).hamiltonian {i} σ'
      ≤ 2 ^ d * κ := by
  rw [hamiltonian_cubePotential_singleton, hamiltonian_cubePotential_singleton,
    ← Finset.sum_sub_distrib]
  calc ∑ c : Fin d → Fin 2, (φ (latticeCubeView σ (i - intCubeCast c))
        - φ (latticeCubeView σ' (i - intCubeCast c)))
      ≤ ∑ _c : Fin d → Fin 2, κ :=
        Finset.sum_le_sum fun c _ ↦ hκ _ _ c fun c' hc' ↦
          latticeCubeView_sub_intCubeCast_congr h c c' hc'
    _ = 2 ^ d * κ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        norm_num

/-! ### The single-site Gibbs kernel of a `C`-potential -/

variable {ν : Measure E} [IsProbabilityMeasure ν]

/-- **The single-site Gibbs kernel of a `C`-potential is dominated by its a priori kernel**, with
the Boltzmann constant of the one-corner oscillation `κ` of `Φ_C`:
`γ^Φ_{\{i\}}(A|η) ≤ e^{2^d κ} λ_{\{i\}}(A|η)`. -/
theorem cubeGibbsSpec_singleton_apply_le (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {κ : ℝ} (hκ : ∀ (ζ ζ' : (Fin d → Fin 2) → E) (c : Fin d → Fin 2),
      (∀ c', c' ≠ c → ζ c' = ζ' c') → φ ζ - φ ζ' ≤ κ)
    (i : Fin d → ℤ) (η : (Fin d → ℤ) → E) {A : Set ((Fin d → ℤ) → E)} (hA : MeasurableSet A) :
    cubeGibbsSpec E φ ν hφ hM {i} η A
      ≤ ENNReal.ofReal (Real.exp (2 ^ d * κ)) *
        Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := E) ν {i} η A := by
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  simp only [cubeGibbsSpec]
  refine Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le
    (cubePotential E φ) ν 1 _ {i} η (fun σ σ' hσ hσ' ↦ ?_) hA
  rw [one_mul]
  refine hamiltonian_cubePotential_singleton_sub_le hκ i fun j hj ↦ ?_
  rw [hσ' j (by simpa using hj), hσ j (by simpa using hj)]

/-- **Georgii's `γ^{βΦ}_{\{i\}}(σ_i ∈ B | ω) ≤ e^{2^d κ} λ̃(B)`** in Example (18.19): the
conditional probability of a single-site event is at most a fixed multiple of its a priori
probability. -/
theorem cubeGibbsSpec_singleton_apply_preimage_eval_le (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) {κ : ℝ}
    (hκ : ∀ (ζ ζ' : (Fin d → Fin 2) → E) (c : Fin d → Fin 2),
      (∀ c', c' ≠ c → ζ c' = ζ' c') → φ ζ - φ ζ' ≤ κ)
    (i : Fin d → ℤ) (η : (Fin d → ℤ) → E) {B : Set E} (hB : MeasurableSet B) :
    cubeGibbsSpec E φ ν hφ hM {i} η ((fun σ : (Fin d → ℤ) → E ↦ σ i) ⁻¹' B)
      ≤ ENNReal.ofReal (Real.exp (2 ^ d * κ)) * ν B := by
  rw [← Specification.sigmaFiniteLambdaFun_singleton_apply_preimage_eval ν i η hB]
  exact cubeGibbsSpec_singleton_apply_le hφ hM hκ i η ((measurable_pi_apply i) hB)

end MeasureTheory.GibbsMeasure
