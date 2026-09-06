/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.Pi
public import GibbsMeasure.Specification.OrderParameterSpace

/-!
# Order parameters: pair potentials and the lattice gas (Georgii §16.3)

Comment (16.24)(3) and Example (16.25)(1) of Georgii's §16.3 read off the *shape* of the potentials
of `ℬ_Θ(f₁, …, f_N)` from the identification of its two descriptions
(`MeasureTheory.GibbsMeasure.mem_BThetaOrder_iff`, proved in
`GibbsMeasure/Specification/OrderParameterSpace.lean`).

## Main definitions

* `Potential.IsPairPotential`: **Georgii (2.16)**, a potential with `Φ_A = 0` whenever `|A| > 2`.
  Its natural home is `GibbsMeasure/Potential/Pair.lean`, next to `Potential.pair`.

## Main results

* `MeasureTheory.GibbsMeasure.isPairPotential_of_mem_BThetaOrder`: **Comment (16.24)(3),** first
  sentence. If the observables `f₁, …, f_N` are `𝓕_{\{0\}}`-measurable and `Λ₀ = {0}` is taken,
  then `ℬ_Θ(f₁, …, f_N)` consists of pair potentials: every volume carrying an interaction term is
  a translate of `Λ_0 = {0}` or of a two-point set `Λ_i = {0} ∪ {−i}`
  (`MeasureTheory.GibbsMeasure.card_le_two_of_mem_orderVolumes`).
* `MeasureTheory.GibbsMeasure.isGasPotential_of_mem_BThetaOrder_gasObservable`: **Example
  (16.25)(1),** the identification of the potentials as *gas potentials with vacuum state `0`*
  (`Potential.IsGasPotential`, Georgii (2.28)): the generating observables `1_{σ₀ = m}` and
  `1_{σ₀ = m} 1_{σ_{−i} = n}` vanish as soon as one of the spins of `Λ_0`, resp. `Λ_i`, is in the
  vacuum state `0`.
* `MeasureTheory.GibbsMeasure.exists_isPairPotential_isGasPotential_isDiscriminating`: **Example
  (16.25)(1),** the conclusion — for every `Φ⁰ ∈ ℬ_Θ` over `E = {0, …, N}` there is a *gas pair
  potential* `Φ¹` with vacuum state `0`, of arbitrarily long range, such that `Φ⁰ + Φ¹` has at
  least `N + 1` extreme shift-invariant Gibbs measures, discriminated by the densities
  `μ(1_{σ₀ = n})` of the `N` non-vacuum states.

* `MeasureTheory.GibbsMeasure.relativeEntropyIn_infinitePi` and
  `MeasureTheory.GibbsMeasure.specificEntropy_infinitePi`: **the specific entropy of a Bernoulli
  field**, `𝓀(α^S) = −𝓗(α | λ)`. This is the ingredient Georgii uses in Comment (16.24)(3) to
  place the product fields `λ(· | A)^S` in `𝓟^λ_Θ(Ω, 𝓕)`. It is a general fact about specific
  entropy, and its natural home is `GibbsMeasure/Specification/SpecificEntropy.lean`.

## Not formalised here

The converse inclusion in Example (16.25)(1) — that *every* shift-invariant absolutely summable
gas pair potential with vacuum state `0` lies in `ℬ_Θ(1_{σ₀=1}, …, 1_{σ₀=N})` — and the criterion
of Comment (16.24)(3) (the hypothesis of Theorem (16.21)(a) holds iff `1, f₁^*, …, f_N^*` are
linearly independent modulo `λ`-null sets), together with Comment (16.24)(4) and Example
(16.25)(2), are not in this file. The forward inclusions proved here are what Georgii's
conclusions in (16.25)(1) use. What is still missing for the criterion of (16.24)(3), on top of
`specificEntropy_infinitePi`, is the value `𝓗(λ(· | A) | λ) = −log λ(A)` of the relative entropy
of a conditioned measure, and the linear-algebra step producing disjoint sets `A_0, …, A_N` with
`(λ(1_{A_m} f_n^*))_{m,n}` of full rank.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (2.16).** A *pair potential* is a potential with `Φ_A = 0` whenever `|A| > 2`.
There is no restriction on the self-interactions `Φ_{\{i\}}`.

The natural home of this definition is `GibbsMeasure/Potential/Pair.lean`, next to
`Potential.pair`. -/
def IsPairPotential (Φ : Potential S E) : Prop := ∀ A : Finset S, 2 < #A → Φ A = 0

lemma IsPairPotential.add {Φ Ψ : Potential S E} (hΦ : IsPairPotential Φ)
    (hΨ : IsPairPotential Ψ) : IsPairPotential (Φ + Ψ) := fun A hA ↦ by
  funext η; rw [add_apply, hΦ A hA, hΨ A hA]; simp

lemma IsPairPotential.smul {Φ : Potential S E} (c : ℝ) (hΦ : IsPairPotential Φ) :
    IsPairPotential (c • Φ) := fun A hA ↦ by
  funext η; rw [smul_apply, hΦ A hA]; simp

end Potential

namespace MeasureTheory.GibbsMeasure

open Potential Potential.BTheta ProbabilityTheory

/-! ### Georgii Comment (16.24)(3): with `Λ₀ = {0}`, `ℬ_Θ(f₁, …, f_N)` consists of pair
potentials -/

section PairPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {N : ℕ}
  {f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {I : Set (ι → ℤ)}

omit [DecidableEq ι] [MeasurableSpace E] in
/-- With `Λ₀ = {0}` the volume `Λ_i = {0} ∪ {−i}` has at most two sites, and so has every
translate of it. -/
lemma card_le_two_of_mem_orderVolumes {A : Finset (ι → ℤ)}
    (hA : A ∈ orderVolumes ({0} : Finset (ι → ℤ)) I) : #A ≤ 2 := by
  obtain ⟨i, -, k, rfl⟩ := hA
  rw [translate, Finset.card_map]
  simpa using card_pairVolume_le ({0} : Finset (ι → ℤ)) i

omit [DecidableEq ι] in
/-- **Georgii Comment (16.24)(3).** If the observables `f₁, …, f_N` are `𝓕_{\{0\}}`-measurable and
`Λ₀ = {0}`, then `ℬ_Θ(f₁, …, f_N)` consists of pair potentials: the only volumes carrying an
interaction term are the translates of `Λ_0 = {0}` and of the two-point sets
`Λ_i = {0} ∪ {−i}`. -/
theorem isPairPotential_of_mem_BThetaOrder
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E {0}) (h0I : (0 : ι → ℤ) ∉ I)
    {Φ : BTheta (ι → ℤ) E} (hΦ : Φ ∈ BThetaOrder {0} f I) :
    IsPairPotential (Φ : Potential (ι → ℤ) E) := fun A hA ↦
  ((mem_BThetaOrder_iff (Finset.singleton_nonempty _) hf h0I).1 hΦ).2.2 A
    fun hc ↦ absurd (card_le_two_of_mem_orderVolumes hc) (by omega)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace E] in
/-- An observable in the span of finitely many observables vanishing at `ζ` vanishes at `ζ`. -/
lemma apply_eq_zero_of_mem_span_range {J : Type*} {g : J → (((ι → ℤ) → E) → ℝ)}
    {v : ((ι → ℤ) → E) → ℝ} (hv : v ∈ Submodule.span ℝ (Set.range g)) {ζ : (ι → ℤ) → E}
    (hg : ∀ j, g j ζ = 0) : v ζ = 0 := by
  have hker : Submodule.span ℝ (Set.range g) ≤ LinearMap.ker (LinearMap.proj (R := ℝ) ζ) :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; simpa [LinearMap.mem_ker] using hg j)
  simpa [LinearMap.mem_ker] using hker hv

end PairPotential

/-! ### Georgii Example (16.25)(1): the lattice gas potentials -/

section Gas

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] {N : ℕ}

omit [Fintype ι] [LinearOrder ι] [Nonempty ι] in
/-- The value of the lattice-gas observable `f_n = 1_{σ₀ = n}` at a configuration. -/
lemma coeFn_gasObservable (n : Fin N) (ζ : (ι → ℤ) → Fin (N + 1)) :
    ⇑(gasObservable ι n) ζ = if ζ 0 = n.succ then 1 else 0 := by
  rw [gasObservable, coeFn_indicatorLp]
  by_cases h : ζ 0 = n.succ
  · rw [Set.indicator_of_mem (show ζ ∈ {ω : (ι → ℤ) → Fin (N + 1) | ω 0 = n.succ} from h),
      ite_eq_left h]
  · rw [Set.indicator_of_notMem (show ζ ∉ {ω : (ι → ℤ) → Fin (N + 1) | ω 0 = n.succ} from h),
      ite_eq_right h]

omit [Fintype ι] [LinearOrder ι] [Nonempty ι] in
/-- A lattice-gas observable vanishes on configurations with vacuum state at the origin. -/
lemma gasObservable_apply_eq_zero (n : Fin N) {ζ : (ι → ℤ) → Fin (N + 1)} (h : ζ 0 = 0) :
    ⇑(gasObservable ι n) ζ = 0 := by
  rw [coeFn_gasObservable, ite_eq_right]
  rw [h]
  exact (Fin.succ_ne_zero n).symm

omit [LinearOrder ι] [Nonempty ι] in
/-- **Georgii Example (16.25)(1).** Every potential of `ℬ_Θ(1_{σ₀=1}, …, 1_{σ₀=N})` is a *gas
potential with vacuum state `0`*: the generating observables `f_n` and `f_m (f_n ∘ θ_i)` vanish as
soon as one of the spins in `Λ_0 = {0}`, resp. `Λ_i = {0, −i}`, is in the vacuum state. -/
theorem isGasPotential_of_mem_BThetaOrder_gasObservable {I : Set (ι → ℤ)} (h0I : (0 : ι → ℤ) ∉ I)
    {Φ : BTheta (ι → ℤ) (Fin (N + 1))} (hΦ : Φ ∈ BThetaOrder {0} (gasObservable ι) I) :
    IsGasPotential (0 : Fin (N + 1)) (Φ : Potential (ι → ℤ) (Fin (N + 1))) := by
  rw [mem_BThetaOrder_iff (Finset.singleton_nonempty _)
    (fun n ↦ gasObservable_mem_localFunctionsOn n) h0I] at hΦ
  intro A η hex
  obtain ⟨j, hjA, hj0⟩ := hex
  by_cases hA : A ∈ orderVolumes ({0} : Finset (ι → ℤ)) I
  · obtain ⟨i, hi, k, rfl⟩ := hA
    rw [apply_translate_of_isShiftInvariant (BTheta.isShiftInvariant Φ) _ k η]
    set ζ : (ι → ℤ) → Fin (N + 1) := (shift (Fin (N + 1)) (-k)).toFun η with hζ
    have hjζ : ζ (j - k) = 0 := by rw [hζ, shift_toFun_apply, sub_neg_eq_add, sub_add_cancel, hj0]
    have hmem : j - k ∈ pairVolume ({0} : Finset (ι → ℤ)) i := mem_translate.1 hjA
    rcases hi with h0 | hiI
    · have hj : j - k = 0 := by
        rw [h0, pairVolume_zero] at hmem
        simpa using hmem
      rw [h0, pairVolume_zero]
      refine apply_eq_zero_of_mem_span_range hΦ.1 fun n ↦ ?_
      exact gasObservable_apply_eq_zero n (by rw [← hj]; exact hjζ)
    · refine apply_eq_zero_of_mem_span_range (hΦ.2.1 i hiI) fun p ↦ ?_
      rw [pairVolume, Finset.mem_union] at hmem
      simp only [pairObservable, lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_precomp,
        Function.comp_apply]
      rcases hmem with hm | hm
      · have hj : j - k = 0 := by simpa using hm
        rw [gasObservable_apply_eq_zero p.1 (by rw [← hj]; exact hjζ), zero_mul]
      · have hj : j - k = -i := by
          rw [mem_translate] at hm
          simpa [sub_neg_eq_add, eq_comm, ← sub_eq_zero] using hm
        have h2 : ((shift (Fin (N + 1)) i).toFun ζ) 0 = 0 := by
          rw [shift_toFun_apply, zero_sub, ← hj]; exact hjζ
        rw [gasObservable_apply_eq_zero p.2 h2, mul_zero]
  · rw [hΦ.2.2 A hA]
    rfl

/-- **Georgii Example (16.25)(1), the conclusion.** For every `Φ⁰ ∈ ℬ_Θ` over the state space
`E = {0, …, N}` there is a *gas pair potential* `Φ¹ = Φ − Φ⁰` with vacuum state `0` such that
`Φ⁰ + Φ¹` has at least `N + 1` extreme shift-invariant Gibbs measures, told apart by the densities
`μ(1_{σ₀ = n})` of the `N` non-vacuum states. The interaction terms on any prescribed finite
family of volumes `Λ_i` can be required to vanish (Comment (16.24)(1)), so `Φ¹` can be made of
arbitrarily long range. -/
theorem exists_isPairPotential_isGasPotential_isDiscriminating {I : Set (ι → ℤ)} (hI : Iᶜ.Finite)
    (h0I : (0 : ι → ℤ) ∉ I) (Φ₀ : BTheta (ι → ℤ) (Fin (N + 1))) :
    ∃ Φ : BTheta (ι → ℤ) (Fin (N + 1)),
      IsPairPotential ((Φ - Φ₀ : BTheta (ι → ℤ) (Fin (N + 1))) :
        Potential (ι → ℤ) (Fin (N + 1))) ∧
      IsGasPotential (0 : Fin (N + 1)) ((Φ - Φ₀ : BTheta (ι → ℤ) (Fin (N + 1))) :
        Potential (ι → ℤ) (Fin (N + 1))) ∧
      IsDiscriminating (invariantG (gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) (Fin (N + 1)))) (uniformOn Set.univ) 1)
          (shiftGroup (ι → ℤ) (Fin (N + 1)))) (gasObservable ι) ∧
      ((N : ℕ∞) + 1) ≤ ((invariantG (gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) (Fin (N + 1)))) (uniformOn Set.univ) 1)
          (shiftGroup (ι → ℤ) (Fin (N + 1)))).extremePoints ℝ≥0∞).encard := by
  obtain ⟨Φ, hmem, hdisc, hcard⟩ := exists_isDiscriminating_gasObservable hI Φ₀
  exact ⟨Φ, isPairPotential_of_mem_BThetaOrder
      (fun n ↦ gasObservable_mem_localFunctionsOn n) h0I hmem,
    isGasPotential_of_mem_BThetaOrder_gasObservable h0I hmem, hdisc, hcard⟩

end Gas

/-! ### The specific entropy of a Bernoulli field

Georgii's Comment (16.24)(3) needs the specific entropy of an i.i.d. random field `α^S`, namely
`𝓀(α^S) = −𝓗(α | λ)`. The natural home of this section is
`GibbsMeasure/Specification/SpecificEntropy.lean`, next to `specificEntropy`. -/

section BernoulliField

open InformationTheory

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (α lam : Measure E)
  [IsProbabilityMeasure α] [IsProbabilityMeasure lam]

omit [Fintype ι] [DecidableEq ι] in
/-- **The relative entropy of an i.i.d. field in a finite volume** is `|Δ|` times the relative
entropy of the single-site laws: the coordinates are independent, and the Kullback–Leibler
divergence of a product is the sum of the divergences (`InformationTheory.klDiv_pi`). -/
theorem relativeEntropyIn_infinitePi (Δ : Finset (ι → ℤ)) :
    relativeEntropyIn (Δ : Set (ι → ℤ)) (Measure.infinitePi fun _ : ι → ℤ ↦ α)
        (Measure.infinitePi fun _ : ι → ℤ ↦ lam) = #Δ * klDiv α lam := by
  rw [relativeEntropyIn_coe_finset, Measure.infinitePi_map_restrict,
    Measure.infinitePi_map_restrict, klDiv_pi_const, Fintype.card_coe]

/-- **The specific entropy of a Bernoulli field:** `𝓀(α^S) = −𝓗(α | λ)`. In particular `α^S` has
finite specific entropy exactly when `𝓗(α | λ) < ∞`, which is Georgii's condition for
`α^S ∈ 𝓟^λ_Θ(Ω, 𝓕)`. -/
theorem specificEntropy_infinitePi :
    specificEntropy lam (Measure.infinitePi fun _ : ι → ℤ ↦ α) = -(klDiv α lam : EReal) := by
  have key : ∀ Δ : Finset (ι → ℤ), Δ.IsBox →
      entropyIn lam (Δ : Set (ι → ℤ)) (Measure.infinitePi fun _ : ι → ℤ ↦ α) / (#Δ : EReal)
        = -(klDiv α lam : EReal) := by
    intro Δ hΔ
    have hpos : 0 < #Δ := hΔ.nonempty.card_pos
    have hne : (#Δ : EReal) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := EReal)).2 hpos.ne'
    rw [entropyIn, relativeEntropyIn_infinitePi α lam Δ,
      EReal.div_eq_iff (EReal.natCast_ne_bot _) (EReal.natCast_ne_top _) hne,
      EReal.coe_ennreal_mul]
    have hcast : ∀ n : ℕ, (((n : ℝ≥0∞)) : EReal) = (n : EReal) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih => push_cast; rw [ih]
    rw [neg_mul, mul_comm, hcast]
  refine le_antisymm ?_ (le_iInf fun Δ ↦ le_iInf fun hΔ ↦ (key Δ hΔ).ge)
  exact (iInf₂_le ({0} : Finset (ι → ℤ)) (Finset.isBox_singleton 0)).trans
    (le_of_eq (key _ (Finset.isBox_singleton 0)))

end BernoulliField

end MeasureTheory.GibbsMeasure

end

end
