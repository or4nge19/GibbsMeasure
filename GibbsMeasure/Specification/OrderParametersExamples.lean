/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.Cond
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

* `MeasureTheory.GibbsMeasure.isDiscriminating_invariantFieldsOfFiniteEntropy_iff`: **the
  criterion of Comment (16.24)(3)** — for single-site observables `f_n = f_n^* ∘ σ₀` the hypothesis
  of Theorem (16.21)(a) holds exactly when `1, f₁^*, …, f_N^*` are linearly independent modulo
  `λ`-null sets, i.e. `λ(f_a^* ≠ c) > 0` for all `a ≠ 0` and all `c`. Its two halves are the
  conditioned product fields `λ(· | A)^S ∈ 𝓟^λ_Θ`
  (`infinitePi_cond_mem_invariantFieldsOfFiniteEntropy`, from `specificEntropy_infinitePi_cond`:
  `𝓀(λ(· | A)^S) = log λ(A)`) and the absolute continuity `σ₀ μ ≪ λ` of the single-site marginal
  of any `μ ∈ 𝓟^λ_Θ` (`absolutelyContinuous_map_eval_of_specificEntropy_ne_bot`).
* `MeasureTheory.GibbsMeasure.isDiscriminating_precomp_eval_iff` and
  `MeasureTheory.GibbsMeasure.exists_isDiscriminating_neg_integral_lt_integral`: **Example
  (16.25)(2)**. For a bounded measurable spin `s : E → ℝ` which is not `λ`-almost surely constant
  (Georgii's non-degenerate `λ` on an even bounded `E ⊆ ℝ`, with `s` the inclusion) every
  `Φ⁰ ∈ ℬ_Θ` can be modified inside the *ferromagnetic* cone `ℬ⁻_Θ(σ₀)`, with arbitrarily long
  range, into a potential admitting two shift-invariant Gibbs measures of different magnetisation
  `μ₁(σ₀) < μ₂(σ₀)`.
* `MeasureTheory.GibbsMeasure.isNormalized_of_mem_BThetaOrder`,
  `MeasureTheory.GibbsMeasure.exists_isNormalized_isDiscriminating_norm_sub_lt` and
  `MeasureTheory.GibbsMeasure.not_isEquivalent_of_coe_apply_ne`: **Comment (16.24)(4)**. If
  `α(f_n^*) = 0` then `ℬ_Θ(f₁, …, f_N)` consists of `α`-normalized pair potentials
  (`avgOn_singleton_eq_integral_update` reduces the check to a single-site average); therefore the
  potentials produced by (16.21)(b) from `α`-normalized `Φ⁰`'s are `α`-normalized, agree with
  `Φ⁰` off the volumes the modification touches, and — being distinct `α`-normalized potentials —
  are pairwise non-equivalent (Georgii's "point", through
  `Potential.BTheta.not_isEquivalent_of_ne_of_isNormalized`, i.e. Theorem (2.35)(a)).

## Not formalised here

The converse inclusion in Example (16.25)(1) — that *every* shift-invariant absolutely summable
gas pair potential with vacuum state `0` lies in `ℬ_Θ(1_{σ₀=1}, …, 1_{σ₀=N})` — is not proved; the
forward inclusion is what Georgii's conclusions in (16.25)(1) use. In Example (16.25)(2) only the
inclusion `ℬ⁻_Θ(σ₀) ⊆ {ferromagnetic pair potentials}` is *used*, and the explicit description of
`ℬ⁻_Θ(σ₀)` as the potentials `Φ_{\{i,j\}} = −J(i−j) σ_i σ_j`, `Φ_{\{i\}} = −h σ_i` with `J ≥ 0`
even and summable is not proved: `mem_BThetaOrder_iff` describes the closed *linear span*
`ℬ_Θ(f)`, and the analogous membership criterion for the closed convex *cone* `ℬ⁻_Θ(f)` is
missing. The Heisenberg Theorem (16.27) with its setting (16.26) is not formalised anywhere in the
tree.
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

/-! ### Georgii Comment (16.24)(3): when does the hypothesis of Theorem (16.21)(a) hold?

For `𝓕_{\{0\}}`-measurable observables `f_n = f_n^* ∘ σ₀` Georgii's criterion says that the
hypothesis of Theorem (16.21)(a) — the existence of `N + 1` measures of `𝓟^λ_Θ(Ω, 𝓕)` whose matrix
of expectations `(μ_m(f_n))_{0 ≤ m,n ≤ N}` has full rank — holds exactly when `1, f₁^*, …, f_N^*`
are linearly independent modulo `λ`-null sets, i.e. when `λ(f_a^* ≠ c) > 0` for all `a ≠ 0` and all
`c ∈ ℝ`.

The natural home of `specificEntropy_infinitePi_cond` and
`absolutelyContinuous_map_eval_of_specificEntropy_ne_bot` is
`GibbsMeasure/Specification/SpecificEntropy.lean`, next to `specificEntropy`. -/

section Criterion1624

open InformationTheory ProbabilityTheory

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {N : ℕ}

/-- The observable `σ₀`, that is `s ∘ σ₀` for a bounded measurable `s : E → ℝ`, is
`𝓕_{\{0\}}`-measurable. -/
lemma precomp_eval_mem_localFunctionsOn {s : lp (fun _ : E ↦ ℝ) ∞} (hs : Measurable ⇑s) :
    lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) s ∈ localFunctionsOn (ι → ℤ) E {0} := by
  exact mem_localFunctionsOn.2 (hs.comp (measurable_cylinderEvent_apply
    (show (0 : ι → ℤ) ∈ ((({0} : Finset (ι → ℤ)) : Finset (ι → ℤ)) : Set (ι → ℤ)) by simp)))

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii, in the proof of Comment (16.24)(3):** the specific entropy of the i.i.d. field
`λ(· | A)^S` is `𝓀(λ(· | A)^S) = log λ(A)`: the specific entropy of a Bernoulli field is minus the
relative entropy of its single-site law (`specificEntropy_infinitePi`), and
`𝓗(λ(· | A) | λ) = −log λ(A)` (`InformationTheory.klDiv_cond_self`). In particular it is finite as
soon as `λ(A) > 0`, so `λ(· | A)^S ∈ 𝓟^λ_Θ(Ω, 𝓕)`. -/
theorem specificEntropy_infinitePi_cond {A : Set E} (hA : MeasurableSet A) (hA0 : ν A ≠ 0) :
    specificEntropy (ι := ι) ν (Measure.infinitePi fun _ : ι → ℤ ↦ ν[|A])
      = ((Real.log (ν.real A) : ℝ) : EReal) := by
  have : IsProbabilityMeasure (ν[|A]) := cond_isProbabilityMeasure hA0
  have hle : ν.real A ≤ 1 := by
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hlog : Real.log (ν.real A) ≤ 0 :=
    Real.log_nonpos ENNReal.toReal_nonneg hle
  rw [specificEntropy_infinitePi (ν[|A]) ν, klDiv_cond_self hA hA0, EReal.coe_ennreal_ofReal,
    max_eq_left (by linarith), ← EReal.coe_neg, neg_neg]

/-- **Georgii Comment (16.24)(3).** `λ(· | A)^S` is a shift-invariant random field of finite
specific entropy. -/
theorem infinitePi_cond_mem_invariantFieldsOfFiniteEntropy {A : Set E} (hA : MeasurableSet A)
    (hA0 : ν A ≠ 0) :
    (Measure.infinitePi fun _ : ι → ℤ ↦ ν[|A])
      ∈ Potential.BTheta.invariantFieldsOfFiniteEntropy ι E ν := by
  have : IsProbabilityMeasure (ν[|A]) := cond_isProbabilityMeasure hA0
  -- `α^S ∈ 𝓟_Θ`; the named form is `infinitePi_mem_invariantFields_shiftGroup` in
  -- `GibbsMeasure/Specification/BlockMcMillan.lean`, which this file does not import.
  exact ⟨mem_invariantFields_shiftGroup.2
      ⟨inferInstance, measurePreserving_shift_infinitePi (ν[|A])⟩,
    by rw [specificEntropy_infinitePi_cond ν hA hA0]; simp⟩

/-- **Georgii, in the proof of Comment (16.24)(3):** a random field with `𝓀(μ) > −∞` satisfies
`𝓗_{\{0\}}(μ) < ∞`, so its single-site marginal `σ₀ μ` is absolutely continuous with respect to the
a priori measure `λ`. -/
theorem absolutelyContinuous_map_eval_of_specificEntropy_ne_bot
    {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ] (hμ : specificEntropy ν μ ≠ ⊥) :
    (μ.map fun ω : (ι → ℤ) → E ↦ ω 0) ≪ ν := by
  classical
  have h0 : (0 : ι → ℤ) ∈ ({0} : Finset (ι → ℤ)) := Finset.mem_singleton_self _
  have hfin : relativeEntropyIn ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ))) μ
      (Measure.infinitePi fun _ : ι → ℤ ↦ ν) ≠ ⊤ := by
    intro htop
    refine hμ (le_bot_iff.1 ?_)
    have h := specificEntropy_le_entropyIn_div_card (E := E) ν (μ := μ)
      (Finset.isBox_singleton (0 : ι → ℤ))
    have hbot : entropyIn ν ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ))) μ
        / ((#({0} : Finset (ι → ℤ)) : ℕ) : EReal) = ⊥ := by
      rw [entropyIn, htop, EReal.coe_ennreal_top, EReal.neg_top]
      simp
    rwa [hbot] at h
  rw [relativeEntropyIn_coe_finset ({0} : Finset (ι → ℤ))] at hfin
  have hac := (klDiv_ne_top_iff.1 hfin).1
  rw [Measure.infinitePi_map_restrict] at hac
  have hev : Measurable fun x : (({0} : Finset (ι → ℤ)) : Type _) → E ↦ x ⟨0, h0⟩ :=
    measurable_pi_apply (⟨0, h0⟩ : (({0} : Finset (ι → ℤ)) : Type _))
  have h1 : (μ.map fun ω : (ι → ℤ) → E ↦ ω 0)
      = (μ.map ({0} : Finset (ι → ℤ)).restrict).map fun x ↦ x ⟨0, h0⟩ := by
    rw [Measure.map_map hev (Finset.measurable_restrict ({0} : Finset (ι → ℤ)))]
    rfl
  have h2 : ((Measure.pi fun _ : (({0} : Finset (ι → ℤ)) : Type _) ↦ ν).map
      fun x ↦ x ⟨0, h0⟩) = ν :=
    (MeasureTheory.measurePreserving_eval
      (μ := fun _ : (({0} : Finset (ι → ℤ)) : Type _) ↦ ν) ⟨0, h0⟩).map_eq
  rw [h1, ← h2]
  exact hac.map hev

/-- **Georgii Comment (16.24)(3), the criterion.** Let `f_n = f_n^* ∘ σ₀` be
`𝓕_{\{0\}}`-measurable observables. The hypothesis of Theorem (16.21)(a) — that `{f₁, …, f_N}` be a
discriminating system for `𝓟^λ_Θ(Ω, 𝓕)` — holds exactly when `1, f₁^*, …, f_N^*` are linearly
independent modulo `λ`-null sets, that is, when `λ(f_a^* ≠ c) > 0` for every `a ∈ ℝ^N ∖ {0}` and
every `c ∈ ℝ`.

For "if", the conditioned product fields `λ(· | A)^S` already span: they lie in `𝓟^λ_Θ`
(`infinitePi_cond_mem_invariantFieldsOfFiniteEntropy`) with expectations `λ(1_A f_n^*)/λ(A)`, so a
covector `b` annihilating all of them makes `b₀ + f_{b'}^*` integrate to `0` over every measurable
set, hence vanish `λ`-almost surely; `b' ≠ 0` contradicts the hypothesis and `b' = 0` forces
`b₀ = 0`. For "only if", every `μ ∈ 𝓟^λ_Θ` has `σ₀ μ ≪ λ`
(`absolutelyContinuous_map_eval_of_specificEntropy_ne_bot`), so `μ(f_a) = c` for all of them and
the covector `(−c, a) ≠ 0` annihilates every row of the matrix of expectations.

Georgii deduces "only if" from the proof of Lemma (16.20)(i) ⇒ (ii); the direct argument used here
is the same computation without the detour through the variance. Georgii also asks the sets
`A_0, …, A_N` produced in the proof of "if" to be disjoint; disjointness is not needed, since only
the ranks of `(λ(1_{A_m} f_n^*))_{m,n}` and of `(μ_m(f_n))_{m,n}` have to agree. -/
theorem isDiscriminating_invariantFieldsOfFiniteEntropy_iff
    {fstar : Fin N → lp (fun _ : E ↦ ℝ) ∞} (hfsm : ∀ n, Measurable ⇑(fstar n))
    {f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
    (hf : ∀ n, ⇑(f n) = fun ω : (ι → ℤ) → E ↦ ⇑(fstar n) (ω 0)) :
    IsDiscriminating (Potential.BTheta.invariantFieldsOfFiniteEntropy ι E ν) f ↔
      ∀ a : Fin N → ℝ, a ≠ 0 → ∀ c : ℝ, ν {x : E | ∑ n, a n * ⇑(fstar n) x ≠ c} ≠ 0 := by
  classical
  have hcombom : ∀ a : Fin N → ℝ, Measurable fun x : E ↦ ∑ n, a n * ⇑(fstar n) x := fun a ↦
    Finset.measurable_sum _ fun n _ ↦ (hfsm n).const_mul _
  have hfm : ∀ n, Measurable ⇑(f n) := fun n ↦ by
    rw [hf n]; exact (hfsm n).comp (measurable_pi_apply (0 : ι → ℤ))
  constructor
  · rintro ⟨μ, hμ, hdet⟩ a ha c hc
    have hprob : ∀ m, IsProbabilityMeasure (μ m) := fun m ↦ (hμ m).1.1
    have hmeas : MeasurableSet {x : E | ∑ n, a n * ⇑(fstar n) x ≠ c} :=
      ((measurableSet_singleton c).preimage (hcombom a)).compl
    have hset : {ω : (ι → ℤ) → E | ∑ n, a n * ⇑(f n) ω ≠ c}
        = (fun ω : (ι → ℤ) → E ↦ ω 0) ⁻¹' {x : E | ∑ n, a n * ⇑(fstar n) x ≠ c} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hf, ne_eq]
    have hmean : ∀ m, ∑ k, a k * ∫ ω, ⇑(f k) ω ∂(μ m) = c := by
      intro m
      haveI := hprob m
      have hac := absolutelyContinuous_map_eval_of_specificEntropy_ne_bot ν (μ := μ m) (hμ m).2
      have hnull : (μ m) {ω : (ι → ℤ) → E | ∑ n, a n * ⇑(f n) ω ≠ c} = 0 := by
        rw [hset, ← Measure.map_apply (measurable_pi_apply (0 : ι → ℤ)) hmeas]
        exact hac hc
      have hae : ∀ᵐ ω ∂(μ m), ∑ n, a n * ⇑(f n) ω = c := MeasureTheory.ae_iff.2 hnull
      calc ∑ k, a k * ∫ ω, ⇑(f k) ω ∂(μ m)
          = ∫ ω, ∑ k, a k * ⇑(f k) ω ∂(μ m) := by
            rw [integral_finset_sum _ fun k _ ↦
              ((lp.integrable_of_measurable (hfm k) (μ m)).const_mul _)]
            exact Finset.sum_congr rfl fun k _ ↦ (integral_const_mul _ _).symm
        _ = c := by rw [integral_congr_ae hae, integral_const]; simp [Measure.real]
    refine hdet ?_
    by_contra hne
    refine Submodule.span_ne_top_of_forall_sum_mul_eq_zero (b := Fin.cases (-c) a) ?_ ?_
      (Matrix.det_ne_zero_iff_span_range_row_eq_top.1 hne)
    · obtain ⟨k, hk⟩ := Function.ne_iff.1 ha
      exact Function.ne_iff.2 ⟨k.succ, by simpa using hk⟩
    · rintro _ ⟨m, rfl⟩
      haveI := hprob m
      rw [observableMatrix_row, Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, observableVector_zero, observableVector_succ,
        mul_one]
      have := hmean m
      linarith
  · intro hli
    rw [isDiscriminating_iff_span_eq_top, Submodule.span_eq_top_iff_forall_sum_mul_eq_zero]
    intro b hb
    set g : E → ℝ := fun x ↦ b 0 + ∑ k : Fin N, b k.succ * ⇑(fstar k) x with hgdef
    have hgint : ∀ (m : Measure E) [IsProbabilityMeasure m], Integrable g m := by
      intro m _
      exact (integrable_const _).add (integrable_finset_sum _ fun k _ ↦
        (lp.integrable_of_measurable (hfsm k) m).const_mul _)
    have hgval : ∀ (m : Measure E) [IsProbabilityMeasure m],
        ∫ x, g x ∂m = b 0 + ∑ k : Fin N, b k.succ * ∫ x, ⇑(fstar k) x ∂m := by
      intro m _
      have h1 : Integrable (fun x : E ↦ ∑ k : Fin N, b k.succ * ⇑(fstar k) x) m :=
        integrable_finset_sum _ fun k _ ↦ (lp.integrable_of_measurable (hfsm k) m).const_mul _
      rw [hgdef, integral_add (integrable_const _) h1, integral_const,
        integral_finset_sum _ fun k _ ↦ (lp.integrable_of_measurable (hfsm k) m).const_mul _]
      simp_rw [integral_const_mul]
      simp [Measure.real]
    have hzero : ∀ A : Set E, MeasurableSet A → ν A < ⊤ → ∫ x in A, g x ∂ν = 0 := by
      intro A hA _
      rcases eq_or_ne (ν A) 0 with h0 | h0
      · exact setIntegral_measure_zero g h0
      · haveI : IsProbabilityMeasure (ν[|A]) := cond_isProbabilityMeasure h0
        have hann := hb (observableVector f (Measure.infinitePi fun _ : ι → ℤ ↦ ν[|A]))
          ⟨_, infinitePi_cond_mem_invariantFieldsOfFiniteEntropy ν hA h0, rfl⟩
        have hvk : ∀ k : Fin N,
            observableVector f (Measure.infinitePi fun _ : ι → ℤ ↦ ν[|A]) k.succ
              = ∫ x, ⇑(fstar k) x ∂(ν[|A]) := by
          intro k
          rw [observableVector_succ, hf k]
          exact Measure.integral_infinitePi_eval (fun _ : ι → ℤ ↦ ν[|A]) 0
            (hfsm k).aestronglyMeasurable
        rw [Fin.sum_univ_succ, observableVector_zero, mul_one] at hann
        simp_rw [hvk] at hann
        have hcond : ∫ x, g x ∂(ν[|A]) = 0 := by rw [hgval (ν[|A])]; exact hann
        rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, mul_eq_zero] at hcond
        refine hcond.resolve_left ?_
        rw [ENNReal.toReal_inv, inv_eq_zero]
        exact ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top ν A⟩
    have hgae : ∀ᵐ x ∂ν, g x = 0 :=
      (hgint ν).ae_eq_zero_of_forall_setIntegral_eq_zero hzero
    by_cases hb' : (fun k : Fin N ↦ b k.succ) = 0
    · have hbz : ∀ k : Fin N, b k.succ = 0 := fun k ↦ by simpa using congrFun hb' k
      have hb0 : b 0 = 0 := by
        obtain ⟨x, hx⟩ := hgae.exists
        have hsum : ∑ k : Fin N, b k.succ * ⇑(fstar k) x = 0 :=
          Finset.sum_eq_zero fun k _ ↦ by rw [hbz k, zero_mul]
        rw [hgdef] at hx
        simp only at hx
        linarith
      funext n
      refine Fin.cases ?_ (fun k ↦ ?_) n
      · simpa using hb0
      · simpa using hbz k
    · exfalso
      refine hli (fun k : Fin N ↦ b k.succ) hb' (-b 0) ?_
      have hsets : {x : E | ∑ n : Fin N, b n.succ * ⇑(fstar n) x ≠ -b 0} = {x : E | ¬ g x = 0} := by
        ext x
        simp only [Set.mem_setOf_eq, hgdef, ne_eq]
        constructor
        · intro h hcon; exact h (by linarith)
        · intro h hcon; exact h (by linarith)
      simpa only [hsets] using MeasureTheory.ae_iff.1 hgae

end Criterion1624

/-! ### Georgii Example (16.25)(2): a ferromagnetic pair potential with spontaneous magnetisation

Georgii takes for `E` a bounded, even, measurable subset of `ℝ`, for `λ` a finite non-degenerate
measure on it and for the observable the spin `f = σ₀`. Nothing below uses more than a bounded
measurable "spin" `s : E → ℝ` which is not `λ`-almost surely constant, which is exactly Georgii's
non-degeneracy of `λ` when `s` is the inclusion `E ⊆ ℝ`. -/

section Example1625b

open Potential Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  [StandardBorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii Example (16.25)(2), the criterion.** A single-site observable `s ∘ σ₀` is a
discriminating system for `𝓟^λ_Θ(Ω, 𝓕)` exactly when `s` is not `λ`-almost surely constant — for
`E ⊆ ℝ` and `s` the inclusion, exactly when `λ` is non-degenerate. -/
theorem isDiscriminating_precomp_eval_iff {s : lp (fun _ : E ↦ ℝ) ∞} (hs : Measurable ⇑s) :
    IsDiscriminating (invariantFieldsOfFiniteEntropy ι E ν)
        (fun _ : Fin 1 ↦ lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) s) ↔
      ∀ c : ℝ, ν {x : E | ⇑s x ≠ c} ≠ 0 := by
  rw [isDiscriminating_invariantFieldsOfFiniteEntropy_iff ν (fstar := fun _ : Fin 1 ↦ s)
    (fun _ ↦ hs) (fun _ ↦ rfl)]
  constructor
  · intro h c
    have h1 := h (fun _ ↦ (1 : ℝ)) (by simp [Function.ne_iff]) c
    simpa using h1
  · intro h a ha c
    have ha0 : a 0 ≠ 0 := by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 ha
      simpa [Subsingleton.elim k (0 : Fin 1)] using hk
    have hset : {x : E | ∑ _n : Fin 1, a 0 * ⇑s x ≠ c} = {x : E | ⇑s x ≠ c / a 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        one_smul, ne_eq, not_iff_not]
      rw [eq_div_iff ha0, mul_comm]
    simpa only [Subsingleton.elim _ (0 : Fin 1), hset] using h (c / a 0)

/-- **Georgii Example (16.25)(2).** Let `s : E → ℝ` be a bounded measurable spin which is not
`λ`-almost surely constant. Then every `Φ⁰ ∈ ℬ_Θ` can be modified inside the *ferromagnetic* cone
`ℬ⁻_Θ(σ₀)` — with the interaction terms on any prescribed finite family of volumes left untouched,
so with arbitrarily long range — into a potential `Φ` whose shift-invariant Gibbs measures include
two of different magnetisation, `μ₁(σ₀) < μ₂(σ₀)`.

Georgii's `J : S → [0, ∞[` is the family of coefficients of the pair terms of `Φ − Φ⁰`; that it may
be prescribed on any finite subset of `S` is the freedom in `Φ⁰` together with the freedom in the
index set `I`. -/
theorem exists_isDiscriminating_neg_integral_lt_integral {I : Set (ι → ℤ)} (hI : Iᶜ.Finite)
    {s : lp (fun _ : E ↦ ℝ) ∞} (hs : Measurable ⇑s) (hnd : ∀ c : ℝ, ν {x : E | ⇑s x ≠ c} ≠ 0)
    (Φ₀ : BTheta (ι → ℤ) E) :
    ∃ Φ : BTheta (ι → ℤ) E,
      Φ - Φ₀ ∈ BThetaOrderNeg {0} (lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) s) I ∧
      ∃ μ₁ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E),
        ∃ μ₂ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E),
          ∫ ω, ⇑s (ω 0) ∂μ₁ < ∫ ω, ⇑s (ω 0) ∂μ₂ := by
  obtain ⟨Φ, hΦ, hdisc⟩ := exists_isDiscriminating_neg_of_isDiscriminating_invariantFieldsOfFiniteEntropy
    ν hI (Finset.singleton_nonempty (0 : ι → ℤ)) (precomp_eval_mem_localFunctionsOn hs)
    (hs.comp (measurable_pi_apply (0 : ι → ℤ)))
    ((isDiscriminating_precomp_eval_iff ν hs).2 hnd) Φ₀
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hlt⟩ :=
    exists_integral_lt_integral_of_isDiscriminating (fun μ hμ ↦ hμ.1.1) hdisc
  exact ⟨Φ, hΦ, μ₁, hμ₁, μ₂, hμ₂, hlt⟩

end Example1625b

/-! ### Georgii Comment (16.24)(4): the potentials of `ℬ_Θ(f₁, …, f_N)` are `α`-normalized -/

section Comment1624d

open Potential Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {N : ℕ}

/-- `α_{\{j\}}` is the average over the spin at the single site `j`: it integrates
`x ↦ F(η with the spin at `j` replaced by `x`)` against `α`. -/
lemma avgOn_singleton_eq_integral_update (α : Measure E) [IsProbabilityMeasure α]
    {F : ((ι → ℤ) → E) → ℝ} (hFm : Measurable F) (j : ι → ℤ) (η : (ι → ℤ) → E) :
    avgOn α ({j} : Finset (ι → ℤ)) F η = ∫ x, F (Function.update η j x) ∂α := by
  classical
  have hup : Measurable fun x : E ↦ Function.update η j x :=
    measurable_update'.comp (measurable_const.prodMk measurable_id)
  have hval : ∀ ζ : (ι → ℤ) → E, F (vacuumCfg η ({j} : Finset (ι → ℤ)) ζ)
      = (fun x : E ↦ F (Function.update η j x)) (ζ j) := by
    intro ζ
    refine congrArg F (funext fun q ↦ ?_)
    rw [vacuumCfg, Function.update_apply]
    by_cases hq : q = j
    · subst hq; simp
    · simp [hq]
  rw [avgOn]
  simp_rw [hval]
  exact Measure.integral_infinitePi_eval (fun _ : ι → ℤ ↦ α) j
    (hFm.comp hup).aestronglyMeasurable

/-- **Georgii Comment (16.24)(4), first sentence.** Suppose the observables are single-site,
`f_n = f_n^* ∘ σ₀`, that `Λ₀ = {0}` is taken, and that some `α ∈ 𝓟(E, 𝓔)` has `α(f_n^*) = 0` for
all `n`. Then every potential of `ℬ_Θ(f₁, …, f_N)` is an `α`-normalized pair potential (a pair
potential by `MeasureTheory.GibbsMeasure.isPairPotential_of_mem_BThetaOrder`).

Averaging over a single site of a volume carrying an interaction term kills every generator: the
interaction term on a translate of `Λ_0 = {0}` is a combination of the `f_n^*` at that site, and
the one on a translate of `Λ_i = \{0, −i\}` is a combination of products
`f_m^*(ω_0) f_n^*(ω_{−i})` of which exactly one factor sits at the averaged site. -/
theorem isNormalized_of_mem_BThetaOrder (α : Measure E) [IsProbabilityMeasure α]
    {fstar : Fin N → lp (fun _ : E ↦ ℝ) ∞} (hfsm : ∀ n, Measurable ⇑(fstar n))
    (hα : ∀ n, ∫ x, ⇑(fstar n) x ∂α = 0)
    {f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
    (hf : ∀ n, f n = lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) (fstar n))
    {I : Set (ι → ℤ)} (h0I : (0 : ι → ℤ) ∉ I)
    {Φ : BTheta (ι → ℤ) E} (hΦ : Φ ∈ BThetaOrder {0} f I) :
    IsNormalized α (Φ : Potential (ι → ℤ) E) := by
  classical
  have hfloc : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E {0} := fun n ↦ by
    rw [hf n]
    exact precomp_eval_mem_localFunctionsOn (hfsm n)
  obtain ⟨h1, h2, h3⟩ :=
    (mem_BThetaOrder_iff (Finset.singleton_nonempty (0 : ι → ℤ)) hfloc h0I).1 hΦ
  have hmeas : ∀ A : Finset (ι → ℤ), Measurable ((Φ : Potential (ι → ℤ) E) A) := fun A ↦
    (IsPotential.measurable (Φ := (Φ : Potential (ι → ℤ) E)) A).mono cylinderEvents_le_pi le_rfl
  have hFn : ∀ n, Measurable ⇑(f n) := fun n ↦ by
    rw [hf n]
    exact (hfsm n).comp (measurable_pi_apply (0 : ι → ℤ))
  have hPq : ∀ (i : ι → ℤ) (q : Fin N × Fin N), Measurable ⇑(pairObservable f i q) := by
    intro i q
    have hcoe : ⇑(pairObservable f i q) = ⇑(f q.1) * (⇑(f q.2) ∘ (shift E i).toFun) := by
      rw [pairObservable, lp.infty_coeFn_mul, lp.coeFn_precomp]
    rw [hcoe]
    exact (hFn q.1).mul ((hFn q.2).comp (shift E i).measurable_toFun)
  have hupd : ∀ (ζ : (ι → ℤ) → E) (p : ι → ℤ),
      Measurable fun x : E ↦ Function.update ζ p x := fun ζ p ↦
    measurable_update'.comp (measurable_const.prodMk measurable_id)
  have hintg : ∀ g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞, Measurable ⇑g →
      ∀ (ζ : (ι → ℤ) → E) (p : ι → ℤ),
      Integrable (fun x : E ↦ ⇑g (Function.update ζ p x)) α := by
    intro g hg ζ p
    refine Integrable.of_bound ((hg.comp (hupd ζ p)).aestronglyMeasurable) ‖g‖
      (Filter.Eventually.of_forall fun x ↦ ?_)
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero g _
  refine isNormalized_of_avgOn_singleton α hmeas
    (fun A ↦ exists_forall_abs_coe_apply_le Φ A) ?_
  intro A j hjA
  funext η
  rw [avgOn_singleton_eq_integral_update α (hmeas A) j η]
  by_cases hA : A ∈ orderVolumes ({0} : Finset (ι → ℤ)) I
  · obtain ⟨i, hi, k, rfl⟩ := hA
    obtain ⟨p, hpmem, hpj⟩ : ∃ p, p ∈ pairVolume ({0} : Finset (ι → ℤ)) i ∧ j = p + k :=
      ⟨j - k, mem_translate.1 hjA, by ring⟩
    set η' : (ι → ℤ) → E := (shift E (-k)).toFun η with hη'
    have hshift : ∀ x : E, (shift E (-k)).toFun (Function.update η j x)
        = Function.update η' p x := by
      intro x
      funext q
      simp only [hη', shift_toFun_apply, Function.update_apply, sub_neg_eq_add]
      by_cases hq : q = p
      · subst hq
        rw [if_pos hpj.symm, if_pos rfl]
      · rw [if_neg hq, if_neg fun hcon ↦ hq (by rw [hpj] at hcon; exact add_right_cancel hcon)]
    have hval : ∀ x : E, (Φ : Potential (ι → ℤ) E)
        (translate (pairVolume ({0} : Finset (ι → ℤ)) i) k) (Function.update η j x)
          = (Φ : Potential (ι → ℤ) E) (pairVolume ({0} : Finset (ι → ℤ)) i)
              (Function.update η' p x) := fun x ↦ by
      rw [apply_translate_of_isShiftInvariant (BTheta.isShiftInvariant Φ) _ k
        (Function.update η j x), hshift x]
    simp_rw [hval]
    rcases eq_or_ne i 0 with rfl | hi0
    · -- the self-interaction volume `Λ_0 = {0}`
      rw [pairVolume_zero] at hpmem ⊢
      have hp0 : p = 0 := by simpa using hpmem
      subst hp0
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
      have hexp : ∀ x : E, (Φ : Potential (ι → ℤ) E) ({0} : Finset (ι → ℤ))
          (Function.update η' 0 x) = ∑ n, c n * ⇑(fstar n) x := by
        intro x
        rw [← hc]
        refine (Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun n _ ↦ ?_)
        rw [Pi.smul_apply, smul_eq_mul, hf n, lp.coeFn_precomp, Function.comp_apply,
          Function.update_self]
      simp_rw [hexp]
      rw [integral_finset_sum _ fun n _ ↦
        (lp.integrable_of_measurable (hfsm n) α).const_mul _]
      exact Finset.sum_eq_zero fun n _ ↦ by rw [integral_const_mul, hα n, mul_zero]
    · -- the pair volumes `Λ_i = {0, −i}`, `i ≠ 0`
      have hiI : i ∈ I := by
        rcases hi with h | h
        · exact absurd h hi0
        · exact h
      have hine : (-i : ι → ℤ) ≠ 0 := neg_ne_zero.2 hi0
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (h2 i hiI)
      have hexp : ∀ x : E, (Φ : Potential (ι → ℤ) E) (pairVolume ({0} : Finset (ι → ℤ)) i)
          (Function.update η' p x)
            = ∑ q : Fin N × Fin N, c q * (⇑(fstar q.1) ((Function.update η' p x) 0)
                * ⇑(fstar q.2) ((Function.update η' p x) (-i))) := by
        intro x
        rw [← hc]
        refine (Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun q _ ↦ ?_)
        rw [Pi.smul_apply, smul_eq_mul, pairObservable, lp.infty_coeFn_mul, Pi.mul_apply,
          lp.coeFn_precomp, Function.comp_apply, hf q.1, hf q.2, lp.coeFn_precomp,
          lp.coeFn_precomp, Function.comp_apply, Function.comp_apply, shift_toFun_apply,
          zero_sub]
      simp_rw [hexp]
      have hp0i : p = 0 ∨ p = -i := by
        rw [pairVolume, Finset.mem_union] at hpmem
        rcases hpmem with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa [mem_translate, sub_eq_zero] using h)
      rcases hp0i with rfl | rfl
      · have hterm : ∀ (q : Fin N × Fin N) (x : E),
            c q * (⇑(fstar q.1) ((Function.update η' 0 x) 0)
              * ⇑(fstar q.2) ((Function.update η' 0 x) (-i)))
            = (c q * ⇑(fstar q.2) (η' (-i))) * ⇑(fstar q.1) x := by
          intro q x
          rw [Function.update_self, Function.update_of_ne hine]
          ring
        simp_rw [hterm]
        rw [integral_finset_sum _ fun q _ ↦
          (lp.integrable_of_measurable (hfsm q.1) α).const_mul _]
        exact Finset.sum_eq_zero fun q _ ↦ by rw [integral_const_mul, hα q.1, mul_zero]
      · have hterm : ∀ (q : Fin N × Fin N) (x : E),
            c q * (⇑(fstar q.1) ((Function.update η' (-i) x) 0)
              * ⇑(fstar q.2) ((Function.update η' (-i) x) (-i)))
            = (c q * ⇑(fstar q.1) (η' 0)) * ⇑(fstar q.2) x := by
          intro q x
          rw [Function.update_self, Function.update_of_ne (Ne.symm hine)]
          ring
        simp_rw [hterm]
        rw [integral_finset_sum _ fun q _ ↦
          (lp.integrable_of_measurable (hfsm q.2) α).const_mul _]
        exact Finset.sum_eq_zero fun q _ ↦ by rw [integral_const_mul, hα q.2, mul_zero]
  · simp [h3 _ hA]

end Comment1624d

/-! ### Georgii Comment (16.24)(4): an infinite-dimensional family of non-equivalent potentials -/

section Comment1624dConclusion

open Potential Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  [StandardBorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {N : ℕ}
  {fstar : Fin N → lp (fun _ : E ↦ ℝ) ∞} {f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
  {I : Set (ι → ℤ)}

omit [Nonempty ι] [StandardBorelSpace E] in
/-- **Georgii Comment (16.24)(4)(i).** A potential differing from `Φ⁰` by an element of
`ℬ_Θ(f₁, …, f_N)` agrees with `Φ⁰` on every volume outside the family `orderVolumes` carrying the
interaction terms of that space — for Georgii's `ℬ^R_Θ`, on every volume of diameter below `R`. -/
lemma coe_apply_eq_of_sub_mem_BThetaOrder (hfsm : ∀ n, Measurable ⇑(fstar n))
    (hf : ∀ n, f n = lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) (fstar n))
    (h0I : (0 : ι → ℤ) ∉ I) {Φ Φ₀ : BTheta (ι → ℤ) E}
    (h : Φ - Φ₀ ∈ BThetaOrder {0} f I) {A : Finset (ι → ℤ)}
    (hA : A ∉ orderVolumes ({0} : Finset (ι → ℤ)) I) :
    (Φ : Potential (ι → ℤ) E) A = (Φ₀ : Potential (ι → ℤ) E) A := by
  have hfloc : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E {0} := fun n ↦ by
    rw [hf n]
    exact precomp_eval_mem_localFunctionsOn (hfsm n)
  have h0 := ((mem_BThetaOrder_iff (Finset.singleton_nonempty (0 : ι → ℤ)) hfloc h0I).1 h).2.2 A hA
  rw [Submodule.coe_sub] at h0
  funext η
  have : (Φ : Potential (ι → ℤ) E) A η - (Φ₀ : Potential (ι → ℤ) E) A η = 0 := congrFun h0 η
  linarith

omit [Nonempty ι] [StandardBorelSpace E] in
/-- **Georgii Comment (16.24)(4)(i).** If `Φ⁰` is `α`-normalized and `Φ − Φ⁰ ∈ ℬ_Θ(f₁, …, f_N)`,
then `Φ` is `α`-normalized as well, because `ℬ_Θ(f₁, …, f_N)` consists of `α`-normalized
potentials (`isNormalized_of_mem_BThetaOrder`). -/
lemma isNormalized_of_sub_mem_BThetaOrder (α : Measure E) [IsProbabilityMeasure α]
    (hfsm : ∀ n, Measurable ⇑(fstar n)) (hα : ∀ n, ∫ x, ⇑(fstar n) x ∂α = 0)
    (hf : ∀ n, f n = lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) (fstar n))
    (h0I : (0 : ι → ℤ) ∉ I) {Φ Φ₀ : BTheta (ι → ℤ) E}
    (hΦ₀ : IsNormalized α (Φ₀ : Potential (ι → ℤ) E)) (h : Φ - Φ₀ ∈ BThetaOrder {0} f I) :
    IsNormalized α (Φ : Potential (ι → ℤ) E) := by
  have hsub : Φ₀ - Φ ∈ BThetaOrder {0} f I := by
    have := Submodule.neg_mem (BThetaOrder ({0} : Finset (ι → ℤ)) f I) h
    rwa [neg_sub] at this
  have hn : IsNormalized α ((Φ₀ - Φ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E) :=
    isNormalized_of_mem_BThetaOrder α hfsm hα hf h0I hsub
  rw [Submodule.coe_sub] at hn
  have hpot : Potential.IsPotential
      ((Φ₀ : Potential (ι → ℤ) E) - (Φ : Potential (ι → ℤ) E)) := Potential.isPotential_sub
  have hbd : ∀ B : Finset (ι → ℤ), ∃ M : ℝ, ∀ η,
      |((Φ₀ : Potential (ι → ℤ) E) - (Φ : Potential (ι → ℤ) E)) B η| ≤ M := fun B ↦ by
    obtain ⟨M₁, hM₁⟩ := exists_forall_abs_coe_apply_le Φ₀ B
    obtain ⟨M₂, hM₂⟩ := exists_forall_abs_coe_apply_le Φ B
    exact ⟨M₁ + M₂, fun ζ ↦ (abs_sub _ _).trans (add_le_add (hM₁ ζ) (hM₂ ζ))⟩
  have hfin := IsNormalized.sub α (exists_forall_abs_coe_apply_le Φ₀) hbd hΦ₀ hn
  rwa [sub_sub_cancel] at hfin

/-- **Georgii Comment (16.24)(4), the special version of Theorem (16.21)(b).** Let the observables
be single-site, `f_n = f_n^* ∘ σ₀`, and let `α ∈ 𝓟(E, 𝓔)` satisfy `α(f_n^*) = 0`, so that
`ℬ_Θ(f₁, …, f_N)` consists of `α`-normalized pair potentials. Let `Ψ ∈ ℬ_Θ` exhibit a phase
transition with discriminating system `{f₁, …, f_N}` and let `ε₀ > 0`. Then there is a `δ > 0` such
that every `α`-normalized `Φ⁰ ∈ ℬ_Θ` with `‖Φ⁰ − Ψ‖₀ < δ` admits an `α`-normalized `Φ ∈ ℬ_Θ` with

* (i) `Φ_A = Φ⁰_A` on every volume outside `orderVolumes {0} I` (Georgii's `1 ≤ diam A ≤ R`),
* (ii) `‖Φ − Ψ‖₀ < ε₀`, and
* (iii) `Φ ≪ {f₁, …, f_N}`. -/
theorem exists_isNormalized_isDiscriminating_norm_sub_lt (α : Measure E) [IsProbabilityMeasure α]
    (hI : Iᶜ.Finite) (h0I : (0 : ι → ℤ) ∉ I) (hfsm : ∀ n, Measurable ⇑(fstar n))
    (hα : ∀ n, ∫ x, ⇑(fstar n) x ∂α = 0)
    (hf : ∀ n, f n = lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) (fstar n))
    {Ψ : BTheta (ι → ℤ) E}
    (hΨ : IsDiscriminating (invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Ψ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)) f)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Φ₀ : BTheta (ι → ℤ) E,
      IsNormalized α (Φ₀ : Potential (ι → ℤ) E) → ‖Φ₀ - Ψ‖ < δ →
      ∃ Φ : BTheta (ι → ℤ) E,
        (∀ A ∉ orderVolumes ({0} : Finset (ι → ℤ)) I,
          (Φ : Potential (ι → ℤ) E) A = (Φ₀ : Potential (ι → ℤ) E) A) ∧
        IsNormalized α (Φ : Potential (ι → ℤ) E) ∧ ‖Φ - Ψ‖ < ε₀ ∧
        IsDiscriminating (invariantG (gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)) f := by
  have hfloc : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E {0} := fun n ↦ by
    rw [hf n]
    exact precomp_eval_mem_localFunctionsOn (hfsm n)
  have hfm : ∀ n, Measurable ⇑(f n) := fun n ↦ by
    rw [hf n]
    exact (hfsm n).comp (measurable_pi_apply (0 : ι → ℤ))
  obtain ⟨δ, hδ, hmain⟩ := exists_pos_forall_exists_isDiscriminating_norm_sub_lt ν hI
    (Finset.singleton_nonempty (0 : ι → ℤ)) hfloc hfm hΨ hε₀
  refine ⟨δ, hδ, fun Φ₀ hΦ₀n hΦ₀ ↦ ?_⟩
  obtain ⟨Φ, hmem, hnorm, hdisc⟩ := hmain Φ₀ hΦ₀
  exact ⟨Φ, fun A hA ↦ coe_apply_eq_of_sub_mem_BThetaOrder hfsm hf h0I hmem hA,
    isNormalized_of_sub_mem_BThetaOrder α hfsm hα hf h0I hΦ₀n hmem, hnorm, hdisc⟩

omit [Nonempty ι] [StandardBorelSpace E] in
/-- **Georgii Comment (16.24)(4), the point.** Two potentials produced by the preceding theorem
from `α`-normalized `Φ⁰₁ ≠ Φ⁰₂` differing on a volume that the modification does not touch are
*not equivalent*: they are distinct `α`-normalized potentials, and distinct `α`-normalized
potentials never define the same specification (Theorem (2.35)(a),
`Potential.BTheta.not_isEquivalent_of_ne_of_isNormalized`). Since `Φ⁰` ranges over an
infinite-dimensional family, so does the resulting family of phase-transition potentials. -/
theorem not_isEquivalent_of_coe_apply_ne (α : Measure E) [IsProbabilityMeasure α]
    (hfsm : ∀ n, Measurable ⇑(fstar n)) (hα : ∀ n, ∫ x, ⇑(fstar n) x ∂α = 0)
    (hf : ∀ n, f n = lp.precomp (fun ω : (ι → ℤ) → E ↦ ω 0) (fstar n))
    (h0I : (0 : ι → ℤ) ∉ I) {Φ₁ Φ₂ Φ₀₁ Φ₀₂ : BTheta (ι → ℤ) E}
    (h₁ : Φ₁ - Φ₀₁ ∈ BThetaOrder {0} f I) (h₂ : Φ₂ - Φ₀₂ ∈ BThetaOrder {0} f I)
    (hn₁ : IsNormalized α (Φ₀₁ : Potential (ι → ℤ) E))
    (hn₂ : IsNormalized α (Φ₀₂ : Potential (ι → ℤ) E))
    {A : Finset (ι → ℤ)} (hA : A ∉ orderVolumes ({0} : Finset (ι → ℤ)) I)
    (hne : (Φ₀₁ : Potential (ι → ℤ) E) A ≠ (Φ₀₂ : Potential (ι → ℤ) E) A) :
    ¬ Potential.IsEquivalent (Φ₁ : Potential (ι → ℤ) E) (Φ₂ : Potential (ι → ℤ) E) := by
  refine not_isEquivalent_of_ne_of_isNormalized α
    (isNormalized_of_sub_mem_BThetaOrder α hfsm hα hf h0I hn₁ h₁)
    (isNormalized_of_sub_mem_BThetaOrder α hfsm hα hf h0I hn₂ h₂) fun hEq ↦ hne ?_
  rw [← coe_apply_eq_of_sub_mem_BThetaOrder hfsm hf h0I h₁ hA,
    ← coe_apply_eq_of_sub_mem_BThetaOrder hfsm hf h0I h₂ hA, hEq]

end Comment1624dConclusion

end MeasureTheory.GibbsMeasure

end

end
