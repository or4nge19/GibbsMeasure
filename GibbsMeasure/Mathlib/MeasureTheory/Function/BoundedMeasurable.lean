/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Bounded measurable functions

The bounded real functions on `α` form the commutative Banach algebra `lp (fun _ : α ↦ ℝ) ∞`. Inside
it, the ones measurable for a σ-algebra `m` form a closed subalgebra `MeasureTheory.boundedMeasurable m`.

## Main declarations

* `MeasureTheory.boundedMeasurable`: the subalgebra of bounded `m`-measurable functions.
* `MeasureTheory.isClosed_boundedMeasurable`: it is closed, i.e. a uniform limit of measurable
  functions is measurable.
* `MeasureTheory.simpleFunctions`: the subalgebra of `m`-simple functions.
* `MeasureTheory.topologicalClosure_simpleFunctions`: `boundedMeasurable m` is the sup-norm closure
  of the `m`-simple functions.
-/

@[expose] public section

open scoped ENNReal Topology
open Filter

noncomputable section

namespace lp

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)]

lemma norm_apply_le_norm_top (f : lp E ∞) (i : α) : ‖f i‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero f i

end lp

namespace MeasureTheory

variable {α : Type*}

/-- The bounded real-valued `m`-measurable functions on `α`, as a subalgebra of the commutative
Banach algebra `lp (fun _ : α ↦ ℝ) ∞` of all bounded real functions on `α`.

This is the ambient algebra for Georgii's local and quasilocal observables (Georgii, *Gibbs Measures
and Phase Transitions*, Definition (2.20)). -/
def boundedMeasurable (m : MeasurableSpace α) : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞) where
  carrier := {f | Measurable[m] (⇑f : α → ℝ)}
  mul_mem' {f g} hf hg := by
    show Measurable[m] (⇑(f * g) : α → ℝ)
    rw [lp.infty_coeFn_mul]
    exact Measurable.mul (m := m) hf hg
  one_mem' := by
    show Measurable[m] (⇑(1 : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ)
    rw [lp.infty_coeFn_one]
    exact measurable_one
  add_mem' {f g} hf hg := by
    show Measurable[m] (⇑(f + g) : α → ℝ)
    rw [lp.coeFn_add]
    exact Measurable.add (m := m) hf hg
  zero_mem' := by
    show Measurable[m] (⇑(0 : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ)
    rw [lp.coeFn_zero]
    exact measurable_zero
  algebraMap_mem' r := by
    show Measurable[m] (⇑(algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r) : α → ℝ)
    have h : ⇑(algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r) = fun _ : α ↦ r := by
      rw [Algebra.algebraMap_eq_smul_one]
      funext x
      simp [lp.coeFn_smul, lp.infty_coeFn_one]
    rw [h]
    exact measurable_const

lemma mem_boundedMeasurable {m : MeasurableSpace α} {f : lp (fun _ : α ↦ ℝ) ∞} :
    f ∈ boundedMeasurable m ↔ Measurable[m] (⇑f : α → ℝ) := Iff.rfl

/-- `boundedMeasurable` is monotone in the σ-algebra. -/
lemma boundedMeasurable_mono {m₁ m₂ : MeasurableSpace α} (h : m₁ ≤ m₂) :
    boundedMeasurable m₁ ≤ boundedMeasurable m₂ :=
  fun _ hf ↦ hf.mono h le_rfl

/-- Convergence in `ℓ^∞` implies pointwise convergence. -/
lemma lp.tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → lp (fun _ : α ↦ ℝ) ∞} {g : lp (fun _ : α ↦ ℝ) ∞} (h : Tendsto f l (𝓝 g)) (x : α) :
    Tendsto (fun n ↦ (f n : α → ℝ) x) l (𝓝 ((g : α → ℝ) x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h
  simpa [_root_.lp.coeFn_sub] using
    _root_.lp.norm_apply_le_norm ENNReal.top_ne_zero (f n - g) x

/-- **Uniform limits of measurable functions are measurable**: the bounded `m`-measurable functions
form a *closed* subalgebra of the bounded functions. -/
lemma isClosed_boundedMeasurable (m : MeasurableSpace α) :
    IsClosed (boundedMeasurable m : Set (lp (fun _ : α ↦ ℝ) ∞)) := by
  refine IsSeqClosed.isClosed fun f g hf hfg ↦ ?_
  rw [SetLike.mem_coe, mem_boundedMeasurable]
  refine measurable_of_tendsto_metrizable (f := fun n ↦ ((f n : α → ℝ))) hf ?_
  rw [tendsto_pi_nhds]
  exact fun x ↦ lp.tendsto_apply_of_tendsto hfg x

/-- A closed subalgebra contains the closure of any subalgebra it contains. In particular the
quasilocal functions consist of measurable functions. -/
lemma topologicalClosure_le_boundedMeasurable {m : MeasurableSpace α}
    {A : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞)} (hA : A ≤ boundedMeasurable m) :
    A.topologicalClosure ≤ boundedMeasurable m :=
  Subalgebra.topologicalClosure_minimal hA (isClosed_boundedMeasurable m)

/-! ### Approximation by simple functions -/

/-- A bounded `m`-measurable function is uniformly approximable by `m`-simple functions. -/
theorem exists_simpleFunc_dist_le {m : MeasurableSpace α} {f : α → ℝ} (hf : Measurable[m] f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : @SimpleFunc α m ℝ, ∀ x, |f x - g x| ≤ ε := by
  classical
  set n : α → ℤ := fun x ↦ ⌊f x / ε⌋ with hn
  have hnmeas : Measurable[m] n := Int.measurable_floor.comp (hf.div_const ε)
  have hrange : (Set.range fun x ↦ ε * (n x : ℝ)).Finite := by
    have hsub : (Set.range fun x ↦ ε * (n x : ℝ))
        ⊆ (fun k : ℤ ↦ ε * (k : ℝ)) '' (Set.Icc (⌊-C / ε⌋) (⌈C / ε⌉)) := by
      rintro _ ⟨x, rfl⟩
      refine ⟨n x, ⟨?_, ?_⟩, rfl⟩
      · exact Int.floor_le_floor (by
          rw [div_le_div_iff_of_pos_right hε]
          linarith [abs_le.1 (hC x)])
      · exact le_trans (Int.floor_le_ceil _) (Int.ceil_le_ceil (by
          rw [div_le_div_iff_of_pos_right hε]
          linarith [abs_le.1 (hC x)]))
    exact Set.Finite.subset ((Set.finite_Icc _ _).image _) hsub
  have hbound : ∀ x, |f x - ε * (n x : ℝ)| ≤ ε := by
    intro x
    have h1 : (n x : ℝ) ≤ f x / ε := Int.floor_le _
    have h2 : f x / ε < n x + 1 := Int.lt_floor_add_one _
    have hA : (n x : ℝ) * ε ≤ f x := (le_div_iff₀ hε).1 h1
    have hB : f x < ((n x : ℝ) + 1) * ε := (div_lt_iff₀ hε).1 h2
    rw [abs_le]
    constructor <;> nlinarith [hA, hB]
  have hfib : ∀ c : ℝ, MeasurableSet[m] ((fun x ↦ ε * (n x : ℝ)) ⁻¹' {c}) := fun c ↦ by
    have hpre : ((fun x ↦ ε * (n x : ℝ)) ⁻¹' {c})
        = n ⁻¹' ((fun k : ℤ ↦ ε * (k : ℝ)) ⁻¹' {c}) := rfl
    rw [hpre]
    exact hnmeas MeasurableSet.of_discrete
  exact ⟨⟨fun x ↦ ε * (n x : ℝ), hfib, hrange⟩, hbound⟩

lemma memℓp_simpleFunc {m : MeasurableSpace α} (g : @SimpleFunc α m ℝ) :
    Memℓp (⇑g : α → ℝ) ∞ := by
  refine memℓp_infty (Set.Finite.bddAbove ?_)
  exact (g.finite_range'.image (‖·‖)).subset (by rintro _ ⟨x, rfl⟩; exact ⟨g x, ⟨x, rfl⟩, rfl⟩)

/-- The `m`-simple functions, as a subalgebra of the bounded functions. -/
def simpleFunctions (m : MeasurableSpace α) : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞) where
  carrier := {f | ∃ g : @SimpleFunc α m ℝ, (⇑f : α → ℝ) = ⇑g}
  mul_mem' := fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ ↦ ⟨g₁ * g₂, by rw [lp.infty_coeFn_mul, h₁, h₂]; rfl⟩
  one_mem' := ⟨1, by rw [lp.infty_coeFn_one]; rfl⟩
  add_mem' := fun ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ ↦ ⟨g₁ + g₂, by rw [lp.coeFn_add, h₁, h₂]; rfl⟩
  zero_mem' := ⟨0, by rw [lp.coeFn_zero]; rfl⟩
  algebraMap_mem' r := ⟨SimpleFunc.const α r, by
    rw [Algebra.algebraMap_eq_smul_one]
    funext x
    simp [lp.coeFn_smul, lp.infty_coeFn_one]⟩

lemma simpleFunctions_le_boundedMeasurable (m : MeasurableSpace α) :
    simpleFunctions m ≤ boundedMeasurable m := by
  rintro f ⟨g, hg⟩
  change Measurable[m] (⇑f : α → ℝ)
  rw [hg]
  exact g.measurable

/-- `boundedMeasurable m` is the sup-norm closure of the `m`-simple functions. -/
theorem topologicalClosure_simpleFunctions (m : MeasurableSpace α) :
    (simpleFunctions m).topologicalClosure = boundedMeasurable m := by
  refine le_antisymm
    (topologicalClosure_le_boundedMeasurable (simpleFunctions_le_boundedMeasurable m))
    fun f hf ↦ ?_
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg⟩ := exists_simpleFunc_dist_le (mem_boundedMeasurable.1 hf)
    (fun x ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f x) (half_pos hε)
  refine ⟨⟨⇑g, memℓp_simpleFunc g⟩, ⟨g, rfl⟩, ?_⟩
  refine lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
  rw [dist_eq_norm]
  exact lp.norm_le_of_forall_le (by positivity) fun x ↦ by
    rw [lp.coeFn_sub, Pi.sub_apply]; simpa [Real.norm_eq_abs] using hg x

end MeasureTheory
