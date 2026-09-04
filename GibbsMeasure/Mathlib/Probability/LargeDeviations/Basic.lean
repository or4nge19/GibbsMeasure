/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Data.EReal.Inv
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Large deviation principles

Mathlib has no large deviation theory (`grep LargeDeviation`, `rateFunction`: no hits), so this
file introduces the basic vocabulary in Mathlib's idiom, for an arbitrary family of measures
`μ : κ → Measure X` indexed by a filter `l` and normalised by a *speed* `a : κ → ℝ`.

## Main definitions

* `MeasureTheory.logRate μ a C = log (μ C) / a`, the normalised log-probability, valued in
  `EReal` (`ENNReal.log 0 = ⊥`, so no positivity of `μ C` is assumed).
* `MeasureTheory.IsLDPUpperBoundOn l a μ I C` and `MeasureTheory.IsLDPLowerBoundOn l a μ I C`:
  `limsup logRate ≤ -⨅_{C} I` and `-⨅_C I ≤ liminf logRate`.
* `MeasureTheory.IsLargeDeviationPrinciple l a μ I`: the upper bound on every closed set and the
  lower bound on every open set, with rate function `I : X → EReal`.

## Main results

* `MeasureTheory.IsLargeDeviationPrinciple.limsup_le_closure` and
  `MeasureTheory.IsLargeDeviationPrinciple.interior_le_liminf`: the form in which a large
  deviation principle is usually *stated* — for an **arbitrary** set `C`,
  `limsup ≤ -⨅_{closure C} I` and `-⨅_{interior C} I ≤ liminf`.
* `MeasureTheory.IsLargeDeviationPrinciple.map`, the **contraction principle**: the image of a
  large deviation principle under a continuous measurable map `f` is a large deviation principle
  with rate function `J y = ⨅_{f x = y} I x`.
* `MeasureTheory.measure_mul_ofReal_exp_le_lintegral`, **Chebyshev's inequality in exponential
  form**, and `MeasureTheory.limsup_logRate_le_of_isCompact`, the **Cramér upper bound over
  compact sets**: if a family `G` of continuous functions has normalised log-moment generating
  functions asymptotically bounded by `Λ`, then the upper bound holds over compact sets with the
  Legendre-type rate function `I x = ⨆_{g ∈ G} (g x - Λ g)`.
* `MeasureTheory.le_liminf_logRate_of_le_smul`, the **change-of-measure lower bound**: if a
  comparison family `ν` puts mass bounded away from `0` on `A` and `ν A ≤ e^{a c} μ A`, then
  `liminf logRate μ a A ≥ -c`. This is the mechanism of every lower bound over an open set:
  choose `ν` to (nearly) minimise the rate function on the set, and let the ergodic theorem
  supply `ν (A) → 1`.

All results are model free: no structure is assumed on `X` beyond a topology and the Borel
measurability of its open sets.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set Topology
open scoped ENNReal Topology

noncomputable section

/-! ### `EReal` arithmetic used by the ε-limits -/

namespace EReal

/-- If `x ≤ -c` for every real `c` strictly below `J`, then `x ≤ -J`. This is the step from
"the estimate holds at every real level below the infimum of the rate function" to the estimate
at the infimum itself. -/
lemma le_neg_of_forall_coe_lt {x J : EReal} (h : ∀ c : ℝ, (c : EReal) < J → x ≤ -(c : EReal)) :
    x ≤ -J := by
  by_contra hx
  rw [not_le] at hx
  have hxJ : -x < J := by rwa [EReal.neg_lt_comm]
  obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hxJ
  have hle := h (q : ℝ) hq2
  rw [← EReal.neg_le_neg_iff, neg_neg] at hle
  exact absurd hq1 (not_lt.2 hle)

/-- If `x ≤ r + ε` for every `ε > 0`, then `x ≤ r`. -/
lemma le_coe_of_forall_pos_add {x : EReal} {r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ((r + ε : ℝ) : EReal)) : x ≤ (r : EReal) := by
  have hc : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r) := tendsto_const_nhds
  have h0 : Tendsto (fun n : ℕ ↦ r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using hc.add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto (EReal.tendsto_coe.2 h0) (.of_forall fun n ↦ h _ (by positivity))

end EReal

namespace MeasureTheory

variable {X Y κ : Type*}

/-! ### The normalised log-probability -/

section Def

variable [MeasurableSpace X]

/-- The normalised log-probability `|Λ|⁻¹ log μ(C)` of a large deviation estimate: `log (μ C) / a`
in `EReal`, with `ENNReal.log 0 = ⊥`. -/
def logRate (μ : Measure X) (a : ℝ) (C : Set X) : EReal := ENNReal.log (μ C) / (a : EReal)

lemma logRate_mono (μ : Measure X) {a : ℝ} (ha : 0 ≤ a) {C D : Set X} (h : C ⊆ D) :
    logRate μ a C ≤ logRate μ a D :=
  _root_.EReal.div_le_div_right_of_nonneg (by exact_mod_cast ha)
    (ENNReal.log_le_log (measure_mono h))

@[simp] lemma logRate_empty (μ : Measure X) (a : ℝ) : logRate μ a ∅ = ⊥ / (a : EReal) := by
  simp [logRate]

end Def

/-! ### The definition of a large deviation principle -/

section Principle

variable [MeasurableSpace X] [TopologicalSpace X]

/-- The large deviation **upper bound** on a set `C`, at speed `a` along the filter `l`. -/
def IsLDPUpperBoundOn (l : Filter κ) (a : κ → ℝ) (μ : κ → Measure X) (I : X → EReal)
    (C : Set X) : Prop :=
  limsup (fun n ↦ logRate (μ n) (a n) C) l ≤ -⨅ x ∈ C, I x

/-- The large deviation **lower bound** on a set `C`, at speed `a` along the filter `l`. -/
def IsLDPLowerBoundOn (l : Filter κ) (a : κ → ℝ) (μ : κ → Measure X) (I : X → EReal)
    (C : Set X) : Prop :=
  -⨅ x ∈ C, I x ≤ liminf (fun n ↦ logRate (μ n) (a n) C) l

/-- A family of measures `μ` satisfies a **large deviation principle** at speed `a` along `l`
with rate function `I` if the upper bound holds on every closed set and the lower bound on every
open set. -/
structure IsLargeDeviationPrinciple (l : Filter κ) (a : κ → ℝ) (μ : κ → Measure X)
    (I : X → EReal) : Prop where
  /-- The upper bound over closed sets. -/
  upper : ∀ ⦃C : Set X⦄, IsClosed C → IsLDPUpperBoundOn l a μ I C
  /-- The lower bound over open sets. -/
  lower : ∀ ⦃U : Set X⦄, IsOpen U → IsLDPLowerBoundOn l a μ I U

variable {l : Filter κ} {a : κ → ℝ} {μ : κ → Measure X} {I : X → EReal}

/-- The upper bound of a large deviation principle, for an arbitrary set: the rate is the
infimum of `I` over the **closure**. -/
theorem IsLargeDeviationPrinciple.limsup_le_closure (h : IsLargeDeviationPrinciple l a μ I)
    (ha : ∀ n, 0 ≤ a n) (C : Set X) :
    limsup (fun n ↦ logRate (μ n) (a n) C) l ≤ -⨅ x ∈ closure C, I x :=
  le_trans (limsup_le_limsup (.of_forall fun n ↦ logRate_mono _ (ha n) subset_closure))
    (h.upper isClosed_closure)

/-- The lower bound of a large deviation principle, for an arbitrary set: the rate is the
infimum of `I` over the **interior**. -/
theorem IsLargeDeviationPrinciple.interior_le_liminf (h : IsLargeDeviationPrinciple l a μ I)
    (ha : ∀ n, 0 ≤ a n) (C : Set X) :
    -⨅ x ∈ interior C, I x ≤ liminf (fun n ↦ logRate (μ n) (a n) C) l :=
  le_trans (h.lower isOpen_interior)
    (liminf_le_liminf (.of_forall fun n ↦ logRate_mono _ (ha n) interior_subset))

end Principle

/-! ### The contraction principle -/

section Contraction

variable [MeasurableSpace X] [TopologicalSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]

omit [MeasurableSpace X] [TopologicalSpace X] [MeasurableSpace Y] [TopologicalSpace Y]
  [OpensMeasurableSpace Y] in
/-- Grouping an infimum over a preimage by fibres. -/
lemma iInf_preimage_eq_iInf_iInf (f : X → Y) (I : X → EReal) (D : Set Y) :
    ⨅ x ∈ f ⁻¹' D, I x = ⨅ y ∈ D, ⨅ x ∈ f ⁻¹' ({y} : Set Y), I x := by
  refine le_antisymm (le_iInf₂ fun y hy ↦ le_iInf₂ fun x hx ↦ ?_)
    (le_iInf₂ fun x hx ↦ le_trans (iInf₂_le (f x) hx)
      (iInf₂_le x (by simp : x ∈ f ⁻¹' ({f x} : Set Y))))
  refine iInf₂_le x ?_
  have hxy : f x = y := hx
  show f x ∈ D
  rw [hxy]; exact hy

variable {l : Filter κ} {a : κ → ℝ} {μ : κ → Measure X} {I : X → EReal} {f : X → Y}

/-- **The contraction principle.** The image of a large deviation principle under a continuous
measurable map is a large deviation principle whose rate function is the fibrewise infimum. -/
theorem IsLargeDeviationPrinciple.map (h : IsLargeDeviationPrinciple l a μ I)
    (hfc : Continuous f) (hfm : Measurable f) :
    IsLargeDeviationPrinciple l a (fun n ↦ (μ n).map f)
      (fun y ↦ ⨅ x ∈ f ⁻¹' ({y} : Set Y), I x) where
  upper D hD := by
    have hmap : ∀ n, logRate ((μ n).map f) (a n) D = logRate (μ n) (a n) (f ⁻¹' D) := fun n ↦ by
      rw [logRate, logRate, Measure.map_apply hfm hD.measurableSet]
    have h1 := h.upper (hD.preimage hfc)
    rw [IsLDPUpperBoundOn, iInf_preimage_eq_iInf_iInf] at h1
    simpa only [IsLDPUpperBoundOn, hmap] using h1
  lower U hU := by
    have hmap : ∀ n, logRate ((μ n).map f) (a n) U = logRate (μ n) (a n) (f ⁻¹' U) := fun n ↦ by
      rw [logRate, logRate, Measure.map_apply hfm hU.measurableSet]
    have h1 := h.lower (hU.preimage hfc)
    rw [IsLDPLowerBoundOn, iInf_preimage_eq_iInf_iInf] at h1
    simpa only [IsLDPLowerBoundOn, hmap] using h1

end Contraction

/-! ### Chebyshev's inequality and the Cramér upper bound over compact sets -/

section Cramer

variable [MeasurableSpace X]

/-- **Chebyshev's inequality in exponential form.** If `g ≥ c` on a measurable set `A` and
`0 ≤ t`, then `μ A · e^{t c} ≤ ∫ e^{t g} dμ`. -/
theorem measure_mul_ofReal_exp_le_lintegral {μ : Measure X} {g : X → ℝ}
    {t c : ℝ} (ht : 0 ≤ t) {A : Set X} (hA : MeasurableSet A) (hgA : ∀ x ∈ A, c ≤ g x) :
    μ A * ENNReal.ofReal (Real.exp (t * c))
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (t * g x)) ∂μ := by
  calc μ A * ENNReal.ofReal (Real.exp (t * c))
      = ∫⁻ _ in A, ENNReal.ofReal (Real.exp (t * c)) ∂μ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (t * g x)) ∂μ :=
        setLIntegral_mono' hA fun x hx ↦ ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hgA x hx) ht))
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (t * g x)) ∂μ := setLIntegral_le_lintegral _ _

variable (μ) in
/-- The normalised logarithmic moment generating function `a⁻¹ log ∫ e^{a g} dμ`. -/
def logMgfRate (μ : Measure X) (a : ℝ) (g : X → ℝ) : EReal :=
  ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (a * g x)) ∂μ) / (a : EReal)

variable [TopologicalSpace X] [OpensMeasurableSpace X]

variable {l : Filter κ} {a : κ → ℝ} {μ : κ → Measure X}

/-- **The Cramér–Chernoff upper bound over compact sets.** Let `G` be a family of continuous
functions whose normalised log-moment generating functions are asymptotically bounded by
`Λ : (X → ℝ) → ℝ`. Then on every compact set the normalised log-probabilities are asymptotically
bounded by minus the infimum of the Legendre-type rate function `I x = ⨆_{g ∈ G} (g x − Λ g)`.

The proof is Chebyshev's inequality on a finite subcover: at every point `x` of the compact set
some `g ∈ G` has `g x − Λ g > c`, hence `g > Λ g + c` on a neighbourhood of `x` by continuity, and
`μ` of that neighbourhood is at most `e^{−a (Λ g + c)} ∫ e^{a g} dμ`; a finite union costs only
`a⁻¹ log (card)`, which vanishes because the speed tends to infinity. -/
theorem limsup_logRate_le_of_isCompact [l.NeBot] (ha : ∀ n, 0 < a n)
    (hatop : Tendsto a l atTop)
    {G : Set (X → ℝ)} (hGc : ∀ g ∈ G, Continuous g) {Λ : (X → ℝ) → ℝ}
    (hΛ : ∀ g ∈ G, limsup (fun n ↦ logMgfRate (μ n) (a n) g) l ≤ (Λ g : EReal))
    {K : Set X} (hK : IsCompact K) :
    limsup (fun n ↦ logRate (μ n) (a n) K) l
      ≤ -⨅ x ∈ K, ⨆ g ∈ G, ((g x - Λ g : ℝ) : EReal) := by
  refine EReal.le_neg_of_forall_coe_lt fun c hc ↦ ?_
  rw [← EReal.coe_neg]
  -- at every point of `K` some `g ∈ G` separates the level `c`
  have hpt : ∀ x ∈ K, ∃ g ∈ G, c < g x - Λ g := by
    intro x hx
    have hlt : (c : EReal) < ⨆ g ∈ G, ((g x - Λ g : ℝ) : EReal) :=
      lt_of_lt_of_le hc (iInf₂_le x hx)
    obtain ⟨g₀, hg₀⟩ := lt_iSup_iff.1 hlt
    obtain ⟨hg₀G, hg₀c⟩ := lt_iSup_iff.1 hg₀
    exact ⟨g₀, hg₀G, EReal.coe_lt_coe_iff.1 hg₀c⟩
  choose! g hgG hgc using hpt
  set U : X → Set X := fun x ↦ {y | Λ (g x) + c < g x y} with hUdef
  have hUopen : ∀ x ∈ K, IsOpen (U x) := fun x hx ↦
    isOpen_lt continuous_const (hGc _ (hgG x hx))
  have hUmem : ∀ x ∈ K, x ∈ U x := fun x hx ↦ by
    have h := hgc x hx
    show Λ (g x) + c < g x x
    linarith
  obtain ⟨t, htK, htfin, htcover⟩ :=
    hK.elim_finite_subcover_image hUopen fun x hx ↦ mem_biUnion hx (hUmem x hx)
  set s : Finset X := htfin.toFinset with hsdef
  have hsK : ∀ x ∈ s, x ∈ K := fun x hx ↦ htK (htfin.mem_toFinset.1 hx)
  have hcover : K ⊆ ⋃ x ∈ s, U x := by
    refine htcover.trans (iUnion₂_subset fun x hx ↦ ?_)
    exact subset_iUnion₂ (s := fun x (_ : x ∈ s) ↦ U x) x (htfin.mem_toFinset.2 hx)
  -- the ε-estimate on each piece of the cover
  refine EReal.le_coe_of_forall_pos_add fun ε hε ↦ ?_
  have hev : ∀ x ∈ s, ∀ᶠ n in l,
      logMgfRate (μ n) (a n) (g x) < ((Λ (g x) + ε : ℝ) : EReal) := fun x hx ↦
    eventually_lt_of_limsup_lt (lt_of_le_of_lt (hΛ _ (hgG x (hsK x hx)))
      (EReal.coe_lt_coe_iff.2 (by linarith)))
  have hevall : ∀ᶠ n in l, ∀ x ∈ s, logMgfRate (μ n) (a n) (g x) < ((Λ (g x) + ε : ℝ) : EReal) :=
    (eventually_all_finset s).2 hev
  -- the resulting bound on `μ n K`
  have hkey : ∀ᶠ n in l, logRate (μ n) (a n) K
      ≤ ((Real.log (s.card + 1) / a n + (ε - c) : ℝ) : EReal) := by
    filter_upwards [hevall] with n hn
    have han : (0 : ℝ) < a n := ha n
    have hpiece : ∀ x ∈ s, μ n (U x)
        ≤ ENNReal.ofReal (Real.exp (a n * (ε - c))) := by
      intro x hx
      set Z : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (Real.exp (a n * g x y)) ∂ (μ n) with hZ
      -- the moment generating function is at most `e^{a (Λ g + ε)}`
      have hZle : Z ≤ ENNReal.ofReal (Real.exp (a n * (Λ (g x) + ε))) := by
        have h1 : ENNReal.log Z ≤ ((a n * (Λ (g x) + ε) : ℝ) : EReal) := by
          have h2 : ENNReal.log Z / (a n : EReal) ≤ ((Λ (g x) + ε : ℝ) : EReal) :=
            (hn x hx).le
          rw [EReal.div_le_iff_le_mul (by exact_mod_cast han) (EReal.coe_ne_top _)] at h2
          rwa [← EReal.coe_mul] at h2
        rwa [← ENNReal.log_le_log_iff, ENNReal.log_ofReal_of_pos (Real.exp_pos _),
          Real.log_exp]
      -- Chebyshev on the piece
      have hcheb : μ n (U x) * ENNReal.ofReal (Real.exp (a n * (Λ (g x) + c))) ≤ Z :=
        measure_mul_ofReal_exp_le_lintegral han.le
          ((hUopen x (hsK x hx)).measurableSet) fun y hy ↦ le_of_lt hy
      have hmul : μ n (U x) * ENNReal.ofReal (Real.exp (a n * (Λ (g x) + c)))
            * ENNReal.ofReal (Real.exp (-(a n * (Λ (g x) + c))))
          ≤ ENNReal.ofReal (Real.exp (a n * (Λ (g x) + ε)))
            * ENNReal.ofReal (Real.exp (-(a n * (Λ (g x) + c)))) := by
        gcongr
        exact hcheb.trans hZle
      rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
        add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, mul_one,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at hmul
      refine hmul.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq (by ring))))
    have hsum : μ n K ≤ (s.card + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (a n * (ε - c))) := by
      refine (measure_mono hcover).trans ((measure_biUnion_finset_le s _).trans ?_)
      refine (Finset.sum_le_sum hpiece).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact le_self_add
    have hlog : ENNReal.log (μ n K)
        ≤ ((Real.log (s.card + 1) + a n * (ε - c) : ℝ) : EReal) := by
      refine (ENNReal.log_le_log hsum).trans ?_
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp,
        EReal.coe_add]
      gcongr
      rw [show ((s.card : ℝ≥0∞) + 1) = ENNReal.ofReal ((s.card : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one],
        ENNReal.log_ofReal_of_pos (by positivity)]
    calc logRate (μ n) (a n) K
        ≤ ((Real.log (s.card + 1) + a n * (ε - c) : ℝ) : EReal) / (a n : EReal) :=
          EReal.div_le_div_right_of_nonneg (by exact_mod_cast han.le) hlog
      _ = ((Real.log (s.card + 1) / a n + (ε - c) : ℝ) : EReal) := by
          rw [← EReal.coe_div]
          congr 1
          field_simp
  refine le_trans (limsup_le_limsup hkey) ?_
  have hten : Tendsto (fun n ↦ ((Real.log (s.card + 1) / a n + (ε - c) : ℝ) : EReal)) l
      (𝓝 (((-c + ε : ℝ)) : EReal)) := by
    refine EReal.tendsto_coe.2 ?_
    have h0 : Tendsto (fun n ↦ Real.log (s.card + 1) / a n) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hatop
    have hrw : (-c + ε : ℝ) = 0 + (ε - c) := by ring
    rw [hrw]
    exact h0.add tendsto_const_nhds
  exact le_of_eq hten.limsup_eq

end Cramer

/-! ### The change-of-measure lower bound -/

section ChangeOfMeasure

variable [MeasurableSpace X] {l : Filter κ} {a : κ → ℝ} {μ ν : κ → Measure X} {A : κ → Set X}

/-- **The change-of-measure (tilting) lower bound.** If a comparison family `ν` charges the sets
`A n` with mass at least a fixed `b > 0`, and if `ν (A n) ≤ e^{a_n c} μ (A n)` — the shape taken by
a Radon–Nikodym bound `dν/dμ ≤ e^{a_n c}` on `A n` — then the normalised log-probabilities of `μ`
are asymptotically at least `-c`.

This is the engine of every large deviation *lower* bound: `ν` is chosen to (nearly) minimise the
rate function on the set in question, `c` is (nearly) its rate, and the sets `A n` are the sets on
which `ν` concentrates, so that `ν (A n) → 1`. -/
theorem le_liminf_logRate_of_le_smul [l.NeBot] {b c : ℝ} (hb : 0 < b)
    (ha : ∀ n, 0 < a n) (hatop : Tendsto a l atTop)
    (hν : ∀ᶠ n in l, ENNReal.ofReal b ≤ ν n (A n))
    (hle : ∀ᶠ n in l, ν n (A n) ≤ ENNReal.ofReal (Real.exp (a n * c)) * μ n (A n)) :
    ((-c : ℝ) : EReal) ≤ liminf (fun n ↦ logRate (μ n) (a n) (A n)) l := by
  have hlow : ∀ᶠ n in l,
      ((Real.log b / a n - c : ℝ) : EReal) ≤ logRate (μ n) (a n) (A n) := by
    filter_upwards [hν, hle] with n h1 h2
    have han : (0 : ℝ) < a n := ha n
    -- divide the tilting bound by the exponential factor
    have h3 : ENNReal.ofReal b * ENNReal.ofReal (Real.exp (-(a n * c)))
        ≤ ENNReal.ofReal (Real.exp (a n * c)) * μ n (A n)
          * ENNReal.ofReal (Real.exp (-(a n * c))) := by gcongr; exact h1.trans h2
    rw [mul_comm (ENNReal.ofReal (Real.exp (a n * c))), mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_mul hb.le] at h3
    have h4 : ((Real.log b - a n * c : ℝ) : EReal) ≤ ENNReal.log (μ n (A n)) := by
      refine le_trans (le_of_eq ?_) (ENNReal.log_le_log h3)
      rw [ENNReal.log_ofReal_of_pos (by positivity), Real.log_mul hb.ne' (Real.exp_ne_zero _),
        Real.log_exp]
      congr 1
    calc ((Real.log b / a n - c : ℝ) : EReal)
        = ((Real.log b - a n * c : ℝ) : EReal) / (a n : EReal) := by
          rw [← EReal.coe_div]; congr 1; field_simp
      _ ≤ logRate (μ n) (a n) (A n) :=
          EReal.div_le_div_right_of_nonneg (by exact_mod_cast han.le) h4
  have hten : Tendsto (fun n ↦ ((Real.log b / a n - c : ℝ) : EReal)) l (𝓝 ((-c : ℝ) : EReal)) := by
    refine EReal.tendsto_coe.2 ?_
    have h0 : Tendsto (fun n ↦ Real.log b / a n) l (𝓝 0) := tendsto_const_nhds.div_atTop hatop
    have hrw : (-c : ℝ) = 0 - c := by ring
    rw [hrw]
    exact h0.sub tendsto_const_nhds
  calc ((-c : ℝ) : EReal) = liminf (fun n ↦ ((Real.log b / a n - c : ℝ) : EReal)) l :=
        hten.liminf_eq.symm
    _ ≤ liminf (fun n ↦ logRate (μ n) (a n) (A n)) l := liminf_le_liminf hlow

end ChangeOfMeasure

end MeasureTheory
