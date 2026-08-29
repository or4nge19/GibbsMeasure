/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.UniformConvergence
public import Mathlib.Topology.Algebra.UniformFilterBasis

/-!
# The space `ℬ` of absolutely summable potentials, and the Gibbs correspondence

Georgii (2.11) and Theorem (4.23)(c)–(d).

* `Potential.absolutelySummable`: the `ℝ`-submodule of absolutely summable potentials with no
  `∅`-interaction — Georgii indexes potentials by the *nonempty* finite sets, so `Φ ∅ = 0` renders
  his indexing on the type `Potential S E` — with the per-site seminorms `Potential.seminormAt`
  and their `WithSeminorms` topology. The seminorms separate, so the space is `T1`, and for
  countable `S` it is metrizable (Georgii (2.11)).
* `Potential.BSpace`: the measurable locus (measurability of the interactions is part of
  Georgii's Definition (2.2)(i)), carrying the Gibbsian specifications.
* `Potential.BSpace.isClosed_graph_GP`: **Georgii (4.23)(c)** — the graph of the Gibbs
  correspondence `𝒢` is closed (no standard Borel hypothesis, matching the book's remark).
* `Potential.BSpace.isClosed_setOf_exists_mem_GP`: **Georgii (4.23)(d)** — `𝒢⁻¹(F)` is closed
  for every closed `F`, over a standard Borel state space.

For countable `S`, `ℬ` is complete (`CompleteSpace`): Georgii's (2.11) Fréchet space.
-/

@[expose] public section

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped Topology ENNReal NNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E]

/-! ### The module structure on potentials

`Potential S E` is definitionally the Pi type `(Δ : Finset S) → (S → E) → ℝ`, so the Pi
instances transport along `inferInstanceAs`; all operations are pointwise by `rfl`. -/

instance : AddCommGroup (Potential S E) :=
  inferInstanceAs (AddCommGroup ((Δ : Finset S) → (S → E) → ℝ))

instance : Module ℝ (Potential S E) :=
  inferInstanceAs (Module ℝ ((Δ : Finset S) → (S → E) → ℝ))

@[simp] lemma add_apply (Φ Ψ : Potential S E) (A : Finset S) (η : S → E) :
    (Φ + Ψ) A η = Φ A η + Ψ A η := rfl

@[simp] lemma sub_apply (Φ Ψ : Potential S E) (A : Finset S) (η : S → E) :
    (Φ - Ψ) A η = Φ A η - Ψ A η := rfl

@[simp] lemma neg_apply (Φ : Potential S E) (A : Finset S) (η : S → E) :
    (-Φ) A η = -(Φ A η) := rfl

@[simp] lemma smul_apply (c : ℝ) (Φ : Potential S E) (A : Finset S) (η : S → E) :
    (c • Φ) A η = c * Φ A η := rfl

@[simp] lemma zero_apply (A : Finset S) (η : S → E) : (0 : Potential S E) A η = 0 := rfl

/-! ### `‖·‖ᵢ` under the module operations -/

@[simp] lemma normAt_zero (i : S) : (0 : Potential S E).normAt i = 0 := by
  simp [normAt]

lemma normAt_neg (Φ : Potential S E) (i : S) : (-Φ).normAt i = Φ.normAt i := by
  simp [normAt]

/-- Subadditivity of Georgii's `‖·‖ᵢ`: the `enorm` triangle inequality under `iSup`, summed by
`ENNReal.tsum_add`. -/
lemma normAt_add_le (Φ Ψ : Potential S E) (i : S) :
    (Φ + Ψ).normAt i ≤ Φ.normAt i + Ψ.normAt i := by
  rw [normAt, normAt, normAt, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h : A ∈ {A : Finset S | i ∈ A}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
    refine iSup_le fun η ↦ ?_
    calc ‖(Φ + Ψ) A η‖ₑ = ‖Φ A η + Ψ A η‖ₑ := rfl
      _ ≤ ‖Φ A η‖ₑ + ‖Ψ A η‖ₑ := enorm_add_le _ _
      _ ≤ _ := add_le_add (le_iSup (fun η ↦ ‖Φ A η‖ₑ) η) (le_iSup (fun η ↦ ‖Ψ A η‖ₑ) η)
  · simp [Set.indicator_of_notMem h]

/-- Exact homogeneity of Georgii's `‖·‖ᵢ`. -/
lemma normAt_smul (c : ℝ) (Φ : Potential S E) (i : S) :
    (c • Φ).normAt i = ‖c‖ₑ * Φ.normAt i := by
  rw [normAt, normAt, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun A ↦ ?_
  by_cases h : A ∈ {A : Finset S | i ∈ A}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.mul_iSup]
    refine iSup_congr fun η ↦ ?_
    rw [show (c • Φ) A η = c * Φ A η from rfl, enorm_mul]
  · simp [Set.indicator_of_notMem h]

protected lemma IsAbsolutelySummable.add {Φ Ψ : Potential S E}
    (hΦ : Φ.IsAbsolutelySummable) (hΨ : Ψ.IsAbsolutelySummable) :
    (Φ + Ψ).IsAbsolutelySummable :=
  ⟨fun i ↦ ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨hΦ.normAt_ne_top i, hΨ.normAt_ne_top i⟩) (normAt_add_le Φ Ψ i)⟩

protected lemma IsAbsolutelySummable.smul (c : ℝ) {Φ : Potential S E}
    (hΦ : Φ.IsAbsolutelySummable) : (c • Φ).IsAbsolutelySummable :=
  ⟨fun i ↦ by
    rw [normAt_smul]
    exact ENNReal.mul_ne_top enorm_ne_top (hΦ.normAt_ne_top i)⟩

protected lemma IsAbsolutelySummable.neg {Φ : Potential S E}
    (hΦ : Φ.IsAbsolutelySummable) : (-Φ).IsAbsolutelySummable :=
  ⟨fun i ↦ by rw [normAt_neg]; exact hΦ.normAt_ne_top i⟩

protected lemma IsAbsolutelySummable.sub {Φ Ψ : Potential S E}
    (hΦ : Φ.IsAbsolutelySummable) (hΨ : Ψ.IsAbsolutelySummable) :
    (Φ - Ψ).IsAbsolutelySummable := by
  rw [sub_eq_add_neg]
  exact hΦ.add hΨ.neg

instance : IsAbsolutelySummable (0 : Potential S E) := ⟨fun i ↦ by simp⟩

/-! ### (B1) Georgii (2.11): the submodule `ℬ` of absolutely summable potentials -/

variable (S E) in
/-- **Georgii (2.11).** The `ℝ`-submodule of absolutely summable potentials, the linear part of
Georgii's space `ℬ`.  (Named after its membership predicate `Potential.IsAbsolutelySummable`,
following the Mathlib pattern `MeasureTheory.Memℒp` / `MeasureTheory.Lp`.) -/
def absolutelySummable : Submodule ℝ (Potential S E) where
  carrier := {Φ | Φ.IsAbsolutelySummable ∧ Φ ∅ = 0}
  add_mem' hΦ hΨ := ⟨hΦ.1.add hΨ.1, funext fun η ↦ by
    rw [add_apply, hΦ.2, hΨ.2]; simp⟩
  zero_mem' := ⟨inferInstanceAs (IsAbsolutelySummable (0 : Potential S E)), rfl⟩
  smul_mem' c _ hΦ := ⟨hΦ.1.smul c, funext fun η ↦ by
    rw [smul_apply, hΦ.2]; simp⟩

@[simp] lemma mem_absolutelySummable {Φ : Potential S E} :
    Φ ∈ absolutelySummable S E ↔ Φ.IsAbsolutelySummable ∧ Φ ∅ = 0 := Iff.rfl

instance (Φ : absolutelySummable S E) : IsAbsolutelySummable (Φ : Potential S E) := Φ.2.1

lemma coe_apply_empty (Φ : absolutelySummable S E) : (Φ : Potential S E) ∅ = 0 := Φ.2.2

/-! ### (B2) Georgii (2.11): the seminorms `‖·‖ᵢ` and the locally convex topology -/

variable (S E) in
/-- **Georgii (2.12) as a seminorm on `ℬ`**: `Φ ↦ ‖Φ‖ᵢ = (normAt Φ i).toReal`.  The triangle
inequality descends from the `ℝ≥0∞`-inequality `normAt_add_le` by `toReal` monotonicity;
finiteness of all the quantities involved comes from membership in the submodule. -/
def seminormAt (i : S) : Seminorm ℝ (absolutelySummable S E) :=
  Seminorm.of (fun Φ ↦ ((Φ : Potential S E).normAt i).toReal)
    (fun Φ Ψ ↦ by
      have hΦ := IsAbsolutelySummable.normAt_ne_top (Φ := (Φ : Potential S E)) i
      have hΨ := IsAbsolutelySummable.normAt_ne_top (Φ := (Ψ : Potential S E)) i
      calc (((Φ + Ψ : absolutelySummable S E) : Potential S E).normAt i).toReal
          = (((Φ : Potential S E) + (Ψ : Potential S E)).normAt i).toReal := by
            rw [Submodule.coe_add]
        _ ≤ ((Φ : Potential S E).normAt i + (Ψ : Potential S E).normAt i).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hΦ, hΨ⟩) (normAt_add_le _ _ i)
        _ = _ := ENNReal.toReal_add hΦ hΨ)
    (fun c Φ ↦ by simp [normAt_smul, ENNReal.toReal_mul])

@[simp] lemma seminormAt_apply (i : S) (Φ : absolutelySummable S E) :
    seminormAt S E i Φ = ((Φ : Potential S E).normAt i).toReal := rfl

variable (S E) in
/-- The family `(‖·‖ᵢ)_{i ∈ S}` of Georgii (2.11), as a Mathlib `SeminormFamily`. -/
def seminormFamily : SeminormFamily ℝ (absolutelySummable S E) S := seminormAt S E

/-- **Georgii (2.11), the topology of `ℬ`**: the locally convex topology generated by the
seminorms `‖·‖ᵢ`, through Mathlib's `SeminormFamily.moduleFilterBasis`. -/
instance : TopologicalSpace (absolutelySummable S E) :=
  (seminormFamily S E).moduleFilterBasis.topology

variable (S E) in
theorem withSeminorms_seminormFamily : WithSeminorms (seminormFamily S E) := ⟨rfl⟩

/-- **Convergence in `ℬ`** is seminorm convergence: `Φₓ → Φ` iff `‖Φₓ − Φ‖ᵢ → 0` for every
site `i`. -/
theorem tendsto_iff_tendsto_seminormAt {ι : Type*} {l : Filter ι}
    {Φs : ι → absolutelySummable S E} {Φ : absolutelySummable S E} :
    Tendsto Φs l (𝓝 Φ) ↔ ∀ i : S, Tendsto (fun x ↦ seminormAt S E i (Φs x - Φ)) l (𝓝 0) := by
  rw [(withSeminorms_seminormFamily S E).tendsto_nhds Φs Φ]
  refine forall_congr' fun i ↦ ⟨fun h ↦ ?_, fun h ε hε ↦ ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [h ε hε] with x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
    exact hx
  · filter_upwards [Metric.tendsto_nhds.1 h ε hε] with x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at hx
    exact hx

/-- The seminorms `‖·‖ᵢ` separate `ℬ`: a potential vanishing in every `‖·‖ᵢ` vanishes on every
nonempty support, and on `∅` by definition of `ℬ`. -/
lemma eq_zero_of_forall_seminormAt_eq_zero {Φ : absolutelySummable S E}
    (h : ∀ i, seminormAt S E i Φ = 0) : Φ = 0 := by
  refine Subtype.ext (funext fun A ↦ funext fun η ↦ ?_)
  show (Φ : Potential S E) A η = 0
  rcases A.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [coe_apply_empty]; rfl
  · have hfin := IsAbsolutelySummable.normAt_ne_top (Φ := (Φ : Potential S E)) i
    have h0 : (Φ : Potential S E).normAt i = 0 := by
      have := h i
      rw [seminormAt_apply] at this
      exact (ENNReal.toReal_eq_zero_iff _).1 this |>.resolve_right hfin
    have hterm : ({A : Finset S | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖(Φ : Potential S E) A η‖ₑ)) A ≤ (Φ : Potential S E).normAt i :=
      ENNReal.le_tsum A
    rw [h0, nonpos_iff_eq_zero, Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hi),
      ENNReal.iSup_eq_zero] at hterm
    simpa using hterm η

instance : T1Space (absolutelySummable S E) :=
  (withSeminorms_seminormFamily S E).T1_of_separating fun Φ hΦ ↦ by
    by_contra h
    push Not at h
    exact hΦ (eq_zero_of_forall_seminormAt_eq_zero fun i ↦ h i)

instance : IsTopologicalAddGroup (absolutelySummable S E) :=
  (seminormFamily S E).addGroupFilterBasis.isTopologicalAddGroup

/-- The uniform structure of the topological group `ℬ`, with its topology the seminorm topology
(`UniformSpace.replaceTopology` avoids an instance diamond). -/
instance : UniformSpace (absolutelySummable S E) :=
  (seminormFamily S E).addGroupFilterBasis.uniformSpace.replaceTopology rfl

instance : IsUniformAddGroup (absolutelySummable S E) :=
  (seminormFamily S E).addGroupFilterBasis.isUniformAddGroup

/-- For countable `S`, `ℬ` is countably seminormed, hence first countable. -/
instance [Countable S] : FirstCountableTopology (absolutelySummable S E) :=
  (withSeminorms_seminormFamily S E).firstCountableTopology

/-- For countable `S`, the countably seminormed space `ℬ` is pseudo-metrizable. -/
instance [Countable S] : (uniformity (absolutelySummable S E)).IsCountablyGenerated :=
  IsUniformAddGroup.uniformity_countably_generated

instance [Countable S] : TopologicalSpace.PseudoMetrizableSpace (absolutelySummable S E) :=
  UniformSpace.pseudoMetrizableSpace

/-- **Georgii (2.11), metrizability**: for countable `S`, the separated countably seminormed space
`ℬ` is metrizable. -/
instance [Countable S] : TopologicalSpace.MetrizableSpace (absolutelySummable S E) :=
  inferInstance

/-! ### Georgii (2.11): `ℬ` is complete -/

/-- `normAt` is lower semicontinuous along pointwise convergence of the interaction terms
(Fatou's lemma for the counting measure). -/
lemma normAt_le_liminf {Φs : ℕ → Potential S E} {Ψ : Potential S E}
    (h : ∀ A η, Tendsto (fun n ↦ Φs n A η) atTop (𝓝 (Ψ A η))) (i : S) :
    Ψ.normAt i ≤ liminf (fun n ↦ (Φs n).normAt i) atTop := by
  classical
  letI : MeasurableSpace (Finset S) := ⊤
  have hterm : ∀ A : Finset S,
      (⨆ η, ‖Ψ A η‖ₑ) ≤ liminf (fun n ↦ ⨆ η, ‖Φs n A η‖ₑ) atTop := by
    intro A
    refine iSup_le fun η ↦ ?_
    have h1 : Tendsto (fun n ↦ ‖Φs n A η‖ₑ) atTop (𝓝 ‖Ψ A η‖ₑ) :=
      (continuous_enorm.tendsto _).comp (h A η)
    rw [← h1.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n ↦ le_iSup (fun η ↦ ‖Φs n A η‖ₑ) η)
  set F : ℕ → Finset S → ℝ≥0∞ :=
    fun n A ↦ ({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φs n A η‖ₑ)) A with hF
  have hind : ∀ A : Finset S,
      ({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Ψ A η‖ₑ)) A ≤ liminf (fun n ↦ F n A) atTop := by
    intro A
    by_cases hA : A ∈ {A : Finset S | i ∈ A}
    · simp only [hF, Set.indicator_of_mem hA]; exact hterm A
    · simp [hF, Set.indicator_of_notMem hA]
  have hmeas : ∀ n, Measurable (F n) := fun n ↦ measurable_from_top
  calc Ψ.normAt i
      = ∑' A, ({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Ψ A η‖ₑ)) A := rfl
    _ ≤ ∑' A, liminf (fun n ↦ F n A) atTop := ENNReal.tsum_le_tsum hind
    _ = ∫⁻ A, liminf (fun n ↦ F n A) atTop ∂Measure.count :=
        (lintegral_count' measurable_from_top).symm
    _ ≤ liminf (fun n ↦ ∫⁻ A, F n A ∂Measure.count) atTop := lintegral_liminf_le hmeas
    _ = liminf (fun n ↦ (Φs n).normAt i) atTop := by
        refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
        rw [lintegral_count' (hmeas n)]
        rfl

/-- The seminorm topology of `ℬ`: Cauchy sequences are Cauchy in every seminorm. -/
lemma seminormAt_sub_lt_of_cauchySeq {u : ℕ → absolutelySummable S E} (hu : CauchySeq u)
    (i : S) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ n ≥ N, seminormAt S E i (u n - u m) < ε := by
  have h := (cauchySeq_iff_tendsto.1 hu)
  rw [uniformity_eq_comap_nhds_zero (absolutelySummable S E), tendsto_comap_iff] at h
  have h' := ((withSeminorms_seminormFamily S E).tendsto_nhds _ 0).1 h i ε hε
  simp only [sub_zero, Prod.map, Function.comp_def] at h'
  rw [← prod_atTop_atTop_eq, eventually_prod_iff] at h'
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := h'
  rw [eventually_atTop] at hpa hpb
  obtain ⟨Na, hNa⟩ := hpa
  obtain ⟨Nb, hNb⟩ := hpb
  refine ⟨max Na Nb, fun m hm n hn ↦ ?_⟩
  exact hab (hNa m (le_of_max_le_left hm)) (hNb n (le_of_max_le_right hn))

/-- A single interaction term is dominated by the seminorm at any of its sites. -/
lemma abs_apply_le_seminormAt (Φ : absolutelySummable S E) {A : Finset S} {i : S} (hi : i ∈ A)
    (η : S → E) : |(Φ : Potential S E) A η| ≤ seminormAt S E i Φ := by
  have hfin := IsAbsolutelySummable.normAt_ne_top (Φ := (Φ : Potential S E)) i
  have h1 : ‖(Φ : Potential S E) A η‖ₑ ≤ (Φ : Potential S E).normAt i := by
    calc ‖(Φ : Potential S E) A η‖ₑ ≤ ⨆ η, ‖(Φ : Potential S E) A η‖ₑ :=
          le_iSup (fun η ↦ ‖(Φ : Potential S E) A η‖ₑ) η
      _ = ({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖(Φ : Potential S E) A η‖ₑ)) A := by
          rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hi)]
      _ ≤ _ := ENNReal.le_tsum A
  rw [seminormAt_apply, ← ENNReal.toReal_ofReal (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]
  exact ENNReal.toReal_mono hfin h1

/-- `normAt` of a sum is controlled by the summands' norms. -/
lemma normAt_le_normAt_add_normAt_sub (Φ Ψ : Potential S E) (i : S) :
    Φ.normAt i ≤ Ψ.normAt i + (Φ - Ψ).normAt i := by
  have := normAt_add_le Ψ (Φ - Ψ) i
  rwa [add_sub_cancel] at this

/-- **Georgii (2.11), completeness.** For countable `S`, the space `ℬ` of absolutely summable
potentials is complete: it is a Fréchet space. -/
instance [Countable S] : CompleteSpace (absolutelySummable S E) := by
  classical
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hptw : ∀ (A : Finset S) (η : S → E), A.Nonempty →
      CauchySeq (fun n ↦ (u n : Potential S E) A η) := by
    intro A η hA
    obtain ⟨i, hi⟩ := hA
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := seminormAt_sub_lt_of_cauchySeq hu i hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [Real.dist_eq]
    calc |(u m : Potential S E) A η - (u n : Potential S E) A η|
        = |((u m - u n : absolutelySummable S E) : Potential S E) A η| := by
          rw [Submodule.coe_sub, sub_apply]
      _ ≤ seminormAt S E i (u m - u n) := abs_apply_le_seminormAt _ hi η
      _ < ε := hN n hn m hm
  choose! L hL using fun (A : Finset S) (η : S → E) (hA : A.Nonempty) ↦
    cauchySeq_tendsto_of_complete (hptw A η hA)
  set Ψ : Potential S E := fun A η ↦ if A.Nonempty then L A η else 0 with hΨ
  have hΨ_empty : Ψ ∅ = 0 := by
    funext η
    simp [hΨ]
  have hconv : ∀ A η, Tendsto (fun n ↦ (u n : Potential S E) A η) atTop (𝓝 (Ψ A η)) := by
    intro A η
    by_cases hA : A.Nonempty
    · simp only [hΨ, if_pos hA]
      exact hL A η hA
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      simp only [hΨ, Finset.not_nonempty_empty, if_false]
      have : ∀ n, (u n : Potential S E) ∅ η = 0 := fun n ↦ by rw [coe_apply_empty]; rfl
      simp only [this]
      exact tendsto_const_nhds
  -- `Ψ` is absolutely summable: `normAt` is lower semicontinuous and the sequence is bounded
  have hbdd : ∀ i : S, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n in atTop, (u n : Potential S E).normAt i ≤ C := by
    intro i
    obtain ⟨N, hN⟩ := seminormAt_sub_lt_of_cauchySeq hu i one_pos
    refine ⟨(u N : Potential S E).normAt i + 1,
      ENNReal.add_ne_top.2 ⟨IsAbsolutelySummable.normAt_ne_top i, ENNReal.one_ne_top⟩, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    calc (u n : Potential S E).normAt i
        ≤ (u N : Potential S E).normAt i
          + ((u n : Potential S E) - (u N : Potential S E)).normAt i :=
          normAt_le_normAt_add_normAt_sub _ _ i
      _ ≤ (u N : Potential S E).normAt i + 1 := by
          gcongr
          have h := hN N le_rfl n hn
          rw [seminormAt_apply, Submodule.coe_sub] at h
          have hfin := IsAbsolutelySummable.normAt_ne_top
            (Φ := ((u n - u N : absolutelySummable S E) : Potential S E)) i
          rw [Submodule.coe_sub] at hfin
          rw [← ENNReal.ofReal_toReal hfin]
          exact ENNReal.ofReal_le_ofReal h.le |>.trans (by simp)
  have hΨ_summable : IsAbsolutelySummable Ψ := by
    refine ⟨fun i ↦ ?_⟩
    obtain ⟨C, hC, hev⟩ := hbdd i
    refine ne_top_of_le_ne_top hC ?_
    refine (normAt_le_liminf hconv i).trans ?_
    exact liminf_le_of_frequently_le' hev.frequently
  set Ψ' : absolutelySummable S E := ⟨Ψ, hΨ_summable, hΨ_empty⟩ with hΨ'
  refine ⟨Ψ', ?_⟩
  rw [tendsto_iff_tendsto_seminormAt]
  intro i
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := seminormAt_sub_lt_of_cauchySeq hu i (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
  -- `normAt (u n - Ψ) i ≤ ofReal (ε / 2)` by lower semicontinuity along `m ↦ u n - u m`
  have hconv' : ∀ A η, Tendsto (fun m ↦ ((u n : Potential S E) - (u m : Potential S E)) A η)
      atTop (𝓝 (((u n : Potential S E) - Ψ) A η)) := by
    intro A η
    simp only [sub_apply]
    exact tendsto_const_nhds.sub (hconv A η)
  have hle : ((u n : Potential S E) - Ψ).normAt i ≤ ENNReal.ofReal (ε / 2) := by
    refine (normAt_le_liminf hconv' i).trans ?_
    refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
    filter_upwards [eventually_ge_atTop N] with m hm
    have h := hN m hm n hn
    rw [seminormAt_apply, Submodule.coe_sub] at h
    have hfin := IsAbsolutelySummable.normAt_ne_top
      (Φ := ((u n - u m : absolutelySummable S E) : Potential S E)) i
    rw [Submodule.coe_sub] at hfin
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal h.le
  calc seminormAt S E i (u n - Ψ')
      = (((u n : Potential S E) - Ψ).normAt i).toReal := by
        rw [seminormAt_apply, Submodule.coe_sub]
    _ ≤ ε / 2 := by
        rw [← ENNReal.toReal_ofReal (half_pos hε).le]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ < ε := half_lt_self hε

/-! ### The measurable locus is closed -/

/-- Convergence in `ℬ` implies pointwise convergence of every interaction term on a nonempty
support. -/
lemma tendsto_apply_of_tendsto {u : ℕ → absolutelySummable S E} {Φ : absolutelySummable S E}
    (hlim : Tendsto u atTop (𝓝 Φ)) {Δ : Finset S} {i : S} (hi : i ∈ Δ) (η : S → E) :
    Tendsto (fun n ↦ (u n : Potential S E) Δ η) atTop (𝓝 ((Φ : Potential S E) Δ η)) := by
  have h := (tendsto_iff_tendsto_seminormAt.1 hlim) i
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at this
  rw [Real.dist_eq]
  calc |(u n : Potential S E) Δ η - (Φ : Potential S E) Δ η|
      = |((u n - Φ : absolutelySummable S E) : Potential S E) Δ η| := by
        rw [Submodule.coe_sub, sub_apply]
    _ ≤ seminormAt S E i (u n - Φ) := abs_apply_le_seminormAt _ hi η
    _ < ε := this

/-- Measurability of the interaction terms is closed under convergence in `ℬ`: Georgii's
measurable locus `BSpace` is a closed subspace. -/
lemma isClosed_setOf_isPotential [Countable S] :
    IsClosed {Φ : absolutelySummable S E | IsPotential (Φ : Potential S E)} := by
  rw [← isSeqClosed_iff_isClosed]
  intro u Φ hu hlim
  constructor
  intro Δ
  rcases Δ.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [coe_apply_empty]
    exact @measurable_const _ _ _ (cylinderEvents (X := fun _ : S ↦ E) (∅ : Finset S)) _
  · letI : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
    exact measurable_of_tendsto_metrizable (fun n ↦ (hu n).measurable Δ)
      (tendsto_pi_nhds.2 fun η ↦ tendsto_apply_of_tendsto hlim hi η)

/-! ### The bridge to Georgii (4.19): Hamiltonians are additive in the potential on `ℬ`

Georgii (2.14) applied to a *difference* of potentials bounds the Hamiltonian difference
`|H_Λ^Φ − H_Λ^Ψ|` by the constant `hamiltonianBound (Φ - Ψ) Λ = ∑_{i ∈ Λ} ‖Φ − Ψ‖ᵢ`, which
tends to `0` along any net converging in the topology of `ℬ` — exactly the bound-function
hypothesis of the repo's Georgii (4.19), `Potential.tendsto_dist_action_gibbsSpecification`. -/

lemma hamiltonianTerms_sub_eq (Φ Ψ : Potential S E) (Λ : Finset S) (η : S → E) :
    (Φ - Ψ).hamiltonianTerms Λ η = Φ.hamiltonianTerms Λ η - Ψ.hamiltonianTerms Λ η := by
  funext A
  by_cases h : Disjoint A Λ
  · simp [hamiltonianTerms_of_disjoint h]
  · simp [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h]

/-- The Hamiltonian is additive in the potential (on absolutely summable potentials), by
linearity of unconditional sums. -/
theorem hamiltonian_sub (Φ Ψ : Potential S E)
    [Φ.IsAbsolutelySummable] [Ψ.IsAbsolutelySummable] (Λ : Finset S) (η : S → E) :
    (Φ - Ψ).hamiltonian Λ η = Φ.hamiltonian Λ η - Ψ.hamiltonian Λ η := by
  have : (Φ - Ψ).IsAbsolutelySummable :=
    IsAbsolutelySummable.sub ‹Φ.IsAbsolutelySummable› ‹Ψ.IsAbsolutelySummable›
  rw [hamiltonian_eq_tsum, hamiltonian_eq_tsum, hamiltonian_eq_tsum, hamiltonianTerms_sub_eq]
  simp only [Pi.sub_apply]
  exact (summable_hamiltonianTerms (Φ := Φ) Λ η).tsum_sub
    (summable_hamiltonianTerms (Φ := Ψ) Λ η)

/-- **Georgii (2.14) for a difference**: `|H_Λ^Φ − H_Λ^Ψ| ≤ ∑_{i ∈ Λ} ‖Φ − Ψ‖ᵢ`. -/
theorem abs_hamiltonian_sub_le (Φ Ψ : Potential S E)
    [Φ.IsAbsolutelySummable] [Ψ.IsAbsolutelySummable] (Λ : Finset S) (η : S → E) :
    |Φ.hamiltonian Λ η - Ψ.hamiltonian Λ η| ≤ (Φ - Ψ).hamiltonianBound Λ := by
  have : (Φ - Ψ).IsAbsolutelySummable :=
    IsAbsolutelySummable.sub ‹Φ.IsAbsolutelySummable› ‹Ψ.IsAbsolutelySummable›
  rw [← hamiltonian_sub Φ Ψ Λ η]
  exact abs_hamiltonian_le Λ η

/-- Coercion form of `abs_hamiltonian_sub_le`, for elements of the submodule. -/
theorem abs_hamiltonian_sub_le' (Φ Ψ : absolutelySummable S E) (Λ : Finset S) (η : S → E) :
    |(Φ : Potential S E).hamiltonian Λ η - (Ψ : Potential S E).hamiltonian Λ η|
      ≤ ((Φ - Ψ : absolutelySummable S E) : Potential S E).hamiltonianBound Λ := by
  have h := abs_hamiltonian_sub_le (Φ : Potential S E) (Ψ : Potential S E) Λ η
  rwa [← Submodule.coe_sub] at h

/-- On the submodule, `hamiltonianBound` is the finite sum of the seminorms. -/
lemma hamiltonianBound_coe (Φ : absolutelySummable S E) (Λ : Finset S) :
    (Φ : Potential S E).hamiltonianBound Λ = ∑ i ∈ Λ, seminormAt S E i Φ := by
  rw [hamiltonianBound,
    ENNReal.toReal_sum fun i _ ↦ IsAbsolutelySummable.normAt_ne_top (Φ := (Φ : Potential S E)) i]
  simp

/-- **The bridge to Georgii (4.19).**  Along a net converging in `ℬ`, the uniform Hamiltonian
bounds `D x Λ := hamiltonianBound (Φₓ − Φ) Λ` of the difference potentials tend to `0` for
every volume `Λ`. -/
theorem tendsto_hamiltonianBound_sub {ι : Type*} {l : Filter ι}
    {Φs : ι → absolutelySummable S E} {Φ : absolutelySummable S E}
    (h : Tendsto Φs l (𝓝 Φ)) (Λ : Finset S) :
    Tendsto (fun x ↦ ((Φs x - Φ : absolutelySummable S E) : Potential S E).hamiltonianBound Λ)
      l (𝓝 0) := by
  have h' := tendsto_iff_tendsto_seminormAt.1 h
  have heq : ∀ x, ((Φs x - Φ : absolutelySummable S E) : Potential S E).hamiltonianBound Λ
      = ∑ i ∈ Λ, seminormAt S E i (Φs x - Φ) := fun x ↦ hamiltonianBound_coe _ Λ
  rw [funext heq]
  have hsum := tendsto_finsetSum Λ (f := fun i x ↦ seminormAt S E i (Φs x - Φ))
    (a := fun _ ↦ (0 : ℝ)) fun i _ ↦ h' i
  simpa using hsum

/-! ### (B3 prelude) Georgii's `ℬ` proper: measurable absolutely summable potentials

Georgii's Definition (2.2)(i) makes measurability of the interaction terms part of the notion
of a potential, so the domain of the Gibbs correspondence `𝒢` of (4.23) is the set of elements
of `absolutelySummable S E` satisfying `Potential.IsPotential`.  (Measurability cannot be
carried along limits of the seminorm topology — the `∅`-indexed term is invisible to every
`‖·‖ᵢ` — so it is part of the ambient space, with the subspace topology, exactly as in
Georgii, where all elements of `ℬ` are potentials by definition.) -/

variable (S E) in
/-- **Georgii's space `ℬ` of (2.11)**: absolutely summable potentials with measurable
interaction terms, topologized as a subspace of the seminormed module
`absolutelySummable S E`. -/
def BSpace : Type _ :=
  {Φ : absolutelySummable S E // IsPotential (Φ : Potential S E)}

namespace BSpace

instance : TopologicalSpace (BSpace S E) :=
  inferInstanceAs (TopologicalSpace
    {Φ : absolutelySummable S E // IsPotential (Φ : Potential S E)})

noncomputable instance : UniformSpace (BSpace S E) :=
  inferInstanceAs (UniformSpace
    ↥{Φ : absolutelySummable S E | IsPotential (Φ : Potential S E)})

/-- Georgii's `ℬ` is complete: a closed subspace of the Fréchet space of absolutely summable
potentials. -/
instance [Countable S] : CompleteSpace (BSpace S E) :=
  (isClosed_setOf_isPotential (S := S) (E := E)).completeSpace_coe

instance [Countable S] : TopologicalSpace.MetrizableSpace (BSpace S E) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace
    ↥{Φ : absolutelySummable S E | IsPotential (Φ : Potential S E)})


/-- The underlying interaction potential. -/
def toPotential (Φ : BSpace S E) : Potential S E := (Φ.1 : Potential S E)

instance (Φ : BSpace S E) : IsPotential Φ.toPotential := Φ.2

instance (Φ : BSpace S E) : IsAbsolutelySummable Φ.toPotential := Φ.1.2.1

lemma continuous_val : Continuous (fun Φ : BSpace S E ↦ Φ.1) := continuous_subtype_val

variable [Countable S] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- The Gibbsian specification of an element of `ℬ` (Georgii Definition (2.9)); total on
`BSpace S E`. -/
def gibbsSpecification (Φ : BSpace S E) : Specification S E :=
  gibbsSpecificationOfAbsolutelySummable (Φ := Φ.toPotential) ν β

lemma isQuasilocal_gibbsSpecification (Φ : BSpace S E) :
    (Φ.gibbsSpecification ν β).IsQuasilocal :=
  isQuasilocal_gibbsSpecificationOfAbsolutelySummable ν β

/-- Georgii (4.14)(1) for elements of `ℬ`: the kernels are dominated by
`e^{2|β| ‖Φ‖_Λ} ν^S` on `𝓕_Λ`-events. -/
lemma gibbsSpecification_apply_le (Φ : BSpace S E) (Λ : Finset S) (η : S → E)
    {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    Φ.gibbsSpecification ν β Λ η A ≤
      ENNReal.ofReal (Real.exp (2 * |β| * Φ.toPotential.hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A :=
  gibbsSpecificationOfAbsolutelySummable_apply_le (Φ := Φ.toPotential) ν β Λ η hA

/-- **Georgii Proposition (4.19) on `ℬ`.**  Along a net of potentials converging in `ℬ`, the
Gibbsian specifications converge uniformly on every volume and every bounded measurable
observable — verbatim the `hunif` hypothesis of Georgii (4.17)/(4.22). -/
theorem tendsto_dist_action_gibbsSpecification {ι : Type*} {l : Filter ι}
    {Φs : ι → BSpace S E} {Φ : BSpace S E} (h : Tendsto Φs l (𝓝 Φ)) (Λ : Finset S)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable ⇑f) :
    Tendsto (fun x ↦ dist (((Φs x).gibbsSpecification ν β).action Λ f)
      ((Φ.gibbsSpecification ν β).action Λ f)) l (𝓝 0) := by
  have hcoe : Tendsto (fun x ↦ (Φs x).1) l (𝓝 Φ.1) :=
    (continuous_val.tendsto Φ).comp h
  exact Potential.tendsto_dist_action_gibbsSpecification ν β
    (Φs := fun x ↦ (Φs x).toPotential) (Φ := Φ.toPotential)
    (D := fun x Λ ↦ (((Φs x).1 - Φ.1 : absolutelySummable S E) :
      Potential S E).hamiltonianBound Λ)
    (fun x Λ' η ↦ abs_hamiltonian_sub_le' ((Φs x).1) Φ.1 Λ' η)
    (fun Λ' ↦ tendsto_hamiltonianBound_sub hcoe Λ') Λ hf

/-! ### (B3) Georgii Theorem (4.23)(c): the graph of the Gibbs correspondence is closed -/

/-- **Georgii Theorem (4.23)(c).**  The graph `{(Φ, μ) : Φ ∈ ℬ, μ ∈ 𝒢(Φ)}` of the Gibbs
correspondence is closed in `ℬ × 𝒫(Ω, 𝓕)` (with the topology of local convergence on the
second factor).  As in Georgii, no standard Borel hypothesis on `E` is needed.

The proof is the product-net architecture of `isClosed_setOf_mem_GP`, with *varying*
specifications: along the directed set `D̄ = D × 𝒮`, the potentials converge in `ℬ`, so by
(4.19) the specifications `γ^{Φᵅ}` converge uniformly to `γ^Φ`, and Georgii (4.17)
(`mem_GP_of_tendsto_withLocalConvergence`) identifies the limit as a Gibbs measure for `Φ`. -/
theorem isClosed_graph_GP :
    IsClosed {p : BSpace S E × WithLocalConvergence S E |
      p.2.toMeasure ∈ GP (S := S) (E := E) (p.1.gibbsSpecification ν β)} := by
  rw [isClosed_iff_clusterPt]
  intro q hq
  set G := {p : BSpace S E × WithLocalConvergence S E |
    p.2.toMeasure ∈ GP (S := S) (E := E) (p.1.gibbsSpecification ν β)} with hG
  have hne : NeBot (𝓝 q ⊓ 𝓟 G) := hq
  have : NeBot ((𝓝 q ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) :=
    Filter.prod_neBot.2 ⟨hne, inferInstance⟩
  show q.2.toMeasure ∈ GP (S := S) (E := E) (q.1.gibbsSpecification ν β)
  refine mem_GP_of_tendsto_withLocalConvergence
    (l := (𝓝 q ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S)))
    (BSpace.isQuasilocal_gibbsSpecification ν β q.1)
    (γs := fun r ↦ r.1.1.gibbsSpecification ν β) (Λs := Prod.snd)
    (νs := fun r ↦ (r.1.2).toMeasure) tendsto_snd ?_ ?_
  · -- (4.19): uniform convergence of the varying specifications
    intro Λ f hf
    have hfst : Tendsto (fun r : (BSpace S E × WithLocalConvergence S E) × Finset S ↦ r.1.1)
        ((𝓝 q ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) (𝓝 q.1) :=
      (continuous_fst.tendsto q).comp (tendsto_fst.mono_right inf_le_left)
    exact BSpace.tendsto_dist_action_gibbsSpecification ν β hfst Λ
      (measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hf))
  · -- the finite-volume Gibbs distributions converge locally to `q.2`
    have hev : ∀ᶠ r : (BSpace S E × WithLocalConvergence S E) × Finset S in
        (𝓝 q ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S)),
        (WithSetwiseTopology.ofMeasure
          ((r.1.1.gibbsSpecification ν β).bindPM r.2 (r.1.2).toMeasure) :
            WithLocalConvergence S E) = r.1.2 := by
      have h1 : ∀ᶠ p in 𝓝 q ⊓ 𝓟 G, p ∈ G :=
        (inf_le_right : 𝓝 q ⊓ 𝓟 G ≤ 𝓟 G) (Filter.mem_principal_self G)
      filter_upwards [h1.prod_inl (atTop : Filter (Finset S))] with r hr
      rw [(mem_GP_iff_forall_bindPM_eq (γ := r.1.1.gibbsSpecification ν β)
        (r.1.2).toMeasure).1 hr r.2]
    have hsnd : Tendsto (fun r : (BSpace S E × WithLocalConvergence S E) × Finset S ↦ r.1.2)
        ((𝓝 q ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) (𝓝 q.2) :=
      (continuous_snd.tendsto q).comp (tendsto_fst.mono_right inf_le_left)
    exact hsnd.congr' (hev.mono fun r hr ↦ hr.symm)

/-! ### (B4) Georgii Theorem (4.23)(d): the Gibbs correspondence is upper semicontinuous -/

/-- **Georgii Theorem (4.23)(d).**  Over a standard Borel state space the Gibbs correspondence
`𝒢` is upper semicontinuous: for every closed `F ⊆ 𝒫(Ω, 𝓕)` (topology of local convergence)
the set `𝒢⁻¹(F) = {Φ ∈ ℬ : 𝒢(Φ) ∩ F ≠ ∅}` is closed in `ℬ`.

Net proof, avoiding Georgii's metrizability reduction (4.15): for a filter on `𝒢⁻¹(F)`
clustering at `Φ`, choose witnesses `μ_Ψ ∈ 𝒢(Ψ) ∩ F`; eventual seminorm boundedness along the
filter (`‖Ψ‖ᵢ ≤ ‖Φ‖ᵢ + 1` for `i ∈ Λ`) dominates the witnesses by the finite measures
`e^{2|β|(‖Φ‖_Λ + |Λ|)} ν^S` (Georgii (4.14)(1)), so they are locally equicontinuous; by
Georgii (4.9) they converge along an ultrafilter to some `μ`, which lies in `F` (closed) and,
by the closed graph (c), in `𝒢(Φ)`. -/
theorem isClosed_setOf_exists_mem_GP [StandardBorelSpace E]
    {F : Set (WithLocalConvergence S E)} (hF : IsClosed F) :
    IsClosed {Φ : BSpace S E | ∃ μ ∈ F,
      μ.toMeasure ∈ GP (S := S) (E := E) (Φ.gibbsSpecification ν β)} := by
  rw [isClosed_iff_clusterPt]
  intro Φ hΦ
  set A := {Φ : BSpace S E | ∃ μ ∈ F,
    μ.toMeasure ∈ GP (S := S) (E := E) (Φ.gibbsSpecification ν β)} with hA
  have hne : NeBot (𝓝 Φ ⊓ 𝓟 A) := hΦ
  set l : Filter (BSpace S E) := 𝓝 Φ ⊓ 𝓟 A with hl
  have : Nonempty (WithLocalConvergence S E) :=
    ⟨WithSetwiseTopology.ofMeasure ⟨Measure.infinitePi (fun _ : S ↦ ν), inferInstance⟩⟩
  -- choose witnesses `μ_Ψ ∈ 𝒢(Ψ) ∩ F` (total function, junk off `A`)
  have hwit : ∀ Ψ : BSpace S E, ∃ μ : WithLocalConvergence S E,
      Ψ ∈ A → μ ∈ F ∧ μ.toMeasure ∈ GP (S := S) (E := E) (Ψ.gibbsSpecification ν β) := by
    intro Ψ
    by_cases h : Ψ ∈ A
    · obtain ⟨μ, hμF, hμGP⟩ := h
      exact ⟨μ, fun _ ↦ ⟨hμF, hμGP⟩⟩
    · exact ⟨Classical.arbitrary _, fun h' ↦ absurd h' h⟩
  choose w hw using hwit
  have hevA : ∀ᶠ Ψ in l, Ψ ∈ A := (inf_le_right : l ≤ 𝓟 A) (mem_principal_self A)
  have hid : Tendsto (fun Ψ : BSpace S E ↦ Ψ) l (𝓝 Φ) := tendsto_id'.2 inf_le_left
  have hval : Tendsto (fun Ψ : BSpace S E ↦ Ψ.1) l (𝓝 Φ.1) :=
    (BSpace.continuous_val.tendsto Φ).comp hid
  have hsem := tendsto_iff_tendsto_seminormAt.1 hval
  -- eventual seminorm boundedness: `‖Ψ‖_Λ ≤ ‖Φ‖_Λ + |Λ|` eventually along `l`
  have hboundEv : ∀ Λ : Finset S, ∀ᶠ Ψ in l,
      (BSpace.toPotential Ψ).hamiltonianBound Λ
        ≤ (BSpace.toPotential Φ).hamiltonianBound Λ + Λ.card := by
    intro Λ
    have h1 : ∀ᶠ Ψ in l, ∀ i ∈ Λ, seminormAt S E i (Ψ.1 - Φ.1) < 1 :=
      Λ.eventually_all.2 fun i _ ↦ (hsem i).eventually_lt_const one_pos
    filter_upwards [h1] with Ψ hΨ
    have hcalc : ∀ i ∈ Λ, seminormAt S E i Ψ.1 ≤ seminormAt S E i Φ.1 + 1 := by
      intro i hi
      have htri := map_add_le_add (seminormAt S E i) (Ψ.1 - Φ.1) Φ.1
      rw [sub_add_cancel] at htri
      have := (hΨ i hi).le
      linarith
    rw [show (BSpace.toPotential Ψ).hamiltonianBound Λ
        = ∑ i ∈ Λ, seminormAt S E i Ψ.1 from hamiltonianBound_coe Ψ.1 Λ,
      show (BSpace.toPotential Φ).hamiltonianBound Λ
        = ∑ i ∈ Λ, seminormAt S E i Φ.1 from hamiltonianBound_coe Φ.1 Λ]
    calc ∑ i ∈ Λ, seminormAt S E i Ψ.1
        ≤ ∑ i ∈ Λ, (seminormAt S E i Φ.1 + 1) := Finset.sum_le_sum hcalc
      _ = ∑ i ∈ Λ, seminormAt S E i Φ.1 + Λ.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the dominating measures `e^{2|β|(‖Φ‖_Λ + |Λ|)} ν^S` (Georgii (4.14)(1))
  set νdom : Finset S → Measure (S → E) := fun Λ ↦
    ENNReal.ofReal (Real.exp (2 * |β| *
      ((BSpace.toPotential Φ).hamiltonianBound Λ + Λ.card))) •
      Measure.infinitePi (fun _ : S ↦ ν) with hνdom
  have : ∀ Λ, IsFiniteMeasure (νdom Λ) := fun Λ ↦ ⟨by
    rw [hνdom, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top⟩
  -- local equicontinuity of the witnesses
  have hle : LocallyEquicontinuous l (fun Ψ ↦ (w Ψ).toMeasure) := by
    refine locallyEquicontinuous_of_eventually_le νdom fun Λ ↦ ?_
    filter_upwards [hevA, hboundEv Λ] with Ψ hΨA hΨb
    intro A' hA'
    refine apply_le_of_mem_GP (hw Ψ hΨA).2 Λ
      (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA') fun ω ↦ ?_
    calc (Ψ.gibbsSpecification ν β) Λ ω A'
        ≤ ENNReal.ofReal
            (Real.exp (2 * |β| * (BSpace.toPotential Ψ).hamiltonianBound Λ)) *
          Measure.infinitePi (fun _ : S ↦ ν) A' :=
        BSpace.gibbsSpecification_apply_le ν β Ψ Λ ω hA'
      _ ≤ νdom Λ A' := by
        rw [hνdom]
        simp only [Measure.smul_apply, smul_eq_mul]
        gcongr
  -- (4.9): the witnesses converge along an ultrafilter
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le l
  obtain ⟨μlim, hμlim⟩ := exists_tendsto_of_locallyEquicontinuous U hU hle
  have hevAU : ∀ᶠ Ψ in (U : Filter (BSpace S E)), Ψ ∈ A := hU hevA
  have hμlimF : μlim ∈ F := hF.mem_of_tendsto hμlim (hevAU.mono fun Ψ h ↦ (hw Ψ h).1)
  -- the pair `(Φ, μlim)` lies in the closed graph (c)
  have hpair : Tendsto (fun Ψ ↦ (Ψ, w Ψ)) (U : Filter (BSpace S E)) (𝓝 (Φ, μlim)) :=
    (hid.mono_left hU).prodMk_nhds hμlim
  have hgraph : (Φ, μlim) ∈ {p : BSpace S E × WithLocalConvergence S E |
      p.2.toMeasure ∈ GP (S := S) (E := E) (p.1.gibbsSpecification ν β)} :=
    (isClosed_graph_GP ν β).mem_of_tendsto hpair (hevAU.mono fun Ψ h ↦ (hw Ψ h).2)
  exact ⟨μlim, hμlimF, hgraph⟩

end BSpace

end Potential

end
