/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification

/-!
# Chains of two-site events under a Gibbs measure

Let `A i j ⊆ E^S` be an event depending only on the spins at the two sites `i` and `j`.  Along a
list of **distinct** sites `i^{(0)}, …, i^{(ℓ)}` the events `A i^{(k)} i^{(k+1)}` can be estimated
one at a time: conditioning on the spins outside `i^{(0)}` leaves all the later events untouched,
so a uniform bound `γ_{\{i\}}(A i j | η) ≤ r` on the single-site conditional probabilities gives

`μ(⋂_{k < ℓ} A i^{(k)} i^{(k+1)}) ≤ r^ℓ`

for every Gibbs measure `μ` of the specification.  This is the estimate behind Georgii's
high-temperature arguments — Example (18.19), and the classical Peierls/self-avoiding-path
counting generally.

* `Specification.apply_le_of_inter_subset`: a specification kernel does not move the spins
  outside `Λ`, so `γ_Λ(A|η) ≤ γ_Λ(A'|η)` as soon as `A` and `A'` agree on the configurations that
  coincide with `η` off `Λ`.  This is what turns Georgii's `σ_i · σ_j ≥ 1 - ε` into the
  single-site event `σ_i · ω_j ≥ 1 - ε`.
* `Specification.chainEvent`: the intersection `⋂_k A i^{(k)} i^{(k+1)}` along a list of sites,
  with `Specification.measurableSet_chainEvent` and
  `Specification.measurableSet_chainEvent_cylinderEvents` (it is an exterior event for any set of
  sites disjoint from the list) and `Specification.mem_chainEvent_of_isChain` (a criterion for a
  configuration to belong to it, used to feed a self-avoiding path into the estimate).
* `Specification.measure_chainEvent_le`: the estimate above.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

/-! ### The carrier of a specification kernel -/

/-- **A specification kernel does not move the spins outside `Λ`.**  If `A` is contained in `A'`
after intersecting with the configurations that agree with `η` at some site `j ∉ Λ`, then
`γ_Λ(A|η) ≤ γ_Λ(A'|η)`: properness gives `γ_Λ(A ∩ {σ_j = η_j}|η) = γ_Λ(A|η)`, because
`{σ_j = η_j}` is an exterior event containing `η`. -/
lemma apply_le_of_inter_subset [Countable S] [MeasurableSingletonClass E]
    (γ : Specification S E) (Λ : Finset S) (η : S → E) {j : S} (hj : j ∉ Λ)
    {A A' : Set (S → E)} (hA : MeasurableSet A) (h : A ∩ {σ : S → E | σ j = η j} ⊆ A') :
    γ Λ η A ≤ γ Λ η A' := by
  have hB : MeasurableSet[cylinderEvents ((Λ : Finset S) : Set S)ᶜ] {σ : S → E | σ j = η j} :=
    measurable_coordinate_projection_2 (Δ := ((Λ : Finset S) : Set S)ᶜ) (by simpa using hj)
      (measurableSet_singleton (η j))
  have hproper := (isProper_iff_inter_eq_indicator_mul (γ := γ)).1 γ.isProper Λ hA hB η
  calc γ Λ η A = γ Λ η (A ∩ {σ : S → E | σ j = η j}) := by
        rw [hproper, Set.indicator_of_mem (by simp), Pi.one_apply, one_mul]
    _ ≤ γ Λ η A' := measure_mono h

/-! ### Chains of two-site events -/

variable (A : S → S → Set (S → E))

/-- The chain of two-site events along a list of sites, read from the head:
`chainEvent A [i₀, i₁, …, i_ℓ] = A i₀ i₁ ∩ A i₁ i₂ ∩ ⋯ ∩ A i_{ℓ-1} i_ℓ`.  A list of at most one
site imposes no condition. -/
def chainEvent : List S → Set (S → E)
  | [] => Set.univ
  | [_] => Set.univ
  | x :: y :: l => A x y ∩ chainEvent (y :: l)

omit [MeasurableSpace E] in
@[simp] lemma chainEvent_nil : chainEvent A ([] : List S) = Set.univ := rfl

omit [MeasurableSpace E] in
@[simp] lemma chainEvent_singleton (x : S) : chainEvent A [x] = Set.univ := rfl

omit [MeasurableSpace E] in
@[simp] lemma chainEvent_cons_cons (x y : S) (l : List S) :
    chainEvent A (x :: y :: l) = A x y ∩ chainEvent A (y :: l) := rfl

variable {A}

/-- A chain of events reading only the sites of `l` is an exterior event for any set of sites
disjoint from `l`. -/
lemma measurableSet_chainEvent_cylinderEvents
    (hA : ∀ x y, MeasurableSet[cylinderEvents ({x, y} : Set S)] (A x y)) {s : Set S} :
    ∀ {l : List S}, (∀ z ∈ l, z ∉ s) → MeasurableSet[cylinderEvents sᶜ] (chainEvent A l)
  | [], _ => by simp
  | [_], _ => by simp
  | y :: z :: l, hx => by
      rw [chainEvent_cons_cons]
      refine MeasurableSet.inter ?_ (measurableSet_chainEvent_cylinderEvents hA
        fun w hw ↦ hx w (by simp [hw]))
      refine (cylinderEvents_mono ?_) _ (hA y z)
      rintro w (rfl | rfl)
      · exact hx w (by simp)
      · exact hx w (by simp)

lemma measurableSet_chainEvent
    (hA : ∀ x y, MeasurableSet[cylinderEvents ({x, y} : Set S)] (A x y)) :
    ∀ l : List S, MeasurableSet (chainEvent A l)
  | [] => MeasurableSet.univ
  | [_] => MeasurableSet.univ
  | x :: y :: l => (cylinderEvents_le_pi _ (hA x y)).inter (measurableSet_chainEvent hA (y :: l))

omit [MeasurableSpace E] in
/-- A configuration lies in the chain of events along `l` as soon as consecutive sites of `l` are
related by `R`, all sites of `l` satisfy `P`, and every `R`-related pair of `P`-sites carries the
event. -/
lemma mem_chainEvent_of_isChain {ω : S → E} {R : S → S → Prop} {P : S → Prop}
    (h : ∀ x y, R x y → P x → P y → ω ∈ A x y) :
    ∀ {l : List S}, l.IsChain R → (∀ z ∈ l, P z) → ω ∈ chainEvent A l
  | [], _, _ => Set.mem_univ _
  | [_], _, _ => Set.mem_univ _
  | x :: y :: l, hchain, hP => by
      rw [List.isChain_cons_cons] at hchain
      exact ⟨h x y hchain.1 (hP x (by simp)) (hP y (by simp)),
        mem_chainEvent_of_isChain h hchain.2 fun z hz ↦ hP z (by simp [hz])⟩

/-- **The chain estimate.**  If every single-site conditional probability of a two-site event is
at most `r` for distinct sites, a Gibbs measure gives the chain of these events along `ℓ + 1`
distinct sites
probability at most `r^ℓ`.  Each step conditions on the spins outside the head of the list; the
head does not occur again, so the remaining events are exterior and factor out by properness. -/
theorem measure_chainEvent_le [Countable S] {γ : Specification S E} {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ)
    (hA : ∀ x y, MeasurableSet[cylinderEvents ({x, y} : Set S)] (A x y))
    {r : ℝ≥0∞} (hr : ∀ (x y : S), x ≠ y → ∀ η : S → E, γ {x} η (A x y) ≤ r) :
    ∀ l : List S, l.Nodup → μ (chainEvent A l) ≤ r ^ (l.length - 1) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
    match t, ih with
    | [], _ => intro _; simp
    | y :: t, ih =>
      intro hnd
      have hx : x ∉ y :: t := (List.nodup_cons.1 hnd).1
      have hC : MeasurableSet[cylinderEvents ((({x} : Finset S) : Set S))ᶜ]
          (chainEvent A (y :: t)) :=
        measurableSet_chainEvent_cylinderEvents hA fun z hz hzs ↦
          hx (Finset.mem_singleton.1 (Finset.mem_coe.1 hzs) ▸ hz)
      have hCm : MeasurableSet (chainEvent A (y :: t)) := measurableSet_chainEvent hA _
      have hAm : MeasurableSet (A x y) := cylinderEvents_le_pi _ (hA x y)
      have hbind := (isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) ({x} : Finset S)
      have hae : AEMeasurable (fun η ↦ γ ({x} : Finset S) η) μ :=
        (((γ ({x} : Finset S)).measurable.mono cylinderEvents_le_pi le_rfl)).aemeasurable
      have hstep : μ (chainEvent A (x :: y :: t)) ≤ r * μ (chainEvent A (y :: t)) := by
        rw [chainEvent_cons_cons]
        calc μ (A x y ∩ chainEvent A (y :: t))
            = ∫⁻ η, γ ({x} : Finset S) η (A x y ∩ chainEvent A (y :: t)) ∂μ := by
              conv_lhs => rw [← hbind]
              exact Measure.bind_apply (hAm.inter hCm) hae
          _ = ∫⁻ η, (chainEvent A (y :: t)).indicator 1 η * γ ({x} : Finset S) η (A x y) ∂μ := by
              refine lintegral_congr fun η ↦ ?_
              exact (isProper_iff_inter_eq_indicator_mul (γ := γ)).1 γ.isProper _ hAm hC η
          _ ≤ ∫⁻ η, (chainEvent A (y :: t)).indicator (fun _ ↦ r) η ∂μ := by
              refine lintegral_mono fun η ↦ ?_
              by_cases hη : η ∈ chainEvent A (y :: t)
              · rw [Set.indicator_of_mem hη, Set.indicator_of_mem hη, Pi.one_apply, one_mul]
                exact hr x y (fun hxy ↦ hx (by simp [hxy])) η
              · rw [Set.indicator_of_notMem hη, Set.indicator_of_notMem hη, zero_mul]
          _ = r * μ (chainEvent A (y :: t)) := lintegral_indicator_const hCm r
      have hih : μ (chainEvent A (y :: t)) ≤ r ^ t.length := by
        simpa using ih (List.nodup_cons.1 hnd).2
      refine hstep.trans ?_
      calc r * μ (chainEvent A (y :: t)) ≤ r * r ^ t.length := by gcongr
        _ = r ^ ((x :: y :: t).length - 1) := by
            simp only [List.length_cons]
            rw [Nat.add_sub_cancel, ← pow_succ']

end Specification
