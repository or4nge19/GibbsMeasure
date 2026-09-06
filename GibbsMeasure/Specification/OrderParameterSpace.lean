/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.OrderParameters

/-!
# The two descriptions of `ℬ_Θ(f₁, …, f_N)` (Georgii §16.3)

Before Theorem (16.21) Georgii fixes a cube `Λ₀` with `f₁, …, f_N ∈ 𝓛_{Λ₀}`, puts
`Λ_i = Λ₀ ∪ (Λ₀ − i)` for `i ≠ 0`, and defines `ℬ_Θ(f₁, …, f_N) ⊆ ℬ_Θ` by three conditions on the
interaction terms:

* (i) `Φ_{Λ₀}` is a linear combination of `f₁, …, f_N`;
* (ii) for each `i ≠ 0`, `Φ_{Λ_i}` is a linear combination of the `f_m (f_n ∘ θ_i)`;
* (iii) `Φ_A = 0` if `A` is not a translate of some `Λ_i`.

He then remarks: "It is easily seen that `ℬ_Θ(f₁, …, f_N)` is closed relative to `‖·‖₀`. More
precisely, `ℬ_Θ(f₁, …, f_N)` is the closed linear span of the potentials `Φ^{(Λ₀, f_n)}` and
`Φ^{(Λ_i, f_m f_n ∘ θ_i)}`." The closed-span description is the definition
`MeasureTheory.GibbsMeasure.BThetaOrder` used in
`GibbsMeasure/Specification/OrderParameters.lean`; this file supplies the conditions description
and proves that the two agree.

## Main definitions

* `MeasureTheory.GibbsMeasure.orderVolumes Λ₀ I`: the volumes that may carry an interaction term,
  namely the translates of `Λ₀ = Λ_0` and of the `Λ_i`, `i ∈ I`. Georgii's condition (iii) is the
  vanishing of `Φ_A` off this family.
* `MeasureTheory.GibbsMeasure.BThetaOrderCond Λ₀ f I`: **Georgii's conditions (i)–(iii)** as a
  submodule of `ℬ_Θ`. Georgii's space is `I = S ∖ {0}`; the parameter `I` also covers his
  `ℬ^R_Θ(f₁, …, f_N)` of Comment (16.24)(1) and his `ℬ^I_Θ(f)` of Theorem (16.30).
* `Potential.restrictVolumes T Φ`: the truncation of a potential to a family `T` of volumes, the
  rounding-free version of `Potential.BTheta.approx`. Its natural home is next to that definition
  in `GibbsMeasure/Specification/TangentFunctional.lean`.

## Main results

* `MeasureTheory.GibbsMeasure.BThetaOrderCond_eq_BThetaOrder` and
  `MeasureTheory.GibbsMeasure.mem_BThetaOrder_iff`: **the identification of the two descriptions**
  and the resulting membership criterion for `ℬ_Θ(f₁, …, f_N)`. The hypotheses are that `Λ₀` is
  nonempty, that `f₁, …, f_N ∈ 𝓛_{Λ₀}`, and that `0 ∉ I` (Georgii's `i ≠ 0`: on `Λ_0 = Λ₀` it is
  condition (i), not condition (ii), that applies).
* `MeasureTheory.GibbsMeasure.isClosed_BThetaOrderCond`: Georgii's "`ℬ_Θ(f₁, …, f_N)` is closed
  relative to `‖·‖₀`". Norm convergence in `ℬ_Θ` forces convergence of each interaction term
  (`MeasureTheory.GibbsMeasure.continuous_coe_volume`), conditions (i) and (ii) confine two of
  them to finite-dimensional, hence closed, spaces of observables, and (iii) is a closed
  condition.
* `MeasureTheory.GibbsMeasure.eq_or_eq_neg_of_translate_pairVolume`: Georgii's "clearly, if
  `i ≠ ±j` then `Λ_i` and `Λ_j` are not a translate of each other". The proof compares the extent
  of `Λ_i` along an integral linear functional `φ`, which is the extent of `Λ₀` plus `|φ i|`, and
  uses that `ℤ^d` is not the union of the two proper subgroups `(i − j)^⊥` and `(i + j)^⊥`.
* `MeasureTheory.GibbsMeasure.exists_mem_BThetaOrder_coe_eq_restrictVolumes`: the truncation of a
  potential satisfying (i)–(iii) to finitely many volume classes is a finite linear combination of
  the generating potentials, and `MeasureTheory.GibbsMeasure.normAt_sub_restrictVolumes_le` bounds
  the truncation error by a tail of the convergent series `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖`.

## Deviations from Georgii

* Georgii takes `Λ₀` to be a *cube*. Nothing here needs that: `Λ_i` and `Λ_j` are translates only
  for `j = ±i` whenever `Λ₀` is a nonempty finite volume.
* Condition (ii) is stated as membership of the *span* of the observables `f_m (f_n ∘ θ_i)`, which
  is what "is a linear combination of" means; likewise for (i).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

open Potential

/-! ### Extents of finite volumes along additive functionals -/

section Extent

variable {S : Type*} [AddCommGroup S]

/-- The supremum of an additive functional over a translate of a finite volume. -/
lemma sup'_translate {φ : S → ℤ} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    {A : Finset S} (hA : A.Nonempty) (g : S) :
    (translate A g).sup' (translate_nonempty.2 hA) φ = A.sup' hA φ + φ g := by
  have h1 : (translate A g).sup' (translate_nonempty.2 hA) φ = A.sup' hA fun x ↦ φ x + φ g := by
    rw [Finset.sup'_map]
    exact Finset.sup'_congr _ rfl fun x _ ↦ hφ x g
  rw [h1, ← Finset.sup'_add]

/-- The infimum of an additive functional over a translate of a finite volume. -/
lemma inf'_translate {φ : S → ℤ} (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    {A : Finset S} (hA : A.Nonempty) (g : S) :
    (translate A g).inf' (translate_nonempty.2 hA) φ = A.inf' hA φ + φ g := by
  have h1 : (translate A g).inf' (translate_nonempty.2 hA) φ = A.inf' hA fun x ↦ φ x + φ g := by
    rw [Finset.inf'_map]
    exact Finset.inf'_congr _ rfl fun x _ ↦ hφ x g
  have h2 : A.inf' hA φ + φ g = A.inf' hA fun x ↦ φ x + φ g := by
    have h := map_finset_inf' (OrderIso.addRight (φ g)) hA φ
    simp only [OrderIso.addRight_apply, Function.comp_def] at h
    exact h
  rw [h1, h2]


/-- **The extent of `A ∪ (A + t)`.** Along an additive functional `φ`, adjoining the translate
`A + t` to `A` increases the extent `sup φ − inf φ` by exactly `|φ t|`. -/
lemma sup'_sub_inf'_union_translate [DecidableEq S] {φ : S → ℤ}
    (hφ : ∀ x y, φ (x + y) = φ x + φ y) {A : Finset S} (hA : A.Nonempty) (t : S) :
    (A ∪ translate A t).sup' (hA.mono Finset.subset_union_left) φ
        - (A ∪ translate A t).inf' (hA.mono Finset.subset_union_left) φ
      = A.sup' hA φ - A.inf' hA φ + |φ t| := by
  have hAt : (translate A t).Nonempty := translate_nonempty.2 hA
  rw [Finset.sup'_union hA hAt, Finset.inf'_union hA hAt, sup'_translate hφ hA,
    inf'_translate hφ hA]
  set s := A.sup' hA φ
  set m := A.inf' hA φ
  rcases le_total 0 (φ t) with ht | ht
  · rw [sup_eq_right.2 (by omega), inf_eq_left.2 (by omega), abs_of_nonneg ht]
    omega
  · rw [sup_eq_left.2 (by omega), inf_eq_right.2 (by omega), abs_of_nonpos ht]
    omega

end Extent

/-! ### Georgii's volumes `Λ_i` are pairwise non-translates for `i ≠ ±j` -/

section PairVolume

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A vector of `ℤ^d` is determined up to sign by the absolute values of all its integral linear
functionals: `ℤ^d` is not the union of the two proper subgroups `(i − j)^⊥` and `(i + j)^⊥`. -/
lemma eq_or_eq_neg_of_forall_abs_inner_eq {i j : ι → ℤ}
    (h : ∀ c : ι → ℤ, |∑ l, c l * i l| = |∑ l, c l * j l|) : j = i ∨ j = -i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hnegne⟩ := hcon
  have hdicho : ∀ c : ι → ℤ, (∑ l, c l * (i l - j l)) = 0 ∨ (∑ l, c l * (i l + j l)) = 0 := by
    intro c
    have := abs_eq_abs.1 (h c)
    rcases this with hc | hc
    · left
      simp only [mul_sub, Finset.sum_sub_distrib, hc, sub_self]
    · right
      simp only [mul_add, Finset.sum_add_distrib, hc, neg_add_cancel]
  have hu : ∃ l₁ : ι, i l₁ - j l₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext fun l ↦ by linarith [hc l])
  have hv : ∃ l₂ : ι, i l₂ + j l₂ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hnegne (funext fun l ↦ by simpa using (by linarith [hc l] : j l = -i l))
  obtain ⟨l₁, hl₁⟩ := hu
  obtain ⟨l₂, hl₂⟩ := hv
  set c₁ : ι → ℤ := fun l ↦ if l = l₁ then 1 else 0 with hc₁
  set c₂ : ι → ℤ := fun l ↦ if l = l₂ then 1 else 0 with hc₂
  have hsum : ∀ (l₀ : ι) (x : ι → ℤ), (∑ l, (if l = l₀ then (1 : ℤ) else 0) * x l) = x l₀ := by
    intro l₀ x
    rw [Finset.sum_congr rfl fun l _ ↦ (by split <;> simp : (if l = l₀ then (1 : ℤ) else 0) * x l
      = if l = l₀ then x l else 0)]
    simp
  have h₁u : (∑ l, c₁ l * (i l - j l)) ≠ 0 := by rw [hc₁, hsum]; exact hl₁
  have h₂v : (∑ l, c₂ l * (i l + j l)) ≠ 0 := by rw [hc₂, hsum]; exact hl₂
  have h₁v : (∑ l, c₁ l * (i l + j l)) = 0 := (hdicho c₁).resolve_left h₁u
  have h₂u : (∑ l, c₂ l * (i l - j l)) = 0 := (hdicho c₂).resolve_right h₂v
  have hadd := hdicho (c₁ + c₂)
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, h₁v, h₂u, zero_add, add_zero] at hadd
  exact hadd.elim h₁u h₂v


omit [DecidableEq ι] in
/-- **Georgii, §16.3 before Theorem (16.21):** "if `i ≠ ±j` then `Λ_i` and `Λ_j` are not a
translate of each other". The extent of `Λ_i = Λ₀ ∪ (Λ₀ − i)` along a linear functional `φ` is the
extent of `Λ₀` plus `|φ i|`, and translating does not change it; so a translate of `Λ_i` can only
be `Λ_j` when `|φ i| = |φ j|` for every integral linear functional `φ`, hence when `j = ±i`.
Georgii states this for a cube `Λ₀`, but it holds for any nonempty finite volume. -/
lemma eq_or_eq_neg_of_translate_pairVolume {Λ₀ : Finset (ι → ℤ)} (hΛ₀ : Λ₀.Nonempty)
    {i j k : ι → ℤ} (h : translate (pairVolume Λ₀ i) k = pairVolume Λ₀ j) :
    j = i ∨ j = -i := by
  refine eq_or_eq_neg_of_forall_abs_inner_eq fun c ↦ ?_
  set φ : (ι → ℤ) → ℤ := fun x ↦ ∑ l, c l * x l with hφdef
  have hφ : ∀ x y, φ (x + y) = φ x + φ y := fun x y ↦ by
    simp [hφdef, mul_add, Finset.sum_add_distrib]
  have hφneg : ∀ x, φ (-x) = -φ x := fun x ↦ by simp [hφdef]
  have key : ∀ (a : ι → ℤ) (hne : (pairVolume Λ₀ a).Nonempty),
      (pairVolume Λ₀ a).sup' hne φ - (pairVolume Λ₀ a).inf' hne φ
        = Λ₀.sup' hΛ₀ φ - Λ₀.inf' hΛ₀ φ + |φ a| := by
    intro a hne
    have h0 : (pairVolume Λ₀ a).sup' hne φ - (pairVolume Λ₀ a).inf' hne φ
        = Λ₀.sup' hΛ₀ φ - Λ₀.inf' hΛ₀ φ + |φ (-a)| :=
      sup'_sub_inf'_union_translate hφ hΛ₀ (-a)
    rw [h0, hφneg, abs_neg]
  have hni := pairVolume_nonempty hΛ₀ i
  have hnj := pairVolume_nonempty hΛ₀ j
  have hs : (pairVolume Λ₀ j).sup' hnj φ = (pairVolume Λ₀ i).sup' hni φ + φ k := by
    rw [← sup'_translate hφ hni k]
    exact Finset.sup'_congr _ h.symm fun _ _ ↦ rfl
  have hm : (pairVolume Λ₀ j).inf' hnj φ = (pairVolume Λ₀ i).inf' hni φ + φ k := by
    rw [← inf'_translate hφ hni k]
    exact Finset.inf'_congr _ h.symm fun _ _ ↦ rfl
  have hi := key i hni
  have hj := key j hnj
  rw [hs, hm] at hj
  have habs : |φ i| = |φ j| := by linarith
  exact habs

omit [DecidableEq ι] in
/-- For `i ≠ 0` the volume `Λ_i = Λ₀ ∪ (Λ₀ − i)` is strictly larger than `Λ₀`, hence not a
translate of it. -/
lemma ne_zero_of_translate_pairVolume {Λ₀ : Finset (ι → ℤ)} (hΛ₀ : Λ₀.Nonempty) {i k : ι → ℤ}
    (h : translate (pairVolume Λ₀ i) k = Λ₀) : i = 0 := by
  have h0 : translate (pairVolume Λ₀ i) k = pairVolume Λ₀ 0 := by
    rw [h, pairVolume, neg_zero, translate_zero, Finset.union_self]
  rcases eq_or_eq_neg_of_translate_pairVolume hΛ₀ h0 with h1 | h1
  · exact h1.symm
  · simpa using h1.symm

end PairVolume


/-! ### Georgii's conditions (i)–(iii) on `ℬ_Θ(f₁, …, f_N)` -/

section Conditions

open Potential Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {N : ℕ}
  {Λ₀ : Finset (ι → ℤ)} {f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {I : Set (ι → ℤ)}

omit [DecidableEq ι] in
@[simp] lemma pairVolume_zero (Λ₀ : Finset (ι → ℤ)) : pairVolume Λ₀ 0 = Λ₀ := by
  rw [pairVolume, neg_zero, translate_zero, Finset.union_self]

variable (Λ₀ I) in
/-- The volumes that may carry an interaction term of a potential of `ℬ_Θ(f₁, …, f_N)`: the
translates of `Λ₀ = Λ_0` and of the `Λ_i = Λ₀ ∪ (Λ₀ − i)`, `i ∈ I`. Georgii's condition (iii)
is the vanishing of `Φ_A` off this family. -/
def orderVolumes : Set (Finset (ι → ℤ)) :=
  {A | ∃ i ∈ insert (0 : ι → ℤ) I, ∃ k : ι → ℤ, A = translate (pairVolume Λ₀ i) k}

omit [DecidableEq ι] in
lemma translate_mem_orderVolumes {A : Finset (ι → ℤ)} (hA : A ∈ orderVolumes Λ₀ I) (k : ι → ℤ) :
    translate A k ∈ orderVolumes Λ₀ I := by
  obtain ⟨i, hi, m, rfl⟩ := hA
  exact ⟨i, hi, m + k, translate_translate (pairVolume Λ₀ i) m k⟩

omit [DecidableEq ι] in
@[simp] lemma translate_mem_orderVolumes_iff {A : Finset (ι → ℤ)} {k : ι → ℤ} :
    translate A k ∈ orderVolumes Λ₀ I ↔ A ∈ orderVolumes Λ₀ I := by
  refine ⟨fun h ↦ ?_, fun h ↦ translate_mem_orderVolumes h k⟩
  have h' := translate_mem_orderVolumes h (-k)
  rwa [translate_translate, add_neg_cancel, translate_zero] at h'

omit [DecidableEq ι] in
lemma pairVolume_mem_orderVolumes {i : ι → ℤ} (hi : i ∈ insert (0 : ι → ℤ) I) :
    pairVolume Λ₀ i ∈ orderVolumes Λ₀ I := ⟨i, hi, 0, (translate_zero _).symm⟩

omit [DecidableEq ι] in
lemma self_mem_orderVolumes (Λ₀ : Finset (ι → ℤ)) (I : Set (ι → ℤ)) :
    Λ₀ ∈ orderVolumes Λ₀ I := by
  simpa using pairVolume_mem_orderVolumes (Λ₀ := Λ₀) (I := I) (i := 0) (Set.mem_insert _ _)

variable (Λ₀ f I) in
/-- **Georgii's space `ℬ_Θ(f₁, …, f_N)` by his conditions (i)–(iii)** (§16.3, before Theorem
(16.21)). A potential `Φ ∈ ℬ_Θ` belongs to it when

* (i) `Φ_{Λ₀}` is a linear combination of `f₁, …, f_N`;
* (ii) for each `i ∈ I`, `Φ_{Λ_i}` is a linear combination of the `f_m (f_n ∘ θ_i)`;
* (iii) `Φ_A = 0` whenever `A` is not a translate of `Λ₀` or of one of the `Λ_i`, `i ∈ I`.

Georgii takes `I = S ∖ {0}`; the parameter `I` also covers his `ℬ^R_Θ(f₁, …, f_N)` of Comment
(16.24)(1) and his `ℬ^I_Θ(f)` of Theorem (16.30). `BThetaOrderCond_eq_BThetaOrder` identifies
this space with the closed linear span `BThetaOrder Λ₀ f I` of the generating potentials, which
is Georgii's "more precise" description of the same space. -/
def BThetaOrderCond : Submodule ℝ (BTheta (ι → ℤ) E) where
  carrier := {Φ |
    (Φ : Potential (ι → ℤ) E) Λ₀ ∈ Submodule.span ℝ (Set.range fun n ↦ ⇑(f n)) ∧
    (∀ i ∈ I, (Φ : Potential (ι → ℤ) E) (pairVolume Λ₀ i) ∈
      Submodule.span ℝ (Set.range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p))) ∧
    ∀ A ∉ orderVolumes Λ₀ I, (Φ : Potential (ι → ℤ) E) A = 0}
  add_mem' {Φ Ψ} hΦ hΨ :=
    ⟨Submodule.add_mem _ hΦ.1 hΨ.1, fun i hi ↦ Submodule.add_mem _ (hΦ.2.1 i hi) (hΨ.2.1 i hi),
      fun A hA ↦ by
        change (Φ : Potential (ι → ℤ) E) A + (Ψ : Potential (ι → ℤ) E) A = 0
        rw [hΦ.2.2 A hA, hΨ.2.2 A hA, add_zero]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ ↦ Submodule.zero_mem _, fun _ _ ↦ rfl⟩
  smul_mem' c Φ hΦ :=
    ⟨Submodule.smul_mem _ c hΦ.1, fun i hi ↦ Submodule.smul_mem _ c (hΦ.2.1 i hi), fun A hA ↦ by
      change c • (Φ : Potential (ι → ℤ) E) A = 0
      rw [hΦ.2.2 A hA, smul_zero]⟩

omit [DecidableEq ι] in
lemma mem_BThetaOrderCond {Φ : BTheta (ι → ℤ) E} :
    Φ ∈ BThetaOrderCond Λ₀ f I ↔
      (Φ : Potential (ι → ℤ) E) Λ₀ ∈ Submodule.span ℝ (Set.range fun n ↦ ⇑(f n)) ∧
      (∀ i ∈ I, (Φ : Potential (ι → ℤ) E) (pairVolume Λ₀ i) ∈
        Submodule.span ℝ (Set.range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p))) ∧
      ∀ A ∉ orderVolumes Λ₀ I, (Φ : Potential (ι → ℤ) E) A = 0 := Iff.rfl

/-! #### The conditions define a closed subspace -/

omit [DecidableEq ι] [Fintype ι] in
/-- Evaluating an interaction term is `1`-Lipschitz on `ℬ_Θ`: `|Φ_A(η)| ≤ ‖Φ‖₀`. -/
lemma continuous_coe_apply (A : Finset (ι → ℤ)) (η : (ι → ℤ) → E) :
    Continuous fun Φ : BTheta (ι → ℤ) E ↦ (Φ : Potential (ι → ℤ) E) A η := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun Φ Ψ ↦ ?_).continuous
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
  rcases A.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [show (Φ : Potential (ι → ℤ) E) ∅ η = 0 from congrFun (BTheta.coe_apply_empty Φ) η,
      show (Ψ : Potential (ι → ℤ) E) ∅ η = 0 from congrFun (BTheta.coe_apply_empty Ψ) η]
    simp
  · have h := abs_apply_le_norm (Φ - Ψ) hi η
    rwa [Submodule.coe_sub, Potential.sub_apply] at h

omit [DecidableEq ι] [Fintype ι] in
/-- Norm convergence in `ℬ_Θ` forces pointwise — indeed uniform — convergence of each interaction
term, so the evaluation `Φ ↦ Φ_A` is continuous into the functions on configuration space with the
topology of pointwise convergence. -/
lemma continuous_coe_volume (A : Finset (ι → ℤ)) :
    Continuous fun Φ : BTheta (ι → ℤ) E ↦ (Φ : Potential (ι → ℤ) E) A :=
  continuous_pi fun η ↦ continuous_coe_apply A η

omit [DecidableEq ι] [Fintype ι] [MeasurableSpace E] in
/-- A subspace of observables spanned by finitely many functions is closed for pointwise
convergence, being finite-dimensional. -/
lemma isClosed_span_range {J : Type*} [Finite J] (g : J → (((ι → ℤ) → E) → ℝ)) :
    IsClosed ((Submodule.span ℝ (Set.range g) : Submodule ℝ ((((ι → ℤ) → E) → ℝ))) :
      Set ((((ι → ℤ) → E) → ℝ))) := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range g)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range g)
  exact Submodule.closed_of_finiteDimensional _

omit [DecidableEq ι] in
/-- **Georgii, §16.3 before Theorem (16.21):** "it is easily seen that `ℬ_Θ(f₁, …, f_N)` is closed
relative to `‖·‖₀`". Conditions (i) and (ii) confine finitely many interaction terms to
finite-dimensional, hence closed, spaces of observables, and condition (iii) is a closed condition
because the evaluation of an interaction term is continuous. -/
lemma isClosed_BThetaOrderCond :
    IsClosed (BThetaOrderCond Λ₀ f I : Set (BTheta (ι → ℤ) E)) := by
  have h1 : IsClosed {Φ : BTheta (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E) Λ₀ ∈ Submodule.span ℝ (Set.range fun n ↦ ⇑(f n))} :=
    (isClosed_span_range fun n ↦ ⇑(f n)).preimage (continuous_coe_volume Λ₀)
  have h2 : ∀ i : ι → ℤ, IsClosed {Φ : BTheta (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E) (pairVolume Λ₀ i) ∈
        Submodule.span ℝ (Set.range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p))} := fun i ↦
    (isClosed_span_range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p)).preimage
      (continuous_coe_volume _)
  have h3 : ∀ A : Finset (ι → ℤ),
      IsClosed {Φ : BTheta (ι → ℤ) E | (Φ : Potential (ι → ℤ) E) A = 0} := fun A ↦
    isClosed_singleton.preimage (continuous_coe_volume A)
  have hset : (BThetaOrderCond Λ₀ f I : Set (BTheta (ι → ℤ) E))
      = ({Φ : BTheta (ι → ℤ) E |
          (Φ : Potential (ι → ℤ) E) Λ₀ ∈ Submodule.span ℝ (Set.range fun n ↦ ⇑(f n))}
        ∩ (⋂ i ∈ I, {Φ : BTheta (ι → ℤ) E | (Φ : Potential (ι → ℤ) E) (pairVolume Λ₀ i) ∈
            Submodule.span ℝ (Set.range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p))}))
        ∩ ⋂ A ∈ (orderVolumes Λ₀ I)ᶜ, {Φ : BTheta (ι → ℤ) E |
            (Φ : Potential (ι → ℤ) E) A = 0} := by
    ext Φ
    simp only [SetLike.mem_coe, mem_BThetaOrderCond, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq, Set.mem_compl_iff, and_assoc]
  rw [hset]
  exact ((h1.inter (isClosed_biInter fun i _ ↦ h2 i)).inter
    (isClosed_biInter fun A _ ↦ h3 A))

/-! #### The generators satisfy conditions (i)–(iii) -/

omit [DecidableEq ι] [Fintype ι] in
lemma shift_zero_toFun : (shift E (0 : ι → ℤ)).toFun = id := by
  funext ω i; simp

omit [DecidableEq ι] [Fintype ι] in
lemma coe_localPotentialB_of_not_translate {Λ : Finset (ι → ℤ)}
    {g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} (hΛ : Λ.Nonempty)
    (hg : g ∈ localFunctionsOn (ι → ℤ) E Λ) {A : Finset (ι → ℤ)}
    (h : ¬ ∃ k : ι → ℤ, A = translate Λ k) :
    (localPotentialB Λ g : Potential (ι → ℤ) E) A = 0 := by
  rw [coe_localPotentialB hΛ hg, localPotential_of_not_translate h]

omit [DecidableEq ι] [Fintype ι] in
lemma coe_localPotentialB_translate {Λ : Finset (ι → ℤ)}
    {g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} (hΛ : Λ.Nonempty)
    (hg : g ∈ localFunctionsOn (ι → ℤ) E Λ) (k : ι → ℤ) :
    (localPotentialB Λ g : Potential (ι → ℤ) E) (translate Λ k) = ⇑g ∘ (shift E (-k)).toFun := by
  rw [coe_localPotentialB hΛ hg, localPotential_translate hΛ]

omit [DecidableEq ι] [Fintype ι] in
lemma coe_localPotentialB_self {Λ : Finset (ι → ℤ)}
    {g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} (hΛ : Λ.Nonempty)
    (hg : g ∈ localFunctionsOn (ι → ℤ) E Λ) :
    (localPotentialB Λ g : Potential (ι → ℤ) E) Λ = ⇑g := by
  have h := coe_localPotentialB_translate hΛ hg 0
  rwa [translate_zero, neg_zero, shift_zero_toFun, Function.comp_id] at h

omit [DecidableEq ι] in
/-- `Λ_i` is a translate of `Λ₀` only for `i = 0`. -/
lemma eq_zero_of_pairVolume_eq_translate (hΛ₀ : Λ₀.Nonempty) {i k : ι → ℤ}
    (h : pairVolume Λ₀ i = translate Λ₀ k) : i = 0 := by
  have h' : translate (pairVolume Λ₀ 0) k = pairVolume Λ₀ i := by
    rw [pairVolume_zero, ← h]
  rcases eq_or_eq_neg_of_translate_pairVolume hΛ₀ h' with h1 | h1
  · exact h1
  · simpa using h1

omit [DecidableEq ι] in
/-- `Λ_{−i}` is the translate `Λ_i + i`. -/
lemma pairVolume_neg (Λ₀ : Finset (ι → ℤ)) (i : ι → ℤ) :
    pairVolume Λ₀ (-i) = translate (pairVolume Λ₀ i) i := by
  rw [pairVolume, pairVolume, neg_neg]
  ext x
  simp only [Finset.mem_union, Finset.map_union, Finset.mem_map,
    Equiv.coe_toEmbedding, Equiv.coe_addRight]
  constructor
  · rintro (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)
  · rintro (hx | hx)
    · exact Or.inr (by simpa using hx)
    · exact Or.inl (by simpa using hx)

omit [DecidableEq ι] [Fintype ι] in
/-- The `θ_{−i}`-translate of `f_m (f_n ∘ θ_i)` is `f_n (f_m ∘ θ_{−i})`, which is the pair
observable at `−i` with the two indices exchanged. -/
lemma pairObservable_comp_shift_neg (f : Fin N → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) (i : ι → ℤ)
    (p : Fin N × Fin N) :
    ⇑(pairObservable f i p) ∘ (shift E (-i)).toFun = ⇑(pairObservable f (-i) (p.2, p.1)) := by
  funext η
  simp only [pairObservable, Function.comp_apply, lp.infty_coeFn_mul, Pi.mul_apply,
    lp.coeFn_precomp]
  have hcomp : (shift E i).toFun ((shift E (-i)).toFun η) = η := by
    have := congrFun (shift_toFun_comp_shift_toFun (E := E) i (-i)) η
    simpa [shift_zero_toFun] using this
  rw [hcomp]
  ring

omit [DecidableEq ι] in
/-- **Georgii's condition (i)–(iii) hold for the generator `Φ^{(Λ₀, f_n)}`.** -/
lemma localPotentialB_mem_BThetaOrderCond (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I) (n : Fin N) :
    localPotentialB Λ₀ (f n) ∈ BThetaOrderCond Λ₀ f I := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_localPotentialB_self hΛ₀ (hf n)]
    exact Submodule.subset_span ⟨n, rfl⟩
  · intro i hi
    have hne : ¬ ∃ k : ι → ℤ, pairVolume Λ₀ i = translate Λ₀ k := by
      rintro ⟨k, hk⟩
      exact h0I (by rwa [eq_zero_of_pairVolume_eq_translate hΛ₀ hk] at hi)
    rw [coe_localPotentialB_of_not_translate hΛ₀ (hf n) hne]
    exact Submodule.zero_mem _
  · intro A hA
    refine coe_localPotentialB_of_not_translate hΛ₀ (hf n) ?_
    rintro ⟨k, rfl⟩
    exact hA ⟨0, Set.mem_insert _ _, k, by rw [pairVolume_zero]⟩

omit [DecidableEq ι] in
/-- **Georgii's conditions (i)–(iii) hold for the generator `Φ^{(Λ_i, f_m (f_n ∘ θ_i))}`.**
The only volumes `Λ_j`, `j ∈ I`, on which it does not vanish are `Λ_i` itself, where its
interaction term is `f_m (f_n ∘ θ_i)`, and `Λ_{−i} = Λ_i + i`, where shift invariance makes it
`f_n (f_m ∘ θ_{−i})`. -/
lemma localPotentialB_pairVolume_mem_BThetaOrderCond (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I)
    {i : ι → ℤ} (hi : i ∈ I) (p : Fin N × Fin N) :
    localPotentialB (pairVolume Λ₀ i) (pairObservable f i p) ∈ BThetaOrderCond Λ₀ f I := by
  have hne : (pairVolume Λ₀ i).Nonempty := pairVolume_nonempty hΛ₀ i
  have hg : pairObservable f i p ∈ localFunctionsOn (ι → ℤ) E (pairVolume Λ₀ i) :=
    pairObservable_mem_localFunctionsOn hf i p
  have hi0 : i ≠ 0 := fun hc ↦ h0I (hc ▸ hi)
  refine ⟨?_, fun j hj ↦ ?_, fun A hA ↦ ?_⟩
  · have hnot : ¬ ∃ k : ι → ℤ, Λ₀ = translate (pairVolume Λ₀ i) k := by
      rintro ⟨k, hk⟩
      have h0 : translate (pairVolume Λ₀ i) k = pairVolume Λ₀ 0 := by rw [pairVolume_zero, ← hk]
      rcases eq_or_eq_neg_of_translate_pairVolume hΛ₀ h0 with h1 | h1
      · exact hi0 h1.symm
      · exact hi0 (by simpa using h1.symm)
    rw [coe_localPotentialB_of_not_translate hne hg hnot]
    exact Submodule.zero_mem _
  · by_cases hcase : ∃ k : ι → ℤ, pairVolume Λ₀ j = translate (pairVolume Λ₀ i) k
    · obtain ⟨k, hk⟩ := hcase
      rcases eq_or_eq_neg_of_translate_pairVolume hΛ₀ hk.symm with rfl | rfl
      · rw [coe_localPotentialB_self hne hg]
        exact Submodule.subset_span ⟨p, rfl⟩
      · rw [pairVolume_neg, coe_localPotentialB_translate hne hg i,
          pairObservable_comp_shift_neg]
        exact Submodule.subset_span ⟨(p.2, p.1), rfl⟩
    · rw [coe_localPotentialB_of_not_translate hne hg hcase]
      exact Submodule.zero_mem _
  · refine coe_localPotentialB_of_not_translate hne hg ?_
    rintro ⟨k, rfl⟩
    exact hA ⟨i, Set.mem_insert_of_mem _ hi, k, rfl⟩

omit [DecidableEq ι] in
/-- The generators of `BThetaOrder Λ₀ f I` satisfy Georgii's conditions (i)–(iii). -/
lemma orderGenerators_subset_BThetaOrderCond (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I) :
    orderGenerators Λ₀ f I ⊆ (BThetaOrderCond Λ₀ f I : Set (BTheta (ι → ℤ) E)) := by
  rintro Φ (⟨n, rfl⟩ | ⟨i, hi, p, rfl⟩)
  · exact localPotentialB_mem_BThetaOrderCond hΛ₀ hf h0I n
  · exact localPotentialB_pairVolume_mem_BThetaOrderCond hΛ₀ hf h0I hi p

omit [DecidableEq ι] in
/-- One half of the identification of the two descriptions of `ℬ_Θ(f₁, …, f_N)`: the closed span
of the generating potentials satisfies Georgii's conditions (i)–(iii). -/
theorem BThetaOrder_le_BThetaOrderCond (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I) :
    BThetaOrder Λ₀ f I ≤ BThetaOrderCond Λ₀ f I :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 (orderGenerators_subset_BThetaOrderCond hΛ₀ hf h0I))
    isClosed_BThetaOrderCond

/-! #### Truncating a potential to a family of volumes

The truncation `Potential.restrictVolumes T Φ` keeps the interaction terms of `Φ` carried by the
volumes of `T` and discards the others. It is the rounding-free version of
`Potential.BTheta.approx`, and its natural home is next to that definition in
`GibbsMeasure/Specification/TangentFunctional.lean`. -/

section Restrict

variable {S : Type*} [AddCommGroup S] {E : Type*} [MeasurableSpace E]

variable (T : Set (Finset S)) (Φ : Potential S E) in
/-- The potential that agrees with `Φ` on the volumes of `T` and vanishes elsewhere. -/
def _root_.Potential.restrictVolumes : Potential S E := T.indicator Φ

variable {T : Set (Finset S)} {Φ : Potential S E}

omit [AddCommGroup S] in
lemma restrictVolumes_of_mem {A : Finset S} (hA : A ∈ T) :
    Potential.restrictVolumes T Φ A = Φ A := Set.indicator_of_mem hA _

omit [AddCommGroup S] in
lemma restrictVolumes_of_notMem {A : Finset S} (hA : A ∉ T) :
    Potential.restrictVolumes T Φ A = 0 := Set.indicator_of_notMem hA _

omit [AddCommGroup S] in
lemma abs_restrictVolumes_le (A : Finset S) (η : S → E) :
    |Potential.restrictVolumes T Φ A η| ≤ |Φ A η| := by
  by_cases h : A ∈ T
  · rw [restrictVolumes_of_mem h]
  · rw [restrictVolumes_of_notMem h]; simp

omit [AddCommGroup S] in
lemma abs_sub_restrictVolumes_le (A : Finset S) (η : S → E) :
    |(Φ - Potential.restrictVolumes T Φ) A η| ≤ |Φ A η| := by
  by_cases h : A ∈ T
  · rw [Potential.sub_apply, restrictVolumes_of_mem h, sub_self]; simp
  · rw [Potential.sub_apply, restrictVolumes_of_notMem h]; simp

lemma isShiftInvariant_restrictVolumes (hΦ : Φ.IsShiftInvariant)
    (hT : ∀ (A : Finset S) (j : S), translate A j ∈ T ↔ A ∈ T) :
    (Potential.restrictVolumes T Φ).IsShiftInvariant := by
  rw [isShiftInvariant_iff]
  intro j A η
  by_cases h : A ∈ T
  · rw [restrictVolumes_of_mem ((hT A j).2 h), restrictVolumes_of_mem h,
      (isShiftInvariant_iff Φ).1 hΦ j A η]
  · rw [restrictVolumes_of_notMem fun hc ↦ h ((hT A j).1 hc), restrictVolumes_of_notMem h]
    rfl

omit [AddCommGroup S] in
lemma isPotential_restrictVolumes [IsPotential Φ] :
    IsPotential (Potential.restrictVolumes T Φ) := by
  refine ⟨fun Δ ↦ ?_⟩
  let : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
  by_cases h : Δ ∈ T
  · rw [restrictVolumes_of_mem h]; exact IsPotential.measurable (Φ := Φ) Δ
  · rw [restrictVolumes_of_notMem h]; exact measurable_const

omit [AddCommGroup S] in
lemma normAt_restrictVolumes_le (i : S) :
    (Potential.restrictVolumes T Φ).normAt i ≤ Φ.normAt i := by
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h0 : i ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h0),
      Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h0)]
    refine iSup_le fun η ↦ le_trans ?_ (le_iSup (fun η ↦ ‖Φ A η‖ₑ) η)
    simpa [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (abs_restrictVolumes_le (T := T) (Φ := Φ) A η)
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from h0)]
    exact bot_le

/-- The truncation of a potential of `ℬ_Θ` to a translation-invariant family of volumes again
lies in `ℬ_Θ`. -/
lemma restrictVolumes_mem_BTheta (Φ : BTheta S E)
    (hT : ∀ (A : Finset S) (j : S), translate A j ∈ T ↔ A ∈ T) :
    Potential.restrictVolumes T (Φ : Potential S E) ∈ BTheta S E := by
  refine ⟨⟨⟨fun i ↦ ?_⟩, ?_, isPotential_restrictVolumes⟩,
    isShiftInvariant_restrictVolumes (BTheta.isShiftInvariant Φ) hT⟩
  · exact ne_top_of_le_ne_top (BTheta.normAt_ne_top Φ i) (normAt_restrictVolumes_le i)
  · by_cases h : (∅ : Finset S) ∈ T
    · rw [restrictVolumes_of_mem h]; exact BTheta.coe_apply_empty Φ
    · rw [restrictVolumes_of_notMem h]

/-- **The truncation estimate.** If every volume of the finite family `𝒜` that carries a nonzero
interaction term of `Φ` belongs to `T`, then the error made by truncating `Φ` to `T` is at most
the tail of the convergent series `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖` outside `𝒜`. -/
lemma normAt_sub_restrictVolumes_le {𝒜 : Finset (Finset S)}
    (h : ∀ A ∈ 𝒜, A ∈ T ∨ Φ A = 0) :
    ((Φ : Potential S E) - Potential.restrictVolumes T Φ).normAt 0
      ≤ ∑' B : {B : Finset S // B ∉ 𝒜},
          {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) (B : Finset S) := by
  classical
  rw [normAt]
  refine le_trans (ENNReal.tsum_le_tsum fun B ↦ ?_)
    (le_of_eq (tsum_subtype ((𝒜 : Set (Finset S))ᶜ)
      (fun A ↦ {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A)).symm)
  by_cases hB : B ∈ 𝒜
  · have hzero : ∀ η, (Φ - Potential.restrictVolumes T Φ) B η = 0 := by
      intro η
      rcases h B hB with hT | hT
      · rw [Potential.sub_apply, restrictVolumes_of_mem hT, sub_self]
      · rw [Potential.sub_apply, hT]
        by_cases hBT : B ∈ T
        · rw [restrictVolumes_of_mem hBT, hT]; simp
        · rw [restrictVolumes_of_notMem hBT]; simp
    have : {A : Finset S | (0 : S) ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖(Φ - Potential.restrictVolumes T Φ) A η‖ₑ) B = 0 := by
      by_cases h0 : (0 : S) ∈ B
      · rw [Set.indicator_of_mem (show B ∈ {A : Finset S | (0 : S) ∈ A} from h0)]
        simp [hzero]
      · exact Set.indicator_of_notMem (show B ∉ {A : Finset S | (0 : S) ∈ A} from h0) _
    rw [this]
    exact bot_le
  · rw [Set.indicator_of_mem (show B ∈ ((𝒜 : Set (Finset S))ᶜ) from hB)]
    by_cases h0 : (0 : S) ∈ B
    · rw [Set.indicator_of_mem (show B ∈ {A : Finset S | (0 : S) ∈ A} from h0),
        Set.indicator_of_mem (show B ∈ {A : Finset S | (0 : S) ∈ A} from h0)]
      refine iSup_le fun η ↦ le_trans ?_ (le_iSup (fun η ↦ ‖Φ B η‖ₑ) η)
      simpa [Real.enorm_eq_ofReal_abs] using
        ENNReal.ofReal_le_ofReal (abs_sub_restrictVolumes_le (T := T) (Φ := Φ) B η)
    · rw [Set.indicator_of_notMem (show B ∉ {A : Finset S | (0 : S) ∈ A} from h0)]
      exact bot_le

end Restrict

/-! #### Every potential satisfying (i)–(iii) is a norm limit of finite sums of generators -/

omit [DecidableEq ι] in
lemma orderVolumes_mono {J J' : Set (ι → ℤ)} (h : J ⊆ J') :
    orderVolumes Λ₀ J ⊆ orderVolumes Λ₀ J' := by
  rintro A ⟨i, hi, k, rfl⟩
  exact ⟨i, Set.insert_subset_insert h hi, k, rfl⟩

omit [DecidableEq ι] [Fintype ι] in
/-- For a shift-invariant potential, the interaction term on a translate is the translated
interaction term: `Φ_{A + k}(η) = Φ_A(θ_{−k} η)`. -/
lemma apply_translate_of_isShiftInvariant {Φ : Potential (ι → ℤ) E} (h : Φ.IsShiftInvariant)
    (A : Finset (ι → ℤ)) (k : ι → ℤ) (η : (ι → ℤ) → E) :
    Φ (translate A k) η = Φ A ((shift E (-k)).toFun η) := by
  have hk := (isShiftInvariant_iff Φ).1 h k A ((shift E (-k)).toFun η)
  have hcomp : (shift E k).toFun ((shift E (-k)).toFun η) = η := by
    have := congrFun (shift_toFun_comp_shift_toFun (E := E) k (-k)) η
    simpa [shift_zero_toFun] using this
  rwa [hcomp] at hk

omit [DecidableEq ι] [Fintype ι] in
/-- A shift-invariant potential vanishing off the translates of a single nonempty volume `Λ` is
the potential `Φ^{(Λ, Φ_Λ)}` of Georgii (16.10). -/
lemma eq_localPotential_of_vanishing {Λ : Finset (ι → ℤ)} (hΛ : Λ.Nonempty)
    {Φ : Potential (ι → ℤ) E} (hshift : Φ.IsShiftInvariant)
    (hzero : ∀ A : Finset (ι → ℤ), (¬ ∃ k : ι → ℤ, A = translate Λ k) → Φ A = 0)
    {g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} (hg : Φ Λ = ⇑g) :
    Φ = localPotential Λ g := by
  funext A
  by_cases hA : ∃ k : ι → ℤ, A = translate Λ k
  · obtain ⟨k, rfl⟩ := hA
    rw [localPotential_translate hΛ]
    funext η
    rw [apply_translate_of_isShiftInvariant hshift Λ k η, hg]
    rfl
  · rw [hzero A hA, localPotential_of_not_translate hA]

omit [DecidableEq ι] in
/-- `Λ_i` is a new volume class as soon as neither `i` nor `−i` is already indexed, and `i ≠ 0`. -/
lemma pairVolume_notMem_orderVolumes (hΛ₀ : Λ₀.Nonempty) {J : Set (ι → ℤ)} {i : ι → ℤ}
    (hi0 : i ≠ 0) (hi : i ∉ J) (hineg : -i ∉ J) : pairVolume Λ₀ i ∉ orderVolumes Λ₀ J := by
  rintro ⟨j, hj, m, hm⟩
  have hcl : i = j ∨ i = -j := eq_or_eq_neg_of_translate_pairVolume hΛ₀ hm.symm
  rcases hj with h0 | hjJ
  · rcases hcl with h1 | h1
    · exact hi0 (by rw [h1, h0])
    · exact hi0 (by rw [h1, h0]; simp)
  · rcases hcl with h1 | h1
    · exact hi (by rw [h1]; exact hjJ)
    · exact hineg (by rw [h1, neg_neg]; exact hjJ)

omit [DecidableEq ι] in
/-- **Splitting one volume class off a truncation.** If `Λ_i` is not among the volume classes
indexed by `J`, the truncation of `Φ` to the classes indexed by `insert i J` is the truncation to
those indexed by `J` plus the potential `Φ^{(Λ_i, Φ_{Λ_i})}` of Georgii (16.10). -/
lemma restrictVolumes_orderVolumes_insert {Φ : Potential (ι → ℤ) E} (hshift : Φ.IsShiftInvariant)
    (hΛ₀ : Λ₀.Nonempty) {J : Set (ι → ℤ)} {i : ι → ℤ}
    (hnew : pairVolume Λ₀ i ∉ orderVolumes Λ₀ J)
    {g : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} (hg : Φ (pairVolume Λ₀ i) = ⇑g) :
    Potential.restrictVolumes (orderVolumes Λ₀ (insert i J)) Φ
      = Potential.restrictVolumes (orderVolumes Λ₀ J) Φ + localPotential (pairVolume Λ₀ i) g := by
  have hΛi : (pairVolume Λ₀ i).Nonempty := pairVolume_nonempty hΛ₀ i
  have hmemi : ∀ k : ι → ℤ, translate (pairVolume Λ₀ i) k ∈ orderVolumes Λ₀ (insert i J) :=
    fun k ↦ ⟨i, Set.mem_insert_of_mem _ (Set.mem_insert _ _), k, rfl⟩
  funext A
  change Potential.restrictVolumes (orderVolumes Λ₀ (insert i J)) Φ A
      = Potential.restrictVolumes (orderVolumes Λ₀ J) Φ A + localPotential (pairVolume Λ₀ i) g A
  by_cases hAi : ∃ k : ι → ℤ, A = translate (pairVolume Λ₀ i) k
  · obtain ⟨k, rfl⟩ := hAi
    have hAJ : translate (pairVolume Λ₀ i) k ∉ orderVolumes Λ₀ J := fun hc ↦
      hnew (translate_mem_orderVolumes_iff.1 hc)
    rw [restrictVolumes_of_mem (hmemi k), restrictVolumes_of_notMem hAJ,
      localPotential_translate hΛi]
    funext η
    rw [apply_translate_of_isShiftInvariant hshift _ k η, hg]
    simp
  · rw [localPotential_of_not_translate hAi]
    have hiff : A ∈ orderVolumes Λ₀ (insert i J) ↔ A ∈ orderVolumes Λ₀ J := by
      refine ⟨fun h ↦ ?_, fun h ↦ orderVolumes_mono (Set.subset_insert _ _) h⟩
      obtain ⟨j, hj, m, rfl⟩ := h
      rcases hj with h0 | hj
      · exact ⟨0, Set.mem_insert _ _, m, by rw [h0]⟩
      · rcases hj with hji | hj
        · exact absurd ⟨m, by rw [hji]⟩ hAi
        · exact ⟨j, Set.mem_insert_of_mem _ hj, m, rfl⟩
    by_cases hAJ : A ∈ orderVolumes Λ₀ J
    · rw [restrictVolumes_of_mem (hiff.2 hAJ), restrictVolumes_of_mem hAJ]
      funext η; simp
    · rw [restrictVolumes_of_notMem fun hc ↦ hAJ (hiff.1 hc), restrictVolumes_of_notMem hAJ]
      funext η; simp

omit [DecidableEq ι] in
/-- If `−i` is already indexed then adjoining `i` adds no new volume: `Λ_{−i}` is the translate
`Λ_i + i`. -/
lemma orderVolumes_insert_of_neg_mem {J : Set (ι → ℤ)} {i : ι → ℤ} (hi : -i ∈ J) :
    orderVolumes Λ₀ (insert i J) = orderVolumes Λ₀ J := by
  refine Set.Subset.antisymm ?_ (orderVolumes_mono (Set.subset_insert _ _))
  rintro A ⟨j, hj, m, rfl⟩
  rcases hj with h0 | hj
  · exact ⟨0, Set.mem_insert _ _, m, by rw [h0]⟩
  · rcases hj with hji | hj
    · rw [hji]
      refine translate_mem_orderVolumes ?_ m
      refine ⟨-i, Set.mem_insert_of_mem _ hi, -i, ?_⟩
      have h := pairVolume_neg Λ₀ (-i)
      rwa [neg_neg] at h
    · exact ⟨j, Set.mem_insert_of_mem _ hj, m, rfl⟩

omit [DecidableEq ι] in
lemma mem_orderVolumes_empty {A : Finset (ι → ℤ)} :
    A ∈ orderVolumes Λ₀ (∅ : Set (ι → ℤ)) ↔ ∃ k : ι → ℤ, A = translate Λ₀ k := by
  constructor
  · rintro ⟨i, hi, k, rfl⟩
    rcases hi with h0 | h0
    · exact ⟨k, by rw [h0, pairVolume_zero]⟩
    · exact absurd h0 (Set.notMem_empty i)
  · rintro ⟨k, rfl⟩
    exact ⟨0, Set.mem_insert _ _, k, by rw [pairVolume_zero]⟩

omit [DecidableEq ι] [Fintype ι] [MeasurableSpace E] in
/-- A bounded observable in the span of finitely many others is a finite linear combination of
them. -/
lemma exists_coeFn_eq_of_mem_span_range {J : Type*} [Fintype J]
    {u : J → lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {v : ((ι → ℤ) → E) → ℝ}
    (hv : v ∈ Submodule.span ℝ (Set.range fun j ↦ ⇑(u j))) :
    ∃ c : J → ℝ, ⇑(∑ j, c j • u j) = v := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  refine ⟨c, ?_⟩
  rw [← hc]
  simp only [lp.coeFn_sum, lp.coeFn_smul]

omit [DecidableEq ι] in
/-- `Φ^{(Λ₀, g)} ∈ ℬ_Θ(f₁, …, f_N)` for every `g` in the span of `f₁, …, f_N`. -/
lemma localPotentialB_mem_BThetaOrder_of_mem_span (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (c : Fin N → ℝ) :
    localPotentialB Λ₀ (∑ n, c n • f n) ∈ BThetaOrder Λ₀ f I := by
  rw [localPotentialB_sum_smul hΛ₀ c f hf]
  exact Submodule.sum_mem _ fun n _ ↦
    Submodule.smul_mem _ _ (subset_BThetaOrder (Or.inl ⟨n, rfl⟩))

omit [DecidableEq ι] in
/-- `Φ^{(Λ_i, g)} ∈ ℬ_Θ(f₁, …, f_N)` for every `g` in the span of the `f_m (f_n ∘ θ_i)`. -/
lemma localPotentialB_pairVolume_mem_BThetaOrder_of_mem_span (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) {i : ι → ℤ} (hi : i ∈ I)
    (c : Fin N × Fin N → ℝ) :
    localPotentialB (pairVolume Λ₀ i) (∑ p, c p • pairObservable f i p) ∈ BThetaOrder Λ₀ f I := by
  rw [localPotentialB_sum_smul (pairVolume_nonempty hΛ₀ i) c _
    (pairObservable_mem_localFunctionsOn hf i)]
  exact Submodule.sum_mem _ fun p _ ↦
    Submodule.smul_mem _ _ (subset_BThetaOrder (Or.inr ⟨i, hi, p, rfl⟩))

omit [DecidableEq ι] in
/-- **The finite truncations of a potential satisfying (i)–(iii) lie in the closed span.** For a
finite set `F ⊆ I` of indices, the potential obtained from `Φ` by keeping only the interaction
terms carried by the translates of `Λ₀` and of the `Λ_i`, `i ∈ F`, is the finite sum
`Φ^{(Λ₀, Φ_{Λ₀})} + ∑_{i} Φ^{(Λ_i, Φ_{Λ_i})}` over a set of representatives of the classes
`{i, −i}` meeting `F`, hence lies in `ℬ_Θ(f₁, …, f_N)`. -/
lemma exists_mem_BThetaOrder_coe_eq_restrictVolumes (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I)
    {Φ : BTheta (ι → ℤ) E} (hΦ : Φ ∈ BThetaOrderCond Λ₀ f I) :
    ∀ F : Finset (ι → ℤ), ↑F ⊆ I → ∃ Ψ : BTheta (ι → ℤ) E, Ψ ∈ BThetaOrder Λ₀ f I ∧
      (Ψ : Potential (ι → ℤ) E) = Potential.restrictVolumes
        (orderVolumes Λ₀ (F : Set (ι → ℤ))) (Φ : Potential (ι → ℤ) E) := by
  classical
  have hshift : (Φ : Potential (ι → ℤ) E).IsShiftInvariant := BTheta.isShiftInvariant Φ
  refine Finset.induction ?_ ?_
  · intro _
    obtain ⟨c, hc⟩ := exists_coeFn_eq_of_mem_span_range (u := f) hΦ.1
    refine ⟨localPotentialB Λ₀ (∑ n, c n • f n),
      localPotentialB_mem_BThetaOrder_of_mem_span hΛ₀ hf c, ?_⟩
    have hmem : (∑ n, c n • f n) ∈ localFunctionsOn (ι → ℤ) E Λ₀ :=
      Subalgebra.sum_mem _ fun n _ ↦ Subalgebra.smul_mem _ (hf n) _
    rw [coe_localPotentialB hΛ₀ hmem]
    refine (eq_localPotential_of_vanishing hΛ₀
      (isShiftInvariant_restrictVolumes hshift fun A j ↦ translate_mem_orderVolumes_iff)
      (fun A hA ↦ restrictVolumes_of_notMem fun hc' ↦ hA (mem_orderVolumes_empty.1 (by
        simpa using hc'))) ?_).symm
    rw [restrictVolumes_of_mem
      (by simpa using mem_orderVolumes_empty.2 ⟨0, (translate_zero _).symm⟩), hc]
  · intro i F hiF ih hins
    have hFI : (F : Set (ι → ℤ)) ⊆ I := fun x hx ↦ hins (by simp [hx])
    have hiI : i ∈ I := hins (by simp)
    obtain ⟨Ψ, hΨmem, hΨeq⟩ := ih hFI
    have hcoe : ((insert i F : Finset (ι → ℤ)) : Set (ι → ℤ)) = insert i (F : Set (ι → ℤ)) :=
      Finset.coe_insert i F
    by_cases hneg : -i ∈ F
    · refine ⟨Ψ, hΨmem, ?_⟩
      rw [hΨeq, hcoe, orderVolumes_insert_of_neg_mem (by simpa using hneg)]
    · have hi0 : i ≠ 0 := fun hc ↦ h0I (hc ▸ hiI)
      have hnew : pairVolume Λ₀ i ∉ orderVolumes Λ₀ (F : Set (ι → ℤ)) :=
        pairVolume_notMem_orderVolumes hΛ₀ hi0 (by simpa using hiF) (by simpa using hneg)
      obtain ⟨c, hc⟩ := exists_coeFn_eq_of_mem_span_range (u := fun p : Fin N × Fin N ↦
        pairObservable f i p) (hΦ.2.1 i hiI)
      have hmem : (∑ p, c p • pairObservable f i p) ∈
          localFunctionsOn (ι → ℤ) E (pairVolume Λ₀ i) :=
        Subalgebra.sum_mem _ fun p _ ↦
          Subalgebra.smul_mem _ (pairObservable_mem_localFunctionsOn hf i p) _
      refine ⟨Ψ + localPotentialB (pairVolume Λ₀ i) (∑ p, c p • pairObservable f i p),
        Submodule.add_mem _ hΨmem
          (localPotentialB_pairVolume_mem_BThetaOrder_of_mem_span hΛ₀ hf hiI c), ?_⟩
      rw [Submodule.coe_add, hΨeq, coe_localPotentialB (pairVolume_nonempty hΛ₀ i) hmem, hcoe]
      exact (restrictVolumes_orderVolumes_insert hshift hΛ₀ hnew hc.symm).symm

omit [DecidableEq ι] in
/-- **The second half of the identification of the two descriptions of `ℬ_Θ(f₁, …, f_N)`.**
A potential satisfying Georgii's conditions (i)–(iii) is the `‖·‖₀`-limit of its truncations to
finitely many volume classes, each of which is a finite linear combination of the generating
potentials. -/
theorem BThetaOrderCond_le_BThetaOrder (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I) :
    BThetaOrderCond Λ₀ f I ≤ BThetaOrder Λ₀ f I := by
  classical
  intro Φ hΦ
  rw [← SetLike.mem_coe, ← isClosed_BThetaOrder.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set g : Finset (ι → ℤ) → ℝ≥0∞ :=
    fun A ↦ {A : Finset (ι → ℤ) | (0 : ι → ℤ) ∈ A}.indicator
      (fun A ↦ ⨆ η, ‖(Φ : Potential (ι → ℤ) E) A η‖ₑ) A with hgdef
  have hgtop : ∑' B, g B ≠ ⊤ := BTheta.normAt_ne_top Φ 0
  obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : Finset (Finset (ι → ℤ)),
      (∑' B : {B : Finset (ι → ℤ) // B ∉ 𝒜}, g (B : Finset (ι → ℤ)))
        ≤ ENNReal.ofReal (ε / 2) :=
    (ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero hgtop)
      (ENNReal.ofReal (ε / 2)) (by positivity)).exists
  have hidx : ∀ A : Finset (ι → ℤ), ∃ i : ι → ℤ, (Φ : Potential (ι → ℤ) E) A ≠ 0 →
      i ∈ insert (0 : ι → ℤ) I ∧ ∃ k : ι → ℤ, A = translate (pairVolume Λ₀ i) k := by
    intro A
    by_cases hA : (Φ : Potential (ι → ℤ) E) A = 0
    · exact ⟨0, fun hc ↦ absurd hA hc⟩
    · have hmem : A ∈ orderVolumes Λ₀ I := by
        by_contra hc
        exact hA (hΦ.2.2 A hc)
      obtain ⟨i, hi, k, hk⟩ := hmem
      exact ⟨i, fun _ ↦ ⟨hi, k, hk⟩⟩
  choose idx hidx using hidx
  set F : Finset (ι → ℤ) := (𝒜.image idx).filter (· ∈ I) with hFdef
  have hFmem : ∀ x : ι → ℤ, x ∈ F ↔ (x ∈ 𝒜.image idx ∧ x ∈ I) := by
    intro x; rw [hFdef, Finset.mem_filter]
  have hFI : (F : Set (ι → ℤ)) ⊆ I := fun x hx ↦ ((hFmem x).1 (by simpa using hx)).2
  obtain ⟨Ψ, hΨmem, hΨeq⟩ :=
    exists_mem_BThetaOrder_coe_eq_restrictVolumes hΛ₀ hf h0I hΦ F hFI
  refine ⟨Ψ, hΨmem, ?_⟩
  have hcover : ∀ A ∈ 𝒜, A ∈ orderVolumes Λ₀ (F : Set (ι → ℤ)) ∨
      (Φ : Potential (ι → ℤ) E) A = 0 := by
    intro A hA
    by_cases hz : (Φ : Potential (ι → ℤ) E) A = 0
    · exact Or.inr hz
    obtain ⟨hi, k, hk⟩ := hidx A hz
    refine Or.inl ?_
    rcases hi with h0 | hiI
    · exact ⟨0, Set.mem_insert _ _, k, by rw [hk, h0]⟩
    · refine ⟨idx A, Set.mem_insert_of_mem _ ?_, k, hk⟩
      simpa [hFdef] using Finset.mem_filter.2 ⟨Finset.mem_image_of_mem idx hA, hiI⟩
  have hle : ((Φ : Potential (ι → ℤ) E) -
      Potential.restrictVolumes (orderVolumes Λ₀ (F : Set (ι → ℤ)))
        (Φ : Potential (ι → ℤ) E)).normAt 0 ≤ ENNReal.ofReal (ε / 2) :=
    (normAt_sub_restrictVolumes_le hcover).trans h𝒜
  rw [dist_eq_norm, BTheta.norm_def, Submodule.coe_sub, hΨeq]
  calc (((Φ : Potential (ι → ℤ) E) -
        Potential.restrictVolumes (orderVolumes Λ₀ (F : Set (ι → ℤ)))
          (Φ : Potential (ι → ℤ) E)).normAt 0).toReal
      ≤ (ENNReal.ofReal (ε / 2)).toReal := ENNReal.toReal_mono (by simp) hle
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := by linarith

omit [DecidableEq ι] in
/-- **Georgii, §16.3 before Theorem (16.21).** "It is easily seen that `ℬ_Θ(f₁, …, f_N)` is closed
relative to `‖·‖₀`. More precisely, `ℬ_Θ(f₁, …, f_N)` is the closed linear span of the potentials
`Φ^{(Λ₀, f_n)}` and `Φ^{(Λ_i, f_m f_n ∘ θ_i)}`." The two descriptions of the space — by the three
conditions (i)–(iii) on the interaction terms, and as the closed linear span of the generating
potentials of Lemma (16.10) — define the same subspace of `ℬ_Θ`.

The hypothesis `0 ∉ I` is Georgii's `i ≠ 0`: the volume `Λ_0` is `Λ₀` itself, on which condition
(i), not condition (ii), applies. -/
theorem BThetaOrderCond_eq_BThetaOrder (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I) :
    BThetaOrderCond Λ₀ f I = BThetaOrder Λ₀ f I :=
  le_antisymm (BThetaOrderCond_le_BThetaOrder hΛ₀ hf h0I)
    (BThetaOrder_le_BThetaOrderCond hΛ₀ hf h0I)

omit [DecidableEq ι] in
/-- **Georgii's conditions (i)–(iii) characterise membership of `ℬ_Θ(f₁, …, f_N)`.** -/
theorem mem_BThetaOrder_iff (hΛ₀ : Λ₀.Nonempty)
    (hf : ∀ n, f n ∈ localFunctionsOn (ι → ℤ) E Λ₀) (h0I : (0 : ι → ℤ) ∉ I)
    {Φ : BTheta (ι → ℤ) E} :
    Φ ∈ BThetaOrder Λ₀ f I ↔
      (Φ : Potential (ι → ℤ) E) Λ₀ ∈ Submodule.span ℝ (Set.range fun n ↦ ⇑(f n)) ∧
      (∀ i ∈ I, (Φ : Potential (ι → ℤ) E) (pairVolume Λ₀ i) ∈
        Submodule.span ℝ (Set.range fun p : Fin N × Fin N ↦ ⇑(pairObservable f i p))) ∧
      ∀ A ∉ orderVolumes Λ₀ I, (Φ : Potential (ι → ℤ) E) A = 0 := by
  rw [← BThetaOrderCond_eq_BThetaOrder hΛ₀ hf h0I]
  exact mem_BThetaOrderCond

end Conditions

end MeasureTheory.GibbsMeasure

end

end
