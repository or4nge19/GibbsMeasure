/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.DotProductCauchySchwarz
public import GibbsMeasure.Potential.TailSummable
public import GibbsMeasure.Specification.InfraredBound

/-!
# Georgii (20.5): the Gibbsian specification of a Heisenberg potential over an unbounded spin space

For an unbounded state space `E = ℝ^N` and a coupling `J` of infinite range, the Heisenberg
potential (20.1) violates Georgii's condition (2.2)(ii): the Hamiltonian series
`H_Λ^Φ = ∑_{A ∩ Λ ≠ ∅} Φ_A` does not converge for every boundary condition.  Under (20.4) it does
converge on the tail event `Ω_*` of slowly increasing configurations, and Georgii's (20.5) is the
resulting specification — Gibbsian on `Ω_*`, a Dirac mass off it.

The general layer is `GibbsMeasure.Potential.TailSummable` (`Potential.tailGibbsSpecification`,
Georgii (13.18)/(20.5) for an arbitrary potential and tail event) and
`GibbsMeasure.Specification.TailGluedSpecification`.  What is proved here is the input it needs
for the Heisenberg potential of `GibbsMeasure.Specification.HeisenbergPeriodic`.

## Main results

* `MeasureTheory.GibbsMeasure.isSummableOn_heisenbergPotential`: **the Hamiltonians `H_Λ^Φ(ω)`,
  `Λ ∈ 𝒮`, are well-defined whenever `ω ∈ Ω_*`** (§20.1, the sentence after (20.4)).  The series
  converges *absolutely*, which is more than Georgii's Convention (2.1) asks.  The hypotheses are
  exactly his: `J` even and (20.4) `IsSlowlySummable J`, plus his normalisation `J 0 = 0` of
  (20.1), which is what kills the one-body term.

## The enumeration of the interaction supports

Georgii's series is indexed by the finite subsets `A` of `ℤ^d` meeting `Λ`, of which only the pairs
contribute.  The summability proof therefore transports the series to an index set on which the
majorant factorises, namely the pairs of sites `(i, j)` with `encode i ≤ encode j` for an arbitrary
injection `encode : ℤ^d → ℕ`; `sitePairFinset` is `(i, j) ↦ {i, j}`, injective on that set and with
range containing every interaction support on which the potential is non-zero.  Nothing in the
statement depends on the choice of `encode`.

## The estimate

For `ω ∈ Ω_*` pick `t ≥ 0` with `|σ_i| ≤ t α(i)` for all `i`.  Cauchy–Schwarz
(`Matrix.abs_dotProduct_le_sqrt_mul_sqrt`) gives `|σ_i · σ_j| ≤ t² α(i) α(j)`, and Georgii's
translated form `∑_j |J(i-j)| α(j) < ∞` of (20.4)
(`MeasureTheory.GibbsMeasure.IsSlowlySummable.summable_sub`) makes the double series converge.
Cauchy–Schwarz is what forces the α's to appear as a *product*; the elementary
`2|x ⬝ᵥ y| ≤ |x|² + |y|²` would need `∑_j |J(i-j)| α(j)²`, which (20.4) does not give.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix MeasureTheory Potential Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ}

/-! ### Enumerating the interaction supports of a pair potential -/

section PairEnumeration

variable (d) in
/-- The pairs of sites, without repetition: ordered by an arbitrary injection of `ℤ^d` into `ℕ`.
This is only an index set for the interaction supports of a pair potential; no statement below
depends on the ordering. -/
private def SitePair : Type :=
  {p : (Fin d → ℤ) × (Fin d → ℤ) // Encodable.encode p.1 ≤ Encodable.encode p.2}

/-- The interaction support attached to a pair of sites. -/
private def sitePairFinset (p : SitePair d) : Finset (Fin d → ℤ) := {p.1.1, p.1.2}

private lemma injective_sitePairFinset : Function.Injective (sitePairFinset (d := d)) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  simp only [sitePairFinset] at h
  have ha : a ∈ ({a', b'} : Finset (Fin d → ℤ)) := h ▸ Finset.mem_insert_self a {b}
  have hb : b ∈ ({a', b'} : Finset (Fin d → ℤ)) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  have ha' : a' ∈ ({a, b} : Finset (Fin d → ℤ)) := h ▸ Finset.mem_insert_self a' {b'}
  have hb' : b' ∈ ({a, b} : Finset (Fin d → ℤ)) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b')
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ha' hb'
  have h1 : Encodable.encode a' ≤ Encodable.encode a := by
    rcases ha with rfl | rfl
    · exact le_rfl
    · exact hab'
  have h2 : Encodable.encode a ≤ Encodable.encode a' := by
    rcases ha' with rfl | rfl
    · exact le_rfl
    · exact hab
  have h3 : Encodable.encode b ≤ Encodable.encode b' := by
    rcases hb with rfl | rfl
    · exact hab'
    · exact le_rfl
  have h4 : Encodable.encode b' ≤ Encodable.encode b := by
    rcases hb' with rfl | rfl
    · exact hab
    · exact le_rfl
  have haa : a = a' := Encodable.encode_injective (le_antisymm h2 h1)
  have hbb : b = b' := Encodable.encode_injective (le_antisymm h3 h4)
  subst haa; subst hbb; rfl

private lemma mem_range_sitePairFinset (i j : Fin d → ℤ) :
    ({i, j} : Finset (Fin d → ℤ)) ∈ Set.range (sitePairFinset (d := d)) := by
  rcases le_total (Encodable.encode i) (Encodable.encode j) with h | h
  · exact ⟨⟨(i, j), h⟩, rfl⟩
  · exact ⟨⟨(j, i), h⟩, by simpa [sitePairFinset] using Finset.pair_comm j i⟩

private lemma heisenbergPotential_eq_zero_of_notMem_range {A : Finset (Fin d → ℤ)}
    (hA : A ∉ Set.range (sitePairFinset (d := d))) (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPotential n J A ω = 0 :=
  heisenbergPotential_of_forall_ne
    (fun i j hij ↦ hA (by rw [hij]; exact mem_range_sitePairFinset i j)) ω

private lemma not_disjoint_sitePairFinset_iff {Λ : Finset (Fin d → ℤ)} (p : SitePair d) :
    ¬ Disjoint (sitePairFinset p) Λ ↔ p.1.1 ∈ Λ ∨ p.1.2 ∈ Λ := by
  simp only [sitePairFinset, Finset.not_disjoint_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha | ha, haΛ⟩
    · exact Or.inl (ha ▸ haΛ)
    · exact Or.inr (ha ▸ haΛ)
  · rintro (h | h)
    · exact ⟨p.1.1, Or.inl rfl, h⟩
    · exact ⟨p.1.2, Or.inr rfl, h⟩

end PairEnumeration

/-! ### The majorant of the Hamiltonian series -/

section Majorant

variable (J)

/-- The majorant of the interaction terms of `H_Λ^Φ`, as a function of an *ordered* pair of sites:
`(1_Λ(i) + 1_Λ(j)) |J(i-j)| |σ_i| |σ_j|`.  Its two summands are summable separately (over the whole
product `ℤ^d × ℤ^d`), which is what makes the Hamiltonian series absolutely convergent. -/
private def pairMajorant (Λ : Finset (Fin d → ℤ)) (ω : (Fin d → ℤ) → (Fin n → ℝ))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  ((if p.1 ∈ Λ then (1 : ℝ) else 0) + (if p.2 ∈ Λ then (1 : ℝ) else 0)) *
    (|J (p.1 - p.2)| * (Real.sqrt (ω p.1 ⬝ᵥ ω p.1) * Real.sqrt (ω p.2 ⬝ᵥ ω p.2)))

variable {J}

private lemma pairMajorant_nonneg {Λ : Finset (Fin d → ℤ)} {ω : (Fin d → ℤ) → (Fin n → ℝ)}
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : 0 ≤ pairMajorant J Λ ω p := by
  refine mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) ?_)
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The interaction terms of `H_Λ^Φ` are dominated by the majorant. -/
private lemma abs_hamiltonianTerms_le_pairMajorant (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (Λ : Finset (Fin d → ℤ)) (ω : (Fin d → ℤ) → (Fin n → ℝ)) (p : SitePair d) :
    |(heisenbergPotential n J).hamiltonianTerms Λ ω (sitePairFinset p)|
      ≤ pairMajorant J Λ ω p.1 := by
  classical
  obtain ⟨⟨i, j⟩, hp⟩ := p
  change |(heisenbergPotential n J).hamiltonianTerms Λ ω ({i, j} : Finset (Fin d → ℤ))|
    ≤ pairMajorant J Λ ω (i, j)
  by_cases hdisj : Disjoint ({i, j} : Finset (Fin d → ℤ)) Λ
  · rw [hamiltonianTerms_of_disjoint hdisj, abs_zero]
    exact pairMajorant_nonneg _
  · rw [hamiltonianTerms_of_not_disjoint hdisj]
    have hmem : i ∈ Λ ∨ j ∈ Λ :=
      (not_disjoint_sitePairFinset_iff (Λ := Λ) ⟨(i, j), hp⟩).1 hdisj
    have hi0 : (0 : ℝ) ≤ if i ∈ Λ then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    have hj0 : (0 : ℝ) ≤ if j ∈ Λ then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    have hone : (1 : ℝ) ≤ (if i ∈ Λ then (1 : ℝ) else 0) + (if j ∈ Λ then (1 : ℝ) else 0) := by
      rcases hmem with h | h
      · have h1 : (if i ∈ Λ then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [h1]; linarith
      · have h1 : (if j ∈ Λ then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [h1]; linarith
    have hbase : |heisenbergPotential n J ({i, j} : Finset (Fin d → ℤ)) ω|
        ≤ |J (i - j)| * (Real.sqrt (ω i ⬝ᵥ ω i) * Real.sqrt (ω j ⬝ᵥ ω j)) := by
      by_cases hij : i = j
      · subst hij
        rw [Finset.pair_eq_singleton, heisenbergPotential_singleton hJ0, abs_zero]
        exact mul_nonneg (abs_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      · rw [heisenbergPotential_pair heven hij, abs_neg, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_dotProduct_le_sqrt_mul_sqrt (ω i) (ω j))
          (abs_nonneg _)
    have hnn : 0 ≤ |J (i - j)| * (Real.sqrt (ω i ⬝ᵥ ω i) * Real.sqrt (ω j ⬝ᵥ ω j)) :=
      mul_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc |heisenbergPotential n J ({i, j} : Finset (Fin d → ℤ)) ω|
        ≤ |J (i - j)| * (Real.sqrt (ω i ⬝ᵥ ω i) * Real.sqrt (ω j ⬝ᵥ ω j)) := hbase
      _ ≤ pairMajorant J Λ ω (i, j) := by
          rw [pairMajorant]
          exact le_mul_of_one_le_left hnn hone

variable (J) in
/-- The first summand of the majorant, `1_Λ(i) |J(i-j)| |σ_i| |σ_j|`. -/
private def pairFst (Λ : Finset (Fin d → ℤ)) (ω : (Fin d → ℤ) → (Fin n → ℝ))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  (if p.1 ∈ Λ then (1 : ℝ) else 0) *
    (|J (p.1 - p.2)| * (Real.sqrt (ω p.1 ⬝ᵥ ω p.1) * Real.sqrt (ω p.2 ⬝ᵥ ω p.2)))

private lemma pairFst_nonneg {Λ : Finset (Fin d → ℤ)} {ω : (Fin d → ℤ) → (Fin n → ℝ)}
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : 0 ≤ pairFst J Λ ω p := by
  refine mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) ?_)
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The majorant is the first summand plus its transpose; the two agree because `J` is even. -/
private lemma pairMajorant_eq_add (heven : ∀ m, J (-m) = J m) (Λ : Finset (Fin d → ℤ))
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) (p : (Fin d → ℤ) × (Fin d → ℤ)) :
    pairMajorant J Λ ω p = pairFst J Λ ω p + pairFst J Λ ω p.swap := by
  have hJ : |J (p.2 - p.1)| = |J (p.1 - p.2)| := by
    rw [show p.2 - p.1 = -(p.1 - p.2) by abel, heven]
  simp only [pairMajorant, pairFst, Prod.fst_swap, Prod.snd_swap, hJ]
  ring

/-- **Summability of the first summand of the majorant**, by Fubini for nonnegative families and
Georgii's translated (20.4). -/
private lemma summable_pairFst (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} {t : ℝ}
    (hω : ∀ i, Real.sqrt (ω i ⬝ᵥ ω i) ≤ t * slowGrowth i) :
    Summable (pairFst J Λ ω) := by
  classical
  set s : (Fin d → ℤ) → ℝ := fun i ↦ Real.sqrt (ω i ⬝ᵥ ω i) with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i ↦ Real.sqrt_nonneg _
  refine (summable_prod_of_nonneg fun p ↦ pairFst_nonneg p).2 ⟨fun i ↦ ?_, ?_⟩
  · by_cases hi : i ∈ Λ
    · simp only [pairFst, hi, ite_true, one_mul]
      refine Summable.of_nonneg_of_le (fun j ↦ by positivity) (fun j ↦ ?_)
        ((hJ.summable_sub' i).mul_left (s i * t))
      have h1 : |J (i - j)| * (s i * s j) ≤ |J (i - j)| * (s i * (t * slowGrowth j)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hω j) (hs0 i)) (abs_nonneg _)
      calc |J (i - j)| * (s i * s j) ≤ |J (i - j)| * (s i * (t * slowGrowth j)) := h1
        _ = s i * t * (|J (i - j)| * slowGrowth j) := by ring
    · simp [pairFst, hi]
  · refine summable_of_ne_finset_zero (s := Λ) fun i hi ↦ ?_
    simp [pairFst, hi]

/-- **Summability of the majorant.** -/
private lemma summable_pairMajorant (heven : ∀ m, J (-m) = J m) (hJ : IsSlowlySummable J)
    (Λ : Finset (Fin d → ℤ)) {ω : (Fin d → ℤ) → (Fin n → ℝ)} {t : ℝ}
    (hω : ∀ i, Real.sqrt (ω i ⬝ᵥ ω i) ≤ t * slowGrowth i) :
    Summable (pairMajorant J Λ ω) := by
  have h₁ := summable_pairFst hJ Λ hω
  have h₂ : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) ↦ pairFst J Λ ω p.swap :=
    ((Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).summable_iff
      (f := pairFst J Λ ω)).2 h₁
  exact (h₁.add h₂).congr fun p ↦ (pairMajorant_eq_add heven Λ ω p).symm

end Majorant
/-! ### A pair-majorant estimate for an arbitrary family supported on the pairs -/

section GeneralPairBound

variable (Λ : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (s : (Fin d → ℤ) → ℝ)

/-- The first summand of a general pair majorant, `1_Λ(i) c(i,j) s_i s_j`. -/
private def genFst (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  (if p.1 ∈ Λ then (1 : ℝ) else 0) * (c p.1 p.2 * (s p.1 * s p.2))

variable {Λ c s}

private lemma genFst_nonneg (hc0 : ∀ i j, 0 ≤ c i j) (hs0 : ∀ i, 0 ≤ s i)
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : 0 ≤ genFst Λ c s p := by
  refine mul_nonneg (by positivity) (mul_nonneg (hc0 _ _) ?_)
  exact mul_nonneg (hs0 _) (hs0 _)

private lemma summable_genFst (hc0 : ∀ i j, 0 ≤ c i j) (hs0 : ∀ i, 0 ≤ s i)
    (hsummable : ∀ i, Summable fun j ↦ c i j * s j) : Summable (genFst Λ c s) := by
  classical
  refine (summable_prod_of_nonneg fun p ↦ genFst_nonneg hc0 hs0 p).2 ⟨fun i ↦ ?_, ?_⟩
  · by_cases hi : i ∈ Λ
    · have : (fun j ↦ genFst Λ c s (i, j)) = fun j ↦ s i * (c i j * s j) := by
        funext j; simp only [genFst, hi, ite_true, one_mul]; ring
      rw [this]
      exact (hsummable i).mul_left _
    · simp [genFst, hi]
  · refine summable_of_ne_finset_zero (s := Λ) fun i hi ↦ ?_
    simp [genFst, hi]

private lemma tsum_genFst (hc0 : ∀ i j, 0 ≤ c i j) (hs0 : ∀ i, 0 ≤ s i)
    (hsummable : ∀ i, Summable fun j ↦ c i j * s j) :
    ∑' q, genFst Λ c s q = ∑ i ∈ Λ, s i * ∑' j, c i j * s j := by
  classical
  rw [(summable_genFst hc0 hs0 hsummable).tsum_prod]
  have hinner : ∀ i, (∑' j, genFst Λ c s (i, j))
      = (if i ∈ Λ then (1 : ℝ) else 0) * (s i * ∑' j, c i j * s j) := by
    intro i
    have hrw : ∀ j, genFst Λ c s (i, j)
        = ((if i ∈ Λ then (1 : ℝ) else 0) * s i) * (c i j * s j) := fun j ↦ by
      simp only [genFst]; ring
    rw [tsum_congr hrw, tsum_mul_left]
    ring
  rw [tsum_congr hinner, tsum_eq_sum (s := Λ) fun i hi ↦ by simp [hi]]
  exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]

/-- **The pair-majorant estimate, for an arbitrary family supported on the pairs of sites.**  If a
family `T` indexed by the finite subsets of `ℤ^d` vanishes off the pairs and off the volumes
disjoint from `Λ`, and its value at a pair `{i, j}` meeting `Λ` is at most `c(i,j) s_i s_j` for a
nonnegative *symmetric* coefficient `c` with summable `α`-weighted rows, then

`|∑_A T(A)| ≤ 2 ∑_{i ∈ Λ} s_i ∑_j c(i,j) s_j`.

This is the estimate behind `exists_abs_hamiltonian_heisenbergPotential_le`, where
`c(i,j) = |J(i-j)|` and `s_i = |σ_i|`; it is stated for a general `c` because the *difference*
`Φ^n - Φ` of a Heisenberg potential and its periodic modification (Georgii's `H_Λ^{Φ^n - Φ}` in
the proof of (20.7)) is a pair potential with an inhomogeneous coefficient. -/
theorem abs_tsum_le_of_pairBound {T : Finset (Fin d → ℤ) → ℝ}
    (hTabs : Summable fun A ↦ |T A|)
    (hTpair : ∀ A : Finset (Fin d → ℤ),
      (∀ x y : Fin d → ℤ, A ≠ ({x, y} : Finset (Fin d → ℤ))) → T A = 0)
    (hTdisj : ∀ i j : Fin d → ℤ, Disjoint ({i, j} : Finset (Fin d → ℤ)) Λ →
      T ({i, j} : Finset (Fin d → ℤ)) = 0)
    (hc0 : ∀ i j, 0 ≤ c i j) (hcsymm : ∀ i j, c i j = c j i) (hs0 : ∀ i, 0 ≤ s i)
    (hsummable : ∀ i, Summable fun j ↦ c i j * s j)
    (hbound : ∀ i j : Fin d → ℤ,
      |T ({i, j} : Finset (Fin d → ℤ))| ≤ c i j * (s i * s j)) :
    |∑' A, T A| ≤ 2 * ∑ i ∈ Λ, s i * ∑' j, c i j * s j := by
  classical
  have hTsum : Summable T := Summable.of_abs hTabs
  -- the absolute values, transported to the pairs
  have hsupp : Function.support (fun A ↦ |T A|) ⊆ Set.range (sitePairFinset (d := d)) := by
    intro A hA
    by_contra hmem
    refine hA ?_
    have : T A = 0 := hTpair A fun x y hxy ↦ hmem (hxy ▸ mem_range_sitePairFinset x y)
    simp [this]
  have hstep₁ : |∑' A, T A| ≤ ∑' A, |T A| := by
    have hn : Summable fun A : Finset (Fin d → ℤ) ↦ ‖T A‖ := by
      simpa only [Real.norm_eq_abs] using hTabs
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
  have hstep₂ : ∑' A, |T A| = ∑' p : SitePair d, |T (sitePairFinset p)| :=
    (injective_sitePairFinset.tsum_eq hsupp).symm
  -- the pair estimate against the majorant
  have hmaj : ∀ p : SitePair d, |T (sitePairFinset p)|
      ≤ genFst Λ c s p.1 + genFst Λ c s p.1.swap := by
    rintro ⟨⟨i, j⟩, hp⟩
    have hnn : (0 : ℝ) ≤ c i j * (s i * s j) :=
      mul_nonneg (hc0 _ _) (mul_nonneg (hs0 _) (hs0 _))
    by_cases hdisj : Disjoint ({i, j} : Finset (Fin d → ℤ)) Λ
    · rw [show sitePairFinset ⟨(i, j), hp⟩ = ({i, j} : Finset (Fin d → ℤ)) from rfl,
        hTdisj i j hdisj, abs_zero]
      exact add_nonneg (genFst_nonneg hc0 hs0 _) (genFst_nonneg hc0 hs0 _)
    · have hmem : i ∈ Λ ∨ j ∈ Λ :=
        (not_disjoint_sitePairFinset_iff (Λ := Λ) ⟨(i, j), hp⟩).1 hdisj
      have hone : (1 : ℝ) ≤ (if i ∈ Λ then (1 : ℝ) else 0) + (if j ∈ Λ then (1 : ℝ) else 0) := by
        rcases hmem with h | h
        · have h1 : (if i ∈ Λ then (1 : ℝ) else 0) = 1 := by simp [h]
          have h2 : (0 : ℝ) ≤ if j ∈ Λ then (1 : ℝ) else 0 := by split_ifs <;> norm_num
          linarith
        · have h1 : (if j ∈ Λ then (1 : ℝ) else 0) = 1 := by simp [h]
          have h2 : (0 : ℝ) ≤ if i ∈ Λ then (1 : ℝ) else 0 := by split_ifs <;> norm_num
          linarith
      have hgen : genFst Λ c s (i, j) + genFst Λ c s (i, j).swap
          = ((if i ∈ Λ then (1 : ℝ) else 0) + (if j ∈ Λ then (1 : ℝ) else 0))
            * (c i j * (s i * s j)) := by
        simp only [genFst, Prod.fst_swap, Prod.snd_swap, hcsymm j i]
        ring
      rw [show sitePairFinset ⟨(i, j), hp⟩ = ({i, j} : Finset (Fin d → ℤ)) from rfl, hgen]
      exact (hbound i j).trans (le_mul_of_one_le_left hnn hone)
  -- summability of the majorant and the resulting bound
  have hfst := summable_genFst (Λ := Λ) (c := c) (s := s) hc0 hs0 hsummable
  have hswap : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) ↦ genFst Λ c s q.swap :=
    ((Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).summable_iff (f := genFst Λ c s)).2 hfst
  have hmajsum : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) ↦
      genFst Λ c s q + genFst Λ c s q.swap := hfst.add hswap
  have hstep₃ : ∑' p : SitePair d, |T (sitePairFinset p)|
      ≤ ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (genFst Λ c s q + genFst Λ c s q.swap) := by
    refine le_trans (Summable.tsum_le_tsum hmaj
      (hTabs.comp_injective injective_sitePairFinset)
      (hmajsum.subtype fun p ↦ Encodable.encode p.1 ≤ Encodable.encode p.2)) ?_
    exact hmajsum.tsum_subtype_le _
      {p : (Fin d → ℤ) × (Fin d → ℤ) | Encodable.encode p.1 ≤ Encodable.encode p.2}
      fun q ↦ add_nonneg (genFst_nonneg hc0 hs0 q) (genFst_nonneg hc0 hs0 q.swap)
  have hstep₄ : ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (genFst Λ c s q + genFst Λ c s q.swap)
      = 2 * ∑ i ∈ Λ, s i * ∑' j, c i j * s j := by
    have hswapeq : ∑' q : (Fin d → ℤ) × (Fin d → ℤ), genFst Λ c s q.swap
        = ∑' q, genFst Λ c s q :=
      (Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).tsum_eq (genFst Λ c s)
    rw [hfst.tsum_add hswap, hswapeq, tsum_genFst hc0 hs0 hsummable]
    ring
  calc |∑' A, T A| ≤ ∑' A, |T A| := hstep₁
    _ = ∑' p : SitePair d, |T (sitePairFinset p)| := hstep₂
    _ ≤ ∑' q : (Fin d → ℤ) × (Fin d → ℤ), (genFst Λ c s q + genFst Λ c s q.swap) := hstep₃
    _ = 2 * ∑ i ∈ Λ, s i * ∑' j, c i j * s j := hstep₄


/-- **The pair sum with only the exterior controlled.**  Let `c ≥ 0` be a symmetric coefficient
whose `a`-weighted rows are bounded by `R` at every site of `Λ`, where `a ≥ 1`, and let `s ≥ 0`
satisfy `s_j ≤ t a_j` **outside** `Λ` — nothing at all being assumed inside `Λ`.  Then

`∑_{i ∈ Λ} s_i ∑_j c(i,j) s_j ≤ R (1 + t) ∑_{i ∈ Λ} [1 + s_i²]`.

This is the combinatorial form of Georgii's `|H_Λ^Φ(ζ ω_{S∖Λ})| ≤ c(ω_{S∖Λ}) ∑_{i∈Λ}[1 + |ζ_i|²]`
of §20.1.  The point is the uniformity in the *inner* configuration `ζ`, which is what makes the
estimate usable inside a partition function and, in the proof of (20.7), uniformly over the
boundary conditions in `Ω_t`.  The bonds inside `Λ` are symmetrised by `s_i s_j ≤ (s_i²+s_j²)/2`,
the bonds leaving it by `s_i ≤ 1 + s_i²`. -/
theorem sum_mul_tsum_le_of_exterior_le {a : (Fin d → ℤ) → ℝ} {t R : ℝ}
    (hc0 : ∀ i j, 0 ≤ c i j) (hcsymm : ∀ i j, c i j = c j i) (hs0 : ∀ i, 0 ≤ s i)
    (ha : ∀ i, 1 ≤ a i) (ht0 : 0 ≤ t) (hR0 : 0 ≤ R)
    (hsummable : ∀ i, Summable fun j ↦ c i j * a j)
    (hrow : ∀ i ∈ Λ, ∑' j, c i j * a j ≤ R)
    (hext : ∀ j ∉ Λ, s j ≤ t * a j) :
    ∑ i ∈ Λ, s i * ∑' j, c i j * s j ≤ R * (1 + t) * ∑ i ∈ Λ, (1 + s i ^ 2) := by
  classical
  have ha0 : ∀ i, (0 : ℝ) ≤ a i := fun i ↦ le_trans zero_le_one (ha i)
  have hfin : ∀ i : Fin d → ℤ, Summable fun j ↦ (if j ∈ Λ then c i j * s j else 0) := fun i ↦
    summable_of_ne_finset_zero (s := Λ) fun j hj ↦ by simp [hj]
  have hle : ∀ i j : Fin d → ℤ,
      c i j * s j ≤ (if j ∈ Λ then c i j * s j else 0) + t * (c i j * a j) := by
    intro i j
    by_cases hj : j ∈ Λ
    · have h0 : (0 : ℝ) ≤ t * (c i j * a j) := mul_nonneg ht0 (mul_nonneg (hc0 i j) (ha0 j))
      simp only [hj, ite_true]
      linarith
    · have h1 : c i j * s j ≤ c i j * (t * a j) :=
        mul_le_mul_of_nonneg_left (hext j hj) (hc0 i j)
      simp only [hj, ite_false, zero_add]
      linarith
  have hsum_s : ∀ i, Summable fun j ↦ c i j * s j := fun i ↦
    Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (hc0 i j) (hs0 j)) (hle i)
      ((hfin i).add ((hsummable i).mul_left t))
  -- the row of `c` against `s`, split at `Λ`
  have hrowsplit : ∀ i ∈ Λ, (∑' j, c i j * s j) ≤ (∑ j ∈ Λ, c i j * s j) + t * R := by
    intro i hi
    calc ∑' j, c i j * s j
        ≤ ∑' j, ((if j ∈ Λ then c i j * s j else 0) + t * (c i j * a j)) :=
          Summable.tsum_le_tsum (hle i) (hsum_s i) ((hfin i).add ((hsummable i).mul_left t))
      _ = (∑ j ∈ Λ, c i j * s j) + t * ∑' j, c i j * a j := by
          rw [(hfin i).tsum_add ((hsummable i).mul_left t), tsum_mul_left,
            tsum_eq_sum (s := Λ) fun j hj ↦ by simp [hj]]
          congr 1
          exact Finset.sum_congr rfl fun j hj ↦ by simp [hj]
      _ ≤ (∑ j ∈ Λ, c i j * s j) + t * R := by
          have := mul_le_mul_of_nonneg_left (hrow i hi) ht0
          linarith
  -- the rows and columns of `c` over `Λ`
  have hrowL : ∀ i ∈ Λ, ∑ j ∈ Λ, c i j ≤ R := by
    intro i hi
    calc ∑ j ∈ Λ, c i j ≤ ∑ j ∈ Λ, c i j * a j :=
          Finset.sum_le_sum fun j _ ↦ le_mul_of_one_le_right (hc0 i j) (ha j)
      _ ≤ ∑' j, c i j * a j :=
          (hsummable i).sum_le_tsum Λ fun j _ ↦ mul_nonneg (hc0 i j) (ha0 j)
      _ ≤ R := hrow i hi
  have hcolL : ∀ j ∈ Λ, ∑ i ∈ Λ, c i j ≤ R := by
    intro j hj
    calc ∑ i ∈ Λ, c i j = ∑ i ∈ Λ, c j i := Finset.sum_congr rfl fun i _ ↦ hcsymm i j
      _ ≤ R := hrowL j hj
  -- the interior double sum
  have hint : ∑ i ∈ Λ, s i * ∑ j ∈ Λ, c i j * s j ≤ R * ∑ i ∈ Λ, s i ^ 2 := by
    have h1 : ∑ i ∈ Λ, s i * ∑ j ∈ Λ, c i j * s j
        ≤ ∑ i ∈ Λ, ∑ j ∈ Λ, (c i j * s i ^ 2 / 2 + c i j * s j ^ 2 / 2) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ ↦ by nlinarith [hc0 i j, sq_nonneg (s i - s j)]
    have hA : ∑ i ∈ Λ, ∑ j ∈ Λ, c i j * s i ^ 2 / 2 ≤ (R * ∑ i ∈ Λ, s i ^ 2) / 2 := by
      have hstep : ∀ i ∈ Λ, ∑ j ∈ Λ, c i j * s i ^ 2 / 2 ≤ R * s i ^ 2 / 2 := by
        intro i hi
        calc ∑ j ∈ Λ, c i j * s i ^ 2 / 2 = (∑ j ∈ Λ, c i j) * (s i ^ 2 / 2) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun j _ ↦ by ring
          _ ≤ R * (s i ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right (hrowL i hi) (by positivity)
          _ = R * s i ^ 2 / 2 := by ring
      calc ∑ i ∈ Λ, ∑ j ∈ Λ, c i j * s i ^ 2 / 2 ≤ ∑ i ∈ Λ, R * s i ^ 2 / 2 :=
            Finset.sum_le_sum hstep
        _ = (R * ∑ i ∈ Λ, s i ^ 2) / 2 := by rw [Finset.mul_sum, Finset.sum_div]
    have hB : ∑ i ∈ Λ, ∑ j ∈ Λ, c i j * s j ^ 2 / 2 ≤ (R * ∑ i ∈ Λ, s i ^ 2) / 2 := by
      rw [Finset.sum_comm]
      have hstep : ∀ j ∈ Λ, ∑ i ∈ Λ, c i j * s j ^ 2 / 2 ≤ R * s j ^ 2 / 2 := by
        intro j hj
        calc ∑ i ∈ Λ, c i j * s j ^ 2 / 2 = (∑ i ∈ Λ, c i j) * (s j ^ 2 / 2) := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun i _ ↦ by ring
          _ ≤ R * (s j ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right (hcolL j hj) (by positivity)
          _ = R * s j ^ 2 / 2 := by ring
      calc ∑ j ∈ Λ, ∑ i ∈ Λ, c i j * s j ^ 2 / 2 ≤ ∑ j ∈ Λ, R * s j ^ 2 / 2 :=
            Finset.sum_le_sum hstep
        _ = (R * ∑ i ∈ Λ, s i ^ 2) / 2 := by rw [Finset.mul_sum, Finset.sum_div]
    have hsplit : ∑ i ∈ Λ, ∑ j ∈ Λ, (c i j * s i ^ 2 / 2 + c i j * s j ^ 2 / 2)
        = (∑ i ∈ Λ, ∑ j ∈ Λ, c i j * s i ^ 2 / 2)
          + ∑ i ∈ Λ, ∑ j ∈ Λ, c i j * s j ^ 2 / 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
    rw [hsplit] at h1
    linarith
  -- assemble
  have hsq_le : ∑ i ∈ Λ, s i ^ 2 ≤ ∑ i ∈ Λ, (1 + s i ^ 2) :=
    Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (s i)]
  have hs_sum : ∑ i ∈ Λ, s i ≤ ∑ i ∈ Λ, (1 + s i ^ 2) :=
    Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (s i - 1), hs0 i]
  calc ∑ i ∈ Λ, s i * ∑' j, c i j * s j
      ≤ ∑ i ∈ Λ, s i * ((∑ j ∈ Λ, c i j * s j) + t * R) :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hrowsplit i hi) (hs0 i)
    _ = (∑ i ∈ Λ, s i * ∑ j ∈ Λ, c i j * s j) + (t * R) * ∑ i ∈ Λ, s i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ R * ∑ i ∈ Λ, s i ^ 2 + (t * R) * ∑ i ∈ Λ, (1 + s i ^ 2) := by
        have := mul_le_mul_of_nonneg_left hs_sum (mul_nonneg ht0 hR0)
        linarith
    _ ≤ R * ∑ i ∈ Λ, (1 + s i ^ 2) + (t * R) * ∑ i ∈ Λ, (1 + s i ^ 2) := by
        have := mul_le_mul_of_nonneg_left hsq_le hR0
        linarith
    _ = R * (1 + t) * ∑ i ∈ Λ, (1 + s i ^ 2) := by ring

end GeneralPairBound


/-! ### Georgii §20.1: the Hamiltonians are defined on `Ω_*` -/

section Convergence

variable (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J)
include heven hJ0 hJ

/-- **The Hamiltonian series of a Heisenberg potential converges absolutely on `Ω_*`.** -/
theorem summable_abs_hamiltonianTerms_heisenbergPotential (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) :
    Summable fun A ↦ |(heisenbergPotential n J).hamiltonianTerms Λ ω A| := by
  classical
  obtain ⟨t, ht0, ht⟩ := exists_nonneg_sqrt_dotProduct_le_of_mem_slowGrowthTailSet hω
  refine (Function.Injective.summable_iff (g := sitePairFinset (d := d))
    injective_sitePairFinset fun A hA ↦ ?_).1 ?_
  · rw [hamiltonianTerms]
    by_cases hdisj : ¬ Disjoint A Λ
    · rw [Set.indicator_of_mem hdisj, heisenbergPotential_eq_zero_of_notMem_range hA, abs_zero]
    · rw [Set.indicator_of_notMem (by simpa using hdisj), abs_zero]
  · refine Summable.of_nonneg_of_le (fun p ↦ abs_nonneg _)
      (fun p ↦ abs_hamiltonianTerms_le_pairMajorant heven hJ0 Λ ω p)
      ((summable_pairMajorant heven hJ Λ ht).subtype
        (fun p ↦ Encodable.encode p.1 ≤ Encodable.encode p.2))

/-- **Georgii, §20.1 after (20.4).**  Under (20.4) — and Georgii's normalisation `J 0 = 0` and
evenness of `J` from (20.1) — the Hamiltonians `H_Λ^Φ(ω)` of the Heisenberg potential are
well-defined for every boundary condition `ω` in the tail event `Ω_*` of slowly increasing
configurations: the series `∑_{A ∩ Λ ≠ ∅} Φ_A(ω)` converges absolutely.

This is Georgii's Definition (2.2)(ii) restricted to `Ω_*`; absolute convergence is stronger than
his Convention (2.1), which is what `Potential.IsSummableOn` asks. -/
theorem isSummableOn_heisenbergPotential :
    Potential.IsSummableOn (heisenbergPotential n J) (slowGrowthTailSet d n) := fun Λ _ω hω ↦
  (Summable.of_abs (summable_abs_hamiltonianTerms_heisenbergPotential heven hJ0 hJ Λ hω)).volume

/-- The Hamiltonian on `Ω_*` is the unconditional sum of its interaction terms. -/
theorem hamiltonian_heisenbergPotential_eq_tsum (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) :
    (heisenbergPotential n J).hamiltonian Λ ω
      = ∑' A, (heisenbergPotential n J).hamiltonianTerms Λ ω A :=
  ((Summable.of_abs
    (summable_abs_hamiltonianTerms_heisenbergPotential heven hJ0 hJ Λ hω)).hasSum.volume).tsum_eq

end Convergence

/-! ### Georgii's estimate preceding (20.5) -/

section Estimate

/-- `∑_{j ∈ Λ} |J(i - j)| ≤ ‖J‖₀`. -/
private lemma sum_abs_sub_le_tsum (hJs : Summable fun m ↦ |J m|) (Λ : Finset (Fin d → ℤ))
    (i : Fin d → ℤ) : ∑ j ∈ Λ, |J (i - j)| ≤ ∑' m, |J m| := by
  have hre : Summable fun j ↦ |J (i - j)| :=
    ((Equiv.subLeft i).summable_iff (f := fun j ↦ |J (i - j)|)).1
      (by simpa [Function.comp_def, sub_sub_cancel] using hJs)
  have heq : (∑' j, |J (i - j)|) = ∑' m, |J m| := by
    have h := (Equiv.subLeft i).tsum_eq fun j ↦ |J (i - j)|
    simp only [Equiv.subLeft_apply, sub_sub_cancel] at h
    exact h.symm
  exact le_trans (hre.sum_le_tsum Λ fun j _ ↦ abs_nonneg _) (le_of_eq heq)

/-- `∑_{i ∈ Λ} |J(i - j)| ≤ ‖J‖₀`. -/
private lemma sum_abs_sub_le_tsum' (hJs : Summable fun m ↦ |J m|) (Λ : Finset (Fin d → ℤ))
    (j : Fin d → ℤ) : ∑ i ∈ Λ, |J (i - j)| ≤ ∑' m, |J m| := by
  have hre : Summable fun i ↦ |J (i - j)| :=
    ((Equiv.addRight j).summable_iff (f := fun i ↦ |J (i - j)|)).1
      (by simpa [Function.comp_def, add_sub_cancel_right] using hJs)
  have heq : (∑' i, |J (i - j)|) = ∑' m, |J m| := by
    have h := (Equiv.addRight j).tsum_eq fun i ↦ |J (i - j)|
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
    exact h.symm
  exact le_trans (hre.sum_le_tsum Λ fun i _ ↦ abs_nonneg _) (le_of_eq heq)

/-- **The Hamiltonian of a Heisenberg potential, bounded by its pair majorant.**  On the tail
event `Ω_*` the Hamiltonian series converges absolutely and

`|H_Λ^Φ(x)| ≤ 2 ∑_{i ∈ Λ} |x_i| ∑_j |J(i-j)| |x_j|`.

This is the majorant estimate of Georgii's §20.1 before any hypothesis on the *size* of the
configuration enters; `abs_hamiltonian_heisenbergPotential_le_of_exterior_le` turns it into his
`|H_Λ^Φ(ω)| ≤ c(ω_{S∖Λ}) ∑_{i ∈ Λ}[1 + |ω_i|²]`. -/
theorem abs_hamiltonian_heisenbergPotential_le_tsum (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ))
    {x : (Fin d → ℤ) → (Fin n → ℝ)} (hxΩ : x ∈ slowGrowthTailSet d n) :
    |(heisenbergPotential n J).hamiltonian Λ x|
      ≤ 2 * ∑ i ∈ Λ, Real.sqrt (x i ⬝ᵥ x i)
          * ∑' j, |J (i - j)| * Real.sqrt (x j ⬝ᵥ x j) := by
  classical
  obtain ⟨tx, htx0, htx⟩ := exists_nonneg_sqrt_dotProduct_le_of_mem_slowGrowthTailSet hxΩ
  set s : (Fin d → ℤ) → ℝ := fun i ↦ Real.sqrt (x i ⬝ᵥ x i) with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i ↦ Real.sqrt_nonneg _
  have hssq : ∀ i, s i ^ 2 = x i ⬝ᵥ x i := fun i ↦
    Real.sq_sqrt (Matrix.dotProduct_self_nonneg _)
  -- the interaction terms, their absolute summability, and the sum they define
  have habsSum := summable_abs_hamiltonianTerms_heisenbergPotential heven hJ0 hJ Λ hxΩ
  have hmajSum : Summable (pairMajorant J Λ x) := summable_pairMajorant heven hJ Λ htx
  have hfstSum : Summable (pairFst J Λ x) := summable_pairFst hJ Λ htx
  -- (1) the Hamiltonian is bounded by the sum of the absolute values of its terms
  have step₁ : |(heisenbergPotential n J).hamiltonian Λ x|
      ≤ ∑' A, |(heisenbergPotential n J).hamiltonianTerms Λ x A| := by
    rw [hamiltonian_heisenbergPotential_eq_tsum heven hJ0 hJ Λ hxΩ]
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := (heisenbergPotential n J).hamiltonianTerms Λ x)
        (by simpa [Real.norm_eq_abs] using habsSum)
  -- (2) transport the series to the pairs and compare with the majorant
  have hrange : ∀ A ∉ Set.range (sitePairFinset (d := d)),
      |(heisenbergPotential n J).hamiltonianTerms Λ x A| = 0 := by
    intro A hA
    rw [hamiltonianTerms]
    by_cases hdisj : ¬ Disjoint A Λ
    · rw [Set.indicator_of_mem hdisj, heisenbergPotential_eq_zero_of_notMem_range hA, abs_zero]
    · rw [Set.indicator_of_notMem (by simpa using hdisj), abs_zero]
  have hsupp : Function.support
      (fun A ↦ |(heisenbergPotential n J).hamiltonianTerms Λ x A|)
        ⊆ Set.range (sitePairFinset (d := d)) := by
    intro A hA
    by_contra hmem
    exact hA (hrange A hmem)
  have step₂ : ∑' A, |(heisenbergPotential n J).hamiltonianTerms Λ x A|
      ≤ ∑' q, pairMajorant J Λ x q := by
    rw [← injective_sitePairFinset.tsum_eq hsupp]
    refine le_trans (Summable.tsum_le_tsum
      (fun p ↦ abs_hamiltonianTerms_le_pairMajorant heven hJ0 Λ x p)
      (habsSum.comp_injective injective_sitePairFinset)
      (hmajSum.subtype fun p ↦ Encodable.encode p.1 ≤ Encodable.encode p.2)) ?_
    exact hmajSum.tsum_subtype_le _
      {p : (Fin d → ℤ) × (Fin d → ℤ) | Encodable.encode p.1 ≤ Encodable.encode p.2}
      fun q ↦ pairMajorant_nonneg q
  -- (3) the majorant is twice its first summand
  have step₃ : ∑' q, pairMajorant J Λ x q = 2 * ∑' q, pairFst J Λ x q := by
    have hswapSum : Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) ↦ pairFst J Λ x q.swap :=
      ((Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).summable_iff (f := pairFst J Λ x)).2 hfstSum
    have hswapEq : (∑' q : (Fin d → ℤ) × (Fin d → ℤ), pairFst J Λ x q.swap)
        = ∑' q, pairFst J Λ x q :=
      (Equiv.prodComm (Fin d → ℤ) (Fin d → ℤ)).tsum_eq (pairFst J Λ x)
    rw [tsum_congr (pairMajorant_eq_add heven Λ x), hfstSum.tsum_add hswapSum, hswapEq, two_mul]
  -- (4) the first summand, summed over the pairs
  have hTsum : ∀ i : Fin d → ℤ, Summable fun j ↦ |J (i - j)| * s j := by
    intro i
    have hmaj : Summable fun j ↦ |J (i - j)| * (tx * slowGrowth j) :=
      ((hJ.summable_sub' i).mul_left tx).congr fun j ↦ by ring
    exact Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (abs_nonneg _) (hs0 j))
      (fun j ↦ mul_le_mul_of_nonneg_left (htx j) (abs_nonneg _)) hmaj
  have hinner : ∀ i : Fin d → ℤ, (∑' j, pairFst J Λ x (i, j))
      = ((if i ∈ Λ then (1 : ℝ) else 0) * s i) * ∑' j, |J (i - j)| * s j := by
    intro i
    rw [← tsum_mul_left]
    exact tsum_congr fun j ↦ by simp only [pairFst, hs]; ring
  have step₄ : ∑' q, pairFst J Λ x q = ∑ i ∈ Λ, s i * ∑' j, |J (i - j)| * s j := by
    rw [hfstSum.tsum_prod]
    rw [tsum_congr hinner]
    rw [tsum_eq_sum (s := Λ) fun i hi ↦ by simp [hi]]
    exact Finset.sum_congr rfl fun i hi ↦ by simp only [hi, ite_true, one_mul]
  calc |(heisenbergPotential n J).hamiltonian Λ x|
      ≤ ∑' A, |(heisenbergPotential n J).hamiltonianTerms Λ x A| := step₁
    _ ≤ ∑' q, pairMajorant J Λ x q := step₂
    _ = 2 * ∑' q, pairFst J Λ x q := step₃
    _ = 2 * ∑ i ∈ Λ, s i * ∑' j, |J (i - j)| * s j := by rw [step₄]
    _ = 2 * ∑ i ∈ Λ, Real.sqrt (x i ⬝ᵥ x i)
          * ∑' j, |J (i - j)| * Real.sqrt (x j ⬝ᵥ x j) := by rw [hs]

/-- **Georgii's estimate preceding (20.5), uniformly over `Ω_t`.**  For a volume `Λ`, a level
`t ≥ 0` and *any* configuration `x` whose spins outside `Λ` satisfy `|x_j| ≤ t α(j)` — the spins
inside `Λ` being arbitrary —

`|H_Λ^Φ(x)| ≤ 2 R (1 + t) ∑_{i ∈ Λ}[1 + |x_i|²]`,  `R = ∑_{i ∈ Λ} ∑_j |J(i-j)| α(j)`.

The constant depends on the boundary condition only through the level `t`, which is Georgii's
`c(ω_{S∖Λ})` made uniform over `Ω_t`; this uniformity is what the comparison of the finite-volume
Gibbs kernels in the proof of (20.7) needs. -/
theorem abs_hamiltonian_heisenbergPotential_le_of_exterior_le (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ)) {t : ℝ} (ht0 : 0 ≤ t)
    {x : (Fin d → ℤ) → (Fin n → ℝ)} (hxΩ : x ∈ slowGrowthTailSet d n)
    (hext : ∀ j ∉ Λ, Real.sqrt (x j ⬝ᵥ x j) ≤ t * slowGrowth j) :
    |(heisenbergPotential n J).hamiltonian Λ x|
      ≤ 2 * ((∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j) * (1 + t))
        * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by
  classical
  set R : ℝ := ∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j with hR
  have hD0 : ∀ i : Fin d → ℤ, (0 : ℝ) ≤ ∑' j, |J (i - j)| * slowGrowth j := fun i ↦
    tsum_nonneg fun j ↦ mul_nonneg (abs_nonneg _) (slowGrowth_pos j).le
  have hR0 : (0 : ℝ) ≤ R := Finset.sum_nonneg fun i _ ↦ hD0 i
  have hrow : ∀ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j ≤ R := fun i hi ↦
    Finset.single_le_sum (f := fun i ↦ ∑' j, |J (i - j)| * slowGrowth j)
      (fun k _ ↦ hD0 k) hi
  have hkey := sum_mul_tsum_le_of_exterior_le (Λ := Λ) (c := fun i j ↦ |J (i - j)|)
    (s := fun i ↦ Real.sqrt (x i ⬝ᵥ x i)) (a := slowGrowth) (t := t) (R := R)
    (fun i j ↦ abs_nonneg _)
    (fun i j ↦ by rw [show j - i = -(i - j) by abel, heven])
    (fun i ↦ Real.sqrt_nonneg _) one_le_slowGrowth ht0 hR0
    (fun i ↦ hJ.summable_sub' i) hrow hext
  have hsq : ∀ i : Fin d → ℤ, Real.sqrt (x i ⬝ᵥ x i) ^ 2 = x i ⬝ᵥ x i := fun i ↦
    Real.sq_sqrt (Matrix.dotProduct_self_nonneg _)
  simp only [hsq] at hkey
  calc |(heisenbergPotential n J).hamiltonian Λ x|
      ≤ 2 * ∑ i ∈ Λ, Real.sqrt (x i ⬝ᵥ x i)
          * ∑' j, |J (i - j)| * Real.sqrt (x j ⬝ᵥ x j) :=
        abs_hamiltonian_heisenbergPotential_le_tsum heven hJ0 hJ Λ hxΩ
    _ ≤ 2 * (R * (1 + t) * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i)) := by linarith
    _ = 2 * (R * (1 + t)) * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by ring

/-- **Georgii's estimate preceding (20.5).**  For every finite volume `Λ` and every boundary
condition `ω ∈ Ω_*` there is a constant `c(ω_{S∖Λ}) < ∞` such that

`|H_Λ^Φ(x)| ≤ c(ω_{S∖Λ}) ∑_{i ∈ Λ} [1 + |x_i|²]`

for every configuration `x` agreeing with `ω` outside `Λ`.  Together with (20.3) this is what makes
the partition function `Z_Λ^Φ(ω)` finite.

The constant is `2 (∑_{i ∈ Λ} ∑_j |J(i-j)| α(j)) (1 + t)`, with `t` any bound in `Ω_*` for `ω`; it
depends on `ω` only through the exterior, as Georgii's notation `c(ω_{S∖Λ})` records. -/
theorem exists_abs_hamiltonian_heisenbergPotential_le (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : (Fin d → ℤ) → (Fin n → ℝ), (∀ i ∉ Λ, x i = ω i) →
      |(heisenbergPotential n J).hamiltonian Λ x| ≤ K * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by
  obtain ⟨t, ht0, ht⟩ := exists_nonneg_sqrt_dotProduct_le_of_mem_slowGrowthTailSet hω
  have hD0 : ∀ i : Fin d → ℤ, (0 : ℝ) ≤ ∑' j, |J (i - j)| * slowGrowth j := fun i ↦
    tsum_nonneg fun j ↦ mul_nonneg (abs_nonneg _) (slowGrowth_pos j).le
  refine ⟨2 * ((∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j) * (1 + t)), ?_, fun x hx ↦ ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j :=
      Finset.sum_nonneg fun i _ ↦ hD0 i
    nlinarith
  · exact abs_hamiltonian_heisenbergPotential_le_of_exterior_le heven hJ0 hJ Λ ht0
      (mem_slowGrowthTailSet_of_eqOn_compl (fun i hi ↦ (hx i hi).symm) hω)
      fun j hj ↦ by rw [hx j hj]; exact ht j

end Estimate

/-! ### Georgii (20.3): the partition functions are finite on `Ω_*` -/

section PartitionFunction

variable {ν : Measure (Fin n → ℝ)}

/-- **Georgii's `Z_Λ^Φ(ω) < ∞` of §20.1.**  The Hamiltonian estimate
`exists_abs_hamiltonian_heisenbergPotential_le` bounds the Boltzmann factor by a product of
one-site Gaussian weights, and (20.3) `HasExpSqMoments` makes each factor integrable. -/
theorem sigmaFiniteLambdaZ_tailBoltzmannFactor_ne_top [SigmaFinite ν]
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hJ : IsSlowlySummable J) (β : ℝ) (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) :
    Specification.sigmaFiniteLambdaZ (S := Fin d → ℤ) (E := Fin n → ℝ) ν
        ((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) β) Λ ω ≠ ⊤ := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_abs_hamiltonian_heisenbergPotential_le heven hJ0 hJ Λ hω
  set a : ℝ := |β| * K with ha
  have ha0 : 0 ≤ a := mul_nonneg (abs_nonneg _) hK0
  have hρmeas : Measurable
      ((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) β Λ) :=
    Potential.measurable_tailBoltzmannFactor measurableSet_slowGrowthTailSet
      (isSummableOn_heisenbergPotential heven hJ0 hJ) β Λ
  have hg : Measurable fun y : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (a * (1 + y ⬝ᵥ y))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.add (Finset.measurable_sum _ fun c _ ↦
        (measurable_pi_apply c).mul (measurable_pi_apply c))).const_mul _))
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hρmeas Measurable.juxt]
  have hbound : ∀ ζ : ↥Λ → (Fin n → ℝ),
      (heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) β Λ
          (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
        ≤ ∏ i : ↥Λ, ENNReal.ofReal (Real.exp (a * (1 + ζ i ⬝ᵥ ζ i))) := by
    intro ζ
    set y : (Fin d → ℤ) → (Fin n → ℝ) := juxt (Λ : Set (Fin d → ℤ)) ω ζ with hy
    have hagree : ∀ i ∉ Λ, y i = ω i := fun i hi ↦
      juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hi) ζ
    have hmemΩ : y ∈ slowGrowthTailSet d n :=
      mem_slowGrowthTailSet_of_eqOn_compl (fun i hi ↦ (hagree i hi).symm) hω
    have hsumeq : ∑ i ∈ Λ, (1 + y i ⬝ᵥ y i)
        = ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
      rw [← Finset.sum_coe_sort Λ fun i ↦ 1 + y i ⬝ᵥ y i]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have : y (i : Fin d → ℤ) = ζ i := by
        rw [hy, juxt_apply_of_mem (Finset.mem_coe.mpr i.2) ζ, Subtype.coe_eta]
      rw [this]
    have hHam := hK y hagree
    rw [Potential.tailBoltzmannFactor_of_mem _ _ hmemΩ, Potential.boltzmannFactor]
    have hexpbound : -β * (heisenbergPotential n J).hamiltonian Λ y
        ≤ a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
      calc -β * (heisenbergPotential n J).hamiltonian Λ y
          ≤ |(-β) * (heisenbergPotential n J).hamiltonian Λ y| := le_abs_self _
        _ = |β| * |(heisenbergPotential n J).hamiltonian Λ y| := by rw [abs_mul, abs_neg]
        _ ≤ |β| * (K * ∑ i ∈ Λ, (1 + y i ⬝ᵥ y i)) :=
            mul_le_mul_of_nonneg_left hHam (abs_nonneg β)
        _ = a * ∑ i ∈ Λ, (1 + y i ⬝ᵥ y i) := by rw [ha]; ring
        _ = a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by rw [hsumeq]
    calc ENNReal.ofReal (Real.exp (-β * (heisenbergPotential n J).hamiltonian Λ y))
        ≤ ENNReal.ofReal
            (Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hexpbound)
      _ = ∏ i : ↥Λ, ENNReal.ofReal (Real.exp (a * (1 + ζ i ⬝ᵥ ζ i))) := by
          rw [Finset.mul_sum, Real.exp_sum,
            ENNReal.ofReal_prod_of_nonneg fun i _ ↦ Real.exp_nonneg _]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
  refine ne_top_of_le_ne_top ?_ (le_of_eq (lintegral_pi_prod (ι := ↥Λ)
    (α := fun _ ↦ (Fin n → ℝ)) (fun _ ↦ ν)
    (g := fun _ (y : Fin n → ℝ) ↦ ENNReal.ofReal (Real.exp (a * (1 + y ⬝ᵥ y)))) fun _ ↦ hg))
  refine ENNReal.prod_ne_top fun i _ ↦ ?_
  have hint : Integrable (fun y : Fin n → ℝ ↦ Real.exp (a * (1 + y ⬝ᵥ y))) ν := by
    have hcongr : (fun y : Fin n → ℝ ↦ Real.exp (a * (1 + y ⬝ᵥ y)))
        = fun y ↦ Real.exp a * Real.exp (a * (y ⬝ᵥ y)) := by
      funext y
      rw [← Real.exp_add]
      ring_nf
    rw [hcongr]
    exact (hexp a).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y ↦ Real.exp_nonneg _)]
  exact ENNReal.ofReal_ne_top

end PartitionFunction

/-! ### Georgii (20.5): the Gibbsian specification `γ^Φ` and its Gibbs measures `𝒢(Φ)` -/

section GibbsSpecification

variable {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] [NeZero ν]

variable (J ν) in
/-- **Georgii, Definition (20.5).**  The Gibbsian specification of the Heisenberg potential
(20.1) over an unbounded spin space:

`γ_Λ^Φ(A | ω) = Z_Λ^Φ(ω)⁻¹ λ_Λ(1_A h_Λ^Φ | ω)` for `ω ∈ Ω_*`,  `δ_{0_Λ ω_{S∖Λ}}(A)` otherwise,

with `Ω_* = {sup_i |σ_i| / α(i) < ∞}` the tail event of §20.1.  The hypotheses are Georgii's:
(20.3) `HasExpSqMoments` on the a priori measure — which he assumes finite and non-degenerate, here
`[IsFiniteMeasure ν] [NeZero ν]` — and (20.4) `IsSlowlySummable J` together with the evenness and
normalisation `J 0 = 0` of `J` from (20.1).  Georgii's inverse temperature is absorbed into `Φ`; it
is the explicit parameter `β` here, as in `Potential.boltzmannFactor`. -/
def heisenbergSpecification (β : ℝ) (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J) : Specification (Fin d → ℤ) (Fin n → ℝ) :=
  Potential.tailGibbsSpecification (heisenbergPotential n J) (slowGrowthTailSet d n) ν β
    measurableSet_tail_slowGrowthTailSet (isSummableOn_heisenbergPotential heven hJ0 hJ)
    fun Λ _ω hω ↦ sigmaFiniteLambdaZ_tailBoltzmannFactor_ne_top hexp heven hJ0 hJ β Λ hω

variable {β : ℝ} {hexp : HasExpSqMoments ν} {heven : ∀ m, J (-m) = J m} {hJ0 : J 0 = 0}
  {hJ : IsSlowlySummable J}

/-- **The Gibbsian branch of (20.5).** -/
theorem heisenbergSpecification_apply_of_mem (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) {A : Set ((Fin d → ℤ) →
      (Fin n → ℝ))} (hA : MeasurableSet A) :
    heisenbergSpecification J ν β hexp heven hJ0 hJ Λ ω A
      = (∫⁻ x, (heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) β Λ x
            ∂(Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := Fin n → ℝ) ν Λ ω))⁻¹
        * ∫⁻ x in A, (heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) β Λ x
            ∂(Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := Fin n → ℝ) ν Λ ω) :=
  Potential.tailGibbsSpecification_apply_of_mem Λ hω hA

/-- **The artificial branch of (20.5).** -/
theorem heisenbergSpecification_apply_of_notMem (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∉ slowGrowthTailSet d n) :
    heisenbergSpecification J ν β hexp heven hJ0 hJ Λ ω
      = Measure.dirac (juxt (Λ : Set (Fin d → ℤ)) ω (0 : Λ → (Fin n → ℝ))) :=
  Potential.tailGibbsSpecification_apply_of_notMem Λ hω

variable (J ν β hexp heven hJ0 hJ) in
/-- **Georgii's `𝒢(Φ) ≜ 𝒢(γ^Φ)`** of §20.1: the Gibbs measures of the Heisenberg potential are by
definition those of its Gibbsian specification (20.5). -/
abbrev heisenbergGibbsMeasures : Set (Measure ((Fin d → ℤ) → (Fin n → ℝ))) :=
  G (heisenbergSpecification J ν β hexp heven hJ0 hJ)

/-- **Georgii's `μ(Ω_*) = 1` for all `μ ∈ 𝒢(Φ)`** of §20.1, in analogy with (13.19): "the
artificial part of the definition of `γ^Φ` has no effect on the associated class of Gibbs
measures". -/
theorem measure_slowGrowthTailSet_eq_one_of_mem_heisenbergGibbsMeasures
    {μ : Measure ((Fin d → ℤ) → (Fin n → ℝ))}
    (hμ : μ ∈ heisenbergGibbsMeasures J ν β hexp heven hJ0 hJ) :
    μ (slowGrowthTailSet d n) = 1 := by
  obtain ⟨hprob, hgibbs⟩ := hμ
  exact Potential.measure_eq_one_of_isGibbsMeasure_tailGibbsSpecification
    (measurableSet_singleton (0 : Fin n → ℝ)) zero_mem_slowGrowthTailSet hgibbs

end GibbsSpecification

end MeasureTheory.GibbsMeasure
