/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.OceanInter
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.OceanPart
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.LinearIndependentSeparated
public import GibbsMeasure.Mathlib.Probability.CondInvariant
public import GibbsMeasure.Model.LowEnergyOceans
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.InvariantDecomposition
public import GibbsMeasure.Specification.PeriodicGibbsSymmetry

/-!
# Georgii §18.2, (18.24)–(18.26): discrete symmetry breaking at low temperatures

Georgii, *Gibbs Measures and Phase Transitions*, §18.2.  Definition (18.23) — a `P`-stable
partition `{G_1, …, G_N}` of the local ground states of a `C`-potential, and its `Φ`-symmetry —
is `MeasureTheory.GibbsMeasure.IsPStablePartition` and
`MeasureTheory.GibbsMeasure.IsPhiSymmetric` in
`GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`, together with the transformation group
`T_{C,λ}` of (18.20)–(18.21), the symmetry subgroup `I_{C,λ}(Φ)` and Remark (18.22).  This file
carries out §18.2 from the display (18.24) to Theorem (18.25) in the plane `d = 2`, where the
plane `P` of (18.5) is the whole lattice and every face of `C` is a `P`-face.

## Main results

* `IsPStablePartition.eq_of_mem_latticePattern_add_single` — Georgii's argument after (18.23):
  two *adjacent* sites of the lattice see their cube configurations through the *same* member of
  the partition, because the two reflected cube views agree on a `P`-face
  (`tauPow_latticeCubeView_add_single_eq_on_face`) and the projections of the `G_n` to a `P`-face
  are disjoint.  `IsPStablePartition.exists_subset_latticePattern_of_connected` is the
  consequence: a *connected* subset of `⋃_n V(G_n, ω)` lies in a single `V(G_n, ω)`.
* `IsPStablePartition.exists_latticeOceanPart_nonempty` and its set form
  `IsPStablePartition.setOf_latticeOceanPart_nonempty_subset_iUnion` — **Georgii (18.24)**:
  `{ξ⁰_P(G_ε(Φ), ·) ≠ ∅} ⊆ ⋃_n {ξ⁰_P(G_n, ·) ≠ ∅}`;
  `IsPStablePartition.disjoint_setOf_latticeOceanPart_nonempty` is Georgii's remark that the
  sets on the right are pairwise disjoint, because two oceans always meet
  (`SimpleGraph.IsOceanIn.nonempty_inter`) while `V(G_m, ω)` and `V(G_n, ω)` are disjoint.
* `IsPStablePartition.latticeOceanPart_iUnion_eq`,
  `IsPStablePartition.setOf_latticeOceanPart_iUnion_nonempty_eq`,
  `IsPStablePartition.setOf_mem_latticeOceanPart_iUnion_eq` — the ocean of
  `G = G_1 ∪ ⋯ ∪ G_N` is the ocean of the single member that carries it, which is what turns
  Georgii's ratio `μ(0 ∈ ξ⁰_P(G_n, ·))/μ(A_n)` into `μ(0 ∈ ξ⁰_P(G, ·))/μ(ξ⁰_P(G, ·) ≠ ∅)`.
* `preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow`,
  `preimage_onLattice_setOf_latticeOceanPart_nonempty` — the two equivariances of the event
  `A(G) = {ξ⁰_P(G, ·) ≠ ∅}`: `θ_a^{-1} A(G) = A(r^a G)` and `τ^{-1} A(G) = A(τ_C^{-1} G)` for a
  cube transformation `τ`.  They give Georgii's shift group `Θ̃_n = {θ_i : r^i G_n = G_n}` and
  the transport of the events `A_n` into each other under `I_{C,λ}(Φ)`.  The underlying
  equivariances of (18.7) are `latticeOceanPart_shift_preimage_tauPow` and
  `latticeOceanPart_onLattice`, the latter through the fact that a cube isometry is an
  automorphism of both the nearest-neighbour and the `*`-neighbour graph of `ℤ^d`
  (`latticeGraph_adj_cubeIsoLin`, `starLatticeGraph_adj_cubeIsoLin`).
* The tail property `A(G) ∈ 𝒯` is `tail_measurableSet_setOf_latticeOceanPart_nonempty` of
  `GibbsMeasure/Model/LowEnergyOceans.lean`, for an *arbitrary* measurable `G ⊆ E^C`: the
  members of a stable partition are in general not `r`-symmetric — that is exactly why the
  shift group of (18.25)(ii) is the subgroup `Θ̃_n` and not all of `Θ`.
* `measure_setOf_latticeOceanPart_nonempty_eq`, `measure_setOf_zero_mem_latticeOceanPart_eq` —
  **Georgii's `μ(A_1) = ⋯ = μ(A_N)`**, from `Φ`-symmetry and Remark (18.22); and
  `measure_setOf_latticeOceanPart_nonempty_pos` — his `Σ_n μ(A_n) > 0`, hence `μ(A_n) > 0`.
* `exists_gibbsMeasure_family` — **Georgii, Theorem (18.25)**, assertions (i), (ii), (iii) and
  the distinctness, for the conditional measures `μ_n = μ(· | A_n)` of a fixed `μ ∈ 𝒢₀(Φ)`; its
  ingredients are the separate lemmas `isGibbsMeasure_cond_setOf_latticeOceanPart_nonempty`
  ((7.7)(b)), `cond_apply_self_setOf_latticeOceanPart_nonempty` (the first half of (i)),
  `le_cond_measure_setOf_zero_mem_latticeOceanPart` (the second half),
  `mutuallySingular_cond_setOf_latticeOceanPart_nonempty` (distinctness),
  `measurePreserving_shift_cond_setOf_latticeOceanPart_nonempty` and
  `measurePreserving_onLattice_cond_setOf_latticeOceanPart_nonempty` ((ii)),
  `map_onLattice_cond_setOf_latticeOceanPart_nonempty` and
  `map_shift_cond_setOf_latticeOceanPart_nonempty` ((iii) and its last sentence).
* `exists_gibbsMeasure_family_of_crossingBound_lt_one` — the theorem with Georgii's explicit
  threshold `δ(β) = 4 z(t(G_ε(Φ), βΦ)) < 1`, which is his **Comment (18.26)(1)**: the upper
  critical inverse temperature is at most any `β₀` with `δ(β) < 1` for all `β ≥ β₀`; and
  `eventually_exists_gibbsMeasure_family` — **Theorem (18.25) as stated**, "if `β` is
  sufficiently large".

## Deviations from Georgii's statement

* Georgii's `Φ`-stable partition is a partition of the local ground states *of `Φ`*, while his
  conclusion is about `βΦ`.  Only condition (18.23)(a)(ii) — which does not mention the potential
  at all — is used in the construction, so `exists_gibbsMeasure_family` takes the partition of a
  potential `φ₀` which is unrelated to the potential `φ` of `𝒢₀(φ)`; the low-temperature
  corollaries instantiate `φ₀ = Φ` and `φ = βΦ`.  `IsPhiSymmetric.const_mul` is the transfer of
  (18.23)(b) from `Φ` to `βΦ`, i.e. `I_{C,λ}(Φ) ⊆ I_{C,λ}(βΦ)`.
* The last statement of (18.25), `|ex 𝒢_Θ̃(βΦ)| ≥ N`, is proved here only for `Θ̃ = Θ`, i.e. when
  every `G_n` is `r`-symmetric: that is
  `le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric`, from Corollary (14.18) for the
  shift group (`le_encard_extremePoints_invariantG_shiftGroup_iff`) and the linear independence
  of measures separated by disjoint events
  (`linearIndependent_of_measure_eq_one_of_measure_eq_zero`).  For a partition which is not
  `r`-symmetric Georgii's `Θ̃ = ⋂_n Θ̃_n` is a proper subgroup of `Θ` containing `2ℤ²`, and he
  appeals to the remark below Corollary (14.18) — that (14.10), (14.17) and (14.18) hold for any
  finitely generated abelian subgroup of `T` containing a non-trivial shift.  The tree has (14.18)
  for a subgroup `Θ` only given a `(𝓟_Θ, 𝓘)`-kernel (`le_encard_extremePoints_invariantG_iff`),
  and such a kernel is constructed only for the *full* shift group; the missing input is the
  `(𝓟_Θ̃, 𝓘)`-kernel of a finite-index subgroup of the shifts, which belongs in
  `GibbsMeasure/Specification/InvariantDecomposition.lean`.  The measure-theoretic half of the
  count — the mutual singularity of `μ_1, …, μ_N` — is unconditional
  (`mutuallySingular_cond_setOf_latticeOceanPart_nonempty`).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E]

/-! ### Adjacent sites of the lattice -/

/-- A nearest neighbour of `x` in `ℤ^d` is `x ± e_k` for exactly one direction `k`. -/
lemma exists_add_single_of_latticeGraph_adj {d : ℕ} {x y : Fin d → ℤ}
    (hxy : (latticeGraph d).Adj x y) :
    ∃ k : Fin d, y = x + Pi.single k 1 ∨ x = y + Pi.single k 1 := by
  classical
  obtain ⟨k, s, hs, rfl⟩ := latticeGraph_adj_decomp hxy
  refine ⟨k, ?_⟩
  rcases hs with rfl | rfl
  · refine Or.inl (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl; simp
    · simp [Function.update_of_ne hl, Pi.single_eq_of_ne hl]
  · refine Or.inr (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl; simp
    · simp [Function.update_of_ne hl, Pi.single_eq_of_ne hl]

/-! ### Georgii, the argument after (18.23) -/

section Partition

variable {d : ℕ} {ι : Type*} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} {P : Set (Fin d)}
  {G : ι → Set ((Fin d → Fin 2) → E)}

/-- **Georgii, the argument after Definition (18.23).**  If `i` and `i + e_k` both show a pattern
of the family, and `k` is a direction of `P`, then it is the *same* member of the family: the
reflected cube views `r^i (θ_{-i} ω)_C` and `r^{i + e_k} (θ_{-i-e_k} ω)_C` agree on the `P`-face
`{c ∈ C : c_k = 1 - parity(i)_k}` of `C`, and by (18.23)(a)(ii) the projections of the `G_n` to
that face are disjoint. -/
theorem IsPStablePartition.eq_of_mem_latticePattern_add_single (h : IsPStablePartition φ ν P G)
    {k : Fin d} (hk : k ∈ P) {m n : ι} {ω : (Fin d → ℤ) → E} {i : Fin d → ℤ}
    (hm : i ∈ latticePattern E (G m) ω)
    (hn : i + Pi.single k 1 ∈ latticePattern E (G n) ω) : m = n := by
  refine h.eq_of_faceRestrict_eq hk (a := latticeParity i k + 1) (mem_latticePattern.1 hm)
    (mem_latticePattern.1 hn) ?_
  funext c
  exact (tauPow_latticeCubeView_add_single_eq_on_face ω i k c.2).symm

/-- Two members of a `P`-stable partition sharing a site of their patterns are the same
member. -/
theorem IsPStablePartition.eq_of_mem_latticePattern (h : IsPStablePartition φ ν P G)
    (hP : P.Nonempty) {m n : ι} {ω : (Fin d → ℤ) → E} {i : Fin d → ℤ}
    (hm : i ∈ latticePattern E (G m) ω) (hn : i ∈ latticePattern E (G n) ω) : m = n := by
  by_contra hmn
  exact Set.disjoint_left.1 (h.pairwise_disjoint hP hmn) (mem_latticePattern.1 hm)
    (mem_latticePattern.1 hn)

/-- **Georgii, the argument after Definition (18.23)**, in the plane: two `latticeGraph`-adjacent
sites of `⋃_n V(G_n, ω)` belong to the same `V(G_n, ω)`. -/
theorem IsPStablePartition.eq_of_adj (h : IsPStablePartition φ ν Set.univ G) {m n : ι}
    {ω : (Fin d → ℤ) → E} {i j : Fin d → ℤ} (hij : (latticeGraph d).Adj i j)
    (hm : i ∈ latticePattern E (G m) ω) (hn : j ∈ latticePattern E (G n) ω) : m = n := by
  obtain ⟨k, hk | hk⟩ := exists_add_single_of_latticeGraph_adj hij
  · exact h.eq_of_mem_latticePattern_add_single (Set.mem_univ k) hm (hk ▸ hn)
  · exact (h.eq_of_mem_latticePattern_add_single (Set.mem_univ k) hn (hk ▸ hm)).symm

/-- **A connected subset of `⋃_n V(G_n, ω)` lies in a single `V(G_n, ω)`** — Georgii's
"each connected subset of `V_P(G_ε(Φ), ω)` is a subset of `V_P(G_n, ω)` for some `n`". -/
theorem IsPStablePartition.exists_subset_latticePattern_of_connected
    (h : IsPStablePartition φ ν Set.univ G) [Nonempty (Fin d)] {ω : (Fin d → ℤ) → E}
    {ξ : Set (Fin d → ℤ)} (hξ : ((latticeGraph d).induce ξ).Connected)
    (hsub : ξ ⊆ ⋃ n, latticePattern E (G n) ω) :
    ∃ n, ξ ⊆ latticePattern E (G n) ω := by
  have hPne : (Set.univ : Set (Fin d)).Nonempty := Set.univ_nonempty
  set f : (Fin d → ℤ) → Set ι := fun i ↦ {n | i ∈ latticePattern E (G n) ω} with hf
  have hadj : ∀ ⦃a b : Fin d → ℤ⦄, a ∈ ξ → b ∈ ξ → (latticeGraph d).Adj a b → f a = f b := by
    intro a b ha hb hab
    obtain ⟨-, ⟨m, rfl⟩, hma⟩ := hsub ha
    obtain ⟨-, ⟨n, rfl⟩, hnb⟩ := hsub hb
    have hmn : m = n := h.eq_of_adj hab hma hnb
    subst hmn
    ext p
    exact ⟨fun hp ↦ (h.eq_of_mem_latticePattern hPne hp hma) ▸ hnb,
      fun hp ↦ (h.eq_of_mem_latticePattern hPne hp hnb) ▸ hma⟩
  obtain ⟨x, hx⟩ := hξ.induce_nonempty
  obtain ⟨-, ⟨m, rfl⟩, hxm⟩ := hsub hx
  refine ⟨m, fun y hy ↦ ?_⟩
  have hfyx : f y = f x := SimpleGraph.Reachable.induce_apply_eq_of_forall_adj (f := f) hadj
    (u := (⟨y, hy⟩ : ξ)) (v := (⟨x, hx⟩ : ξ)) (hξ.preconnected _ _)
  have hmem : m ∈ f x := hxm
  rw [← hfyx] at hmem
  exact hmem

end Partition

/-! ### Georgii (18.24) in the plane -/

section Plane

open Peierls

variable {ι : Type*} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E}
  {G : ι → Set ((Fin 2 → Fin 2) → E)} {W W' : Set ((Fin 2 → Fin 2) → E)}

/-- The plane minus a finite set percolates in the `*`-neighbour graph: the hypothesis under
which an ocean of the plane is infinite and `ξ⁰_P` is the maximal ocean. -/
theorem nonempty_infiniteClusters_univ_diff_star (F : Set Peierls.Site) (hF : F.Finite) :
    ((starLatticeGraph 2).infiniteClusters (Set.univ \ F)).Nonempty :=
  Peierls.nonempty_infiniteClusters_univ_diff (latticeGraph_le_starLatticeGraph 2) hF

/-- **Georgii (18.7) is monotone in the pattern**: a larger pattern set has a larger maximal
ocean, because an ocean of `V(W, ω)` is an ocean of `V(W', ω)`. -/
theorem latticeOceanPart_mono (hWW' : W ⊆ W') (ω : (Fin 2 → ℤ) → E) :
    latticeOceanPart E W ω ⊆ latticeOceanPart E W' ω :=
  SimpleGraph.oceanPart_mono (latticeGraph_le_starLatticeGraph 2)
    nonempty_infiniteClusters_univ_diff_star (fun _ hi ↦ hWW' hi) (Set.subset_univ _)

/-- **Georgii (18.24).**  If `W` is covered by the members of a stable partition then a
configuration whose pattern `V(W, ·)` carries an ocean has some `V(G_n, ·)` carrying an ocean:
the ocean is connected, hence contained in a single `V(G_n, ·)`, where it is again an ocean. -/
theorem IsPStablePartition.exists_latticeOceanPart_nonempty
    (h : IsPStablePartition φ ν Set.univ G) (hW : W ⊆ ⋃ n, G n) {ω : (Fin 2 → ℤ) → E}
    (hne : (latticeOceanPart E W ω).Nonempty) : ∃ n, (latticeOceanPart E (G n) ω).Nonempty := by
  obtain ⟨ξ, hξW, hξ⟩ := (latticeOceanPart_nonempty_iff (G := W) ω).1 hne
  have hVsub : latticePattern E W ω ⊆ ⋃ n, latticePattern E (G n) ω := by
    intro i hi
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hW (mem_latticePattern.1 hi))
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  obtain ⟨n, hn⟩ :=
    h.exists_subset_latticePattern_of_connected hξ.connected (hξW.trans hVsub)
  exact ⟨n, (Peierls.oceanPart_nonempty_iff_exists_isOceanIn _).2 ⟨ξ, hn, hξ⟩⟩

/-- **Georgii (18.24)** as the displayed inclusion of events:
`{ξ⁰_P(G_ε(Φ), ·) ≠ ∅} ⊆ ⋃_n {ξ⁰_P(G_n, ·) ≠ ∅}`. -/
theorem IsPStablePartition.setOf_latticeOceanPart_nonempty_subset_iUnion
    (h : IsPStablePartition φ ν Set.univ G) (hW : W ⊆ ⋃ n, G n) :
    {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E W ω).Nonempty}
      ⊆ ⋃ n, {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty} :=
  fun _ hω ↦ Set.mem_iUnion.2 (h.exists_latticeOceanPart_nonempty hW hω)

/-- **Georgii's remark after (18.24)**: the events `{ξ⁰_P(G_n, ·) ≠ ∅}` are pairwise disjoint.
Two oceans of the plane always meet (`SimpleGraph.IsOceanIn.nonempty_inter`), while a common
site of `V(G_m, ω)` and `V(G_n, ω)` would put one cube configuration in both `G_m` and `G_n`. -/
theorem IsPStablePartition.disjoint_setOf_latticeOceanPart_nonempty
    (h : IsPStablePartition φ ν Set.univ G) {m n : ι} (hmn : m ≠ n) :
    Disjoint {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G m) ω).Nonempty}
      {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty} := by
  refine Set.disjoint_left.2 fun ω hm hn ↦ hmn ?_
  obtain ⟨i, him, hin⟩ := SimpleGraph.IsOceanIn.nonempty_inter
    (latticeGraph_le_starLatticeGraph 2) nonempty_infiniteClusters_univ_diff_star
    (SimpleGraph.isOceanIn_oceanPart_of_nonempty hm)
    (SimpleGraph.isOceanIn_oceanPart_of_nonempty hn)
  exact h.eq_of_mem_latticePattern Set.univ_nonempty
    (SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset him))
    (SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hin))

/-- **The ocean of `G = G_1 ∪ ⋯ ∪ G_N` is the ocean of the single member that carries it.**
This is what makes Georgii's identity `μ(0 ∈ ξ⁰_P(G_n, ·))/μ(A_n) = μ(0 ∈ ξ⁰_P(G, ·))/μ(A)`
work. -/
theorem IsPStablePartition.latticeOceanPart_iUnion_eq (h : IsPStablePartition φ ν Set.univ G)
    {ω : (Fin 2 → ℤ) → E} {n : ι} (hn : (latticeOceanPart E (G n) ω).Nonempty) :
    latticeOceanPart E (⋃ m, G m) ω = latticeOceanPart E (G n) ω := by
  have hmono := latticeOceanPart_mono (E := E) (Set.subset_iUnion G n) ω
  refine Set.Subset.antisymm ?_ hmono
  have hune : (latticeOceanPart E (⋃ m, G m) ω).Nonempty := hn.mono hmono
  have hocean := SimpleGraph.isOceanIn_oceanPart_of_nonempty hune
  have hsub : latticeOceanPart E (⋃ m, G m) ω ⊆ ⋃ m, latticePattern E (G m) ω := by
    intro i hi
    have hiV : i ∈ latticePattern E (⋃ m, G m) ω :=
      SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hi)
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (mem_latticePattern.1 hiV)
    exact Set.mem_iUnion.2 ⟨m, hm⟩
  obtain ⟨p, hp⟩ := h.exists_subset_latticePattern_of_connected hocean.connected hsub
  obtain ⟨i, hi⟩ := hn
  have hpn : p = n := h.eq_of_mem_latticePattern Set.univ_nonempty (hp (hmono hi))
    (SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hi))
  subst hpn
  exact SimpleGraph.IsOceanIn.subset_oceanPart (latticeGraph_le_starLatticeGraph 2)
    nonempty_infiniteClusters_univ_diff_star hocean hp (Set.subset_univ _)

/-- The event that `G = G_1 ∪ ⋯ ∪ G_N` carries an ocean is the disjoint union of the events
`A_n = {ξ⁰_P(G_n, ·) ≠ ∅}`. -/
theorem IsPStablePartition.setOf_latticeOceanPart_iUnion_nonempty_eq
    (h : IsPStablePartition φ ν Set.univ G) :
    {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (⋃ n, G n) ω).Nonempty}
      = ⋃ n, {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty} := by
  refine Set.Subset.antisymm (h.setOf_latticeOceanPart_nonempty_subset_iUnion Set.Subset.rfl) ?_
  refine Set.iUnion_subset fun n ω hω ↦ ?_
  exact hω.mono (latticeOceanPart_mono (E := E) (Set.subset_iUnion G n) ω)

/-- The event that a site lies in the ocean of `G = G_1 ∪ ⋯ ∪ G_N` is the union of the events
that it lies in the ocean of a single member. -/
theorem IsPStablePartition.setOf_mem_latticeOceanPart_iUnion_eq
    (h : IsPStablePartition φ ν Set.univ G) (i : Peierls.Site) :
    {ω : (Fin 2 → ℤ) → E | i ∈ latticeOceanPart E (⋃ n, G n) ω}
      = ⋃ n, {ω : (Fin 2 → ℤ) → E | i ∈ latticeOceanPart E (G n) ω} := by
  refine Set.Subset.antisymm (fun ω hω ↦ ?_) (Set.iUnion_subset fun n ω hω ↦ ?_)
  · obtain ⟨n, hn⟩ := h.exists_latticeOceanPart_nonempty (W := ⋃ n, G n) Set.Subset.rfl ⟨i, hω⟩
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    have : i ∈ latticeOceanPart E (⋃ m, G m) ω := hω
    rwa [h.latticeOceanPart_iUnion_eq hn] at this
  · exact latticeOceanPart_mono (E := E) (Set.subset_iUnion G n) ω hω

end Plane

/-! ### The equivariance of `{ξ⁰_P(G, ·) ≠ ∅}` -/

section Equivariance

variable {d : ℕ}

lemma natAbs_signMul_sub (b : Bool) (a c : ℤ) :
    (signMul b a - signMul b c).natAbs = (a - c).natAbs := by
  cases b
  · simp
  · simp only [signMul_true]; omega

lemma abs_signMul_sub (b : Bool) (a c : ℤ) : |signMul b a - signMul b c| = |a - c| := by
  cases b
  · simp
  · simp only [signMul_true]; rw [neg_sub_neg, abs_sub_comm]

/-- **A cube isometry is an automorphism of the nearest-neighbour graph of `ℤ^d`**: it permutes
the coordinates and changes signs, which leaves the `ℓ¹`-distance alone. -/
lemma latticeGraph_adj_cubeIsoLin (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (x y : Fin d → ℤ) :
    (latticeGraph d).Adj (cubeIsoLin π ε x) (cubeIsoLin π ε y) ↔ (latticeGraph d).Adj x y := by
  have hsum : ∑ k, (cubeIsoLin π ε x k - cubeIsoLin π ε y k).natAbs
      = ∑ l, (x l - y l).natAbs := by
    rw [← Equiv.sum_comp π fun l ↦ (x l - y l).natAbs]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [cubeIsoLin_apply, cubeIsoLin_apply, natAbs_signMul_sub]
  constructor
  · intro h
    have h1 : ∑ k, (cubeIsoLin π ε x k - cubeIsoLin π ε y k).natAbs = 1 := h
    change ∑ l, (x l - y l).natAbs = 1
    rw [← hsum]; exact h1
  · intro h
    have h1 : ∑ l, (x l - y l).natAbs = 1 := h
    change ∑ k, (cubeIsoLin π ε x k - cubeIsoLin π ε y k).natAbs = 1
    rw [hsum]; exact h1

/-- **A cube isometry is an automorphism of the `*`-neighbour graph of `ℤ^d`**: it permutes the
coordinates and changes signs, which leaves the `ℓ^∞`-distance alone. -/
lemma starLatticeGraph_adj_cubeIsoLin (π : Equiv.Perm (Fin d)) (ε : Fin d → Bool)
    (x y : Fin d → ℤ) :
    (starLatticeGraph d).Adj (cubeIsoLin π ε x) (cubeIsoLin π ε y) ↔
      (starLatticeGraph d).Adj x y := by
  rw [starLatticeGraph_adj, starLatticeGraph_adj]
  have habs : ∀ k, |cubeIsoLin π ε x k - cubeIsoLin π ε y k| = |x (π k) - y (π k)| := fun k ↦ by
    rw [cubeIsoLin_apply, cubeIsoLin_apply, abs_signMul_sub]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨fun hxy ↦ hne (by rw [hxy]), fun l ↦ ?_⟩
    have hl := h (π.symm l)
    rwa [habs, Equiv.apply_symm_apply] at hl
  · rintro ⟨hne, h⟩
    exact ⟨fun hxy ↦ hne ((cubeIsoLin π ε).injective hxy), fun k ↦ by rw [habs]; exact h _⟩

/-- **Georgii (18.7) is equivariant under the cube transformations**:
`ξ⁰_P(G, τ ω) = τ_*(ξ⁰_P(τ_C^{-1} G, ω))`. -/
theorem latticeOceanPart_onLattice (τ : CubeTransformation E 2)
    (W : Set ((Fin 2 → Fin 2) → E)) (ω : (Fin 2 → ℤ) → E) :
    latticeOceanPart E W ((τ.onLattice E).toFun ω)
      = τ.lin '' latticeOceanPart E (τ.onCube.toFun ⁻¹' W) ω := by
  have hR : ⇑τ.lin.toEquiv '' (Set.univ : Set (Fin 2 → ℤ)) = Set.univ := by
    rw [Set.image_univ]; exact τ.lin.toEquiv.surjective.range_eq
  have h := SimpleGraph.oceanPart_image (G := latticeGraph 2) (H := starLatticeGraph 2)
    (R := Set.univ) (e := τ.lin.toEquiv)
    (fun a b ↦ latticeGraph_adj_cubeIsoLin τ.perm τ.sign a b)
    (fun a b ↦ starLatticeGraph_adj_cubeIsoLin τ.perm τ.sign a b) hR
    (latticePattern E (τ.onCube.toFun ⁻¹' W) ω)
  rw [latticeOceanPart, latticeOceanPart, τ.latticePattern_onLattice]
  simpa using h

/-- **Georgii (18.7) under the shift**: `ξ⁰_P(G, θ_a ω) = ξ⁰_P(r^a G, ω) + a`. -/
theorem latticeOceanPart_shift_preimage_tauPow (W : Set ((Fin 2 → Fin 2) → E))
    (a : Fin 2 → ℤ) (ω : (Fin 2 → ℤ) → E) :
    latticeOceanPart E W ((shift E a).toFun ω)
      = (· + a) '' latticeOceanPart E (tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' W) ω := by
  rw [latticeOceanPart, latticeOceanPart, latticePattern_shift_preimage_tauPow,
    Peierls.oceanPart_image_add_right]

/-- **The event `A(G) = {ξ⁰_P(G, ·) ≠ ∅}` under the shift**: `θ_a^{-1} A(G) = A(r^a G)`.  For
`r^a G = G` — Georgii's shift group `Θ̃ = {θ_i : r^i G = G}` of (18.25)(ii) — the event is
shift invariant. -/
theorem preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow (W : Set ((Fin 2 → Fin 2) → E))
    (a : Fin 2 → ℤ) :
    (shift E a).toFun ⁻¹' {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E W ω).Nonempty}
      = {ω : (Fin 2 → ℤ) → E |
          (latticeOceanPart E (tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' W) ω).Nonempty} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    latticeOceanPart_shift_preimage_tauPow W a ω, Set.image_nonempty]

/-- **The event that a site lies in the ocean, under the shift**. -/
theorem preimage_shift_setOf_mem_latticeOceanPart (W : Set ((Fin 2 → Fin 2) → E))
    (a : Fin 2 → ℤ) (i : Peierls.Site) :
    (shift E a).toFun ⁻¹' {ω : (Fin 2 → ℤ) → E | i ∈ latticeOceanPart E W ω}
      = {ω : (Fin 2 → ℤ) → E |
          i - a ∈ latticeOceanPart E (tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' W) ω} := by
  ext ω
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    latticeOceanPart_shift_preimage_tauPow W a ω]
  constructor
  · rintro ⟨j, hj, rfl⟩; simpa using hj
  · exact fun h ↦ ⟨i - a, h, sub_add_cancel i a⟩

/-- **The event `A(G) = {ξ⁰_P(G, ·) ≠ ∅}` under a cube transformation**:
`τ^{-1} A(G) = A(τ_C^{-1} G)`. -/
theorem preimage_onLattice_setOf_latticeOceanPart_nonempty (τ : CubeTransformation E 2)
    (W : Set ((Fin 2 → Fin 2) → E)) :
    (τ.onLattice E).toFun ⁻¹' {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E W ω).Nonempty}
      = {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (τ.onCube.toFun ⁻¹' W) ω).Nonempty} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, latticeOceanPart_onLattice τ W ω,
    Set.image_nonempty]

/-- **The event that the origin lies in the ocean, under a cube transformation.**  The spatial
part fixes the origin, so `τ^{-1} {0 ∈ ξ⁰_P(G, ·)} = {0 ∈ ξ⁰_P(τ_C^{-1} G, ·)}`. -/
theorem preimage_onLattice_setOf_zero_mem_latticeOceanPart (τ : CubeTransformation E 2)
    (W : Set ((Fin 2 → Fin 2) → E)) :
    (τ.onLattice E).toFun ⁻¹'
        {ω : (Fin 2 → ℤ) → E | (0 : Peierls.Site) ∈ latticeOceanPart E W ω}
      = {ω : (Fin 2 → ℤ) → E |
          (0 : Peierls.Site) ∈ latticeOceanPart E (τ.onCube.toFun ⁻¹' W) ω} := by
  ext ω
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, latticeOceanPart_onLattice τ W ω]
  constructor
  · rintro ⟨j, hj, hj0⟩
    have hj0' : j = 0 := τ.lin.injective (by rw [hj0, map_zero])
    rwa [hj0'] at hj
  · exact fun h ↦ ⟨0, h, map_zero _⟩

end Equivariance


/-! ### Georgii, the proof of Theorem (18.25) -/

section Theorem1825

open Peierls

variable {ι : Type*} {φ φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {G : ι → Set ((Fin 2 → Fin 2) → E)} {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)}

/-- **Georgii's `μ(A_1) = ⋯ = μ(A_N)`.**  For a `Φ`-symmetric family the events
`A_n = {ξ⁰_P(G_n, ·) ≠ ∅}` are carried into each other by transformations of `I_{C,λ}(Φ)`, and
every `μ ∈ 𝒢₀(Φ)` is invariant under those by Remark (18.22). -/
theorem measure_setOf_latticeOceanPart_nonempty_eq (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hsym : IsPhiSymmetric φ ν G) (hμ : μ ∈ GZero E φ ν) (m n : ι) :
    (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (latticeOceanPart E (G m) ω).Nonempty}
      = (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (latticeOceanPart E (G n) ω).Nonempty} := by
  obtain ⟨τ, hτ, himg⟩ := hsym m n
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' G n = G m := by rw [← himg, Set.preimage_image_eq _ hinj]
  have hmp := hτ.measurePreserving_onLattice_of_mem_GZero hφ hM hμ
  have h := hmp.measure_preimage_emb (τ.onLattice E).toMeasurableEquiv.measurableEmbedding
    {ω | (latticeOceanPart E (G n) ω).Nonempty}
  rwa [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre] at h

/-- **Georgii's `μ(0 ∈ ξ⁰_P(G_1, ·)) = ⋯ = μ(0 ∈ ξ⁰_P(G_N, ·))`.**  The spatial part of a cube
transformation fixes the origin, so the same argument applies to the events that the origin lies
in the ocean. -/
theorem measure_setOf_zero_mem_latticeOceanPart_eq (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hsym : IsPhiSymmetric φ ν G) (hμ : μ ∈ GZero E φ ν) (m n : ι) :
    (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticeOceanPart E (G m) ω}
      = (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω} := by
  obtain ⟨τ, hτ, himg⟩ := hsym m n
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' G n = G m := by rw [← himg, Set.preimage_image_eq _ hinj]
  have hmp := hτ.measurePreserving_onLattice_of_mem_GZero hφ hM hμ
  have h := hmp.measure_preimage_emb (τ.onLattice E).toMeasurableEquiv.measurableEmbedding
    {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}
  rwa [preimage_onLattice_setOf_zero_mem_latticeOceanPart, hpre] at h

/-- **Georgii's `Σ_n μ(A_n) > 0`, hence `μ(A_n) > 0` for every `n`.**  By (18.24) the events
`A_n` cover the event that `G_1 ∪ ⋯ ∪ G_N` carries an ocean, which has positive mass; by
`Φ`-symmetry they all have the same mass. -/
theorem measure_setOf_latticeOceanPart_nonempty_pos [Countable ι] (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hsym : IsPhiSymmetric φ ν G) (hμ : μ ∈ GZero E φ ν)
    (hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty}) (n : ι) :
    0 < (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (latticeOceanPart E (G n) ω).Nonempty} := by
  rw [pos_iff_ne_zero]
  intro h0
  refine hpos.ne' ?_
  rw [hpart.setOf_latticeOceanPart_iUnion_nonempty_eq]
  refine measure_iUnion_null fun m ↦ ?_
  rw [measure_setOf_latticeOceanPart_nonempty_eq hφ hM hsym hμ m n, h0]

/-- **Georgii's estimate of `μ_n(0 ∈ ξ⁰_P(G_n, ·))`**, the computation at the end of his proof of
(18.25): `μ_n(0 ∈ ξ⁰_P(G_n, ·)) = μ(0 ∈ ξ⁰_P(G, ·))/μ(ξ⁰_P(G, ·) ≠ ∅) ≥ μ(0 ∈ ξ⁰_P(G, ·))`,
where `G = G_1 ∪ ⋯ ∪ G_N`.  Both numerator and denominator split into `N` equal pieces, and the
denominator is at most `1`. -/
theorem le_cond_measure_setOf_zero_mem_latticeOceanPart [Finite ι] (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hsym : IsPhiSymmetric φ ν G) (hμ : μ ∈ GZero E φ ν)
    (hAmeas : ∀ n, MeasurableSet {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty})
    (hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty}) (n : ι) :
    (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}
      ≤ ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}])
          {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω} := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set ρ := (μ : Measure ((Fin 2 → ℤ) → E)) with hρ
  set A : ι → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (latticeOceanPart E (G m) ω).Nonempty} with hA
  set C : ι → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (0 : Site) ∈ latticeOceanPart E (G m) ω} with hC
  have hCA : ∀ m, C m ⊆ A m := fun m ω hω ↦ ⟨0, hω⟩
  have ha0 : ρ (A n) ≠ 0 :=
    (measure_setOf_latticeOceanPart_nonempty_pos hφ hM hpart hsym hμ hpos n).ne'
  have haTop : ρ (A n) ≠ ∞ := measure_ne_top _ _
  -- the numerator: `μ(0 ∈ ξ⁰_P(G, ·)) ≤ N μ(0 ∈ ξ⁰_P(G_n, ·))`
  have hnum : ρ {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}
      ≤ (Fintype.card ι : ℝ≥0∞) * ρ (C n) := by
    rw [hpart.setOf_mem_latticeOceanPart_iUnion_eq 0]
    have hUn : (⋃ m : ι, C m) = ⋃ m ∈ (Finset.univ : Finset ι), C m := by simp
    refine (hUn ▸ measure_biUnion_finset_le (μ := ρ) Finset.univ C).trans_eq ?_
    rw [Finset.sum_congr rfl fun m _ ↦
      measure_setOf_zero_mem_latticeOceanPart_eq hφ hM hsym hμ m n,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the denominator: `N μ(A_n) = μ(⋃ A_m) ≤ 1`
  have hden : (Fintype.card ι : ℝ≥0∞) * ρ (A n) ≤ 1 := by
    have hUn : (⋃ m : ι, A m) = ⋃ m ∈ (Finset.univ : Finset ι), A m := by simp
    have heq : ρ (⋃ m : ι, A m) = ∑ m : ι, ρ (A m) := by
      rw [hUn]
      exact measure_biUnion_finset
        (fun m _ p _ hmp ↦ hpart.disjoint_setOf_latticeOceanPart_nonempty hmp)
        fun m _ ↦ hAmeas m
    rw [Finset.sum_congr rfl fun m _ ↦
      measure_setOf_latticeOceanPart_nonempty_eq hφ hM hsym hμ m n, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at heq
    exact heq ▸ prob_le_one
  rw [cond_apply (hAmeas n), Set.inter_eq_self_of_subset_right (hCA n),
    ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl haTop)]
  calc ρ {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω} * ρ (A n)
      ≤ ((Fintype.card ι : ℝ≥0∞) * ρ (C n)) * ρ (A n) := by gcongr
    _ = ρ (C n) * ((Fintype.card ι : ℝ≥0∞) * ρ (A n)) := by ring
    _ ≤ ρ (C n) * 1 := by gcongr
    _ = ρ (C n) := mul_one _

/-- **The events `A_n = {ξ⁰_P(G_n, ·) ≠ ∅}` are measurable**, Georgii's `G_n ∈ ℰ^C`. -/
theorem measurableSet_setOf_latticeOceanPart_nonempty_family
    (hGmeas : ∀ n, MeasurableSet (G n)) (n : ι) :
    MeasurableSet {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty} :=
  measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n)

omit [IsProbabilityMeasure ν] in
/-- **Georgii's "the measures `μ_1, …, μ_N` are mutually singular and thereby distinct"**: the
events `A_n` are pairwise disjoint and `μ_n` is carried by `A_n`. -/
theorem mutuallySingular_cond_setOf_latticeOceanPart_nonempty
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ n, MeasurableSet (G n))
    {m n : ι} (hmn : m ≠ n) :
    ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G m) ω).Nonempty}]).MutuallySingular
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]) := by
  have hAmeas := measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas
  refine ⟨{ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G m) ω).Nonempty}ᶜ, (hAmeas m).compl, ?_, ?_⟩
  · rw [cond_apply (hAmeas m), Set.inter_compl_self, measure_empty, mul_zero]
  · rw [compl_compl, cond_apply (hAmeas n),
      Set.disjoint_iff_inter_eq_empty.1
        ((hpart.disjoint_setOf_latticeOceanPart_nonempty hmn).symm),
      measure_empty, mul_zero]

/-! #### The conditional measures `μ_n = μ(· | A_n)` -/

section Cond

variable (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
  (hpart : IsPStablePartition φ₀ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
  (hGmeas : ∀ n, MeasurableSet (G n)) (hμ : μ ∈ GZero E φ ν)
  (hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
    {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty})

include hφ hM hpart hsym hGmeas hμ hpos

/-- **Georgii, Theorem (7.7)(b) applied to `A_n ∈ 𝒯`**: `μ_n = μ(· | A_n)` is a Gibbs measure. -/
theorem isGibbsMeasure_cond_setOf_latticeOceanPart_nonempty [Countable ι] (n : ι) :
    Specification.IsGibbsMeasure (cubeGibbsSpec E φ ν hφ hM)
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]) :=
  isGibbsMeasure_cond_of_tail _ (mem_GP_of_mem_GZero hφ hM hμ)
    (tail_measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n))
    (measure_setOf_latticeOceanPart_nonempty_pos hφ hM hpart hsym hμ hpos n).ne'

omit hGmeas in
/-- `μ_n` is a probability measure. -/
theorem isProbabilityMeasure_cond_setOf_latticeOceanPart_nonempty [Countable ι] (n : ι) :
    IsProbabilityMeasure
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]) :=
  cond_isProbabilityMeasure
    (measure_setOf_latticeOceanPart_nonempty_pos hφ hM hpart hsym hμ hpos n).ne'

omit hGmeas in
/-- **Georgii (18.25)(i)**, first half: `μ_n(ξ⁰_P(G_n, ·) ≠ ∅) = 1`. -/
theorem cond_apply_self_setOf_latticeOceanPart_nonempty [Countable ι] (n : ι) :
    ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}])
        {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1 :=
  cond_apply_self (measure_setOf_latticeOceanPart_nonempty_pos hφ hM hpart hsym hμ hpos n).ne'
    (measure_ne_top _ _)

omit hM hpart hsym hpos in
/-- **Georgii (18.25)(ii)**, the shifts: `μ_n` is invariant under `θ_a` whenever `r^a G_n = G_n`,
i.e. under Georgii's shift group `Θ̃_n = {θ_i : r^i G_n = G_n}` — the iterated reflections are
involutions, so his `r^a G_n = G_n` is the hypothesis `r^a ⁻¹' G_n = G_n` used here
(`image_tauPow_cubeRefl_latticeToTorus_zero`). -/
theorem measurePreserving_shift_cond_setOf_latticeOceanPart_nonempty (n : ι) {a : Fin 2 → ℤ}
    (hGa : tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n) :
    MeasurePreserving (shift E a).toFun
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}])
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]) :=
  (measurePreserving_shift_of_mem_GZero hφ hμ a).cond_of_preimage_eq
    (measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas n)
    (by rw [preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow, hGa])

omit hpart hsym hpos in
/-- **Georgii (18.25)(ii)**, the symmetries: `μ_n` is invariant under every `τ ∈ I_{C,λ}(Φ)` with
`τ G_n = G_n`. -/
theorem measurePreserving_onLattice_cond_setOf_latticeOceanPart_nonempty (n : ι)
    {τ : CubeTransformation E 2} (hτ : τ.IsSymmetry φ ν) (hGτ : τ.onCube.toFun '' G n = G n) :
    MeasurePreserving (τ.onLattice E).toFun
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}])
      ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]) := by
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' G n = G n := by
    conv_lhs => rw [← hGτ]
    exact Set.preimage_image_eq _ hinj
  exact (hτ.measurePreserving_onLattice_of_mem_GZero hφ hM hμ).cond_of_preimage_eq
    (measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas n)
    (by rw [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre])

omit hpart hpos in
/-- **Georgii (18.25)(iii)**: `τ(μ_m) = μ_n` whenever `τ ∈ I_{C,λ}(Φ)` carries `G_m` to `G_n`. -/
theorem map_onLattice_cond_setOf_latticeOceanPart_nonempty (m n : ι)
    {τ : CubeTransformation E 2} (hτ : τ.IsSymmetry φ ν) (hGτ : τ.onCube.toFun '' G m = G n) :
    ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G m) ω).Nonempty}]).map
        (τ.onLattice E).toFun
      = (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}] := by
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' G n = G m := by rw [← hGτ, Set.preimage_image_eq _ hinj]
  exact (hτ.measurePreserving_onLattice_of_mem_GZero hφ hM hμ).map_cond_of_preimage_eq
    (measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas n)
    (by rw [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre])
    (measure_setOf_latticeOceanPart_nonempty_eq hφ hM hsym hμ m n)

omit hpart hpos in
/-- **Georgii (18.25)(iii), the last sentence**: for `τ = r_k` the shift `θ_{e_k}` does the same
job, because `r^{e_k} = r_k` acts on the pattern sets as `r_k` acts on `E^C`. -/
theorem map_shift_cond_setOf_latticeOceanPart_nonempty (m n : ι) {k : Fin 2}
    (hGk : cubeRefl E k ⁻¹' G m = G n) :
    ((μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}]).map
        (shift E (Pi.single k 1)).toFun
      = (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G m) ω).Nonempty}] :=
  (measurePreserving_shift_of_mem_GZero hφ hμ _).map_cond_of_preimage_eq
    (measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas m)
    (by rw [preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow,
      tauPow_cubeRefl_latticeToTorus_zero_single, hGk])
    (measure_setOf_latticeOceanPart_nonempty_eq hφ hM hsym hμ n m)

/-- **Georgii, Theorem (18.25)** for a fixed potential: `N` distinct Gibbs measures with (i), (ii)
and (iii).  They are the conditional measures `μ_n = μ(· | ξ⁰_P(G_n, ·) ≠ ∅)` of a `μ ∈ 𝒢₀(Φ)`.

Only condition (18.23)(a)(ii) of the stable partition enters — which is why the partition may be
one of Georgii's `Φ` while the potential `φ` here is his `βΦ` — and the positivity hypothesis is
what his choice of `ε` and `β` supplies through (18.24) and (18.17); see
`eventually_exists_gibbsMeasure_family` for that step. -/
theorem exists_gibbsMeasure_family [Finite ι] :
    ∃ ρ : ι → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E φ ν hφ hM) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}
            ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : ι) (a : Fin 2 → ℤ), tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n →
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (∀ (n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry φ ν →
        τ.onCube.toFun '' G n = G n → MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
      (∀ (m n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry φ ν →
        τ.onCube.toFun '' G m = G n → (ρ m).map (τ.onLattice E).toFun = ρ n) := by
  classical
  have hAmeas := measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas
  refine ⟨fun n ↦ (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}],
    isProbabilityMeasure_cond_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hμ hpos,
    isGibbsMeasure_cond_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hGmeas hμ hpos,
    fun m n hmn ↦ mutuallySingular_cond_setOf_latticeOceanPart_nonempty hpart hGmeas hmn, ?_,
    cond_apply_self_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hμ hpos,
    fun n ↦ le_cond_measure_setOf_zero_mem_latticeOceanPart hφ hM hpart hsym hμ hAmeas hpos n,
    fun n a ha ↦ measurePreserving_shift_cond_setOf_latticeOceanPart_nonempty hφ hGmeas hμ n ha,
    fun n τ hτ hGτ ↦ measurePreserving_onLattice_cond_setOf_latticeOceanPart_nonempty hφ hM
      hGmeas hμ n hτ hGτ,
    fun m n τ hτ hGτ ↦ map_onLattice_cond_setOf_latticeOceanPart_nonempty hφ hM hsym hGmeas hμ
      m n hτ hGτ⟩
  intro m n hmn
  by_contra hne
  have hmn' : (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G m) ω).Nonempty}]
      = (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}] := hmn
  have h1 := cond_apply_self_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hμ hpos m
  rw [hmn', cond_apply (hAmeas n),
    Set.disjoint_iff_inter_eq_empty.1
      (hpart.disjoint_setOf_latticeOceanPart_nonempty (Ne.symm hne)),
    measure_empty, mul_zero] at h1
  exact zero_ne_one h1

end Cond

/-! #### The last statement of (18.25) when the partition is `r`-symmetric -/

section ExtremePoints

/-- **The last statement of Georgii's Theorem (18.25)**, `|ex 𝒢_Θ̃(Φ)| ≥ N`, in the case
`Θ̃ = Θ`.  If every member of the partition is `r`-symmetric then `Θ̃_n = {θ_i : r^i G_n = G_n}`
is the whole shift group, so the `N` mutually singular measures `μ_n` are `N` shift-invariant
Gibbs measures; being separated by the pairwise disjoint events `A_n` they are linearly
independent over `ℝ≥0∞` (`linearIndependent_of_measure_eq_one_of_measure_eq_zero`), and Corollary
(14.18) turns that into `|ex 𝒢_Θ(Φ)| ≥ N`.

For a partition which is *not* `r`-symmetric — the interesting case, and the reason Georgii
writes `Θ̃` — his `Θ̃ = ⋂_n Θ̃_n` is a proper subgroup of `Θ` containing `2ℤ²`, and the
corresponding statement needs (14.10)/(14.18) for that subgroup, i.e. a `(𝓟_Θ̃, 𝓘)`-kernel for a
finite-index subgroup of the shifts.  That is the remark below Corollary (14.18), and it is not
in the tree; the measure-theoretic half — the mutual singularity of `μ_1, …, μ_N` — is
`mutuallySingular_cond_setOf_latticeOceanPart_nonempty`. -/
theorem le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric [StandardBorelSpace E]
    {N : ℕ} {G : Fin N → Set ((Fin 2 → Fin 2) → E)} (hφ : Measurable φ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hsym : IsPhiSymmetric φ ν G) (hGmeas : ∀ n, MeasurableSet (G n))
    (hGsym : ∀ n, IsRSymmetric E (G n)) (hμ : μ ∈ GZero E φ ν)
    (hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty}) :
    (N : ℕ∞) ≤ ((invariantG (cubeGibbsSpec E φ ν hφ hM)
      (shiftGroup (Fin 2 → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  classical
  obtain ⟨F, C, hF, hne, hFol, hC, hC', -⟩ := exists_monotone_regular_foelner_cube (ι := Fin 2)
  have hAmeas := measurableSet_setOf_latticeOceanPart_nonempty_family (G := G) hGmeas
  refine (le_encard_extremePoints_invariantG_shiftGroup_iff hFol hF hne hC hC' N).2
    ⟨fun n ↦ (μ : Measure ((Fin 2 → ℤ) → E))[|{ω | (latticeOceanPart E (G n) ω).Nonempty}],
      fun n ↦ mem_invariantG.2 ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isProbabilityMeasure_cond_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hμ hpos n
  · exact isGibbsMeasure_cond_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hGmeas hμ hpos n
  · refine smulInvariantMeasure_iff_forall_measurePreserving.2 ?_
    rintro τ ⟨a, rfl⟩
    exact measurePreserving_shift_cond_setOf_latticeOceanPart_nonempty hφ hGmeas hμ n
      ((hGsym n).preimage_tauPow _)
  · refine linearIndependent_of_measure_eq_one_of_measure_eq_zero
      (A := fun n ↦ {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (G n) ω).Nonempty})
      (fun n ↦ cond_apply_self_setOf_latticeOceanPart_nonempty hφ hM hpart hsym hμ hpos n)
      fun m n hmn ↦ ?_
    rw [cond_apply (hAmeas n),
      Set.disjoint_iff_inter_eq_empty.1
        (hpart.disjoint_setOf_latticeOceanPart_nonempty (Ne.symm hmn)),
      measure_empty, mul_zero]

end ExtremePoints

/-! #### Georgii's choice of `ε` and `β`, and Comment (18.26)(1) -/

section LowTemperature

/-- **Georgii, Theorem (18.25)**, in the quantitative form his proof gives, which is also his
**Comment (18.26)(1)**: the conclusion holds for every `β > 0` with `δ(β) = 4 z(t(G_ε(Φ), βΦ)) < 1`,
where `ε > 0` is any number with `G_ε(Φ) ⊆ G_1 ∪ ⋯ ∪ G_N`.  Hence the upper critical inverse
temperature is at most the infimum of the `β₀` with `δ(β) < 1` for all `β ≥ β₀`.

Georgii's proof: (18.12) gives a `μ ∈ 𝒢₀(βΦ)`; (18.17) gives `μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) ≥ 1 - δ(β)`,
so the event that `G_1 ∪ ⋯ ∪ G_N` carries an ocean has positive mass, and
`exists_gibbsMeasure_family` applies. -/
theorem exists_gibbsMeasure_family_of_crossingBound_lt_one [StandardBorelSpace E] [Finite ι]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) {ε : ℝ}
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) {β : ℝ} (hβ : 0 < β)
    (hδ : 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1)
    (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ) :
    ∃ ρ : ι → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - 4 * Peierls.crossingBound
          (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
            ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : ι) (a : Fin 2 → ℤ), tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n →
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (∀ (n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
        τ.onCube.toFun '' G n = G n → MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
      (∀ (m n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
        τ.onCube.toFun '' G m = G n → (ρ m).map (τ.onLattice E).toFun = ρ n) := by
  classical
  have : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (ν := ν) hφβ (M := β * M)
    (fun ζ ↦ mul_le_mul_of_nonneg_left (hM ζ) hβ.le) (fun k ζ ↦ by rw [hφk k ζ])
    (hK.const_mul hβ) fun _ ↦ Classical.arbitrary E
  -- Georgii's `μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) ≥ 1 - δ(β) > 0`
  have hbound := le_measure_mem_latticeOceanPart_localGroundStates hφ hM hφk ε hβ.le hμ
  have hmono : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (localGroundStates φ ν ε) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω} :=
    measure_mono fun ω hω ↦ latticeOceanPart_mono (E := E) hGε ω hω
  have hzero : (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticeOceanPart E (⋃ n, G n) ω}
        ≤ (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    measure_mono fun ω hω ↦ ⟨0, hω⟩
  have hpos : 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (latticeOceanPart E (⋃ n, G n) ω).Nonempty} :=
    lt_of_lt_of_le (tsub_pos_of_lt hδ) ((hbound.trans hmono).trans hzero)
  obtain ⟨ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_gibbsMeasure_family (φ₀ := φ) hφβ hMβ hpart (hsym.const_mul hφk β) hGmeas hμ hpos
  exact ⟨ρ, h1, h2, h3, h4, h5,
    fun n ↦ ((hbound.trans hmono).trans (h6 n)), h7, h8, h9⟩

/-- **Georgii, Theorem (18.25)** as he states it: *if `β` is sufficiently large* there are `N`
distinct Gibbs measures for `βΦ` with (i), (ii) and (iii).  Georgii's `δ(β) → 0` is Remark
(18.9)(4) (`tendsto_patternWeight_smul_atTop`, through
`tendsto_bound_latticeOceanPart_localGroundStates`). -/
theorem eventually_exists_gibbsMeasure_family [StandardBorelSpace E] [Finite ι]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E} (hK : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hsym : IsPhiSymmetric φ ν G)
    (hGmeas : ∀ n, MeasurableSet (G n)) {ε : ℝ} (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * φ ζ) (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * φ ζ),
      ∃ ρ : ι → Measure ((Fin 2 → ℤ) → E),
        (∀ n, IsProbabilityMeasure (ρ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν hφβ hMβ) (ρ n)) ∧
        (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
        (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - 4 * Peierls.crossingBound
            (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
              ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
        (∀ (n : ι) (a : Fin 2 → ℤ), tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G n = G n →
          MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
        (∀ (n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
          τ.onCube.toFun '' G n = G n → MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
        (∀ (m n : ι) (τ : CubeTransformation E 2), τ.IsSymmetry (fun ζ ↦ β * φ ζ) ν →
          τ.onCube.toFun '' G m = G n → (ρ m).map (τ.onLattice E).toFun = ρ n) := by
  have hz : ∀ᶠ β : ℝ in atTop, 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)) < 1 := by
    have h := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
    have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound
        (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
    exact h4.eventually_lt_const (by norm_num)
  filter_upwards [eventually_gt_atTop 0, hz] with β hβ hδ hφβ hMβ
  exact exists_gibbsMeasure_family_of_crossingBound_lt_one hφ hM hφk hK hpart hsym hGmeas hGε
    hβ hδ hφβ hMβ

end LowTemperature

end Theorem1825

end MeasureTheory.GibbsMeasure

end

end
