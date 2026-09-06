/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Data.Finset.Pair
public import GibbsMeasure.Specification.HeisenbergPeriodic
public import GibbsMeasure.Specification.PeriodicGibbsLimits

/-!
# Georgii (17.24): the periodic Gibbs distribution of a Heisenberg potential

`GibbsMeasure.Specification.HeisenbergPeriodic` *defines* Georgii's `°γ_Λ^Φ` of (17.24) by the
density `exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j]` relative to `λ^Λ`, with `J_Λ` the periodised
coupling (17.25).  This file is the missing computation: (17.24) is Georgii's Example (4.20)(2)
for the Heisenberg potential (17.22), and the density is the Boltzmann factor of the periodic
modification `Φ̃^{Λ(N)}` of `Φ` in the cube `Λ(N)`.

Throughout, the cube is `Λ(N) = Potential.latticeBox d L = [-N, N)^d` with `N = L + 1`: a
translate of Georgii's `]-N, N]^d` of (17.1) and the same fundamental domain of the period group
`2N ℤ^d`.  The torus is `(ℤ/2N)^d`, and `L` — rather than `N` — indexes the cube, so that
`latticeToTorus L` of `GibbsMeasure.Specification.PeriodicGibbsLimits` and the `N`-torus of
`GibbsMeasure.Specification.HeisenbergPeriodic` agree on the nose; `n` is the spin dimension, as
in `heisenbergPotential n J`.

## The bonds of the torus

* `heisBond L i j r` — the representative of Georgii's class `ℛ({i, j})` of (4.20)(2) with
  *relative period* `r`: the unique period translate of the bond `{i, j + 2N r}` whose
  lexicographic anchor lies in `Λ(N)`.  `heisBond_injective` (for `i ≠ j`) and
  `exists_eq_heisBond` say that `r ↦ heisBond L i j r` enumerates `ℛ({i, j})` faithfully, and
  `heisenbergPotential_heisBond` evaluates the interaction on it as `-J(i - j - 2N r) σ_i·σ_j`.
* At a single site the enumeration is two-to-one: `heisBond_neg_self` is
  `heisBond L i i (-r) = heisBond L i i r` and `heisBond_self_zero` is
  `heisBond L i i 0 = {i}`, so `ℛ({i})` is indexed by the lexicographically positive relative
  periods `lexPos d` (`heisBond_self_injective`).  `tsum_lexPos_eq_half` and
  `tsum_lexPos_intBoxLen_smul` are the resulting halving, `∑_{r >_lex 0} J(2N r) = ½ J_Λ(0)`.

## Main results

* `heisenbergPeriodicPotential n J L` — an **abbreviation** of `Potential.periodicModification`
  at `Potential.latticeTorus` and `Potential.lexAnchor`; Georgii's `Φ^n` in the proof of (20.7).
* `heisenbergPeriodicPotential_pair` — **(17.24) off the diagonal**:
  `Φ̃^{Λ(N)}_{{i,j}}(σ) = -J_Λ(i-j) σ_i·σ_j` for distinct sites `i, j` of the cube.
* `heisenbergPeriodicPotential_singleton` — **(17.24) on the diagonal**:
  `Φ̃^{Λ(N)}_{{i}}(σ) = -½ J_Λ(0) |σ_i|²`, the self-energy of a site interacting with its own
  translates.  The `½` is the two-to-one covering above, not a convention.
* `heisenbergPeriodicPotential_of_forall_ne` — `Φ̃^{Λ(N)}_A = 0` for every `A` which is not a
  pair; together with `Potential.periodicModification_of_not_subset` (`A ⊄ Λ(N)`) this exhausts
  the interaction terms.
* `hasSummableRepSeries_heisenbergPotential` — **Georgii (17.23) is exactly the hypothesis that
  makes Example (4.20)(2) converge here**, and `isPotential_heisenbergPeriodicPotential` is the
  resulting Georgii (2.2)(i).  `isFiniteRange_heisenbergPeriodicPotential` needs nothing.
* `interactingHamiltonian_heisenbergPeriodicPotential` — **the Hamiltonian identity**:
  `H^{Φ̃^{Λ(N)}}_{Λ(N)}(σ) = -½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j`, diagonal included.
* `heisenbergPeriodicGibbsSpec` and `heisenbergPeriodicGibbsSpec_latticeBox` — **Georgii (17.24)
  as a theorem**: the Gibbs kernel `γ^{Φ̃^{Λ(N)}}_{Λ(N)}(·|ω)` of the periodic modification is
  the image of `°γ_{Λ(N)}^Φ` under the coupling map, i.e. Georgii's `°γ_{Λ(N)}^Φ × δ_ω` of
  Example (5.20)(3) — the `ℤ^d`-embedded field.  `map_periodicJuxt_heisenbergPeriodicGibbs` is
  the same statement before normalisation, and needs no admissibility hypothesis at all.

## Hypotheses, against Georgii

* **(17.23)** `Summable J` enters exactly where Georgii uses it: in the diagonal term
  (`tsum_lexPos_intBoxLen_smul`), hence in `heisenbergPeriodicPotential_singleton`, in
  `hasSummableRepSeries_heisenbergPotential` and in everything downstream.  It is *not* needed
  for `heisenbergPeriodicPotential_pair`, where both sides are unconditional `tsum`s and the
  identity is a reindexing; only evenness of `J` is used there.
* **`J 0 = 0`**, Georgii's normalisation in (17.22), is used for the diagonal only.
* **Absolute summability (2.11) is false here** and is not assumed:
  `not_isAbsolutelySummable_heisenbergPotential` in
  `GibbsMeasure.Specification.HeisenbergPeriodic`.  This is why
  `Potential.HasSummableRepSeries` — pointwise convergence of the representative series — was
  introduced in `GibbsMeasure.Potential.Periodic` and why
  `Potential.HasSummableRepSeries.isPotential` is stated with it rather than with `ℬ`.
* **The a priori measure** is only assumed σ-finite (and non-zero where a normalisation is
  taken), as in Georgii's standing hypothesis; `°Z_Λ^Φ < ∞` appears as the `λ`-admissibility
  argument `hadm`, which is Georgii's own standing assumption in §17.2.
* **The cube** is `[-N, N)^d`, a translate of Georgii's `]-N, N]^d`; the two are the same
  fundamental domain of `2N ℤ^d`, and (17.24) does not see the choice.

## Not formalised

Georgii's (20.5) — the Gibbsian specification of a Heisenberg potential over an unbounded spin
space — is `MeasureTheory.GibbsMeasure.heisenbergSpecification` in
`GibbsMeasure.Specification.HeisenbergSpecification`; it does not use this file.  What is still
missing is (20.7) and the transfer of the infrared bound (20.6) to `𝒢₀(Φ)`: what they need from
(17.24) is `heisenbergPeriodicGibbsSpec_latticeBox` together with
`Potential.mem_GP_of_mapClusterPt_*` of `GibbsMeasure.Potential.Periodic`, and the latter is still
stated for an absolutely summable potential.
-/

@[expose] public section

open Matrix MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d n L : ℕ} {J : (Fin d → ℤ) → ℝ}

/-! ### The bonds of the torus and their representatives -/

section Bonds

variable (L) in
/-- Georgii's representative of the class of the bond `{i, j + 2N r}` (Example (4.20)(2)) in the
cube `Λ(N) = [-N, N)^d`, `N = L + 1`: the unique translate of that bond by a period whose
lexicographic anchor lies in the cube.  Here `r` is the *relative period*: as `r` runs through
`ℤ^d`, `heisBond L i j r` runs through the representatives of the bonds of the torus joining the
class of `i` to the class of `j`. -/
def heisBond (i j r : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Potential.red (Potential.latticeTorus d L) Potential.lexAnchor
    ({i, j + Potential.intBoxLen L • r} : Finset (Fin d → ℤ))

variable {i j r r' : Fin d → ℤ}

/-- The representative bond, written out: a period translate of `{i, j + 2N r}`. -/
lemma heisBond_eq_pair (L : ℕ) (i j r : Fin d → ℤ) :
    ∃ g ∈ Potential.piPeriods (fun _ : Fin d ↦ Potential.intBoxLen L),
      heisBond L i j r = ({i + g, j + Potential.intBoxLen L • r + g} : Finset (Fin d → ℤ)) := by
  refine ⟨_, (Potential.isTorusReduction_latticeTorus d L).sub_mem'
    (Potential.lexAnchor ({i, j + Potential.intBoxLen L • r} : Finset (Fin d → ℤ))), ?_⟩
  simp only [heisBond, Potential.red, Potential.translate_pair]

lemma heisBond_nonempty : (heisBond L i j r).Nonempty :=
  Potential.red_nonempty.2 ⟨i, Finset.mem_insert_self _ _⟩

lemma isRep_heisBond :
    Potential.IsRep (Potential.latticeBox d L) Potential.lexAnchor (heisBond L i j r) :=
  Potential.isRep_red (Potential.isTorusReduction_latticeTorus d L) Potential.isAnchor_lexAnchor
    ⟨i, Finset.mem_insert_self _ _⟩

lemma zsmul_mem_latticePeriods (r : Fin d → ℤ) :
    Potential.intBoxLen L • r ∈ Potential.piPeriods (fun _ : Fin d ↦ Potential.intBoxLen L) :=
  Potential.mem_piPeriods_const_iff.2 ⟨r, rfl⟩

/-- The representative bond over `{i, j}` really projects onto `{i, j}`. -/
lemma starImage_heisBond (hi : i ∈ Potential.latticeBox d L)
    (hj : j ∈ Potential.latticeBox d L) :
    Potential.starImage (Potential.latticeTorus d L) (heisBond L i j r)
      = ({i, j} : Finset (Fin d → ℤ)) := by
  have hπ := Potential.isTorusReduction_latticeTorus d L
  rw [heisBond, Potential.starImage_red hπ, Potential.starImage_pair,
    hπ.eq_self i hi, hπ.add_mem j (zsmul_mem_latticePeriods r), hπ.eq_self j hj]

/-- **The interaction of a representative bond**, evaluated on the periodic continuation:
Georgii's `-J(i - j - 2N r) σ_i · σ_j`.  The hypothesis `hne` says the bond is not degenerate. -/
lemma heisenbergPotential_heisBond (heven : ∀ m, J (-m) = J m)
    (hi : i ∈ Potential.latticeBox d L) (hj : j ∈ Potential.latticeBox d L)
    (hne : i ≠ j + Potential.intBoxLen L • r) (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPotential n J (heisBond L i j r)
        (Potential.periodicExtend (Potential.latticeTorus d L) η)
      = -(J (i - j - Potential.intBoxLen L • r) * (η i ⬝ᵥ η j)) := by
  obtain ⟨g, hg, hB⟩ := heisBond_eq_pair L i j r
  have hπ := Potential.isTorusReduction_latticeTorus d L
  have hxy : i + g ≠ j + Potential.intBoxLen L • r + g := fun h ↦ hne (add_right_cancel h)
  have hσ1 : Potential.periodicExtend (Potential.latticeTorus d L) η (i + g) = η i := by
    rw [Potential.periodicExtend_apply, hπ.add_mem i hg, hπ.eq_self i hi]
  have hσ2 : Potential.periodicExtend (Potential.latticeTorus d L) η
      (j + Potential.intBoxLen L • r + g) = η j := by
    rw [Potential.periodicExtend_apply, add_assoc,
      hπ.add_mem j (AddSubgroup.add_mem _ (zsmul_mem_latticePeriods r) hg), hπ.eq_self j hj]
  have hdiff : i + g - (j + Potential.intBoxLen L • r + g)
      = i - j - Potential.intBoxLen L • r := by abel
  rw [hB, heisenbergPotential_pair heven hxy, hσ1, hσ2, hdiff]

/-- **Distinct relative periods give distinct representatives** over a bond `{i, j}` of the torus
with `i ≠ j`. -/
lemma heisBond_injective (hi : i ∈ Potential.latticeBox d L)
    (hj : j ∈ Potential.latticeBox d L) (hij : i ≠ j) :
    Function.Injective (heisBond L i j) := by
  intro r r' h
  have hπ := Potential.isTorusReduction_latticeTorus d L
  obtain ⟨g, hg, hB⟩ := heisBond_eq_pair L i j r
  obtain ⟨g', hg', hB'⟩ := heisBond_eq_pair L i j r'
  have hx : Potential.latticeTorus d L (i + g) = i := by rw [hπ.add_mem i hg, hπ.eq_self i hi]
  have hx' : Potential.latticeTorus d L (i + g') = i := by rw [hπ.add_mem i hg', hπ.eq_self i hi]
  have hy : Potential.latticeTorus d L (j + Potential.intBoxLen L • r + g) = j := by
    rw [add_assoc, hπ.add_mem j (AddSubgroup.add_mem _ (zsmul_mem_latticePeriods r) hg),
      hπ.eq_self j hj]
  have hy' : Potential.latticeTorus d L (j + Potential.intBoxLen L • r' + g') = j := by
    rw [add_assoc, hπ.add_mem j (AddSubgroup.add_mem _ (zsmul_mem_latticePeriods r') hg'),
      hπ.eq_self j hj]
  have hne : Potential.latticeTorus d L (i + g)
      ≠ Potential.latticeTorus d L (j + Potential.intBoxLen L • r + g) := by
    rw [hx, hy]; exact hij
  obtain ⟨h1, h2⟩ := Potential.eq_of_pair_eq_pair_of_apply_ne hne (hx'.trans hx.symm)
    (hy'.trans hy.symm) (by rw [← hB, ← hB', h])
  have hgg : g = g' := add_left_cancel h1
  rw [hgg] at h2
  have hcc : Potential.intBoxLen L • r = Potential.intBoxLen L • r' :=
    add_left_cancel (add_right_cancel h2)
  funext k
  have hk := congrFun hcc k
  simp only [Pi.smul_apply, smul_eq_mul] at hk
  exact mul_left_cancel₀ (Potential.intBoxLen_pos L).ne' hk

/-- **Every representative over a bond of the torus is a `heisBond`.**  This is Georgii's
enumeration of `ℛ(A)` in Example (4.20)(2) for a pair potential: modulo the periods, a bond of
the torus joining the class of `i` to that of `j` is determined by its relative period. -/
lemma exists_eq_heisBond {B : Finset (Fin d → ℤ)} {x y : Fin d → ℤ}
    (hrep : Potential.IsRep (Potential.latticeBox d L) Potential.lexAnchor B)
    (hBxy : B = ({x, y} : Finset (Fin d → ℤ)))
    (hstar : Potential.starImage (Potential.latticeTorus d L) B
      = ({i, j} : Finset (Fin d → ℤ))) :
    ∃ r, B = heisBond L i j r := by
  have hπ := Potential.isTorusReduction_latticeTorus d L
  subst hBxy
  obtain ⟨u, v, hu, hv, huv⟩ := Potential.exists_pair_of_starImage_eq_pair hstar
  have hg1 : u - i ∈ Potential.piPeriods (fun _ : Fin d ↦ Potential.intBoxLen L) := by
    have h := hπ.sub_mem u
    rwa [hu] at h
  have hg2 : v - j ∈ Potential.piPeriods (fun _ : Fin d ↦ Potential.intBoxLen L) := by
    have h := hπ.sub_mem v
    rwa [hv] at h
  obtain ⟨s, hs⟩ := Potential.mem_piPeriods_const_iff.1 (AddSubgroup.sub_mem _ hg2 hg1)
  refine ⟨s, Potential.eq_red_of_isRep_of_eq_translate hπ Potential.isAnchor_lexAnchor
    ⟨i, Finset.mem_insert_self _ _⟩ hrep hg1 ?_⟩
  have h1 : i + (u - i) = u := by abel
  have h2 : j + Potential.intBoxLen L • s + (u - i) = v := by rw [← hs]; abel
  rw [Potential.translate_pair, h1, h2]
  exact huv

/-- Reversing the relative period does not change the representative bond at a single site: this
is the two-to-one covering behind the factor `1/2` on the diagonal of Georgii (17.24). -/
lemma heisBond_neg_self (L : ℕ) (i r : Fin d → ℤ) :
    heisBond L i i (-r) = heisBond L i i r := by
  have hπ := Potential.isTorusReduction_latticeTorus d L
  have hg : -(Potential.intBoxLen L • r)
      ∈ Potential.piPeriods (fun _ : Fin d ↦ Potential.intBoxLen L) :=
    AddSubgroup.neg_mem _ (zsmul_mem_latticePeriods r)
  have h1 : i + Potential.intBoxLen L • r + -(Potential.intBoxLen L • r) = i := by abel
  have h2 : i + Potential.intBoxLen L • (-r) = i + -(Potential.intBoxLen L • r) := by
    rw [smul_neg]
  have hset : ({i, i + Potential.intBoxLen L • (-r)} : Finset (Fin d → ℤ))
      = Potential.translate ({i, i + Potential.intBoxLen L • r} : Finset (Fin d → ℤ))
          (-(Potential.intBoxLen L • r)) := by
    rw [Potential.translate_pair, h1, h2]
    exact Finset.pair_comm _ _
  rw [heisBond, hset, Potential.red_translate hπ Potential.isAnchor_lexAnchor hg
    ⟨i, Finset.mem_insert_self _ _⟩]
  rfl

/-- The representative bond of relative period `0` at a site of the cube is the site itself. -/
lemma heisBond_self_zero (hi : i ∈ Potential.latticeBox d L) :
    heisBond L i i 0 = ({i} : Finset (Fin d → ℤ)) := by
  have h0 : ({i, i + Potential.intBoxLen L • (0 : Fin d → ℤ)} : Finset (Fin d → ℤ)) = {i} := by
    simp
  rw [heisBond, h0]
  exact Potential.red_eq_self (Potential.isTorusReduction_latticeTorus d L)
    (Potential.isRep_of_subset Potential.isAnchor_lexAnchor ⟨i, Finset.mem_singleton_self i⟩
      (Finset.singleton_subset_iff.2 hi))

end Bonds

/-! ### The lexicographically positive relative periods, and Georgii's self-energy -/

section LexPos

variable (d) in
/-- The lexicographically positive vectors of `ℤ^d`: a fundamental domain for `r ↦ -r` on the
nonzero relative periods.  Each unordered pair `{r, -r}` of nonzero relative periods carries a
single representative bond at a site of the torus, which is where the factor `1/2` on the
diagonal of Georgii (17.24) comes from. -/
def lexPos : Set (Fin d → ℤ) := {r | toLex (0 : Fin d → ℤ) < toLex r}

@[simp] lemma mem_lexPos {r : Fin d → ℤ} :
    r ∈ lexPos d ↔ toLex (0 : Fin d → ℤ) < toLex r := Iff.rfl

/-- **Halving a symmetric sum.**  A summable even function on `ℤ^d` vanishing at the origin has
half of its total sum over the lexicographically positive vectors. -/
lemma tsum_lexPos_eq_half {F : (Fin d → ℤ) → ℝ} (hF : Summable F) (heven : ∀ m, F (-m) = F m)
    (hF0 : F 0 = 0) : ∑' ρ : lexPos d, F ρ.1 = (∑' m, F m) / 2 := by
  have hlt : ∀ m : Fin d → ℤ,
      (toLex (-m) < toLex (0 : Fin d → ℤ)) ↔ (toLex (0 : Fin d → ℤ) < toLex m) :=
    fun m ↦ neg_lt_zero (a := toLex m)
  have hind : ∀ m : Fin d → ℤ,
      (lexPos d).indicator F m
        + ({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F m
        + (if m = 0 then F 0 else 0) = F m := by
    intro m
    rcases lt_trichotomy (toLex (0 : Fin d → ℤ)) (toLex m) with h | h | h
    · have hm : m ≠ 0 := by rintro rfl; exact absurd h (lt_irrefl _)
      rw [Set.indicator_of_mem (mem_lexPos.2 h),
        Set.indicator_of_notMem
          (show m ∉ {r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)} from
            fun hx ↦ absurd h (lt_asymm hx)),
        ite_eq_right hm]
      ring
    · have hm0 : m = 0 := (toLex_inj.1 h).symm
      subst hm0
      rw [Set.indicator_of_notMem
          (show (0 : Fin d → ℤ) ∉ lexPos d from fun hx ↦ absurd (mem_lexPos.1 hx) (lt_irrefl _)),
        Set.indicator_of_notMem
          (show (0 : Fin d → ℤ) ∉ {r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)} from
            fun hx ↦ lt_irrefl (toLex (0 : Fin d → ℤ)) hx),
        ite_eq_left rfl]
      ring
    · have hm : m ≠ 0 := by rintro rfl; exact absurd h (lt_irrefl _)
      rw [Set.indicator_of_notMem
          (show m ∉ lexPos d from fun hx ↦ absurd h (lt_asymm (mem_lexPos.1 hx))),
        Set.indicator_of_mem (show m ∈ {r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)} from h),
        ite_eq_right hm]
      ring
  have hQP : ∀ m : Fin d → ℤ,
      ({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F (-m)
        = (lexPos d).indicator F m := by
    intro m
    by_cases hm : toLex (0 : Fin d → ℤ) < toLex m
    · rw [Set.indicator_of_mem
        (show -m ∈ {r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)} from (hlt m).2 hm),
        Set.indicator_of_mem (mem_lexPos.2 hm), heven]
    · rw [Set.indicator_of_notMem
        (show -m ∉ {r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)} from
          fun hx ↦ hm ((hlt m).1 hx)),
        Set.indicator_of_notMem (show m ∉ lexPos d from fun hx ↦ hm (mem_lexPos.1 hx))]
  have hPs : Summable ((lexPos d).indicator F) := hF.indicator _
  have hQs : Summable (({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F) :=
    hF.indicator _
  have hxy : ∑' m, ({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F m
      = ∑' m, (lexPos d).indicator F m := by
    rw [← Equiv.tsum_eq (Equiv.neg (Fin d → ℤ))
      (({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F)]
    exact tsum_congr hQP
  have h3 : HasSum (fun m : Fin d → ℤ ↦ if m = 0 then F 0 else 0) (F 0) :=
    hasSum_ite_eq (0 : Fin d → ℤ) (F 0)
  have hHS : HasSum F ((∑' m, (lexPos d).indicator F m)
      + (∑' m, ({r : Fin d → ℤ | toLex r < toLex (0 : Fin d → ℤ)}).indicator F m) + F 0) := by
    have h := (hPs.hasSum.add hQs.hasSum).add h3
    rwa [funext hind] at h
  rw [tsum_subtype (lexPos d) F, hHS.tsum_eq, hxy, hF0]
  ring

/-- The side `2N` of the cube `Λ(N) = [-N, N)^d`, `N = L + 1`, as it appears in the periodised
coupling (17.25). -/
lemma intBoxLen_eq (L : ℕ) : Potential.intBoxLen L = 2 * ((L + 1 : ℕ) : ℤ) := by
  rw [Potential.intBoxLen]; push_cast; ring

lemma injective_intBoxLen_smul (L : ℕ) :
    Function.Injective fun r : Fin d → ℤ ↦ Potential.intBoxLen L • r := by
  intro a b h
  funext k
  have hk := congrFun h k
  simp only [Pi.smul_apply, smul_eq_mul] at hk
  exact mul_left_cancel₀ (Potential.intBoxLen_pos L).ne' hk

/-- **Georgii's self-energy (17.24).**  Summing the coupling over the lexicographically positive
periods gives half the periodised coupling at the origin, `½ J_Λ(0)`. -/
lemma tsum_lexPos_intBoxLen_smul (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) :
    ∑' ρ : lexPos d, J (Potential.intBoxLen L • ρ.1) = periodizedCoupling (L + 1) J 0 / 2 := by
  have hF : Summable fun r : Fin d → ℤ ↦ J (Potential.intBoxLen L • r) :=
    hsum.comp_injective (injective_intBoxLen_smul L)
  have hev : ∀ m : Fin d → ℤ, J (Potential.intBoxLen L • (-m)) = J (Potential.intBoxLen L • m) := by
    intro m
    rw [smul_neg, heven]
  have hzero : J (Potential.intBoxLen L • (0 : Fin d → ℤ)) = 0 := by rw [smul_zero, hJ0]
  have htot : ∑' r : Fin d → ℤ, J (Potential.intBoxLen L • r) = periodizedCoupling (L + 1) J 0 := by
    rw [periodizedCoupling_eq_tsum (J := J) (m := (0 : Fin d → ℤ)) (z := 0) (by simp)]
    exact tsum_congr fun ℓ ↦ by rw [zero_add, intBoxLen_eq]
  rw [tsum_lexPos_eq_half hF hev hzero, htot]

/-- **Distinct lexicographically positive relative periods give distinct representatives** at a
single site of the torus.  Together with `heisBond_neg_self` this says that the representatives
over `{i}` are indexed by `lexPos d`: each unordered pair `{r, -r}` of nonzero relative periods
carries exactly one of them. -/
lemma heisBond_self_injective (i : Fin d → ℤ) :
    Function.Injective fun ρ : lexPos d ↦ heisBond L i i ρ.1 := by
  rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
  simp only at h
  obtain ⟨g, hg, hB⟩ := heisBond_eq_pair L i i r
  obtain ⟨g', hg', hB'⟩ := heisBond_eq_pair L i i r'
  have hpair : ({i + g, i + Potential.intBoxLen L • r + g} : Finset (Fin d → ℤ))
      = ({i + g', i + Potential.intBoxLen L • r' + g'} : Finset (Fin d → ℤ)) := by
    rw [← hB, ← hB', h]
  rcases Finset.pair_eq_pair_iff.1 hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hgg : g = g' := add_left_cancel h1
    rw [hgg] at h2
    exact Subtype.ext (injective_intBoxLen_smul L (add_left_cancel (add_right_cancel h2)))
  · exfalso
    have e1 : g = Potential.intBoxLen L • r' + g' :=
      add_left_cancel (a := i) (by rw [h1]; abel)
    have e2 : Potential.intBoxLen L • r + g = g' :=
      add_left_cancel (a := i) (by rw [← h2]; abel)
    have e6 : Potential.intBoxLen L • r + (Potential.intBoxLen L • r' + g') = g' := by
      rw [← e1]; exact e2
    have e5 : Potential.intBoxLen L • r + Potential.intBoxLen L • r' = 0 := by
      refine add_right_cancel (b := g') ?_
      rw [zero_add]
      calc Potential.intBoxLen L • r + Potential.intBoxLen L • r' + g'
          = Potential.intBoxLen L • r + (Potential.intBoxLen L • r' + g') := by abel
        _ = g' := e6
    have e7 : r + r' = 0 := by
      refine injective_intBoxLen_smul L ?_
      simp only
      rw [smul_add, e5, smul_zero]
    have hpos := add_pos (mem_lexPos.1 hr) (mem_lexPos.1 hr')
    rw [show toLex r + toLex r' = toLex (r + r') from rfl, e7] at hpos
    exact lt_irrefl _ hpos

end LexPos

/-! ### Georgii (17.24): the periodic modification of the Heisenberg potential -/

section PeriodicModification

variable (n) in
/-- **Georgii's `Φ̃^{Λ(N)}`** for the Heisenberg potential (17.22): its periodic modification of
Example (4.20)(2) in the cube `Λ(N) = [-N, N)^d`, `N = L + 1`, taken at the torus reduction
`Potential.latticeTorus` of the cube and the lexicographic anchor.  This is the potential Georgii
writes `Φ^n` in the proof of (20.7); its interaction terms are computed by
`heisenbergPeriodicPotential_pair` and `heisenbergPeriodicPotential_singleton`. -/
abbrev heisenbergPeriodicPotential (J : (Fin d → ℤ) → ℝ) (L : ℕ) :
    Potential (Fin d → ℤ) (Fin n → ℝ) :=
  Potential.periodicModification (heisenbergPotential n J) (Potential.latticeBox d L)
    (Potential.latticeTorus d L) Potential.lexAnchor

/-- The set `ℛ(A)` of Georgii (4.20)(2) for the Heisenberg potential in the cube. -/
private def heisRep (L : ℕ) (A : Finset (Fin d → ℤ)) : Set (Finset (Fin d → ℤ)) :=
  {C | Potential.IsRep (Potential.latticeBox d L) Potential.lexAnchor C
    ∧ Potential.starImage (Potential.latticeTorus d L) C = A}

variable {A : Finset (Fin d → ℤ)} {η : (Fin d → ℤ) → (Fin n → ℝ)}

private lemma mem_heisRep {B : Finset (Fin d → ℤ)} :
    B ∈ heisRep L A ↔ Potential.IsRep (Potential.latticeBox d L) Potential.lexAnchor B
      ∧ Potential.starImage (Potential.latticeTorus d L) B = A := Iff.rfl

private lemma heisenbergPeriodicPotential_eq_tsum (L : ℕ) (A : Finset (Fin d → ℤ))
    (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPeriodicPotential n J L A η
      = ∑' B : Finset (Fin d → ℤ), (heisRep L A).indicator
          (fun B ↦ heisenbergPotential n J B
            (Potential.periodicExtend (Potential.latticeTorus d L) η)) B := rfl

/-- **`Φ̃^{Λ(N)}_A = 0` unless `A` is a pair.**  The Heisenberg potential is a pair potential and
the projection of a pair is a pair, so the representative series over any other `A` is
identically zero. -/
private lemma indicator_heisRep_eq_zero_of_forall_ne
    (hA : ∀ x y : Fin d → ℤ, A ≠ ({x, y} : Finset (Fin d → ℤ)))
    (η : (Fin d → ℤ) → (Fin n → ℝ)) (B : Finset (Fin d → ℤ)) :
    (heisRep L A).indicator (fun B ↦ heisenbergPotential n J B
      (Potential.periodicExtend (Potential.latticeTorus d L) η)) B = 0 := by
  by_cases hB : B ∈ heisRep L A
  · rw [Set.indicator_of_mem hB]
    refine heisenbergPotential_of_forall_ne (fun x y hxy ↦ ?_) _
    exact hA (Potential.latticeTorus d L x) (Potential.latticeTorus d L y)
      (by rw [← (mem_heisRep.1 hB).2, hxy, Potential.starImage_pair])
  · exact Set.indicator_of_notMem hB _

/-- The representatives over `A` all project into the cube, so there are none when `A ⊄ Λ(N)`. -/
private lemma heisRep_eq_empty_of_not_subset (hA : ¬ A ⊆ Potential.latticeBox d L) :
    heisRep L A = (∅ : Set (Finset (Fin d → ℤ))) := by
  ext B
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hB
  exact hA ((mem_heisRep.1 hB).2 ▸
    Potential.starImage_subset (Potential.isTorusReduction_latticeTorus d L) B)

/-- **`Φ̃^{Λ(N)}_A = 0` unless `A` is a pair.**  The Heisenberg potential is a pair potential and
the projection of a pair is a pair, so the representative series over any other `A` is
identically zero. -/
theorem heisenbergPeriodicPotential_of_forall_ne
    (hA : ∀ x y : Fin d → ℤ, A ≠ ({x, y} : Finset (Fin d → ℤ)))
    (η : (Fin d → ℤ) → (Fin n → ℝ)) : heisenbergPeriodicPotential n J L A η = 0 := by
  rw [heisenbergPeriodicPotential_eq_tsum]
  simp [indicator_heisRep_eq_zero_of_forall_ne hA η]

variable {i j r : Fin d → ℤ}

/-- The value of the representative series at the bond `heisBond L i j r`. -/
private lemma indicator_heisRep_heisBond (heven : ∀ m, J (-m) = J m)
    (hi : i ∈ Potential.latticeBox d L) (hj : j ∈ Potential.latticeBox d L)
    (hne : i ≠ j + Potential.intBoxLen L • r) (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisRep L ({i, j} : Finset (Fin d → ℤ))).indicator
        (fun B ↦ heisenbergPotential n J B
          (Potential.periodicExtend (Potential.latticeTorus d L) η)) (heisBond L i j r)
      = -(J (i - j - Potential.intBoxLen L • r) * (η i ⬝ᵥ η j)) := by
  rw [Set.indicator_of_mem
    (mem_heisRep.2 ⟨isRep_heisBond, starImage_heisBond hi hj⟩)]
  exact heisenbergPotential_heisBond heven hi hj hne η

/-- Every volume carrying a nonzero interaction and representing `{i, j}` is a `heisBond`. -/
private lemma support_subset_range_heisBond (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    Function.support ((heisRep L ({i, j} : Finset (Fin d → ℤ))).indicator
        (fun B ↦ heisenbergPotential n J B
          (Potential.periodicExtend (Potential.latticeTorus d L) η)))
      ⊆ Set.range (heisBond L i j) := by
  intro B hB
  have hmem : B ∈ heisRep L ({i, j} : Finset (Fin d → ℤ)) := by
    by_contra hc
    exact hB (Set.indicator_of_notMem hc _)
  have hval : heisenbergPotential n J B
      (Potential.periodicExtend (Potential.latticeTorus d L) η) ≠ 0 := by
    intro hc
    exact hB (by rw [Set.indicator_of_mem hmem]; exact hc)
  obtain ⟨x, y, hxy⟩ : ∃ x y, B = ({x, y} : Finset (Fin d → ℤ)) := by
    by_contra hc
    push Not at hc
    exact hval (heisenbergPotential_of_forall_ne (fun x y ↦ hc x y) _)
  obtain ⟨r, hr⟩ := exists_eq_heisBond (mem_heisRep.1 hmem).1 hxy (mem_heisRep.1 hmem).2
  exact ⟨r, hr.symm⟩

/-- A bond joining two distinct sites of the cube is not degenerate. -/
private lemma ne_add_intBoxLen_smul_of_ne (hi : i ∈ Potential.latticeBox d L)
    (hj : j ∈ Potential.latticeBox d L) (hij : i ≠ j) (r : Fin d → ℤ) :
    i ≠ j + Potential.intBoxLen L • r := by
  intro hcon
  refine hij ?_
  have hπ := Potential.isTorusReduction_latticeTorus d L
  have h := hπ.add_mem j (zsmul_mem_latticePeriods r)
  rw [← hcon, hπ.eq_self i hi, hπ.eq_self j hj] at h
  exact h

/-- **Georgii (17.24) off the diagonal.**  For two distinct sites of the cube the periodic
modification of the Heisenberg potential is `-J_Λ(i-j) σ_i · σ_j`, with `J_Λ` the periodised
coupling (17.25).  The hypothesis is exactly Georgii's (17.23), `∑_m |J(m)| < ∞`. -/
theorem heisenbergPeriodicPotential_pair (heven : ∀ m, J (-m) = J m)
    (hi : i ∈ Potential.latticeBox d L) (hj : j ∈ Potential.latticeBox d L) (hij : i ≠ j)
    (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPeriodicPotential n J L ({i, j} : Finset (Fin d → ℤ)) η
      = -(periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) * (η i ⬝ᵥ η j)) := by
  have hre : ∑' r : Fin d → ℤ, J (i - j - Potential.intBoxLen L • r)
      = periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) := by
    rw [periodizedCoupling_eq_tsum (J := J) (m := i - j) (z := latticeToTorus L (i - j))
      (fun c ↦ rfl), ← Equiv.tsum_eq (Equiv.neg (Fin d → ℤ))
      (fun r : Fin d → ℤ ↦ J (i - j + (2 * ((L + 1 : ℕ) : ℤ)) • r))]
    refine tsum_congr fun r ↦ ?_
    simp only [Equiv.neg_apply]
    congr 1
    rw [intBoxLen_eq, smul_neg]
    abel
  rw [heisenbergPeriodicPotential_eq_tsum,
    ← (heisBond_injective hi hj hij).tsum_eq (support_subset_range_heisBond η),
    tsum_congr (fun r ↦ indicator_heisRep_heisBond heven hi hj
      (ne_add_intBoxLen_smul_of_ne hi hj hij r) η), tsum_neg, tsum_mul_right, hre]

/-- A bond joining a site to a distinct translate of itself is not degenerate. -/
private lemma ne_add_intBoxLen_smul (i : Fin d → ℤ) (hr : r ≠ 0) :
    i ≠ i + Potential.intBoxLen L • r := by
  intro hcon
  have h0 : Potential.intBoxLen L • r = 0 :=
    (add_left_cancel (a := i) (by rw [add_zero]; exact hcon)).symm
  refine hr (injective_intBoxLen_smul L ?_)
  change Potential.intBoxLen L • r = Potential.intBoxLen L • (0 : Fin d → ℤ)
  rw [h0, smul_zero]

private lemma pair_self_eq_singleton (i : Fin d → ℤ) :
    ({i, i} : Finset (Fin d → ℤ)) = {i} := by simp

/-- The value of the representative series at a bond joining `i` to one of its own translates. -/
private lemma indicator_heisRep_heisBond_self (heven : ∀ m, J (-m) = J m)
    (hi : i ∈ Potential.latticeBox d L) (hr : r ≠ 0) (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisRep L ({i} : Finset (Fin d → ℤ))).indicator
        (fun B ↦ heisenbergPotential n J B
          (Potential.periodicExtend (Potential.latticeTorus d L) η)) (heisBond L i i r)
      = -(J (Potential.intBoxLen L • r) * (η i ⬝ᵥ η i)) := by
  have hdiff : i - i - Potential.intBoxLen L • r = -(Potential.intBoxLen L • r) := by abel
  rw [Set.indicator_of_mem
      (mem_heisRep.2 ⟨isRep_heisBond, by
        rw [starImage_heisBond hi hi, pair_self_eq_singleton]⟩),
    heisenbergPotential_heisBond heven hi hi (ne_add_intBoxLen_smul i hr) η, hdiff, heven]

/-- Every volume carrying a nonzero interaction and representing `{i}` is a bond `{i, i + 2N ρ}`
with `ρ` lexicographically positive. -/
private lemma support_subset_range_heisBond_self (hJ0 : J 0 = 0)
    (hi : i ∈ Potential.latticeBox d L) (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    Function.support ((heisRep L ({i} : Finset (Fin d → ℤ))).indicator
        (fun B ↦ heisenbergPotential n J B
          (Potential.periodicExtend (Potential.latticeTorus d L) η)))
      ⊆ Set.range (fun ρ : lexPos d ↦ heisBond L i i ρ.1) := by
  intro B hB
  have hmem : B ∈ heisRep L ({i} : Finset (Fin d → ℤ)) := by
    by_contra hc
    exact hB (Set.indicator_of_notMem hc _)
  have hval : heisenbergPotential n J B
      (Potential.periodicExtend (Potential.latticeTorus d L) η) ≠ 0 := by
    intro hc
    exact hB (by rw [Set.indicator_of_mem hmem]; exact hc)
  obtain ⟨x, y, hxy⟩ : ∃ x y, B = ({x, y} : Finset (Fin d → ℤ)) := by
    by_contra hc
    push Not at hc
    exact hval (heisenbergPotential_of_forall_ne (fun x y ↦ hc x y) _)
  obtain ⟨r, hr⟩ := exists_eq_heisBond (i := i) (j := i) (mem_heisRep.1 hmem).1 hxy
    (by rw [(mem_heisRep.1 hmem).2, pair_self_eq_singleton])
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [heisBond_self_zero hi] at hr
    exact hval (by rw [hr]; exact heisenbergPotential_singleton hJ0 i _)
  rcases lt_trichotomy (toLex (0 : Fin d → ℤ)) (toLex r) with h | h | h
  · exact ⟨⟨r, h⟩, hr.symm⟩
  · exact absurd (toLex_inj.1 h).symm hr0
  · refine ⟨⟨-r, mem_lexPos.2 (neg_pos.2 h)⟩, ?_⟩
    simp only
    rw [heisBond_neg_self]
    exact hr.symm

/-- **Georgii (17.24) on the diagonal.**  At a single site of the cube the periodic modification
of the Heisenberg potential is the self-energy `-½ J_Λ(0) |σ_i|²`.  The representatives over `{i}`
are the bonds `{i, i + 2N r}` joining `i` to its own translates, and `{i, i + 2N r}` and
`{i, i - 2N r}` are period translates of one another (`heisBond_neg_self`), so each unordered
pair `{r, -r}` of nonzero relative periods is counted once: this is the factor `1/2` on the
diagonal of (17.24), and Georgii's `Φ^n_{{i}}` in the proof of (20.7). -/
theorem heisenbergPeriodicPotential_singleton (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (hi : i ∈ Potential.latticeBox d L) (η : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPeriodicPotential n J L ({i} : Finset (Fin d → ℤ)) η
      = -(periodizedCoupling (L + 1) J 0 * (η i ⬝ᵥ η i)) / 2 := by
  have hterm : ∀ ρ : lexPos d,
      (heisRep L ({i} : Finset (Fin d → ℤ))).indicator
        (fun B ↦ heisenbergPotential n J B
          (Potential.periodicExtend (Potential.latticeTorus d L) η)) (heisBond L i i ρ.1)
      = -(J (Potential.intBoxLen L • ρ.1) * (η i ⬝ᵥ η i)) := fun ρ ↦
    indicator_heisRep_heisBond_self heven hi
      (fun h0 ↦ absurd (h0 ▸ mem_lexPos.1 ρ.2) (lt_irrefl _)) η
  rw [heisenbergPeriodicPotential_eq_tsum,
    ← (heisBond_self_injective (L := L) i).tsum_eq (support_subset_range_heisBond_self hJ0 hi η),
    tsum_congr hterm, tsum_neg, tsum_mul_right, tsum_lexPos_intBoxLen_smul hsum heven hJ0]
  ring

/-! ### Georgii (17.23) makes the representative series converge -/

/-- **Georgii (17.23) is exactly what makes Example (4.20)(2) converge for a Heisenberg
potential.**  Under `Summable J` the representative series defining `Φ̃^{Λ(N)}_A` converges at
every interaction support and every configuration — even though the Heisenberg potential is
*not* absolutely summable in the sense of (2.11) over an unbounded spin space
(`not_isAbsolutelySummable_heisenbergPotential`), so that Georgii's series is not dominated by
the sup-norms (2.12). -/
theorem hasSummableRepSeries_heisenbergPotential (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (L : ℕ) :
    Potential.HasSummableRepSeries (heisenbergPotential n J) (Potential.latticeBox d L)
      (Potential.latticeTorus d L) Potential.lexAnchor := by
  intro A η
  change Summable fun B ↦ (heisRep L A).indicator
    (fun B ↦ heisenbergPotential n J B
      (Potential.periodicExtend (Potential.latticeTorus d L) η)) B
  by_cases hA : ∃ x y : Fin d → ℤ, A = ({x, y} : Finset (Fin d → ℤ))
  · obtain ⟨x, y, rfl⟩ := hA
    by_cases hsub : ({x, y} : Finset (Fin d → ℤ)) ⊆ Potential.latticeBox d L
    · have hx : x ∈ Potential.latticeBox d L := hsub (Finset.mem_insert_self x {y})
      have hy : y ∈ Potential.latticeBox d L :=
        hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
      by_cases hxy : x = y
      · subst hxy
        rw [pair_self_eq_singleton]
        refine ((heisBond_self_injective (L := L) x).summable_iff (fun B hB ↦ ?_)).1 ?_
        · by_contra hc
          exact hB (support_subset_range_heisBond_self hJ0 hx η hc)
        · have hJs : Summable fun ρ : lexPos d ↦ J (Potential.intBoxLen L • (ρ : Fin d → ℤ)) :=
            (hsum.comp_injective (injective_intBoxLen_smul L)).subtype _
          refine ((hJs.mul_right (η x ⬝ᵥ η x)).neg).congr fun ρ ↦ ?_
          exact (indicator_heisRep_heisBond_self heven hx
            (fun h0 ↦ absurd (h0 ▸ mem_lexPos.1 ρ.2) (lt_irrefl _)) η).symm
      · refine ((heisBond_injective hx hy hxy).summable_iff (fun B hB ↦ ?_)).1 ?_
        · by_contra hc
          exact hB (support_subset_range_heisBond η hc)
        · have hinj2 : Function.Injective
              (fun r : Fin d → ℤ ↦ x - y - Potential.intBoxLen L • r) := by
            intro r r' h
            funext k
            have hk := congrFun h k
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hk
            exact mul_left_cancel₀ (Potential.intBoxLen_pos L).ne' (by linarith)
          refine (((hsum.comp_injective hinj2).mul_right (η x ⬝ᵥ η y)).neg).congr fun r ↦ ?_
          exact (indicator_heisRep_heisBond heven hx hy
            (ne_add_intBoxLen_smul_of_ne hx hy hxy r) η).symm
    · exact summable_zero.congr fun B ↦ by
        rw [heisRep_eq_empty_of_not_subset hsub]; simp
  · push Not at hA
    exact summable_zero.congr fun B ↦ (indicator_heisRep_eq_zero_of_forall_ne hA η B).symm

/-- **Georgii (2.2)(i) for `Φ̃^{Λ(N)}`.**  The periodic modification of a Heisenberg potential
with `Summable J` is a potential: `Φ̃^{Λ(N)}_A` is `𝓕_A`-measurable. -/
theorem isPotential_heisenbergPeriodicPotential (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (L : ℕ) : Potential.IsPotential (heisenbergPeriodicPotential n J L) :=
  (hasSummableRepSeries_heisenbergPotential hsum heven hJ0 L).isPotential

/-- `Φ̃^{Λ(N)}` is supported in the cube, hence has finite range (Georgii (2.15)); no summability
is needed for this, and it is what makes all its Hamiltonians finite sums. -/
instance isFiniteRange_heisenbergPeriodicPotential :
    Potential.IsFiniteRange (heisenbergPeriodicPotential n J L) :=
  Potential.isFiniteRange_periodicModification (Potential.isTorusReduction_latticeTorus d L)

/-! ### Georgii (17.24): the Hamiltonian in the cube -/

variable (J L) in
/-- The contribution of an *ordered* pair of sites of the cube to the Hamiltonian of `Φ̃^{Λ(N)}`.
A bond `{i, j}` with `i ≠ j` has two ordered representatives and a site `{i}` has one, which is
how the diagonal of Georgii (17.24) acquires its factor `1/2`. -/
private def heisPairTerm (η : (Fin d → ℤ) → (Fin n → ℝ))
    (p : (Fin d → ℤ) × (Fin d → ℤ)) : ℝ :=
  -(2 : ℝ)⁻¹ * (periodizedCoupling (L + 1) J (latticeToTorus L (p.1 - p.2)) * (η p.1 ⬝ᵥ η p.2))

/-- **Georgii (17.24), the Hamiltonian.**  The Hamiltonian in the cube `Λ(N)` of the periodic
modification of a Heisenberg potential is minus the exponent of (17.24): summing the interaction
terms `-J_Λ(i-j) σ_i·σ_j` over the bonds of `Λ(N)` and the self-energies `-½ J_Λ(0)|σ_i|²` over
its sites reassembles Georgii's `½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j`, diagonal included. -/
theorem interactingHamiltonian_heisenbergPeriodicPotential (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) (η : (Fin d → ℤ) → (Fin n → ℝ))
    (hη : ∀ i ∈ Potential.latticeBox d L, η i = ζ (latticeToTorus L i)) :
    Potential.interactingHamiltonian (Φ := heisenbergPeriodicPotential n J L)
        (Potential.latticeBox d L) η = -heisenbergExponent (L + 1) n J ζ := by
  classical
  have hT : Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L)
      (Potential.latticeBox d L)
      ⊆ (Potential.latticeBox d L ×ˢ Potential.latticeBox d L).image
        fun p ↦ ({p.1, p.2} : Finset (Fin d → ℤ)) := by
    intro A hA
    obtain ⟨-, hz⟩ := Potential.mem_interactingSupport.1 hA
    have hsub : A ⊆ Potential.latticeBox d L := by
      by_contra hc
      exact hz (Potential.periodicModification_of_not_subset
        (Potential.isTorusReduction_latticeTorus d L) hc)
    obtain ⟨x, y, rfl⟩ : ∃ x y, A = ({x, y} : Finset (Fin d → ℤ)) := by
      by_contra hc
      push Not at hc
      exact hz (funext fun σ ↦ heisenbergPeriodicPotential_of_forall_ne (fun x y ↦ hc x y) σ)
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2
      ⟨hsub (Finset.mem_insert_self x {y}),
        hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))⟩, rfl⟩
  have hzero : ∀ A ∈ (Potential.latticeBox d L ×ˢ Potential.latticeBox d L).image
      (fun p ↦ ({p.1, p.2} : Finset (Fin d → ℤ))),
      A ∉ Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L)
        (Potential.latticeBox d L) → heisenbergPeriodicPotential n J L A η = 0 := by
    intro A hA hnot
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨hp1, -⟩ := Finset.mem_product.1 hp
    by_cases hz : heisenbergPeriodicPotential n J L ({p.1, p.2} : Finset (Fin d → ℤ)) = 0
    · rw [hz]; rfl
    · exact absurd (Potential.mem_interactingSupport.2
        ⟨⟨p.1, by simp, by exact_mod_cast hp1⟩, hz⟩) hnot
  have heq : ∀ p ∈ Potential.latticeBox d L ×ˢ Potential.latticeBox d L,
      heisenbergPeriodicPotential n J L ({p.1, p.2} : Finset (Fin d → ℤ)) η
        = ∑ q ∈ (Potential.latticeBox d L ×ˢ Potential.latticeBox d L).filter
            (fun q ↦ ({q.1, q.2} : Finset (Fin d → ℤ)) = {p.1, p.2}), heisPairTerm L J η q := by
    rintro ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
    simp only at ha hb ⊢
    by_cases hab : a = b
    · subst hab
      have hfil : (Potential.latticeBox d L ×ˢ Potential.latticeBox d L).filter
          (fun q ↦ ({q.1, q.2} : Finset (Fin d → ℤ)) = {a, a}) = {(a, a)} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
          Finset.pair_eq_pair_iff, Prod.ext_iff]
        constructor
        · rintro ⟨-, h | h⟩ <;> exact ⟨h.1, h.2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1 ▸ ha, h2 ▸ ha⟩, Or.inl ⟨h1, h2⟩⟩
      rw [hfil, Finset.sum_singleton, pair_self_eq_singleton,
        heisenbergPeriodicPotential_singleton hsum heven hJ0 ha η]
      simp only [heisPairTerm, sub_self, latticeToTorus_zero]
      ring
    · have hfil : (Potential.latticeBox d L ×ˢ Potential.latticeBox d L).filter
          (fun q ↦ ({q.1, q.2} : Finset (Fin d → ℤ)) = {a, b}) = {(a, b), (b, a)} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, Finset.pair_eq_pair_iff, Prod.ext_iff]
        constructor
        · rintro ⟨-, h | h⟩
          · exact Or.inl ⟨h.1, h.2⟩
          · exact Or.inr ⟨h.1, h.2⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨⟨h1 ▸ ha, h2 ▸ hb⟩, Or.inl ⟨h1, h2⟩⟩
          · exact ⟨⟨h1 ▸ hb, h2 ▸ ha⟩, Or.inr ⟨h1, h2⟩⟩
      have hcomm : periodizedCoupling (L + 1) J (latticeToTorus L (b - a))
          = periodizedCoupling (L + 1) J (latticeToTorus L (a - b)) := by
        rw [show latticeToTorus L (b - a) = -latticeToTorus L (a - b) by
          rw [latticeToTorus_sub, latticeToTorus_sub]; abel, periodizedCoupling_neg heven]
      rw [hfil, Finset.sum_pair (fun h ↦ hab (congrArg Prod.fst h)),
        heisenbergPeriodicPotential_pair heven ha hb hab η]
      simp only [heisPairTerm, hcomm, dotProduct_comm (η b) (η a)]
      ring
  have key : ∑ p ∈ Potential.latticeBox d L ×ˢ Potential.latticeBox d L, heisPairTerm L J η p
      = -heisenbergExponent (L + 1) n J ζ := by
    rw [Finset.sum_product]
    have h1 : ∀ a ∈ Potential.latticeBox d L, ∑ b ∈ Potential.latticeBox d L,
        heisPairTerm L J η (a, b)
        = ∑ v, -(2 : ℝ)⁻¹ * (periodizedCoupling (L + 1) J (latticeToTorus L a - v)
            * (ζ (latticeToTorus L a) ⬝ᵥ ζ v)) := by
      intro a ha
      rw [← sum_latticeBox_comp_latticeToTorus (n := L)
        (fun v ↦ -(2 : ℝ)⁻¹ * (periodizedCoupling (L + 1) J (latticeToTorus L a - v)
          * (ζ (latticeToTorus L a) ⬝ᵥ ζ v)))]
      exact Finset.sum_congr rfl fun b hb ↦ by
        simp only [heisPairTerm, latticeToTorus_sub, hη a ha, hη b hb]
    rw [Finset.sum_congr rfl h1, sum_latticeBox_comp_latticeToTorus (n := L)
      (fun u ↦ ∑ v, -(2 : ℝ)⁻¹ * (periodizedCoupling (L + 1) J (u - v) * (ζ u ⬝ᵥ ζ v))),
      heisenbergExponent]
    simp only [← Finset.mul_sum]
    ring
  rw [Potential.interactingHamiltonian, Finset.sum_subset hT hzero,
    Finset.sum_image' (heisPairTerm L J η) heq, key]

end PeriodicModification

/-! ### Georgii (17.24): the Gibbs distribution with periodic boundary condition -/

section Identification

variable {ν : Measure (Fin n → ℝ)}

/-- The Boltzmann factor of `Φ̃^{Λ(N)}` in the cube, evaluated on a configuration which is
periodic inside the cube, is the density of Georgii (17.24). -/
theorem boltzmannFactor_heisenbergPeriodicPotential_periodicJuxt (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (ω : (Fin d → ℤ) → (Fin n → ℝ))
    (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :
    (heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L)
        (periodicJuxt (Fin n → ℝ) L ω ζ)
      = ENNReal.ofReal (Real.exp (heisenbergExponent (L + 1) n J ζ)) := by
  classical
  rw [Potential.boltzmannFactor, Potential.hamiltonian_eq_interactingHamiltonian,
    interactingHamiltonian_heisenbergPeriodicPotential hsum heven hJ0 ζ _
      (fun i hi ↦ periodicJuxt_apply_of_mem ζ hi)]
  norm_num

/-- **Georgii (17.24), before normalisation.**  Georgii's `°Z_Λ^Φ °γ_Λ^Φ` — the measure on the
torus with density `exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j]` relative to `λ^Λ` — read on `ℤ^d` by
freezing the configuration outside the cube, is the unnormalised finite-volume Gibbs distribution
`e^{-H^{Φ̃^{Λ(N)}}_{Λ(N)}} λ_{Λ(N)}(·|ω)` of the periodic modification of the Heisenberg
potential.  This is the computation Georgii performs to state (17.24). -/
theorem map_periodicJuxt_heisenbergPeriodicGibbs [SigmaFinite ν] (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisenbergPeriodicGibbs (L + 1) n J ν).map (periodicJuxt (Fin n → ℝ) L ω)
      = (Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := Fin n → ℝ) ν
            (Potential.latticeBox d L) ω).withDensity
          ((heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L)) := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  have hmeas : Measurable
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L)) := by
    have hb : (heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L)
        = Potential.boltzmannWeight (Φ := heisenbergPeriodicPotential n J L) 1
            (Potential.latticeBox d L) :=
      funext fun σ ↦ Potential.boltzmannFactor_eq_boltzmannWeight 1 _ σ
    rw [hb]
    exact Potential.measurable_boltzmannWeight 1 _
  have hdens : (fun ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergExponent (L + 1) n J ζ)))
      = fun ζ ↦ (heisenbergPeriodicPotential n J L).boltzmannFactor 1
        (Potential.latticeBox d L) (periodicJuxt (Fin n → ℝ) L ω ζ) :=
    funext fun ζ ↦
      (boltzmannFactor_heisenbergPeriodicPotential_periodicJuxt hsum heven hJ0 ω ζ).symm
  rw [heisenbergPeriodicGibbs, hdens,
    map_withDensity_comp _ (measurable_periodicJuxt L ω) hmeas,
    map_periodicJuxt_sigmaFiniteLambdaFun]

variable (n) in
/-- **Georgii's `γ^{Φ̃^{Λ(N)}}`** for a Heisenberg potential: the Gibbsian specification
(Definition (2.9)) of the periodic modification of (17.22) in the cube `Λ(N)`, at inverse
temperature `1` — Georgii carries `β` inside `J`.  The hypotheses are Georgii's (17.23) together
with `λ`-admissibility, which in the volume `Λ(N)` is his standing assumption `°Z_Λ^Φ < ∞`. -/
noncomputable def heisenbergPeriodicGibbsSpec (J : (Fin d → ℤ) → ℝ) (L : ℕ)
    (ν : Measure (Fin n → ℝ)) [SigmaFinite ν] [NeZero ν] (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1)) :
    Specification (Fin d → ℤ) (Fin n → ℝ) :=
  haveI := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  Potential.gibbsSpecificationOfSigmaFiniteAdmissible (heisenbergPeriodicPotential n J L) ν 1 hadm

/-- **Georgii (17.24) as a theorem.**  The projection onto `E^{Λ(N)}` of the Gibbs distribution
in `Λ(N)` with periodic boundary condition for the Heisenberg potential (17.22) is Georgii's
`°γ_{Λ(N)}^Φ`, the normalised measure with density `exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j]` relative
to `λ^Λ`: at every boundary condition `ω` the finite-volume Gibbs kernel of `Φ̃^{Λ(N)}` is
`°γ_{Λ(N)}^Φ × δ_ω`, the `ℤ^d`-embedded field of Example (5.20)(3). -/
theorem heisenbergPeriodicGibbsSpec_latticeBox [SigmaFinite ν] [NeZero ν] (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1))
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm (Potential.latticeBox d L) ω
      = (heisenbergPeriodicGibbsDist (L + 1) n J ν).map (periodicJuxt (Fin n → ℝ) L ω) := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  have hmap := map_periodicJuxt_heisenbergPeriodicGibbs (ν := ν) (L := L) hsum heven hJ0 ω
  have hmuniv : ((Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := Fin n → ℝ) ν
        (Potential.latticeBox d L) ω).withDensity
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L)))
      Set.univ = heisenbergPeriodicGibbs (L + 1) n J ν Set.univ := by
    rw [← hmap, Measure.map_apply (measurable_periodicJuxt L ω) MeasurableSet.univ]
    rfl
  have hrhs : (heisenbergPeriodicGibbsDist (L + 1) n J ν).map (periodicJuxt (Fin n → ℝ) L ω)
      = (heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)⁻¹ •
        ((Specification.sigmaFiniteLambdaFun (S := Fin d → ℤ) (E := Fin n → ℝ) ν
            (Potential.latticeBox d L) ω).withDensity
          ((heisenbergPeriodicPotential n J L).boltzmannFactor 1 (Potential.latticeBox d L))) := by
    rw [heisenbergPeriodicGibbsDist, Measure.map_smul, hmap]
  have hZ : Specification.sigmaFiniteLambdaZ (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1) (Potential.latticeBox d L) ω
      = heisenbergPeriodicGibbs (L + 1) n J ν Set.univ := by
    rw [← hmuniv, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      Specification.sigmaFiniteLambdaZ]
  refine Measure.ext fun A hA ↦ ?_
  rw [hrhs, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    heisenbergPeriodicGibbsSpec,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set _ _ _ _ _ _ hA, hZ]

end Identification

end MeasureTheory.GibbsMeasure

end

end
