/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.Pi
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiBlocks
public import GibbsMeasure.Specification.ErgodicDense
public import GibbsMeasure.Specification.SpecificEntropy

/-!
# The specific entropy of a randomly shifted independent-block field (Georgii (15.52))

Let `(C, H)` be a tiling of the group of sites `S` (`AddSubgroup.IsComplement`, Georgii: the cube
`Λ` of side `p` and the sublattice `pℤ^d`), let `λ` be an a priori probability measure on the state
space `E` and let `γ` be a probability measure on the tile, i.e. on `E^C`. Georgii's

* `γ̂ = ∏_{i} θ_{-pi}(γ)` is `tileProduct hCH γ` (`GibbsMeasure/Specification/ErgodicDense.lean`),
  the measure making the blocks `C + h`, `h ∈ H`, independent with law `γ`;
* `γ̃ = |Λ|⁻¹ ∑_{j ∈ Λ} θ_{-j}(γ̂)` is `tileAverage hCH γ`, which is ergodic by Theorem (14.12).

**Proposition (15.52)** states `𝓀(γ̃) = |Λ|⁻¹ 𝓗_Λ(γ)`.

## Main results

* `relativeEntropyIn_tileProduct`, **additivity over the blocks**: if `Δ` is a union of tiles
  (`IsTileUnion`), `𝓗_Δ(γ̂ | λ^S) = |K| 𝓗(γ | λ^C)` with `K` the set of tile indices met by `Δ`.
  The measure-theoretic content is that the relative entropy of two product measures is the sum
  of the relative entropies of the factors, `InformationTheory.klDiv_pi`.
* `card_mul_relativeEntropyIn_tileProduct_le`,
  `le_card_mul_relativeEntropyIn_tileProduct`, **the sandwich**: for `Δ⁻ ⊆ Δ ⊆ Δ⁺` with `Δ^±`
  unions of tiles, `|Δ⁻| 𝓗(γ | λ^C) ≤ |C| 𝓗_Δ(γ̂ | λ^S) ≤ |Δ⁺| 𝓗(γ | λ^C)`.
* `card_mul_relativeEntropyIn_tileAverage_le`,
  `le_card_mul_relativeEntropyIn_tileAverage_add`: the same sandwich for the *averaged* measure
  `γ̃`, up to the entropy `log |C|` of the uniform weights. This is where Georgii's "obvious
  extension of Proposition (15.14)" enters, as
  `MeasureTheory.GibbsMeasure.finset_sum_smul_relativeEntropyIn_le` (the `n`-ary convexity defect
  of the relative entropy) and `relativeEntropyIn_finset_sum_smul_le` (`n`-ary concavity), both
  in `GibbsMeasure/Specification/SpecificEntropy.lean`.
* `card_mul_relativeEntropyIn_tileAverage_le_sum`,
  `sum_relativeEntropyIn_le_card_mul_relativeEntropyIn_tileAverage_add`: Georgii's "obvious
  extension of Proposition (15.14)" for `γ̃`, the two halves of
  `|C| 𝓗_Λ(γ̃ | λ^S) = ∑_{j ∈ C} 𝓗_Λ(θ_j γ̂ | λ^S)` up to the entropy `log |C|` of the uniform
  weights.
* `specificEntropy_tileAveragePM`, `exists_tendsto_specificEntropy`, the **second assertion of
  Proposition (15.52)**: for `μ ∈ 𝓟_Θ` the randomly shifted independent repetitions of the
  `Λ(n)`-marginals of `μ` have specific entropy `|Λ(n)|⁻¹ 𝓗_{Λ(n)}(μ)`, so they converge to `μ`
  locally (Theorem (14.12)) with `𝓀(μ_n) → 𝓀(μ)` (Theorem (15.12)).
* `specificEntropy_tileAverage_of_sandwich`, **the limit argument of Proposition (15.52)** for
  any sequence of boxes of `ℤ^d` that are unions of tiles, sandwich the shifts `Δ_m - j` with a
  fixed lag and have cardinalities `c_m |C|` with `c_{m+r}/c_m → 1`: `𝓀(γ̃) = -𝓗(γ | λ^C) / |C|`.
* `specificEntropy_tileAverage`, **Proposition (15.52)** on `ℤ^d` (`d ≥ 1`) for the cube tiling
  `Λ(n) = [-n, n]^d`, `H = (2n+1) ℤ^d`: `𝓀(γ̃) = -𝓗(γ | λ^{Λ(n)}) / |Λ(n)|`, in Georgii's sign
  convention `𝓀(γ̃) = |Λ|⁻¹ 𝓗_Λ(γ)`. Georgii's cube `Δ` of the sandwich is `tileCube n (m+1)`,
  of radius `(m+1)p + n`; the cubes of radius `m p + n` and `(m+2) p + n` are the `Δ⁻` and `Δ⁺`
  that work simultaneously for all the shifts `Δ - j`, `j ∈ Λ(n)`
  (`isTileUnion_piFinset_Icc`, `tileCube_subset_image_sub`, `image_sub_subset_tileCube`).
* `specificEntropy_tileAverage_Icc`, **Proposition (15.52) for an arbitrary box**
  `∏_k [a_k, a_k + s_k]` and its tiling `isComplement_Icc a s` of `ErgodicDense.lean`, Georgii's
  cubes of even side included: `𝓀(γ̃) = -𝓗(γ | λ^Λ) / ∏_k (s_k + 1)`, the sandwich being the
  box unions `boxUnion a s N` with the lag `1 + ∑_k |a_k|`.

## The proof

Georgii computes `lim |Δ|⁻¹ 𝓗_Δ(γ̂^j)` for each shifted copy `γ̂^j = θ_j γ̂`, `j ∈ C`, by
sandwiching a cube `Δ` between the union `Δ⁻` of the tiles it contains and the union `Δ⁺` of the
tiles it meets, and then passes to the average by (15.14). We do the same, but everything is
carried out on the *relative* entropy `𝓗_Δ(· | λ^S) ∈ [0, ∞]` rather than on
`𝓗_Δ(·) = -𝓗_Δ(· | λ^S) ∈ [-∞, 0]`, so that the case `𝓗(γ | λ^C) = ∞` (a block law that is not
absolutely continuous with respect to `λ^C`) is handled honestly: it is exactly the case
`𝓀(γ̃) = -∞`.

Two remarks on the hypotheses.

* Georgii's `Λ` is a cube and his `S` is `ℤ^d`; the block additivity, the sandwich and the
  averaging need only a tiling `(C, H)` of an arbitrary abelian group of sites, and are stated at
  that generality (`relativeEntropyIn_tileProduct`, `card_mul_relativeEntropyIn_tileAverage_le`,
  `le_card_mul_relativeEntropyIn_tileAverage_add`); the limit argument is stated once, for any
  sequence of boxes of `ℤ^d` with the sandwich property, and instantiated twice: for the centred
  cubes `Λ(n) = [-n, n]^d` with the sublattice `(2n+1) ℤ^d`, and for an arbitrary box
  `∏_k [a_k, a_k + s_k]` with `∏_k (s_k + 1) ℤ^d`.
* The shifts `θ_j γ̂` are *not* shift invariant, so their entropy density is not `𝓀` of anything;
  only the average `γ̃` is a shift-invariant random field. This is why the limit is computed by
  hand on `𝓗_Δ` and only then compared with `𝓀(γ̃) = lim |Δ|⁻¹ 𝓗_Δ(γ̃)` of Theorem (15.12).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Real Topology
open InformationTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Additivity of the relative entropy over the blocks -/

section Blocks

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {C : Finset S} {H : AddSubgroup S}
  (hCH : AddSubgroup.IsComplement (C : Set S) (H : Set S))
  (lam : Measure E) [IsProbabilityMeasure lam]
  (γ : Measure (C → E)) [IsProbabilityMeasure γ]

/-- **The relative entropy of the independent-block field in a union of tiles.** If `Δ` is the
union of the `|K|` tiles indexed by `K = tileIdxImage hCH Δ`, then
`𝓗_Δ(γ̂ | λ^S) = |K| 𝓗(γ | λ^C)`: the blocks are independent with common law `γ`, and the
relative entropy of a product is the sum of the relative entropies (`klDiv_pi`). -/
theorem relativeEntropyIn_tileProduct {Δ : Finset S} (h : IsTileUnion hCH Δ) :
    relativeEntropyIn (Δ : Set S) (tileProduct hCH γ) (Measure.infinitePi fun _ : S ↦ lam)
      = #(tileIdxImage hCH Δ) * klDiv γ (Measure.pi fun _ : C ↦ lam) := by
  classical
  have hβm : Measurable ⇑(blockEquiv (E := E) hCH h) := (blockEquiv hCH h).measurable
  have hmapγ : ((tileProduct hCH γ).map Δ.restrict).map (blockEquiv (E := E) hCH h)
      = Measure.pi fun _ : tileIdxImage hCH Δ ↦ γ := by
    rw [tileProduct, Measure.map_map (Finset.measurable_restrict Δ) (tilingEquiv hCH).measurable,
      Measure.map_map hβm ((Finset.measurable_restrict Δ).comp (tilingEquiv hCH).measurable),
      blockEquiv_comp_finsetRestrict_comp_tilingEquiv, Measure.infinitePi_map_restrict]
  have hmapLam : ((Measure.infinitePi fun _ : S ↦ lam).map Δ.restrict).map
        (blockEquiv (E := E) hCH h)
      = Measure.pi fun _ : tileIdxImage hCH Δ ↦ Measure.pi fun _ : C ↦ lam := by
    rw [Measure.infinitePi_map_restrict, blockEquiv_eq_comp_tileSite]
    exact (measurePreserving_blocks lam (injective_tileSite hCH h)).map_eq
  rw [relativeEntropyIn_coe_finset, ← klDiv_map_measurableEquiv _ _ (blockEquiv (E := E) hCH h),
    hmapγ, hmapLam, klDiv_pi_const, Fintype.card_coe]

omit [DecidableEq S] in
/-- **The upper half of Georgii's sandwich.** If `Δ` is contained in a union of tiles `Δ⁺`, then
`|C| 𝓗_Δ(γ̂ | λ^S) ≤ |Δ⁺| 𝓗(γ | λ^C)`. -/
theorem card_mul_relativeEntropyIn_tileProduct_le {Δ Δ' : Finset S} (h : IsTileUnion hCH Δ')
    (hsub : Δ ⊆ Δ') :
    (#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileProduct hCH γ)
        (Measure.infinitePi fun _ : S ↦ lam)
      ≤ #Δ' * klDiv γ (Measure.pi fun _ : C ↦ lam) := by
  classical
  calc (#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileProduct hCH γ)
          (Measure.infinitePi fun _ : S ↦ lam)
      ≤ (#C : ℝ≥0∞) * relativeEntropyIn (Δ' : Set S) (tileProduct hCH γ)
          (Measure.infinitePi fun _ : S ↦ lam) := by
        gcongr
        exact relativeEntropyIn_mono (by exact_mod_cast hsub)
    _ = (#C : ℝ≥0∞) * (#(tileIdxImage hCH Δ') * klDiv γ (Measure.pi fun _ : C ↦ lam)) := by
        rw [relativeEntropyIn_tileProduct hCH lam γ h]
    _ = #Δ' * klDiv γ (Measure.pi fun _ : C ↦ lam) := by
        rw [← mul_assoc, ← Nat.cast_mul, mul_comm (#C), ← card_of_isTileUnion hCH h]

omit [DecidableEq S] in
/-- **The lower half of Georgii's sandwich.** If `Δ` contains a union of tiles `Δ⁻`, then
`|Δ⁻| 𝓗(γ | λ^C) ≤ |C| 𝓗_Δ(γ̂ | λ^S)`. -/
theorem le_card_mul_relativeEntropyIn_tileProduct {Δ Δ' : Finset S} (h : IsTileUnion hCH Δ')
    (hsub : Δ' ⊆ Δ) :
    (#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam)
      ≤ (#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileProduct hCH γ)
          (Measure.infinitePi fun _ : S ↦ lam) := by
  classical
  calc (#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam)
      = (#C : ℝ≥0∞) * (#(tileIdxImage hCH Δ') * klDiv γ (Measure.pi fun _ : C ↦ lam)) := by
        rw [← mul_assoc, ← Nat.cast_mul, mul_comm (#C), ← card_of_isTileUnion hCH h]
    _ = (#C : ℝ≥0∞) * relativeEntropyIn (Δ' : Set S) (tileProduct hCH γ)
          (Measure.infinitePi fun _ : S ↦ lam) := by
        rw [relativeEntropyIn_tileProduct hCH lam γ h]
    _ ≤ _ := by
        gcongr
        exact relativeEntropyIn_mono (by exact_mod_cast hsub)

end Blocks

/-! ### The randomly shifted field `γ̃` -/

section Average

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {C : Finset S} {H : AddSubgroup S}
  (hCH : AddSubgroup.IsComplement (C : Set S) (H : Set S))
  (lam : Measure E) [IsProbabilityMeasure lam]
  (γ : Measure (C → E)) [IsProbabilityMeasure γ]

include hCH in
omit [DecidableEq S] [IsProbabilityMeasure lam] [IsProbabilityMeasure γ] in
private lemma nnreal_card_ne_zero : ((#C : ℝ≥0))⁻¹ ≠ 0 := by
  simp only [ne_eq, inv_eq_zero, Nat.cast_eq_zero]
  exact (nonempty_of_isComplement hCH).card_pos.ne'

include hCH in
omit [DecidableEq S] [IsProbabilityMeasure lam] [IsProbabilityMeasure γ] in
private lemma ennreal_card_ne_zero : ((#C : ℝ≥0∞)) ≠ 0 := by
  simp only [ne_eq, Nat.cast_eq_zero]
  exact (nonempty_of_isComplement hCH).card_pos.ne'

omit [DecidableEq S] [IsProbabilityMeasure lam] [IsProbabilityMeasure γ] in
/-- `γ̃` as a finite mixture with uniform weights. -/
lemma tileAverage_eq_finset_sum_smul :
    tileAverage hCH γ
      = ∑ j ∈ C, ((#C : ℝ≥0))⁻¹ • ((tileProduct hCH γ).map (shift E j).toFun) := by
  have hne : ((#C : ℝ≥0)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (nonempty_of_isComplement hCH).card_pos.ne'
  rw [tileAverage, uniformAverage, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  refine Measure.ext fun s _ ↦ ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [ENNReal.coe_inv hne, ENNReal.coe_natCast]

omit [DecidableEq S] in
/-- **The concavity half of Georgii's "obvious extension of (15.14)" for `γ̃`**:
`|C| 𝓗_Λ(γ̃ | λ^S) ≤ ∑_{j ∈ C} 𝓗_Λ(θ_j γ̂ | λ^S)`. -/
theorem card_mul_relativeEntropyIn_tileAverage_le_sum (Λ : Set S) :
    (#C : ℝ≥0∞) * relativeEntropyIn Λ (tileAverage hCH γ) (Measure.infinitePi fun _ : S ↦ lam)
      ≤ ∑ j ∈ C, relativeEntropyIn Λ ((tileProduct hCH γ).map (shift E j).toFun)
          (Measure.infinitePi fun _ : S ↦ lam) := by
  have hne : ((#C : ℝ≥0)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (nonempty_of_isComplement hCH).card_pos.ne'
  have hsum : ∑ _j ∈ C, ((#C : ℝ≥0))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hne]
  have h := relativeEntropyIn_finset_sum_smul_le (s := C) (a := fun _ ↦ ((#C : ℝ≥0))⁻¹) hsum
    (fun j ↦ (tileProduct hCH γ).map (shift E j).toFun)
    (Measure.infinitePi fun _ : S ↦ lam) Λ
  rw [← tileAverage_eq_finset_sum_smul hCH γ] at h
  calc (#C : ℝ≥0∞) * relativeEntropyIn Λ (tileAverage hCH γ)
        (Measure.infinitePi fun _ : S ↦ lam)
      ≤ (#C : ℝ≥0∞) * ∑ j ∈ C, ((((#C : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞)
          * relativeEntropyIn Λ ((tileProduct hCH γ).map (shift E j).toFun)
            (Measure.infinitePi fun _ : S ↦ lam) := by gcongr
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← mul_assoc, ENNReal.coe_inv hne, ENNReal.coe_natCast,
          ENNReal.mul_inv_cancel (ennreal_card_ne_zero hCH) (ENNReal.natCast_ne_top _), one_mul]

omit [DecidableEq S] in
/-- **The convexity-defect half of Georgii's "obvious extension of (15.14)" for `γ̃`**:
`∑_{j ∈ C} 𝓗_Λ(θ_j γ̂ | λ^S) ≤ |C| 𝓗_Λ(γ̃ | λ^S) + |C| log |C|`. -/
theorem sum_relativeEntropyIn_le_card_mul_relativeEntropyIn_tileAverage_add (Λ : Set S) :
    ∑ j ∈ C, relativeEntropyIn Λ ((tileProduct hCH γ).map (shift E j).toFun)
        (Measure.infinitePi fun _ : S ↦ lam)
      ≤ (#C : ℝ≥0∞) * relativeEntropyIn Λ (tileAverage hCH γ)
            (Measure.infinitePi fun _ : S ↦ lam)
        + (#C : ℝ≥0∞) * ENNReal.ofReal (log (#C : ℝ)) := by
  have hne : ((#C : ℝ≥0)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact (nonempty_of_isComplement hCH).card_pos.ne'
  have hposR : (0 : ℝ) < (#C : ℝ) := by
    exact_mod_cast (nonempty_of_isComplement hCH).card_pos
  have hsum : ∑ _j ∈ C, ((#C : ℝ≥0))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hne]
  have hpos : ∀ j ∈ C, (0 : ℝ≥0) < ((#C : ℝ≥0))⁻¹ := fun j _ ↦ by positivity
  have h := finset_sum_smul_relativeEntropyIn_le (s := C) (a := fun _ ↦ ((#C : ℝ≥0))⁻¹) hpos hsum
    (fun j ↦ (tileProduct hCH γ).map (shift E j).toFun)
    (Measure.infinitePi fun _ : S ↦ lam) Λ
  rw [← tileAverage_eq_finset_sum_smul hCH γ] at h
  -- the entropy of the uniform weights is `log |C|`
  have hcoe : ((((#C : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) = ((#C : ℝ))⁻¹ := by
    rw [NNReal.coe_inv, NNReal.coe_natCast]
  have hweights : ∑ _j ∈ C, ENNReal.ofReal (-(((((#C : ℝ≥0))⁻¹ : ℝ≥0) : ℝ)
        * log ((((#C : ℝ≥0))⁻¹ : ℝ≥0) : ℝ)))
      = ENNReal.ofReal (log (#C : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (#C),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    rw [hcoe, Real.log_inv]
    field_simp
  calc ∑ j ∈ C, relativeEntropyIn Λ ((tileProduct hCH γ).map (shift E j).toFun)
        (Measure.infinitePi fun _ : S ↦ lam)
      = (#C : ℝ≥0∞) * ∑ j ∈ C, ((((#C : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞)
          * relativeEntropyIn Λ ((tileProduct hCH γ).map (shift E j).toFun)
            (Measure.infinitePi fun _ : S ↦ lam) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← mul_assoc, ENNReal.coe_inv hne, ENNReal.coe_natCast,
          ENNReal.mul_inv_cancel (ennreal_card_ne_zero hCH) (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ (#C : ℝ≥0∞) * (relativeEntropyIn Λ (tileAverage hCH γ)
            (Measure.infinitePi fun _ : S ↦ lam) + ENNReal.ofReal (log (#C : ℝ))) := by
        gcongr
        rw [← hweights]
        exact h
    _ = _ := by rw [mul_add]

/-- **Georgii's sandwich for the randomly shifted field, upper half.** If every shifted volume
`Δ - j`, `j ∈ C`, is contained in the union of tiles `Δ⁺`, then
`|C| 𝓗_Δ(γ̃ | λ^S) ≤ |Δ⁺| 𝓗(γ | λ^C)`. -/
theorem card_mul_relativeEntropyIn_tileAverage_le {Δ Δ' : Finset S} (h' : IsTileUnion hCH Δ')
    (hsub : ∀ j ∈ C, Δ.image (· - j) ⊆ Δ') :
    (#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileAverage hCH γ)
        (Measure.infinitePi fun _ : S ↦ lam)
      ≤ #Δ' * klDiv γ (Measure.pi fun _ : C ↦ lam) := by
  rw [← ENNReal.mul_le_mul_iff_right (ennreal_card_ne_zero hCH) (ENNReal.natCast_ne_top _)]
  calc (#C : ℝ≥0∞) * ((#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileAverage hCH γ)
          (Measure.infinitePi fun _ : S ↦ lam))
      ≤ (#C : ℝ≥0∞) * ∑ j ∈ C, relativeEntropyIn (Δ : Set S)
          ((tileProduct hCH γ).map (shift E j).toFun)
            (Measure.infinitePi fun _ : S ↦ lam) := by
        gcongr
        exact card_mul_relativeEntropyIn_tileAverage_le_sum hCH lam γ _
    _ = ∑ j ∈ C, (#C : ℝ≥0∞) * relativeEntropyIn ((Δ.image (· - j) : Finset S) : Set S)
          (tileProduct hCH γ) (Measure.infinitePi fun _ : S ↦ lam) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [relativeEntropyIn_map_shift lam (Δ : Set S) j, Finset.coe_image]
    _ ≤ ∑ _j ∈ C, (#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam) :=
        Finset.sum_le_sum fun j hj ↦
          card_mul_relativeEntropyIn_tileProduct_le hCH lam γ h' (hsub j hj)
    _ = (#C : ℝ≥0∞) * ((#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Georgii's sandwich for the randomly shifted field, lower half.** If every shifted volume
`Δ - j`, `j ∈ C`, contains the union of tiles `Δ⁻`, then
`|Δ⁻| 𝓗(γ | λ^C) ≤ |C| 𝓗_Δ(γ̃ | λ^S) + |C| log |C|`; the defect `log |C|` is the entropy of the
uniform weights in Georgii's extension of (15.14). -/
theorem le_card_mul_relativeEntropyIn_tileAverage_add {Δ Δ' : Finset S} (h' : IsTileUnion hCH Δ')
    (hsub : ∀ j ∈ C, Δ' ⊆ Δ.image (· - j)) :
    (#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam)
      ≤ (#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileAverage hCH γ)
            (Measure.infinitePi fun _ : S ↦ lam)
        + (#C : ℝ≥0∞) * ENNReal.ofReal (log (#C : ℝ)) := by
  rw [← ENNReal.mul_le_mul_iff_right (ennreal_card_ne_zero hCH) (ENNReal.natCast_ne_top _)]
  calc (#C : ℝ≥0∞) * ((#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam))
      = ∑ _j ∈ C, (#Δ' : ℝ≥0∞) * klDiv γ (Measure.pi fun _ : C ↦ lam) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ C, (#C : ℝ≥0∞) * relativeEntropyIn ((Δ.image (· - j) : Finset S) : Set S)
          (tileProduct hCH γ) (Measure.infinitePi fun _ : S ↦ lam) :=
        Finset.sum_le_sum fun j hj ↦
          le_card_mul_relativeEntropyIn_tileProduct hCH lam γ h' (hsub j hj)
    _ = (#C : ℝ≥0∞) * ∑ j ∈ C, relativeEntropyIn (Δ : Set S)
          ((tileProduct hCH γ).map (shift E j).toFun)
            (Measure.infinitePi fun _ : S ↦ lam) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [relativeEntropyIn_map_shift lam (Δ : Set S) j, Finset.coe_image]
    _ ≤ (#C : ℝ≥0∞) * ((#C : ℝ≥0∞) * relativeEntropyIn (Δ : Set S) (tileAverage hCH γ)
            (Measure.infinitePi fun _ : S ↦ lam)
          + (#C : ℝ≥0∞) * ENNReal.ofReal (log (#C : ℝ))) := by
        gcongr
        exact sum_relativeEntropyIn_le_card_mul_relativeEntropyIn_tileAverage_add hCH lam γ _

end Average

/-! ### The limit argument of Proposition (15.52) -/

section Sandwich

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {C : Finset (ι → ℤ)} {H : AddSubgroup (ι → ℤ)}
  (hCH : AddSubgroup.IsComplement (C : Set (ι → ℤ)) (H : Set (ι → ℤ)))
  (lam : Measure E) [IsProbabilityMeasure lam]
  (γ : Measure (C → E)) [IsProbabilityMeasure γ]

/-- **The limit argument of Georgii's Proposition (15.52), for any sequence of tile unions.**
Let `Δ_m = [lo_m, hi_m]` be boxes of `ℤ^d`, each the union of `c_m` tiles of the tiling `hCH`,
whose side lengths tend to infinity, such that for a fixed lag `r` every shift `Δ_m − j` by a tile
point `j ∈ C` lies in `Δ_{m+r}` and contains ... more precisely `Δ_m ⊆ Δ_{m+r} − j`, and with
`c_{m+r}/c_m → 1`, `c_m → ∞`. Then the specific entropy of the randomly shifted independent-block
field `γ̃ = tileAverage hCH γ` is `−𝓗(γ | λ^C)/|C|`, in `[−∞, 0]`, the value `𝓗(γ | λ^C) = ∞` giving
`−∞`.

The two sandwich inequalities `card_mul_relativeEntropyIn_tileAverage_le` and
`le_card_mul_relativeEntropyIn_tileAverage_add` give `|C| 𝓗_{Δ_m}(γ̃) ≤ |Δ_{m+r}| 𝓗(γ|λ^C)` and
`|Δ_m| 𝓗(γ|λ^C) ≤ |C| 𝓗_{Δ_{m+r}}(γ̃) + |C| log |C|`; dividing by `|Δ_m|` and letting `m → ∞`
squeezes `|Δ_m|⁻¹ 𝓗_{Δ_m}(γ̃)` to `𝓗(γ|λ^C)/|C|`, and Theorem (15.12) identifies the limit with
`−𝓀(γ̃)` because `γ̃` is shift invariant. -/
theorem specificEntropy_tileAverage_of_sandwich {lo hi : ℕ → ι → ℤ} {r : ℕ} {c : ℕ → ℕ}
    (htile : ∀ m, IsTileUnion hCH (Finset.Icc (lo m) (hi m)))
    (hsub₁ : ∀ m, ∀ j ∈ C,
      (Finset.Icc (lo m) (hi m)).image (· - j) ⊆ Finset.Icc (lo (m + r)) (hi (m + r)))
    (hsub₂ : ∀ m, ∀ j ∈ C,
      Finset.Icc (lo m) (hi m) ⊆ (Finset.Icc (lo (m + r)) (hi (m + r))).image (· - j))
    (hcard : ∀ m, #(Finset.Icc (lo m) (hi m)) = c m * #C)
    (hcpos : ∀ m, 0 < c m)
    (hratio : Tendsto (fun m ↦ (c (m + r) : ℝ) / c m) atTop (𝓝 1))
    (hc : Tendsto (fun m ↦ (c m : ℝ)) atTop atTop)
    (hside : ∀ k, Tendsto (fun m ↦ hi m k - lo m k) atTop atTop) :
    specificEntropy lam (tileAverage hCH γ)
      = -((klDiv γ (Measure.pi fun _ : C ↦ lam) : ℝ≥0∞) : EReal) / (#C : EReal) := by
  classical
  set ν := tileAverage hCH γ with hνdef
  set κ := klDiv γ (Measure.pi fun _ : C ↦ lam) with hκdef
  set q : ℕ := #C with hqdef
  set R : ℕ → ℝ≥0∞ := fun m ↦
    relativeEntropyIn (Finset.Icc (lo m) (hi m) : Set (ι → ℤ)) ν
      (Measure.infinitePi fun _ : ι → ℤ ↦ lam) with hRdef
  have hq0 : 0 < q := (nonempty_of_isComplement hCH).card_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq0
  have hlogq : 0 ≤ log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq0)
  have hqE : ((q : ℕ) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hq0.ne'
  have hqT : ((q : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hlohi : ∀ m, lo m ≤ hi m := fun m ↦ by
    by_contra h
    have h0 := hcard m
    rw [Finset.Icc_eq_empty h, Finset.card_empty] at h0
    exact absurd h0.symm (Nat.mul_pos (hcpos m) hq0).ne'
  have hbox : ∀ m, (Finset.Icc (lo m) (hi m)).IsBox := fun m ↦ Finset.isBox_Icc (hlohi m)
  have hU : ∀ m, ((q : ℕ) : ℝ≥0∞) * R m ≤ ((c (m + r) * q : ℕ) : ℝ≥0∞) * κ := fun m ↦ by
    have h := card_mul_relativeEntropyIn_tileAverage_le hCH lam γ (htile (m + r)) (hsub₁ m)
    rwa [hcard (m + r)] at h
  have hL : ∀ m, ((c m * q : ℕ) : ℝ≥0∞) * κ
      ≤ ((q : ℕ) : ℝ≥0∞) * R (m + r)
        + ((q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (log ((q : ℕ) : ℝ)) := fun m ↦ by
    have h := le_card_mul_relativeEntropyIn_tileAverage_add hCH lam γ (htile m) (hsub₂ m)
    rwa [hcard m] at h
  have hcardR : ∀ m, (#(Finset.Icc (lo m) (hi m)) : ℝ) = (c m : ℝ) * q := fun m ↦ by
    rw [hcard m]; push_cast; ring
  by_cases hκtop : κ = ⊤
  · -- both sides are `-∞`
    have hRr : R r = ⊤ := by
      have hl := hL 0
      rw [hκtop] at hl
      have hne : ((c 0 * q : ℕ) : ℝ≥0∞) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact (Nat.mul_pos (hcpos 0) hq0).ne'
      rw [ENNReal.mul_top hne, top_le_iff, ENNReal.add_eq_top] at hl
      rcases hl with hl | hl
      · rcases ENNReal.mul_eq_top.1 hl with ⟨_, h2⟩ | ⟨h2, _⟩
        · simpa using h2
        · exact absurd h2 hqT
      · exact absurd hl (ENNReal.mul_ne_top hqT ENNReal.ofReal_ne_top)
    have hent : entropyIn lam (Finset.Icc (lo r) (hi r) : Set (ι → ℤ)) ν = ⊥ := by
      change -((R r : ℝ≥0∞) : EReal) = ⊥
      rw [hRr]
      simp
    have hcardr : #(Finset.Icc (lo r) (hi r)) ≠ 0 := by
      rw [hcard r]
      exact (Nat.mul_pos (hcpos r) hq0).ne'
    have hbot : specificEntropy lam ν = ⊥ :=
      le_antisymm ((specificEntropy_le_entropyIn_div_card lam (hbox r)).trans
        (le_of_eq (by rw [hent, EReal.bot_div_natCast hcardr]))) bot_le
    rw [hbot, hκtop, EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_div_natCast hq0.ne']
  · -- the finite case: a two-sided estimate and a squeeze
    set Hr := κ.toReal with hHrdef
    have hHr0 : (0 : ℝ) ≤ Hr := ENNReal.toReal_nonneg
    have hRne : ∀ m, R m ≠ ⊤ := by
      intro m hcon
      have hu := hU m
      rw [hcon, ENNReal.mul_top hqE, top_le_iff] at hu
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hκtop hu
    have hU' : ∀ m, (q : ℝ) * (R m).toReal ≤ (c (m + r) : ℝ) * q * Hr := by
      intro m
      have h1 : (((q : ℕ) : ℝ≥0∞) * R m).toReal ≤ (((c (m + r) * q : ℕ) : ℝ≥0∞) * κ).toReal :=
        (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hqT (hRne m))
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hκtop)).2 (hU m)
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast] at h1
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    have hL' : ∀ m, (c m : ℝ) * q * Hr ≤ (q : ℝ) * (R (m + r)).toReal + (q : ℝ) * log (q : ℝ) := by
      intro m
      have h1 : (((c m * q : ℕ) : ℝ≥0∞) * κ).toReal
          ≤ (((q : ℕ) : ℝ≥0∞) * R (m + r)
              + ((q : ℕ) : ℝ≥0∞) * ENNReal.ofReal (log ((q : ℕ) : ℝ))).toReal :=
        (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hκtop)
          (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hqT (hRne (m + r)),
            ENNReal.mul_ne_top hqT ENNReal.ofReal_ne_top⟩)).2 (hL m)
      rw [ENNReal.toReal_add (ENNReal.mul_ne_top hqT (hRne (m + r)))
          (ENNReal.mul_ne_top hqT ENNReal.ofReal_ne_top),
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlogq] at h1
      refine le_trans (le_of_eq ?_) h1
      push_cast
      ring
    set g : ℕ → ℝ := fun m ↦ (R m).toReal / ((c m : ℝ) * q) with hgdef
    have hcR : ∀ m, (0 : ℝ) < (c m : ℝ) := fun m ↦ by exact_mod_cast hcpos m
    have hNpos : ∀ m, (0 : ℝ) < (c m : ℝ) * q := fun m ↦ mul_pos (hcR m) hqR
    have hhi : ∀ m, g m ≤ ((c (m + r) : ℝ) / c m) * (Hr / q) := by
      intro m
      have h2 : (R m).toReal ≤ (c (m + r) : ℝ) * Hr := by
        have h3 := hU' m
        nlinarith [hqR]
      rw [hgdef]
      simp only
      rw [div_le_iff₀ (hNpos m)]
      have hcm0 : (c m : ℝ) ≠ 0 := (hcR m).ne'
      have : (c (m + r) : ℝ) / c m * (Hr / q) * ((c m : ℝ) * q) = (c (m + r) : ℝ) * Hr := by
        field_simp
      rw [this]
      exact h2
    have hlo : ∀ m, ((c m : ℝ) / c (m + r)) * (Hr / q) - log (q : ℝ) / ((c (m + r) : ℝ) * q)
        ≤ g (m + r) := by
      intro m
      have h2 : (c m : ℝ) * Hr - log (q : ℝ) ≤ (R (m + r)).toReal := by
        have h3 := hL' m
        nlinarith [hqR]
      rw [hgdef]
      simp only
      rw [le_div_iff₀ (hNpos (m + r))]
      have hcmr0 : (c (m + r) : ℝ) ≠ 0 := (hcR (m + r)).ne'
      have : ((c m : ℝ) / c (m + r) * (Hr / q) - log (q : ℝ) / ((c (m + r) : ℝ) * q))
          * ((c (m + r) : ℝ) * q) = (c m : ℝ) * Hr - log (q : ℝ) := by
        field_simp
      rw [this]
      exact h2
    have hglim : Tendsto g atTop (𝓝 (Hr / q)) := by
      rw [← tendsto_add_atTop_iff_nat r]
      have hhi' : Tendsto (fun m : ℕ ↦ ((c (m + r + r) : ℝ) / c (m + r)) * (Hr / q))
          atTop (𝓝 (1 * (Hr / q))) :=
        Tendsto.mul_const _ (hratio.comp (tendsto_add_atTop_nat r))
      have hz : Tendsto (fun m : ℕ ↦ log (q : ℝ) / ((c (m + r) : ℝ) * q)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.Tendsto.atTop_mul_const hqR (hc.comp (tendsto_add_atTop_nat r)))
      have hinv : Tendsto (fun m : ℕ ↦ ((c m : ℝ) / c (m + r))) atTop (𝓝 1) := by
        have h := hratio.inv₀ one_ne_zero
        rw [inv_one] at h
        refine h.congr fun m ↦ ?_
        rw [inv_div]
      have hlo' : Tendsto (fun m : ℕ ↦ ((c m : ℝ) / c (m + r)) * (Hr / q)
          - log (q : ℝ) / ((c (m + r) : ℝ) * q)) atTop (𝓝 (1 * (Hr / q) - 0)) :=
        Tendsto.sub (Tendsto.mul_const _ hinv) hz
      rw [one_mul] at hhi'
      rw [one_mul, sub_zero] at hlo'
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo' hhi' hlo fun m ↦ hhi (m + r)
    have hdens : ∀ m,
        entropyIn lam (Finset.Icc (lo m) (hi m) : Set (ι → ℤ)) ν
            / (#(Finset.Icc (lo m) (hi m)) : EReal) = ((-g m : ℝ) : EReal) := by
      intro m
      have h1 : entropyIn lam (Finset.Icc (lo m) (hi m) : Set (ι → ℤ)) ν
          = ((-(R m).toReal : ℝ) : EReal) := by
        change -((R m : ℝ≥0∞) : EReal) = _
        rw [← EReal.coe_ennreal_toReal (hRne m), ← EReal.coe_neg]
      have h2 : ((#(Finset.Icc (lo m) (hi m)) : ℕ) : EReal) = (((c m : ℝ) * q : ℝ) : EReal) := by
        rw [← EReal.coe_natCast, hcardR m]
      rw [h1, h2, ← EReal.coe_div, hgdef]
      congr 1
      simp only
      rw [neg_div]
    have htend : Tendsto (fun m : ℕ ↦
        entropyIn lam (Finset.Icc (lo m) (hi m) : Set (ι → ℤ)) ν
          / (#(Finset.Icc (lo m) (hi m)) : EReal)) atTop (𝓝 (specificEntropy lam ν)) :=
      tendsto_entropyIn_div_card (lam := lam) (μ := ν) (l := atTop)
        (tileAverage_mem_invariantFields_shiftGroup hCH γ) (m := lo) (n := hi) hside
    have hlim : Tendsto (fun m : ℕ ↦
        entropyIn lam (Finset.Icc (lo m) (hi m) : Set (ι → ℤ)) ν
          / (#(Finset.Icc (lo m) (hi m)) : EReal)) atTop (𝓝 ((-(Hr / q) : ℝ) : EReal)) :=
      (EReal.tendsto_coe.2 hglim.neg).congr fun m ↦ (hdens m).symm
    rw [tendsto_nhds_unique htend hlim, ← EReal.coe_ennreal_toReal hκtop, ← hHrdef,
      ← EReal.coe_natCast (n := q), ← EReal.coe_neg, ← EReal.coe_div]
    congr 1
    rw [neg_div]

end Sandwich

/-! ### The cube tiling of `ℤ^d`

Georgii's `Λ` is a cube of side `p = 2n+1` and his sublattice is `p ℤ^d`; the cubes `Λ(A)` of
radius `A = M p + n` are exactly the unions of tiles among the centred cubes. -/

section Lattice

variable {d : ℕ} {E : Type*} [MeasurableSpace E]

private lemma mem_piFinset_Icc_iff {A : ℤ} {x : Fin d → ℤ} :
    x ∈ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A) ↔ ∀ k, |x k| ≤ A := by
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

private lemma piFinset_Icc_eq_Icc (A : ℤ) :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A)
      = Finset.Icc (fun _ ↦ -A) (fun _ : Fin d ↦ A) := by
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, Pi.le_def]
  exact ⟨fun h ↦ ⟨fun k ↦ (h k).1, fun k ↦ (h k).2⟩, fun h k ↦ ⟨h.1 k, h.2 k⟩⟩

/-- The elementary estimate behind "a centred cube of radius `M p + n` is a union of tiles": for
`|a| ≤ n` and `p = 2n + 1`, one has `|a + p i| ≤ M p + n` if and only if `|i| ≤ M`. -/
private lemma abs_add_mul_le_iff (n M : ℕ) {a i : ℤ} (ha : |a| ≤ (n : ℤ)) :
    |a + (2 * (n : ℤ) + 1) * i| ≤ (M : ℤ) * (2 * (n : ℤ) + 1) + n ↔ |i| ≤ (M : ℤ) := by
  have hp : (0 : ℤ) < 2 * (n : ℤ) + 1 := by positivity
  constructor
  · intro hle
    by_contra hi
    rw [not_le] at hi
    have h1 : (M : ℤ) + 1 ≤ |i| := hi
    have h2 : |(2 * (n : ℤ) + 1) * i| - |a| ≤ |a + (2 * (n : ℤ) + 1) * i| := by
      have h := abs_sub_abs_le_abs_sub ((2 * (n : ℤ) + 1) * i) (-a)
      rw [abs_neg, sub_neg_eq_add, add_comm ((2 * (n : ℤ) + 1) * i) a] at h
      exact h
    rw [abs_mul, abs_of_pos hp] at h2
    nlinarith
  · intro hi
    calc |a + (2 * (n : ℤ) + 1) * i| ≤ |a| + |(2 * (n : ℤ) + 1) * i| := abs_add_le _ _
      _ = |a| + (2 * (n : ℤ) + 1) * |i| := by rw [abs_mul, abs_of_pos hp]
      _ ≤ (n : ℤ) + (2 * (n : ℤ) + 1) * (M : ℤ) := by gcongr
      _ = (M : ℤ) * (2 * (n : ℤ) + 1) + n := by ring

/-- **The centred cube of radius `M p + n` is a union of tiles** of the tiling of `ℤ^d` by the
cubes `Λ(n) = [-n, n]^d` and the sublattice `p ℤ^d`, `p = 2n + 1`: membership depends only on the
tile index. -/
theorem isTileUnion_piFinset_Icc (n M : ℕ) :
    IsTileUnion (isComplement_piFinset_Icc (d := d) n)
      (Fintype.piFinset fun _ : Fin d ↦
        Finset.Icc (-((M * (2 * n + 1) + n : ℕ) : ℤ)) ((M * (2 * n + 1) + n : ℕ) : ℤ)) := by
  intro x y hxy
  set hCH := isComplement_piFinset_Icc (d := d) n with hCHdef
  have hcoe : (tileIdx hCH x : Fin d → ℤ) = (tileIdx hCH y : Fin d → ℤ) := congrArg Subtype.val hxy
  have hrep : ∀ z : Fin d → ℤ, ∀ k, |(tileRep hCH z : Fin d → ℤ) k| ≤ (n : ℤ) := by
    intro z k
    have hz := Fintype.mem_piFinset.1 (tileRep hCH z).2 k
    rw [Finset.mem_Icc] at hz
    exact abs_le.2 ⟨hz.1, hz.2⟩
  have hdvd : ∀ k, (2 * (n : ℤ) + 1) ∣ (tileIdx hCH x : Fin d → ℤ) k := fun k ↦
    Int.mem_zmultiples_iff.1 ((AddSubgroup.mem_pi _).1 (tileIdx hCH x).2 k (Set.mem_univ k))
  choose i hi using hdvd
  have hsplit : ∀ z : Fin d → ℤ, ∀ k,
      z k = (tileRep hCH z : Fin d → ℤ) k + (tileIdx hCH z : Fin d → ℤ) k := fun z k ↦
    (congrFun (coe_tileRep_add_coe_tileIdx hCH z) k).symm
  have hx' : ∀ k, x k = (tileRep hCH x : Fin d → ℤ) k + (2 * (n : ℤ) + 1) * i k := fun k ↦ by
    rw [hsplit x k, hi k]
  have hy' : ∀ k, y k = (tileRep hCH y : Fin d → ℤ) k + (2 * (n : ℤ) + 1) * i k := fun k ↦ by
    rw [hsplit y k, ← hcoe, hi k]
  have hcast : ((M * (2 * n + 1) + n : ℕ) : ℤ) = (M : ℤ) * (2 * (n : ℤ) + 1) + n := by
    push_cast
    ring
  simp only [mem_piFinset_Icc_iff, hcast]
  constructor <;> intro hmem k
  · rw [hy' k, abs_add_mul_le_iff n M (hrep y k), ← abs_add_mul_le_iff n M (hrep x k), ← hx' k]
    exact hmem k
  · rw [hx' k, abs_add_mul_le_iff n M (hrep x k), ← abs_add_mul_le_iff n M (hrep y k), ← hy' k]
    exact hmem k

/-- A centred cube is symmetric. -/
private lemma neg_mem_piFinset_Icc {A : ℤ} {j : Fin d → ℤ}
    (hj : j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A) :
    -j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A := by
  rw [mem_piFinset_Icc_iff] at hj ⊢
  intro k
  rw [Pi.neg_apply, abs_neg]
  exact hj k

/-- Shifting a centred cube by an element of a centred cube stays in the sum cube. -/
private lemma add_mem_piFinset_Icc {A B : ℤ} {x j : Fin d → ℤ}
    (hx : x ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A)
    (hj : j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-B) B) :
    x + j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(A + B)) (A + B) := by
  rw [mem_piFinset_Icc_iff] at hx hj ⊢
  intro k
  exact (abs_add_le _ _).trans (add_le_add (hx k) (hj k))

private lemma piFinset_Icc_mono {A B : ℤ} (h : A ≤ B) :
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-A) A)
      ⊆ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-B) B := by
  intro x hx
  rw [mem_piFinset_Icc_iff] at hx ⊢
  exact fun k ↦ (hx k).trans h

end Lattice

/-! ### Georgii Proposition (15.52) -/

section Prop1552

variable {d : ℕ} {E : Type*} [MeasurableSpace E] (lam : Measure E) [IsProbabilityMeasure lam]
  (n : ℕ) (γ : Measure ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) → E))
  [IsProbabilityMeasure γ]

/-- The centred cube of radius `M p + n`, `p = 2n + 1`: a union of `(2M+1)^d` tiles. -/
private def tileCube (M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d ↦
    Finset.Icc (-((M * (2 * n + 1) + n : ℕ) : ℤ)) ((M * (2 * n + 1) + n : ℕ) : ℤ)

private lemma card_tileCube (M : ℕ) :
    #(tileCube (d := d) n M) = (2 * M + 1) ^ d * (2 * n + 1) ^ d := by
  rw [tileCube, card_piFinset_Icc, ← mul_pow]
  congr 1
  ring

private lemma card_tile : #(Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n)
    = (2 * n + 1) ^ d := card_piFinset_Icc n

private lemma isTileUnion_tileCube (M : ℕ) :
    IsTileUnion (isComplement_piFinset_Icc (d := d) n) (tileCube (d := d) n M) :=
  isTileUnion_piFinset_Icc n M

private lemma tileCube_eq_Icc (M : ℕ) :
    tileCube (d := d) n M
      = Finset.Icc (fun _ ↦ -((M * (2 * n + 1) + n : ℕ) : ℤ))
          (fun _ : Fin d ↦ ((M * (2 * n + 1) + n : ℕ) : ℤ)) :=
  piFinset_Icc_eq_Icc _

/-- Every shift `Δ - j`, `j ∈ Λ(n)`, of the cube of radius `(m+1)p + n` contains the cube of
radius `m p + n`. -/
private lemma tileCube_subset_image_sub (m : ℕ) {j : Fin d → ℤ}
    (hj : j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) :
    tileCube (d := d) n m ⊆ (tileCube (d := d) n (m + 1)).image (· - j) := by
  intro x hx
  refine Finset.mem_image.2 ⟨x + j, ?_, by abel⟩
  have h := add_mem_piFinset_Icc hx hj
  refine piFinset_Icc_mono ?_ h
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℤ) m, Nat.cast_nonneg (α := ℤ) n]

/-- Every shift `Δ - j`, `j ∈ Λ(n)`, of the cube of radius `(m+1)p + n` is contained in the cube
of radius `(m+2)p + n`. -/
private lemma image_sub_subset_tileCube (m : ℕ) {j : Fin d → ℤ}
    (hj : j ∈ Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) :
    (tileCube (d := d) n (m + 1)).image (· - j) ⊆ tileCube (d := d) n (m + 2) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  have h := add_mem_piFinset_Icc hx (neg_mem_piFinset_Icc hj)
  rw [← sub_eq_add_neg] at h
  refine piFinset_Icc_mono ?_ h
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℤ) m, Nat.cast_nonneg (α := ℤ) n]

/-- **Georgii's sandwich for the cubes of `ℤ^d`, upper half.** -/
private lemma card_tile_mul_relativeEntropyIn_le (m : ℕ) :
    (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞)
        * relativeEntropyIn (tileCube (d := d) n (m + 1) : Set (Fin d → ℤ))
            (tileAverage (isComplement_piFinset_Icc n) γ)
            (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam)
      ≤ (((2 * (m + 2) + 1) ^ d * (2 * n + 1) ^ d : ℕ) : ℝ≥0∞)
          * klDiv γ (Measure.pi fun _ ↦ lam) := by
  have h := card_mul_relativeEntropyIn_tileAverage_le (isComplement_piFinset_Icc (d := d) n) lam γ
    (isTileUnion_tileCube n (m + 2)) fun j hj ↦ image_sub_subset_tileCube n m hj
  rwa [card_tile, card_tileCube] at h

/-- **Georgii's sandwich for the cubes of `ℤ^d`, lower half.** -/
private lemma le_card_tile_mul_relativeEntropyIn_add (m : ℕ) :
    (((2 * m + 1) ^ d * (2 * n + 1) ^ d : ℕ) : ℝ≥0∞) * klDiv γ (Measure.pi fun _ ↦ lam)
      ≤ (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞)
          * relativeEntropyIn (tileCube (d := d) n (m + 1) : Set (Fin d → ℤ))
              (tileAverage (isComplement_piFinset_Icc n) γ)
              (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam)
        + (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞)
            * ENNReal.ofReal (log (((2 * n + 1) ^ d : ℕ) : ℝ)) := by
  have h := le_card_mul_relativeEntropyIn_tileAverage_add (isComplement_piFinset_Icc (d := d) n)
    lam γ (isTileUnion_tileCube n m) fun j hj ↦ tileCube_subset_image_sub n m hj
  rwa [card_tile, card_tileCube] at h

private lemma tendsto_ratio (c : ℝ) (d : ℕ) :
    Tendsto (fun m : ℕ ↦ ((2 * (m : ℝ) + 3 + c) / (2 * (m : ℝ) + 3)) ^ d) atTop (𝓝 1) := by
  have hden : Tendsto (fun m : ℕ ↦ (2 * (m : ℝ) + 3)) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos).atTop_add tendsto_const_nhds
  have h0 : Tendsto (fun m : ℕ ↦ c / (2 * (m : ℝ) + 3)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h1 : Tendsto (fun m : ℕ ↦ (2 * (m : ℝ) + 3 + c) / (2 * (m : ℝ) + 3)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun m : ℕ ↦ 1 + c / (2 * (m : ℝ) + 3)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h2
    refine h2.congr fun m ↦ ?_
    have h3 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
    field_simp
  simpa using h1.pow d

/-- **Georgii Proposition (15.52)** on `S = ℤ^d`, `d ≥ 1`. Let `Λ = Λ(n) = [-n, n]^d` be a cube of
side `p = 2n + 1`, let `γ` be a probability measure on `E^Λ`, let `γ̂ = ∏_i θ_{-pi}(γ)` be the
measure making the blocks `Λ + p i` independent with law `γ` (`tileProduct`) and let
`γ̃ = |Λ|⁻¹ ∑_{j ∈ Λ} θ_{-j}(γ̂)` be its random shift (`tileAverage`). Then `γ̃` is an ergodic
shift-invariant random field (`tileAverage_mem_extremePoints_invariantFields`, Theorem (14.12))
and its specific entropy is the entropy per site of the block law:
`𝓀(γ̃) = |Λ|⁻¹ 𝓗_Λ(γ) = -𝓗(γ | λ^Λ) / |Λ|`. -/
theorem specificEntropy_tileAverage [NeZero d] :
    specificEntropy lam (tileAverage (isComplement_piFinset_Icc n) γ)
      = -((klDiv γ (Measure.pi fun _ ↦ lam) : ℝ≥0∞) : EReal)
          / (((2 * n + 1) ^ d : ℕ) : EReal) := by
  have hcube : ∀ m : ℕ, Finset.Icc (fun _ : Fin d ↦ -(((m + 1) * (2 * n + 1) + n : ℕ) : ℤ))
      (fun _ : Fin d ↦ (((m + 1) * (2 * n + 1) + n : ℕ) : ℤ)) = tileCube (d := d) n (m + 1) :=
    fun m ↦ (tileCube_eq_Icc n (m + 1)).symm
  have h := specificEntropy_tileAverage_of_sandwich (isComplement_piFinset_Icc (d := d) n) lam γ
    (lo := fun m _ ↦ -(((m + 1) * (2 * n + 1) + n : ℕ) : ℤ))
    (hi := fun m _ ↦ (((m + 1) * (2 * n + 1) + n : ℕ) : ℤ)) (r := 1) (c := fun m ↦ (2 * m + 3) ^ d)
    (fun m ↦ by rw [hcube m]; exact isTileUnion_tileCube n (m + 1))
    (fun m j hj ↦ by rw [hcube m, hcube (m + 1)]; exact image_sub_subset_tileCube n m hj)
    (fun m j hj ↦ by rw [hcube m, hcube (m + 1)]; exact tileCube_subset_image_sub n (m + 1) hj)
    (fun m ↦ by rw [hcube m, card_tileCube, card_tile]; ring)
    (fun m ↦ by positivity)
    (by
      have h := tendsto_ratio 2 d
      refine h.congr fun m ↦ ?_
      have h5 : (2 * (m : ℝ) + 3 + 2) = 2 * ((m : ℝ) + 1) + 3 := by ring
      push_cast
      rw [div_pow, h5])
    (((tendsto_pow_atTop (NeZero.ne d)).comp
      (((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos).atTop_add
        (tendsto_const_nhds (x := (3 : ℝ))))).congr fun m ↦ by
          simp only [Function.comp]; push_cast; ring)
    (fun k ↦ by
      refine tendsto_atTop_mono (fun j ↦ ?_) (tendsto_natCast_atTop_atTop (R := ℤ))
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℤ) n, Nat.cast_nonneg (α := ℤ) j])
  rw [card_tile] at h
  exact h

/-- **Georgii Proposition (15.52), the specific entropy of the block average is the entropy
density of the block law.** For `μ ∈ 𝓟_Θ` and the cube `Λ(n) = [-n, n]^d`, the randomly shifted
independent repetition of the `Λ(n)`-marginal of `μ` has specific entropy `|Λ(n)|⁻¹ 𝓗_{Λ(n)}(μ)`;
this is the finite-volume entropy density of `μ` itself. -/
theorem specificEntropy_tileAveragePM [NeZero d] (μ : ProbabilityMeasure ((Fin d → ℤ) → E)) :
    specificEntropy lam (tileAveragePM (isComplement_piFinset_Icc (d := d) n) μ :
        Measure ((Fin d → ℤ) → E))
      = entropyIn lam ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n :
            Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) (μ : Measure ((Fin d → ℤ) → E))
          / (#(Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n :
              Finset (Fin d → ℤ)) : EReal) := by
  rw [coe_tileAveragePM, specificEntropy_tileAverage lam n
    ((μ : Measure ((Fin d → ℤ) → E)).map
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n : Finset (Fin d → ℤ)).restrict),
    card_piFinset_Icc]
  congr 2
  rw [relativeEntropyIn_coe_finset, Measure.infinitePi_map_restrict]

/-- **Georgii Proposition (15.52), second assertion.** For every shift-invariant random field `μ`
on `ℤ^d`, `d ≥ 1`, there is a sequence `(μ_n)` of *ergodic* shift-invariant random fields with
`μ_n → μ` in the topology of local convergence and `𝓀(μ_n) → 𝓀(μ)`: take the randomly shifted
independent repetitions `μ_n = v_n` of the `Λ(n)`-marginals of `μ` (Theorem (14.12)), whose
specific entropies are the finite-volume entropy densities `|Λ(n)|⁻¹ 𝓗_{Λ(n)}(μ)` of `μ`, which
converge to `𝓀(μ)` by Theorem (15.12). -/
theorem exists_tendsto_specificEntropy [NeZero d] {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hμ : (μ : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)) :
    ∃ ν : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E),
      (∀ m, (ν m : Measure ((Fin d → ℤ) → E)) ∈
          (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞) ∧
        Tendsto (fun m ↦ (WithSetwiseTopology.ofMeasure (ν m) :
            WithLocalConvergence (Fin d → ℤ) E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) ∧
        Tendsto (fun m ↦ specificEntropy lam (ν m : Measure ((Fin d → ℤ) → E))) atTop
          (𝓝 (specificEntropy lam (μ : Measure ((Fin d → ℤ) → E)))) := by
  refine ⟨fun m ↦ tileAveragePM (isComplement_piFinset_Icc (d := d) m) μ, fun m ↦ ?_, ?_, ?_⟩
  · simpa only [coe_tileAveragePM] using
      tileAverage_mem_extremePoints_invariantFields (isComplement_piFinset_Icc (d := d) m)
        (γ := (μ : Measure ((Fin d → ℤ) → E)).map
          (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(m : ℤ)) m : Finset (Fin d → ℤ)).restrict)
  · exact tendsto_tileAverage (isComplement_piFinset_Icc (d := d))
      tendsto_card_filter_sub_notMem_piFinset_Icc_div hμ
  · have h := tendsto_entropyIn_div_card (lam := lam) (μ := (μ : Measure ((Fin d → ℤ) → E)))
      (l := atTop) hμ (m := fun m : ℕ ↦ fun _ : Fin d ↦ -(m : ℤ))
      (n := fun m : ℕ ↦ fun _ : Fin d ↦ (m : ℤ)) ?_
    · refine h.congr fun m ↦ ?_
      rw [← piFinset_Icc_eq_Icc]
      exact (specificEntropy_tileAveragePM lam m μ).symm
    · intro k
      have h1 : Tendsto (fun j : ℕ ↦ (j : ℤ)) atTop atTop := tendsto_natCast_atTop_atTop
      refine tendsto_atTop_mono (fun j ↦ ?_) h1
      omega

end Prop1552

/-! ### Georgii Proposition (15.52) for an arbitrary box -/

section Box1552

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  (lam : Measure E) [IsProbabilityMeasure lam] (a : ι → ℤ) (s : ι → ℕ)
  (γ : Measure ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) → E)) [IsProbabilityMeasure γ]

private lemma tendsto_ratio_shift (r D : ℕ) :
    Tendsto (fun N : ℕ ↦ ((2 * ((N + r : ℕ) : ℝ) + 1) / (2 * (N : ℝ) + 1)) ^ D) atTop (𝓝 1) := by
  have hden : Tendsto (fun N : ℕ ↦ (2 * (N : ℝ) + 1)) atTop atTop :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos).atTop_add tendsto_const_nhds
  have h0 : Tendsto (fun N : ℕ ↦ (2 * (r : ℝ)) / (2 * (N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h1 : Tendsto (fun N : ℕ ↦ (2 * ((N + r : ℕ) : ℝ) + 1) / (2 * (N : ℝ) + 1)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun N : ℕ ↦ 1 + (2 * (r : ℝ)) / (2 * (N : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h2
    refine h2.congr fun N ↦ ?_
    have h3 : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  simpa using h1.pow D

/-- **Georgii Proposition (15.52) for an arbitrary box.** Let `Λ = ∏_k [a_k, a_k + s_k]` be a box
of `ℤ^d`, `d ≥ 1`, with any base point and any side lengths (Georgii's cubes of even side
included), and let `γ` be a probability measure on `E^Λ`. The randomly shifted independent-block
field `γ̃` of the tiling of `ℤ^d` by the translates of `Λ` has specific entropy
`𝓀(γ̃) = -𝓗(γ | λ^Λ) / |Λ|`, with `|Λ| = ∏_k (s_k + 1)`. -/
theorem specificEntropy_tileAverage_Icc :
    specificEntropy lam (tileAverage (isComplement_Icc a s) γ)
      = -((klDiv γ (Measure.pi fun _ ↦ lam) : ℝ≥0∞) : EReal)
          / ((∏ k, (s k + 1) : ℕ) : EReal) := by
  set m₀ : ℕ := ∑ k, (a k).natAbs with hm₀def
  have hm₀ : ∀ k, |a k| ≤ (m₀ : ℤ) := fun k ↦ by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.single_le_sum (fun k _ ↦ Nat.zero_le ((a k).natAbs))
      (Finset.mem_univ k)
  have hD : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have h := specificEntropy_tileAverage_of_sandwich (isComplement_Icc a s) lam γ
    (lo := fun N k ↦ a k - N * ((s k : ℤ) + 1))
    (hi := fun N k ↦ a k + s k + N * ((s k : ℤ) + 1))
    (r := 1 + m₀) (c := fun N ↦ (2 * N + 1) ^ Fintype.card ι)
    (fun N ↦ isTileUnion_boxUnion a s N)
    (fun N j hj ↦ by rw [← Nat.add_assoc]; exact image_sub_boxUnion_subset a s hm₀ N hj)
    (fun N j hj ↦ by rw [← Nat.add_assoc]; exact boxUnion_subset_image_sub a s hm₀ N hj)
    (fun N ↦ by rw [card_Icc_add]; exact card_boxUnion a s N)
    (fun N ↦ by positivity)
    (by
      have h := tendsto_ratio_shift (1 + m₀) (Fintype.card ι)
      refine h.congr fun N ↦ ?_
      push_cast
      rw [div_pow])
    (((tendsto_pow_atTop hD).comp
      (((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos).atTop_add
        (tendsto_const_nhds (x := (1 : ℝ))))).congr fun N ↦ by
          simp only [Function.comp]; push_cast; ring)
    (fun k ↦ by
      refine tendsto_atTop_mono (fun N ↦ ?_) (tendsto_natCast_atTop_atTop (R := ℤ))
      have hs : (0 : ℤ) ≤ s k := Int.natCast_nonneg _
      have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg _
      nlinarith)
  rw [card_Icc_add] at h
  exact h

end Box1552

end MeasureTheory.GibbsMeasure
