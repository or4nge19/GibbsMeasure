/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Limits of ratios with a controlled numerator

If `‖u j − v j‖ ≤ t j` eventually and `t j → 0`, then `u` and `v` have the same limits
(`Filter.Tendsto.of_norm_sub_le`). Dividing by a common `c j`, the same holds for the ratios
`u j / c j` and `v j / c j` as soon as `t j / ‖c j‖ → 0` (`Filter.Tendsto.div_of_norm_sub_le`);
this is the shape in which "`u j = v j + o(c j)`" is used for normalised sums over growing boxes.
-/

@[expose] public section

open Filter Topology

namespace Filter.Tendsto

variable {κ : Type*} {l : Filter κ}

/-- If `v → L` and `‖u j − v j‖ ≤ t j` eventually with `t → 0`, then `u → L`. -/
theorem of_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] {u v : κ → E} {t : κ → ℝ} {L : E}
    (hv : Tendsto v l (𝓝 L)) (hle : ∀ᶠ j in l, ‖u j - v j‖ ≤ t j) (ht : Tendsto t l (𝓝 0)) :
    Tendsto u l (𝓝 L) :=
  hv.congr_dist <| squeeze_zero_norm' (hle.mono fun j hj ↦ by
    rwa [Real.norm_of_nonneg dist_nonneg, dist_comm, dist_eq_norm]) ht

/-- If `v j / c j → L` and `‖u j − v j‖ ≤ t j` eventually with `t j / ‖c j‖ → 0`, then
`u j / c j → L`. -/
theorem div_of_norm_sub_le {𝕜 : Type*} [NormedField 𝕜] {u v c : κ → 𝕜} {t : κ → ℝ} {L : 𝕜}
    (hv : Tendsto (fun j ↦ v j / c j) l (𝓝 L)) (hle : ∀ᶠ j in l, ‖u j - v j‖ ≤ t j)
    (ht : Tendsto (fun j ↦ t j / ‖c j‖) l (𝓝 0)) :
    Tendsto (fun j ↦ u j / c j) l (𝓝 L) :=
  hv.of_norm_sub_le (hle.mono fun j hj ↦ by
    rw [← sub_div, norm_div]
    exact div_le_div_of_nonneg_right hj (norm_nonneg _)) ht

end Filter.Tendsto
