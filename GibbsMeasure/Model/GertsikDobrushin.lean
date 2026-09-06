/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.IsingOceans

/-!
# Georgii 18.3.3: the Gertsik–Dobrushin model

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.3.  The `C`-potential **(18.29)**

`Φ_C = -J₁ ∑_{{i,j} ⊆ C, |i-j|=1} σ_i σ_j - J₂ ∑_{{i,j} ⊆ C, |i-j|=√2} σ_i σ_j - h ∑_{i ∈ C} σ_i`

on `E = {-1, 1}` (`Bool` through `spin`) in the plane, with a nearest-neighbour coupling `J₁`, a
next-nearest-neighbour coupling `J₂` and an external field `h`.  It contains the Ising
ferromagnet (18.27) (`J₁ = 1, J₂ = h = 0`) and the antiferromagnet (18.28)
(`J₁ = -1, J₂ = 0`) of `GibbsMeasure/Model/IsingOceans.lean`.

## The value table

`gdCube_values` is the complete list of the values of `Φ_C` on the sixteen configurations of the
unit square, which is what makes each of Georgii's four parameter regions a finite computation:

| configurations | number | `Φ_C` |
|---|---|---|
| the two constants `(++)`, `(--)` | `2` | `-4J₁ - 2J₂ ∓ 4h` |
| the two staggered ones | `2` | `4J₁ - 2J₂` |
| the four striped ones | `4` | `2J₂` |
| the eight with a single reversed spin | `8` | `∓2h` |

## Main results

Georgii's four regions in which Theorem (18.25) applies.  In each the local ground states are
identified exactly (`localGroundStates` is then handled by
`exists_pos_localGroundStates_subset`, valid over any finite state space), the partition into
singletons is stable by a finite check on the four faces of `C`, and the members are exchanged by
explicit elements of `I_{C,λ}(Φ)`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {J₁ J₂ h : ℝ}

/-- **Georgii (18.29)**: the Gertsik–Dobrushin `C`-potential of the plane. -/
abbrev gdCube (J₁ J₂ h : ℝ) : ((Fin 2 → Fin 2) → Bool) → ℝ := fun ζ ↦
  -J₁ * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ
    - J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ
    - h * cubeSiteSum 2 spin ζ

lemma measurable_gdCube : Measurable (gdCube J₁ J₂ h) := Measurable.of_discrete

/-- **Condition (iii) of Georgii (17.18)** for (18.29). -/
lemma gdCube_cubeRefl (k : Fin 2) (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h (cubeRefl Bool k ζ) = gdCube J₁ J₂ h ζ := by
  simp only [gdCube, cubeBondSum_cubeRefl, cubeSiteSum_cubeRefl,
    sqDiagSum_cubeRefl (fun x y ↦ mul_comm _ _) k ζ]

/-- **`|Φ_C| ≤ 4|J₁| + 2|J₂| + 4|h|`** for (18.29), the first alternative of condition (iv) of
(17.18). -/
lemma abs_gdCube_le (ζ : (Fin 2 → Fin 2) → Bool) :
    |gdCube J₁ J₂ h ζ| ≤ 4 * |J₁| + 2 * |J₂| + 4 * |h| := by
  have hb1 := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ spin x * spin y) (m := -1) (ζ := ζ)
    fun c c' ↦ neg_one_le_spin_mul_spin _ _
  have hb2 := cubeBondSum_le (d := 2) (ψ := fun x y ↦ spin x * spin y) (M := 1) (ζ := ζ)
    fun c c' ↦ spin_mul_spin_le_one _ _
  have hd1 := sqDiagSum_ge (ψ := fun x y ↦ spin x * spin y) (m := -1) (ζ := ζ)
    fun x y ↦ neg_one_le_spin_mul_spin _ _
  have hd2 := sqDiagSum_le (ψ := fun x y ↦ spin x * spin y) (M := 1) (ζ := ζ)
    fun x y ↦ spin_mul_spin_le_one _ _
  have hs1 := cubeSiteSum_ge (d := 2) (v := spin) (m := -1) (ζ := ζ) fun c ↦ neg_one_le_spin _
  have hs2 := cubeSiteSum_le (d := 2) (v := spin) (M := 1) (ζ := ζ) fun c ↦ spin_le_one _
  norm_num at hb1 hb2 hs1 hs2 hd1 hd2
  have hb : |cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ| ≤ 4 := abs_le.2 ⟨hb1, hb2⟩
  have hd : |sqDiagSum (fun x y ↦ spin x * spin y) ζ| ≤ 2 := abs_le.2 ⟨hd1, hd2⟩
  have hs : |cubeSiteSum 2 spin ζ| ≤ 4 := abs_le.2 ⟨hs1, hs2⟩
  have h1 : |(-J₁) * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ| ≤ |J₁| * 4 := by
    rw [abs_mul, abs_neg]; gcongr
  have h2 : |J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ| ≤ |J₂| * 2 := by
    rw [abs_mul]; gcongr
  have h3 : |h * cubeSiteSum 2 spin ζ| ≤ |h| * 4 := by rw [abs_mul]; gcongr
  calc |gdCube J₁ J₂ h ζ|
      ≤ |(-J₁) * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ
          - J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ| + |h * cubeSiteSum 2 spin ζ| := by
        simpa only [gdCube, sub_eq_add_neg, abs_neg] using
          abs_add_le ((-J₁) * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ
            - J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ) (-(h * cubeSiteSum 2 spin ζ))
    _ ≤ (|(-J₁) * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ|
          + |J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ|)
        + |h * cubeSiteSum 2 spin ζ| := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le ((-J₁) * cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ)
            (-(J₂ * sqDiagSum (fun x y ↦ spin x * spin y) ζ))
    _ ≤ 4 * |J₁| + 2 * |J₂| + 4 * |h| := by linarith

/-- **The value of (18.29) on a configuration of the unit square**, in Georgii's notation
`ω = (w z / u v)`: the four nearest-neighbour bonds, the two diagonals and the four sites. -/
lemma gdCube_apply (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h ζ =
      -J₁ * (spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 1 0))
          + spin (ζ (sqCorner 0 1)) * spin (ζ (sqCorner 1 1))
          + spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 0 1))
          + spin (ζ (sqCorner 1 0)) * spin (ζ (sqCorner 1 1)))
        - J₂ * (spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 1 1))
          + spin (ζ (sqCorner 1 0)) * spin (ζ (sqCorner 0 1)))
        - h * (spin (ζ (sqCorner 0 0)) + spin (ζ (sqCorner 1 0))
          + spin (ζ (sqCorner 0 1)) + spin (ζ (sqCorner 1 1))) := by
  rw [gdCube, cubeBondSum_two (fun x y ↦ by rw [mul_comm]) ζ, sqDiagSum_def, cubeSiteSum_def,
    sum_univ_cubeCorners]


/-! ### The symmetries of (18.29)

Georgii: "`I_{C,λ}(Φ)` always contains the rotation `r_0` and the reflections `r_1` and `r_2`.
If `h = 0` then `I_{C,λ}(Φ)` also contains the spin-flip, and if `h = J₁ = 0` then the
sublattice spin-flip `ω → ((-1)^{i_1+i_2} ω_i)` is a further symmetry of `Φ`." -/

/-- Georgii's rotation `r_0` (18.20) is a symmetry of (18.29) for all parameters. -/
lemma gdCube_onCube_planeRot (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h ((CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun ζ)
      = gdCube J₁ J₂ h ζ := by
  have hb := cubeBondSum_onCube_of_spin_refl (ψ := fun x y ↦ spin x * spin y)
    (CubeTransformation.planeRot (E := Bool) (d := 0)) (fun _ ↦ rfl) ζ
  have hs := cubeSiteSum_onCube_of_spin_refl (v := spin)
    (CubeTransformation.planeRot (E := Bool) (d := 0)) (fun _ ↦ rfl) ζ
  have hd := sqDiagSum_onCube_planeRot (ψ := fun x y ↦ spin x * spin y)
    (fun x y ↦ mul_comm _ _) ζ
  simp only [gdCube]
  rw [hb, hs, hd]

/-- **Every spatial cube transformation is a symmetry of (18.29)**: the nearest-neighbour bonds,
the diagonals and the sites of `C` are permuted among themselves by a cube isometry. -/
theorem isSymmetry_of_spin_refl_gdCube (τ : CubeTransformation Bool 2)
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl Bool) :
    τ.IsSymmetry (gdCube J₁ J₂ h) uniformSpinMeasure :=
  CubeTransformation.isSymmetry_of_spin_refl gdCube_cubeRefl hτ fun ζ ↦ by
    have hb := cubeBondSum_onCube_of_spin_refl (ψ := fun x y ↦ spin x * spin y) τ hτ ζ
    have hd := sqDiagSum_onCube_of_spin_refl (ψ := fun x y ↦ spin x * spin y)
      (fun x y ↦ mul_comm _ _) τ hτ ζ
    have hs := cubeSiteSum_onCube_of_spin_refl (v := spin) τ hτ ζ
    simp only [gdCube]
    rw [hb, hd, hs]

theorem isSymmetry_planeRot_gdCube :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (gdCube J₁ J₂ h) uniformSpinMeasure :=
  isSymmetry_of_spin_refl_gdCube _ fun _ ↦ rfl

theorem isSymmetry_refl_gdCube (k : Fin 2) :
    (CubeTransformation.refl (E := Bool) k).IsSymmetry (gdCube J₁ J₂ h) uniformSpinMeasure :=
  isSymmetry_of_spin_refl_gdCube _ fun _ ↦ rfl

/-- **The spin flip reverses the external field**: `Φ^{J₁,J₂,h}_C ∘ τ = Φ^{J₁,J₂,-h}_C`.  Hence
`τ ∈ I_{C,λ}(Φ)` exactly when Georgii's `h = 0`. -/
lemma gdCube_onCube_isingSpinFlip (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h ((isingSpinFlip 2).onCube.toFun ζ) = gdCube J₁ J₂ (-h) ζ := by
  have hval : ∀ c, (isingSpinFlip 2).onCube.toFun ζ c = !(ζ c) := fun c ↦ by
    rw [CubeTransformation.pureSpin_onCube_toFun_apply]
    rfl
  rw [gdCube_apply, gdCube_apply]
  simp only [hval, spin_not]
  ring

theorem isSymmetry_isingSpinFlip_gdCube :
    (isingSpinFlip 2).IsSymmetry (gdCube J₁ J₂ 0) uniformSpinMeasure :=
  CubeTransformation.IsSymmetry.of_apply_onCube gdCube_cubeRefl
    (fun _ ↦ measurePreserving_boolNot_uniformSpinMeasure)
    fun ζ ↦ by rw [gdCube_onCube_isingSpinFlip, neg_zero]

/-- **Georgii's sublattice spin flip** `ω → ((-1)^{i_1+i_2} ω_i)`, a pure spin transformation
(18.21) of `T_{C,λ}`: it reverses the spins on the corners of parity `p` only.  Every
nearest-neighbour bond of `C` joins corners of opposite parity and every diagonal joins corners
of equal parity, so it reverses the nearest-neighbour term and the field term and fixes the
next-nearest-neighbour term. -/
abbrev sublatticeFlip (p : Fin 2) : CubeTransformation Bool 2 :=
  CubeTransformation.pureSpin fun c ↦ if ∑ k, c k = p then boolNot else MeasurableEquiv.refl Bool

lemma onCube_sublatticeFlip_apply (p : Fin 2) (ζ : (Fin 2 → Fin 2) → Bool)
    (c : Fin 2 → Fin 2) :
    (sublatticeFlip p).onCube.toFun ζ c = if ∑ k, c k = p then !(ζ c) else ζ c := by
  rw [CubeTransformation.pureSpin_onCube_toFun_apply]
  split_ifs with hc <;> simp [hc]

lemma measurePreserving_sublatticeFlip_spin (p : Fin 2) (c : Fin 2 → Fin 2) :
    MeasurePreserving ((sublatticeFlip p).spin c) uniformSpinMeasure uniformSpinMeasure := by
  by_cases hc : ∑ k, c k = p
  · have hspin : (sublatticeFlip p).spin c = boolNot := if_pos hc
    rw [hspin]
    exact measurePreserving_boolNot_uniformSpinMeasure
  · have hspin : (sublatticeFlip p).spin c = MeasurableEquiv.refl Bool := if_neg hc
    rw [hspin]
    exact MeasurePreserving.id _

/-- **The sublattice spin flip reverses the nearest-neighbour coupling**:
`Φ^{J₁,J₂,0}_C ∘ σ = Φ^{-J₁,J₂,0}_C`.  In a nonzero field `σ` is not a symmetry at all — it
reverses only *half* the spins, so the field term `-h ∑_{i ∈ C} σ_i` is turned into
`-h(-σ_u + σ_v + σ_w - σ_z)`, which is no field term.  Hence `σ ∈ I_{C,λ}(Φ)` exactly in
Georgii's case `h = J₁ = 0`. -/
lemma gdCube_onCube_sublatticeFlip (p : Fin 2) (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ 0 ((sublatticeFlip p).onCube.toFun ζ) = gdCube (-J₁) J₂ 0 ζ := by
  rw [gdCube_apply, gdCube_apply]
  simp only [onCube_sublatticeFlip_apply, sum_sqCorner, show (0 + 0 : Fin 2) = 0 from rfl,
    show (1 + 0 : Fin 2) = 1 from rfl, show (0 + 1 : Fin 2) = 1 from rfl,
    show (1 + 1 : Fin 2) = 0 from rfl]
  fin_cases p <;> norm_num [spin_not] <;> ring

theorem isSymmetry_sublatticeFlip_gdCube (p : Fin 2) :
    (sublatticeFlip p).IsSymmetry (gdCube 0 J₂ 0) uniformSpinMeasure :=
  CubeTransformation.IsSymmetry.of_apply_onCube gdCube_cubeRefl
    (measurePreserving_sublatticeFlip_spin p)
    fun ζ ↦ by rw [gdCube_onCube_sublatticeFlip]; norm_num


/-- The value of (18.29) on a staggered configuration. -/
lemma gdCube_staggerCube (b : Bool) : gdCube J₁ J₂ h (staggerCube b) = 4 * J₁ - 2 * J₂ := by
  rw [gdCube_apply]
  simp only [staggerCube_sqCorner_zero_zero, staggerCube_sqCorner_one_zero,
    staggerCube_sqCorner_zero_one, staggerCube_sqCorner_one_one]
  cases b <;> (norm_num [spin]; ring)

/-! ### Georgii 18.3.3(a): `J₁ > 0`, `J₁ + J₂ > 0`, `h = 0` — the ferromagnetic region

"The set of local ground states then consists of the configurations `(++)` and `(--)`, and we
obtain the same result as in the case of the Ising ferromagnet." -/

section CaseA

/-- `m_Φ = -4J₁ - 2J₂` in region (a): the value table gives `-4J₁-2J₂` on the constants,
`4J₁-2J₂` on the staggered configurations, `2J₂` on the striped ones and `0` on the eight with a
single reversed spin, and `J₁ > 0`, `J₁ + J₂ > 0` make the first the smallest. -/
lemma le_gdCube_caseA (hJ₁ : 0 < J₁) (hJ : 0 < J₁ + J₂) (ζ : (Fin 2 → Fin 2) → Bool) :
    -4 * J₁ - 2 * J₂ ≤ gdCube J₁ J₂ 0 ζ := by
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> linarith

lemma gdCube_const (b : Bool) : gdCube J₁ J₂ 0 (fun _ ↦ b) = -4 * J₁ - 2 * J₂ := by
  rw [gdCube_apply]
  cases b <;> (norm_num [spin]; ring)

/-- **Georgii's local ground states in region (a)**: exactly the two constant configurations. -/
theorem gdCube_eq_iff_caseA (hJ₁ : 0 < J₁) (hJ : 0 < J₁ + J₂) (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ 0 ζ = -4 * J₁ - 2 * J₂ ↔ ∃ b : Bool, ζ = fun _ ↦ b := by
  refine ⟨fun heq ↦ ⟨ζ (sqCorner 0 0), ?_⟩, fun ⟨b, hb⟩ ↦ by rw [hb, gdCube_const]⟩
  rw [gdCube_apply] at heq
  have key : ζ (sqCorner 1 0) = ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = ζ (sqCorner 0 0)
      ∧ ζ (sqCorner 1 1) = ζ (sqCorner 0 0) := by
    revert heq
    generalize ζ (sqCorner 0 0) = u
    generalize ζ (sqCorner 1 0) = v
    generalize ζ (sqCorner 0 1) = w
    generalize ζ (sqCorner 1 1) = z
    cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> intro heq <;> linarith
  exact funext_sqCorner rfl key.1 key.2.1 key.2.2

theorem isPStablePartition_gdCube_caseA (hJ₁ : 0 < J₁) (hJ : 0 < J₁ + J₂) :
    IsPStablePartition (gdCube J₁ J₂ 0) uniformSpinMeasure Set.univ isingFerroG where
  exists_localGroundStates_subset := by
    obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube J₁ J₂ 0)
      (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseA hJ₁ hJ)
      (ζ₀ := fun _ ↦ true) (gdCube_const true)
    refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
    obtain ⟨b, rfl⟩ := (gdCube_eq_iff_caseA hJ₁ hJ ζ).1 (hsub hζ)
    exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_isingFerroG k a

/-- **Georgii's `{G_+, G_-}` is `Φ`-symmetric in region (a)**, by the spin flip (which is a
symmetry of (18.29) exactly because `h = 0`). -/
theorem isPhiSymmetric_gdCube_caseA :
    IsPhiSymmetric (gdCube J₁ J₂ 0) uniformSpinMeasure isingFerroG := by
  refine isPhiSymmetric_of_ne gdCube_cubeRefl fun m n hmn ↦
    ⟨isingSpinFlip 2, isSymmetry_isingSpinFlip_gdCube, ?_⟩
  fin_cases m <;> fin_cases n <;> first
    | exact absurd rfl hmn
    | (change (isingSpinFlip 2).onCube.toFun '' {fun _ ↦ _} = _
       rw [image_onCube_isingSpinFlip]; rfl)

/-- **Georgii 18.3.3(a)**: in the region `J₁ > 0`, `J₁ + J₂ > 0`, `h = 0` the Gertsik–Dobrushin
model has, for all sufficiently large `β`, two mutually singular shift-invariant Gibbs measures
which are random perturbations of the two constant ground states and are exchanged by the spin
flip — "the same result as in the case of the Ising ferromagnet", 18.3.1.  In particular
`|ex 𝒢_Θ(βΦ)| ≥ 2`. -/
theorem eventually_two_le_encard_extremePoints_gdCube_caseA (hJ₁ : 0 < J₁) (hJ : 0 < J₁ + J₂) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * gdCube J₁ J₂ 0 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * gdCube J₁ J₂ 0 ζ),
      (2 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec Bool (fun ζ ↦ β * gdCube J₁ J₂ 0 ζ)
        uniformSpinMeasure hφβ hMβ) (shiftGroup (Fin 2 → ℤ) Bool)).extremePoints ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube J₁ J₂ 0)
    (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseA hJ₁ hJ)
    (ζ₀ := fun _ ↦ true) (gdCube_const true)
  refine eventually_le_encard_extremePoints (E := Bool) (φ := gdCube J₁ J₂ 0)
    (ν := uniformSpinMeasure) (G := isingFerroG) measurable_gdCube (le_gdCube_caseA hJ₁ hJ)
    gdCube_cubeRefl (isCubeConfining_univ ⟨4 * |J₁| + 2 * |J₂| + 4 * |0|, abs_gdCube_le⟩)
    (isPStablePartition_gdCube_caseA hJ₁ hJ) isPhiSymmetric_gdCube_caseA measurableSet_isingFerroG
    isRSymmetric_isingFerroG hε fun ζ hζ ↦ ?_
  obtain ⟨b, rfl⟩ := (gdCube_eq_iff_caseA hJ₁ hJ ζ).1 (hsub hζ)
  exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩

end CaseA


/-! ### Georgii 18.3.3(b): `J₁ < 0`, `J₂ > J₁`, `|h| < -2J₁ + (J₂ ∧ 0)` — the antiferromagnetic
region

"In this case there are again two ground states", the staggered ones, "and Theorem (18.25) thus
implies the same result as in Example 18.3.2 (which corresponds to the particular choice
`J₁ = -1`, `J₂ = 0`)." -/

section CaseB

variable (hJ₁ : J₁ < 0) (hJ₂ : J₁ < J₂) (hh : |h| < -2 * J₁ + min J₂ 0)

include hJ₁ hJ₂ hh

/-- `m_Φ = 4J₁ - 2J₂` in region (b). -/
lemma le_gdCube_caseB (ζ : (Fin 2 → Fin 2) → Bool) : 4 * J₁ - 2 * J₂ ≤ gdCube J₁ J₂ h ζ := by
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  have hm1 : min J₂ 0 ≤ J₂ := min_le_left _ _
  have hm2 : min J₂ 0 ≤ 0 := min_le_right _ _
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> linarith

/-- In region (b) every configuration other than the two staggered ones has strictly larger
energy. -/
lemma lt_gdCube_caseB {ζ : (Fin 2 → Fin 2) → Bool} (hζ : ¬ ∃ b, ζ = staggerCube b) :
    4 * J₁ - 2 * J₂ < gdCube J₁ J₂ h ζ := by
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  have hm1 : min J₂ 0 ≤ J₂ := min_le_left _ _
  have hm2 : min J₂ 0 ≤ 0 := min_le_right _ _
  rw [exists_eq_staggerCube_iff] at hζ
  rw [gdCube_apply]
  revert hζ
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> intro hno <;>
    first
      | exact absurd ⟨rfl, rfl, rfl⟩ hno
      | (norm_num [spin]; linarith)

/-- **Georgii's local ground states in region (b)**: exactly the two staggered configurations. -/
theorem gdCube_eq_iff_caseB (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h ζ = 4 * J₁ - 2 * J₂ ↔ ∃ b : Bool, ζ = staggerCube b := by
  refine ⟨fun heq ↦ ?_, fun ⟨b, hb⟩ ↦ by rw [hb, gdCube_staggerCube]⟩
  by_contra hno
  exact absurd heq (lt_gdCube_caseB hJ₁ hJ₂ hh hno).ne'


lemma exists_pos_localGroundStates_subset_isingAntiG_caseB :
    ∃ ε > 0, localGroundStates (gdCube J₁ J₂ h) uniformSpinMeasure ε ⊆ ⋃ n, isingAntiG n := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube J₁ J₂ h)
    (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseB hJ₁ hJ₂ hh)
    (ζ₀ := staggerCube true) (gdCube_staggerCube true)
  refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
  obtain ⟨b, rfl⟩ := (gdCube_eq_iff_caseB hJ₁ hJ₂ hh ζ).1 (hsub hζ)
  exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩

theorem isPStablePartition_gdCube_caseB :
    IsPStablePartition (gdCube J₁ J₂ h) uniformSpinMeasure Set.univ isingAntiG where
  exists_localGroundStates_subset := exists_pos_localGroundStates_subset_isingAntiG_caseB hJ₁ hJ₂ hh
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_isingAntiG k a

omit hJ₁ hJ₂ hh in
/-- **`{G_1, G_2}` is `Φ`-symmetric** for (18.29): the reflections `r_1, r_2` and the rotation
`r_0` exchange the two staggered configurations, and they belong to `I_{C,λ}(Φ)` for all
parameter values. -/
theorem isPhiSymmetric_gdCube_isingAntiG :
    IsPhiSymmetric (gdCube J₁ J₂ h) uniformSpinMeasure isingAntiG := by
  refine isPhiSymmetric_of_ne gdCube_cubeRefl fun m n hmn ↦
    ⟨CubeTransformation.refl 0, isSymmetry_refl_gdCube 0, ?_⟩
  fin_cases m <;> fin_cases n <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] at hmn ⊢ <;>
    first
      | exact absurd rfl hmn
      | exact image_onCube_refl_isingAntiG_zero 0
      | exact image_onCube_refl_isingAntiG_one 0

open Peierls in
/-- **Georgii 18.3.3(b)**: in the region `J₁ < 0`, `J₂ > J₁`, `|h| < -2J₁ + (J₂ ∧ 0)` the
Gertsik–Dobrushin model gives, for all sufficiently large `β`, the same result as Example 18.3.2:
two mutually singular Gibbs measures which are random perturbations of the two staggered ground
states, invariant under the translations `θ_a` with `a_1 + a_2` even, and related to each other
by `r_0, r_1, r_2, θ_{(1,0)}, θ_{(0,1)}`. -/
theorem eventually_exists_gdCube_caseB_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * gdCube J₁ J₂ h ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * gdCube J₁ J₂ h ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → Bool),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec Bool
          (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart Bool (isingAntiG n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ), Even (a 0 + a 1) →
          MeasurePreserving (shift Bool a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 1 ∧
        (μ 1).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 0 ∧
        (∀ k : Fin 2,
          (μ 0).map ((CubeTransformation.refl (E := Bool) k).onLattice Bool).toFun = μ 1) ∧
        (∀ k : Fin 2,
          (μ 1).map ((CubeTransformation.refl (E := Bool) k).onLattice Bool).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 1).map (shift Bool (Pi.single k 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 0).map (shift Bool (Pi.single k 1)).toFun = μ 1) := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_isingAntiG_caseB hJ₁ hJ₂ hh
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := Bool)
    (φ := gdCube J₁ J₂ h) (ν := uniformSpinMeasure) (G := isingAntiG)
    measurable_gdCube (le_gdCube_caseB hJ₁ hJ₂ hh) gdCube_cubeRefl
    (isCubeConfining_univ ⟨4 * |J₁| + 2 * |J₂| + 4 * |h|, abs_gdCube_le⟩)
    (isPStablePartition_gdCube_caseB hJ₁ hJ₂ hh) isPhiSymmetric_gdCube_isingAntiG
    measurableSet_isingAntiG hε hsub] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hβ hφβ hMβ
  have hrot : (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure :=
    isSymmetry_planeRot_gdCube.const_mul gdCube_cubeRefl β
  have hrefl : ∀ k : Fin 2, (CubeTransformation.refl (E := Bool) k).IsSymmetry
      (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure := fun k ↦
    (isSymmetry_refl_gdCube k).const_mul gdCube_cubeRefl β
  exact ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n a ha ↦ h6 n a (preimage_tauPow_staggerCube ha _),
    h8 0 1 _ hrot image_onCube_planeRot_isingAntiG_zero,
    h8 1 0 _ hrot image_onCube_planeRot_isingAntiG_one,
    fun k ↦ h8 0 1 _ (hrefl k) (image_onCube_refl_isingAntiG_zero k),
    fun k ↦ h8 1 0 _ (hrefl k) (image_onCube_refl_isingAntiG_one k),
    fun k ↦ h9 0 1 k (preimage_cubeRefl_isingAntiG_zero k),
    fun k ↦ h9 1 0 k (preimage_cubeRefl_isingAntiG_one k)⟩

end CaseB


/-! ### Georgii 18.3.3(c): `J₁ = 0`, `J₂ > 0`, `h = 0` — four symmetry-related ground states

"These parameter values constitute a half-line in `ℝ³` which is the common border of the regions
(a) and (b). … The same result also follows from Theorem (18.25) because there are four
symmetry-related ground states." -/

section CaseC

/-- Georgii's four local ground states in region (c): with `J₁ = h = 0` the energy is
`-J₂(σ_u σ_z + σ_v σ_w)`, minimal exactly when `σ_z = σ_u` and `σ_w = σ_v`.  The four
configurations are the two constants (`u = v`) and the two staggered ones (`v = !u`). -/
def gdUC : Fin 4 → Bool := ![true, false, true, false]

/-- The second parameter of Georgii's four ground states in region (c). -/
def gdVC : Fin 4 → Bool := ![true, false, false, true]

/-- Georgii's four local ground states in region (c). -/
def gdGroundC (n : Fin 4) : (Fin 2 → Fin 2) → Bool := sqOf (gdUC n) (gdVC n) (gdVC n) (gdUC n)

/-- The partition `{G_1, …, G_4}` of the local ground states in region (c). -/
def gdGC (n : Fin 4) : Set ((Fin 2 → Fin 2) → Bool) := {gdGroundC n}

lemma measurableSet_gdGC (n : Fin 4) : MeasurableSet (gdGC n) := measurableSet_singleton _

/-- `m_Φ = -2J₂` in region (c). -/
lemma le_gdCube_caseC (hJ₂ : 0 < J₂) (ζ : (Fin 2 → Fin 2) → Bool) :
    -2 * J₂ ≤ gdCube 0 J₂ 0 ζ := by
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> linarith

lemma gdCube_sqOf_caseC (u v : Bool) : gdCube 0 J₂ 0 (sqOf u v v u) = -2 * J₂ := by
  rw [gdCube_apply]
  simp only [sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero, sqOf_sqCorner_zero_one,
    sqOf_sqCorner_one_one]
  cases u <;> cases v <;> (norm_num [spin]; try ring)

/-- **Georgii's local ground states in region (c)**: exactly the four configurations with
`σ_z = σ_u` and `σ_w = σ_v`. -/
theorem gdCube_eq_iff_caseC (hJ₂ : 0 < J₂) (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube 0 J₂ 0 ζ = -2 * J₂ ↔
      ζ (sqCorner 1 1) = ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = ζ (sqCorner 1 0) := by
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;>
    simp only [spin, if_true, if_false, and_true, and_false, true_and, false_and,
      Bool.true_eq_false, Bool.false_eq_true, iff_false, iff_true] <;>
    first
      | (intro hcon; linarith)
      | (norm_num; try ring)
      | (constructor <;> intro hcon <;> first | linarith | trivial)

theorem exists_eq_gdGroundC_iff (ζ : (Fin 2 → Fin 2) → Bool) :
    (∃ n : Fin 4, ζ = gdGroundC n) ↔
      ζ (sqCorner 1 1) = ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = ζ (sqCorner 1 0) := by
  constructor
  · rintro ⟨n, rfl⟩
    fin_cases n <;> exact ⟨rfl, rfl⟩
  · rintro ⟨h11, h01⟩
    have hζ := eq_sqOf ζ
    rcases hu : ζ (sqCorner 0 0) with _ | _ <;> rcases hv : ζ (sqCorner 1 0) with _ | _
    · exact ⟨1, by rw [hζ, h11, h01, hu, hv]; rfl⟩
    · exact ⟨3, by rw [hζ, h11, h01, hu, hv]; rfl⟩
    · exact ⟨2, by rw [hζ, h11, h01, hu, hv]; rfl⟩
    · exact ⟨0, by rw [hζ, h11, h01, hu, hv]; rfl⟩


/-! #### The Klein group of sublattice spin flips -/

/-- **The Klein group of sublattice spin flips**: `gdFlip s t` reverses the spins at the corners
of even parity when `s` and at those of odd parity when `t`.  `gdFlip true true` is Georgii's
spin flip, `gdFlip true false` and `gdFlip false true` his sublattice spin flips, and
`gdFlip false false` the identity of `T_{C,λ}`.  In region (c) — `h = J₁ = 0` — all four belong
to `I_{C,λ}(Φ)`. -/
abbrev gdFlip (s t : Bool) : CubeTransformation Bool 2 :=
  CubeTransformation.pureSpin fun c ↦
    if (if ∑ k, c k = 0 then s else t) then boolNot else MeasurableEquiv.refl Bool

lemma onCube_gdFlip_apply (s t : Bool) (ζ : (Fin 2 → Fin 2) → Bool) (c : Fin 2 → Fin 2) :
    (gdFlip s t).onCube.toFun ζ c = xor (if ∑ k, c k = 0 then s else t) (ζ c) := by
  rw [CubeTransformation.pureSpin_onCube_toFun_apply]
  generalize (if ∑ k, c k = 0 then s else t) = b
  cases b <;> cases ζ c <;> rfl

lemma measurePreserving_gdFlip_spin (s t : Bool) (c : Fin 2 → Fin 2) :
    MeasurePreserving ((gdFlip s t).spin c) uniformSpinMeasure uniformSpinMeasure := by
  by_cases hc : (if ∑ k, c k = 0 then s else t) = true
  · have hspin : (gdFlip s t).spin c = boolNot := if_pos hc
    rw [hspin]
    exact measurePreserving_boolNot_uniformSpinMeasure
  · have hspin : (gdFlip s t).spin c = MeasurableEquiv.refl Bool := if_neg hc
    rw [hspin]
    exact MeasurePreserving.id _

lemma spin_xor_mul_spin_xor (s x y : Bool) :
    spin (xor s x) * spin (xor s y) = spin x * spin y := by
  cases s <;> cases x <;> cases y <;> norm_num [spin]

/-- With `J₁ = h = 0` the energy is `-J₂(σ_u σ_z + σ_v σ_w)`, a sum over the two diagonals. -/
lemma gdCube_zero_zero_apply (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube 0 J₂ 0 ζ = -J₂ * (spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 1 1))
      + spin (ζ (sqCorner 1 0)) * spin (ζ (sqCorner 0 1))) := by
  rw [gdCube_apply]
  ring

/-- **The sublattice spin flips are symmetries of (18.29) in region (c)**: each diagonal of `C`
joins two corners of the same parity, so both of its spins are reversed or neither. -/
lemma gdCube_onCube_gdFlip (s t : Bool) (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube 0 J₂ 0 ((gdFlip s t).onCube.toFun ζ) = gdCube 0 J₂ 0 ζ := by
  rw [gdCube_zero_zero_apply, gdCube_zero_zero_apply]
  simp only [onCube_gdFlip_apply, sum_sqCorner, show (0 + 0 : Fin 2) = 0 from rfl,
    show (1 + 0 : Fin 2) = 1 from rfl, show (0 + 1 : Fin 2) = 1 from rfl,
    show (1 + 1 : Fin 2) = 0 from rfl, if_true,
    if_neg (show ¬((1 : Fin 2) = 0) by decide)]
  rw [spin_xor_mul_spin_xor, spin_xor_mul_spin_xor]

theorem isSymmetry_gdFlip (s t : Bool) :
    (gdFlip s t).IsSymmetry (gdCube 0 J₂ 0) uniformSpinMeasure :=
  CubeTransformation.IsSymmetry.of_apply_onCube gdCube_cubeRefl
    (measurePreserving_gdFlip_spin s t) (gdCube_onCube_gdFlip s t)

lemma onCube_gdFlip_sqOf (s t u v w z : Bool) :
    (gdFlip s t).onCube.toFun (sqOf u v w z)
      = sqOf (xor s u) (xor t v) (xor t w) (xor s z) := by
  refine funext_sqCorner ?_ ?_ ?_ ?_ <;>
    simp only [onCube_gdFlip_apply, sum_sqCorner, show (0 + 0 : Fin 2) = 0 from rfl,
      show (1 + 0 : Fin 2) = 1 from rfl, show (0 + 1 : Fin 2) = 1 from rfl,
      show (1 + 1 : Fin 2) = 0 from rfl, if_true,
      if_neg (show ¬((1 : Fin 2) = 0) by decide), sqOf_sqCorner_zero_zero,
      sqOf_sqCorner_one_zero, sqOf_sqCorner_zero_one, sqOf_sqCorner_one_one]

lemma bool_xor_xor_left (a b : Bool) : xor (xor a b) a = b := by cases a <;> cases b <;> rfl

/-- **Georgii's "four symmetry-related ground states"** in region (c): the Klein group of
sublattice spin flips acts simply transitively on `{G_1, …, G_4}`. -/
theorem isPhiSymmetric_gdGC : IsPhiSymmetric (gdCube 0 J₂ 0) uniformSpinMeasure gdGC := by
  intro m n
  refine ⟨gdFlip (xor (gdUC m) (gdUC n)) (xor (gdVC m) (gdVC n)), isSymmetry_gdFlip _ _, ?_⟩
  rw [gdGC, gdGC, Set.image_singleton, gdGroundC, gdGroundC, onCube_gdFlip_sqOf,
    bool_xor_xor_left, bool_xor_xor_left]

theorem isPStablePartition_gdGC (hJ₂ : 0 < J₂) :
    IsPStablePartition (gdCube 0 J₂ 0) uniformSpinMeasure Set.univ gdGC where
  exists_localGroundStates_subset := by
    obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube 0 J₂ 0)
      (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseC hJ₂)
      (ζ₀ := gdGroundC 0) (by rw [gdGroundC]; exact gdCube_sqOf_caseC _ _)
    refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
    obtain ⟨n, rfl⟩ := (exists_eq_gdGroundC_iff ζ).2 ((gdCube_eq_iff_caseC hJ₂ ζ).1 (hsub hζ))
    exact Set.mem_iUnion.2 ⟨n, rfl⟩
  pairwise_disjoint_faceRestrict k _ a := by
    refine pairwise_disjoint_faceRestrict_singleton (ζ := gdGroundC) fun m n hmn ↦ ?_
    fin_cases k <;> fin_cases a <;> fin_cases m <;> fin_cases n <;> revert hmn <;> decide

/-- **Georgii 18.3.3(c)**: at `J₁ = 0`, `J₂ > 0`, `h = 0` the Gertsik–Dobrushin model has, for
all sufficiently large `β`, at least four extreme Gibbs measures: `|ex 𝒢(βΦ)| ≥ 4`.  Georgii
obtains the same bound from the product structure (7.19) of the specification (the even and odd
sublattices are independent Ising ferromagnets) and Example 18.3.1. -/
theorem eventually_four_le_encard_extremePoints_gdCube_caseC (hJ₂ : 0 < J₂) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * gdCube 0 J₂ 0 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * gdCube 0 J₂ 0 ζ),
      (4 : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G (cubeGibbsSpec Bool
        (fun ζ ↦ β * gdCube 0 J₂ 0 ζ) uniformSpinMeasure hφβ hMβ)).extremePoints ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube 0 J₂ 0)
    (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseC hJ₂)
    (ζ₀ := gdGroundC 0) (by rw [gdGroundC]; exact gdCube_sqOf_caseC _ _)
  refine eventually_le_encard_extremePoints_G (E := Bool) (φ := gdCube 0 J₂ 0)
    (ν := uniformSpinMeasure) (Gs := gdGC) measurable_gdCube (le_gdCube_caseC hJ₂)
    gdCube_cubeRefl (isCubeConfining_univ ⟨4 * |(0 : ℝ)| + 2 * |J₂| + 4 * |(0 : ℝ)|, abs_gdCube_le⟩)
    (isPStablePartition_gdGC hJ₂) isPhiSymmetric_gdGC measurableSet_gdGC hε fun ζ hζ ↦ ?_
  obtain ⟨n, rfl⟩ := (exists_eq_gdGroundC_iff ζ).2 ((gdCube_eq_iff_caseC hJ₂ ζ).1 (hsub hζ))
  exact Set.mem_iUnion.2 ⟨n, rfl⟩

end CaseC


/-! ### Georgii 18.3.3(d): `|J₁| + J₂ < 0`, `|h| < -J₂ - (J₁ ∨ 0)` — four striped ground states

"In this case we find a new behaviour.  There are four local ground states, namely the
configuration with `+` on the bottom row and `-` on the top row and
its three images under the powers of `r_0`.  These local ground states satisfy the stability
condition (18.23)(a)(ii).  Consequently, if `β` is large enough then `𝒢(βΦ)` contains four
mutually singular Gibbs measures which are shift-invariant in one direction and shift-periodic
with period 2 in the other direction and are transformed into each other by suitable powers of
the rotation `r_0`." -/

section CaseD

/-- Georgii's striped configuration: constant in the direction `1 - k` and alternating in the
direction `k`. -/
def gdStripe (k : Fin 2) (b : Bool) : (Fin 2 → Fin 2) → Bool := fun c ↦ if c k = 0 then b else !b

lemma gdStripe_zero_eq_sqOf (b : Bool) : gdStripe 0 b = sqOf b (!b) b (!b) :=
  funext_sqCorner (by simp [gdStripe]) (by simp [gdStripe]) (by simp [gdStripe])
    (by simp [gdStripe])

lemma gdStripe_one_eq_sqOf (b : Bool) : gdStripe 1 b = sqOf b b (!b) (!b) :=
  funext_sqCorner (by simp [gdStripe]) (by simp [gdStripe]) (by simp [gdStripe])
    (by simp [gdStripe])

/-- The direction of the `n`-th striped ground state. -/
def gdDirD : Fin 4 → Fin 2 := ![0, 1, 0, 1]

/-- The sign of the `n`-th striped ground state. -/
def gdSgnD : Fin 4 → Bool := ![true, true, false, false]

/-- **Georgii's four striped local ground states** in region (d): the configuration with `+` on
the bottom row and `-` on the top row, and its three images under the powers of `r_0`. -/
def gdGroundD (n : Fin 4) : (Fin 2 → Fin 2) → Bool := gdStripe (gdDirD n) (gdSgnD n)

/-- The partition `{G_1, …, G_4}` of the local ground states in region (d). -/
def gdGD (n : Fin 4) : Set ((Fin 2 → Fin 2) → Bool) := {gdGroundD n}

lemma measurableSet_gdGD (n : Fin 4) : MeasurableSet (gdGD n) := measurableSet_singleton _

lemma gdGroundD_zero : gdGroundD 0 = sqOf true false true false := gdStripe_zero_eq_sqOf true

lemma gdGroundD_one : gdGroundD 1 = sqOf true true false false := gdStripe_one_eq_sqOf true

lemma gdGroundD_two : gdGroundD 2 = sqOf false true false true := gdStripe_zero_eq_sqOf false

lemma gdGroundD_three : gdGroundD 3 = sqOf false false true true := gdStripe_one_eq_sqOf false

section Region

variable (hJ : |J₁| + J₂ < 0) (hh : |h| < -J₂ - max J₁ 0)

include hJ hh

/-- `m_Φ = 2J₂` in region (d). -/
lemma le_gdCube_caseD (ζ : (Fin 2 → Fin 2) → Bool) : 2 * J₂ ≤ gdCube J₁ J₂ h ζ := by
  have h1 : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h2 : J₁ ≤ |J₁| := le_abs_self J₁
  have h3 : J₁ ≤ max J₁ 0 := le_max_left _ _
  have h4 : (0 : ℝ) ≤ max J₁ 0 := le_max_right _ _
  have h5 : -|h| ≤ h := neg_abs_le h
  have h6 : h ≤ |h| := le_abs_self h
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> linarith

/-- **Georgii's local ground states in region (d)**: exactly the four configurations whose two
diagonals are both antiferromagnetic, `σ_z = -σ_u` and `σ_w = -σ_v` — the striped ones. -/
theorem gdCube_eq_iff_caseD (ζ : (Fin 2 → Fin 2) → Bool) :
    gdCube J₁ J₂ h ζ = 2 * J₂ ↔
      ζ (sqCorner 1 1) = !ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = !ζ (sqCorner 1 0) := by
  have h1 : -|J₁| ≤ J₁ := neg_abs_le J₁
  have h2 : J₁ ≤ |J₁| := le_abs_self J₁
  have h3 : J₁ ≤ max J₁ 0 := le_max_left _ _
  have h4 : (0 : ℝ) ≤ max J₁ 0 := le_max_right _ _
  have h5 : -|h| ≤ h := neg_abs_le h
  have h6 : h ≤ |h| := le_abs_self h
  rw [gdCube_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;>
    simp only [spin, if_true, if_false, Bool.not_true, Bool.not_false, and_true, and_false,
      true_and, false_and, Bool.true_eq_false, Bool.false_eq_true, iff_false, iff_true] <;>
    first
      | (intro hcon; linarith)
      | (norm_num; try ring)
      | (constructor <;> intro hcon <;> first | linarith | trivial)

end Region

theorem exists_eq_gdGroundD_iff (ζ : (Fin 2 → Fin 2) → Bool) :
    (∃ n : Fin 4, ζ = gdGroundD n) ↔
      ζ (sqCorner 1 1) = !ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = !ζ (sqCorner 1 0) := by
  constructor
  · rintro ⟨n, rfl⟩
    fin_cases n <;> refine ⟨?_, ?_⟩ <;> decide
  · rintro ⟨h11, h01⟩
    have hζ := eq_sqOf ζ
    rcases hu : ζ (sqCorner 0 0) with _ | _ <;> rcases hv : ζ (sqCorner 1 0) with _ | _
    · exact ⟨3, by rw [hζ, h11, h01, hu, hv, gdGroundD_three]; rfl⟩
    · exact ⟨2, by rw [hζ, h11, h01, hu, hv, gdGroundD_two]; rfl⟩
    · exact ⟨0, by rw [hζ, h11, h01, hu, hv, gdGroundD_zero]; rfl⟩
    · exact ⟨1, by rw [hζ, h11, h01, hu, hv, gdGroundD_one]; rfl⟩


/-! #### The dihedral group permutes the four striped ground states -/

lemma image_sqTranspose_gdGD_zero :
    (sqTranspose Bool).onCube.toFun '' gdGD 0 = gdGD 1 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_zero, onCube_sqTranspose_sqOf,
    gdGroundD_one]

lemma image_sqTranspose_gdGD_one :
    (sqTranspose Bool).onCube.toFun '' gdGD 1 = gdGD 0 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_one, onCube_sqTranspose_sqOf,
    gdGroundD_zero]

lemma image_sqTranspose_gdGD_two :
    (sqTranspose Bool).onCube.toFun '' gdGD 2 = gdGD 3 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_two, onCube_sqTranspose_sqOf,
    gdGroundD_three]

lemma image_sqTranspose_gdGD_three :
    (sqTranspose Bool).onCube.toFun '' gdGD 3 = gdGD 2 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_three, onCube_sqTranspose_sqOf,
    gdGroundD_two]

lemma image_sqAntiTranspose_gdGD_zero :
    (sqAntiTranspose Bool).onCube.toFun '' gdGD 0 = gdGD 3 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_zero, onCube_sqAntiTranspose_sqOf,
    gdGroundD_three]

lemma image_sqAntiTranspose_gdGD_three :
    (sqAntiTranspose Bool).onCube.toFun '' gdGD 3 = gdGD 0 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_three, onCube_sqAntiTranspose_sqOf,
    gdGroundD_zero]

lemma image_sqAntiTranspose_gdGD_one :
    (sqAntiTranspose Bool).onCube.toFun '' gdGD 1 = gdGD 2 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_one, onCube_sqAntiTranspose_sqOf,
    gdGroundD_two]

lemma image_sqAntiTranspose_gdGD_two :
    (sqAntiTranspose Bool).onCube.toFun '' gdGD 2 = gdGD 1 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_two, onCube_sqAntiTranspose_sqOf,
    gdGroundD_one]

lemma image_refl_zero_gdGD_zero :
    (CubeTransformation.refl (E := Bool) 0).onCube.toFun '' gdGD 0 = gdGD 2 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_zero, onCube_refl_zero_sqOf,
    gdGroundD_two]

lemma image_refl_zero_gdGD_two :
    (CubeTransformation.refl (E := Bool) 0).onCube.toFun '' gdGD 2 = gdGD 0 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_two, onCube_refl_zero_sqOf,
    gdGroundD_zero]

lemma image_refl_one_gdGD_one :
    (CubeTransformation.refl (E := Bool) 1).onCube.toFun '' gdGD 1 = gdGD 3 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_one, onCube_refl_one_sqOf,
    gdGroundD_three]

lemma image_refl_one_gdGD_three :
    (CubeTransformation.refl (E := Bool) 1).onCube.toFun '' gdGD 3 = gdGD 1 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_three, onCube_refl_one_sqOf,
    gdGroundD_one]

/-- **Georgii's "the four local ground states satisfy the stability condition (18.23)(a)(ii)"**
for region (d): any two of the four striped configurations differ somewhere on each face of `C`.
-/
theorem pairwise_disjoint_faceRestrict_gdGD (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict Bool k a '' gdGD m)
      (faceRestrict Bool k a '' gdGD n) := by
  refine pairwise_disjoint_faceRestrict_singleton (ζ := gdGroundD) fun m n hmn ↦ ?_
  fin_cases k <;> fin_cases a <;> fin_cases m <;> fin_cases n <;> revert hmn <;> decide

/-- **`{G_1, …, G_4}` is `Φ`-symmetric in region (d)**: the four striped configurations are
permuted by the dihedral group of the square, all of whose elements are symmetries of (18.29). -/
theorem isPhiSymmetric_gdGD : IsPhiSymmetric (gdCube J₁ J₂ h) uniformSpinMeasure gdGD := by
  have hT := isSymmetry_of_spin_refl_gdCube (J₁ := J₁) (J₂ := J₂) (h := h)
    (sqTranspose Bool) fun _ ↦ rfl
  have hA := isSymmetry_of_spin_refl_gdCube (J₁ := J₁) (J₂ := J₂) (h := h)
    (sqAntiTranspose Bool) fun _ ↦ rfl
  have hR0 := isSymmetry_refl_gdCube (J₁ := J₁) (J₂ := J₂) (h := h) 0
  have hR1 := isSymmetry_refl_gdCube (J₁ := J₁) (J₂ := J₂) (h := h) 1
  refine isPhiSymmetric_of_ne gdCube_cubeRefl fun m n hmn ↦ ?_
  fin_cases m <;> fin_cases n <;>
    first
      | exact absurd rfl hmn
      | exact ⟨sqTranspose Bool, hT, image_sqTranspose_gdGD_zero⟩
      | exact ⟨sqTranspose Bool, hT, image_sqTranspose_gdGD_one⟩
      | exact ⟨sqTranspose Bool, hT, image_sqTranspose_gdGD_two⟩
      | exact ⟨sqTranspose Bool, hT, image_sqTranspose_gdGD_three⟩
      | exact ⟨sqAntiTranspose Bool, hA, image_sqAntiTranspose_gdGD_zero⟩
      | exact ⟨sqAntiTranspose Bool, hA, image_sqAntiTranspose_gdGD_one⟩
      | exact ⟨sqAntiTranspose Bool, hA, image_sqAntiTranspose_gdGD_two⟩
      | exact ⟨sqAntiTranspose Bool, hA, image_sqAntiTranspose_gdGD_three⟩
      | exact ⟨CubeTransformation.refl 0, hR0, image_refl_zero_gdGD_zero⟩
      | exact ⟨CubeTransformation.refl 0, hR0, image_refl_zero_gdGD_two⟩
      | exact ⟨CubeTransformation.refl 1, hR1, image_refl_one_gdGD_one⟩
      | exact ⟨CubeTransformation.refl 1, hR1, image_refl_one_gdGD_three⟩

/-! #### The shift group of a striped ground state -/

lemma gdStripe_add_of_apply_eq_zero {p : Fin 2 → Fin 2} {k : Fin 2} (hp : p k = 0) (b : Bool)
    (c : Fin 2 → Fin 2) : gdStripe k b (c + p) = gdStripe k b c := by
  rw [gdStripe, gdStripe]
  simp only [Pi.add_apply, hp, add_zero]

/-- **Georgii's "shift-invariant in one direction and shift-periodic with period 2 in the
other"**: the iterated reflection `r^a` fixes the striped configuration `gdStripe k b` exactly
when `a_k` is even. -/
lemma preimage_tauPow_gdStripe {a : Fin 2 → ℤ} {k : Fin 2} (ha : Even (a k)) (b : Bool) :
    tauPow (cubeRefl Bool) (latticeToTorus 0 a)
        ⁻¹' ({gdStripe k b} : Set ((Fin 2 → Fin 2) → Bool)) = {gdStripe k b} := by
  have hp : latticeParity a k = 0 := by rw [latticeParity_apply, if_pos ha]
  ext ζ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, tauPow_cubeRefl_latticeToTorus_zero,
    funext_iff]
  constructor
  · intro hζ c
    have hc := hζ (c + latticeParity a)
    rwa [add_assoc, corner_add_self, add_zero, gdStripe_add_of_apply_eq_zero hp] at hc
  · intro hζ c
    rw [hζ, gdStripe_add_of_apply_eq_zero hp]


/-- Georgii's rotation `r_0` cycles the four striped ground states. -/
lemma image_planeRot_gdGD_zero :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' gdGD 0 = gdGD 1 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_zero, onCube_planeRot_sqOf,
    gdGroundD_one]

lemma image_planeRot_gdGD_one :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' gdGD 1 = gdGD 2 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_one, onCube_planeRot_sqOf,
    gdGroundD_two]

lemma image_planeRot_gdGD_two :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' gdGD 2 = gdGD 3 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_two, onCube_planeRot_sqOf,
    gdGroundD_three]

lemma image_planeRot_gdGD_three :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' gdGD 3 = gdGD 0 := by
  rw [gdGD, gdGD, Set.image_singleton, gdGroundD_three, onCube_planeRot_sqOf,
    gdGroundD_zero]

section RegionD

variable (hJ : |J₁| + J₂ < 0) (hh : |h| < -J₂ - max J₁ 0)

include hJ hh

lemma gdCube_gdGroundD (n : Fin 4) : gdCube J₁ J₂ h (gdGroundD n) = 2 * J₂ :=
  (gdCube_eq_iff_caseD hJ hh _).2 ((exists_eq_gdGroundD_iff (gdGroundD n)).1 ⟨n, rfl⟩)

lemma exists_pos_localGroundStates_subset_gdGD :
    ∃ ε > 0, localGroundStates (gdCube J₁ J₂ h) uniformSpinMeasure ε ⊆ ⋃ n, gdGD n := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset (φ := gdCube J₁ J₂ h)
    (ν := uniformSpinMeasure) uniformSpinMeasure_singleton_ne_zero (le_gdCube_caseD hJ hh)
    (ζ₀ := gdGroundD 0) (gdCube_gdGroundD hJ hh 0)
  refine ⟨ε, hε, fun ζ hζ ↦ ?_⟩
  obtain ⟨n, rfl⟩ := (exists_eq_gdGroundD_iff ζ).2 ((gdCube_eq_iff_caseD hJ hh ζ).1 (hsub hζ))
  exact Set.mem_iUnion.2 ⟨n, rfl⟩

theorem isPStablePartition_gdGD :
    IsPStablePartition (gdCube J₁ J₂ h) uniformSpinMeasure Set.univ gdGD where
  exists_localGroundStates_subset := exists_pos_localGroundStates_subset_gdGD hJ hh
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_gdGD k a

open Peierls in
/-- **Georgii 18.3.3(d)**: in the region `|J₁| + J₂ < 0`, `|h| < -J₂ - (J₁ ∨ 0)` the
Gertsik–Dobrushin model has, for all sufficiently large `β`, four mutually singular Gibbs
measures which are *shift-invariant in one direction and shift-periodic with period 2 in the
other* and are transformed into each other by the powers of the rotation `r_0`.  They are random
perturbations of the four striped ground states. -/
theorem eventually_exists_gdCube_caseD_gibbsMeasure_family :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * gdCube J₁ J₂ h ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * gdCube J₁ J₂ h ζ),
      ∃ μ : Fin 4 → Measure ((Fin 2 → ℤ) → Bool),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec Bool
          (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure hφβ hMβ) (μ n)) ∧
        (Pairwise fun m n ↦ (μ m).MutuallySingular (μ n)) ∧
        (∀ n, μ n {ω | (latticeOceanPart Bool (gdGD n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 4) (a : Fin 2 → ℤ), Even (a (gdDirD n)) →
          MeasurePreserving (shift Bool a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 1 ∧
        (μ 1).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 2 ∧
        (μ 2).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 3 ∧
        (μ 3).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 0 := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_gdGD hJ hh
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := Bool)
    (φ := gdCube J₁ J₂ h) (ν := uniformSpinMeasure) (G := gdGD)
    measurable_gdCube (le_gdCube_caseD hJ hh) gdCube_cubeRefl
    (isCubeConfining_univ ⟨4 * |J₁| + 2 * |J₂| + 4 * |h|, abs_gdCube_le⟩)
    (isPStablePartition_gdGD hJ hh) isPhiSymmetric_gdGD measurableSet_gdGD hε hsub]
    with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, -⟩ := hβ hφβ hMβ
  have hrot : (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure :=
    isSymmetry_planeRot_gdCube.const_mul gdCube_cubeRefl β
  refine ⟨ρ, h1, h2, h3, h4, fun n a ha ↦ h6 n a ?_,
    h8 0 1 _ hrot image_planeRot_gdGD_zero, h8 1 2 _ hrot image_planeRot_gdGD_one,
    h8 2 3 _ hrot image_planeRot_gdGD_two, h8 3 0 _ hrot image_planeRot_gdGD_three⟩
  exact preimage_tauPow_gdStripe ha _

/-- **Georgii 18.3.3(d)**: `|ex 𝒢(βΦ)| ≥ 4` for large `β`. -/
theorem eventually_four_le_encard_extremePoints_gdCube_caseD :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * gdCube J₁ J₂ h ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * gdCube J₁ J₂ h ζ),
      (4 : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G (cubeGibbsSpec Bool
        (fun ζ ↦ β * gdCube J₁ J₂ h ζ) uniformSpinMeasure hφβ
          hMβ)).extremePoints ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_gdGD hJ hh
  exact eventually_le_encard_extremePoints_G (E := Bool) (φ := gdCube J₁ J₂ h)
    (ν := uniformSpinMeasure) (Gs := gdGD) measurable_gdCube (le_gdCube_caseD hJ hh)
    gdCube_cubeRefl (isCubeConfining_univ ⟨4 * |J₁| + 2 * |J₂| + 4 * |h|, abs_gdCube_le⟩)
    (isPStablePartition_gdGD hJ hh) isPhiSymmetric_gdGD measurableSet_gdGD hε hsub

end RegionD

end CaseD

end MeasureTheory.GibbsMeasure

end

end
