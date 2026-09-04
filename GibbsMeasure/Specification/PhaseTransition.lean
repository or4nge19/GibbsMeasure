/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.TangentFunctional
public import GibbsMeasure.Specification.VariationalPrinciple

/-!
# A geometric view of Gibbs measures (Georgii §16.2)

Georgii's §16.2 identifies the shift-invariant Gibbs measures of a potential `Φ ∈ ℬ_Θ` with the
tangent functionals of the pressure at `Φ`. The duality between `ℬ_Θ` and `𝓟_Θ(Ω, 𝓕)` is
established by the specific energy `⟨μ, Φ⟩` (15.24), (15.27): a random field `μ` is mapped to the
linear functional `j(μ) = −⟨μ, ·⟩` on `ℬ_Θ`.

## Main definitions

* `Potential.localPotential Λ f`, **Georgii (16.10)**: the shift-invariant potential
  `Φ^{(Λ,f)}` attached to a bounded local observable `f ∈ 𝓛_Λ`, with `Φ_A = f ∘ θ_i` when
  `A = Λ + i` and `Φ_A = 0` otherwise.
* `Potential.siteEnergyLp Φ i`: Georgii's energy density `f_Φ` (15.22) as a bounded observable;
  it is quasilocal (`Potential.siteEnergyLp_mem_quasilocalFunctions`).
* `Potential.BTheta.specificEnergyFunctional μ`, Georgii's `j(μ) = −⟨μ, ·⟩`, a linear functional
  on `ℬ_Θ`; `Potential.BTheta.fieldsOf L` is the set of shift-invariant random fields with
  `j(μ) = L` (a subsingleton), and `Potential.BTheta.specificEntropyDual ν L` is Georgii's
  extension `𝓀(L)` of the specific entropy to `ℬ_Θ*` used in the proof of (16.11).
* `Potential.BTheta.dualPairing ι E`: the evaluation pairing, so that
  `WeakBilin (dualPairing ι E)` is `ℬ_Θ*` with the weak* topology, and
  `Potential.BTheta.entropyHypograph ν` is Georgii's set `C = {(L, t) : t ≤ 𝓀(L)}`.

## Main results

* `Potential.normAt_localPotential`, `Potential.specificEnergy_localPotential`:
  **Georgii Lemma (16.10)**, `‖Φ^{(Λ,f)}‖₀ = |Λ| ‖f‖` and `⟨μ, Φ^{(Λ,f)}⟩ = μ(f)` for every
  shift-invariant `μ`; `Potential.localPotential_mem_BTheta` puts `Φ^{(Λ,f)}` in `ℬ_Θ`.
* `Potential.BTheta.specificEnergyFunctional_injective`: the injectivity of `j` asserted before
  **Georgii (16.11)** — a shift-invariant random field is determined by the specific energies
  `⟨μ, Φ⟩`, `Φ ∈ ℬ_Θ`, because these already determine all integrals of bounded local observables.
* `Potential.BTheta.continuous_specificEnergyFunctional` and
  `Potential.BTheta.isCompact_setOf_le_specificEntropyDual`: **Step 2 of Georgii (16.11)**, `j` is
  continuous from local convergence to the weak* topology and the level sets `{𝓀 ≥ c}` are the
  `j`-images of the compact level sets of the specific entropy (15.14), hence weak* compact.
* `Potential.BTheta.specificEntropyDual_eq_iInf`: **Georgii Proposition (16.11)**,
  `𝓀(L) = inf_Φ [P(Φ) − L(Φ)]`, by Hahn–Banach separation of the closed convex hypograph of `𝓀`
  and the weak representation theorem (`LinearMap.dualEmbedding_surjective`).
* `Potential.BTheta.isBoundedBy_pressure_iff`, `Potential.BTheta.fieldsOf_subsingleton`:
  **Georgii Theorem (16.13)**, `j` is a bijection from the shift-invariant random fields of finite
  specific entropy onto the `P`-bounded linear functionals on `ℬ_Θ`.
* `Potential.BTheta.specificEntropy_eq_iInf`: **Georgii (16.12)**,
  `𝓀(μ) = inf_Φ [⟨μ, Φ⟩ + P(Φ)]`, i.e. `inf_Φ 𝓀(μ|Φ) = 0` on `𝓟_Θ`.
* `Potential.BTheta.mem_subgradientAt_pressure_of_mem_invariantG`,
  `Potential.BTheta.mem_invariantG_of_mem_subgradientAt_pressure'`,
  `Potential.BTheta.mem_subgradientAt_pressure_iff_mem_invariantG'` and
  `Potential.BTheta.exists_mem_fieldsOf_mem_invariantG`: **Georgii Theorem (16.14)**, `j` is a
  one-to-one correspondence between `𝒢_Θ(Φ)` and the tangent functionals `∂P(Φ)`.
* `Potential.BTheta.gateauxDifferentiable_pressure_iff_subsingleton` and
  `Potential.BTheta.gateauxDifferentiable_pressure_iff_eq_singleton`: the pressure is Gateaux
  differentiable at `Φ` if and only if `Φ` has exactly one shift-invariant Gibbs measure.

Georgii's Corollaries (16.15) and (16.16) are not here: they rest on the converse half of Theorem
(2.34) (`Φ ∼ Ψ` iff `𝒢(Φ) ∩ 𝒢(Ψ) ≠ ∅`) and on (2.35), of which only the direct half
(`Potential.lambdaSpecification_eq_of_isEquivalent`) is available. Corollary (16.17) is the
Dobrushin-regime differentiability and needs (8.37).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Topology

noncomputable section

namespace Potential

/-! ### Georgii Lemma (16.10): the potential of a bounded local observable -/

section LocalPotential

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]

/-- On `ℤ^d` a nonempty finite volume has pairwise distinct translates: `Λ + i = Λ + j` forces
`i = j`, because summing over the volume gives `∑Λ + |Λ| i = ∑Λ + |Λ| j`. -/
lemma translate_injective {ι : Type*} {Λ : Finset (ι → ℤ)} (hΛ : Λ.Nonempty) :
    Function.Injective (translate Λ) := by
  intro i j hij
  have hsum : ∑ x ∈ translate Λ i, x = ∑ x ∈ translate Λ j, x := by rw [hij]
  simp only [translate, Finset.sum_map, Equiv.coe_toEmbedding, Equiv.coe_addRight,
    Finset.sum_add_distrib, Finset.sum_const] at hsum
  have hcard : (#Λ : ℕ) • i = (#Λ : ℕ) • j := add_left_cancel hsum
  funext k
  have hk : (#Λ : ℤ) * i k = (#Λ : ℤ) * j k := by
    have := congrFun hcard k
    simpa [Pi.smul_apply, nsmul_eq_mul] using this
  exact mul_left_cancel₀ (by exact_mod_cast hΛ.card_pos.ne') hk

variable (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞)

open scoped Classical in
/-- **Georgii (16.10).** The potential `Φ^{(Λ,f)}` of a bounded local observable `f ∈ 𝓛_Λ`:
`Φ_A = f ∘ θ_i` if `A = Λ + i`, and `Φ_A = 0` if `A` is not a translate of `Λ`. -/
def localPotential : Potential S E :=
  fun A ↦ if h : ∃ i : S, A = translate Λ i then ⇑f ∘ (shift E (-h.choose)).toFun else 0

variable {Λ f}

lemma localPotential_of_not_translate {A : Finset S} (h : ¬ ∃ i : S, A = translate Λ i) :
    localPotential Λ f A = 0 := by
  classical
  exact dite_eq_right h

/-- The interaction term of `Φ^{(Λ,f)}` on the translate `Λ + i` is `f ∘ θ_i`. -/
lemma localPotential_translate {ι : Type*} {Λ : Finset (ι → ℤ)} (hΛ : Λ.Nonempty)
    (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) (i : ι → ℤ) :
    localPotential Λ f (translate Λ i) = ⇑f ∘ (shift E (-i)).toFun := by
  classical
  have h : ∃ j : ι → ℤ, translate Λ i = translate Λ j := ⟨i, rfl⟩
  rw [localPotential, dite_eq_left h]
  rw [translate_injective hΛ h.choose_spec.symm]

section Lattice

variable {ι E : Type*} [MeasurableSpace E] {Λ : Finset (ι → ℤ)}
  {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}

/-- The translates of `Λ` are exactly the volumes on which `Φ^{(Λ,f)}` may be nonzero, and this
family is translation invariant. -/
lemma exists_translate_of_translate {A : Finset (ι → ℤ)} {j : ι → ℤ}
    (h : ∃ i, translate A j = translate Λ i) : ∃ i, A = translate Λ i := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i - j, ?_⟩
  have h2 : translate (translate A j) (-j) = translate (translate Λ i) (-j) := by rw [hi]
  rwa [translate_translate, translate_translate, add_neg_cancel, translate_zero,
    ← sub_eq_add_neg] at h2

/-- **Georgii (16.10):** `Φ^{(Λ,f)}` is shift invariant. -/
lemma isShiftInvariant_localPotential (hΛ : Λ.Nonempty) (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) :
    (localPotential Λ f).IsShiftInvariant := by
  rw [isShiftInvariant_iff]
  intro j A η
  by_cases h : ∃ i, A = translate Λ i
  · obtain ⟨i, rfl⟩ := h
    show localPotential Λ f (translate (translate Λ i) j) ((shift E j).toFun η) = _
    rw [translate_translate, localPotential_translate hΛ, localPotential_translate hΛ]
    refine congrArg (⇑f) (funext fun k ↦ ?_)
    simp only [shift_toFun_apply]
    ring_nf
  · rw [localPotential_of_not_translate fun hc ↦ h (exists_translate_of_translate hc),
      localPotential_of_not_translate h]
    rfl

/-- **Georgii (16.10):** the interaction terms of `Φ^{(Λ,f)}` are measurable for the cylinder
σ-algebra of their volume, since `f ∈ 𝓛_Λ`. -/
lemma isPotential_localPotential (hΛ : Λ.Nonempty) (hf : f ∈ localFunctionsOn (ι → ℤ) E Λ) :
    IsPotential (localPotential Λ f) := by
  refine ⟨fun Δ ↦ ?_⟩
  by_cases h : ∃ i, Δ = translate Λ i
  · obtain ⟨i, rfl⟩ := h
    rw [localPotential_translate hΛ]
    have hmeas := (shift E (-i)).measurable_comp_cylinderEvents (Λ := (Λ : Set (ι → ℤ)))
      (mem_localFunctionsOn.1 hf)
    have hset : ((shift E (-i)).sites ⁻¹' (Λ : Set (ι → ℤ)))
        = ((translate Λ i : Finset (ι → ℤ)) : Set (ι → ℤ)) := by
      ext x
      simp [shift]
    rwa [hset] at hmeas
  · rw [localPotential_of_not_translate h]
    exact @measurable_const _ _ _
      (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Δ : Set (ι → ℤ))) _

/-- The sup-norm of a bounded observable, as an extended nonnegative real. -/
lemma iSup_enorm_eq_ofReal_norm {α : Type*} (g : lp (fun _ : α ↦ ℝ) ∞) :
    ⨆ x, ‖(g : α → ℝ) x‖ₑ = ENNReal.ofReal ‖g‖ := by
  refine le_antisymm (iSup_le fun x ↦ ?_) ?_
  · rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal
      (by simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g x)
  · by_cases htop : (⨆ x, ‖(g : α → ℝ) x‖ₑ) = ⊤
    · rw [htop]; exact le_top
    refine ENNReal.ofReal_le_of_le_toReal (lp.norm_le_of_forall_le ENNReal.toReal_nonneg
      fun x ↦ ?_)
    have hx : ‖(g : α → ℝ) x‖ₑ ≤ ⨆ y, ‖(g : α → ℝ) y‖ₑ :=
      le_iSup (fun y ↦ ‖(g : α → ℝ) y‖ₑ) x
    rw [← ENNReal.toReal_le_toReal (by simp) htop] at hx
    simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
      using hx

/-- The volumes containing the origin on which `Φ^{(Λ,f)}` is nonzero: the translates `Λ − x`,
`x ∈ Λ`. -/
lemma zero_mem_translate_iff {x : ι → ℤ} : (0 : ι → ℤ) ∈ translate Λ (-x) ↔ x ∈ Λ := by
  rw [mem_translate]
  simp

open scoped Classical in
/-- The volumes containing the origin on which `Φ^{(Λ,f)}` does not vanish are the `|Λ|`
translates `Λ − x`, `x ∈ Λ`. -/
lemma localPotential_eq_zero_of_notMem_image {A : Finset (ι → ℤ)}
    (h0 : (0 : ι → ℤ) ∈ A) (hA : A ∉ Λ.image fun x ↦ translate Λ (-x)) :
    localPotential Λ f A = 0 := by
  by_cases h : ∃ i, A = translate Λ i
  · obtain ⟨i, rfl⟩ := h
    refine absurd (Finset.mem_image.2 ⟨-i, ?_, ?_⟩) hA
    · simpa using mem_translate.1 h0
    · rw [neg_neg]
  · exact localPotential_of_not_translate h

/-- The sup-norm of the interaction term of `Φ^{(Λ,f)}` on a translate of `Λ` is the sup-norm
of `f`, the shift being a bijection of configuration space. -/
lemma iSup_enorm_localPotential_translate (hΛ : Λ.Nonempty) (i : ι → ℤ) :
    ⨆ η, ‖localPotential Λ f (translate Λ i) η‖ₑ = ENNReal.ofReal ‖f‖ := by
  rw [localPotential_translate hΛ, ← iSup_enorm_eq_ofReal_norm f]
  exact (shift E (-i)).toMeasurableEquiv.toEquiv.iSup_comp
    (g := fun ζ ↦ ‖(f : ((ι → ℤ) → E) → ℝ) ζ‖ₑ)

open scoped Classical in
/-- **Georgii Lemma (16.10):** `‖Φ^{(Λ,f)}‖₀ = |Λ| ‖f‖`. -/
theorem normAt_localPotential (hΛ : Λ.Nonempty) (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) :
    (localPotential Λ f).normAt 0 = #Λ * ENNReal.ofReal ‖f‖ := by
  rw [normAt, tsum_eq_sum (s := Λ.image fun x ↦ translate Λ (-x)) fun A hA ↦ ?_]
  · rw [Finset.sum_image fun x _ y _ hxy ↦ neg_injective
      (translate_injective hΛ hxy)]
    have hterm : ∀ x ∈ Λ, {A : Finset (ι → ℤ) | (0 : ι → ℤ) ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖localPotential Λ f A η‖ₑ) (translate Λ (-x)) = ENNReal.ofReal ‖f‖ := by
      intro x hx
      rw [Set.indicator_of_mem (show translate Λ (-x) ∈ {A : Finset (ι → ℤ) | (0 : ι → ℤ) ∈ A}
        from zero_mem_translate_iff.2 hx), iSup_enorm_localPotential_translate hΛ]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  · by_cases h0 : (0 : ι → ℤ) ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset (ι → ℤ) | (0 : ι → ℤ) ∈ A} from h0),
        localPotential_eq_zero_of_notMem_image h0 hA]
      simp
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset (ι → ℤ) | (0 : ι → ℤ) ∈ A} from h0) _

/-- `Φ^{(Λ,f)}` is absolutely summable: only `|Λ|` interaction terms contain a given site. -/
lemma isAbsolutelySummable_localPotential (hΛ : Λ.Nonempty)
    (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) : IsAbsolutelySummable (localPotential Λ f) := by
  refine ⟨fun i ↦ ?_⟩
  rw [(isShiftInvariant_localPotential hΛ f).normAt_eq i, normAt_localPotential hΛ f]
  exact ENNReal.mul_ne_top (by simp) (by simp)

/-- **Georgii (16.10):** `Φ^{(Λ,f)} ∈ ℬ_Θ` for a bounded local observable `f ∈ 𝓛_Λ`. -/
theorem localPotential_mem_BTheta (hΛ : Λ.Nonempty) (hf : f ∈ localFunctionsOn (ι → ℤ) E Λ) :
    localPotential Λ f ∈ BTheta (ι → ℤ) E := by
  refine ⟨⟨isAbsolutelySummable_localPotential hΛ f, ?_,
    isPotential_localPotential hΛ hf⟩, isShiftInvariant_localPotential hΛ f⟩
  refine localPotential_of_not_translate fun ⟨i, hi⟩ ↦ ?_
  exact absurd (hi ▸ (translate_nonempty.2 hΛ)) (by simp)

open scoped Classical in
/-- The energy density (15.22) of `Φ^{(Λ,f)}` is the average of the `|Λ|` translates of `f`
over `Λ`. -/
lemma energyDensity_localPotential (hΛ : Λ.Nonempty) (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞)
    (η : (ι → ℤ) → E) :
    (localPotential Λ f).energyDensity η
      = (#Λ : ℝ)⁻¹ * ∑ x ∈ Λ, (f : ((ι → ℤ) → E) → ℝ) ((shift E x).toFun η) := by
  rw [energyDensity, siteEnergy,
    tsum_eq_sum (s := Λ.image fun x ↦ translate Λ (-x)) fun A hA ↦ ?_]
  · rw [Finset.sum_image fun x _ y _ hxy ↦ neg_injective (translate_injective hΛ hxy),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [siteEnergyTerms_of_mem (zero_mem_translate_iff.2 hx), localPotential_translate hΛ]
    simp [translate, neg_neg]
  · by_cases h0 : (0 : ι → ℤ) ∈ A
    · rw [siteEnergyTerms_of_mem h0, localPotential_eq_zero_of_notMem_image h0 hA]
      simp
    · exact siteEnergyTerms_of_not_mem h0 η

/-- **Georgii Lemma (16.10):** `⟨μ, Φ^{(Λ,f)}⟩ = μ(f)` for every shift-invariant random field
`μ`: the specific energy of the potential of a local observable is the integral of the
observable. -/
theorem specificEnergy_localPotential (hΛ : Λ.Nonempty)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Λ) {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun μ μ) :
    (localPotential Λ f).specificEnergy μ = ∫ η, (f : ((ι → ℤ) → E) → ℝ) η ∂μ := by
  have hmeas : Measurable (⇑f) := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  have hint : Integrable (⇑f) μ := lp.integrable_of_measurable hmeas μ
  rw [specificEnergy]
  simp_rw [energyDensity_localPotential hΛ f]
  rw [integral_const_mul,
    integral_finsetSum (f := fun x η ↦ (f : ((ι → ℤ) → E) → ℝ) ((shift E x).toFun η)) _
      fun x _ ↦ (hμ x).integrable_comp_of_integrable hint]
  have hshift : ∀ x ∈ Λ, ∫ η, (f : ((ι → ℤ) → E) → ℝ) ((shift E x).toFun η) ∂μ
      = ∫ η, (f : ((ι → ℤ) → E) → ℝ) η ∂μ :=
    fun x _ ↦ (hμ x).integral_comp' (f := (shift E x).toMeasurableEquiv) _
  rw [Finset.sum_congr rfl hshift, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hΛ.card_pos.ne'), one_mul]

end Lattice

end LocalPotential

/-! ### The specific energy is continuous for the topology of local convergence

Georgii's `f_Φ = ∑_{A ∋ 0} |A|⁻¹ Φ_A` (15.22) is a uniformly convergent sum of local observables,
hence quasilocal, so `μ ↦ ⟨μ, Φ⟩` is continuous for the topology of local convergence (4.3)(2).
This is the continuity of the map `j` used in the proof of Georgii Proposition (16.11). -/

section Quasilocal

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} [IsAbsolutelySummable Φ]

variable (Φ) in
/-- The term `|A|⁻¹ Φ_A` of the energy density at the site `i`, as a bounded observable. -/
def siteEnergyTermLp (i : S) (A : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ Φ.siteEnergyTerms i η A,
    memℓp_infty ⟨({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A).toReal, by
      rintro _ ⟨η, rfl⟩
      have h := enorm_siteEnergyTerms_le (Φ := Φ) i η A
      rw [← ENNReal.toReal_le_toReal (by simp)
        (ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
          (ENNReal.le_tsum A))] at h
      simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h⟩⟩

lemma norm_siteEnergyTermLp_le (i : S) (A : Finset S) :
    ‖Φ.siteEnergyTermLp i A‖
      ≤ ({A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A).toReal := by
  refine lp.norm_le_of_forall_le ENNReal.toReal_nonneg fun η ↦ ?_
  have h := enorm_siteEnergyTerms_le (Φ := Φ) i η A
  rw [← ENNReal.toReal_le_toReal (by simp)
    (ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
      (ENNReal.le_tsum A))] at h
  simpa [siteEnergyTermLp, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

lemma summable_siteEnergyTermLp (i : S) : Summable (Φ.siteEnergyTermLp i) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun A ↦ norm_nonneg _)
    (fun A ↦ norm_siteEnergyTermLp_le (Φ := Φ) i A) ?_)
  exact ENNReal.summable_toReal (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)

lemma siteEnergyTermLp_mem_localFunctionsOn [IsPotential Φ] (i : S) (A : Finset S) :
    Φ.siteEnergyTermLp i A ∈ localFunctionsOn S E A := by
  change Measurable[cylinderEvents (X := fun _ : S ↦ E) (A : Set S)]
    (fun η ↦ Φ.siteEnergyTerms i η A)
  by_cases h : i ∈ A
  · simp only [siteEnergyTerms_of_mem h]
    exact (IsPotential.measurable (Φ := Φ) A).const_mul _
  · simp only [siteEnergyTerms_of_not_mem h]
    exact measurable_const

variable (Φ) in
/-- Georgii's energy density `f_Φ` (15.22), as a bounded observable. -/
def siteEnergyLp (i : S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨Φ.siteEnergy i, memℓp_infty ⟨(Φ.normAt i).toReal, by
    rintro _ ⟨η, rfl⟩
    simpa [Real.norm_eq_abs] using abs_siteEnergy_le (Φ := Φ) i η⟩⟩

@[simp] lemma coeFn_siteEnergyLp (i : S) : ⇑(Φ.siteEnergyLp i) = Φ.siteEnergy i := rfl

lemma hasSum_siteEnergyTermLp (i : S) :
    HasSum (Φ.siteEnergyTermLp i) (Φ.siteEnergyLp i) := by
  obtain ⟨T, hT⟩ := summable_siteEnergyTermLp (Φ := Φ) i
  have hpt : ∀ η : S → E, (T : (S → E) → ℝ) η = Φ.siteEnergy i η := by
    intro η
    have h1 : HasSum (fun A ↦ (Φ.siteEnergyTermLp i A : (S → E) → ℝ) η) ((T : (S → E) → ℝ) η) := by
      refine (lp.tendsto_apply_of_tendsto hT η).congr fun s ↦ ?_
      simp only [siteEnergyTermLp, lp.coeFn_sum]
      exact Finset.sum_apply _ _ _
    exact h1.unique (summable_siteEnergyTerms (Φ := Φ) i η).hasSum
  have hTeq : T = Φ.siteEnergyLp i := lp.ext (funext hpt)
  exact hTeq ▸ hT

/-- **Georgii, after (15.22):** the energy density `f_Φ` is a quasilocal observable. -/
theorem siteEnergyLp_mem_quasilocalFunctions [IsPotential Φ] (i : S) :
    Φ.siteEnergyLp i ∈ quasilocalFunctions S E := by
  refine (Subalgebra.isClosed_topologicalClosure (localFunctions S E)).mem_of_tendsto
    (hasSum_siteEnergyTermLp (Φ := Φ) i) (.of_forall fun s ↦ ?_)
  exact Subalgebra.sum_mem _ fun A _ ↦ localFunctions_le_quasilocalFunctions
    (mem_localFunctions.2 ⟨A, siteEnergyTermLp_mem_localFunctionsOn (Φ := Φ) i A⟩)

/-- **Georgii (4.3)(2) and (15.22):** the specific energy `μ ↦ ⟨μ, Φ⟩` is continuous for the
topology of local convergence. This is the continuity of `j` in the proof of (16.11). -/
theorem continuous_specificEnergy [Zero S] [IsPotential Φ] :
    Continuous fun μ : WithLocalConvergence S E ↦
      Φ.specificEnergy (μ.toMeasure : Measure (S → E)) :=
  lContinuous_of_mem_quasilocalFunctions (siteEnergyLp_mem_quasilocalFunctions (Φ := Φ) 0)

end Quasilocal

/-! ### The affine map `j : μ ↦ −⟨μ, ·⟩` of Georgii §16.2 -/

section Duality

variable {S E : Type*} [Countable S] [Zero S] [MeasurableSpace E] {Φ Ψ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ]
  {μ : Measure (S → E)} [IsFiniteMeasure μ]

/-- The specific energy is additive in the potential. -/
lemma specificEnergy_add : (Φ + Ψ).specificEnergy μ = Φ.specificEnergy μ + Ψ.specificEnergy μ := by
  have : IsAbsolutelySummable (Φ + Ψ) := inferInstance
  rw [specificEnergy, specificEnergy, specificEnergy,
    ← integral_add (integrable_siteEnergy 0 μ) (integrable_siteEnergy 0 μ)]
  exact integral_congr_ae (.of_forall fun η ↦ siteEnergy_add 0 η)

/-- The specific energy is additive in the potential. -/
lemma specificEnergy_sub : (Φ - Ψ).specificEnergy μ = Φ.specificEnergy μ - Ψ.specificEnergy μ := by
  have : IsAbsolutelySummable (Φ - Ψ) := inferInstance
  rw [specificEnergy, specificEnergy, specificEnergy,
    ← integral_sub (integrable_siteEnergy 0 μ) (integrable_siteEnergy 0 μ)]
  exact integral_congr_ae (.of_forall fun η ↦ siteEnergy_sub 0 η)

omit [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ]
  [IsAbsolutelySummable Ψ] [IsFiniteMeasure μ] in
/-- The specific energy is homogeneous in the potential. -/
lemma specificEnergy_smul (c : ℝ) : (c • Φ).specificEnergy μ = c * Φ.specificEnergy μ := by
  rw [specificEnergy, specificEnergy, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun η ↦ siteEnergy_smul c 0 η)

end Duality

namespace BTheta

section Duality

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

variable (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] in
/-- **Georgii §16.2:** the linear functional `j(μ) = −⟨μ, ·⟩` on `ℬ_Θ` attached to a random
field `μ`, the specific energy establishing the duality between `ℬ_Θ` and `𝓟_Θ(Ω, 𝓕)`. -/
def specificEnergyFunctional : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ where
  toFun Φ := -(Φ : Potential (ι → ℤ) E).specificEnergy μ
  map_add' Φ Ψ := by
    rw [Submodule.coe_add, specificEnergy_add, neg_add]
  map_smul' c Φ := by
    rw [Submodule.coe_smul, specificEnergy_smul, smul_eq_mul, ← neg_mul_eq_mul_neg]
    rfl

omit [DecidableEq ι] in
@[simp] lemma specificEnergyFunctional_apply (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ]
    (Φ : BTheta (ι → ℤ) E) :
    specificEnergyFunctional μ Φ = -(Φ : Potential (ι → ℤ) E).specificEnergy μ := rfl

omit [DecidableEq ι] in
/-- **Georgii, before (16.11):** `j` is injective on `𝓟_Θ(Ω, 𝓕)`. By Lemma (16.10) the specific
energies `⟨μ, Φ⟩`, `Φ ∈ ℬ_Θ`, already determine all integrals `μ(f)` of bounded local
observables, hence all probabilities of local events, hence `μ`. -/
theorem specificEnergyFunctional_injective {μ μ' : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun μ μ)
    (hμ' : ∀ j : ι → ℤ, MeasurePreserving (shift E j).toFun μ' μ')
    (h : specificEnergyFunctional μ = specificEnergyFunctional μ') : μ = μ' := by
  refine separatesOn_localEvents ‹IsProbabilityMeasure μ› ‹IsProbabilityMeasure μ'›
    fun A hA ↦ ?_
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hmeasA : MeasurableSet A := cylinderEvents_le_pi _ hΛ
  set Λ' : Finset (ι → ℤ) := insert 0 Λ with hΛ'def
  have hΛ'ne : Λ'.Nonempty := Finset.insert_nonempty _ _
  have hmem : indicatorLp A ∈ localFunctionsOn (ι → ℤ) E Λ' :=
    localFunctionsOn_mono (Finset.subset_insert _ _) (indicatorLp_mem_localFunctionsOn hΛ)
  have hkey := LinearMap.congr_fun h
    (⟨localPotential Λ' (indicatorLp A), localPotential_mem_BTheta hΛ'ne hmem⟩ :
      BTheta (ι → ℤ) E)
  simp only [specificEnergyFunctional_apply, neg_inj] at hkey
  rw [specificEnergy_localPotential hΛ'ne hmem hμ,
    specificEnergy_localPotential hΛ'ne hmem hμ'] at hkey
  rw [coeFn_indicatorLp, integral_indicator_const _ hmeasA,
    integral_indicator_const _ hmeasA] at hkey
  simp only [smul_eq_mul, mul_one] at hkey
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ A), ← ENNReal.ofReal_toReal (measure_ne_top μ' A),
    ← measureReal_def, ← measureReal_def, hkey]

end Duality

/-! ### Georgii Theorem (16.14): shift-invariant Gibbs measures are the tangent functionals -/

section Tangent

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν] {Φ : BTheta (ι → ℤ) E}
  {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]

/-- Tangency of `j(μ)` at `Φ` is exactly the statement that the specific free energy
`⟨μ, ·⟩ + P(·)` is minimal at `Φ`. -/
lemma mem_subgradientAt_pressure_iff (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ ↔
      ∀ Ψ : BTheta (ι → ℤ) E,
        (Φ : Potential (ι → ℤ) E).specificEnergy μ + pressure ν Φ
          ≤ (Ψ : Potential (ι → ℤ) E).specificEnergy μ + pressure ν Ψ := by
  constructor
  · intro h Ψ
    have hΨ := h (Ψ - Φ)
    rw [specificEnergyFunctional_apply, add_sub_cancel, Submodule.coe_sub,
      specificEnergy_sub] at hΨ
    linarith
  · intro h Ψ
    have hΨ := h (Φ + Ψ)
    rw [specificEnergyFunctional_apply, Submodule.coe_add, specificEnergy_add] at *
    linarith

/-- **Georgii Theorem (16.14), first half.** Every `μ ∈ 𝒢_Θ(Φ)` gives a tangent functional
`j(μ) = −⟨μ, ·⟩ ∈ ∂P(Φ)`: by Corollary (15.35) the specific free energy of `μ` is `−P(Φ)`, and
it is at least `−P(Ψ)` for every other potential `Ψ`. -/
theorem mem_subgradientAt_pressure_of_mem_invariantG
    (hμ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)) :
    specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ := by
  refine (mem_subgradientAt_pressure_iff ν μ).2 fun Ψ ↦ ?_
  have heq := specificEntropy_eq_specificEnergy_add_pressure (Φ := (Φ : Potential (ι → ℤ) E)) ν
    (isShiftInvariant Φ) hμ.2 hμ.1.2
  have hle := specificEntropy_le_specificEnergy_add_pressure (Φ := (Ψ : Potential (ι → ℤ) E)) ν
    (isShiftInvariant Ψ) hμ.2
  rw [heq, EReal.coe_le_coe_iff] at hle
  exact hle

/-- **Georgii Theorem (16.14), second half.** A shift-invariant random field whose functional
`j(μ)` is tangent to `P` at `Φ`, and which is a Gibbs measure for *some* potential of `ℬ_Θ`, is a
Gibbs measure for `Φ`: tangency says that the specific free energy `⟨μ, ·⟩ + P(·)` is minimal at
`Φ`, and by Corollary (15.35) its value at `Ψ` is the specific entropy `𝓀(μ)`, so the variational
principle (15.39) applies at `Φ`.

Georgii obtains the hypothesis `hΨ` — equivalently `inf_Ψ 𝓀(μ|Ψ) = 0`, his (16.12) — from the
Fenchel duality of Proposition (16.11), which identifies the `P`-bounded functionals on `ℬ_Θ`
with `𝓟^λ_Θ(Ω, 𝓕)`. -/
theorem mem_invariantG_of_mem_subgradientAt_pressure [StandardBorelSpace E]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {Ψ : BTheta (ι → ℤ) E}
    (hΨ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Ψ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E))
    (h : specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) := by
  refine (specificEntropy_eq_specificEnergy_add_pressure_iff_mem_invariantG ν
    (isShiftInvariant Φ) hμ).1 ?_
  have hΨeq := specificEntropy_eq_specificEnergy_add_pressure
    (Φ := (Ψ : Potential (ι → ℤ) E)) ν (isShiftInvariant Ψ) hμ hΨ.1.2
  have hle := specificEntropy_le_specificEnergy_add_pressure
    (Φ := (Φ : Potential (ι → ℤ) E)) ν (isShiftInvariant Φ) hμ
  have hmin := (mem_subgradientAt_pressure_iff ν μ).1 h Ψ
  rw [hΨeq, EReal.coe_le_coe_iff] at hle
  rw [hΨeq, EReal.coe_eq_coe_iff]
  exact le_antisymm hle hmin

/-- **Georgii Theorem (16.14)**, as a one-to-one correspondence in the case where `μ` is known to
be a Gibbs measure for some potential: `j(μ) ∈ ∂P(Φ)` if and only if `μ ∈ 𝒢_Θ(Φ)`. -/
theorem mem_subgradientAt_pressure_iff_mem_invariantG [StandardBorelSpace E]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {Ψ : BTheta (ι → ℤ) E}
    (hΨ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Ψ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)) :
    specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ ↔
      μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
        (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) :=
  ⟨fun h ↦ mem_invariantG_of_mem_subgradientAt_pressure ν hμ hΨ h,
    fun h ↦ mem_subgradientAt_pressure_of_mem_invariantG ν h⟩

/-- **Georgii (16.14) with Remark (16.6)(1).** If the pressure is Gateaux differentiable at `Φ`
then `Φ` has at most one shift-invariant Gibbs measure: the tangent functionals at a point of
differentiability are at most one, and `j` is injective on `𝓟_Θ`.

The converse — a unique shift-invariant Gibbs measure forces differentiability — is Georgii's,
and needs the other half of (16.14), that *every* tangent functional is of the form `j(μ)`. -/
theorem subsingleton_invariantG_of_gateauxDifferentiable
    (hdiff : ∀ Ψ : BTheta (ι → ℤ) E,
      leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ) :
    Set.Subsingleton (invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)) := by
  intro μ₁ hμ₁ μ₂ hμ₂
  have h₁ : IsProbabilityMeasure μ₁ := hμ₁.1.1
  have h₂ : IsProbabilityMeasure μ₂ := hμ₂.1.1
  obtain ⟨-, hs₁⟩ := mem_invariantFields_shiftGroup.1 hμ₁.2
  obtain ⟨-, hs₂⟩ := mem_invariantFields_shiftGroup.1 hμ₂.2
  refine specificEnergyFunctional_injective hs₁ hs₂
    (subgradientAt_pressure_subsingleton ν hdiff ?_ ?_)
  · exact mem_subgradientAt_pressure_of_mem_invariantG ν hμ₁
  · exact mem_subgradientAt_pressure_of_mem_invariantG ν hμ₂

end Tangent

/-! ### Georgii Proposition (16.11): the specific entropy on the dual `ℬ_Θ*`

Georgii extends the specific entropy to the algebraic dual `ℬ_Θ*` by `𝓀(L) = 𝓀(μ)` when
`L = j(μ)` and `𝓀(L) = −∞` otherwise, and shows that it is concave and upper semicontinuous for
the weak\* topology, its level sets being the `j`-images of the compact level sets of the specific
entropy (15.14). -/

section Fenchel

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν]

variable (ι E) in
/-- The evaluation pairing between `ℬ_Θ*` and `ℬ_Θ`. `WeakBilin (dualPairing ι E)` is Georgii's
space `ℬ_Θ*` of all linear functionals on `ℬ_Θ`, with the weak\* topology of §16.2. -/
abbrev dualPairing : (BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) →ₗ[ℝ] BTheta (ι → ℤ) E →ₗ[ℝ] ℝ := LinearMap.id

omit [Fintype ι] [DecidableEq ι] in
lemma dualPairing_injective : Function.Injective (dualPairing ι E) := fun _ _ h ↦ h

instance : T2Space (WeakBilin (dualPairing ι E)) :=
  (WeakBilin.isEmbedding (B := dualPairing ι E) dualPairing_injective).t2Space

/-- The shift-invariant random fields represented by `L ∈ ℬ_Θ*`, that is with `j(μ) = L`. By
Lemma (16.10) there is at most one (`Potential.BTheta.fieldsOf_subsingleton`). -/
def fieldsOf (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) : Set (Measure ((ι → ℤ) → E)) :=
  {μ | μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
    ∀ Φ : BTheta (ι → ℤ) E, (Φ : Potential (ι → ℤ) E).specificEnergy μ = -L Φ}

omit [Fintype ι] [DecidableEq ι] in
lemma mem_fieldsOf_iff {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} {μ : Measure ((ι → ℤ) → E)} :
    μ ∈ fieldsOf L ↔ μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      ∀ Φ : BTheta (ι → ℤ) E, (Φ : Potential (ι → ℤ) E).specificEnergy μ = -L Φ := Iff.rfl

omit [DecidableEq ι] in
lemma mem_fieldsOf_specificEnergyFunctional {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    μ ∈ fieldsOf (specificEnergyFunctional μ) :=
  ⟨hμ, fun Φ ↦ by rw [specificEnergyFunctional_apply, neg_neg]⟩

omit [DecidableEq ι] in
/-- **Georgii, before (16.11):** `j` is injective, so a functional represents at most one
random field. -/
lemma fieldsOf_subsingleton (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) : (fieldsOf L).Subsingleton := by
  intro μ hμ μ' hμ'
  have h₁ : IsProbabilityMeasure μ := hμ.1.1
  have h₂ : IsProbabilityMeasure μ' := hμ'.1.1
  obtain ⟨-, hs₁⟩ := mem_invariantFields_shiftGroup.1 hμ.1
  obtain ⟨-, hs₂⟩ := mem_invariantFields_shiftGroup.1 hμ'.1
  refine specificEnergyFunctional_injective hs₁ hs₂ (LinearMap.ext fun Φ ↦ ?_)
  rw [specificEnergyFunctional_apply, specificEnergyFunctional_apply, hμ.2 Φ, hμ'.2 Φ]

/-- **Georgii's `𝓀` on `ℬ_Θ*`, in the proof of (16.11):** the specific entropy of the random
field represented by `L`, and `−∞` if there is none. -/
def specificEntropyDual (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) : EReal :=
  ⨆ μ ∈ fieldsOf L, specificEntropy ν μ

omit [IsProbabilityMeasure ν] in
lemma specificEntropyDual_eq {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} {μ : Measure ((ι → ℤ) → E)}
    (hμ : μ ∈ fieldsOf L) : specificEntropyDual ν L = specificEntropy ν μ := by
  refine le_antisymm (iSup₂_le fun μ' hμ' ↦ ?_) (le_iSup₂ (f := fun μ _ ↦ specificEntropy ν μ) μ hμ)
  rw [fieldsOf_subsingleton L hμ' hμ]

omit [IsProbabilityMeasure ν] in
lemma specificEntropyDual_specificEnergyFunctional {μ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropyDual ν (specificEnergyFunctional μ) = specificEntropy ν μ :=
  specificEntropyDual_eq ν (mem_fieldsOf_specificEnergyFunctional hμ)

omit [IsProbabilityMeasure ν] in
lemma specificEntropyDual_nonpos (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) :
    specificEntropyDual ν L ≤ 0 :=
  iSup₂_le fun _ _ ↦ specificEntropy_nonpos ν

omit [IsProbabilityMeasure ν] in
/-- If the extended specific entropy of `L` is at least a real number, then `L` represents a
random field of at least that specific entropy. -/
lemma exists_mem_fieldsOf {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} {c : ℝ}
    (hc : (c : EReal) ≤ specificEntropyDual ν L) :
    ∃ μ ∈ fieldsOf L, (c : EReal) ≤ specificEntropy ν μ := by
  rcases Set.eq_empty_or_nonempty (fieldsOf L) with h | ⟨μ, hμ⟩
  · rw [specificEntropyDual, h] at hc
    simp at hc
  · exact ⟨μ, hμ, (specificEntropyDual_eq ν hμ) ▸ hc⟩

/-- The identity map from `ℬ_Θ*` to `ℬ_Θ*` with the weak\* topology. -/
def toWeakDual (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) : WeakBilin (dualPairing ι E) := L

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma toWeakDual_apply (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) (Φ : BTheta (ι → ℤ) E) :
    dualPairing ι E (toWeakDual L) Φ = L Φ := rfl

omit [DecidableEq ι] in
/-- **Georgii, Step 2 of the proof of (16.11):** `j` is continuous from the topology of local
convergence to the weak\* topology of `ℬ_Θ*`, because each `μ ↦ ⟨μ, Φ⟩` is (the energy density
`f_Φ` is quasilocal). -/
theorem continuous_specificEnergyFunctional :
    Continuous fun μ : WithLocalConvergence (ι → ℤ) E ↦
      toWeakDual (specificEnergyFunctional (μ.toMeasure : Measure ((ι → ℤ) → E))) := by
  refine WeakBilin.continuous_of_continuous_eval _ fun Φ ↦ ?_
  exact (continuous_specificEnergy (Φ := (Φ : Potential (ι → ℤ) E))).neg

/-- **Georgii, Step 2 of the proof of (16.11):** the level sets `{𝓀 ≥ c}` of the extended
specific entropy are the `j`-images of the level sets `{𝓀 ≥ c}` of the specific entropy on
`𝓟_Θ`, which are compact by Proposition (15.14); so they are weak\* compact, and `𝓀` is upper
semicontinuous on `ℬ_Θ*`. -/
theorem isCompact_setOf_le_specificEntropyDual [StandardBorelSpace E] (c : ℝ) :
    IsCompact {L : WeakBilin (dualPairing ι E) | (c : EReal) ≤ specificEntropyDual ν L} := by
  set K : Set (WithLocalConvergence (ι → ℤ) E) :=
    {μ | (c : EReal) ≤ specificEntropy ν (μ.toMeasure : Measure ((ι → ℤ) → E))} ∩
      {μ | ∀ τ ∈ shiftGroup (ι → ℤ) E, MeasurePreserving τ.toFun
        (μ.toMeasure : Measure ((ι → ℤ) → E)) (μ.toMeasure : Measure ((ι → ℤ) → E))} with hKdef
  have hKcompact : IsCompact K :=
    (isCompact_setOf_le_specificEntropy ν c).inter_right
      (isClosed_setOf_forall_measurePreserving _)
  have himage : {L : WeakBilin (dualPairing ι E) | (c : EReal) ≤ specificEntropyDual ν L}
      = (fun μ : WithLocalConvergence (ι → ℤ) E ↦
          toWeakDual (specificEnergyFunctional (μ.toMeasure : Measure ((ι → ℤ) → E)))) ''
            K := by
    ext L
    constructor
    · intro hL
      obtain ⟨μ, hμ, hkμ⟩ := exists_mem_fieldsOf ν hL
      have hprob : IsProbabilityMeasure μ := hμ.1.1
      obtain ⟨-, hshift⟩ := mem_invariantFields_shiftGroup.1 hμ.1
      refine ⟨WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩, ⟨hkμ, ?_⟩, ?_⟩
      · rintro τ ⟨j, rfl⟩
        exact hshift j
      · refine LinearMap.ext fun Φ ↦ ?_
        show -(Φ : Potential (ι → ℤ) E).specificEnergy μ = _
        rw [hμ.2 Φ, neg_neg]
    · rintro ⟨μ, ⟨hkμ, hshift⟩, rfl⟩
      have hinv : (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) :=
        mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦ hshift _ (shift_mem_shiftGroup j)⟩
      show (c : EReal) ≤ specificEntropyDual ν
        (specificEnergyFunctional (μ.toMeasure : Measure ((ι → ℤ) → E)))
      rw [specificEntropyDual_specificEnergyFunctional ν hinv]
      exact hkμ
  rw [himage]
  exact hKcompact.image continuous_specificEnergyFunctional

/-- The specific energy is affine in the random field. -/
lemma specificEnergy_smul_add_smul {S : Type*} [Countable S] [Zero S] {F : Type*}
    [MeasurableSpace F] {Φ : Potential S F} [IsPotential Φ] [IsAbsolutelySummable Φ]
    (μ₁ μ₂ : Measure (S → F)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (s t : ℝ≥0) :
    Φ.specificEnergy (s • μ₁ + t • μ₂)
      = s * Φ.specificEnergy μ₁ + t * Φ.specificEnergy μ₂ := by
  have h₁ : IsFiniteMeasure ((s : ℝ≥0∞) • μ₁) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ₁ _)
  have h₂ : IsFiniteMeasure ((t : ℝ≥0∞) • μ₂) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ₂ _)
  rw [specificEnergy, specificEnergy, specificEnergy, ENNReal.smul_def, ENNReal.smul_def,
    integral_add_measure (integrable_siteEnergy 0 _) (integrable_siteEnergy 0 _),
    integral_smul_measure, integral_smul_measure]
  simp [smul_eq_mul]

/-- Georgii's set `C = {(L, t) : t ≤ 𝓀(L)}` of Step 3 in the proof of (16.11): the hypograph of
the extended specific entropy on `ℬ_Θ* × ℝ`. -/
def entropyHypograph : Set (WeakBilin (dualPairing ι E) × ℝ) :=
  {p | (p.2 : EReal) ≤ specificEntropyDual ν p.1}

omit [IsProbabilityMeasure ν] in
lemma mem_entropyHypograph_iff {p : WeakBilin (dualPairing ι E) × ℝ} :
    p ∈ entropyHypograph ν ↔ (p.2 : EReal) ≤ specificEntropyDual ν p.1 := Iff.rfl

/-- `C ≠ ∅`, because `𝓟^λ_Θ ≠ ∅`: over a standard Borel state space the potential `0` has a
shift-invariant Gibbs measure, whose specific entropy is finite by Corollary (15.35). -/
theorem entropyHypograph_nonempty [StandardBorelSpace E] :
    (entropyHypograph (ι := ι) (E := E) ν).Nonempty := by
  obtain ⟨μ, hμ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := ((0 : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant 0)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have heq := specificEntropy_eq_specificEnergy_add_pressure
    (Φ := ((0 : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν (isShiftInvariant 0) hμ.2 hμ.1.2
  refine ⟨(toWeakDual (specificEnergyFunctional μ),
    ((0 : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      + ((0 : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).pressure ν), ?_⟩
  show (_ : EReal) ≤ specificEntropyDual ν (specificEnergyFunctional μ)
  rw [specificEntropyDual_specificEnergyFunctional ν hμ.2, heq]

/-- `C` is convex: the specific entropy is concave (15.14) and `j` is affine. -/
theorem convex_entropyHypograph : Convex ℝ (entropyHypograph (ι := ι) (E := E) ν) := by
  rintro ⟨L₁, r₁⟩ h₁ ⟨L₂, r₂⟩ h₂ a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simpa [(by linarith : b = 1)] using h₂
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simpa [(by linarith : a = 1)] using h₁
  obtain ⟨μ₁, hμ₁, hk₁⟩ := exists_mem_fieldsOf ν h₁
  obtain ⟨μ₂, hμ₂, hk₂⟩ := exists_mem_fieldsOf ν h₂
  have hp₁ : IsProbabilityMeasure μ₁ := hμ₁.1.1
  have hp₂ : IsProbabilityMeasure μ₂ := hμ₂.1.1
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ) = b := ⟨⟨b, hb⟩, rfl⟩
  have hst : s + t = 1 := by
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_add, NNReal.coe_one, hs, ht]
    exact hab
  have hmem : (s • μ₁ + t • μ₂) ∈ fieldsOf (a • L₁ + b • L₂) := by
    refine ⟨smul_add_smul_mem_invariantFields_shiftGroup hμ₁.1 hμ₂.1 hst, fun Φ ↦ ?_⟩
    have hRHS : dualPairing ι E (a • L₁ + b • L₂) Φ
        = a * dualPairing ι E L₁ Φ + b * dualPairing ι E L₂ Φ := rfl
    have hL : (s : ℝ) * -(dualPairing ι E L₁ Φ) + (t : ℝ) * -(dualPairing ι E L₂ Φ)
        = -(a * dualPairing ι E L₁ Φ + b * dualPairing ι E L₂ Φ) := by
      rw [hs, ht]; ring
    refine Eq.trans ?_ (neg_inj.2 hRHS).symm
    rw [specificEnergy_smul_add_smul, hμ₁.2 Φ, hμ₂.2 Φ]
    exact hL
  show ((a * r₁ + b * r₂ : ℝ) : EReal) ≤ specificEntropyDual ν (a • L₁ + b • L₂)
  rw [specificEntropyDual_eq ν hmem]
  calc ((a * r₁ + b * r₂ : ℝ) : EReal)
      = ((s : ℝ) : EReal) * (r₁ : EReal) + ((t : ℝ) : EReal) * (r₂ : EReal) := by
        rw [hs, ht, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    _ ≤ ((s : ℝ) : EReal) * specificEntropy ν μ₁ + ((t : ℝ) : EReal) * specificEntropy ν μ₂ :=
        add_le_add (mul_le_mul_of_nonneg_left hk₁ (EReal.coe_nonneg.2 s.coe_nonneg))
          (mul_le_mul_of_nonneg_left hk₂ (EReal.coe_nonneg.2 t.coe_nonneg))
    _ ≤ specificEntropy ν (s • μ₁ + t • μ₂) :=
        smul_specificEntropy_add_smul_specificEntropy_le ν hst

/-- `C` is closed: by Step 2 the level sets `{𝓀 ≥ c}` are weak\* compact, hence closed, so `𝓀`
is upper semicontinuous and its hypograph is closed. -/
theorem isClosed_entropyHypograph [StandardBorelSpace E] :
    IsClosed (entropyHypograph (ι := ι) (E := E) ν) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  rintro ⟨L, r⟩ h
  have hlt : specificEntropyDual ν L < (r : EReal) := not_le.1 h
  obtain ⟨c, hc₁, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hU : IsOpen {L' : WeakBilin (dualPairing ι E) |
      ¬ ((c : EReal) ≤ specificEntropyDual ν L')} :=
    (isCompact_setOf_le_specificEntropyDual ν c).isClosed.isOpen_compl
  refine Filter.mem_of_superset
    (prod_mem_nhds (hU.mem_nhds (not_le.2 hc₁)) (isOpen_Ioi.mem_nhds (EReal.coe_lt_coe_iff.1 hc₂)))
    ?_
  rintro ⟨L', r'⟩ ⟨hL', hr'⟩ hmem
  exact hL' (le_of_lt ((EReal.coe_lt_coe_iff.2 hr').trans_le hmem))

/-! ### Georgii, Step 1 of (16.11): the pressure is the Legendre transform of `−𝓀` -/

/-- **Georgii, Step 1 of the proof of (16.11)** (Corollary (15.35)): `L(Φ) + 𝓀(L) ≤ P(Φ)` for
every `L ∈ ℬ_Θ*` and every `Φ ∈ ℬ_Θ`. -/
theorem add_le_pressure {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} {r : ℝ}
    (hr : (r : EReal) ≤ specificEntropyDual ν L) (Φ : BTheta (ι → ℤ) E) :
    L Φ + r ≤ pressure ν Φ := by
  obtain ⟨μ, hμ, hkμ⟩ := exists_mem_fieldsOf ν hr
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have hle := specificEntropy_le_specificEnergy_add_pressure
    (Φ := (Φ : Potential (ι → ℤ) E)) ν (isShiftInvariant Φ) hμ.1
  have hreal : (r : EReal) ≤ (((Φ : Potential (ι → ℤ) E).specificEnergy μ
      + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := hkμ.trans hle
  rw [EReal.coe_le_coe_iff] at hreal
  have hL : L Φ = -(Φ : Potential (ι → ℤ) E).specificEnergy μ := by
    have := hμ.2 Φ
    linarith [this]
  rw [hL, pressure_apply]
  linarith

/-- **Georgii, Step 1 of the proof of (16.11):** the pressure is attained, `P(Φ) = L(Φ) + 𝓀(L)`
for `L = j(μ)` with `μ ∈ 𝒢_Θ(Φ)`, which is nonempty over a standard Borel state space. -/
theorem exists_add_eq_pressure [StandardBorelSpace E] (Φ : BTheta (ι → ℤ) E) :
    ∃ (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) (r : ℝ), (r : EReal) ≤ specificEntropyDual ν L ∧
      pressure ν Φ ≤ L Φ + r := by
  obtain ⟨μ, hμ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant Φ)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have heq := specificEntropy_eq_specificEnergy_add_pressure
    (Φ := (Φ : Potential (ι → ℤ) E)) ν (isShiftInvariant Φ) hμ.2 hμ.1.2
  refine ⟨specificEnergyFunctional μ,
    (Φ : Potential (ι → ℤ) E).specificEnergy μ + (Φ : Potential (ι → ℤ) E).pressure ν, ?_, ?_⟩
  · rw [specificEntropyDual_specificEnergyFunctional ν hμ.2, heq]
  · rw [specificEnergyFunctional_apply, pressure_apply]
    linarith

/-! ### Georgii Proposition (16.11) -/

/-- **Georgii Proposition (16.11).** The extended specific entropy is the Legendre–Fenchel
transform of the pressure: `𝓀(L) = inf_Φ [P(Φ) − L(Φ)]` for every linear functional `L` on
`ℬ_Θ`. Consequently `L` is `P`-bounded if and only if `L = j(μ)` for a shift-invariant random
field `μ` of finite specific entropy, and then `inf_Φ [P(Φ) − L(Φ)] = 𝓀(μ)`.

The proof is Georgii's: `≤` is Corollary (15.35); `≥` is the duality theorem for Fenchel
transforms, proved by separating the closed convex hypograph
`C = {(L, t) : t ≤ 𝓀(L)}` of the upper semicontinuous concave function `𝓀` from a point
`(L, c)` above it by a weak\*-continuous linear functional, which by the weak representation
theorem is of the form `(L', t) ↦ L'(Φ) + t a`. -/
theorem specificEntropyDual_eq_iInf [StandardBorelSpace E] (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) :
    specificEntropyDual ν L
      = ⨅ Φ : BTheta (ι → ℤ) E, ((pressure ν Φ - L Φ : ℝ) : EReal) := by
  refine le_antisymm (le_iInf fun Φ ↦ iSup₂_le fun μ hμ ↦ ?_) ?_
  · have hprob : IsProbabilityMeasure μ := hμ.1.1
    have hle := specificEntropy_le_specificEnergy_add_pressure
      (Φ := (Φ : Potential (ι → ℤ) E)) ν (isShiftInvariant Φ) hμ.1
    refine hle.trans (EReal.coe_le_coe_iff.2 ?_)
    have h2 := hμ.2 Φ
    rw [pressure_apply]
    linarith
  · rw [← not_lt]
    intro hcon
    obtain ⟨c, hc₁, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hcΦ : ∀ Φ : BTheta (ι → ℤ) E, L Φ + c < pressure ν Φ := by
      intro Φ
      have h := hc₂.trans_le (iInf_le (fun Φ ↦ ((pressure ν Φ - L Φ : ℝ) : EReal)) Φ)
      rw [EReal.coe_lt_coe_iff] at h
      linarith
    have hnot : (toWeakDual L, c) ∉ entropyHypograph ν := not_le.2 hc₁
    obtain ⟨f, u, hf₁, hf₂⟩ := geometric_hahn_banach_closed_point
      (convex_entropyHypograph ν) (isClosed_entropyHypograph ν) hnot
    set g : StrongDual ℝ (WeakBilin (dualPairing ι E)) :=
      f.comp (ContinuousLinearMap.inl ℝ (WeakBilin (dualPairing ι E)) ℝ) with hgdef
    obtain ⟨Φ', hΦ'⟩ := LinearMap.dualEmbedding_surjective (dualPairing ι E) g
    set a : ℝ := f (0, 1) with hadef
    have hf : ∀ (L' : WeakBilin (dualPairing ι E)) (t : ℝ),
        f (L', t) = dualPairing ι E L' Φ' + t * a := by
      intro L' t
      have hsplit : ((L', t) : WeakBilin (dualPairing ι E) × ℝ) = (L', 0) + t • (0, 1) := by
        refine Prod.ext ?_ ?_
        · simp
        · simp
      rw [hsplit, _root_.map_add, _root_.map_smul, smul_eq_mul, hadef]
      congr 1
      have : f (L', 0) = g L' := rfl
      rw [this, ← hΦ']
      rfl
    -- the separating functional evaluated at the point and on `C`
    have hpoint : u < dualPairing ι E (toWeakDual L) Φ' + c * a := by
      rw [← hf]; exact hf₂
    have hC : ∀ (L' : WeakBilin (dualPairing ι E)) (t : ℝ), (t : EReal) ≤ specificEntropyDual ν L' →
        dualPairing ι E L' Φ' + t * a < u := by
      intro L' t ht
      rw [← hf]
      exact hf₁ (L', t) ht
    -- `a ≥ 0`, since `C` contains a half line in the second coordinate
    obtain ⟨⟨L₀, r₀⟩, hL₀⟩ := entropyHypograph_nonempty (ι := ι) (E := E) ν
    have hanonneg : 0 ≤ a := by
      by_contra hneg
      rw [not_le] at hneg
      set t : ℝ := min r₀ ((u - dualPairing ι E L₀ Φ') / a - 1) with htdef
      have ht₁ : t ≤ r₀ := min_le_left _ _
      have ht₂ : t < (u - dualPairing ι E L₀ Φ') / a := lt_of_le_of_lt (min_le_right _ _)
        (by linarith)
      have hmem : (t : EReal) ≤ specificEntropyDual ν L₀ :=
        (EReal.coe_le_coe_iff.2 ht₁).trans hL₀
      have hlt := hC L₀ t hmem
      have : u - dualPairing ι E L₀ Φ' < t * a := by
        rw [lt_div_iff_of_neg hneg] at ht₂
        linarith
      linarith
    rcases eq_or_lt_of_le hanonneg with hazero | hapos
    · -- `a = 0` is impossible: rescale `Φ'` and use that `P` is the supremum
      have hLΦ' : u < dualPairing ι E (toWeakDual L) Φ' := by
        rw [← hazero] at hpoint; linarith
      have hLΦ'' : u < L Φ' := hLΦ'
      set s : ℝ := (|c| + 1) / (L Φ' - u) with hsdef
      have hspos : 0 < s := div_pos (by positivity) (by linarith)
      obtain ⟨L', r', hr', hP⟩ := exists_add_eq_pressure ν (s • Φ')
      have hCL' : dualPairing ι E (toWeakDual L') Φ' + r' * a < u := hC (toWeakDual L') r' hr'
      have hr'0 : r' ≤ 0 := by
        have := hr'.trans (specificEntropyDual_nonpos ν L')
        exact_mod_cast this
      have hL'Φ' : L' Φ' < u := by
        rw [← hazero] at hCL'
        have : dualPairing ι E (toWeakDual L') Φ' = L' Φ' := rfl
        linarith [this ▸ hCL']
      have hLs : L' (s • Φ') = s * L' Φ' := by rw [_root_.map_smul, smul_eq_mul]
      have hLs2 : L (s • Φ') = s * L Φ' := by rw [_root_.map_smul, smul_eq_mul]
      have h1 : pressure ν (s • Φ') < s * u := by
        rw [hLs] at hP
        nlinarith
      have h2 := hcΦ (s • Φ')
      rw [hLs2] at h2
      have h3 : s * (L Φ' - u) < -c := by nlinarith
      have hpos : (0 : ℝ) < L Φ' - u := by linarith
      have hcancel : s * (L Φ' - u) = |c| + 1 := by
        rw [hsdef]
        field_simp
      rw [hcancel] at h3
      linarith [neg_le_abs c]
    · -- `a > 0`: rescale to `a = 1` and contradict the definition of the pressure
      obtain ⟨L', r', hr', hP⟩ := exists_add_eq_pressure ν (a⁻¹ • Φ')
      have hCL' : dualPairing ι E (toWeakDual L') Φ' + r' * a < u := hC (toWeakDual L') r' hr'
      have hL'eq : dualPairing ι E (toWeakDual L') Φ' = L' Φ' := rfl
      rw [hL'eq] at hCL'
      rw [show L' (a⁻¹ • Φ') = a⁻¹ * L' Φ' by rw [_root_.map_smul, smul_eq_mul]] at hP
      have h2 := hcΦ (a⁻¹ • Φ')
      rw [show L (a⁻¹ • Φ') = a⁻¹ * L Φ' by rw [_root_.map_smul, smul_eq_mul]] at h2
      have hpoint' : u < L Φ' + c * a := hpoint
      have ha1 : a * a⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hapos)
      have step1 : a * (a⁻¹ * L Φ' + c) < a * pressure ν (a⁻¹ • Φ') :=
        mul_lt_mul_of_pos_left h2 hapos
      have step2 : a * pressure ν (a⁻¹ • Φ') ≤ a * (a⁻¹ * L' Φ' + r') :=
        mul_le_mul_of_nonneg_left hP hapos.le
      have step3 : a * (a⁻¹ * L' Φ' + r') = L' Φ' + r' * a := by
        rw [mul_add, ← mul_assoc, ha1, one_mul]; ring
      rw [step3] at step2
      have hkey : a * (a⁻¹ * L Φ' + c) < u := by linarith
      rw [mul_add, ← mul_assoc, ha1, one_mul] at hkey
      linarith

/-- A functional is `P`-bounded exactly when its extended specific entropy is finite. -/
theorem isBoundedBy_pressure_iff_ne_bot [StandardBorelSpace E]
    (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) :
    IsBoundedBy (pressure ν) L ↔ specificEntropyDual ν L ≠ ⊥ := by
  rw [specificEntropyDual_eq_iInf ν L]
  constructor
  · rintro ⟨c, hc⟩
    refine ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe c) (le_iInf fun Φ ↦ ?_))
    exact EReal.coe_le_coe_iff.2 (hc (Set.mem_range_self Φ))
  · intro h
    obtain ⟨c, -, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 h)
    refine ⟨c, ?_⟩
    rintro _ ⟨Φ, rfl⟩
    have h' := hc₂.trans_le (iInf_le (fun Φ ↦ ((pressure ν Φ - L Φ : ℝ) : EReal)) Φ)
    exact (EReal.coe_lt_coe_iff.1 h').le

/-- **Georgii Theorem (16.13).** The map `j : μ ↦ −⟨μ, ·⟩` is a bijection from the shift-invariant
random fields of finite specific entropy onto the `P`-bounded linear functionals on `ℬ_Θ`. Here
surjectivity: a `P`-bounded functional is represented by a (unique, by
`Potential.BTheta.fieldsOf_subsingleton`) shift-invariant random field of finite specific
entropy. -/
theorem isBoundedBy_pressure_iff [StandardBorelSpace E] (L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ) :
    IsBoundedBy (pressure ν) L ↔ ∃ μ ∈ fieldsOf L, specificEntropy ν μ ≠ ⊥ := by
  rw [isBoundedBy_pressure_iff_ne_bot ν L]
  constructor
  · intro h
    rcases Set.eq_empty_or_nonempty (fieldsOf L) with hempty | ⟨μ, hμ⟩
    · rw [specificEntropyDual, hempty] at h
      simp at h
    · exact ⟨μ, hμ, by rwa [specificEntropyDual_eq ν hμ] at h⟩
  · rintro ⟨μ, hμ, hk⟩
    rwa [specificEntropyDual_eq ν hμ]

omit [DecidableEq ι] in
/-- **Georgii Theorem (16.13), injectivity**: the random field representing a `P`-bounded
functional is unique. -/
theorem fieldsOf_specificEnergyFunctional_eq
    {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    fieldsOf (specificEnergyFunctional μ) = {μ} :=
  Set.Subsingleton.eq_singleton_of_mem (fieldsOf_subsingleton _)
    (mem_fieldsOf_specificEnergyFunctional hμ)

/-- **Georgii (16.12).** The specific entropy is the conjugate concave function of the pressure:
`𝓀(μ) = inf_Φ [⟨μ, Φ⟩ + P(Φ)]`, i.e. `inf_Φ 𝓀(μ|Φ) = 0` for every shift-invariant random
field `μ`. -/
theorem specificEntropy_eq_iInf [StandardBorelSpace E] {μ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy ν μ = ⨅ Φ : BTheta (ι → ℤ) E,
      (((Φ : Potential (ι → ℤ) E).specificEnergy μ + pressure ν Φ : ℝ) : EReal) := by
  rw [← specificEntropyDual_specificEnergyFunctional ν hμ,
    specificEntropyDual_eq_iInf ν (specificEnergyFunctional μ)]
  refine iInf_congr fun Φ ↦ ?_
  rw [specificEnergyFunctional_apply]
  ring_nf

/-! ### Georgii Theorem (16.14), unconditionally -/

variable {Φ : BTheta (ι → ℤ) E} {μ : Measure ((ι → ℤ) → E)}

/-- **Georgii Theorem (16.14), second half.** Over a standard Borel state space a shift-invariant
random field whose functional `j(μ)` is tangent to `P` at `Φ` is a Gibbs measure for `Φ`: by
(16.12) the specific entropy `𝓀(μ)` is the infimum of `⟨μ, ·⟩ + P(·)`, and tangency says that the
infimum is attained at `Φ`, so `𝓀(μ|Φ) = 0` and the variational principle (15.39) applies. -/
theorem mem_invariantG_of_mem_subgradientAt_pressure' [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h : specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) := by
  refine (specificEntropy_eq_specificEnergy_add_pressure_iff_mem_invariantG ν
    (isShiftInvariant Φ) hμ).1 ?_
  rw [specificEntropy_eq_iInf ν hμ]
  refine le_antisymm (iInf_le _ Φ) (le_iInf fun Ψ ↦ ?_)
  exact EReal.coe_le_coe_iff.2 ((mem_subgradientAt_pressure_iff ν μ).1 h Ψ)

/-- **Georgii Theorem (16.14).** Over a standard Borel state space, `j` maps `𝒢_Θ(Φ)` onto the
tangent functionals of the pressure at `Φ`, and injectively; the two halves are
`Potential.BTheta.mem_subgradientAt_pressure_of_mem_invariantG` and
`Potential.BTheta.mem_invariantG_of_mem_subgradientAt_pressure'`. -/
theorem mem_subgradientAt_pressure_iff_mem_invariantG' [StandardBorelSpace E]
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEnergyFunctional μ ∈ subgradientAt (pressure ν) Φ ↔
      μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
        (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) :=
  ⟨fun h ↦ mem_invariantG_of_mem_subgradientAt_pressure' ν hμ h,
    fun h ↦ mem_subgradientAt_pressure_of_mem_invariantG ν h⟩

/-- **Georgii Theorem (16.14), surjectivity of `j` onto `∂P(Φ)`.** Every tangent functional to
the pressure at `Φ` is `j(μ)` for a shift-invariant Gibbs measure `μ` of `Φ`: a tangent functional
is `P`-bounded, hence of the form `j(μ)` by Theorem (16.13), and then `μ ∈ 𝒢_Θ(Φ)`. -/
theorem exists_mem_fieldsOf_mem_invariantG [StandardBorelSpace E]
    {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt (pressure ν) Φ) :
    ∃ μ ∈ fieldsOf L, μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) := by
  obtain ⟨μ, hμ, -⟩ := (isBoundedBy_pressure_iff ν L).1 (isBoundedBy_of_mem_subgradientAt hL)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have hjμ : specificEnergyFunctional μ = L :=
    LinearMap.ext fun Ψ ↦ by rw [specificEnergyFunctional_apply, hμ.2 Ψ, neg_neg]
  exact ⟨μ, hμ, mem_invariantG_of_mem_subgradientAt_pressure' ν hμ.1 (hjμ ▸ hL)⟩

/-- **Georgii (16.14) with Remark (16.6).** Over a standard Borel state space the pressure is
Gateaux differentiable at `Φ` if and only if `Φ` has at most one — equivalently, by Theorem
(4.23) and Corollary (5.16), exactly one — shift-invariant Gibbs measure. -/
theorem gateauxDifferentiable_pressure_iff_subsingleton [StandardBorelSpace E] :
    (∀ Ψ : BTheta (ι → ℤ) E,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ) ↔
      (invariantG (gibbsSpecificationOfAbsolutelySummable
        (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E)).Subsingleton := by
  refine ⟨subsingleton_invariantG_of_gateauxDifferentiable ν, fun h ↦ ?_⟩
  refine leftDirDeriv_eq_rightDirDeriv_pressure_of_subgradientAt_subsingleton ν ?_
  intro L₁ hL₁ L₂ hL₂
  obtain ⟨μ₁, hμ₁, hG₁⟩ := exists_mem_fieldsOf_mem_invariantG ν hL₁
  obtain ⟨μ₂, hμ₂, hG₂⟩ := exists_mem_fieldsOf_mem_invariantG ν hL₂
  have hprob₁ : IsProbabilityMeasure μ₁ := hμ₁.1.1
  have hprob₂ : IsProbabilityMeasure μ₂ := hμ₂.1.1
  have hμ : μ₁ = μ₂ := h hG₁ hG₂
  refine LinearMap.ext fun Ψ ↦ ?_
  have h₁ := hμ₁.2 Ψ
  have h₂ := hμ₂.2 Ψ
  rw [hμ] at h₁
  linarith

/-- **Georgii (16.14) with Remark (16.6).** Over a standard Borel state space the pressure is
Gateaux differentiable at `Φ` if and only if `Φ` has exactly one shift-invariant Gibbs measure
(one exists by Theorem (4.23) and Corollary (5.16)). -/
theorem gateauxDifferentiable_pressure_iff_eq_singleton [StandardBorelSpace E] :
    (∀ Ψ : BTheta (ι → ℤ) E,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ) ↔
      ∃ μ : Measure ((ι → ℤ) → E), invariantG (gibbsSpecificationOfAbsolutelySummable
        (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E) = {μ} := by
  rw [gateauxDifferentiable_pressure_iff_subsingleton ν]
  constructor
  · intro h
    obtain ⟨μ, hμ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant Φ)
    exact ⟨μ, h.eq_singleton_of_mem hμ⟩
  · rintro ⟨μ, hμ⟩
    rw [hμ]
    exact Set.subsingleton_singleton

end Fenchel

end BTheta

end Potential

end

end
