import Comparator.Defs_LowTemperature
import GibbsMeasure

/-!
# Comparator solution: Georgii Theorem (6.9), first assertion — the low-temperature limit

The solution file matching `Comparator/Challenge_LowTemperature.lean`.  The `Bridge` namespace
identifies the from-scratch Ising model of `Comparator.Defs_Ising` with the library's
`isingSpecification`, and `LowTempBridge` identifies Georgii's phases `μ_±^β` with the library's
`Peierls.plusPhase` and `Peierls.minusPhase`, transporting the Peierls estimate
`μ_±^β(σ_a ≠ ω_a^±) ≤ r(β) → 0` to the challenge's notions of local event, local convergence and
Georgii metric.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Theorem (6.9)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

noncomputable section

namespace IsingChallenge

/-! ### The bridge to the `GibbsMeasure` library -/

namespace Bridge

open scoped ENNReal
open MeasureTheory.GibbsMeasure (isingPotential latticeGraph isingSpecification
  uniformSpinMeasure GP)

/-- The library's Ising potential on `ℤ²` with coupling `1` and no external field. -/
abbrev P : Potential Site Bool := isingPotential (latticeGraph 2) 1 0

lemma P_eq : P = Potential.nearestNeighbourPair (latticeGraph 2) 1 0
    MeasureTheory.GibbsMeasure.spin := rfl

lemma spin_eq : spin = MeasureTheory.GibbsMeasure.spin := rfl

/-! #### Unit vectors and nearest-neighbour bonds -/

lemma e_self (k : Fin 2) : e k k = 1 := by simp [e]

lemma e_of_ne {k l : Fin 2} (h : l ≠ k) : e k l = 0 := by simp [e, h]

lemma add_e_ne_self (i : Site) (k : Fin 2) : i + e k ≠ i := by
  intro h
  have h1 := congrFun h k
  rw [Pi.add_apply, e_self] at h1
  omega

lemma e_inj {k m : Fin 2} (h : e k = e m) : k = m := by
  by_contra hkm
  have h1 := congrFun h k
  rw [e_self, e_of_ne hkm] at h1
  exact one_ne_zero h1

lemma adj_add_e (i : Site) (k : Fin 2) : (latticeGraph 2).Adj i (i + e k) := by
  show ∑ l, (i l - (i + e k) l).natAbs = 1
  rw [Finset.sum_eq_single k]
  · have h1 : i k - (i + e k) k = -1 := by rw [Pi.add_apply, e_self]; ring
    rw [h1]
    rfl
  · intro l _ hl
    have h1 : i l - (i + e k) l = 0 := by rw [Pi.add_apply, e_of_ne hl]; ring
    rw [h1]
    rfl
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma adj_decomp {i j : Site} (h : (latticeGraph 2).Adj i j) :
    ∃ k : Fin 2, j = i + e k ∨ i = j + e k := by
  classical
  have h1 : ∑ l, (i l - j l).natAbs = 1 := h
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [h1]; exact one_ne_zero)
  have hk1 : (i k - j k).natAbs = 1 := by
    have hle : (i k - j k).natAbs ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun l ↦ (i l - j l).natAbs)
        (fun l _ ↦ Nat.zero_le _) (Finset.mem_univ k)
    omega
  have herase : ∑ l ∈ Finset.univ.erase k, (i l - j l).natAbs = 0 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun l ↦ (i l - j l).natAbs) (Finset.mem_univ k)
    omega
  have hrest : ∀ l, l ≠ k → j l = i l := by
    intro l hl
    have hle : (i l - j l).natAbs ≤ ∑ m ∈ Finset.univ.erase k, (i m - j m).natAbs :=
      Finset.single_le_sum (f := fun m ↦ (i m - j m).natAbs) (fun m _ ↦ Nat.zero_le _)
        (Finset.mem_erase.2 ⟨hl, Finset.mem_univ l⟩)
    omega
  refine ⟨k, ?_⟩
  rcases (by omega : j k = i k + 1 ∨ i k = j k + 1) with hjk | hjk
  · refine Or.inl (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl
      rw [Pi.add_apply, e_self, hjk]
    · rw [Pi.add_apply, e_of_ne hl, add_zero, hrest l hl]
  · refine Or.inr (funext fun l ↦ ?_)
    by_cases hl : l = k
    · subst hl
      rw [Pi.add_apply, e_self, hjk]
    · rw [Pi.add_apply, e_of_ne hl, add_zero, (hrest l hl).symm]

lemma pair_eq_pair {a b : Site} {k m : Fin 2}
    (h : ({a, a + e k} : Finset Site) = {b, b + e m}) : a = b ∧ k = m := by
  have ha : a ∈ ({b, b + e m} : Finset Site) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  have hak : a + e k ∈ ({b, b + e m} : Finset Site) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rcases Finset.mem_insert.1 ha with rfl | ha'
  · rcases Finset.mem_insert.1 hak with h1 | h1
    · exact absurd h1 (add_e_ne_self a k)
    · rw [Finset.mem_singleton] at h1
      exact ⟨rfl, e_inj (add_left_cancel h1)⟩
  · rw [Finset.mem_singleton] at ha'
    rcases Finset.mem_insert.1 hak with h1 | h1
    · exfalso
      have hz : e m + e k = 0 := by
        have h2 : b + (e m + e k) = b + 0 := by
          rw [← add_assoc, ← ha', h1, add_zero]
        exact add_left_cancel h2
      have h3 := congrFun hz k
      rw [Pi.add_apply, Pi.zero_apply, e_self] at h3
      rcases eq_or_ne k m with rfl | hkm
      · rw [e_self] at h3; omega
      · rw [e_of_ne hkm] at h3; omega
    · rw [Finset.mem_singleton] at h1
      exact absurd (h1.trans ha'.symm) (add_e_ne_self a k)

/-! #### The Hamiltonian -/

lemma P_pair (a : Site) (k : Fin 2) (σ : Config) :
    P {a, a + e k} σ = -(spin (σ a) * spin (σ (a + e k))) := by
  have hne : a ≠ a + e k := (add_e_ne_self a k).symm
  have hcard : ({a, a + e k} : Finset Site).card = 2 := Finset.card_pair hne
  have hadj : ∃ x ∈ ({a, a + e k} : Finset Site), ∃ y ∈ ({a, a + e k} : Finset Site),
      (latticeGraph 2).Adj x y :=
    ⟨a, Finset.mem_insert_self _ _, a + e k,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), adj_add_e a k⟩
  rw [P_eq, Potential.nearestNeighbourPair_apply_pair ⟨hcard, hadj⟩, Finset.prod_pair hne,
    ← spin_eq]
  ring

lemma exists_pair_of_P_ne_zero {Δ : Finset Site} (h : P Δ ≠ 0) :
    ∃ (a : Site) (k : Fin 2), Δ = {a, a + e k} := by
  classical
  by_cases h1 : Δ.card = 1
  · exact absurd (funext fun η ↦ by
      rw [P_eq, Potential.nearestNeighbourPair_apply_card_one h1]
      simp) h
  by_cases h2 : Δ.card = 2 ∧ ∃ x ∈ Δ, ∃ y ∈ Δ, (latticeGraph 2).Adj x y
  · obtain ⟨hcard, x, hx, y, hy, hxy⟩ := h2
    have hne : x ≠ y := (latticeGraph 2).ne_of_adj hxy
    have hsub : ({x, y} : Finset Site) ⊆ Δ := by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton] at hz; exact hz ▸ hy
    have hΔ : Δ = {x, y} :=
      (Finset.eq_of_subset_of_card_le hsub
        (le_of_eq (by rw [hcard, Finset.card_pair hne]))).symm
    obtain ⟨k, hk | hk⟩ := adj_decomp hxy
    · exact ⟨x, k, by rw [hΔ, hk]⟩
    · exact ⟨y, k, by rw [hΔ, hk, Finset.pair_comm]⟩
  · exact absurd (funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero (G := latticeGraph 2)
      (J := 1) (h := 0) (σ := MeasureTheory.GibbsMeasure.spin) h1 h2 η) h

lemma hamiltonian_P_eq (Λ : Finset Site) (σ : Config) :
    P.hamiltonian Λ σ = hamiltonian Λ σ := by
  classical
  have hmem : ∀ Δ ∈ (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)),
      ((Δ : Set Site) ∩ (Λ : Set Site)).Nonempty := by
    intro Δ hΔ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hΔ
    rcases (mem_bonds Λ p.1 p.2).1 hp with hp' | hp'
    · exact ⟨p.1, by simp, by simpa using hp'⟩
    · exact ⟨p.1 + e p.2, by simp, by simpa using hp'⟩
  have hsub : Potential.interactingSupport (Φ := P) Λ ⊆
      (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)) := by
    intro Δ hΔ
    obtain ⟨hne, hΦ⟩ := Potential.mem_interactingSupport.1 hΔ
    obtain ⟨a, k, rfl⟩ := exists_pair_of_P_ne_zero hΦ
    refine Finset.mem_image.2 ⟨(a, k), ?_, rfl⟩
    rw [mem_bonds]
    obtain ⟨x, hxΔ, hxΛ⟩ := hne
    have hxΔ' : x = a ∨ x = a + e k := by
      simpa using hxΔ
    rcases hxΔ' with rfl | rfl
    · exact Or.inl (by simpa using hxΛ)
    · exact Or.inr (by simpa using hxΛ)
  have hzero : ∀ Δ ∈ (bonds Λ).image (fun p : Site × Fin 2 ↦ ({p.1, p.1 + e p.2} : Finset Site)),
      Δ ∉ Potential.interactingSupport (Φ := P) Λ → P Δ σ = 0 := by
    intro Δ hΔ hΔ'
    have := Potential.mem_interactingSupport (Φ := P) (Λ := Λ) (Δ := Δ)
    have hPz : P Δ = 0 := by
      by_contra hc
      exact hΔ' (this.2 ⟨hmem Δ hΔ, hc⟩)
    exact congrFun hPz σ
  have hinj : ∀ p ∈ bonds Λ, ∀ q ∈ bonds Λ,
      ({p.1, p.1 + e p.2} : Finset Site) = {q.1, q.1 + e q.2} → p = q := by
    intro p _ q _ hpq
    obtain ⟨h1, h2⟩ := pair_eq_pair hpq
    exact Prod.ext h1 h2
  rw [Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian,
    Finset.sum_subset hsub hzero, Finset.sum_image hinj, hamiltonian,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ P_pair p.1 p.2 σ

/-! #### The independent specification over the uniform spin measure -/

lemma glue_extend (Λ : Finset Site) (ζ : Λ → Bool) (ω : Config) :
    glue Λ (extend Λ ζ ω) ω = extend Λ ζ ω := by
  funext i
  by_cases h : i ∈ Λ <;> simp [glue, extend, h]

lemma juxt_eq_extend (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) :
    juxt (Λ : Set Site) ω ζ = extend Λ ζ ω := by
  funext i
  by_cases h : i ∈ Λ <;> simp [juxt, extend, h]

lemma uniformSpinMeasure_singleton (c : Bool) : uniformSpinMeasure {c} = 2⁻¹ := by
  show ((2 : ℝ≥0∞)⁻¹ • Measure.count) {c} = 2⁻¹
  rw [Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

lemma pi_uniform_singleton (Λ : Finset Site) (ζ : Λ → Bool) :
    (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) {ζ} = (2 ^ Λ.card : ℝ≥0∞)⁻¹ := by
  rw [← Set.univ_pi_singleton ζ, Measure.pi_pi]
  simp only [uniformSpinMeasure_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [← ENNReal.inv_pow]

lemma isssd_eq (Λ : Finset Site) (ω : Config) :
    Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω
      = Measure.map (juxt (Λ : Set Site) ω) (Measure.pi fun _ : Λ ↦ uniformSpinMeasure) := rfl

lemma lintegral_isssd (Λ : Finset Site) (ω : Config) {f : Config → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω)
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ * ∑ ζ : Λ → Bool, f (extend Λ ζ ω) := by
  rw [isssd_eq, lintegral_map hf Measurable.juxt, lintegral_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [pi_uniform_singleton, juxt_eq_extend, mul_comm]

/-! #### Identification of the finite-volume kernels -/

lemma inv_mul_cancel_aux {c s x : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    (c * s)⁻¹ * (c * x) = s⁻¹ * x := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c⁻¹ s⁻¹, mul_assoc,
    ← mul_assoc c⁻¹ c x, ENNReal.inv_mul_cancel hc0 hct, one_mul]

lemma boltzmann_extend (β : ℝ) (Λ : Finset Site) (ω : Config) (ζ : Λ → Bool) :
    P.boltzmannFactor β Λ (extend Λ ζ ω) = ENNReal.ofReal (weight β Λ ω ζ) := by
  rw [Potential.boltzmannFactor, hamiltonian_P_eq, weight, glue_extend]

lemma gibbsMeasure_apply (β : ℝ) (Λ : Finset Site) (ω : Config) {A : Set Config}
    (hA : MeasurableSet A) :
    gibbsMeasure β Λ ω A
      = (∑ ζ : Λ → Bool, ENNReal.ofReal (weight β Λ ω ζ))⁻¹ *
        ∑ ζ : Λ → Bool,
          A.indicator (fun _ ↦ ENNReal.ofReal (weight β Λ ω ζ)) (extend Λ ζ ω) := by
  rw [gibbsMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply, partitionFunction,
    ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun ζ : Λ → Bool ↦ weight β Λ ω ζ) (fun ζ _ ↦ (Real.exp_pos _).le)]
  refine congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, glue_extend]
  by_cases hx : extend Λ ζ ω ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

lemma spec_apply (β : ℝ) (Λ : Finset Site) (ω : Config) {A : Set Config} (hA : MeasurableSet A) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω A = gibbsMeasure β Λ ω A := by
  classical
  have hc0 : (2 ^ Λ.card : ℝ≥0∞)⁻¹ ≠ 0 := by simp
  have hct : (2 ^ Λ.card : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  have hZ : Specification.premodifierZ (S := Site) (E := Bool) uniformSpinMeasure
      (P.boltzmannFactor β) Λ ω
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ * ∑ ζ : Λ → Bool, ENNReal.ofReal (weight β Λ ω ζ) := by
    rw [Specification.premodifierZ, Specification.relZ,
      lintegral_isssd Λ ω (Potential.measurable_boltzmannFactor (Φ := P) β Λ)]
    exact congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ boltzmann_extend β Λ ω ζ)
  have hnum : ∫⁻ y in A, P.boltzmannFactor β Λ y
        ∂(Specification.isssd (S := Site) (E := Bool) uniformSpinMeasure Λ ω)
      = (2 ^ Λ.card : ℝ≥0∞)⁻¹ *
        ∑ ζ : Λ → Bool,
          A.indicator (fun _ ↦ ENNReal.ofReal (weight β Λ ω ζ)) (extend Λ ζ ω) := by
    rw [← lintegral_indicator hA,
      lintegral_isssd Λ ω
        ((Potential.measurable_boltzmannFactor (Φ := P) β Λ).indicator hA)]
    refine congrArg _ (Finset.sum_congr rfl fun ζ _ ↦ ?_)
    by_cases hx : extend Λ ζ ω ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact boltzmann_extend β Λ ω ζ
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [isingSpecification, Potential.gibbsSpecificationOfAbsolutelySummable,
    Specification.modification_apply,
    Specification.withDensity_premodifierNorm_apply uniformSpinMeasure
      (Potential.isPremodifier_boltzmannFactor (Φ := P) β) hA ω,
    hZ, hnum, gibbsMeasure_apply β Λ ω hA]
  exact inv_mul_cancel_aux hc0 hct

lemma spec_eq (β : ℝ) (Λ : Finset Site) (ω : Config) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω = gibbsMeasure β Λ ω :=
  Measure.ext fun _ hA ↦ spec_apply β Λ ω hA

/-! #### The DLR equation -/

lemma dlr_iff (β : ℝ) (μ : Measure Config) [IsProbabilityMeasure μ] :
    (∀ Λ : Finset Site, ∀ A : Set Config, MeasurableSet A →
        μ A = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ)
      ↔ Specification.IsGibbsMeasure (isingSpecification (latticeGraph 2) 1 0 β) μ := by
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  constructor
  · intro h Λ
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA
      (((isingSpecification (latticeGraph 2) 1 0 β Λ).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable)]
    calc ∫⁻ a, (isingSpecification (latticeGraph 2) 1 0 β Λ a) A ∂μ
        = ∫⁻ a, gibbsMeasure β Λ a A ∂μ := lintegral_congr fun a ↦ spec_apply β Λ a hA
      _ = μ A := (h Λ A hA).symm
  · intro h Λ A hA
    have h1 : μ.bind (isingSpecification (latticeGraph 2) 1 0 β Λ) A = μ A := by rw [h Λ]
    rw [Measure.bind_apply hA
      (((isingSpecification (latticeGraph 2) 1 0 β Λ).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable)] at h1
    calc μ A = ∫⁻ a, (isingSpecification (latticeGraph 2) 1 0 β Λ a) A ∂μ := h1.symm
      _ = ∫⁻ ω, gibbsMeasure β Λ ω A ∂μ := lintegral_congr fun a ↦ spec_apply β Λ a hA

lemma isGibbs_of_mem_GP (β : ℝ) (m : ProbabilityMeasure Config)
    (hm : m ∈ GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β)) :
    IsGibbs β (m : Measure Config) :=
  ⟨inferInstance, (dlr_iff β (m : Measure Config)).2 hm⟩

lemma mem_GP_of_isGibbs (β : ℝ) (μ : Measure Config) (h : IsGibbs β μ) :
    (⟨μ, h.1⟩ : ProbabilityMeasure Config) ∈
      GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β) := by
  have := h.1
  exact (dlr_iff β μ).1 h.2

/-! #### The lattice shifts and the spin flip -/

lemma shift_eq (j : Site) : (MeasureTheory.GibbsMeasure.shift Bool j).toFun = shift j :=
  funext fun ω ↦ funext fun i ↦ MeasureTheory.GibbsMeasure.shift_toFun_apply j ω i

lemma spinFlip_eq :
    MeasureTheory.GibbsMeasure.Peierls.spinFlip.toFun = fun (σ : Config) (i : Site) ↦ !σ i := rfl

end Bridge


/-! ### The bridge for the low-temperature limit -/

namespace LowTempBridge

open scoped ENNReal
open MeasureTheory.GibbsMeasure.Peierls (plusPhase minusPhase r
  plusPhase_mem_GP plusPhase_measurePreserving_shift plusPhase_real_ne_le
  minusPhase_mem_GP minusPhase_measurePreserving_shift minusPhase_real_ne_le
  tendsto_toReal_r_atTop)

/-- Georgii's plus phase `μ_+^β`, as a plain measure on the challenge's configuration space. -/
def muP (b : ℝ) : Measure Config := ((plusPhase b : ProbabilityMeasure Config) : Measure Config)

/-- Georgii's minus phase `μ_-^β = τ(μ_+^β)`, as a plain measure. -/
def muM (b : ℝ) : Measure Config := ((minusPhase b : ProbabilityMeasure Config) : Measure Config)

instance instIsProbabilityMeasureMuP (b : ℝ) : IsProbabilityMeasure (muP b) := (plusPhase b).2

instance instIsProbabilityMeasureMuM (b : ℝ) : IsProbabilityMeasure (muM b) := (minusPhase b).2

lemma muP_mem (b : ℝ) : muP b ∈ shiftInvariantGibbs b := by
  refine ⟨Bridge.isGibbs_of_mem_GP b (plusPhase b) (plusPhase_mem_GP b), fun j ↦ ?_⟩
  show Measure.map (shift j) (muP b) = muP b
  rw [← Bridge.shift_eq j]
  exact (plusPhase_measurePreserving_shift b j).map_eq

lemma muM_mem (b : ℝ) : muM b ∈ shiftInvariantGibbs b := by
  refine ⟨Bridge.isGibbs_of_mem_GP b (minusPhase b) (minusPhase_mem_GP b), fun j ↦ ?_⟩
  show Measure.map (shift j) (muM b) = muM b
  rw [← Bridge.shift_eq j]
  exact (minusPhase_measurePreserving_shift b j).map_eq

/-- The Peierls estimate together with `r(β) → 0` gives `μ_+^β(A) → δ_+(A)` for a local `A`. -/
lemma tendsto_toReal_muP {A : Set Config} (hA : IsLocalEvent A) :
    Tendsto (fun b : ℝ ↦ (muP b A).toReal) atTop
      (𝓝 (((Measure.dirac fun _ : Site ↦ true) : Measure Config) A).toReal) := by
  obtain ⟨Λ, hΛ⟩ := hA
  have hAm : MeasurableSet A := GibbsChallenge.measurableSet_of_inside hΛ
  have hdep : ∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A) :=
    fun _ _ h ↦ GibbsChallenge.mem_iff_mem_of_inside hΛ h
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine squeeze_zero' (g := fun b : ℝ ↦ (Λ.card : ℝ) * (r b).toReal)
    (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb
    exact abs_measureReal_sub_dirac_le (μ := muP b) (ω := fun _ : Site ↦ true)
      (c := (r b).toReal) (Λ := Λ) hAm hdep fun a _ ↦ plusPhase_real_ne_le hb a
  · simpa using tendsto_toReal_r_atTop.const_mul (Λ.card : ℝ)

/-- The same for the minus phase. -/
lemma tendsto_toReal_muM {A : Set Config} (hA : IsLocalEvent A) :
    Tendsto (fun b : ℝ ↦ (muM b A).toReal) atTop
      (𝓝 (((Measure.dirac fun _ : Site ↦ false) : Measure Config) A).toReal) := by
  obtain ⟨Λ, hΛ⟩ := hA
  have hAm : MeasurableSet A := GibbsChallenge.measurableSet_of_inside hΛ
  have hdep : ∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A) :=
    fun _ _ h ↦ GibbsChallenge.mem_iff_mem_of_inside hΛ h
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine squeeze_zero' (g := fun b : ℝ ↦ (Λ.card : ℝ) * (r b).toReal)
    (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb
    exact abs_measureReal_sub_dirac_le (μ := muM b) (ω := fun _ : Site ↦ false)
      (c := (r b).toReal) (Λ := Λ) hAm hdep fun a _ ↦ minusPhase_real_ne_le hb a
  · simpa using tendsto_toReal_r_atTop.const_mul (Λ.card : ℝ)

/-- The Peierls estimate for the plus phase, in the challenge's vocabulary. -/
lemma abs_muP_sub_dirac_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (Λ : Finset Site) {A : Set Config}
    (hAm : MeasurableSet A) (hdep : ∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) :
    |(muP b A).toReal - (((Measure.dirac fun _ : Site ↦ true) : Measure Config) A).toReal|
      ≤ Λ.card * (r b).toReal :=
  abs_measureReal_sub_dirac_le (μ := muP b) (ω := fun _ : Site ↦ true) (c := (r b).toReal)
    (Λ := Λ) hAm hdep fun a _ ↦ plusPhase_real_ne_le hb a

/-- The Peierls estimate for the minus phase. -/
lemma abs_muM_sub_dirac_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (Λ : Finset Site) {A : Set Config}
    (hAm : MeasurableSet A) (hdep : ∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) :
    |(muM b A).toReal - (((Measure.dirac fun _ : Site ↦ false) : Measure Config) A).toReal|
      ≤ Λ.card * (r b).toReal :=
  abs_measureReal_sub_dirac_le (μ := muM b) (ω := fun _ : Site ↦ false) (c := (r b).toReal)
    (Λ := Λ) hAm hdep fun a _ ↦ minusPhase_real_ne_le hb a

/-- The challenge's Peierls series is the library's. -/
lemma peierlsBound_eq (β : ℝ) : peierlsBound β = r β := rfl

/-- `μ_+^β → δ_+` locally, in the `ℝ≥0∞`-valued form of the preamble's `TendstoLocally`. -/
lemma tendsto_muP_apply {A : Set Config} (hA : IsLocalEvent A) :
    Tendsto (fun b : ℝ ↦ muP b A) atTop
      (𝓝 (((Measure.dirac fun _ : Site ↦ true) : Measure Config) A)) := by
  have h := tendsto_toReal_muP hA
  have hfun : (fun b : ℝ ↦ muP b A) = fun b : ℝ ↦ ENNReal.ofReal ((muP b A).toReal) := by
    funext b
    rw [ENNReal.ofReal_toReal (measure_ne_top (muP b) A)]
  rw [hfun, ← ENNReal.ofReal_toReal
    (measure_ne_top ((Measure.dirac fun _ : Site ↦ true) : Measure Config) A)]
  exact ENNReal.tendsto_ofReal h

/-- `μ_-^β → δ_-` locally. -/
lemma tendsto_muM_apply {A : Set Config} (hA : IsLocalEvent A) :
    Tendsto (fun b : ℝ ↦ muM b A) atTop
      (𝓝 (((Measure.dirac fun _ : Site ↦ false) : Measure Config) A)) := by
  have h := tendsto_toReal_muM hA
  have hfun : (fun b : ℝ ↦ muM b A) = fun b : ℝ ↦ ENNReal.ofReal ((muM b A).toReal) := by
    funext b
    rw [ENNReal.ofReal_toReal (measure_ne_top (muM b) A)]
  rw [hfun, ← ENNReal.ofReal_toReal
    (measure_ne_top ((Measure.dirac fun _ : Site ↦ false) : Measure Config) A)]
  exact ENNReal.tendsto_ofReal h

/-- Local convergence upgrades to convergence in Georgii's metric `d` of Remark (4.3)(3), by
dominated convergence for the series `∑ 2⁻ⁿ |·|`. -/
lemma tendsto_localDist_muP (A : ℕ → Set Config) (hA : ∀ n : ℕ, IsLocalEvent (A n)) :
    Tendsto (fun b : ℝ ↦ localDist A (muP b) (Measure.dirac fun _ : Site ↦ true))
      atTop (𝓝 0) := by
  have hterm : ∀ n : ℕ, Tendsto (fun b : ℝ ↦ (2 : ℝ)⁻¹ ^ (n + 1) *
      |(muP b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ true) : Measure Config) (A n)).toReal|)
      atTop (𝓝 0) := by
    intro n
    have h2 : Tendsto (fun b : ℝ ↦ |(muP b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ true) : Measure Config) (A n)).toReal|)
        atTop (𝓝 0) := by
      simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.1 (tendsto_toReal_muP (hA n))
    simpa using h2.const_mul ((2 : ℝ)⁻¹ ^ (n + 1))
  have hbd : ∀ᶠ b : ℝ in atTop, ∀ n : ℕ, ‖(2 : ℝ)⁻¹ ^ (n + 1) *
      |(muP b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ true) : Measure Config) (A n)).toReal|‖
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
    refine Eventually.of_forall fun b n ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (localDist_summand_nonneg A (muP b) _ n)]
    exact localDist_summand_le (μ := muP b) (ν := (Measure.dirac fun _ : Site ↦ true)) A n
  simpa [localDist] using tendsto_tsum_of_dominated_convergence summable_geomHalf hterm hbd

/-- The same for the minus phase. -/
lemma tendsto_localDist_muM (A : ℕ → Set Config) (hA : ∀ n : ℕ, IsLocalEvent (A n)) :
    Tendsto (fun b : ℝ ↦ localDist A (muM b) (Measure.dirac fun _ : Site ↦ false))
      atTop (𝓝 0) := by
  have hterm : ∀ n : ℕ, Tendsto (fun b : ℝ ↦ (2 : ℝ)⁻¹ ^ (n + 1) *
      |(muM b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ false) : Measure Config) (A n)).toReal|)
      atTop (𝓝 0) := by
    intro n
    have h2 : Tendsto (fun b : ℝ ↦ |(muM b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ false) : Measure Config) (A n)).toReal|)
        atTop (𝓝 0) := by
      simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.1 (tendsto_toReal_muM (hA n))
    simpa using h2.const_mul ((2 : ℝ)⁻¹ ^ (n + 1))
  have hbd : ∀ᶠ b : ℝ in atTop, ∀ n : ℕ, ‖(2 : ℝ)⁻¹ ^ (n + 1) *
      |(muM b (A n)).toReal -
        (((Measure.dirac fun _ : Site ↦ false) : Measure Config) (A n)).toReal|‖
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
    refine Eventually.of_forall fun b n ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (localDist_summand_nonneg A (muM b) _ n)]
    exact localDist_summand_le (μ := muM b) (ν := (Measure.dirac fun _ : Site ↦ false)) A n
  simpa [localDist] using tendsto_tsum_of_dominated_convergence summable_geomHalf hterm hbd

end LowTempBridge

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), first assertion**, in the form produced by Georgii's proof: there
are families `β ↦ μ₊^β`, `β ↦ μ₋^β` of shift-invariant Gibbs measures of the two-dimensional Ising
ferromagnet with `μ₊^β → δ₊` and `μ₋^β → δ₋` as `β → ∞`, both in the topology of local convergence
(4.2) and in every metric `d` of Remark (4.3)(3) built from a sequence of local events. -/
theorem ising_low_temperature_limit :
    ∃ μp μm : ℝ → Measure Config,
      (∀ β : ℝ, μp β ∈ shiftInvariantGibbs β) ∧
      (∀ β : ℝ, μm β ∈ shiftInvariantGibbs β) ∧
      TendstoLocally μp atTop (Measure.dirac fun _ : Site ↦ true) ∧
      TendstoLocally μm atTop (Measure.dirac fun _ : Site ↦ false) ∧
      (∀ A : ℕ → Set Config, (∀ n : ℕ, IsLocalEvent (A n)) →
        Tendsto (fun β : ℝ ↦ localDist A (μp β) (Measure.dirac fun _ : Site ↦ true))
            atTop (𝓝 0) ∧
          Tendsto (fun β : ℝ ↦ localDist A (μm β) (Measure.dirac fun _ : Site ↦ false))
            atTop (𝓝 0)) := by
  refine ⟨LowTempBridge.muP, LowTempBridge.muM, LowTempBridge.muP_mem, LowTempBridge.muM_mem,
    fun _ hA ↦ LowTempBridge.tendsto_muP_apply hA,
    fun _ hA ↦ LowTempBridge.tendsto_muM_apply hA,
    fun A hA ↦ ⟨LowTempBridge.tendsto_localDist_muP A hA,
      LowTempBridge.tendsto_localDist_muM A hA⟩⟩

/-- **Georgii, Theorem (6.9), first assertion**, in the displayed form
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`, for the metric `d` of Remark
(4.3)(3) built from an arbitrary sequence `A` of local events. -/
theorem ising_low_temperature_localDistSet (A : ℕ → Set Config)
    (hA : ∀ n : ℕ, IsLocalEvent (A n)) :
    Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ true)) atTop (𝓝 0) ∧
      Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ false)) atTop (𝓝 0) := by
  obtain ⟨μp, μm, hp, hm, -, -, hd⟩ := ising_low_temperature_limit
  obtain ⟨hdp, hdm⟩ := hd A hA
  exact ⟨squeeze_zero (fun _ ↦ localDistSet_nonneg A _ _) (fun b ↦ localDistSet_le A (hp b)) hdp,
    squeeze_zero (fun _ ↦ localDistSet_nonneg A _ _) (fun b ↦ localDistSet_le A (hm b)) hdm⟩

/-- **Georgii, Theorem (6.9), first assertion** in quantitative form: shift-invariant Gibbs
measures `μ₊^β, μ₋^β` with `|μ_±^β(A) − δ_±(A)| ≤ |Λ| r(β)` for `β ≥ 8 log 2` and every `Λ`-local
`A`, where `r(β)` is `peierlsBound` and `r(β) → 0`.  `8 log 2` and the constant inside
`peierlsBound` are what this development proves; they are not sharp, and nothing is asserted about
the critical inverse temperature. -/
theorem ising_low_temperature_peierls :
    Tendsto (fun β : ℝ ↦ (peierlsBound β).toReal) atTop (𝓝 0) ∧
      ∃ μp μm : ℝ → Measure Config,
        (∀ β : ℝ, μp β ∈ shiftInvariantGibbs β) ∧
        (∀ β : ℝ, μm β ∈ shiftInvariantGibbs β) ∧
        (∀ β : ℝ, 8 * Real.log 2 ≤ β → ∀ (Λ : Finset Site) (A : Set Config), MeasurableSet A →
          (∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) →
            |(μp β A).toReal
                - (((Measure.dirac fun _ : Site ↦ true) : Measure Config) A).toReal|
              ≤ Λ.card * (peierlsBound β).toReal) ∧
        ∀ β : ℝ, 8 * Real.log 2 ≤ β → ∀ (Λ : Finset Site) (A : Set Config), MeasurableSet A →
          (∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) →
            |(μm β A).toReal
                - (((Measure.dirac fun _ : Site ↦ false) : Measure Config) A).toReal|
              ≤ Λ.card * (peierlsBound β).toReal := by
  refine ⟨?_, LowTempBridge.muP, LowTempBridge.muM, LowTempBridge.muP_mem,
    LowTempBridge.muM_mem, fun β hβ Λ A hAm hdep ↦ ?_, fun β hβ Λ A hAm hdep ↦ ?_⟩
  · simpa only [LowTempBridge.peierlsBound_eq] using
      MeasureTheory.GibbsMeasure.Peierls.tendsto_toReal_r_atTop
  · rw [LowTempBridge.peierlsBound_eq]
    exact LowTempBridge.abs_muP_sub_dirac_le hβ Λ hAm hdep
  · rw [LowTempBridge.peierlsBound_eq]
    exact LowTempBridge.abs_muM_sub_dirac_le hβ Λ hAm hdep


end IsingChallenge

end
