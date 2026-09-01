import Comparator.Defs_Ising
import GibbsMeasure

/-!
# Comparator solution: the two-dimensional Ising phase transition

The solution file matching `Comparator/Challenge.lean`, whose statements it repeats verbatim over
the same from-scratch definitions of `Comparator.Defs_Ising`.

The auxiliary `Bridge` namespace identifies those definitions with the `GibbsMeasure` library's:
`gibbsMeasure β Λ ω` is literally the `Λ`-kernel of `isingSpecification (latticeGraph 2) 1 0 β`,
whence `IsGibbs β μ ↔ μ ∈ GP (isingSpecification (latticeGraph 2) 1 0 β)`; `nonUniqueness` and
`betaC` are `isingNonUniqueness` and `isingBetaC`; `IsLocal` is membership of `localEvents`; the
all-`+` local limit is `plusState`, and `∫ σ, spin (σ 0)` against it is
`spontaneousMagnetisation`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

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

/-! #### Non-uniqueness and the critical inverse temperature -/

lemma exists_two_iff_nontrivial (β : ℝ) :
    (∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν)
      ↔ (GP (S := Site) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial := by
  constructor
  · rintro ⟨μ, ν, hμ, hν, hμν⟩
    exact ⟨⟨μ, hμ.1⟩, mem_GP_of_isGibbs β μ hμ, ⟨ν, hν.1⟩, mem_GP_of_isGibbs β ν hν,
      fun h ↦ hμν (congrArg Subtype.val h)⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨(x : Measure Config), (y : Measure Config), isGibbs_of_mem_GP β x hx,
      isGibbs_of_mem_GP β y hy, fun h ↦ hxy (ProbabilityMeasure.toMeasure_injective h)⟩

lemma nonUniqueness_eq : nonUniqueness = MeasureTheory.GibbsMeasure.isingNonUniqueness :=
  Set.ext fun β ↦ and_congr_right fun _ ↦ exists_two_iff_nontrivial β

lemma betaC_eq : betaC = MeasureTheory.GibbsMeasure.isingBetaC :=
  congrArg sInf nonUniqueness_eq

/-! #### Local events -/

lemma isLocalEvent_iff {A : Set Config} : IsLocal A ↔ A ∈ localEvents Site Bool := by
  constructor
  · rintro ⟨Λ, hΛ⟩
    refine mem_localEvents_iff_exists_finsetRestrict_preimage.2
      ⟨Λ, Λ.restrict '' A, (Set.toFinite _).measurableSet, Set.ext fun σ ↦ ?_⟩
    refine ⟨fun hσ ↦ ⟨σ, hσ, rfl⟩, ?_⟩
    rintro ⟨τ, hτ, hres⟩
    exact (hΛ τ σ fun i hi ↦ congrFun hres ⟨i, hi⟩).1 hτ
  · intro hA
    obtain ⟨Λ, B, -, rfl⟩ := mem_localEvents_iff_exists_finsetRestrict_preimage.1 hA
    exact ⟨Λ, fun σ τ h ↦ by
      simp only [Set.mem_preimage]
      rw [show Λ.restrict σ = Λ.restrict τ from funext fun i ↦ h i i.2]⟩

lemma measurableSet_of_isLocalEvent {A : Set Config} (hA : IsLocal A) : MeasurableSet A :=
  MeasurableSet.of_mem_measurableCylinders (isLocalEvent_iff.1 hA)

lemma isLocalEvent_univ : IsLocal (Set.univ : Set Config) := ⟨∅, fun _ _ _ ↦ Iff.rfl⟩

/-! #### The plus and the minus phase -/

open Filter Topology in
lemma tendsto_plus (β : ℝ) (hβ : 0 ≤ β) {A : Set Config} (hA : IsLocal A) :
    Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A) atTop
      (𝓝 ((MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β : Measure Config) A)) := by
  have h := MeasureTheory.GibbsMeasure.tendsto_measure_plusState (latticeGraph 2) 1 0 β
    zero_le_one hβ (isLocalEvent_iff.1 hA)
  refine h.congr fun Λ ↦ ?_
  exact spec_apply β Λ _ (measurableSet_of_isLocalEvent hA)

open Filter Topology in
lemma tendsto_minus (β : ℝ) (hβ : 0 ≤ β) {A : Set Config} (hA : IsLocal A) :
    Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ false) A) atTop
      (𝓝 ((MeasureTheory.GibbsMeasure.minusState (latticeGraph 2) 1 0 β : Measure Config) A)) := by
  have h := MeasureTheory.GibbsMeasure.tendsto_measure_minusState (latticeGraph 2) 1 0 β
    zero_le_one hβ (isLocalEvent_iff.1 hA)
  refine h.congr fun Λ ↦ ?_
  exact spec_apply β Λ _ (measurableSet_of_isLocalEvent hA)

open Filter Topology in
/-- A measure agreeing with the all-`+` local limit on every local event is the plus phase. -/
lemma eq_plusState (β : ℝ) (hβ : 0 ≤ β) (μ : Measure Config)
    (hμ : ∀ A : Set Config, IsLocal A →
      Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A) atTop (𝓝 (μ A))) :
    μ = (MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β : Measure Config) := by
  have key : ∀ A ∈ localEvents Site Bool, μ A =
      (MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β : Measure Config) A :=
    fun A hA ↦ tendsto_nhds_unique (hμ A (isLocalEvent_iff.2 hA))
      (tendsto_plus β hβ (isLocalEvent_iff.2 hA))
  have huniv : μ Set.univ = 1 := by
    rw [key _ (isLocalEvent_iff.1 isLocalEvent_univ), measure_univ]
  have : IsFiniteMeasure μ := ⟨by rw [huniv]; exact ENNReal.one_lt_top⟩
  refine MeasureTheory.ext_of_generate_finite (localEvents Site Bool) ?_
    isPiSystem_measurableCylinders key ?_
  · exact generateFrom_measurableCylinders.symm
  · rw [huniv, measure_univ]

lemma isGibbs_plusState (β : ℝ) (hβ : 0 ≤ β) :
    IsGibbs β (MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β : Measure Config) :=
  isGibbs_of_mem_GP β _
    (MeasureTheory.GibbsMeasure.plusState_mem_GP (latticeGraph 2) 1 0 β zero_le_one hβ)

lemma isGibbs_minusState (β : ℝ) (hβ : 0 ≤ β) :
    IsGibbs β (MeasureTheory.GibbsMeasure.minusState (latticeGraph 2) 1 0 β : Measure Config) :=
  isGibbs_of_mem_GP β _
    (MeasureTheory.GibbsMeasure.minusState_mem_GP (latticeGraph 2) 1 0 β zero_le_one hβ)

/-- Every Gibbs measure is dominated by the plus phase on measurable increasing events. -/
lemma le_plusState (β : ℝ) (hβ : 0 ≤ β) {μ : Measure Config} (hμ : IsGibbs β μ)
    {A : Set Config} (hA : MeasurableSet A) (hup : IsUpperSet A) :
    μ A ≤ (MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β : Measure Config) A :=
  MeasureTheory.GibbsMeasure.stochasticallyLE_plusState (latticeGraph 2) 1 0 β zero_le_one hβ
    (mem_GP_of_isGibbs β μ hμ) hA hup

/-- The minus phase is dominated by every Gibbs measure on measurable increasing events. -/
lemma minusState_le (β : ℝ) (hβ : 0 ≤ β) {μ : Measure Config} (hμ : IsGibbs β μ)
    {A : Set Config} (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (MeasureTheory.GibbsMeasure.minusState (latticeGraph 2) 1 0 β : Measure Config) A ≤ μ A :=
  MeasureTheory.GibbsMeasure.minusState_stochasticallyLE (latticeGraph 2) 1 0 β zero_le_one hβ
    (mem_GP_of_isGibbs β μ hμ) hA hup

/-! #### The spontaneous magnetisation -/

lemma integral_spin_plusState (β : ℝ) :
    ∫ σ, spin (σ 0) ∂(MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β :
        Measure Config)
      = MeasureTheory.GibbsMeasure.spontaneousMagnetisation β := by
  rw [spin_eq, MeasureTheory.GibbsMeasure.Peierls.integral_spin_eq
    (MeasureTheory.GibbsMeasure.plusState (latticeGraph 2) 1 0 β)]
  rfl

end Bridge

/-! ### The theorems -/

/-- **Georgii (6.9)**, the "in particular" half at the explicit threshold `log 3`: for `β ≥ log 3`
the two-dimensional Ising ferromagnet admits two distinct shift-invariant Gibbs measures, exchanged
by the global spin flip, with spontaneous magnetisations of opposite sign. -/
theorem ising_phase_transition (β : ℝ) (hβ : Real.log 3 ≤ β) :
    ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      μp ≠ μm ∧
      (∀ j : Site, μp.map (shift j) = μp) ∧
      (∀ j : Site, μm.map (shift j) = μm) ∧
      μm = μp.map (fun σ i ↦ !σ i) ∧
      ∫ σ, spin (σ 0) ∂μm < 0 ∧
      0 < ∫ σ, spin (σ 0) ∂μp := by
  have hb : Real.log 9 ≤ 2 * β := by
    rw [← MeasureTheory.GibbsMeasure.PeierlsSharp.log_nine_div_two] at hβ
    linarith
  obtain ⟨mp, mm, hne, hp, hm, hsp, hsm, hmap, -, hgt, hgtT⟩ :=
    MeasureTheory.GibbsMeasure.PeierlsSharp.exists_two_shiftInvariant_gibbs_sharp β hb
  refine ⟨(mp : Measure Config), (mm : Measure Config),
    Bridge.isGibbs_of_mem_GP β mp hp, Bridge.isGibbs_of_mem_GP β mm hm,
    fun hcon ↦ hne (ProbabilityMeasure.toMeasure_injective hcon), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [← Bridge.shift_eq j]
    exact (hsp j).map_eq
  · intro j
    rw [← Bridge.shift_eq j]
    exact (hsm j).map_eq
  · rw [hmap, ← Bridge.spinFlip_eq]
  · exact MeasureTheory.GibbsMeasure.Peierls.integral_spin_neg hgt
  · exact MeasureTheory.GibbsMeasure.Peierls.integral_spin_pos hgtT

/-- **Georgii (8.7) with (8.8)**, Dobrushin's uniqueness condition: `β_c ≥ 1/4`. -/
theorem quarter_le_betaC : (1 : ℝ) / 4 ≤ betaC := by
  rw [Bridge.betaC_eq]
  exact MeasureTheory.GibbsMeasure.le_isingBetaC

/-- `β_c ≤ log 3`, by the Peierls argument at Georgii's own contour count. -/
theorem betaC_le_log_three : betaC ≤ Real.log 3 := by
  rw [Bridge.betaC_eq]
  exact MeasureTheory.GibbsMeasure.isingBetaC_le

/-- For every `0 ≤ β < β_c` there is exactly one Gibbs measure. -/
theorem ising_existsUnique_gibbs_of_lt_betaC (β : ℝ) (hβ₀ : 0 ≤ β) (hβ : β < betaC) :
    ∃! μ : Measure Config, IsGibbs β μ := by
  rw [Bridge.betaC_eq] at hβ
  obtain ⟨m, hm, huniq⟩ := MeasureTheory.GibbsMeasure.existsUnique_of_lt_isingBetaC hβ₀ hβ
  refine ⟨(m : Measure Config), Bridge.isGibbs_of_mem_GP β m hm, fun ν hν ↦ ?_⟩
  exact congrArg (fun x : ProbabilityMeasure Config ↦ (x : Measure Config))
    (huniq ⟨ν, hν.1⟩ (Bridge.mem_GP_of_isGibbs β ν hν))

/-- For every `β > β_c` there are two distinct Gibbs measures. -/
theorem ising_nonuniqueness_of_betaC_lt (β : ℝ) (hβ : betaC < β) :
    ∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν := by
  rw [Bridge.betaC_eq] at hβ
  exact (Bridge.exists_two_iff_nontrivial β).2
    (MeasureTheory.GibbsMeasure.nontrivial_of_isingBetaC_lt hβ)

/-- Uniqueness at high temperature, up to the critical inverse temperature. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < betaC → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν := by
  intro β hβ₀ hβ μ ν hμ hν
  exact (ising_existsUnique_gibbs_of_lt_betaC β hβ₀ hβ).unique hμ hν

/-- **Georgii (8.7) with (8.8)**: since every site has four neighbours, Dobrushin's condition
holds as soon as `β < 1 / 4`, so the Gibbs measure is then unique. -/
theorem ising_uniqueness_of_lt_quarter :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  fun β hβ₀ hβ ↦ ising_uniqueness_at_high_temperature β hβ₀ (hβ.trans_le quarter_le_betaC)

/-- **Georgii, Section 6.2, after (6.9)**: for `β ≥ 0` the finite-volume Gibbs distributions with
constant boundary conditions converge on every local event to Gibbs measures `μ₊` and `μ₋`.
Georgii records there only that the magnetisation of `μ₊^β` is maximal; the stochastic sandwich
`μ₋ ≼ μ ≼ μ₊` on increasing events stated here is the FKG strengthening from which that
follows. -/
theorem ising_plus_minus_phases (β : ℝ) (hβ : 0 ≤ β) :
    ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      (∀ A : Set Config, IsLocal A →
        Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A)
          Filter.atTop (nhds (μp A))) ∧
      (∀ A : Set Config, IsLocal A →
        Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ false) A)
          Filter.atTop (nhds (μm A))) ∧
      (∀ μ : Measure Config, IsGibbs β μ →
        ∀ A : Set Config, MeasurableSet A → IsUpperSet A → μ A ≤ μp A) ∧
      (∀ μ : Measure Config, IsGibbs β μ →
        ∀ A : Set Config, MeasurableSet A → IsUpperSet A → μm A ≤ μ A) := by
  exact ⟨_, _, Bridge.isGibbs_plusState β hβ, Bridge.isGibbs_minusState β hβ,
    fun A hA ↦ Bridge.tendsto_plus β hβ hA, fun A hA ↦ Bridge.tendsto_minus β hβ hA,
    fun μ hμ A hA hup ↦ Bridge.le_plusState β hβ hμ hA hup,
    fun μ hμ A hA hup ↦ Bridge.minusState_le β hβ hμ hA hup⟩

/-- **Georgii, Section 6.2** (the Lebowitz–Martin-Löf/Ruelle criterion, cited there without
proof): for `β ≥ 0` the model has more than one Gibbs measure iff the spontaneous magnetisation is
strictly positive. Here `μ₊` is pinned down as the all-`+` local limit, which exists by
`ising_plus_minus_phases`. -/
theorem ising_lebowitz_martin_lof (β : ℝ) (hβ : 0 ≤ β) (μp : Measure Config)
    (hμp : ∀ A : Set Config, IsLocal A →
      Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A)
        Filter.atTop (nhds (μp A))) :
    (∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν)
      ↔ 0 < ∫ σ, spin (σ 0) ∂μp := by
  rw [Bridge.eq_plusState β hβ μp hμp, Bridge.integral_spin_plusState,
    Bridge.exists_two_iff_nontrivial β]
  exact MeasureTheory.GibbsMeasure.nontrivial_GP_ising2D_iff_spontaneousMagnetisation_pos β hβ

end IsingChallenge

end
