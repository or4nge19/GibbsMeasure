import Comparator.Defs

/-!
# Definitions: uniqueness in one dimension (Georgii, Section 8.3)

Vocabulary for Georgii's Section 8.3: the oscillation of (8.2), potentials in the sense of
Definition (2.2), the Hamiltonian (2.3), the Boltzmann factor (2.4), the finite-volume Gibbs
distribution (2.9) against an arbitrary σ-finite a priori measure, the uniform domination
hypothesis of Proposition (8.38), the spanning sum of condition (8.40) and the chain structure
that condition exploits.

## Main definitions

* `osc`: the oscillation `δ(f) = sup f - inf f` of (8.2)
* `IsPotential`, `hamiltonian`, `boltzmannFactor`: Georgii (2.2)-(2.4)
* `freeMeasure`, `partitionFunction`, `IsAdmissible`, `gibbsKernel`: Georgii (1.26), (2.7)-(2.9)
* `IsAbsolutelySummable`: Georgii's class `ℬ` of (2.11)
* `IsUniformlyDominated`: the hypothesis of Proposition (8.38)
* `Spans`, `oscSpan`: the sum of condition (8.40)
* `HasBoundedBoundary`: the chain structure of `ℤ` and `ℕ` exploited in (8.39)

Following Convention (2.1), `HasHamiltonian` is the convergence of the net of partial sums
`∑_{A ⊆ Δ} Φ_A` over finite volumes ordered by inclusion, which is strictly weaker than absolute
summability; Theorem (8.39) is stated at exactly this generality. `IsAbsolutelySummable` is used
only where Georgii uses it, namely for the existence half of (8.39).

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Section 8.3
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace OneDimChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## Georgii (8.2): the oscillation -/

/-- **Georgii (8.2)**: the oscillation `δ(f) = sup f − inf f = sup_{ζ,η} |f(ζ) − f(η)|`, valued in
`[0, ∞]` so that no boundedness need be assumed. -/
def osc (f : Config S E → ℝ) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E), ENNReal.ofReal |f ζ - f η|

omit [MeasurableSpace E] in
theorem le_osc (f : Config S E → ℝ) (ζ η : Config S E) :
    ENNReal.ofReal |f ζ - f η| ≤ osc f :=
  le_iSup_of_le ζ (le_iSup_of_le η le_rfl)

omit [MeasurableSpace E] in
theorem osc_le {f : Config S E → ℝ} {c : ℝ≥0∞}
    (h : ∀ ζ η : Config S E, ENNReal.ofReal |f ζ - f η| ≤ c) : osc f ≤ c :=
  iSup₂_le h

omit [MeasurableSpace E] in
@[simp] theorem osc_const (r : ℝ) : osc (fun _ : Config S E ↦ r) = 0 := by
  simp [osc]

/-! ## Georgii (2.1)–(2.4): potentials, Hamiltonians, Boltzmann factors -/

/-- The interaction terms entering the Hamiltonian in the volume `Λ` (Georgii (2.3)), extended by
zero: `Φ_A` for those supports `A` that meet `Λ`, and `0` otherwise. -/
def hamiltonianTerm (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E)
    (A : Finset S) : ℝ :=
  {B : Finset S | ∃ i ∈ B, i ∈ Λ}.indicator (fun B ↦ Φ B ω) A

/-- **Georgii, Convention (2.1)**: the sum `∑_{A ∩ Λ ≠ ∅} Φ_A` is the limit of the partial sums
`∑_{A ⊆ Δ} Φ_A` over the finite volumes `Δ` ordered by inclusion.  `HasHamiltonian Φ Λ ω h` says
that this net converges to `h`. -/
def HasHamiltonian (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) (h : ℝ) :
    Prop :=
  Tendsto (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, hamiltonianTerm Φ Λ ω A) atTop (𝓝 h)

/-- **Georgii, Definition (2.2)**: a family `Φ` indexed by the finite subsets of `S` with each
`Φ_A` being `𝓕_A`-measurable and each Hamiltonian series convergent in the sense of Convention
(2.1).  No *absolute* convergence is assumed; that is the separate class `ℬ` of (2.11), see
`IsAbsolutelySummable`. -/
structure IsPotential (Φ : Finset S → Config S E → ℝ) : Prop where
  /-- Georgii (2.2)(i): `Φ_A` is `𝓕_A`-measurable. -/
  measurable_inside : ∀ A : Finset S, Measurable[inside A] (Φ A)
  /-- Georgii (2.2)(ii): the Hamiltonian series converges in the sense of Convention (2.1). -/
  exists_hasHamiltonian : ∀ (Λ : Finset S) (ω : Config S E), ∃ h : ℝ, HasHamiltonian Φ Λ ω h

/-- **Georgii (2.3)**: the Hamiltonian `H_Λ^Φ = ∑_{A ∩ Λ ≠ ∅} Φ_A`, the limit of the partial sums
of `hamiltonianTerm` over increasing volumes. -/
def hamiltonian (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) : ℝ :=
  limUnder atTop (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset, hamiltonianTerm Φ Λ ω A)

theorem hasHamiltonian_hamiltonian {Φ : Finset S → Config S E → ℝ} (hΦ : IsPotential Φ)
    (Λ : Finset S) (ω : Config S E) : HasHamiltonian Φ Λ ω (hamiltonian Φ Λ ω) := by
  obtain ⟨h, hh⟩ := hΦ.exists_hasHamiltonian Λ ω
  rwa [hamiltonian, hh.limUnder_eq]

omit [MeasurableSpace E] in
theorem hamiltonian_eq_of_hasHamiltonian {Φ : Finset S → Config S E → ℝ} {Λ : Finset S}
    {ω : Config S E} {h : ℝ} (hh : HasHamiltonian Φ Λ ω h) : hamiltonian Φ Λ ω = h :=
  hh.limUnder_eq

/-- **The Boltzmann factor** `h_Λ^Φ = e^{−β H_Λ^Φ}`, Georgii (2.4). -/
def boltzmannFactor (Φ : Finset S → Config S E → ℝ) (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * hamiltonian Φ Λ ω))

/-! ## Georgii (1.26), (2.7)–(2.9): the finite-volume Gibbs distribution -/

open Classical in
/-- Extend an inner configuration `ζ : Λ → E` to a configuration on all of `S`, keeping the
boundary condition `ω` outside `Λ`. -/
def extend (Λ : Finset S) (ζ : Λ → E) (ω : Config S E) : Config S E :=
  fun i ↦ if h : i ∈ Λ then ζ ⟨i, h⟩ else ω i

theorem measurable_extend (Λ : Finset S) (ω : Config S E) :
    Measurable fun ζ : Λ → E ↦ extend Λ ζ ω := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ Λ
  · have h : (fun ζ : Λ → E ↦ extend Λ ζ ω i) = fun ζ ↦ ζ ⟨i, hi⟩ := by
      funext ζ; simp [extend, hi]
    rw [h]; exact measurable_pi_apply _
  · have h : (fun ζ : Λ → E ↦ extend Λ ζ ω i) = fun _ ↦ ω i := by
      funext ζ; simp [extend, hi]
    rw [h]; exact measurable_const

/-- **Georgii, Notation (1.26)**: the finite-volume a priori measure
`λ_Λ(·|ω) = λ^Λ × δ_{ω_{S∖Λ}}`.  No normalization of `λ` is assumed. -/
def freeMeasure (lam : Measure E) (Λ : Finset S) (ω : Config S E) : Measure (Config S E) :=
  Measure.map (fun ζ : Λ → E ↦ extend Λ ζ ω) (Measure.pi fun _ : Λ ↦ lam)

/-- **The partition function** `Z_Λ^Φ(ω) = λ_Λ(h_Λ^Φ|ω)`, Georgii (2.7). -/
def partitionFunction (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : ℝ≥0∞ :=
  ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω)

/-- **`λ`-admissibility**, Georgii (2.7): every finite-volume partition function is non-zero and
finite — Georgii asks only that `Z_Λ^Φ(ω)` be finite, the non-vanishing being implicit in the
quotient (2.8). -/
def IsAdmissible (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) : Prop :=
  ∀ (Λ : Finset S) (ω : Config S E),
    partitionFunction Φ lam β Λ ω ≠ 0 ∧ partitionFunction Φ lam β Λ ω ≠ ⊤

/-- **Georgii, Definition (2.9)**: the finite-volume Gibbs distribution
`γ_Λ^Φ(A | ω) = Z_Λ^Φ(ω)⁻¹ ∫ 1_A(σ) e^{−β H_Λ^Φ(σ)} λ_Λ(dσ|ω)`.  Numerator and normalization use
the same un-normalized `λ`, so the total mass `λ(E)^{|Λ|}` cancels. -/
def gibbsKernel (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : Measure (Config S E) :=
  (partitionFunction Φ lam β Λ ω)⁻¹ • (freeMeasure lam Λ ω).withDensity (boltzmannFactor Φ β Λ)

theorem gibbsKernel_apply (Φ : Finset S → Config S E → ℝ) (lam : Measure E) (β : ℝ)
    (Λ : Finset S) (ω : Config S E) {A : Set (Config S E)} (hA : MeasurableSet A) :
    gibbsKernel Φ lam β Λ ω A
      = (∫⁻ σ in A, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω))
        / ∫⁻ σ, boltzmannFactor Φ β Λ σ ∂(freeMeasure lam Λ ω) := by
  rw [gibbsKernel, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA, partitionFunction,
    ENNReal.div_eq_inv_mul]

/-! ## Georgii (2.11), (2.12): absolutely summable potentials -/

/-- **Georgii (2.12)**: the interaction norm `‖Φ‖_i = ∑_{A ∋ i} sup_ω |Φ_A(ω)|`. -/
def potentialNormAt (Φ : Finset S → Config S E → ℝ) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {B : Finset S | i ∈ B}.indicator (fun B ↦ ⨆ ω : Config S E, ENNReal.ofReal |Φ B ω|) A

/-- **Georgii (2.11)**: `Φ ∈ ℬ`, i.e. `‖Φ‖_i < ∞` at every site. -/
def IsAbsolutelySummable (Φ : Finset S → Config S E → ℝ) : Prop :=
  ∀ i : S, potentialNormAt Φ i ≠ ⊤

/-! ## Georgii (8.38): uniform domination -/

/-- **The hypothesis of Georgii, Proposition (8.38)**: every cylinder event `A` admits a volume
`Λ` with `γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all boundary conditions `ζ, η`. -/
def IsUniformlyDominated (γ : Finset S → Config S E → Measure (Config S E)) (c : ℝ≥0∞) : Prop :=
  ∀ A : Set (Config S E), IsLocalEvent A →
    ∃ Λ : Finset S, ∀ ζ η : Config S E, c * γ Λ η A ≤ γ Λ ζ A

/-! ## Events inside a finite volume -/

def restrictInside (Δ : Finset S) (ω : Config S E) : {i : S // i ∈ Δ} → E := fun i ↦ ω i.1

theorem measurable_restrictInside (Δ : Finset S) :
    Measurable[inside Δ] (restrictInside (E := E) Δ) :=
  measurable_pi_of _ fun i ↦ Measurable.of_comap_le (comap_le_inside i.2)

/-- `𝓕_Δ` is the σ-algebra pulled back along the restriction map `ω ↦ ω|_Δ`. -/
theorem inside_eq_comap (Δ : Finset S) :
    inside (E := E) Δ = MeasurableSpace.comap (restrictInside Δ) inferInstance := by
  refine le_antisymm ?_ (measurable_restrictInside Δ).comap_le
  refine iSup₂_le fun i hi ↦ ?_
  have h1 : Measurable[MeasurableSpace.comap (restrictInside (E := E) Δ) inferInstance]
      (restrictInside Δ) := Measurable.of_comap_le le_rfl
  exact ((measurable_pi_apply (⟨i, by simpa using hi⟩ : {i : S // i ∈ Δ})).comp h1).comap_le

/-- Events measurable inside `Δ` do not depend on the coordinates outside `Δ`. -/
theorem mem_iff_mem_of_inside {Δ : Finset S} {B : Set (Config S E)}
    (hB : MeasurableSet[inside Δ] B) {ω ω' : Config S E} (h : ∀ i ∈ Δ, ω i = ω' i) :
    ω ∈ B ↔ ω' ∈ B := by
  rw [inside_eq_comap] at hB
  obtain ⟨C, -, rfl⟩ := hB
  have hr : restrictInside Δ ω = restrictInside Δ ω' := funext fun i ↦ h i.1 i.2
  simp only [Set.mem_preimage, hr]

/-- For `Δ ⊆ Λ`, the measure of a `Δ`-local event under `freeMeasure lam Λ ω` does not depend on
the boundary condition `ω`. -/
theorem freeMeasure_apply_congr (lam : Measure E) {Δ Λ : Finset S} (hΔΛ : Δ ⊆ Λ)
    {A : Set (Config S E)} (hA : MeasurableSet[inside Δ] A) (ω ω' : Config S E) :
    freeMeasure lam Λ ω A = freeMeasure lam Λ ω' A := by
  have hAm : MeasurableSet A := measurableSet_of_inside hA
  rw [freeMeasure, freeMeasure, Measure.map_apply (measurable_extend Λ ω) hAm,
    Measure.map_apply (measurable_extend Λ ω') hAm]
  congr 1
  ext ζ
  simp only [Set.mem_preimage]
  exact mem_iff_mem_of_inside hA fun i hi ↦ by simp [extend, hΔΛ hi]

/-! ## Georgii (8.40): the spanning sum -/

section Order

variable [Preorder S]

/-- `A` **spans** the site `i`, i.e. `min A ≤ i < max A`: `A` has an element `≤ i` and an element
`> i`.  (For `A = ∅` this is false, matching `min ∅ = ∞`.) -/
def Spans (A : Finset S) (i : S) : Prop := (∃ a ∈ A, a ≤ i) ∧ ∃ b ∈ A, i < b

/-- **Georgii (8.40)**: the sum `∑_{A ∈ 𝓢, min A ≤ i < max A} δ(Φ_A)`. -/
def oscSpan (Φ : Finset S → Config S E → ℝ) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {B : Finset S | Spans B i}.indicator (fun B ↦ osc (Φ B)) A

variable (S) in
/-- **Georgii, Section 8.3**: `S` is exhausted by intervals with at most `m` boundary sites, i.e.
every finite `Λ₀` sits inside a volume `Λ` admitting `D` with `|D| ≤ m` such that every support
meeting `Λ` and leaving `Λ` spans a site of `D`.  Georgii's cases are `S = ℤ` with `Λ = ]−n, n]`,
`D = {−n, n}` (`m = 2`) and `S = ℕ` with `Λ = [0, n]`, `D = {n}` (`m = 1`). -/
def HasBoundedBoundary (m : ℕ) : Prop :=
  ∀ Λ₀ : Finset S, ∃ Λ : Finset S, Λ₀ ⊆ Λ ∧ ∃ D : Finset S, D.card ≤ m ∧
    ∀ A : Finset S, ¬ Disjoint A Λ → ¬ A ⊆ Λ → ∃ k ∈ D, Spans A k

end Order

/-! ## Georgii (8.41): translates on `ℤ` -/

/-- **Georgii, Comments (8.41)**: the translate `A + n` of a finite set of integers. -/
def shiftFinset (n : ℤ) (A : Finset ℤ) : Finset ℤ := A.map (Equiv.addRight n).toEmbedding

@[simp] theorem mem_shiftFinset {n x : ℤ} {A : Finset ℤ} : x ∈ shiftFinset n A ↔ x - n ∈ A := by
  simp only [shiftFinset, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.coe_addRight]
  exact ⟨by rintro ⟨a, ha, rfl⟩; simpa using ha, fun h ↦ ⟨x - n, h, by ring⟩⟩

/-! ## Non-vacuity: the zero potential -/

section Zero

omit [MeasurableSpace E] in
@[simp] theorem hamiltonianTerm_zero (Λ : Finset S) (ω : Config S E) (A : Finset S) :
    hamiltonianTerm (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) Λ ω A = 0 := by
  rw [hamiltonianTerm]
  by_cases h : A ∈ {B : Finset S | ∃ i ∈ B, i ∈ Λ} <;> simp [h]

omit [MeasurableSpace E] in
@[simp] theorem hamiltonian_zero (Λ : Finset S) (ω : Config S E) :
    hamiltonian (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) Λ ω = 0 :=
  hamiltonian_eq_of_hasHamiltonian (by simp [HasHamiltonian])

theorem isPotential_zero : IsPotential (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) where
  measurable_inside _ := measurable_const
  exists_hasHamiltonian Λ ω := ⟨0, by simp [HasHamiltonian]⟩

omit [MeasurableSpace E] in
theorem isAbsolutelySummable_zero :
    IsAbsolutelySummable (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) := by
  intro i
  have h : potentialNormAt (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun A ↦ ?_
    by_cases hA : A ∈ {B : Finset S | i ∈ B} <;> simp [hA]
  simp [h]

omit [MeasurableSpace E] in
@[simp] theorem boltzmannFactor_zero (β : ℝ) (Λ : Finset S) :
    boltzmannFactor (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) β Λ = 1 := by
  funext σ; simp [boltzmannFactor]

instance isProbabilityMeasure_freeMeasure (lam : Measure E) [IsProbabilityMeasure lam]
    (Λ : Finset S) (ω : Config S E) : IsProbabilityMeasure (freeMeasure lam Λ ω) := by
  rw [freeMeasure]
  exact Measure.isProbabilityMeasure_map (measurable_extend Λ ω).aemeasurable

theorem partitionFunction_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    partitionFunction (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β Λ ω = 1 := by
  rw [partitionFunction, boltzmannFactor_zero]
  simp

theorem isAdmissible_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) :
    IsAdmissible (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β := fun Λ ω ↦ by
  rw [partitionFunction_zero]
  exact ⟨one_ne_zero, ENNReal.one_ne_top⟩

/-- The Gibbsian specification of the zero potential is the independent one. -/
theorem gibbsKernel_zero (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) (Λ : Finset S)
    (ω : Config S E) :
    gibbsKernel (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β Λ ω
      = freeMeasure lam Λ ω := by
  rw [gibbsKernel, partitionFunction_zero, boltzmannFactor_zero, withDensity_one, inv_one,
    one_smul]

/-- Non-vacuity of the hypothesis of Proposition (8.38): the independent specification is
uniformly dominated with `c = 1`. -/
theorem isUniformlyDominated_gibbsKernel_zero (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    IsUniformlyDominated (gibbsKernel (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) lam β) 1 := by
  rintro A ⟨Δ, hΔ⟩
  refine ⟨Δ, fun ζ η ↦ ?_⟩
  rw [one_mul, gibbsKernel_zero, gibbsKernel_zero]
  exact le_of_eq (freeMeasure_apply_congr lam le_rfl hΔ η ζ)

variable [Preorder S]

omit [MeasurableSpace E] in
theorem oscSpan_zero (i : S) :
    oscSpan (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun A ↦ ?_
  by_cases hA : A ∈ {B : Finset S | Spans B i} <;> simp [hA]

omit [MeasurableSpace E] in
theorem iSup_oscSpan_zero_ne_top :
    (⨆ i : S, oscSpan (fun (_ : Finset S) (_ : Config S E) ↦ (0 : ℝ)) i) ≠ ⊤ := by
  simp [oscSpan_zero]

end Zero

end OneDimChallenge

end
