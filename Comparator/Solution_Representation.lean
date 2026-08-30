import Comparator.Defs_Representation
import GibbsMeasure

/-!
# The Gibbs representation theorem

Solution file matching `Comparator/Challenge_Representation.lean`; the statements below are the
challenge's statements verbatim, and the extra `namespace Bridge` translates the from-scratch
definitions of `Comparator.Defs_Representation` into the `GibbsMeasure` library.

Georgii (2.30) is `Potential.exists_unique_isGasPotential_sigmaFinitePremodifierNorm_eq` and
`Potential.eq_of_isGasPotential_of_sigmaFinitePremodifierNorm_eq`, and (2.5) is
`Potential.isPremodifier_boltzmannFactor`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

namespace Representation

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E]

/-! ### Bridge to the `GibbsMeasure` library

Georgii's convergence convention (2.1) for `H^Φ_Λ` is the library's summation filter
`SummationFilter.volume S`, so `IsPotential` is `Potential.IsPotential` together with
`Potential.IsSummable`. -/

namespace Bridge

open ProbabilityTheory MeasureTheory.GibbsMeasure

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E]

omit [Countable S] [DecidableEq S] in
/-- The challenge's `𝓕_A` is the library's `cylinderEvents ↑A`. -/
theorem inside_eq_cylinderEvents (A : Finset S) :
    inside (E := E) A = cylinderEvents (X := fun _ : S => E) (A : Set S) := rfl

omit [Countable S] [DecidableEq S] [MeasurableSpace E] in
/-- The challenge's `ζ η_{S∖Λ}` is the library's `juxt`. -/
theorem paste_eq (Λ : Finset S) (η : Config S E) (ζ : Λ → E) :
    paste Λ η ζ = juxt (Λ : Set S) η ζ := by
  funext x
  by_cases hx : x ∈ Λ
  · rw [paste_of_mem hx η ζ,
      juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η) (x := x) (by simpa using hx) ζ]
  · rw [paste_of_notMem hx η ζ,
      juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (x := x) (by simpa using hx) ζ]

omit [Countable S] [DecidableEq S] in
/-- The challenge's `λ_Λ f` is integration against `Specification.sigmaFiniteLambdaFun ν Λ`. -/
theorem lambdaInt_eq (ν : Measure E) [SigmaFinite ν] {f : Config S E → ℝ≥0∞} (hf : Measurable f)
    (Λ : Finset S) (η : Config S E) :
    lambdaInt ν Λ f η
      = ∫⁻ x, f x ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hf (Measurable.juxt (Λ := (Λ : Set S)) (η := η))]
  exact lintegral_congr fun ζ => by rw [paste_eq]

omit [Countable S] in
/-- The partial Hamiltonians of Georgii (2.13) are the partial sums of the library's
`Potential.hamiltonianTerms` over the powerset of `Δ`. -/
theorem sum_powerset_hamiltonianTerms (Φ : Potential S E) (Λ Δ : Finset S) (η : Config S E) :
    ∑ A ∈ Δ.powerset, _root_.Potential.hamiltonianTerms Φ Λ η A = partialHamiltonian Φ Λ Δ η := by
  rw [partialHamiltonian, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  split_ifs with h
  · exact _root_.Potential.hamiltonianTerms_of_not_disjoint
      (Finset.not_disjoint_iff_nonempty_inter.2 h) η
  · exact _root_.Potential.hamiltonianTerms_of_disjoint
      (Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 h)) η

omit [Countable S] in
/-- Georgii's summation convention (2.1) for the energy `H^Φ_Λ` is summation along the library's
`SummationFilter.volume S`. -/
theorem hasSum_iff (Φ : Potential S E) (Λ : Finset S) (η : Config S E) (H : ℝ) :
    HasSum (_root_.Potential.hamiltonianTerms Φ Λ η) H (SummationFilter.volume S)
      ↔ HasHamiltonian Φ Λ η H := by
  show Tendsto (fun s : Finset (Finset S) =>
      ∑ A ∈ s, _root_.Potential.hamiltonianTerms Φ Λ η A)
    (SummationFilter.volume S).filter (nhds H) ↔ _
  rw [SummationFilter.volume_filter, tendsto_map'_iff]
  simp only [Function.comp_def, sum_powerset_hamiltonianTerms]
  rfl

omit [Countable S] in
/-- A challenge potential is a library potential which is summable in Georgii's sense. -/
theorem toLibrary {Φ : Potential S E} (h : IsPotential Φ) :
    _root_.Potential.IsPotential Φ ∧ _root_.Potential.IsSummable Φ :=
  ⟨⟨fun A => h.measurable A⟩,
    ⟨fun Λ η => (h.exists_hamiltonian Λ η).imp fun H hH => (hasSum_iff Φ Λ η H).2 hH⟩⟩

omit [Countable S] in
/-- …and conversely. -/
theorem ofLibrary {Φ : Potential S E} [_root_.Potential.IsPotential Φ]
    [_root_.Potential.IsSummable Φ] : IsPotential Φ where
  measurable A := _root_.Potential.IsPotential.measurable (Φ := Φ) A
  exists_hamiltonian Λ η :=
    ⟨_root_.Potential.hamiltonian Φ Λ η,
      (hasSum_iff Φ Λ η _).1 (_root_.Potential.hasSum_hamiltonian Λ η)⟩

omit [Countable S] in
/-- The challenge's Hamiltonian is the library's. -/
theorem hamiltonian_eq {Φ : Potential S E} [_root_.Potential.IsSummable Φ] (Λ : Finset S)
    (η : Config S E) : hamiltonian Φ Λ η = _root_.Potential.hamiltonian Φ Λ η :=
  HasHamiltonian.hamiltonian_eq ((hasSum_iff Φ Λ η _).1 (_root_.Potential.hasSum_hamiltonian Λ η))

omit [Countable S] in
/-- The challenge's Boltzmann factor is the library's, at inverse temperature `β = 1`. -/
theorem boltzmann_eq {Φ : Potential S E} [_root_.Potential.IsSummable Φ] (Λ : Finset S)
    (η : Config S E) : boltzmann Φ Λ η = _root_.Potential.boltzmannFactor Φ 1 Λ η := by
  have h1 : boltzmann Φ Λ η = ENNReal.ofReal (Real.exp (-hamiltonian Φ Λ η)) := rfl
  have h2 : _root_.Potential.boltzmannFactor Φ 1 Λ η
      = ENNReal.ofReal (Real.exp (-1 * _root_.Potential.hamiltonian Φ Λ η)) := rfl
  rw [h1, h2, neg_one_mul, hamiltonian_eq]

omit [Countable S] in
theorem boltzmann_eq' {Φ : Potential S E} [_root_.Potential.IsSummable Φ] (Λ : Finset S) :
    boltzmann Φ Λ = _root_.Potential.boltzmannFactor Φ 1 Λ :=
  funext fun η => boltzmann_eq Λ η

/-- The challenge's partition function is the library's `sigmaFiniteLambdaZ`. -/
theorem partitionFunction_eq (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    [_root_.Potential.IsPotential Φ] [_root_.Potential.IsSummable Φ] (Λ : Finset S)
    (η : Config S E) :
    partitionFunction ν Φ Λ η
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
          (_root_.Potential.boltzmannFactor Φ 1) Λ η := by
  rw [partitionFunction, boltzmann_eq' (Φ := Φ) Λ, Specification.sigmaFiniteLambdaZ]
  exact lambdaInt_eq ν (_root_.Potential.measurable_boltzmannFactor (Φ := Φ) 1 Λ) Λ η

/-- The challenge's `ρ^Φ` is the library's normalized premodifier. -/
theorem gibbsModification_eq (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    [_root_.Potential.IsPotential Φ] [_root_.Potential.IsSummable Φ] (Λ : Finset S)
    (η : Config S E) :
    gibbsModification ν Φ Λ η
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (_root_.Potential.boltzmannFactor Φ 1) Λ η := by
  rw [gibbsModification, Specification.sigmaFinitePremodifierNorm, boltzmann_eq,
    partitionFunction_eq]

/-- `λ`-admissibility, both ways. -/
theorem isAdmissible_iff (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    [_root_.Potential.IsPotential Φ] [_root_.Potential.IsSummable Φ] :
    IsAdmissible ν Φ ↔ Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (_root_.Potential.boltzmannFactor Φ 1) := by
  simp only [IsAdmissible, Specification.IsSigmaFiniteLambdaAdmissible,
    partitionFunction_eq ν (Φ := Φ)]

omit [Countable S] [DecidableEq S] in
/-- Pre-modifications, both ways. -/
theorem isPreModification_iff (ρ : Finset S → Config S E → ℝ≥0∞) :
    IsPreModification ρ ↔ Specification.IsPremodifier ρ :=
  ⟨fun h => ⟨h.measurable, fun _ _ _ _ hΛ hr => h.mul_comm_of_subset hΛ hr⟩,
    fun h => ⟨h.measurable, fun _ _ hΛ _ _ hr => h.comm_of_subset hΛ hr⟩⟩

omit [Countable S] [DecidableEq S] in
/-- Gas potentials, both ways. -/
theorem isGasPotential_iff (a : E) (Φ : Potential S E) :
    IsGasPotential a Φ ↔ _root_.Potential.IsGasPotential a Φ := Iff.rfl

omit [Countable S] [DecidableEq S] [MeasurableSpace E] in
/-- Quasilocality, both ways: Georgii (2.22) in net form and in `ε`-form. -/
theorem isQuasilocalFun_iff' {f : Config S E → ℝ} :
    IsQuasilocalFun f ↔ MeasureTheory.GibbsMeasure.IsQuasilocalFun f :=
  isQuasilocalFun_iff f

end Bridge

/-! ### The statements -/

/-- **Georgii (2.30)**, the Gibbs representation theorem: a positive quasilocal pre-modification
`ρ` with `λ_Λ ρ_Λ = 1` is, for each vacuum state `a ∈ E`, the `λ`-modification of a unique
`λ`-admissible gas potential `Φ^a` with vacuum state `a`.

Uniqueness is asserted on Georgii's index set `𝒮 = {A : 0 < |A| < ∞}`, the value at `A = ∅`
entering no Hamiltonian.  `Φ^a` is claimed to be a potential in the sense of (2.2) and nothing
more: not absolutely summable (2.11), not even uniformly convergent — Georgii gets a uniformly
convergent representative only when `log ρ_Λ` is bounded, and absolute summability is the separate
Kozlov–Sullivan theorem, not proved in §2.3. -/
theorem existsUnique_gasPotential (ν : Measure E) [SigmaFinite ν]
    (ρ : Finset S → Config S E → ℝ≥0∞) (hρ : IsPreModification ρ) (hpos : IsPositive ρ)
    (hql : ∀ Λ : Finset S, IsQuasilocalFun fun η => (ρ Λ η).toReal)
    (hnorm : ∀ (Λ : Finset S) (η : Config S E), lambdaInt ν Λ (ρ Λ) η = 1) (a : E) :
    ∃ Φ : Potential S E, IsPotential Φ ∧ IsGasPotential a Φ ∧ IsAdmissible ν Φ ∧
      (∀ (Λ : Finset S) (η : Config S E), gibbsModification ν Φ Λ η = ρ Λ η) ∧
      ∀ Ψ : Potential S E, IsPotential Ψ → IsGasPotential a Ψ → IsAdmissible ν Ψ →
        (∀ (Λ : Finset S) (η : Config S E), gibbsModification ν Ψ Λ η = ρ Λ η) →
        ∀ A : Finset S, A.Nonempty → ∀ η : Config S E, Ψ A η = Φ A η := by
  have hρ' : Specification.IsPremodifier ρ := (Bridge.isPreModification_iff ρ).1 hρ
  have hql' : ∀ Λ : Finset S,
      MeasureTheory.GibbsMeasure.IsQuasilocalFun fun η : S → E => (ρ Λ η).toReal :=
    fun Λ => Bridge.isQuasilocalFun_iff'.1 (hql Λ)
  have hnorm' : ∀ (Λ : Finset S) (η : S → E),
      Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η = 1 := by
    intro Λ η
    rw [Specification.sigmaFiniteLambdaZ, ← Bridge.lambdaInt_eq ν (hρ'.measurable Λ) Λ η]
    exact hnorm Λ η
  obtain ⟨Φ, hΦP, hΦS, hΦgas, hΦadm, hΦρ, huniq⟩ :=
    _root_.Potential.exists_unique_isGasPotential_sigmaFinitePremodifierNorm_eq
      (S := S) (E := E) (ρ := ρ) ν hρ' (fun Λ η => (hpos Λ η).1) (fun Λ η => (hpos Λ η).2)
      hql' hnorm' a
  have := hΦP
  have := hΦS
  refine ⟨Φ, Bridge.ofLibrary, hΦgas, (Bridge.isAdmissible_iff ν).2 hΦadm, ?_, ?_⟩
  · intro Λ η
    exact (Bridge.gibbsModification_eq ν Λ η).trans (congrFun (congrFun hΦρ Λ) η)
  · intro Ψ hΨ hΨgas hΨadm hΨρ A hA η
    have := (Bridge.toLibrary hΨ).1
    have := (Bridge.toLibrary hΨ).2
    have hΨρ' : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (_root_.Potential.boltzmannFactor Ψ 1) = ρ :=
      funext fun Λ => funext fun ξ =>
        (Bridge.gibbsModification_eq (Φ := Ψ) ν Λ ξ).symm.trans (hΨρ Λ ξ)
    exact congrFun (huniq Ψ inferInstance inferInstance hΨgas
      ((Bridge.isAdmissible_iff ν).1 hΨadm) hΨρ' A hA) η

/-- **Georgii (2.30)**, the uniqueness half (his step 5): two `λ`-admissible gas potentials with the
same vacuum state defining the same `λ`-modification agree on every non-empty support. -/
theorem eq_of_isGasPotential (ν : Measure E) [SigmaFinite ν] {a : E} {Φ Ψ : Potential S E}
    (hΦ : IsPotential Φ) (hΨ : IsPotential Ψ)
    (hΦgas : IsGasPotential a Φ) (hΨgas : IsGasPotential a Ψ)
    (hΦadm : IsAdmissible ν Φ) (hΨadm : IsAdmissible ν Ψ)
    (heq : ∀ (Λ : Finset S) (η : Config S E),
      gibbsModification ν Φ Λ η = gibbsModification ν Ψ Λ η)
    {A : Finset S} (hA : A.Nonempty) (η : Config S E) : Φ A η = Ψ A η := by
  have := (Bridge.toLibrary hΦ).1
  have := (Bridge.toLibrary hΦ).2
  have := (Bridge.toLibrary hΨ).1
  have := (Bridge.toLibrary hΨ).2
  refine _root_.Potential.eq_of_isGasPotential_of_sigmaFinitePremodifierNorm_eq
    (S := S) (E := E) ν hΦgas hΨgas ((Bridge.isAdmissible_iff ν).1 hΦadm)
    ((Bridge.isAdmissible_iff ν).1 hΨadm) ?_ hA η
  exact funext fun Λ => funext fun ξ =>
    ((Bridge.gibbsModification_eq (Φ := Φ) ν Λ ξ).symm.trans (heq Λ ξ)).trans
      (Bridge.gibbsModification_eq (Φ := Ψ) ν Λ ξ)

/-- **Georgii (2.5)**: the Boltzmann factors `h^Φ_Λ = exp(-H^Φ_Λ)` of a potential form a positive
pre-modification. -/
theorem isPreModification_boltzmann {Φ : Potential S E} (hΦ : IsPotential Φ) :
    IsPreModification (boltzmann Φ) ∧ IsPositive (boltzmann Φ) := by
  have := (Bridge.toLibrary hΦ).1
  have := (Bridge.toLibrary hΦ).2
  have hb : ∀ (Λ : Finset S) (η : Config S E),
      boltzmann Φ Λ η = _root_.Potential.boltzmannFactor Φ 1 Λ η :=
    fun Λ η => Bridge.boltzmann_eq Λ η
  have hlib : Specification.IsPremodifier (_root_.Potential.boltzmannFactor Φ 1) :=
    _root_.Potential.isPremodifier_boltzmannFactor 1
  refine ⟨⟨fun Λ => ?_, fun Λ Δ hΛ ζ η hr => ?_⟩, fun Λ η => ?_⟩
  · have h : boltzmann Φ Λ = _root_.Potential.boltzmannFactor Φ 1 Λ := funext (hb Λ)
    rw [h]
    exact hlib.measurable Λ
  · rw [hb, hb, hb, hb]
    exact hlib.comm_of_subset hΛ hr
  · rw [hb]
    exact ⟨(_root_.Potential.boltzmannFactor_pos (Φ := Φ) 1 Λ η).ne',
      _root_.Potential.boltzmannFactor_ne_top (Φ := Φ) 1 Λ η⟩

/-- **Georgii (2.8), (1.32)**: the `λ`-modification `ρ^Φ` of a `λ`-admissible potential is
normalized, `λ_Λ ρ^Φ_Λ = 1` for every finite volume `Λ`. -/
theorem lambdaInt_gibbsModification_eq_one (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) (Λ : Finset S) (η : Config S E) :
    lambdaInt ν Λ (gibbsModification ν Φ Λ) η = 1 := by
  have := (Bridge.toLibrary hΦ).1
  have := (Bridge.toLibrary hΦ).2
  have hb : Specification.IsPremodifier (_root_.Potential.boltzmannFactor Φ 1) :=
    _root_.Potential.isPremodifier_boltzmannFactor 1
  have hmod : gibbsModification ν Φ Λ
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (_root_.Potential.boltzmannFactor Φ 1) Λ :=
    funext fun ξ => Bridge.gibbsModification_eq ν Λ ξ
  rw [hmod, Bridge.lambdaInt_eq ν
    (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E) ν hb Λ) Λ η]
  exact Specification.lintegral_sigmaFinitePremodifierNorm_eq_one (S := S) (E := E) ν hb
    ((Bridge.isAdmissible_iff ν).1 hadm) Λ η

/-- **Georgii (2.5) and (1.32)**, the converse direction of (2.30): the `λ`-modification
`ρ^Φ = h^Φ / Z^Φ` of a `λ`-admissible potential is itself a positive pre-modification. -/
theorem isPreModification_gibbsModification (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) :
    IsPreModification (gibbsModification ν Φ) ∧ IsPositive (gibbsModification ν Φ) := by
  have := (Bridge.toLibrary hΦ).1
  have := (Bridge.toLibrary hΦ).2
  have hb := isPreModification_boltzmann (Φ := Φ) hΦ
  have hZ : ∀ (Δ : Finset S) (ζ ξ : Config S E), (∀ i ∉ Δ, ζ i = ξ i) →
      partitionFunction ν Φ Δ ζ = partitionFunction ν Φ Δ ξ := by
    intro Δ ζ ξ hr
    rw [Bridge.partitionFunction_eq ν Δ ζ, Bridge.partitionFunction_eq ν Δ ξ]
    exact Specification.sigmaFiniteLambdaZ_congr_of_eqOn_compl ν
      (_root_.Potential.measurable_boltzmannFactor (Φ := Φ) 1 Δ) hr
  refine ⟨⟨fun Λ => ?_, fun Λ Δ hΛ ζ η hr => ?_⟩, fun Λ η => ?_⟩
  · have h : gibbsModification ν Φ Λ
        = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (_root_.Potential.boltzmannFactor Φ 1) Λ :=
      funext fun ξ => Bridge.gibbsModification_eq ν Λ ξ
    rw [h]
    exact Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E) ν
      (_root_.Potential.isPremodifier_boltzmannFactor 1) Λ
  · have hZΛ : partitionFunction ν Φ Λ ζ = partitionFunction ν Φ Λ η := hZ Λ ζ η hr
    have hZΔ : partitionFunction ν Φ Δ ζ = partitionFunction ν Φ Δ η :=
      hZ Δ ζ η fun i hi => hr i fun hiΛ => hi (hΛ hiΛ)
    have key : boltzmann Φ Δ ζ * boltzmann Φ Λ η = boltzmann Φ Λ ζ * boltzmann Φ Δ η :=
      hb.1.mul_comm_of_subset hΛ hr
    show boltzmann Φ Δ ζ / partitionFunction ν Φ Δ ζ
          * (boltzmann Φ Λ η / partitionFunction ν Φ Λ η)
        = boltzmann Φ Λ ζ / partitionFunction ν Φ Λ ζ
          * (boltzmann Φ Δ η / partitionFunction ν Φ Δ η)
    rw [hZΛ, hZΔ]
    calc boltzmann Φ Δ ζ / partitionFunction ν Φ Δ η
            * (boltzmann Φ Λ η / partitionFunction ν Φ Λ η)
        = boltzmann Φ Δ ζ * boltzmann Φ Λ η
            * ((partitionFunction ν Φ Δ η)⁻¹ * (partitionFunction ν Φ Λ η)⁻¹) := by
          simp only [div_eq_mul_inv]; ring
      _ = boltzmann Φ Λ ζ * boltzmann Φ Δ η
            * ((partitionFunction ν Φ Λ η)⁻¹ * (partitionFunction ν Φ Δ η)⁻¹) := by
          rw [key]; ring
      _ = boltzmann Φ Λ ζ / partitionFunction ν Φ Λ η
            * (boltzmann Φ Δ η / partitionFunction ν Φ Δ η) := by
          simp only [div_eq_mul_inv]; ring
  · have hbpos := hb.2 Λ η
    have hZpos := hadm Λ η
    refine ⟨?_, ?_⟩
    · simp [gibbsModification, ENNReal.div_eq_zero_iff, hbpos.1, hZpos.2]
    · simp [gibbsModification, ENNReal.div_eq_top, hbpos.1, hbpos.2, hZpos.1, hZpos.2]

end Representation

end GibbsChallenge

end
