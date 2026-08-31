# Comparator checks for the Georgii milestone theorems

[leanprover/comparator](https://github.com/leanprover/comparator) is a trustworthy judge for Lean
proofs: it verifies that a `Solution` proves exactly the theorems stated in a `Challenge`, using no
axioms beyond a permitted list, and that the result is accepted by the Lean kernel — inside a
`landrun` sandbox.

## Layout

| module | imports | contents |
| --- | --- | --- |
| `Defs.lean` | **`Mathlib` only** | the shared Georgii vocabulary: `Config`, `glue`, `outside`, `inside`, `tail`, `IsProper`, `IsSpecification`, `IsGibbs`, `IsLocalEvent`, `TendstoLocally`, `localTopology`, and the Dirac / independent examples that keep them non-vacuous |
| `Defs_Ising.lean` | **`Mathlib` only** | the two-dimensional Ising model from first principles: `Site`, `Config`, `spin`, `e`, `bonds`, `hamiltonian`, `glue`, `extend`, `weight`, `partitionFunction`, `gibbsMeasure`, `IsGibbs`, `shift` |
| `Defs_X.lean` | `Comparator.Defs` (+ `Comparator.Defs_Ising` for `Defs_LowTemperature`) | the definitions specific to entry `X` |
| `Challenge_X.lean` | `Comparator.Defs_X` | **only** the theorem statements, each proved by `sorry` |
| `Solution_X.lean` | `Comparator.Defs_X` and `GibbsMeasure` | the *same* statements — byte-identical text — with a `Bridge` namespace and real proofs |
| `config_X.json` | — | the comparator entry: challenge module, solution module, theorem names, permitted axioms |

## Entries

| entry `X` | config | thms | Georgii result |
| --- | --- | ---: | --- |
| — (`Challenge.lean`/`Solution.lean`) | `config.json` | 9 | **(6.9)** at the explicit threshold `log 3`; the critical inverse temperature `β_c` with `1/4 ≤ β_c ≤ log 3`, uniqueness for `0 ≤ β < β_c` and non-uniqueness for `β_c < β`; the plus and minus phases as genuine local limits with the sandwich `μ₋ ≼ μ ≼ μ₊`; and the **Lebowitz–Martin-Löf/Ruelle** equivalence `|𝒢(β)| > 1 ↔ 0 < μ₊(σ₀)` |
| `OneDim` | `config_OneDim.json` | 9 | **(8.38)**, a uniqueness criterion for an arbitrary specification, and **(8.39)** on `ℤ` and `ℕ`, ending in uniqueness for pair potentials with `δ(Φ_{0,n}) ≤ c n^{-p}`, `p > 2` |
| `Simplex` | `config_Simplex.json` | 7 | (7.7)(a), **(7.26)**, and (7.29): distinct extreme Gibbs measures are mutually singular, and `|ex 𝒢(γ)| ≥ n` is detected by an `n`-fold splitting of the tail |
| `Dobrushin` | `config_Dobrushin.json` | 7 | **(8.7)** in `∃!` form, (8.20), (8.23): under Dobrushin's condition the finite-volume distributions *converge*, so uniqueness is a construction |
| `Existence` | `config_Existence.json` | 6 | (4.22), **(4.23)(a),(c),(d)**: existence, compactness, and closedness of the Gibbs correspondence along a net of potentials |
| `LocalLimit` | `config_LocalLimit.json` | 5 | **(7.12)(a)** and **(7.12)(c)**: for an extreme Gibbs measure of a λ-specification over an arbitrary state space, `γ_{Λₙ}(·\|ω) → μ` in total variation on every finite volume |
| `NoGibbs` | `config_NoGibbs.json` | 5 | **(4.16)**: a specification with no Gibbs measure — quasilocality cannot be dropped from (4.17)/(4.22) |
| `Representation` | `config_Representation.json` | 5 | **(2.30)**: the Gibbs representation theorem, plus its converse (2.5), (2.8), (1.32) |
| `LowTemperature` | `config_LowTemperature.json` | 3 | **(6.9)**, first assertion: the low-temperature limit |
| `MarkovChain` | `config_MarkovChain.json` | 3 | **(3.5)**: Markov chains as Gibbs measures on `ℤ`, the unique one being the stationary chain |
| `Sharpness` | `config_Sharpness.json` | 2 | **(2.27)**: a specification with `C(γ) ≡ 0` — hence `c(γ) = 0 < 1` — and uncountably many Gibbs measures. It carries `¬ IsDobrushin γ` explicitly: it does *not* contradict (8.7), it shows (8.7)'s quasilocality hypothesis cannot be removed |

Eleven entries, 61 theorems.

> [!NOTE]
> Judged by comparator on 2026-08-30:
> [run 33340000915](https://github.com/or4nge19/GibbsMeasure/actions/runs/33340000915), 26 minutes,
> concluding `comparator accepted all 11 entries`. Eleven `systemd-run --user` units with
> `RestrictAddressFamilies=~AF_UNIX`, one per entry; eleven `nanoda kernel accepts the solution`;
> eleven `Lean default kernel accepts the solution`. So all 61 theorems were checked by two
> independent kernels inside the sandbox comparator's README prescribes.
>
> Before that date the workflow had never executed a step — every run died in seconds with
> `The job was not started because your account is locked due to a billing issue`. Anything
> written about this suite before 2026-08-30 rested on a re-implementation of comparator's checks
> by this project on itself, which is the self-report comparator exists to replace.

For each entry comparator builds the challenge from its Mathlib-only `Defs`, exports the named
theorems together with `propext`, `Quot.sound` and `Classical.choice` and nothing else, builds the
solution separately, and confirms the exported types match and both kernels accept.

A third party reproducing this must start from a clean checkout. comparator's assumption 2 is that
the checker "has not previously tried to compile the `Solution` file", since doing so could
compromise the `Challenge`. Our CI pre-builds the *library* deliberately, so that only the
challenge and solution modules are compiled inside the sandbox — that is the intended
arrangement, but it is sound only because we control both sides.

Two conventions are worth stating because they are what keeps the suite honest. **Nothing is
claimed at `β = β_c`**, and Onsager's exact value appears nowhere: it is not proved here, and
Georgii does not prove it either. And the second half of (8.39) (`|𝒢(Φ)| = 1` rather than `≤ 1`)
is stated at the hypotheses the library actually has — an absolutely summable potential over a
probability a priori measure — not at Georgii's, because the existence half rests on (4.23)(a),
which is available only there.

`Challenge_Representation.lean` states exactly Georgii (2.30) and nothing more: the potential it
produces is a potential in the sense of (2.2) — its Hamiltonians exist as limits of the partial
sums (2.13) — and is **not** claimed to be absolutely summable (2.11) or uniformly convergent.
Georgii's second sentence in (2.30) obtains uniform convergence only under the additional
hypothesis that `log ρ_Λ` be bounded, and "every quasilocal specification comes from an absolutely
summable potential" is the separate Kozlov–Sullivan theorem, which §2.3 does not prove.

## Hypotheses

The challenges state Georgii's hypotheses, not the ones that happen to be convenient.  The
quasilocality premise of `Defs_Dobrushin.lean` quantifies over **local** observables, which is
Georgii's own formulation of (2.23) and the weaker demand on `γ` — the passage to quasilocal
observables is a genuine analytic step, and the solution invokes it from the library rather than
assuming it.  The a priori measure of `Defs_Existence.lean` is **finite and non-zero**, as in (2.9)
and (4.23), not normalised; the `λ(E)^{|Λ|}` factors cancel, which is Remark (1.28)(3) and is
proved in the challenge itself.  The parameter set of `Defs.lean`'s independent specification is an
**arbitrary countable** `S`, its Gibbs measure being `Measure.infinitePi`.

## Why the `Defs*` modules may never import `GibbsMeasure`

Comparator's guarantees hold under the assumption that the **transitive imports of the challenge**
are trustworthy, so the challenge may not depend on the library under test — otherwise a mistake in
this development's own definitions (`GP`, `isingSpecification`, …) would be inherited by the
"verified" statement.  `Defs.lean` and `Defs_Ising.lean` therefore import `Mathlib` and nothing
else, and every other `Defs_X.lean` imports only those.  **No `Defs*` module may ever import
`GibbsMeasure`.**

Sharing the definitions between a challenge and its solution — rather than restating them verbatim
in both files — makes the comparison *stronger*, not weaker: comparator compares the exported types
of the named declarations in the two modules, and those types are now literally built from the same
constants.  For the same reason the solution must **not** import the challenge: the challenge's
sorried theorems would then be in scope under exactly the names comparator looks up.

Everything is spelled out from first principles in the `Defs*` modules: the Hamiltonian as a sum
over nearest-neighbour bonds meeting a finite volume, the finite-volume Gibbs distribution as a
normalised finite sum of Dirac measures, the DLR equations as `μ A = ∫⁻ ω, γ_Λ(A | ω) ∂μ`, and the
shift as `σ ↦ σ(· − j)`.  A skeptical reader can check each definition by eye against the book
without trusting anything but Mathlib.

Each solution's `Bridge` namespace does the translation.  For `Solution.lean`, for instance,
`Bridge.hamiltonian_P_eq` identifies the library's `Potential.hamiltonian` for the Ising potential
with the explicit bond sum, `Bridge.spec_eq` then identifies the kernels
`isingSpecification (latticeGraph 2) 1 0 β Λ ω = gibbsMeasure β Λ ω` (the `2^{-|Λ|}` from the
a-priori measure cancelling against the partition function), and `Bridge.dlr_iff` converts the
integral form of the DLR equations into membership in `GP`.

## Running it

`landrun` uses the Linux Landlock LSM, so the check cannot run on macOS; use the CI workflow, or a
Linux machine with `landrun` and a `lean4export` matching the toolchain on `PATH`:

```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- bash -c 'lake env path/to/comparator Comparator/config.json'
```
