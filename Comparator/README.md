# Comparator checks for the Georgii milestone theorems

[leanprover/comparator](https://github.com/leanprover/comparator) checks that a `Solution` module
proves exactly the theorems a `Challenge` module states, that no axiom outside a permitted list is
used, and that the Lean kernel accepts the proofs — inside a `landrun` sandbox.

## Layout

| module | imports | contents |
| --- | --- | --- |
| `Defs.lean` | **`Mathlib` only** | the shared Georgii vocabulary: `Config`, `glue`, `outside`, `inside`, `tail`, `IsProper`, `IsSpecification`, `IsGibbs`, `IsLocalEvent`, `TendstoLocally`, `localTopology`, and the Dirac / independent examples that keep them non-vacuous |
| `Defs_Ising.lean` | **`Mathlib` only** | the two-dimensional Ising model from first principles: `Site`, `Config`, `spin`, `e`, `bonds`, `hamiltonian`, `glue`, `extend`, `weight`, `partitionFunction`, `gibbsMeasure`, `IsGibbs`, `shift` |
| `Defs_X.lean` | other `Defs*` modules only | the definitions specific to entry `X` (`Defs_LowTemperature` also imports `Defs_Ising`; `Defs_Sharpness` imports `Defs_Dobrushin`) |
| `Challenge_X.lean` | `Comparator.Defs_X` | **only** the theorem statements, each proved by `sorry` |
| `Solution_X.lean` | `Comparator.Defs_X` and `GibbsMeasure` | the *same* statements — byte-identical text — with a `Bridge` namespace and real proofs |
| `config_X.json` | — | the comparator entry: challenge module, solution module, theorem names, permitted axioms |

## Entries

| entry `X` | config | thms | Georgii result |
| --- | --- | ---: | --- |
| — (`Challenge.lean`/`Solution.lean`) | `config.json` | 9 | **(6.9)** at the explicit threshold `log 3`; the critical inverse temperature `β_c` with `1/4 ≤ β_c ≤ log 3`, uniqueness for `0 ≤ β < β_c` and non-uniqueness for `β_c < β`; the plus and minus phases as local limits with the sandwich `μ₋ ≼ μ ≼ μ₊`; the **Lebowitz–Martin-Löf/Ruelle** equivalence `\|𝒢(β)\| > 1 ↔ 0 < μ₊(σ₀)` |
| `OneDim` | `config_OneDim.json` | 9 | **(8.38)**, a uniqueness criterion for an arbitrary specification, and **(8.39)** at Georgii's hypotheses in both halves — any σ-finite non-zero `λ`-admissible a priori measure, no absolute summability — with the uniqueness half on any parameter set with a chain structure, `ℤ` and `ℕ` included, and the `∃!` half on `ℤ`, ending in uniqueness for pair potentials with `δ(Φ_{0,n}) ≤ c n^{-p}`, `p > 2` |
| `Simplex` | `config_Simplex.json` | 7 | (7.7)(a),(d), **(7.26)**, (7.29): extremality is tail-triviality, distinct extreme Gibbs measures are mutually singular, every Gibbs measure is the barycentre of a unique weight on `ex 𝒢(γ)`, and `\|ex 𝒢(γ)\| ≥ N` iff `𝒢(γ)` contains `N` linearly independent measures |
| `Dobrushin` | `config_Dobrushin.json` | 7 | **(8.7)** in `∃!` form, (8.20), (8.23): under Dobrushin's condition the finite-volume distributions *converge*, so uniqueness is a construction |
| `Existence` | `config_Existence.json` | 6 | (4.22), **(4.23)(a),(b),(c),(d)**: existence, compactness, relative compactness over a bounded family, and closedness of the Gibbs correspondence along a net of potentials |
| `LocalLimit` | `config_LocalLimit.json` | 5 | **(7.12)(a)** and **(7.12)(c)**: for an extreme Gibbs measure of a λ-specification over an arbitrary state space, `γ_{Λₙ}(·\|ω) → μ` in total variation on every finite volume |
| `NoGibbs` | `config_NoGibbs.json` | 5 | **(4.16)**: a specification with no Gibbs measure — quasilocality cannot be dropped from (4.17)/(4.22) |
| `Representation` | `config_Representation.json` | 5 | **(2.30)**: the Gibbs representation theorem, plus its converse (2.5), (2.8), (1.32) |
| `DeFinetti` | `config_DeFinetti.json` | 4 | **(7.17)**: the Hewitt–Savage zero-one law, and `ex 𝒫_I` = the i.i.d. product measures — the substantial half over an **arbitrary** state space. **(7.31)**: de Finetti's theorem in the version of Dynkin, a unique mixing weight on `𝒫(E, ℰ)`, with exchangeability of every mixture as the converse |
| `LowTemperature` | `config_LowTemperature.json` | 3 | **(6.9)**, first assertion: the low-temperature limit |
| `MarkovChain` | `config_MarkovChain.json` | 3 | **(3.5)**: Markov chains as Gibbs measures on `ℤ`, the unique one being the stationary chain |
| `Sharpness` | `config_Sharpness.json` | 2 | **(2.27)**: a specification with `C(γ) ≡ 0` — hence `c(γ) = 0 < 1` — and uncountably many Gibbs measures. It carries `¬ IsDobrushin γ` explicitly: it does *not* contradict (8.7), it shows (8.7)'s quasilocality hypothesis cannot be removed |

Twelve entries, 65 theorems. Every entry sets `enable_nanoda: true` and permits exactly `propext`,
`Quot.sound` and `Classical.choice`.

The workflow runs on every push to `mc3` and `main` and judges every `Comparator/config*.json`, so
adding an entry needs no workflow change. Latest recorded pass:
[run 33340000915](https://github.com/or4nge19/GibbsMeasure/actions/runs/33340000915) (2026-08-30),
`comparator accepted all 11 entries` — the eleven entries then present, at the statements then
present; `DeFinetti` and the strengthened `OneDim` statements postdate it.

## What is and is not claimed

**Nothing is claimed at `β = β_c`.** Onsager's exact value appears nowhere: it is not proved here,
and Georgii does not prove it either.

`Challenge_Representation.lean` states Georgii (2.30) and nothing more: the potential it produces
is a potential in the sense of (2.2) — its Hamiltonians exist as limits of the partial sums (2.13)
— and is **not** claimed to be absolutely summable (2.11) or uniformly convergent. Georgii's second
sentence in (2.30) obtains uniform convergence only under the additional hypothesis that `log ρ_Λ`
be bounded, and "every quasilocal specification comes from an absolutely summable potential" is the
separate Kozlov–Sullivan theorem, which §2.3 does not prove.

Comparator's threat model is a solution author who might cheat; here the same author writes both
sides, so what the sandbox and the kernel replay establish is that the statements match and the
proofs check — not that an adversary was defeated. Its assumption 2 is that the checker "has not
previously tried to compile the `Solution` file". CI pre-builds the *library* only, so just the
challenge and solution modules are compiled inside the sandbox.

## Hypotheses

The challenges state Georgii's hypotheses, not the ones that happen to be convenient. The
quasilocality premise of `Defs_Dobrushin.lean` quantifies over **local** observables, which is
the form of (2.23) Georgii gives in the remark following the definition; Definition (2.23) itself
quantifies over quasilocal observables, and Georgii notes that for a specification the two agree.
The passage from local to quasilocal observables is carried out in the solution, not assumed. The
a priori measure of `Defs_Existence.lean` is **finite and non-zero**, as (4.23) requires and (2.9)
permits, not normalised; the `λ(E)^{|Λ|}` factors cancel, which is Remark (1.28)(3) and is
proved in the challenge itself. The a priori measure of `Defs_OneDim.lean` is **σ-finite, non-zero
and `λ`-admissible**, and its potentials are summable in the sense of Convention (2.1), not
absolutely summable — Georgii's hypotheses for (8.39), in the existence half as well as the
uniqueness half. The parameter set of `Defs.lean`'s independent specification is an **arbitrary
countable** `S`, its Gibbs measure being `Measure.infinitePi`.

## Why the `Defs*` modules may never import `GibbsMeasure`

Comparator's guarantees hold under the assumption that the **transitive imports of the challenge**
are trustworthy, so the challenge may not depend on the library under test — otherwise a mistake in
this development's own definitions (`GP`, `isingSpecification`, …) would be inherited by the
"verified" statement. `Defs.lean` and `Defs_Ising.lean` therefore import `Mathlib` and nothing
else, and every other `Defs_X.lean` imports only other `Defs*` modules. **No `Defs*` module may
ever import `GibbsMeasure`.**

Challenge and solution share those definitions rather than restating them: comparator compares the
exported types of the named declarations in the two modules, and sharing makes those types
literally the same constants. The solution must **not** import the challenge, or the challenge's
sorried theorems would be in scope under the names comparator looks up.

Everything is spelled out from first principles in the `Defs*` modules: the Hamiltonian as a sum
over nearest-neighbour bonds meeting a finite volume, the finite-volume Gibbs distribution as a
normalised finite sum of Dirac measures, the DLR equations as `μ A = ∫⁻ ω, γ_Λ(A | ω) ∂μ`, the
shift as `σ ↦ σ(· − j)`, and the i.i.d. map `λ ↦ λ^ℕ` with its Giry-measurability. Each definition
can be checked against the book without trusting anything but Mathlib.

Each solution's `Bridge` namespace does the translation. For `Solution.lean`,
`Bridge.hamiltonian_P_eq` identifies the library's `Potential.hamiltonian` for the Ising potential
with the explicit bond sum, `Bridge.spec_eq` identifies the kernels
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
