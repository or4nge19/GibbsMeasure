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

The entries are `Challenge.lean`/`Solution.lean` (Georgii (6.9), the "in particular" half) and
`Challenge_X.lean`/`Solution_X.lean` for
`X ∈ {Existence, Simplex, Dobrushin, MarkovChain, LowTemperature, NoGibbs}`.

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
