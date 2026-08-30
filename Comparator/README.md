# Comparator check for the milestone theorem

[leanprover/comparator](https://github.com/leanprover/comparator) is a trustworthy judge for Lean
proofs: it verifies that a `Solution` proves exactly the theorems stated in a `Challenge`, using no
axioms beyond a permitted list, and that the result is accepted by the Lean kernel — inside a
`landrun` sandbox.

`Challenge.lean` imports **only Mathlib**. That is essential: comparator's guarantees hold under
the assumption that the transitive imports of the challenge are trustworthy, so the challenge may
not import the library under test — otherwise a mistake in this development's own definitions
(`GP`, `isingSpecification`, …) would be inherited by the "verified" statement. The challenge
therefore spells the two-dimensional Ising model out from first principles: the Hamiltonian as a
sum over nearest-neighbour bonds meeting a finite volume, the finite-volume Gibbs distribution as
a normalised finite sum of Dirac measures, the DLR equations as
`μ A = ∫⁻ ω, γ_Λ(A | ω) ∂μ`, and the shift as `σ ↦ σ(· − j)`.

`Solution.lean` restates those definitions verbatim (the definition block is byte-identical to the
challenge's) and proves both theorems from this development. The bridge is in its `Bridge`
namespace: `Bridge.hamiltonian_P_eq` identifies the library's `Potential.hamiltonian` for the Ising
potential with the challenge's explicit bond sum, `Bridge.spec_eq` then identifies the kernels
`isingSpecification (latticeGraph 2) 1 0 β Λ ω = gibbsMeasure β Λ ω` (the `2^{-|Λ|}` from the
a-priori measure cancelling against the partition function), and `Bridge.dlr_iff` converts the
challenge's integral form of the DLR equations into membership in `GP`.

## Running it

`landrun` uses the Linux Landlock LSM, so the check cannot run on macOS; use the CI workflow, or a
Linux machine with `landrun` and a `lean4export` matching the toolchain on `PATH`:

```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- bash -c 'lake env path/to/comparator Comparator/config.json'
```
