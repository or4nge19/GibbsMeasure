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

`Solution.lean` must restate those definitions verbatim and prove the two theorems from this
development. **That bridge is the remaining work**: it requires showing that the kernels of
`isingSpecification (latticeGraph 2) 1 0 β` coincide with the challenge's explicit finite sum of
Diracs. Until it lands, `.github/workflows/comparator.yml` runs on `workflow_dispatch` only.

## Running it

`landrun` uses the Linux Landlock LSM, so the check cannot run on macOS; use the CI workflow, or a
Linux machine with `landrun` and a `lean4export` matching the toolchain on `PATH`:

```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  --working-directory $(pwd) -- bash -c 'lake env path/to/comparator Comparator/config.json'
```
