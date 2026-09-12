# Agent contract

Portable standing policy for libraries you own or steer (AxiomaticX, matteo-ax,
or4nge19, and siblings). Copy this file as `AGENTS.md`. Keep repo-specific
invariants in `CLAUDE.md`; do not repeat this file there. Do not paste this
file into the turn.

On a **host** repo (mathlib, Physlib, lattice-system, LeanOA, …) the host's
`AGENTS.md` / `CLAUDE.md` / `CONTRIBUTING` wins on naming, files, PRs, and
`sorry`. This contract still sets the loss: contribute the object the host
would keep. Do not import a private wrapper stack. Do not add this file to a
host index: use `~/.claude/CLAUDE.md`, `~/.cursor/rules/`, and
`.git/info/exclude` so it cannot enter a public PR.

## Loss

The bitter lesson: general methods that scale beat local repair. Optimize
**irreplaceability** of the library, not the file in front of you. Repo
invariants specify the goal; they are not a playbook of special cases.

**Loss.** Maximal *real* value, hidden and manifest.
- **Manifest:** theorems and APIs a Challenge file, customer, or downstream
  library can name.
- **Hidden:** host-native substrate (Mathlib, Physlib, LatticeSystem, …) that
  other libraries in the ecosystem reuse.

Replaceable: wrappers, surrogates, one characterization among many.
Irreplaceable: the native Bourbaki / mathlib / host-library object, at the
right generality, with a thick API and nothing extra.

**Radius.** A paper or book on a subdomain is the *occasion*, not the ontology.
Value is how much of the ambient domain (nearby papers and books: same objects,
same host hypotheses, adjacent chapters) typechecks as theorems or corollaries
of the library, without new carriers. Do not invent a numerical literature
distance; the test is whether a second paper is a corollary.

**Driver.** Inverse: the genuine general gap in the *host* ontology first.
Special cases are corollaries. Forward-looking: the form the host library
should have, not the workaround that compiles today.

**Nothing less, nothing more.** Honest/partial is not the object. Recording a
gap is not filling it. No wrappers, parallel theories, extra carriers, or
abstraction theatre. Definitions carry data, not proof obligations. Prefer a
theorem that discharges an obligation over a definition that stores one.
Fewer definitions, more theorems: that is the radius.

**Compression.** Fully compress docs and code so another agent or human can
**losslessly decompress**: recover the unique intended meaning from names,
types, and the deepest why, with the host ontology, and nothing hidden in chat
or local notes. Truncation, cryptic slag, and restating the type are lossy.
A kernel-checked file is not a proof if it cannot be read back.

## Turn prompts

Name a mode and a target.

1. **Gap** — Prove the missing general theorem at host-library generality.
   Specialize only as a corollary. Nothing less, nothing more.
2. **Review** — Adversarial host-standard review of this diff. Score
   irreplaceability, radius, native ontology, lossless compression, hidden and
   manifest value. Implement gaps; do not only document them.
3. **Collapse** — Refactor to the unique native object. Same or more power,
   strictly less API, losslessly readable.
4. **Why** — Compress to lossless: another reader recovers the meaning.
5. **Continue** — Continue the current goal. Smallest verification target.
   Preserve user changes.

Optional one-shot addenda only: an attachment, a named declaration, a pin/PR
to check. Search the host tree, open PRs, and the host tracker before adding
API (`octo` / `ax-assistant search-lean` for Lean).

## Own libraries vs hosts

- **Own** (AxiomaticX, matteo-ax, or4nge19 originals): this file plus `CLAUDE.md`
  for invariants only.
- **Host / fork** (mathlib, Physlib/HepLean, lattice-system, LeanOA, PNT, …):
  host policy wins. Contribute the object the host would keep. Leave this file
  untracked.

Paper or book hypotheses stay hypotheses. Missing host-library lemmas are not
paper hypotheses.
