# orb-compiler — taking `leanc` out of the trusted base

The Orb server ([`../orb`](../orb)) is a Lean-verified serve core compiled to machine
code by `leanc` (Lean's C backend) + a C compiler. Those compilers are **trusted** —
the proofs are about the Lean *model*, and you take `leanc`'s word that the binary
matches it.

This drop is the work to remove that trust: a **verified/validated compilation path**
that emits a serve fragment's Lean spec to [Pancake](https://cakeml.org/) (the CakeML
project's first-order systems language), and proves — in the HOL4 kernel, against the
real Pancake semantics and the CakeML backend correctness theorem — that the resulting
**machine code refines the Lean specification**. Where this reaches, `leanc` is out of
the trusted base end-to-end.

## What is proven

Each `hol-cN/` is a HOL4 development; each `CN-*-REPORT.md` is its writeup. The
progression:

- **C0–C13** — the technique, bottom-up: a bounds check, a saturating counter, a
  request-line byte scan, arena/free-list allocation, and their composition, each
  emitted to Pancake and proved to refine its Lean spec. **C13** closes the first full
  `spec → machine code` theorem (`boundScan_machine_code`, 0 axioms) with `leanc` out
  of the trusted base end-to-end.
- **C14–C16** — generalization: a second primitive (branch), then **automation** — a
  tactic + generator that closes the loop-free class (bespoke proof 629 → ~2 lines),
  a whole-program wrapper generator, and a **fold-loop schema** (the bounded
  fold-over-array invariant, ~8-line per-fold fill-in).
- **C17–C19** — reaching *real* serve code: `Redirect.Code.status` (a real deployed
  redirect decision) auto-descends; the scalar comparison-guard set is completed across
  four real serve-stage decisions (C18); and the fold schema closes a **real serve
  fold** — the cache-key hash run on every request (C19).

Every headline carries `[oracles: DISK_THM] [axioms: ]` (HOL4) / a clean axiom
footprint — no cheats, no vacuous statements.

## What is NOT done (honestly)

This does **not** yet compile the whole serve. The proven fragments are loop-free
decisions and single folds. Composing the full `deployStagesFull2` pipeline, the
remaining general loops (DEFLATE, the JWT FSM, CIDR walks), and — the deep one — a
verified data-layout / recursion / heap-allocation story for the model's algebraic
datatypes and allocating recursion, are open. Treat this as a demonstrated technique
that now reaches real loop-free serve fragments and the first real fold, with the
general case unsolved.

## Building

The HOL4 developments build with `Holmake` in each `hol-cN/` directory, against a
[HOL4](https://hol-theorem-prover.org/) + [CakeML](https://github.com/CakeML/cakeml)
tree (the `Holmakefile`s expect `CAKEMLDIR` set). This is a proof-checking build on a
dedicated box, not a one-command local build. `emit/` and `hol-emit/` hold the
Lean → Pancake emission tooling.

## Licence

AGPL-3.0, matching the Orb.
