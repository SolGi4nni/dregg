# The crown-lowering linchpin + the assurance ladder (with the TEE rung)

*Status: DESIGN / coordination artifact, updated to current state. The core gap it coordinated
around is closed: the standalone gadget crate exists (`constraint-lowering`) and the game terminal's
compiler lowers every ordering tooth through a range gadget. What remains named below: the two
gadget implementations are not yet ONE, and the `tee_attested` `CiAssurance` rung is unbuilt.*

## The gap (grounded) — and its closure

The executor enforces rules as `StateConstraint` teeth (kernel predicates: an unlit descent, an HP
floor, a scene ratchet — refused in-band, anti-ghost). Proving that a run obeyed those rules means
lowering each tooth to the circuit DSL `ConstraintExpr` (`circuit/src/dsl/circuit.rs:125`).
`ConstraintExpr` carries `Equality / Multiplication / Binary / PiBinding / Transition / Polynomial /
Gated / InvertedGated / Squared / ConditionalNonzero / AtLeastOne / Lookup` plus the hash family
(`Hash`, `Hash2to1/4to1/3Cap`, `MerkleHash/MerkleHash8`, chained/seeded variants) — **still no native
inequality/comparison variant**, though `Lookup` gives table-membership range checks. The state of
the lowering:
- Arithmetic / equality / boolean / transition teeth lower cleanly through single
  `Polynomial`/`Binary` emissions (`game-turn-slice/src/compiler.rs`).
- **Ordering teeth — `FieldGte`, `FieldLte`, `Monotonic`, `StrictMonotonic` — lower through a real
  bit-decomposition range gadget**, not per-rule hand-authoring: `game-turn-slice`'s `compiler`
  module (`game-turn-slice/src/lib.rs:20`) lowers every ordering tooth via boolean bit columns +
  a recomposition `Polynomial`, driven end-to-end by `game-turn-slice/tests/game_program_compiler.rs` (an honest
  leaf accepts; a forged ordering-violating witness has no satisfying leaf).

**Scope boundary (architectural law #1, enforced in CI):** Rust-authored `ConstraintExpr` emission
is NOT the sanctioned path to constraints for DEPLOYED circuits. The ratchet
`circuit-prove/tests/law1_enforcement_gate.rs` forbids new Rust-authored constraints there and
names `lean_lookup_air.rs` as the proven range gadget on the deployed side. The gadget below serves
the executor-rule → custom-leaf lowering path (game teeth, DreggCloud rungs, forge checks) — rules
proved as foldable custom leaves, not additions to deployed first-party circuits.

## The linchpin: a reusable range/comparison gadget

A standalone gadget that emits the inequality primitive over the *existing* `ConstraintExpr` ops, so
the `StateConstraint → ConstraintExpr` compiler lowers ANY ordering tooth by calling it — no
per-rule hand-authoring.

**Core: `a ≥ b` over BabyBear via bit-decomposition of the difference.**
- Let `d = a − b`. Prove `d ∈ [0, 2^k)` for a `k` that bounds the domain (game HP, scene index, budget
  — all small; `k ≈ 16–32`). If `d` is in range, `a ≥ b`; the wraparound case (`a < b` ⇒ `d = a − b + p`
  huge) fails the range check.
- **Encoding (all existing `ConstraintExpr`):** allocate `k` bit columns `b_0..b_{k-1}`; a `Binary`
  constraint per bit (`b_i·(b_i−1)=0`); one `Polynomial` reconstruction (`Σ b_i·2^i − d = 0`, `d` from
  a `Transition`/`Polynomial` over `a`,`b`). No new `ConstraintExpr` variant needed — the gadget is a
  *composition*. (`ConstraintExpr::Lookup` — preprocessed table membership — exists at HEAD as a
  succinct range-check alternative, but the game compiler's lowering deliberately uses the
  bit-decomposition form, never a refused `Lookup`; see `game-turn-slice/src/lib.rs:20`.)
- Derived: `a > b` = `a ≥ b+1`; `a ≤ b` = `b ≥ a`; `Monotonic(next ≥ local)` and `StrictMonotonic` fall
  straight out per transition.

**Built — the standalone crate `constraint-lowering`** (`constraint-lowering/src/lib.rs`): pure
`ConstraintExpr` emission, no prover, no executor deps. Its surface exceeds the design sketch:
`emit_nonneg` / `emit_ge` / `emit_ge_const` / `emit_gt` / `emit_le` / `emit_lt` / `emit_range` over
a `ColAlloc`, plus **multi-limb u64 borrow-chain variants** (`emit_ge_multilimb`,
`emit_ge_multilimb_ops`) this design never specified. Unit-tested in isolation (honest accepts,
`a<b` rejects).

**Named seam — TWO gadget implementations, not ONE.** `game-turn-slice/src/compiler.rs` lowers its
ordering teeth through its *own* bit-decomposition gadget; it does not consume `constraint-lowering`.
Both implement the same construction (Binary bit columns + recomposition `Polynomial`), but the
convergence this document coordinates toward — every consumer calling the one standalone lib — has
not happened. Unifying them (the game compiler, DreggCloud, and the forge all calling
`constraint-lowering`) is the open coordination item.

## The assurance ladder — and where the TEE rung sits

The lowering gadget delivers the **`proof_checked`** rung for kernel rules. But that rung is *slow*
(recursive STARK ≈ minutes). The honest ladder (adopt DreggCloud's discipline breadstuffs-wide, as a
first-class tag, no rung inferred from a lower one):

| rung | means | trust root | speed |
|---|---|---|---|
| `modeled` | a spec/fixture stands in | none (it's a placeholder) | — |
| `host_checked` | the host says it checked | the host | fast |
| `dregg_executed` | a real cap-gated committed turn | the executor + the host that ran it | fast |
| **`tee_attested`** | **ran in a hardware-attested enclave** | **the TEE vendor's silicon (named)** | **~native** |
| `proof_checked` | a STARK proves the run (the lowering gadget) | crypto floor (FRI/MLWE/DL) | slow (minutes) |
| `lean_proven` | a Lean theorem | Lean's kernel | build-time |

**The TEE rung (`tee_attested`) is a rung, never a root.** It slots into the expensive gap between
`dregg_executed` (trust the host) and `proof_checked` (trust only crypto): a hardware-attested enclave
(SGX/TDX/SEV/Nitro/Secure-Enclave) runs the workload and signs an attestation — *native speed*, with an
**explicitly named** assumption (trust the vendor). It is `ReExecuted{quorum}`'s hardware cousin. **Rules:**
- The security *root* — capabilities + the MLWE/DL/hash-CR crypto floor — **never** depends on a TEE. A
  compromised enclave degrades a workload from `tee_attested` to `host_checked`; it cannot forge a cap,
  a signature, or a proof. TEE ∉ the trusted base.
- It is an **optional per-workload accelerator**: choose it where a STARK is too slow (arbitrary code,
  the whole-history R3 fold, a heavy CI check) and the vendor-trust assumption is acceptable. Where you
  need trustlessness, you pay for `proof_checked`; where you need speed, you take `tee_attested` and
  *name the assumption*.
- It composes with the existing `CiAssurance` lattice as a new variant `TeeAttested{ measurement, vendor }`
  (verify the enclave measurement + the attestation signature — same shape as `Proven` but the "proof"
  is a hardware attestation over the same public inputs). **Classified: unbuilt as a `CiAssurance`
  rung** — the lattice at HEAD is `TrustedSigned / ReExecuted / OptimisticChallenge / Proven / Staked`
  (`dregg-doc/src/ci_assurance.rs:878`). The rung's *ingredients* exist elsewhere: `tee-verify`
  carries a real Nitro attestation verifier (COSE_Sign1 + X.509 chain to the pinned AWS root,
  `tee-verify/src/lib.rs`) behind `dregg_cell::tee_attest::TeeAttestationVerifier`, and oracle marks
  already carry a `MarkProvenance::TeeAttested { kind, measurement }`
  (`tee-verify/src/oracle_mark.rs:114`). Adding the `CiAssurance` variant is wiring, not research.

So: **the linchpin makes the *proven* path automatic; the TEE makes a *fast* path available; the ladder
keeps both honest.** Kernel-enforced → `{re-executed | tee-attested | proven}`, pick per workload.

## Why this is the move (maturity · feature · fun · less-LARP, at once)

- **Less-LARP:** it closes the exact `host_checked → proof_checked` gap as a *tool* instead of a
  per-rule chore — and the game-compiler path demonstrates it end-to-end.
- **Maturity:** the substrate has the missing primitive; the first-class assurance-rung type
  (`tee_attested`) is the remaining addition.
- **Feature:** every executor rule becomes provable; the TEE rung unlocks fast attestation for
  workloads STARKs can't touch.
- **Fun:** it's what unblocks the games' D-crown (a game rule reaching the crown *automatically*) and
  DreggCloud's honest agent story.

## Sequencing — where it stands

1. **This doc** — the coordination artifact (align the game terminal, DreggCloud, forge on ONE gadget).
2. ✅ **DONE — the standalone gadget**: `constraint-lowering` exists with the `emit_*` family +
   multilimb variants, unit-tested in isolation (honest accepts, `a<b` rejects).
3. **PARTIAL — the wire-in**: the game terminal's `compiler.rs` lowers ordering teeth through a
   range gadget end-to-end (`game-turn-slice/tests/game_program_compiler.rs`), but through its OWN implementation,
   not `constraint-lowering`. The remaining coordination item is convergence: game compiler,
   DreggCloud, and forge all consuming the one standalone crate.
4. **UNBUILT — the `tee_attested` rung**: add `CiAssurance::TeeAttested{measurement,vendor}`. The
   attestation verifier already exists (`tee-verify`'s Nitro verifier); the rung is the missing
   `CiAssurance` variant + its check wiring.
