# The crown-lowering linchpin + the assurance ladder (with the TEE rung)

*Status: DESIGN / coordination artifact (2026-07-11). The single highest-leverage "less-LARPing" move
on the board — it turns "a kernel-enforced rule reaches `proof_checked` only by hand-authoring a
circuit" into "any executor rule lifts to the crown automatically." Named here so the game-engine,
DreggCloud, and forge efforts converge on ONE gadget instead of hand-cranking around the same gap.*

## The gap (grounded)

The executor enforces rules as `StateConstraint` teeth (kernel predicates: an unlit descent, an HP
floor, a scene ratchet — refused in-band, anti-ghost). Proving that a run obeyed those rules means
lowering each tooth to the circuit DSL `ConstraintExpr` (`circuit/src/dsl/circuit.rs:125`). But
`ConstraintExpr` today is `Equality / Multiplication / Binary / PiBinding / Transition / Polynomial /
Gated` — **there is no inequality/comparison primitive.** So:
- Arithmetic / equality / boolean / transition teeth lower cleanly (the game terminal's teeth-probe
  confirms — `game-turn-slice`).
- **Ordering teeth — `FieldGte`, `FieldLte`, `Monotonic`, `StrictMonotonic` — have nothing to lower
  onto.** Each is reached only by a *hand-authored* bit-decomposition per rule
  (`game-turn-slice/src/lib.rs:24`, `tests/game_turn_slice.rs:25`).

This is the bottleneck **everyone is hand-cranking around**: the game engine's D-crown (a rule reaches
the fold only by being hand-authored as a circuit), DreggCloud's honest-rung ceiling, and the forge's
checks all hit it. Close it once → every executor rule lifts to `proof_checked` for free.

## The linchpin: a reusable range/comparison gadget

A standalone gadget that emits the inequality primitive over the *existing* `ConstraintExpr` ops, so
the `StateConstraint → ConstraintExpr` compiler lowers ANY ordering tooth by calling it — no more
per-rule hand-authoring.

**Core: `a ≥ b` over BabyBear via bit-decomposition of the difference.**
- Let `d = a − b`. Prove `d ∈ [0, 2^k)` for a `k` that bounds the domain (game HP, scene index, budget
  — all small; `k ≈ 16–32`). If `d` is in range, `a ≥ b`; the wraparound case (`a < b` ⇒ `d = a − b + p`
  huge) fails the range check.
- **Encoding (all existing `ConstraintExpr`):** allocate `k` bit columns `b_0..b_{k-1}`; a `Binary`
  constraint per bit (`b_i·(b_i−1)=0`); one `Polynomial` reconstruction (`Σ b_i·2^i − d = 0`, `d` from
  a `Transition`/`Polynomial` over `a`,`b`). No new `ConstraintExpr` variant needed — the gadget is a
  *composition*. (If a native `RangeLookup`/`Lte` variant is later added for succinctness, the gadget's
  API stays; only its lowering changes. Adding the variant is the game+crypto terminals' call.)
- Derived: `a > b` = `a ≥ b+1`; `a ≤ b` = `b ≥ a`; `Monotonic(next ≥ local)` and `StrictMonotonic` fall
  straight out per transition.

**API (the thing the compiler consumes):**
```
// standalone, pure ConstraintExpr emission — no prover, no executor deps
pub fn emit_ge(a: Col, b: Col, bits: u32, alloc: &mut ColAlloc) -> Vec<ConstraintExpr>;
pub fn lower_ordering_tooth(t: &StateConstraint, ctx: &LowerCtx) -> Vec<ConstraintExpr>; // Gte/Lte/Monotonic/StrictMonotonic
```
Pure, testable in isolation (assert the emitted constraints accept the honest witness and reject
`a<b`), then the game terminal's `game-turn-slice/src/compiler.rs` calls `lower_ordering_tooth` instead
of hand-authoring. **Ownership: the compiler is theirs; this gadget is a standalone lib they consume.
Coordinate before wiring — it is on their critical path.**

**Home:** a small module/crate that depends on `dsl::ConstraintExpr` and emits it — NOT edited inside
`circuit/`'s hot files (crypto-terminal storm). A new `crate: constraint-lowering` (or
`circuit/src/dsl/lowering.rs` if the crypto terminal blesses it) keeps it collision-free.

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
  is a hardware attestation over the same public inputs).

So: **the linchpin makes the *proven* path automatic; the TEE makes a *fast* path available; the ladder
keeps both honest.** Kernel-enforced → `{re-executed | tee-attested | proven}`, pick per workload.

## Why this is the move (maturity · feature · fun · less-LARP, at once)

- **Less-LARP:** it's the exact `host_checked → proof_checked` gap the whole ecosystem is stuck at,
  built as a *tool* instead of a per-rule chore.
- **Maturity:** the substrate gains the missing primitive + a first-class assurance-rung type.
- **Feature:** every executor rule becomes provable; the TEE rung unlocks fast attestation for
  workloads STARKs can't touch.
- **Fun:** it's what unblocks the games' D-crown (a game rule reaching the crown *automatically*) and
  DreggCloud's honest agent story.

## Sequencing

1. **This doc** — the coordination artifact (align the game terminal, DreggCloud, forge on ONE gadget).
2. **Build `emit_ge` / `lower_ordering_tooth`** standalone + unit-test it in isolation (honest accepts,
   `a<b` rejects) — good weather, no collision.
3. **Coordinate the wire-in**: the game terminal's `compiler.rs` calls the gadget for ordering teeth
   (their lane, their call). DreggCloud + forge consume the same gadget.
4. **The `tee_attested` rung**: add `CiAssurance::TeeAttested{measurement,vendor}` + a Nitro/SEV
   attestation verifier (a later slice — the ladder makes room for it now).
