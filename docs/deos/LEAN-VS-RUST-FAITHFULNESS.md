# Lean-vs-Rust faithfulness — where the model IS the execution vs where a mirror could drift

The honest answer to "is our Lean model what we execute, or do we still have lots
of parallel Rust codepaths?" is **layered**. It is neither "the Lean is fully
executed" (it is not) nor "it is all drifty parallel Rust" (the turn core genuinely
IS the Lean, compiled and run). This document classifies each layer precisely,
names the faithfulness bridge (or the gap) that binds the Rust to the Lean, and
grades the drift risk — with `file:line` citations against HEAD.

Classification vocabulary:

- **LEAN-EXECUTED** — a Lean `@[export]` is the authoritative run; the Lean output
  is what the node commits. The model *is* the execution.
- **LEAN-EMITTED** — Lean authors the artifact (a circuit descriptor) that the Rust
  ingests; a byte-pinned golden binds the two. Lean is the source of truth.
- **UNTRUSTED-RUST-BY-DESIGN** — the Rust is a *search*; correctness rides on a
  Lean-modeled/checked **certificate**, not on trusting the search. Correct by
  construction (verify-not-find), not a drift gap.
- **RUST-PROVER-OF-LEAN-CONSTRAINTS** — Rust proves whatever the Lean-emitted
  descriptor says; soundness is the Lean-proven AIR + the checked certificate.
- **RUST-MIRROR-OF-LEAN** — a Rust re-implementation of a Lean verb/theorem, bound
  to the Lean only by a named citation (a *hand-mirror*), a byte-*differential*, a
  byte-*twin*, or a proven *refinement*. This is where drift lives; graded per bridge.
- **RUST-ONLY** — no Lean model at all.

## The classification table

| Layer | Classification | Faithfulness bridge (or gap) | Drift risk |
|---|---|---|---|
| **Turn / state executor** (the node's authoritative state producer) | **LEAN-EXECUTED** | `@[export dregg_exec_full_forest_auth_direct]` = `execDirect` (`metatheory/Dregg2/Exec/FFIDirect.lean:285`), called by `produce_via_lean` (`exec-lean/src/lean_apply.rs`) through the single gate `execute_via_producer` (`node/src/executor_setup.rs:120`). Default ON (`lean_producer_effective`, `node/src/state.rs:65`). On the covered set the Lean post-state is **installed unconditionally and committed**; the Rust `TurnExecutor` is demoted to a differential cross-check. | **LOW** on the covered set (Lean is the run + Rust agrees-or-is-a-bug). The real caveat is the **covered/uncovered partition**: an unmappable turn or a root-gap effect *falls back to Rust-authoritative* for that turn (`executor_setup.rs` `Fallback` arm) — logged, explicit, never silent. |
| **Effect-VM / circuit descriptors** (the constraint IR the prover ingests) | **LEAN-EMITTED** | Constraints authored in Lean: `NoteSpendingLeafEmit.lean` (`noteSpendLeafDesc`), `EmitRotationV3.lean`, `Market/CertFDescriptor.lean`. Byte-pinned in Lean via `emitVmJson2` `#guard`. The Rust twin (`note_spend_to_descriptor2`, `circuit-prove/src/note_spend_leaf_adapter.rs:298`) is bound by an **emit-equality KAT**: `circuit-prove/tests/note_spending_emit_gate.rs` embeds the exact Lean golden string, decodes it, and asserts byte-equality with the Rust lowering (a drift on either side breaks the test or the Lean `#guard`). | **LOW** — real byte-golden bridge on both directions. |
| **Clearing search** (fhEgg convex solver) | **UNTRUSTED-RUST-BY-DESIGN** | `fhegg-solver` is a standalone crate (no protocol deps). verify-not-find: `Market/CertF.lean` proves the certificate check sound (`weak_duality:113`, `certifies_epsilon_optimal:133`); the Rust check is `fhegg-solver/src/cert.rs CertF::check`. The PDHG *search* is untrusted; only the **certificate** is checked, and that check is both Lean-modeled and lowered to an AIR (`circuit-prove/src/cert_f_air.rs`, `CertFDescriptor.lean`). | **N/A (correct by design)** — the untrust is the architecture; correctness rides on the checked certificate, not on the search. NOT a drift gap. |
| **STARK prover** (`circuit-prove`) | **RUST-PROVER-OF-LEAN-CONSTRAINTS** | Ingests the Lean-emitted descriptor and proves it (`prove_vm_descriptor2`/`verify_vm_descriptor2`). Soundness = the Lean-proven AIR (the linking tower / BCIKS20, `~112.6` accepted bits) + the checked certificate. The prover proves *whatever the descriptor says*; the descriptor is Lean-authored and byte-pinned. | **LOW** — no independent semantics to drift; the constraints are the Lean-emitted artifact. |
| **Shielded-pool note crypto** (Poseidon2 commitment / nullifier / value-binding / Merkle membership) | **LEAN-EMITTED** | The note leg rides the note-spend descriptor family (byte-pinned emit, above) and is proven by the real AIR (`shielded/spend_circuit.rs` C6/C7, `note_spend_leaf_adapter.rs`). Modeled in `ShieldedValue.lean` §6 / `Shielded/RealCrypto.lean`. | **LOW** — same byte-pinned bridge as the descriptor layer. |
| **Shielded-pool conservation + custody accounting** (`shieldK`/`unshieldK`/`release`/`drawMint`/nullifier, and the composition bricks) | **RUST-MIRROR-OF-LEAN — hand-mirror** | Lean models: `ShieldedValue.lean` `shieldK:330`/`unshieldK:345` + theorems `created_value_conservation:148`, `unshield_value_binding:408`, `unshieldK_preserves_pool:571`; `InterchainCustody.lean` `release:162`/`drawMint` + `release_backed`/`overMint_refused`/`overRelease_refused`. **None are `@[export]`ed** (zero exports in these files). The Rust re-implements them: production `bridge/src/solana_mirror.rs MirrorState` (`invariant_holds:419`); POC-local `MirrorState` re-defs (`shielded_deposit_glue_poc.rs:303`, `shielded_settle_back_poc.rs:251`) + `check_conservation`/`check_settle_conservation`. The bridge is **prose only**: `InterchainCustody.lean:16,108` says "a faithful model of the Rust `bridge/src/solana_mirror.rs MirrorState`"; the POCs say "the Rust mirror of `ShieldedValue.lean created_value_conservation`". No `@[export]`, no refinement/simulation theorem, no byte-differential harness exists (grep-confirmed absent). | **MED–HIGH** — the one genuine drift surface. The direction is even inverted from ideal: **Lean models the Rust** (post-hoc faithfulness) rather than Lean authoring/exporting the executed path, and there are *two* independent Rust `MirrorState` implementations (production + per-POC) bound to the Lean by nothing stronger than a doc-comment. |

## The honest verdict — how much is genuinely Lean-executed

- **The commit-path turn core IS Lean-executed.** `execDirect`/`dregg_exec_full_forest_auth_direct` is the authoritative producer for every ingress (thin HTTP, signed-envelope, blocklace-finalized) on the covered set, default ON. This is the load-bearing claim and it holds: the model *is* the execution here, with the Rust demoted to a checked reference. Do not over-deflate this.
- **The proving stack is Lean-emitted / Lean-proven, not a parallel Rust semantics.** Descriptors are Lean-authored and byte-pinned; the prover proves them; the fhEgg search is untrusted-by-design with a Lean-checked certificate. None of these is drift.
- **The one real drift surface is the shielded-pool conservation/custody accounting** — the `MirrorState` state machine and the composition bricks (`shielded_*_poc.rs`). These are **hand-mirrors**: Rust re-implementations bound to their Lean theorems by prose citation only. The note *crypto* underneath is fine (Lean-emitted AIR); it is the *accounting wrapper* around it that could drift. This layer is also the newest (PoC-stage composition), which is exactly where a mirror is most likely to be edited out from under its Lean twin. Do not over-claim it away.

Roughly: **the commit path is Lean-executed; the proving artifacts are Lean-emitted/proven; the shielded-pool composition layer is the single hand-mirror with real drift risk.**

## The tightening plan — closing the hand-mirrors (highest-drift-risk first)

There are three conceivable ways to close a hand-mirror, and they are **not**
equal. The architectural call: **`@[export]`/FFI is primary — it dissolves the
problem**; a byte-differential is a useful interim *canary*; "prove the Rust
refines the Lean" is **not a real option**. Honestly graded:

1. **`@[export]` / FFI — ELIMINATE the mirror (PRIMARY).** Make the Lean the
   *executed* code. There is then no parallel Rust to keep faithful: the Rust
   collapses to plumbing (marshalling, prover-harness, IO), and the composition
   bricks become Lean-compiled *calls* instead of hand-mirrors. The turn core
   already works exactly this way (`lean_producer`). The residual TCB is the
   Lean→C compiler + the C toolchain — a **single, shared, well-understood TCB**,
   far smaller than N independently-edited hand-mirrors. This is the tightening.

2. **Byte-differential harness — a drift CANARY (interim, for anything not yet
   exported).** Run the Lean step and the Rust step over a shared op-trace and
   assert equal states. This is **testing, not proof**: it only witnesses the
   inputs you run, and byte-identity is not denotational faithfulness (see the
   repo's own `feedback-byte-identity-differential-is-not-faithfulness`). Valuable
   as a cheap early-warning while an op still has a Rust twin — not a closure.

3. **"Prove the Rust refines the Lean" — NOT a real option (do not pursue as the
   tightening).** The only tools (Aeneas/Charon, hax) *extract a subset* of the
   Rust into a proof-assistant model and prove *that*. The extractor becomes a
   TCB — its translation faithfulness is unprovable within the system — and it
   handles only a subset (arbitrary `unsafe`/real-systems Rust is excluded), at
   research-grade maturity. So it is "prove a *trusted translation of a subset*",
   not "prove the Rust": it **moves the TCB, it does not eliminate it**, and buys
   less than option 1 for far more effort. Named honestly so it is not mistaken
   for a clean path.

Per-op, highest drift first — all recommend option 1, with option 2 as the interim
canary until the export lands:

1. **Custody state machine — `drawMint` / `release` / `recordEscrow` (the `supply ≤ locked` conservation). HIGHEST.** Three implementations (Lean `InterchainCustody.MirrorState`, Rust prod `solana_mirror.rs`, POC-local `MirrorState`) bound only by prose. `MirrorState` is a two-integer `(locked, supply)` record with fully `Decidable` ops — trivially exportable. **`@[export]` `drawMint`/`release`/`recordEscrow`** and have `solana_mirror.rs` and the bricks call the Lean step; three implementations collapse to one Lean-executed custody path. Interim canary: a byte-differential Lean-step-vs-Rust-step over a shared op-trace (cheap given the tiny state) until the export cutover lands.

2. **`shieldK` / `unshieldK` / nullifier pool-state accounting (pool debit + nullifier consume). HIGH.** The note leg already rides the Lean-emitted AIR (low drift); the *pool-state transition* around it is the mirror. **`@[export]` the shielded-pool verbs** (`shieldK`/`unshieldK`/`release`/`clear`/nullifier) so the pool transition is Lean-executed exactly like the main turn core, and the composition bricks become Lean-compiled calls rather than per-POC re-implementations.

3. **`check_conservation` / `check_settle_conservation` (Σin = Σout = V*; released = note value). HIGH.** These recompute the arithmetic of `created_value_conservation` / `unshield_value_binding` / `unshieldK_preserves_pool` in Rust. Once the verbs above are exported the conservation follows from the Lean theorems over the executed path (no separate Rust recompute to keep faithful). Interim: a differential against the Lean-exported predicate over the same notes+fills as a drift canary.

A concrete first cut that removes the most drift for the least work: `@[export]`
the `InterchainCustody.MirrorState` step (item 1) and delete the two POC-local
`MirrorState` re-defs in favor of it — one Lean-authored, Lean-compiled custody
state machine, called from both the production bridge and the composition bricks.
The residual TCB is the one shared Lean→C toolchain, not N hand-mirrors.
