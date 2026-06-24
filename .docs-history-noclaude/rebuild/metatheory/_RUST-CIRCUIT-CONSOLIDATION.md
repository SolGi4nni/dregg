# Rust Circuit Consolidation — can we DELETE the manual AIRs because Lean is better?

Investigation for task #12 (rust-circuit-consolidation). Read-only audit, 2026-06-06.
Verdict up front: **NO blanket delete yet.** The Lean-extracted path and the bespoke Rust
AIRs are at **different abstraction layers**, not competing implementations of the same
circuit. The Lean path is the verified *state-transition* layer (digest algebra); the
bespoke AIRs are the *hashing / membership / VM-dispatch* layer (in-circuit Poseidon2,
Merkle paths, selector-gated multi-effect dispatch). Almost nothing is a like-for-like
replacement today. There is a real DELETE list (4 items: dead/duplicated/deprecated), and
a FRONTIER list (what Lean must gain before the production circuits can go).

---

## 0. The three+one descriptor systems (this is the whole crux)

| System | Where authored | Grammar / power | Lean-verified? | Wired to real executor? |
|---|---|---|---|---|
| **A. Lean PART-I** `EmittedDescriptor` → `circuit/src/lean_descriptor_air.rs` | Lean (`Dregg2/Exec/CircuitEmit.lean`), interpreted at eval-time | `var/const/add/mul`, `lhs=rhs`, + bit-decomp `RangeSpec`. **No hash, no transition, no lookup.** Per-row only. | YES (the load-bearing theorems) | **NO — zero external consumers** (grep: `turn/ wasm/ bridge/` = none) |
| **B. Lean PART-II** `EmittedMerkleDescriptor` (`Poseidon2Emit.lean`) | Lean | `merkle_hash/transition/pi_binding` opcodes; multi-row Merkle chain | YES (`emit_faithful_poseidon2_compress`) | **NO Rust interpreter consumes it** — `poseidon2_air.rs` only golden-string-compares the emitted JSON |
| **C. Rust DSL** `CircuitDescriptor` (`circuit/src/dsl/*.rs`) | **Rust** (hand-authored) | rich: `Hash`/`Hash2to1`/`Hash4to1`/`MerkleHash`/`Lookup`/`Selector`/`Squared` | **NO** (not emitted from Lean) | YES (e.g. `dsl::note_spending` is the live, non-deprecated note-spend) |
| **D. Bespoke AIRs** `note_spending_air.rs`, `effect_vm/`, … | **Rust** (hand-coded `eval_constraints`) | full transition + boundary + in-circuit Poseidon2 | NO | YES — `effect_vm` is referenced by **37 external files** incl. `turn/src/executor/` |

The naïve framing of the task ("Lean-extracted ones vs bespoke Rust, pick a winner") assumes
A and D are the same circuit at two fidelities. **They are not.** What Lean emits (system A)
is a *digest-equality* statement: e.g. `dregg-transfer-v1` is literally
`var2 = var0 − var4 ∧ var3 = var1 + var4 ∧ (var2+var3)=(var0+var1) ∧ guardbits=1`, and
`dregg-setfield-fullstate-v1` is `framePre_digest = framePost_digest` etc. The Poseidon2
that *produces* those digest felts lives in system B/D and the Part-I interpreter **cannot
evaluate a hash gate** (its `LeanExpr` has no Hash node). So deleting D and keeping A would
delete the only place the digests are actually bound to preimages → catastrophic soundness
loss. Memory `feedback-conservation-is-not-correctness.md` is exactly this trap.

Where Lean *is* strictly better: the digest algebra is verified end-to-end (52 `Inst/*.lean`
effect instances, each with a `_full_sound` keystone over ALL kernel state fields, grounded
on the single named `Poseidon2SpongeCR` hypothesis). Where the bespoke AIRs are strictly
better: they actually compute the hashes / Merkle paths / nullifiers in-circuit and dispatch
54 effects from one selector-gated trace.

---

## 1. Per-AIR table

Columns: **REAL?** (non-trivial constraints w/ non-zero coeffs + adversarial tests) ·
**Lean covers?** (does a Lean `Inst/*` descriptor express the SAME statement) ·
**As-efficient?** (column/constraint count parity, or slow universal interpreter) · **Verdict**.

| Rust AIR (LOC) | REAL? | Lean covers? | As-efficient? | Verdict |
|---|---|---|---|---|
| `effect_vm/air.rs` (3066) + `effect_vm/*` (13.5k total) — 54 effects, 186 cols, selector-gated, in-circuit Poseidon2 | **YES.** 187 tamper/reject tests in `effect_vm/tests.rs`, balance-limb borrow logic, hash-truncation teeth, differential test in `protocol-tests/`. THE live production circuit. | **PARTIAL.** Lean's 52 `Inst/*` cover the *digest-level* state transition for ~all effects, but NOT the in-VM Poseidon2 hashing, balance-limb decomposition, or the 54-way selector dispatch. Many `effect_vm` effects are *passthrough* (`CreateCell`/`CreateSealPair` only bind a `*_hash` PI, no inner semantics) — there Lean's full-state digest model is RICHER. | N/A — different layer. Lean has no selector-dispatch / limb / hash machinery to compare. | **KEEP + FRONTIER.** This is the crown jewel of the Rust side and the thing the swap must eventually subsume. Not deletable until Lean emits in-circuit hash + limb + dispatch (frontier F1–F4). |
| `note_spending_air.rs` (1837) — in-circuit Poseidon2 commitment + nullifier + Merkle path, boundary PIs | **YES.** 26 tamper markers; full-width 28-limb commitment chain; cross-federation replay boundary; value-inflation boundary. BUT marked `#[deprecated]`. | Lean `noteSpendA.lean`/`noteCreateA.lean` cover the *nullifier-set / commitment-set* digest transition + anti-replay guard bit — NOT the Poseidon2 preimage/Merkle membership. | N/A — different layer. | **KEEP (deprecate-track), do NOT delete.** Superseded *in Rust* by `dsl::note_spending` (system C), not by Lean. See DELETE-2. |
| `effect_action_air.rs` (2386) — per-effect transition AIR, balance two-limb subtraction, borrow bool | **YES.** 98 tamper markers (emit_event/set_permissions/set_vk tamper-rejected). | Lean `Inst/*` cover the digest-level versions of these effects; the limb-subtraction/borrow is Rust-only. | N/A — different layer (limb arithmetic). | **KEEP + FRONTIER** unless confirmed superseded by `effect_vm` (it shares column constants with effect_vm/pi.rs — likely the *predecessor* of effect_vm). Audit: is `effect_action_air` still on any live path, or fully absorbed into `effect_vm`? If absorbed → DELETE candidate (see DELETE-4). |
| `bridge_action_air.rs` (708) | **YES.** 15 tamper markers; used by `bridge/src/action_binding.rs` (2 external files). | `bridgeLockA/bridgeMintA/bridgeFinalizeA/bridgeCancelA.lean` cover digest transition + balance. NOT the cross-chain action binding hash. | N/A — different layer. | **KEEP.** Live in `bridge/`. Lean covers the ledger side, not the action-binding commitment. |
| `bridge_lock_action_air.rs` (381) | **YES.** 16 tamper markers. | `bridgeLockA.lean` covers the digest side. | N/A | **KEEP**, but check overlap with `bridge_action_air` / `effect_vm`'s `BridgeLock` arm — possible 3-way duplication (frontier audit). |
| `lean_descriptor_air.rs` (1578) — the generic Lean Part-I interpreter | **YES (as a prover), but TOY in coverage.** Real prove/verify via p3-uni-stark; round-trip + 6 adversarial tests (conservation, range, frame-reuse, authority gate). Proves `dregg-transfer-v1`, `dregg-transfer-fullstate-v1`, `dregg-setfield-fullstate-v1`. | This IS the Lean path. But it only ingests system-A descriptors — flat digest gates. | **Slow universal interpreter** (walks the `LeanExpr` AST at eval-time). For tiny digest descriptors (11–20 cols) the cost is negligible; it has never been exercised on a hash-bearing circuit because it *can't*. | **KEEP — this is the swap beachhead, not a deletion target.** Frontier: extend its grammar (Hash/transition opcodes) so it can ingest system-B descriptors and eventually replace D. |
| `poseidon2_air.rs` (1361) — Poseidon2 round AIR | **YES.** The actual Poseidon2 permutation constraints. | Lean `Poseidon2Emit` emits the merkle-chain descriptor and proves it faithful to `merkle_hash`, but does NOT emit the round-by-round permutation gates. | N/A — Lean abstracts Poseidon2 as `Poseidon2SpongeCR` (a hypothesis), never the rounds. | **KEEP (foundational).** The named crypto hypothesis on the Lean side is *discharged* in Rust here. Deleting this removes the actual hash. |
| `merkle_air.rs` (264 — table's old "9 LOC" was stale), `fold_air.rs` (9), `predicate_air.rs` (9), `compound_predicate_air.rs` (8), `native_signature_air.rs` (6), `merkle`/`block_transition_air.rs` (16) | `merkle_air.rs` is NOT a stub — it carries the AUDITED `p3-batch-stark` Merkle-membership prove/verify path (`prove_membership_p3`/`verify_membership_p3` + anti-ghost tests) on top of the re-exports. The others are thin re-export shims. | n/a | n/a | **NOT DELETABLE — no-use check FAILED 2026-06-22 (see §2 DELETE-1).** Each shim's `pub use` names are imported live through the module path across the workspace. |
| `bilateral_aggregation_air.rs` (1451), `membership_adjacency_air.rs` (811), `derivation_air.rs` (517), `garbled_air.rs`/`garbled_air_p3.rs`, `schnorr_air.rs`, `plonky3_verifier_air.rs`, `multi_step_air.rs`, `effect_vm_p3_air.rs`, `*_predicate_air.rs` | Mixed — `bilateral_aggregation` and `membership_adjacency` are REAL and live (tests external); the small predicate AIRs back the DSL. | Lean covers NONE of these (aggregation, garbled circuits, signatures, recursion verifier are entirely outside the `Inst/*` digest model). | N/A — no Lean counterpart exists. | **KEEP (all).** These are capabilities Lean has not modeled at all. Pure frontier. |

---

## 2. DELETE list (safe to remove once the cheap verification passes — NOT done here)

1. **DELETE-1 — stub/shim AIRs. NO-USE CHECK RAN 2026-06-22 → FAILED → NOT DELETABLE.**
   `merkle_air.rs`, `fold_air.rs`, `predicate_air.rs` were checked: each is imported LIVE
   through its module path across the workspace, so deleting the file + its `pub mod` line
   breaks the build. The shims are load-bearing module-path aliases, not dead weight. The
   precondition ("no external `use` that isn't already served by the canonical module") is
   FALSE — callers import via the SHIM path, not the canonical one. Detail:
   - `dregg_circuit::merkle_air::{MerkleAir, MerkleWitness, MerkleLevelWitness,
     compute_parent_poseidon2, create_test_witness}` — live in `bridge/src/present.rs`,
     `sdk/src/{full_turn_proof,cipherclerk}.rs`, `perf/`, and `circuit/src/{ivc,presentation,
     backends/plonky3,dsl/fold}.rs` (plus tests). `merkle_air.rs` ALSO owns the audited
     `prove_membership_p3`/`verify_membership_p3` path — it is not a re-export shim at all.
   - `dregg_circuit::fold_air::{FoldAir, FoldWitness, RemovedFact, build_shared_tree,
     compute_test_checks_commitment, prove_fold_stark, verify_fold_stark, ...}` — live in
     `circuit/src/{ivc,presentation,backends/plonky3}.rs`, `sdk/src/cipherclerk.rs`,
     `preflight/src/checks/{sovereign,composition,proofs,backends}.rs`, `bridge/`.
   - `dregg_circuit::predicate_air::{PredicateType, PredicateWitness, PredicateProof,
     compute_fact_commitment, prove_predicate, verify_predicate, prove_in_range, ...}` —
     live in `turn/src/executor/membership_verifier.rs` (the LIVE executor), and
     `circuit/src/{predicate_program,temporal_predicate_dsl,committed_threshold,presentation,
     backends/plonky3}.rs`, plus `teasting/` and `dregg-dsl-tests/`.
   To make these deletable, callers must first be migrated off the shim module paths onto the
   canonical modules (`crate::merkle_types`/`merkle_air`'s own p3 path, `crate::dsl::fold`,
   `crate::dsl::predicates`) — a wide rename, not a mechanical delete. NOT DONE; not in scope
   for a mechanical cleanup. (`compound_predicate_air.rs`, `native_signature_air.rs`,
   `block_transition_air.rs` were not separately re-checked but are presumed to share the same
   live-module-path posture; do not delete without the same grep.)
2. **DELETE-2 (TRACK, don't delete yet) — `note_spending_air.rs` (1844 LOC).** No-use check
   RAN 2026-06-22 → NOT DELETABLE. Only the `NoteSpendingAir` STRUCT and the
   `prove/verify_note_spend` FUNCTIONS carry `#[deprecated]`; the MODULE also exports
   non-deprecated, live types/helpers that the canonical `dsl::note_spending` path itself
   re-exports and consumes: `NoteSpendingWitness`, `key_to_field_elements`,
   `test_spending_key`, `commitment_chain`, `AIR_DESCRIPTOR`, the `limb_col`/`col`/`pi`
   modules. Live consumers via `dregg_circuit::note_spending_air::…`: `sdk/src/privacy.rs`,
   `commit/src/poseidon2_tree.rs`, `tests/src/full_pipeline.rs`, `circuit/src/dsl/
   note_spending.rs` (the canonical path itself: `use crate::note_spending_air::…` +
   `pub use crate::note_spending_air::…`), `circuit/src/{soundness_tests,air_descriptor}.rs`,
   plus benches and `circuit/tests/*`. Deleting the module breaks `dsl::note_spending` (the
   supposed successor) and the live SDK privacy path. The deprecated AIR struct/fns could be
   pruned only AFTER splitting the live helpers into a non-deprecated module — a refactor,
   not a delete. NOTE: this is a Rust→Rust supersession, **NOT** Lean replacing it.
3. **DELETE-3 — `effect_vm_p3_air.rs` (299) vs `effect_vm/air.rs`.** Verify whether the
   standalone `effect_vm_p3_air.rs` is a superseded earlier p3 wrapper now subsumed by
   `effect_vm/`. If so, delete the orphan.
4. **DELETE-4 (audit-gated) — `effect_action_air.rs` (2386).** Strong suspicion it is the
   *predecessor* of `effect_vm/` (shares `effect_vm/pi.rs` / `effect_vm/effect.rs` column
   constants). If grep confirms no live (non-test) caller and `effect_vm` covers every arm
   with ≥ the tamper coverage, delete. **This is the single biggest LOC win (2386) and is
   pure Rust-vs-Rust consolidation — Lean is not involved.**

None of these four is "delete because Lean is ≥". They are "delete because *another Rust
module* supersedes them." The Lean path does not currently let us delete ANY production AIR.

---

## 3. FRONTIER list (what Lean must gain before the bespoke AIRs can go)

For the swap to actually retire `effect_vm` + `note_spending` + `poseidon2_air`, the
Lean-emitted descriptor system needs to climb from *digest algebra* to *full circuit*:

- **F1 — In-circuit hash gates in the emitted grammar.** Extend `EmittedExpr` (system A) or
  promote system B (`EmittedMerkleDescriptor`'s `merkle_hash`) into the interpreter
  `lean_descriptor_air.rs`. Today the interpreter has `var/const/add/mul` only and cannot
  bind a digest to its preimage. Until then, every Lean descriptor's digest columns are
  *unconstrained inputs* on the Rust side — soundness leans entirely on system B/D, which the
  interpreter doesn't run. **This is the #1 frontier; nothing else matters without it.**
- **F2 — Balance-limb range/borrow.** `effect_vm`/`effect_action` do two-32-bit-limb
  subtraction with a borrow bit. Lean models balances as unbounded `ℤ` + a single 30-bit
  `RangeSpec`. To match, Lean must emit the limb decomposition + borrow constraint.
- **F3 — Selector-gated multi-effect dispatch.** `effect_vm` is ONE 186-col AIR dispatching
  54 effects by selector. Lean emits one descriptor PER effect (52 separate `Inst/*`). To
  replace `effect_vm` Lean must emit a single selector-gated descriptor (or the swap must
  prove a composition theorem: ⊕ of per-effect descriptors ≅ the dispatch AIR).
- **F4 — Wire the interpreter to the real executor.** `lean_descriptor_air` has ZERO
  external consumers. Even with F1–F3, a swap requires `turn/src/executor/` to call
  `prove_descriptor`/`verify_descriptor` instead of `EffectVmAir`. Today the executor is
  100% on `effect_vm`.
- **F5 — Capabilities Lean hasn't modeled at all (no path to delete):** bilateral
  aggregation, membership/adjacency, garbled circuits, Schnorr/native signatures, the
  plonky3 recursion verifier AIR. Keep indefinitely; these are not in the `Inst/*` universe.
- **F6 — Passthrough-effect richness (Lean is AHEAD here).** Several `effect_vm` effects
  (`CreateCell`, `CreateSealPair`, `CreateCellFromFactory`) only bind a `*_hash` PI and do
  NOT enforce inner state semantics. Lean's `Inst/*` full-state digest model DOES enforce
  the post-state for these. So the swap is not strictly "Lean catches up" — for the
  passthrough effects, porting Lean's full-state binding INTO `effect_vm` is an upgrade the
  Rust side should adopt now, independent of any deletion.

---

## 4. Bottom line for ember

- **Can we delete the manual Rust circuits because Lean is better? NO**, not the production
  ones. Lean is *better at the state-transition algebra* (verified, full-state, 52 effects)
  but it is not *the same circuit*: it abstracts Poseidon2/Merkle/dispatch/limbs away as a
  hypothesis (`Poseidon2SpongeCR`) and as separate un-interpreted descriptors. The bespoke
  AIRs are the only place those are actually enforced in-circuit, and `effect_vm` is the live
  executor circuit (37 external consumers).
- **Real, safe consolidation wins exist — but they are Rust-vs-Rust**, not Lean-vs-Rust:
  DELETE-1 (≤16-LOC shims), DELETE-2 (deprecated `note_spending_air` → `dsl::note_spending`,
  after test migration), DELETE-3 (`effect_vm_p3_air` orphan), DELETE-4 (`effect_action_air`
  2386 LOC if subsumed by `effect_vm`). Net potential: ~2.7k+ LOC, zero soundness change.
- **The Lean path's value is the FRONTIER**: it is the verified specification the production
  circuits should be proven to refine. The end-state is not "delete Rust, run the Lean
  interpreter" (the interpreter can't hash); it is "prove `effect_vm` REFINES the Lean
  per-effect digest descriptors" (the `TurnEffectRefinement`/`EffectEmittedRefinement`
  Lean modules are exactly this bridge in progress), then F1–F4 let the interpreter
  *become* a real prover and the bespoke AIRs retire one frontier at a time.
- **Do NOT delete anything yet.** Each DELETE item has a stated precondition (grep for live
  callers / migrate tests). Recommend a follow-up that executes DELETE-1 + DELETE-3 first
  (lowest risk), then audits DELETE-4 (highest payoff).

### 2026-06-22 mechanical-cleanup pass — DELETE-1 + DELETE-2 no-use check RAN, BOTH BLOCKED

The cheap no-use verification DELETE-1/DELETE-2 were "blocked on" was performed (workspace-wide
grep of each module's public-item module paths). **Result: nothing in the shim/deprecated set
is safely deletable.** `merkle_air.rs`, `fold_air.rs`, `predicate_air.rs` and the deprecated
`note_spending_air.rs` are ALL imported live through their module paths (including by the live
`turn/` executor, the `sdk/` privacy + full-turn-proof paths, and — for note_spending — by its
own intended successor `dsl::note_spending`). `merkle_air.rs` is moreover NOT a shim: it hosts
the audited `p3-batch-stark` membership path. The consolidation remains BLOCKED on a wide
caller-migration off the shim module paths, which is a refactor, not a mechanical delete. No
files were removed in this pass.
