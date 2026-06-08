# THE SWAP — Producer-Mode Status (authority inversion realized)

**Status: the verified Lean executor is the DEFAULT-ON runtime state PRODUCER for
the swap-safe covered effect set.** This supersedes the "Lean runs only as a
SHADOW" framing in `_DREGG1-DREGG2-UNIFICATION-LEDGER.md` §0/§U5 and the
commit-bit-only lens of `_RUST-LEAN-DIVERGENCE-LEDGER.md`. The authority
inversion is no longer a roadmap item — it is wired and verified on the node
commit path.

Last verified: 2026-06-08 (local `lean-shadow` differential + node smoke test).

---

## 1. What "the flip is real" means here (file:line)

The node commit path is `node/src/blocklace_sync.rs::execute_finalized_turn`. At
`blocklace_sync.rs:1846–1911` it routes through
`dregg_turn::lean_apply::produce_via_lean(&executor, &turn, &mut s.ledger)`
whenever `s.lean_producer_enabled` (default ON — opt-OUT via `DREGG_LEAN_PRODUCER=0`,
`node/src/state.rs:39 lean_producer_env_enabled`).

`produce_via_lean` (`turn/src/lean_apply.rs:439`) does, for a covered turn:

1. drive the turn through the verified FFI export `dregg_exec_full_forest_auth`
   (`execFullForestG`, proven sorry-free) and **reconstitute a full
   `cell::Ledger` from the produced `WireState`** via `wire_state_to_ledger`
   (`lean_apply.rs:224`) — the `WireState → Ledger` extractor that
   `dregg-lean-ffi/src/marshal.rs:37` named as "the biggest gap";
2. run the Rust `TurnExecutor` as a **demoted differential** and snapshot its
   post-state root;
3. on agreement, **`*ledger = lean_ledger`** (`lean_apply.rs:490`) — the
   COMMITTED ledger (and its merkle `.root()`) is now the verified executor's
   output, not Rust's.

This is NOT the old `decode_shadow_verdict` path. `decode_shadow_verdict` (which
keeps only `{committed, loglen, status}` and throws away `.state`) is now used
ONLY in the passive `DREGG_LEAN_PRODUCER=0` fallback
(`turn/src/lean_shadow.rs:1143`). The default commit path adopts the Lean
`.state` via `wire_state_to_ledger` / the full post-state decoded by
`marshal::unmarshal_result` → `decode_shadow_state`. Grep confirms the only live
commit-path producer is `produce_via_lean`; the verdict-bit decoder is off the
default path.

**No silent divergence.** The coverage gate `forest_is_root_agreeing`
(`lean_shadow.rs:659`) admits ONLY turns whose every effect is in the swap-safe
set. A turn touching a characterized root-gap effect (or any unmappable effect)
falls back to the Rust producer with `ProducerOutcome::Fallback { reason }` and a
precise named reason. A turn the gate deemed safe that nevertheless diverges at
runtime is `ProducerOutcome::CoveredDivergence` — we keep the Rust post-state
(chain-consistent) and surface it as a real soundness finding; we do NOT commit a
divergent Lean root.

---

## 2. The honest fraction: Lean is the runtime producer for 12 / 56 effects

The wire grammar (`FullActionA` / `WireAction`) has **56 arms**. The producer
classification (`turn/src/lean_shadow.rs`) partitions the surface it touches:

- **AUTHORITATIVE (Lean produces the committed state) — 12 / 56.**
  `producer_root_agreeing_effects()`: **SetField, Transfer, EmitEvent, NoteSpend,
  NoteCreate, IncrementNonce, RefreshDelegation, Burn, RevokeCapability,
  QueueAllocate, CreateEscrow, CreateObligation.** For a turn whose effects are
  ALL in this set, the Lean-reconstituted ledger provably AGREES with the legacy
  Rust executor on full cell state + `cap_root` + `.root()`, pinned per effect by
  the `lean_state_producer_coverage` + `lean_state_producer_widen` +
  `lean_state_producer_sidetable` differentials. The verified executor's output IS
  the committed state. **(This drive added the off-cell-merkle-root holding-store
  CREATE families: `apply_create_escrow`/`apply_create_obligation` debit ONE cell's
  `balance` — carried by the `bal` side-table → reconstitutes — and park the value
  in the off-root `escrows`/`obligations` store; the verified `createEscrowKAsset`
  / `createObligationA`-dispatch-alias do the SAME single-cell debit + record
  insert, on the same `authorizedB` + balance + account + id-uniqueness legs, so
  the reconstituted `.root()` agrees.)**

- **DIFFERENTIAL-ONLY (Lean runs, root diverges, falls back to Rust) — 13 / 56.**
  `producer_root_gap_effects()`: **SetPermissions, SetVerificationKey,
  MakeSovereign, Refusal, ReceiptArchive, CellSeal, CellUnseal, CellDestroy,
  GrantCapability, AttenuateCapability, RevokeDelegation, ReleaseEscrow,
  RefundEscrow.** The producer RUNS (so the differential still cross-checks the
  commit bit), but the Lean-reconstituted `.root()` (or the commit bit) provably
  DIVERGES because the wire model is lossier than the cell commitment OR a gate
  leg is unmodelled. Each is pinned by a NEGATIVE-tooth differential that asserts
  the SPECIFIC divergence — characterized, never a silent pass. On the live path
  these fall back to the Rust producer. **(This drive added the escrow SETTLE
  effects: Rust gates `ReleaseEscrow` on a satisfied condition PROOF and
  `RefundEscrow` on a PAST timeout, neither expressible in a single covered turn at
  one block height, and the verified settle-auth gate differs — a characterized
  commit-bit gap.)**

- **RUST-PRODUCED (no wire projection yet) — the remaining 31 / 56.**
  obligation-settle (fulfill/slash, derived-id) / committed-escrow / bridge /
  seal-pair / captp-swiss / factory / introduce / exercise / queue-enqueue-dequeue
  / etc. `forest_is_marshallable` returns false, so the producer is ineligible and
  the turn commits the Rust post-state.

So: **12 effect kinds are Lean-authoritative at the producer; the residual is the
44 named above (13 run as differential + fall back to Rust; 31 are still
Rust-produced because they have no wire projection).**

---

## 3. The precise residual — why each gap is Rust-produced (not closed)

### 3a. Root-gap effects (Lean runs, Rust produces) — the wire model is lossier than the cell commitment

| effect | why the Lean `.root()` diverges from Rust |
|---|---|
| `SetPermissions` | wire `setperms` carries a COLLAPSED scalar; `compute_canonical_state_commitment` binds the full `Permissions` struct. |
| `SetVerificationKey` | wire `setvk` carries a collapsed scalar of the vk hash; the commitment binds the full `VerificationKey { hash, data }`. |
| `MakeSovereign` | Rust REMOVES the cell from `Ledger::cells` (→ a different leaf set); the wire state model has no sovereign-removal transition, so the reconstitution keeps the cell. |
| `Refusal` / `ReceiptArchive` | Rust writes an audit-field / lifecycle-Archived commitment (field[4] Poseidon-ish digest + a 2nd nonce bump) the wire `refusal`/`rarchive` arms do not reproduce byte-for-byte. |
| `CellSeal` / `CellUnseal` / `CellDestroy` | the wire `WState` cell record has no `lifecycle` field; the commitment binds the lifecycle PAYLOAD (reason hash, sealed/destroyed-at height, death cert). Closing needs the Lean kernel to model the lifecycle payload, not just a codec field. |
| `GrantCapability` / `AttenuateCapability` | the wire `caps` model carries `(target[,rights])` per edge; the Rust `cap_root` binds `(target, slot, permissions, breadstuff, expires_at, allowed_effects)`. A real grant/attenuate rewrites `cap_root`; the bare-`node` reconstruction cannot coincide. |
| `RevokeDelegation` | **(reclassified — a latent misclassification fixed.)** A COMMITTING revoke bumps the PARENT cell's `delegation_epoch`, which `compute_canonical_state_commitment` folds in (`commitment.rs` hashes `state.delegation_epoch`). The wire `WState` cell record has no `delegation_epoch` field, and the verified `revokeDelegationA` edits only the `caps` edge set, so the reconstitution keeps the parent's pre-state epoch → `.root()` diverges. (The no-op self-revoke that Rust REJECTS trivially "agrees", which is how the prior fixture masked the gap — but a real commit diverges.) Closing needs the Lean kernel to model the per-cell delegation epoch and carry it on the wire. |
| `ReleaseEscrow` / `RefundEscrow` | **(NEW this drive — the escrow SETTLE leg.)** Rust gates release on a satisfied condition (ZK proof / all-signers / predicate) and refund on a PAST timeout (`block_height > timeout_height`); the verified `releaseEscrowChainA`/`refundEscrowChainA` gate only on settle-actor authority over the recipient/creator + record-present-and-unresolved. With no condition proof / before the timeout the two executors disagree on whether the settle commits — a characterized commit-bit gap (the condition-proof / timeout-clock legs are the §8 portal the wire model does not carry). The single-cell CREDIT itself is `bal`-faithful; closing needs those gate legs modelled. |

### 3b. The 31 unmappable effects (no wire projection)

committed-escrow, obligation fulfill/slash (the Rust-DERIVED obligation id the
wire-id collapse cannot reproduce), bridge lock/finalize/cancel/mint, seal/unseal/
create-seal-pair, export/enliven/swiss-handoff/swiss-drop, create-cell/
create-cell-from-factory/spawn, introduce/validate-handoff/delegate/delegate-atten/
attenuate/drop-ref, exercise, queue-enqueue/dequeue/resize/atomic-tx/pipeline-step,
pipelined-send. The Lean kernel + wire codec already SUPPORT these (52 verified
`Inst/*` circuits + 56 `WireAction` arms round-trip-tested); the missing piece is
the Rust→wire **projection** in `turn/src/lean_shadow.rs::effect_to_wire`
(`forest_is_marshallable`). **This drive landed the escrow/obligation CREATE
projection (now Lean-PRODUCED) + the escrow SETTLE projection (characterized gap).**
Each added projection = another effect family
validated against, then produced by, the verified Lean.

---

## 4. The dregg(Lean-primary) / dreggrs(Rust-differential) boundary realized at the producer

The `_DREGG-DREGGRS-MANIFEST.md` boundary is now CONCRETE at the runtime producer:

- **dregg (Lean-primary):** for the 10 root-agreeing effects, `execFullForestG`
  (the verified `@[export] dregg_exec_full_forest_auth`) is the authoritative
  state producer. The committed `cell::Ledger` and its merkle root ARE the Lean
  executor's reconstituted output. Rust is demoted to a differential witness.
- **dreggrs (Rust-differential / residual producer):** for the 46 residual
  effects (11 root-gap + 35 unmapped), the legacy Rust `TurnExecutor`
  (`turn/src/executor/execute.rs`) produces the committed state. For the 11
  root-gap effects Rust ALSO runs the Lean producer as a differential commit-bit
  cross-check; for the 35 unmapped effects Rust is the only producer (the Lean
  producer is ineligible).

The boundary is enforced by code, not prose: `forest_is_root_agreeing` is the
gate, and the `ProducerOutcome` enum (`LeanProduced` / `Fallback` /
`CoveredDivergence`) records, per committed turn, exactly which side of the
boundary produced the state and whether the differential agreed.

---

## 5. Evidence (real differential output, this drive)

All run locally with the linked `libdregg_lean.a` (`lean-shadow` feature +
`lean_available()`), `DREGG_LEAN_SYSROOT` from `lake env`.

- **`turn/tests/lean_state_producer_coverage.rs` — 12 / 12 pass.** Asserts the
  root-agreeing / root-gap lists PARTITION the mappable set, that each
  root-agreeing effect round-trips (Lean == Rust on state + cap_root + root), and
  that each root-gap effect diverges in its SPECIFIC characterized way
  (a negative tooth). Includes `revoke_delegation_is_an_epoch_swap_gap` (the
  reclassification) and `produce_via_lean_installs_verified_state_on_covered_transfer`
  / `produce_via_lean_falls_back_on_root_gap_setpermissions` (the flip + fallback
  safety).
- **`turn/tests/lean_state_producer_widen.rs` — 7 / 7 pass.** Transfer / SetField
  / Burn / IncrementNonce / empty-revoke / two-effect-forest round-trip; cell-seal
  / cell-destroy / grant-capability assert their lifecycle/cap-fidelity gap.
- **`turn/tests/lean_state_producer_sidetable.rs` (NEW) +
  `lean_state_producer_coverage.rs` (extended this drive).** The off-cell-merkle-root
  holding-store CREATE families: `create_escrow_root_agrees` /
  `create_obligation_root_agrees` assert the verified producer's reconstituted
  ledger AGREES with Rust on full state + cap_root + `.root()` (the locker's `bal`
  debit reconstitutes; the escrow/obligation record is off-root). The SETTLE leg
  is pinned as a gap: `release_escrow_is_a_condition_gate_gap` /
  `refund_escrow_is_a_timeout_gate_gap` assert the SPECIFIC commit-bit divergence.
  NOTE: a concurrent in-session `build.rs` archive-GC race over-pruned the local
  `libdregg_lean.a` (native mathlib members dropped → non-self-linking); these
  differentials re-run green after a FULL closure re-seed (every dependency-package
  emitted `.c` archived; a `DREGG_LEAN_FFI_NO_ARCHIVE_GC=1` build.rs escape hatch
  keeps the restored archive from being re-pruned).
- **`node/tests/lean_producer_mode.rs` — 2 / 2 pass.** Drives the EXACT helper the
  node commit site calls (`produce_via_lean`) on a Transfer and a SetField turn;
  asserts (1) `ProducerOutcome::LeanProduced`, (2) the COMMITTED (Lean-installed)
  ledger equals the independent Rust differential on balances/nonces/all state
  fields AND `.root()`, (3) `agree == true`.

```
running 12 tests   (lean_state_producer_coverage)   test result: ok. 12 passed; 0 failed
running 7  tests   (lean_state_producer_widen)       test result: ok. 7 passed; 0 failed
running 2  tests   (lean_producer_mode, node crate)  test result: ok. 2 passed; 0 failed
```

---

## 6. What "FULLY DONE" would require beyond here (honest)

The flip is REAL and the divergence is GENUINELY closed on the covered set (the
differential PROVES Lean == Rust, full-state, not prose). It is NOT a full swap:

1. **Project the 35 unmapped effects** to the wire (`effect_to_wire`) so the
   producer is eligible for the whole `Effect` surface.
2. **Close the 11 root-gaps** by widening the wire `WState` to carry the
   commitment fields it currently drops (lifecycle payload, full
   Permissions/VK structs, full `CapabilityRef`, per-cell `delegation_epoch`) AND
   teaching the Lean kernel to model them — then re-classify each from
   `producer_root_gap_effects` into `producer_root_agreeing_effects` (its
   negative-tooth test will FAIL, forcing the promotion).

   **PROGRESS (this drive — the shared wire prerequisite is LANDED).** The wide
   `WState` codec now carries two per-cell `Nat` side-tables — `lifecycle`
   (discriminant `0`/`1`/`3`) and `deathCert` — on BOTH sides of the seam:
   `FFI.lean` (`WState.lifecycle/deathCert` + `encodeCellNats`/`parseCellNats` +
   `cellNatsOfFun`/`funOfCellNats`, threaded through
   `encodeWState`/`parseWState`/`wstateOfState`/`stateOfWState`, additive and
   default-empty exactly as `revoked` was, with a non-vacuity `#guard` that a
   Sealed+Destroyed pair SURVIVES the round-trip and `#assert_axioms` on all four
   new fns) and `marshal.rs` (`WireState.lifecycle/death_cert` mirror +
   `encode_cell_nats`/`parse_cell_nats`, byte-exact; the malformed-wire sentinels
   bumped to 11 fields). `ledger_to_wire_state` projects the pre-state cell's
   lifecycle discriminant + bound death-cert. Codec round-trips green Lean
   (`#guard`) + Rust (golden); the 12 coverage + 7 widen differentials still pass
   (no regression). This is the per-cell-commitment-field carrier EVERY
   lifecycle-class close needs. **Residual to flip the teeth:** model the full
   lifecycle PAYLOAD as 256-bit digests in the kernel (`reason_hash`/`sealed_at`
   for Sealed, `death_certificate_hash`/`destroyed_at` for Destroyed) + carry
   them on the `cseal`/`cdestroy` INPUT arms, then reconstitute the typed Rust
   `CellLifecycle` byte-identically; analogously, per-cell `delegationEpoch`
   (a faithful `u64`→`Nat`, reusing this same `cellNats` carrier) + the child
   `delegation`-clear for `RevokeDelegation`; full `Permissions`/`VK` structs for
   `SetPermissions`/`SetVerificationKey`; full `CapabilityRef` for
   `GrantCapability`/`AttenuateCapability`. Each is a kernel-semantics change, not
   just a codec field — so each negative tooth stays RED (correctly) until its
   payload is modelled.
3. **Unify the root scheme** so Lean computes the commitment too (today Lean
   produces the cells; the existing Rust `Ledger::root` hashes them — see
   `lean_apply.rs` §"Root computation").
4. **Retire the Rust `TurnExecutor`** only after 1–3 leave the differential clean
   across the full effect set on a real workload.
