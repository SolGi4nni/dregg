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

## 2. The honest fraction: Lean is the runtime producer for 10 / 56 effects

The wire grammar (`FullActionA` / `WireAction`) has **56 arms**. The producer
classification (`turn/src/lean_shadow.rs`) partitions the surface it touches:

- **AUTHORITATIVE (Lean produces the committed state) — 10 / 56.**
  `producer_root_agreeing_effects()`: **SetField, Transfer, EmitEvent, NoteSpend,
  NoteCreate, IncrementNonce, RefreshDelegation, Burn, RevokeCapability,
  QueueAllocate.** For a turn whose effects are ALL in this set, the
  Lean-reconstituted ledger provably AGREES with the legacy Rust executor on full
  cell state + `cap_root` + `.root()`, pinned per effect by the
  `lean_state_producer_coverage` + `lean_state_producer_widen` differentials. The
  verified executor's output IS the committed state.

- **DIFFERENTIAL-ONLY (Lean runs, root diverges, falls back to Rust) — 11 / 56.**
  `producer_root_gap_effects()`: **SetPermissions, SetVerificationKey,
  MakeSovereign, Refusal, ReceiptArchive, CellSeal, CellUnseal, CellDestroy,
  GrantCapability, AttenuateCapability, RevokeDelegation.** The producer RUNS (so
  the differential still cross-checks the commit bit), but the
  Lean-reconstituted `.root()` provably DIVERGES because the wire model is
  lossier than the cell commitment. Each is pinned by a NEGATIVE-tooth
  differential that asserts the SPECIFIC divergence — characterized, never a
  silent pass. On the live path these fall back to the Rust producer.

- **RUST-PRODUCED (no wire projection yet) — the remaining 35 / 56.**
  escrow / obligation / bridge / seal-pair / captp-swiss / factory / introduce /
  exercise / queue-enqueue-dequeue / etc. `forest_is_marshallable` returns false,
  so the producer is ineligible and the turn commits the Rust post-state.

So: **10 effect kinds are Lean-authoritative at the producer; the residual is the
46 named above (11 run as differential + fall back to Rust; 35 are still
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
| `RevokeDelegation` | **(reclassified this drive — a latent misclassification fixed.)** A COMMITTING revoke bumps the PARENT cell's `delegation_epoch`, which `compute_canonical_state_commitment` folds in (`commitment.rs` hashes `state.delegation_epoch`). The wire `WState` cell record has no `delegation_epoch` field, and the verified `revokeDelegationA` edits only the `caps` edge set, so the reconstitution keeps the parent's pre-state epoch → `.root()` diverges. (The no-op self-revoke that Rust REJECTS trivially "agrees", which is how the prior fixture masked the gap — but a real commit diverges.) Closing needs the Lean kernel to model the per-cell delegation epoch and carry it on the wire. |

### 3b. The 35 unmappable effects (no wire projection)

escrow create/release/refund, committed-escrow, obligation create/fulfill/slash,
bridge lock/finalize/cancel/mint, seal/unseal/create-seal-pair, export/enliven/
swiss-handoff/swiss-drop, create-cell/create-cell-from-factory/spawn, introduce/
validate-handoff/delegate/delegate-atten/attenuate/drop-ref, exercise,
queue-enqueue/dequeue/resize/atomic-tx/pipeline-step, pipelined-send,
bridge-mint. The Lean kernel + wire codec already SUPPORT these (52 verified
`Inst/*` circuits + 56 `WireAction` arms round-trip-tested); the missing piece is
the Rust→wire **projection** in `turn/src/lean_shadow.rs::effect_to_wire`
(`forest_is_marshallable`). Each added projection = another effect family
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
3. **Unify the root scheme** so Lean computes the commitment too (today Lean
   produces the cells; the existing Rust `Ledger::root` hashes them — see
   `lean_apply.rs` §"Root computation").
4. **Retire the Rust `TurnExecutor`** only after 1–3 leave the differential clean
   across the full effect set on a real workload.
