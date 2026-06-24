# dregg1 ↔ dregg2 Unification Ledger

The core types are duplicated between the dregg1 Rust surface (`turn/`, `cell/`,
`macaroon/`, `token/`, `circuit/`, `federation/`) and the verified dregg2 Lean
surface (`metatheory/Dregg2/`). This ledger maps every duplication precisely
(Rust file:line ↔ Lean file:line), states whether the FFI codec
(`dregg-lean-ffi/src/marshal.rs`) bridges them, and records the exact condition
to finish unification.

dregg2 Lean is the source of truth: verified, kernel-clean — the `lake build` of
`Dregg2.Exec.FFI` + the `Inst/*` per-effect circuits is green,
`#assert_namespace_axioms` whitelisting only `{propext, Classical.choice,
Quot.sound}`. The Rust types are hand-written, unverified duplicates that dregg2
*replaces*. **The Lean is the ORACLE; the Rust is the subject-under-test.**

**The Lean executor is the default-on runtime state PRODUCER for the swap-safe
covered set** (`_SWAP-COMPLETE-STATUS.md`). The node commit path
(`node/src/blocklace_sync.rs:1846`) routes through
`dregg_turn::lean_apply::produce_via_lean` by default (`DREGG_LEAN_PRODUCER`,
opt-OUT). For the covered effect kinds (SetField, Transfer, EmitEvent, NoteSpend,
NoteCreate, IncrementNonce, RefreshDelegation, Burn, RevokeCapability,
QueueAllocate, CellUnseal, …) the verified Lean executor PRODUCES the committed
`cell::Ledger` — `wire_state_to_ledger` reconstitutes it from the `WireState` —
and the Rust `TurnExecutor` runs as a demoted differential. The residual (root-gap
effects that fall back to Rust + still-unmapped effects) is named in
`_SWAP-COMPLETE-STATUS.md` §3; the U5 step below is covered-set authoritative, and
§U1–§U4 are the path to the full flip. The passive `decode_shadow_verdict` shadow
is the `DREGG_LEAN_PRODUCER=0` fallback.

---

## 1. Type-duplication map

| Concept | dregg1 Rust (file:line) | dregg2 Lean (file:line) | FFI bridge | Status |
|---|---|---|---|---|
| **Authorization** | `turn/src/action.rs:206` `pub enum Authorization` (10 variants) | `metatheory/Dregg2/Exec/FullForestAuth.lean:103` `inductive Authorization (Digest Proof)` | `dregg-lean-ffi/src/marshal.rs` `WireAuth` (`auth_to_wire` in `lean_shadow.rs:486`) | **BRIDGED (shadow).** All 10 Rust variants project to `WireAuth`; WHO-leg digests cross in full. Not yet *derived from* the Lean. |
| **Effect / Action** | `turn/src/action.rs:760` `pub enum Effect` | `metatheory/Dregg2/Exec/TurnExecutorFull.lean:3203` `inductive FullActionA` | `dregg-lean-ffi/src/marshal.rs:360` `pub enum WireAction` (56 arms) | **PARTIAL.** `lean_shadow::effect_to_wire` projects: SetField, Transfer, SetPermissions, SetVerificationKey, NoteSpend, NoteCreate, EmitEvent, MakeSovereign, RevokeDelegation. REMAINING: IncrementNonce (needs nonce threading), escrows, obligations, queues, bridge, seal/unseal, captp/swiss, factory, exercise — the Lean+wire already support these; only the Rust→wire projection is missing. |
| **CellProgram** | `cell/src/program.rs:53` `pub enum CellProgram`; also `circuit/src/dsl/circuit.rs:947` `pub struct CellProgram` (a 2nd, unrelated Rust dup!) | `metatheory/Dregg2/Exec/CellProgram.lean:76` `structure CellProgram` | none | **UNBRIDGED.** Two Rust `CellProgram`s (cell + circuit) vs one Lean. No codec. |
| **Caveat** | `macaroon/src/caveat.rs:108` `CaveatSet`; `token/src/dregg_caveats.rs:137` `enum DreggGrant` | `metatheory/Dregg2/Authority/Caveat.lean:38` `inductive Caveat (Ctx Gateway)` | wire `caveats` field exists in `WForest`/`WChild` but `lean_shadow` sends `vec![]` (caveats not projected) | **UNBRIDGED.** The wire grammar HAS a caveats slot; the shadow projector drops it. |
| **Predicate / Permissions** | `cell/src/permissions.rs:85` `pub struct Permissions`; `cell/src/predicate.rs:402` `enum PredicateInput`; `bridge/src/present.rs:2780` `enum Predicate` | `metatheory/Dregg2/` predicate surfaces (`Projection.lean`, `Coordination.lean`, the per-effect guard predicates in `Inst/*`) | `SetPerms { perms: i128 }` — collapses to `0` marker (`permissions_to_i128`) | **LOSSY BRIDGE.** Permissions collapse to a neutral scalar; the commit-bit decision doesn't depend on the exact value, but the structure is not carried. |
| **Token** | `federation/src/types.rs:538` `pub struct Token` | `Token Ctx Gateway` (used throughout `Dregg2/Exec/AuthModes.lean:152`) | via `WireAuth::Token` / `auth_cell_macaroon` | **PARTIAL.** Token authorization crosses; the federation `Token` struct itself is separate. |

---

## 2. The THREE representations problem

For Authorization/Effect there are currently **three** parallel encodings:

1. dregg1 Rust native (`turn::action::{Authorization, Effect}`) — what the live executor runs.
2. FFI wire (`dregg-lean-ffi::marshal::{WireAuth, WireAction}`) — the hand-rolled byte grammar; comment at `marshal.rs:269` admits "Variant order matches the dregg1 `Authorization` enum".
3. dregg2 Lean (`Authorization`, `FullActionA`) — the verified truth.

The wire (2) is the unification seam. It is byte-exact round-trip-tested against
the Lean `encodeActionW`/`parseActionW` (`metatheory/Dregg2/Exec/CodecRoundtrip/`).
The remaining unification work is to make the dregg1 Rust types (1) *project
totally* onto (2) — i.e. close every `_ => return None` in
`lean_shadow::effect_to_wire` — so EVERY turn is validated against the Lean,
then make the Lean verdict authoritative (the SWAP).

---

## 3. Actionable unification steps (in priority order)

- **U1 — finish `effect_to_wire` projection.** Map the remaining Rust effects to
  their existing `WireAction` arms. The Lean executor + wire codec ALREADY
  support escrow/obligation/queue/bridge/seal/captp/swiss/factory (52 verified
  `Inst/*` circuits + 56 `WireAction` arms). The only missing piece is the
  Rust→wire projection in `turn/src/lean_shadow.rs`. Each added effect = more of
  every turn validated against the verified Lean.
- **U2 — project caveats.** `WForest.caveats` is sent as `vec![]`; wire the Rust
  per-node caveats onto `Dregg2/Authority/Caveat.lean`.
- **U3 — carry Permissions structure** instead of the `0` collapse
  (`permissions_to_i128`), once the Lean models structured perms on the wire.
- **U4 — collapse the two Rust `CellProgram`s** (`cell/src/program.rs:53` and
  `circuit/src/dsl/circuit.rs:947`) and bridge to `CellProgram.lean`.
- **U5 — THE SWAP (covered-set authoritative).** For the root-agreeing effects
  the Lean executor (`dregg_exec_full_forest_auth`) produces the committed state
  and the Rust `TurnExecutor` runs as a differential
  (`turn/src/lean_apply.rs::produce_via_lean`, default-on via
  `DREGG_LEAN_PRODUCER`). Full retirement of the Rust `TurnExecutor` needs U1
  (project the remaining unmapped effects), the root-gap closures (widen `WState`
  to carry lifecycle/Permissions/VK/cap/`delegation_epoch`), and root-scheme
  unification. See `_SWAP-COMPLETE-STATUS.md` for the boundary + the precise
  residual; `SUCCESSOR-ROADMAP.md` for the remaining path.

---

## 4. Why the Rust circuits are NOT yet Lean-redundant (verified, not guessed)

`lake build` confirms the dregg2 `Inst/*` circuits are verified at the
**digest/state-transition layer** (e.g. `transfer.lean`'s `transfer_full_sound`,
`noteSpendA.lean`'s nullifier-set transition). They abstract Poseidon2 as the
named hypothesis `Poseidon2SpongeCR` and do NOT compute hashes/Merkle paths
in-circuit. The Rust AIRs (`effect_vm/`, `note_spending_air`, `poseidon2_air`,
`effect_action_air`) are the layer that actually enforces those hashes. So they
are a different abstraction layer, not a competing implementation — deleting them
would delete the only place digests bind to preimages (the
`feedback-conservation-is-not-correctness` trap). They retire one FRONTIER at a
time (in-circuit hash gates in the emitted grammar → limb arithmetic → selector
dispatch → wire the Lean interpreter to the executor), per
`_RUST-CIRCUIT-CONSOLIDATION.md` §3.

The only Lean-verified-redundant circuit code was dead scaffolding, already
deleted: `effect_interp.rs` (1713 LOC) + `garbled_air_p3.rs` (206 LOC).
