# Nullifier Accumulator Unification — design

**Status:** design, pre-implementation. **Author:** this session (Fable), for ember review.
**Why:** the kernel nullifier accumulator is currently *three incoherent mechanisms*. On a real
multi-node devnet running note-spends, that incoherence is a soundness/liveness hole. This unifies them
into one coherent, persistent, cross-node-consistent indexed accumulator.

## 1. The problem — three mechanisms that drift

| # | Mechanism | Where | Role today | Flaw |
|---|-----------|-------|-----------|------|
| 1 | Persisted store | `node/src/blocklace_sync.rs:4449/4658` (`store_nullifier`/`load_all_nullifiers`) | THE working cross-node anti-replay (freshness = "not yet spent" vs this canonical set) | a flat set, not the committed root; freshness is a heuristic ("canonical set exceeds", `:4997`), not a witness |
| 2 | In-memory set | `turn/src/executor/mod.rs:771` `note_nullifiers: Mutex<NullifierSet>` | per-process double-spend reject | not persisted; not reconstructed on restart/catchup |
| 3 | Committed root | limb 26 (+ completion lanes 67..73) | *should* be the accumulator root | **flickers**: real (grow-gate) on a spend turn, empty `hash_bytes([0;32])` on a non-spend turn; **cross-turn-discontinuous** (grow-gate before-leaf `value:1` vs after-inserted leaf `value:nf` ⇒ turn N after-root ≠ turn N+1 before-root) |

The committed limb-26 accumulator is **half-built and not the source of truth**. Freshness works via (1),
but (3) is unreliable for light clients / catchup / any verifier, and the three can diverge.

## 2. The invariants the unified accumulator MUST hold (the contract)

- **INV-1 STABLE** — limb 26 = the *current* committed nullifier-set root on **every** turn (spend or not), never empty-when-nonempty.
- **INV-2 CONTINUOUS** — turn N's *after*-root == turn N+1's *before*-root over the same set (one consistent leaf encoding).
- **INV-3 PERSISTENT** — the accumulator is reconstructable from durable state on restart/catchup, and `reconstructed_root == committed_root`.
- **INV-4 SOUND** — a spend inserts `nf` **iff** `nf ∉ accumulator` (fail-closed double-spend); the committed after-root reflects the insert.
- **INV-5 VERIFIABLE** — freshness = a non-membership witness checkable against the *committed* root (light-client-friendly), not a node-local heuristic.
- **INV-6 AGREED** — all honest nodes commit the same root for the same finalized turn sequence.

## 3. The unified design

**One accumulator representation.** The deployed `CanonicalHeapTree8` (arity-16 sorted-Poseidon2,
`HEAP_TREE_DEPTH`), leaf `HeapLeaf { addr: fold_bytes32_to_bb(nf), value: nf_value }` — a **`(nf, value)`
map**, NOT a bare set. **DECISION (corrected — the leaf value is load-bearing, not `value:1`):** the
circuit noteSpend grow-gate already inserts `leaf.value = nf_value` (the note value, published as `PI[38]`
— `trace_rotated.rs:1227/1439`, "the audit felt"); the accumulator is an *auditable `(nullifier, value)`
record*. The value is NOT a privacy/unlinkability leak (it is already a public input; unlinkability rides
the nullifier derivation, `cells.md:263`). So **match the circuit — do NOT change it.** The incoherence
is on the Rust side: `NullifierSet::root8()` (landed `369895cce`) uses `value:1`, and the persisted store
persists only `nf`. Fix: make `NullifierSet` a **map `nf → value`**; `root8()` uses `(nf, value)` leaves
matching the circuit exactly; persist `(nf, value)`. Then before-root (stored) == the circuit's after-root
⇒ INV-2 holds, **with no circuit change and no VK regen for the value binding**, audit record preserved.
The differential tooth: Rust `root8()` == the in-circuit grow-gate after-root over the same `(nf, value)`.

**Backed by the persisted store; derived in memory.** The durable source of truth stays the persisted
store (already there). The in-memory `CanonicalHeapTree8` is *derived* from it: reconstruct on
load/catchup (`load_all_nullifiers` → build tree, O(n) once), advance incrementally per spend
(`insert_witness`, O(log n)), persist each new `nf` (already done). This collapses mechanism (2) into a
*view* of (1), and gives INV-3 (reconstruct + assert `root8() == committed`).

**Committed every turn.** The rotation-witness builders feed the accumulator's `root8()` into
`V9RotationContext` for **before and after** on *every* turn: non-spend ⇒ before==after==current root
(fixes the flicker, INV-1); spend ⇒ before = pre-insert root, after = post-insert root, and the
grow-gate's in-circuit after-root must equal the accumulator's post-insert root (consistency, requires
the `value:1` unification). This is the "live-root threading."

**Freshness as a witness (INV-5).** A spend carries a non-membership witness (`GapOpen8`/`NfAccWitness`,
proven in `metatheory/Dregg2/Exec/NullifierAccumulator.lean`) checked against the committed root —
replacing the node-local "canonical set exceeds" heuristic. (Deeper; stage E, can follow the stable root.)

**Faithful 8-felt.** Fill lanes `[26,67..73]` from the `root8()` `Faithful8` (not the lossy 1-felt
`hash_bytes`), in both twins (`commitment.rs::compute_rotated_pre_limbs`, `rotation_witness.rs::produce`).

**SEGREGATION (Stage-A finding).** `note_nullifiers` is an *omnibus* dedup set — NoteSpend + shielded +
React/pending-hole + cross-fed bridge all insert into it — but the circuit limb-26 grow-gate grows ONLY on
NoteSpend. So `root8()` over the whole set diverges from what the circuit commits. The committed limb-26
accumulator must be **NoteSpend-only** (a segregated view/set), matching the circuit. **DECISION (ember to
confirm):** commit the NoteSpend-only accumulator first (closes the primary monetary double-spend hole);
shielded/React/bridge replay-protection stays in-memory as a **same-class residual** (each needs its own
in-circuit grow-gate + committed root — a follow-on campaign). Mechanism: either a separate NoteSpend set,
or tag each `note_nullifiers` entry with its effect-kind and filter to NoteSpend for `root8()`.

**The `commitments_root` twin** (limb 27, lanes 74..80): the note-CREATE commitment set — identical
design, a parallel `CanonicalHeapTree8` accumulator. Do it in the same campaign (§4 stage F).

## 3b. CANONICAL-FIRST reorientation (ember, 07-09) — the Lean is canonical, the Rust is a ghost

**Scope = the THREE canonical accumulators** (`RecordKernelState`): `nullifiers` (← noteSpend; shielded
folds in via the shared `EFFECT_NOTE_SPEND` facet), `commitments` (← noteCreate), `revoked` (← cap_revoke).
Main is **pre-flip**: all three are `List Nat` committed via `ListCommit.listDigest`; the circuit already
carries the tree-root geometry (`nullifierRootGroupCol`) — the kernel just hasn't flipped to match. The
Rust `note_nullifiers` omnibus (shielded/React/bridge dedup) is **ghost divergence**, not canonical.

**Order of work: Lean canonical FIRST, Rust ghost MIRRORS.**
- **Phase 1 — canonical Lean flip** (per set): add the `Digest8` root field to `RecordKernelState`; the
  effect advances the root via the proven `NullifierAccumulator` gate (retire the `List`'s canonical
  authority); `StateCommit.RH`/`RestHashIffFrame` absorbs the root (16→18→… fields); the full-state
  frame-apex cascade re-derives (the ~130-file wave — bs-vk `78dcb1527` etc. is the PATTERN, ported to
  main). Proven + `#assert_axioms`-clean; the gate soundness (`present_no_witness`) is the anti-replay.
  Do `nullifiers` first, then `commitments`, then `revoked` (same shape).
- **Phase 2 — Rust ghost mirror**: executor advances the roots, commitment producer fills the faithful
  8-felt, persistence carries `(nf,value)` + reconstruction, netlayer coherent — all *derived from* the
  canonical Lean encoding (Stage-A's `(nf,value)` primitive re-anchored to the Lean, not the circuit).
- **Phase 3 — deploy**: VK regen + fresh federation + all-three-accumulator cross-node replay-refused proof.

Stage-A (Rust `(nf,value)`, `fe1545543`) stands as the Phase-2 primitive but must be re-anchored to the
canonical Lean encoding once Phase 1 fixes it. Build Lean on hbox (`~/dev/bs-vk-flip` or a main worktree),
Rust on nextop.

## 4. Staging (LEGACY ghost-first plan below — superseded by §3b canonical-first; kept for the Rust-mirror detail)

- **A — coherent primitive + leaf-encoding continuity.** Make `NullifierSet` a `nf → value` map; `root8()` uses `(nf, value)` leaves matching the circuit's `value:nf` exactly (NOT `value:1`). Differential tooth: Rust `root8()` == the in-circuit grow-gate after-root over the same `(nf, value)`. VERIFY: turn N after-root == turn N+1 before-root. *(NO circuit change; the circuit is already right — Rust catches up.)*
- **B — live-root threading (INV-1).** Executor exposes the current `root8()`; `rotation_witness_for_self_sovereign`/`_for_capability` gain before/after `Faithful8` params fed from `executor.note_nullifiers.root8()`; update the ~4 prod callers (`blocklace_sync.rs`, `api.rs`, `cipherclerk.rs` — now clean post-quiesce). Spend path feeds pre/post from the freshness path's already-in-hand sets. VERIFY: non-spend turn commits the non-empty current root.
- **C — Faithful8 ripple.** `V9RotationContext.nullifier_root: [u8;32]→Faithful8`; `produce(&Faithful8)` (12 sites, `rotation_witness.rs`) + the 6 `mint_*` helpers; `write_lanes([26,67..73])` both twins; `sg`-sweep the `&[0u8;32]` → `&empty_nullifier_root_8()` callers (mostly tests). Atomic (Green-Or-Bust). *(Reference: bs-vk `78dcb1527`+`cf98413f8`.)*
- **D — persistence/reconstruction (INV-3).** On load/catchup reconstruct the tree from the store; assert `root8() == committed`. Restart-survives-double-spend test.
- **E — freshness witness (INV-5).** Non-membership witness vs the committed root; retire the "canonical set exceeds" heuristic.
- **F — commitments_root twin.** Parallel unification (limb 27, lanes 74..80).
- **G — VK regen.** `cd metatheory && lake build Dregg2`; `emit-descriptors.sh`; `check-descriptor-drift.sh` PASS. The committed value shifted fleet-wide.
- **H — LIVE proof.** Fresh-genesis n=4 (hbox×2+nextop×2), a cross-node double-spend attempt is REFUSED, root advances, catchup/restart reconstructs consistently.

## 5. Ripple surface (from `sg`, so we size it honestly)

- `V9RotationContext` literals: **17** (≈4 prod: `rotation_witness.rs`, `commitment.rs`, `cipherclerk.rs`; ≈13 test).
- `produce(...)` rotation-witness calls: **12**, all in `turn/src/rotation_witness.rs`.
- `nullifier_root: &[u8;32]` param sigs: **2 files** (`rotation_witness.rs`, `commitment.rs`).
- `&[0u8;32]` arg passes: small, mostly test — `sg`-sweepable.

The production surface is ~3 files + a mechanical test sweep — **not** the "~87 callers" first feared.

## 6. Risks / gates

- **`value:1` unification is a circuit + VK change** (stage A/G) — ember-gated, greenfield-authorized. A wrong leaf encoding = UNSAT or a silent continuity break; the differential (accumulator `root8()` == in-circuit grow-gate after-root) is the tooth.
- **before/after ordering** (stage B) — a wrong pre/post root is a soundness bug; test it explicitly.
- **reconstruction consistency** (stage D) — if the store→tree rebuild ≠ the committed root, catchup wedges; assert it.
- **commitments twin** must move in lockstep or the commitment binds a mixed regime.
- **VK regen** invalidates old proofs — fine on fresh genesis (H), authorized.

## 7. Coordination

Touches `blocklace_sync.rs` (was a live-lane file — ember quiescing). Stay atomic per stage; `sg` for the
mechanical sweeps; independent clean build/test is the gate (lanes have false-claimed green repeatedly).
The verified-Lean side (`NullifierAccumulator.lean` gate, the bs-vk `advanceRoot8Exec`/discharge proofs)
is the spec these Rust changes must match — salvage it as the reference, not a merge.

## COMMITMENTS-RUST executor-set design (night 07-10, for after the Lean dual lands)
The commitments accumulator (note-CREATE set) mirrors the nullifier one but needs a NEW executor set (there
is no note_commitments today — grep empty). Design (mirror TurnExecutor.note_nullifiers):
- ADD `note_commitments: Mutex<CommitmentSet>` to TurnExecutor (turn/src/executor/mod.rs, beside
  note_nullifiers:771). CommitmentSet = a (commitment→value) map over the deployed CanonicalHeapTree8, leaf
  `HeapLeaf { addr: fold(commitment), value }` — EXACTLY mirroring NullifierSet::root8()'s circuit-faithful
  encoding (reuse the same helpers split_u64/fold; commitment is a single BabyBear felt per
  effect.rs:276 `NoteCreate { commitment: BabyBear, value: u64 }`, so addr = commitment.as_canonical()).
- On apply_note_create (apply.rs:1549), after validating: `note_commitments.lock().insert(commitment,
  value)` — GROW-ONLY (a commitment is created once; a duplicate is an error, mirroring the double-create
  guard). No removal.
- Feed limb 27 FAITHFULLY: node/turn_proving.rs + blocklace_sync feed `note_commitments.lock().root8()` into
  V9RotationContext.commitments_root (change [u8;32]→Faithful8 like nullifier_root); cell/commitment.rs:1093
  `pre[27]=hash_bytes(ctx.commitments_root)` → `commitments_root.write_lanes([27,74,75,76,77,78,79,80])`
  (the circuit already binds commitmentsRootGroupCol at limb 27+completion lanes — same as nullifier at 26).
- VERIFY like nullifier: a test commitments_root_faithful_8felt_and_cross_node_distinguishing (write
  correctness limbs [27,74..80]==root lanes; non-vacuous; different commitment sets → different roots).
- Persistence/reconstruction: same as nullifier (reconstruct from the persisted commitment set on catchup;
  assert root8()==committed). NO VK regen (geometry already there, only witness values change).
This is a bigger unit than the nullifier mirror (needs the new set + the note-create wiring), but purely
mechanical against the nullifier precedent (commit 9e77654b5). BLOCKED on the Lean commitments-dual landing
(so the Lean commitmentsRoot is the canonical spec the Rust mirrors).
