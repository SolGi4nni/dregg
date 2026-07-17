# Bridge Architecture & Soundness

Three questions about the Solana → dregg bridge, answered against the code at HEAD:

1. How invasive is the bridge to dregg **core**?
2. Is the existing **Custom-VK** machinery enough for "different kinds of recursive custom circuits," or do we need an architecture extension?
3. What happens if **multiple parties bridge Solana into dregg at once** — can it double-mint / break conservation / race?

This started as an analysis + a design. **The concurrency-safe ledger designed in §3 is now BUILT** —
`TurnExecutor::bridge_mint_against_lock` (`turn/src/executor/bridge_ledger.rs`) performs the whole bridge
mint over committed state (consume-once `lock_nullifier` in the committed `note_nullifiers` set + committed
mirror-ledger cell), with the per-relayer RAM path superseded. The concurrent-relayer double-mint hole §3
described is **closed and regression-tested** (`bridge/tests/committed_double_mint.rs`, 4 green tests). The
one remaining honest gap is the **in-circuit foreign-proof binding** (§4, the `EffectVmEmitBridgeMint`
HONEST BOUNDARY): a pure light client witnesses the balance credit but not yet the backing — that closure is
a recursive-verify VK epoch, not built here.

---

## 1. Invasiveness — the bridge is NOT core-invasive

**Verdict: the bridge does not touch the kernel or the circuit at all. It is a pure library that *produces* ordinary kernel effects.**

The entire Solana bridge lives in `bridge/src/{solana_mirror,solana_trustless,solana_consensus,solana_wire,solana_provenance}.rs`. Nothing in `bridge/` is referenced by the executor (`turn/`) or the circuit (`circuit/`); the call graph is one-directional — bridge depends on `dregg_turn::action::Effect`, never the reverse. A grep for `MirrorState` / `mint_against_lock` / `credit_lock` / `verify_lock_proof_consensus` outside `bridge/src/` returns nothing: the bridge is a leaf.

What the bridge actually emits:

- `MirrorState::credit_lock` (`solana_mirror.rs:366-408`) returns a **plain `Effect::Mint { target, slot: 0, amount }`** (line 400-404). That is the *only* kernel coupling on the inbound path.
- `MirrorState::redeem` (`solana_mirror.rs:415-455`) returns a plain `Effect::Burn` plus a `SolanaUnlockRequest` (Solana-side, off-dregg).
- Payment of the mirrored asset routes through the existing `dregg_payable::resolve_pay` → `Effect::Transfer` rail (`solana_mirror.rs:649-667`), with no bridge-specific verb.

The module docstring states it directly: *"No new kernel verb is introduced"* (`solana_mirror.rs:37`).

**Exactly what touches core:**

| Surface | Status |
|---|---|
| `Effect::Mint` (verb) | Pre-existing kernel verb (`turn/src/action.rs:1761`, applied at `executor/apply.rs:249,2765`). Bridge is just one *caller*. |
| Mint authority gate | `holds_mint_authority` (`apply.rs:2734`) — a control-grade cap carrying `EFFECT_MINT` over the asset's **issuer well**. Bridge must hold this cap like any other minter; it gets no special path. |
| Per-asset conservation | The mint debits the issuer well and credits the recipient, Σδ=0 per asset per turn (`apply.rs:2775-2781`, the sign-flipped dual of burn). Unchanged by the bridge. |
| `AssetId := issuer-cell` | The mirror's asset is an ordinary `AssetId` = its issuer well (`MirrorConfig.asset`, `solana_mirror.rs:170-171`). |

Everything else — attestation verification, Solana consensus arithmetic, replay dedup, the `live_supply ≤ currently_locked` invariant, lock/redeem accounting — is **bridge-local** and lives entirely inside `MirrorState` / `solana_consensus`. The kernel never sees a Solana fact; it sees a well-authorized `Effect::Mint`.

Consequence (sets up §3): **the kernel cannot distinguish a bridge mint from any other mint by a holder of that issuer well's mint-cap.** The backing relationship to Solana exists *only* in the bridge's off-chain `MirrorState`.

There is also a *separate* core verb `Effect::BridgeMint { portable_proof }` (`action.rs:1115`) for
cross-*federation* note bridging. **Precise posture (corrected — do not over-read "in-circuit"):** only
the *balance credit* of a bridge mint is in the deployed per-turn VK — its trace body credits
`value_lo`, byte-identical to a plain `Effect::Mint` (`circuit/src/effect_vm/trace.rs`,
`Effect::BridgeMint`). The two backing guarantees are **executor-side**, NOT in the per-turn AIR a pure
light client checks:

- the **foreign note-spend STARK** is verified by the executor (`apply_bridge_mint` →
  `verify_note_spend_dsl_full`, `turn/src/executor/apply.rs`); the Lean descriptor
  `EffectVmEmitBridgeMint` names this exactly as the **HONEST BOUNDARY** — "the inbound-value
  attestation is NOT internalized in-circuit … enforced at `execFullA`'s ADMISSION";
- the **nullifier consume-once** rides the committed `note_nullifiers` / `bridged_nullifiers` set
  (`bridge_mint_against_lock`, `apply_bridge_mint`), i.e. committed-state-side, outside the per-turn VK
  view.

So a pure light client witnesses *that a credit happened*, not *that a valid foreign spend backs it* nor
*that the nullifier was consumed exactly once in-proof*. The full-fidelity binding AIR
(`circuit/src/bridge_action_witness.rs`, 18 green teeth) and the recursive foreign-spend verify exist but are
**not folded into the deployed effect-vm VK** — that fold is the named residual in §4 (the in-circuit
foreign-proof VK epoch). The Solana mirror does **not** use `Effect::BridgeMint`; the Solana path uses
plain `Effect::Mint` over the committed mirror ledger (§3).

---

## 2. Custom-VK fitness

### Current (trusted-oracle) bridge: Custom-VK is irrelevant

Today's inbound path verifies a threshold Ed25519 attestation **in Rust, off-circuit** (`SolanaLockAttestation::verify_under`, `solana_mirror.rs:141-146`). The trustless upgrade in `solana_consensus.rs` verifies real Tower-BFT stake-weighted votes + bank-hash binding + accounts-inclusion + PoH — **also entirely in Rust, off-circuit** (`verify_supermajority`, `verify_accounts_inclusion`, `verify_poh_segment`). No dregg proof, no AIR, no VK is involved on either path. So **Custom-VK has nothing to do with the bridge as built** — the consensus check is a trusted/replayable Rust gate that gates an `Effect::Mint`. A light client re-running the Rust check is trusting the relayer's word that the inputs (stake table, votes) are the real Solana ones.

### Future (in-circuit, trustless) bridge: the machinery is *architecturally* ready, but ONE deployment step is needed

The question is whether a Solana light-client **verified inside a dregg proof** (so a light client, not a re-executing validator, witnesses the lock) fits the existing Custom-VK / recursive-fold architecture.

**What already exists and is general enough:**

- `Effect::Custom` carries an **arbitrary** `program_vk_hash: [BabyBear; 8]` + `proof_commitment` (`circuit/src/effect_vm/effect.rs:281-293`). It is a single selector parameterized over *which* program — not one hardcoded circuit.
- `ProgramRegistry` (`circuit/src/dsl/circuit.rs:1285-1359`) is a `HashMap<[u8;32], CellProgram>` with `deploy()` and `iter()` — **multiple** programs, keyed by VK hash, registrable at runtime.
- `verify_proof_bind` (`circuit-prove/src/custom_proof_bind.rs:237-282`) is **generic over `CellProgram`**: it resolves the program by VK-hash projection and calls `program.verify_transition(public_inputs, proof_bytes)`. A Solana light-client compiled to a `CircuitDescriptor`/`CellProgram` would verify through this engine with no new machinery.
- The Lean design is explicitly open-ended: *"any future kind registers (vk, circuit, relation, bridge) and inherits the cascade"* (`metatheory/Dregg2.lean:152`); the apex routes through `proofBind_bound` / `proofBind_determined` under a named `EngineBinding E` carrier (`metatheory/Dregg2/Circuit/CustomApex.lean:28-48`).

So: **Custom-VK supports arbitrary / multiple recursive custom circuits, not one fixed kind.** Compiling a Solana light client to a `CellProgram` and deploying it to the registry is *engineering*, not an architecture extension.

**What is NOT yet deployed (the honest gap):**

1. **The in-AIR `proof_bind` constraint is currently vacuous.** The deployed `customVmDescriptor` treats `ProofBind` as a bounds/declaration check, not the genuine recursive verify; the real program-correctness recursion runs in the *external* engine (`circuit/src/effect_vm/trace_rotated.rs:3267`; `docs/deos/CUSTOM-VK-AUTHORIZATION.md:173-181` — the custom sub-proof is **not folded into the IVC chain**). The genuine in-circuit verifier exists in Lean as `VmConstraint2.holdsAtStaged` (`CustomApex.lean:90-98`) — `proofBind` upgraded from `True` to `ProofBind.boundAt E env` — but it is **staged, not flipped**. Deploying it is a **gated VK epoch** (the same shape as the parked umem VK epoch), not new architecture.
2. **The `custom_proof_commitment` column is 4 felts (~62-bit), not 8** (`custom_proof_bind.rs:52-70`). A new foreign verifier sharpens the collision concern; the 4→8-felt lift should ride the same gated VK epoch (matching `.docs-history-noclaude/FAITHFUL-STATE-COMMITMENT.md`'s 8-felt floor).
3. **The IVC fold is dregg-turn-specific** (`circuit-prove/src/ivc_turn_chain.rs` folds `EffectVmDescriptorAir` leaves only). It is *not* a generic foreign-proof folder. For a Solana verifier this is fine — it rides the per-turn `Effect::Custom` ProofBind, which is verified inline, not folded — but if we ever wanted the foreign proof *inside* the recursive whole-chain fold, that would be a real extension.

**Is "the Custom-VK stuff we have good enough"?**

- For an **inline** in-circuit foreign verifier (verify a Solana-light-client proof as one `Effect::Custom` ProofBind per bridge turn): **YES, the architecture is sufficient — but it is gated behind one undeployed step** (flip `proofBind` from vacuous to `boundAt` + the 4→8-felt commitment lift, in a single gated VK epoch). No new selector, no new registry, no new gadget. The named extension, if you insist on naming one, is: *deploy the staged recursive-verify constraint that already exists in Lean.*
- For folding the foreign proof into the **recursive whole-chain IVC**: **NO — that needs an extension** (a generic foreign-leaf folder; today IVC leaves are dregg's own EffectVM AIR only). This is not required for a trustless Solana bridge and should not be pursued for it.

Recommendation: a trustless in-circuit Solana bridge is a `CellProgram` + the gated `proofBind` VK epoch. Do not invent a new effect or a new recursion layer for it.

---

## 3. Concurrency — the (now-closed) double-mint risk: per-relayer RAM → committed consume-once

### The trace

`MirrorState` holds the entire backing relationship in **in-memory, per-instance** fields (`solana_mirror.rs:255-267`):

- `currently_locked` — Solana-side locked supply (a `u64`),
- `live_supply` — circulating mirror supply (a `u64`),
- `seen_locks: BTreeSet<[u8;32]>` — the replay/double-mint dedup set,
- the invariant `live_supply ≤ currently_locked` (checked at `credit_lock`, `solana_mirror.rs:385-391`).

**None of this is committed dregg state.** It is not a cell, not a field, not a nullifier set — it is a Rust struct owned by whatever relayer process holds the mirror's mint-cap. The kernel's `apply_mint` (§1) checks only the mint-cap and per-asset Σδ=0; it has **no knowledge of `lock_id`, `currently_locked`, or `seen_locks`.**

Now run N relayers (or one relayer restarted from a stale snapshot), each holding a copy of (or a shared) mint-cap over the same mirror issuer well, each with its **own** `MirrorState`:

1. The same Solana lock event (one `lock_id`, one real backing of `amount`) is observed by relayer A and relayer B.
2. A's `seen_locks` does not contain `lock_id` → A mints `amount`. B's *separate* `seen_locks` also does not contain `lock_id` → B mints `amount`.
3. Two `Effect::Mint`s land. Each is independently well-authorized; each conserves Σδ=0 against the issuer well locally. **The executor's per-turn serialization happily applies both** — it serializes turns and enforces per-asset conservation *within dregg*, but the issuer well is a sign-flipped supply sink with no global cap, so "minting twice" is two perfectly valid kernel transitions.
4. Result: `2·amount` mirror-$DREGG now circulates against `amount` of real Solana backing. `live_supply > currently_locked` **globally**, even though each instance's local view satisfies its own invariant. Conservation against the real backing is broken; redemptions will eventually fail to unlock.

**The hole is precisely that the locked-supply ledger and the `lock_id` dedup are bridge-local and per-instance, not a single committed source of truth.** Per-turn serialization does not save it, because the kernel never sees the cross-instance accounting. The `lock_id` is a replay nonce *within one `MirrorState`* (`solana_mirror.rs:342,372`), not a globally-consumed-once token.

### Verdict — the hole was real; it is now CLOSED in committed state

The per-relayer-RAM analysis below was correct: with `MirrorState`'s in-memory `seen_locks`,
concurrent/duplicated bridge instances **could** double-mint. **This is now fixed.** The fix is the
design in "The concurrency-safe design" immediately below, BUILT as
`TurnExecutor::bridge_mint_against_lock` (`turn/src/executor/bridge_ledger.rs`): the `lock_id` becomes a
domain-separated consume-once **`lock_nullifier`** (`bridge/src/solana_mirror.rs::lock_nullifier`) gated
against the committed `note_nullifiers` set with the same atomic contains-then-insert NoteSpend/BridgeMint
ride, and `currently_locked`/`live_supply` live in a committed mirror-ledger cell. `MirrorState::verify_lock`
now returns a `VerifiedLock` **without mutating per-relayer RAM** — the committed state is the authority,
the in-memory `seen_locks` is a non-authoritative cache. Regression-tested green in
`bridge/tests/committed_double_mint.rs`: `two_solana_relayers_one_lock_only_one_mint`,
`two_stripe_relayers_one_payment_only_one_mint` (second relayer → `DuplicateLock`),
`solana_distinct_locks_both_mint_and_conserve`, `unauthorized_bridge_mint_is_refused_and_rolls_back`.

**Honest residual (the same boundary as §4):** this consume-once is enforced over *committed state* by a
re-executing validator / the committed nullifier set, NOT yet bound *inside the per-turn AIR*. A pure
light client that runs only the per-turn STARK does not witness the nullifier-consume; that in-circuit
binding is the §4 VK epoch.

### The concurrency-safe design (BUILT — see verdict above)

The fix is to move the two things that must be globally unique — **the locked-supply ledger** and **the `lock_id` consume-once** — out of the relayer's RAM and into **committed dregg state**, gated *inside the mint turn itself*, so the executor's existing per-turn serialization becomes the serialization point for the whole bridge.

dregg already has the exact primitive: the committed **`note_nullifiers`** set used by `Effect::NoteSpend` / `Effect::BridgeMint` (`turn/src/executor/apply.rs:997-1027`) — a sparse-Merkle nullifier set with atomic `contains`-then-`insert`, double-spend rejection, journaled and rollback-safe, and a race-guarded insert (`apply.rs:1004-1027`). This is the cross-federation bridge's defense and it is the template.

**Design — a single committed bridge cell + consume-once lock_id:**

1. **One mirror-ledger cell per mirrored token (the single source of truth).** A dregg cell whose committed fields hold `currently_locked` and `live_supply` for that `spl_mint`. It is part of the committed state root, so every node/light-client sees the same value. There is exactly one such cell per mirror; the relayer's in-memory `MirrorState` becomes a *cache* of it, never the authority.

2. **`lock_id` as a committed consume-once nullifier.** Derive a domain-separated nullifier `nf = H("dregg-solana-lock" ‖ spl_mint ‖ lock_id)` and gate the mint on inserting `nf` into the committed nullifier set (reuse `note_nullifiers`, or a dedicated `bridge_locks` set with the same machinery). The atomic contains-then-insert at `apply.rs:1004-1027` makes a second mint against the same lock **fail-closed regardless of how many relayers race it** — the first turn to commit consumes `nf`; every other turn (this height or any later) is rejected as a double-spend.

3. **Bind the mint to both in one atomic turn.** The bridge mint becomes a turn that, atomically: (a) consumes the `lock_id` nullifier, (b) debits the committed mirror-ledger cell's `currently_locked`/asserts `live_supply + amount ≤ currently_locked` against the *committed* value, and (c) emits the `Effect::Mint`. Because all three are in one turn over committed state, the executor's per-turn serialization is now the global serialization point — there is no cross-instance window. The within-turn chaining is already expressible via `EffectDependency` (`turn/src/binding_proof.rs:93-119`), which binds a producer's `nullifier` output to a consumer effect in the same turn — the existing `NoteSpend → BridgeMint` pattern (`binding_proof.rs:96-102`) is the precedent.

4. **Redeem mirrors it symmetrically:** a redeem turn consumes a `redeem_id` nullifier and credits the committed `currently_locked` back, under `Effect::Burn`.

Under this design, N relayers are **safe and even desirable** (liveness/redundancy): they all race to land the bridge turn, the committed nullifier set lets exactly one win per `lock_id`, and the committed mirror-ledger cell is the single arithmetic source of truth. `live_supply ≤ currently_locked` holds *globally* because it is checked against committed state inside the serialized turn, not against a per-process `u64`.

**Mapping to existing primitives (nothing new to invent):**

| Need | Existing primitive | Location |
|---|---|---|
| Consume-once `lock_id` | committed sparse-Merkle nullifier set, atomic contains+insert, double-spend reject | `executor/apply.rs:997-1027` |
| Single locked-supply ledger | a committed dregg cell with `currently_locked`/`live_supply` fields in the state root | cell fields / committed-heap-root (`Heap.root_binds_get`) |
| Atomic mint-gated-on-nullifier in one turn | within-turn `EffectDependency` chaining (the `NoteSpend → BridgeMint` shape) | `turn/src/binding_proof.rs:93-119` |
| Serialization of competing relayers | the executor's existing per-turn application over the committed ledger | `turn/src/executor/` |

This is a bridge-layer + new-cell-shape change, not a kernel-verb change — it composes `Effect::Mint` with the existing nullifier gate. It is the named follow-up; this document is the analysis that justifies it.

---

## 4. The in-circuit foreign-proof binding (G1) — the named VK-epoch residual

This is the one genuine remaining gap (the under-wired-circuit catalog's G1, the highest
soundness-value money primitive). It is **scrupulously named in-code, not a hidden hole**: the Lean
descriptor `EffectVmEmitBridgeMint` flags the foreign attestation as its **HONEST BOUNDARY**, and the
binding AIR (`circuit/src/bridge_action_witness.rs`) exists, is sound+complete in Lean
(`metatheory/Dregg2/Crypto/Bridge.lean`, `#assert_axioms`-clean under the named `extractable` carrier),
and carries 18 green adversarial teeth — but it is a **standalone sidecar, not folded into the deployed
effect-vm VK**.

**What a pure light client does NOT yet witness** (and a re-executing validator DOES enforce):
1. that a valid **foreign note-spend** with the bound `(nullifier, recipient, dest_federation, amount)`
   ever existed (the backing);
2. that the **nullifier was consumed exactly once** (the in-proof double-mint gate).

**Why this is not a localizable green weld** (and was correctly NOT force-landed):
- Binding the *parameters* at full fidelity (folding `bridge_action_air`'s boundary into the
  `mintVmDescriptor2R24` member) is a **VK-affecting flip of the bridge-mint descriptor**: new PI slots +
  boundary constraints, the Lean `EffectVmEmitBridgeMint`/`mintV3` emission must change, the wide twin
  must change, every producer fills the new aux, the VK fingerprint changes, and the closure apex
  (`CircuitSoundness.lean:453` `lightclient_unfoolable` + the assembled forest) must re-verify clean.
  That is a gated VK epoch, not a one-line weld — even though it touches only the bridge member.
- Witnessing the **backing-existence** (point 1) needs the foreign note-spend STARK **recursively
  verified in-AIR** — the same machinery as G2's `proofBind` flip (`True` → `boundAt`) + the 4→8-felt
  commitment lift. `BRIDGE-ARCHITECTURE-SOUNDNESS` §2 and the Custom-VK apex (`CustomApex.lean`) establish
  the architecture is *sufficient* for this (arbitrary `CellProgram` + generic `verify_proof_bind`), but
  it is gated behind that undeployed recursive-verify epoch. Folding a foreign proof into the recursive
  whole-chain IVC is a further real extension (§2, item 3) and is NOT required here.
- Witnessing the **in-proof consume-once** (point 2) additionally needs the committed `note_nullifiers`
  membership/insertion surfaced into the per-turn commitment the proof binds — today it is a global
  executor structure outside the single-cell effect-vm view.

**The weld plan (the burn-down, in order):**
1. Emit a `bridge_action_air`-style full-fidelity boundary (`nullifier[8] + recipient[8] +
   dest_federation[8] + amount[lo,hi]`) into the bridge-mint descriptor, **additively + staged** beside
   the bare `mintVmDescriptor2R24` (the umem/capacity-satisfaction staging pattern), gated on a witness —
   sound for a witness-holding verifier, no deployed-default VK change. Prove the teeth in Lean + Rust.
2. The gated VK epoch: make the bridge-mint producer thread the witness, commit the welded descriptor as
   the sole accepted bridge-mint form, re-prove the gauntlet, re-verify the closure apex. (Parameter
   binding becomes a pure-LC truth.)
3. Recursive foreign-spend verify (the G2-shaped `proofBind` flip + 4→8-felt lift) for backing-existence,
   and surface the nullifier consume into the per-turn commitment for the in-proof double-mint gate.

Until step 2, a pure light client is protected only for the **balance credit**; the **backing** and
**consume-once** are the re-executing-validator / committed-state posture (sound today, just not
light-client-witnessed). The apex `lightclient_unfoolable` is unchanged and stays `#assert_axioms`-clean
(no circuit/Lean code was touched by this pass — only this doc).

---

## Summary

1. **Invasiveness:** Not core-invasive. The bridge is a leaf library; the only core coupling is that it calls the pre-existing `Effect::Mint` and must hold the issuer well's mint-cap (`holds_mint_authority`). No new verb, no circuit change.
2. **Custom-VK:** Irrelevant to the bridge as built (the consensus check is off-circuit Rust). For a future in-circuit trustless bridge, the Custom-VK machinery is architecturally sufficient (arbitrary programs via `ProgramRegistry` + generic `verify_proof_bind`) but gated behind one undeployed step — flip the staged `proofBind` constraint from vacuous to `boundAt` and lift the commitment 4→8 felts, in a single gated VK epoch. Folding a foreign proof into the recursive whole-chain IVC *would* need a real extension, but a Solana bridge does not require that.
3. **Concurrency (the risk — now CLOSED):** Concurrent/duplicated bridge instances *could* double-mint
   while the locked-supply ledger and `lock_id` dedup were bridge-local, per-process, in-memory. **Fixed**:
   a **single committed mirror-ledger cell** plus a **consume-once `lock_id` nullifier**, both gated inside
   the mint turn (`TurnExecutor::bridge_mint_against_lock`), reusing the committed `note_nullifiers`
   double-spend machinery — the executor's per-turn serialization is now the global serialization point and
   `live_supply ≤ currently_locked` is a committed-state invariant. Green in
   `bridge/tests/committed_double_mint.rs`. Residual: this is committed-state / re-executing-validator
   enforcement, not yet a per-turn-AIR witness (§4).
4. **In-circuit foreign-proof binding (G1, the named residual):** only the *balance credit* of a bridge
   mint is in the deployed per-turn VK; the foreign note-spend STARK verify and the nullifier consume-once
   are executor-side (the `EffectVmEmitBridgeMint` HONEST BOUNDARY). Closing it so a *pure light client*
   witnesses the backing is a gated VK epoch (descriptor flip + recursive foreign-spend verify), not a
   localizable weld — the weld plan is §4. The binding AIR + its 18 teeth already exist; the fold does not.
