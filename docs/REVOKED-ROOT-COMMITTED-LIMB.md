# revokedRoot — the committed credential-revocation accumulator (hole #3 / #139)

**Status:** LANDED through Stage E (the gate cutover) — `RevokedSet` (`cell/src/revoked_set.rs`), the
executor registry (`TurnExecutor::note_revoked`, `turn/src/executor/mod.rs:820`), the flag-day circuit
geometry (`revoked_root` = base limb 37, completion 82..=88, `circuit/src/effect_vm/trace_rotated.rs:280-283`),
the commitment twins (`cell/src/commitment.rs:793`, `turn/src/rotation_witness.rs:495`), and the
committed-registry gate labeled `STAGE E / hole #139` in `turn/src/executor/authorize.rs:1338-1360`.
**Named residual (Stage G):** the node's proving call sites pass the canonical EMPTY root
(`empty_revoked_root_8`, byte-identical to a fresh `RevokedSet::root8`) — a live-advanced root does not
yet ride the committed lanes there (`node/src/turn_proving.rs:513,522,658,667`). **Why this exists:**
without a *committed, canonical* revocation root, nobody can **attest to correctly-revoked behavior** —
and trustless validium interchain therefore does not hold. (ember, 2026-07-10.) The rest of this document
is the design record: the hole as found, the decisions, and the staged plan the landing followed.

## 1. The hole (as found; closed by Stage E)

- `turn/src/executor/authorize.rs:1402` — `if let Some(channel_id) = &proof.revocation_channel` — the
  **proof (wire)** supplies which revocation channel the gate consults; `:1317` looks up the node-local
  `self.revocation_channels`.
- `docs/reference/lean-distributed.md` — the deployed rest-hash encoder absorbs the **revocation-channel
  WIRE root**.
- So the committed state *bound* a wire-supplied root but never proved it **canonical**. A malicious node
  supplies an empty/stale revocation root ⇒ the fail-closed gate sees nothing revoked ⇒ the commitment
  faithfully records the lie ⇒ a light client (holding no revocation set) **cannot detect it**.
- The canonical Lean says exactly this: `RecordKernelState.revoked` is *"the committed set of revoked
  credential nullifiers … read off committed state (**NOT** the wire-supplied `NodeAuth.rev`), so the
  fail-closed gate `gateOK` honours revocation"* — tagged **hole #3 / #139** (`RecordKernel.lean`).

**Do not conflate** (I did, at first): the Rust `canonical_revocation_tree_for_set(previously_spent)` is a
tree of **spent nullifiers** (the non-revocation/*freshness* circuit), i.e. the nullifier set — already
accumulator-ized. `revoked` is **credential revocation**, a different set with no runtime registry at all.
Also distinct: **delegation** revocation already has a light-client foil (`delegation_epoch` bumped by
`apply_revoke_delegation`, folded into the canonical state commitment — the "pale ghost" mechanism).
**Credential** revocation has no such foil. That is the gap.

## 2. What the canonical Lean already assumes

`NullifierAccumulatorKernelBridge.toNfAccState k = { nullifierRoot := k.nullifierRoot, revokedRoot :=
k.revokedRoot }` — `revokedRoot` is **already modeled on the same `Heap8Scheme` accumulator as
`nullifierRoot`**, and `kernel_revoked_gate_fails` proves: *a revoked `credNul` admits NO non-membership
witness against `revokedRoot` ⇒ the revocation gate cannot pass* (fail-closed). `RecordKernelState` carries
`revokedRoot : Fin 8 → ℤ` and `RH`/`RestHashIffFrame` absorbs it. **The canonical side
is done**, and the runtime ghost has caught up to it (Stages A–E, header) — same pattern as
nullifier/commitments.

## 3. The design (ember-approved)

**Uniform accumulator.** `revoked` joins `nullifier` + `commitments` on the SAME deployed
`CanonicalHeapTree8` (arity-16 sorted-Poseidon2) — one proven primitive, one gate, and the shape the Lean
already models. New `cell/src/revoked_set.rs`: `RevokedSet` — a grow-only `(credNul → value)` map,
`root8() -> Faithful8`, mirroring `NullifierSet`/`CommitmentSet` exactly.

**Leaf value — DECIDED (ember, 2026-07-10): `value = revocation_height`.** The nullifier leaf's `value` is
load-bearing (the note value, `PI[38]`, "the audit felt"). Credential revocation has no published amount,
and the Lean gate needs only membership (`credNul ∈ keysOf8 revokedRoot`); since no revoked-credential
circuit gate exists yet, we chose. `revocation_height` is the audit felt — *when* the credential was revoked:
auditable, monotone, and non-degenerate so the completion lanes stay non-vacuous (a `value = 1` presence
marker would throw the "when" away). Leaf: `HeapLeaf { addr: fold_bytes32_to_bb(credNul), value:
split_u64(revocation_height).0 }` — the SAME encoding `NullifierSet`/`CommitmentSet` use, via the circuit's
own exported helpers so it cannot drift. The Stage-C circuit grow-gate MUST insert this exact leaf; the
differential tooth (Rust `root8()` == in-circuit after-root) then holds by construction and is tested.

**Runtime registry.** `note_revoked: Mutex<RevokedSet>` on `TurnExecutor` (beside `note_nullifiers` /
`note_commitments`). `cap_revoke` / `Effect::RevokeCapability` inserts the revoked `credNul`. Rollback wired
(a failed turn must not leave a phantom revocation). The per-cell cap **tombstone** (limb 25 `cap_root`)
stays — it is capability-slot revocation, orthogonal to the credential registry.

**Gate reads COMMITTED state.** The landed shape (Stage E, `authorize.rs:1338-1360` and the bearer-cap
mirror at `:1430`): the node-local `revocation_channels` check is KEPT as a fast advisory/liveness path,
and BESIDE it the gate reads the **committed registry `note_revoked`** — deterministic from the finalized
turns, so a re-executor reproduces it and a node that skips the check commits a divergent state consensus
rejects. Two domain-separated keys are checked: `cred_nul(provenance)` and `chan_nul(token)`. This is the
hole-#139 closure — the wire-channel consult was subordinated to advisory, not retired (the original
design's "retire the wire root" was narrowed at landing; the committed check is what the attestation
rests on).

**Committed geometry (flag-day; VK regen is cheap per ember).** Every faithful-8-felt group is
`(lane-0 in the base region, 7 completion felts in 37..87)`. Base limbs 0..36 are FULL
(`cells_root · r0..r23 · cap_root(25) · nullifier(26) · commitments(27) · heap(28) · lifecycle · epoch ·
committed_height · lifecycle_disc · perms_digest · vk_digest · mode · fields_root(36)`); completion 37..87
has exactly **7 free (81..87)**. So: **widen the base 37→38**, `revoked_root` = base limb **37**, shifting
completion→38..88, carrier→89..112, fields→113..168, pad→169, `V9_NUM_PRE_LIMBS` 169→**170**. Group column
`(37, 82..88)`. Every index ≥37 shifts +1 (mechanical, `sg`-sweepable). Chosen over the zero-churn "append
lane-0 at 169" hack because `revoked_root` IS a base root and the base region is where the circuit expresses
that — keeps `preLimbsAt` honest.

**Landing divergence (tail only).** The landed layout follows this plan through group column, carrier
89..=112, and fields 113..=168, but the tail was widened at landing: limbs 169..=175 are a circuit-only
`cells_root` 8-felt completion reservation (zero in the producer, filled by the createCell trace generator,
placed there to keep it off `revoked_root`'s committed group at 82..=88 — the relocation is
`circuit/src/effect_vm/trace_rotated.rs:92`), the two zero pads sit at 176..=177 (landing body `[4..177]` =
174 = 58×3, the clean-3-grouping discipline), and `V9_NUM_PRE_LIMBS` = **178**, not 170
(`cell/src/commitment.rs:748-757`; `turn/src/rotation_witness.rs:64-70`).

## 3b. THE CRYSTALLIZED DESIGN (after 4 read-only scholars, 2026-07-10) — smaller than it looked

**The scholars' verdict.** Lean PROVES the refusal teeth (`gateOK_revoked_fails`, `kernel_revoked_gate_fails`,
`id_revoked_rejected_forever` — all `#assert_axioms`-clean, genuinely two-valued via
`witness_inhabited_of_bindings`) AND PROVES the registry is frame-invariant (`execFullA_revoked_eq`: *"No
current effect grows it"*). The `⊆` "grow-only" theorem is proved BY REFLEXIVITY. `cap_revoke`,
`revokeCredentialAcc`, and "the MDB root" are COMMENTS WITH NO DEFS, on both sides. **A perfect lock on an
empty registry.** The reader is right; the writer was never built.

**The semantics were already right in the circuit.** The circuit crate's `dsl/revocation.rs` +
`non_revocation_witness.rs` proved non-membership of an **`ancestor_hash`** against
`[revocation_root, queried_item]`. ⚑ Both files are DELETED (`d40f0b78a`) — hole #139 was closed
not by widening that root but by retiring the whole 1-felt rail in favour of the limb-26
`.absent` map-op, whose root is already the committed 8-felt one. That is seL4 MDB `revoke`-tears-down-the-subtree, achieved the cheap way:
each cap proves NO ANCESTOR OF MINE IS REVOKED. Revoking a parent kills descendants with ONE insert — no
subtree walk, no O(N), and the executor never needs the CDT. **The ONLY defect: `revocation_root` is a
wire-supplied single `BabyBear` PI instead of the committed 8-felt root.** That is the entirety of hole #139.

**DECISIONS (ember, 2026-07-10):**
- **Identity `credNul` = the capability instance's derivation-node / provenance hash** — the same
  `ancestor_hash` the circuit already queries (`Poseidon2(cell ‖ slot ‖ parent_hash ‖ derivation_type)` /
  `DerivationNode::hash()` which also folds `created_at ‖ created_by_turn`). **NOT `(cell, slot)`**: slots are
  REUSED after revoke (`derivation.rs:189-190`), so `(cell,slot)` keying makes a revoke-then-regrant inherit
  the revoked identity and permanently poison the slot. **NOT `breadstuff`**: caller-supplied, defaults None,
  already overloaded as a channel_id (`apply.rs:1911`).
- **Batch revoke, without inheriting coarseness.** TWO key-kinds in ONE accumulator, DOMAIN-SEPARATED:
  `credNul = H("dregg-cred-revocation-v1" ‖ provenance_hash)` and
  `chanNul = H("dregg-chan-revocation-v1" ‖ channel_id)`. The gate checks non-membership of BOTH (a cap
  presents its provenance hash, and its channel_id if it names one). Individual revoke = one provenance
  insert; batch revoke = one channel insert killing every subscriber at O(1). This batching is INTENTIONAL
  (caps opt in by subscribing) — unlike `delegation_epoch`'s COLLATERAL coarseness (one bump stales every
  earlier cap from that grantor, targeted or not).
- **Leaf value = `revocation_height`** (the audit felt). `RevokedSet` (Stage A) takes all of this
  unchanged: `[u8;32] -> u64`.
- **`gatedActionInvG` MUST gain the `revocationGate` conjunct — LANDED.** `gateOK` is now
  `credentialValidG && capAuthorityG && caveatsDischarged && revocationGate`
  (`FullForestAuth.lean:490`), and `gatedActionInvG` ANDs all FOUR conjuncts (`:1030-1034`;
  `revocationGate` = `na.credNul ∉ s.kernel.revoked`, the COMMITTED registry, fail-closed). A committed
  node therefore attests "was not revoked" — this was as load-bearing as the registry itself for ember's
  attestation/validium goal.
- **Non-vacuity is the acceptance test.** Today every revocation theorem takes `credNul ∈ revoked` as a
  HYPOTHESIS, discharged only by hand-built fixtures. After this campaign, an ACTION must discharge it.

## 4. Stages (each verified before the next; never leave the tree red)

- **A ✅ LANDED** — `RevokedSet` primitive + `root8()` (`cell/src/revoked_set.rs`), the circuit's own
  exported leaf encoding so it cannot drift.
- **B ✅ LANDED** — Executor registry: `note_revoked` (`turn/src/executor/mod.rs:820`) + the
  `cap_revoke` insert at `revocation_height` + journaled rollback (`turn/src/executor/apply.rs:803-827`;
  rollback threaded through `atomic.rs` / `bridge_ledger.rs`).
- **C ✅ LANDED** — Circuit AIR: `B_REVOKED_ROOT = 37` with the 8-felt group at `(37, 82..=88)`
  (`circuit/src/effect_vm/trace_rotated.rs:280-283,1819`); every index ≥37 shifted (+1), Lean
  `EffectVmEmitRotationV3` mirrors it.
- **D ✅ LANDED** — Rust commitment twins: `V9RotationContext.revoked_root: Faithful8`
  (`cell/src/commitment.rs:793`) and `write_lanes(&mut pre_limbs, [37, 82..=88])`
  (`turn/src/rotation_witness.rs:495`).
- **E ✅ LANDED** — Gate cutover: the committed-registry check labeled `STAGE E / hole #139` in
  `authorize.rs` (see §3 for the landed shape — advisory channel check kept beside it). **This is the
  hole-#139 closure** — the one stage that changes what the deployed executor *trusts*.
- **F ✅ LANDED** — the deployed descriptor geometry carries the post-flag-day limb layout (the
  Lean-emitted descriptors and the trace constants agree on 37 / 82..=88).
- **G ◻ NAMED RESIDUAL** — Live root threading: the proving call sites in `node/src/turn_proving.rs`
  pass `empty_revoked_root_8()` (canonical empty root, byte-identical to a fresh `RevokedSet::root8`,
  and COMMITTED — so the lanes are honest for the empty registry); a live-advanced root after an actual
  revocation does not yet ride those lanes, and the cross-node differential tests mirroring nullifier's
  are with it.

## 5. Why this matters (the payoff)

With `revokedRoot` committed + the gate reading it (both landed): a light client verifies from
commitment+proof alone that (i) revocations accumulated correctly and (ii) the turn honoured them. That
yields **attestable correctly-revoked behavior**, and with it **trustless validium-based interchain** — a
remote chain can verify dregg state transitions without trusting dregg's nodes about revocation.
Enforcement ≠ attestability; the full payoff arrives when the Stage-G residual closes and a
live-advanced root rides the committed lanes.
