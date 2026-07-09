# effect-vocabulary — the closed verb set and its six-color linearity (grounded at HEAD)

*A file:line-grounded record of dregg's effect vocabulary: the complete `enum Effect`
catalog, the `LinearityClass` color each variant carries, and the authority gate the
executor holds it to. Present-tense what-is; every row points at code. Companion to
`docs/reference/turns.md` (what a turn is) and `docs/reference/lean-conserve.md` (the
conservation metatheory this coloring feeds).*

## What the vocabulary IS

A turn's power is a `Vec<Effect>`. `Effect` (`turn/src/action.rs:1061`) is a **closed**
enum — the only verbs the executor can apply. There is no "raw write" escape hatch: an act
that is not one of these variants is *not expressible*, and an act you are not authorized
for is refused before it applies. Closure is load-bearing twice over:

- **Authority.** `determine_required_permissions` (`turn/src/executor/authorize.rs:2182`) is
  an **exhaustive match with NO `_ =>` catch-all** (the CAP-1 discipline, comment at
  `authorize.rs:2206`): every variant names its authority decision, so a newly-added effect
  *cannot compile* until someone decides how it is gated. The historical hole was a trailing
  `_ => {}` that let `SetProgram`/`MakeSovereign`/`CellSeal`/`CellDestroy` fall through to the
  permissionless `Access` gate.
- **Conservation.** Each variant carries a `LinearityClass` color (`Effect::linearity`,
  `action.rs:1807`) — *how* it is permitted to move a conserved quantity. The conservation
  checker reads the color to know whether a delta must be paired to zero, may only grow, or
  is a disclosed break.

## The six colors (`LinearityClass`)

The colors are defined identically in Rust (`action.rs:919-996`, the `LinearityClass` enum +
its `requires_pairing`/`is_disclosed_non_conservation` helpers) and in the Lean source of
truth `metatheory/Dregg2/Spec/Conservation.lean:78-96`. Exactly six; both classifiers are
exhaustive matches with no default arm, so a new color cannot compile until it answers "must
it have a paired sibling?" and "is it a disclosed non-conservation?".

| Color | Meaning (Conservation.lean) | Conservation obligation |
|---|---|---|
| **Conservative** | Paired conservation — the per-domain deltas must sum to `0` (`Σδ = 0`); a debit must be matched by an equal credit (the move discipline). `Conservation.lean:79-81` | The one color for which `requires_paired_sibling = true` (`Conservation.lean:104-110`, `theorem requires_paired_sibling_iff:127`). |
| **Monotonic** | Monotone growth — the quantity may only increase (an append-only counter, a monotone clock); never decreases, no paired sibling. `Conservation.lean:82-84` | Stands alone; non-decreasing. |
| **Terminal** | One-way / terminal — a state transitions out but never back (a finalized/consumed marker); irreversible, unpaired. `Conservation.lean:85-87` | Stands alone; no inverse. |
| **Generative** | Ex-nihilo creation (a mint) — NOT conserved, but the non-conservation is *disclosed* (bound into the receipt). `Conservation.lean:88-90` | `is_disclosed_non_conservation = true`; the created amount is un-strippable receipt data. |
| **Annihilative** | Destruction (a burn) — NOT conserved, but, like Generative, disclosed in the receipt. `Conservation.lean:91-93` | `is_disclosed_non_conservation = true` (`Conservation.lean:116-122`, `theorem …_iff:132`). |
| **Neutral** | No delta — touches no conserved quantity in any domain (setting an opaque metadata field). The trivial color. `Conservation.lean:94-96` | None. |

The two classifiers are provably **disjoint** — nothing both requires a paired sibling and is
a disclosed non-conservation (`theorem paired_and_disclosed_exclusive`,
`Conservation.lean:139`). Conservation runs per-domain (`balance` / `note`-per-asset / `gas` /
`crossCell`, `Conservation.lean:189-198`), parametric over a value monoid so cleartext (`ℤ`)
and Pedersen-committed balances obey the *same* `Σδ = 0` law.

## The catalog

33 variants. **Color** is cited to its `Effect::linearity` arm (`action.rs`); the **fields**
column is abbreviated; **authority gate** names the `action.target` permission from
`determine_required_permissions` (or "self-auth"/"cross-cell"/"cap-slot" when the gate lives
in `apply.rs`), plus the effect-mask facet from `effect_kind_mask` (`action.rs:2590`) that a
faceted capability checks under `ExerciseViaCapability`.

| Effect (decl line) | Fields (brief) | Color (linearity line) | Authority gate |
|---|---|---|---|
| `Transfer` (1069) | `from, to, amount` | **Conservative** (1810) | `Send` on `from` when `from == target`; cross-cell `Send` on `from` + `Receive`-check on `to` (`authorize.rs:2230,263`). Facet `EFFECT_TRANSFER`. |
| `NoteSpend` (1137) | `nullifier, note_tree_root, value, asset_type, spending_proof, value_commitment?` | **Conservative** (1815) | Self-auth: ZK spending proof + nullifier membership IS the authority (`authorize.rs:2338`). Facet `EFFECT_NOTE_SPEND`. |
| `NoteCreate` (1159) | `commitment, value, asset_type, encrypted_note, value_commitment?, range_proof?` | **Conservative** (1816) | Self-auth (paired with sibling spend; conservation checked across the turn). Facet `EFFECT_NOTE_CREATE`. |
| `ShieldedTransfer` (1542) | `payload: ShieldedTransferPayload` | **Conservative** (1820) | Self-auth: hidden STARK proof of note ownership IS the authority (`action.rs:1531`). Facet `EFFECT_NOTE_SPEND`. |
| `IncrementNonce` (1085) | `cell` | **Monotonic** (1837) | `IncrementNonce` perm on target (`authorize.rs:2243`). Facet `EFFECT_INCREMENT_NONCE`. |
| `Refusal` (1311) | `cell, offered_action_commitment, refusal_reason, proof_witness_index` | **Monotonic** (1844) | `SetState` perm — overwrites the audit slot + bumps nonce (`authorize.rs:2256`). Facet `EFFECT_REFUSAL`. |
| `RevokeCapability` (1081) | `cell, slot` | **Terminal** (1847) | `Delegate` perm on target (`authorize.rs:2263`). Facet `EFFECT_REVOKE_CAPABILITY`. |
| `RevokeDelegation` (1203) | `child` | **Terminal** (1848) | Cap-graph: parent bumps its own epoch (`authorize.rs:2345`). Facet `EFFECT_DELEGATION_OPS`. |
| `CellDestroy` (1369) | `target, certificate` | **Terminal** (1855) | `SetPermissions` floor ("Lifecycle", `authorize.rs:2321`). Facet `EFFECT_LIFECYCLE_OPS`. |
| `MakeSovereign` (1249) | `cell` | **Terminal** (1859) | `SetVerificationKey` floor — a hosting/accounting-model edit (`authorize.rs:2308`). Facet `EFFECT_SOVEREIGN_OPS`. |
| `ReceiptArchive` (1416) | `prefix_end_height, checkpoint` | **Terminal** (1863) | Receipt-only; attestation `cell_id` must match target (`authorize.rs:2333`). Facet `EFFECT_LIFECYCLE_OPS`. |
| `AttenuateCapability` (1396) | `cell, slot, narrower_permissions, narrower_effects?, narrower_expiry?` | **Terminal** (1866) | Cap-slot: actor's own c-list slot; narrow-only, widening rejected (`authorize.rs:2345`). Facet `EFFECT_ATTENUATE_CAPABILITY`. |
| `CellSeal` (1351) | `target, reason` | **Terminal** (1874) | `SetPermissions` floor ("Lifecycle", `authorize.rs:2321`). Facet `EFFECT_LIFECYCLE_OPS`. |
| `CellUnseal` (1360) | `target` | **Terminal** (1875) | `SetPermissions` floor (same arm). Facet `EFFECT_LIFECYCLE_OPS`. |
| `React` (1471) | `pending_id, condition, resolution_proof, wake` | **Terminal** (1918) | One-shot nullifier spend; the proof discharges `condition`; `wake` hash must equal `pending_id` (`authorize.rs:2350`). Facet `EFFECT_REACTIVE_OPS`. |
| `BridgeMint` (1214) | `portable_proof` | **Generative** (1881) | Self-auth: portable STARK proof against trusted federation roots (`authorize.rs:2338`). Facet `EFFECT_BRIDGE_OPS`. |
| `CreateCell` (1087) | `public_key, token_id, balance` | **Generative** (1882) | Fresh cell — no victim to gate (`authorize.rs:2335`). Facet `EFFECT_CREATE_CELL`. |
| `CreateCellFromFactory` (1258) | `factory_vk, owner_pubkey, token_id, params` | **Generative** (1883) | Factory constraints validated in-handler (`authorize.rs:2335`). Facet `EFFECT_CREATE_CELL`. |
| `SpawnWithDelegation` (1180) | `child_public_key, child_token_id, max_staleness` | **Generative** (1884) | Fresh child; snapshot delegation validated in-handler (`authorize.rs:2335`). Facet `EFFECT_DELEGATION_OPS`. |
| `GrantCapability` (1075) | `from, to, cap` | **Generative** (1893) | `Delegate` perm on target (`authorize.rs:2263`). Facet `EFFECT_GRANT_CAPABILITY`. |
| `Introduce` (1220) | `introducer, recipient, target, permissions` | **Generative** (1894) | Cap-graph three-party introduction (`authorize.rs:2345`). Facet `EFFECT_INTRODUCE`. |
| `Promise` (1440) | `cell, resolution_condition, wake, timeout_height` | **Generative** (1900) | Sub-turn `wake` carries its own auth; mints a promise-hole (`authorize.rs:2350`). Facet `EFFECT_REACTIVE_OPS`. |
| `Notify` (1454) | `from, to, wake, resolution_condition, timeout_height` | **Generative** (1901) | Deposits a hole in `to`'s registry; `wake` carries its own auth (`authorize.rs:2350`). Facet `EFFECT_REACTIVE_OPS`. |
| `Mint` (1506) | `target, slot, amount` | **Generative** (1910) | Control-grade cap over the issuer WELL carrying the `EFFECT_MINT` facet — the Rust image of Lean `mintAuthorizedB`; NOT bare ownership (`apply.rs:2955-2998`). Facet `EFFECT_MINT`. |
| `Burn` (1382) | `target, slot, amount` | **Annihilative** (1904) | Apply-gated: self-burn permissionless; cross-cell burn `Send`-gated on the holder (`authorize.rs:2342`). Facet `EFFECT_BURN`. |
| `SetField` (1063) | `cell, index, value` | **Neutral** (1921) | `SetState` perm on target (`authorize.rs:2237`). Facet `EFFECT_SET_FIELD`. |
| `EmitEvent` (1083) | `cell, event` | **Neutral** (1922) | Receipt-only; no ledger mutation (`authorize.rs:2333`). Facet `EFFECT_EMIT_EVENT`. |
| `SetPermissions` (1099) | `cell, new_permissions` | **Neutral** (1923) | `SetPermissions` perm; applied LAST in the action against snapshotted perms (`action.rs:1094`, `authorize.rs:2271`). Facet `EFFECT_SET_PERMISSIONS`. |
| `SetVerificationKey` (1106) | `cell, new_vk?` | **Neutral** (1924) | `SetVerificationKey` perm; applied LAST (`authorize.rs:2280`). Facet `EFFECT_SET_VERIFICATION_KEY`. |
| `SetProgram` (1130) | `cell, program` | **Neutral** (1925) | `SetVerificationKey` perm (program + VK are one authority surface); applied LAST (`authorize.rs:2295`). Facet `EFFECT_SET_PROGRAM`. |
| `RefreshDelegation` (1190) | `child, snapshot` | **Neutral** (1926) | Self-refresh (`child == target`); executor derives + refuses a mismatching snapshot (`authorize.rs:2345`). Facet `EFFECT_DELEGATION_OPS`. |
| `PipelinedSend` (1226) | `target: EventualRef, action: Box<Action>` | **Neutral** (1927) | Resolved sub-action carries its own authorization (`authorize.rs:2350`). Facet `EFFECT_INTRODUCE`. |
| `ExerciseViaCapability` (1238) | `cap_slot, inner_effects` | **Neutral** (1928) | Cap-slot: actor's held c-list slot; enforces the cap permission-level AND the `allowed_effects` facet on *every* inner effect (`authorize.rs:2345`). Facet `EFFECT_ALL`. |

## Honest notes

- **`Mint` is `Generative`, not `Conservative` — even though its own doc says it "conserves
  exactly."** The variant doc (`action.rs:1489-1494`) states a mint *conserves* per-asset
  (`Σδ = 0`): the issuer well is debited (`−supply` grows) as the holder is credited. But its
  linearity color is `Generative` (`action.rs:1910`), justified by the inline comment
  (`action.rs:1906-1909`): *from the holder's point of view* value appears without a paired
  consumer *in the same turn*; the well-debit is the conserving dual but the color is assigned
  from the disclosed-appearance view. So `Mint` is the color-dual of `Burn`'s `Annihilative`.
  This is a genuine subtlety — the conservation *fact* and the linearity *color* are measured
  from different vantage points. (`Mint` is also physically the last-appended enum variant, so
  its `postcard` discriminant does not shift the durable codec, `action.rs:1502`.)

- **`React` sits under the `Annihilative` comment block but is `Terminal`.** In the match,
  `React`'s arm (`action.rs:1918`) follows `Burn`/`Mint` yet is colored `Terminal`: it spends
  a promise-hole nullifier once with no inverse and no monetary delta, so it is a one-way
  transition, *not* a disclosed non-conservation (`action.rs:1912-1917`). The promise-hole IS
  a nullifier — `React` spends it into the same production `note_nullifiers` set that gates
  `NoteSpend` double-spends (`action.rs:1430-1435`).

- **Reactive verbs (`Promise`/`Notify`/`React`) are the async-coordination track.** They are
  a distinct family (`action.rs:1425`) whose kernel weld lives in `crate::reactive`; a
  `Promise`/`Notify` mints a hole (Generative) and the later `React` (Terminal) discharges it
  — a create/consume pair split *across turns*, so they are not siblings the conservation
  checker pairs within one turn.

- **Named circuit-witness seams (executor enforces; light-client descriptor owed).** Two
  variants apply and are conserved live but have no in-circuit descriptor rung yet, so a pure
  light client (not a re-executor) does not yet witness them — binding them is VK-affecting
  and ember-gated: `SetProgram` (`action.rs:1125-1129`) and `ShieldedTransfer`
  (`action.rs:1537-1541`). These are named follow-ups, not holes in the executor gate.

- **Retired verbs are gone, not hidden.** The old CapTP verb set (`ExportSturdyRef`,
  `EnlivenRef`, `ValidateHandoff`, `DropRef`, `CreateSealPair`, `Seal`) no longer exists as
  effects — replaced by caps-in-slots (`action.rs:1838-1840,1849-1850,1886-1888`). The catalog
  above is the whole live set; no `Effect` variant is `#[cfg]`-feature-gated.
