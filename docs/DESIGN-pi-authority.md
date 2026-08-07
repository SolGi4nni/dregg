# DESIGN — what a public input is FOR, and who is authoritative for each slot

**Measured 2026-08-06 at HEAD (`a0ee6e9d9`), by direct read of the files cited. Every number below
is one I reproduced; where I reproduced a different number than the brief or a prior doc gave, the
correction is marked ⚠.**

This is a design pass. It lands no code. It answers one question — *who decides what a PI slot
says* — and then argues, from what it found, that the parked `TURN_HASH` geometry cutover **should
not be done**, names the three things that should be done instead, and designs the sovereign
reconstruction change anyway so that the conditional is a real conditional rather than a shrug.

---

## 0. The three authority modes, stated precisely

| mode | mechanism | binds the prover to | who can use it |
|---|---|---|---|
| **A — AIR pin** | a `pi_binding` constraint: `local[col] − pv[pi_index]` on a first/last row | **their own trace column** | anyone who verifies the STARK |
| **R — verifier reconstruction** | the verifier *builds* the PI vector from data it trusts and verifies against that | **the verifier's truth** | only a party that holds the truth |
| **T — transcript** | `p3-batch-stark` observes every public value into the challenger | **the artifact** (no post-hoc edit) | anyone; costs nothing; forbids only relabelling |

`pi_binding` is the **only** constraint kind that reads a public input.
⚠ The brief cites `circuit/src/descriptor_ir2.rs:3826`; at HEAD the sole `pv[*pi_index]` site is
**`circuit/src/descriptor_ir2.rs:3845`** (the `VmConstraint::PiBinding` arm opening at `:3839`).
`grep -n 'pv\['` over that file returns exactly one line. `pv` itself is materialised at `:3952` and
`:4384`. So *unpinned means the constraint system never looks* — and that is now a Lean theorem, not
a reading (`PiDeclaration.unpinned_pi_admits_any_value`, per `docs/PI-DISPOSITION.md` §1).

### ⚑ The fact that reorganises everything: on the executor path, R is not a comparison

`turn/src/executor/proof_verify.rs::verify_one_cohort_run` (`:1097`) takes **no PI vector
parameter**. It takes the trusted `&Turn`, the trusted before-cell, the trusted 8-felt anchors, the
committed height and the fee — and it *constructs* `dpis` (`:1330`–`:1560`), then hands that vector
to `verify_vm_descriptor2` as the descriptor's public values (`:1871`). The prover's own published
PI vector is never deserialised, never read, never compared.

So on the sovereign full-node path **every slot in the vector is executor-authoritative, pinned or
not.** A `pi_binding` there is not a second opinion; it is a subset of what reconstruction already
forces. This is why 57% of the deployed registry's published felts carrying no pin costs the full
node nothing, and it is the single strongest argument in this document.

The doctrine is already written down in the tree, correctly, at
`sdk/src/full_turn_proof.rs:985-1004` (the `TurnIdentity` type doc) and at
`sdk/src/cipherclerk.rs:6181`, `:6217`, `:6405`. This design agrees with it and extends it.

---

## 1. The authority table

**Measurement** (mine, reproduced independently of `docs/PI-DISPOSITION.md`): parsing
`circuit/descriptors/rotation-wide-registry-staged.tsv` — 57 members, **Σ `public_input_count` =
3,821**, **1,642 felts named by some member's `pi_binding`**, **2,179 never named (57.0%)**. That
matches the brief and §1 of `PI-DISPOSITION.md` exactly.

Offsets are the v1 cascade in `circuit/src/effect_vm/pi.rs`; the rotated leg publishes
`pis[..V1_PI_COUNT]` = `[0,42)` plus four appended pins (`trace_rotated.rs:334`, `:336`, `:677-681`).

Columns: **is** = what actually decides the value at HEAD, per verifier class.
FN = full node (`verify_one_cohort_run`). LC = the wire verifiers
(`sdk::verify_full_turn_bound`, `dregg_verifier::check_receipt_pi_binding`).

| slot | offsets | members pinning | FN — is | LC — is | **should be** |
|---|---|---|---|---|---|
| `OLD_COMMIT` | `0..8` | PI 0 by 47/57; lanes 1..7 by none | **R** | **A** on lane 0 + the wide-16 tail | keep; lanes 1..7 are carried by the wide 16, say so in the manifest |
| `NEW_COMMIT` | `8..16` | PI 8 by 35/57; lanes 1..7 none | **R** | **A** + wide-16 tail | as above |
| `EFFECTS_HASH` | `16..20` | 4 felt-bindings in the whole registry | **R** | **T** | ⚠ see §5(c): the one carrier a Burn target reaches, and the deployed descriptor binds none of it |
| `INIT_BAL_LO/HI` | `20`,`21` | 47/56 each | **R** | **A** + `verify_balance_limb_pis` range | keep |
| `FINAL_BAL_LO/HI` | `22`,`23` | 34/56 each | **R** | **A** (34) / **T** (22) + range | keep; the 22 unpinned members are the gap |
| **`NET_DELTA_MAG/SIGN`** | `24`,`25` | **0/56** | **R** (derived from `run_effects`) | **T** — nobody | **R for FN, and DELETE the LC pretence**: its only readers (`extract_net_delta` at `atomic.rs:1244`, `:1597`) sit on an unreachable path — see §4 |
| **`CURRENT_BLOCK_HEIGHT`** | `26` | **0/56** | **R, and the reconstructed value is `0`** | **T** | **DELETE.** Superseded by the rotated pin at 44 |
| **`MAX_CUSTOM_EFFECTS`** | `27` | **0/56** | **R, and the value is `MAX_CUSTOM_EFFECTS_DEFAULT` (4), not the cell's** | **T** | **DELETE** |
| **`CUSTOM_EFFECT_COUNT`** | `28` | **0/56** | **R** | **T** | **DELETE** — its named enforcement reads no PI (§4) |
| **`APPROVED_HANDOFFS`** | `29..33` | **0/56** | **R** (zero sentinel) | **T** | **DELETE** — `ValidateHandoff` is not an effect |
| **`TURN_HASH`** | **`33..37`** | **0/56** | **R, and the reconstructed value is `[0,0,0,0]`** | **caller-anchored comparison** against `expected_turn_hash` | **stay transcript-only.** See §3 |
| **`EFFECTS_HASH_GLOBAL`** | `37..41` | **0/56** | **R** (zero) | **nobody** | **DELETE** from this window; the real object lives at `bilateral_aggregation_air::OUTER_EFFECTS_HASH_GLOBAL_BASE` |
| `ACTOR_NONCE` | `41` | **47/56**, pinned to `STATE_BEFORE_BASE + state::NONCE` | **R + A** | **A**, and the column is *forced* by the v1 machinery | **the model.** This is what a bound slot looks like |
| `rot::OLD/NEW_COMMIT` | `42`,`43` | 0/56 on wide | **R** (overridden from stored/claimed) | carried by the wide 16 | keep as vestigial or compact away |
| `rot::COMMITTED_HEIGHT` | `44` | **56/56** | **R + A** (overridden from `cell_committed_height`) | **A** | keep |
| `rot::CAVEAT_COMMIT` | `45` | **56/56** | **R + A** | **A** — but the *value* is prover-chosen (§3) | keep, and stop treating the pin as a value binding |
| per-family extra | `46` | family-dependent | **R + A** + in-circuit welds | **A** + welds (disc / perms-VK / lifecycle-payload / refusal `.write` / noteSpend `.absent`) | keep — these are the genuinely light-client-forced slots |
| membership teeth | `50`,`51` on `transferVmDescriptor2R24` | **0** — and their columns 1735/1736 are read by nothing | **R** | **nobody** — `MembershipBackingAttack §A` live | **R for FN; the in-AIR weld is the LC answer**, not a pin |
| **wide 8-felt anchors** | last 16 | **16/16 on every wide member** | **R** (anchored from trusted commits) | **A** + caller's `expected_old/new_commit` — *which no caller has* (§2) | keep; the missing half is an API field, not a constraint |

⚠ Two rows above are worse than "unpinned". `CURRENT_BLOCK_HEIGHT` and `MAX_CUSTOM_EFFECTS` are
slots where the **reconstruction itself writes a constant that is not the truth**:
`trace_rotated.rs:615-619` builds the v1 context as
`EffectVmContext { actor_nonce, asset_class, ..Default::default() }`, and
`trace.rs:387-401` makes `Default` write `current_block_height: 0`,
`max_custom_effects: MAX_CUSTOM_EFFECTS_DEFAULT`, `turn_hash: [ZERO;4]`,
`effects_hash_global: [ZERO;4]`, `previous_receipt_hash: [ZERO;4]`. Both the producer
(`cipherclerk::prove_sovereign_turn_rotated`, `sdk::prove_effect_vm_rotated_wide`) and the verifier
(`verify_one_cohort_run`) call the *same* generators, so those constants are on the wire on both
sides and Fiat–Shamir agrees. **A slot whose published value is a library default is not a public
input; it is padding with a name.**

⚠ **Correction to the brief's framing.** The brief lists `TURN_HASH` as one of the classes and asks
who is authoritative. On the deployed sovereign leg the honest answer is: *the reconstruction is
authoritative, and it says zero.* That is not the same as "nobody is authoritative" — Fiat–Shamir
forces the prover to have bound zero there too. What is missing is not authority; it is **content**.

---

## 2. The verifier split — three classes, not two

The brief poses full node vs light client. The tree has three, and the middle one is where the real
gap is.

### Class I — the full node (`turn::executor::verify_one_cohort_run`)

Holds: the `Turn`, the before-`Cell`, the `Ledger`, the stored sovereign commitment, the committed
height, the fee. Reconstructs: the entire `dpis` vector. Reads from the prover: **nothing but the
proof bytes.**

**What it can check:** everything. Every slot is R. An AIR pin buys it *literally nothing* — the pin
constrains the prover to a column, and reconstruction already constrains the prover to the executor's
value, which is strictly stronger (a pin binds you to your own trace; reconstruction binds you to the
truth). This is the brief's design insight, and it survives measurement.

**What it cannot check:** nothing in the PI vector. Its real residuals are elsewhere — the fold at
`node/src/turn_proving.rs:1159`, the `CommitSurface` injectivity floor, the FRI floor.

### Class II — the turn-holding wire verifier (`sdk::verify_full_turn_bound`, `dregg_verifier::check_receipt_pi_binding`)

Holds: the artifact off the wire, plus whatever external anchors the *caller* passes. Reads the
leg's own `sub_public_inputs`. Live call sites: `node/src/turn_proving.rs:1335`, `:1725`, `:3263`
(production), and `verifier/src/rotated_replay.rs:397` + `verifier/src/cross_fed.rs:385` for the
receipt binding.

**What it can check:**
* every leg is a sound STARK against a uniquely-accepting wide-registry descriptor
  (`verify_effect_vm_rotated_inner`, `sdk/src/full_turn_proof.rs:4440`);
* `PI[TURN_HASH..+4] == canonical_32_to_felts_4(expected_turn_hash)` on **every** leg
  (`:5201-5225`) — *when the caller has an external turn hash*;
* balance-limb ranges (`verify_balance_limb_pis`, `circuit/src/effect_vm/verify.rs:140`);
* leg-to-leg **adjacency** of the 8-felt anchors (`:5310-5322`) — this one genuinely fires;
* the in-circuit welds a light client inherits for free: lifecycle disc, perms/VK, lifecycle
  payload hash, refusal `fields_root` `.write`, noteSpend `.absent`/`.insert`.

**What it cannot check, measured:** the **endpoints**. `expected_old_commit`/`expected_new_commit`
are caller-supplied, and the one production surface that serves proofs to a third party has no
canonical value to supply. `discord-bot/src/commands/proof_verify.rs:20-33` states it as data:
`check_proof_hex` reads the anchors out of the artifact via `extract_commits` and hands them back,
so the two `CommitmentMismatch` teeth compare `x != x` and **structurally cannot fire**, because
"`/api/turn/{hash}/proof` serves `{turn_hash, proof_len, proof_hex}` and no commitment, and no
endpoint publishes a per-turn canonical 8-felt state commit."

**That is the largest live hole on the light path, and no AIR pin anywhere touches it.**

### Class III — the pure light client (no turn, no state)

Holds: the artifact and a VK epoch. Gets: descriptor identity, internal consistency, the in-circuit
welds, adjacency. Gets **nothing** about which turn, which cell, or which chain position — and
cannot, because it has no external anchor to compare anything against. `lightclient/src/lib.rs` is
a different layer (the recursive whole-chain fold) and its own honest residual is at
`circuit/src/ivc.rs:311-328`: the per-turn aggregate is *summarised*, not recursively verified, so a
fabricated `TurnTransitionSummary` with an arbitrary `turn_hash` folds cleanly.

---

## 3. Verdict on the geometry cutover: **do not do it**

The parked cutover is specified at `docs/PI-DISPOSITION.md` §4: add `C_TH_OFF` (4 felts) and
`C_TH_CARRIER = hash[old_commit, th0, th1, th2]` to the caveat region, absorb the carrier into
`C_COMMIT` (the published caveat commit, PI 45), and add four
`.piBinding .last (… C_TH_OFF + i) (33 + i)`. No `piCount` change. Cost as priced there: a 7,199-line
Lean module with 268 downstream modules, `EffectVmEmitRotationCaveat` extension, `trace_rotated`'s
`C_*` constants and `fill_caveat`, a turn hash threaded into `RotatedBlockWitness` (which carries
none today), an ack-gated re-emit re-keying `WIDE_REGISTRY_STAGED_FP` / `dregg-epoch`'s
`registry_fp` / `PROVENANCE.json` / `layout_generated.rs` / ~20 tests' geometry pins, and a VK
rotation.

Three findings kill it, in increasing order of severity.

### 3a. The pin does not force the value, for the party that would need it forced

Follow the chain the cutover builds, from a Class II/III verifier's seat:

`PI[33..36]` ← pinned to → `C_TH_OFF` columns ← absorbed into → `C_TH_CARRIER` ← absorbed into →
`C_COMMIT` ← published at → `PI[45]`, which **is** pinned (56/56) — and whose *value* is anchored by
nothing a wire verifier holds. `verify_full_turn_bound` never looks at PI 45. So the prover picks
the quartet, writes matching columns, gets a matching carrier, publishes a matching caveat commit,
and the whole chain is satisfiable end-to-end at any value it likes.

What the pin *does* buy is real but small: it makes the columns **forced**, so
`UnforcedPiPins.dropUnforcedPins` cannot delete the pins and the slot can be declared `.bound`
rather than `.transcriptOnly` in `PiDeclaration`. That is a **hygiene** win in the manifest, not a
**soundness** win at any verifier. Paying a VK rotation and a 268-module Lean move for a manifest
label is the wrong trade.

For the pin to force anything, the circuit would have to *derive* the identity from the proven
transition. Which brings us to:

### 3b. `Turn::hash()` is not derivable in-circuit, and for a sovereign turn it is a fixpoint

`turn/src/turn.rs:526-583` — `hash_with_forest` is **BLAKE3** over `agent ‖ nonce ‖ forest_hash ‖
fee ‖ memo ‖ valid_until ‖ depends_on ‖ previous_receipt_hash ‖ …`, and `forest_hash` is itself a
per-action BLAKE3 walk of the whole call tree. Arithmetising that in a BabyBear AIR is not a VK
rotation; it is a new circuit an order of magnitude larger than the effect VM, over a hash function
the system does not otherwise arithmetise.

And worse — `turn.rs:572-583` absorbs **`execution_proof`**, the proof bytes themselves. On the
sovereign path `cipherclerk.rs:6228` sets `turn.execution_proof = Some(proof_bytes)` *after*
proving. **A sovereign proof can never publish `turn.hash()`: it would have to contain a hash of
itself.** The tree already concedes this — `proof_verify.rs:3327-3337` computes the identity from a
`proofless` clone precisely because "a proof cannot commit to a hash that includes its own bytes".

So there are **two different turn hashes** in circulation:

| | `turn.hash()` (full) | `proofless.hash()` |
|---|---|---|
| used by | `verify_full_turn_bound`, `check_receipt_pi_binding`, `bind_turn_identity_pi`, the receipt's `turn_hash`, `/api/turn/{hash}/proof` | `compute_turn_identity_pi` (`proof_verify.rs:3327`) |
| available to a sovereign leg | **never** | yes |

An AIR pin cannot bridge them. The best a pin could ever reach is the proofless identity, and only
by arithmetising BLAKE3.

### 3c. The consumer that would have used it is unreachable

⚠ **The brief's load-bearing claim is CONFIRMED at source.**
`turn/src/executor/proof_verify.rs:1934` defines `verify_proof_carrying_turn_bundle`. Its **only**
call site in the entire tree is `:2210`, inside `verify_proof_carrying_turn_bundle_with_ledger`
(`:2191`). And `verify_proof_carrying_turn_bundle_with_ledger` has **zero call sites** — `grep -rn
proof_carrying_turn_bundle --include='*.rs'` over the whole repo returns 11 lines: 1 definition,
1 definition, 1 internal call, and 8 doc comments. `ast-grep` for the call shape returns nothing.

So the *only* executor-side turn-hash↔PI comparison in the tree is dead code, and the docblocks in
`circuit/src/effect_vm/pi.rs:88-96`, `circuit/src/effect_vm/mod.rs:143`,
`circuit/src/block_conservation.rs:101` and `turn/src/turn.rs:454` all describe an enforcement that
does not run.

**Verdict: drop the `TURN_HASH` geometry cutover.** It cannot help Class I (reconstruction subsumes
it), it cannot help Class II/III (the carrier chain is prover-chosen end to end), the value it would
pin is uncomputable in-circuit and for sovereign turns logically impossible, and the consumer that
motivated it never runs. `/proof turn`'s seam 2 — "the identity is prover-CHOSEN, not
prover-FORCED" — is **not transmutable debt. It is a theorem of the model**, and it should be
rewritten in the tree as one instead of standing as a promissory note.

---

## 4. What is actually broken, and is cheaper

### (a) ⚑ Publish a canonical per-turn commit anchor — LANDED IN PART, and this section was WRONG

**Original text (kept, because the correction is the interesting part):** *"Class II's two endpoint
teeth are structurally dead because no endpoint publishes the canonical 8-felt
`old_commit`/`new_commit` for a turn. Adding them to `/api/turn/{hash}/proof` (from the node's own
committed state, which it has) converts `x != x` into a live check that a third party can run. No
VK, no re-emit, no re-genesis, no Lean."*

⚠⚠ **MEASURED FALSE 2026-08-06. The node's committed state does not hold that pair.**

It holds *an* 8-felt per-turn pair — `TurnReceipt::{pre,post}_state_hash`, which
`dregg_turn::state_commit` made the chip 8-felt consensus commitment and which the attestation's
`receipt_stream_root` transitively covers. **It is a different commitment from the one the proof
publishes**, and two causes are independently sufficient
(`turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`):

* **`iroot`** — `state_commit::consensus_ctx` pins `rotation_witness::empty_iroot()` deliberately
  (a receipt cannot bind a commitment its own hash is computed from); the proof's witness folds the
  real receipt chain (`turn_proving::rotation_witness_for_self_sovereign_with_root` threads
  `[receipt.receipt_hash()]`).
* **`cells_root`** — `consensus_ctx` folds the WHOLE ledger; `rotation_witness_for_self_sovereign_impl`
  folds a single-cell `ctx_ledger` holding only the actor.

So serving the receipt's pair as `expected_old_commit` would **refuse every honest proof**. The
endpoint teeth stay reflexive, and closing them is not an API field — it is aligning the executor's
and the prover's `V9RotationContext` to one commit per turn, which moves what the committee signs
*and* what the proof publishes. Real work, correctly the next item, and **undone, not terminal**.

**What DID land (2026-08-06):** `GET /api/turn/{hash}/anchor`, serving
`dregg_federation::TurnAnchorV1` — the receipt whole, its chain position, and the attestation with
both quorum legs. A holder verifies it against a roster of their own and gets a **committee-signed
turn hash**, which `verify_full_turn_bound` already takes as a required argument. `/proof turn` now
requires one and refuses without it; a proof of turn B under turn A's anchor is rejected end to end
(`node/tests/turn_anchor_binds_a_proof_to_the_committee.rs`). No VK, no re-emit, no re-genesis, no
Lean — that part of the original estimate held.

⚠ **And a second correction, to a premise this document did not state but relied on.** "The
committee signed it" is weaker than it reads. `AttestedRoot::quorum_signatures` — the ONLY preimage
that absorbs `receipt_stream_root`, hence the only one that reaches a receipt — receives exactly one
push on the live path, the local node's (`blocklace_sync.rs:9741`); there is no gossip merge
(`PeerMessage::AttestedRootUpdate` has zero handlers). The `>= threshold` hybrid quorum that DOES
assemble signs `dregg-finalization-vote-v3 || block_id || merkle_root` and covers no per-turn value
at all. **No `>= threshold` committee signature anywhere in this tree covers a turn hash, a receipt
hash, or a receipt's state commit.** `TurnAnchorV1::verify` therefore REFUSES on any federation with
`threshold > 1` rather than reporting a caveat. The fix is one field in the vote preimage
(`finalization_vote_signing_message` v3 → v4, carrying `receipt_stream_root`); the emitter already
runs *after* `execute_finalized_turn` returns, with the durable attested root readable
(`blocklace_sync.rs:6044-6077` re-reads the live ledger instead). It also touches
`FinalizationVote::sign`, `VoteCollector::assembled_quorum` (group by `(root, stream_root)`),
`StoredAttestedRoot::verify_finalization_quorum` / `has_any_valid_committee_signature`,
`backfill_finalization_quorums`, and the Lean-side `verified_finalization_quorum` decider
(`node/src/finalization_votes.rs:594`). That Lean twin is why it is a separate change, not a line.

⚠ Related, found while measuring and NOT fixed here: the live path fills
`AttestedRoot::hybrid_quorum` by copying `finalization_quorum`'s signature bytes
(`blocklace_sync.rs:9773`), which are over the *vote* preimage — while the field's own docs and
`verifier/src/cross_fed.rs:599` check them against `signing_message()`. A live-produced root's
`hybrid_quorum` therefore cannot pass `verify_attested_root_hybrid`. Fail-closed, and invisible in
test because the cross-fed tests sign `signing_message()` directly.

### (b) Collapse the three `TURN_HASH` fill conventions to one — a live liveness bug

Measured at HEAD, producers writing `PI[TURN_HASH_BASE..]`:

| producer | writes |
|---|---|
| `sdk/src/full_turn_proof.rs:964` `bind_turn_identity_pi` (called at `:1507`, `:1651`, `:2896`, `:3608`) | 4 felts, `canonical_32_to_felts_4` |
| `turn-prover/src/proven_receipt.rs:126-127` | 4 felts |
| `wasm/src/runtime.rs:555` | 4 felts |
| `node/src/blocklace_sync.rs` (per `PI-DISPOSITION` §2) | 4 felts |
| **`turn-prover/src/rotation_witness.rs:166`** | **1 felt** — `dpis[TURN_HASH_BASE] = tid`, three left zero |
| **`circuit-prove/src/joint_turn_aggregation.rs:900, 1031, 1168, 1302`** | **1 felt**, same shape |
| `sdk/src/cipherclerk.rs` (sovereign) | **nothing** — deliberately, `None` at `:6190`, `:6219`, `:6407` |

Every reader compares all four felts (`verify_full_turn_bound:5201`, `check_receipt_pi_binding`).
**So the five 1-felt producers mint legs that both deployed checkers refuse.** That is a soundness-
neutral liveness break, fixable by editing five lines, and it is exactly the class `b340ca447`
already fixed once for the SDK path. Do this first regardless of anything else in this document.

### (c) Delete the dead slots instead of pinning them

`APPROVED_HANDOFFS` (retired effect), `CURRENT_BLOCK_HEIGHT` (superseded by the pinned+anchored PI
44), `MAX_CUSTOM_EFFECTS` (the reconstruction publishes the library default, not the cell's),
`EFFECTS_HASH_GLOBAL` (zero on every deployed leg, no reader), `CUSTOM_EFFECT_COUNT`. That is
**11 of the 39 unpinned felts** on `transferVmDescriptor2R24` (unpinned set measured:
`1..7, 9..15, 16..19, 24..40, 42, 43, 50, 51`; the 11 are `26, 27, 28, 29..32, 37..40`).

`CUSTOM_EFFECT_COUNT` deserves its own line. `turn/src/executor/proof_verify.rs:236` states the
off-circuit dispatch count "must equal the in-circuit committed Custom-effect count
`PI[CUSTOM_EFFECT_COUNT]`". `enforce_custom_proof_count_committed` (`:783-799`) **reads no public
input at all** — it compares `turn.custom_program_proofs.len()` against a re-derivation from the
turn's own effects. Two executor-derived quantities compared to each other. The docblock is false
and the slot is doing nothing.

This IS a PI-layout compaction, so it IS a VK rotation — but it *removes false surface* rather than
adding true surface, which is the opposite trade from §3.

### (d) Delete the unreachable verifiers, so the docblocks stop lying

* `verify_proof_carrying_turn_bundle` + `_with_ledger` (§3c).
* `Executor::execute_atomic` / `execute_atomic_sovereign` — measured: `grep -rn execute_atomic
  --include='*.rs'` outside `turn/src/executor/atomic.rs` returns exactly **one** hit, a doc comment
  at `circuit/src/block_conservation.rs:85`. The only in-module callers are `#[cfg(test)]`. This
  matters: `atomic.rs:1146-1155` **forwards prover-supplied PIs** (overriding only the 8-felt
  commits) and then reads `extract_net_delta` off them at `:1244`/`:1597`. If that path were live,
  `NET_DELTA` would be a prover-chosen input to the conservation gate. It is not live. **An
  unreachable verifier is not a wound — and an unreachable wound is not a wound either.**

Together (c)+(d) delete most of the tree's "the executor checks X against PI[Y]" prose that is false
at HEAD, which is worth more to the next reader than a pin.

---

## 5. If the cutover proceeds anyway — the sovereign reconstruction change, designed

The brief asks for this design conditionally. Here it is, because a conditional whose antecedent is
undesigned is not an argument. **This change is a strict prerequisite: landing the pin without it
makes every honest sovereign proof UNSAT**, exactly as the second lane reported.

### 5.1 What breaks and why

Producer and verifier call the *same* generators (`generate_rotated_transfer_shape_wide`,
`…_with_fee_wide`, `…_record_pin_wide`, …), which build the v1 context at
`trace_rotated.rs:615-619` as `..Default::default()` ⇒ `turn_hash = [ZERO;4]`. Today both sides
write zero at 33..36 and Fiat–Shamir agrees. Pin those four PIs to columns, and the *columns* must
also carry the value the *reconstruction* publishes — so the moment the verifier keeps writing zero
while a producer writes the identity (or vice versa), the transcript diverges and the proof is
refused. **The two halves must move in one commit.**

### 5.2 The value: the proofless identity, and it is stable across the prove boundary

The only identity a sovereign leg *can* carry is the proofless hash — §3b. I measured that it is
stable across the prove boundary, which is the load-bearing detail:

* `sdk/src/cipherclerk.rs:6089-6107` constructs the whole `Turn` — `agent`, `nonce`, `call_forest`,
  `fee`, `memo`, `valid_until`, `previous_receipt_hash`, `depends_on`,
  `execution_proof_new_commitment: Some(new_commitment)` — with `execution_proof: None`, **before**
  the prove.
* The prove happens at `:6182-6220`.
* The **only** post-prove mutation is `turn.execution_proof = Some(proof_bytes)` at `:6228`.
* `execute_sovereign_turn_with_proof` (`:5461-5476`) returns `proven.turn` unmodified.

So `turn.hash()` at prove time **equals** `proofless.hash()` at verify time, byte for byte. The
change is feasible. Concretely:

**Verifier side** — in `verify_one_cohort_run`, after the generator returns and *before* the
`dpis.len() != desc.public_input_count` gate (`proof_verify.rs:1510-1516`):

```
// The sovereign leg publishes the PROOFLESS turn identity (turn.hash() absorbs
// execution_proof, so a proof cannot commit to a hash of itself —
// turn/src/turn.rs:572-583, and the same rule at proof_verify.rs:3327-3337).
let th = Self::proofless_turn_hash_felts(turn);
dpis[pi::TURN_HASH_BASE..pi::TURN_HASH_BASE + pi::TURN_HASH_LEN].copy_from_slice(&th);
```

with `proofless_turn_hash_felts` **factored out of** `compute_turn_identity_pi` so there is one
implementation, not two. (That function is currently only reachable from dead code; extracting the
rule is how it becomes live.)

**Producer side** — `prove_sovereign_turn_rotated` threads `Some(turn.hash())` where it today passes
`None` (`:6190`, `:6219`) and `prove_sovereign_cohort_chain` likewise (`:6407`), routing through the
existing `TurnIdentity` plumbing and `bind_turn_identity_pi`. ⚑ It must hash **at `:6108`**, after
the `Turn` literal is complete and before any weld routing mutates anything.

**Both sides must also write the columns**, not just the PI — the pin equates them, so a producer
that fills the PI and leaves `C_TH_OFF` zero is UNSAT against itself. That is a `fill_caveat`
change plus a `RotatedBlockWitness`/`RotatedCaveatManifest` field, which is the "every caller in
sdk/turn/turn-prover/circuit-prove changes" line in `PI-DISPOSITION.md` §4.

### 5.3 ⚠ The cost this creates that nobody has priced: wire malleability becomes a liveness failure

Today the slot is zero, so **any** benign mutation of a `Turn` between prove and verify — a relayer
touching `depends_on`, a re-serialisation that changes a memo, a submitter that fills
`previous_receipt_hash` — is harmless to the proof. After the change, every such mutation moves the
proofless hash, diverges the reconstruction, and **refuses an honest turn with a Fiat–Shamir
failure** (`InvalidPowWitness` / "proof bound NO descriptor"), which is the least diagnosable error
this system produces. `turn.hash()` binds fourteen fields; the executor would then be requiring
byte-identity on all fourteen between the producer's moment and the verifier's.

That is not an argument against ever doing it. It is an argument that the change needs a *diagnostic*
— if PI 33..36 is the only mismatch, say so by name rather than reporting "bound NO descriptor" —
and it is one more reason the §3 verdict is *don't*.

---

## 6. Sequencing (only if §3's verdict is overridden)

Ordered. Each step is independently landable and independently valuable except where noted.

| # | step | separable? | flag day |
|---|---|---|---|
| 0 | **§4(b)** — collapse the five 1-felt producers onto `canonical_32_to_felts_4`. | **yes**, do it regardless | none |
| 1 | **§4(d)** — delete `verify_proof_carrying_turn_bundle{,_with_ledger}` and `execute_atomic{,_sovereign}`, and the docblocks that cite them. | **yes** | none |
| 2 | **§4(a)** — publish canonical per-turn commit anchors. | **yes** | API addition (operator's call) |
| 3 | Factor `proofless_turn_hash_felts` out of `compute_turn_identity_pi` (single source). | **yes** | none |
| 4 | **§5.2 producer+verifier fill, in ONE commit**, still unpinned. Land the diagnostic from §5.3 with it. | **no** — atomic pair | wire: sovereign legs stop publishing zero |
| 5 | Lean: `EffectVmEmitRotationCaveat` `C_TH_OFF`/`C_TH_CARRIER`, `EffectVmEmitRotationV3` region shift (`CANON9_REGION_OFF` 547→553, `APPENDIX_SPAN` 659→665), four `.piBinding`. | no | 268 downstream Lean modules |
| 6 | Rust `trace_rotated` `C_*` + `fill_caveat` + `RotatedBlockWitness` field. | no | every producer call site |
| 7 | Ack-gated re-emit + **VK rotation**: `WIDE_REGISTRY_STAGED_FP`, `dregg-epoch` `registry_fp`, `PROVENANCE.json`, `layout_generated.rs`, ~20 tests' geometry pins. Not a re-genesis — `CANONICAL_STATE_SCHEMA_EPOCH` stays 23. | no | VK epoch |
| 8 | Update `PiDeclarationDeployed` to declare 33..36 `.bound`, and delete `turn_hash_is_transcript_only`. | no | none |

**Explicitly NOT in this sequence** — and this is a correction to the brief's framing:

⚠ **`V9RotationContext.iroot` → `Faithful8` is not a prerequisite for any of the above.**
Measured: the field is a bare `dregg_circuit::field::BabyBear` at `cell/src/commitment.rs:859`,
sitting among three `Faithful8` siblings (`cells_root:832`, `nullifier_root:839`,
`commitments_root:847`), and `iroot` appears as a field access at **133 sites** (`ast-grep '$X.iroot'`)
across ~18 crates. It is a `docs/FAITHFUL-COMMITMENT-LAW.md` item — the same wound class as
`cell/src/commitment.rs:561` and `node/src/turn_proving.rs:1159` — and it is entirely orthogonal to
which PI carries the turn identity. Bundling it is what makes this cutover's price look like 43
sites in 10 crates when the turn-hash work itself does not touch `iroot` at all. **Price them apart,
and do the `iroot` lift on its own merits** (it closes a ~31-bit component riding inside the
consensus anchor, which is worth more than the pin).

`ROTATED_PAYLOAD_WIDTH` (`circuit/src/exact_nullifier_aafi_rotated_trace.rs:32`) is likewise
unrelated: it is `ROTATED_PRE_LIMBS + 1` for the exact-nullifier AAFI trace, asserted equal to
`layout_generated::B_STATE_COMMIT` at `:91`. It hardcodes one felt of *state commit*, not of turn
identity.

---

## 7. The rule this design proposes, in one paragraph

**A published public input must name its authority, and the authority must be the strongest one the
consuming verifier can actually exercise.** For a slot a full node reconstructs, reconstruction *is*
the authority and a pin is decoration — say `.transcriptOnly` with that as the reason and stop
calling it a hole. For a slot a wire verifier must judge without the turn or the state, the only
things that work are (i) an in-circuit weld that forces the value from data the client can recompute
— the disc gate, the perms/VK weld, the lifecycle-payload hash gate, the refusal `.write` map-op,
the noteSpend `.absent`; these are the tree's real light-client teeth and they are the pattern to
extend — or (ii) an external anchor the caller supplies, which is what `expected_turn_hash` is and
what `expected_old_commit` needs to become. **A pin onto a carrier whose published value nobody
anchors is neither**, and that is precisely what the `TURN_HASH` geometry cutover would buy.
