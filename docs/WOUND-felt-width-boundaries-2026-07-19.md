# WOUND — narrowed-digest security boundaries (the felt-width class)

**Opened 2026-07-19.** Found while chasing an unrelated FRI-soundness question ("why an 8-to-1
fold?"). The 8-to-1 fold is fine (costs `log₂7 ≈ 2.8` bits, documented). But the question surfaced
the *real* version of the worry: places where a Poseidon2/BabyBear digest (8 felts, ~124 bits) is
silently squeezed to **one felt (~31 bits, birthday-collidable at ~2^15.5 — and O(1) where the
prover picks the bytes, see the RE-PRICING section below)** and then used as a
**security boundary** — a commitment, a signed payload, a membership key, an authorizing equality.

The v10 / "faithful 8-felt" / `Faithful8` campaign was real and closed the sites it *targeted*
(cell state commitment, heap/fields/cap roots, umem boundary — `reference-umem-boundary-31bit` is
**closed at HEAD**). But it **widened roots, not key-spaces**, and its two defenses do not
generalize:

- `scripts/check-no-degraded-felt.sh` covers exactly **three files**
  (`cell/src/commitment.rs`, `turn/src/rotation_witness.rs`, `circuit/src/effect_vm/trace_rotated.rs`)
  — and (07-24 sweep) it is blind **inside** those three: its rule matches only
  `fold_bytes32_to_bb`, so the 32→1 `cap_root::fold_bytes32` at `cell/src/commitment.rs:547` (#24's
  producer) passes the gate in a scoped file. See the SWEEP section's gate-scope answer.
- The `Faithful8` type wall only bites where a value flows into a **typed octet sink**.

Every finding below lives in the **complement of both** — the class regrows there. The recurring
tell: **a doc-comment asserting collision-resistance over a value that has been squeezed to one felt.**

Provenance tags: **[V]** = verified by direct read this session · **[A]** = agent-read, not yet
independently confirmed · **[?]** = severity needs one more trace before pricing.

---

## ⚑ RE-PRICING (2026-07-24) — READ BEFORE QUOTING A COST FROM THIS FILE

Most `~2^31` figures below were derived from the felt WIDTH. Width bounds the image; it does not
price the attack. The #25 closure (`fc61678a43`) found one fold that is LINEAR; re-reading the four
byte→felt encoders this catalogue actually rides shows the correction is broader than that one fold
and narrower than "everything is O(1)". **Three regimes, and the row's cost depends on which one it
is in AND on whether the attack needs a COLLISION or a TARGETED HIT.**

### The four encoders, read at HEAD

**(1) `fold_bytes32_to_bb` — LINEAR. Confirmed.** `circuit/src/effect_vm/helpers.rs:167-179`:

```rust
const MIX: u32 = 0x4FD3_9C8B % crate::field::BABYBEAR_P;
let limbs = bytes32_to_8_limbs(b);
let mut acc = BabyBear::ZERO;
for i in (0..8).rev() { acc = acc * mix + limbs[i]; }
```

`Σ_{i<8} limbs[i]·MIX^i` over `𝔽_p`. The limb vector is prover-choosable coordinate-wise (see (2)),
so this is an onto linear form on `𝔽_p^8`. **Both a colliding pair AND a hit on any chosen target
felt are ONE linear solve — O(1).** The collision constructor is exhibited and asserted, not argued:
`circuit/tests/effects_hash_fold_and_burn_target_width.rs::fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`.

**(2) `bytes32_to_8_limbs` — the "wide" octet is NOT injective.** `helpers.rs:37-45` is
`out[i] = BabyBear::new(u32::from_le_bytes(chunk)) ` with `BabyBear::new(v) = v % BABYBEAR_P`
(`circuit/src/field.rs:114-116`, `p = 2^31 − 2^27 + 1 = 2013265921`). So for **any** 4-byte LE chunk
whose u32 value `v < 2^32 − p` (≈53% of the u32 space), the 32-byte string with that chunk replaced
by `v + p` is a DISTINCT value with an IDENTICAL 8-limb projection. `hash_to_8` — the executor and
SDK "full ~256-bit binding" projector (`turn/src/executor/effect_vm_bridge.rs:104-106`,
`sdk/src/cipherclerk.rs:6741-6743`) — **is** `bytes32_to_8_limbs`. Widening a carrier to the octet
therefore retires the linear-solve collision family (the #25 falsifier asserts exactly that:
`assert_ne!(la, lb)` on the solved pair) and **does not retire the mod-p alias family**. Against
hash-image inputs this costs nothing (you cannot steer a BLAKE3 output into an aliased chunk without
grinding); against a prover-chosen 32-byte wire blob it is a free collision at any width.

**(3) `cap_root::fold_bytes32` and `bridge::present::bytes_to_babybear` — NOT linear, but O(1)
collidable for the OTHER reason.** `circuit/src/cap_root.rs:254-256` is
`hash_many(&BabyBear::encode_hash(bytes))` and `bridge/src/present.rs:1768-1771` is the same
composition. Poseidon2 is not a linear form, so the lane's linearity correction **does not** extend
here — but `BabyBear::encode_hash` (`field.rs:212-219`) is the same non-canonical `Self::new(val)`
per 4-byte chunk as (2), so the fold inherits the alias family. **Already exhibited in-tree, twice,
and both were read as evidence FOR the ~2^31 pricing rather than against it:**
`circuit/src/exact_cap_root.rs:505` (`assert_eq!(fold_bytes32(&a), fold_bytes32(&b))`, `a = [0;32]`
vs `b` = `p` in the low chunk) and `cell/src/state.rs:1430-1435` (`0x0800_0000` vs `0x8000_0001` —
differing by exactly `p = 0x7800_0001`). `poseidon2::hash_bytes`
(`circuit/src/poseidon2.rs:566-569` → `from_bytes_packed`, `field.rs:194-209`) is the same shape
over arbitrary-length input.

**(4) `commit::typed::canonical_32_to_felts_8` — LOSSY BY CONSTRUCTION, and this file called it
benign.** `commit/src/typed.rs:565-576` packs `lo | mid1<<8 | mid2<<16 | ((hi & 0x3F) << 24)` —
**bits 6 and 7 of bytes 3, 7, 11, 15, 19, 23, 27, 31 are DISCARDED**, 16 bits of a 256-bit input.
A colliding pair is two bit flips, no search. The triage table's "30 bits/limb ⇒ 240-bit" is a
statement about the IMAGE SIZE, not about collision cost. This feeds `compress_member`
(`:604-610`), the `SenderAuthorized` membership leaf (#9) and the nullifier/adjacency leaves.

### The rule — classify EVERY new entry on these two axes before writing a cost

| axis 1: who picks the 32 bytes | axis 2: what the attack needs | cost |
|---|---|---|
| **DIRECT-LINEAR** — a prover-chosen wire field / witness column folded by `fold_bytes32_to_bb` | collision **or** targeted hit | **O(1)** — one linear solve |
| **DIRECT-ALIAS** — prover-chosen bytes through `encode_hash` / `bytes32_to_8_limbs` / `from_bytes_packed` / `canonical_32_to_felts_8` | **collision** (conflate two objects I authored) | **O(1)** — add `p` to a chunk, or flip the dropped bits |
| **DIRECT-ALIAS** | **targeted hit** (match a felt someone else fixed) | **~2^31 unchanged** — aliasing gives collisions, never preimages |
| **PREIMAGE** — the 32 bytes are a hash image the attacker must invert or grind (`CellId::derive_raw`, a BLAKE3 receipt hash, a Poseidon2 state fold) | collision | ~2^15.5 birthday |
| **PREIMAGE** | targeted hit | **~2^31 unchanged** |

The distinction that moves rows is **DIRECT-ALIAS + collision**. That is where this catalogue was
consistently ~31 bits too expensive, and it is the regime the two in-tree exhibited collisions were
already sitting in. `#18`, `#19` and the umem value fold are in it; `#20`, `#22`, `#23`, `#24`,
`#26`, `#2` are not — each was traced individually below and each one's `~2^31` **stands**.

### What this does NOT license

- **It is not a general "everything is O(1)."** Every one of the four encoders is followed, at some
  sites, by a Poseidon2 squeeze over values the attacker cannot steer. Trace the byte source per
  row; the wound's prose is not evidence.
- **An exhibited collision is not an exponent.** #23's falsifier found a real present-cell-set
  collision in **7,323 offline folds** and recorded it as an OBSERVATION, which is the right
  discipline. Quantifying the caution: under the analytic 31-bit birthday model, a first collision
  at `n = 7 323` has probability `1 − exp(−n²/2p) ≈ 1.2%` — a 1-in-80 draw, so it is weak evidence
  of sub-31-bit effective entropy, not a measurement of it. If the fold really carried ~2^31 the
  median first-collision count is `1.177·√p ≈ 54 500`; a median near 7 300 would imply an effective
  image near **2^25**. The cheap discriminator is to re-run the existing `#[ignore]`d search with
  ten different agent legs and read the MEDIAN. Until that runs, the honest statement is "cheaper
  than quoted by an unknown factor", not "2^12.8".
- **Do not let a KEY collision be scored as a VALUE collision.** #23's falsifier deliberately
  REFUSES a key-collision pair so a same-leaf-address hit cannot be laundered as a root collision.
  Any row whose cost was measured without that separation is attributing the wrong collision;
  #5/#9/#11/#20/#24 are all key-or-leaf sites where the two are easy to confuse.

### Sites this re-pricing surfaced that the catalogue did not have

- **#32 — `umem_fold_bytes_v1` is an AFFINE byte fold whose doc-comment says "injective".**
  `turn/src/umem.rs:1149-1156`: `acc = BabyBear::ONE; for b in bytes { acc = acc * mul + BabyBear::new(b as u32 + 1) }`
  with `mul = 0x1000_0193`. It is the FALLBACK universal-map ADDRESS for every `UKey` outside the
  five hot planes and the VALUE felt for every `UVal` outside `Bytes32`/`UmemRef`
  (`:1197`, `:1211`), computed over `serde_json::to_vec(other)`. The comment at `:1194-1196` calls
  it "a deterministic **injective** felt over its canonical serialization" — it is a linear form on
  the byte vector into a ~2^31 image, so it is not injective and collisions are a solve, not a
  search: meet-in-the-middle over four free serialization bytes is ~2^16, and O(1) wherever the
  serialization carries a numeric field spanning the field. Same class as `fold_bytes32_to_bb`,
  outside `check-no-degraded-felt.sh`'s scope, with the strongest false claim in the tree.
  **DIRECT-LINEAR.** Kind C/D — the umem address grammar is Lean-authored (Rank-1 `uaddrEnc`).
- **#33 — the umem `Bytes32` value felt is DIRECT-ALIAS.** `turn/src/umem.rs:1208`:
  `Some(UVal::Bytes32(b)) | Some(UVal::UmemRef(b)) => (BabyBear::ONE, fold_bytes32(b))` — a
  32-byte umem value the writer picks, through encoder (3). Two distinct committed umem values
  collide for free. Same line for `UKey::NoteNullifier` / `UKey::BridgedNullifier` at `:1193`.
- **The octet-widening residual (applies to #25's repair and to every "absorb all 8 limbs
  (~256-bit binding)" comment in `effects_hash_inputs`).** Per (2), those arms bind the 8 limbs,
  not the 32 bytes. For `CellDestroy`/`CellSeal`/`ReceiptArchive` targets (CellIds, hash images) the
  gap is unreachable; for `EmitEvent`'s `topic_hash`/`payload_hash` and `Refusal`'s
  `offered_action_commitment` — prover-chosen 32-byte blobs — two distinct effect lists share an
  identical octet, hence an identical `PI[EFFECTS_HASH_BASE..+4]`, at zero cost. The tree already
  owns the injective codec: `bytes32_to_u16_limbs` (`cell/src/note.rs:201-207`, sixteen `u16` lanes,
  each `< 2^16 < p`, "no source chunk is reduced modulo BabyBear"), which is exactly what the v11
  fields leaf switched to and why `cell/src/state.rs:1430-1445` separates the alias pair that
  `fold_bytes32` conflates. Any future widening should use THAT, not `bytes32_to_8_limbs`.

---

## Probe findings — deeper seams surfaced by the Lean-port recon (2026-07-19)

The four terrain probes turned up holes **bigger than felt-width**, and one correction to my own
readiness claim. Captured here so they ride the same campaign.

- **#15 Shielded `merkle_root` is wire-supplied, not pinned to the committed accumulator [A, HIGH].**
  `apply_shielded_transfer` (`turn/src/executor/apply.rs:1315-1412`) reconstructs the tree
  `from_serialized_parts(payload.merkle_root, …)` and verifies membership against **that** root — with
  NO check it equals the live committed commitment-tree root. A prover supplies a root of their choosing
  and proves membership in an attacker-built tree. Theft/inflation vector **larger than any birthday
  collision**; widening the felt does not fix it.
- **#16 Shielded value-link is honest-prover-trusted [A, HIGH].** `verify_value_link` (leaf-value ↔
  Pedersen-leg-value equality) is called **only in a test** (`circuit-prove/tests/shielded_transfer_m2a.rs`),
  never in `apply_shielded_transfer`. Conservation over `value_binding` is attested, not proved — the real
  inflation exposure, independent of the 31-bit width.
- **#17 Shielded PQ-commitment disagreement [A].** The Lean apex rests on Shor-broken Ristretto Pedersen
  (`commit_hidden_asset`, DLog) while `spend_circuit.rs:42-48` declares a "PQ cutover (Option A)" making
  the Poseidon2 `value_binding` authoritative — the two disagree on which commitment is load-bearing.
- **Consequence for #10:** the shielded pool is **not** "widen 3 felts." It is "port the Rust-authored
  `spend_circuit` AIR to Lean + pin `merkle_root` to the committed accumulator + fold the value-link
  into the AIR + resolve the PQ-commitment story." Felt-width is the entry point, not the fix. Reachable
  only in a `prover`-enabled executor (verify-only fails closed); not in the committed VK.
- **Correction to #4/#10 (note/nullifier):** I over-claimed this as "finish an existing port." The
  accumulator NODE digests are 8-felt + proven (`DeployedHeapTree`/`SortedTreeNonMembershipHeap8`), but
  the note commitment/nullifier **value and the sorted key** are still 1-felt and UNSTARTED.
  **CORRECTION (07-20 scoping):** the "new bracketing math" fear was too pessimistic — the sorted-gap
  soundness (`Crypto/NonMembership.lean`) is already `[LinearOrder Digest]`-**generic**, so instantiating
  `Digest := Lex (Fin 8 → ℤ)` gives the whole adjacency bracketing FOR FREE (the IMT/Heap8 wrappers are
  ℤ-typed but their proofs never touch ℤ arithmetic — mechanical generalization, machine-confirmable by a
  one-section spike). The genuine new work is bounded and nameable: **one lex-`<`-over-8-felts AIR gadget**
  (✅ **LANDED / VERIFIED 2026-07-22** — `metatheory/Dregg2/Circuit/Emit/LexCompare8Emit.lean::lexLt8_refines`: the emitted
  `lexLt8Descriptor` decides `toLex a < toLex b` as a proven iff (`lexLt8_sound`+`lexLt8_complete`, canonicity
  hypotheses explicit, teeth incl. LSB-decider limb-7 + p-boundary canary), with the order-corollaries +
  sorted-tree wiring bridge in `Crypto/Digest8KeySpike.lean` (`Digest8Key := Lex (Fin 8 → ℤ)`, `LinearOrder`
  via `Pi.Lex`, `sorted_gap_excludes_digest8`); `#assert_axioms`-clean, rooted, rebuild-confirmed), a
  **leaf-schema widening** (addr/nextAddr → 8 felts,
  arity-17 leaf), and the **easy value widening** (`hash_many→hash_many_8`, `felt_to_bytes32→digest8_to_bytes32`).
  The compare-gadget half is DONE; the residual is leaf-widening + value-widening + the ember-gated deploy.
  Still HIGH — but the cost is now just a leaf widening, **not new combinatorics**. Plus the
  **ember-gated, frozen** kernel flip (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal").
- **#12 interface_id has NO Lean model and NO wide twin** — left behind when cap_root grew its `_8`.
  Reusable wide primitive exists (`Market/WideCommitBoundary.lean` `wireCommitR8`/`Poseidon2Width8`;
  Rust `hash_many_8`/`digest8_to_bytes32`). Anti-laundering: the fold accumulator must be 8-felt
  end-to-end, not just the final squeeze. Severity MODERATE (discovery/factory-identity, not funds).
  **CORRECTION (07-22): the "NO wide twin" half is STALE.** At HEAD `cell/src/interface.rs::compute_interface_id`
  is a FULL 8-felt fold end-to-end (`hash_many_8` at every step, `0x1FACE`+`len` seed, 8-lane sorted,
  `digest8_to_bytes32` tail) — the Rust widening ALREADY LANDED. **The Lean proof-half is now
  LANDED** (`metatheory/Dregg2/Cell/InterfaceIdWidth.lean`, rooted, `#assert_axioms`-clean): FALSIFIER
  `narrow_conflates`/`narrow_colliding_interfaces_share_vk` (the pre-widening 1-felt lane-0 leaf
  conflates two DISTINCT method sets ⇒ they share a `derive_service_factory_vk` factory VK), FIX SOUND
  `wideId_injective`/`wide_separates` (the deployed 8-felt fold is injective in the leaf list under the
  wide-hash CR floor `Function.Injective hash8`, a NAMED hypothesis), the exact anti-launder
  `finalSqueezeOnly_still_conflates` (widening ONLY the final squeeze STILL conflates), and the arity
  tooth `seed_arity_injective`. Site #12 is **byte-safe PROVEN** (Rust-fixed + machine-checked).

## SWEEP — 2026-07-24 (second pass): the four-detector 1-felt-collapse sweep

Four blind detectors (type-level mixed-width · narrowing-idiom · Lean-model-vs-deployed · cross-rung
seam) swept for narrow security boundaries; this section is the **adversarial synthesis**: every
claimed GENUINE finding re-verified at HEAD by direct read, a sample of the claimed SAVED verdicts
re-verified too, duplicates merged, and everything that could not be confirmed **demoted and named**.
Result: **five new GENUINE entries (#23–#27), two DOMINATED entries (#28–#29), one saved-verdict
FLIP, one detector claim DEMOTED, and three stale catalogue rows corrected.** No code was changed.

### #23 — Ledger `cells_root` is ONE felt inside the FAITHFUL 8-felt consensus anchor. GENUINE, DEPLOYED, Kind C. Soundness MODERATE-HIGH / availability NONE.

**A detector had this as SAVED ("bound WIDE, limb 0 + the 8-felt completion group at 169..175"). That
verdict is WRONG, and the flip is this sweep's worst find.** The completion lanes exist in the layout
but are **ZERO in the producer** — `cell/src/commitment.rs:773-776`, verbatim: limbs `169..=175` are
"the circuit-only `cells_root` 8-felt completion group (lanes 1..7 — **ZERO in the producer**, filled
by the createCell trace generator)". So on every turn that is not a createCell/factory/spawn, the
committed `cells_root` is lane 0 alone.

- **The value.** `turn/src/rotation_witness.rs:297` `pub fn cells_root(ledger: &Ledger) -> BabyBear`
  — a sorted-heap existence fold over the WHOLE present-cell set (`hash_bytes(id.as_bytes())` keys,
  existence bit `ONE`, through `heap_root::compute_heap_root_entries -> BabyBear`,
  `circuit/src/heap_root.rs:528`). Natively one felt, ~31 bits.
- **Where it lands.** `pre[0] = ctx.cells_root` (`cell/src/commitment.rs:1109`) inside
  `compute_canonical_state_commitment_v9_felt8` — the CHIP 8-felt chain. The wide chain is faithful;
  the *component* is not. The tell is inside ONE struct (`V9RotationContext`, `commitment.rs:790-820`):
  `nullifier_root`, `commitments_root`, `revoked_root` are all `dregg_circuit::Faithful8` with
  documented completion lanes; `cells_root` and `iroot` are bare `BabyBear`. **This is the `Faithful8`
  type wall's complement, in the same 30 lines as three uses of it.**
- **What rides on it.** The DEPLOYED consensus anchor. `turn/src/state_commit.rs:121` builds the ctx;
  `consensus_state_commitment` → `cell_state_commitment` is stamped as `pre_state_hash` /
  `post_state_hash` on every turn receipt (`turn/src/executor/execute.rs:596,691,1479`), and
  `state_commit.rs`'s own "What the quorum signs" says `TurnReceipt::receipt_hash` (domain
  `dregg-receipt-v5`) absorbs both ⇒ **the executor signature signs it and the federation receipt QC
  (BLS threshold) aggregates over it.** The module's own §2 states the consequence plainly: the anchor
  "binds the agent cell's own state faithfully and the rest of the ledger only through the
  `cells_root` *existence* fold (limb 0)". That "only" is ~31 bits.
- **The absent-agent case is worse: the anchor IS the narrow felt.** `absent_cell_commitment`
  (`state_commit.rs:170-172`) commits an all-zero limb vector with `limbs[0] = ctx.cells_root` under
  `iroot`. Its docstring's claim — "still MOVES when the set of present cells moves" — holds at 31
  bits: two present-cell sets colliding on the fold give **one signed post-state anchor** for two
  different ledgers.
- **Soundness pricing: ~2^31 OFFLINE, the #20 amplifier is present.** Keys are
  `hash_bytes(CellId)` and `CellId::derive_raw` is BLAKE3 over attacker-chosen
  `(public_key, token_id)` (`types/src/lib.rs:901`), so candidate ids are ground offline with no chain
  interaction until the hit; only the final planted cell costs a real createCell turn. Effect:
  present-cell-set equivocation under an honest signature/QC (agent-present case: the other cells'
  existence; agent-absent case: the entire post-state). NOT a direct balance forgery — the agent leg's
  own limbs are faithful — which is why this is MODERATE-HIGH rather than HIGH.
- **Availability NONE** for the commitment itself (same projection both sides: the executor computes
  the pre and post anchor from its own ledger). The *related* `cellsFreshOp` `.absent` map-op on limb 0
  (`trace_rotated.rs:1668-1676`) is the #20 geometry — a colliding new-cell key over-includes ⇒ an
  honest createCell goes UNSAT — but that key is #5's already-catalogued family, not this entry.
- **Kind C, and cheaper than most C sites: the wide scheme already exists and is already used three
  fields away.** `CanonicalHeapTree8` / `heap_root::empty_heap_root_8` / `root8()` are the same
  primitives `nullifier_root`/`commitments_root`/`revoked_root` ride, and the createCell trace
  generator already fills lanes 1..7 of this very group. The close is: make `cells_root` return the
  `root8` octet and fill limbs 169..=175 in the CELL/TURN producer (not only the createCell generator).
  **Anti-launder:** the fold must be 8-felt end-to-end over the real cell-id preimages — re-hashing the
  existing 1-felt `cells_root` is `finalSqueezeOnly_still_conflates` (#12). Committed-state binding
  change ⇒ flag-day, ember-gated; NOT a `MapOp` key change and NOT new combinatorics.

### #23 — CLOSED 2026-07-24. The repair was PRODUCER-ONLY; the price is a receipt/consensus epoch.

**The lead question the repair had to answer first — producer-only, AIR, or consensus epoch? — has a
three-part answer, established by read before anything was changed.**

**(i) The AIR constrains limbs 169..=175 ONLY under the createCell / factory / spawn selectors.** The
`.cells` group is the subject of exactly two `MapOp`s, `cellsFreshOp` (`.absent`) and `cellsInsertOp`
(`.aafiInsert`), both `guard := .var sel` and both appended only by `createCellV3` / `factoryV3` /
`spawnV3` (`Emit/EffectVmEmitRotationV3.lean:2850-2890`; the member lists at
`AlgoStarkSoundFanoutMemory.lean:284-316`). `rotated178` is a pure column ALLOCATOR — `Legal` obliges
disjointness / bounds / body-alignment and **nothing about a limb's value**, so no constraint pins
169..=175 to zero on any member. On every non-birth member those seven limbs are absorbed by
`wireCommitR` (they are `< NUM_PRE_LIMBS`) and gated by nothing at all.

**(ii) Filling them changes NO descriptor byte and NO VK — only the committed VALUE.** The trace's
rotated blocks take those limbs straight from the producer: `fill_block`
(`circuit/src/effect_vm/trace_rotated.rs`) opens with
`row[base..base + NUM_PRE_LIMBS].copy_from_slice(&w.pre_limbs[..NUM_PRE_LIMBS])`, then recomputes the
chain and `STATE_COMMIT` on this row's own limbs. So a producer that fills the group is carried into
the trace by copy, the chain stays satisfiable, and the descriptor — which encodes columns and ops,
never producer values — is byte-identical. **No VK regen, no Lean AIR change, no `MapOp` key change.**

**(iii) It IS a receipt/consensus epoch, and the price is exactly that.** Every
`pre_state_hash` / `post_state_hash` moves (the anchor absorbs limb 0 and 169..=175, and lane 0 itself
moves too — the 8-felt fold is a genuine `node8` re-fold, not a widening of the old value). Therefore:
`TurnReceipt::receipt_hash` (`dregg-receipt-v5`) moves ⇒ the executor signature signs a different
message ⇒ the federation receipt QC aggregates over a different body ⇒ `receipt_stream_root` and the
`AttestedRoot` quorum move. **Retained receipts do not verify against re-derived anchors across the
boundary, and `verify_receipt_chain`'s continuity check
(`curr.pre_state_hash == prev.post_state_hash`) is only satisfiable within one side of it.** The
`AttestedRoot::merkle_root` / `FinalizationVote::merkle_root` BLAKE3 whole-image restart anchor is
UNAFFECTED (it is `dregg_persist::canonical_ledger_root`, not this value). Priced against reality: the
devnet ledger was already lost on reboot, nothing is deployed, and the campaign has run this exact
flag-day before (the REVOKED-ROOT base widen 37→38), so the epoch costs a re-genesis, not a migration.

**What changed.**
- `turn/src/rotation_witness.rs` — `cells_root(ledger) -> Faithful8` via
  `heap_root::compute_canonical_heap_root_8_entries` (was `compute_heap_root_entries -> BabyBear`);
  `produce` writes the group with `write_lanes(&mut pre_limbs, CELLS_ROOT_GROUP)`.
- `cell/src/commitment.rs` — **the TYPE**: `V9RotationContext.cells_root : dregg_circuit::Faithful8`,
  matching its three `Faithful8` siblings; `compute_rotated_pre_limbs` writes the group.
- `turn/src/state_commit.rs` — `absent_cell_commitment` fills the group (the case where the anchor WAS
  the narrow felt).
- Consumers rewired to the producer rather than to `pre_limbs[0]`: `sdk/src/cipherclerk.rs` (the live
  producer cross-check), `sdk/tests/{sovereign_rotated_c1,sovereign_rotated_wide,executor_welded_commit}.rs`,
  `circuit/tests/{effect_vm_rotation_flip,effect_vm_wide_roundtrip}.rs`, `perf`, `turn-prover` tests.
- Lean docstrings (`Emit/RotatedLayout.lean`, `Emit/EffectVmEmitRotationV3.lean`) — they ASSERTED
  "producer-zero"; leaving that in the authoritative source is what let a detector read the layout and
  call the site SAVED. No emitted object changed (comments only; the group table is unchanged).

**ANTI-LAUNDER — the fold's internals, checked, not assumed.** `compute_canonical_heap_root_8_entries`
is wide at every intermediate: each leaf is `HeapLeaf::digest8` = `chip_absorb_all_lanes(3, [addr,
value, next_addr])` (all 8 output lanes of the arity-3 chip) and each node is `heap_node8` =
`chip_absorb_all_lanes(16, L8 ‖ R8)` (all 8 lanes of the arity-16 `node8` chip); every value in the
fold is `[BabyBear; 8]`, including `EMPTY_SUBTREE_ROOTS_8`. There is **no ~31-bit waist anywhere** and
the wide root is **not** a re-hash of the narrow one (a pinned assertion: `wide.limbs()[0] != narrow`).
This is not `finalSqueezeOnly_still_conflates` (#12). Contrast the `iroot` sibling, which IS that
shape and is untouched — see below.

**FALSIFIED, both polarities** (`turn/tests/cells_root_width_falsification.rs`, 3 tests + an
`#[ignore]`d reproducible search). Two present-cell sets `{agent, filler_4084}` and
`{agent, filler_7322}`, identical agent leg, distinct filler ids AND distinct existence keys:
- **BEFORE** — the pre-fix producer shape (lane 0 = the narrow fold, completion ZERO) gives ONE anchor
  for both ledgers, agent-present AND agent-absent. The narrow fold value is pinned (`1976398739`).
- **AFTER** — `consensus_state_commitment` and `absent_cell_commitment` both SEPARATE them.
- The pair was found in **7 323 offline folds** (~3 s, unoptimized, no chain interaction). The analytic
  birthday price for a full 31-bit fold is ~2^16 samples; landing at 7.3k is either a lucky draw or a
  hint that the fold carried fewer than 31 effective bits. One sample settles neither — recorded as an
  observation, not a claim, and the search is kept runnable rather than asserted.

**WHAT THIS DOES NOT CLOSE — three residuals, all named at the sites.**
1. **The tree's KEYS are still ONE felt.** A leaf address is `heap_addr(CELLS_COLLECTION,
   hash_bytes(id))`, a 1-felt digest of a 32-byte `CellId`. Two ids whose key folds collide produce
   literally the SAME leaf at ANY root width. That is the accumulator-KEY class (kind D — #5/#9/#11/#20),
   un-widenable producer-side (`DescriptorIR2.lean:301-313`'s scalar `key : EmittedExpr`), and it must
   ride the `MapOp` key epoch. The falsifier REFUSES a key-collision pair so the fixture cannot launder
   one as a root collision.
2. **Width is not content, and it is not AIR-forced.** `cells_root` is an EXISTENCE fold — an
   attacker-visible set of present ids, not their states — and on every non-birth member NOTHING in the
   AIR constrains it. It is an executor-computed witness limb absorbed by the commitment chain.
3. **The executor's cells tree and the circuit's accounts tree are DIFFERENT OBJECTS** (found while
   pricing this, worth its own entry): the anchor folds `heap_addr(CELLS_COLLECTION, hash_bytes(id)) ↦ 1`
   through `CanonicalHeapTree8`, while the createCell/factory/spawn grow-gate opens
   `HeapLeaf::entry(cell_key, cell_key)` over the threaded `before_accounts` (empty `&[]` on the deployed
   wide recipe, `turn-prover/src/rotation_witness.rs`). The generator OVERWRITES limb 0 (and now the
   whole group) with its own root, so on a birth turn the executor's committed anchor and the proof's
   published `STATE_COMMIT` do not describe the same tree. That divergence predates this repair and is
   NOT closed by it. **→ ADJUDICATED as #32 below: REAL, broader than "birth turns", and NOT a
   felt-width wound (cost is ZERO, not 2^n) — a model/producer CORRESPONDENCE gap.**

**`iroot` — the other bare `BabyBear` in `V9RotationContext` — is NOT closed by this move, and cannot
be by the same shape.** It is a left-leaning MMR fold whose every intermediate `root: BabyBear` is
~31 bits (`rotation_witness::iroot`), i.e. widening only its carrier would be exactly the
`finalSqueezeOnly_still_conflates` laundering this entry's anti-launder check exists to refuse — the
whole chain has to be re-folded at 8 felts. It stays DOMINATED-BY-ABSENCE for now (#28: the executor's
`consensus_ctx` pins it to ZERO and no deployed path opens a receipt against it) and remains its own
**standing falsifier**: the moment a live receipt-index MMR root is threaded into the anchor, the
deployed consensus commitment reacquires a ~31-bit component, and this repair will not have covered it.

### #32 — The executor's cells tree and the circuit's accounts tree are DIFFERENT OBJECTS. GENUINE. **NOT A FELT-WIDTH WOUND** — a model/producer CORRESPONDENCE gap, catalogued here only because #23's residual 3 points at it. Soundness NONE on the deployed executor path (fails closed) / OVER-CLAIM on the light-client surface / availability NONE. Cost to exploit the over-claim: **ZERO**, not 2^n.

**Why it lives here and not in the felt-width catalogue.** Nothing here is narrow. Both trees are
faithful 8-felt `CanonicalHeapTree8` folds; widening changes nothing. The wound is that the two
folds are over **different sets, keyed in different domains, with different values, under different
insert laws** — a correspondence failure, not a width failure. If the felt-width campaign ever spins
out a "producer↔model correspondence" catalogue, this row moves there whole.

**THE TWO OBJECTS, quoted.**

- **Executor (the consensus anchor's component).** `turn/src/rotation_witness.rs:323`
  `cells_root(ledger) -> Faithful8`: one existence leaf per **present cell in the whole ledger**,
  `HeapLeaf::entry(heap_addr(CELLS_COLLECTION, hash_bytes(id)), 1)`, folded by `CanonicalHeapTree8`
  (sort by `addr`, dedup, relink, **sorted-compact rebuild**). Lands at limb 0 ‖ 169..=175 via
  `compute_rotated_pre_limbs`, chip-chained by `state_commit::consensus_state_commitment` into the
  receipt `pre_state_hash`/`post_state_hash`.
- **Circuit (what `STATE_COMMIT` absorbs on a birth turn).**
  `circuit/src/effect_vm/trace_rotated.rs:1687` `generate_rotated_create_cell_trace_with_accounts_tree`:
  `before_tree = CanonicalHeapTree8::new(before_accounts)` over a **caller-supplied** leaf set, and
  `after = before_tree.insert_witness_aafi(HeapLeaf::entry(cell_key, cell_key))` — **append-at-free-index**,
  not the sorted-compact rebuild. `cell_key = trace[0][PARAM_BASE + key_col]`, i.e. `create_hash[0]`
  (`trace.rs:686`), the limb-0 projection of `BLAKE3(public_key ‖ token_id ‖ balance)`
  (`turn/src/executor/effect_vm_bridge.rs:246-253`). The Lean is the same object:
  `EffectVmEmitRotationV3.{cellsFreshOp,cellsInsertOp}` — `key := .var keyCol`, `value := .var keyCol`,
  `op := .aafiInsert`, `root/newRoot := before/afterCellsRootGroup`.

**FOUR independent divergences**, so this is not one object under two encodings:
1. **Key domain.** `heap_addr(CELLS, hash_bytes(CellId::derive_raw(pk, token)))` vs the raw felt
   `create_hash[0]`. Different preimage (the circuit's includes `balance`, the id's does not) *and*
   different projection (Poseidon2 fold + collection tag vs a BLAKE3 lane-0 `u32`).
2. **Value.** existence bit `1` vs the key as its own value (`entry(k, k)`).
3. **Population.** the whole ledger vs `before_accounts`, which every deployed caller passes as
   **`&[]`** (`sdk/src/cipherclerk.rs:6050,6070,6093`; `sdk/src/full_turn_proof.rs:3121`).
4. **Insert law.** sorted-compact rebuild vs AAFI append-at-free-index.

**PREMISE CORRECTION — it is NOT birth-only.** The key/value/insert-law divergence is birth-only (only
the grow-gate generators overwrite the group; `fill_block` otherwise carries the producer's value by
`copy_from_slice`). But a **population** divergence is on EVERY turn: the deployed producer builds its
`cells_root` from `ctx_ledger`, a **single-cell ledger holding only the before-cell**
(`sdk/src/cipherclerk.rs:5806-5807`), while the anchor folds the executor's whole ledger. So the two
values disagree on every turn with more than one cell; birth is where they stop being even the same
*kind* of object.

**DIRECTION — (b) coverage, not (a) soundness. NOTHING reconciles them.** The executor's anchor is not
weakened: it genuinely folds the executor's cells tree. The proof's limb 0 is a *different,
prover-chosen* object, and the executor's verifier never recomputes it — `verify_one_cohort_run`
reconstructs PIs from **all-zero placeholder** block witnesses and OVERRIDES the 16 wide commit PIs
from the stored OLD / claimed NEW sovereign commitments (`proof_verify.rs:1192-1195,1407-1411`), so
limb 0 is never compared with anything the executor holds. The nearest candidate for a reconciling
check is the producer-side cross-check in `cipherclerk.rs:6199-6239` — and it is **explicitly skipped**
for grow-gate leads (`lead_is_grow_gate`), on the stated ground that "the executor anchors it through
the grow-gate's own opening". It does not; see reachability.

**REACHABILITY (established before pricing).**
- **Producer: LIVE.** cipherclerk mints createCell / factory / spawn wide proofs
  (`generate_rotated_{create_cell,create_from_factory,spawn}_wide`), all at `before_accounts = &[]`.
- **Deployed executor verify: UNREACHABLE, fails closed.** `verify_one_cohort_run`'s PI-reconstruction
  dispatch (`proof_verify.rs:1201-1356`) has **no birth arm**; a birth lead falls through to
  `generate_rotated_transfer_shape_wide` → 66 PIs, while the resolved descriptor wants 67
  (`createCellVmDescriptor2R24` / `spawnVmDescriptor2R24`) or 83 (`factoryVmDescriptor2R24`) —
  registry-committed values. The `dpis.len() != desc.public_input_count` gate (`proof_verify.rs:1385`)
  rejects **before** the cap-open candidate set is built, so `spawn{,Write}CapOpenVmDescriptor2R24`
  never gets a chance either. No birth turn commits through the proof-carrying path.
- **SDK chained full-turn path: explicit NAMED refusal** for birth leads
  (`sdk/src/full_turn_proof.rs:478-490`).
- **Pure wire / light-client verify (`verify_effect_vm_rotated_with_cutover`) DOES accept a birth
  proof** — and has **no in-tree production caller** (tests and doc references only).
- Hosted (non-sovereign) births run with **no proof at all**.

**SOUNDNESS — the over-claim, priced honestly.** The birth family is advertised as light-client
FORCED-ON-WIRE for freshness: Lean `EffectVmEmitRotationV3` says "a re-creation of an existing cell id
has no bracketing witness and is UNSAT (no account-id collision)", and
`circuit/tests/vk_epoch_birth_light_client_binding.rs`'s header terminates its binding chain at
"key ∉ BEFORE". **That last link does not reach the ledger.** `.absent` is opened against a tree the
prover chooses, which is EMPTY on every deployed producer path, and which is keyed in a domain
disjoint from the executor's — so a present cell is a non-member at the gate's key *even when the
executor's real leaf set is threaded*. **Cost to exhibit: ZERO.** No grinding, no collision, no 2^31;
the collision is simply invisible to the gate. ⚑ Do not price this as a width wound.
What the gate *does* force is real and holds: the after-root is the genuine AAFI insert of the
published key into the published before-root (forged and frozen after-roots are UNSAT — both
polarities exercised in that same test). It just says nothing about the ledger.

**AVAILABILITY — NONE.** The gate never refuses an honest turn on this account (the empty before-set
always brackets). The adjacent liveness fact — birth turns cannot ride the proof-carrying executor
path at all — is the pre-existing coverage gap named above, not a cost of this.

**EXHIBIT.** `turn/tests/executor_cells_tree_vs_circuit_accounts_tree.rs`, 3 tests, no proving,
~0.1 s:
1. `executor_cells_leaf_construction_is_the_deployed_one` — the quote check (also pins the private
   `CELLS_COLLECTION == 0`), so the rest is not argued against a reconstruction.
2. `circuit_accounts_limb_is_independent_of_the_executor_ledger` — two ledgers with **different**
   `cells_root` produce **byte-identical** committed limb-0 groups (BEFORE and AFTER), neither equal
   to the producer's own committed group, and the AFTER root is not the executor's post-birth
   `cells_root`. The proof's tree is a free-floating prover object.
3. `freshness_gate_admits_the_birth_of_an_already_present_cell` — the money exhibit. A cell that IS in
   the ledger (and whose re-creation the executor refuses, `CellAlreadyExists`) is born again through
   the deployed wiring, at `&[]` **and** with the executor's real leaf set threaded; the opposite
   polarity (a before-set carrying the gate's OWN key) is refused, so the tooth is live and this is an
   ENCODING miss, not a dead gate. **MUTATION CANARY run:** forcing `create_hash[0] :=
   heap_addr(CELLS, hash_bytes(id))` flips it to a distinct RED at the key-domain assertion — i.e. if
   the encodings agreed, the bracket WOULD see the collision. Restored, green.

**WHY THERE IS NO BYTE-SAFE FIX (scoped, deliberately not forced).** Aligning the two requires all
three of: (i) the AIR's map-op key changed from `create_hash[0]` to the executor's addr encoding
(Lean `DescriptorIR2`'s scalar `key : EmittedExpr`, plus the executor bridge putting that felt in
`param0`), (ii) the leaf value changed from `k` to the existence bit `1`, and (iii) the insert law
reconciled — AAFI vs the executor's sorted-compact rebuild. All three are **descriptor/VK bytes**, and
they ride the same `MapOp` key epoch as felt-width #5/#11/#20. It also needs the producer to thread
the executor's real leaf set, which the **ledgerless** SDK producers structurally cannot do — the
same shape as the `.absent` divergence adjudicated elsewhere in this sweep. So: model the deployed
reality, do not force an equivalence that does not hold. Until the epoch runs, the honest statement is
**"the birth grow-gate binds the published before/after accounts roots to each other, and to nothing
in the executor's ledger."**

**Related, noted not chased.** `TurnReceipt::{pre,post}_state_hash` carries two different objects
depending on path: `consensus_state_commitment` on the classical path (`executor/execute.rs:596,694,1484`)
but the sovereign OLD/NEW commitments on the atomic path (`executor/atomic.rs:653-654`). Same field,
two meanings — its own question, not this one.

### #24 — The cap LEAF's `target` (and `breadstuff`) is a 1-felt fold INSIDE the faithful 8-felt leaf digest. GENUINE, rung-level, Kind D. Soundness HIGH-when-anchored / NONE today / availability NONE.

Distinct from #3 (the cap **root**) and #5 (accumulator **keys**): this is a leaf **VALUE** fold, so
the leaf digest's proven injectivity does not reach it.

- **The value.** `circuit/src/cap_root.rs:209` `pub target: BabyBear` = `fold_bytes32(cell_id)`
  (`:254`, `hash_many(&BabyBear::encode_hash(bytes))`), minted at `cell/src/commitment.rs:547`
  (`target: cap_root::fold_bytes32(cap.target.as_bytes())`). `breadstuff` rides the same fold; the
  sort key `slot_hash` is 1 felt too. `CapLeaf::digest()` is a faithful 8-lane chip absorb — of a
  7-tuple whose `target` limb is already a 31-bit image. **`capLeafDigest_injective` is injectivity in
  the TUPLE; two cells whose ids fold equal produce literally the same tuple.**
- **Deployed verdicts today do NOT ride on it — verified, both legs.** (1) The runtime authorizes over
  FULL `CellId`s: `cap.breadstuff.as_ref() == Some(token) && cap.target == target_id`
  (`turn/src/executor/authorize.rs:1329`), `if cap.target == *from` (`apply.rs:714`) — wide,
  fail-closed. (2) The deployed light-client leg binds wide but against a CALLER-declared leaf:
  `verify_full_turn_bound` step 9 compares `proof_leaf_digest != expected.leaf.digest()` and
  `proof_cap_root != expected.cap_root`, both 8-felt (`sdk/src/full_turn_proof.rs:5249-5265`). (3) The
  in-AIR `targetBindGate` (`Dregg2/Circuit/DeployedCapOpen.lean:225`, `leaf.target = src`) is satisfied
  **by construction** — the producer sets `src: leaf[1]` (`trace_rotated.rs:3293`) — and **no deployed
  verifier anchors the `src` PI**: `CAP_OPEN_TB_PI_SRC/ACTOR/DST` (46/47/48,
  `trace_rotated.rs:3027-3029`) are compared only in `#[cfg(test)]` (`node/src/turn_proving.rs:4950`,
  `circuit/tests/*`), and `CapMembershipWitness::target_is` (`cap_root.rs:975`) has **zero production
  callers**. The Lean names the missing half itself: `TurnIdentityAnchored` is "the NAMED verifier PI
  override … REALIZABLE, deployment analog" (`Dregg2.lean:854`) — i.e. not realized.
- **STANDING FALSIFIER (this entry's whole point).** The moment any verifier anchors PI 46/47/48 to
  values recomputed from the trusted turn, the cap-facet authorization becomes a **live ~31-bit
  authorizing equality** — and the producer half is ALREADY WIRED for it:
  `node/src/turn_proving.rs:1570-1582` publishes `src = BabyBear::new(consumed.leaf_target)`,
  `actor = fold_bytes32(agent.as_bytes())`, `dst = fold_bytes32(to.as_bytes())` on the deployed node
  prove path. Exploit at that point: grind an attacker-owned cell `B` with
  `fold_bytes32(B) == fold_bytes32(A)` (~2^31 offline via `CellId::derive_raw`), hold a legitimate cap
  over `B`, exercise it against victim `A` — the anchored gate accepts. Cross-target capability
  confusion. Availability NONE (a collision can only make a failing authorization pass).
- **The detector's "dangerous model asymmetry" is DEMOTED, and replaced with the precise statement.**
  Claim was: "the Lean apex proves cap authorization over INJECTIVE CellId equality, STRICTLY STRONGER
  than deployed, so the machine-checked soundness is void at deployed width." Read at HEAD, the Lean
  leaf is **faithful**: `DeployedCapTree.CapLeaf.target : ℤ` is documented "the capability's target
  cell id, **folded to one felt** (`cap_root.rs:98`)". The abstract-label equality
  (`capAuthorizesFacet`, `authorizedFacetB` over `Label := Nat`) reaches the deployed narrow felt only
  through the carried encoding contract `DeployedFaithful.backed`
  (`DeployedCapTree.lean:306-312`), which the file itself calls "the runtime-encoding contract". So:
  **not a laundering — a conditional keystone whose hypothesis has an unpriced deployed cost.** At
  deployed width a fold collision makes `leafAt actor src = leafAt actor src'`, so `backed` demands a
  real held cap over BOTH labels: the hypothesis is **falsified for an honest cap set by a ~2^31
  grind**, and that price appears nowhere. Fix: widen `target`/`breadstuff` to 8-felt limb groups
  (arity 7 → 21 leaf), re-point `targetBindGate` at the octet, widen PIs 46/47/48. VK-affecting AND
  committed-state-affecting ⇒ one epoch with #3/#5.

### #25 — `Effect::Burn.target_hash`. ✅ **CARRIER WIDENED (byte-safe, no VK change)**; the "AIR PI" half was a WRONG PREMISE — there is no AIR. Re-verdict: DOMINATED-BY-ABSENCE, Kind C **retargeted at the ANCHOR, not the width**.

**The entry as written (07-24 sweep) was half right. Four premises corrected at HEAD by direct read
plus the COMMITTED DESCRIPTOR BYTES; read the corrections before re-deriving anything from it.**

- ✅ **CONFIRMED** — the carrier was 1 felt: `effect.rs:348` `Burn { target_hash: BabyBear }`, produced
  `hash_to_bb(target.as_bytes())` at `effect_vm_bridge.rs:496`, absorbed as a **single** `push` at
  `helpers.rs:447`, twenty lines above `CellDestroy`'s 8-lane `extend_from_slice`. It was the **LAST**
  1-felt `target_hash` in that enum (CellDestroy / CellSeal / CellUnseal / ReceiptArchive / Refusal
  are all `[BabyBear; 8]`).
- ✅ **CONFIRMED** — `expected_burn_target_bb` is dead: `#[allow(dead_code)]`, zero call sites.
- ✅ **CONFIRMED** — full nodes are safe wide: `apply.rs:3482` gates `if actor != target {
  check_cross_cell_permission(… Action::Send, EFFECT_BURN …) }` over full `CellId`s.
- ❌ **CORRECTED — "pinned per-row to a 1-felt PI slot" describes a RETIRED AIR.** `air.rs`'s own
  header at HEAD: "The v1 hand-AIR (`EffectVmAir` + its `StarkAir` impl) is **RETIRED**; the rotated
  IR-v2 multi-table descriptor is the **sole** effect-VM circuit." The `PiSlot { "burn_target" }` at
  `air.rs:290-294` is a *shape* entry feeding the VK-v2 fingerprint; the constraint
  `s_burn·(param0 − PI[BURN_TARGET_PI])` it documents **no longer exists in any circuit**. The
  Lean-authored deployed descriptor `EffectVmEmitBurn.burnVmDescriptor` (`piCount := 42`;
  `burnRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins ++ selectorGates`) has **no
  gate, hash site or PI binding over `param0`** — its 7 pins are ACTOR_NONCE / INIT_BAL_LO,HI /
  OLD_COMMIT / NEW_COMMIT / FINAL_BAL_LO,HI, and its 4 hash sites are the GROUP-4 state commitment.
  **Machine-checked on the committed registry bytes** (`circuit/descriptors/rotation-v3-staged-registry.tsv`):
  the live member `burnVmDescriptor2R24` (piCount 50, width 1700) references trace col **68**
  (`PARAM_BASE + param::BURN_TARGET`) **ZERO times** across constraints, hash sites and ranges. The
  burn target is an **UNCONSTRAINED WITNESS COLUMN**, not a narrow binding.
- ❌ **CORRECTED — offset 200 is not published.** The rotated leg's PI vector is
  `pis[..V1_PI_COUNT]` (42) + 4 pins (`trace_rotated.rs:650-651`), so `BURN_TARGET_PI = 200` is
  absent from every leg a verifier sees. The sdk's own note says it: "offsets >= 34 [stale; now 42]
  … are absent from the rotated leg."
- ❌ **CORRECTED — "1 felt in the AIR PI *and* in `effects_hash`" is ONE narrowing, not two.**
  `VmEffect::Burn.target_hash` is a single field written once by the bridge; the PI writer and the
  `compute_effects_hash` absorb are two *readers* of it. Widening the field fixes both by
  construction.
- ❌ **CORRECTED — the cost is not "~2^31" for a directly-chosen preimage.** `fold_bytes32_to_bb` is
  the LINEAR form `Σ_i limbs[i]·MIX^i` over `𝔽_p^8`, so a colliding pair is obtained by **one linear
  solve, O(1)** — bump limb 0 by δ and limb 1 by `−δ·MIX⁻¹` (exhibited and asserted in
  `circuit/tests/effects_hash_fold_and_burn_target_width.rs::fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`).
  The ~2^31 figure survives ONLY where the 32 bytes are pinned to a hash image (a `CellId::derive_raw`
  burn target ⇒ second-preimage ~2^31, birthday ~2^15.5). **Every other `fold_bytes32_to_bb` site in
  this catalogue whose preimage a prover picks directly is priced too high by ~31 bits of work.**

**WHAT LANDED (this commit).** `Burn.target_hash: BabyBear → [BabyBear; 8]` (`bytes32_to_8_limbs`
via the bridge's existing `hash_to_8`), the trace anchoring limb[0] into `params[0]` exactly as
`CellDestroy` does, and all 8 limbs absorbed into `compute_effects_hash`. `expected_burn_target_bb`
→ `expected_burn_target_limbs` returning the octet, so **wiring the dead comparer can now only
produce a ~256-bit attributing equality — the narrow twin is retired, not left beside a live
socket** (Kind B discipline applied inside a Kind C site). **No VK / descriptor / registry change**:
`piCount` and every constraint are untouched, and the anchored column keeps its position.

**ANTI-LAUNDER — the widening was COSMETIC until #30 was fixed in the same commit.** The only carrier
the burn target reaches is `compute_effects_hash`, whose published 4-felt output was itself a
function of ONE ~31-bit felt. See **#30**. Widening the component alone would have been the
`finalSqueezeOnly_still_conflates` move; both halves rode one commit.

**RE-VERDICT — DOMINATED-BY-ABSENCE (twice), soundness NONE today, availability NONE.** At HEAD the
target is bound by *nothing*: the AIR does not read it, the PI carrying it is not published, and the
one carrier that does hold it (`PI[EFFECTS_HASH_BASE..+4]`) is bound by no deployed descriptor
either. At the full node the executor recomputes `effects_hash` from `turn.effects` through the SAME
projection it compares against ⇒ #21 geometry, a collision buys nothing. The width was the *third*-order
problem behind two absences.

**STANDING FALSIFIER (re-pointed).** The work is **ANCHORING**, not widening — and the anchor must be
laid against the octet: bind the burn target (or `effects_hash`) into a PI the rotated descriptor
actually pins. Whoever does it inherits ~2^31 mis-attribution the moment they anchor a *fold* rather
than the *limbs*. The pre-fix behaviour is executed, not remembered, by
`burn_target_collision_was_byte_identical_before_the_repair`: a fold-colliding target pair produced a
BYTE-IDENTICAL published 4-felt PI. Blast if anchored narrow: mis-attribution / supply-accounting
ambiguity ("which cell's supply was destroyed"), never privilege escalation. Siblings
`notespend_nullifier` / `notecreate_commitment` (#4) carry the SAME retired three-teeth doc-comment
and are STILL 1-felt carriers — their entry inherits every correction above.

### #26 — The cell-program `HashKind::Poseidon2` hash-lock arm: `PreimageGate` + `KeyRotationGate` bind ~31 bits. GENUINE, LATENT, Kind B. Soundness HIGH-if-selected / availability NONE.

- **The value.** `hash_preimage32` (`cell/src/program/eval.rs:2818-2825`): the Blake3 arm returns the
  full 256-bit digest; the Poseidon2 arm returns `felt_to_bytes32(poseidon2::hash_bytes(preimage))` —
  ONE felt in the low 4 bytes of a 32-byte slot word, **28 structurally-zero bytes** (the #18 padding
  tell: looks 256-bit on the wire, carries ≤31 bits).
- **The two gates.** `PreimageGate` (`eval.rs:1007-1010`): `hash_preimage32(kind,&preimage) !=
  new_state.fields[idx] ⇒ violated` — an HTLC-style knowledge/conditional-release gate. `KeyRotationGate`
  (`eval.rs:1100`): `hash_preimage32(kind,&preimage) != old_fields[d] ⇒ violated` — **the whole KERI
  pre-rotation property**. Under the Poseidon2 arm an attacker who never held the next keys grinds a
  key set whose 31-bit digest matches the committed next-keys register (~2^31 offline, fully
  attacker-chosen `WitnessKindTag::Preimage32` preimage) and **rotates the identity to keys they
  control** — the exact catastrophe pre-rotation exists to prevent. An honest executor does not save
  this: it faithfully accepts the colliding preimage.
- **Not live: no deployed program selects the narrow arm — verified by read.** Deployed KERI/identity
  installs Blake3 (`starbridge-apps/polis/src/lib.rs:1654`, `sdk/src/guardian_rotation.rs:161`), the
  storage queue gate is raw `blake3::hash` (`storage/src/programmable.rs:650`), and
  `impl Default for HashKind = Blake3` (`cell/src/program/types.rs:286-290`). Poseidon2 appears only
  in `cell/src/program/tests.rs`, `game-turn-slice/tests/game_program_compiler.rs:194`,
  `circuit/tests/poseidon2_cell_circuit_kat.rs:37`. **But the arm is reachable by any SDK author:**
  `sdk::program::preimage_gate(idx, hash_kind)` (`sdk/src/program.rs:70`) takes the kind from the
  caller and `sdk-py` parses `"poseidon2"` (`sdk-py/src/lib.rs:1382`).
- **The footgun is aimed at exactly the wrong reader.** `HashKind::Poseidon2`'s doc-comment is
  "Poseidon2 — preferred for in-circuit verification" (`types.rs:282`) while **both** constraints have
  **no in-circuit projection at all**: `turn/src/executor/mod.rs:470-475` lists them as
  executor-enforced, with the comment "`KeyRotationGate` (pre-rotation) is executor-enforced like
  `PreimageGate`; no AIR projection yet". So the recommendation buys nothing and costs 93 bits.
- **Kind B (retire the narrow twin), not C:** the wide arm is in the same function. Close =
  Poseidon2 arm returns the wide digest (`hash_bytes_8`/`digest8_to_bytes32`), or refuse
  `HashKind::Poseidon2` for these two constraints until it does. No AIR, no VK.

### #27 — The seL4 executor-PD crypto floor: Merkle node, BLAKE3→field, nullifier, and keyed MAC all ~31 bits — and the MAC key is ≤1 felt. GENUINE, frontier/unreached, Kind C/E rooted in the LEAN PORTAL TYPES.

`sel4/dregg-pd/executor-pd/crypto-floor/src/lib.rs`: `dreggcf_poseidon2_2to1` (:134),
`dreggcf_blake3_to_field` (:159), `dreggcf_nullifier` (:195), `dreggcf_keyed_mac` (:224) — every one
returns `….as_u32() as u64`. The doc-comment tells are verbatim: "collision-resistant (Poseidon2 CR,
the carried assumption)" and "A full 256-bit digest does not fit a Nat scalar, so the field-reduced
form is the faithful Nat-shaped result."

- **Additional finding beyond the detector's:** `dreggcf_keyed_mac` derives its BLAKE3 key as
  `key_material[..8] = key.to_le_bytes()` with the remaining 24 bytes ZERO — so the macaroon
  caveat-chain MAC has a **≤64-bit (in practice ≤ field-order, ~31-bit) key space**, not merely a
  31-bit tag. Key recovery at ~2^31 forges arbitrary caveat chains, which is strictly worse than tag
  collision.
- **The width is imposed in LEAN, not in the shim.** `Dregg2/Crypto/PortalFloor.lean`:
  `poseidon2HashExtern : Nat → Nat → Nat` (:140), `blake3HashExtern : List Nat → Nat` (:173),
  `nullifierDeriveExtern : Nat → Nat` (:200), `hmacSha256Extern : Nat → Nat → Nat` (:257). A wide fix
  starts at the portal type (a digest carrier, not a scalar `Nat`); the Rust shim follows. **Kind C/E,
  authored in Lean** — do not "fix" this by widening only the Rust return.
- **Reachability: UNREACHED today, by the crate's own header.** "The demo turn never reaches them (the
  closure routes the portals through in-Lean reference dictionaries, not the externs)" (lib.rs:10-12).
  The only consumers of the `dreggcf_*` symbols are the C shim, the selftest, and
  `sel4/crypto-floor-hosttest`. This is the `firmament-sel4-boots` frontier, not the deployed hbox
  executor. **Severity HIGH-if-reached and broad** (nullifier collision ⇒ double-spend; MAC forgery ⇒
  macaroon attenuation-chain forgery — the whole biscuit model; node collision ⇒ membership
  equivocation), **priced as rung-level because reachability is unconfirmed, not because it is small.**
- **STANDING FALSIFIER:** the day the seL4 executor PD routes a real turn through the `@[extern]`
  portals instead of the in-Lean reference dictionaries — or any PD verdict consumes
  `dreggcf_nullifier` / `dreggcf_keyed_mac` — this becomes a live ~31-bit TCB at four boundaries at
  once.

### #28 — `iroot` (the receipt-index MMR root) is natively 1 felt in the proof-side commitment. DOMINATED-BY-ABSENCE. Soundness NONE / availability NONE.

`turn/src/rotation_witness.rs:320` `pub fn iroot(receipt_hashes: &[[u8;32]]) -> BabyBear` — a
left-leaning Poseidon2 fold whose every intermediate `root: BabyBear` is ~31 bits. It is absorbed LAST
into `wire_commit` (:352) **and** into the FAITHFUL `wire_commit_8` (:364,
`Faithful8::from_wire_commit`), plus the circuit twin (`descriptor_ir2.rs:9467`) and
`cell/src/commitment.rs:1404` / `turn/src/state_commit.rs:171`. The docstring is the catalogue's own
tell: the fold is claimed to make "the root bind the WHOLE log … the Rust realization of the Lean MMR
whose `mroot_injective` makes the root bind the WHOLE log" — **`mroot_injective` cannot survive a
31-bit image**; the Lean statement is over felt-valued leaves, the deployed image is 2^31 wide.

- **Why NONE today: nothing OPENS a receipt against it.** Tree-wide, `iroot` is only ever *absorbed*
  (commitment producers, the descriptor twin, tests). Receipt authenticity rides on the signature
  chain (`verify_receipt_chain` / `verify_receipt_signature`), never on an `iroot` MMR inclusion proof.
- **Sharpening a detector claim:** the DEPLOYED consensus anchor does not even carry it —
  `state_commit.rs:124` sets `iroot: BabyBear::ZERO` in `consensus_ctx`. So the narrow `iroot` lives on
  the *prover-side* rotated commitment / circuit `STATE_COMMIT`, and the executor's signed anchor binds
  no receipt log at all. (That divergence is a separate question from felt width; noted, not priced.)
- **STANDING FALSIFIER:** any deployed gate that authorizes a receipt or event by an MMR inclusion
  proof against `iroot`, or compares an expected `iroot` recomputed from a claimed receipt log,
  converts this to a live ~31-bit binding of the **entire receipt log** (~2^31 offline; a turn's
  emitted events shape the leaves, so the domain is attacker-influenceable). **Kind D.**

### #29 — `verify_full_turn_bound`'s NARROW-leg state-commit endpoints. DOMINATED (#21 geometry). Soundness NONE / availability NONE.

`sdk/src/full_turn_proof.rs:5140-5150`: for a leg where `leg_is_wide(leg)` is false (the cap-open
residual, or a non-rotated v1 leg) the 8-felt anchor is `before[0] = pi[OLD_COMMIT]`,
`after[0] = pi[NEW_COMMIT]`, lanes 1..7 zero — and the endpoint/adjacency compares then run over those
`[felt,0,…]` arrays.

**Saving conjunct, quoted, and it runs on the same path.** The deployed caller derives its `expected_*`
by the SAME projection from its OWN authoritative pre-state, never from the proof:

> ```rust
> None => (
>     wide_from_felt(initial_vm_state.state_commitment),
>     wide_from_felt(pi[dregg_circuit::effect_vm::pi::NEW_COMMIT]),
> ),
> ```
> (`node/src/turn_proving.rs:941-944`, and identically at `:1205-1208`; `wide_from_felt` at `:136`
> is `wide[0] = felt`.)

Both sides are the same projection of the same locally-computed value (`pi` here is the node's OWN
re-generated trace, not the proof's claim) ⇒ #21 geometry: a collision can only make a check that
should fail PASS, and the node has no adversarial preimage freedom against its own state. The separate
executor mirror binds the octet unconditionally (`turn/src/executor/proof_verify.rs:1392-1404`, "the
1-felt waist is GONE").

- **The falsifier's NEAR-MISS, found and named rather than left implied.** There IS a foreign-proof
  consumer: `discord-bot/src/commands/proof_verify.rs:77,93` runs `verify_full_turn` on submitted
  bytes. It does **not** convert #29, because it takes BOTH anchors from the artifact itself
  (`let (old_commit, new_commit) = extract_commits(&composed.sub_proofs)?`) — a collision buys nothing
  against a self-supplied anchor. What it IS: **the #22 self-anchoring disease in a shipped consumer**
  (a verifier reading its trust anchor off the thing it is verifying). Width-independent, informational
  surface (a bot display, no ledger verdict) — logged here so the next person does not mistake it for
  the falsifier firing.
- **STANDING FALSIFIER:** a verifier that binds a FOREIGN `FullTurnProof`'s narrow-leg anchors against
  an **independently trusted** state (a peer-shipped `(old_commit,new_commit)`, or a light client with
  its own head) ⇒ ~2^31 offline grind of a fake pre-state colliding at lane 0 (balance/nonce/fields/
  record_digest all vary; `cap_root` stays pinned wide by step 9). The two live narrow-leg producers to
  watch are the cap-open residual and the `not(recursion)` v1 fallback. **Kind D.**

### #30 — `PI[EFFECTS_HASH_BASE..+4]`'s four "independent squeezes" were FOUR FUNCTIONS OF ONE ~31-bit FELT. GENUINE, ✅ **FIXED** (byte-safe, no VK change). Found while tracing #25.

**This is the anti-launder answer for the whole `compute_effects_hash` family — and it says ~15
already-landed widenings inside that function bought NOTHING at the PI boundary until now.**

- **The find.** `compute_effects_hash_4` (`circuit/src/effect_vm/helpers.rs`) was
  `[h, hash_4_to_1([h,1,0,0]), hash_4_to_1([h,2,0,0]), hash_4_to_1([h,3,0,0])]` with
  `h = compute_effects_hash(effects).0`, a **single `hash_many` squeeze**. Every published lane was a
  function of that one felt, so the 4-tuple's image had at most `p ≈ 2^31` points and any two effect
  lists agreeing on `h` produced a **byte-identical `PI[EFFECTS_HASH_BASE..+4]`**. Its doc-comment
  claimed "4 independent squeezes, giving ~124-bit collision resistance." The true figure was
  ~2^15.5 birthday — the campaign's #1 recurring tell (a doc-comment asserting collision resistance
  over a value squeezed to one felt) sitting on the effects binding itself.
- **Why it retro-prices the other work.** `effects_hash_inputs` deliberately absorbs 8 lanes for
  `CellDestroy` / `CellSeal` / `CellUnseal` / `ReceiptArchive` / `Refusal` / `GrantCapability`, 16 for
  `AttenuateCapability`, each carrying a "32-byte widening: absorb all 8 limbs (~256-bit binding)"
  comment. All of it collapsed through the one-felt output. **This is
  `finalSqueezeOnly_still_conflates` with the sign flipped:** the preimage was wide and the SQUEEZE
  was narrow, which is the same laundering. `hash_many_8`'s own contract states the law
  ("must not be bolted only onto the final squeeze of a one-felt chain") — the deployed effects hash
  was violating it.
- **THE FIX.** `effects_hash_inputs` split out; `compute_effects_hash_4 = hash_many_8(&inputs)[0..4]`
  — four genuine rate-position sponge squeezes over the REAL preimage, ~124-bit, matching the
  `Faithful8` state commitment beside it in the same PI vector. The narrow legacy
  `compute_effects_hash` is kept (the `EFFECTS_HASH_LO` alias) with its width stated honestly.
  **Byte-safe:** `piCount` unchanged, no hash site or `pi_binding` touches these PIs, the
  effects-hash witness columns (aux 4/5 = trace cols 94/95) are referenced ZERO times by the live
  registry members, so no descriptor byte, fingerprint or VK moves.
- **Reachability (why this is LATENT, not a live close).** The deployed rotated descriptors bind
  **none** of `PI[16..20]` — `burnVmDescriptor2R24`'s 15 `pi_binding`s are `{0,8,20,21,22,23,41,42..49}`
  — which `circuit/tests/vk_epoch_misc_light_client_binding.rs` already asserts as a named residual
  ("a forged declared-hash param is ACCEPTED through the rotated path"). At the full node both sides
  are recomputed from `turn.effects` by the same code ⇒ #21 geometry. So the ~31 bits were dominated
  by a strictly larger absence; the repair makes the *anchoring* work land on a sound base instead of
  on a laundered one.
- **FALSIFIER (both runs executed, `circuit/tests/effects_hash_fold_and_burn_target_width.rs`, 6/6
  green):** `effects_hash_4_no_longer_factors_through_one_felt` (no lane equals the retired
  derivation; every lane moves when the list moves) and
  `effects_hash_4_is_the_wide_sponge_over_the_real_preimage` (the published felts ARE
  `hash_many_8`'s first four squeezes over an independently reconstructed preimage).
- **Kind C→F crossover.** The repair itself is Kind B (swap to the existing wide twin `hash_many_8`,
  retire the derived-lane form). The LESSON is Kind F: **read the SQUEEZE, not only the absorb.** The
  07-24 sweep's sharpening #1 said "a FAITHFUL 8-felt chain can absorb a ~31-bit COMPONENT"; #30 is
  its converse and the sweep did not look for it — **a faithful 8-felt PREIMAGE can be published
  through a ~31-bit SQUEEZE.** Both directions belong in the next detector.

### #31 — `effect_action_binding` — the capability-security weld — is a ~31-bit AUTHORIZING equality, and its "real binding" rationale cites a RETIRED AIR. GENUINE, library surface with NO in-tree consumer. Kind C/E.

- `sdk/src/full_turn_proof.rs::effect_action_binding` is
  `hash_fact(ALLOW_PREDICATE, [compute_effects_hash(effects).0, 0, 0, 0])` — the fact a verifying
  authorization sub-proof must conclude for its derivation to authorize the turn. The bound value is
  **one felt**. As an authorizing equality that is a ~2^31 offline grind over fully attacker-chosen
  effect parameters to make ONE authorization derivation authorize a **DIFFERENT effect list** — the
  exact "a commitment, a signed payload, a membership key, an **authorizing equality**" boundary this
  wound is about.
- **Its stated justification is false at HEAD, twice.** The doc claimed `PI[EFFECTS_HASH_BASE]` is
  "pinned **in-circuit** … via a row-0 boundary constraint (`effect_vm/air.rs` 'Effects hash
  binding')" — that AIR is RETIRED and no deployed descriptor binds those PIs (see #30's registry
  read). And "we bind position 0 … because only position 0 is enforced in-circuit" rested on the same
  retired pin. Corrected in place at the site.
- **Reachability: NOT WIRED.** `effect_action_binding` has zero non-doc callers, and the error
  variant `FullTurnVerifyError::AuthEffectMismatch` is declared with a `Display` arm but is **never
  CONSTRUCTED**. Price as **soundness HIGH / availability NONE on a library surface with no in-tree
  consumer** — the #2 verdict shape. Cheap to close now; it MUST be closed before any consumer wires
  it.
- **The close, and its one blocker.** Since #30, `compute_effects_hash_4` gives four genuine squeezes,
  so `hash_fact(ALLOW, [h0,h1,h2,h3])` is a ~124-bit authorizing equality — the `hash_fact` arity is
  already 4. **Blocked on the derivation rule's single-variable head:**
  `derivation_authorizing_effects` builds `Allow(?0) :- capability(?0)` with `num_variables: 1` and
  one variable head term, so binding four felts needs a 4-variable head whose extra variables are
  range-restricted by the body — a **Lean-authored derivation-circuit** change, not a Rust edit.
  Do not close it by binding four felts of the OLD derived-lane form: before #30 that was exactly the
  laundering.

### Catalogue corrections (three stale rows)

- **#1 BFT finality cert — REMEDIATED at HEAD; the triage table's worst-first row was STALE.**
  `finality_signing_message` is v2 and absorbs ALL EIGHT lanes (`lightclient/src/lib.rs:311-321`,
  domain `dregg-finality-cert-v2\0`, `for f in finalized_root { m.extend_from_slice(&f.as_u32()
  .to_le_bytes()) }`); `FinalityCert.finalized_root : [BabyBear; SEG_ANCHOR_WIDTH]` with
  `SEG_ANCHOR_WIDTH = 8` (`circuit-prove/src/ivc_turn_chain.rs:284`); every vote verifies over
  `signing_message()` (`:402-403`); and the deployed seam compares FULL arrays —
  `if agg.final_root != finalized_root` (`:732`), `if cert.finalized_root != finalized_root` (`:740`).
  The `.as_u32()` calls at `:720-743` are inside the **error-return structs** (diagnostic display), one
  line below the full-array gates. The only lane-0 signing left is a `v1_message` closure INSIDE the
  test `finality_cert_rejects_lane0_colliding_fork` (`:1693-1698`) demonstrating the closed hole.
- **#2 federation membership root — CONFIRMED narrow ([A][?] → [V]), reachability DEMOTED.** The
  narrow read holds exactly as catalogued: `expected_federation_root(&[u8;32]) -> BabyBear`
  (`sdk/src/verify.rs:137-149`; low-4-bytes `u32` branch, else `bytes_to_babybear` folds all 32 bytes
  to one felt), compared single-index at `blinded_pis[PI_ROOT_4ARY] != expected_root` (`:202`) and
  `bound_pis[FEDERATION_ROOT] != expected_root` (`:214`), while the action-binding conjunct **fifteen
  lines below** loops all `ACTION_BINDING_WIDTH = 8` felts (`:216-221`, `circuit/src/binding.rs:53`).
  Threat model confirmed: the attacker builds their own 4-ary ring and chooses every sibling, so the
  ~2^31 grind is offline over a fully-controlled preimage, with one final proof. **But a detector's
  "the path is live" is DEMOTED:** `verify_authorization_proof` is a public SDK export
  (`sdk/src/lib.rs:338`) whose in-tree callers are **only** `verify_production` / `verify_any_tier`
  (themselves with **zero** in-tree callers) and its own tests; `app-framework`/`bridge`/`intent`
  authorize by other paths. Price it as **soundness HIGH / availability NONE on a library surface with
  no in-tree consumer** — cheap to close now, and it must be closed before any consumer wires it.
- **#22 Grain R3 — the triage-table row is STALE (the 07-24 update log already records the close).**
  Working tree confirms: `let aggregate_head = core::array::from_fn(|i| proof.final_root[i].as_u32())`
  (all 8 lanes, `grain-verify/src/r3.rs:277`) and
  `r3_verify(finalized, anchored_head: &[u32; SEG_ANCHOR_WIDTH], expected_vk: &RecursionVk)` (`:366`)
  with the caller supplying the out-of-band VK (`fold_and_status`, `:350-360`: "The proof's own
  `root_vk_fingerprint()` is recomputed and reported, but is NEVER used as the anchor"). Files carry
  `M` in git status plus the new `grain-verify/tests/r3_width_falsification.rs`; the row below is
  updated to CLOSED.

### SAVED verdicts re-verified (a wrong (b) is a missed wound)

Sampled five; **four CONFIRMED, one FLIPPED to genuine (#23)**.

- **CONFIRMED — `attestation_commitment` dominates the narrow `content_commit`** (`deos-hermes/src/
  attest.rs:92-106`): the SAME BLAKE3 hash that absorbs `att.content_commit.as_u32()` also absorbs the
  length-prefixed `pres.sent` / `pres.recv` (the notary-signed body) and `pres.notary_sig` — the
  fingerprint is dominated by the wide transcript, so the narrow weld adds no independent binding.
  #18's real exposure stays the narrator data lane.
- **CONFIRMED — `BoundPresentationInput.final_root` is not a compared boundary**
  (`circuit-prove/src/presentation_leaf_adapter.rs:116`): it is a HIDDEN witness (col 19,
  `bound_presentation_witness.rs:57` "a HIDDEN witness (not a PI)"), consumed only as a preimage of the
  arity-4 chip tag; the tag is chip-lookup-served (a forged tag has no serving row ⇒ UNSAT) and no
  verifier compares `final_root` against anything.
- **CONFIRMED — `aggregate_bilateral_prover` child digests are an identity tag over already-verified
  objects** (`turn-prover/src/aggregate_bilateral_prover.rs:945-971`): each child runs
  `verify_aggregated_bundle(child)?` BEFORE `bundle_digest(child)` is taken, and the load-bearing fold
  is `build_tree_fold_trace(&digests)` over the RECOMPUTED digests. A 1-felt collision conflates two
  already-sound children; it cannot admit an unverified one.
- **CONFIRMED — lightclient `.as_u32()` at `:720-743` is display-only** (see #1 above).
- **FLIPPED — `V9RotationContext.cells_root` is NOT bound wide.** See #23. The completion group the
  detector cited is zero-filled in the producer.

### The sweep itself — modalities, coverage, and what this did NOT cover

**Detector modalities (four, blind, then adversarially merged):** (1) **type-level mixed-width** — a
`[T; 8]`/octet field sitting beside a single-felt field, scanned over Rust struct bodies in
`circuit/ circuit-prove/ cell/ turn/ types/ lightclient/ grain-verify` and over Lean `structure`s in
`metatheory/Dregg2/**` (1720 files); (2) **narrowing-idiom** — every `fold_bytes32_to_bb` /
`fold_bytes32` / `felt_to_bytes32` / `hash_many`-non-8 / `split_u64(x).0` / `.as_u32()` /
`state[0]`/`out[0]` / single-index PI equality across the tree; (3) **Lean-model-vs-deployed** — all
786 `.piBinding`/`piExposure` sites, every `MapOp` key in the deployed RotationV3 descriptor, the
`keysOf`/`keysOf8`/`keysOfW` membership families, `ProofBind`, the `*Encodes` refinement structures,
each traced to its Rust twin **in both directions** (deployed-narrower-than-model AND
model-narrower-than-deployed); (4) **cross-rung seam** — solana/cosmos settlement, eth-lightclient,
`chain/` + all 10 Solidity contracts, `bridge/` action-binding, `federation/` (24 files), grain R1/R2/R3,
the deployed per-turn verifier, the recursion apex, `sdk/src/verify.rs`.

**Re-verification standard applied here:** every claimed GENUINE finding was re-read at HEAD before
being written down, and each was checked for a **dominating full-width compare in the same body** (the
#21 lesson) and for a **deployed AIR stronger than its Lean model** (the `eval_canon_decomp` lesson).
That standard produced three demotions and one flip, all named above: the cap "model asymmetry" (#24),
#2's "live path", and the `cells_root` saved verdict (#23).

**Coverage claim.** Confirmed by read at HEAD: #1 (remediated), #2 (narrow + no in-tree caller),
#3/#5/#9 (still narrow as catalogued), #18 (dominated at the hermes seam), #20/#21 (unchanged),
#22 (closed). Deployed prove/verify, light-client, finality, settlement, and grain R1/R2 paths are
**wide at their actual gates** — the finality signing message and seam, the executor's octet commit
mirror, `verify_full_turn_bound`'s wide-leg tail + step-9 cap binding, the 8-lane settlement
continuity, the 26-limb IR-v2 action binding, and grain's `[u8;32]` head/receipt compares. The five new
GENUINE sites are all in the **complement of both defenses**, as the class predicts: none is in
`check-no-degraded-felt.sh`'s scope under its current pattern, and none flows into a `Faithful8` sink.

**NOT covered (say it, so the next person does not assume it):** no Lean or Rust build/proof run this
pass (read-only) — the R3 working-tree edits were READ, not machine-re-verified; no collision was
executed (all ~2^31 prices are analytic, resting on `fold_bytes32`'s exhibited in-tree collision
`circuit/src/exact_cap_root.rs:505` and the `CellId::derive_raw` BLAKE3 amplifier) — **⚠ corrected
07-24: that exhibited collision is the FREE mod-p alias pair `(0, p)`, so citing it as the basis of
a ~2^31 price had the evidence exactly backwards; it is a witness that the fold collides in O(1) on
directly-chosen bytes. See the re-pricing section**; seL4 PD deployment
status was established only from the crate header and symbol consumers, not from a boot; the Tier-2
4-felt sites (`dsl_leaf_adapter`, `sovereign_leaf_adapter`, `verifier/src/lib.rs:466`) were not
re-priced; `dreggnet-*`, `dungeon-on-dregg` beyond #18, `zkoracle` beyond #18/#19, `attested-dm`, and
`starbridge-v2` beyond #8 were not swept; the whole turn-gossip acceptance protocol was not
exhaustively traced for a foreign-proof anchor consumer (#29's falsifier), though the one foreign-proof
consumer found (discord-bot) was read and classified.

### Should `check-no-degraded-felt.sh`'s three-file scope be widened? YES — and the cheapest widening is a PATTERN change inside the EXISTING scope.

The gate today matches only `fold_bytes32_to_bb($_)` (plus the `[$X; 8]` replicate rule) in three
files (`cell/src/commitment.rs`, `turn/src/rotation_witness.rs`,
`circuit/src/effect_vm/trace_rotated.rs`). Measured against those files at HEAD:

- **The gate is blind to a 32→1 fold in a file it ALREADY scopes.** `cell/src/commitment.rs:547` is
  `target: cap_root::fold_bytes32(cap.target.as_bytes())` — the #24 producer, a 32-byte CellId folded
  to one felt, written straight into a committed leaf, **in a scoped file, unflagged**, purely because
  the narrowing function has a different name. Adding `fold_bytes32($_)` / `$$$::fold_bytes32($_)` to
  the rule's existing `any:` is a **two-line change** and fires on exactly that one live line (the
  `provenance` sibling at `:569` is commented out, and ast-grep does not match comments). Do this
  first: it is mechanically trivial, zero false positives in scope, and it catches a real entry.
- **Adding `felt_to_bytes32($_)` in the same scope** fires on two lines, both of which SHOULD carry an
  earned suppression rather than silence: `:666` (the #3 narrow leg-(1) cap-root gate — the suppression
  cites `CapUniquenessWidth.lean`'s proved redundancy) and `:1371` (the additive 1-felt v9 commitment
  beside the faithful `_felt8` one). The `pub fn felt_to_bytes32` definition at `:692` is not a call
  expression and does not match.
- **New files worth scoping, with the narrow-idiom patterns:** `cell/src/program/eval.rs` (#26 —
  fires on the Poseidon2 arm at `:2822`; it would NOT fire on the legitimate Blake3 arm, since that
  arm calls neither function), `turn/src/executor/effect_vm_bridge.rs` (#25's `hash_to_bb` producer),
  and `turn/src/state_commit.rs` + `turn/src/rotation_witness.rs:297` for #23 — though #23's narrowing
  is *the absence of an octet*, i.e. a bare `-> BabyBear` return in a commitment producer, which no
  call-site pattern can see.
- **`.as_u32()` is NOT lintable and should not be added.** It is a LOSSLESS felt encode in the
  overwhelming majority of uses (each BabyBear < 2^31: `commit/src/accumulator.rs:356` Fiat-Shamir,
  `commit/src/poseidon2_tree.rs:111` `faithful8_from_lanes`, the finality v2 message's own per-lane
  absorb, every error-display struct). A gate that fires there would be turned off within a week —
  the #27 (sel4) and #23 shapes need the **type wall** (kind F), not the linter: a `Faithful8`-style
  carrier on commitment components and portal returns makes narrow-at-a-boundary
  *un-representable* rather than merely flagged. The gate widening buys the two call-site shapes
  cheaply; it does not retire kind F.

## Update log — 2026-07-24

- **#25 CLOSED-as-widened + RE-VERDICTED, and #30/#31 OPENED while tracing it.** The sweep entry's
  soundness half ("1 felt in the AIR PI") did not survive contact with the deployed bytes: the AIR
  that would enforce it is RETIRED, the live `burnVmDescriptor2R24` references the burn-target param
  column **zero** times, and offset 200 is not in the rotated PI vector at all — the burn target was
  UNBOUND, not narrowly bound. Two things landed anyway, together, because either alone is cosmetic:
  the carrier widened to 8 limbs (#25) **and** the fold it rides stopped being four functions of one
  ~31-bit felt (#30). Falsifiers execute the *before* as well as the *after*
  (`circuit/tests/effects_hash_fold_and_burn_target_width.rs`, 6/6). Three doc-comments asserting
  security that HEAD does not provide were corrected at their sites (`pi.rs`'s D5c "three teeth",
  `air.rs`'s burn-target slot, `full_turn_proof.rs`'s "why this is a real binding"). Gate:
  `DREGG_REQUIRE_LEAN=0 cargo test -p dregg-circuit --lib` = **721 passed / 0 failed / 2 ignored**,
  the stated baseline, unmoved.
- **A pricing correction that reaches beyond #25: `fold_bytes32_to_bb` is LINEAR.** It is
  `Σ_i limbs[i]·MIX^i` over `𝔽_p^8`, so where a prover chooses the 32 bytes DIRECTLY, a collision is
  **one linear solve, O(1)** — not a 2^31 grind and not a 2^15.5 birthday. The ~2^31 pricing holds
  only where the preimage is pinned to a hash image (`CellId::derive_raw`). Every catalogue row whose
  narrow value is a prover-supplied 32-byte blob folded by this function is priced ~31 bits too
  expensive. Exhibited (not argued) by
  `fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`.

- **The correction CARRIED THROUGH the whole catalogue — per-row classification (07-24).** The rule
  and the four encoders are at the top of this file; this is the ledger of which regime each
  cost-bearing row is in. **Two rows moved (#18, #19), two are new (#32, #33), one "checked-benign"
  entry was wrong (`canonical_32_to_felts_8`); every other `~2^31` was traced to its byte source and
  STANDS.** The whole job is *who picks the 32 bytes*, so the byte source is named for each.

  | # | narrow value | byte source | regime | verdict |
  |---|---|---|---|---|
  | 1 | `final_root[0]` of `wire_commit_8` | a state-commit fold over the aggregate's own execution | PREIMAGE | ~2^31 STANDS (moot — remediated) |
  | 2 | `expected_federation_root` = `bytes_to_babybear(root)` | expected side is the VERIFIER'S CONFIG; the PI is computed in-circuit over the attacker's 4-ary ring | PREIMAGE, targeted | ~2^31 STANDS. Sub-note: the low-4-bytes branch (`sdk/src/verify.rs:139-146`) is `BabyBear::new(u32)`, so two distinct *configured* roots alias — config hygiene, not an attack surface |
  | 3 | `compute_canonical_capability_root_felt` | attacker-chosen cap leaves through the Poseidon2 cap tree | PREIMAGE, collision | ~2^15.5 STANDS (already priced as birthday) |
  | 4 | note commitment / nullifier as accumulator KEYS (`cell/src/{nullifier_set,commitment_set,shielded_note_set}.rs`, `fold_bytes32_to_bb`) | on the deployed exact-v3 path the nullifier is pinned to the accepted proof carrier (`apply.rs:1434`), so it is a derivation image | PREIMAGE | ~2^31 STANDS **conditionally** — the fold is DIRECT-LINEAR, so any path that admits a wire-chosen nullifier/commitment collapses this to O(1). Named as a standing falsifier, not re-priced |
  | 5 | accumulator leaf keys (nf / cm / revoked) | same fold, same three hash-image sources | PREIMAGE | ~2^31 STANDS. Note the shape: once you hold ANY colliding 32-byte pair from any source, the linear fold puts them on the same leaf for free |
  | 7 | `deco_payment_hash_felt` | `hash_many` over `[amount, felt_of_str(currency), hash_many(encode_hash(recipient)), felt_of_str(intent_id)]`; the strings arrive from Stripe, the recipient is a `CellId` | PREIMAGE | ~2^16 STANDS |
  | 9 | `compress_member(pk)` leaf + `root_felt_from_slot` | leaf: a 32-byte candidate (`Sender` = an ed25519 pk / `Bytes` = arbitrary); root: **read raw from the slot, not folded** | DIRECT-ALIAS (leaf) / N-A (root) | **RESTATE, do not re-price.** The leaf encoder drops 16 bits (O(1) collision) but under `Sender` the bytes are a curve point that cannot be nudged, and under `Bytes` an attacker who can supply arbitrary bytes supplies the honest member's key outright — the lossiness buys nothing at THIS gate. The row's `~2^31` is not a fold cost and should not be quoted as one |
  | 10 | shielded `merkle_root`/`nullifier`/`value_binding` declared `u32` | — | N-A | not a fold collision; #15/#16 dominate (wire-supplied root, unproved value link) |
  | 11 | freshness/revocation root, depth 4 | prover-chosen padding leaves | DIRECT | "grind padding leaves" was never a 2^31 claim; unchanged |
  | 12 | `interface_id` | the method list, folded `hash_many_8` end-to-end at HEAD | PREIMAGE | ~2^31 STANDS (widened + proven) |
  | 13 | sandstorm-bridge | not traced this pass | — | UNPRICED — say so rather than inherit `~2^31` |
  | 18 | `content_commitment` | **the oracle RESPONSE BODY — attacker-authored** | **DIRECT-ALIAS, collision** | **MOVED: ~2^15.5 → O(1)** |
  | 19 | `template_commit` / `output_commit` | **the template segment encoding / the render output — prover-authored** | **DIRECT-ALIAS, collision** | **MOVED: ~2^15.5 → O(1)** (`output_commit` still gated by the `CompactCert` replay tooth) |
  | 20 | `undelegated_spend_ancestor()` sentinel vs the revoked-set insert key `bytes32_to_8_limbs(child_id)[0]` | **`CellId::derive_raw` = BLAKE3 over `(public_key, token_id)`** (`types/src/lib.rs:891`) — the attacker must HIT the fixed public sentinel | PREIMAGE, targeted | **~2^31 STANDS — checked specifically.** The sentinel is computed by the linear fold but is a FIXED PUBLIC CONSTANT the attacker does not get to choose; what they must produce is a child id whose lane 0 equals it, and child ids are BLAKE3 images. Availability HIGH is unchanged. (The entry's own "an adversarial prover mints the same trace, because the AIR accepts any key" remains the cheaper, **width-independent** path — that is the unbound-witness hole, not this row's price) |
  | 21 | `genesis_root[0]` / `final_root[0]` | `turn_anchors8` state folds | PREIMAGE | ~2^31 STANDS; DOMINATED unchanged |
  | 22 | `final_root[0]` vs `anchored_head` | a host-grindable turn sequence's state-commit fold | PREIMAGE, targeted | ~2^31 STANDS — checked; CLOSED anyway |
  | 23 | `cells_root` existence fold | keys are `hash_bytes(CellId)`; ids are BLAKE3 over attacker-chosen `(public_key, token_id)` | PREIMAGE | ~2^31 STANDS analytically — **but see the measured 7,323-fold hit and its 1.2% caveat in the re-pricing section.** Do not quote 2^12.8 |
  | 24 | cap leaf `target`/`breadstuff` = `cap_root::fold_bytes32(CellId)` | **`CellId::derive_raw`, a BLAKE3 image** | PREIMAGE, targeted | **~2^31 STANDS — checked specifically.** Encoder (3)'s alias family does not help: you cannot steer a BLAKE3 output into an aliased chunk of a *chosen victim's* fold without grinding. Severity and the standing falsifier are unchanged |
  | 25 | `Burn.target_hash` | prover-chosen where not pinned to a `CellId` | DIRECT-LINEAR | **O(1)** — the original correction; carrier widened |
  | 26 | `hash_preimage32` Poseidon2 arm | the preimage is fully attacker-chosen (`WitnessKindTag::Preimage32`) | **DIRECT-ALIAS, but the attack needs a TARGETED HIT** | **~2^31 STANDS — checked specifically.** Both gates compare against a value the *honest* party committed earlier (`new_state.fields[idx]`, `old_fields[d]`), so a cheap collision between two attacker preimages is worthless; the KERI pre-rotation break needs the targeted grind. This is the clearest case of "aliasing gives collisions, never preimages" |
  | 27 | seL4 `dreggcf_*` | Poseidon2 / BLAKE3 images; the MAC KEY is a ≤64-bit derivation | PREIMAGE | ~2^31 STANDS (the MAC key-recovery leg was never a fold cost) |
  | 28 | `iroot` MMR | receipt hashes (BLAKE3 images), event-shaped leaves | PREIMAGE | ~2^31 STANDS; DOMINATED-BY-ABSENCE unchanged |
  | 29 | narrow-leg `old_commit`/`new_commit` | a fabricated pre-state ground through the commitment chain | PREIMAGE, targeted | ~2^31 STANDS; DOMINATED unchanged |
  | 30 | `compute_effects_hash` squeeze | Poseidon2 over the effect list | PREIMAGE | ~2^15.5 STANDS (fixed) |
  | 31 | `effect_action_binding` | Poseidon2 squeeze over attacker-chosen effect params | PREIMAGE, targeted | ~2^31 STANDS |
  | 32 | `umem_fold_bytes_v1` | `serde_json` bytes of a `UKey`/`UVal` | **DIRECT-LINEAR** | **NEW — O(1)–2^16** |
  | 33 | umem `Bytes32` value / nullifier key | writer-chosen 32 bytes | **DIRECT-ALIAS, collision** | **NEW — O(1)** |

  **Does the fix ORDER change?** Marginally, and in one direction: **#18/#19 rise past #25/#28/#29**
  and now sit with the HIGH-severity library-surface rows (#2, #31) rather than below them — they
  are live-consumer paths (`bound_attestation_commit` reads the committed narration weld off the
  receipt) whose exploitation cost is now zero rather than 2^15.5. The campaign's TOP of the
  worst-first table does **not** move: #23 is closed, #24's `~2^31` survived the re-pricing intact,
  and the three biggest exposures in this file remain the non-width ones (#15 wire-supplied
  shielded `merkle_root`, #16 the unproved value link, and the unbound-witness columns named at #20
  and #25) — all of which dominate every fold price on this page regardless of which regime it is
  in. **What DOES change is the meta-repair:** kind F part (i) should lint the *encoders*
  (`encode_hash` / `bytes32_to_8_limbs` / `from_bytes_packed` / `canonical_32_to_felts_8` reached
  from prover-chosen bytes), not only the two fold call-sites, and kind C's "the wide scheme must
  fold the REAL PREIMAGES 8-felt end-to-end" needs one more clause: **through a CANONICAL byte→felt
  codec** (`bytes32_to_u16_limbs`), because an 8-felt fold over a non-canonical encoder is still
  O(1) collidable on directly-chosen bytes.

- **No wound already CLOSED was closed at the wrong price — checked, with one qualification.** #1
  (all 8 lanes signed), #12 (8-felt end-to-end fold), #22 (full `Digest8` + caller-supplied VK),
  #23 (`Faithful8` producer), #30 (`hash_many_8` squeeze) and #6/#14 (logic bugs) were all
  remediated by *removing the narrow value*, not by out-pricing an attacker — so none of them
  depended on a 2^31 estimate being right, and each stays sound at O(1). The qualification is #25:
  its widening to `bytes32_to_8_limbs` retires the linear-solve family but not the mod-p alias
  family (see encoder (2) at the top), so the repair is correct for a `CellId` burn target and
  incomplete for any prover-chosen 32-byte carrier that later rides the same projection. That is a
  residual on the repair, not a mis-sized fix: the anchoring work #25 re-pointed at is still the
  first-order item.

- **#20 Spend delegation-ancestor key — NEWLY LOGGED, and the first EARNED
  `check-no-degraded-felt.sh` suppression in the tree.** `63a5bdd362` (the repair that restored the
  deployed `noteSpend` prove path, broken since the 07-23 descriptor sweep) threaded the producer
  half of `7d49b0f449`'s third map-op, `spendAncestorFreshOp`. Its honest "this spend rides no
  delegated capability" sentinel is `undelegated_spend_ancestor()`
  (`circuit/src/effect_vm/trace_rotated.rs:1402,1415`) = `fold_bytes32_to_bb(cred_nul(mint_provenance()))`
  — a 32-byte BLAKE3 nullifier squeezed to ONE felt. The ast-grep gate fired because
  `trace_rotated.rs` is one of its three scoped files. **The disposition below is a suppression, so
  it has to be argued, not asserted** — the reasoning, both directions, is at the site.

  - **NOT a commitment position (so not a law violation in the law's own terms).** The felt lands
    only in `row[PARAM_BASE + 3]` (col 71). The rotated commitment is `recompute_block_commit`'s
    chain over `row[BEFORE_BASE..]` / `row[AFTER_BASE..]` (bases 188 / 427); no PI binds col 71
    (`rotateV3WithNullifierPin` pins `prmCol 0` only). It is a map-op KEY in a witness column — the
    law's own "fine per-effect param projector" case. The ROOT it opens against is already faithful
    (the producer writes `revoked_tree.root8()` into all 8 lanes of `REVOKED_ROOT_GROUP`).
  - **Widening is NOT representable producer-side — verified, not assumed.**
    `Dregg2/Circuit/DescriptorIR2.lean:301-313` types `root, newRoot : Fin 8 → EmittedExpr` but
    `key : EmittedExpr` — a map-op key is ONE felt by construction, and the deployed op is
    `key := .var SPEND_ANCESTOR_PARAM_COL` (`EffectVmEmitRotationV3.lean:2410`). The INSERT side is
    one felt too (`revokedInsertOp` keys `param0` = `child_hash[0]`, `trace.rs:683`), so widening
    only the open side makes the `.absent` op unopenable rather than safer. 8-felt keys = change
    `MapOp` + lex-8 sorted/AAFI bracketing = **VK-affecting Lean AIR**, same epoch as #5/#11.
  - **Soundness: the width buys the attacker NOTHING here. Argued, not waved.** The set is keyed by
    the SAME projection on both the insert and the open side, and a projection is a function, so
    `A` revoked ⟹ `key(A) ∈ set` ⟹ the `.absent` open is UNSAT regardless of what collides with it.
    Collisions only ADD to the set's key-space preimage — they **over**-revoke, never under-revoke.
    A 31-bit collision cannot make a revoked ancestor look fresh at any width. (This is the *inverse*
    of the classic degraded-commitment danger, where a collision swaps the committed value; a
    non-membership op over a same-fold-keyed set has the opposite failure direction. Worth
    generalizing: not every narrow felt in this catalogue is a soundness felt — #5's key family
    deserves the same both-sides check before it is priced as a theft vector.)
  - **Availability: the width IS independently load-bearing, and this one is REAL — ~2^31, cheap,
    permanent, system-wide.** The revoked set is grow-only and its key domain is attacker-writable:
    `RevokeDelegation` inserts `hash_to_8(child_id)[0]`, and `CellId::derive_raw`
    (`types/src/lib.rs:891`) is BLAKE3 over an attacker-chosen `(public_key, token_id)` — so
    candidates are ground **offline**, no chain interaction until the hit. ~2^31 offline hashes find a
    child id whose lane 0 equals a chosen target; one legitimate create+delegate+revoke plants it
    forever. Aimed at THIS sentinel — public, fixed, system-wide — it permanently bricks every
    undelegated `NoteSpend`. Aimed at a victim's real ancestor id it bricks that lineage. With no
    adversary, N ancestors × M revocations collide at ≈ N·M/2^31 (~5% at 10^4 × 10^4), which caps the
    honest registry scale. **It gets worse when we do the right thing next:** today a producer could
    dodge a poisoned key only by exploiting the unbound-witness hole that `7d49b0f449`'s lineage weld
    is meant to close.
  - **Not to be confused with the bigger, separate hole.** Col 71 is an unbound witness column: a
    prover parks any non-revoked felt (this public constant will do) and the op is satisfied
    regardless of the exercised lineage. Zero work, pure soundness, `7d49b0f449`'s named follow-up —
    and **width-independent**, so it neither excuses nor is excused by #20. Both close in the same
    AIR epoch; neither closes the other.
  - **Rejected as a repair:** a producer-side "refuse to revoke a child whose key equals the
    sentinel" guard. It would block the systemic variant *via our own tooling only* — an adversarial
    prover mints the same trace, because the AIR accepts any key. That is a mitigation that looks like
    a fix, i.e. the laundering shape this catalogue exists to catch. Named here, deliberately not
    written.
  - **Kind D**, severity **HIGH for availability / NONE for soundness**. The 3rd `fold_bytes32_to_bb`
    the repair added is `cell/src/derivation.rs:1045`, inside `#[cfg(test)]` — the cross-crate domain
    pin, explicitly out of the law's scope and correct by construction (it must recompute the same
    value from the authority or the pin is vacuous).

- **#21 Whole-chain binding-descriptor endpoints — NEWLY LOGGED, and DOMINATED (not a wound).
  Soundness NONE / availability NONE.** Two sites, one pair, both comparing chain anchors at lane 0:

  - **Producer** `circuit-prove/src/accumulator.rs:968-978` (`finalize_binding_leaf`) —
    `if first != summary.genesis_root[0] || last != summary.head_root[0]`, self-described as
    "binding scalar endpoints", an HONEST narrow check rather than a misleading `X != X` message.
  - **Verifier** `circuit-prove/src/ivc_turn_chain.rs:5485-5497` (tooth 2) — the *deployed*
    half, on every light-client path:
    `let expected_scalar = [genesis_root[0], final_root[0], BabyBear::new(num_turns as u32)];
     if binding_pis[..3] != expected_scalar { … }`.

  **The narrow value is all that exists on this path — verified, not assumed.** The wide anchors are
  in hand on ONE side (`summary.genesis_root` / `head_root` are the genuine 8-felt
  `turn_anchors8` octets since codex #4), but the other side is scalar BY CONSTRUCTION: the seam
  witness is pushed as `self.seam_pairs.push((this_old8[0], this_new8[0]))` (`accumulator.rs:846`),
  the K-fold path projects identically (`binding_roots`, `ivc_turn_chain.rs:750-753`), and the
  Lean-emitted `dregg-turn-chain-binding-v2` descriptor is 7 SCALAR columns
  `[old_root, new_root, acc_in, acc_out, idx, is_real, real_count]` with 4 SCALAR PIs
  (`circuit/src/turn_chain_witness.rs:25-41`, mirroring
  `Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean`). So "compare all 8 felts" is **not** a
  two-line fix here; it is a `MapOp`-class **VK-affecting Lean AIR change**, same epoch as #5/#11/#20.
  Deliberately NOT made.

  **Soundness: NONE, because the octet is bound by tooth 4 on the SAME code path.** Quoted, since
  "something else is stronger" only excuses a narrow check if that something actually runs
  (`ivc_turn_chain.rs:5561-5573`):

  > ```rust
  > let mut expected = Vec::with_capacity(SEG_WIDTH);
  > expected.extend_from_slice(&genesis_root);
  > expected.extend_from_slice(&final_root);
  > expected.push(BabyBear::new(num_turns as u32));
  > expected.extend_from_slice(&chain_digest);
  > … if exposed != expected { return Err(ClaimedPublicsUnattested { … }) }
  > ```

  Tooth 4 is unconditional, in the same function body, AFTER tooth 2, and compares all 8 genesis
  lanes + all 8 final lanes + count + all 8 digest lanes (+ the board window) against the root's
  `expose_claim` exposure — which is derived in-circuit from the real descriptor leaves. **Every**
  verify entry funnels through that one body: `verify_turn_chain_recursive`,
  `…_from_parts`, `…_from_parts_with_board_window`, `verify_whole_chain_proof_bytes`,
  `verify_turn_chain_recursive_from_blobs`, and `lightclient::verify_history` /
  `verify_history_bytes`. So the verdict fields (`AttestedHistory`) are all tooth-4-pinned; tooth 2
  contributes no field to any verdict, and the carried binding proof is explicitly "NO LONGER a
  soundness dependency" since the ordered-segment close. A ~31-bit collision therefore buys only the
  right to staple a DIFFERENT scalar seam sequence's descriptor proof onto an honest root — the
  attested history stays the root's. **The #20 amplifier is present and still buys nothing:** the key
  domain IS attacker-writable and grindable offline (own a cell, drive turns ⇒ ~2^31 cheap state-root
  computations, per the #1 note below), but the grind is aimed at a comparison that decides nothing.

  **Availability: NONE, and structurally so.** Both sides of both checks are the *same projection* of
  the *same* octet, so an honest producer satisfies them by construction; a collision can only make a
  check that should fail PASS, never make a passing check fail. (Contrast #20, where the narrow key
  sat in a grow-only non-membership set and collisions therefore OVER-revoked ⇒ availability HIGH.
  Same both-sides analysis, opposite conclusion, because there is no set here — just an equality.)

  **The domination was already argued AND executably witnessed** at
  `preflight/src/checks/proofs.rs` (`check_ivc_wrong_initial_root`): it flips `genesis_root[7]` —
  a lane the scalar binding publics cannot see — and demands a refusal, so only the 8-felt segment
  claim can be the one biting.

  **What this lane found and CLOSED: the witness covered the wrong endpoint.** The wide-lane tooth
  existed for `genesis_root` only. Across the WHOLE tree, no test or check ever flipped a non-zero
  lane of `final_root` and asserted the RECURSIVE VERIFIER refuses — every one of the ~12 final-root
  tampers that reach the verifier
  (`lightclient/src/lib.rs:2215`, `dreggnet-prove-service/tests/match_fold.rs:225`,
  `ugc-dregg/tests/proof_leaderboard.rs:138`, `pg-dregg/tests/tier_c_real_proof.rs:207`,
  `dregg-multiway-tug`, `game-turn-slice`, `dregg-circuit-prove`'s own rotated teeth, …) flips lane 0,
  which the NARROW tooth alone would catch, so not one of them could distinguish the two teeth. (The
  single tree-wide exception, `circuit-prove/tests/gnark_witness_export_teeth.rs:193`, writes
  `final_root[7]` but is a canonical-RANGE tooth on the exporter and never runs the verifier — so it
  does not witness binding either.) The
  final anchor is the more load-bearing endpoint — it is what the BFT quorum signs
  (`finality_signing_message` v2) and what `verify_finalized_history`'s seam compares. Two legs added
  to the same preflight check (scalar + wide lane 7 on `final_root`), reusing the one honest fold.

  **FALSIFIED, not asserted — and the falsification is what makes the domination a fact rather than
  a reading.** Against ONE real 2-turn `prove_turn_chain_recursive` fold (persvati, debug, 136s), each
  endpoint was tampered at lane 0 and at lane 7 and the REFUSING TOOTH was read off the error reason
  (teeth 2 and 4 return the same `ClaimedPublicsUnattested` variant, so only the reason text
  distinguishes them):

  > ```
  > HONEST envelope verifies: true
  > LEG genesis[0]: refused by TOOTH-2 (narrow, lane-0 binding publics)
  > LEG genesis[7]: refused by TOOTH-4 (full-octet segment claim)
  > LEG final[0]:   refused by TOOTH-2 (narrow, lane-0 binding publics)
  > LEG final[7]:   refused by TOOTH-4 (full-octet segment claim)
  > ```

  The lane-7 rows are exactly the "lanes 1..7 disagree, lane 0 honest" perturbation: the ~31-bit
  tooth-2 comparison PASSES them (it cannot see past lane 0) and tooth 4 is what REDs. So (i) the
  octet genuinely is bound at BOTH endpoints, (ii) the two new legs are NOT redundant with the ~12
  existing lane-0 tampers — those are all caught one tooth earlier, which is precisely why none of
  them could ever have witnessed tooth 4 on the final anchor, and (iii) if tooth 4 stops covering the
  final octet, `final[7]` flips to `ACCEPTED` while every lane-0 leg stays green — a failure mode the
  tree previously had no tooth positioned to see.

  **STANDING FALSIFIER (the liveness condition this entry exists to record).** #21 is NONE/NONE
  *because* tooth 4 covers the octet on the same path. If any future path ever verifies the binding
  descriptor WITHOUT the segment tooth — a "cheap" pre-check exported on its own, a bridge/settlement
  consumer reading `binding_pis` directly, tooth 4 made conditional — then the ~31-bit endpoint
  comparison becomes the deciding one and **#21 converts to a live soundness wound at ~2^31 offline
  grinding**. The preflight wide legs are what go red. **Kind D**, disposition **DOMINATED**.

- **#22 Grain R3 anti-ghost head binding — NEWLY LOGGED, GENUINE, and NOT dominated. Soundness HIGH
  (rung-level) / availability NONE.** Surfaced while tracing #21's consumers.
  `grain-verify/src/r3.rs:148` marshals `let aggregate_head = proof.final_root[0].as_u32();` and
  `r3_verify(finalized, anchored_head: u32)` sends `"{verified} {aggregate_head} {anchored_head}"` to
  the Lean-proven decision `r3VerifyCore (aggregateVerified) (aggregateHead anchoredHead : ℤ) :=
  aggregateVerified && aggregateHead == anchoredHead` (`Dregg2/Grain/R3Verify.lean:69`). The
  anti-ghost tooth — "a valid whole-history proof cannot be re-pointed at a foreign anchor" — is a
  **~31-bit equality**.

  **Why it is NOT dominated, unlike #21.** The other conjunct is self-anchored:
  `let vk = proof.root_vk_fingerprint(); let verified = verify_whole_chain_proof_bytes(&bytes, &vk)`
  (`r3.rs:143-145`) — the producer mints the anchor from its OWN fold, so `verified` says "this
  supplied chain folds and self-verifies", NOT "this is the renter's chain". The head equality is
  therefore the SOLE binding of the aggregate to the grain, and it is 31 bits wide. The width is
  load-bearing precisely BECAUSE the VK is self-anchored; the module doc names the self-anchoring as
  "orthogonal", which is true of the light-client path but is exactly what makes this projection
  carry the whole weight.
  - **Soundness.** A malicious executor host *is* the party that supplies `finalized`. It grinds its
    own turn sequence offline (~2^31 cheap state-commit computations, no proving until the hit) for a
    final wide anchor `W'` with `W'[0] == anchored_head`, then folds ONCE. R3 accepts a fabricated
    history as the renter's — defeating the exact property R3 exists to establish. The wide value
    exists on BOTH sides (the aggregate carries the 8-felt `final_root`; R1's countersigned
    `RenterCheckpoint.head_root` is `[u8; 32]`, `grain-verify/src/lib.rs:226`) and is squeezed at the
    seam.
  - **Availability: NONE** (a collision only makes acceptance easier, never rejection).
  - **Reachability, honestly.** `r3_verify` has no production caller at HEAD — only
    `grain-verify/tests/r3_whole_history.rs` and `grain-turn/tests/r3_grain_adapter.rs`, both
    `#[ignore]`d heavy folds. So this is a **rung-level design wound, not a live exploit**; it must be
    closed before R3 carries any renting decision.
  - **The fix needs LEAN, and is NOT VK-affecting.** `r3VerifyCore`'s head parameters are `ℤ`; the
    close is to widen them (or take a wide digest) and re-point `r3_unfoolable`'s
    `final_is_genuine_fold` rewrite at the full anchor, plus widen the `@[export] r3VerifyFFI` wire
    and the `anchored_head: u32` API. No AIR, no descriptor, no VK — the turn-chain AIR is untouched
    (contrast #21, whose close IS VK-affecting). Deliberately NOT made by this lane. **Kind E.**
  - **CLOSED 2026-07-24 — BOTH conjuncts repaired, Lean + Rust, no AIR/VK/descriptor byte touched.**
    Both weaknesses CONFIRMED at HEAD by direct read before any change, and one premise of the entry
    above was found to *understate* the second one.
    - **⚠ CORRECTION to this entry's own premise.** The entry above named "R1's countersigned
      `RenterCheckpoint.head_root` is `[u8; 32]`" as the wide value on the anchor side. **That is the
      wrong object.** `head_root` is the RECEIPT-CHAIN tip — `AgentRunReport::tip()`, a 32-byte
      `receipt_hash()` over the ed25519-signed receipt chain (`lib.rs:375`, `:655`) — whereas the
      aggregate's `final_root` is the 8-felt Poseidon2 **state-commit** fold. They are different
      commitments over different data and could never compare equal; widening to `head_root` would
      have produced a binding that always fails. The genuine wide counterpart, and what both existing
      tests already supplied, is the leg's `wide_new_root8() -> [BabyBear; 8]` — the SAME object
      `final_root` is (`turn_anchors8` → `leaf_seg.last_new8` → `combine_seg` propagates
      `r.last_new8` → `final_root = root_seg.last_new8`). The repair widens to THAT.
    - **A SEPARATE residual this surfaced (not felt-width, named not fixed).** Because of the above,
      R3's `anchored_head` is a STATE-commit anchor while the R1 countersignature commits to a
      RECEIPT-chain tip. So "the R1-anchored head" in `r3_verify`'s doc is not literally the value the
      renter countersigned; there is no check in-tree binding the state-commit anchor R3 pins to the
      receipt-chain tip R1 acknowledged. The renter-authority leg of the anti-ghost story therefore
      rests on an UNBRIDGED correspondence between two commitments. Orthogonal to width — widening
      does not touch it — and it is the next thing to close before R3 carries a renting decision.
    - **Width.** `r3VerifyCore` now decides over the full `Digest8` (`Fin 8 → Felt`, = Rust
      `[BabyBear; SEG_ANCHOR_WIDTH]`, ~124-bit) and `r3_verify` takes `anchored_head: &[u32; 8]`. No
      encoding was invented: the aggregate already carried `WholeChainProof.final_root: [BabyBear; 8]`
      and the anchor is sourced from the leg's existing `wide_new_root8() -> [BabyBear; 8]`. The wire
      (`@[export] dregg_grain_r3_verify`) went from 3 ints to 33 and its parse is now strict `mapM`
      (a malformed token can no longer be dropped and shift lanes); the **pre-repair 3-int wire now
      fails CLOSED**, so a stale caller cannot re-open the ~31-bit binding by accident.
    - **Self-anchoring — the entry called it "orthogonal per the module doc"; it is a documented API
      contract VIOLATION.** `WholeChainProof::root_vk_fingerprint`'s own docstring says "A VERIFIER
      must NEVER take the anchor from the artifact it is verifying", and
      `verify_whole_chain_proof_bytes`'s says "`expected_vk` is the caller's OWN configured anchor —
      it is NEVER read from the envelope". The pre-fix seam did exactly the forbidden thing. Its
      self-justification ("self-anchors exactly as `dregg_lightclient::fold_and_attest` does") cited
      the SETUP-side anchor *minter* as precedent for a VERIFIER decision — `fold_and_attest`'s own
      doc says "A remote verifier must instead call `verify_history` with its configured anchor".
      **And the effect is sharper than "self-anchored": tooth 1 was a TAUTOLOGY.** The verifier's VK
      pin is `if recursion_vk_fingerprint(root_proof) != *expected_vk { refuse }`
      (`ivc_turn_chain.rs:5491-5497`), and `WholeChainProof::root_vk_fingerprint()` is *defined* as
      `recursion_vk_fingerprint(&self.root.0)` (`:1911`) over the same root the envelope carries. So
      the pre-fix call fed the check its own answer: `found == found`. The pin did not merely bind
      weakly — it could not fail, so `verify_whole_chain_proof_bytes`'s FIRST tooth was inert on this
      path, and only the ~31-bit head equality remained.
    - **Where the expected VK comes from: the CALLER.** `r3_verify(finalized, anchored_head,
      expected_vk)`. A governance constant is NOT usable here — the fingerprint is a function of the
      root circuit SHAPE, which varies with `num_turns` and leaf trace heights, so one pinned scalar
      cannot cover R3's fold shapes (unlike `DREGG_APEX_RECURSION_VK`, which pins the ONE fixed
      apex-shrink shape). New `r3_setup_anchor` mints the anchor from a fold the honest party produced
      ITSELF — the `fold_and_attest` role, where self-anchoring is correct — and the Lean core decides
      `presentedVk == expectedVk` over the recomputed fingerprint, so the anchor's provenance is
      structurally visible on the wire instead of implicit in Rust.
    - **ANTI-LAUNDER, machine-checked.** `Dregg2.Grain.R3Verify.neither_half_alone_suffices`:
      widening the head ALONE still admits a foreign circuit's root
      (`headWidenedOnly_admits_foreign_circuit`, since `selfAnchoredVk_vacuous` proves the
      self-anchored decision is *literally independent* of which circuit the root belongs to), and
      pinning the VK ALONE still admits the ~2^31 grind (`vkPinnedOnly_still_conflates`). This is
      #12's `finalSqueezeOnly_still_conflates` shape, proved for BOTH conjuncts.
    - **Falsifiers + fix-soundness.** `narrowHead_conflates` / `narrow_seam_underdetermines` (the
      lane-0 form accepts a genuinely-distinct wide anchor; a lane-0 pin does not determine which
      history was folded) · `selfAnchoredVk_vacuous` / `selfAnchoredVk_accepts_foreign_root` ·
      `r3_wide_head_mismatch_rejected` / `r3_vk_mismatch_rejected` / `wideHead_refuses_the_forgery` /
      `vkPin_refuses_the_foreign_root` / `r3_unverified_rejected`. `r3_unfoolable` is unchanged in
      strength: it reduces through `r3VerifyCore_implies_narrow` (the widened accept set is a SUBSET
      of the old one) into `light_client_verifies_whole_history`, carrying the SAME `EngineSound`
      hypothesis. **No floor added** — exact 8-lane and 32-byte equality, no hash.
    - **Falsified in Rust too**, at the DEPLOYED Lean decision (extracted native code via
      `shadow_grain_r3_verify`): `grain-verify/tests/r3_width_falsification.rs` REDs on a forged
      aggregate head perturbed at each of lanes 1..7 (lane 0 byte-identical) and on each of the 32
      fingerprint bytes flipped, restores on the honest facts, and pins the anti-launder ON THE WIRE
      (the same foreign fingerprint, self-anchored, still ACCEPTS). It is NOT `#[ignore]`d — it forges
      the FACTS, so it pays for no fold. The heavy end-to-end tests (`r3_whole_history.rs`,
      `grain-turn/tests/r3_grain_adapter.rs`) now use the lane-1-only perturbation and a swapped
      anchor as their negative poles, and `dregg-lean-ffi`'s own
      `verified_grain_r3_verify_runs_in_lean` unit test was carrying `assert_eq!(…("1 42 42"), "1")`
      — the pre-repair narrow wire — and is rewritten to the 33-int one.
    - **⚑ A vacuity caught in this lane's OWN work, worth recording as a lesson.** The falsification
      file first used the repo's `report-and-stop` idiom (absent core ⇒ `eprintln!` + `return`). On a
      remote build host whose `dregg-lean-ffi` splice omitted `dregg_grain_r3_verify`, it reported
      **`4 passed`** while executing NONE of the assertions. Report-and-stop is right for an
      end-to-end demo; in a FALSIFICATION test it converts an absent or stale archive into a green —
      the exact failure shape this repair exists to remove. It now `assert!`s core availability, so
      absent core ⇒ RED = "blocked", never "verified". (The splice gap is a persvati-side build
      artifact, not a defect in this repair: the local spliced archives DO export the symbol.)
    - **RESIDUAL (precise, and it is NOT this wound).** `RecursiveAggregation.Aggregate.finalRoot` and
      `foldedFinalRoot` remain `ℤ`-valued, with that ℤ *denoting* the 8-felt anchor by its own
      docstring. `r3_unfoolable` therefore takes an EXPLICIT denotation `den : Digest8 → Felt` plus its
      coherence `hden : agg.finalRoot = den wideAggHead` — the modeling step the pre-fix seam performed
      silently and unfaithfully (as `den := lane0`) is now a visible hypothesis rather than a hidden
      squeeze. Widening `foldedFinalRoot` itself is a separate model refactor across
      `RecursiveAggregation`/`HistoryAggregation`. **Reachability is unchanged: still no production
      caller** — which is what made this the cheapest possible time to fix it, and the API break
      (`anchored_head: u32` → `&[u32; 8]`, plus the new `expected_vk` parameter) cost nothing.

## Update log — 2026-07-22

- **#18 + #19 zkOracle / render attestation commitments — NEWLY LOGGED, code NOT touched.** Two
  attestation welds were never in this catalogue. Both are in the complement of both defenses (not in
  `check-no-degraded-felt.sh`'s three files; no `Faithful8` sink on the path). Verified by direct read.

  - **#18 — `content_commitment` (the zkOracle CROSS-LEG WELD).**
    `zkoracle-prove/src/attestation.rs:47` is `pub fn content_commitment(response_body: &[u8]) ->
    BabyBear { hash_bytes(response_body) }` — one felt. `ZkOracleAttestation::content_commit`
    (`:89`) is that felt, and its doc-comment says it "bind[s] all three legs to the SAME response";
    it binds them to the same **~31-bit image** of the response. It then rides the narration data
    lane: `dungeon-on-dregg/src/narrator.rs:417-418`
    `fn attestation_commit_field(att) -> FieldElement { field_from_u64(att.content_commit.0 as u64) }`
    (same encoding again at `:1064` on the live-attest path), pushed as the second `data` field of the
    `NARRATION_TOPIC` `Effect::EmitEvent` (`:400-413`), and is read back off the committed receipt by
    the public `bound_attestation_commit` (`:316`) — a real consumer path, not a dead field.
    **The tell is the padding:** `field_from_u64`
    (`cell/src/program/eval.rs:2953`) writes the value big-endian into bytes `[24..32]` of a zeroed
    `[u8;32]`, so the receipt carries a 32-byte field whose leading 28 bytes are structurally zero —
    it **looks** like every other ~256-bit commitment on the wire and is ≤31 bits. Contrast the
    FIRST data field on the same event, `narration_commitment` (`:292-298`), which is a real
    domain-separated BLAKE3 32-byte `symbol` — the prose is bound wide, the attestation weld is not.
    ~~Cost: ~2^15.5 to find two bodies sharing a `content_commitment`, ~2^31 to hit a chosen one.~~
    **RE-PRICED 07-24 — DIRECT-ALIAS, and the attack this site enables is the COLLISION half, so the
    cost is O(1), not ~2^15.5.** `content_commitment(response_body) = hash_bytes(body)` and
    `hash_bytes` is `hash_many(from_bytes_packed(data))` (`circuit/src/poseidon2.rs:566-569`), whose
    per-4-byte packer is the non-canonical `Self::new(val) = val % p` (`field.rs:194-209`). The
    response body is **attacker-chosen bytes**, so two bodies differing by exactly `p` in one 4-byte
    group carry a **byte-identical** `content_commitment` with no search at all. That is precisely
    "WHICH authenticated oracle body backs a committed narration": author both bodies, commit one,
    present the other. The ~2^31 figure survives only for the *targeted* variant (hit a
    `content_commit` someone else fixed), which is not the exposure this entry describes. Severity
    moves **MODERATE → HIGH within its reachability class** (a live consumer path:
    `bound_attestation_commit`). Kind **C** — there is no
    wide `content_commitment`; one must be BUILT (⇒ Lean-authored, Rust calls in).
  - **#19 — `RenderAttestation`'s two welds.** `zkoracle-prove/src/render.rs:198`
    `pub output_commit: BabyBear` is the gate in `verify_render_attestation` (`:295`, recompute over
    the presented output, refuse mismatch); `:201` `pub template_commit: BabyBear` (from
    `template_commitment`, `:166`, `hash_bytes` over the segment encoding) is the gate in
    `verify_render_reproducible` (`:312`, "generated by THIS template"). Both single felts.
    `template_commit` is the load-bearing one — a collision is a **template substitution** that
    passes the reproducibility check. `output_commit` has a genuine compensating tooth: the colliding
    output must ALSO replay the same `CompactCert` (`verify_cfg_compact`, `:299`), which constrains
    the search to structurally-identical renders — real, but not a width argument. Kind **C**.
    **RE-PRICED 07-24 — DIRECT-ALIAS on both welds; the collision half is O(1), not ~2^15.5.** Both
    are `hash_bytes` over prover-authored bytes (`template_commitment` at `:166` over the segment
    encoding, `output_commit` over the presented output), i.e. encoder (3)/(4) of the re-pricing
    section. A template substitution is: author two segment encodings differing by `+p` in one
    4-byte group, commit one, present the other — no search. `template_commit`'s severity moves
    **HIGH within its reachability class**; `output_commit`'s stays gated by the `CompactCert`
    tooth, which is a *structural* constraint on the colliding output and is unaffected by the
    re-pricing (it neither helps nor hurts the alias construction — the two outputs must still both
    replay the cert). The targeted-hit variant of either weld remains ~2^31.

  **⚠ ANTI-PATTERN — do NOT repair these by re-hashing the narrow felts.** The obvious "widen it"
  move (`hash_many_8([content_commit, template_commit, …])`, or any wide fold seeded from the
  EXISTING `BabyBear`s) launders ~31 bits into a ~124-bit-looking digest: the wide output is a
  function of a 31-bit input, so its collision set is exactly the narrow one. This is the already-
  catalogued `finalSqueezeOnly_still_conflates` shape (#12, `metatheory/Dregg2/Cell/InterfaceIdWidth.lean`) — proved
  there that widening only the final squeeze STILL conflates. The **correct** derivation re-hashes
  the REAL PREIMAGES, 8-felt end-to-end with no 31-bit waist anywhere in the chain: the response /
  output BYTES, the template's own structural encoding (`PromptTemplate::template_hash`,
  `attested-dm/src/prompt_template.rs:257-280` — an existing domain-separated BLAKE3 over
  `(data_from, segment count, per-segment tag ‖ len ‖ bytes)`, which is the right shape and is
  already 32 real bytes), and the bindings. Related prior art with the same waist: the recursion leaf
  `circuit-prove/src/zkoracle_leaf_adapter.rs` already keeps every INTERNAL carrier 8-felt but
  exposes a 1-felt claim lane, and its header names the un-done weld to `content_commitment` — that
  weld should be built at 8 felts, not by squeezing the leaf to match the narrow attestation.

  Code NOT changed in this lane; logged only.
- **#12 interface_id — PROOF-HALF LANDED, site byte-safe PROVEN.** Re-audit found it ALREADY
  Rust-widened at HEAD (full 8-felt `hash_many_8` fold, arity-seeded, 8-lane sorted,
  `digest8_to_bytes32` tail); the wound's "NO wide twin" was stale. Authored
  `metatheory/Dregg2/Cell/InterfaceIdWidth.lean` (rooted in `Dregg2.lean`, `#assert_axioms`-clean,
  `lake build` exit 0) — falsifier (1-felt lane-0 leaf conflates distinct method sets → shared factory
  VK), fold soundness (`wideId_injective` under the wide-hash CR floor), the anti-launder
  (`finalSqueezeOnly_still_conflates`), and the arity tooth. Mirrors the #1/`FinalityCertWidth`
  pattern. Nothing deployed touched.
- **#3 cap-uniqueness — PROOF-HALF LANDED, deploy stays gated.** Re-audit confirms the executor's
  leg-(1) root gate STILL compares the NARROW lane-0 `felt_to_bytes32(compute_canonical_capability_root_felt)`
  at HEAD (`commitment.rs:665`), while the off-chain state commitment already absorbs the WIDE
  `digest8_to_bytes32(compute_canonical_capability_root_8)` (`commitment.rs:684`). Authored
  `metatheory/Dregg2/Cell/CapUniquenessWidth.lean` (rooted, `#assert_axioms`-clean, `lake build` exit
  0) — falsifier (`narrow_capRoot_underdetermines`: distinct wide roots collide on lane 0), wide-encoding
  soundness (`wide_capRoot_determines`), the wound's own **"redundant projection" DOWNGRADE proved**
  (`narrow_root_is_projection_of_wide`/`narrow_gate_redundant`: the narrow value is lane 0 of the wide
  root the state commitment binds), and the compensating tooth (`accept_implies_unique`: uniqueness is
  the felt-independent leg-(2) dup-scan). **RESIDUAL:** widening leg (1)'s in-circuit gate ITSELF is a
  committed-state binding change (ember-gated deploy), out of scope; the security-carrying WIDE binding
  is already deployed, so the site is defense-in-depth-narrow, PROVEN redundant.

## Update log — 2026-07-20

- **#11 freshness/revocation rail — FOLD-IN LANDED (ember chose ①c(b)).** Redundancy premise
  CONFIRMED by read: the limb-26 `nullifierFreshOp` `.absent` map-op is the freshness authority over
  EXACTLY the set the deleted `DslRevocationTree::revoked_leaves` seeded (`full_turn_proof.rs`
  threads `FullTurnWitness::spent_nullifiers` → the limb-26 BEFORE tree; the `.absent` key IS the
  published nullifier `param0`; the BEFORE root8 is absorbed into the pinned OLD commit; forge
  test `circuit/tests/vk_epoch_notes_light_client_binding.rs`). DELETED: the whole 1-felt rail
  (`circuit/src/dsl/revocation.rs`, `non_revocation{,_adjacency}_witness.rs`,
  `NonRevocation{,Adjacency}Emit.lean` + the Refine/Rung2 satellite proofs + `descriptor_by_name`
  registration + the SDK `NonRevocationProof`/`NonRevocationWitness` component + verifier bindings
  (a)/(b) + `expected_revocation_root` threading). ADDED: `spendAncestorFreshOp` — the limb-37
  delegation-ancestor `.absent` open on spend turns (`EffectVmEmitRotationV3.noteSpendV3`, Lean
  single-file-checked; theorem `noteSpendV3_opens_delegation_ancestor`, #assert_axioms-clean).
  RESIDUALS (named): the ancestor key column (`param3`) is not yet in-circuit-bound to the cap
  lineage; registry re-emit + Rust spend-generator threading (param3 fill + revoked map-heap) are
  the integrator's; keys stay 31-bit (#5's lane). Freshness capacity 14 → 65534.

## Update log — 2026-07-19 (post-pricing, verified reads)

- **#6 CI exit_code — FIXED + VERIFIED GREEN.** `ci_verdict_public_inputs` now returns `Option`
  and REFUSES non-canonical exit codes (`exit_code_is_canonical` = `0 ≤ e < BABYBEAR_P`); prove →
  `Err`, verify → `false`. Canary `failing_exit_code_cannot_alias_into_the_pass_gate` +
  8/8 `ci_assurance::tests` pass (`--features substrate`). The trusted reconstructor is fail-closed
  by construction, so a future caller cannot reintroduce the alias.
- **#1 finality cert — CONFIRMED real, cost (a) ~2^31 offline hashes + 1 proof.** The `:686` segment
  tooth binds the aggregate to its own execution, NOT the committee's *signature* to the wide root.
  `final_root` is a host-searchable `wire_commit_8` (`joint_turn_aggregation.rs:1156`). **Fix is
  clean and NOT AIR:** the wide root already exists in the PIs; widen `finality_signing_message` +
  `FinalityCert.finalized_root` + the seam to all 8 lanes. Kind E → rotation epoch.
- **#3 cap-uniqueness — DOWNGRADE to defense-in-depth.** State commitment already binds the wide cap
  root independently (`commitment.rs:243`); the narrow gate is a redundant projection. Fix is
  actually-hard (declared-root writers widen in lockstep; slot is committed state → circuit binding),
  NOT the quick swap I first ranked.
- **#4 note/nullifier — MINT BLOCKED, availability real via shielded path.** Deployed node injects no
  `proof_verifier` ⇒ cleartext `NoteSpend` fail-closes (`apply.rs:1195`); every real verifier's base
  `verify()` is hardcoded `false`. Availability break is reachable via the *shielded-transfer* path
  (`apply.rs:1370`, self-contained `verify_stark_side`, ~31-bit keys) — ties #4↔#10. Residual: the
  Lean-authoritative producer's note-effect semantics (`exec-lean` `wire_state_to_ledger`) not fully
  traced; all evidence says no value created.
- **#8 topic mask — RECLASSIFY to low-severity design limitation.** Inherent 64-bucket `u64` lattice;
  collisions cause spurious wakes (no payload/cap leak; recipient still filters on the true hash).
  Real per-topic attenuation = a change to the Lean-authored firmament `NotifyCap` model.
- **#14 leg_is_wide — FIXED + VERIFIED GREEN.** Deleted the `#[cfg(not(feature = "prover"))] → false`
  stub; extracted the classifier to an unconditional module-level `vk_hash_is_wide(&[u8;32])` (deps —
  ungated `WIDE_REGISTRY_STAGED_TSV` const + non-optional `blake3` — confirmed available without
  `prover`). Non-prover **lib compiles**; canary `wide_leg_classifier_works_without_prover` **passes**.
  Now one unconditional code path, so the light-client verify build classifies wide legs correctly and
  binds their ~124-bit anchors instead of a slot-0 residual.

## Follow-ups opened 2026-07-19

- **Restore non-prover (light-client) test coverage → `project-ci-meaningfulness-audit`.** `cargo test
  -p dregg-sdk --no-default-features` did not compile on HEAD: ungated tests reference `prover`/
  `exec-lean`-only symbols (`descriptor_authority_class` — fixed one instance; `dregg_exec_lean` import
  — still open; likely more). So the wasm/light-client verify config's tests have not been running —
  **which is exactly where #14's bug survived.** Restore it: gate the remaining ungated tests, then
  wire `--no-default-features` into CI so the trust-minimized config is actually exercised.
- **Kind-E rotation epoch designed** → `docs/DESIGN-felt-width-rotation-epoch-2026-07-19.md` (E1 pure-
  Rust #1; E2 descriptor-PI-widening #2/#9/#11, Lean AIR).

---

## Triage — worst first

| # | Site | file:line | Cost | Kind | Prov |
|---|------|-----------|------|------|------|
| 23 | ~~**Ledger `cells_root` is ONE felt in the FAITHFUL 8-felt consensus anchor**~~ **CLOSED 2026-07-24 (producer-only; a receipt/consensus epoch, NO VK regen)** | `turn/src/rotation_witness.rs:297`; `cell/src/commitment.rs:791,1128`; `turn/src/state_commit.rs:132,181` | — | C | **[V] FIXED** `cells_root : Faithful8` (the TYPE, not just the value); both producers fill limbs 0 ‖ 169..=175 from `compute_canonical_heap_root_8_entries` (`node8` at every intermediate — NOT a re-hash of the narrow root); `absent_cell_commitment` fills the group too. Falsified BOTH polarities in `turn/tests/cells_root_width_falsification.rs`. **Residual: the tree's KEYS are still 1 felt** (kind D) and the AIR still constrains this group only on createCell/factory/spawn |
| 24 | **Cap LEAF `target`/`breadstuff` — a 1-felt `fold_bytes32(cell_id)` INSIDE the faithful 8-felt leaf digest**, so the proven leaf injectivity is over a tuple that already lost 93 bits | `circuit/src/cap_root.rs:209,254`; `cell/src/commitment.rs:547`; `Dregg2/Circuit/DeployedCapOpen.lean:225` | ~2^31 **offline** ⇒ a cap for cell A authorizes an exercise on B | D | **[V]** soundness HIGH-**when-anchored** / NONE today / availability NONE. Runtime authorizes over full `CellId`s (`authorize.rs:1329`); step-9 leaf binding is 8-felt but against a CALLER-declared leaf; `targetBindGate`'s `src` PI (46) is **unanchored** and `target_is` has zero production callers. **STANDING FALSIFIER: realizing `TurnIdentityAnchored`** (the node producer already publishes the folds) |
| 1 | ~~BFT finality cert — signed message is 4 bytes of lane-0~~ **REMEDIATED at HEAD (row was STALE)** | `lightclient/src/lib.rs:311-321,732,740` | — | E | **[V] FIXED** v2 domain tag, ALL 8 lanes absorbed, `finalized_root: [BabyBear; 8]`, seam compares FULL arrays; the `.as_u32()` at `:720-743` is error-display only; lane-0 signing survives ONLY inside the test that demonstrates the closed hole |
| 2 | Federation membership gate — bare 1-felt PI compare, public SDK export | `sdk/src/verify.rs:137,202,214` | ~2^31 **offline** (attacker owns the whole ring preimage) + 1 proof | E | **[V]** CONFIRMED narrow by read ([A][?]→[V]); action-binding 15 lines below correctly loops all 8. Soundness HIGH / availability NONE — **on a library surface: `verify_authorization_proof` has NO in-tree deployed caller** (`verify_production`/`verify_any_tier` are themselves uncalled). Close before a consumer wires it |
| 26 | **Cell-program `HashKind::Poseidon2` hash-lock arm** — `PreimageGate` (knowledge/escrow gate) and `KeyRotationGate` (**KERI pre-rotation**) bind a ~31-bit zero-padded digest; the Blake3 arm in the same function binds 256 | `cell/src/program/eval.rs:2822,1007,1100`; doc at `types.rs:282` | ~2^31 targeted / ~2^15.5 birthday, fully OFFLINE | B | **[V] LATENT** soundness HIGH-if-selected / availability NONE. NO AIR projection (`executor/mod.rs:470-475`); every deployed program uses Blake3 (polis, guardian_rotation, storage) and `Default = Blake3` — but the SDK/py surface lets any author pick it, and the doc-comment **recommends** Poseidon2 "for in-circuit verification" for two constraints that have no circuit |
| 27 | **seL4 executor-PD crypto floor** — Merkle 2-to-1, BLAKE3→field, nullifier tag, and macaroon keyed-MAC all `.as_u32()`; the MAC KEY is derived from one u64 field element (24 zero bytes) | `sel4/dregg-pd/executor-pd/crypto-floor/src/lib.rs:134,159,195,224`; portals `Dregg2/Crypto/PortalFloor.lean:140,173,200,257` | ~2^31 ⇒ double-spend (nullifier) · caveat-chain forgery (MAC) · membership equivocation (node) | C/E | **[V]** HIGH-**if-reached**; UNREACHED per the crate's own header (portals route through in-Lean reference dictionaries). Width is imposed by the **Lean portal types** (`Nat`) ⇒ the fix starts in Lean. Frontier (`firmament-sel4-boots`), priced rung-level for reachability, not for size |
| 25 | **`Effect::Burn.target_hash`** — 1 felt in the AIR PI (`burn_target`, len 1) AND a single `push` into `effects_hash`, twenty lines above `CellDestroy`'s 8-lane `extend_from_slice` | `circuit/src/effect_vm/effect.rs:348`; `air.rs:287-293`; `helpers.rs:447`; producer `turn/src/executor/effect_vm_bridge.rs:496` | ~2^31 **offline** ⇒ which cell's supply a burn proof destroyed is 31-bit ambiguous | C | **[V]** soundness MODERATE-**if-wired** / NONE today / availability NONE. `expected_burn_target_bb` (`proof_verify.rs:2742`) is the trusted-side comparer and is **`#[allow(dead_code)]` with zero callers**; full nodes gate burn wide (`apply.rs:3477`). **STANDING FALSIFIER: wiring that checker** |
| 3 | Executor cap-uniqueness gate — narrow root, wide twin exists 19 lines away | `turn/src/executor/execute_tree.rs:328` | ~2^15.5 | B | **[V]** breaks root-binding (1), NOT the structural dup-scan (2, `:345`) — **PROOF-HALF LANDED 07-22** (`CapUniquenessWidth.lean`; redundant-projection DOWNGRADE proved; leg-(1) gate widening = gated deploy) |
| 4 | Note commitment + nullifier — 1 felt each, no `_8` variant | `cell/src/note.rs:329,243` | ~46k spends | C | [A] availability **certain**; mint contingent on deployed verifier [?] |
| 5 | Accumulator leaf **keys** (nf/cm/revoked) — 31-bit addresses | `circuit/src/effect_vm/trace_rotated.rs:1377,1575,1661` | ~2^31 | D | [A] roots are `Faithful8`, membership answered by key |
| 6 | CI pass gate — `exit_code % BABYBEAR_P` aliases failure→0 | `dregg-doc/src/ci_assurance.rs:255` | **zero** | A | **[V]** `2013265921 % p = 0`, gate is `COL_EXIT==0`, bond path unguarded |
| 7 | Fiat mint gate — payment identity folded to 1 felt | `circuit/src/dsl/deco_payment.rs:107` | ~2^16 | C | [A] bridge gate live (`bridge/src/stripe_deco.rs:287`); fold arm fail-closed |
| 8 | Topic wake mask — `1u64 << (topic_hash[0] % 64)` | `starbridge-v2/src/swarm.rs:111` | **~64 evals** | ? | [A][?] load-bearing vs optimization unconfirmed |
| 9 | `SenderAuthorized` authorized-set root — 1 felt, leaf proves no path | `turn/src/executor/membership_verifier.rs:105` | ~2^31 | D/E | [A] |
| 10 | Shielded pool — `merkle_root`/`nullifier`/`value_binding` declared **`u32`** | `turn/src/action.rs:1005`; `circuit-prove/src/shielded/spend_circuit.rs:462` | direct inflation on value collision | C | [A] `Effect::ShieldedTransfer` live |
| 11 | Freshness/revocation root — 1 felt, tree depth 4 ≤14 entries | `sdk/src/full_turn_proof.rs:5248` | grind padding leaves | D/E | [A] |
| 12 | `interface_id` — ~~1 felt, no wide twin~~ **Rust-widened to 8-felt at HEAD**; a factory VK is derived from it | `cell/src/interface.rs:275`; `directory/src/service_factory.rs:92` | ~2^31 → colliding interfaces share a VK | C | [V] **BYTE-SAFE PROVEN 07-22** (`InterfaceIdWidth.lean`; wound "no wide twin" was STALE) |
| 13 | sandstorm-bridge — narrow throughout; byte-identity claim now **false** | `sandstorm-bridge/.../cell.rs:87,138` | ~2^31 (hostile host) | C/drift | [A] `cell/src/state.rs:535` widened, sandstorm did not — correctness drift too |
| 14 | `leg_is_wide` cfg trap — non-prover build forces **every** leg narrow | `sdk/src/full_turn_proof.rs:5144` | verifies ~124-bit anchors at 31 bits | A | [A] wasm verifier is exactly this config; live trap, no current caller |
| 18 | zkOracle `content_commitment` — the **cross-leg weld** is ONE `BabyBear`, then zero-padded to 32 bytes and bound into a receipt | `zkoracle-prove/src/attestation.rs:47,89`; `dungeon-on-dregg/src/narrator.rs:417-418,1064` | **O(1)** (DIRECT-ALIAS collision; ~~2^15.5~~) / ~2^31 targeted | C | **[V]** `BabyBear(pub u32)`; `field_from_u64` puts it in the LAST 8 bytes of a `[u8;32]` ⇒ **looks** ~256-bit on the wire, carries ≤31 bits. **RE-PRICED 07-24:** `hash_bytes`'s `from_bytes_packed` reduces each 4-byte group mod `p`, and the response body is attacker-chosen ⇒ a colliding body pair is CONSTRUCTED (`+p` in one group), not searched |
| 19 | `RenderAttestation` — `output_commit` (the verify-gate weld) and `template_commit` (the "generated by THIS template" gate) are both single felts | `zkoracle-prove/src/render.rs:166,198,201` | **O(1)** (DIRECT-ALIAS collision; ~~2^15.5~~) / ~2^31 targeted | C | **[V]** `verify_render_attestation:295` gates on `output_commit`; `verify_render_reproducible:314` gates on `template_commit`. **RE-PRICED 07-24:** both fold prover-authored bytes through `hash_bytes`; `template_commit`'s substitution needs no search. `output_commit` stays gated by the `CompactCert` replay tooth (structural, width-independent) |
| 32 | **`umem_fold_bytes_v1` — an AFFINE byte fold documented as "injective"**; the fallback universal-map ADDRESS for every non-hot `UKey` and the VALUE felt for every non-`Bytes32` `UVal`, over `serde_json` bytes | `turn/src/umem.rs:1149-1156,1197,1211` | **O(1)–2^16** (DIRECT-LINEAR; MITM over 4 free bytes, O(1) with a field-spanning numeric) | C/D | **[V] NEW 07-24** `acc = acc*mul + (b+1)` is a linear form into a ~2^31 image; the `:1194` doc-comment's "deterministic **injective** felt" is false. Outside `check-no-degraded-felt.sh` scope. Address grammar is Lean-authored (Rank-1 `uaddrEnc`) |
| 33 | **umem `Bytes32`/`UmemRef` value felt and `NoteNullifier`/`BridgedNullifier` key** — writer-chosen 32 bytes through `cap_root::fold_bytes32` | `turn/src/umem.rs:1193,1208` | **O(1)** (DIRECT-ALIAS collision) / ~2^31 targeted | D | **[V] NEW 07-24** encoder (3): `hash_many(encode_hash(b))` with non-canonical per-chunk `% p`. Two distinct committed umem values collide with no search |
| 20 | Spend delegation-ancestor key — the public, fixed, system-wide "undelegated" sentinel is ONE felt in the grow-only revoked set's key domain | `circuit/src/effect_vm/trace_rotated.rs:1402,1415` | ~2^31 **offline** grind ⇒ permanent DoS on every undelegated `NoteSpend` | D | **[V]** availability HIGH / soundness NONE — same-fold-keyed `.absent` can only over-revoke; `MapOp.key : EmittedExpr` is one felt in the deployed IR ⇒ widening is VK-affecting. **The tree's one EARNED `check-no-degraded-felt` suppression** |
| 22 | ~~Grain R3 anti-ghost head binding — ONE felt, beside a SELF-anchored VK~~ **CLOSED (row was STALE; see the 07-24 entry)** | `grain-verify/src/r3.rs:277,366`; `Dregg2/Grain/R3Verify.lean` | — | E | **[V] FIXED** both conjuncts: full `Digest8` head (all 8 lanes) + a caller-supplied `expected_vk` parameter (the proof's own fingerprint is reported, never the anchor); `neither_half_alone_suffices` machine-checked; new `r3_width_falsification.rs` drives the deployed Lean decision. No AIR/VK/descriptor byte touched |

**Tier 2 (~62-bit, 4 felts):** `circuit-prove/src/dsl_leaf_adapter.rs:152` (`DFA_RC_LEN=4`, leaf exposes 8
on the wire — cheapest real fix), `sovereign_leaf_adapter.rs:85` (`KEY_COMMIT_LEN=4`, authorizes a
sovereign turn, six lines from `COMMIT_LEN=8`), `verifier/src/lib.rs:466` (receipt chain).

**Checked-benign (coverage, not omission):** `storage/src/bucket_commitment.rs:112`,
`starbridge-apps/site-host/src/site.rs:174` (1-felt root is one input to a `wire_commit_8` fold that
binds all limbs — no 31-bit intermediate); `circuit/src/effect_vm/trace.rs:673` anchor tags (all 8
bound via `compute_effects_hash`); ~~`commit/src/typed.rs:565` (30 bits/limb ⇒ 240-bit)~~
**— CORRECTED 07-24, this row was wrong.** `canonical_32_to_felts_8` DISCARDS bits 6-7 of bytes
3,7,…,31 (`(hi & 0x3F) << 24`), so 16 of 256 input bits are dropped and a colliding 32-byte pair is
**two bit flips, O(1)**. "240-bit" describes the IMAGE SIZE, not a collision cost. It is benign only
where the 32 bytes are a hash image or a curve point the attacker cannot nudge (`compress_member`'s
ed25519 sender pk under `PredicateInput::Sender`) — it is NOT benign as a general encoder, and
`turn/src/executor/membership_verifier.rs:206` also accepts `PredicateInput::Bytes` (arbitrary
32 bytes). Re-read #9's leaf domain before quoting its `~2^31`; the ROOT half of that row is not a
fold at all (`root_felt_from_slot`, `:105-108`, reads a raw LE u32 out of the slot); **#21** the
whole-chain binding-descriptor endpoints (`circuit-prove/src/ivc_turn_chain.rs:5485` tooth 2 +
`circuit-prove/src/accumulator.rs:970`) — DOMINATED by the segment tooth's full-octet compare on the
same code path, argued and now witnessed at BOTH endpoints in
`preflight/src/checks/proofs.rs::check_ivc_wrong_initial_root`; see the 07-24 entry for the standing
liveness condition that would convert it. **#28** `iroot` (`turn/src/rotation_witness.rs:320`) — a
natively 1-felt receipt-index MMR root absorbed into the proof-side commitment (and zeroed in the
executor's `consensus_ctx`), DOMINATED-BY-ABSENCE because no deployed path ever OPENS a receipt against
it; **#29** `verify_full_turn_bound`'s narrow-leg state anchors (`sdk/src/full_turn_proof.rs:5140-5150`
+ `node/src/turn_proving.rs:136,941,1205`) — #21 geometry, both sides the same projection of the node's
OWN pre-state, with the executor mirror binding the octet unconditionally. Both carry standing
falsifiers in the SWEEP section. Display strings / hash-map keys / `#[cfg(test)]` fixtures
not itemized.

---

## The six repair kinds (kind decides the mechanism and who can touch it)

- **A — Logic bugs, not width. Fix now, no crypto.** #6 (range-check `exit_code`), #14 (cfg gate).
- **B — Gate swap to existing wide twin, AND retire the narrow twin** so it can't be reached again.
  #3, **#26** (the wide arm is `HashKind::Blake3`, in the same function — retire or widen the Poseidon2
  arm; no AIR involved).
- **C — No wide scheme exists; must BUILD it — and these are circuit commitments ⇒ authored in
  Lean, Rust calls in.** ⚠️ TRIPWIRE (`~/.claude/CLAUDE.md` law #1). #4, #7, #10, #12, #13, #18, #19,
  ~~**#23**~~ (**CLOSED 07-24** — and it turned out to be the cheapest C for a reason the entry
  under-called: the wide scheme did NOT have to be BUILT, so it was never really a C. `compute_canonical_heap_root_8_entries` already existed as the exact 8-felt twin, the completion group
  was already in the verified layout, and the AIR constrains that group ONLY under the
  createCell/factory/spawn selectors — so the repair was PRODUCER-ONLY: no descriptor byte, no VK, no
  Lean AIR change. What it DOES change is the committed value of every `pre_state_hash`/`post_state_hash`,
  i.e. a receipt/consensus epoch), **#25**, **#27**.
  #27 is C/E and its width lives in the **Lean portal types**, so it starts in Lean by construction.
  Substrate partly exists (`CommitmentTreeAccumulator`, `DeployedHeapTree`/`Heap8Scheme` are
  Lean+wide); the work is authoring the wide note/nullifier/interface/attestation schemes there and
  routing deployed narrow paths through them. **NEVER hand-write the wide commitment in Rust.**
  And for every one of these: the wide scheme must fold the **REAL PREIMAGES** 8-felt end-to-end —
  re-hashing the existing narrow felt is `finalSqueezeOnly_still_conflates`, proved to still conflate
  — **and it must do so through a CANONICAL byte→felt codec** (`bytes32_to_u16_limbs`, sixteen `u16`
  lanes each `< 2^16 < p`), added 07-24: an 8-felt fold seeded by `encode_hash` /
  `bytes32_to_8_limbs` / `from_bytes_packed` / `canonical_32_to_felts_8` is still O(1) collidable on
  directly-chosen bytes, because those encoders are non-injective before the sponge ever runs.
- **D — 31-bit KEYS inside accumulators; widening the root did nothing.** The sorted-tree membership
  descriptor's key width — also Lean-authored AIR. #5, #9, #11, #20, **#24** (a leaf **VALUE** fold, not
  a key — the digest's proven injectivity is over a tuple that already lost the bits), **#28**/**#29**
  (dominated; standing falsifiers). The IR-level statement of the
  whole kind (found while pricing #20): `DescriptorIR2.lean:301-313` gives a `MapOp` 8-felt `root` /
  `newRoot` groups but a **scalar `key : EmittedExpr`**. That one type line is why every D site is
  un-widenable producer-side and why they must all ride ONE VK epoch. Price the D sites BOTH
  directions before calling them theft vectors: a same-fold-keyed `.absent` op can only over-include
  (availability), while a `.present`/membership-authorizes op is the soundness shape.
- **E — Narrow signed / PI payloads; wire + Fiat-Shamir changes ⇒ batch into ONE rotation epoch.**
  ~~#1~~ (DONE — v2 message, all 8 lanes), #2, #9, #11, **#27** (portal wire). Cheap now (nothing
  deployed), only gets more expensive.
- **F — Generalize the two defenses (the meta-repair; without it we play whack-a-mole).**
  (i) lint the whole tree for `felt_to_bytes32` / `.as_u32()` / `[0]` / `as u32` at security
  boundaries; (ii) extend the `Faithful8` type wall to **keys, PI vectors, signed payloads** so
  narrow-at-a-boundary becomes *un-representable*, not merely linted. **Refined by the 07-24 sweep:**
  part (i) splits. The **call-site shapes are lintable today and cheaply** — add `fold_bytes32($_)` and
  `felt_to_bytes32($_)` to `.ast-grep/rules/faithful-commitment-felt.yml`'s existing `any:` (two lines,
  no new files) and the gate immediately catches #24's producer, which sits in a file the gate ALREADY
  scopes. `.as_u32()` is **NOT lintable** — it is a lossless felt encode almost everywhere (Fiat-Shamir
  derivation, `faithful8_from_lanes`, the finality v2 per-lane absorb, every error-display struct) and a
  gate that fires there gets turned off. The shapes the linter structurally cannot see — a commitment
  producer that simply *returns `BabyBear`* (#23's `cells_root`, #28's `iroot`) and a Lean portal typed
  `Nat` (#27) — are exactly what part (ii) is for. Part (i) is a week's win; part (ii) is the only thing
  that retires the class.

---

## Notes / open severity questions (verify before pricing)

- **#1 exact cost — MOOT, the fix landed.** ~~depends on whether an attacker can mint alternate valid
  aggregates cheaply…~~ `finality_signing_message` is v2 and absorbs all 8 lanes; the seam compares
  full arrays. Kept as the record of how the question was framed, not as an open question.
- **#4 mint leg:** the legacy AIR's Merkle path chains from the 1-felt commitment
  (`circuit/src/note_spending_witness.rs:538`); whether the mint is reachable depends on which
  `ProofVerifier` `turn/src/executor/apply.rs:1221` is configured with (trait object, PI buffer
  "advisory"). Availability break is unconditional regardless.
- **#2 threat model — CONFIRMED and priced (07-24 sweep):** attacker builds their own 4-ary ring and
  chooses every sibling ⇒ controls the whole preimage, so the ~2^31 grind is OFFLINE with one final
  proof; same path as the action-binding 15 lines below (`sdk/src/verify.rs:216-221`) which correctly
  loops all 8 felts. Residual question answered too: **there is no in-tree deployed caller** of
  `verify_authorization_proof`, so this is a library-surface wound, not a live in-tree verdict.
- **#23 residual question — MOOT for the root, LIVE for the KEYS (the entry is CLOSED, see above):** how expensive is *mounting* a present-cell-set collision, as opposed to
  finding one? The grind is offline, but planting the colliding cell requires a real createCell turn
  (permissioned/priced per deployment). Nothing about the ~2^31 search changes; the deployment cost of
  the final step was not measured here.
- **#27 residual question (the one that decides its severity):** does any seL4 PD verdict actually
  route through the `@[extern]` portals rather than the in-Lean reference dictionaries? Answered only
  from the crate header + symbol consumers this pass; a boot would settle it.

## Meta-lesson (for memory)

The campaign widened **roots**, not **keys/payloads**; the lint covers **three files**; the class
lives in the **complement of both defenses**. A doc-comment asserting collision-resistance is a
*name*, not a proof — read the width, not the comment. Same discipline that surfaced the FRI floor:
check whether the deployed value equals what the proof/scheme actually binds.

**Added by the 07-24 sweep, three sharpenings of that lesson:**
1. **"Widened roots, not values" now has its sharpest instance: a FAITHFUL 8-felt chain can absorb a
   ~31-bit COMPONENT.** #23's `cells_root` and #28's `iroot` rode the genuine `Faithful8` chip chain as
   bare `BabyBear` limbs, three fields away from three siblings that are `Faithful8`. "The commitment is
   8-felt" is a statement about the CHAIN, never about what was fed to it. Read the component types.
   **Repaired for `cells_root` 07-24 by changing the TYPE, not the value** — `V9RotationContext.cells_root`
   is now `Faithful8`, so the next component of this anchor that is narrow will not compile. `iroot` is
   still bare, and deliberately: its FOLD is narrow too, so widening its carrier alone would launder.
2. **A layout slot for the wide lanes is not a wide binding.** #23's completion group 169..=175 existed
   and was documented — and was ZERO in the producer, filled only by one specialized trace generator. A
   detector read the layout and called the site safe. Check the WRITER, not the layout. **Corollary
   learned in the repair: an existing-but-unfilled slot can make a wound look expensive and be cheap.**
   #23 was catalogued kind C ("no wide scheme exists; must BUILD it") and was in fact producer-only —
   the wide twin already existed, the layout slot already existed, and the AIR gated the group only
   under three selectors. Price the WRITER and the SELECTOR before pricing the epoch.
3. **An unanchored gate hides a width question rather than answering it.** #24's `targetBindGate` and
   #25's `burn_target` PI both look like authorizing equalities and neither is compared against a
   trusted value today (the producer sets both sides; the one trusted-side comparer is dead code). That
   makes them NOT-live — and it makes the width a *pre-priced* liability, because the anchoring work is
   already half-wired. When you find a narrow gate nobody anchors, the entry to write is the standing
   falsifier, not a dismissal.

**Added by the 07-24 re-pricing, the fourth and sharpest:**
4. **WIDTH IS NOT A PRICE. The price is the ENCODER plus who picks the bytes plus whether the attack
   needs a collision or a targeted hit.** This catalogue quoted `~2^31` from the felt width ~42
   times; the width bounds the IMAGE, and every one of the four byte→felt encoders in the tree is
   non-injective *by construction* — one is a linear form (`fold_bytes32_to_bb`), two reduce each
   4-byte chunk mod `p` without a canonicity check (`encode_hash`, `bytes32_to_8_limbs`,
   `from_bytes_packed`), one simply discards 16 bits (`canonical_32_to_felts_8`). Where the bytes
   are prover-chosen, a colliding pair is CONSTRUCTED. The `~2^31` survives only against hash
   images, and only for the *targeted* half of the threat. The tell that this was missed for five
   days: two in-tree tests already EXHIBIT free collisions of the deployed fold
   (`exact_cap_root.rs:505`, `state.rs:1435`) and the sweep cited one of them as the *evidence base*
   for the 2^31 prices. **Read the encoder, then the byte source, then the threat direction — in
   that order — before any cost goes on this page.**
