//! **THE consensus state anchor** — the AIR-bound chip 8-felt commitment that a
//! receipt chains, an executor signs, and a federation quorum certifies.
//!
//! # What this replaced, and why
//!
//! Until this module landed, `TurnReceipt::{pre,post}_state_hash` carried
//! [`dregg_cell::Ledger::root`] — a hand-written BLAKE3 Merkle tree over the
//! ledger's cells. That value is **trusted Rust**: no AIR constrains it, no
//! circuit ever recomputes it, and the object chained/signed/gossiped as "the
//! state" was therefore attested by a witness generator with zero proof
//! obligation (assurance-perimeter inventory #1/#2).
//!
//! There *is* a genuine dual-hash architecture in this tree — see the ADR in
//! `dregg_commit::hash`: BLAKE3 for non-ZK paths (storage keys, gossip message
//! hashes, capability-token derivation, general-purpose Merkle commitments),
//! Poseidon2 for anything a circuit must recompute. The consensus ledger root
//! sat **outside** that ADR's stated scope while inheriting its hash: it is not
//! a fast path chosen over Poseidon2, it is the un-migrated remainder. The
//! lazy-materialization comment on `Ledger::root` justifies *when* to hash, not
//! *which* hash. BLAKE3 keeps every site the ADR actually covers; it loses the
//! consensus anchor.
//!
//! # What the anchor is
//!
//! [`consensus_state_commitment`] is
//! `felt8_to_bytes32(compute_canonical_state_commitment_v9_felt8(cell, ctx))` —
//! the **chip** 8-felt chain (`Faithful8::from_wire_commit_chip`), i.e. the same
//! value the deployed rotated EffectVM trace publishes as its wide `STATE_COMMIT`
//! carrier. ~124-bit collision resistance, an 8-felt carrier at every
//! intermediate step, no ~31-bit waist in the chain.
//!
//! ⚑ It is deliberately NOT `rotation_witness::wire_commit_8`: that helper calls
//! the plain [`dregg_circuit::Faithful8::from_wire_commit`], which **diverges**
//! from the deployed `wire_commit_8_chip` (no arity-tag seeding — see
//! `dregg_circuit::poseidon2`). Anchoring on the plain chain would produce a
//! commitment no honest wide proof's BEFORE carrier equals. The sovereign and
//! encrypted paths already anchor on the chip chain; this module makes the
//! classical path agree with them.
//!
//! # ⚑ THE RESIDUAL — read this before citing the anchor as "proven"
//!
//! Landing this does **not** close assurance-perimeter #2. Precisely:
//!
//! 1. **The flagship `⟺` theorems certify the 1-felt `wireCommitR`, not this
//!    8-felt chain.** `transferDescriptor_commit_iff` and its siblings are
//!    machine-checked against the ~31-bit `wire_commit`. The 8-felt value is
//!    **chip-bound and soundness-ADDITIVE** — it is the carrier the deployed
//!    trace publishes, which is strictly more binding than the 1-felt waist, but
//!    `air_accepts ⟺ spec` **at 8 felts** awaits the S2 flag-day plus an 8-felt
//!    re-derivation of the refinement. That re-derivation is itself gated on
//!    `Poseidon2WideCR` / `InjectiveFloorRegrounded`, which are **vacuous at real
//!    parameters** (a compressing hash HAS collisions; the named carrier is an
//!    assumption, not a discharge). So: the anchor is the *right object*, and it
//!    is *not yet a proven* one.
//! 2. **This is a per-cell / per-transition commit, NOT the whole-ledger
//!    snapshot `Ledger::root()` was.** A multi-cell turn has multiple legs and
//!    therefore multiple such commitments; this anchors the turn's *agent* leg.
//!    The whole-ledger 8-felt state root is the deferred `cells_root` Phase-E
//!    work. The consequence is visible in [`consensus_state_commitment`]'s
//!    contract: it binds the agent cell's own state faithfully and the rest of
//!    the ledger only through the `cells_root` *existence* fold, which is a
//!    set-of-present-cells digest, not a state digest. That fold is now
//!    **faithful in WIDTH** (wound #23: the 8-felt `CanonicalHeapTree8` group at
//!    limb 0 ‖ 169..=175, `node8` at every intermediate) — but width is not
//!    content: an existence bit per cell still says nothing about those cells'
//!    balances, and the *keys* of that tree are still one-felt digests of the
//!    32-byte `CellId` (the accumulator-KEY class, kind D, unclosed).
//! 3. **The lane-0 waist persists** wherever a narrow leg still broadcasts into
//!    slot 0 of a wide carrier. This anchor does not touch those sites. The one
//!    that was IN this anchor — `cells_root` — is closed; `V9RotationContext.iroot`
//!    is the remaining bare `BabyBear` in the same struct (see below).
//! 3b. **`iroot` is STILL a 1-felt left-leaning fold** (`rotation_witness::iroot`,
//!    every intermediate `root: BabyBear` ~31 bits). It is ZERO on this path — the
//!    ctx builder below pins it, deliberately — so it contributes nothing to the
//!    deployed anchor today; it is a standing falsifier the moment a live receipt
//!    MMR root is threaded here, and widening `cells_root` did NOT close it.
//! 4. **Cost.** `Ledger::root()` was an incrementally-maintained O(log n) leaf
//!    patch. This anchor is O(n_cells) Poseidon2 for `cells_root` plus a
//!    `CanonicalHeapTree8` rebuild per accumulator, twice per turn (pre + post).
//!    That is a real regression on the hot path, taken deliberately: the node's
//!    `canonical_ledger_root` already pays O(n) BLAKE3 + postcard per finalized
//!    block, so this is not a new asymptotic class at the consensus boundary,
//!    but the executor did get slower. `executor::turn_profile`'s `pre_root` /
//!    `post_root` phases measure it.
//!
//! # What the quorum signs
//!
//! `TurnReceipt::receipt_hash` (domain `dregg-receipt-v5`) absorbs both
//! `pre_state_hash` and `post_state_hash`, so:
//!
//! * the **executor signature** (`executor-receipt-sig-v5`) signs the anchor;
//! * the **federation receipt QC** — a BLS threshold aggregate over
//!   `FederationReceiptBody::body_hash` (`dregg-fed-receipt-body-v2`) — is a
//!   genuine quorum certificate over the anchor;
//! * the **`AttestedRoot` quorum** binds `receipt_stream_root`, a Merkle root
//!   over `receipt_hash()`es, so the attestation signature transitively covers
//!   the anchor too.
//!
//! `AttestedRoot::merkle_root` and `FinalizationVote::merkle_root` deliberately
//! remain `dregg_persist::canonical_ledger_root` (BLAKE3): that value is the
//! **whole-image restart anchor** — a node re-reads its store, reconstructs the
//! ledger, and checks the reconstruction hashes to the quorum-signed root. No
//! per-cell algebraic commitment fills that role, and the whole-ledger 8-felt
//! that would is the deferred Phase-E `cells_root`. Those preimages are
//! domain-bumped so the *meaning* change is fenced, but the whole-image digest
//! itself stays BLAKE3 on a documented, non-circuit rationale.

use dregg_cell::commitment::{RotationCarrierMaterial, V9_NUM_PRE_LIMBS, V9RotationContext};
use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::Faithful8;
use dregg_circuit::field::BabyBear;

/// Build the turn-level rotation context the anchor commits against.
///
/// The three accumulator roots are the executor's LIVE `root8()`s, so the
/// commitment moves when the shielded-note / revocation accumulators move —
/// exactly as the circuit's carrier does.
///
/// `iroot` is **zero** (the empty receipt-log MMR). The receipt-index MMR is a
/// node-level accumulator (`node::api`'s `receipt_index`), not state the
/// executor holds; and the anchor cannot bind the *current* turn's receipt
/// anyway, since that receipt's hash is computed FROM this commitment. The
/// receipt log is bound into `receipt_hash` by `previous_receipt_hash` instead,
/// which chains the whole history. Using the same constant for pre and post is
/// what makes chain continuity exact.
pub fn consensus_ctx(
    ledger: &Ledger,
    nullifier_root: Faithful8,
    commitments_root: Faithful8,
    revoked_root: Faithful8,
) -> V9RotationContext {
    V9RotationContext {
        cells_root: crate::rotation_witness::cells_root(ledger),
        nullifier_root,
        commitments_root,
        revoked_root,
        iroot: BabyBear::ZERO,
        material: RotationCarrierMaterial::default(),
    }
}

/// **THE anchor.** The AIR-bound chip 8-felt commitment of `agent`'s cell under
/// `ctx`, packed as 32 bytes (8 felts × 4 LE bytes — the whole slot, unlike the
/// 1-felt encoding which leaves 28 bytes zero).
///
/// `pre_state_hash` and `post_state_hash` MUST both come from this function, or
/// every consumer that compares them across receipts compares incomparable
/// values.
///
/// ⚑ To be exact about WHICH consumer, because the note that stood here named
/// the wrong one: `verify::verify_receipt_chain` does **NOT** check
/// `curr.pre_state_hash == prev.post_state_hash`, and says so deliberately
/// (`verify.rs:147-153`) — the chain is agent-scoped while these snapshots
/// absorb executor-GLOBAL roots, so another agent's intervening turn legitimately
/// moves them. The comparison is made only by head-binding callers
/// (`federation/src/types.rs:522`, the exit path, which raises
/// `VerifyError::StateChainBreak`). Nothing on the ordinary receipt-chain path
/// checks the pre-state a turn claims to have begun from.
///
/// # The absent agent
///
/// A turn can remove its own agent cell (`MakeSovereign`, a destroy). The
/// post-state then has no cell to commit. Rather than stamp a sentinel that
/// collides across ledgers, the absent case commits the turn-level **boundary**:
/// an all-zero limb vector carrying the faithful 8-felt `cells_root` group (limb
/// 0 ‖ 169..=175), chip-chained under the same `iroot`. That value is well
/// defined, distinct from any live cell's commitment (a live cell's limbs 1..3
/// carry balance/nonce, which the zero vector does not), and still MOVES when the
/// set of present cells moves — so a removal is not a fixed point. Since wound
/// #23 that "still MOVES" holds at ~124 bits: before the completion group was
/// filled, the entire absent anchor was a chip chain over ONE ~31-bit felt.
///
/// ⚑ "STILL MOVES" IS FALSE FOR A COLLIDING PAIR, and the width fix does not
/// reach it. `cells_root` keys each cell by `heap_addr(CELLS_COLLECTION,
/// hash_bytes(id))` — ONE ~31-bit felt (`rotation_witness.rs:311`, and see the
/// ⚑ on that fn) — and `compute_canonical_heap_root_8` DEDUPES leaves by that
/// address (`circuit/src/heap_root.rs:832`, `leaves.dedup_by_key(|l|
/// l.addr.as_u32())`), silently, with no error. So two cells whose key folds
/// collide occupy ONE leaf: removing either one leaves the root UNCHANGED, and
/// the removal IS a fixed point of the anchor. `CellId::derive_raw` is BLAKE3
/// over attacker-chosen `(public_key, token_id)`, so a targeted second preimage
/// against a chosen victim cell is a ~2^31 offline grind. The ~124-bit claim
/// prices the root's WIDTH; it does not price the KEY, and the key is what
/// decides whether a cell is in the set at all.
pub fn consensus_state_commitment(
    ledger: &Ledger,
    agent: &CellId,
    ctx: &V9RotationContext,
) -> [u8; 32] {
    match ledger.get(agent) {
        Some(cell) => cell_state_commitment(cell, ctx),
        None => absent_cell_commitment(ctx),
    }
}

/// The anchor for a cell already in hand — the shared body of
/// [`consensus_state_commitment`]. Delegates to the cell crate's
/// `compute_canonical_state_commitment_v9_felt8`, which is the CHIP chain.
pub fn cell_state_commitment(cell: &Cell, ctx: &V9RotationContext) -> [u8; 32] {
    dregg_cell::commitment::compute_canonical_state_commitment_v9_felt8(cell, ctx).to_bytes32()
}

/// The boundary commitment for a turn whose agent cell is gone post-state — see
/// [`consensus_state_commitment`]'s "absent agent" section.
pub fn absent_cell_commitment(ctx: &V9RotationContext) -> [u8; 32] {
    let mut limbs = vec![BabyBear::ZERO; V9_NUM_PRE_LIMBS];
    // The FAITHFUL 8-felt `cells_root` group (lane 0 = limb 0 ‖ completion 169..=175) — the SAME
    // fill `compute_rotated_pre_limbs` does, so the absent anchor is the boundary projection of
    // the live one. This case is where wound #23 bit hardest: with a zero-filled completion group
    // the WHOLE absent post-state anchor was one ~31-bit felt (every other limb is zero), so two
    // present-cell sets colliding on the lane-0 fold produced one signed post-state for two
    // different ledgers. At 8 felts the "still MOVES when the set of present cells moves" claim
    // below holds at the chain's own ~124-bit width instead of ~31.
    ctx.cells_root.write_lanes(
        &mut limbs,
        dregg_circuit::effect_vm::layout_generated::CELLS_ROOT_GROUP,
    );
    Faithful8::from_wire_commit_chip(&limbs, ctx.iroot).to_bytes32()
}

/// Convenience: build the context and commit in one call, for callers that hold
/// the accumulator roots but not a context.
pub fn consensus_state_commitment_with_roots(
    ledger: &Ledger,
    agent: &CellId,
    nullifier_root: Faithful8,
    commitments_root: Faithful8,
    revoked_root: Faithful8,
) -> [u8; 32] {
    let ctx = consensus_ctx(ledger, nullifier_root, commitments_root, revoked_root);
    consensus_state_commitment(ledger, agent, &ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::commitment::compute_rotated_pre_limbs;

    fn empty_ctx(ledger: &Ledger) -> V9RotationContext {
        consensus_ctx(
            ledger,
            crate::rotation_witness::empty_nullifier_root_8(),
            crate::rotation_witness::empty_commitments_root_8(),
            crate::rotation_witness::empty_revoked_root_8(),
        )
    }

    fn cell_with(balance: u64) -> Cell {
        let mut c = Cell::new([7u8; 32], [0u8; 32]);
        let _ = c.state.credit_balance(balance);
        c
    }

    /// THE anchor test: the committed value is the chip 8-felt, NOT the BLAKE3
    /// ledger root — and it fills the whole 32-byte slot.
    #[test]
    fn anchor_is_the_chip_8_felt_not_blake3() {
        let cell = cell_with(500);
        let id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell.clone()).unwrap();
        let ctx = empty_ctx(&ledger);

        let anchor = consensus_state_commitment(&ledger, &id, &ctx);
        let blake3_root = ledger.root();
        assert_ne!(
            anchor, blake3_root,
            "the anchor must not be the trusted-Rust BLAKE3 ledger root"
        );

        // It IS the chip chain over the rotated pre-limbs.
        let pre = compute_rotated_pre_limbs(&cell, &ctx);
        let expected = Faithful8::from_wire_commit_chip(&pre, ctx.iroot).to_bytes32();
        assert_eq!(anchor, expected, "anchor must be `wire_commit_8_chip`");

        // The 1-felt encoding leaves 28 zero bytes; the 8-felt fills the slot.
        assert!(
            anchor[8..].iter().any(|b| *b != 0),
            "the 8-felt anchor must fill the whole slot, not just the low felt"
        );
    }

    /// ⚑ THE FOOTGUN CANARY: the plain `wire_commit_8` chain DIVERGES from the
    /// deployed chip chain (arity-tag seeding). If this ever passes, the two
    /// chains have been unified and the footgun warning can go — until then, a
    /// site that anchors on the plain chain is anchoring on a value no honest
    /// wide proof carries.
    #[test]
    fn plain_wire_commit_8_diverges_from_the_chip_chain() {
        let cell = cell_with(11);
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell.clone()).unwrap();
        let ctx = empty_ctx(&ledger);
        let pre = compute_rotated_pre_limbs(&cell, &ctx);

        let chip = Faithful8::from_wire_commit_chip(&pre, ctx.iroot);
        let plain = crate::rotation_witness::wire_commit_8(&pre, ctx.iroot);
        assert_ne!(
            chip.to_bytes32(),
            plain.to_bytes32(),
            "chip and plain 8-felt chains must differ — the anchor MUST use the chip chain"
        );
    }

    /// A tampered cell state moves the anchor (it is a commitment, not a tag).
    #[test]
    fn anchor_moves_when_state_moves() {
        let cell = cell_with(500);
        let id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();
        let before = {
            let ctx = empty_ctx(&ledger);
            consensus_state_commitment(&ledger, &id, &ctx)
        };

        ledger
            .update_with(&id, |c| {
                let _ = c.state.credit_balance(1);
            })
            .unwrap();

        let after = {
            let ctx = empty_ctx(&ledger);
            consensus_state_commitment(&ledger, &id, &ctx)
        };
        assert_ne!(before, after, "a balance change must move the anchor");
    }

    /// The absent-agent boundary commitment is well defined, distinct from any
    /// live cell's commitment, and moves with the present-cell set.
    #[test]
    fn absent_agent_commitment_is_distinct_and_live() {
        let cell = cell_with(3);
        let id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();
        let ctx = empty_ctx(&ledger);

        let live = consensus_state_commitment(&ledger, &id, &ctx);
        let absent = absent_cell_commitment(&ctx);
        assert_ne!(live, absent, "absent boundary must not alias a live cell");

        let empty_ledger = Ledger::new();
        let absent_empty = absent_cell_commitment(&empty_ctx(&empty_ledger));
        assert_ne!(
            absent, absent_empty,
            "the absent boundary must move with `cells_root`"
        );
    }

    /// The accumulator roots are BOUND: a different nullifier root is a
    /// different commitment (so the anchor tracks the circuit's carrier).
    #[test]
    fn accumulator_roots_are_bound() {
        let cell = cell_with(9);
        let id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();

        let a = consensus_state_commitment(&ledger, &id, &empty_ctx(&ledger));

        let mut nulls = dregg_cell::nullifier_set::NullifierSet::new();
        nulls
            .insert(dregg_cell::note::Nullifier([4u8; 32]), 1)
            .unwrap();
        let ctx_b = consensus_ctx(
            &ledger,
            nulls.root8(),
            crate::rotation_witness::empty_commitments_root_8(),
            crate::rotation_witness::empty_revoked_root_8(),
        );
        let b = consensus_state_commitment(&ledger, &id, &ctx_b);
        assert_ne!(a, b, "the nullifier accumulator root must be bound");
    }
}
