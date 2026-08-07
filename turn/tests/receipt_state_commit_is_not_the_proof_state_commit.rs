//! ⚑ **THE MEASUREMENT THAT DECIDES WHAT A PER-TURN ANCHOR CAN AND CANNOT BIND.**
//!
//! `docs/DESIGN-pi-authority.md` §4(a) proposed publishing "the canonical 8-felt
//! `old_commit`/`new_commit` for a turn (from the node's own committed state, which it has)" so
//! that `verify_full_turn_bound`'s two endpoint `CommitmentMismatch` teeth stop comparing
//! `x != x`. The node's committed state DOES hold a per-turn 8-felt commit pair — the receipt's
//! `pre_state_hash` / `post_state_hash`, which the committee's attestation signature transitively
//! covers via `receipt_stream_root`.
//!
//! **It is not the pair the full-turn proof publishes.** This file measures that, and isolates
//! the two causes, each independently sufficient:
//!
//! * **`iroot`.** `state_commit::consensus_ctx` pins `rotation_witness::empty_iroot()`
//!   deliberately (a receipt cannot bind a commitment its own hash is computed from). The
//!   proof-side witness folds the REAL receipt chain — the live commit path threads
//!   `[receipt.receipt_hash()]` into `rotation_witness_for_self_sovereign_with_root`.
//! * **`cells_root`.** `consensus_ctx` folds `rotation_witness::cells_root(ledger)` over the
//!   WHOLE ledger. The proof-side builder
//!   (`node::turn_proving::rotation_witness_for_self_sovereign_impl`) folds a SINGLE-CELL context
//!   ledger holding only the actor.
//!
//! So `dregg_federation::TurnAnchorV1` carries a committee-signed 8-felt pair that must be
//! REPORTED and must never be handed to `verify_full_turn_bound` as `expected_old_commit` — it
//! would refuse every honest proof. The anchor binds the **turn identity** instead, which every
//! effect-vm leg publishes and the verifier takes as a required argument.
//!
//! ## This test is a GATE, not a note
//!
//! It asserts the divergence, so aligning the two contexts (the real fix, priced in
//! `docs/DESIGN-pi-authority.md`) makes this file go RED and forces whoever does it to come here,
//! delete the divergence assertions, and open the endpoint binding this file's docs forbid. A
//! silent alignment is not possible.

use dregg_cell::{Cell, Ledger};
use dregg_circuit::Faithful8;
use dregg_turn::rotation_witness as rw;
use dregg_turn::state_commit;

fn cell_with(seed: u8, balance: u64) -> Cell {
    let mut c = Cell::new([seed; 32], [0u8; 32]);
    let _ = c.state.credit_balance(balance);
    c
}

/// The chip 8-felt commit of `cell` under an explicitly-built context — the shared body of both
/// sides, so the only thing that varies between the arms below is the context itself.
fn commit_under(
    cell: &Cell,
    ctx_ledger: &Ledger,
    receipt_hashes: &[[u8; 32]],
    revoked: &Faithful8,
) -> [u8; 32] {
    let w = rw::produce(
        cell,
        ctx_ledger,
        &rw::empty_nullifier_root_8(),
        &rw::empty_commitments_root_8(),
        revoked,
        receipt_hashes,
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    Faithful8::from_wire_commit_chip(&w.pre_limbs, w.iroot).to_bytes32()
}

#[test]
fn the_receipt_state_commit_is_not_the_proof_state_commit() {
    // A ledger with more than one cell — every devnet has many.
    let alice = cell_with(0xA1, 1000);
    let bob = cell_with(0xB2, 500);
    let alice_id = alice.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(alice.clone()).expect("insert alice");
    ledger.insert_cell(bob).expect("insert bob");

    // The proof-side builder's context ledger: the ACTOR ALONE.
    let mut ctx_ledger = Ledger::new();
    ctx_ledger.insert_cell(alice.clone()).expect("insert actor");

    let revoked = rw::empty_revoked_root_8();

    // ── THE RECEIPT SIDE — what the committee signs. ────────────────────────
    let exec_ctx = state_commit::consensus_ctx(
        &ledger,
        rw::empty_nullifier_root_8(),
        rw::empty_commitments_root_8(),
        revoked,
    );
    let receipt_commit = state_commit::consensus_state_commitment(&ledger, &alice_id, &exec_ctx);

    // CONTROL: reproducing the executor's context reproduces its commit exactly. Without this,
    // every `assert_ne!` below could be an artefact of a mis-built helper rather than a real
    // divergence.
    assert_eq!(
        receipt_commit,
        commit_under(&alice, &ledger, &[], &revoked),
        "CONTROL: the same context must reproduce the receipt's anchor"
    );

    // ── CAUSE 1: `iroot`, alone. ────────────────────────────────────────────
    // Same whole-ledger cells_root, same accumulator roots; only the receipt-chain fold differs.
    let a_receipt_hash = [0x7Eu8; 32];
    let iroot_only = commit_under(&alice, &ledger, &[a_receipt_hash], &revoked);
    assert_ne!(
        receipt_commit, iroot_only,
        "folding the real receipt chain into `iroot` must move the commit — if it does not, \
         `empty_iroot()` is aliasing a real fold and the anchor is weaker than documented"
    );

    // ── CAUSE 2: `cells_root`, alone. ───────────────────────────────────────
    // Same empty iroot, same accumulator roots; only the context ledger differs.
    let cells_only = commit_under(&alice, &ctx_ledger, &[], &revoked);
    assert_ne!(
        receipt_commit, cells_only,
        "a single-cell context ledger must move the commit — the whole-ledger `cells_root` is a \
         real component of the consensus anchor"
    );

    // ── BOTH, as the live paths actually differ. ────────────────────────────
    let proof_commit = commit_under(&alice, &ctx_ledger, &[a_receipt_hash], &revoked);
    assert_ne!(
        receipt_commit, proof_commit,
        "⚑ if this passes, the receipt's committee-signed 8-felt pair HAS become the proof's \
         published pair. That is the alignment `docs/DESIGN-pi-authority.md` prices, and it is \
         GOOD NEWS — but it means `dregg_federation::turn_anchor`'s docs, and the endpoint's \
         refusal to publish `expected_old_commit`, are now wrong. Go update them."
    );
}
