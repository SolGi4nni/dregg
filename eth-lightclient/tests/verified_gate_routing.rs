//! **The relayer's own entry point is gated by the archive — and the gate BITES there.**
//!
//! `dregg-lean-ffi`'s own tests prove `dregg_eth_lc_verify` discriminates when called directly.
//! That is a fact about the BRIDGE. This file is a fact about the RELAYER: every assertion here
//! goes through `eth_lightclient::finality::verify_finalized_update` — the function a node
//! actually calls — on REAL captured mainnet data (the same period-1800 fixture `end_to_end.rs`
//! uses: 512 genuine committee pubkeys, a genuine aggregate G2 signature at 397/512, a genuine
//! depth-7 post-Electra finality branch and depth-4 execution branch).
//!
//! ## Why these tests are a mutation canary and not decoration
//!
//! After the twin deletion there is NO Rust rule left in this crate's ETH verify path: no
//! threshold, no committee-size check, no floor, no depth admissibility. The only thing that
//! can turn a `LightClientUpdate` into a `FinalizedExecution` is the archive's verdict. So:
//!
//!   * Swap the gate for **always-accept** and every `must be REFUSED` case below fails —
//!     there is no second opinion to catch the forgery.
//!   * Swap it for **always-reject** (or always-`"ERR"`, the drift that fail-closes everything
//!     and would otherwise satisfy every reject assertion) and
//!     [`real_mainnet_update_is_accepted_through_the_relayer_entry_point`] fails.
//!   * [`one_field_apart_verdicts_must_differ`] is the assertion no CONSTANT gate can satisfy at
//!     all: two updates differing in a single bit, straddling the decision boundary, must get
//!     different answers through the entry point.
//!   * [`the_entry_point_verdict_is_the_archives_verdict`] pins that the `Ok`/`Err` this crate
//!     returns is the archive's own `"1"`/`"0"` on the projected wire — case by case, over the
//!     whole mutation grid, so agreement is not a coincidence of one sample.
//!
//! ## Archive-absent posture
//!
//! `eth-lightclient` FAILS CLOSED: with no `dregg_eth_lc_verify` export it cannot verify
//! anything, and [`the_archive_is_a_hard_requirement`] says so once, loudly, instead of letting
//! it surface as a dozen confusing failures elsewhere. There is deliberately no skip and no
//! fallback — a light client that quietly reverts to unverified rules when its verifier is
//! missing is the exact posture this wiring exists to end.

#[path = "fixtures/e2e_mainnet.rs"]
#[allow(dead_code)]
mod e2e;

use eth_lightclient::execution::ExecutionPayloadHeader;
use eth_lightclient::finality::{
    project_update, verify_finalized_update, LightClientHeader, LightClientUpdate,
};
use eth_lightclient::verified_gate;
use eth_lightclient::{
    BeaconBlockHeader, Error, SyncAggregate, TrustedCommittee, SYNC_COMMITTEE_SIZE,
};

// -------------------- hex helpers (same fixture as end_to_end.rs) --------------------

fn h32(s: &str) -> [u8; 32] {
    hex::decode(s).expect("hex32").try_into().expect("32 bytes")
}
fn h20(s: &str) -> [u8; 20] {
    hex::decode(s).expect("hex20").try_into().expect("20 bytes")
}
fn h48(s: &str) -> [u8; 48] {
    hex::decode(s).expect("hex48").try_into().expect("48 bytes")
}
fn h64(s: &str) -> [u8; 64] {
    hex::decode(s).expect("hex64").try_into().expect("64 bytes")
}
fn h96(s: &str) -> [u8; 96] {
    hex::decode(s).expect("hex96").try_into().expect("96 bytes")
}
fn h256(s: &str) -> [u8; 256] {
    hex::decode(s)
        .expect("hex256")
        .try_into()
        .expect("256 bytes")
}
fn branch(list: &[&str]) -> Vec<[u8; 32]> {
    list.iter().map(|s| h32(s)).collect()
}

fn gvr() -> [u8; 32] {
    h32(e2e::GENESIS_VALIDATORS_ROOT)
}

fn committee_pubkeys() -> Vec<[u8; 48]> {
    let pks: Vec<[u8; 48]> = e2e::COMMITTEE_PUBKEYS.iter().map(|s| h48(s)).collect();
    assert_eq!(pks.len(), SYNC_COMMITTEE_SIZE);
    pks
}

fn update() -> LightClientUpdate {
    LightClientUpdate {
        attested_header: BeaconBlockHeader {
            slot: e2e::ATTESTED_SLOT,
            proposer_index: e2e::ATTESTED_PROPOSER,
            parent_root: h32(e2e::ATTESTED_PARENT_ROOT),
            state_root: h32(e2e::ATTESTED_STATE_ROOT),
            body_root: h32(e2e::ATTESTED_BODY_ROOT),
        },
        finalized_header: LightClientHeader {
            beacon: BeaconBlockHeader {
                slot: e2e::FIN_SLOT,
                proposer_index: e2e::FIN_PROPOSER,
                parent_root: h32(e2e::FIN_PARENT_ROOT),
                state_root: h32(e2e::FIN_STATE_ROOT),
                body_root: h32(e2e::FIN_BODY_ROOT),
            },
            execution: ExecutionPayloadHeader {
                parent_hash: h32(e2e::EX_PARENT_HASH),
                fee_recipient: h20(e2e::EX_FEE_RECIPIENT),
                state_root: h32(e2e::EX_STATE_ROOT),
                receipts_root: h32(e2e::EX_RECEIPTS_ROOT),
                logs_bloom: h256(e2e::EX_LOGS_BLOOM),
                prev_randao: h32(e2e::EX_PREV_RANDAO),
                block_number: e2e::EX_BLOCK_NUMBER,
                gas_limit: e2e::EX_GAS_LIMIT,
                gas_used: e2e::EX_GAS_USED,
                timestamp: e2e::EX_TIMESTAMP,
                extra_data: hex::decode(e2e::EX_EXTRA_DATA).expect("extra_data hex"),
                base_fee_per_gas: h32(e2e::EX_BASE_FEE_LE32),
                block_hash: h32(e2e::EX_BLOCK_HASH),
                transactions_root: h32(e2e::EX_TRANSACTIONS_ROOT),
                withdrawals_root: h32(e2e::EX_WITHDRAWALS_ROOT),
                blob_gas_used: e2e::EX_BLOB_GAS_USED,
                excess_blob_gas: e2e::EX_EXCESS_BLOB_GAS,
            },
            execution_branch: branch(e2e::EXECUTION_BRANCH),
        },
        finality_branch: branch(e2e::FINALITY_BRANCH),
        sync_aggregate: SyncAggregate {
            sync_committee_bits: h64(e2e::SYNC_COMMITTEE_BITS),
            sync_committee_signature: h96(e2e::SYNC_COMMITTEE_SIGNATURE),
        },
    }
}

/// Clear set participation bits (highest index first) until exactly `target` remain.
fn thin_participation_to(agg: &mut SyncAggregate, target: usize) {
    for i in (0..SYNC_COMMITTEE_SIZE).rev() {
        let count: usize = agg
            .sync_committee_bits
            .iter()
            .map(|b| b.count_ones() as usize)
            .sum();
        if count <= target {
            break;
        }
        if agg.participated(i) {
            agg.sync_committee_bits[i / 8] &= !(1u8 << (i % 8));
        }
    }
}

fn verdict(u: &LightClientUpdate, committee: &[[u8; 48]]) -> Result<(), Error> {
    verify_finalized_update(
        u,
        &TrustedCommittee::new_unchecked(committee, gvr()),
        e2e::FORK_VERSION,
    )
    .map(|_| ())
}

// ---------------------------------------------------------------------------

/// The whole crate's verify surface routes through `dregg_eth_lc_verify`. If the archive does
/// not export it, `eth-lightclient` verifies NOTHING — say that once, here, in terms an operator
/// can act on, rather than letting it show up as an unrelated-looking failure in five files.
#[test]
fn the_archive_is_a_hard_requirement() {
    assert!(
        verified_gate::available(),
        "the linked archive does not export dregg_eth_lc_verify, so eth-lightclient cannot \
         render ANY light-client verdict (it fails closed: every verify entry point returns \
         Error::VerifiedGateUnavailable). There is no Rust fallback — the Rust rules WERE the \
         twin this crate deleted. Seed a HEAD-matching dregg-lean-ffi/libdregg_lean.a and \
         rebuild."
    );
}

/// ACCEPT, through the relayer's own entry point, on external mainnet data. Present so nothing
/// below can be satisfied by a gate that refuses everything.
#[test]
fn real_mainnet_update_is_accepted_through_the_relayer_entry_point() {
    let u = update();
    let committee = committee_pubkeys();
    let finalized = verify_finalized_update(
        &u,
        &TrustedCommittee::new_unchecked(&committee, gvr()),
        e2e::FORK_VERSION,
    )
    .expect("the verified Lean gate must ACCEPT the genuine mainnet update");
    assert_eq!(finalized.finalized_slot(), e2e::FIN_SLOT);
    assert_eq!(finalized.execution_state_root(), h32(e2e::EX_STATE_ROOT));

    // And the projections handed to the archive really are the update's (397/512, depth 7 / 4),
    // not neutral filler that would accept regardless of the data.
    let (p, _) = project_update(&u, &committee, e2e::FORK_VERSION, gvr());
    assert_eq!(p.committee_len, 512);
    assert_eq!(p.bits_len, 512);
    assert_eq!(p.participant_count, 397);
    assert!(p.bls_ok);
    assert_eq!(p.finality_len, 7);
    assert!(p.finality_ok);
    assert_eq!(p.exec_len, 4);
    assert!(p.exec_ok);
    assert_eq!(verified_gate::raw(&p).as_deref(), Ok("1"));
}

/// REFUSED, through the relayer's own entry point — one forgery per conjunct of the verified
/// decision. Every one of these is an update a light client must not advance on, and every one
/// of them is refused by the archive, not by a Rust rule.
#[test]
fn forged_updates_are_refused_through_the_relayer_entry_point() {
    let committee = committee_pubkeys();

    // Sub-quorum: 341/512 signed (3·341 = 1023 < 1024 = 2·512). The sharpest tooth — one below
    // the threshold, so a `>` / `>=` / rounding slip in the rules shows up here and nowhere else.
    let mut u = update();
    thin_participation_to(&mut u.sync_aggregate, 341);
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::InsufficientParticipation {
            participants: 341,
            required: 342,
        }),
        "a SUB-QUORUM update must be REFUSED"
    );

    // The Nomad zero floor: nobody signed at all.
    let mut u = update();
    u.sync_aggregate.sync_committee_bits = [0u8; SYNC_COMMITTEE_SIZE / 8];
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::NoParticipants),
        "a zero-participant update must be REFUSED"
    );

    // A FORGED aggregate signature: full genuine participation, one flipped bit in the G2 point.
    let mut u = update();
    u.sync_aggregate.sync_committee_signature[95] ^= 0x01;
    assert!(
        matches!(
            verdict(&u, &committee),
            Err(Error::BadSignature) | Err(Error::BadPubkey)
        ),
        "a forged BLS aggregate must be REFUSED, got {:?}",
        verdict(&u, &committee)
    );

    // A committee that is not exactly 512 keys — the denominator the 2/3 threshold divides
    // cannot be shrunk to manufacture a quorum.
    let mut short = committee.clone();
    short.pop();
    assert_eq!(
        verdict(&update(), &short),
        Err(Error::WrongCommitteeSize { got: 511 }),
        "a committee that is not exactly 512 keys must be REFUSED"
    );

    // A finality branch of an inadmissible DEPTH (5): this is what stops a proof rooted at the
    // wrong generalized index from being replayed as a finality proof.
    let mut u = update();
    u.finality_branch.truncate(5);
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::WrongBranchLength {
            got: 5,
            expected: 7
        }),
        "a wrong-depth finality branch must be REFUSED"
    );

    // A TAMPERED finality branch (right depth, does not reconstruct the attested state root):
    // a correctly-signed update still cannot smuggle in an unproven finalized header.
    let mut u = update();
    u.finality_branch[3][7] ^= 0x01;
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::BadFinalityBranch),
        "a finality branch that does not reconstruct must be REFUSED"
    );

    // A wrong-depth execution branch.
    let mut u = update();
    u.finalized_header.execution_branch.truncate(3);
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::WrongBranchLength {
            got: 3,
            expected: 4
        }),
        "a wrong-depth execution branch must be REFUSED"
    );

    // A SUBSTITUTED EVM state root under an otherwise genuine, genuinely-signed update. This is
    // the payload the whole light client exists to deliver; it cannot be swapped.
    let mut u = update();
    u.finalized_header.execution.state_root[0] ^= 0x01;
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::BadExecutionBranch),
        "a substituted execution state root must be REFUSED"
    );
}

/// **THE STANDING NON-CONSTANCY CANARY, at the relayer's entry point.**
///
/// Two updates that differ in exactly ONE BIT — a single flipped bit of the aggregate G2
/// signature, which moves only the `bls` field of the projected wire — straddle the decision
/// boundary and MUST get different answers. A gate that has become always-accept, always-reject
/// or always-`"ERR"` collapses them and this fires. It is the assertion a gate that decides
/// nothing cannot satisfy, and every other assertion in this file shares its blind spot.
#[test]
fn one_field_apart_verdicts_must_differ() {
    let committee = committee_pubkeys();
    let accept = update();
    let mut reject = update();
    reject.sync_aggregate.sync_committee_signature[95] ^= 0x01;

    let (pa, _) = project_update(&accept, &committee, e2e::FORK_VERSION, gvr());
    let (pr, _) = project_update(&reject, &committee, e2e::FORK_VERSION, gvr());

    // The two wires differ in exactly one field, and it is the crypto carrier's result.
    assert_eq!(
        (
            pa.committee_len,
            pa.bits_len,
            pa.participant_count,
            pa.finality_len,
            pa.finality_ok,
            pa.exec_len,
            pa.exec_ok
        ),
        (
            pr.committee_len,
            pr.bits_len,
            pr.participant_count,
            pr.finality_len,
            pr.finality_ok,
            pr.exec_len,
            pr.exec_ok
        ),
        "the canary pair must differ in ONE field only"
    );
    assert!(pa.bls_ok && !pr.bls_ok);

    let raw_accept = verified_gate::raw(&pa);
    let raw_reject = verified_gate::raw(&pr);
    assert_eq!(raw_accept.as_deref(), Ok("1"));
    assert_eq!(raw_reject.as_deref(), Ok("0"));
    assert_ne!(
        raw_accept, raw_reject,
        "the archive returned the SAME verdict on both sides of the decision boundary — it is a \
         constant, not a gate"
    );

    // …and the entry point inherits the discrimination rather than flattening it.
    assert!(verdict(&accept, &committee).is_ok());
    assert!(verdict(&reject, &committee).is_err());
}

/// The `Ok`/`Err` this crate returns IS the archive's `"1"`/`"0"` on the projected wire — over
/// the whole mutation grid, not one sample. If the entry point ever stops consulting the gate
/// (or starts second-guessing it), a case diverges here.
#[test]
fn the_entry_point_verdict_is_the_archives_verdict() {
    let committee = committee_pubkeys();
    let mut short = committee.clone();
    short.pop();

    let mut subquorum = update();
    thin_participation_to(&mut subquorum.sync_aggregate, 341);
    let mut exact_quorum = update();
    thin_participation_to(&mut exact_quorum.sync_aggregate, 342);
    let mut zero = update();
    zero.sync_aggregate.sync_committee_bits = [0u8; SYNC_COMMITTEE_SIZE / 8];
    let mut forged_sig = update();
    forged_sig.sync_aggregate.sync_committee_signature[95] ^= 0x01;
    let mut short_fin = update();
    short_fin.finality_branch.truncate(5);
    let mut tampered_fin = update();
    tampered_fin.finality_branch[3][7] ^= 0x01;
    let mut short_exec = update();
    short_exec.finalized_header.execution_branch.truncate(3);
    let mut swapped_root = update();
    swapped_root.finalized_header.execution.state_root[0] ^= 0x01;

    let grid: Vec<(&str, LightClientUpdate, &[[u8; 48]])> = vec![
        ("genuine", update(), &committee),
        ("sub-quorum-341", subquorum, &committee),
        ("exact-quorum-342", exact_quorum, &committee),
        ("zero-participants", zero, &committee),
        ("forged-aggregate", forged_sig, &committee),
        ("committee-511", update(), &short),
        ("finality-depth-5", short_fin, &committee),
        ("finality-tampered", tampered_fin, &committee),
        ("exec-depth-3", short_exec, &committee),
        ("exec-root-swapped", swapped_root, &committee),
    ];

    for (name, u, c) in grid {
        let (p, _) = project_update(&u, c, e2e::FORK_VERSION, gvr());
        let archive = verified_gate::raw(&p).expect("the archive must answer");
        let entry = verdict(&u, c).is_ok();
        assert_eq!(
            entry,
            archive == "1",
            "case `{name}`: the entry point said {entry} but the archive said {archive:?} on \
             wire {}",
            p.wire()
        );
    }
}

/// The dominated-conjunct short-circuit is an optimization, not a decision: an update that fails
/// a cheap conjunct is refused for THAT reason, and the expensive `blst` pairing was never run
/// (a sub-quorum update carrying a garbage signature must not buy a 342-key aggregate verify).
#[test]
fn the_short_circuit_never_admits_and_never_pays_for_the_pairing() {
    let committee = committee_pubkeys();
    let mut u = update();
    thin_participation_to(&mut u.sync_aggregate, 300);
    u.sync_aggregate.sync_committee_signature = [0xC0u8; 96]; // not a valid G2 point

    let (p, bls_err) = project_update(&u, &committee, e2e::FORK_VERSION, gvr());
    assert_eq!(p.participant_count, 300);
    // The carrier was skipped: reported false with NO classification (a run carrier would have
    // produced `BadSignature` from the un-deserializable point).
    assert!(!p.bls_ok);
    assert_eq!(bls_err, None);
    // …and the refusal names the dominating conjunct, never the substituted one.
    assert_eq!(
        verdict(&u, &committee),
        Err(Error::InsufficientParticipation {
            participants: 300,
            required: 342,
        })
    );
}
