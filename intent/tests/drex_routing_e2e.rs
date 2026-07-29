//! End-to-end integration test for the DrEX ring-of-locks routing capstone
//! (`dregg_intent::drex_routing`): a real lock → mirror-mint → DrEX-clear → clearing-root →
//! per-leg escrow-release flow, plus the fixture generator the Foundry e2e
//! (`chain/test/DrexRoutingE2E.t.sol`) replays.
//!
//! This lives as an INTEGRATION test (not an inline `#[cfg(test)]` unit module) on purpose: an
//! integration test links the lib compiled NORMALLY (its `#[cfg(test)]` units excluded), which is
//! the shape a consumer gets — and, since `e3f0e7b92`, the only shape in which the fail-closed
//! verified-settle path runs at all (the in-crate `#[cfg(test)]` sibling keeps the Rust fold
//! authoritative). Run it with `cargo test -p dregg-intent --test drex_routing_e2e`.
//!
//! (This header used to add "the `dregg-intent` lib-test build is independently broken —
//! `fulfillment.rs` test code references circuit symbols that drifted away". That has not been true
//! since `991c9d18d`: `cargo nextest run -p dregg-intent` compiles and runs 287 lib unit tests.)
//!
//! # ⚠ THIS BINARY MUST INSTALL THE VERIFIED EXECUTOR GATE
//!
//! Linking `dregg-intent` normally is exactly what makes `verified_settle`'s INVERTED, fail-closed
//! consumer path run: the Lean export `dregg_record_kernel_step` decides every ring leg, and with
//! no `IntentVerifiedGate` registered the ring is REFUSED (`FfiUnavailable`), not settled by an
//! unverified in-process Rust fold. `e3f0e7b92` (2026-07-24) made that the polarity and named
//! `tussle` as downstream fallout but missed this file, so `ring_of_locks_routes_end_to_end` and
//! `generate_fixture` went red on 2026-07-24 with
//!
//! ```text
//! VerifiedSettleRefused("verified-executor FFI unavailable: no verified gate registered")
//! ```
//!
//! — which `exec-lean/src/bin/drex_clear.rs` already calls out by name as the failure that "reads
//! like a matcher bug and sends a day of debugging at the matcher instead of at the missing gate".
//! It is: the ring was NEVER JUDGED, it was not rejected. Every test here that drives `route` calls
//! [`gate`] first, exactly as `node/src/lib.rs` and that bin do at startup.

use std::collections::{BTreeMap, BTreeSet};

use dregg_intent::drex_routing::{MirrorLeg, Party, RoutingError, route, verify_mirror_lock};
use dregg_intent::exchange::AssetId;
use dregg_intent::verified_settle::{
    VerifiedSettleError, funded_ledger, settle_ring_verified, touched_assets,
};

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorError, MirrorState, SolanaLockAttestation};
use dregg_cell::CellId;
use ed25519_dalek::SigningKey;
use serde::Serialize;

/// Install the REAL verified-Lean executor gate for this process (idempotent — the seam holds a
/// `OnceLock`). Without it `settle_ring_verified` refuses every non-empty ring fail-closed.
fn gate() {
    dregg_exec_lean::register_distributed_gates();
}

fn asset(byte: u8) -> AssetId {
    let mut a = [0u8; 32];
    a[0] = byte;
    a
}

const GOLD: u8 = 0x61;
const ART: u8 = 0x62;
const USD: u8 = 0x63;

fn hex32(b: &[u8; 32]) -> String {
    let mut s = String::from("0x");
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// Oracle key for a mirror (deterministic test key).
fn oracle(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// A mirror for `spl` under oracle `o`.
fn mirror(spl: u8, asset_id: u8, o: &SigningKey) -> MirrorState {
    MirrorState::new(MirrorConfig {
        spl_mint: [spl; 32],
        asset: asset(asset_id),
        oracle_keys: vec![EpochKey {
            from_epoch: 0,
            to_epoch: None,
            pubkey: o.verifying_key().to_bytes(),
        }],
        min_amount: 1,
        max_amount: 1_000_000,
        vault_account: [0x22u8; 32],
        lock_program: [0x07u8; 32],
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    })
}

/// A signed lock attestation: `amount` of `spl` to cell `recipient_byte`.
fn lock(
    spl: u8,
    amount: u64,
    recipient_byte: u8,
    lock_id: u8,
    o: &SigningKey,
) -> SolanaLockAttestation {
    SolanaLockAttestation::create(
        [lock_id; 32],
        [spl; 32],
        amount,
        CellId::from_bytes([recipient_byte; 32]),
        0,
        o,
    )
}

/// The canonical 3-party ring-of-locks: Alice offers GOLD wants ART; Bob offers ART wants USD;
/// Carol offers USD wants GOLD — a genuine 3-cycle no bilateral pair can clear.
fn three_party() -> (Vec<Party>, SigningKey, SigningKey, SigningKey) {
    let parties = vec![
        Party {
            name: "Alice".into(),
            id_byte: 1,
            evm_address: {
                let mut a = [0u8; 20];
                a[19] = 0xA1;
                a
            },
            offer_asset: asset(GOLD),
            offer_amount: 100,
            want_asset: asset(ART),
            want_min: 10,
        },
        Party {
            name: "Bob".into(),
            id_byte: 2,
            evm_address: {
                let mut a = [0u8; 20];
                a[19] = 0xB0;
                a
            },
            offer_asset: asset(ART),
            offer_amount: 50,
            want_asset: asset(USD),
            want_min: 20,
        },
        Party {
            name: "Carol".into(),
            id_byte: 3,
            evm_address: {
                let mut a = [0u8; 20];
                a[19] = 0xC0;
                a
            },
            offer_asset: asset(USD),
            offer_amount: 200,
            want_asset: asset(GOLD),
            want_min: 30,
        },
    ];
    (parties, oracle(11), oracle(12), oracle(13))
}

/// Verify each party's lock through the real mirror, returning the mirror legs. Also exercises the
/// REAL mint accounting (`mint_against_lock`) so the conservation invariant `live_supply ≤
/// currently_locked` is a genuine gate, not just arithmetic in `route`.
fn verify_all(
    parties: &[Party],
    o_a: &SigningKey,
    o_b: &SigningKey,
    o_c: &SigningKey,
) -> Vec<MirrorLeg> {
    let mut m_gold = mirror(0xAA, GOLD, o_a);
    let mut m_art = mirror(0xBB, ART, o_b);
    let mut m_usd = mirror(0xCC, USD, o_c);

    let a = lock(0xAA, 100, 1, 1, o_a);
    let b = lock(0xBB, 50, 2, 2, o_b);
    let c = lock(0xCC, 200, 3, 3, o_c);

    // The REAL mint accounting (raises currently_locked then draws the mint), so the invariant is
    // exercised as a live gate: mint refuses when it would push live_supply past currently_locked.
    let ma = m_gold
        .mint_against_lock(&a)
        .expect("Alice's GOLD lock mints");
    let mb = m_art.mint_against_lock(&b).expect("Bob's ART lock mints");
    let mc = m_usd.mint_against_lock(&c).expect("Carol's USD lock mints");
    assert_eq!(ma.amount, 100);
    assert_eq!(mb.amount, 50);
    assert_eq!(mc.amount, 200);
    assert!(m_gold.invariant_holds() && m_art.invariant_holds() && m_usd.invariant_holds());

    vec![
        verify_mirror_lock(&m_gold, &parties[0], &a).expect("Alice verifies"),
        verify_mirror_lock(&m_art, &parties[1], &b).expect("Bob verifies"),
        verify_mirror_lock(&m_usd, &parties[2], &c).expect("Carol verifies"),
    ]
}

/// POLE 1 (the ring CLEARS): an honest ring of locks settles through the REAL verified Lean
/// executor, conserves per asset, and — the part a `ring_conserves: true` bool cannot show —
/// actually MOVES value between the three parties, each of them ending in a DIFFERENT asset than
/// it started in.
///
/// Every assertion below is over the verified pre/post BALANCES, not over a rendered flag. A
/// conserving no-op ring (nobody's balance changes) satisfies `ring_conserves` trivially and would
/// pass the old version of this test; it fails `each party's offered column is DRAINED` and `each
/// party's wanted column is CREDITED` here.
#[test]
fn ring_of_locks_routes_end_to_end() {
    gate();
    let (parties, oa, ob, oc) = three_party();
    let mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    let fx = route(&parties, &mirror_legs, 0).expect("the ring-of-locks routes");

    // The whole flow held: mirror conserved, ring cleared + conserved, one release per leg.
    assert!(fx.mirror_conserves, "mirror must conserve");
    assert!(
        fx.ring_conserves,
        "ring must conserve on the verified executor"
    );
    assert_eq!(fx.legs.len(), 3, "a 3-party ring has 3 release legs");

    // ── A RING OF LOCKS IS A CYCLE OF SAME-ASSET LEGS ────────────────────────────────────────
    // Each leg re-assigns ONE party's own lock, in that party's OWN asset, to whoever the cycle
    // matched to receive it. No leg is cross-asset — the cross-asset effect is the CYCLE. If the
    // solver ever emitted a leg whose asset is not the sender's offered asset, that leg would be
    // the unbacked cross-asset teleport `b1a370194` closed in the executor, and this fails.
    let offer_of: BTreeMap<u8, AssetId> =
        parties.iter().map(|p| (p.id_byte, p.offer_asset)).collect();
    assert_eq!(fx.verified_legs.len(), 3, "3 verified single-column legs");
    for (i, leg) in fx.verified_legs.iter().enumerate() {
        assert_eq!(
            leg.asset, offer_of[&leg.from],
            "leg {i} ({}→{}) must move the SENDER's own locked asset — a cross-asset leg would be \
             the teleport the executor refuses",
            leg.from, leg.to
        );
        assert_ne!(leg.from, leg.to, "leg {i} must not be a self-transfer");
        assert!(leg.amount > 0, "leg {i} must move a positive amount");
    }
    // The three legs form a closed cycle: every party sends exactly once and receives exactly once.
    let senders: BTreeSet<u8> = fx.verified_legs.iter().map(|l| l.from).collect();
    let receivers: BTreeSet<u8> = fx.verified_legs.iter().map(|l| l.to).collect();
    assert_eq!(
        senders,
        BTreeSet::from([1u8, 2, 3]),
        "each party sends once"
    );
    assert_eq!(
        receivers,
        BTreeSet::from([1u8, 2, 3]),
        "each party receives once"
    );

    // ── CONSERVATION, ASSERTED ON THE BALANCES (not on `fx.ring_conserves`) ──────────────────
    let assets = touched_assets(&fx.verified_legs);
    assert_eq!(assets.len(), 3, "the ring touches GOLD, ART and USD");
    for a in &assets {
        let before = fx.pre_ledger.total_asset(a);
        let after = fx.post_ledger.total_asset(a);
        assert_eq!(
            before, after,
            "asset {:02x} must be conserved across the verified settle ({before} -> {after})",
            a[0]
        );
        assert!(
            before > 0,
            "asset {:02x} must carry real supply — a ring over empty columns conserves vacuously",
            a[0]
        );
    }

    // ── ANTI-VACUITY: VALUE ACTUALLY CROSSED PARTIES, INTO A DIFFERENT ASSET ─────────────────
    // Settled amounts are the RECEIVER's declared minimum capped by the sender's offer
    // (`solver.rs`): Alice→Carol 30 GOLD, Carol→Bob 20 USD, Bob→Alice 10 ART.
    let expect: [(u8, u8, u8, i128); 3] = [
        (1, 3, GOLD, 30), // Alice's locked GOLD is re-assigned to Carol, who wanted GOLD
        (3, 2, USD, 20),  // Carol's locked USD to Bob
        (2, 1, ART, 10),  // Bob's locked ART to Alice
    ];
    let mut moved: i128 = 0;
    for (from, to, a, amount) in expect {
        let a = asset(a);
        assert_eq!(
            fx.pre_ledger.get(from, &a),
            amount,
            "party {from} must start holding its own {amount} of asset {:02x}",
            a[0]
        );
        assert_eq!(
            fx.post_ledger.get(from, &a),
            0,
            "party {from}'s offered column must be DRAINED by the ring (it gave its lock away)"
        );
        assert_eq!(
            fx.pre_ledger.get(to, &a),
            0,
            "party {to} must start with NONE of asset {:02x} — it is buying it",
            a[0]
        );
        assert_eq!(
            fx.post_ledger.get(to, &a),
            amount,
            "party {to} must END holding the {amount} of asset {:02x} the ring matched to it",
            a[0]
        );
        moved += amount;
    }
    assert_eq!(moved, 60, "the ring moved 30 GOLD + 20 USD + 10 ART");
    // And each party genuinely swapped: it holds NONE of what it offered and SOME of what it wanted.
    for p in &parties {
        assert_eq!(
            fx.post_ledger.get(p.id_byte, &p.offer_asset),
            0,
            "{} must end holding none of the asset it offered",
            p.name
        );
        assert!(
            fx.post_ledger.get(p.id_byte, &p.want_asset) >= p.want_min as i128,
            "{} must end holding at least its declared minimum of the asset it wanted",
            p.name
        );
        assert_ne!(
            p.offer_asset, p.want_asset,
            "{} must be swapping ACROSS assets — otherwise the cycle proves nothing",
            p.name
        );
    }

    // The clearing root is non-zero and stable across a re-run (deterministic).
    assert_ne!(fx.clearing_root, hex32(&[0u8; 32]));
    let fx2 = route(&parties, &mirror_legs, 0).expect("re-route");
    assert_eq!(
        fx.clearing_root, fx2.clearing_root,
        "clearing root is deterministic"
    );

    // Every leg names a distinct escrow id, a real depositor, and a real recipient (the counterparty).
    let ids: BTreeSet<&String> = fx.legs.iter().map(|l| &l.escrow_id).collect();
    assert_eq!(ids.len(), 3, "escrow ids are distinct per leg");
    for l in &fx.legs {
        assert!(l.amount > 0);
        assert!(l.depositor.starts_with("0x") && l.depositor.len() == 42);
        assert!(l.recipient.starts_with("0x") && l.recipient.len() == 42);
        assert_ne!(
            l.depositor, l.recipient,
            "a leg releases to the COUNTERPARTY, not the depositor"
        );
    }
}

/// TOOTH (lock→mirror boundary): a FORGED lock attestation is rejected by the mirror, so it never
/// mints and never enters the book. The routing flow's first gate bites.
#[test]
fn forged_lock_is_rejected_before_it_can_route() {
    let (parties, oa, _, _) = three_party();
    let m_gold = mirror(0xAA, GOLD, &oa);
    // Sign Alice's lock with the WRONG key.
    let forger = oracle(0xEE);
    let forged = lock(0xAA, 100, 1, 1, &forger);
    let res = verify_mirror_lock(&m_gold, &parties[0], &forged);
    assert!(
        matches!(
            res,
            Err(RoutingError::MirrorRejected {
                err: MirrorError::AttestationInvalid,
                ..
            })
        ),
        "a forged lock must be refused at the mirror; got {res:?}"
    );
}

/// TOOTH (lock→book binding, driving `route`): with NO verified locks, `route` cannot build a book
/// from self-asserted offers — every party is unbacked, so routing refuses at the binding gate.
/// This is the falsifier the old `x <= x` gate could never fail (empty `mirror_legs` made
/// conservation VACUOUSLY true and the book was built entirely from `p.offer_amount`).
#[test]
fn no_lock_no_book_entry() {
    let (parties, _, _, _) = three_party();
    let res = route(&parties, &[], 0);
    assert!(
        matches!(res, Err(RoutingError::MissingLock { .. })),
        "a party with no verified lock must not enter the book; got {res:?}"
    );
}

/// TOOTH (lock→book binding): a party that LOCKS 100 but claims 1_000_000 into the book is refused
/// — the offer exceeds the verified lock. Under the old `x <= x` gate this routed (the book took
/// `offer_amount` at face value and conservation compared the lock against itself).
///
/// MUTATION CANARY ANCHOR: reverting the `mirror_legs -> parties` bind in `route` (back to
/// populating `locked`/`minted` from the same `leg.amount`) makes THIS test go RED again.
#[test]
fn offer_exceeding_the_verified_lock_is_refused() {
    let (mut parties, oa, ob, oc) = three_party();
    // Alice's REAL verified lock is 100 GOLD (see `verify_all`); inflate only her BOOK offer.
    let mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    parties[0].offer_amount = 1_000_000;
    let res = route(&parties, &mirror_legs, 0);
    assert!(
        matches!(
            res,
            Err(RoutingError::UnbackedOffer {
                backed: 100,
                offered: 1_000_000,
                ..
            })
        ),
        "an offer larger than the verified lock must be refused; got {res:?}"
    );
}

/// TOOTH (lock→book binding): a FORGED lock never mints, so it never backs a book offer — and now
/// this is proven by DRIVING `route` (not just `verify_mirror_lock`). Alice's forged lock fails
/// mirror verification, so she has NO `MirrorLeg`; `route` over the remaining legs refuses her offer
/// with `MissingLock`. The routing flow's binding gate bites.
#[test]
fn a_forged_lock_never_enters_the_book() {
    let (parties, oa, ob, oc) = three_party();
    // Everyone locks honestly EXCEPT Alice, whose lock is forged (wrong oracle key) and so is
    // rejected at the mirror — she gets no leg.
    let all_legs = verify_all(&parties, &oa, &ob, &oc);
    let forger = oracle(0xEE);
    let m_gold = mirror(0xAA, GOLD, &oa);
    let forged = lock(0xAA, 100, 1, 1, &forger);
    assert!(
        verify_mirror_lock(&m_gold, &parties[0], &forged).is_err(),
        "the forged lock must fail mirror verification"
    );
    // The book still lists Alice, but only Bob's and Carol's legs verified.
    let backed_legs: Vec<MirrorLeg> = all_legs.into_iter().skip(1).collect();
    let res = route(&parties, &backed_legs, 0);
    assert!(
        matches!(res, Err(RoutingError::MissingLock { .. })),
        "a party whose lock never minted must not enter the book; got {res:?}"
    );
}

/// TOOTH (lock→book binding): a verified lock for the WRONG asset does not back the offer. Alice's
/// lock verifies for GOLD, but if the book claims she offers ART, the lock→offer asset mismatch is
/// refused — a lock in one asset cannot silently back an offer in another.
#[test]
fn a_lock_for_the_wrong_asset_does_not_back_the_offer() {
    let (mut parties, oa, ob, oc) = three_party();
    let mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    // Alice's verified leg is GOLD; rewrite her BOOK offer asset to ART (her lock does not back it).
    parties[0].offer_asset = asset(ART);
    let res = route(&parties, &mirror_legs, 0);
    assert!(
        matches!(res, Err(RoutingError::LockAssetMismatch { .. })),
        "a lock in the wrong asset must not back the offer; got {res:?}"
    );
}

/// TOOTH (lock→book binding): a verified lock for a party NOT in the book is an orphan mint — it is
/// refused, not silently ignored (which would let a mint float free of any offer).
#[test]
fn an_orphan_lock_is_refused() {
    let (parties, oa, ob, oc) = three_party();
    let mut mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    // Append a leg whose party byte (0x77) matches no party in the book.
    mirror_legs.push(MirrorLeg {
        party_byte: 0x77,
        asset: asset(GOLD),
        amount: 100,
    });
    let res = route(&parties, &mirror_legs, 0);
    assert!(
        matches!(res, Err(RoutingError::OrphanLock { party_byte: 0x77 })),
        "a lock for no party in the book must be refused; got {res:?}"
    );
}

/// POLE 2 (the ring is REFUSED when it does not balance): take the EXACT legs the honest ring
/// settled, fund the ledger from those honest legs, then inflate the LAST leg so the ring tries to
/// re-assign more than was ever locked — Bob releases 11 ART when only 10 was minted against his
/// lock. The verified executor refuses that leg by variant (`LegRejected`), and because a ring is
/// all-or-none (`settleRing_atomic`) the WHOLE ring aborts: the two legs that already committed
/// leave no trace in the caller's ledger.
///
/// The inflated leg is deliberately LAST, so this cannot pass by refusing before anything moved —
/// legs 0 and 1 commit inside the fold and must be rolled back.
///
/// This drives the SAME registered Lean gate as pole 1, so an accept and a refusal are decided by
/// the same authority.
#[test]
fn a_ring_that_does_not_balance_is_refused_and_nothing_moves() {
    gate();
    let (parties, oa, ob, oc) = three_party();
    let mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    let fx = route(&parties, &mirror_legs, 0).expect("the honest ring routes");

    // Fund from the HONEST legs (the locks that actually minted), then over-claim on the last leg.
    let honest = fx.verified_legs.clone();
    let k0 = funded_ledger(&honest);
    let mut inflated = honest.clone();
    let last = inflated.len() - 1;
    inflated[last].amount += 1;

    // The honest ring over this same ledger settles — so the refusal below is about the inflation,
    // not about a ledger that could never settle anything.
    let post_before =
        settle_ring_verified(&k0, &honest).expect("the honest ring settles on this ledger");

    let res = settle_ring_verified(&k0, &inflated);
    match &res {
        Err(VerifiedSettleError::LegRejected { index, leg }) => {
            assert_eq!(*index, last, "the REFUSED leg must be the inflated one");
            assert_eq!(
                leg.amount,
                honest[last].amount + 1,
                "the refusal must name the over-claimed amount"
            );
            assert_eq!(leg.asset, honest[last].asset);
        }
        other => panic!(
            "a ring releasing more than was locked must be refused by LegRejected; got {other:?}"
        ),
    }

    // ATOMICITY, with content: legs 0 and 1 DID commit inside the aborted fold. Re-settling the
    // honest ring must reproduce the identical post-ledger — if the aborted attempt had left any
    // partial state behind (in the ledger or through the gate), these would diverge.
    let post_after = settle_ring_verified(&k0, &honest)
        .expect("the honest ring must still settle after an aborted one");
    assert_eq!(
        post_before, post_after,
        "an aborted ring must leave NO trace: the honest settle is unchanged by it"
    );
    for a in touched_assets(&honest) {
        assert_eq!(
            post_after.total_asset(&a),
            k0.total_asset(&a),
            "asset {:02x} must still conserve after the aborted ring",
            a[0]
        );
    }
}

/// A book with no cross-chain cycle does not clear — surfaced honestly, no fixture emitted.
#[test]
fn non_clearing_book_yields_no_ring() {
    let parties = vec![
        Party {
            name: "X".into(),
            id_byte: 1,
            evm_address: [0x11; 20],
            offer_asset: asset(GOLD),
            offer_amount: 100,
            want_asset: asset(ART),
            want_min: 10,
        },
        Party {
            name: "Y".into(),
            id_byte: 2,
            evm_address: [0x22; 20],
            offer_asset: asset(USD),
            offer_amount: 100,
            want_asset: asset(GOLD),
            want_min: 10,
        },
    ];
    let legs = vec![
        MirrorLeg {
            party_byte: 1,
            asset: asset(GOLD),
            amount: 100,
        },
        MirrorLeg {
            party_byte: 2,
            asset: asset(USD),
            amount: 100,
        },
    ];
    assert!(matches!(
        route(&parties, &legs, 0),
        Err(RoutingError::NoClearingRing)
    ));
}

/// Foundry-friendly wire shape: PARALLEL arrays (`vm.parseJson*Array` reads each directly).
#[derive(Serialize)]
struct FixtureWire {
    clearing_root: String,
    batch_id: u64,
    escrow_ids: Vec<String>,
    depositors: Vec<String>,
    recipients: Vec<String>,
    amounts: Vec<u64>,
    assets: Vec<String>,
    mirror_conserves: bool,
    ring_conserves: bool,
    provenance: String,
}

/// Emit the committed fixture `chain/test/fixtures/drex_routing.json` that
/// `chain/test/DrexRoutingE2E.t.sol` replays. Always prints the JSON between markers (so it can be
/// captured from a remote pbuild run); `DREX_WRITE_FIXTURE=1` additionally writes it to the local
/// tree (for a LOCAL cargo run).
#[test]
fn generate_fixture() {
    gate();
    let (parties, oa, ob, oc) = three_party();
    let mirror_legs = verify_all(&parties, &oa, &ob, &oc);
    let fx = route(&parties, &mirror_legs, 0).expect("routes");
    let wire = FixtureWire {
        clearing_root: fx.clearing_root.clone(),
        batch_id: fx.batch_id,
        escrow_ids: fx.legs.iter().map(|l| l.escrow_id.clone()).collect(),
        depositors: fx.legs.iter().map(|l| l.depositor.clone()).collect(),
        recipients: fx.legs.iter().map(|l| l.recipient.clone()).collect(),
        amounts: fx.legs.iter().map(|l| l.amount).collect(),
        assets: fx.legs.iter().map(|l| l.asset.clone()).collect(),
        mirror_conserves: fx.mirror_conserves,
        ring_conserves: fx.ring_conserves,
        provenance: fx.provenance.clone(),
    };
    let json = serde_json::to_string_pretty(&wire).expect("serialize");

    eprintln!("===DREX_FIXTURE_BEGIN===\n{json}\n===DREX_FIXTURE_END===");
    if std::env::var("DREX_WRITE_FIXTURE").as_deref() == Ok("1") {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../chain/test/fixtures/drex_routing.json"
        );
        std::fs::write(path, format!("{json}\n")).expect("write fixture");
        eprintln!("wrote {path}");
    }
    assert!(fx.legs.len() == 3 && fx.mirror_conserves && fx.ring_conserves);
}
