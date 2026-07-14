//! End-to-end integration test for the DrEX ring-of-locks routing capstone
//! (`dregg_intent::drex_routing`): a real lock → mirror-mint → DrEX-clear → clearing-root →
//! per-leg escrow-release flow, plus the fixture generator the Foundry e2e
//! (`chain/test/DrexRoutingE2E.t.sol`) replays.
//!
//! This lives as an INTEGRATION test (not an inline `#[cfg(test)]` unit module) on purpose: the
//! `dregg-intent` lib-test build is independently broken (`fulfillment.rs` test code references
//! circuit symbols that drifted away — `prove_predicate`/`stark`/`verify_authorization_dsl`), so
//! the whole `cargo test -p dregg-intent` unit build fails to compile. An integration test links
//! the lib compiled NORMALLY (its `#[cfg(test)]` units excluded), so this runs cleanly via
//! `cargo test -p dregg-intent --test drex_routing_e2e`.

use std::collections::BTreeSet;

use dregg_intent::drex_routing::{MirrorLeg, Party, RoutingError, route, verify_mirror_lock};
use dregg_intent::exchange::AssetId;

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorError, MirrorState, SolanaLockAttestation};
use dregg_cell::CellId;
use ed25519_dalek::SigningKey;
use serde::Serialize;

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

#[test]
fn ring_of_locks_routes_end_to_end() {
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
