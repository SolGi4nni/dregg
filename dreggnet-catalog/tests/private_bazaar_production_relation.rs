//! The proven private-book relation on the PRODUCTION path.
//!
//! `prepare_private_clearing_zk` (and its durable-binding sibling) is the only
//! thing in this stack that runs real cryptography over a private order book:
//! a Plonky3 `HidingFriPcs` proof of the Lean-emitted `N=4,K=4` descriptor
//! (`metatheory/Market/DarkBazaarPrivateDescriptor.lean` →
//! `circuit/descriptors/by-name/dark-bazaar-private-n4k4.json`). Every caller of
//! it used to be test code, so the deployed worker polled a source that no
//! production caller could fill. These tests drive the production producer —
//! `PrivateBazaarLiveDeployment::settle_private_clearing_verified` and the
//! worker's `PrivateBazaarAuthenticatedReceiptSource::settle_and_capture` — and
//! pin its teeth.
//!
//! SCALE, stated plainly: the proved family is four committed order slots, four
//! price buckets, four-bit quantities. One slot is always the synthetic
//! top-price ask, so at most THREE real sealed bids and limits in `0..=3` are
//! inside the proof. A larger book is refused at ingress, before a single BID
//! turn touches the executor board. Nothing here clears an out-of-family book,
//! proved or unproved.
//!
//! Honest boundary, unchanged by this wiring: the proof hides the book from
//! proof consumers, not from the worker process building the witness. This is
//! Tier-1 operator-visible clearing, not Tier-0 no-single-viewer clearing.

#![cfg(feature = "private-bazaar-live")]

use dregg_app_framework::{
    CellId, MlDsaKeygenCoreRealInstall, MlDsaSignCoreRealInstall, MlDsaVerifyCoreInstall,
    install_verified_mldsa_keygen_core_real, install_verified_mldsa_sign_core_real,
    install_verified_mldsa_verify_core, symbol,
};
use dreggnet_catalog::private_bazaar_live::{
    PrivateBazaarLiveDeployment, PrivateBazaarLiveDeploymentError,
};
use dreggnet_catalog::{CatalogConfig, full_catalog_host_with_private_bazaar};
use dreggnet_market::private_bazaar_journey::{
    PrivateBazaarDeploymentPin, PrivateBazaarRaidPolicy,
};
use dreggnet_market::private_bazaar_live_host::PRIVATE_BAZAAR_RAID_KEY;
use dreggnet_market::private_clearing::{
    PROVEN_MAX_SEALED_BIDS, PROVEN_PRICE_BUCKETS, PrivateClearingError, PrivateSealedIngressBook,
};
use dreggnet_market::private_clearing_guild_allocation::{GuildMember, GuildReward, GuildRoster};
use dreggnet_offerings::{DreggIdentity, OfferingHost, Outcome, SessionConfig, SessionId};
use dungeon_on_dregg::progression::{PRIVATE_BAZAAR_XP_EVENT, PRIVATE_BAZAAR_XP_METHOD};
use std::path::Path;

const SELLER: &str = "production-private-seller";
const LOW_BIDDER: &str = "production-private-low-bidder";
const WINNER: &str = "production-private-winner";

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_owned())
}

/// Stand this process up the way a native node does.
///
/// Two independent verified cores are required, and NEITHER is waived here:
///
/// * the ML-DSA cores the executor signs every real turn with —
///   `DREGG_ALLOW_UNAUDITED_PQ` is asserted ABSENT, so a green run means the
///   audited cores answered rather than an escape hatch waiving them; and
/// * the verified Lean distributed gate, without which `dregg-intent`'s ring
///   settlement fails closed and no proof-authorized SETTLE can land.
///
/// RESIDUAL, and it is not this test's to fix: the three shipped binaries that
/// mount `PrivateBazaarLiveDeployment::from_env()` — `dreggnet-web-server`,
/// `dreggnet-telegram-bot`, `discord-bot` — install NO gate and do not even
/// depend on `dregg-exec-lean`. So the production private clearing still cannot
/// settle in a deployed process. This is the `drex_clear` regression class
/// (see `exec-lean/tests/drex_clear_gate.rs`) on a second, product-facing path,
/// and the fix is the same: the APP installs the gate at startup.
fn install_verified_test_pq_runtime() {
    dregg_exec_lean::register_distributed_gates();
    assert!(std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").is_none());
    assert!(matches!(
        install_verified_mldsa_keygen_core_real(),
        MlDsaKeygenCoreRealInstall::Installed | MlDsaKeygenCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_sign_core_real(),
        MlDsaSignCoreRealInstall::Installed | MlDsaSignCoreRealInstall::AlreadyInstalled
    ));
    assert!(matches!(
        install_verified_mldsa_verify_core(),
        MlDsaVerifyCoreInstall::Installed | MlDsaVerifyCoreInstall::AlreadyInstalled
    ));
}

fn deployment(root: &Path) -> PrivateBazaarLiveDeployment {
    install_verified_test_pq_runtime();
    let roster = GuildRoster::new(vec![
        GuildMember::new(actor(SELLER), CellId([0x41; 32])),
        GuildMember::new(actor(LOW_BIDDER), CellId([0x42; 32])),
        GuildMember::new(actor(WINNER), CellId([0x43; 32])),
    ])
    .expect("fixed production roster");
    let reward = GuildReward::new("raid-xp/production-relation/v1", 144).expect("fixed reward");
    let pin = PrivateBazaarDeploymentPin::new(
        [0x11; 32],
        roster.digest(),
        PrivateBazaarRaidPolicy::reward_commitment_for_configuration(&reward),
        PRIVATE_BAZAAR_XP_METHOD,
        symbol(PRIVATE_BAZAAR_XP_EVENT),
        [0x22; 32],
        [0x33; 32],
    )
    .expect("deployment pin");
    PrivateBazaarLiveDeployment::open(
        PrivateBazaarRaidPolicy::load(pin, roster, reward).expect("validated policy"),
        1,
        root,
    )
    .expect("deployment opens")
}

/// Mount the deployment and drive the ONE public action a frontend has: Enter,
/// which is a real executor LIST turn. No bid, limit, blind, witness, or proof
/// crosses this boundary.
fn enter_hosted_raid(deployment: &PrivateBazaarLiveDeployment, seed: u64) -> OfferingHost {
    let mut host = full_catalog_host_with_private_bazaar(&CatalogConfig::default(), deployment);
    let id = SessionId::new("production-private-bazaar");
    host.open_session(
        PRIVATE_BAZAAR_RAID_KEY,
        id.clone(),
        SessionConfig::with_seed(seed),
    )
    .expect("hosted session opens");
    let enter = host
        .actions(PRIVATE_BAZAAR_RAID_KEY, &id)
        .expect("mounted action set")[0]
        .clone();
    let outcome = host
        .advance(PRIVATE_BAZAAR_RAID_KEY, &id, enter, actor(SELLER))
        .expect("mounted route");
    assert!(matches!(outcome, Outcome::Landed { .. }), "{outcome:?}");
    host
}

/// Read-only look at the exact hosted market, through the deployment-owned
/// registry the worker uses. Returns `(receipts, onledger_phase, settled)`.
fn board_state(deployment: &PrivateBazaarLiveDeployment, seed: u64) -> (usize, Option<u64>, bool) {
    deployment
        .registry()
        .with_entered_typed(seed, |market, _| {
            Ok::<_, ()>((
                market.market().receipts_len(),
                market.market().onledger_phase(),
                market.is_settled(),
            ))
        })
        .expect("live registry reaches the hosted market")
        .expect("infallible read")
}

/// The exact production scan the deployed worker's source performs.
fn finalized(
    deployment: &PrivateBazaarLiveDeployment,
    seed_after: Option<u64>,
) -> Vec<(
    u64,
    dreggnet_market::private_clearing::PrivateClearingReceipt,
)> {
    deployment
        .registry()
        .finalized_private_receipts_for_worker(seed_after, 32)
        .expect("live registry scan")
        .0
}

fn in_family_book() -> PrivateSealedIngressBook {
    PrivateSealedIngressBook::new(vec![(actor(LOW_BIDDER), 2), (actor(WINNER), 3)])
        .expect("two bids with limits inside the proved four-bucket family")
}

/// THE PRODUCTION PATH RUNS THE REAL RELATION.
///
/// The worker mints a genuine `HidingFriPcs` proof of the Lean-emitted
/// descriptor over its own sealed book, that proof must verify against public
/// values derived independently of it, and only then does the executor SETTLE
/// land. The receipt is then visible to the exact live scan the deployed
/// worker's authenticated source performs.
#[test]
fn the_production_worker_mints_and_verifies_the_real_private_book_proof() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let deployment = deployment(temp.path());
    let seed = 0x9E_11_A2;
    let _host = enter_hosted_raid(&deployment, seed);

    // Before the producer runs there is nothing for the worker to consume: the
    // source is empty precisely because no proof has authorized anything.
    let (receipts_after_list, phase, settled) = board_state(&deployment, seed);
    assert_eq!(phase, Some(0), "an untouched commit phase");
    assert!(!settled);
    assert!(
        finalized(&deployment, None).is_empty(),
        "nothing may be finalized before a proof verifies"
    );

    let produced = deployment
        .settle_private_clearing_verified(seed, &in_family_book(), Some([7; 8]))
        .expect("the production worker clears an in-family book under a verified proof");
    assert_eq!((produced.price(), produced.volume()), (3, 1));

    // The clearing is the real first-price award, and it landed as a real
    // executor settlement on the same hosted market a frontend entered.
    let found = finalized(&deployment, None);
    assert_eq!(found.len(), 1);
    let (found_seed, receipt) = &found[0];
    assert_eq!(*found_seed, seed);
    assert_eq!((receipt.price(), receipt.volume()), (3, 1));
    assert_eq!(receipt.winner, actor(WINNER));
    assert_eq!(receipt.statement.rule, 1_430_520_836);
    assert_eq!(receipt.statement.order_root, produced.statement.order_root);
    assert_ne!(receipt.settlement_turn.turn_hash, [0; 32]);

    let (receipts_after_settle, phase, settled) = board_state(&deployment, seed);
    assert!(settled, "the executor SETTLE landed");
    assert_ne!(phase, Some(0));
    assert!(
        receipts_after_settle > receipts_after_list,
        "settlement is real executor turns, not a synthetic receipt"
    );

    // A second attempt on the same terminal market is refused; the proof
    // authorizes exactly one settlement.
    let replay = deployment.settle_private_clearing_verified(seed, &in_family_book(), Some([7; 8]));
    assert!(
        replay.is_err(),
        "a settled market cannot be cleared again: {replay:?}"
    );
}

/// CLOSED DEFECT — the durable spool now CARRIES a real settlement receipt.
///
/// What this test used to pin: the worker's append-only v2 spool refused any
/// receipt with a non-empty `emitted_events`, and a real Dark Bazaar SETTLE is
/// one atomic turn of `close_commit` + one `reveal_bid` per sealed bid +
/// `resolve`, every one of which emits an event. So the durable leg had only
/// ever been exercised against SYNTHETIC receipts built from
/// `TurnReceipt::default()`, and a production receipt was structurally
/// unspoolable — which meant the deployed worker would have FAULTED on the
/// first real book it ever settled.
///
/// v3 carries them, in a fixed-capacity region sized for exactly this shape
/// (`PROVEN_MAX_SEALED_BIDS` + 2 events, two felts each, with headroom); a
/// larger list is still refused BY NAME rather than truncated, because
/// `TurnReceipt::receipt_hash` binds the events and dropping one would forge a
/// different outcome under the same executor signature. The round-trip below is
/// what the old test demanded as the condition for its own replacement.
#[test]
fn the_durable_spool_carries_a_real_settlement_receipt() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let deployment = deployment(temp.path());
    let seed = 0x9E_11_A6;
    let _host = enter_hosted_raid(&deployment, seed);

    let mut source = deployment
        .private_authenticated_receipt_source()
        .expect("production authenticated source");
    let captured = source
        .settle_and_capture(seed, &in_family_book(), Some([17; 8]))
        .expect("the real clearing is produced AND reaches the durable spool");
    assert_eq!(captured.observed, 1);
    assert_eq!(
        captured.appended, 1,
        "a production receipt must be appended, not refused: {captured:?}"
    );

    let (_, _, settled) = board_state(&deployment, seed);
    assert!(settled, "the proof-authorized executor SETTLE landed");
    let found = finalized(&deployment, None);
    assert_eq!(found.len(), 1);
    assert_eq!((found[0].1.price(), found[0].1.volume()), (3, 1));
    assert!(
        !found[0].1.settlement_turn.emitted_events.is_empty(),
        "a real SETTLE emits events — if it stopped, this test no longer covers the \
         schema gap it was written for"
    );

    // Re-capture is idempotent rather than a second consequence.
    let again = source.capture_once().expect("a second capture is bounded");
    assert_eq!(again.observed, 1);
    assert_eq!(again.appended, 0);
}

/// A BOOK LARGER THAN THE PROVEN SHAPE IS REFUSED — NEVER SILENTLY ACCEPTED.
///
/// Both out-of-family directions are refused by name at ingress construction,
/// so the refusal happens before a bid, a blind, or a proof exists.
#[test]
fn a_book_outside_the_proven_family_is_refused_at_ingress() {
    assert_eq!(PROVEN_MAX_SEALED_BIDS, 3);
    assert_eq!(PROVEN_PRICE_BUCKETS, 4);

    // Four real bids need five committed slots once the synthetic ask is added;
    // the descriptor commits exactly four.
    let too_many = PrivateSealedIngressBook::new(vec![
        (actor("a"), 0),
        (actor("b"), 1),
        (actor("c"), 2),
        (actor("d"), 3),
    ]);
    assert!(
        matches!(too_many, Err(PrivateClearingError::TooManyBids(4))),
        "{too_many:?}"
    );

    // A limit of 4 is outside the proved four-bucket price family.
    let too_wide = PrivateSealedIngressBook::new(vec![(actor(WINNER), 4)]);
    assert!(
        matches!(
            too_wide,
            Err(PrivateClearingError::PriceOutsideFixedFamily(4))
        ),
        "{too_wide:?}"
    );

    let negative = PrivateSealedIngressBook::new(vec![(actor(WINNER), -1)]);
    assert!(
        matches!(
            negative,
            Err(PrivateClearingError::PriceOutsideFixedFamily(-1))
        ),
        "{negative:?}"
    );

    let empty = PrivateSealedIngressBook::new(Vec::new());
    assert!(
        matches!(empty, Err(PrivateClearingError::NoBids)),
        "{empty:?}"
    );

    // And the refusal is structural, not a runtime branch a caller can skip:
    // the production seam takes `PrivateSealedIngressBook` by type, and the only
    // constructor is the gate above. The board is therefore never mutated by an
    // out-of-family attempt.
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let deployment = deployment(temp.path());
    let seed = 0x9E_11_A3;
    let _host = enter_hosted_raid(&deployment, seed);
    let before = board_state(&deployment, seed);
    assert!(PrivateSealedIngressBook::new(vec![(actor(WINNER), 4)]).is_err());
    assert_eq!(
        board_state(&deployment, seed),
        before,
        "an out-of-family book cannot reach the executor board at all"
    );
}

/// A TAMPERED WITNESS IS REFUSED.
///
/// The witness is (four canonical orders, eight blind limbs). On the production
/// path both halves are pinned by the worker-private durable binding, so the two
/// reachable substitutions are: swap the private book under an existing
/// commitment, and corrupt the persisted blind. Both fail closed, and the book
/// substitution is caught while the executor board is still untouched.
#[test]
fn a_tampered_private_witness_cannot_authorize_a_settlement() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let authority = temp.path().to_path_buf();

    // One honest deployment binds a commitment to the exact book {2, 3}.
    let seed = 0x9E_11_A4;
    let first = deployment(&authority);
    let _host = enter_hosted_raid(&first, seed);
    let honest = first
        .settle_private_clearing_verified(seed, &in_family_book(), Some([11; 8]))
        .expect("the honest in-family book clears under a verified proof");
    assert_eq!((honest.price(), honest.volume()), (3, 1));
    drop(_host);
    drop(first);

    // Restart: the same authority directory, a freshly listed market with the
    // same deterministic seed, and therefore the same durable binding. A
    // SUBSTITUTED private book is refused — before any BID turn commits.
    let replayed = deployment(&authority);
    let _host = enter_hosted_raid(&replayed, seed);
    let untouched = board_state(&replayed, seed);
    let substituted =
        PrivateSealedIngressBook::new(vec![(actor(LOW_BIDDER), 1), (actor(WINNER), 3)])
            .expect("the substituted book is itself in-family; only its contents differ");
    let refused = replayed.settle_private_clearing_verified(seed, &substituted, None);
    assert!(
        matches!(
            refused,
            Err(PrivateBazaarLiveDeploymentError::PrivateClearing(
                PrivateClearingError::CommitmentBindingMismatch
            ))
        ),
        "a substituted private book must not be provable under the bound commitment: {refused:?}"
    );
    assert_eq!(
        board_state(&replayed, seed),
        untouched,
        "the substitution is refused on an untouched board, not after mutation"
    );

    // Replaying the EXACT bound book is still accepted, so the tooth above is
    // discriminating rather than a blanket restart refusal.
    let recovered = replayed
        .settle_private_clearing_verified(seed, &in_family_book(), None)
        .expect("the exact bound book re-proves after restart");
    assert_eq!(
        (recovered.price(), recovered.volume()),
        (honest.price(), honest.volume())
    );
    assert_eq!(recovered.statement.order_root, honest.statement.order_root);
}

/// A CORRUPTED PERSISTED BLIND IS REFUSED.
///
/// The eight blind limbs are the hiding half of the witness. Flipping a byte in
/// the durable record must not yield a usable commitment.
#[test]
fn a_corrupted_durable_commitment_blind_is_refused() {
    let temp = tempfile::tempdir().expect("scratch authority dir");
    let authority = temp.path().to_path_buf();
    let seed = 0x9E_11_A5;

    let first = deployment(&authority);
    let _host = enter_hosted_raid(&first, seed);
    first
        .settle_private_clearing_verified(seed, &in_family_book(), Some([13; 8]))
        .expect("honest bind + settle");
    drop(_host);
    drop(first);

    // Flip one byte inside the persisted blind limbs.
    let by_market = authority.join("private-commitments").join("by-market");
    let record = std::fs::read_dir(&by_market)
        .expect("durable market bindings exist")
        .map(|entry| entry.expect("dir entry").path())
        .find(|path| path.extension().is_some_and(|ext| ext == "binding"))
        .expect("one bound market");
    let mut bytes = std::fs::read(&record).expect("read binding");
    let blind_offset = 80;
    bytes[blind_offset] ^= 1;
    std::fs::write(&record, &bytes).expect("tamper the persisted blind");

    let replayed = deployment(&authority);
    let _host = enter_hosted_raid(&replayed, seed);
    let untouched = board_state(&replayed, seed);
    let refused = replayed.settle_private_clearing_verified(seed, &in_family_book(), None);
    assert!(
        matches!(
            refused,
            Err(PrivateBazaarLiveDeploymentError::PrivateClearing(
                PrivateClearingError::CorruptCommitmentBinding
            ))
        ),
        "a tampered blind record must not authorize a clearing: {refused:?}"
    );
    assert_eq!(
        board_state(&replayed, seed),
        untouched,
        "the corrupt record is caught on an untouched board"
    );
}
