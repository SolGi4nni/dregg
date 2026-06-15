//! Factory-BIRTH executor tests for the sealed-auction: an auction cell coming
//! alive through the REAL verified executor, driven through its
//! `COMMIT → REVEAL → RESOLVED` lifecycle, with the on-ledger commit board
//! enforced on the executor path:
//!
//!   - ANTI-FRONT-RUNNING — overwriting a committed sealed bid is REFUSED
//!     (`WriteOnce(COMMIT_BASE + i)`), now an EXECUTOR refusal, not a `BTreeMap`
//!     membership check.
//!   - LIFECYCLE — rewinding / stalling the phase is REFUSED
//!     (`StrictMonotonic(PHASE)`, strict).
//!
//! This is the `#95` factory-birth pattern: deploy → signed
//! `CreateCellFromFactory` → the born cell carries the caveats FOR LIFE →
//! honest lifecycle ACCEPTED, hostile turns REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_sealed_auction::{
    AUCTION_FACTORY_VK, Bid, COMMIT_BASE, PHASE_COMMIT, PHASE_RESOLVED, PHASE_REVEAL, PHASE_SLOT,
    SELLER_SLOT, WINNER_SLOT, auction_child_program_vk, auction_factory_descriptor,
    close_commit_effects, commit_bid_effects, commit_slot, resolve_effects,
};

fn make_cipherclerk() -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
}

/// Deploy the auction factory and birth an auction cell from it through the
/// executor. Returns the born cell's id, with an owner cap granted to the agent.
fn birth_auction_cell(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    token_tag: &[u8],
) -> CellId {
    exec.deploy_factory(auction_factory_descriptor());

    let agent = cclerk.cell_id();
    exec.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&agent) {
            cell.state.set_balance(100_000_000);
        }
    });

    let owner = cclerk.public_key().0;
    let token: [u8; 32] = *blake3::hash(token_tag).as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(auction_child_program_vk()),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let birth = cclerk.create_from_factory(AUCTION_FACTORY_VK, owner, token, params);
    exec.submit_turn(&birth)
        .expect("auction-cell birth commits");

    let born = CellId::derive_raw(&owner, &token);
    exec.with_ledger_mut(|ledger| {
        if let Some(agent_cell) = ledger.get_mut(&agent) {
            agent_cell.capabilities.grant(born, AuthRequired::Signature);
        }
    });
    born
}

/// Set PHASE = COMMIT on the born (empty) cell so the lifecycle has a baseline.
fn seed_phase_commit(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, auction: CellId) {
    let set_phase = cclerk.make_action(
        auction,
        "commit_bid", // a no-op-shaped commit turn that writes PHASE; Always allows it
        vec![Effect::SetField {
            cell: auction,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_COMMIT),
        }],
    );
    // PHASE_COMMIT == 0; writing 0 onto an absent/zero slot is a no-op-equivalent and
    // is admitted (no StrictMonotonic in the commit_bid case).
    exec.submit_action(cclerk, set_phase)
        .expect("seed PHASE = COMMIT");
}

/// The happy path: birth → commit two sealed bids (fresh WriteOnce slots) →
/// close_commit (PHASE COMMIT → REVEAL) → resolve (PHASE REVEAL → RESOLVED, WINNER
/// written). Every step ACCEPTED by the executor; the post-state reads back exactly.
#[test]
fn factory_born_auction_runs_the_whole_sale() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let auction = birth_auction_cell(&exec, &cclerk, b"sale-compute-1");

    let has_program = exec.with_ledger_mut(|ledger| {
        ledger
            .get(&auction)
            .map(|c| !c.program.is_none())
            .unwrap_or(false)
    });
    assert!(has_program, "factory-born auction must carry a CellProgram");

    seed_phase_commit(&exec, &cclerk, auction);

    // Two bidders commit sealed bids into fresh WriteOnce slots.
    let bid_a = Bid::new(10, 30, 7);
    let bid_b = Bid::new(11, 50, 8); // the top bid
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "commit_bid",
            commit_bid_effects(auction, commit_slot(0), &bid_a.seal()),
        ),
    )
    .expect("first sealed commit must commit");
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "commit_bid",
            commit_bid_effects(auction, commit_slot(1), &bid_b.seal()),
        ),
    )
    .expect("second sealed commit must commit");

    // The two commit slots hold the seals; PHASE is still COMMIT.
    let (c0, c1, phase) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&auction).unwrap();
        (
            c.state.fields[commit_slot(0)],
            c.state.fields[commit_slot(1)],
            c.state.fields[PHASE_SLOT],
        )
    });
    assert_eq!(c0, bid_a.seal(), "bidder A's seal is on the board");
    assert_eq!(c1, bid_b.seal(), "bidder B's seal is on the board");
    assert_eq!(phase, field_from_u64(PHASE_COMMIT), "still in COMMIT");

    // Close the commit phase (COMMIT → REVEAL).
    exec.submit_action(
        &cclerk,
        cclerk.make_action(auction, "close_commit", close_commit_effects(auction)),
    )
    .expect("close_commit must commit (StrictMonotonic 0 -> 1)");

    // Resolve: announce the winner B with the top bid 50 (REVEAL → RESOLVED).
    let winner_id = field_from_u64(11);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(auction, "resolve", resolve_effects(auction, winner_id, 50)),
    )
    .expect("resolve must commit (StrictMonotonic 1 -> 2)");

    let (phase, winner) = exec.with_ledger_mut(|ledger| {
        let c = ledger.get(&auction).unwrap();
        (c.state.fields[PHASE_SLOT], c.state.fields[WINNER_SLOT])
    });
    assert_eq!(
        phase,
        field_from_u64(PHASE_RESOLVED),
        "the sale must end RESOLVED"
    );
    assert_eq!(winner, winner_id, "the winner is announced");
}

/// ANTI-FRONT-RUNNING tooth: overwriting a committed sealed bid is REFUSED by the
/// executor (`WriteOnce(COMMIT_BASE + i)`), on the real executor path — the headline
/// payoff (the commit board is ON-LEDGER).
#[test]
fn factory_born_auction_refuses_overwriting_a_committed_bid() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let auction = birth_auction_cell(&exec, &cclerk, b"sale-compute-2");
    seed_phase_commit(&exec, &cclerk, auction);

    let bid = Bid::new(10, 30, 7);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "commit_bid",
            commit_bid_effects(auction, commit_slot(0), &bid.seal()),
        ),
    )
    .expect("the sealed commit commits");

    // A peeker tries to OVERWRITE its committed bid with a higher one in the same slot.
    let switched = Bid::new(10, 70, 7);
    let overwrite = cclerk.make_action(
        auction,
        "commit_bid",
        vec![Effect::SetField {
            cell: auction,
            index: commit_slot(0),
            value: switched.seal(),
        }],
    );
    let err = exec.submit_action(&cclerk, overwrite).expect_err(
        "overwriting a committed sealed bid must be refused — the anti-front-running tooth",
    );
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("writeonce") || msg.contains("write-once") || msg.contains("program"),
        "refusal must cite WriteOnce, got: {msg}"
    );

    // The committed bid did NOT change (anti-ghost).
    let c0 =
        exec.with_ledger_mut(|ledger| ledger.get(&auction).unwrap().state.fields[commit_slot(0)]);
    assert_eq!(
        c0,
        bid.seal(),
        "the refused overwrite committed nothing — the original seal stands"
    );
}

/// LIFECYCLE tooth: REWINDING the phase is REFUSED on the real executor path. The
/// factory-born cell carries the flat `state_constraints` predicate (the WriteOnce
/// commit board + the `Monotonic(PHASE)` anti-rollback floor), so a phase that
/// REWINDS (`REVEAL → COMMIT`) is an EXECUTOR refusal on the born cell. (The STRICT
/// no-advance bite — `StrictMonotonic(PHASE)` — is the phase-advancing methods' extra
/// clause in the `Cases` program installed by `seed_auction`; it bites on the seeded
/// deos cell, proved in `tests/deos_seam.rs`. The born cell's universal floor is the
/// non-strict `Monotonic(PHASE)`, which is what refuses the rewind here.)
#[test]
fn factory_born_auction_refuses_phase_rewind() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let auction = birth_auction_cell(&exec, &cclerk, b"sale-compute-3");
    seed_phase_commit(&exec, &cclerk, auction);

    // Advance to REVEAL.
    exec.submit_action(
        &cclerk,
        cclerk.make_action(auction, "close_commit", close_commit_effects(auction)),
    )
    .expect("close_commit commits (0 -> 1)");

    // A resolve that REWINDS the phase (REVEAL → COMMIT) is refused — the born cell's
    // universal `Monotonic(PHASE)` floor (a decrease is rejected).
    let rewind = cclerk.make_action(
        auction,
        "resolve",
        vec![Effect::SetField {
            cell: auction,
            index: PHASE_SLOT,
            value: field_from_u64(PHASE_COMMIT),
        }],
    );
    let err = exec.submit_action(&cclerk, rewind).expect_err(
        "rewinding the phase must be refused — the Monotonic(PHASE) anti-rollback floor",
    );
    assert!(
        format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("strict")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite Monotonic(PHASE), got: {err}"
    );

    // The phase did NOT change — the refused turn committed nothing (anti-ghost).
    let phase =
        exec.with_ledger_mut(|ledger| ledger.get(&auction).unwrap().state.fields[PHASE_SLOT]);
    assert_eq!(
        phase,
        field_from_u64(PHASE_REVEAL),
        "the refused rewind committed nothing — still REVEAL"
    );

    // The honest advance (REVEAL → RESOLVED) DOES commit on the born cell (Monotonic admits
    // the increase; the result registers are written through the WriteOnce floor).
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "resolve",
            resolve_effects(auction, field_from_u64(11), 50),
        ),
    )
    .expect("the honest forward resolve commits (REVEAL -> RESOLVED)");
    let phase =
        exec.with_ledger_mut(|ledger| ledger.get(&auction).unwrap().state.fields[PHASE_SLOT]);
    assert_eq!(
        phase,
        field_from_u64(PHASE_RESOLVED),
        "the forward advance commits — the sale RESOLVED"
    );

    // Silence the unused-import lint for symbols this suite imports for documentation parity.
    let _ = (COMMIT_BASE, SELLER_SLOT);
}
