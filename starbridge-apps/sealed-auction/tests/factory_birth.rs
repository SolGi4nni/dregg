//! Factory-BIRTH executor tests for the sealed-auction: an auction cell coming
//! alive through the REAL verified executor, driven through its
//! `COMMIT → REVEAL → RESOLVED` lifecycle, with the on-ledger commit board
//! enforced on the executor path:
//!
//!   - ANTI-FRONT-RUNNING — overwriting a committed sealed bid is REFUSED
//!     (`WriteOnce(COMMIT_BASE + i)`), now an EXECUTOR refusal, not a `BTreeMap`
//!     membership check.
//!   - LIFECYCLE — rewinding/skipping the phase is REFUSED by the exact
//!     factory-installed `AllowedTransitions(PHASE)` table.
//!   - PROGRAM IDENTITY — the born cell's installed program, advertised VK, and
//!     every subsequent Bazaar-shaped transition remain one exact identity.
//!
//! This is the `#95` factory-birth pattern: deploy → signed
//! `CreateCellFromFactory` → the born cell carries the caveats FOR LIFE →
//! honest lifecycle ACCEPTED, hostile turns REFUSED.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, Effect, EmbeddedExecutor,
    canonical_program_vk, field_from_u64,
};
use dregg_cell::FactoryCreationParams;
use starbridge_sealed_auction::{
    AUCTION_FACTORY_VK, Bid, COMMIT_BASE, PHASE_COMMIT, PHASE_RESOLVED, PHASE_REVEAL, PHASE_SLOT,
    SELLER_SLOT, WINNER_SLOT, auction_child_program_vk, auction_factory_cell_program,
    auction_factory_descriptor, close_commit_effects, commit_bid_effects, commit_slot,
    resolve_effects, reveal_bid_effects,
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

/// Factory birth must install exactly the program whose content address it
/// advertises. Checking only `!program.is_none()` would miss the Cases-vs-Predicate
/// substitution this regression guards.
fn assert_factory_program_identity(exec: &EmbeddedExecutor, auction: CellId) {
    let advertised = auction_factory_cell_program();
    let advertised_vk = auction_child_program_vk();
    assert_eq!(canonical_program_vk(&advertised), advertised_vk);
    exec.with_ledger_mut(|ledger| {
        let cell = ledger.get(&auction).expect("factory-born auction exists");
        assert_eq!(
            cell.program, advertised,
            "born auction must execute the exact advertised CellProgram"
        );
        assert_eq!(
            cell.verification_key.as_ref().map(|vk| vk.hash),
            Some(advertised_vk),
            "born auction VK must identify its actually installed program"
        );
    });
}

#[test]
fn factory_refuses_program_bytes_only_or_other_vk() {
    let cclerk = make_cipherclerk();
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    exec.deploy_factory(auction_factory_descriptor());
    exec.with_ledger_mut(|ledger| {
        ledger
            .get_mut(&cclerk.cell_id())
            .expect("agent cell")
            .state
            .set_balance(100_000_000);
    });

    let program = auction_factory_cell_program();
    let legacy_program_bytes_vk = dregg_cell::canonical_program_vk(&program);
    assert_ne!(
        legacy_program_bytes_vk,
        auction_child_program_vk(),
        "the old v1 program-bytes hash is not the layered v2 recipe"
    );
    let owner = cclerk.public_key().0;
    let token = *blake3::hash(b"sale-wrong-program-vk").as_bytes();
    let params = FactoryCreationParams {
        mode: CellMode::Sovereign,
        program_vk: Some(legacy_program_bytes_vk),
        initial_fields: vec![],
        initial_caps: vec![],
        owner_pubkey: owner,
    };
    let turn = cclerk.create_from_factory(AUCTION_FACTORY_VK, owner, token, params);
    let err = exec
        .submit_turn(&turn)
        .expect_err("factory must reject a VK that does not match the full v2 recipe");
    assert!(
        format!("{err}").to_lowercase().contains("program vk")
            || format!("{err}").to_lowercase().contains("mismatch"),
        "wrong-VK refusal must name the mismatch: {err}"
    );
    let born = CellId::derive_raw(&owner, &token);
    assert!(
        exec.with_ledger_mut(|ledger| ledger.get(&born).is_none()),
        "a refused mismatched-VK birth must not leave a ghost cell"
    );
}

/// Set PHASE = COMMIT on the born (empty) cell so the lifecycle has a baseline.
fn seed_phase_commit(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, auction: CellId) {
    let set_phase = cclerk.make_action(
        auction,
        "commit_bid", // a no-op-shaped commit turn that writes PHASE; Always allows it
        vec![Effect::SetField {
            cell: auction,
            index: PHASE_SLOT as u64,
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

    assert_factory_program_identity(&exec, auction);

    seed_phase_commit(&exec, &cclerk, auction);
    assert_factory_program_identity(&exec, auction);

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
    assert_factory_program_identity(&exec, auction);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "commit_bid",
            commit_bid_effects(auction, commit_slot(1), &bid_b.seal()),
        ),
    )
    .expect("second sealed commit must commit");
    assert_factory_program_identity(&exec, auction);

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
    .expect("close_commit must commit (allowed adjacent phase 0 -> 1)");
    assert_factory_program_identity(&exec, auction);

    // A Bazaar reveal is event-only, but still touches the target and therefore
    // runs the same installed program against the REVEAL -> REVEAL self-pair.
    exec.submit_action(
        &cclerk,
        cclerk.make_action(
            auction,
            "reveal_bid",
            reveal_bid_effects(auction, field_from_u64(11), 50),
        ),
    )
    .expect("reveal_bid must commit under the advertised program");
    assert_factory_program_identity(&exec, auction);

    // Resolve: announce the winner B with the top bid 50 (REVEAL → RESOLVED).
    let winner_id = field_from_u64(11);
    exec.submit_action(
        &cclerk,
        cclerk.make_action(auction, "resolve", resolve_effects(auction, winner_id, 50)),
    )
    .expect("resolve must commit (allowed adjacent phase 1 -> 2)");
    assert_factory_program_identity(&exec, auction);

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
            index: commit_slot(0) as u64,
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
/// factory-born cell carries the exact advertised flat predicate (the WriteOnce
/// commit board + the explicit adjacent `AllowedTransitions(PHASE)` table), so a
/// phase that REWINDS (`REVEAL → COMMIT`) is an EXECUTOR refusal on the born cell.
/// The method-scoped strict no-advance tooth is part of that same factory-installed
/// `Cases` program through `ChildVkStrategy::FixedProgram`.
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
    // universal `AllowedTransitions(PHASE)` floor (the pair is absent).
    let rewind = cclerk.make_action(
        auction,
        "resolve",
        vec![Effect::SetField {
            cell: auction,
            index: PHASE_SLOT as u64,
            value: field_from_u64(PHASE_COMMIT),
        }],
    );
    let err = exec.submit_action(&cclerk, rewind).expect_err(
        "rewinding the phase must be refused — pair absent from AllowedTransitions(PHASE)",
    );
    assert!(
        format!("{err}").to_lowercase().contains("allowed")
            || format!("{err}").to_lowercase().contains("transition")
            || format!("{err}").to_lowercase().contains("monotonic")
            || format!("{err}").to_lowercase().contains("strict")
            || format!("{err}").to_lowercase().contains("program"),
        "refusal must cite the phase program, got: {err}"
    );

    // The phase did NOT change — the refused turn committed nothing (anti-ghost).
    let phase =
        exec.with_ledger_mut(|ledger| ledger.get(&auction).unwrap().state.fields[PHASE_SLOT]);
    assert_eq!(
        phase,
        field_from_u64(PHASE_REVEAL),
        "the refused rewind committed nothing — still REVEAL"
    );

    // The honest adjacent advance (REVEAL → RESOLVED) DOES commit; the result
    // registers are written through the WriteOnce floor.
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
