//! THE PURE-JS SEALED-BID AUCTION, PROVEN BY RUNNING: a single JavaScript program — run in
//! the NATIVE runtime (pure-Rust `boa`, NO servo, NO SpiderMonkey/mozjs) — drives a whole
//! MULTI-PARTY, COMMIT-REVEAL sealed-bid auction across FIVE cells: three competing bidders
//! (`alice`, `bob`, `carol`), the awarding `seller`, and the `auction` coordinator that holds
//! the sealed board + the lifecycle phase. This is the THIRD and hardest pure-JS app (after
//! the single-cell kvstore and the two-party escrow): several parties COMPETE for one award
//! by sealing hidden bids, then OPENING them under a runtime-enforced binding, after which the
//! highest committed-and-revealed bid wins and SETTLES.
//!
//! It mirrors the real `starbridge-apps/sealed-auction` shape (the executable surface of the
//! Lean `Dregg2/Intent/SealedAuction.lean`), and the SAME guarantees that development proves
//! are exercised here AS PURE JS:
//!
//!   | Lean keystone                | proven by running here                                |
//!   |------------------------------|-------------------------------------------------------|
//!   | `reveal_binds_committed`     | (b) a switched value's reveal is refused IN-BAND.     |
//!   | `uncommitted_cannot_open`    | (c) a non-committed party cannot reveal.              |
//!   | anti-front-running (WriteOnce)| (d) a committed bid cannot be overwritten.            |
//!   | `reveal_requires_reveal_phase`| (e) a reveal before the commit phase closes is refused.|
//!   | `winner_was_committed`       | (a) the winner's value came from a bound reveal.      |
//!   | `settle_conserves`           | (a) value is conserved (only per-turn fees burned).   |
//!   | settlement confinement       | (f) the payout cannot drain to an unheld party.       |
//!
//! THE POWER-UP THIS APP NEEDED (added to the runtime host API): a **commit-reveal helper**.
//! No existing primitive could enforce that a reveal BINDS to its sealed commitment — and a
//! binding the JS computed and the JS checked would enforce nothing (a malicious script would
//! just write whatever). So the RUNTIME owns the seal:
//!
//!   - `seal(bidder, value, nonce)` — a pure host fn returning the BLAKE3 sealed commitment
//!     (the SAME construction the real `Bid::seal` uses). A bidder publishes ONLY this digest
//!     at commit time; the secret value/nonce stay in JS variables until reveal.
//!   - `commitSeal(auction, {slot, seal, guard?})` — freeze a sealed bid as ONE cap-gated
//!     verified turn; WRITE-ONCE (no overwriting a committed bid) + an optional phase guard.
//!   - `revealBid(auction, {sealSlot, revealSlot, bidder, value, nonce, guard?})` — open a
//!     bid; the runtime RE-HASHES the opening and refuses one that does not bind to the frozen
//!     seal (the keystone binding tooth), optionally phase-guarded. The revealed value is
//!     written as a verified turn.
//!
//! Every effect is a REAL cap-gated verified turn through the embedded executor; the app names
//! cells only by the handles the cap table installed (no ambient cell ids), and the binding /
//! phase / write-once / confinement teeth all bite in-band.

use deos_js_runtime::{seal_commitment, CellWorld, FireError, NativeRuntime};
use dregg_cell::interface::{method_symbol, ArgsSchema, InterfaceDescriptor, MethodSig, Semantics};
use dregg_cell::AuthRequired;

/// Each verified turn the world stamps burns this fee from the acting cell.
const FEE: i64 = 10_000;
/// The starting balance every party is funded with.
const START: i64 = 1_000_000;

// ── The auction cell's slot layout ──────────────────────────────────────────────────────
/// The lifecycle phase: `COMMIT → REVEAL → RESOLVED` (only ever advances, guarded).
const PHASE_SLOT: usize = 0;
/// The announced winner (a bidder tag) — written at resolve.
const WINNER_SLOT: usize = 1;
/// The announced winning (highest) bid — written at resolve.
const HIGH_BID_SLOT: usize = 2;
/// Bidder `i`'s 256-bit sealed commitment lives in slot `SEAL_BASE + i` (a full FieldElement).
const SEAL_BASE: usize = 3;
/// Bidder `i`'s revealed bid value lives in slot `REVEAL_BASE + i` (written only on a binding
/// open).
const REVEAL_BASE: usize = 6;

const COMMIT: u64 = 0;
const REVEAL: u64 = 1;
const RESOLVED: u64 = 2;

// ── The bidder tags + their (secret) bids ───────────────────────────────────────────────
const ALICE: u64 = 1;
const BOB: u64 = 2;
const CAROL: u64 = 3;
const ALICE_BID: u64 = 500_000;
const BOB_BID: u64 = 750_000; // the high bid — bob wins.
const CAROL_BID: u64 = 300_000;
const ALICE_NONCE: u64 = 1111;
const BOB_NONCE: u64 = 2222;
const CAROL_NONCE: u64 = 3333;

/// The auction's **published typed interface** — `commit`/`reveal` gated on the published
/// `MethodSig` (the SAME content-addressed descriptor a real coordinator cell publishes). The
/// commit-reveal primitives resolve their cap requirement through this via `route_method`, the
/// same DFA dispatch `invoke()` speaks. `reveal_auth` is parameterized so the unauthorized
/// test can publish a stronger `Proof` requirement than the `Signature` the app holds.
fn auction_interface(reveal_auth: AuthRequired) -> InterfaceDescriptor {
    InterfaceDescriptor::new(vec![
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::Signature,
            ..MethodSig::replayable(method_symbol("commit"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(3),
            auth_required: reveal_auth,
            ..MethodSig::replayable(method_symbol("reveal"))
        },
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol("status"))
        },
    ])
}

/// A five-cell sealed-auction world the JS coordinates: three bidders, a seller, and the
/// auction coordinator (phase seeded at COMMIT, the typed interface published). `held_auction`
/// is the authority the app holds toward the coordinator.
fn auction_world(reveal_auth: AuthRequired, held_auction: AuthRequired) -> CellWorld {
    let mut w = CellWorld::new();

    for (name, tag) in [
        ("alice", 0xA1u8),
        ("bob", 0xB0),
        ("carol", 0xCA),
        ("seller", 0x5E),
    ] {
        let mut pk = [0u8; 32];
        pk[0] = tag;
        w.add_cell(
            name,
            pk,
            [0u8; 32],
            START,
            &[],
            Vec::new(),
            AuthRequired::Signature,
        );
    }

    let mut auction_pk = [0u8; 32];
    auction_pk[0] = 0xA0;
    w.add_cell(
        "auction",
        auction_pk,
        [0u8; 32],
        START,
        &[(PHASE_SLOT, COMMIT)],
        Vec::new(),
        held_auction,
    );
    w.publish_interface("auction", auction_interface(reveal_auth));

    w
}

/// The conserved quantity — the sum of the five parties' balances. Each committed turn burns
/// exactly one [`FEE`] from its acting cell, so this equals `5 * START - FEE * receipts`.
fn balance_sum(w: &CellWorld) -> i64 {
    ["alice", "bob", "carol", "seller", "auction"]
        .iter()
        .map(|n| w.balance(n).unwrap())
        .sum()
}

/// The JS that runs the WHOLE auction lifecycle: three sealed commits, close, three bound
/// reveals, winner selection off committed state, an atomic resolve, and the first-price
/// settlement transfer.
fn full_auction_app() -> String {
    format!(
        r#"
        // ── COMMIT PHASE: each bidder seals its bid and publishes ONLY the digest. ──────
        // The secret value/nonce never leave JS until reveal; the guard pins phase==COMMIT.
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        commitSeal("auction", JSON.stringify({{ slot:{sb}, seal: seal({bob},{bb},{bn}),   guard:{{slot:{ps},value:{commit}}} }}));
        commitSeal("auction", JSON.stringify({{ slot:{sc}, seal: seal({carol},{cb},{cn}), guard:{{slot:{ps},value:{commit}}} }}));

        // ── close the commit phase (advance COMMIT -> REVEAL, only from COMMIT). ────────
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{commit}}}, ops:[{{setSlot:{{slot:{ps},value:{reveal}}}}}] }}));

        // ── REVEAL PHASE: each bidder opens; the runtime re-hashes + binds; phase-guarded. ─
        revealBid("auction", JSON.stringify({{ sealSlot:{sa}, revealSlot:{ra}, bidder:{alice}, value:{ab}, nonce:{an}, guard:{{slot:{ps},value:{reveal}}} }}));
        revealBid("auction", JSON.stringify({{ sealSlot:{sb}, revealSlot:{rb}, bidder:{bob},   value:{bb}, nonce:{bn}, guard:{{slot:{ps},value:{reveal}}} }}));
        revealBid("auction", JSON.stringify({{ sealSlot:{sc}, revealSlot:{rc}, bidder:{carol}, value:{cb}, nonce:{cn}, guard:{{slot:{ps},value:{reveal}}} }}));

        // ── determine the winner from the REVEALED (hence committed-bound) bids. ─────────
        var va = get("auction", {ra}), vb = get("auction", {rb}), vc = get("auction", {rc});
        var winnerTag = {alice}, high = va, winnerCell = "alice";
        if (vb > high) {{ winnerTag = {bob};   high = vb; winnerCell = "bob"; }}
        if (vc > high) {{ winnerTag = {carol}; high = vc; winnerCell = "carol"; }}

        // ── RESOLVE: announce winner + high + phase=RESOLVED ATOMICALLY, only from REVEAL. ─
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{reveal}}}, ops:[
            {{setSlot:{{slot:{ws},value:winnerTag}}}},
            {{setSlot:{{slot:{hs},value:high}}}},
            {{setSlot:{{slot:{ps},value:{resolved}}}}}
        ]}}));

        // ── SETTLE (first-price): the winner pays the seller exactly the winning bid. ────
        transfer(winnerCell, "seller", high);
        high;
    "#,
        sa = SEAL_BASE,
        sb = SEAL_BASE + 1,
        sc = SEAL_BASE + 2,
        ra = REVEAL_BASE,
        rb = REVEAL_BASE + 1,
        rc = REVEAL_BASE + 2,
        ps = PHASE_SLOT,
        ws = WINNER_SLOT,
        hs = HIGH_BID_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        resolved = RESOLVED,
        alice = ALICE,
        bob = BOB,
        carol = CAROL,
        ab = ALICE_BID,
        bb = BOB_BID,
        cb = CAROL_BID,
        an = ALICE_NONCE,
        bn = BOB_NONCE,
        cn = CAROL_NONCE,
    )
}

/// (a) THE HAPPY PATH: one pure-JS program runs the whole sealed-bid auction. Three sealed
/// commits hide the bids, three bound reveals open them, the highest (bob) wins, and the
/// first-price payment reaches the seller — value conserved (only per-turn fees burned).
#[test]
fn pure_js_sealed_auction_happy_path_settles_and_conserves() {
    let world = auction_world(AuthRequired::Signature, AuthRequired::Signature);
    let initial_sum = balance_sum(&world);
    assert_eq!(initial_sum, 5 * START, "five parties funded at START each");

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &full_auction_app())
        .expect("the pure-JS sealed auction runs natively");
    let w = &outcome.world;

    assert!(
        outcome.last_fire_error.is_none(),
        "every coordinated auction effect committed cleanly: {:?}",
        outcome.last_fire_error
    );

    // The lifecycle reached RESOLVED and announced the right winner + price.
    assert_eq!(
        w.get_slot("auction", PHASE_SLOT).unwrap(),
        RESOLVED,
        "auction RESOLVED"
    );
    assert_eq!(
        w.get_slot("auction", WINNER_SLOT).unwrap(),
        BOB,
        "the highest committed-and-revealed bidder (bob) was announced winner"
    );
    assert_eq!(
        w.get_slot("auction", HIGH_BID_SLOT).unwrap(),
        BOB_BID,
        "the winning bid is bob's 750k"
    );
    assert_eq!(
        outcome.result,
        Some(BOB_BID as i32),
        "the app returned the winning bid"
    );

    // NINE verified turns: 3 commit + 1 close + 3 reveal + 1 resolve + 1 settle-transfer.
    assert_eq!(
        w.receipts().len(),
        9,
        "3 commits + close + 3 reveals + resolve + settle = 9 verified turns"
    );

    // VALUE MOVED to the seller, and is CONSERVED:
    //   bob (winner): START - FEE (his settle turn) - BOB_BID (paid to the seller).
    //   seller: START + BOB_BID. alice/carol: untouched. auction: START - 8*FEE (its turns).
    assert_eq!(
        w.balance("bob").unwrap(),
        START - FEE - BOB_BID as i64,
        "the winner paid his bid plus his settle-turn fee"
    );
    assert_eq!(
        w.balance("seller").unwrap(),
        START + BOB_BID as i64,
        "the seller received exactly the winning bid"
    );
    assert_eq!(
        w.balance("alice").unwrap(),
        START,
        "a losing bidder paid nothing"
    );
    assert_eq!(
        w.balance("carol").unwrap(),
        START,
        "a losing bidder paid nothing"
    );
    assert_eq!(
        w.balance("auction").unwrap(),
        START - 8 * FEE,
        "the coordinator moved no value — it paid only its eight turn fees"
    );

    // CONSERVATION: the five-cell sum dropped by exactly one fee per committed turn.
    assert_eq!(
        balance_sum(w),
        initial_sum - FEE * w.receipts().len() as i64,
        "balance conserved: initial sum minus the burned per-turn fees"
    );

    // The revealed values are genuinely BOUND to the sealed commitments (winner_was_committed):
    // re-hashing each opening reproduces the digest frozen at commit time.
    assert_eq!(
        w.get_seal("auction", SEAL_BASE + 1).unwrap(),
        seal_commitment(BOB, BOB_BID, BOB_NONCE),
        "bob's frozen seal binds to his revealed (bidder,value,nonce)"
    );
}

/// (b) THE BINDING TOOTH (`reveal_binds_committed`): a bidder who sealed one value cannot
/// reveal a DIFFERENT one. The opening's re-hash does not match the frozen seal, so the reveal
/// is refused IN-BAND (`CommitmentMismatch`) before any turn — no peeking-then-switching.
#[test]
fn pure_js_reveal_with_switched_value_is_refused() {
    let world = auction_world(AuthRequired::Signature, AuthRequired::Signature);

    // alice seals 500k, closes the commit phase, then tries to open as 999k (a higher bid she
    // never committed to). The runtime re-hashes (alice, 999k, nonce) — it does NOT match the
    // seal of (alice, 500k, nonce), so the reveal is refused.
    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{commit}}}, ops:[{{setSlot:{{slot:{ps},value:{reveal}}}}}] }}));
        try {{
            revealBid("auction", JSON.stringify({{ sealSlot:{sa}, revealSlot:{ra}, bidder:{alice}, value:999000, nonce:{an}, guard:{{slot:{ps},value:{reveal}}} }}));
        }} catch (e) {{ /* CommitmentMismatch: the switched bid does not bind */ }}
        get("auction", {ra});
    "#,
        sa = SEAL_BASE,
        ra = REVEAL_BASE,
        ps = PHASE_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        alice = ALICE,
        ab = ALICE_BID,
        an = ALICE_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the throw");
    let w = &outcome.world;

    assert!(
        matches!(
            outcome.last_fire_error,
            Some(FireError::CommitmentMismatch(_))
        ),
        "a switched value's reveal is refused as a binding mismatch, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        w.get_slot("auction", REVEAL_BASE).unwrap(),
        0,
        "no bid was revealed — the switched opening committed nothing"
    );
    // Only the commit + close committed; the refused reveal never reached the executor.
    assert_eq!(
        w.receipts().len(),
        2,
        "commit + close only; the non-binding reveal committed nothing"
    );
}

/// (c) `uncommitted_cannot_open`: a party who never sealed a bid cannot reveal one. carol's
/// seal slot is all-zero (no commitment), so any opening fails the binding check IN-BAND.
#[test]
fn pure_js_uncommitted_party_cannot_reveal() {
    let world = auction_world(AuthRequired::Signature, AuthRequired::Signature);

    // alice commits; the phase closes; carol — who never committed — tries to reveal at her
    // (empty) seal slot. The all-zero seal never matches any opening: CommitmentMismatch.
    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{commit}}}, ops:[{{setSlot:{{slot:{ps},value:{reveal}}}}}] }}));
        try {{
            revealBid("auction", JSON.stringify({{ sealSlot:{sc}, revealSlot:{rc}, bidder:{carol}, value:{cb}, nonce:{cn}, guard:{{slot:{ps},value:{reveal}}} }}));
        }} catch (e) {{ /* CommitmentMismatch: nothing was ever sealed at carol's slot */ }}
        0;
    "#,
        sa = SEAL_BASE,
        sc = SEAL_BASE + 2,
        rc = REVEAL_BASE + 2,
        ps = PHASE_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        alice = ALICE,
        ab = ALICE_BID,
        an = ALICE_NONCE,
        carol = CAROL,
        cb = CAROL_BID,
        cn = CAROL_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the throw");
    let w = &outcome.world;

    assert!(
        matches!(
            outcome.last_fire_error,
            Some(FireError::CommitmentMismatch(_))
        ),
        "an uncommitted party's reveal is refused, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        w.get_slot("auction", REVEAL_BASE + 2).unwrap(),
        0,
        "carol revealed nothing"
    );
    assert_eq!(w.receipts().len(), 2, "commit + close only");
}

/// (d) ANTI-FRONT-RUNNING (WRITE-ONCE): a sealed bid is FROZEN the instant it is committed —
/// a second commit to the same slot is refused IN-BAND, so a committed bid can never be
/// overwritten (e.g. front-run after peeking at a rival's seal). The original seal stands.
#[test]
fn pure_js_committed_bid_cannot_be_overwritten() {
    let world = auction_world(AuthRequired::Signature, AuthRequired::Signature);

    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        try {{
            // a second commit to the SAME slot — write-once refuses it, the sealed board is append-only.
            commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},999000,{an}), guard:{{slot:{ps},value:{commit}}} }}));
        }} catch (e) {{ /* CommitmentMismatch: cannot overwrite a committed bid */ }}
        0;
    "#,
        sa = SEAL_BASE,
        ps = PHASE_SLOT,
        commit = COMMIT,
        alice = ALICE,
        ab = ALICE_BID,
        an = ALICE_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the throw");
    let w = &outcome.world;

    assert!(
        matches!(
            outcome.last_fire_error,
            Some(FireError::CommitmentMismatch(_))
        ),
        "the overwrite was refused as write-once, got {:?}",
        outcome.last_fire_error
    );
    // The ORIGINAL seal stands — the overwrite changed nothing.
    assert_eq!(
        w.get_seal("auction", SEAL_BASE).unwrap(),
        seal_commitment(ALICE, ALICE_BID, ALICE_NONCE),
        "the first sealed bid is intact; the overwrite committed nothing"
    );
    assert_eq!(w.receipts().len(), 1, "only the first commit committed");
}

/// (e) `reveal_requires_reveal_phase`: a reveal attempted while still in the COMMIT phase is
/// refused. The opening BINDS (a faithful re-hash), but the phase guard (`require_field_equals
/// phase == REVEAL`) fails inside the executor, so the WHOLE turn is refused atomically — no
/// reveal before the commit phase closes, and the gate is folded into the action commitment
/// (light-client-witnessed), not an ordering the JS chose.
#[test]
fn pure_js_reveal_before_commit_phase_closes_is_refused() {
    let world = auction_world(AuthRequired::Signature, AuthRequired::Signature);

    // commit alice, then reveal WITHOUT closing the commit phase (phase is still COMMIT).
    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        try {{
            revealBid("auction", JSON.stringify({{ sealSlot:{sa}, revealSlot:{ra}, bidder:{alice}, value:{ab}, nonce:{an}, guard:{{slot:{ps},value:{reveal}}} }}));
        }} catch (e) {{ /* PreconditionFailed: phase is still COMMIT */ }}
        0;
    "#,
        sa = SEAL_BASE,
        ra = REVEAL_BASE,
        ps = PHASE_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        alice = ALICE,
        ab = ALICE_BID,
        an = ALICE_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the throw");
    let w = &outcome.world;

    match &outcome.last_fire_error {
        Some(FireError::Executor(msg)) => assert!(
            msg.contains("Precondition") || msg.contains("precondition"),
            "the early reveal names the failed phase precondition, got: {msg}"
        ),
        other => panic!("expected an Executor(PreconditionFailed) refusal, got {other:?}"),
    }
    assert_eq!(
        w.get_slot("auction", REVEAL_BASE).unwrap(),
        0,
        "nothing was revealed"
    );
    assert_eq!(
        w.get_slot("auction", PHASE_SLOT).unwrap(),
        COMMIT,
        "still in COMMIT phase"
    );
    // Only the commit left a receipt; the phase-refused reveal left none (but burned its fee,
    // since the guard refusal happens inside the executor).
    assert_eq!(
        w.receipts().len(),
        1,
        "commit only; the early reveal committed no receipt"
    );
}

/// (f) SETTLEMENT CONFINEMENT: the winner's first-price payment cannot be drained to a party
/// the app holds no cap to. After a full resolve, `transfer(winner, "ghost", ..)` to an
/// unheld cell is `NoCapability` (the ocap stance — you cannot even name what you do not
/// hold); the winner's funds are untouched and the legitimate payout to the real seller still
/// commits afterward.
#[test]
fn pure_js_settlement_cannot_drain_to_an_unheld_party() {
    let mut world = auction_world(AuthRequired::Signature, AuthRequired::Signature);
    // a cell on the SAME ledger the app holds NO cap to (no handle names it).
    let mut ghost_pk = [0u8; 32];
    ghost_pk[0] = 0x66;
    let ghost_id = world.add_uncapped_cell(ghost_pk, [0u8; 32], 4_242, &[(0usize, 88u64)]);

    // run the full auction up to RESOLVED, then attempt a drain before the real settlement.
    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sb}, seal: seal({bob},{bb},{bn}), guard:{{slot:{ps},value:{commit}}} }}));
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{commit}}}, ops:[{{setSlot:{{slot:{ps},value:{reveal}}}}}] }}));
        revealBid("auction", JSON.stringify({{ sealSlot:{sb}, revealSlot:{rb}, bidder:{bob}, value:{bb}, nonce:{bn}, guard:{{slot:{ps},value:{reveal}}} }}));
        var high = get("auction", {rb});
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{reveal}}}, ops:[
            {{setSlot:{{slot:{ws},value:{bob}}}}},
            {{setSlot:{{slot:{hs},value:high}}}},
            {{setSlot:{{slot:{ps},value:{resolved}}}}}
        ]}}));
        try {{
            transfer("bob", "ghost", high);   // drain to an unheld cell — refused in-band.
        }} catch (e) {{ /* NoCapability: the winner is never touched by this */ }}
        transfer("bob", "seller", high);      // the LEGITIMATE payout still commits.
        high;
    "#,
        sb = SEAL_BASE + 1,
        rb = REVEAL_BASE + 1,
        ps = PHASE_SLOT,
        ws = WINNER_SLOT,
        hs = HIGH_BID_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        resolved = RESOLVED,
        bob = BOB,
        bb = BOB_BID,
        bn = BOB_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the drain over-reach");
    let w = &outcome.world;

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::NoCapability(_))),
        "the drain to an unheld cell recorded a NoCapability refusal, got {:?}",
        outcome.last_fire_error
    );
    // the ghost cell is byte-untouched: same balance, same field.
    let ghost = w.cell_on_ledger(ghost_id).expect("ghost on the ledger");
    assert_eq!(
        ghost.state.balance(),
        4_242,
        "uncapped ghost balance untouched"
    );
    // ⚑ READ THROUGH `unpack_u64`, NOT `fe[0]`.
    //
    // `pack_u64` is `dregg_cell::field_from_u64` — the CANONICAL encoding, which does not put the
    // value in lane 0. Its own doc says so: "the pair must stay on the same lane or every stored
    // value reads back as garbage." Reading `fe[0]` returned 0 for a field seeded to 123, so this
    // assertion compared a lane nobody writes.
    //
    // ⚠ That matters more here than in an ordinary fixture: this is a SECURITY refusal — "the
    // uncapped cell was not touched". A read that always yields 0 would keep passing after a real
    // breach wrote a value, because the breach would land in the canonical lane and this looked
    // somewhere else.
    assert_eq!(
        ghost
            .state
            .get_field(0)
            .copied()
            .map(|fe| deos_js_core::unpack_u64(&fe)),
        Some(88),
        "uncapped ghost field untouched — the drain never reached it"
    );
    // the legitimate payout still reached the real seller.
    assert_eq!(
        w.balance("seller").unwrap(),
        START + BOB_BID as i64,
        "the legitimate first-price payout still committed after the refused drain"
    );
}

/// (g) THE CAP GATE COMES FROM THE PUBLISHED INTERFACE: the app holds only `Signature` toward
/// the auction, but the PUBLISHED `reveal` method requires the stronger, incomparable `Proof`.
/// The commit succeeds, but the reveal is refused IN-BAND (`Unauthorized`, via the same
/// `is_attenuation` tooth, gated on the published `MethodSig`) — nothing is revealed.
#[test]
fn pure_js_reveal_cap_gate_comes_from_the_published_interface() {
    // reveal requires Proof; the app holds only Signature toward the auction.
    let world = auction_world(AuthRequired::Proof, AuthRequired::Signature);

    let app = format!(
        r#"
        commitSeal("auction", JSON.stringify({{ slot:{sa}, seal: seal({alice},{ab},{an}), guard:{{slot:{ps},value:{commit}}} }}));
        batch("auction", JSON.stringify({{ guard:{{slot:{ps},value:{commit}}}, ops:[{{setSlot:{{slot:{ps},value:{reveal}}}}}] }}));
        try {{
            revealBid("auction", JSON.stringify({{ sealSlot:{sa}, revealSlot:{ra}, bidder:{alice}, value:{ab}, nonce:{an}, guard:{{slot:{ps},value:{reveal}}} }}));
        }} catch (e) {{ /* Unauthorized: the published reveal requires Proof */ }}
        0;
    "#,
        sa = SEAL_BASE,
        ra = REVEAL_BASE,
        ps = PHASE_SLOT,
        commit = COMMIT,
        reveal = REVEAL,
        alice = ALICE,
        ab = ALICE_BID,
        an = ALICE_NONCE,
    );

    let mut rt = NativeRuntime::new();
    let outcome = rt
        .run_world(world, &app)
        .expect("the try/catch swallows the throw");
    let w = &outcome.world;

    assert!(
        matches!(outcome.last_fire_error, Some(FireError::Unauthorized(_))),
        "the published Proof requirement gates the reveal, got {:?}",
        outcome.last_fire_error
    );
    assert_eq!(
        w.get_slot("auction", REVEAL_BASE).unwrap(),
        0,
        "the unauthorized reveal revealed nothing"
    );
    assert_eq!(
        w.receipts().len(),
        2,
        "commit + close only; the unauthorized reveal committed nothing"
    );
}
