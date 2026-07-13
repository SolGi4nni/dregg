//! **The game-loop / AI-DM-as-Reactor — the WRITE/react complement to the
//! just-landed reactive-read indexer (`src/indexer.rs`).**
//!
//! The indexer is the READ half: a client folds the VERIFIED receipt stream into
//! a materialized view and renders off it. This is the WRITE half: an on-chain
//! **Reactor** (the AI-DM / NPC) WATCHES the game/board cell and, when a party
//! move commits, FIRES a cap-gated world-resolution turn — driven LIVE off the
//! SAME verified stream (`src/receipt_stream.rs`), so the game-loop triggers are
//! in-order, un-forged, non-omission-certified.
//!
//! ## What is real (driven by the tests below)
//!
//!  * **[`GameReactor`] — the AI-DM/NPC as a cap-gated Reactor.** It watches the
//!    board cell for the party's move method and reacts by re-using
//!    [`AgentPlayer::choose_move`] to pick the NPC's world-resolution move. Because
//!    `choose_move` fires through the GENUINE `is_attenuation` affordance gate
//!    (`src/game.rs`), the NPC's action space **is its cap set** — the reaction can
//!    only ever be one of the NPC's own units' authorized moves; it cannot cheat
//!    past the affordance/CellProgram (a move it is not authorized for is never even
//!    produced, and off its turn it produces nothing).
//!  * **The framework cap-gate refuses an over-reach, non-vacuously.** The
//!    reaction's `auth_required` is the NPC side's REAL rights identity
//!    ([`side_rights`] = `AuthRequired::Custom { vk_hash }`, the side's genuine
//!    vision-predicate hash). [`plan_reaction`] refuses (fail-closed) when the
//!    presented [`InvokeAuthority`] does not satisfy it — the WRONG side's identity,
//!    or none, is `ReactRefused::Unauthorized`; the RIGHT side reacts. (Non-vacuous:
//!    both the refuse and the admit branch fire.)
//!  * **Driven LIVE off the verified stream.** [`drive_over_stream`] feeds each
//!    frame through [`ReceiptStream::ingest`]'s gate FIRST; only an `Admitted::New`
//!    receipt is turned into an [`ObservedReceipt`] and handed to the reactor. A
//!    forged frame (body does not hash to its claimed `receipt_hash`) or an
//!    out-of-order frame (a gap) is REJECTED there — the reactor never sees it, so
//!    the game loop cannot be spoofed. This replaces the bot's naive unverified 5s
//!    poll with an in-order + un-forged trigger source.
//!  * **The reaction is a genuine executor turn that verifies.** [`react_build`]
//!    signs the reaction into a real [`Turn`]; submitting it through an
//!    [`EmbeddedExecutor`] COMMITS it and moves on-ledger state — it is an ordinary
//!    executor-refereed turn (there is no kernel `Effect::React`; a reaction
//!    desugars to ordinary effects). The [`RevealReactor`]'s daily-reveal further
//!    rides a REAL executor tooth: a `StrictMonotonic` day counter, so a replayed
//!    beacon cannot re-reveal the same day (the executor refuses it).
//!  * **[`RevealReactor`] — the daily clock.** It watches a committed
//!    beacon/temporal tick (the daily clock the event-triggered reactor otherwise
//!    lacks) and fires the daily-reveal turn (open/announce today's Descent —
//!    `docs/GAME-STRATEGY.md` "at midnight ... a new dungeon is revealed").
//!
//! ## The named seams (not faked)
//!
//!  * **The live transport.** This is the pure react-build CORE (exactly the
//!    discipline `ReceiptStream`/`Indexer` keep): a caller feeds frames and submits
//!    the returned turns. The live SSE subscription + submit loop a deploy wires is
//!    the transport lane's, above this boundary.
//!  * **The typed-effect enrichment.** The `(cell, method, effects)` an
//!    [`ObservedReceipt`] carries is the node's per-receipt DISCLOSURE (the same
//!    named seam `src/indexer.rs` documents): the stream verifies a receipt's ORDER
//!    + INTEGRITY; the typed effect body is node-attested.
//!  * **The AI brain behind `choose_move`.** Here the NPC is the built-in scripted
//!    [`AgentPlayer`] policy — a legitimate stand-in. The attested-narrator crown
//!    (the real MPC-TLS/attestation path, `docs/GAME-STRATEGY.md` decision 3) is the
//!    named upgrade: the reactor's `react()` is exactly the seam an attested model's
//!    proposal plugs into (AI proposes, the cap-gate + executor dispose).
//!  * **Re-enforcing the Custom vision-predicate AT the executor.** The NPC's
//!    Custom-`vk_hash` rights are enforced at the affordance layer (`choose_move`)
//!    and at the framework cap-gate; driving that SAME predicate through the
//!    executor's witnessed-predicate registry (vs. the signed self-write the
//!    embedded executor commits here) is the vision-predicate-registry wiring seam.
//!
//! ## Why this file lives in `tests/`
//!
//! `dregg-app-framework` already depends on `starbridge-web-surface` (for its
//! affordance/rehydration re-exports), so this crate can only consume
//! `app_framework::Reactor` as a **dev-dependency** (cargo permits a dev-dependency
//! cycle; a normal one would be forbidden). The reactors are therefore defined
//! alongside their driving tests here — additive and non-breaking to the shipping
//! library.

use dregg_app_framework::{
    field_from_u64, hex_encode_32, plan_reaction, react_build, symbol, AgentCipherclerk,
    AppCipherclerk, AuthRequired, Effect, EmbeddedExecutor, FieldElement, InvokeAuthority,
    ObservedReceipt, ReactRefused, ReactionPlan, Reactor, ReceiptFilter, Turn, WatchCells,
    WatchMethods,
};
use dregg_cell::{CellProgram, StateConstraint};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use starbridge_web_surface::affordance::AffordanceIntent;
use starbridge_web_surface::game::{demo_skirmish, side_rights, AgentPlayer, Board, Side};
use starbridge_web_surface::receipt_stream::{
    Admitted, IngestError, ReceiptEnvelope, ReceiptStream, StreamedReceipt,
};

// ───────────────────────────────────────────────────────────────────────────────
// The GameReactor — the AI-DM / NPC as a cap-gated Reactor.
// ───────────────────────────────────────────────────────────────────────────────

/// The AI-DM / NPC reactor. Watches `board_cell` for the party's move method(s) and
/// reacts with the NPC's world-resolution move, picked through the SAME cap-gated
/// affordance surface a human fires.
struct GameReactor {
    /// The board/game cell whose party-move receipts wake the reactor.
    board_cell: CellId,
    /// The party's move method symbols this reactor watches (the human party's move
    /// affordance names, hashed).
    party_move_methods: Vec<FieldElement>,
    /// The NPC agent player — its action space IS its attenuated cap set.
    npc: AgentPlayer,
    /// The world state AFTER the party's move (its `turn` is the NPC's side): the
    /// board the AI-DM resolves the world against.
    board: Board,
}

impl Reactor for GameReactor {
    fn filter(&self) -> ReceiptFilter {
        // What it watches: the board cell, for the party's move method(s). The
        // reactive analogue of the board cell's interface descriptor.
        ReceiptFilter {
            cells: WatchCells::OneOf(vec![self.board_cell]),
            methods: WatchMethods::OneOf(self.party_move_methods.clone()),
        }
    }

    fn react(&self, _observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // RESOLVE THE WORLD — the AI-DM/NPC picks its move via the SAME cap-gated
        // affordance surface a human fires. `choose_move` projects the NPC's move
        // surface for its OWN side (the genuine `is_attenuation` gate) and fires
        // within it, so the returned intent is ALWAYS one of the NPC's own units'
        // authorized moves — the NPC cannot cheat past the CellProgram, and off its
        // turn it produces nothing (`None` => the NPC passes).
        let intent: AffordanceIntent = self.npc.choose_move(&self.board)?;
        Some(ReactionPlan {
            target: self.board_cell,
            method: intent.affordance.clone(),
            args: vec![],
            // The reaction desugars to the ordinary REAL move effect the affordance
            // fired — the kernel/circuit see only what they already know.
            effects: vec![intent.effect.clone()],
            // The NPC's cap identity: the side's genuine vision-predicate rights.
            auth_required: side_rights(self.npc.side),
        })
    }
}

// ───────────────────────────────────────────────────────────────────────────────
// The RevealReactor — a beacon/temporal tick as the daily clock.
// ───────────────────────────────────────────────────────────────────────────────

/// The daily-reveal reactor. Watches a committed beacon/temporal tick (the daily
/// clock) and reacts by opening/announcing today's Descent — advancing a
/// `StrictMonotonic` day counter (so a replayed beacon can't re-reveal the same
/// day) and posting the beacon-derived dungeon seed.
struct RevealReactor {
    /// The beacon/temporal cell whose committed tick wakes the reveal.
    beacon_cell: CellId,
    /// The beacon tick method this reactor watches.
    tick_method: FieldElement,
    /// The Descent/day cell the reveal writes.
    descent_cell: CellId,
    /// The slot holding the day/round counter (StrictMonotonic — the reveal
    /// strictly advances it; a stale/replayed beacon is refused by the executor).
    day_slot: usize,
    /// The slot holding today's revealed dungeon seed.
    seed_slot: usize,
}

impl Reactor for RevealReactor {
    fn filter(&self) -> ReceiptFilter {
        ReceiptFilter {
            cells: WatchCells::OneOf(vec![self.beacon_cell]),
            methods: WatchMethods::OneOf(vec![self.tick_method]),
        }
    }

    fn react(&self, observed: &ObservedReceipt) -> Option<ReactionPlan> {
        // PERCEIVE — the beacon's committed round (the temporal tick / drand round),
        // read straight off the observed tick's first field write. Fail-closed: a
        // tick with no field is nothing to reveal against.
        let round = observed.effects.iter().find_map(|e| match e {
            Effect::SetField { value, .. } => Some(*value),
            _ => None,
        })?;
        // The revealed dungeon seed is bound to the beacon round (unpredictable
        // until the beacon commits).
        let seed = *blake3::hash(&round).as_bytes();
        // ACT — open/announce today's Descent: advance the day counter and post the
        // seed. `reveal_descent` desugars to ordinary field writes.
        Some(ReactionPlan {
            target: self.descent_cell,
            method: "reveal_descent".into(),
            args: vec![round],
            effects: vec![
                Effect::SetField {
                    cell: self.descent_cell,
                    index: self.day_slot,
                    value: round,
                },
                Effect::SetField {
                    cell: self.descent_cell,
                    index: self.seed_slot,
                    value: seed,
                },
            ],
            auth_required: AuthRequired::Signature,
        })
    }
}

// ───────────────────────────────────────────────────────────────────────────────
// The driver: a reactor driven LIVE off the verified receipt stream.
// ───────────────────────────────────────────────────────────────────────────────

/// The node's per-receipt typed DISCLOSURE (the named enrichment seam) — the
/// `(cell, method, effects)` body delivered alongside a verified receipt. The
/// stream verifies ORDER + INTEGRITY; this typed body is node-attested (exactly the
/// boundary `src/indexer.rs` documents).
struct Enrichment {
    cell: CellId,
    method: FieldElement,
    effects: Vec<Effect>,
}

/// Why driving a reactor off the stream refused a step.
#[derive(Debug)]
#[allow(dead_code)] // `React`'s payload is part of the driver's surface (a stream
                    // reaction CAN be cap-refused); the tests here exercise the `Ingest` refusals.
enum DriveError {
    /// The stream's in-order + un-forged gate rejected the frame BEFORE the reactor
    /// saw it — a forged / out-of-order trigger. The game loop cannot be spoofed.
    Ingest(IngestError),
    /// The reaction's required authority is not satisfied (the framework cap-gate,
    /// fail-closed).
    React(ReactRefused),
}

/// **Drive a reactor off the VERIFIED receipt stream.** Feed one frame (`env`) +
/// its typed enrichment; the frame first passes [`ReceiptStream::ingest`]'s gate —
/// a forged or out-of-order frame is [`DriveError::Ingest`] and the reactor is
/// NEVER invoked. On an `Admitted::New` receipt the verified provenance
/// (`receipt_hash` + committing agent) is joined with the node's enrichment into an
/// [`ObservedReceipt`] and handed to [`react_build`]; a benign duplicate re-delivery
/// fires nothing.
fn drive_over_stream<R: Reactor + ?Sized>(
    stream: &mut ReceiptStream,
    cclerk: &AppCipherclerk,
    reactor: &R,
    authority: InvokeAuthority,
    env: ReceiptEnvelope,
    enrichment: Enrichment,
) -> Result<Option<Turn>, DriveError> {
    match stream.ingest(env).map_err(DriveError::Ingest)? {
        // A benign at-least-once re-delivery: verified again, deduplicated, no fire.
        Admitted::Duplicate => Ok(None),
        Admitted::New => {
            let sr: &StreamedReceipt = stream
                .latest()
                .expect("Admitted::New => a latest verified receipt exists");
            let observed = ObservedReceipt {
                cell: enrichment.cell,
                method: enrichment.method,
                effects: enrichment.effects,
                // The VERIFIED (recomputed) receipt hash — provenance, not the
                // claimed wire string.
                turn_hash: sr.receipt_hash,
                // Whose committed op woke the reactor.
                signer: *sr.receipt.agent.as_bytes(),
            };
            react_build(cclerk, reactor, &observed, authority).map_err(DriveError::React)
        }
    }
}

// ───────────────────────────────────────────────────────────────────────────────
// Fixtures.
// ───────────────────────────────────────────────────────────────────────────────

/// A real, distinctly-hashed [`TurnReceipt`] (mirrors the `receipt_stream` /
/// `indexer` test fixtures) so distinct receipts have distinct canonical hashes.
fn receipt(seed: u8) -> TurnReceipt {
    let mut agent = [0u8; 32];
    agent[0] = 0xA0;
    agent[1] = seed;
    TurnReceipt {
        turn_hash: [seed; 32],
        forest_hash: [seed.wrapping_add(1); 32],
        pre_state_hash: [seed.wrapping_add(2); 32],
        post_state_hash: [seed.wrapping_add(3); 32],
        effects_hash: [seed.wrapping_add(4); 32],
        timestamp: 1_718_000_000 + seed as i64,
        computrons_used: 100 + seed as u64,
        action_count: 1 + seed as usize,
        agent: CellId::derive_raw(&agent, &[0u8; 32]),
        ..Default::default()
    }
}

/// An HONEST stream frame at dense `idx` carrying `receipt(seed)` (its claimed hash
/// is the canonical digest, so it passes the forge-check).
fn honest_frame(idx: u64, seed: u8) -> ReceiptEnvelope {
    ReceiptEnvelope::honest(idx, 1880 + idx, receipt(seed))
}

/// The `Custom { vk_hash }` value of a side's genuine rights — the
/// [`InvokeAuthority`] a reactor of that side presents.
fn side_vk(side: Side) -> [u8; 32] {
    match side_rights(side) {
        AuthRequired::Custom { vk_hash } => vk_hash,
        other => panic!("a side's rights are Custom, got {other:?}"),
    }
}

/// Build the AI-DM/NPC scenario: the party (Blue) fires a real move and it commits
/// (the turn passes to Red); returns the post-party board (Red to move), the party's
/// fired intent, and the watched party-move method. `board_cell` overrides the
/// board's backing cell (so an executor test can make it the NPC's own cell).
fn party_moved_scenario(board_cell: CellId) -> (Board, AffordanceIntent, FieldElement) {
    let (mut board, _uri, _web) = demo_skirmish();
    board.cell = board_cell; // the affordance/move surface fires against THIS cell
    let blue = AgentPlayer::new(Side::Blue, CellId::derive_raw(&[0xB1; 32], &[0u8; 32]));
    let party_intent = blue
        .choose_move(&board)
        .expect("Blue (the party) has a legal, authorized opening move");
    let party_method = symbol(&party_intent.affordance);
    // The party's move COMMITS: the board advances and the turn passes to Red.
    board
        .apply_move(&party_intent, Side::Blue)
        .expect("the party's fired move is legal + applies");
    assert_eq!(
        board.turn,
        Side::Red,
        "after the party move it is the NPC's turn"
    );
    (board, party_intent, party_method)
}

/// The NPC (Red) agent player.
fn npc(board_cell: CellId) -> AgentPlayer {
    // The NPC's own cell — distinct from the board cell in the general case.
    let _ = board_cell;
    AgentPlayer::new(Side::Red, CellId::derive_raw(&[0xED; 32], &[0u8; 32]))
}

// ───────────────────────────────────────────────────────────────────────────────
// (1) A committed party move → the AI-DM/NPC reacts with a world-resolution turn.
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn a_committed_party_move_drives_the_ai_dm_to_resolve_the_world() {
    let board_cell = CellId::derive_raw(&[0xB0; 32], &[0u8; 32]);
    let (board, _party_intent, party_method) = party_moved_scenario(board_cell);

    let reactor = GameReactor {
        board_cell,
        party_move_methods: vec![party_method],
        npc: npc(board_cell),
        board,
    };

    // The observed committed party move (matches the filter).
    let observed = ObservedReceipt {
        cell: board_cell,
        method: party_method,
        effects: vec![],
        turn_hash: [1u8; 32],
        signer: [2u8; 32],
    };

    // The AI-DM reacts with a genuine world-resolution plan (the NPC's move).
    let action = plan_reaction(
        &reactor,
        &observed,
        InvokeAuthority::Custom {
            vk_hash: side_vk(Side::Red),
        },
    )
    .expect("the NPC of the right side is authorized")
    .expect("a watched party move drives the AI-DM to resolve the world");

    assert_eq!(
        action.target, board_cell,
        "the reaction resolves the board cell"
    );
    // The reaction is exactly ONE real move effect (a SetField relocating a unit).
    match action.effects.as_slice() {
        [Effect::SetField { cell, index, .. }] => {
            assert_eq!(*cell, board_cell);
            // The NPC (Red) units are at indices 2 and 3 of the demo skirmish — the
            // reaction can ONLY move one of the NPC's OWN units. Its action space is
            // its cap set: it never moves a party (Blue, index 0/1) unit.
            assert!(
                *index == 2 || *index == 3,
                "the AI-DM only ever moves its OWN units (its cap set), got slot {index}"
            );
        }
        other => panic!("expected one real move SetField, got {other:?}"),
    }
}

// ───────────────────────────────────────────────────────────────────────────────
// (2) The reaction is cap-gated — an over-reach is REFUSED (non-vacuous).
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn an_over_reach_reaction_is_refused_fail_closed_non_vacuous() {
    let board_cell = CellId::derive_raw(&[0xB0; 32], &[0u8; 32]);
    let (board, _pi, party_method) = party_moved_scenario(board_cell);
    let reactor = GameReactor {
        board_cell,
        party_move_methods: vec![party_method],
        npc: npc(board_cell),
        board,
    };
    let observed = ObservedReceipt {
        cell: board_cell,
        method: party_method,
        effects: vec![],
        turn_hash: [1u8; 32],
        signer: [2u8; 32],
    };

    // OVER-REACH #1: no authority at all — refused before any turn is built.
    let refused = plan_reaction(&reactor, &observed, InvokeAuthority::None)
        .expect_err("a None-authority reactor cannot satisfy the NPC's Custom rights");
    assert!(matches!(refused, ReactRefused::Unauthorized { .. }));

    // OVER-REACH #2: the WRONG side's identity (Blue) — incomparable to Red's
    // Custom vk_hash, so refused. This is the anti-cheat at the cap-gate: an
    // identity that is not the NPC's cannot fire the NPC's world-resolution.
    let wrong = plan_reaction(
        &reactor,
        &observed,
        InvokeAuthority::Custom {
            vk_hash: side_vk(Side::Blue),
        },
    )
    .expect_err("Blue's identity cannot satisfy Red's reaction");
    assert!(matches!(wrong, ReactRefused::Unauthorized { .. }));

    // ...but the RIGHT side (Red) reacts. NON-VACUOUS: the admit branch fires.
    let ok = plan_reaction(
        &reactor,
        &observed,
        InvokeAuthority::Custom {
            vk_hash: side_vk(Side::Red),
        },
    )
    .expect("Red's identity satisfies its own reaction");
    assert!(ok.is_some(), "the correctly-authorized NPC does react");
}

// ───────────────────────────────────────────────────────────────────────────────
// (3) The AI-DM cannot cheat: off its turn it resolves nothing.
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn the_ai_dm_cannot_act_out_of_turn() {
    // A board where it is the PARTY's (Blue's) turn — NOT the NPC's. `choose_move`
    // projects the NPC's authorized surface and finds no move (it is not Red's
    // turn), so the reactor produces nothing: the AI-DM cannot resolve the world on
    // someone else's turn.
    let board_cell = CellId::derive_raw(&[0xB0; 32], &[0u8; 32]);
    let (mut board, _uri, _web) = demo_skirmish();
    board.cell = board_cell;
    assert_eq!(board.turn, Side::Blue, "fresh board: the party moves first");

    let reactor = GameReactor {
        board_cell,
        party_move_methods: vec![symbol("move:whatever")],
        npc: npc(board_cell),
        board,
    };
    let observed = ObservedReceipt {
        cell: board_cell,
        method: symbol("move:whatever"),
        effects: vec![],
        turn_hash: [1u8; 32],
        signer: [2u8; 32],
    };
    // Even fully authorized, the NPC produces no reaction off its turn.
    let out = plan_reaction(
        &reactor,
        &observed,
        InvokeAuthority::Custom {
            vk_hash: side_vk(Side::Red),
        },
    )
    .expect("no auth error");
    assert!(
        out.is_none(),
        "the AI-DM cannot resolve the world off its turn"
    );
}

// ───────────────────────────────────────────────────────────────────────────────
// (4) Driven LIVE off the VERIFIED stream: react on an admitted trigger, and a
//     forged / out-of-order trigger is REJECTED before the reactor.
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn driven_off_the_verified_stream_forged_and_out_of_order_are_rejected() {
    let board_cell = CellId::derive_raw(&[0xB0; 32], &[0u8; 32]);
    let (board, party_intent, party_method) = party_moved_scenario(board_cell);
    let reactor = GameReactor {
        board_cell,
        party_move_methods: vec![party_method],
        npc: npc(board_cell),
        board,
    };
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [7u8; 32]);
    let red = InvokeAuthority::Custom {
        vk_hash: side_vk(Side::Red),
    };
    let mut stream = ReceiptStream::new(64);

    // The party's move enrichment (the node-disclosed typed body).
    let party_enrichment = |m: FieldElement, e: Effect| Enrichment {
        cell: board_cell,
        method: m,
        effects: vec![e],
    };

    // (a) An HONEST party-move frame at index 0: admitted → the AI-DM reacts.
    let turn = drive_over_stream(
        &mut stream,
        &cclerk,
        &reactor,
        red,
        honest_frame(0, 0),
        party_enrichment(party_method, party_intent.effect.clone()),
    )
    .expect("an honest in-order party-move frame drives the reactor")
    .expect("the AI-DM reacts with a world-resolution turn");
    // The reaction is a genuine signed turn (its hash is well-formed).
    assert_ne!(
        turn.hash(),
        [0u8; 32],
        "the reaction turn is a real signed turn"
    );

    // (b) A FORGED frame at index 1: the claimed hash is a DIFFERENT receipt's, so
    //     its body does not hash to it. REJECTED by the stream gate — the reactor
    //     is NEVER invoked (the game loop cannot be spoofed by a forged trigger).
    let forged = ReceiptEnvelope::new(
        1,
        hex_encode_32(&receipt(99).receipt_hash()), // claims receipt(99)...
        1881,
        vec![],
        vec![],
        receipt(7), // ...but the body is receipt(7). Mismatch.
    );
    let err = drive_over_stream(
        &mut stream,
        &cclerk,
        &reactor,
        red,
        forged,
        party_enrichment(party_method, party_intent.effect.clone()),
    )
    .expect_err("a forged trigger is rejected before the reactor");
    assert!(
        matches!(
            err,
            DriveError::Ingest(IngestError::Forged { chain_index: 1 })
        ),
        "the forged frame is caught by the stream's forge-check, got {err:?}"
    );

    // (c) An OUT-OF-ORDER frame (a gap: index 3 when 1 is expected): REJECTED. A
    //     spoofed re-ordering of the game loop is caught before the reactor.
    let err = drive_over_stream(
        &mut stream,
        &cclerk,
        &reactor,
        red,
        honest_frame(3, 3),
        party_enrichment(party_method, party_intent.effect.clone()),
    )
    .expect_err("an out-of-order trigger is rejected before the reactor");
    assert!(
        matches!(
            err,
            DriveError::Ingest(IngestError::OutOfOrder {
                expected: 1,
                got: 3
            })
        ),
        "the gapped frame is caught by the stream's order-check, got {err:?}"
    );

    // (d) The correct next honest frame (index 1) still flows after the rejections:
    //     the verified game loop resumes.
    let resumed = drive_over_stream(
        &mut stream,
        &cclerk,
        &reactor,
        red,
        honest_frame(1, 1),
        party_enrichment(party_method, party_intent.effect.clone()),
    )
    .expect("the verified stream resumes after a rejected trigger")
    .expect("the AI-DM reacts to the next in-order party move");
    assert_ne!(resumed.hash(), [0u8; 32]);
}

// ───────────────────────────────────────────────────────────────────────────────
// (5) The reaction is a GENUINE executor turn that verifies (commits on-ledger).
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn the_ai_dm_reaction_is_a_genuine_executor_turn_that_commits() {
    // The NPC executor drives turns from its own cell; make the board cell BE that
    // cell so the world-resolution SetField is a signed self-turn the executor
    // commits (mirroring the CoordinatorReactor exemplar, where board == cell_id()).
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let board_cell = executor.cell_id();
    // A permissive program (no state constraints) so the reaction's field write is
    // admitted by the executor — the point here is that a reaction is an ORDINARY
    // executor turn, not that the game program gates it (that is the affordance +
    // cap-gate story, tests 1-3).
    executor.install_program(board_cell, CellProgram::Predicate(vec![]));

    let (board, _pi, party_method) = party_moved_scenario(board_cell);
    let reactor = GameReactor {
        board_cell,
        party_move_methods: vec![party_method],
        npc: npc(board_cell),
        board,
    };
    let observed = ObservedReceipt {
        cell: board_cell,
        method: party_method,
        effects: vec![],
        turn_hash: [1u8; 32],
        signer: cclerk.public_key().0,
    };

    // Build the SIGNED reaction turn (the AI-DM's world-resolution move).
    let turn = react_build(
        &cclerk,
        &reactor,
        &observed,
        InvokeAuthority::Custom {
            vk_hash: side_vk(Side::Red),
        },
    )
    .expect("the correctly-authorized NPC reaction builds")
    .expect("the AI-DM reacts");

    // SUBMIT it through the real executor — it COMMITS (a genuine executor turn that
    // verifies) and moves on-ledger state: the NPC's chosen unit is relocated.
    let _receipt = executor
        .submit_turn(&turn)
        .expect("the AI-DM's world-resolution reaction commits as an ordinary turn");
    let state = executor
        .cell_state(board_cell)
        .expect("the board cell exists after the committed reaction");
    // Whichever NPC unit slot (2 or 3) the AI-DM moved now holds a non-zero packed
    // destination coordinate — the world moved on-ledger.
    let moved = state.fields.get(2).is_some_and(|f| *f != [0u8; 32])
        || state.fields.get(3).is_some_and(|f| *f != [0u8; 32]);
    assert!(
        moved,
        "the AI-DM's committed reaction relocated an NPC unit on-ledger"
    );
}

// ───────────────────────────────────────────────────────────────────────────────
// (6) The RevealReactor fires the daily reveal on a beacon/temporal tick — driven
//     off the verified stream, and cap-gated non-vacuously.
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn the_reveal_reactor_fires_the_daily_reveal_on_a_beacon_tick() {
    let beacon_cell = CellId::derive_raw(&[0xBE; 32], &[0u8; 32]);
    let descent_cell = CellId::derive_raw(&[0xDE; 32], &[0u8; 32]);
    let tick_method = symbol("beacon_tick");
    let reactor = RevealReactor {
        beacon_cell,
        tick_method,
        descent_cell,
        day_slot: 0,
        seed_slot: 1,
    };
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [9u8; 32]);
    let mut stream = ReceiptStream::new(64);

    // A committed beacon tick carrying round 1000 (the daily clock's time-tick).
    let round = field_from_u64(1000);
    let tick_effects = vec![Effect::SetField {
        cell: beacon_cell,
        index: 0,
        value: round,
    }];

    // Driven off the VERIFIED stream: the committed beacon event is the trigger.
    let turn = drive_over_stream(
        &mut stream,
        &cclerk,
        &reactor,
        InvokeAuthority::Signature,
        honest_frame(0, 0),
        Enrichment {
            cell: beacon_cell,
            method: tick_method,
            effects: tick_effects.clone(),
        },
    )
    .expect("the beacon tick drives the reveal")
    .expect("the RevealReactor fires the daily reveal");
    assert_ne!(
        turn.hash(),
        [0u8; 32],
        "the daily reveal is a real signed turn"
    );

    // The plan itself: it reveals TODAY's Descent (day + seed on the descent cell).
    let observed = ObservedReceipt {
        cell: beacon_cell,
        method: tick_method,
        effects: tick_effects,
        turn_hash: [3u8; 32],
        signer: [4u8; 32],
    };
    let action = plan_reaction(&reactor, &observed, InvokeAuthority::Signature)
        .expect("Signature satisfies the reveal")
        .expect("the reveal fires");
    assert_eq!(
        action.target, descent_cell,
        "the reveal opens the Descent cell"
    );
    match action.effects.as_slice() {
        [Effect::SetField {
            index: d,
            value: day,
            ..
        }, Effect::SetField { index: s, .. }] => {
            assert_eq!(*d, 0, "day counter slot");
            assert_eq!(*day, round, "today's day is the beacon round");
            assert_eq!(*s, 1, "seed slot");
        }
        other => panic!("expected day + seed writes, got {other:?}"),
    }

    // Cap-gate NON-VACUOUS: without Signature the reveal is refused.
    let refused = plan_reaction(
        &reactor,
        &observed_none(beacon_cell, tick_method, round),
        InvokeAuthority::None,
    )
    .expect_err("a None-authority reveal is refused");
    assert!(matches!(refused, ReactRefused::Unauthorized { .. }));
}

/// A beacon-tick observation (helper for the cap-gate branch).
fn observed_none(
    beacon_cell: CellId,
    tick_method: FieldElement,
    round: FieldElement,
) -> ObservedReceipt {
    ObservedReceipt {
        cell: beacon_cell,
        method: tick_method,
        effects: vec![Effect::SetField {
            cell: beacon_cell,
            index: 0,
            value: round,
        }],
        turn_hash: [3u8; 32],
        signer: [4u8; 32],
    }
}

// ───────────────────────────────────────────────────────────────────────────────
// (7) The daily reveal is a genuine executor turn; a REPLAYED beacon cannot
//     re-reveal the same day (the executor's StrictMonotonic tooth bites).
// ───────────────────────────────────────────────────────────────────────────────

#[test]
fn a_replayed_beacon_cannot_re_reveal_the_same_day() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x22; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let descent_cell = executor.cell_id();
    let beacon_cell = CellId::derive_raw(&[0xBE; 32], &[0u8; 32]);
    // The day counter (slot 0) is StrictMonotonic: each reveal must strictly advance
    // it, so a replayed beacon (same round) is refused by the executor.
    executor.install_program(
        descent_cell,
        CellProgram::Predicate(vec![StateConstraint::StrictMonotonic { index: 0 }]),
    );
    let tick_method = symbol("beacon_tick");
    let reactor = RevealReactor {
        beacon_cell,
        tick_method,
        descent_cell,
        day_slot: 0,
        seed_slot: 1,
    };

    let reveal_turn = |round_val: u64| -> Turn {
        let observed = ObservedReceipt {
            cell: beacon_cell,
            method: tick_method,
            effects: vec![Effect::SetField {
                cell: beacon_cell,
                index: 0,
                value: field_from_u64(round_val),
            }],
            turn_hash: [round_val as u8; 32],
            signer: cclerk.public_key().0,
        };
        react_build(&cclerk, &reactor, &observed, InvokeAuthority::Signature)
            .expect("authorized")
            .expect("the reveal fires")
    };

    // Day 1 (round 1000) reveals: commits (0 -> 1000).
    executor
        .submit_turn(&reveal_turn(1000))
        .expect("the first daily reveal commits");

    // A REPLAYED beacon (round 1000 again): the executor REFUSES it — the day
    // counter cannot re-advance to the same value (StrictMonotonic). The daily clock
    // cannot be double-fired.
    let replayed = executor.submit_turn(&reveal_turn(1000));
    assert!(
        replayed.is_err(),
        "the executor must refuse a replayed beacon re-revealing the same day"
    );

    // The NEXT day (round 1001) reveals normally: commits (1000 -> 1001).
    executor
        .submit_turn(&reveal_turn(1001))
        .expect("the next day's reveal commits (strictly advances the day counter)");
}
