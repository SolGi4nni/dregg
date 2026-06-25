//! CONSENSUAL VIRTUALIZED-PAST STITCH, SETTLEMENT-SOUND — branch-and-stitch made real on
//! the live two-instance multiplayer membrane.
//!
//! The companion `two_instance_multiplayer_session.rs` demonstrated the field-granular umem
//! STATE stitch (disjoint edits fold clean; a same-address clash is a held `UmemConflict`,
//! fail-closed). This test adds the second, non-monotone axis distributed time-travel turns
//! on: AUTHORITY. It is the operable realization of the two proven Lean keystones —
//!
//!   * `Metatheory.SettlementSoundness.stitch_drops_revoked_authority` — "a cap I have since
//!     revoked cannot ride a stitch into my real world": the linear DROP IS the unsettleable
//!     revoked-authority confer.
//!   * `Dregg2.Circuit.SettlementSoundness.settlement_soundness` — authority is honored AT THE
//!     SETTLEMENT TIP (`honorsAtSettlement` / `settledRevView`), never at the branch.
//!
//! The story, end to end, over ORDINARY cap-gated verified turns (no GM self-grant):
//!
//!   1. CONSENSUAL VIRTUALIZED PAST. Two co-inhabitants (`ada`, `boris`) fork the SAME past
//!      config into a cap-bounded umem branch (the virtualized past — `UmemBranch::mint` at a
//!      recorded `minted_height`). The branch is confined: the `offstage` cell no principal in
//!      the room subgraph reaches is structurally ABSENT (anti-amplification by omission), and
//!      a branch turn that tries to drain a cell it holds no cap to is REFUSED by the executor
//!      — its side-effect stays imaginary (`branch_cannot_drain_main`).
//!
//!   2. THE DRIVE. Each co-inhabitant drives real verified turns on its own independent
//!      `World`: ada edits her doc + the shared board; boris edits his doc + the same board
//!      (the field-granular conflict). At branch time ada also HOLDS a cap to `gift` — the
//!      authority her stitch would confer back into main.
//!
//!   3. THE REVOCATION (non-monotone-at-settlement). BETWEEN branch and settlement, on MAIN,
//!      ada revokes her own `gift` cap with a real verified `RevokeCapability` turn. Main
//!      advances — this is the settlement tip, where the authority view differs from branch.
//!
//!   4. THE SETTLEMENT-SOUND STITCH. The field-granular pushout folds the disjoint edits clean
//!      and holds the board conflict (fail-closed). The settlement gate reads ada's authority
//!      AT THE TIP (`settlement_held_at_tip`, AFTER the revoke): the `gift` confer is
//!      LINEAR-DROPPED (revoked-before-tip), while a cap ada STILL holds is admitted. The state
//!      merge is untouched by the gate — pushout-correct AND settlement-sound.
//!
//! Run (gpui-free, no GPU):
//!   cd starbridge-v2 && cargo test --no-default-features \
//!     --features "embedded-executor dev-surfaces" \
//!     --test branch_stitch_settlement_sound_multiplayer -- --nocapture

#![cfg(all(feature = "dev-surfaces", feature = "embedded-executor"))]

use dregg_cell::{AuthRequired, CellId};
use dregg_turn::umem::{UKey, UVal};

use starbridge_v2::umem_membrane::{
    ConferredCap, UmemBranch, UmemEnvelope, open_umem_envelope, settle_umem_stitch,
    settlement_held_at_tip, stitch_umem_forks,
};
use starbridge_v2::world::{World, make_open_cell, revoke_capability, set_field};

/// The shared world the two co-inhabitants live in — ORDINARY genesis grants only. Returns:
///   `room`     — the focus the membrane culls around (reaches both + the board).
///   `ada` / `boris` — two DISTINCT principals.
///   `board`    — the shared surface both hold (the collision candidate).
///   `doc_ada` / `doc_boris` — each co-inhabitant's own doc (the disjoint edits).
///   `gift`     — a cell ada holds a cap to at branch time (the conferrable authority she
///                later REVOKES — the settlement-sound DROP candidate).
///   `offstage` — a cell NO principal in the room subgraph reaches (the confinement foil).
#[allow(clippy::type_complexity)]
fn shared_world() -> (
    World,
    CellId,
    CellId,
    CellId,
    CellId,
    CellId,
    CellId,
    CellId,
    CellId,
) {
    let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
    let board = w.genesis_cell(0x5D, 0);
    let doc_ada = w.genesis_cell(0xA1, 0);
    let doc_boris = w.genesis_cell(0xB2, 0);
    let gift = w.genesis_cell(0x91, 0);
    let offstage = w.genesis_cell(0xEE, 0);

    let mut ada = make_open_cell(0x0A, 0);
    ada.capabilities
        .grant(board, AuthRequired::None)
        .expect("ada holds the board");
    ada.capabilities
        .grant(doc_ada, AuthRequired::None)
        .expect("ada holds her doc");
    ada.capabilities
        .grant(gift, AuthRequired::None)
        .expect("ada holds the gift cap at branch time");
    let ada_id = w.genesis_install(ada);

    let mut boris = make_open_cell(0x0B, 0);
    boris
        .capabilities
        .grant(board, AuthRequired::None)
        .expect("boris holds the board");
    boris
        .capabilities
        .grant(doc_boris, AuthRequired::None)
        .expect("boris holds his doc");
    let boris_id = w.genesis_install(boris);

    let mut room = make_open_cell(0x40, 0);
    room.capabilities
        .grant(ada_id, AuthRequired::None)
        .expect("room reaches ada");
    room.capabilities
        .grant(boris_id, AuthRequired::None)
        .expect("room reaches boris");
    room.capabilities
        .grant(board, AuthRequired::None)
        .expect("room reaches the board");
    let room_id = w.genesis_install(room);

    (
        w, room_id, ada_id, boris_id, board, doc_ada, doc_boris, gift, offstage,
    )
}

#[test]
fn consensual_virtualized_past_stitch_is_settlement_sound() {
    let (mut world, room, ada, boris, board, doc_ada, doc_boris, gift, offstage) = shared_world();
    eprintln!(
        "\n=== SETTLEMENT-SOUND BRANCH-AND-STITCH: ada ⋈ boris, a revoked cap is dropped ==="
    );

    // ── (1) THE CONSENSUAL VIRTUALIZED PAST — both co-inhabitants fork the SAME config. ──
    // The umem branch IS the virtualized past: a cap-bounded cull projected to the universal
    // address space, recorded at the config's `minted_height`.
    let base = UmemBranch::mint(&world, room, 3);
    let past_height = base.minted_height;
    assert!(
        !base.umem.is_empty(),
        "the virtualized past captured the in-view subgraph"
    );
    eprintln!(
        "  · virtualized past minted at height {past_height}: {} addresses in the cull",
        base.umem.len()
    );

    // CONFINEMENT (anti-amplification by omission): the cap-bounded cull does NOT reach the
    // offstage cell — it cannot ride the branch.
    assert!(
        !base.umem.keys().any(|k| k.cell() == Some(offstage)),
        "the virtualized past is confined: offstage is structurally absent (no amplification)"
    );
    eprintln!("  · confinement: offstage cell is NOT in the cap-bounded virtualized past ✓");

    // CONFINEMENT (the no-drain tooth): a branch turn that tries to mutate `offstage` — a cell
    // ada holds NO cap to — is REFUSED by the executor. Its side-effect stays imaginary.
    let mut imaginary_fork = world.fork();
    let drain_attempt = imaginary_fork
        .commit_turn(imaginary_fork.turn(ada, vec![set_field(offstage, 0, [0x66; 32])]));
    assert!(
        !drain_attempt.is_committed(),
        "a branch turn cannot drain a main cell it holds no cap to (branch_cannot_drain_main)"
    );
    eprintln!("  · no-drain: ada's branch cannot touch offstage — the side-effect is imaginary ✓");

    // ── (2) THE DRIVE — two independent instances, real verified turns. ──────────────────
    const ADA_BOARD: [u8; 32] = [0xAA; 32];
    const BORIS_BOARD: [u8; 32] = [0xBB; 32];
    const ADA_DOC: [u8; 32] = [0x11; 32];
    const BORIS_DOC: [u8; 32] = [0x22; 32];

    let board_f0 = UKey::Field {
        cell: board,
        slot: 0,
    };
    let doc_ada_f0 = UKey::Field {
        cell: doc_ada,
        slot: 0,
    };
    let doc_boris_f0 = UKey::Field {
        cell: doc_boris,
        slot: 0,
    };

    // Carry the branch over a serialization boundary (the "two instances"); each side
    // rehydrates an INDEPENDENT World from the wire bytes.
    let (base_bytes, base_root) = UmemEnvelope::seal(base.clone());
    let base_env = open_umem_envelope(&base_bytes, base_root).expect("the virtualized past opens");
    assert_eq!(
        base_env.branch.minted_height, past_height,
        "the carry preserves the past config"
    );

    let mut world_ada = world.fork();
    let mut world_boris = world.fork();

    assert!(
        world_ada
            .commit_turn(world_ada.turn(
                ada,
                vec![
                    set_field(board, 0, ADA_BOARD),
                    set_field(doc_ada, 0, ADA_DOC)
                ],
            ))
            .is_committed(),
        "ada drives a real verified turn on her instance"
    );
    assert!(
        world_boris
            .commit_turn(world_boris.turn(
                boris,
                vec![
                    set_field(board, 0, BORIS_BOARD),
                    set_field(doc_boris, 0, BORIS_DOC)
                ],
            ))
            .is_committed(),
        "boris drives a real verified turn on his instance"
    );
    // The two instances genuinely diverge on the shared board (a real same-field clash).
    assert_ne!(
        world_ada.ledger().get(&board).unwrap().state.fields[0],
        world_boris.ledger().get(&board).unwrap().state.fields[0],
        "the two instances genuinely diverge on board"
    );
    eprintln!("  · two instances drove real turns; they diverge on board.field[0] (AA vs BB)");

    // ── (3) THE REVOCATION — between branch and settlement, on MAIN. ─────────────────────
    // ada's branch was built while she HELD the gift cap; she revokes it before the stitch
    // settles. Authority is non-monotone: the branch-time view said "held", the tip says "gone".
    let held_at_branch = settlement_held_at_tip(&world, ada);
    assert!(
        held_at_branch.iter().any(|c| c.target == gift),
        "at branch time ada held the gift cap"
    );
    let gift_slot = world
        .ledger()
        .get(&ada)
        .unwrap()
        .capabilities
        .iter()
        .find(|c| c.target == gift)
        .map(|c| c.slot)
        .expect("ada's gift cap slot");
    assert!(
        world
            .commit_turn(world.turn(ada, vec![revoke_capability(ada, gift_slot)]))
            .is_committed(),
        "ada revokes her own gift cap with a real verified turn (the non-monotone op)"
    );
    let settlement_held = settlement_held_at_tip(&world, ada); // the SETTLEMENT-TIP view.
    assert!(
        !settlement_held.iter().any(|c| c.target == gift),
        "at the settlement tip the gift cap is GONE (revoked between branch and tip)"
    );
    assert!(
        settlement_held.iter().any(|c| c.target == doc_ada),
        "ada still holds her doc cap at the tip"
    );
    eprintln!("  · ada revoked her gift cap on MAIN — the settlement-tip authority view changed");

    // ── (4) THE SETTLEMENT-SOUND STITCH — pushout-correct + authority at the tip. ────────
    let proj_ada = UmemBranch::mint(&world_ada, base.focus, base.max_depth);
    let (ada_bytes, ada_root) = UmemEnvelope::seal(proj_ada);
    let env_ada = open_umem_envelope(&ada_bytes, ada_root).expect("ada's driven projection opens");
    // The field-granular STATE pushout: ada's carried branch folded against boris's live fork.
    let state_stitch = stitch_umem_forks(&base, &env_ada, &world_boris);

    // ada's branch claims to confer back TWO caps: `gift` (held at branch, REVOKED at tip) and
    // `doc_ada` (still held at the tip). The gate reads the SETTLEMENT-TIP view.
    let conferred = vec![
        ConferredCap {
            target: gift,
            debit_reach: true,
        },
        ConferredCap {
            target: doc_ada,
            debit_reach: true,
        },
    ];
    let settled = settle_umem_stitch(state_stitch, &conferred, &settlement_held);

    // (4a) PUSHOUT-CORRECT (state, orthogonal to the gate): disjoint edits folded clean;
    //      the board clash is held fail-closed (no settled root until resolved).
    assert_eq!(
        settled.stitch.merged.get(&doc_ada_f0),
        Some(&UVal::Bytes32(ADA_DOC)),
        "ada's disjoint doc edit folded clean (pushout leg)"
    );
    assert_eq!(
        settled.stitch.merged.get(&doc_boris_f0),
        Some(&UVal::Bytes32(BORIS_DOC)),
        "boris's disjoint doc edit folded clean (pushout leg)"
    );
    let board_conflict = settled
        .stitch
        .conflicts
        .iter()
        .find(|c| c.key == board_f0)
        .expect("the same-field board clash is a held conflict");
    assert_eq!(
        board_conflict.a,
        Some(UVal::Bytes32(ADA_BOARD)),
        "ada's board reading lives"
    );
    assert_eq!(
        board_conflict.b,
        Some(UVal::Bytes32(BORIS_BOARD)),
        "boris's board reading lives"
    );
    assert!(
        !settled.settles(),
        "an unresolved field clash does NOT settle (fail-closed)"
    );
    assert!(
        settled.settled_root().is_none(),
        "no settled root pending resolution"
    );

    // (4b) SETTLEMENT-SOUND (authority at the tip): the revoked-before-tip gift confer is
    //      LINEAR-DROPPED; the still-held doc_ada confer is admitted (the gate is non-vacuous).
    assert_eq!(
        settled.dropped,
        vec![ConferredCap {
            target: gift,
            debit_reach: true
        }],
        "the revoked-before-tip gift cap is LINEAR-DROPPED — it cannot ride the stitch into main"
    );
    assert_eq!(
        settled.admitted,
        vec![ConferredCap {
            target: doc_ada,
            debit_reach: true
        }],
        "the cap still held at the settlement tip is admitted"
    );
    eprintln!(
        "  · settlement-sound: gift cap DROPPED (revoked@tip), doc_ada cap admitted (held@tip) ✓"
    );

    // (4c) The DROP is below — never conjured: the dropped cap appears in neither the admitted
    //      set nor (it being authority, not state) the merged state. Pushout-correct on both axes.
    assert!(
        !settled.admitted.iter().any(|c| c.target == gift),
        "the dropped gift authority is NOT conjured into the admitted set"
    );

    // ── COUNTERFACTUAL (the gate is not always-drop): had ada NOT revoked, gift would ride. ─
    let settled_counterfactual = settle_umem_stitch(
        settled.stitch.clone(),
        &conferred,
        &held_at_branch, // the branch-time view, where gift WAS held
    );
    assert!(
        settled_counterfactual
            .admitted
            .iter()
            .any(|c| c.target == gift),
        "against the branch-time view the gift cap rides — so the DROP is caused by the revocation, \
         not a blanket refusal (the gate reads authority at the settlement tip)"
    );
    eprintln!(
        "  · counterfactual: against the branch-time view gift WOULD ride — the drop is the revoke ✓"
    );

    // ── RESOLVE the state conflict explicitly — both readings were live (linear-forced). ──
    let mut resolved = settled;
    assert!(
        resolved
            .stitch
            .resolve(&board_f0, Some(UVal::Bytes32(BORIS_BOARD))),
        "the conflict is resolvable (the loser was never silently dropped)"
    );
    assert!(resolved.settles(), "resolved — the state pushout settles");
    assert!(
        resolved.settled_root().is_some(),
        "a settled stitch has a binding root"
    );
    assert_eq!(
        resolved.stitch.merged.get(&board_f0),
        Some(&UVal::Bytes32(BORIS_BOARD)),
        "the CHOSEN board reading folds in (explicit choice, not silent LWW)"
    );
    // The authority verdict is unchanged by the state resolution — orthogonal axes.
    assert!(
        resolved.dropped.iter().any(|c| c.target == gift),
        "the revoked authority stays dropped after the state conflict is resolved"
    );
    eprintln!(
        "=== state settled by explicit choice; revoked authority stayed dropped (settlement-sound) ===\n"
    );
}
