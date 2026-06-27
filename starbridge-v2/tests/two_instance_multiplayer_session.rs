//! TWO CO-INHABITANTS, ONE WORLD — a real two-instance multiplayer deos session.
//!
//! This is the multiplayer leg made demonstrable end-to-end with ORDINARY cap-gated
//! turns (no GM self-grant superpower — every mutation is a real verified turn through
//! the embedded executor, exactly what `World::commit_turn` admits). Two distinct
//! principals — `ada` and `boris` — co-inhabit one shared world. Each is handed the
//! SAME cap-bounded membrane (`ForkMembraneHost::mint`), drives a real verified turn on
//! its OWN fork, and the two forks reconcile through the membrane's FIELD-GRANULAR umem
//! stitch:
//!
//!   * DISJOINT per-cell-field edits (Ada's own doc, Boris's own doc) both LAND — folded
//!     clean at their exact universal-memory addresses (the per-address win over the
//!     opaque cell-granular `Atom` merge, which would have collided each cell to one atom);
//!   * a SAME-FIELD clash (both write `board.field[0]` to different values) surfaces as a
//!     first-class `ConflictObject` keyed at the EXACT umem address (`ValueCollision`) —
//!     both attributed readings live, never a silent last-writer-wins — and the stitch
//!     does NOT settle until it is explicitly resolved (fail-closed).
//!
//! It proves this TWO WAYS and shows they AGREE:
//!   1. THE COORDINATED reconcile — the room host holds both co-inhabitants' driven forks
//!      and folds them with `ForkMembraneHost::stitch_pair` (the running comms-PD path).
//!   2. THE DISTRIBUTED reconcile — the membrane envelope crosses a serialization boundary
//!      (the "two instances"), each side rehydrates the wire bytes into an INDEPENDENT real
//!      `World`, drives its own verified turn, and the two are folded with
//!      `stitch_umem_forks`. The conflict address it names is byte-identical to (1)'s.
//!
//! Run (gpui-free, no GPU — the headless engine):
//!   cd starbridge-v2 && cargo test --no-default-features \
//!     --features "embedded-executor dev-surfaces" \
//!     --test two_instance_multiplayer_session -- --nocapture

#![cfg(all(feature = "dev-surfaces", feature = "embedded-executor"))]

use deos_matrix::membrane::{ConflictReason, FrustumCut, MembraneEnvelope, MembraneHost};
use dregg_cell::{AuthRequired, CellId};
use dregg_turn::umem::{UKey, UVal};

use starbridge_v2::shared_fork::{ForkMembraneHost, MembraneFrustum};
use starbridge_v2::umem_membrane::{
    open_umem_envelope, stitch_umem_forks, umem_event_id, UmemBranch, UmemEnvelope,
};
use starbridge_v2::world::{make_open_cell, set_field, World};

/// The shared world the two co-inhabitants live in — built with ORDINARY genesis grants
/// (a principal can only hold what it was granted; nobody self-grants). Returns the role
/// cells:
///   * `room`    — the focus the membrane culls around (reaches both co-inhabitants + the
///     board); the cap-bounded co-inhabited surface.
///   * `ada` / `boris` — two DISTINCT principals.
///   * `board`   — the shared surface both hold a cap over (the collision candidate).
///   * `doc_ada` / `doc_boris` — each co-inhabitant's own doc (the disjoint edits).
///   * `offstage`— a cell NO principal in the room subgraph reaches (the confinement foil:
///     it must NOT ride the cap-bounded membrane — anti-amplification by omission).
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
) {
    let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
    let board = w.genesis_cell(0x5D, 0);
    let doc_ada = w.genesis_cell(0xA1, 0);
    let doc_boris = w.genesis_cell(0xB2, 0);
    // Granted to nobody — never reachable from the room cull (the confinement foil).
    let offstage = w.genesis_cell(0xEE, 0);

    let mut ada = make_open_cell(0x0A, 0);
    ada.capabilities
        .grant(board, AuthRequired::None)
        .expect("ada holds the board");
    ada.capabilities
        .grant(doc_ada, AuthRequired::None)
        .expect("ada holds her doc");
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

    // The room reaches BOTH co-inhabitants + the shared board — ordinary grants, NOT a GM
    // self-grant. The membrane cull centred here captures exactly the co-inhabited surface.
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
        w, room_id, ada_id, boris_id, board, doc_ada, doc_boris, offstage,
    )
}

#[test]
fn two_co_inhabitants_sync_via_the_field_granular_membrane_stitch() {
    let (world, room, ada, boris, board, doc_ada, doc_boris, offstage) = shared_world();
    eprintln!("\n=== TWO-INSTANCE MULTIPLAYER deos: ada ⋈ boris over one shared world ===");
    eprintln!(
        "  room={:.8}  ada={:.8}  boris={:.8}  board={:.8}",
        hexk(&room),
        hexk(&ada),
        hexk(&boris),
        hexk(&board),
    );

    // ── THE MEMBRANE: the owner mints a cap-bounded cull of the co-inhabited surface. ──
    let owner_fork = world.fork();
    let host = ForkMembraneHost::new(owner_fork, room);
    let cut = FrustumCut {
        focus_cell: [0u8; 32],
        max_depth: 3,
        authority_bounded: true,
        cell_count: 0,
    };
    let env = host
        .mint(room.0, cut)
        .expect("the owner mints the membrane");
    eprintln!(
        "  · minted membrane: {} cells in view, root {:.8}",
        env.cut.cell_count,
        hex32k(&env.frustum_root)
    );

    // ANTI-AMPLIFICATION (confinement by omission): the membrane is cap-bounded, so the
    // `offstage` cell — reachable by NObody in the room subgraph — is structurally ABSENT.
    let frustum = MembraneFrustum::from_snapshot_bytes(&env.snapshot).expect("snapshot decodes");
    let in_view: std::collections::HashSet<CellId> = frustum.cells.iter().map(|c| c.id()).collect();
    for (label, id) in [
        ("room", room),
        ("ada", ada),
        ("boris", boris),
        ("board", board),
        ("doc_ada", doc_ada),
        ("doc_boris", doc_boris),
    ] {
        assert!(
            in_view.contains(&id),
            "the co-inhabited surface includes {label}"
        );
    }
    assert!(
        !in_view.contains(&offstage),
        "the cap-bounded membrane does NOT amplify to the offstage cell (confinement by omission)"
    );
    eprintln!("  · confinement: offstage cell is NOT in the cap-bounded cull ✓");

    // The carried payload IS a witnessed umem (its umem_root reproduces from the cells).
    let carried = UmemBranch::from_frustum(&frustum);
    assert_eq!(
        carried.umem_root(),
        frustum.umem_root(),
        "the carry is a witnessed umem — its boundary root the handoff"
    );

    // ── THE WIRE CROSSING (two instances): the envelope serializes, travels, rehydrates. ─
    let wire = serde_json::to_string(&env).expect("the membrane serializes to the wire");
    let env_wire: MembraneEnvelope =
        serde_json::from_str(&wire).expect("the membrane survives the wire");
    assert_eq!(env_wire, env, "byte-intact across the instance boundary");
    assert_eq!(
        env_wire.frustum_root, env.frustum_root,
        "anti-substitution root survived"
    );

    // The two co-inhabitants author IDENTICAL intents on both reconcile paths:
    //   · ada writes board.field[0] = AA  AND  her own doc_ada.field[0] = 11
    //   · boris writes board.field[0] = BB AND  his own doc_boris.field[0] = 22
    // They COLLIDE on board.field[0] (a real same-field clash) and edit DISJOINT private
    // fields. Each turn is an ORDINARY verified turn signed AS its own principal.
    const ADA_BOARD: [u8; 32] = [0xAA; 32];
    const BORIS_BOARD: [u8; 32] = [0xBB; 32];
    const ADA_DOC: [u8; 32] = [0x11; 32];
    const BORIS_DOC: [u8; 32] = [0x22; 32];

    // The three umem addresses at play (field-granular — the EXACT (cell, slot) keys).
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

    // =====================================================================================
    // PATH 1 — THE COORDINATED reconcile: the room host holds both driven forks and folds
    //          them with `stitch_pair` (the running comms-PD multiplayer leg).
    // =====================================================================================
    let (h_ada, _) = host.rehydrate(&env).expect("ada rehydrates her fork");
    let (h_boris, _) = host.rehydrate(&env).expect("boris rehydrates his fork");

    // Author a turn against a fresh rehydrate of the same frustum (identical chain head),
    // then drive it through the host's verified executor.
    let author = |who: CellId, ops: Vec<dregg_turn::action::Effect>| {
        let driver = frustum
            .rehydrate(env.frustum_root)
            .expect("driver rehydrates");
        postcard::to_stdvec(&driver.turn(who, ops)).expect("turn serializes")
    };
    host.drive(
        &h_ada,
        &author(
            ada,
            vec![
                set_field(board, 0, ADA_BOARD),
                set_field(doc_ada, 0, ADA_DOC),
            ],
        ),
    )
    .expect("ada drives a real verified turn on her fork");
    host.drive(
        &h_boris,
        &author(
            boris,
            vec![
                set_field(board, 0, BORIS_BOARD),
                set_field(doc_boris, 0, BORIS_DOC),
            ],
        ),
    )
    .expect("boris drives a real verified turn on his fork");

    let coordinated = host
        .stitch_pair(&h_ada, &h_boris)
        .expect("the room host stitches the two co-inhabitants' umems");

    // The same-field clash is ONE field-granular ValueCollision, named at its EXACT address.
    let board_event = umem_event_id(&board_f0);
    assert_eq!(
        coordinated.dropped.len(),
        1,
        "exactly one field-granular conflict (board.field[0]): {:?}",
        coordinated.dropped
    );
    assert_eq!(
        coordinated.dropped[0].event, board_event,
        "the conflict names the EXACT universal-memory address that diverged"
    );
    assert_eq!(
        coordinated.dropped[0].reason,
        ConflictReason::ValueCollision,
        "a same-field write collision is a first-class ValueCollision object"
    );
    assert!(
        coordinated.settled_root.is_none(),
        "an unresolved field collision does NOT settle (fail-closed)"
    );
    // The disjoint per-cell edits fold CLEAN — both co-inhabitants' private edits land.
    assert!(
        coordinated.merged.contains(&umem_event_id(&doc_ada_f0)),
        "ada's disjoint doc edit folded clean"
    );
    assert!(
        coordinated.merged.contains(&umem_event_id(&doc_boris_f0)),
        "boris's disjoint doc edit folded clean"
    );
    assert!(
        !coordinated.merged.contains(&board_event),
        "the conflicted address is held back from the clean-merged set"
    );
    eprintln!(
        "  · PATH 1 (stitch_pair): {} disjoint edits folded clean · 1 ValueCollision at board.field[0] {:.8} · unsettled",
        coordinated.merged.len(),
        hex32k(&board_event),
    );

    // =====================================================================================
    // PATH 2 — THE DISTRIBUTED reconcile: each co-inhabitant rehydrates the WIRE bytes into
    //          an INDEPENDENT real `World`, drives its own turn, and the two fold via
    //          `stitch_umem_forks`. (The genuinely two-instance leg — no shared host.)
    // =====================================================================================
    let frustum_wire =
        MembraneFrustum::from_snapshot_bytes(&env_wire.snapshot).expect("wire snapshot decodes");
    let base = UmemBranch::from_frustum(&frustum_wire);

    let mut world_ada = frustum_wire
        .rehydrate(env_wire.frustum_root)
        .expect("ada's instance rehydrates a real World");
    let mut world_boris = frustum_wire
        .rehydrate(env_wire.frustum_root)
        .expect("boris's instance rehydrates a real World");

    let ta = world_ada.turn(
        ada,
        vec![
            set_field(board, 0, ADA_BOARD),
            set_field(doc_ada, 0, ADA_DOC),
        ],
    );
    assert!(
        world_ada.commit_turn(ta).is_committed(),
        "ada commits a real verified turn on her own instance"
    );
    let tb = world_boris.turn(
        boris,
        vec![
            set_field(board, 0, BORIS_BOARD),
            set_field(doc_boris, 0, BORIS_DOC),
        ],
    );
    assert!(
        world_boris.commit_turn(tb).is_committed(),
        "boris commits a real verified turn on his own instance"
    );
    // The two instances genuinely diverge on the shared cell — a real conflict.
    assert_ne!(
        world_ada.ledger().get(&board).unwrap().state.fields[0],
        world_boris.ledger().get(&board).unwrap().state.fields[0],
        "the two instances genuinely diverge on board (a real same-field clash)"
    );

    // Ada's instance seals its driven projection for carry; Boris's instance folds it
    // against its own live driven fork (the distributed merge happens here).
    let proj_ada = UmemBranch::mint(&world_ada, base.focus, base.max_depth);
    let (ada_bytes, ada_root) = UmemEnvelope::seal(proj_ada);
    let env_ada = open_umem_envelope(&ada_bytes, ada_root).expect("ada's projection opens");
    let mut distributed = stitch_umem_forks(&base, &env_ada, &world_boris);

    // SAME conflict, field-granular — at the EXACT same address PATH 1 named.
    assert!(
        !distributed.is_clean(),
        "the same-field clash surfaces a conflict in the distributed reconcile too"
    );
    let conflict = distributed
        .conflicts
        .iter()
        .find(|c| c.key == board_f0)
        .expect("the conflict names board.field[0]");
    // BOTH attributed readings live — never a silent last-writer-wins.
    assert_eq!(
        conflict.a,
        Some(UVal::Bytes32(ADA_BOARD)),
        "ada's reading lives"
    );
    assert_eq!(
        conflict.b,
        Some(UVal::Bytes32(BORIS_BOARD)),
        "boris's reading lives"
    );
    // Pre-resolution, the merged map holds the baseline at the conflicted address.
    assert_eq!(
        distributed.merged.get(&board_f0).cloned(),
        base.umem.get(&board_f0).cloned(),
        "the conflicted address holds the baseline pending an explicit resolution"
    );
    // The disjoint private fields BOTH land clean.
    assert_eq!(
        distributed.merged.get(&doc_ada_f0),
        Some(&UVal::Bytes32(ADA_DOC)),
        "ada's disjoint doc edit kept"
    );
    assert_eq!(
        distributed.merged.get(&doc_boris_f0),
        Some(&UVal::Bytes32(BORIS_DOC)),
        "boris's disjoint doc edit kept — both fields of the subrealm merged"
    );

    // THE TWO PATHS AGREE: the coordinated `stitch_pair` and the distributed fold name the
    // IDENTICAL conflict address.
    assert_eq!(
        umem_event_id(&conflict.key),
        coordinated.dropped[0].event,
        "the coordinated and distributed reconciles name the SAME conflict address"
    );
    eprintln!(
        "  · PATH 2 (distributed, two Worlds): both disjoint edits kept · conflict at board.field[0] holds both readings (AA & BB)"
    );

    // ── THE CONFLICT IS HELD, NOT LOST — resolve it explicitly (linear-logic forced). ────
    assert!(
        distributed.resolve(&board_f0, Some(UVal::Bytes32(BORIS_BOARD))),
        "the conflict is resolvable (the loser was never silently dropped)"
    );
    assert!(
        distributed.is_clean(),
        "resolved — no live conflict remains"
    );
    assert_eq!(
        distributed.merged.get(&board_f0),
        Some(&UVal::Bytes32(BORIS_BOARD)),
        "the CHOSEN reading folds into the merged umem (an explicit choice, not silent LWW)"
    );
    eprintln!(
        "  · resolved board.field[0] := BB by explicit choice — both readings were live, the merge settles ✓"
    );
    eprintln!(
        "=== two co-inhabitants reconciled, field-granular, over ordinary verified turns ===\n"
    );
}

/// Short hex (first 4 bytes) of a cell id for the transcript.
fn hexk(id: &CellId) -> String {
    hex4(id.as_bytes())
}

/// Short hex (first 4 bytes) of a 32-byte root for the transcript.
fn hex32k(b: &[u8; 32]) -> String {
    hex4(b)
}

fn hex4(b: &[u8]) -> String {
    let mut s = String::with_capacity(8);
    for byte in &b[..4] {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}
