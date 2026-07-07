//! **The card-fork carry bridge** — where a portable card-fork envelope meets the
//! Matrix membrane wire, and where the anti-substitution tooth fires on receipt.
//!
//! Pillar 3 of distributed deos wants a co-driven card's fork-envelope to cross a
//! LIVE homeserver between two RUNNING cockpit processes, so two principals co-drive
//! ONE card and the stitch lands on both. Two halves already exist, each proven on
//! its own:
//!
//!   * [`crate::distributed_card`] — a [`CardForkEnvelope`] made portable
//!     ([`seal_fork`](crate::distributed_card::seal_fork) → sealed bytes + a
//!     domain-separated blake3 `fork_root`), with the anti-substitution root tooth
//!     ([`open_envelope`](crate::distributed_card::open_envelope)) that REFUSES a
//!     substituted/forged envelope before a byte is trusted, then
//!     [`rehydrate_fork`](crate::distributed_card::rehydrate_fork) +
//!     [`stitch_with_fork`](crate::distributed_card::stitch_with_fork) (the
//!     `dregg_doc` pushout). But its bytes only ever crossed an in-process boundary.
//!   * [`deos_matrix::card_carry`] — the byte-only Matrix vehicle: it wraps the
//!     sealed bytes + claimed root into a
//!     [`deos_matrix::MembraneEnvelope`](deos_matrix::MembraneEnvelope) that rides the
//!     homeserver-proven membrane wire path. But deos-matrix never links the card
//!     type, so it cannot fire the tooth — it only CARRIES the tooth's two inputs.
//!
//! This bridge joins them, and it is the ONLY place the tooth re-fires over the wire:
//!   * [`seal_card_fork_to_membrane`] — an originator seals its driven card-fork and
//!     wraps it into a card-carry `MembraneEnvelope` (hand to
//!     [`MatrixClient::send_membrane`](deos_matrix::MatrixClient::send_membrane) /
//!     [`deos_matrix::send_card_fork`]).
//!   * [`open_card_fork_from_membrane`] — a recipient pulls the carried bytes + root
//!     OFF the wire and re-runs [`open_envelope`](crate::distributed_card::open_envelope):
//!     the decoded envelope MUST reproduce the carried `fork_root`, else the carry is
//!     REFUSED ([`CardCarryError::Card`]`(`[`RootMismatch`](crate::distributed_card::DistributedCardError::RootMismatch)`)`).
//!     The wire is never trusted — acceptance is re-decided here, on the executor side.
//!   * [`rehydrate_card_fork_from_membrane`] — open (tooth) then rehydrate the
//!     recipient's OWN live cap-bounded fork over the carried seed, ready to drive +
//!     stitch by the same `dregg_doc` pushout.
//!
//! Gated on `agent-js` (the card machinery: `deos-js` + `dregg-doc`) AND
//! `dev-surfaces` (the `deos-matrix` wire types). gpui-free + `cargo test`-able.

use deos_js::card_editor::Author;
use deos_js::{CardFork, SharedCard};
use dregg_cell::AuthRequired;

use deos_matrix::MembraneEnvelope;

use crate::distributed_card::{self, CardForkEnvelope, DistributedCardError};

/// **Seal a driven card-fork and wrap it into a card-carry membrane** — the
/// originator's send half. Drives nothing itself: the caller drives its fork first
/// ([`deos_js::drive_view`]), then hands the live fork here. Returns the
/// [`MembraneEnvelope`] to ship over a room (via
/// [`deos_matrix::send_card_fork`] / [`MatrixClient::send_membrane`](deos_matrix::MatrixClient::send_membrane)).
///
/// This never re-implements the seal: it IS
/// [`distributed_card::seal_fork`](crate::distributed_card::seal_fork) (the sealed
/// bytes + the claimed `fork_root`) wrapped by
/// [`deos_matrix::card_fork_membrane`] (the byte-only vehicle). Both tooth inputs
/// ride together, unchanged, so the recipient can re-check them.
pub fn seal_card_fork_to_membrane(
    card: &SharedCard,
    fork: &CardFork,
    edit_authority: AuthRequired,
) -> MembraneEnvelope {
    let (bytes, root) = distributed_card::seal_fork(card, fork, edit_authority);
    deos_matrix::card_fork_membrane(&bytes, root)
}

/// **Open a received card-carry membrane, fail-closed — the tooth re-fires here.**
///
/// Routes the envelope to the card path (its `sturdyref` must bear
/// [`deos_matrix::CARD_FORK_STURDYREF_PREFIX`], else [`CardCarryError::NotACardCarry`]),
/// recovers the carried sealed bytes + claimed `fork_root`, and re-runs the REAL
/// anti-substitution tooth [`distributed_card::open_envelope`](crate::distributed_card::open_envelope):
/// the decoded [`CardForkEnvelope`] MUST reproduce the carried root, else the carry
/// is REFUSED. Never trusts the wire — a substituted/forged carry cannot pass.
pub fn open_card_fork_from_membrane(
    env: &MembraneEnvelope,
) -> Result<CardForkEnvelope, CardCarryError> {
    let (bytes, root) =
        deos_matrix::as_card_fork_carry(env).ok_or(CardCarryError::NotACardCarry)?;
    // THE TOOTH: re-derive fork_root from the decoded envelope and refuse a mismatch.
    Ok(distributed_card::open_envelope(&bytes, root)?)
}

/// **Rehydrate the recipient's OWN live card-fork from a received card-carry
/// membrane.** Opens (the tooth fires first), then hands principal `b_who` a fresh
/// live [`CardFork`] over the carried seed — bounded by `b_held` (the cap tooth in
/// deos-js). Returns `(rebuilt_card, b_fork)` for the recipient to drive
/// ([`deos_js::drive_view`]) and stitch
/// ([`distributed_card::stitch_with_fork`](crate::distributed_card::stitch_with_fork)).
pub fn rehydrate_card_fork_from_membrane(
    env: &MembraneEnvelope,
    b_who: Author,
    b_held: AuthRequired,
) -> Result<(SharedCard, CardFork), CardCarryError> {
    let (bytes, root) =
        deos_matrix::as_card_fork_carry(env).ok_or(CardCarryError::NotACardCarry)?;
    let card_env = distributed_card::open_envelope(&bytes, root)?; // tooth
    Ok(distributed_card::rehydrate_fork(
        &card_env, root, b_who, b_held,
    )?)
}

/// Errors the card-carry bridge raises (fail-closed paths). `Display`/`Error` are
/// hand-written (matching [`crate::distributed_card`]'s discipline) so the bridge
/// compiles under the lean executor build with no macro dep.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CardCarryError {
    /// The membrane is not a card-fork carry (no `dregg://card-fork/` sturdyref, or
    /// an unsupported wire version) — route it elsewhere, do not half-interpret it.
    NotACardCarry,
    /// The carried card-fork was refused by [`crate::distributed_card`] — the
    /// anti-substitution root tooth fired ([`DistributedCardError::RootMismatch`]), the
    /// bytes were malformed, or an authoring cap was unmet. The wire is never trusted.
    Card(DistributedCardError),
}

impl From<DistributedCardError> for CardCarryError {
    fn from(e: DistributedCardError) -> Self {
        CardCarryError::Card(e)
    }
}

impl std::fmt::Display for CardCarryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CardCarryError::NotACardCarry => write!(
                f,
                "membrane is not a card-fork carry (wrong sturdyref scheme or wire version)"
            ),
            CardCarryError::Card(e) => write!(f, "card-fork carry refused: {e}"),
        }
    }
}

impl std::error::Error for CardCarryError {}

#[cfg(test)]
mod tests {
    use super::*;
    use deos_js::coauthored_card::drive_view;
    use deos_js::ViewPatch;

    const ALICE: Author = Author(0xA);
    const BOB: Author = Author(0xB);

    fn authority() -> AuthRequired {
        AuthRequired::None
    }

    /// A drives a relabel and seals its fork into a card-carry membrane.
    fn originate_membrane() -> (MembraneEnvelope, CardForkEnvelope) {
        let card = SharedCard::seed(authority());
        let mut a = card.fork_for(ALICE, authority());
        drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice's counter".into(),
            },
        )
        .expect("A authorized");
        let membrane = seal_card_fork_to_membrane(&card, &a, authority());
        let expected = CardForkEnvelope::of(&card, &a, authority());
        (membrane, expected)
    }

    #[test]
    fn card_fork_round_trips_through_the_membrane_wire_and_the_tooth_admits_it() {
        let (membrane, expected) = originate_membrane();

        // It IS a card carry (the deos-matrix routing sees the sturdyref scheme).
        assert!(deos_matrix::is_card_fork_carry(&membrane));

        // It survives the SAME JSON the `m.room.message` custom field carries on the
        // wire — the leg a real homeserver relays verbatim.
        let json = serde_json::to_string(&membrane).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(
            membrane, back,
            "the card carry survives the wire byte-intact"
        );

        // The tooth ADMITS the genuine carry and recovers EXACTLY the sealed envelope
        // (CardForkEnvelope → MembraneEnvelope → bytes → CardForkEnvelope identity).
        let opened =
            open_card_fork_from_membrane(&back).expect("the tooth admits the genuine carry");
        assert_eq!(
            opened, expected,
            "the carried card-fork envelope round-trips identity through the wire"
        );

        // And the full distributed stitch lands: B rehydrates over the carried seed,
        // drives a DISJOINT edit, and the pushout keeps BOTH edits (co-drive, not LWW).
        let (b_card, mut b_fork) =
            rehydrate_card_fork_from_membrane(&back, BOB, authority()).expect("B rehydrates");
        drive_view(
            &mut b_fork,
            ViewPatch::AddButton {
                label: "increment".into(),
                turn: "inc".into(),
                arg: 1,
            },
        )
        .expect("B authorized");
        let stitch = distributed_card::stitch_with_fork(&opened, &b_card, &b_fork);
        assert!(
            !stitch.has_conflict(),
            "disjoint co-drives fold clean over the wire"
        );
        let merged = stitch.marked();
        assert!(
            merged.contains("alice's counter"),
            "A's carried edit survives: {merged}"
        );
        assert!(
            merged.contains("increment") || merged.contains("\"inc\""),
            "B's rehydrated edit survives: {merged}"
        );
    }

    #[test]
    fn a_forged_card_carry_is_refused_by_the_root_tooth() {
        let (mut membrane, _expected) = originate_membrane();

        // SUBSTITUTION: decode the carried card-fork, tamper its driven view, re-pack
        // the snapshot WITHOUT updating the carried root (the classic forgery). The
        // wire preserves both inputs (deos-matrix does not heal them), so the tooth
        // here sees bytes↔root disagree and REFUSES — fail-closed.
        let (bytes, _root) = deos_matrix::as_card_fork_carry(&membrane).expect("card carry");
        let mut tampered = CardForkEnvelope::from_snapshot_bytes(&bytes).expect("decodes");
        tampered
            .driven_view_source
            .push_str("\n<<bob's sneaky injected node>>");
        membrane.snapshot = tampered.to_snapshot_bytes(); // frustum_root left stale

        // Survive the wire, then re-open: the tooth must fire RootMismatch.
        let json = serde_json::to_string(&membrane).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(
            open_card_fork_from_membrane(&back),
            Err(CardCarryError::Card(DistributedCardError::RootMismatch)),
            "a forged card carry is REFUSED by the anti-substitution root tooth over the wire"
        );
        // And a rehydrate of the same forged carry is refused identically.
        assert!(matches!(
            rehydrate_card_fork_from_membrane(&back, BOB, authority()),
            Err(CardCarryError::Card(DistributedCardError::RootMismatch))
        ));
    }

    #[test]
    fn garbage_card_carry_bytes_are_refused_fail_closed() {
        // A card-carry-tagged membrane whose payload is not a valid envelope: the
        // decode fails and the carry is refused (MalformedEnvelope), never half-trusted.
        let membrane =
            deos_matrix::card_fork_membrane(b"\xff\x00 not a postcard envelope", [7u8; 32]);
        assert_eq!(
            open_card_fork_from_membrane(&membrane),
            Err(CardCarryError::Card(
                DistributedCardError::MalformedEnvelope
            ))
        );
    }

    #[test]
    fn a_world_fork_membrane_is_not_a_card_carry() {
        // A genuine world-fork membrane must not be routed to the card path.
        let world = deos_matrix::MockMembraneHost::sample_envelope();
        assert_eq!(
            open_card_fork_from_membrane(&world),
            Err(CardCarryError::NotACardCarry)
        );
    }

    // ---- THE ONE-PROCESS FULL LOOP OVER A REAL HOMESERVER --------------------
    // Two live Matrix sessions in THIS process (two `MatrixWorker`s, separate
    // clients/devices/stores) co-drive ONE card whose fork-envelopes CROSS a real
    // Conduit server, and the `dregg_doc` stitch lands on BOTH — with the root tooth
    // refusing a forged carry over the wire. Mirrors `shared_fork`'s
    // `full_loop_one_process_real_executor_over_real_matrix` (the world-fork twin) and
    // is gated identically: creds-gated on the two-user env quintet, no-op without it
    // (CI stays green). Run it via `scripts/live-test.sh` with `CARD_LOOP=1`.

    #[cfg(not(target_family = "wasm"))]
    fn live_two_user() -> Option<(String, String, String, String, String)> {
        Some((
            std::env::var("DEOS_MATRIX_TEST_HS").ok()?,
            std::env::var("DEOS_MATRIX_TEST_USER").ok()?,
            std::env::var("DEOS_MATRIX_TEST_PASS").ok()?,
            std::env::var("DEOS_MATRIX_TEST_USER_B").ok()?,
            std::env::var("DEOS_MATRIX_TEST_PASS_B").ok()?,
        ))
    }

    #[cfg(not(target_family = "wasm"))]
    fn tmp_store(tag: &str) -> std::path::PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!(
            "starbridge-card-loop-{tag}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        p
    }

    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn full_loop_card_fork_over_real_matrix() {
        use deos_matrix::worker::MatrixWorker;

        let Some((hs, user_a, pass_a, user_b, pass_b)) = live_two_user() else {
            eprintln!(
                "DEOS_MATRIX_TEST_HS/_USER/_PASS/_USER_B/_PASS_B not set — skipping the \
                 one-process card-fork FULL loop (seal→real Matrix A→B→open(tooth)→rehydrate→\
                 drive→stitch, both ways, + forged-refusal). Run it via the live harness: from \
                 starbridge-v2, homeserver up + env quintet set, \
                 `cargo test --no-default-features --features \"agent-js dev-surfaces\" --lib \
                  full_loop_card_fork -- --nocapture`."
            );
            return;
        };

        // (A) A seeds the shared card, forks, and drives a RELABEL — then seals its
        //     driven fork into a card-carry membrane + keeps its own CardForkEnvelope.
        let card = SharedCard::seed(authority());
        let mut a_fork = card.fork_for(ALICE, authority());
        drive_view(
            &mut a_fork,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice's counter".into(),
            },
        )
        .expect("A authorized");
        let membrane_a = seal_card_fork_to_membrane(&card, &a_fork, authority());
        let a_env = CardForkEnvelope::of(&card, &a_fork, authority());

        // Two live workers — genuinely separate clients/devices/stores.
        let (a, _a_thread) = MatrixWorker::spawn().expect("spawn worker A");
        let (b, _b_thread) = MatrixWorker::spawn().expect("spawn worker B");
        a.login_password(
            hs.clone(),
            tmp_store("A"),
            "live-cardA-pass".into(),
            user_a.clone(),
            pass_a,
            "starbridge-card-A".into(),
        )
        .expect("A logs in");
        b.login_password(
            hs.clone(),
            tmp_store("B"),
            "live-cardB-pass".into(),
            user_b.clone(),
            pass_b,
            "starbridge-card-B".into(),
        )
        .expect("B logs in");
        let uid_b = b.whoami().expect("B has a user id");

        // (A→B WIRE) A creates the shared room + invites B; B accepts.
        let room_id = a
            .create_room(
                Some("deos card loop".into()),
                Some("the live co-driven card".into()),
                vec![uid_b.clone()],
            )
            .expect("A creates the room + invites B");
        let mut joined = false;
        for _ in 0..20 {
            b.sync_once().expect("B sync for invite");
            if b.invited_rooms()
                .map(|v| v.iter().any(|r| r.room_id == room_id))
                .unwrap_or(false)
            {
                b.accept_invite(room_id.clone()).expect("B accepts");
                joined = true;
                break;
            }
            if b.joined_rooms()
                .map(|v| v.iter().any(|r| r.room_id == room_id))
                .unwrap_or(false)
            {
                joined = true;
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(400));
        }
        assert!(joined, "B never saw/accepted the invite");
        b.sync_once().expect("B sync after join");

        // Receive-until helper over the sync worker.
        let recv_until = |w: &deos_matrix::worker::MatrixHandle, id: &str| {
            for _ in 0..25 {
                w.sync_once().expect("sync for carry");
                let tl = w.recent_timeline(room_id.clone(), 100).expect("timeline");
                if let Some(m) = tl.into_iter().find(|m| m.event_id == id) {
                    return m;
                }
                std::thread::sleep(std::time::Duration::from_millis(400));
            }
            panic!("carry never arrived over the real server");
        };

        // (A→B) A ships its card-fork carry over the REAL homeserver.
        let carry_id = a
            .send_membrane(room_id.clone(), String::new(), membrane_a.clone())
            .expect("A ships the card-fork carry A→B");
        let got = recv_until(&b, &carry_id);
        let wire_a = got
            .membrane
            .clone()
            .expect("B extracts the carry off the wire");

        // (B OPENS — the tooth re-fires on the RECEIVED bytes) and rehydrates its own
        // live cap-bounded fork over the carried seed.
        let opened_a =
            open_card_fork_from_membrane(&wire_a).expect("B's tooth admits the genuine carry");
        assert_eq!(
            opened_a, a_env,
            "A's carried envelope survived A→B byte-intact + tooth-verified"
        );
        let (b_card, mut b_fork) = rehydrate_card_fork_from_membrane(&wire_a, BOB, authority())
            .expect("B rehydrates its own live fork");
        // (B DRIVES) a DISJOINT edit on its own view document.
        drive_view(
            &mut b_fork,
            ViewPatch::AddButton {
                label: "increment".into(),
                turn: "inc".into(),
                arg: 1,
            },
        )
        .expect("B authorized");
        let membrane_b = seal_card_fork_to_membrane(&b_card, &b_fork, authority());
        let b_env = CardForkEnvelope::of(&b_card, &b_fork, authority());

        // (B→A) B ships ITS driven fork back over the REAL server.
        let carry_id_b = b
            .send_membrane(room_id.clone(), String::new(), membrane_b)
            .expect("B ships its driven carry B→A");
        let got_b = recv_until(&a, &carry_id_b);
        let wire_b = got_b
            .membrane
            .clone()
            .expect("A extracts B's carry off the wire");
        let opened_b = open_card_fork_from_membrane(&wire_b).expect("A's tooth admits B's carry");
        assert_eq!(
            opened_b, b_env,
            "B's carried envelope survived B→A byte-intact + tooth-verified"
        );

        // (STITCH — both edits survive on BOTH sides.)
        let on_a = distributed_card::stitch_envelopes(&a_env, &opened_b);
        assert!(!on_a.has_conflict(), "disjoint co-drives fold clean on A");
        let on_a_marked = on_a.marked();
        assert!(
            on_a_marked.contains("alice's counter"),
            "A's edit on A: {on_a_marked}"
        );
        assert!(
            on_a_marked.contains("increment") || on_a_marked.contains("\"inc\""),
            "B's edit on A: {on_a_marked}"
        );

        let on_b = distributed_card::stitch_with_fork(&opened_a, &b_card, &b_fork);
        assert!(!on_b.has_conflict(), "disjoint co-drives fold clean on B");
        let on_b_marked = on_b.marked();
        assert!(
            on_b_marked.contains("alice's counter"),
            "A's edit on B: {on_b_marked}"
        );
        assert!(
            on_b_marked.contains("increment") || on_b_marked.contains("\"inc\""),
            "B's edit on B: {on_b_marked}"
        );

        // (FORGED — over the real wire, refused by the root tooth.) A ships a carry
        // whose payload is substituted but whose claimed root is stale; B's tooth fires.
        let mut forged = seal_card_fork_to_membrane(&card, &a_fork, authority());
        let (fbytes, _fr) = deos_matrix::as_card_fork_carry(&forged).expect("card carry");
        let mut tampered = CardForkEnvelope::from_snapshot_bytes(&fbytes).expect("decodes");
        tampered.driven_view_source.push_str("\n<<forged node>>");
        forged.snapshot = tampered.to_snapshot_bytes(); // root left stale
        let forged_id = a
            .send_membrane(room_id.clone(), String::new(), forged)
            .expect("A ships the forged carry");
        let got_forged = recv_until(&b, &forged_id);
        let wire_forged = got_forged
            .membrane
            .clone()
            .expect("B extracts the forged carry");
        assert_eq!(
            open_card_fork_from_membrane(&wire_forged),
            Err(CardCarryError::Card(DistributedCardError::RootMismatch)),
            "the forged carry is REFUSED by the anti-substitution root tooth over the real server"
        );

        eprintln!(
            "LIVE OK (card loop): two sessions co-drove ONE card over {hs}; A's and B's \
             fork-envelopes crossed the real server, the tooth verified each, the stitch kept \
             BOTH edits on BOTH sides, and a forged carry was refused."
        );
    }
}
