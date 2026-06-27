//! **Distributed multiplayer cards** — two principals on DIFFERENT instances
//! co-drive ONE shared card across a membrane boundary.
//!
//! The two halves this welds are each proven on their own:
//!
//! * **The local stitch** ([`deos_js::coauthored_card`]) — one shared card, two
//!   principals each take a [`deos_js::CardFork`], each drives a real receipted
//!   view-patch on its OWN `view_source` document, and the two divergent
//!   documents STITCH by the `dregg_doc` pushout (a clean merge keeps both edits;
//!   a true conflict is a first-class [`dregg_doc::ConflictRegion`] antichain,
//!   never a silent last-writer-wins). But both forks live in ONE process.
//! * **The membrane carry** ([`crate::shared_fork`]) — a real cap-bounded fork
//!   SERIALIZES, crosses an instance boundary (e.g. over Matrix), and REHYDRATES
//!   into a real `World` the recipient drives, with an anti-substitution
//!   [`crate::shared_fork::MembraneFrustum::frustum_root`] tooth (a substituted
//!   snapshot is refused fail-closed before a single byte is trusted). But it
//!   carries a `Cell` subgraph, not a card.
//!
//! This module JOINS them. A card-fork is made **portable** as a
//! [`CardForkEnvelope`] — the three serializable strings the stitch actually
//! consumes (the shared seed `view_source`, this principal's driven
//! `view_source`, and its blame author) plus the authoring authority. Principal A
//! drives its fork, [`seal_fork`]s it to envelope bytes + a claimed root, and the
//! envelope CROSSES THE BOUNDARY. Principal B (a different instance) [`open_envelope`]s
//! it (the anti-substitution root tooth fires fail-closed on a tampered/substituted
//! envelope), [`rehydrate_fork`]s its OWN live [`deos_js::CardFork`] over the carried
//! seed — bounded by B's `held`, the cap tooth — drives ITS view, and the two forks
//! STITCH by the same `dregg_doc` pushout ([`stitch_envelopes`]).
//!
//! So the full distributed loop is real end to end:
//!   A: seed → fork → drive → **seal**(serialize + root)  ─wire→  B: **open**(verify
//!   root) → **rehydrate** a live cap-bounded fork → drive → **stitch** (clean fold
//!   keeps both · an overlap surfaces a resolvable ConflictRegion · an unauthorized B
//!   contributes no patch — the cap tooth).
//!
//! It reinvents NONE of the machinery: the stitch IS [`deos_js::CardStitch::from_sources`]
//! (the `dregg_doc` pushout); the carry MIRRORS the membrane's three load-bearing
//! teeth (canonical-bytes serialization, a domain-separated blake3 root, fail-closed
//! rehydrate). gpui-free + `cargo test`-able under `--features "embedded-executor
//! agent-js"`.

use deos_js::card_editor::Author;
use deos_js::{CardFork, CardStitch, EditError, SharedCard};
use dregg_cell::AuthRequired;
use serde::{Deserialize, Serialize};

/// **A card-fork made portable — the card crossing an instance boundary.**
///
/// This is the membrane carry of a CARD (the twin of
/// [`crate::shared_fork::MembraneFrustum`], which carries a `Cell` subgraph). A
/// [`deos_js::CardFork`] itself is NOT serializable — it holds a live
/// [`deos_js::CardEditor`] over an `Applet` with closures. The envelope instead
/// carries exactly the serializable state the stitch consumes: the shared seed
/// prefix both forks branch from, this principal's driven view-source fold, its
/// blame author, and the authoring authority. From these, a recipient on another
/// instance reconstitutes its own fork and folds the merge faithfully.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CardForkEnvelope {
    /// The shared seed `view_source` — the common ancestor BOTH forks branch from.
    /// Carried so the receiver's stitch (and a rehydrated fork) re-root on EXACTLY
    /// these bytes (the real common prefix the `dregg_doc` pushout needs).
    pub seed_view_source: String,
    /// The authoring authority a fork's `held` must satisfy to author the card (the
    /// cap tooth). [`AuthRequired`] is serde; carried verbatim.
    pub edit_authority: AuthRequired,
    /// This principal's blame identity (`dregg_doc::Author(pub u64)`), carried as the
    /// raw `u64` (the type is not serde-derived, but it is just a `u64`).
    pub who: u64,
    /// This principal's DRIVEN view-source — the document fold after it edited its own
    /// fork. The branch the receiver's stitch folds in (or a rehydrated fork replays).
    pub driven_view_source: String,
}

impl CardForkEnvelope {
    /// Build a portable envelope from a live card-fork (the card's shared seed, this
    /// principal's driven view, its author + the authoring authority). The originator
    /// calls this (via [`seal_fork`]) to make its fork cross the boundary.
    pub fn of(card: &SharedCard, fork: &CardFork, edit_authority: AuthRequired) -> Self {
        CardForkEnvelope {
            seed_view_source: card.seed_view_source().to_string(),
            edit_authority,
            who: fork.who.0,
            driven_view_source: fork.view_source(),
        }
    }

    /// **The card-fork root — the anti-substitution tooth.** A domain-separated
    /// blake3 commitment over EXACTLY the carried fields (mirroring
    /// [`crate::shared_fork::MembraneFrustum::frustum_root`]), so a substituted or
    /// tampered envelope is refused before a single byte is trusted (fail-closed at
    /// [`open_envelope`] / [`rehydrate_fork`]). The authority is folded via its
    /// canonical postcard bytes (deterministic) rather than a `Hash` impl.
    pub fn fork_root(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"deos-distributed-card-fork-root-v1");
        for field in [&self.seed_view_source, &self.driven_view_source] {
            h.update(&(field.len() as u64).to_le_bytes());
            h.update(field.as_bytes());
        }
        h.update(&self.who.to_le_bytes());
        let auth = postcard::to_stdvec(&self.edit_authority)
            .expect("AuthRequired is postcard-serializable");
        h.update(&(auth.len() as u64).to_le_bytes());
        h.update(&auth);
        *h.finalize().as_bytes()
    }

    /// Serialize the envelope for the wire — postcard, the canonical codec
    /// (mirroring [`crate::shared_fork::MembraneFrustum::to_snapshot_bytes`]). These
    /// are the bytes that ride the membrane (e.g. a Matrix message's membrane field).
    pub fn to_snapshot_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("card-fork envelope is postcard-serializable")
    }

    /// Deserialize an envelope from wire bytes (fail-closed on a malformed payload).
    pub fn from_snapshot_bytes(bytes: &[u8]) -> Result<Self, DistributedCardError> {
        postcard::from_bytes(bytes).map_err(|_| DistributedCardError::MalformedEnvelope)
    }

    /// This envelope's principal as a [`deos_js::card_editor::Author`].
    pub fn author(&self) -> Author {
        Author(self.who)
    }
}

/// **A principal seals its driven card-fork for carry across the boundary.**
///
/// Returns the envelope's wire bytes AND its claimed [`CardForkEnvelope::fork_root`]
/// — the two things the originator hands the membrane: the recipient opens the bytes
/// and checks them against the root (the anti-substitution tooth). The originator
/// drives its fork first ([`deos_js::drive_view`]); this freezes the driven view into
/// the envelope.
pub fn seal_fork(
    card: &SharedCard,
    fork: &CardFork,
    edit_authority: AuthRequired,
) -> (Vec<u8>, [u8; 32]) {
    let env = CardForkEnvelope::of(card, fork, edit_authority);
    let root = env.fork_root();
    (env.to_snapshot_bytes(), root)
}

/// **A recipient opens a received card-fork envelope, fail-closed.**
///
/// Deserializes the wire bytes and fires the anti-substitution tooth: the decoded
/// envelope MUST reproduce the `expected_root` the originator claimed, else
/// [`DistributedCardError::RootMismatch`] (a tampered/substituted card is refused
/// before it is trusted). Malformed bytes are [`DistributedCardError::MalformedEnvelope`].
/// This mirrors [`crate::shared_fork::MembraneFrustum::rehydrate`]'s root check.
pub fn open_envelope(
    bytes: &[u8],
    expected_root: [u8; 32],
) -> Result<CardForkEnvelope, DistributedCardError> {
    let env = CardForkEnvelope::from_snapshot_bytes(bytes)?;
    if env.fork_root() != expected_root {
        return Err(DistributedCardError::RootMismatch);
    }
    Ok(env)
}

/// **Rehydrate a recipient's OWN live card-fork from a carried envelope.**
///
/// The full carry: rebuild the shared card from the envelope's carried seed +
/// authority ([`deos_js::SharedCard::seed_from_source`]), then hand principal
/// `b_who` a fresh live [`deos_js::CardFork`] over that SAME seed prefix — bounded by
/// `b_held` (the cap tooth: a principal whose `held` does not satisfy the card's
/// `edit_authority` may take the fork, but every view edit it attempts is refused
/// in-band, so it contributes no patch). The anti-substitution root tooth fires
/// fail-closed first.
///
/// The recipient then drives its returned fork ([`deos_js::drive_view`]) — a real
/// receipted patch on ITS view document — and stitches it against the originator's
/// envelope via [`stitch_envelopes`]. Returns `(rebuilt_card, b_fork)`: the card so
/// the recipient can [`deos_js::SharedCard::seed_view_source`] / re-fork; the fork to
/// drive.
pub fn rehydrate_fork(
    env: &CardForkEnvelope,
    expected_root: [u8; 32],
    b_who: Author,
    b_held: AuthRequired,
) -> Result<(SharedCard, CardFork), DistributedCardError> {
    // (a) Anti-substitution: the envelope MUST reproduce the claimed root.
    if env.fork_root() != expected_root {
        return Err(DistributedCardError::RootMismatch);
    }
    // (b) Rebuild the shared card from the CARRIED seed (not a fresh local seed) —
    //     so the receiver's fork branches from EXACTLY the originator's common
    //     ancestor, and the stitch re-roots faithfully.
    let card = SharedCard::seed_from_source(env.edit_authority.clone(), &env.seed_view_source);
    // (c) Hand the recipient principal its own live fork, bounded by ITS held (the
    //     cap tooth lives in deos-js's CardEditor; this layer never re-implements it).
    let fork = card.fork_for(b_who, b_held);
    Ok((card, fork))
}

/// **Stitch the originator's envelope against a recipient's live driven fork** by the
/// `dregg_doc` pushout — the distributed twin of [`deos_js::SharedCard::stitch`].
///
/// `a` is the carried envelope (the originator's driven view, off the wire); `b_card`
/// + `b_fork` are the recipient's rebuilt card and its OWN driven fork. Both re-root
///   on the SAME carried seed (the real common ancestor), so disjoint edits fold CLEAN
///   (both kept) and an overlapping edit (both touched the same node) surfaces a
///   first-class [`dregg_doc::ConflictRegion`] (both attributed alternatives live —
///   never a silent overwrite). An unauthorized recipient's `b_fork` never advanced past
///   the seed (its edits were refused in-band), so it contributes no patch.
pub fn stitch_with_fork(
    a: &CardForkEnvelope,
    _b_card: &SharedCard,
    b_fork: &CardFork,
) -> CardStitch {
    CardStitch::from_sources(
        &a.seed_view_source,
        a.author(),
        &a.driven_view_source,
        b_fork.who,
        &b_fork.view_source(),
    )
}

/// **Stitch two carried card-fork envelopes** by the `dregg_doc` pushout — the
/// string-only distributed stitch (when both sides carry their driven view over the
/// boundary and the merge happens at a third place, or when the recipient need not
/// hold a live fork).
///
/// Both envelopes MUST carry the SAME `seed_view_source` (the shared common ancestor);
/// the stitch re-roots both branches on it. Returns a genuine [`deos_js::CardStitch`]
/// (the SAME type the local [`deos_js::SharedCard::stitch`] produces): clean merge →
/// `!has_conflict()`, both edits kept; overlap → a resolvable conflict region.
pub fn stitch_envelopes(a: &CardForkEnvelope, b: &CardForkEnvelope) -> CardStitch {
    // Both branches re-root on the SHARED seed (the originator's). A faithful pairing
    // carries the same seed on both; the merge folds A's driven view against B's.
    CardStitch::from_sources(
        &a.seed_view_source,
        a.author(),
        &a.driven_view_source,
        b.author(),
        &b.driven_view_source,
    )
}

/// Errors the distributed card carry raises (the fail-closed paths — mirroring
/// [`crate::shared_fork::MembraneError`]). `Display`/`Error` are hand-written (no
/// macro dep) so the substrate compiles under the lean executor build.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributedCardError {
    /// The envelope bytes did not deserialize into a card-fork (corrupt/truncated wire
    /// payload) — fail-closed.
    MalformedEnvelope,
    /// The decoded envelope did not reproduce the claimed root — the anti-substitution
    /// tooth fired (refuse before trusting one byte).
    RootMismatch,
    /// The recipient principal's `held` does not satisfy the card's `edit_authority`:
    /// its drive was refused in-band by the cap tooth (no patch, no receipt). Surfaced
    /// from [`deos_js::EditError::Unauthorized`] for callers that drive through this
    /// layer.
    Unauthorized,
}

impl From<EditError> for DistributedCardError {
    fn from(e: EditError) -> Self {
        match e {
            EditError::Unauthorized => DistributedCardError::Unauthorized,
            // Any other authoring failure is not a carry error; surface it opaquely as
            // a malformed-edit (the distributed layer's drives are simple view-patches).
            _ => DistributedCardError::MalformedEnvelope,
        }
    }
}

impl std::fmt::Display for DistributedCardError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DistributedCardError::MalformedEnvelope => {
                write!(f, "card-fork envelope is malformed (not a valid envelope)")
            }
            DistributedCardError::RootMismatch => write!(
                f,
                "card-fork root mismatch — refusing to open a substituted card envelope"
            ),
            DistributedCardError::Unauthorized => write!(
                f,
                "the recipient's held authority does not satisfy the card's authoring cap (refused)"
            ),
        }
    }
}

impl std::error::Error for DistributedCardError {}

#[cfg(test)]
mod tests {
    use super::*;
    use deos_js::coauthored_card::drive_view;
    use deos_js::ViewPatch;

    /// The authoring authority the shared card requires (the broadest — `None`).
    fn authority() -> AuthRequired {
        AuthRequired::None
    }

    /// Principal A's identity; principal B's identity. Distinct authors → distinct
    /// blame, distinct sovereign cells, distinct instances.
    const ALICE: Author = Author(0xA);
    const BOB: Author = Author(0xB);

    /// The originator side: A seeds its card, takes its fork, drives `patch_a`, and
    /// SEALS the driven fork to envelope bytes + the claimed root (the card crossing
    /// the boundary). Returns `(bytes, root)`.
    fn originate(patch_a: ViewPatch) -> (Vec<u8>, [u8; 32]) {
        let card = SharedCard::seed(authority());
        let mut a = card.fork_for(ALICE, authority());
        drive_view(&mut a, patch_a).expect("A authorized to author the card");
        seal_fork(&card, &a, authority())
    }

    #[test]
    fn distributed_clean_merge_keeps_both_edits() {
        // ── A (instance 1): drive a RELABEL, then SEAL + carry across the boundary ──
        let (bytes, root) = originate(ViewPatch::Relabel {
            from: "shared counter".into(),
            to: "alice's counter".into(),
        });

        // ── B (instance 2): OPEN the envelope (the anti-substitution root tooth admits
        //    the genuine card), REHYDRATE B's OWN live fork over the carried seed, and
        //    drive a DISJOINT edit (add a button — a different node) on B's view doc. ──
        let env_a =
            open_envelope(&bytes, root).expect("the root tooth admits the genuine envelope");
        let (b_card, mut b_fork) = rehydrate_fork(&env_a, root, BOB, authority())
            .expect("B rehydrates a real live cap-bounded fork");
        let edit_b = drive_view(
            &mut b_fork,
            ViewPatch::AddButton {
                label: "increment".into(),
                turn: "inc".into(),
                arg: 1,
            },
        )
        .expect("B authorized to author its rehydrated fork");
        assert!(
            edit_b.tree.has_button_for("inc"),
            "B's rehydrated fork re-folded with the new button: {:?}",
            edit_b.tree
        );

        // ── STITCH across the boundary: A's carried envelope ⋈ B's live driven fork. ──
        let stitch = stitch_with_fork(&env_a, &b_card, &b_fork);
        assert!(
            !stitch.has_conflict(),
            "disjoint co-drives across instances fold CLEAN: {}",
            stitch.marked()
        );
        // BOTH principals' edits survive the cross-boundary merge (co-drive, not LWW).
        let merged = stitch.marked();
        assert!(
            merged.contains("alice's counter"),
            "A's relabel (carried over the boundary) kept in the stitched view: {merged}"
        );
        assert!(
            merged.contains("increment") || merged.contains("\"inc\""),
            "B's button (driven on its rehydrated fork) kept in the stitched view: {merged}"
        );
    }

    #[test]
    fn distributed_true_conflict_surfaces_a_resolvable_region() {
        // A drives a relabel of the title; carry it.
        let (bytes, root) = originate(ViewPatch::Relabel {
            from: "shared counter".into(),
            to: "alice's title".into(),
        });

        // B opens + rehydrates, then relabels the SAME node DIFFERENTLY (the canonical
        // overlapping edit) on its own instance.
        let env_a = open_envelope(&bytes, root).expect("genuine envelope opens");
        let (b_card, mut b_fork) =
            rehydrate_fork(&env_a, root, BOB, authority()).expect("B rehydrates a fork");
        drive_view(
            &mut b_fork,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "bob's title".into(),
            },
        )
        .expect("B authorized");

        // The collision is a FIRST-CLASS conflict region across the boundary — both
        // attributed alternatives survive (the loser is never hidden).
        let stitch = stitch_with_fork(&env_a, &b_card, &b_fork);
        assert!(
            stitch.has_conflict(),
            "two cross-instance edits to the SAME node MUST surface a conflict: {}",
            stitch.marked()
        );
        assert!(
            stitch.conflict_carries("alice's title"),
            "A's reading (carried) survives as a live alternative: {}",
            stitch.marked()
        );
        assert!(
            stitch.conflict_carries("bob's title"),
            "B's reading survives as a live alternative (loser never hidden): {}",
            stitch.marked()
        );
    }

    #[test]
    fn an_unauthorized_distributed_driver_contributes_no_patch_the_cap_tooth() {
        // A holds the required (broadest `None`) authority and drives a relabel; carry.
        let card = SharedCard::seed(AuthRequired::None);
        let mut a = card.fork_for(ALICE, AuthRequired::None);
        drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice owns this".into(),
            },
        )
        .expect("A holds the authoring authority");
        let (bytes, root) = seal_fork(&card, &a, AuthRequired::None);

        // B (another instance) opens + rehydrates a fork bounded by only the STRICTER
        // `Signature` authority — which does NOT satisfy the card's `None` authoring
        // cap, so every edit B attempts is refused in-band (no patch, no receipt).
        let env_a = open_envelope(&bytes, root).expect("genuine envelope opens");
        let (b_card, mut b_fork) = rehydrate_fork(&env_a, root, BOB, AuthRequired::Signature)
            .expect("B can take the fork (the refusal is per-edit, in-band)");
        let refused = drive_view(
            &mut b_fork,
            ViewPatch::AddButton {
                label: "sneak".into(),
                turn: "inc".into(),
                arg: 1,
            },
        );
        assert!(
            matches!(refused, Err(EditError::Unauthorized)),
            "the unauthorized cross-instance driver's edit is refused in-band by the cap tooth"
        );
        // B's rehydrated fork never advanced — its view is still the carried seed.
        assert_eq!(
            b_fork.view_source(),
            b_card.seed_view_source(),
            "the refused driver's view document never advanced past the carried seed"
        );

        // The stitch carries ONLY A's authorized reading — B contributed nothing.
        let stitch = stitch_with_fork(&env_a, &b_card, &b_fork);
        assert!(
            !stitch.has_conflict(),
            "no conflict — B contributed nothing: {}",
            stitch.marked()
        );
        assert!(
            stitch.marked().contains("alice owns this"),
            "only A's authorized edit is in the merged view: {}",
            stitch.marked()
        );
    }

    #[test]
    fn anti_substitution_root_tooth_fails_closed() {
        // A seals a genuine driven fork.
        let (bytes, root) = originate(ViewPatch::Relabel {
            from: "shared counter".into(),
            to: "alice's real title".into(),
        });

        // (1) GENUINE: the envelope opens and re-derives the claimed root byte-for-byte.
        let env = open_envelope(&bytes, root).expect("the genuine envelope opens");
        assert_eq!(
            env.fork_root(),
            root,
            "the carried envelope reproduces its root"
        );
        // Wire byte-identity: the envelope survives serialize → deserialize intact.
        assert_eq!(
            CardForkEnvelope::from_snapshot_bytes(&bytes).expect("round-trips"),
            env,
            "the card-fork envelope survives the wire byte-intact"
        );

        // (2) SUBSTITUTION: tamper the driven view WITHOUT updating the root. Opening
        //     against the original root MUST fail-closed (a substituted card is refused
        //     before a single byte is trusted) — the membrane's anti-substitution tooth.
        let mut tampered = env.clone();
        tampered
            .driven_view_source
            .push_str("\n<<bob's sneaky injected node>>");
        let tampered_bytes = tampered.to_snapshot_bytes();
        assert!(
            matches!(
                open_envelope(&tampered_bytes, root),
                Err(DistributedCardError::RootMismatch)
            ),
            "a substituted card envelope is REFUSED against the original root (fail-closed)"
        );
        // (Sanity: the tampered envelope DOES open against ITS OWN root — the tooth is a
        //  binding check, not a blanket reject; only the substitution-under-old-root fails.)
        assert!(
            open_envelope(&tampered_bytes, tampered.fork_root()).is_ok(),
            "the tooth binds bytes↔root, it is not a blanket reject"
        );

        // (3) MALFORMED: garbage bytes do not decode into an envelope (fail-closed).
        assert!(
            matches!(
                open_envelope(b"\xff\x00 not a postcard envelope at all", root),
                Err(DistributedCardError::MalformedEnvelope)
            ),
            "malformed wire bytes are refused (fail-closed)"
        );
    }

    #[test]
    fn string_only_envelope_stitch_matches_the_live_fork_stitch() {
        // The string-only path ([`stitch_envelopes`]) and the live-fork path
        // ([`stitch_with_fork`]) agree: both are the SAME `dregg_doc` pushout. A drives
        // a relabel; B drives a disjoint button. Carry BOTH as envelopes and stitch.
        let card_a = SharedCard::seed(authority());
        let mut a = card_a.fork_for(ALICE, authority());
        drive_view(
            &mut a,
            ViewPatch::Relabel {
                from: "shared counter".into(),
                to: "alice's counter".into(),
            },
        )
        .expect("A authorized");
        let (a_bytes, a_root) = seal_fork(&card_a, &a, authority());
        let env_a = open_envelope(&a_bytes, a_root).unwrap();

        // B rehydrates from A's envelope, drives a disjoint button, then seals ITS fork.
        let (b_card, mut b_fork) = rehydrate_fork(&env_a, a_root, BOB, authority()).unwrap();
        drive_view(
            &mut b_fork,
            ViewPatch::AddButton {
                label: "increment".into(),
                turn: "inc".into(),
                arg: 1,
            },
        )
        .expect("B authorized");
        let (b_bytes, b_root) = seal_fork(&b_card, &b_fork, authority());
        let env_b = open_envelope(&b_bytes, b_root).unwrap();

        // Both stitch routes keep both edits, no conflict.
        let via_envelopes = stitch_envelopes(&env_a, &env_b);
        let via_fork = stitch_with_fork(&env_a, &b_card, &b_fork);
        assert!(!via_envelopes.has_conflict() && !via_fork.has_conflict());
        for stitch in [&via_envelopes, &via_fork] {
            let merged = stitch.marked();
            assert!(
                merged.contains("alice's counter"),
                "A's edit kept: {merged}"
            );
            assert!(
                merged.contains("increment") || merged.contains("\"inc\""),
                "B's edit kept: {merged}"
            );
        }
    }
}
