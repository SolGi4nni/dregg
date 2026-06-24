//! **FORK / CONSENT — the membrane's shared-fork tiers, made visible + actionable.**
//!
//! Hyperdreggmedia authoring surface #4 (`docs/deos/HYPERDREGGMEDIA-NOTES.md` §6):
//! "show EMBEDDED/STUDYREF/NETWORKBOUNDARY tiers + a consent inbox (pending
//! ConditionalTurns, upgrade requests). Multiplayer you can *see*."
//!
//! When you hand someone a fork of your world ([`crate::shared_fork::SharedFork`]),
//! their authority is graduated into three tiers. This module is the **trusted-UI
//! face** of that fork — the gpui-free logic core the cockpit's FORK/CONSENT surface
//! renders:
//!
//! * **[`fork_tiers`]** — what each participant HOLDS: one [`TierHolding`] per
//!   designated target, naming its tier (EMBEDDED / STUDYREF / NETWORKBOUNDARY) and
//!   the exact attenuated cap behind it. The membrane's authority typing, surfaced as
//!   rows.
//! * **[`ConsentInbox`]** — the pending [`dregg_turn::ConditionalTurn`]s a guest's
//!   boundary exercises raised, each awaiting MY consent. A real inbox of real
//!   conditional turns (the [`crate::shared_fork::ConsentRequest`]s carried back over
//!   the chat lane), each one a turn that does NOTHING until I [`approve`]
//!   it — or expires if I [`deny`].
//! * **[`approve`] / [`deny`]** — every grant/deny a REAL
//!   verified turn. APPROVE runs the owner's powerbox grant
//!   ([`crate::shared_fork::SharedFork::resolve_consent`]) — the signed receipt is the
//!   [`crate::shared_fork::ConsentWitness`] that opens the boundary gate — then COMMITS
//!   the pending conditional turn through [`crate::shared_fork::SharedFork::commit_turn_gated`]
//!   (the boundary fires exactly once, the nullifier prevents replay). DENY refuses:
//!   the boundary did NOT fire, nothing reached the owner's real world (fail-closed).
//! * **[`request_upgrade`] / [`grant_upgrade`]** — the STUDYREF→write-cap upgrade: a
//!   read-only holder ASKS for write authority over the cell it can currently only
//!   inspect ([`crate::shared_fork::StudyRef::upgrade_request`]), and the owner GRANTS
//!   it as a real powerbox grant (attenuating, never amplifying — an over-amplifying
//!   upgrade is REFUSED, the cap tooth).
//!
//! This reinvents NONE of the membrane machinery. It is a thin face over
//! [`crate::shared_fork`] (the three tiers + the real grant/consent path),
//! [`crate::powerbox`] (the grant ceremony + the upgrade grant), and
//! [`dregg_cell_crypto::ReadCap`] (the studyref). Every grant/deny is the SAME verified
//! turn the cockpit-free flow already proves — so a stranger across the planet can check
//! a consent receipt without trusting the UI.
//!
//! gpui-free + `cargo test`-able: the tier rows are read off a real constructed
//! [`crate::shared_fork::SharedFork`], an approve is a real signed grant + a real
//! committed conditional turn, a deny runs no turn, and an upgrade is a real attenuated
//! grant whose over-amplifying form is refused — the whole FORK/CONSENT face proven
//! without a GPU.

use std::collections::HashSet;

use dregg_cell::{AuthRequired, CapabilityRef, CellId};
use dregg_turn::conditional::ConditionalTurn;
use dregg_turn::turn::Turn;

use crate::powerbox::{CapabilityRequest, Powerbox, PowerboxOutcome};
use crate::reflect;
use crate::shared_fork::{
    ConsentRequest, ConsentWitness, EmbeddedCap, GatedCommit, NetworkBoundary, SharedFork, StudyRef,
};
use crate::world::World;

/// **Which tier a participant's holding sits in** — the three graduated-consent tiers
/// of [`crate::shared_fork::SharedFork`], as a flat label the UI renders.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tier {
    /// A real cap fully granted into the guest's fork c-list — exercised LOCALLY, no
    /// consent. Carries the conferred authority (`≤` what the owner held).
    Embedded { conferred: AuthRequired },
    /// A read/STUDY-only reference — the guest can inspect the exposed slots but holds
    /// NO write cap; exercise needs an upgrade request. Carries the slot-set (the
    /// read-lattice mask) the guest may open.
    StudyRef { slots: u16 },
    /// A consent-gated boundary — NO cap rides into the guest's c-list; an exercise
    /// opens a consent request. Carries the ceiling the owner's consent could confer.
    NetworkBoundary { ceiling: AuthRequired },
}

impl Tier {
    /// The short trusted-UI name of the tier ("EMBEDDED" / "STUDYREF" /
    /// "NETWORKBOUNDARY") — what the FORK/CONSENT surface labels the row.
    pub fn name(&self) -> &'static str {
        match self {
            Tier::Embedded { .. } => "EMBEDDED",
            Tier::StudyRef { .. } => "STUDYREF",
            Tier::NetworkBoundary { .. } => "NETWORKBOUNDARY",
        }
    }
}

/// **One row of the FORK/CONSENT tier view** — what the guest HOLDS over one target:
/// the target cell, its tier, and (for EMBEDDED) the exact attenuated cap behind it.
///
/// Built by [`fork_tiers`] off a real constructed [`SharedFork`]. The membrane's
/// authority typing, one row per designated target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TierHolding {
    /// The cell this holding designates.
    pub target: CellId,
    /// Which tier the holding sits in (+ its tier-specific authority/lattice data).
    pub tier: Tier,
    /// The exact attenuated cap minted into the guest's c-list — present ONLY for an
    /// EMBEDDED holding (STUDYREF / NETWORKBOUNDARY mint no write cap into the fork).
    pub embedded_cap: Option<CapabilityRef>,
}

impl TierHolding {
    /// The trusted-UI line for this row — the tier name + the target + the held
    /// authority. What the FORK/CONSENT surface renders per holding.
    pub fn label(&self) -> String {
        match &self.tier {
            Tier::Embedded { conferred } => format!(
                "EMBEDDED · {} → holds {:?} (exercised locally, no consent)",
                reflect::short_hex(&self.target.0),
                conferred
            ),
            Tier::StudyRef { slots } => format!(
                "STUDYREF · {} → read-only over slots {:#06x} (exercise = upgrade request)",
                reflect::short_hex(&self.target.0),
                slots
            ),
            Tier::NetworkBoundary { ceiling } => format!(
                "NETWORKBOUNDARY · {} → consent-gated up to {:?} (exercise = consent request)",
                reflect::short_hex(&self.target.0),
                ceiling
            ),
        }
    }
}

/// **What each participant holds — the tier view of a shared fork.**
///
/// Reads a constructed [`SharedFork`] and projects every designated target into a
/// [`TierHolding`], in a stable order (EMBEDDED, then STUDYREF, then NETWORKBOUNDARY).
/// A guest that holds an EMBEDDED cap exercises it locally; a STUDYREF holder can only
/// inspect (exercise = upgrade request); a NETWORKBOUNDARY holder must raise a consent
/// request. The rows ARE the membrane's authority typing — what the guest got, made
/// visible, attenuation-faithful (an EMBEDDED cap carries exactly the rights the
/// powerbox minted, never wider).
pub fn fork_tiers(fork: &SharedFork) -> Vec<TierHolding> {
    let mut out = Vec::with_capacity(
        fork.embedded.len() + fork.studyrefs.len() + fork.boundaries.len(),
    );
    for EmbeddedCap { target, cap } in &fork.embedded {
        out.push(TierHolding {
            target: *target,
            tier: Tier::Embedded {
                conferred: cap.permissions.clone(),
            },
            embedded_cap: Some(cap.clone()),
        });
    }
    for StudyRef { target, read_cap } in &fork.studyrefs {
        out.push(TierHolding {
            target: *target,
            tier: Tier::StudyRef {
                slots: read_cap.slots.0,
            },
            embedded_cap: None,
        });
    }
    for NetworkBoundary { target, ceiling } in &fork.boundaries {
        out.push(TierHolding {
            target: *target,
            tier: Tier::NetworkBoundary {
                ceiling: ceiling.clone(),
            },
            embedded_cap: None,
        });
    }
    out
}

/// **One pending item in the consent inbox** — a guest's boundary exercise awaiting MY
/// consent. Wraps the real [`ConsentRequest`] (the pending [`ConditionalTurn`] gated on
/// the owner's grant) the chat lane carried back. Sits here, doing nothing, until the
/// owner [`approve`]s it (commits the turn) or [`deny`]s it
/// (lets it expire, fail-closed).
#[derive(Clone, Debug)]
pub struct PendingConsent {
    /// The real consent request raised by the guest's boundary exercise.
    pub request: ConsentRequest,
}

impl PendingConsent {
    /// The guest principal whose boundary exercise raised this.
    pub fn guest(&self) -> CellId {
        self.request.guest
    }
    /// The real/network cell the guest wants to elaborate to.
    pub fn target(&self) -> CellId {
        self.request.target
    }
    /// The pending, consent-gated turn (does nothing until resolved).
    pub fn pending_turn(&self) -> &ConditionalTurn {
        &self.request.pending
    }
    /// The trusted-UI line for this pending item — who asks, for what, up to what.
    pub fn label(&self) -> String {
        format!(
            "PENDING CONSENT · guest {} wants to elaborate to {} (up to {:?}) — expires at height {}",
            reflect::short_hex(&self.request.guest.0),
            reflect::short_hex(&self.request.target.0),
            self.request.ceiling,
            self.request.pending.timeout_height,
        )
    }
}

/// The outcome of resolving a consent inbox item — every branch a real verdict.
#[derive(Debug)]
pub enum ConsentResolution {
    /// The owner APPROVED: the consent grant ran (a signed receipt), the pending
    /// conditional turn COMMITTED through the boundary gate, and the boundary fired
    /// exactly once. Carries the gated commit (the executor's verdict + the fired
    /// boundary).
    Approved { commit: GatedCommit },
    /// The owner DENIED, or the approve path refused (an over-amplifying consent, an
    /// unheld target, an expired request, or the gate rejecting the turn). Fail-closed:
    /// the boundary did NOT fire, nothing reached the owner's real world.
    Refused { reason: String },
}

impl ConsentResolution {
    /// Did the approve actually commit the pending turn on the fork?
    pub fn is_approved(&self) -> bool {
        matches!(self, ConsentResolution::Approved { commit } if commit.is_committed())
    }
    /// Was the resolution a refusal (a deny, or a fail-closed approve)?
    pub fn is_refused(&self) -> bool {
        matches!(self, ConsentResolution::Refused { .. })
    }
}

/// **THE CONSENT INBOX — pending boundary exercises awaiting the owner's consent.**
///
/// The trusted-UI face of the membrane's consent flow: every guest boundary exercise
/// that was refused fail-closed (no consent witness yet) parks its [`ConsentRequest`]
/// here as a [`PendingConsent`]. The owner walks the inbox and, per item, runs a REAL
/// verified turn — [`approve`] (the consent grant + the committed
/// conditional turn) or [`deny`] (refuse, no effect).
///
/// The inbox owns NO authority — it is a pure list of requests + the resolution
/// machinery delegating straight to [`SharedFork`]. gpui-free; the cockpit renders one
/// row per [`PendingConsent`] with approve/deny buttons.
#[derive(Clone, Debug, Default)]
pub struct ConsentInbox {
    /// The pending consent requests awaiting the owner's verdict, in arrival order.
    pub pending: Vec<PendingConsent>,
}

impl ConsentInbox {
    /// An empty inbox.
    pub fn new() -> Self {
        ConsentInbox {
            pending: Vec::new(),
        }
    }

    /// Park a guest's [`ConsentRequest`] (raised by a fail-closed boundary exercise) in
    /// the inbox, awaiting the owner's consent.
    pub fn push(&mut self, request: ConsentRequest) {
        self.pending.push(PendingConsent { request });
    }

    /// Is the inbox empty (no pending consents)?
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty()
    }

    /// The trusted-UI lines the inbox renders — one per pending consent.
    pub fn all_text(&self) -> Vec<String> {
        let mut out = vec![format!(
            "CONSENT INBOX — {} pending boundary exercise(s) awaiting your consent:",
            self.pending.len()
        )];
        for p in &self.pending {
            out.push(format!("· {}", p.label()));
        }
        if self.pending.is_empty() {
            out.push("(no pending consents)".to_string());
        }
        out
    }
}

/// **APPROVE a pending consent — every grant a REAL verified turn.**
///
/// The owner consents to `pending`'s boundary exercise. Two real verified turns, in
/// order:
///   1. The CONSENT GRANT: [`SharedFork::resolve_consent`] runs the owner's powerbox
///      grant over the LIVE `world` (the two gates + executor backstop fire); its signed
///      receipt is the [`ConsentWitness`]. An over-amplifying / unheld / expired grant
///      is DENIED here — and `approve` refuses, fail-closed (the boundary never fired).
///   2. The CONDITIONAL-TURN COMMIT: with the witness in hand,
///      [`SharedFork::commit_turn_gated`] re-verifies the witness at the boundary gate
///      (binding + authenticity + one-shot) and commits the pending turn on the `fork`.
///      The boundary fires EXACTLY once (the nullifier prevents replay).
///
/// `confer_rights` is the authority the owner consents to confer (treated as a ceiling,
/// `≤` what the owner holds — the consent attenuates, never amplifies).
/// `trusted_executor_keys` verify the witness signature (pass
/// `&[world.executor_public_key()?]`). `current_height` is the live height the timeout +
/// gate are checked against. `owner_used` is the OWNER world's persistent nullifier set;
/// `fork_used` is the FORK's own one-shot ledger. They are DISTINCT one-shot ledgers (the
/// resolve records into `owner_used`, the gate re-verifies + records into `fork_used`) —
/// passing one set to both would make the gate reject the witness as already-used. The
/// boundary fires exactly once per ledger.
///
/// NOTE: the consent grant elaborates on the OWNER's live `world`; the consented turn
/// commits on the guest's `fork`. They are distinct worlds (the membrane seam), so the
/// caller passes both. The boundary's own ceiling drives the gate's hole-fill; pass a
/// `confer_rights` `≤` it (the gate's own grant re-checks non-amplification too).
#[allow(clippy::too_many_arguments)]
pub fn approve(
    fork: &SharedFork,
    world: &mut World,
    fork_world: &mut World,
    owner: CellId,
    pending: &PendingConsent,
    confer_rights: AuthRequired,
    trusted_executor_keys: &[[u8; 32]],
    current_height: u64,
    owner_used: &mut HashSet<[u8; 32]>,
    fork_used: &mut HashSet<[u8; 32]>,
) -> ConsentResolution {
    // (1) THE CONSENT GRANT — a real powerbox grant over the owner's live world. Its
    //     signed receipt is the witness. A refusal (over-amplify / unheld / expired)
    //     denies the consent, fail-closed (the boundary never fires). The nullifier is
    //     recorded into the OWNER's one-shot ledger.
    let outcome = SharedFork::resolve_consent(
        world,
        owner,
        &pending.request,
        confer_rights,
        trusted_executor_keys,
        current_height,
        owner_used,
    );
    let timeout = pending.request.pending.timeout_height;
    let witness = match ConsentWitness::from_outcome(pending.request.target, timeout, outcome) {
        Some(w) => w,
        None => {
            return ConsentResolution::Refused {
                reason: "consent grant denied (over-amplifying, unheld, or expired) — the boundary did not fire (fail-closed)".to_string(),
            };
        }
    };

    // (2) THE CONDITIONAL-TURN COMMIT — the witness opens the boundary gate ONCE; the
    //     pending turn commits on the fork. The gate re-verifies binding + authenticity
    //     + one-shot against the FORK's OWN nullifier ledger (`fork_used`, distinct from
    //     the owner's), and its own hole-fill grant re-checks non-amplification.
    let commit = fork.commit_turn_gated(
        fork_world,
        owner,
        pending.request.pending.turn.clone(),
        Some(&witness),
        trusted_executor_keys,
        current_height,
        fork_used,
    );
    match &commit {
        GatedCommit::Committed { .. } => ConsentResolution::Approved { commit },
        GatedCommit::Refused { reason, .. } => ConsentResolution::Refused {
            reason: format!("consent valid but the gated commit refused: {reason}"),
        },
    }
}

/// **DENY a pending consent — refuse, no effect (fail-closed).**
///
/// The owner declines `pending`'s boundary exercise. NO grant runs, NO turn commits:
/// the pending conditional turn simply never resolves and expires at its
/// `timeout_height` (the fail-closed default). Nothing reaches the owner's real world.
/// Returns a [`ConsentResolution::Refused`] naming the denial — the same shape an
/// over-amplifying approve produces, so the UI handles both uniformly.
pub fn deny(pending: &PendingConsent) -> ConsentResolution {
    ConsentResolution::Refused {
        reason: format!(
            "owner DENIED the boundary exercise of {} by guest {} — no grant, no turn, fail-closed (the pending turn expires at height {})",
            reflect::short_hex(&pending.request.target.0),
            reflect::short_hex(&pending.request.guest.0),
            pending.request.pending.timeout_height,
        ),
    }
}

/// **REQUEST an upgrade — a STUDYREF holder asks for a write cap.**
///
/// The guest holds only a read-only [`StudyRef`] over a cell; to MUTATE it, it must
/// ask. This is exactly [`StudyRef::upgrade_request`]: a [`CapabilityRequest`] for WRITE
/// authority over the cell the guest can currently only inspect, routed to the owner
/// like any powerbox request. `guest` is the requesting principal; `desired` is the
/// write authority it would like (a ceiling the owner may grant or less).
pub fn request_upgrade(
    studyref: &StudyRef,
    guest: CellId,
    desired: AuthRequired,
) -> CapabilityRequest {
    studyref.upgrade_request(guest, desired)
}

/// **GRANT an upgrade — the STUDYREF→write-cap promotion as a real grant turn.**
///
/// The owner promotes a STUDYREF holder to an EMBEDDED write cap over `target` — a REAL
/// [`Powerbox::grant`] over the owner's live `world`. The two real gates fire:
/// `mint_needs_held_factory` (the owner must hold a cap reaching `target`) and
/// `gen_conferral_is_attenuation` (`confer_rights ⊆ held` — the cap tooth). An
/// OVER-AMPLIFYING upgrade (conferring wider than the owner holds) is REFUSED here,
/// before any turn — the guest cannot be promoted past the owner's own authority.
///
/// On success the guest's c-list gains exactly one write cap: `target`, narrowed to
/// `confer_rights` — the STUDYREF is now an EMBEDDED holding (read became write, but only
/// up to the owner's ceiling). Returns the real [`PowerboxOutcome`] (the executor's own
/// receipt + the conferred cap, or the denial).
pub fn grant_upgrade(
    world: &mut World,
    owner: CellId,
    guest: CellId,
    target: CellId,
    confer_rights: AuthRequired,
) -> PowerboxOutcome {
    Powerbox::grant(world, owner, guest, target, confer_rights)
}

/// Build the guest's intended boundary-exercise turn raised as a consent request, for
/// the inbox flow. A small convenience: shape the guest's `intended` turn into a
/// [`ConsentRequest`] gated on the owner's grant of `boundary.target` (the same
/// [`NetworkBoundary::consent_request`] the fork gate emits), bound to the SPECIFIC
/// grant turn the owner would run (so a stray receipt cannot fire it).
///
/// `owner` + `world` are used only to PREDICT the owner's grant turn hash (via
/// [`Powerbox::grant_turn`] — the one shared constructor `resolve_consent` commits), so
/// the consent binds to exactly that grant. No turn is run here.
#[allow(clippy::too_many_arguments)]
pub fn raise_consent(
    boundary: &NetworkBoundary,
    world: &World,
    owner: CellId,
    guest: CellId,
    intended: Turn,
    confer_rights: AuthRequired,
    submitted_at: u64,
    timeout_height: u64,
) -> ConsentRequest {
    let grant_turn = Powerbox::grant_turn(world, owner, guest, boundary.target, confer_rights);
    boundary.consent_request(
        guest,
        intended,
        grant_turn.hash(),
        submitted_at,
        timeout_height,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::make_open_cell;
    use dregg_cell_crypto::ReadCap;

    /// A signed fork world tailored to the FORK/CONSENT surface: an OWNER holding two
    /// resources (`docs` at full `None`, `peer` at narrowed `Signature` — distinct
    /// ceilings so the attenuation lattice is a real witness), a confined `guest`, and a
    /// `boundary_target` the owner holds (`peer`) the guest may only reach via consent.
    /// Returns `(world, owner, guest, docs, peer, exec_seed)`.
    fn fc_world() -> (World, CellId, CellId, CellId, CellId, [u8; 32]) {
        let exec_seed = [0x42u8; 32];
        let mut w = World::new().with_executor_signing_key(exec_seed);
        let docs = w.genesis_cell(0xD0, 0);
        let peer = w.genesis_cell(0xBE, 0);
        let guest = w.genesis_cell(0xA9, 0);
        let mut owner_cell = make_open_cell(0x55, 0);
        owner_cell
            .capabilities
            .grant(docs, AuthRequired::None)
            .expect("owner holds docs");
        owner_cell
            .capabilities
            .grant(peer, AuthRequired::Signature)
            .expect("owner holds peer");
        let owner = w.genesis_install(owner_cell);
        (w, owner, guest, docs, peer, exec_seed)
    }

    /// Build a shared fork with all three tiers: an EMBEDDED grant of `docs`, a STUDYREF
    /// over a `study` cell, and a NETWORKBOUNDARY over `peer`. Returns the fork + the
    /// constructed fork-world (for the consent commit) alongside the live owner world.
    #[test]
    fn fork_tiers_shows_what_each_participant_holds() {
        let (mut world, owner, guest, docs, peer, _seed) = fc_world();
        let study = world.genesis_cell(0x57, 0);
        let view_key = dregg_cell_crypto::ViewKey::from_root([7u8; 32]);
        let study_ref = StudyRef {
            target: study,
            read_cap: ReadCap::new(study, dregg_cell_crypto::FieldSet::single(0), view_key),
        };

        let mut fork = world.fork();
        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            // EMBEDDED: grant docs at an ATTENUATED Signature (owner holds None).
            &[(docs, AuthRequired::Signature)],
            // STUDYREF: a read-only ref over `study`.
            vec![study_ref],
            // NETWORKBOUNDARY: consent-gated peer, ceiling = the owner's Signature.
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );

        let rows = fork_tiers(&sf);
        assert_eq!(rows.len(), 3, "one row per designated target across all tiers");

        // EMBEDDED: docs, holds the ATTENUATED Signature (never the owner's wider None).
        let emb = rows
            .iter()
            .find(|r| matches!(r.tier, Tier::Embedded { .. }))
            .expect("an embedded row");
        assert_eq!(emb.target, docs);
        assert_eq!(
            emb.tier,
            Tier::Embedded {
                conferred: AuthRequired::Signature
            },
            "the embedded holding carries the attenuated cap, not the owner's wider authority"
        );
        let cap = emb.embedded_cap.as_ref().expect("embedded carries the real cap");
        assert_eq!(cap.target, docs);
        assert_eq!(
            cap.permissions,
            AuthRequired::Signature,
            "the held cap is the executor-minted attenuated one"
        );

        // STUDYREF: study, read-only over slot 0, NO write cap.
        let study_row = rows
            .iter()
            .find(|r| matches!(r.tier, Tier::StudyRef { .. }))
            .expect("a studyref row");
        assert_eq!(study_row.target, study);
        assert_eq!(study_row.tier, Tier::StudyRef { slots: 0b1 });
        assert!(
            study_row.embedded_cap.is_none(),
            "a studyref holds NO write cap into the fork"
        );

        // NETWORKBOUNDARY: peer, ceiling Signature, NO cap into the fork.
        let bnd = rows
            .iter()
            .find(|r| matches!(r.tier, Tier::NetworkBoundary { .. }))
            .expect("a networkboundary row");
        assert_eq!(bnd.target, peer);
        assert_eq!(
            bnd.tier,
            Tier::NetworkBoundary {
                ceiling: AuthRequired::Signature
            }
        );
        assert!(
            bnd.embedded_cap.is_none(),
            "a networkboundary mints no cap into the fork (exercise = consent)"
        );
    }

    #[test]
    fn a_conditional_turn_sits_in_the_inbox_until_approve_commits_it() {
        // THE CONSENT INBOX FLOW: a guest's boundary exercise parks a pending
        // ConditionalTurn in the inbox; it does NOTHING until the owner APPROVES, which
        // runs a REAL consent grant (signed receipt) and COMMITS the conditional turn
        // through the boundary gate (a real verified turn, fired once).
        let (mut world, owner, guest, _docs, peer, _seed) = fc_world();
        let exec_pub = world.executor_public_key().expect("the world signs receipts");

        // The fork carries the consent-gated boundary over `peer`.
        let mut fork_world = world.fork();
        let sf = SharedFork::construct(
            &mut fork_world,
            owner,
            guest,
            &[],
            vec![],
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );

        // The guest's intended boundary exercise — a turn touching `peer`. We shape it
        // into a consent request bound to the SPECIFIC grant the owner would run.
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let boundary = &sf.boundaries[0];
        let request = raise_consent(
            boundary,
            &world,
            owner,
            guest,
            intended,
            AuthRequired::Signature,
            0,
            100,
        );

        // It sits in the inbox, doing nothing.
        let mut inbox = ConsentInbox::new();
        inbox.push(request);
        assert_eq!(inbox.pending.len(), 1, "the conditional turn awaits consent");
        assert_eq!(inbox.pending[0].target(), peer);
        assert!(inbox.all_text().iter().any(|l| l.contains("PENDING CONSENT")));

        // APPROVE: a real consent grant + a real committed conditional turn. Two DISTINCT
        // one-shot ledgers (the owner's world + the fork's own).
        let mut owner_used: HashSet<[u8; 32]> = HashSet::new();
        let mut fork_used: HashSet<[u8; 32]> = HashSet::new();
        let receipts_before = world.receipts().len();
        let resolution = approve(
            &sf,
            &mut world,
            &mut fork_world,
            owner,
            &inbox.pending[0],
            AuthRequired::Signature,
            &[exec_pub],
            10,
            &mut owner_used,
            &mut fork_used,
        );
        assert!(
            resolution.is_approved(),
            "approve runs the consent grant AND commits the conditional turn: {resolution:?}"
        );
        assert_eq!(
            world.receipts().len(),
            receipts_before + 1,
            "the consent grant is a real verified turn on the owner's world"
        );
        if let ConsentResolution::Approved { commit } = &resolution {
            assert!(
                matches!(commit, GatedCommit::Committed { fired_boundary: Some(t), .. } if *t == peer),
                "the boundary fired exactly once: {commit:?}"
            );
        }
    }

    #[test]
    fn deny_refuses_the_boundary_with_no_effect() {
        // DENY: the owner declines. NO grant runs, NO turn commits — the pending turn
        // never resolves, nothing reaches the owner's real world (fail-closed).
        let (mut world, owner, guest, _docs, peer, _seed) = fc_world();
        let mut fork_world = world.fork();
        let sf = SharedFork::construct(
            &mut fork_world,
            owner,
            guest,
            &[],
            vec![],
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let request = raise_consent(
            &sf.boundaries[0],
            &world,
            owner,
            guest,
            intended,
            AuthRequired::Signature,
            0,
            100,
        );
        let mut inbox = ConsentInbox::new();
        inbox.push(request);

        let receipts_before = world.receipts().len();
        let resolution = deny(&inbox.pending[0]);
        assert!(resolution.is_refused(), "deny is a refusal");
        assert!(
            !resolution.is_approved(),
            "a denied consent commits no turn"
        );
        // Fail-closed: no turn ran on the owner's world.
        assert_eq!(
            world.receipts().len(),
            receipts_before,
            "a deny runs no grant turn — nothing reached the owner's real world"
        );
    }

    #[test]
    fn an_upgrade_request_then_grant_yields_a_wider_but_attenuated_cap() {
        // THE STUDYREF→WRITE UPGRADE: a read-only holder requests write authority; the
        // owner grants it as a REAL attenuated powerbox grant. The guest, which held no
        // write cap, now holds one — narrowed to the owner's ceiling (never wider).
        let (mut world, owner, guest, docs, _peer, _seed) = fc_world();

        // The guest holds a STUDYREF over `docs` (read-only). Precondition: no write cap.
        let view_key = dregg_cell_crypto::ViewKey::from_root([7u8; 32]);
        let study_ref = StudyRef {
            target: docs,
            read_cap: ReadCap::new(docs, dregg_cell_crypto::FieldSet::single(0), view_key),
        };
        assert!(
            !world
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&docs),
            "the studyref holder holds NO write cap to docs before the upgrade"
        );

        // REQUEST the upgrade: a real powerbox CapabilityRequest for WRITE over docs.
        let req = request_upgrade(&study_ref, guest, AuthRequired::Signature);
        assert_eq!(req.app_cell, guest);
        assert_eq!(req.desired_rights, AuthRequired::Signature);
        assert!(req.reason.contains("studyref upgrade"));

        // GRANT the upgrade at an attenuated Signature (owner holds docs at None).
        let receipts_before = world.receipts().len();
        let outcome = grant_upgrade(&mut world, owner, guest, docs, AuthRequired::Signature);
        let conferred = outcome
            .conferred()
            .expect("a held, attenuated upgrade grants")
            .clone();
        assert_eq!(conferred.target, docs);
        assert_eq!(
            conferred.conferred_rights,
            AuthRequired::Signature,
            "the upgrade is wider than read-only but ATTENUATED to the owner's ceiling"
        );
        assert_eq!(
            world.receipts().len(),
            receipts_before + 1,
            "the upgrade grant is a real verified turn"
        );
        // The guest now reaches docs with a write cap — the STUDYREF became EMBEDDED.
        let guest_cell = world.ledger().get(&guest).unwrap();
        assert!(
            guest_cell.capabilities.has_access(&docs),
            "the upgraded guest now holds a write cap to docs (studyref → embedded)"
        );
        let granted = guest_cell
            .capabilities
            .iter()
            .find(|c| c.target == docs)
            .expect("the granted upgrade cap is in the guest's c-list");
        assert_eq!(
            granted.permissions,
            AuthRequired::Signature,
            "the guest holds the ATTENUATED upgrade, never wider than the owner"
        );
    }

    #[test]
    fn an_over_amplifying_upgrade_is_refused() {
        // THE CAP TOOTH: the owner holds only Signature over `peer`. A studyref holder
        // requesting a WIDER None (full) write authority over peer is REFUSED — the
        // guest cannot be promoted past the owner's own authority (no amplification).
        let (mut world, owner, guest, _docs, peer, _seed) = fc_world();
        let receipts_before = world.receipts().len();

        // Over-amplifying: confer None where the owner holds only Signature.
        let outcome = grant_upgrade(&mut world, owner, guest, peer, AuthRequired::None);
        assert!(
            !outcome.is_granted(),
            "an over-amplifying upgrade must be refused (the cap tooth)"
        );
        match outcome {
            PowerboxOutcome::Denied { reason } => assert!(
                reason.contains("AMPLIFY") || reason.contains("attenuation"),
                "the denial cites amplification, got: {reason}"
            ),
            PowerboxOutcome::Granted { .. } => panic!("an over-amplifying upgrade must be denied"),
        }
        assert_eq!(
            world.receipts().len(),
            receipts_before,
            "a refused upgrade runs no turn"
        );
        assert!(
            !world
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&peer),
            "the guest gained no cap from the refused upgrade"
        );

        // But the LEGITIMATE upgrade (at or below the owner's Signature ceiling) grants.
        let ok = grant_upgrade(&mut world, owner, guest, peer, AuthRequired::Signature);
        assert!(
            ok.is_granted(),
            "an upgrade ⊆ the owner's held authority is a legitimate grant"
        );
    }
}
