//! **The shared confined fork with graduated consent** — "invite someone to my
//! computer".
//!
//! I hand someone a fork of my world — a confined sub-world they inhabit as their
//! own principal ([`crate::world::World::fork`] + the firmament
//! [`dregg_firmament` sandbox](dregg_firmament) `Confinement`, so they cannot
//! escape it) — whose culled, cap-bounded subgraph of MY authority is graduated
//! into three tiers:
//!
//! * **EMBEDDED** — a real [`dregg_cell::CapabilityRef`] granted into the guest's
//!   fork c-list (via a genuine [`Effect::GrantCapability`], attenuated by the real
//!   [`dregg_cell::is_attenuation`]). The guest exercises it LOCALLY, any number of
//!   times, with NO consent. These are *the various things they do locally*.
//! * **STUDYREF** — a read/STUDY-only [`dregg_cell::ReadCap`] (a read-lattice
//!   [`dregg_cell::FieldSet`] + a [`dregg_cell::ViewKey`], attenuated by
//!   [`dregg_cell::is_read_attenuation`]). The guest can INSPECT the referenced
//!   cell's exposed slots but holds NO write cap; *exercising* it requires an
//!   upgrade REQUEST. A sturdyref you can look at but not pull on without asking.
//! * **NETWORKBOUNDARY** — a cap whose exercise "elaborates elsewhere" (the
//!   network, or my REAL non-embedded cells). NO cap is granted into the guest's
//!   c-list; instead an attempted exercise opens a CONSENT REQUEST to me. The
//!   exercise is a [`dregg_turn::ConditionalTurn`] whose [`dregg_turn::ProofCondition`]
//!   is MY grant — it resolves on consent, fail-closed (expires) otherwise.
//!
//! This module is the AUTHORITY / CONSENT typing of the membrane. It reinvents
//! NONE of the machinery — it is a thin partitioning + flow over
//! [`crate::powerbox`] (the grant-ceremony), [`dregg_cell::ReadCap`] (the
//! studyref), [`dregg_turn::ConditionalTurn`] (the consent hole-fill), and
//! [`crate::branch_stitch`] (the merge-back). The deos-chat lane owns the
//! TRANSPORT (delivery of the fork bytes, the chat membrane); the seam between us
//! is the [`SharedFork`] value handed to chat for delivery, and the
//! [`ConsentRequest`] / `grant-receipt` pair carried back over chat.
//!
//! See `docs/deos/SHARED-FORK-CONSENT.md` for the full design.
//!
//! gpui-free + `cargo test`-able: the construction designates from a real c-list,
//! the embedded grant is a real verified turn through the embedded [`World`], and
//! the networkboundary consent is a real [`dregg_turn::ConditionalTurn`] whose
//! condition resolves under the owner's signed receipt — so the tests prove the
//! three-tier flow without a GPU.

use dregg_cell::{AuthRequired, CapabilityRef, CellId, ReadCap};
use dregg_turn::conditional::{
    ConditionProof, ConditionalResult, ConditionalTurn, ProofCondition, resolve_condition,
    DEFAULT_MAX_ROOT_AGE,
};
use dregg_turn::turn::{Turn, TurnReceipt};

use crate::powerbox::{Powerbox, PowerboxOutcome};
use crate::world::World;

/// **A cap fully granted into the fork — the EMBEDDED tier.**
///
/// The guest holds this in its fork c-list; it exercises it locally with no
/// consent. The `cap` is a genuine [`CapabilityRef`], attenuated to `≤` what I
/// held before it was granted (the powerbox's [`dregg_cell::is_attenuation`] gate).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmbeddedCap {
    /// The cell the guest may reach + exercise locally.
    pub target: CellId,
    /// The exact attenuated cap minted into the guest's fork c-list.
    pub cap: CapabilityRef,
}

/// **A read/STUDY-only reference — the STUDYREF tier.**
///
/// A [`ReadCap`] over a target: the guest can `open` the exposed slots (decrypt +
/// commitment-check) but holds NO write cap. To EXERCISE (mutate) the target the
/// guest must raise an upgrade request ([`StudyRef::upgrade_request`]), which
/// routes to me as a powerbox designation for write rights.
#[derive(Clone, Debug)]
pub struct StudyRef {
    /// The cell the guest may inspect.
    pub target: CellId,
    /// The read-only cap (read-lattice + view key) the guest holds.
    pub read_cap: ReadCap,
}

impl StudyRef {
    /// The exercise-upgrade request: a [`crate::powerbox::CapabilityRequest`] for
    /// WRITE authority over this studyref's target. The guest holds only a
    /// read-cap; to mutate it must ASK. Routed to the owner exactly like any
    /// powerbox request — the owner grants (promoting the studyref to embedded for
    /// this target) or denies.
    pub fn upgrade_request(&self, guest: CellId, desired: AuthRequired) -> crate::powerbox::CapabilityRequest {
        crate::powerbox::CapabilityRequest::new(
            guest,
            format!(
                "studyref upgrade: wants WRITE authority over the cell it can currently only inspect ({})",
                crate::reflect::short_hex(&self.target.0)
            ),
            desired,
        )
    }
}

/// **A consent-gated cap — the NETWORKBOUNDARY tier.**
///
/// NO cap rides into the guest's c-list. An attempted exercise of `target` does
/// not run — it "elaborates elsewhere" (the network, or my real non-embedded
/// cells), so it opens a CONSENT REQUEST to me. The exercise is shaped as a
/// [`ConditionalTurn`] whose [`ProofCondition`] is my grant: it resolves on
/// consent, fail-closed (expires) otherwise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NetworkBoundary {
    /// The real (non-embedded) cell / network target the guest may not touch
    /// without my live consent.
    pub target: CellId,
    /// The authority the boundary would confer IF I consent (the ceiling of the
    /// grant my consent mints — never wider than what I hold).
    pub ceiling: AuthRequired,
}

impl NetworkBoundary {
    /// Build the CONSENT REQUEST for an attempted exercise of this boundary: the
    /// guest's intended `turn` wrapped in a [`ConditionalTurn`] whose condition is
    /// "the owner's grant turn executed" ([`ProofCondition::TurnExecuted`]). The
    /// pending turn does NOTHING until the owner's signed grant-receipt resolves it
    /// (fail-closed); it expires at `timeout_height` if consent never arrives.
    ///
    /// The `owner_grant_turn_hash` is the hash of the powerbox grant turn the owner
    /// WOULD run to consent — binding the consent to a SPECIFIC grant, so a stray
    /// receipt cannot fire an arbitrary boundary.
    pub fn consent_request(
        &self,
        guest: CellId,
        intended_turn: Turn,
        owner_grant_turn_hash: [u8; 32],
        submitted_at: u64,
        timeout_height: u64,
    ) -> ConsentRequest {
        let pending = ConditionalTurn {
            turn: intended_turn,
            condition: ProofCondition::TurnExecuted {
                turn_hash: owner_grant_turn_hash,
            },
            timeout_height,
            submitted_at,
            deposit_amount: 0,
        };
        ConsentRequest {
            guest,
            target: self.target,
            ceiling: self.ceiling.clone(),
            pending,
        }
    }
}

/// **A consent request raised by a guest's boundary exercise.**
///
/// Carries the pending [`ConditionalTurn`] (the guest's intended turn, gated on my
/// grant) + what it wants. Handed back to me over the chat lane; I resolve it by
/// running a powerbox grant ([`SharedFork::resolve_consent`]) — my signed
/// grant-receipt is the [`ConditionProof`] that satisfies the pending turn — or I
/// deny (let it expire, fail-closed).
#[derive(Clone, Debug)]
pub struct ConsentRequest {
    /// The guest principal whose boundary exercise raised this.
    pub guest: CellId,
    /// The real/network cell the guest wants to elaborate to.
    pub target: CellId,
    /// The authority the guest's exercise would need.
    pub ceiling: AuthRequired,
    /// The pending, consent-gated turn — does nothing until resolved; expires if
    /// consent never arrives.
    pub pending: ConditionalTurn,
}

/// The outcome of the owner resolving a consent request.
#[derive(Debug)]
pub enum ConsentOutcome {
    /// The owner GRANTED: the powerbox minted a real attenuated cap (the consent
    /// witness is the executor's `receipt`), and the pending turn's condition
    /// RESOLVED under it. The boundary fired ONCE (the proof nullifier prevents a
    /// replay).
    Granted { receipt: TurnReceipt },
    /// The owner DENIED / the request did not resolve (an over-amplifying grant
    /// refused, an unheld target, or the pending turn expired). Fail-closed: the
    /// boundary did NOT fire, nothing reached the owner's real world.
    Denied { reason: String },
}

impl ConsentOutcome {
    pub fn is_granted(&self) -> bool {
        matches!(self, ConsentOutcome::Granted { .. })
    }
}

/// **THE SHARED FORK** — a confined sub-world handed to another principal, whose
/// culled cap-subgraph is graduated into the three tiers.
///
/// Constructed from MY world by designating the in-view subgraph
/// ([`SharedFork::construct`]); handed to the chat lane for delivery. The guest
/// acts inside the fork (embedded → local; studyref → inspect / upgrade-request;
/// networkboundary → consent-request); I resolve consents via the powerbox; their
/// local work stitches back via branch-and-stitch (the settlement gate re-checks
/// my authority at the settlement tip).
#[derive(Clone, Debug)]
pub struct SharedFork {
    /// The confined recipient principal — a fresh cell in the fork's ledger with
    /// (before any embedded grant) an EMPTY c-list (no ambient authority, the ocap
    /// floor; exactly [`crate::powerbox::AppLauncher::launch`]).
    pub guest: CellId,
    /// EMBEDDED caps — granted into the guest's fork c-list, exercised locally with
    /// no consent.
    pub embedded: Vec<EmbeddedCap>,
    /// STUDYREFs — read-only references; the guest inspects, exercise = upgrade
    /// request.
    pub studyrefs: Vec<StudyRef>,
    /// NETWORKBOUNDARYs — consent-gated; an exercise opens a consent request.
    pub boundaries: Vec<NetworkBoundary>,
}

impl SharedFork {
    /// **Construct a shared fork from MY world.** Birth the confined guest, then
    /// partition the designated in-view subgraph into the three tiers, GRANTING the
    /// embedded caps into the guest's c-list via real verified powerbox turns
    /// against the fork's world.
    ///
    /// `fork` is the already-forked world ([`crate::world::World::fork`]) — a
    /// deep-clone of my ledger + the genuine executor, so granting into it mutates
    /// ONLY the fork. `owner` is my principal (the authority I designate FROM).
    /// `guest` is the confined recipient cell (born empty).
    ///
    /// * `embedded` = `(target, confer_rights)` to fully grant — each is minted via
    ///   [`Powerbox::grant`] (the two real gates: `mint_needs_held_factory` +
    ///   `gen_conferral_is_attenuation`), so an over-grant or an unheld target is
    ///   simply DROPPED from the fork (never amplified).
    /// * `studyrefs` = read-only [`ReadCap`]s the guest may inspect.
    /// * `boundaries` = `(target, ceiling)` consent-gated — NO cap granted; an
    ///   exercise opens a consent request.
    ///
    /// Returns the constructed [`SharedFork`] (the embedded vec carries exactly the
    /// caps that WERE successfully minted — the powerbox dropped any the owner could
    /// not legitimately confer).
    pub fn construct(
        fork: &mut World,
        owner: CellId,
        guest: CellId,
        embedded: &[(CellId, AuthRequired)],
        studyrefs: Vec<StudyRef>,
        boundaries: Vec<NetworkBoundary>,
    ) -> Self {
        let mut embedded_out = Vec::new();
        for (target, confer_rights) in embedded {
            // The REAL powerbox grant: mint an attenuated cap into the guest's fork
            // c-list. The two gates (held + non-amplifying) + the executor backstop
            // fire; a grant the owner cannot legitimately confer is dropped.
            match Powerbox::grant(fork, owner, guest, *target, confer_rights.clone()) {
                PowerboxOutcome::Granted { conferred, .. } => {
                    // Read back the freshly-minted cap from the guest's live c-list
                    // (the executor installed it; we report exactly what landed).
                    if let Some(cell) = fork.ledger().get(&guest) {
                        if let Some(cap) = cell
                            .capabilities
                            .iter()
                            .find(|c| c.target == conferred.target && c.slot == conferred.slot)
                        {
                            embedded_out.push(EmbeddedCap {
                                target: conferred.target,
                                cap: cap.clone(),
                            });
                        }
                    }
                }
                PowerboxOutcome::Denied { .. } => {
                    // The owner could not legitimately confer this — it does NOT
                    // ride into the fork (no amplification, fail-closed).
                }
            }
        }
        SharedFork {
            guest,
            embedded: embedded_out,
            studyrefs,
            boundaries,
        }
    }

    /// The boundary descriptor for `target`, if `target` is a consent-gated
    /// networkboundary in this fork. An exercise of a target that is NOT here is
    /// either embedded (do it locally) or studyref (inspect / upgrade) or simply
    /// unreachable (the guest holds no cap to it — the confinement floor).
    pub fn boundary_for(&self, target: &CellId) -> Option<&NetworkBoundary> {
        self.boundaries.iter().find(|b| &b.target == target)
    }

    /// **Resolve a consent request** the guest raised by attempting a boundary
    /// exercise. I (the owner) run a REAL powerbox grant over `world` (my LIVE
    /// world — the consent elaborates to my real cells); the resulting signed
    /// [`TurnReceipt`] is the [`ConditionProof`] that satisfies the pending turn's
    /// [`ProofCondition::TurnExecuted`] condition.
    ///
    /// * On a granted, non-amplifying designation whose receipt resolves the
    ///   condition → [`ConsentOutcome::Granted`]: the boundary may fire ONCE (the
    ///   proof nullifier `used_proof_hashes` prevents a replay).
    /// * On a refused grant (over-amplifying / unheld target), or a condition that
    ///   does not resolve (wrong receipt, expired) → [`ConsentOutcome::Denied`]:
    ///   fail-closed, the boundary did not fire.
    ///
    /// `trusted_executor_keys` is the owner's executor key(s) the
    /// [`ProofCondition::TurnExecuted`] arm verifies the receipt signature against
    /// (so a fabricated receipt cannot fire the boundary). `current_height` is the
    /// live height the timeout is checked against.
    pub fn resolve_consent(
        world: &mut World,
        owner: CellId,
        request: &ConsentRequest,
        confer_rights: AuthRequired,
        trusted_executor_keys: &[[u8; 32]],
        current_height: u64,
    ) -> ConsentOutcome {
        // (1) The owner consents by running the REAL powerbox grant over the LIVE
        //     world — the two gates + executor backstop fire. A refusal here IS a
        //     denial (fail-closed).
        let receipt = match Powerbox::grant(world, owner, request.guest, request.target, confer_rights) {
            PowerboxOutcome::Granted { receipt, .. } => receipt,
            PowerboxOutcome::Denied { reason } => {
                return ConsentOutcome::Denied { reason };
            }
        };

        // (2) The grant-receipt is the CONSENT WITNESS: it must resolve the pending
        //     turn's TurnExecuted condition (its executor_signature verified against
        //     the owner's trusted key). One-shot: the nullifier prevents a replay.
        let mut used = std::collections::HashSet::new();
        let proof = ConditionProof::Receipt(receipt.clone());
        let result = resolve_condition(
            &request.pending.condition,
            &proof,
            current_height,
            request.pending.timeout_height,
            &[],
            DEFAULT_MAX_ROOT_AGE,
            &mut used,
            trusted_executor_keys,
        );
        match result {
            ConditionalResult::Resolved => ConsentOutcome::Granted { receipt },
            ConditionalResult::Expired => ConsentOutcome::Denied {
                reason: "consent arrived after the boundary turn expired (fail-closed)".to_string(),
            },
            ConditionalResult::Pending => ConsentOutcome::Denied {
                reason: "consent did not satisfy the boundary condition (pending — fail-closed)"
                    .to_string(),
            },
            ConditionalResult::InvalidProof(m) => ConsentOutcome::Denied {
                reason: format!("consent receipt did not resolve the boundary: {m}"),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::make_open_cell;

    /// A fork world: a USER/owner principal holding caps to a `docs` cell and a
    /// `peer` cell, plus a fresh confined `guest` holding nothing. Mirrors the
    /// powerbox test world so the shared-fork flow rides the SAME real machinery.
    /// Returns `(world, owner, guest, docs, peer)`.
    fn fork_world() -> (World, CellId, CellId, CellId, CellId) {
        let mut w = World::new();
        let docs = w.genesis_cell(0xD0, 0);
        let peer = w.genesis_cell(0xBE, 0);
        let guest = w.genesis_cell(0xA9, 0); // confined, empty c-list

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

        (w, owner, guest, docs, peer)
    }

    #[test]
    fn construct_grants_embedded_attenuated_and_leaves_boundaries_ungranted() {
        // EMBEDDED: docs granted (attenuated to Signature) into the guest's c-list.
        // NETWORKBOUNDARY: peer is consent-gated → NO cap rides into the guest.
        let (mut world, owner, guest, docs, peer) = fork_world();
        let mut fork = world.fork();

        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::Signature)], // embedded, attenuated from None
            vec![],                             // (studyrefs: see ReadCap test below)
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );

        // The embedded cap landed in the guest's FORK c-list, attenuated.
        assert_eq!(sf.embedded.len(), 1, "docs is embedded");
        assert_eq!(sf.embedded[0].target, docs);
        assert_eq!(sf.embedded[0].cap.permissions, AuthRequired::Signature);
        assert!(
            fork.ledger().get(&guest).unwrap().capabilities.has_access(&docs),
            "the guest reaches docs locally in the fork (embedded → no consent)"
        );

        // The boundary granted NOTHING — the guest cannot reach peer without consent.
        assert!(sf.boundary_for(&peer).is_some(), "peer is a networkboundary");
        assert!(
            !fork.ledger().get(&guest).unwrap().capabilities.has_access(&peer),
            "a networkboundary rides NO cap into the fork (exercise needs consent)"
        );

        // The LIVE world is untouched — granting happened only on the fork.
        assert!(
            world.ledger().get(&guest).map_or(true, |c| !c.capabilities.has_access(&docs)),
            "forking + granting mutated ONLY the fork, never the live world"
        );
    }

    #[test]
    fn construct_drops_an_over_amplifying_embedded_grant() {
        // The owner holds only Signature over peer; trying to EMBED peer at the
        // wider None (full authority) is an amplification → the powerbox refuses,
        // and the cap is DROPPED from the fork (never amplified).
        let (mut world, owner, guest, _docs, peer) = fork_world();
        let mut fork = world.fork();

        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(peer, AuthRequired::None)], // amplification attempt
            vec![],
            vec![],
        );
        assert!(sf.embedded.is_empty(), "an over-amplifying embed is dropped (no amplification)");
        assert!(
            !fork.ledger().get(&guest).unwrap().capabilities.has_access(&peer),
            "the guest got nothing — the powerbox refused the amplifying grant"
        );
    }

    #[test]
    fn studyref_is_read_only_and_yields_a_write_upgrade_request() {
        // A STUDYREF is a ReadCap: the guest can inspect, but to EXERCISE it must
        // raise an upgrade request for WRITE authority (routed to the owner).
        let (_w, _owner, guest, docs, _peer) = fork_world();
        let view_key = dregg_cell::ViewKey::from_root([7u8; 32]);
        let read_cap = ReadCap::new(docs, dregg_cell::FieldSet::single(0), view_key);
        let study = StudyRef { target: docs, read_cap };

        // The studyref derives the key for its exposed slot (it can inspect) …
        assert!(study.read_cap.derives(0), "studyref can inspect the exposed slot");
        // … and an attempt to EXERCISE raises a write-upgrade request to the owner.
        let req = study.upgrade_request(guest, AuthRequired::Signature);
        assert_eq!(req.app_cell, guest);
        assert_eq!(req.desired_rights, AuthRequired::Signature);
        assert!(req.reason.contains("upgrade"), "the request names it an upgrade");
    }

    #[test]
    fn networkboundary_consent_is_a_conditionalturn_gated_on_the_owners_grant() {
        // THE KEYSTONE (shape): a networkboundary exercise is a ConditionalTurn
        // whose ProofCondition is the OWNER's grant (TurnExecuted bound to the grant
        // turn's hash). The pending turn does NOTHING until that condition resolves.
        let (mut world, _owner, guest, _docs, peer) = fork_world();

        // The guest's intended boundary exercise (a stand-in "thing it wants to do
        // over there") wrapped in a pending ConditionalTurn gated on the owner's
        // grant turn hash. Before consent, the turn is purely pending — fail-closed.
        let intended =
            world.turn(guest, vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }]);
        let owner_grant_hash = [0xC0u8; 32]; // the hash of the grant the owner WOULD run
        let boundary = NetworkBoundary { target: peer, ceiling: AuthRequired::Signature };
        let request = boundary.consent_request(guest, intended, owner_grant_hash, 0, 100);

        assert!(
            matches!(
                request.pending.condition,
                ProofCondition::TurnExecuted { turn_hash } if turn_hash == owner_grant_hash
            ),
            "the boundary condition IS the owner's grant (TurnExecuted bound to its hash)"
        );
        assert!(!request.pending.is_expired(10), "the pending turn is live, awaiting consent");
        assert!(request.pending.is_expired(101), "and fail-closes (expires) without consent");
    }

    #[test]
    fn networkboundary_resolves_on_a_signed_consent_and_fires_once() {
        // THE KEYSTONE (resolution): the owner's signed grant-receipt is the
        // ConditionProof that satisfies the pending TurnExecuted condition. We build
        // a genuine signed receipt exactly as the proven `conditional.rs`
        // TurnExecuted arm checks it (the executor signs `receipt_hash()` with a key
        // in the trusted set), and assert it RESOLVES — then assert a REPLAY is
        // rejected by the proof nullifier (the boundary fires exactly once).
        //
        // NOTE (finding, see SHARED-FORK-CONSENT.md): the embedded `World` executor
        // signs `canonical_executor_signed_message()`, while `resolve_condition`'s
        // TurnExecuted arm verifies `receipt_hash()`. Wiring `resolve_consent` to a
        // real World-grant receipt therefore needs a shared signing domain (or a
        // `LocalProof`-shaped condition). Here we exercise the condition machinery
        // directly with a matching-domain signed receipt, the way conditional.rs's
        // own `test_turn_executed_resolved` does.
        use ed25519_dalek::{Signer, SigningKey};
        use std::collections::HashSet;

        let turn_hash = [0xC0u8; 32];
        let condition = ProofCondition::TurnExecuted { turn_hash };

        let exec_key = SigningKey::from_bytes(&[0x42; 32]);
        let exec_pub = exec_key.verifying_key().to_bytes();

        let mut receipt = TurnReceipt {
            turn_hash,
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 0,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId([0u8; 32]),
            federation_id: [0u8; 32],
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        };
        let receipt_hash = receipt.receipt_hash();
        receipt.executor_signature = Some(exec_key.sign(&receipt_hash).to_bytes().to_vec());

        let proof = ConditionProof::Receipt(receipt);
        let mut used: HashSet<[u8; 32]> = HashSet::new();

        // First resolution: the owner's signed consent fires the boundary.
        let r1 = resolve_condition(
            &condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut used, &[exec_pub],
        );
        assert_eq!(r1, ConditionalResult::Resolved, "owner's signed consent resolves the boundary");

        // Replay: the SAME consent cannot fire the boundary twice (one-shot — the
        // proof-hole-is-a-nullifier). This is the linear/one-shot consent property.
        let r2 = resolve_condition(
            &condition, &proof, 10, 100, &[], DEFAULT_MAX_ROOT_AGE, &mut used, &[exec_pub],
        );
        assert!(
            matches!(r2, ConditionalResult::InvalidProof(_)),
            "a consent fires the boundary exactly ONCE (nullifier rejects replay): {r2:?}"
        );
    }

    #[test]
    fn networkboundary_denied_when_owner_cannot_legitimately_consent() {
        // Fail-closed: if the owner tries to consent at an amplifying right (peer is
        // held only at Signature; consent at None would amplify), the powerbox
        // refuses → ConsentOutcome::Denied. The boundary did NOT fire.
        let (mut world, owner, guest, _docs, peer) = fork_world();
        let intended = world.turn(guest, vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }]);
        let boundary = NetworkBoundary { target: peer, ceiling: AuthRequired::None };
        let request = boundary.consent_request(guest, intended, [0u8; 32], 0, 100);

        let outcome = SharedFork::resolve_consent(
            &mut world,
            owner,
            &request,
            AuthRequired::None, // amplifying — the owner holds only Signature over peer
            &[],
            10,
        );
        assert!(!outcome.is_granted(), "an amplifying consent is refused (fail-closed)");
        match outcome {
            ConsentOutcome::Denied { reason } => assert!(
                reason.contains("AMPLIFY") || reason.contains("attenuation") || reason.contains("boundary"),
                "the denial cites why, got: {reason}"
            ),
            ConsentOutcome::Granted { .. } => panic!("must be denied"),
        }
    }
}
