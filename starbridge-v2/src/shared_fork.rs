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
//! * **STUDYREF** — a read/STUDY-only [`dregg_cell_crypto::ReadCap`] (a read-lattice
//!   [`dregg_cell_crypto::FieldSet`] + a [`dregg_cell_crypto::ViewKey`], attenuated by
//!   [`dregg_cell_crypto::is_read_attenuation`]). The guest can INSPECT the referenced
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
//! [`crate::powerbox`] (the grant-ceremony), [`dregg_cell_crypto::ReadCap`] (the
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

use std::collections::HashSet;

use dregg_cell::{AuthRequired, CapabilityRef, CellId};
use dregg_cell_crypto::ReadCap;
use dregg_turn::conditional::{
    compute_proof_hash, ConditionProof, ConditionalResult, ConditionalTurn, ProofCondition,
    resolve_condition, DEFAULT_MAX_ROOT_AGE,
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
    /// [`TurnReceipt`] is the CONSENT WITNESS that satisfies the pending turn's
    /// [`ProofCondition::TurnExecuted`] condition.
    ///
    /// * On a granted, non-amplifying designation whose receipt resolves the
    ///   condition → [`ConsentOutcome::Granted`]: the boundary may fire ONCE (the
    ///   proof nullifier prevents a replay).
    /// * On a refused grant (over-amplifying / unheld target), or a condition that
    ///   does not resolve (wrong grant turn, unsigned receipt, untrusted key,
    ///   expired) → [`ConsentOutcome::Denied`]: fail-closed, the boundary did not
    ///   fire.
    ///
    /// **The consent signing domain (the closed finding).** The pending condition
    /// is a [`ProofCondition::TurnExecuted`] bound to the grant turn's hash, but a
    /// genuine `World`-grant receipt is signed by the embedded executor over
    /// [`TurnReceipt::canonical_executor_signed_message`] (the `v3` domain) — NOT
    /// over the bare `receipt_hash()` the generic [`resolve_condition`]
    /// `TurnExecuted` arm checks. So routing a REAL receipt through that arm always
    /// rejected (`executor_signature not verified`). This resolver instead verifies
    /// the receipt in the executor's OWN signing domain via [`verify_consent_witness`]
    /// — so consent resolves against a real grant, with the SAME three guarantees
    /// the generic arm gives: (a) the receipt's `turn_hash` must equal the bound
    /// grant turn hash (consent binds a SPECIFIC grant); (b) the signature must
    /// verify under a trusted executor key (no fabricated witness); (c) the proof
    /// nullifier makes the boundary fire exactly ONCE.
    ///
    /// `trusted_executor_keys` is the owner's executor public key(s) the witness
    /// signature is verified against — pass `&[world.executor_public_key()?]` for a
    /// world configured with [`World::with_executor_signing_key`]. `current_height`
    /// is the live height the timeout is checked against. `used_proof_hashes` is the
    /// owner's persistent nullifier set (one-shot across calls); pass a fresh set
    /// for a single resolution.
    pub fn resolve_consent(
        world: &mut World,
        owner: CellId,
        request: &ConsentRequest,
        confer_rights: AuthRequired,
        trusted_executor_keys: &[[u8; 32]],
        current_height: u64,
        used_proof_hashes: &mut HashSet<[u8; 32]>,
    ) -> ConsentOutcome {
        // (0) Timeout: a consent arriving after the boundary turn expired is
        //     fail-closed (the same first gate `resolve_condition` applies).
        if current_height > request.pending.timeout_height {
            return ConsentOutcome::Denied {
                reason: "consent arrived after the boundary turn expired (fail-closed)".to_string(),
            };
        }

        // (1) The owner consents by running the REAL powerbox grant over the LIVE
        //     world — the two gates + executor backstop fire. A refusal here IS a
        //     denial (fail-closed). The grant's receipt is the CONSENT WITNESS.
        let receipt = match Powerbox::grant(world, owner, request.guest, request.target, confer_rights) {
            PowerboxOutcome::Granted { receipt, .. } => receipt,
            PowerboxOutcome::Denied { reason } => {
                return ConsentOutcome::Denied { reason };
            }
        };

        // (2) Verify the witness in the executor's OWN signing domain against the
        //     bound grant turn hash + a trusted key. This is the closed finding: a
        //     real World-grant receipt resolves here, where it could NOT through the
        //     generic TurnExecuted arm (which checks the wrong message).
        match verify_consent_witness(
            &request.pending.condition,
            &receipt,
            trusted_executor_keys,
            used_proof_hashes,
        ) {
            Ok(()) => ConsentOutcome::Granted { receipt },
            Err(reason) => ConsentOutcome::Denied {
                reason: format!("consent receipt did not resolve the boundary: {reason}"),
            },
        }
    }
}

/// **Verify a consent witness in the executor's real signing domain.**
///
/// The closed finding (`docs/deos/SHARED-FORK-CONSENT.md`): the embedded `World`
/// executor signs [`TurnReceipt::canonical_executor_signed_message`] (the `v3`
/// domain `b"executor-receipt-sig-v3:" || receipt_hash`), while the generic
/// [`resolve_condition`] `TurnExecuted` arm verifies the bare `receipt_hash()`.
/// A real grant receipt therefore cannot satisfy that arm. This function applies
/// the IDENTICAL three checks the `TurnExecuted` arm applies — turn-hash binding,
/// executor-signature authenticity, and the one-shot proof nullifier — but over
/// the executor's ACTUAL signed message, so a genuine `World`-grant receipt
/// resolves a [`NetworkBoundary`] consent.
///
/// Returns `Ok(())` and records the nullifier on success; `Err(reason)` (and
/// records NOTHING) on any failure — fail-closed.
fn verify_consent_witness(
    condition: &ProofCondition,
    receipt: &TurnReceipt,
    trusted_executor_keys: &[[u8; 32]],
    used_proof_hashes: &mut HashSet<[u8; 32]>,
) -> Result<(), String> {
    // The condition MUST be a grant-bound TurnExecuted (the boundary shape).
    let ProofCondition::TurnExecuted { turn_hash } = condition else {
        return Err("consent condition is not a grant-bound TurnExecuted".to_string());
    };

    // (a) BINDING: the witness must be the receipt of the SPECIFIC grant turn this
    //     boundary was gated on — a stray receipt cannot fire an arbitrary boundary.
    if receipt.turn_hash != *turn_hash {
        return Err(format!(
            "receipt turn_hash mismatch: expected {:02x}{:02x}..., got {:02x}{:02x}...",
            turn_hash[0], turn_hash[1], receipt.turn_hash[0], receipt.turn_hash[1],
        ));
    }

    // (b) ONE-SHOT: the proof nullifier — over the SAME `compute_proof_hash` the
    //     generic resolver uses — makes a consent fire the boundary exactly ONCE.
    //     Checked before signature verification (a replay is rejected regardless).
    let proof = ConditionProof::Receipt(receipt.clone());
    let proof_hash = compute_proof_hash(&proof);
    if used_proof_hashes.contains(&proof_hash) {
        return Err("proof already used (consent fires the boundary exactly once)".to_string());
    }

    // (c) AUTHENTICITY: the executor signature must verify under a trusted key, in
    //     the executor's OWN signing domain (`canonical_executor_signed_message`).
    let Some(ref sig_bytes) = receipt.executor_signature else {
        return Err("receipt has no executor_signature (cannot verify authenticity)".to_string());
    };
    if sig_bytes.len() != 64 {
        return Err(format!(
            "executor_signature has invalid length: {} (expected 64)",
            sig_bytes.len()
        ));
    }
    if trusted_executor_keys.is_empty() {
        return Err("no trusted executor keys configured to verify receipt".to_string());
    }
    let msg = receipt.canonical_executor_signed_message();
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(sig_bytes);
    let signature = ed25519_dalek::Signature::from_bytes(&sig_arr);
    let verified = trusted_executor_keys.iter().any(|key_bytes| {
        ed25519_dalek::VerifyingKey::from_bytes(key_bytes)
            .map(|vk| vk.verify_strict(&msg, &signature).is_ok())
            .unwrap_or(false)
    });
    if !verified {
        return Err("receipt executor_signature not verified by any trusted executor key".to_string());
    }

    // All checks pass: record the nullifier (the boundary has now fired once).
    used_proof_hashes.insert(proof_hash);
    Ok(())
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
        let view_key = dregg_cell_crypto::ViewKey::from_root([7u8; 32]);
        let read_cap = ReadCap::new(docs, dregg_cell_crypto::FieldSet::single(0), view_key);
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
        // THE KEYSTONE (resolution shape): a signed grant-receipt is the
        // ConditionProof that satisfies the pending TurnExecuted condition. We build
        // a genuine signed receipt exactly as the proven `conditional.rs`
        // TurnExecuted arm checks it (the executor signs `receipt_hash()` with a key
        // in the trusted set), and assert it RESOLVES — then assert a REPLAY is
        // rejected by the proof nullifier (the boundary fires exactly once). This
        // proves the GENERIC `resolve_condition` one-shot shape directly;
        // `networkboundary_resolves_against_a_real_world_grant` (below) proves the
        // SAME property end-to-end against a real `World`-grant receipt through
        // `SharedFork::resolve_consent` — the closed finding.
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

        let mut used = HashSet::new();
        let outcome = SharedFork::resolve_consent(
            &mut world,
            owner,
            &request,
            AuthRequired::None, // amplifying — the owner holds only Signature over peer
            &[],
            10,
            &mut used,
        );
        assert!(!outcome.is_granted(), "an amplifying consent is refused (fail-closed)");
        assert!(used.is_empty(), "a denied consent records NO nullifier (the boundary never fired)");
        match outcome {
            ConsentOutcome::Denied { reason } => assert!(
                reason.contains("AMPLIFY") || reason.contains("attenuation") || reason.contains("boundary"),
                "the denial cites why, got: {reason}"
            ),
            ConsentOutcome::Granted { .. } => panic!("must be denied"),
        }
    }

    // ── THE CLOSED FINDING: consent resolves against a REAL World-grant receipt ──
    //
    // A signed fork world: the owner-cell holds caps to `docs`/`peer`; the world's
    // embedded executor is configured to SIGN its receipts (the consent witness).
    // Returns `(world, owner, guest, docs, peer, exec_seed)`.
    fn signed_fork_world() -> (World, CellId, CellId, CellId, CellId, [u8; 32]) {
        let exec_seed = [0x42u8; 32];
        let mut w = World::new().with_executor_signing_key(exec_seed);
        let docs = w.genesis_cell(0xD0, 0);
        let peer = w.genesis_cell(0xBE, 0);
        let guest = w.genesis_cell(0xA9, 0);
        let mut owner_cell = make_open_cell(0x55, 0);
        owner_cell.capabilities.grant(docs, AuthRequired::None).expect("owner holds docs");
        owner_cell.capabilities.grant(peer, AuthRequired::Signature).expect("owner holds peer");
        let owner = w.genesis_install(owner_cell);
        (w, owner, guest, docs, peer, exec_seed)
    }

    #[test]
    fn networkboundary_resolves_against_a_real_world_grant_and_fires_once() {
        // THE CLOSED FINDING, end-to-end: a guest's networkboundary exercise is a
        // ConditionalTurn gated on the OWNER's grant of `peer`. The owner consents
        // by running a REAL powerbox grant through `resolve_consent`; the grant's
        // signed `TurnReceipt` is the consent witness, verified IN THE EXECUTOR'S
        // OWN SIGNING DOMAIN (canonical_executor_signed_message) — the wiring the
        // finding asked for, which the generic TurnExecuted arm could not do.
        let (mut world, owner, guest, _docs, peer, _seed) = signed_fork_world();
        let exec_pub = world.executor_public_key().expect("the world signs its receipts");

        // The guest's intended boundary exercise, gated on the SPECIFIC grant turn
        // the owner will run. We PREDICT that grant turn's hash via the one shared
        // constructor `Powerbox::grant_turn` (the same turn `grant` commits), so the
        // consent binds to exactly this grant — not a stray receipt.
        let intended =
            world.turn(guest, vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }]);
        let grant_turn =
            crate::powerbox::Powerbox::grant_turn(&world, owner, guest, peer, AuthRequired::Signature);
        let grant_hash = grant_turn.hash();
        let boundary = NetworkBoundary { target: peer, ceiling: AuthRequired::Signature };
        let request = boundary.consent_request(guest, intended, grant_hash, 0, 100);

        let mut used: HashSet<[u8; 32]> = HashSet::new();
        // The owner consents: a real grant runs, the signed receipt resolves the
        // boundary IN the executor's signing domain (the closed finding).
        let outcome = SharedFork::resolve_consent(
            &mut world,
            owner,
            &request,
            AuthRequired::Signature, // non-amplifying (owner holds peer at Signature)
            &[exec_pub],
            10,
            &mut used,
        );
        assert!(
            outcome.is_granted(),
            "a real signed World-grant receipt RESOLVES the boundary (finding closed): {outcome:?}"
        );
        // The witness really is the executor's signed receipt bound to THIS grant.
        if let ConsentOutcome::Granted { receipt } = &outcome {
            assert_eq!(receipt.turn_hash, grant_hash, "the witness is the bound grant turn's receipt");
            assert!(receipt.executor_signature.is_some(), "the witness carries a real signature");
        }
        assert_eq!(used.len(), 1, "the boundary fired once → one nullifier recorded");

        // ONE-SHOT: re-presenting the SAME witness (same nullifier set) cannot fire
        // the boundary again — the proof-hole-is-a-nullifier, against the REAL
        // signed receipt. (A fresh, independent consent would be a new grant with a
        // new receipt; replaying THIS one is what is refused.)
        let first_witness = match outcome {
            ConsentOutcome::Granted { receipt } => receipt,
            _ => unreachable!(),
        };
        let replay = verify_consent_witness(
            &request.pending.condition,
            &first_witness,
            &[exec_pub],
            &mut used,
        );
        assert!(
            replay.is_err() && replay.unwrap_err().contains("already used"),
            "the SAME consent witness fires the boundary exactly ONCE (nullifier)"
        );
    }

    #[test]
    fn consent_rejects_a_fabricated_or_untrusted_witness() {
        // AUTHENTICITY (fail-closed): a receipt bound to the right grant but signed
        // by an UNTRUSTED key (or unsigned) does NOT resolve the boundary.
        let (mut world, owner, guest, _docs, peer, _seed) = signed_fork_world();
        let intended =
            world.turn(guest, vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }]);
        let grant_turn =
            crate::powerbox::Powerbox::grant_turn(&world, owner, guest, peer, AuthRequired::Signature);
        let request =
            NetworkBoundary { target: peer, ceiling: AuthRequired::Signature }
                .consent_request(guest, intended, grant_turn.hash(), 0, 100);

        // An attacker's key is NOT the world's executor key.
        let attacker_pub = ed25519_dalek::SigningKey::from_bytes(&[0x99; 32])
            .verifying_key()
            .to_bytes();
        let mut used = HashSet::new();
        let outcome = SharedFork::resolve_consent(
            &mut world,
            owner,
            &request,
            AuthRequired::Signature,
            &[attacker_pub], // wrong trusted key
            10,
            &mut used,
        );
        assert!(!outcome.is_granted(), "a witness not signed by a trusted key is refused");
        assert!(used.is_empty(), "no nullifier recorded — the boundary never fired");
    }

    #[test]
    fn consent_rejects_a_witness_bound_to_a_different_grant() {
        // BINDING (fail-closed): a real signed receipt whose turn_hash is NOT the
        // grant this boundary was gated on cannot fire it (no stray-receipt replay).
        // The owner's grant produces a receipt for the ACTUAL grant turn; we gate the
        // boundary on a DIFFERENT (wrong) hash, so the binding check refuses.
        let (mut world, owner, guest, _docs, peer, _seed) = signed_fork_world();
        let exec_pub = world.executor_public_key().unwrap();
        let intended =
            world.turn(guest, vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }]);
        // Bind the boundary to a hash that is NOT the grant turn's hash.
        let request = NetworkBoundary { target: peer, ceiling: AuthRequired::Signature }
            .consent_request(guest, intended, [0xAB; 32], 0, 100);
        let mut used = HashSet::new();
        let outcome = SharedFork::resolve_consent(
            &mut world,
            owner,
            &request,
            AuthRequired::Signature,
            &[exec_pub],
            10,
            &mut used,
        );
        assert!(!outcome.is_granted(), "a receipt for a DIFFERENT grant cannot fire this boundary");
        assert!(used.is_empty());
    }

    // ── GRADUATED RIGHTS — each tier enforces correctly ──────────────────────────

    #[test]
    fn embedded_tier_is_exercisable_locally_with_no_consent() {
        // EMBEDDED: a real cap is granted into the guest's fork c-list; the guest
        // DRIVES a real turn over it (set_field on docs) with NO consent — and it
        // commits against the fork's verified executor.
        let (mut world, owner, guest, docs, _peer, _seed) = signed_fork_world();
        let mut fork = world.fork();
        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::None)], // embed docs at full authority
            vec![],
            vec![],
        );
        assert_eq!(sf.embedded.len(), 1, "docs is embedded");
        assert!(fork.ledger().get(&guest).unwrap().capabilities.has_access(&docs));

        // The guest drives a REAL turn over its embedded cap — no consent door.
        let drive = fork.turn(guest, vec![crate::world::set_field(docs, 3, [9u8; 32])]);
        let committed = fork.commit_turn(drive).is_committed();
        assert!(committed, "the guest exercises the embedded cap locally with no consent");
        assert_eq!(
            fork.ledger().get(&docs).unwrap().state.fields[3], [9u8; 32],
            "the embedded exercise really mutated the fork"
        );
    }

    #[test]
    fn studyref_tier_inspects_but_refuses_exercise_without_an_upgrade() {
        // STUDYREF: the guest holds a ReadCap (inspect-only). It can derive the
        // exposed slot's key (inspect), but holds NO write cap — exercising requires
        // an upgrade REQUEST (routed to the owner). The fork c-list carries no write
        // cap for a studyref target.
        let (mut world, owner, guest, docs, _peer, _seed) = signed_fork_world();
        let mut fork = world.fork();
        let view_key = dregg_cell_crypto::ViewKey::from_root([7u8; 32]);
        let read_cap = ReadCap::new(docs, dregg_cell_crypto::FieldSet::single(0), view_key);
        let study = StudyRef { target: docs, read_cap };

        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[],                  // nothing embedded
            vec![study.clone()],  // docs is a studyref
            vec![],
        );
        assert_eq!(sf.studyrefs.len(), 1);
        // INSPECT ok: the studyref derives the key for its exposed slot.
        assert!(sf.studyrefs[0].read_cap.derives(0), "studyref inspects the exposed slot");
        // EXERCISE refused: the guest holds NO write cap to docs in the fork c-list.
        assert!(
            !fork.ledger().get(&guest).unwrap().capabilities.has_access(&docs),
            "a studyref grants NO write cap (exercise needs an upgrade)"
        );
        // The exercise path is an upgrade REQUEST routed to the owner (not a turn).
        let req = study.upgrade_request(guest, AuthRequired::Signature);
        assert_eq!(req.app_cell, guest);
        assert!(req.reason.contains("upgrade"));
    }

    // ── THE ROUND-TRIP: mint → rehydrate → drive → stitch (each property) ─────────

    #[test]
    fn mint_rehydrate_drive_stitch_round_trip() {
        use crate::branch_stitch::{Atom, BranchCap, DocGraph, MainFrontier, Stitch, VirtualBranch};
        use std::collections::BTreeSet;

        // A live world: the owner holds docs (embeddable) + peer (networkboundary).
        let (mut world, owner, guest, docs, peer, _seed) = signed_fork_world();

        // (1) MINT — frustum-cull the in-view cap subgraph + snapshot. We fork the
        //     live world (the snapshot: a deep clone of the ledger + the genuine
        //     executor) and partition the in-view subgraph: docs EMBEDDED, peer a
        //     NETWORKBOUNDARY (no cap rides in).
        let mut fork = world.fork();
        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::Signature)], // embedded, attenuated from None
            vec![],
            vec![NetworkBoundary { target: peer, ceiling: AuthRequired::Signature }],
        );

        // (2) REHYDRATE — assert the rehydrated fork holds ONLY the granted subgraph
        //     (anti-amplification): the guest reaches docs (embedded) but NOT peer
        //     (boundary), and the LIVE world is untouched (the per-viewer fork is
        //     attenuated, never wider than what was minted).
        assert!(
            fork.ledger().get(&guest).unwrap().capabilities.has_access(&docs),
            "rehydrated fork holds the granted (embedded) docs cap"
        );
        assert!(
            !fork.ledger().get(&guest).unwrap().capabilities.has_access(&peer),
            "anti-amplification: the boundary cap did NOT ride into the fork"
        );
        assert_eq!(sf.embedded[0].cap.permissions, AuthRequired::Signature, "attenuated, not wider");
        assert!(
            world.ledger().get(&guest).map_or(true, |c| !c.capabilities.has_access(&docs)),
            "the live world is untouched — minting mutated ONLY the fork"
        );

        // (3) DRIVE — the guest commits a REAL turn on the fork over its embedded
        //     cap (set_field on docs). It commits against the fork's verified
        //     executor; the live world stays diverged-away.
        let drive = fork.turn(guest, vec![crate::world::set_field(docs, 1, [42u8; 32])]);
        assert!(fork.commit_turn(drive).is_committed(), "the guest drives a real turn on the fork");
        assert_eq!(fork.ledger().get(&docs).unwrap().state.fields[1], [42u8; 32]);
        // The live world did NOT see the guest's local mutation (the branch is
        // structurally imaginary to main until stitched).
        assert_ne!(
            world.ledger().get(&docs).map(|c| c.state.fields[1]).unwrap_or([0u8; 32]),
            [42u8; 32],
            "the guest's local work is imaginary to the live world until stitched"
        );

        // (4) STITCH — branch-and-stitch the guest's work back. The branch is
        //     CONFINED away from main (it cannot drain a main cell), and the stitch
        //     is the pushout-correct, settlement-gated merge: clean where disjoint,
        //     REFUSED where it would confer authority the owner does not hold at the
        //     settlement tip.
        let docs_key: u64 = 0xD0;
        let peer_key: u64 = 0xBE;
        let main = MainFrontier::from([docs_key, peer_key]);

        // (4a) CONFINEMENT: a branch authored by the guest, holding only its embedded
        //      docs cap (no debit reach to a main cell), is confined.
        let branch = VirtualBranch::enter(
            0xA9, // the guest author
            main.clone(),
            vec![BranchCap { target: docs_key, debit_reach: false }],
        );
        assert!(branch.confined(), "the guest branch reaches no main cell by debit — confined");

        // (4b) CLEAN STITCH (disjoint/I-confluent): the guest's discovery (a new atom)
        //      merges into main as the pushout (LUB), conferring only authority the
        //      owner DOES hold at settlement (docs).
        let main_graph = DocGraph { atoms: [(docs_key, Atom::Alive)].into_iter().collect() };
        let branch_graph =
            DocGraph { atoms: [(99u64, Atom::Alive)].into_iter().collect() }; // a new discovery
        let clean = Stitch {
            main: main_graph.clone(),
            branch: branch_graph.clone(),
            conferred: vec![BranchCap { target: docs_key, debit_reach: false }],
        };
        let settlement_held = vec![BranchCap { target: docs_key, debit_reach: false }];
        match clean.settle(&settlement_held, None) {
            crate::branch_stitch::SettleOutcome::Settled(merged) => {
                assert!(merged.atoms.contains_key(&99), "the clean discovery merged into main");
                assert!(merged.atoms.contains_key(&docs_key), "main's own atom is preserved (LUB)");
            }
            other => panic!("a clean, in-authority stitch must settle: {other:?}"),
        }

        // (4c) CONFLICT / over-authorized DROP: a stitch that tries to confer peer
        //      (which the owner does NOT hold at the settlement tip — it was a
        //      networkboundary, never embedded) is REFUSED (the settlement gate),
        //      i.e. a cap-amplification at merge is a linear DROP, not a silent
        //      conjure.
        let amp = Stitch {
            main: main_graph,
            branch: branch_graph,
            conferred: vec![BranchCap { target: peer_key, debit_reach: true }],
        };
        match amp.settle(&settlement_held, Some(&BTreeSet::from([docs_key]))) {
            crate::branch_stitch::SettleOutcome::Refused { over_authorized_target } => {
                assert_eq!(over_authorized_target, peer_key, "the stitch drops the over-authorized peer cap");
            }
            other => panic!("an over-authorized stitch must be refused: {other:?}"),
        }
    }
}
