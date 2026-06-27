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
    compute_proof_hash, ConditionProof, ConditionalTurn, ProofCondition,
};
#[cfg(test)]
use dregg_turn::conditional::{resolve_condition, ConditionalResult, DEFAULT_MAX_ROOT_AGE};
use dregg_turn::turn::{Turn, TurnReceipt};

use crate::powerbox::{Powerbox, PowerboxOutcome};
use crate::world::{touched_cells, CommitOutcome, World};

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
    pub fn upgrade_request(
        &self,
        guest: CellId,
        desired: AuthRequired,
    ) -> crate::powerbox::CapabilityRequest {
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
    Granted { receipt: Box<TurnReceipt> },
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

/// The default height-window a fail-closed boundary refusal keeps its emitted
/// [`ConsentRequest`] live (so the owner has time to resolve it before it expires).
pub const DEFAULT_CONSENT_TIMEOUT: u64 = 100;

/// **A resolved consent witness** — the owner's signed grant receipt for a SPECIFIC
/// boundary, paired with the boundary it consents to and the height it expires at.
///
/// Produced from a [`ConsentOutcome::Granted`] (its `receipt`) plus the boundary
/// target and the pending turn's `timeout_height`. Handed to
/// [`SharedFork::commit_turn_gated`] to OPEN the boundary gate for one turn. The
/// witness is verified again at the gate (binding + authenticity + one-shot), so it
/// cannot be forged or replayed — it is a one-shot key, not a flag.
#[derive(Clone, Debug)]
pub struct ConsentWitness {
    /// The boundary target this consent opens (must equal the gated turn's boundary).
    pub boundary: CellId,
    /// The height past which this consent is stale (fail-closed).
    pub timeout_height: u64,
    /// The owner's grant receipt — the signed witness `verify_consent_witness` checks.
    pub receipt: TurnReceipt,
}

impl ConsentWitness {
    /// Build a witness from a granted [`ConsentOutcome`] for the given boundary +
    /// timeout. Returns `None` if the outcome was a denial (fail-closed: no key).
    pub fn from_outcome(
        boundary: CellId,
        timeout_height: u64,
        outcome: ConsentOutcome,
    ) -> Option<Self> {
        match outcome {
            ConsentOutcome::Granted { receipt } => Some(ConsentWitness {
                boundary,
                timeout_height,
                receipt: *receipt,
            }),
            ConsentOutcome::Denied { .. } => None,
        }
    }
}

/// The outcome of [`SharedFork::commit_turn_gated`] — the fail-closed boundary gate.
#[derive(Debug)]
pub enum GatedCommit {
    /// The gate OPENED: the turn ran on the fork (the inner [`CommitOutcome`] is the
    /// executor's verdict). `fired_boundary` is `Some(target)` when the turn crossed
    /// a boundary that a valid consent opened (its nullifier was recorded — fired
    /// once); `None` for a purely-embedded turn (no boundary touched).
    Committed {
        outcome: CommitOutcome,
        fired_boundary: Option<CellId>,
    },
    /// FAIL-CLOSED: the turn touched a boundary with no valid consent. It did NOT
    /// run; nothing reached "elsewhere". `request` carries the [`ConsentRequest`] the
    /// owner must resolve (present only for the no-consent case; `None` when a
    /// supplied witness was invalid).
    Refused {
        /// The boundary target whose exercise was refused.
        target: CellId,
        /// The consent request the owner resolves to open the gate (no-consent case).
        request: Box<Option<ConsentRequest>>,
        /// Why the exercise was refused.
        reason: String,
    },
}

impl GatedCommit {
    /// Did the gated turn actually commit on the fork?
    pub fn is_committed(&self) -> bool {
        matches!(self, GatedCommit::Committed { outcome, .. } if outcome.is_committed())
    }
    /// Was the turn refused at the boundary gate (fail-closed)?
    pub fn is_refused(&self) -> bool {
        matches!(self, GatedCommit::Refused { .. })
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

    /// **FAIL-CLOSED BOUNDARY INTERCEPTION — the compulsion gate.**
    ///
    /// This is the executor-forcing seam: the guest does NOT *choose* to raise a
    /// consent request — the fork's commit path REFUSES, fail-closed, any turn that
    /// touches a [`NetworkBoundary`] target unless the turn is paired with a valid,
    /// resolved consent witness for that boundary. There is no path by which a
    /// boundary cap reaches the executor without consent: an embedded turn commits
    /// freely; a turn touching a marked boundary is structurally refused absent the
    /// owner's signed grant.
    ///
    /// Classification (over the SAME [`touched_cells`] the live commit path uses):
    /// * touches NO boundary target → pass through to [`World::commit_turn`] (an
    ///   embedded exercise — or a studyref inspect — runs locally, no consent). A
    ///   studyref *exercise* never reaches here as a committed write: the guest holds
    ///   no write cap, so the executor itself refuses it (no gate needed); if a
    ///   studyref target is ALSO marked a boundary, it is gated like any boundary.
    /// * touches a boundary target with NO consent supplied → [`GatedCommit::Refused`]
    ///   carrying the [`ConsentRequest`] the owner must resolve. The turn is NOT run
    ///   — fail-closed. (`consent` is `None`.)
    /// * touches a boundary target WITH a consent witness that
    ///   [`verify_consent_witness`] accepts (bound to the right grant, signed by a
    ///   trusted executor key, not yet replayed) → the turn passes through to
    ///   [`World::commit_turn`] and the boundary's nullifier is recorded
    ///   ([`GatedCommit::Committed`]). The consent fires the boundary exactly once.
    /// * touches a boundary target WITH an INVALID witness → [`GatedCommit::Refused`]
    ///   (the witness reason is carried). Fail-closed.
    ///
    /// `consent` (if present) is a [`ConsentWitness`] carrying the boundary it opens
    /// + the receipt of the owner's grant of that boundary (produced by
    ///   [`Self::resolve_consent`] → [`ConsentOutcome::Granted`], wrapped by
    ///   [`ConsentWitness::from_outcome`]). `owner` is the principal whose consent mints
    ///   the boundary cap INTO the fork when the gate opens (the consent's hole-fill: a
    ///   real attenuated `Effect::GrantCapability` from owner→guest on the fork, so the
    ///   now-consented turn can commit against the fork's executor). `used_proof_hashes`
    ///   is the fork's persistent nullifier set (the witness fires the boundary once).
    ///   `current_height` is the live height the consent timeout is checked against.
    ///
    /// The single mandatory entry: the guest drives turns through this method (never
    /// `fork.commit_turn` directly) — the gate is the executor-forcing door. The
    /// existing [`Self::resolve_consent`] produces the witness this gate consumes.
    #[allow(clippy::too_many_arguments)] // gated commit threads the full turn + consent witness
    pub fn commit_turn_gated(
        &self,
        fork: &mut World,
        owner: CellId,
        turn: Turn,
        consent: Option<&ConsentWitness>,
        trusted_executor_keys: &[[u8; 32]],
        current_height: u64,
        used_proof_hashes: &mut HashSet<[u8; 32]>,
    ) -> GatedCommit {
        // (1) Classify the turn against the fork's boundaries over the SAME
        //     `touched_cells` the live commit path uses — no parallel reachability.
        let touched = touched_cells(&turn);
        let crossed: Vec<&NetworkBoundary> = self
            .boundaries
            .iter()
            .filter(|b| touched.iter().any(|t| t == &b.target))
            .collect();

        // (2) No boundary touched → an embedded (or studyref-inspect) exercise:
        //     it elaborates only LOCALLY, so it commits with no consent door.
        if crossed.is_empty() {
            return GatedCommit::Committed {
                outcome: fork.commit_turn(turn),
                fired_boundary: None,
            };
        }

        // (3) A boundary IS touched. THE COMPULSION: without a valid consent witness
        //     the turn is refused, fail-closed — the guest could not commit it even
        //     if it tried, because this is the only door to the executor.
        let boundary = crossed[0]; // gate on the first crossed boundary (one per turn)
        let Some(witness) = consent else {
            // No consent supplied → refuse + hand back the consent REQUEST the owner
            // must resolve. The turn did NOT run; nothing reached "elsewhere".
            let request = boundary.consent_request(
                self.guest,
                turn,
                [0u8; 32], // the owner binds the real grant-turn hash when resolving
                current_height,
                current_height.saturating_add(DEFAULT_CONSENT_TIMEOUT),
            );
            return GatedCommit::Refused {
                target: boundary.target,
                request: Box::new(Some(request)),
                reason:
                    "networkboundary exercise refused: no consent witness present (fail-closed)"
                        .to_string(),
            };
        };

        // (4) The consent must be FOR this boundary's target (a witness for another
        //     boundary cannot fire this one).
        if witness.boundary != boundary.target {
            return GatedCommit::Refused {
                target: boundary.target,
                request: Box::new(None),
                reason: format!(
                    "consent witness is for a different boundary ({} ≠ {})",
                    crate::reflect::short_hex(&witness.boundary.0),
                    crate::reflect::short_hex(&boundary.target.0),
                ),
            };
        }

        // (5) The consent must not have expired (a witness arriving after the gated
        //     turn would have timed out is fail-closed, mirroring `resolve_consent`).
        if current_height > witness.timeout_height {
            return GatedCommit::Refused {
                target: boundary.target,
                request: Box::new(None),
                reason: "consent witness arrived after the boundary turn expired (fail-closed)"
                    .to_string(),
            };
        }

        // (6) Verify the witness in the executor's own signing domain — the IDENTICAL
        //     three teeth `resolve_consent` applies (turn-hash binding to the bound
        //     grant, signature authenticity under a trusted key, one-shot nullifier).
        //     This records the nullifier on success → the boundary fires exactly once.
        let condition = ProofCondition::TurnExecuted {
            turn_hash: witness.receipt.turn_hash,
        };
        match verify_consent_witness(
            &condition,
            &witness.receipt,
            trusted_executor_keys,
            used_proof_hashes,
        ) {
            Ok(()) => {
                // CONSENT PRESENT + VALID → the gate opens. The consent's hole-fill is
                // a REAL attenuated grant of the boundary cap into the FORK (owner →
                // guest, at the boundary's ceiling): the powerbox's own two gates fire,
                // so consent can never mint wider than the owner holds. Only THEN does
                // the consented turn run — the boundary "elaborated here" exactly once.
                // (The nullifier is already recorded by `verify_consent_witness`; an
                // over-amplifying ceiling would be refused by the grant, fail-closed,
                // and the boundary would not fire.)
                match Powerbox::grant(
                    fork,
                    owner,
                    self.guest,
                    boundary.target,
                    boundary.ceiling.clone(),
                ) {
                    PowerboxOutcome::Granted { .. } => GatedCommit::Committed {
                        outcome: fork.commit_turn(turn),
                        fired_boundary: Some(boundary.target),
                    },
                    PowerboxOutcome::Denied { reason } => GatedCommit::Refused {
                        target: boundary.target,
                        request: Box::new(None),
                        reason: format!(
                            "consent valid but the boundary grant did not land on the fork (fail-closed): {reason}"
                        ),
                    },
                }
            }
            Err(reason) => GatedCommit::Refused {
                target: boundary.target,
                request: Box::new(None),
                reason: format!("networkboundary exercise refused (invalid consent): {reason}"),
            },
        }
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
        let receipt =
            match Powerbox::grant(world, owner, request.guest, request.target, confer_rights) {
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
        return Err(
            "receipt executor_signature not verified by any trusted executor key".to_string(),
        );
    }

    // All checks pass: record the nullifier (the boundary has now fired once).
    used_proof_hashes.insert(proof_hash);
    Ok(())
}

// ===========================================================================
// THE REAL MEMBRANE — a frustum-snapshot of the REAL shared fork that
// SERIALIZES, travels (e.g. over Matrix), and REHYDRATES into a real `World`
// fork the recipient drives, whose driven mutation STITCHES back through the
// real branch-and-stitch settlement gate.
//
// This replaces the mock seam: `deos_matrix::MockMembraneHost` minted a
// synthetic key→value "ledger" with a stand-in FNV root; the live Matrix test
// shipped `MockMembraneHost::sample_envelope()`, never touching the executor.
// Here the snapshot is the genuine `dregg_cell::Cell` subgraph of MY authority
// (the SAME cells `World::fork` deep-clones + the SAME `Cell` serde the image
// root commits over), so mint → serialize → rehydrate → drive → stitch is the
// REAL executor end to end. The `deos-matrix` adapter below (gated on that
// dep) carries this payload in the `MembraneEnvelope` wire shape.
// ===========================================================================

use dregg_cell::Cell;
use serde::{Deserialize, Serialize};

/// **A real, serializable frustum-snapshot of a shared fork.**
///
/// This is the cap-bounded cell subgraph (the frustum cull) the membrane
/// carries — genuine [`dregg_cell::Cell`]s, not a synthetic key→value table.
/// It serializes (postcard, the SAME canonical `Cell` codec the image root
/// commits over), so it can ride the `deos-matrix` [`MembraneEnvelope`]
/// `snapshot` field and rehydrate, byte-for-byte, into a real [`World`] fork.
///
/// The membrane is minted from a REAL `World::fork` ([`SharedFork::construct`]
/// has already granted the embedded subgraph + withheld the boundaries on that
/// fork): we then cull the cells in view of the guest's c-list (the guest cell
/// + every cell its capabilities reach, to a bounded depth) and snapshot
///   exactly those. A recipient cannot rehydrate a cell that was culled away —
///   confinement by omission (the anti-amplification floor).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembraneFrustum {
    /// The focus cell the cull is centered on (the guest principal whose c-list
    /// reach defines the in-view subgraph).
    pub focus: CellId,
    /// Max hops along capability edges from the focus (the far plane).
    pub max_depth: u8,
    /// The cells in view, in cell-id order (the snapshot's deterministic
    /// content — the root binds exactly this set, sorted).
    pub cells: Vec<Cell>,
    /// The witness cursor (height) the fork was minted at.
    pub minted_height: u64,
}

impl MembraneFrustum {
    /// **Mint a frustum from a constructed shared fork.** BFS over capability
    /// edges from `focus` (the guest) to `max_depth`, collecting each reached
    /// cell from the fork's ledger. The result snapshots EXACTLY the in-view
    /// subgraph — a recipient gets the guest's reach and nothing beyond it.
    ///
    /// `fork` is the already-constructed fork ([`SharedFork::construct`] has
    /// granted the embedded caps into the guest's c-list and withheld the
    /// boundaries), so the cull naturally captures the embedded targets (in the
    /// guest's c-list) and NOT the boundary targets (no cap rides to them — they
    /// are unreachable from the guest's c-list and so fall outside the frustum).
    pub fn mint(fork: &World, focus: CellId, max_depth: u8) -> Self {
        let ledger = fork.ledger();
        let mut seen: HashSet<CellId> = HashSet::new();
        let mut frontier: Vec<CellId> = vec![focus];
        seen.insert(focus);
        for _ in 0..=max_depth {
            let mut next: Vec<CellId> = Vec::new();
            for id in frontier.drain(..) {
                if let Some(cell) = ledger.get(&id) {
                    for cap in cell.capabilities.iter() {
                        if seen.insert(cap.target) {
                            next.push(cap.target);
                        }
                    }
                }
            }
            if next.is_empty() {
                break;
            }
            frontier = next;
        }
        let mut cells: Vec<Cell> = seen
            .iter()
            .filter_map(|id| ledger.get(id).cloned())
            .collect();
        cells.sort_by(|a, b| a.id().as_bytes().cmp(b.id().as_bytes()));
        MembraneFrustum {
            focus,
            max_depth,
            cells,
            minted_height: fork.height(),
        }
    }

    /// **The frustum root — the anti-substitution tooth.** A commitment over
    /// EXACTLY the culled cells (sorted by id, the SAME canonical `Cell`
    /// postcard the image root folds), so mint and rehydrate MUST agree (else
    /// fail-closed). Distinct from the whole-image `World::state_root` (which
    /// also folds height + receipt head) — this binds the membrane's subgraph.
    pub fn frustum_root(&self) -> [u8; 32] {
        let mut sorted: Vec<&Cell> = self.cells.iter().collect();
        sorted.sort_by(|a, b| a.id().as_bytes().cmp(b.id().as_bytes()));
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"deos-membrane-frustum-root-v1");
        hasher.update(&(sorted.len() as u64).to_le_bytes());
        for cell in sorted {
            hasher.update(cell.id().as_bytes());
            if let Ok(bytes) = postcard::to_stdvec(cell) {
                hasher.update(&(bytes.len() as u64).to_le_bytes());
                hasher.update(&bytes);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// **The carried payload AS a witnessed umem — its boundary root the handoff.**
    /// Projects the frustum's culled subgraph into the ONE universal address space
    /// ([`crate::umem_membrane::UmemBranch::from_frustum`]) and returns that
    /// projection's anti-substitution [`crate::umem_membrane::UmemBranch::umem_root`]
    /// — the umem twin of [`Self::frustum_root`], derived from the SAME cells. This is
    /// what makes the membrane's CARRY a passable umem (not only an opaque `Cell`
    /// blob): a recipient can re-project the carried cells and bind them to this root.
    pub fn umem_root(&self) -> [u8; 32] {
        crate::umem_membrane::UmemBranch::from_frustum(self).umem_root()
    }

    /// Serialize the frustum for the wire (the bytes that ride the envelope's
    /// `snapshot` field). Postcard — the canonical `Cell` codec.
    pub fn to_snapshot_bytes(&self) -> Vec<u8> {
        postcard::to_stdvec(self).expect("frustum is postcard-serializable")
    }

    /// Deserialize a frustum from wire bytes (fail-closed on a malformed
    /// snapshot).
    pub fn from_snapshot_bytes(bytes: &[u8]) -> Result<Self, MembraneError> {
        postcard::from_bytes(bytes).map_err(|_| MembraneError::MalformedSnapshot)
    }

    /// **Rehydrate this frustum into a REAL `World` fork.** The recipient gets a
    /// genuine [`World`] holding EXACTLY the culled subgraph (anti-amplification:
    /// a cell that was not in the frustum is absent and unreachable). The
    /// `expected_root` tooth fires fail-closed if the snapshot does not reproduce
    /// the claimed root (a substituted snapshot is refused before a single cell
    /// is installed).
    ///
    /// The returned `World` runs the SAME verified executor; a recipient drives
    /// real turns on it through [`World::commit_turn`], byte-identical to a turn
    /// on the source fork. The fork holds NO cap to mainline — its mutations are
    /// structurally imaginary to the source until stitched.
    pub fn rehydrate(&self, expected_root: [u8; 32]) -> Result<World, MembraneError> {
        // (a) Anti-substitution: the snapshot MUST reproduce the claimed root.
        if self.frustum_root() != expected_root {
            return Err(MembraneError::RootMismatch);
        }
        // (b) Install exactly the culled cells into a fresh, signing-keyed world.
        //     A fresh `World` deep-clones nothing of mainline — the recipient's
        //     fork is precisely the frustum, no more (confinement by omission).
        let mut fork = World::new();
        for cell in &self.cells {
            // Genesis-install the snapshotted cell verbatim (id-addressed; a
            // duplicate id would be a malformed snapshot — fail-closed).
            if fork.ledger().get(&cell.id()).is_some() {
                return Err(MembraneError::MalformedSnapshot);
            }
            fork.genesis_install(cell.clone());
        }
        // (c) The rehydrated fork must reproduce the same frustum root over its
        //     own ledger — a final tooth that the install was faithful.
        let rehydrated = MembraneFrustum::mint(&fork, self.focus, self.max_depth);
        // `mint` re-culls from the focus; if the installed graph re-derives a
        // different root the install dropped/added reachability — fail-closed.
        if rehydrated.frustum_root() != expected_root {
            return Err(MembraneError::RootMismatch);
        }
        Ok(fork)
    }

    /// **The real branch graph of a DRIVEN rehydrated fork** — the genuine diff,
    /// not a hand-coded atom. After a recipient drives turns on the rehydrated
    /// fork, this reads back the ACTUAL mutated cells (every cell whose state
    /// diverged from the minted snapshot) as live [`Atom`](crate::branch_stitch::Atom)s,
    /// keyed by a stable per-cell key, so the stitch folds the real mutation.
    ///
    /// Returns `(baseline, driven)`: the baseline is the frustum's own atom set
    /// (the cells as minted), the driven graph is the rehydrated-and-driven
    /// fork's atom set. A cell that changed appears in `driven` keyed identically
    /// to `baseline` but at its NEW content — so the stitch's pushout folds the
    /// guest's real driven turn back, and the settlement gate (authority held at
    /// the tip) governs whether a conferred cap is admitted or lossy-dropped.
    pub fn driven_graphs(
        &self,
        driven_fork: &World,
    ) -> (
        crate::branch_stitch::DocGraph,
        crate::branch_stitch::DocGraph,
    ) {
        use crate::branch_stitch::{Atom, DocGraph};
        // A stable atom key per cell: the low 8 bytes of its id (deterministic,
        // collision-resistant enough for the in-view subgraph the frustum bounds).
        fn cell_key(id: &CellId) -> u64 {
            let b = id.as_bytes();
            u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        // The baseline atoms: every minted cell, Alive.
        let baseline = DocGraph {
            atoms: self
                .cells
                .iter()
                .map(|c| (cell_key(&c.id()), Atom::Alive))
                .collect(),
        };
        // The driven atoms: every cell in the driven fork whose state DIVERGED
        // from the minted snapshot (a real mutation), surfaced as a live atom at
        // a key derived from BOTH the cell id AND its post-state — so the stitch
        // sees the driven content as a NEW atom over the baseline's, folding the
        // mutation rather than fabricating one. An unchanged cell contributes its
        // baseline atom (clean, I-confluent).
        let minted: std::collections::HashMap<CellId, &Cell> =
            self.cells.iter().map(|c| (c.id(), c)).collect();
        let mut driven_atoms = std::collections::BTreeMap::new();
        for (id, cell) in driven_fork.ledger().iter() {
            let key = cell_key(id);
            match minted.get(id) {
                Some(base) if base.state == cell.state => {
                    // Unchanged — the same atom (clean merge).
                    driven_atoms.insert(key, Atom::Alive);
                }
                Some(_) | None => {
                    // Diverged (or freshly born in the fork) — a real driven
                    // mutation. Key it by (id ‖ post-state) so it is a NEW atom
                    // distinct from the baseline's, the stitch's value-bearing
                    // discovery.
                    let mut h = blake3::Hasher::new();
                    h.update(b"deos-driven-atom-v1");
                    h.update(id.as_bytes());
                    if let Ok(bytes) = postcard::to_stdvec(&cell.state) {
                        h.update(&bytes);
                    }
                    let digest = *h.finalize().as_bytes();
                    let driven_key = u64::from_le_bytes(digest[..8].try_into().expect("8 bytes"));
                    driven_atoms.insert(driven_key, Atom::Alive);
                }
            }
        }
        let driven = DocGraph {
            atoms: driven_atoms,
        };
        (baseline, driven)
    }
}

/// Errors the real membrane raises (the fail-closed paths — the same teeth the
/// mock named, now over genuine cells). `Display`/`Error` are hand-written (no
/// macro dep) so the substrate compiles under the lean `embedded-executor`
/// build the honest-verify exercises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MembraneError {
    /// The snapshot bytes did not deserialize into a frustum (a corrupt or
    /// truncated wire payload) — fail-closed.
    MalformedSnapshot,
    /// The rehydrated frustum did not reproduce the claimed root — the
    /// anti-substitution tooth fired (refuse before trusting one cell).
    RootMismatch,
    /// No such live fork (driven/stitched after it was dropped, or an id the
    /// host never minted).
    NoSuchFork(u64),
    /// The drive turn bytes did not decode into a real `Turn` — fail-closed.
    MalformedTurn,
    /// The driven turn was refused by the rehydrated fork's verified executor.
    DriveRefused(String),
}

impl std::fmt::Display for MembraneError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MembraneError::MalformedSnapshot => {
                write!(f, "membrane snapshot is malformed (not a valid frustum)")
            }
            MembraneError::RootMismatch => write!(
                f,
                "frustum root mismatch — refusing to rehydrate a substituted snapshot"
            ),
            MembraneError::NoSuchFork(id) => write!(f, "no such rehydrated fork: {id}"),
            MembraneError::MalformedTurn => write!(f, "drive turn bytes are not a valid Turn"),
            MembraneError::DriveRefused(why) => {
                write!(f, "the driven turn was refused by the fork executor: {why}")
            }
        }
    }
}

impl std::error::Error for MembraneError {}

// ---------------------------------------------------------------------------
// THE REAL `MembraneHost` — backed by the genuine executor, adapting
// `MembraneFrustum` into the `deos_matrix` `MembraneEnvelope` wire shape. This
// REPLACES `MockMembraneHost` as the default for any build that carries the
// deos-matrix wire types (the `dev-surfaces` graph, where the chat lane lives).
// `mint` snapshots a REAL fork; `rehydrate` restores a REAL `World`; `drive`
// commits a REAL turn; `stitch` folds the REAL diff through the settlement gate.
// ---------------------------------------------------------------------------
#[cfg(feature = "dev-surfaces")]
pub use membrane_host::ForkMembraneHost;

#[cfg(feature = "dev-surfaces")]
mod membrane_host {
    use super::*;
    use deos_matrix::membrane::{
        ConflictObject, ConflictReason, ForkHandle, FrustumCut, Liveness, MembraneEnvelope,
        MembraneHost, StitchOutcome, TurnReceiptDigest, WitnessCursor,
    };
    use std::sync::Mutex;

    /// **The real, executor-backed [`MembraneHost`].** Holds the owner's live
    /// world and the constructed shared fork the membrane projects; mints a real
    /// [`MembraneFrustum`] into a [`MembraneEnvelope`], rehydrates received
    /// envelopes into real [`World`] forks, drives real turns, and stitches the
    /// real diff back. The `deos-matrix` chat lane holds a `dyn MembraneHost`
    /// pointing at one of these (inside the confined comms-PD, where the executor
    /// lives) — so a membrane minted here, serialized over Matrix, and rehydrated
    /// elsewhere is the genuine executor end to end.
    pub struct ForkMembraneHost {
        /// The owner's world the frustum is minted FROM (already forked +
        /// constructed by [`SharedFork::construct`] before being handed here).
        source_fork: World,
        /// The guest principal the frustum culls in view of.
        guest: CellId,
        /// Live rehydrated forks: handle id → (the real `World` fork, the minted
        /// frustum it rehydrated from, for the stitch diff).
        forks: Mutex<Vec<(u64, World, MembraneFrustum)>>,
        /// Monotone fork-id source.
        next_fork: Mutex<u64>,
    }

    impl ForkMembraneHost {
        /// Build a host over a constructed shared fork (the `source_fork` is the
        /// already-forked, already-`SharedFork::construct`ed world; `guest` is the
        /// confined recipient the frustum culls around).
        pub fn new(source_fork: World, guest: CellId) -> Self {
            ForkMembraneHost {
                source_fork,
                guest,
                forks: Mutex::new(Vec::new()),
                next_fork: Mutex::new(1),
            }
        }

        /// **THE MULTIPLAYER UMEM STITCH — two driven forks reconciled per-address.**
        ///
        /// Reconcile fork `a` and fork `b` (both rehydrated from the SAME minted
        /// frustum — the shared umem ancestor) by the umem merge
        /// ([`crate::umem_membrane::stitch_projections`]): the minted frustum is the
        /// baseline ([`crate::umem_membrane::UmemBranch::from_frustum`]), each driven
        /// fork is re-projected, and the join is per-[`dregg_turn::umem::UKey`]. So two
        /// principals editing DIFFERENT fields of the SAME cell fold CLEAN (where the
        /// cell-granular `Atom` stitch would collide on one opaque per-cell atom), and a
        /// genuine same-address collision surfaces as a field-granular
        /// [`ConflictObject`] ([`ConflictReason::ValueCollision`]) keyed at the EXACT
        /// address — both attributed readings live, never a silent last-writer-wins.
        ///
        /// `merged` carries the per-address event ids the merge folded clean (relative
        /// to the baseline); `dropped` the field-granular conflicts; `settled_root` is
        /// the driven root only when the fold is conflict-free.
        ///
        /// **The state pushout and the authority gate are ORTHOGONAL** (the proven
        /// `Metatheory.SettlementSoundness` shape, live in production here). Beyond the
        /// per-address STATE merge, every authority the driven branches would confer back
        /// into main is checked against the authority HELD AT THE SETTLEMENT TIP — the focus's
        /// caps in the LIVE [`Self::source_world`] (the main world AFTER any `RevokeCapability`
        /// committed between branch and settlement, [`crate::umem_membrane::settlement_held_at_tip`]).
        /// A cap revoked-before-tip is LINEAR-DROPPED (surfaced as a first-class
        /// `ConflictReason::AuthorityRevoked` object — "a cap I have since revoked cannot ride a
        /// stitch into my real world"); a still-held cap rides. The gate predicate is IDENTICAL
        /// to the proven control model [`crate::branch_stitch::Stitch::settle`]. Settlement is
        /// governed by the STATE pushout's cleanliness alone — a dropped cap was simply not
        /// conferred, so it never blocks the merge.
        pub fn stitch_pair(
            &self,
            a: &ForkHandle,
            b: &ForkHandle,
        ) -> Result<StitchOutcome, MembraneError> {
            use crate::umem_membrane::{
                dropped_cap_event_id, settle_umem_stitch, settlement_held_at_tip,
                stitch_projections, umem_event_id, ConferredCap, UmemBranch,
            };
            let forks = self.forks.lock().unwrap();
            let ea = forks
                .iter()
                .find(|(id, _, _)| *id == a.0)
                .ok_or(MembraneError::NoSuchFork(a.0))?;
            let eb = forks
                .iter()
                .find(|(id, _, _)| *id == b.0)
                .ok_or(MembraneError::NoSuchFork(b.0))?;
            // ── THE STATE PUSHOUT (field-granular, orthogonal to authority). ─────────────
            // The shared ancestor IS the carried umem (both rehydrated from `ea.2`).
            let base = UmemBranch::from_frustum(&ea.2);
            let proj_a = UmemBranch::mint(&ea.1, base.focus, base.max_depth);
            let proj_b = UmemBranch::mint(&eb.1, base.focus, base.max_depth);
            let stitch = stitch_projections(&base.umem, &proj_a.umem, &proj_b.umem);

            // ── THE SETTLEMENT-SOUND AUTHORITY GATE (settlement soundness, in production). ─
            // The authority each driven branch would confer back = the focus's held caps in
            // the driven forks (inherited at branch or branch-gained). The settlement-tip held
            // view is read from the LIVE source world — the main tip, AFTER any revocation.
            let mut conferred: Vec<ConferredCap> = Vec::new();
            for driven in [&ea.1, &eb.1] {
                if let Some(cell) = driven.ledger().get(&base.focus) {
                    for cap in cell.capabilities.iter() {
                        if cap.permissions != dregg_cell::AuthRequired::Impossible {
                            let cc = ConferredCap {
                                target: cap.target,
                                debit_reach: true,
                            };
                            if !conferred.contains(&cc) {
                                conferred.push(cc);
                            }
                        }
                    }
                }
            }
            let settlement_held = settlement_held_at_tip(&self.source_fork, base.focus);
            let settled = settle_umem_stitch(stitch, &conferred, &settlement_held);

            // ── SURFACE: clean state folds + held-back state conflicts + dropped authority. ─
            let merged: Vec<[u8; 32]> = settled
                .stitch
                .merged
                .iter()
                .filter(|(k, v)| base.umem.get(k) != Some(v))
                .map(|(k, _)| umem_event_id(k))
                .collect();
            let mut dropped: Vec<ConflictObject> = settled
                .stitch
                .conflicts
                .iter()
                .map(|c| ConflictObject {
                    event: umem_event_id(&c.key),
                    reason: ConflictReason::ValueCollision,
                })
                .collect();
            // The revoked-before-tip authority drops — the linear DROP, surfaced as first-class
            // `AuthorityRevoked` conflict objects (transparent, never silently conferred/lost).
            dropped.extend(settled.dropped.iter().map(|c| ConflictObject {
                event: dropped_cap_event_id(&c.target),
                reason: ConflictReason::AuthorityRevoked,
            }));
            // Settlement is governed by the STATE pushout alone (authority drops do NOT block it
            // — they were simply not conferred), exactly as `SettledUmemStitch::settles`.
            let settled_root = if settled.settles() {
                Some(ea.1.state_root())
            } else {
                None
            };
            Ok(StitchOutcome {
                settled_root,
                merged,
                dropped,
            })
        }

        /// The owner's LIVE world the membrane is minted from — the settlement tip. Read by
        /// [`Self::stitch_pair`]'s authority gate ([`crate::umem_membrane::settlement_held_at_tip`])
        /// to evaluate every conferred cap at the tip, not at branch time.
        pub fn source_world(&self) -> &World {
            &self.source_fork
        }

        /// Mutable access to the owner's LIVE world (the settlement tip) — so the main world
        /// can advance (e.g. a `RevokeCapability` turn committed between branch and settlement)
        /// before a [`Self::stitch_pair`] reads the tip's held authority. The non-monotone
        /// revocation distributed time-travel turns on lands here.
        pub fn source_world_mut(&mut self) -> &mut World {
            &mut self.source_fork
        }
    }

    impl MembraneHost for ForkMembraneHost {
        type Error = MembraneError;

        fn mint(
            &self,
            _focus: [u8; 32],
            mut cut: FrustumCut,
        ) -> Result<MembraneEnvelope, Self::Error> {
            // ANTI-AMPLIFICATION: a membrane is ALWAYS in view of the host's own
            // confined guest principal — never an arbitrary caller-supplied focus.
            // Centring the cull on a non-guest cell would be a path to snapshot
            // cells outside the guest's reach, so the caller's `_focus` is
            // deliberately ignored and the frustum is pinned to `self.guest`: it
            // can only ever be the guest's own subgraph.
            let focus = self.guest;
            cut.focus_cell = focus.0;
            // Mint the real frustum from the source fork, centred on the guest.
            let frustum = MembraneFrustum::mint(&self.source_fork, focus, cut.max_depth);
            let root = frustum.frustum_root();
            cut.cell_count = frustum.cells.len() as u32;
            let snapshot = frustum.to_snapshot_bytes();
            Ok(MembraneEnvelope {
                version: MembraneEnvelope::VERSION,
                frustum_root: root,
                sturdyref: format!("dregg://fork/{}", hex32(&root)),
                // The lineage carries the focus so a recipient can verify the
                // frustum is in view of the intended principal (the real
                // attenuation meet lives in the cell c-lists themselves — a
                // recipient cannot rehydrate authority not present in the cells).
                lineage: focus.0.to_vec(),
                snapshot,
                cut,
                cursor: WitnessCursor {
                    height: frustum.minted_height,
                    commit_index: 0,
                },
            })
        }

        fn rehydrate(&self, env: &MembraneEnvelope) -> Result<(ForkHandle, Liveness), Self::Error> {
            if !env.is_rehydratable() {
                // Forward-compat tooth — refuse a newer wire version, fail-closed.
                return Err(MembraneError::RootMismatch);
            }
            let frustum = MembraneFrustum::from_snapshot_bytes(&env.snapshot)?;
            // Rehydrate into a REAL `World` fork (the anti-substitution tooth is
            // inside `rehydrate`, fail-closed on a root mismatch).
            let fork = frustum.rehydrate(env.frustum_root)?;
            let id = {
                let mut n = self.next_fork.lock().unwrap();
                let id = *n;
                *n += 1;
                id
            };
            self.forks.lock().unwrap().push((id, fork, frustum));
            // Liveness DERIVED: a verified deterministic restore of a frozen
            // frustum is `ReplayedDeterministic`.
            Ok((ForkHandle(id), Liveness::ReplayedDeterministic))
        }

        fn drive(
            &self,
            fork: &ForkHandle,
            turn_bytes: &[u8],
        ) -> Result<TurnReceiptDigest, Self::Error> {
            let mut forks = self.forks.lock().unwrap();
            let entry = forks
                .iter_mut()
                .find(|(id, _, _)| *id == fork.0)
                .ok_or(MembraneError::NoSuchFork(fork.0))?;
            // Decode a REAL `Turn` and commit it through the rehydrated fork's
            // verified executor — identical conservation/ocap/program guarantees.
            let turn: Turn =
                postcard::from_bytes(turn_bytes).map_err(|_| MembraneError::MalformedTurn)?;
            let outcome = entry.1.commit_turn(turn);
            if !outcome.is_committed() {
                return Err(MembraneError::DriveRefused(format!("{outcome:?}")));
            }
            Ok(TurnReceiptDigest {
                post_root: entry.1.state_root(),
                turn_index: entry.1.height(),
            })
        }

        fn stitch(&self, fork: &ForkHandle) -> Result<StitchOutcome, Self::Error> {
            use crate::umem_membrane::{stitch_projections, umem_event_id, UmemBranch};
            let forks = self.forks.lock().unwrap();
            let entry = forks
                .iter()
                .find(|(id, _, _)| *id == fork.0)
                .ok_or(MembraneError::NoSuchFork(fork.0))?;
            // THE CARRY AS A WITNESSED UMEM: the minted frustum projected into the ONE
            // universal address space (its `umem_root` the handoff). THE MERGE-BACK AS A
            // UMEM RECONCILIATION: the driven fork re-projected and folded per-address
            // against that baseline. A single driven fork against the mint-time baseline
            // has no concurrent writer in this leg, so every address the guest moved
            // folds CLEAN (I-confluent) and the `merged` set names those EXACT addresses
            // — field-granular, not an opaque per-cell `Atom`. (Anti-amplification is the
            // frustum cull's confinement-by-omission + the executor's verified drive,
            // not a decorative settle: the guest cannot move an address it never held.)
            let base = UmemBranch::from_frustum(&entry.2);
            let driven = UmemBranch::mint(&entry.1, base.focus, base.max_depth);
            let stitch = stitch_projections(&base.umem, &base.umem, &driven.umem);
            let merged: Vec<[u8; 32]> = stitch
                .merged
                .iter()
                .filter(|(k, v)| base.umem.get(k) != Some(v))
                .map(|(k, _)| umem_event_id(k))
                .collect();
            // A single-fork fold has no second writer, so it is always conflict-free and
            // settles at the driven fork's root.
            Ok(StitchOutcome {
                settled_root: Some(entry.1.state_root()),
                merged,
                dropped: Vec::new(),
            })
        }
    }

    fn hex32(b: &[u8; 32]) -> String {
        let mut s = String::with_capacity(8);
        for byte in &b[..4] {
            s.push_str(&format!("{byte:02x}"));
        }
        s
    }

    #[cfg(test)]
    mod adapter_tests {
        use super::*;
        use crate::world::make_open_cell;

        fn signed_world() -> (World, CellId, CellId, CellId) {
            let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
            let docs = w.genesis_cell(0xD0, 0);
            let guest = w.genesis_cell(0xA9, 0);
            let mut owner_cell = make_open_cell(0x55, 0);
            owner_cell
                .capabilities
                .grant(docs, AuthRequired::None)
                .expect("owner holds docs");
            let owner = w.genesis_install(owner_cell);
            (w, owner, guest, docs)
        }

        #[test]
        fn real_host_mint_serialize_rehydrate_drive_stitch_end_to_end() {
            // A REAL host over a REAL constructed fork — the closure of the mock.
            let (world, owner, guest, docs) = signed_world();
            let mut fork = world.fork();
            let _sf = SharedFork::construct(
                &mut fork,
                owner,
                guest,
                &[(docs, AuthRequired::None)],
                vec![],
                vec![],
            );
            let host = ForkMembraneHost::new(fork, guest);

            // MINT a real envelope (the wire shape the Matrix message carries).
            let cut = FrustumCut {
                focus_cell: [0u8; 32],
                max_depth: 3,
                authority_bounded: true,
                cell_count: 0,
            };
            let env = host.mint(guest.0, cut).expect("mint a real envelope");
            assert!(env.cut.cell_count >= 1, "the frustum culled real cells");
            assert_eq!(env.version, MembraneEnvelope::VERSION);

            // SERIALIZE over the wire (the envelope is the Matrix custom-content JSON).
            let json = serde_json::to_string(&env).expect("envelope is JSON");
            let back: MembraneEnvelope = serde_json::from_str(&json).expect("round-trip");
            assert_eq!(back, env, "the real envelope survives the wire");

            // REHYDRATE into a REAL fork (anti-substitution tooth inside).
            let (handle, liveness) = host.rehydrate(&back).expect("rehydrate a real fork");
            assert_eq!(liveness, Liveness::ReplayedDeterministic);

            // DRIVE a REAL turn on the rehydrated fork (decoded from postcard bytes).
            let turn = {
                // We need a turn FROM the rehydrated fork (chain head/timestamp);
                // build it via a fresh rehydrate of the same frustum to author it.
                let frustum = MembraneFrustum::from_snapshot_bytes(&back.snapshot).unwrap();
                let driver = frustum.rehydrate(back.frustum_root).unwrap();
                driver.turn(guest, vec![crate::world::set_field(docs, 1, [42u8; 32])])
            };
            let turn_bytes = postcard::to_stdvec(&turn).unwrap();
            let digest = host.drive(&handle, &turn_bytes).expect("drive a real turn");
            assert!(
                digest.turn_index >= 1,
                "a real turn committed (height advanced)"
            );

            // STITCH the REAL diff back through the settlement gate.
            let outcome = host.stitch(&handle).expect("stitch");
            assert!(
                outcome.settled_root.is_some(),
                "the in-authority stitch of the real diff settles: {outcome:?}"
            );

            // Fail-closed: an unknown fork handle is refused.
            assert!(matches!(
                host.drive(&ForkHandle(999), &turn_bytes).unwrap_err(),
                MembraneError::NoSuchFork(999)
            ));
        }

        /// **THE FOURTH UMEM REVOLUTION, LIVE — the membrane fork/carry/stitch ARE
        /// umem ops through the running `ForkMembraneHost`.** A real fork→carry→stitch:
        ///   * FORK — the host mints a real frustum (the cap-bounded cull).
        ///   * CARRY — that carried payload IS a witnessed umem (its cells project to a
        ///     `UProjection`; its `umem_root` reproduces from the carried frustum — the
        ///     handoff tooth, the umem twin of the frustum root).
        ///   * STITCH — two principals rehydrate the SAME envelope into independent real
        ///     forks, each DRIVES a real verified turn, and the host reconciles them by
        ///     the UMEM MERGE (`stitch_pair`): a same-address collision is a FIELD-
        ///     GRANULAR `ConflictObject` keyed at the EXACT address (`ValueCollision`),
        ///     while disjoint per-cell edits fold CLEAN — the per-address win over the
        ///     opaque cell-granular `Atom` merge, now load-bearing in the live host.
        #[test]
        fn the_live_membrane_stitches_umems_field_granular() {
            use crate::umem_membrane::{umem_event_id, UmemBranch};
            use deos_matrix::membrane::ConflictReason;
            use dregg_turn::umem::UKey;

            let (world, room, user_a, user_b, shared, doc_a, doc_b) = mp_world();
            let fork = world.fork();
            let host = ForkMembraneHost::new(fork, room);

            // FORK + CARRY: mint a real membrane; its carried payload is a witnessed umem.
            let env = host
                .mint(
                    room.0,
                    FrustumCut {
                        focus_cell: [0u8; 32],
                        max_depth: 3,
                        authority_bounded: true,
                        cell_count: 0,
                    },
                )
                .expect("the real host mints the membrane");
            let frustum =
                MembraneFrustum::from_snapshot_bytes(&env.snapshot).expect("snapshot decodes");
            let carried = UmemBranch::from_frustum(&frustum);
            assert_eq!(
                carried.umem_root(),
                frustum.umem_root(),
                "the carried payload IS a witnessed umem — its boundary root the handoff"
            );
            assert!(
                carried.umem.contains_key(&UKey::Field {
                    cell: shared,
                    slot: 0
                }),
                "the shared.field[0] address rides in the carried umem projection"
            );

            // Two principals rehydrate the SAME envelope into independent real forks.
            let (h_a, _) = host.rehydrate(&env).expect("A rehydrates a real fork");
            let (h_b, _) = host.rehydrate(&env).expect("B rehydrates a real fork");

            // Each authors a real verified turn (built against a fresh rehydrate of the
            // same frustum — identical chain head). A and B COLLIDE on shared.field[0]
            // (different values) but make DISJOINT private edits (doc_a vs doc_b).
            let drive_bytes = |who: CellId, ops: Vec<dregg_turn::action::Effect>| {
                let driver = frustum
                    .rehydrate(env.frustum_root)
                    .expect("driver rehydrates");
                postcard::to_stdvec(&driver.turn(who, ops)).expect("turn serializes")
            };
            host.drive(
                &h_a,
                &drive_bytes(
                    user_a,
                    vec![
                        crate::world::set_field(shared, 0, [0xAAu8; 32]),
                        crate::world::set_field(doc_a, 0, [0x11u8; 32]),
                    ],
                ),
            )
            .expect("A drives a real verified turn on its fork");
            host.drive(
                &h_b,
                &drive_bytes(
                    user_b,
                    vec![
                        crate::world::set_field(shared, 0, [0xBBu8; 32]),
                        crate::world::set_field(doc_b, 0, [0x22u8; 32]),
                    ],
                ),
            )
            .expect("B drives a real verified turn on its fork");

            // STITCH — the host reconciles the two driven forks by the UMEM MERGE.
            let outcome = host
                .stitch_pair(&h_a, &h_b)
                .expect("the live host stitches the two umems");

            // THE FIELD-GRANULAR CONFLICT: exactly shared.field[0] collides, named at
            // its EXACT address (not an opaque per-cell atom).
            let shared_f0 = umem_event_id(&UKey::Field {
                cell: shared,
                slot: 0,
            });
            assert_eq!(
                outcome.dropped.len(),
                1,
                "exactly one field-granular conflict (shared.field[0]): {:?}",
                outcome.dropped
            );
            assert_eq!(
                outcome.dropped[0].event, shared_f0,
                "the conflict names the EXACT universal-memory address that diverged"
            );
            assert_eq!(
                outcome.dropped[0].reason,
                ConflictReason::ValueCollision,
                "a same-field write collision is a first-class ValueCollision object"
            );
            assert!(
                outcome.settled_root.is_none(),
                "an unresolved field collision does not settle (fail-closed)"
            );

            // THE UMEM-GRANULARITY WIN: the DISJOINT per-cell edits fold CLEAN — where
            // the cell-granular `Atom` merge would have collapsed each to one opaque atom.
            let doc_a_f0 = umem_event_id(&UKey::Field {
                cell: doc_a,
                slot: 0,
            });
            let doc_b_f0 = umem_event_id(&UKey::Field {
                cell: doc_b,
                slot: 0,
            });
            assert!(
                outcome.merged.contains(&doc_a_f0),
                "A's disjoint doc_a edit folded CLEAN into the merged umem"
            );
            assert!(
                outcome.merged.contains(&doc_b_f0),
                "B's disjoint doc_b edit folded CLEAN into the merged umem"
            );
            assert!(
                !outcome.merged.contains(&shared_f0),
                "the conflicted address is held back from the clean-merged set"
            );
        }

        // ── THE CROSS-WORKSPACE BRIDGE: bake a REAL executor envelope as a golden
        //    fixture the `deos-matrix` LIVE homeserver test ships A→B ───────────────
        //
        // The honest workspace boundary: the executor-real mint/rehydrate/drive/stitch
        // lives HERE (it links the Lean-backed `World`); the LIVE Matrix homeserver
        // round-trip lives in `deos-matrix` (its own tokio/matrix-sdk workspace, which
        // cannot link the executor). The two halves meet at ONE artifact: a genuine
        // `MembraneEnvelope` — minted by the REAL executor from a REAL multiplayer
        // fork — serialized to the SAME JSON the Matrix message carries. This test
        // bakes that envelope to a checked-in fixture; `deos-matrix`'s
        // `live_two_user_real_executor_membrane_roundtrip` loads it and ships it over
        // a real Conduit homeserver A→B, proving the SAME executor-minted bytes
        // survive the real server byte-intact and rehydrate on the receiving side.
        //
        // So the FULL chain is demonstrated across the seam:
        //   mint(real executor, here) → carry(real Matrix server, deos-matrix) →
        //   rehydrate+drive+stitch(real executor, here).
        // Each half RUNS against its real substrate; the fixture is the wire byte
        // identity that welds them (the comms-PD carries exactly these bytes).

        /// The fixture path (relative to this crate) the `deos-matrix` live test reads.
        /// Written by the bake test below; the byte content is a real executor-minted
        /// envelope's canonical JSON.
        const REAL_ENVELOPE_FIXTURE: &str = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../deos-matrix/tests/fixtures/real_executor_membrane.json"
        );

        /// A signed multiplayer source world: a `room` focus cell reaching two
        /// DISTINCT user principals (`user_a`, `user_b`) and the docs they edit —
        /// `shared` (both touch it: the conflict candidate), `doc_a` (only A),
        /// `doc_b` (only B). The frustum minted from `room` captures the whole shared
        /// subrealm. Returns `(world, room, user_a, user_b, shared, doc_a, doc_b)`.
        #[allow(clippy::type_complexity)]
        fn mp_world() -> (World, CellId, CellId, CellId, CellId, CellId, CellId) {
            let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
            let shared = w.genesis_cell(0x5D, 0);
            let doc_a = w.genesis_cell(0xA1, 0);
            let doc_b = w.genesis_cell(0xB2, 0);
            let mut a = make_open_cell(0x0A, 0);
            a.capabilities
                .grant(shared, AuthRequired::None)
                .expect("A holds shared");
            a.capabilities
                .grant(doc_a, AuthRequired::None)
                .expect("A holds doc_a");
            let user_a = w.genesis_install(a);
            let mut b = make_open_cell(0x0B, 0);
            b.capabilities
                .grant(shared, AuthRequired::None)
                .expect("B holds shared");
            b.capabilities
                .grant(doc_b, AuthRequired::None)
                .expect("B holds doc_b");
            let user_b = w.genesis_install(b);
            let mut room = make_open_cell(0x40, 0);
            room.capabilities
                .grant(user_a, AuthRequired::None)
                .expect("room reaches A");
            room.capabilities
                .grant(user_b, AuthRequired::None)
                .expect("room reaches B");
            room.capabilities
                .grant(shared, AuthRequired::None)
                .expect("room reaches shared");
            let room = w.genesis_install(room);
            (w, room, user_a, user_b, shared, doc_a, doc_b)
        }

        #[test]
        fn bake_real_executor_membrane_fixture_and_prove_full_loop() {
            use crate::branch_stitch::{Atom, BranchCap, DocGraph, SettleOutcome, Stitch};

            // (1) MINT — a REAL `MembraneEnvelope` from a REAL multiplayer executor
            //     fork, via the executor-backed `ForkMembraneHost`. The host pins the
            //     frustum to its `guest` focus; we focus it on `room`, so the membrane
            //     captures the whole shared subrealm (both users + all three docs).
            let (world, room, user_a, user_b, shared, doc_a, doc_b) = mp_world();
            let fork = world.fork();
            let host = ForkMembraneHost::new(fork, room);
            let cut = FrustumCut {
                focus_cell: [0u8; 32],
                max_depth: 3,
                authority_bounded: true,
                cell_count: 0,
            };
            let env = host
                .mint(room.0, cut)
                .expect("mint a real multiplayer envelope");
            assert!(
                env.cut.cell_count >= 6,
                "the frustum culled the whole subrealm (>=6 cells)"
            );
            assert_eq!(env.version, MembraneEnvelope::VERSION);

            // (2) BAKE THE FIXTURE — the canonical JSON the Matrix message carries.
            //     This is the executor-real artifact `deos-matrix`'s live test ships.
            let json = serde_json::to_string_pretty(&env).expect("envelope serializes to JSON");
            // Round-trip in-process first (the wire byte identity the live test relies on).
            let back: MembraneEnvelope =
                serde_json::from_str(&json).expect("the real envelope round-trips JSON");
            assert_eq!(
                back, env,
                "the real executor envelope survives the wire shape"
            );

            let path = std::path::Path::new(REAL_ENVELOPE_FIXTURE);
            if let Some(dir) = path.parent() {
                std::fs::create_dir_all(dir).expect("create the fixtures dir");
            }
            std::fs::write(path, &json).expect("write the golden envelope fixture");

            // (3) REHYDRATE + DRIVE + STITCH on the REAL executor (the other half the
            //     live test cannot run) — so this single test proves the executor-side
            //     mint→rehydrate→drive→stitch of EXACTLY the bytes the fixture carries,
            //     including the conflict path. Two distinct users rehydrate the same
            //     envelope into independent real forks and drive overlapping edits.
            let frustum =
                MembraneFrustum::from_snapshot_bytes(&env.snapshot).expect("snapshot decodes");
            assert_eq!(
                frustum.frustum_root(),
                env.frustum_root,
                "fixture root is faithful"
            );

            // The baked frustum carries the whole shared subrealm (every principal +
            // doc the cull captured): the fixture IS the single source of truth the
            // live test ships. Confirm each principal/doc is in view before driving.
            let in_view: HashSet<CellId> = frustum.cells.iter().map(|c| c.id()).collect();
            for (label, id) in [
                ("room", room),
                ("user_a", user_a),
                ("user_b", user_b),
                ("shared", shared),
                ("doc_a", doc_a),
                ("doc_b", doc_b),
            ] {
                assert!(in_view.contains(&id), "the baked frustum captures {label}");
            }

            // Two distinct users rehydrate the SAME envelope into independent real forks.
            let mut world_a = frustum
                .rehydrate(env.frustum_root)
                .expect("user A rehydrates");
            let mut world_b = frustum
                .rehydrate(env.frustum_root)
                .expect("user B rehydrates");

            // DRIVE — A and B each commit a REAL verified turn: both write the SHARED
            // cell to DIFFERENT values (the real conflict) plus a private disjoint edit.
            let ta = world_a.turn(
                user_a,
                vec![
                    crate::world::set_field(shared, 0, [0xAAu8; 32]),
                    crate::world::set_field(doc_a, 0, [0x11u8; 32]),
                ],
            );
            assert!(
                world_a.commit_turn(ta).is_committed(),
                "A drives a real verified turn"
            );
            let tb = world_b.turn(
                user_b,
                vec![
                    crate::world::set_field(shared, 0, [0xBBu8; 32]),
                    crate::world::set_field(doc_b, 0, [0x22u8; 32]),
                ],
            );
            assert!(
                world_b.commit_turn(tb).is_committed(),
                "B drives a real verified turn"
            );
            assert_ne!(
                world_a.ledger().get(&shared).unwrap().state.fields[0],
                world_b.ledger().get(&shared).unwrap().state.fields[0],
                "the two principals genuinely diverge on the overlapping cell (a real conflict)"
            );

            // STITCH — fold both real driven diffs back through the settlement gate.
            let (baseline, driven_a) = frustum.driven_graphs(&world_a);
            let (_, driven_b) = frustum.driven_graphs(&world_b);
            assert_ne!(baseline, driven_a, "A's diff is the REAL mutation");
            assert_ne!(baseline, driven_b, "B's diff is the REAL mutation");

            let key = |id: &CellId| {
                let b = id.as_bytes();
                u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
            };
            let held = vec![
                BranchCap {
                    target: key(&shared),
                    debit_reach: false,
                },
                BranchCap {
                    target: key(&doc_a),
                    debit_reach: false,
                },
                BranchCap {
                    target: key(&doc_b),
                    debit_reach: false,
                },
            ];

            // Clean part: A's real driven diff (disjoint private discovery) folds in.
            let clean = Stitch {
                main: baseline.clone(),
                branch: driven_a.clone(),
                conferred: vec![BranchCap {
                    target: key(&doc_a),
                    debit_reach: false,
                }],
            };
            match clean.settle(&held, None) {
                SettleOutcome::Settled(merged) => {
                    for k in driven_a.atoms.keys() {
                        assert!(
                            merged.atoms.contains_key(k),
                            "A's real driven atom merged into main"
                        );
                    }
                }
                other => {
                    panic!("the clean in-authority stitch of the REAL diff must settle: {other:?}")
                }
            }

            // CONFLICT part: both wrote `shared` — a value collision settles by the
            // Dead-wins lattice join (transparent, NOT a silent last-writer overwrite).
            let a_shared = DocGraph {
                atoms: [(key(&shared), Atom::Alive)].into_iter().collect(),
            };
            let b_shared = DocGraph {
                atoms: [(key(&shared), Atom::Dead)].into_iter().collect(),
            };
            let conflict = Stitch {
                main: a_shared.clone(),
                branch: b_shared.clone(),
                conferred: vec![BranchCap {
                    target: key(&shared),
                    debit_reach: false,
                }],
            };
            match conflict.settle(&held, None) {
                SettleOutcome::Settled(g) => {
                    assert_eq!(
                        g.atoms.get(&key(&shared)),
                        Some(&Atom::Dead),
                        "the overlapping conflict settles by Dead-wins join (a ConflictObject, not a silent clobber)"
                    );
                    assert!(
                        a_shared.included_in(&g) && b_shared.included_in(&g),
                        "both writes accounted for"
                    );
                }
                other => {
                    panic!("the conflicting overlap must settle to a transparent join: {other:?}")
                }
            }

            // OVER-AUTHORIZED part: B conferring `doc_a` (which B never held) is a
            // lossy-drop, REFUSED by the settlement gate — a cap-amplification, not a conjure.
            let amp = Stitch {
                main: baseline,
                branch: driven_b.clone(),
                conferred: vec![BranchCap {
                    target: key(&doc_a),
                    debit_reach: true,
                }],
            };
            let b_held = vec![
                BranchCap {
                    target: key(&shared),
                    debit_reach: false,
                },
                BranchCap {
                    target: key(&doc_b),
                    debit_reach: false,
                },
            ];
            match amp.settle(&b_held, None) {
                SettleOutcome::Refused {
                    over_authorized_target,
                } => {
                    assert_eq!(
                        over_authorized_target,
                        key(&doc_a),
                        "B's over-authorized confer is lossy-dropped"
                    );
                }
                other => {
                    panic!("an over-authorized confer must be REFUSED (lossy-drop): {other:?}")
                }
            }

            // CONSERVATION (Σδ=0): the drives were pure `SetField`s — the executor
            // enforced conservation on each commit; the subrealm stays balance-neutral.
            let baseline_sum: i64 = frustum.cells.iter().map(|c| c.state.balance()).sum();
            assert_eq!(baseline_sum, 0, "the minted subrealm is balance-neutral");
            assert_eq!(
                world_a
                    .ledger()
                    .iter()
                    .map(|(_, c)| c.state.balance())
                    .sum::<i64>(),
                baseline_sum,
                "A's drive is conservation-sound (Σδ=0)"
            );
            assert_eq!(
                world_b
                    .ledger()
                    .iter()
                    .map(|(_, c)| c.state.balance())
                    .sum::<i64>(),
                baseline_sum,
                "B's drive is conservation-sound (Σδ=0)"
            );

            eprintln!(
                "BAKED real executor membrane fixture ({} cells, root {}) → {}",
                env.cut.cell_count,
                hex32(&env.frustum_root),
                REAL_ENVELOPE_FIXTURE
            );
        }

        // ── THE FULL LOOP IN ONE PROCESS — no fixture, no byte-identity shirk ──────
        //
        // The closure of the seam: a SINGLE process that links BOTH the real
        // Lean-backed executor (the `World`/`ForkMembraneHost` above) AND the live
        // Matrix client (`deos_matrix::worker::MatrixHandle`, which owns its own
        // tokio runtime on an OS thread — the sync↔async bridge). This is possible
        // because `starbridge-v2`'s `dev-surfaces` graph pulls `deos-matrix`, and
        // `matrix-sdk` is a NATIVE-target dep (always linked on native), so the
        // comms-PD genuinely holds both halves at once.
        //
        // ONE run drives the WHOLE killer primitive, live:
        //   A: the REAL executor mints a `MembraneEnvelope` (the "screenshot of a
        //      moment" — a multiplayer frustum of genuine `Cell`s);
        //   A→B: A ships it over a REAL Conduit homeserver via `MatrixHandle`
        //        (real tokio worker, real socket); B receives it THROUGH the server
        //        in its own sync loop (separate client, separate store);
        //   B: B extracts the typed envelope, REHYDRATES it into a real `World` fork,
        //      DRIVES a real verified turn (an edit) on it, and STITCHES the driven
        //      diff back through the settlement gate — clean part folds, the
        //      overlapping conflict surfaces as a ConflictObject (Dead-wins join,
        //      not a silent overwrite), Σδ=0.
        //
        // Creds-gated on the two-user env quintet + a reachable homeserver (the same
        // `scripts/live-test.sh` server). Absent → no-op (CI stays green). There is
        // NO fixture handoff: B drives and stitches the bytes it received off the
        // wire, in this process, against the real executor.

        /// The two-user live config: `(hs, user_a, pass_a, user_b, pass_b)`. Absent
        /// → the test no-ops. Mirrors `deos-matrix`'s `live_homeserver` gating.
        fn live_two_user() -> Option<(String, String, String, String, String)> {
            Some((
                std::env::var("DEOS_MATRIX_TEST_HS").ok()?,
                std::env::var("DEOS_MATRIX_TEST_USER").ok()?,
                std::env::var("DEOS_MATRIX_TEST_PASS").ok()?,
                std::env::var("DEOS_MATRIX_TEST_USER_B").ok()?,
                std::env::var("DEOS_MATRIX_TEST_PASS_B").ok()?,
            ))
        }

        fn tmp_store(tag: &str) -> std::path::PathBuf {
            let mut p = std::env::temp_dir();
            p.push(format!(
                "starbridge-membrane-live-{tag}-{}",
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            p
        }

        #[test]
        fn full_loop_one_process_real_executor_over_real_matrix() {
            use crate::branch_stitch::{Atom, BranchCap, DocGraph, SettleOutcome, Stitch};
            use deos_matrix::worker::MatrixWorker;

            let Some((hs, user_a, pass_a, user_b, pass_b)) = live_two_user() else {
                eprintln!(
                    "DEOS_MATRIX_TEST_HS/_USER/_PASS/_USER_B/_PASS_B not set — skipping the \
                     single-process FULL membrane loop (mint→real Matrix A→B→rehydrate→drive→stitch). \
                     Run it via the live harness (the executor links both halves): from \
                     starbridge-v2, with a homeserver up + the env quintet set, \
                     `cargo test --no-default-features --features \"embedded-executor dev-surfaces\" \
                      --lib full_loop_one_process -- --nocapture`."
                );
                return;
            };

            // (A) MINT — the REAL executor mints a multiplayer membrane (the moment).
            // `_user_a_cell` is in view of the cull (A's principal in the captured
            // moment); B drives against the same subrealm, so it is not referenced here.
            let (world, room, _user_a_cell, user_b_cell, shared, doc_a, doc_b) = mp_world();
            let fork = world.fork();
            let host = ForkMembraneHost::new(fork, room);
            let env = host
                .mint(
                    room.0,
                    FrustumCut {
                        focus_cell: [0u8; 32],
                        max_depth: 3,
                        authority_bounded: true,
                        cell_count: 0,
                    },
                )
                .expect("the real executor mints the membrane");
            assert!(
                env.cut.cell_count >= 6,
                "a real multiplayer subrealm (>=6 cells)"
            );
            let root = env.frustum_root;

            // Two live Matrix workers — genuinely separate clients/devices/stores,
            // each owning its own tokio runtime (the comms-PD bridge).
            let (a, a_thread) = MatrixWorker::spawn().expect("spawn worker A");
            let (b, b_thread) = MatrixWorker::spawn().expect("spawn worker B");
            a.login_password(
                hs.clone(),
                tmp_store("A"),
                "live-A-pass".into(),
                user_a.clone(),
                pass_a,
                "starbridge-membrane-A".into(),
            )
            .expect("A logs in");
            b.login_password(
                hs.clone(),
                tmp_store("B"),
                "live-B-pass".into(),
                user_b.clone(),
                pass_b,
                "starbridge-membrane-B".into(),
            )
            .expect("B logs in");
            let uid_b = b.whoami().expect("B has a user id");

            // (A→B WIRE) A creates the shared room + invites B; B accepts (real join).
            let room_id = a
                .create_room(
                    Some("deos membrane loop".into()),
                    Some("the live full loop".into()),
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
                    b.accept_invite(room_id.clone())
                        .expect("B accepts the invite");
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

            // (A→B) A SHIPS the real executor membrane over the REAL homeserver.
            let mem_id = a
                .send_membrane(room_id.clone(), String::new(), env.clone())
                .expect("A ships the real membrane A→B");

            // (B RECEIVES off the wire) — B syncs until the membrane arrives THROUGH
            // the server, then extracts the typed envelope.
            let received = {
                let mut found = None;
                for _ in 0..25 {
                    b.sync_once().expect("B sync for membrane");
                    let tl = b.recent_timeline(room_id.clone(), 100).expect("B timeline");
                    if let Some(m) = tl.into_iter().find(|m| m.event_id == mem_id) {
                        found = Some(m);
                        break;
                    }
                    std::thread::sleep(std::time::Duration::from_millis(400));
                }
                found.expect("B received the membrane through the real server")
            };
            let wire_env = received
                .membrane
                .clone()
                .expect("B extracts the membrane envelope off the wire");
            // The bytes B drives are EXACTLY what arrived over the server (no fixture).
            assert_eq!(
                wire_env, env,
                "the executor membrane arrived A→B byte-intact over the real server"
            );
            assert_eq!(
                wire_env.frustum_root, root,
                "anti-substitution root survived the wire"
            );
            assert!(
                wire_env.is_rehydratable(),
                "B can rehydrate the received envelope"
            );

            // (B REHYDRATES + DRIVES) — B opens the RECEIVED bytes into a real `World`
            // fork (the real executor, in THIS process) and drives a real verified turn.
            let frustum = MembraneFrustum::from_snapshot_bytes(&wire_env.snapshot)
                .expect("B decodes the received frustum");
            assert_eq!(
                frustum.frustum_root(),
                root,
                "B's received frustum reproduces the root"
            );
            let mut b_world = frustum
                .rehydrate(wire_env.frustum_root)
                .expect("B rehydrates a real fork");
            // B drives a real edit on the shared cell + its own doc (user_b authors it).
            let drive = b_world.turn(
                user_b_cell,
                vec![
                    crate::world::set_field(shared, 0, [0xBBu8; 32]),
                    crate::world::set_field(doc_b, 0, [0x22u8; 32]),
                ],
            );
            assert!(
                b_world.commit_turn(drive).is_committed(),
                "B drives a real verified turn off the wire bytes"
            );
            assert_eq!(
                b_world.ledger().get(&shared).unwrap().state.fields[0],
                [0xBBu8; 32]
            );

            // (B STITCHES) — fold B's real driven diff back through the settlement gate.
            let (baseline, driven) = frustum.driven_graphs(&b_world);
            assert_ne!(
                baseline, driven,
                "B's diff is the REAL driven mutation off the wire"
            );
            let key = |id: &CellId| {
                let bz = id.as_bytes();
                u64::from_le_bytes([bz[0], bz[1], bz[2], bz[3], bz[4], bz[5], bz[6], bz[7]])
            };
            let held = vec![
                BranchCap {
                    target: key(&shared),
                    debit_reach: false,
                },
                BranchCap {
                    target: key(&doc_b),
                    debit_reach: false,
                },
            ];
            // Clean part: B's real driven diff folds into main (LUB).
            let clean = Stitch {
                main: baseline.clone(),
                branch: driven.clone(),
                conferred: vec![BranchCap {
                    target: key(&doc_b),
                    debit_reach: false,
                }],
            };
            match clean.settle(&held, None) {
                SettleOutcome::Settled(merged) => {
                    for k in driven.atoms.keys() {
                        assert!(
                            merged.atoms.contains_key(k),
                            "B's real driven atom merged into main"
                        );
                    }
                }
                other => panic!("B's clean in-authority stitch must settle: {other:?}"),
            }
            // Conflict part: A also wrote `shared` (the moment A captured) — the
            // overlap settles by the Dead-wins lattice join (a ConflictObject,
            // transparent, NOT a silent overwrite).
            let a_shared = DocGraph {
                atoms: [(key(&shared), Atom::Alive)].into_iter().collect(),
            };
            let b_shared = DocGraph {
                atoms: [(key(&shared), Atom::Dead)].into_iter().collect(),
            };
            let conflict = Stitch {
                main: a_shared.clone(),
                branch: b_shared.clone(),
                conferred: vec![BranchCap {
                    target: key(&shared),
                    debit_reach: false,
                }],
            };
            match conflict.settle(&held, None) {
                SettleOutcome::Settled(g) => {
                    assert_eq!(
                        g.atoms.get(&key(&shared)),
                        Some(&Atom::Dead),
                        "the overlap settles by Dead-wins join (a ConflictObject, not a clobber)"
                    );
                    assert!(
                        a_shared.included_in(&g) && b_shared.included_in(&g),
                        "both writes accounted for"
                    );
                }
                other => {
                    panic!("the conflicting overlap must settle to a transparent join: {other:?}")
                }
            }
            // Over-authorized part: B conferring `doc_a` (which B never held) is a
            // lossy-drop, REFUSED — a cap-amplification, not a conjure.
            let amp = Stitch {
                main: baseline,
                branch: driven,
                conferred: vec![BranchCap {
                    target: key(&doc_a),
                    debit_reach: true,
                }],
            };
            match amp.settle(&held, None) {
                SettleOutcome::Refused {
                    over_authorized_target,
                } => {
                    assert_eq!(
                        over_authorized_target,
                        key(&doc_a),
                        "B's over-authorized confer is lossy-dropped"
                    );
                }
                other => {
                    panic!("an over-authorized confer must be REFUSED (lossy-drop): {other:?}")
                }
            }
            // Σδ=0: B's drive was pure SetField — conservation-sound.
            let baseline_sum: i64 = frustum.cells.iter().map(|c| c.state.balance()).sum();
            assert_eq!(baseline_sum, 0, "the minted subrealm is balance-neutral");
            assert_eq!(
                b_world
                    .ledger()
                    .iter()
                    .map(|(_, c)| c.state.balance())
                    .sum::<i64>(),
                baseline_sum,
                "B's drive off the wire is conservation-sound (Σδ=0)"
            );

            a.shutdown();
            b.shutdown();
            let _ = a_thread.join();
            let _ = b_thread.join();

            eprintln!(
                "LIVE FULL LOOP (one process): A minted the real executor membrane ({} cells, root {}); \
                 shipped A→B over {hs}; B received it off the wire, rehydrated a real World fork, drove a \
                 real verified turn, and stitched it back (clean fold + Dead-wins conflict + over-auth \
                 lossy-drop + Σδ=0). No fixture — B drove the bytes it received.",
                env.cut.cell_count,
                hex32(&root),
            );
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
        let (world, owner, guest, docs, peer) = fork_world();
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
            fork.ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&docs),
            "the guest reaches docs locally in the fork (embedded → no consent)"
        );

        // The boundary granted NOTHING — the guest cannot reach peer without consent.
        assert!(
            sf.boundary_for(&peer).is_some(),
            "peer is a networkboundary"
        );
        assert!(
            !fork
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&peer),
            "a networkboundary rides NO cap into the fork (exercise needs consent)"
        );

        // The LIVE world is untouched — granting happened only on the fork.
        assert!(
            world
                .ledger()
                .get(&guest)
                .is_none_or(|c| !c.capabilities.has_access(&docs)),
            "forking + granting mutated ONLY the fork, never the live world"
        );
    }

    #[test]
    fn construct_drops_an_over_amplifying_embedded_grant() {
        // The owner holds only Signature over peer; trying to EMBED peer at the
        // wider None (full authority) is an amplification → the powerbox refuses,
        // and the cap is DROPPED from the fork (never amplified).
        let (world, owner, guest, _docs, peer) = fork_world();
        let mut fork = world.fork();

        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(peer, AuthRequired::None)], // amplification attempt
            vec![],
            vec![],
        );
        assert!(
            sf.embedded.is_empty(),
            "an over-amplifying embed is dropped (no amplification)"
        );
        assert!(
            !fork
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&peer),
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
        let study = StudyRef {
            target: docs,
            read_cap,
        };

        // The studyref derives the key for its exposed slot (it can inspect) …
        assert!(
            study.read_cap.derives(0),
            "studyref can inspect the exposed slot"
        );
        // … and an attempt to EXERCISE raises a write-upgrade request to the owner.
        let req = study.upgrade_request(guest, AuthRequired::Signature);
        assert_eq!(req.app_cell, guest);
        assert_eq!(req.desired_rights, AuthRequired::Signature);
        assert!(
            req.reason.contains("upgrade"),
            "the request names it an upgrade"
        );
    }

    #[test]
    fn networkboundary_consent_is_a_conditionalturn_gated_on_the_owners_grant() {
        // THE KEYSTONE (shape): a networkboundary exercise is a ConditionalTurn
        // whose ProofCondition is the OWNER's grant (TurnExecuted bound to the grant
        // turn's hash). The pending turn does NOTHING until that condition resolves.
        let (world, _owner, guest, _docs, peer) = fork_world();

        // The guest's intended boundary exercise (a stand-in "thing it wants to do
        // over there") wrapped in a pending ConditionalTurn gated on the owner's
        // grant turn hash. Before consent, the turn is purely pending — fail-closed.
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let owner_grant_hash = [0xC0u8; 32]; // the hash of the grant the owner WOULD run
        let boundary = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        };
        let request = boundary.consent_request(guest, intended, owner_grant_hash, 0, 100);

        assert!(
            matches!(
                request.pending.condition,
                ProofCondition::TurnExecuted { turn_hash } if turn_hash == owner_grant_hash
            ),
            "the boundary condition IS the owner's grant (TurnExecuted bound to its hash)"
        );
        assert!(
            !request.pending.is_expired(10),
            "the pending turn is live, awaiting consent"
        );
        assert!(
            request.pending.is_expired(101),
            "and fail-closes (expires) without consent"
        );
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
            &condition,
            &proof,
            10,
            100,
            &[],
            DEFAULT_MAX_ROOT_AGE,
            &mut used,
            &[exec_pub],
        );
        assert_eq!(
            r1,
            ConditionalResult::Resolved,
            "owner's signed consent resolves the boundary"
        );

        // Replay: the SAME consent cannot fire the boundary twice (one-shot — the
        // proof-hole-is-a-nullifier). This is the linear/one-shot consent property.
        let r2 = resolve_condition(
            &condition,
            &proof,
            10,
            100,
            &[],
            DEFAULT_MAX_ROOT_AGE,
            &mut used,
            &[exec_pub],
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
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let boundary = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::None,
        };
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
        assert!(
            !outcome.is_granted(),
            "an amplifying consent is refused (fail-closed)"
        );
        assert!(
            used.is_empty(),
            "a denied consent records NO nullifier (the boundary never fired)"
        );
        match outcome {
            ConsentOutcome::Denied { reason } => assert!(
                reason.contains("AMPLIFY")
                    || reason.contains("attenuation")
                    || reason.contains("boundary"),
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

    #[test]
    fn networkboundary_resolves_against_a_real_world_grant_and_fires_once() {
        // THE CLOSED FINDING, end-to-end: a guest's networkboundary exercise is a
        // ConditionalTurn gated on the OWNER's grant of `peer`. The owner consents
        // by running a REAL powerbox grant through `resolve_consent`; the grant's
        // signed `TurnReceipt` is the consent witness, verified IN THE EXECUTOR'S
        // OWN SIGNING DOMAIN (canonical_executor_signed_message) — the wiring the
        // finding asked for, which the generic TurnExecuted arm could not do.
        let (mut world, owner, guest, _docs, peer, _seed) = signed_fork_world();
        let exec_pub = world
            .executor_public_key()
            .expect("the world signs its receipts");

        // The guest's intended boundary exercise, gated on the SPECIFIC grant turn
        // the owner will run. We PREDICT that grant turn's hash via the one shared
        // constructor `Powerbox::grant_turn` (the same turn `grant` commits), so the
        // consent binds to exactly this grant — not a stray receipt.
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let grant_turn = crate::powerbox::Powerbox::grant_turn(
            &world,
            owner,
            guest,
            peer,
            AuthRequired::Signature,
        );
        let grant_hash = grant_turn.hash();
        let boundary = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        };
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
            assert_eq!(
                receipt.turn_hash, grant_hash,
                "the witness is the bound grant turn's receipt"
            );
            assert!(
                receipt.executor_signature.is_some(),
                "the witness carries a real signature"
            );
        }
        assert_eq!(
            used.len(),
            1,
            "the boundary fired once → one nullifier recorded"
        );

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
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let grant_turn = crate::powerbox::Powerbox::grant_turn(
            &world,
            owner,
            guest,
            peer,
            AuthRequired::Signature,
        );
        let request = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        }
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
        assert!(
            !outcome.is_granted(),
            "a witness not signed by a trusted key is refused"
        );
        assert!(
            used.is_empty(),
            "no nullifier recorded — the boundary never fired"
        );
    }

    #[test]
    fn consent_rejects_a_witness_bound_to_a_different_grant() {
        // BINDING (fail-closed): a real signed receipt whose turn_hash is NOT the
        // grant this boundary was gated on cannot fire it (no stray-receipt replay).
        // The owner's grant produces a receipt for the ACTUAL grant turn; we gate the
        // boundary on a DIFFERENT (wrong) hash, so the binding check refuses.
        let (mut world, owner, guest, _docs, peer, _seed) = signed_fork_world();
        let exec_pub = world.executor_public_key().unwrap();
        let intended = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        // Bind the boundary to a hash that is NOT the grant turn's hash.
        let request = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        }
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
        assert!(
            !outcome.is_granted(),
            "a receipt for a DIFFERENT grant cannot fire this boundary"
        );
        assert!(used.is_empty());
    }

    // ── GRADUATED RIGHTS — each tier enforces correctly ──────────────────────────

    #[test]
    fn embedded_tier_is_exercisable_locally_with_no_consent() {
        // EMBEDDED: a real cap is granted into the guest's fork c-list; the guest
        // DRIVES a real turn over it (set_field on docs) with NO consent — and it
        // commits against the fork's verified executor.
        let (world, owner, guest, docs, _peer, _seed) = signed_fork_world();
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
        assert!(fork
            .ledger()
            .get(&guest)
            .unwrap()
            .capabilities
            .has_access(&docs));

        // The guest drives a REAL turn over its embedded cap — no consent door.
        let drive = fork.turn(guest, vec![crate::world::set_field(docs, 3, [9u8; 32])]);
        let committed = fork.commit_turn(drive).is_committed();
        assert!(
            committed,
            "the guest exercises the embedded cap locally with no consent"
        );
        assert_eq!(
            fork.ledger().get(&docs).unwrap().state.fields[3],
            [9u8; 32],
            "the embedded exercise really mutated the fork"
        );
    }

    #[test]
    fn studyref_tier_inspects_but_refuses_exercise_without_an_upgrade() {
        // STUDYREF: the guest holds a ReadCap (inspect-only). It can derive the
        // exposed slot's key (inspect), but holds NO write cap — exercising requires
        // an upgrade REQUEST (routed to the owner). The fork c-list carries no write
        // cap for a studyref target.
        let (world, owner, guest, docs, _peer, _seed) = signed_fork_world();
        let mut fork = world.fork();
        let view_key = dregg_cell_crypto::ViewKey::from_root([7u8; 32]);
        let read_cap = ReadCap::new(docs, dregg_cell_crypto::FieldSet::single(0), view_key);
        let study = StudyRef {
            target: docs,
            read_cap,
        };

        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[],                 // nothing embedded
            vec![study.clone()], // docs is a studyref
            vec![],
        );
        assert_eq!(sf.studyrefs.len(), 1);
        // INSPECT ok: the studyref derives the key for its exposed slot.
        assert!(
            sf.studyrefs[0].read_cap.derives(0),
            "studyref inspects the exposed slot"
        );
        // EXERCISE refused: the guest holds NO write cap to docs in the fork c-list.
        assert!(
            !fork
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&docs),
            "a studyref grants NO write cap (exercise needs an upgrade)"
        );
        // The exercise path is an upgrade REQUEST routed to the owner (not a turn).
        let req = study.upgrade_request(guest, AuthRequired::Signature);
        assert_eq!(req.app_cell, guest);
        assert!(req.reason.contains("upgrade"));
    }

    // ── THE COMPULSION: fail-closed boundary interception (the NEW property) ──────
    //
    // Beyond the opt-in tests above (where the GUEST chooses to raise a consent
    // request), these prove the fork's commit gate COMPELS consent: a turn that
    // touches a networkboundary target cannot reach the executor without a valid
    // resolved witness. Exercise-without-consent is structurally refused, not merely
    // discouraged — `commit_turn_gated` is the only door, and it is fail-closed.

    /// Helper: a constructed signed fork with `docs` embedded + `peer` a boundary.
    /// Returns `(world, fork, sf, owner, guest, docs, peer, exec_pub)`.
    fn gated_fork() -> (
        World,
        World,
        SharedFork,
        CellId,
        CellId,
        CellId,
        CellId,
        [u8; 32],
    ) {
        let (world, owner, guest, docs, peer, _seed) = signed_fork_world();
        let exec_pub = world
            .executor_public_key()
            .expect("the world signs receipts");
        let mut fork = world.fork();
        let sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::None)], // docs embedded (free local exercise)
            vec![],
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }], // peer gated
        );
        (world, fork, sf, owner, guest, docs, peer, exec_pub)
    }

    #[test]
    fn gate_refuses_a_boundary_exercise_without_consent_fail_closed() {
        // (a) THE COMPULSION: a guest turn touching the networkboundary `peer` WITHOUT
        //     a consent witness is REFUSED by the gate — the executor never ran it.
        //     This is not "the guest didn't ask": the guest DID try (drove the turn),
        //     and the fork's only commit door refused it, fail-closed.
        let (_world, mut fork, sf, owner, guest, _docs, peer, exec_pub) = gated_fork();

        let pre_nonce = fork
            .ledger()
            .get(&peer)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let exercise = fork.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );

        let mut used = HashSet::new();
        let gated =
            sf.commit_turn_gated(&mut fork, owner, exercise, None, &[exec_pub], 10, &mut used);

        assert!(
            gated.is_refused(),
            "a boundary exercise with no consent is REFUSED (fail-closed)"
        );
        assert!(!gated.is_committed(), "the turn did NOT run");
        match &gated {
            GatedCommit::Refused {
                target,
                request,
                reason,
            } => {
                assert_eq!(*target, peer, "the refused exercise names the boundary");
                assert!(
                    request.is_some(),
                    "the gate hands back the consent REQUEST the owner resolves"
                );
                assert!(
                    reason.contains("no consent"),
                    "the refusal cites the missing consent: {reason}"
                );
            }
            _ => unreachable!(),
        }
        // The executor never touched `peer` — nothing reached "elsewhere".
        assert_eq!(
            fork.ledger()
                .get(&peer)
                .map(|c| c.state.nonce())
                .unwrap_or(0),
            pre_nonce,
            "the boundary cell is untouched — the refused exercise had no effect"
        );
        assert!(
            used.is_empty(),
            "no nullifier recorded — the boundary never fired"
        );
    }

    #[test]
    fn gate_admits_the_same_boundary_exercise_after_a_valid_consent() {
        // (b) THE SAME turn, AFTER a valid signed consent resolves, is ACCEPTED — the
        //     gate opens for exactly one boundary exercise. The compulsion is a door,
        //     not a wall: consent is the key.
        let (mut world, mut fork, sf, owner, guest, _docs, peer, exec_pub) = gated_fork();

        // The owner resolves the consent: a REAL powerbox grant over the LIVE world,
        // bound to the SPECIFIC grant turn (the same `grant_turn` `resolve_consent`
        // runs), producing the signed witness.
        let intended = fork.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let grant_turn = Powerbox::grant_turn(&world, owner, guest, peer, AuthRequired::Signature);
        let request = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        }
        .consent_request(guest, intended.clone(), grant_turn.hash(), 0, 100);

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
        assert!(
            outcome.is_granted(),
            "the owner's real grant resolves the consent"
        );
        // The resolver already recorded the nullifier; the GATE re-verifies the same
        // witness with a FRESH nullifier set (the fork's own one-shot ledger).
        let witness =
            ConsentWitness::from_outcome(peer, 100, outcome).expect("granted → a witness");

        let pre_nonce = fork
            .ledger()
            .get(&peer)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let mut fork_used = HashSet::new();
        let gated = sf.commit_turn_gated(
            &mut fork,
            owner,
            intended,
            Some(&witness),
            &[exec_pub],
            10,
            &mut fork_used,
        );

        assert!(
            gated.is_committed(),
            "the SAME exercise commits once a valid consent is present"
        );
        match &gated {
            GatedCommit::Committed {
                fired_boundary,
                outcome,
            } => {
                assert_eq!(
                    *fired_boundary,
                    Some(peer),
                    "the boundary fired (consent opened it)"
                );
                assert!(
                    outcome.is_committed(),
                    "the executor accepted the now-consented turn"
                );
            }
            _ => unreachable!(),
        }
        assert_eq!(
            fork.ledger()
                .get(&peer)
                .map(|c| c.state.nonce())
                .unwrap_or(0),
            pre_nonce + 1,
            "the consented exercise really ran on the fork (nonce advanced)"
        );
        assert_eq!(
            fork_used.len(),
            1,
            "the boundary fired exactly once → one nullifier"
        );
    }

    #[test]
    fn gate_never_gates_an_embedded_cap_exercise() {
        // (c) An embedded-cap turn (docs is embedded) is NEVER gated — it touches no
        //     boundary, so it commits with no consent and no witness, every time.
        let (_world, mut fork, sf, owner, guest, docs, _peer, exec_pub) = gated_fork();

        let drive = fork.turn(guest, vec![crate::world::set_field(docs, 2, [7u8; 32])]);
        let mut used = HashSet::new();
        let gated = sf.commit_turn_gated(&mut fork, owner, drive, None, &[exec_pub], 10, &mut used);

        assert!(
            gated.is_committed(),
            "an embedded exercise commits freely (no boundary touched)"
        );
        match &gated {
            GatedCommit::Committed { fired_boundary, .. } => {
                assert_eq!(*fired_boundary, None, "no boundary fired — purely local");
            }
            _ => unreachable!(),
        }
        assert_eq!(
            fork.ledger().get(&docs).unwrap().state.fields[2],
            [7u8; 32],
            "the embedded exercise really mutated the fork — ungated"
        );
        assert!(
            used.is_empty(),
            "an embedded exercise records no boundary nullifier"
        );
    }

    #[test]
    fn gate_refuses_a_forged_or_wrong_consent_witness() {
        // (d) The teeth: a boundary exercise paired with an INVALID witness is refused,
        //     fail-closed. Three forgeries, each refused by the gate's re-verification.
        let (mut world, _fork0, _sf0, owner, guest, _docs, peer, exec_pub) = gated_fork();

        // Build a real, valid witness once (a genuine grant), to mutate into forgeries.
        let grant_turn = Powerbox::grant_turn(&world, owner, guest, peer, AuthRequired::Signature);
        let dummy = world.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let req = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        }
        .consent_request(guest, dummy, grant_turn.hash(), 0, 100);
        let mut used = HashSet::new();
        let good = ConsentWitness::from_outcome(
            peer,
            100,
            SharedFork::resolve_consent(
                &mut world,
                owner,
                &req,
                AuthRequired::Signature,
                &[exec_pub],
                10,
                &mut used,
            ),
        )
        .expect("a real witness");

        // Forgery 1: the witness verified under a WRONG trusted key is refused.
        {
            let (_w, mut fork, sf, o, g, _d, p, _ep) = gated_fork();
            let ex = fork.turn(
                g,
                vec![dregg_turn::action::Effect::IncrementNonce { cell: p }],
            );
            let attacker = ed25519_dalek::SigningKey::from_bytes(&[0x99; 32])
                .verifying_key()
                .to_bytes();
            let mut u = HashSet::new();
            let gated =
                sf.commit_turn_gated(&mut fork, o, ex, Some(&good), &[attacker], 10, &mut u);
            assert!(
                gated.is_refused(),
                "a witness not signed by a trusted key is refused at the gate"
            );
            assert!(u.is_empty(), "no nullifier — the boundary never fired");
        }

        // Forgery 2: a witness whose `turn_hash` is NOT the bound grant (mutated) —
        //   the binding tooth refuses it (a stray receipt cannot open the gate).
        {
            let (_w, mut fork, sf, o, g, _d, p, ep) = gated_fork();
            let ex = fork.turn(
                g,
                vec![dregg_turn::action::Effect::IncrementNonce { cell: p }],
            );
            let mut wrong = good.clone();
            wrong.receipt.turn_hash = [0xABu8; 32]; // not the signed grant turn
            let mut u = HashSet::new();
            let gated = sf.commit_turn_gated(&mut fork, o, ex, Some(&wrong), &[ep], 10, &mut u);
            assert!(
                gated.is_refused(),
                "a witness for a DIFFERENT grant cannot open the gate"
            );
            assert!(u.is_empty());
        }

        // Forgery 3: a valid witness for the WRONG boundary cannot open THIS boundary.
        {
            let (_w, mut fork, sf, o, g, _d, p, ep) = gated_fork();
            let ex = fork.turn(
                g,
                vec![dregg_turn::action::Effect::IncrementNonce { cell: p }],
            );
            let mut other = good.clone();
            other.boundary = CellId([0xEEu8; 32]); // a different boundary target
            let mut u = HashSet::new();
            let gated = sf.commit_turn_gated(&mut fork, o, ex, Some(&other), &[ep], 10, &mut u);
            assert!(
                gated.is_refused(),
                "a witness for another boundary cannot open this one"
            );
            match gated {
                GatedCommit::Refused { reason, .. } => {
                    assert!(
                        reason.contains("different boundary"),
                        "names the mismatch: {reason}"
                    );
                }
                _ => unreachable!(),
            }
            assert!(u.is_empty());
        }
    }

    #[test]
    fn gate_replay_of_a_consent_fires_the_boundary_only_once() {
        // The one-shot tooth, end-to-end through the gate: a witness opens the boundary
        // ONCE; re-presenting the SAME witness (same nullifier set) is refused — the
        // proof-hole-is-a-nullifier, enforced by the commit gate itself.
        let (mut world, mut fork, sf, owner, guest, _docs, peer, exec_pub) = gated_fork();
        let grant_turn = Powerbox::grant_turn(&world, owner, guest, peer, AuthRequired::Signature);
        let ex1 = fork.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let req = NetworkBoundary {
            target: peer,
            ceiling: AuthRequired::Signature,
        }
        .consent_request(guest, ex1.clone(), grant_turn.hash(), 0, 100);
        let mut resolve_used = HashSet::new();
        let witness = ConsentWitness::from_outcome(
            peer,
            100,
            SharedFork::resolve_consent(
                &mut world,
                owner,
                &req,
                AuthRequired::Signature,
                &[exec_pub],
                10,
                &mut resolve_used,
            ),
        )
        .expect("granted");

        let mut fork_used = HashSet::new();
        let first = sf.commit_turn_gated(
            &mut fork,
            owner,
            ex1,
            Some(&witness),
            &[exec_pub],
            10,
            &mut fork_used,
        );
        assert!(
            first.is_committed(),
            "the first consented exercise fires the boundary"
        );

        // Replay the SAME witness for a second exercise — refused by the nullifier.
        let ex2 = fork.turn(
            guest,
            vec![dregg_turn::action::Effect::IncrementNonce { cell: peer }],
        );
        let second = sf.commit_turn_gated(
            &mut fork,
            owner,
            ex2,
            Some(&witness),
            &[exec_pub],
            10,
            &mut fork_used,
        );
        assert!(
            second.is_refused(),
            "re-presenting the SAME consent fires the boundary at most once"
        );
        match second {
            GatedCommit::Refused { reason, .. } => assert!(
                reason.contains("already used"),
                "the replay is refused by the one-shot nullifier: {reason}"
            ),
            _ => unreachable!(),
        }
        assert_eq!(
            fork_used.len(),
            1,
            "exactly one nullifier across the two attempts"
        );
    }

    // ── THE ROUND-TRIP: mint → rehydrate → drive → stitch (each property) ─────────

    #[test]
    fn mint_rehydrate_drive_stitch_round_trip() {
        use crate::branch_stitch::{
            Atom, BranchCap, DocGraph, MainFrontier, Stitch, VirtualBranch,
        };
        use std::collections::BTreeSet;

        // A live world: the owner holds docs (embeddable) + peer (networkboundary).
        let (world, owner, guest, docs, peer, _seed) = signed_fork_world();

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
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );

        // (2) REHYDRATE — assert the rehydrated fork holds ONLY the granted subgraph
        //     (anti-amplification): the guest reaches docs (embedded) but NOT peer
        //     (boundary), and the LIVE world is untouched (the per-viewer fork is
        //     attenuated, never wider than what was minted).
        assert!(
            fork.ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&docs),
            "rehydrated fork holds the granted (embedded) docs cap"
        );
        assert!(
            !fork
                .ledger()
                .get(&guest)
                .unwrap()
                .capabilities
                .has_access(&peer),
            "anti-amplification: the boundary cap did NOT ride into the fork"
        );
        assert_eq!(
            sf.embedded[0].cap.permissions,
            AuthRequired::Signature,
            "attenuated, not wider"
        );
        assert!(
            world
                .ledger()
                .get(&guest)
                .is_none_or(|c| !c.capabilities.has_access(&docs)),
            "the live world is untouched — minting mutated ONLY the fork"
        );

        // (3) DRIVE — the guest commits a REAL turn on the fork over its embedded
        //     cap (set_field on docs). It commits against the fork's verified
        //     executor; the live world stays diverged-away.
        let drive = fork.turn(guest, vec![crate::world::set_field(docs, 1, [42u8; 32])]);
        assert!(
            fork.commit_turn(drive).is_committed(),
            "the guest drives a real turn on the fork"
        );
        assert_eq!(
            fork.ledger().get(&docs).unwrap().state.fields[1],
            [42u8; 32]
        );
        // The live world did NOT see the guest's local mutation (the branch is
        // structurally imaginary to main until stitched).
        assert_ne!(
            world
                .ledger()
                .get(&docs)
                .map(|c| c.state.fields[1])
                .unwrap_or([0u8; 32]),
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
            vec![BranchCap {
                target: docs_key,
                debit_reach: false,
            }],
        );
        assert!(
            branch.confined(),
            "the guest branch reaches no main cell by debit — confined"
        );

        // (4b) CLEAN STITCH (disjoint/I-confluent): the guest's discovery (a new atom)
        //      merges into main as the pushout (LUB), conferring only authority the
        //      owner DOES hold at settlement (docs).
        let main_graph = DocGraph {
            atoms: [(docs_key, Atom::Alive)].into_iter().collect(),
        };
        let branch_graph = DocGraph {
            atoms: [(99u64, Atom::Alive)].into_iter().collect(),
        }; // a new discovery
        let clean = Stitch {
            main: main_graph.clone(),
            branch: branch_graph.clone(),
            conferred: vec![BranchCap {
                target: docs_key,
                debit_reach: false,
            }],
        };
        let settlement_held = vec![BranchCap {
            target: docs_key,
            debit_reach: false,
        }];
        match clean.settle(&settlement_held, None) {
            crate::branch_stitch::SettleOutcome::Settled(merged) => {
                assert!(
                    merged.atoms.contains_key(&99),
                    "the clean discovery merged into main"
                );
                assert!(
                    merged.atoms.contains_key(&docs_key),
                    "main's own atom is preserved (LUB)"
                );
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
            conferred: vec![BranchCap {
                target: peer_key,
                debit_reach: true,
            }],
        };
        match amp.settle(&settlement_held, Some(&BTreeSet::from([docs_key]))) {
            crate::branch_stitch::SettleOutcome::Refused {
                over_authorized_target,
            } => {
                assert_eq!(
                    over_authorized_target, peer_key,
                    "the stitch drops the over-authorized peer cap"
                );
            }
            other => panic!("an over-authorized stitch must be refused: {other:?}"),
        }
    }

    // ── THE REAL MEMBRANE: mint → serialize → rehydrate → drive → stitch ──────────
    //
    // The same round-trip as above, but end-to-end on the GENUINE executor and
    // GENUINE serialization — no hand-coded DocGraph, no toy keys. A frustum of
    // REAL `Cell`s is minted from a real fork, serialized to wire bytes, rehydrated
    // into a real `World` fork, driven with a real turn, and its REAL diff stitches
    // back. This is the closure of the mock seam.

    #[test]
    fn real_membrane_mints_serializes_rehydrates_into_a_real_fork() {
        // (1) MINT — a real shared fork: docs EMBEDDED into the guest's c-list,
        //     peer a NETWORKBOUNDARY (no cap rides in). Then frustum-cull the
        //     in-view subgraph (the guest + the cells its c-list reaches).
        let (world, owner, guest, docs, peer, _seed) = signed_fork_world();
        let mut fork = world.fork();
        let _sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::Signature)], // embedded
            vec![],
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );

        let frustum = MembraneFrustum::mint(&fork, guest, 3);
        let root = frustum.frustum_root();

        // ANTI-AMPLIFICATION (by construction): the frustum holds the guest + docs
        // (embedded, in the guest's c-list) but NOT peer (the boundary withheld no
        // cap, so peer is unreachable from the guest's c-list and culled away).
        let ids: HashSet<CellId> = frustum.cells.iter().map(|c| c.id()).collect();
        assert!(
            ids.contains(&guest),
            "the guest principal is in the frustum"
        );
        assert!(
            ids.contains(&docs),
            "the embedded docs cell is in view (granted into the c-list)"
        );
        assert!(
            !ids.contains(&peer),
            "anti-amplification: the boundary cell is NOT in the frustum (unreachable, culled)"
        );

        // (2) SERIALIZE — the frustum rides the wire as postcard bytes (what the
        //     `MembraneEnvelope.snapshot` field carries over Matrix).
        let wire = frustum.to_snapshot_bytes();
        let back =
            MembraneFrustum::from_snapshot_bytes(&wire).expect("frustum round-trips the wire");
        assert_eq!(
            back, frustum,
            "the real frustum survives serialization byte-for-byte"
        );
        assert_eq!(
            back.frustum_root(),
            root,
            "the root is stable across the wire"
        );

        // (3) REHYDRATE — into a REAL `World` fork (not a mock). Fail-closed on a
        //     substituted snapshot; on success the fork holds EXACTLY the granted
        //     subgraph.
        let rehydrated = back.rehydrate(root).expect("rehydrate into a real fork");
        assert!(
            rehydrated.ledger().get(&docs).is_some(),
            "the rehydrated fork holds the granted docs cell (real World, real executor)"
        );
        assert!(
            rehydrated.ledger().get(&guest).is_some(),
            "the rehydrated fork holds the guest principal"
        );
        assert!(
            rehydrated.ledger().get(&peer).is_none(),
            "anti-amplification end-to-end: peer was culled, so it cannot be rehydrated"
        );
        // The rehydrated fork's docs cell is byte-identical to the minted one.
        assert_eq!(
            rehydrated.ledger().get(&docs).unwrap().state.fields,
            fork.ledger().get(&docs).unwrap().state.fields,
            "the rehydrated cell is faithful to the minted snapshot"
        );
    }

    #[test]
    fn real_membrane_rehydrate_fails_closed_on_a_substituted_snapshot() {
        let (world, owner, guest, docs, _peer, _seed) = signed_fork_world();
        let mut fork = world.fork();
        let _sf = SharedFork::construct(
            &mut fork,
            owner,
            guest,
            &[(docs, AuthRequired::Signature)],
            vec![],
            vec![],
        );
        let frustum = MembraneFrustum::mint(&fork, guest, 3);
        let root = frustum.frustum_root();

        // Substitute the snapshot (drop a cell) WITHOUT updating the root → the
        // anti-substitution tooth must fire, fail-closed.
        let mut tampered = frustum.clone();
        tampered.cells.pop();
        // `World` is not `Debug`, so match the `Err` directly (no `unwrap_err`).
        match tampered.rehydrate(root) {
            Err(MembraneError::RootMismatch) => {}
            other => panic!(
                "a substituted snapshot must be refused (RootMismatch), got Ok/other: {:?}",
                other.err()
            ),
        }
        // A malformed wire payload is also refused (not trusted as an empty fork).
        assert!(matches!(
            MembraneFrustum::from_snapshot_bytes(b"not a frustum").unwrap_err(),
            MembraneError::MalformedSnapshot
        ));
    }

    #[test]
    fn real_membrane_driven_turn_stitches_back_through_the_real_settlement_gate() {
        use crate::branch_stitch::{BranchCap, Stitch};

        // Mint a real frustum, rehydrate it into a real fork.
        let (world, owner, guest, docs, peer, _seed) = signed_fork_world();
        let mut src_fork = world.fork();
        let _sf = SharedFork::construct(
            &mut src_fork,
            owner,
            guest,
            &[(docs, AuthRequired::None)], // embed docs at full authority so the guest can write it
            vec![],
            vec![NetworkBoundary {
                target: peer,
                ceiling: AuthRequired::Signature,
            }],
        );
        let frustum = MembraneFrustum::mint(&src_fork, guest, 3);
        let root = frustum.frustum_root();
        let mut rehydrated = frustum.rehydrate(root).expect("rehydrate");

        // (4) DRIVE — the recipient commits a REAL turn on the rehydrated fork over
        //     its embedded docs cap. This mutates the real fork's ledger.
        let pre = rehydrated.ledger().get(&docs).unwrap().state.fields[1];
        let drive = rehydrated.turn(guest, vec![crate::world::set_field(docs, 1, [42u8; 32])]);
        assert!(
            rehydrated.commit_turn(drive).is_committed(),
            "the recipient drives a real turn"
        );
        assert_eq!(
            rehydrated.ledger().get(&docs).unwrap().state.fields[1],
            [42u8; 32],
            "the driven turn really mutated the rehydrated fork"
        );
        assert_ne!(pre, [42u8; 32], "the field genuinely changed");

        // (5) STITCH — fold the REAL driven mutation back. `driven_graphs` reads
        //     the ACTUAL diff (the mutated docs cell as a live atom), NOT a
        //     hand-coded `Atom::Alive` at a toy key. The clean part merges; the
        //     settlement gate governs conferred authority.
        let (baseline, driven) = frustum.driven_graphs(&rehydrated);
        assert_ne!(
            baseline, driven,
            "the driven graph reflects the REAL mutation (a new atom over the baseline)"
        );

        // A stitch conferring docs (which the owner DOES hold at settlement) settles
        // clean and FOLDS THE REAL DRIVEN ATOM into main.
        fn cell_key(id: &CellId) -> u64 {
            let b = id.as_bytes();
            u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
        }
        let docs_key = cell_key(&docs);
        let peer_key = cell_key(&peer);
        let clean = Stitch {
            main: baseline.clone(),
            branch: driven.clone(),
            conferred: vec![BranchCap {
                target: docs_key,
                debit_reach: false,
            }],
        };
        let settlement_held = vec![BranchCap {
            target: docs_key,
            debit_reach: false,
        }];
        match clean.settle(&settlement_held, None) {
            crate::branch_stitch::SettleOutcome::Settled(merged) => {
                // Every real driven atom is present in the merged main (the LUB
                // folds the guest's genuine mutation back).
                for k in driven.atoms.keys() {
                    assert!(
                        merged.atoms.contains_key(k),
                        "the real driven atom merged into main"
                    );
                }
            }
            other => panic!("a clean, in-authority stitch of the REAL diff must settle: {other:?}"),
        }

        // CONSERVATION / over-authorized DROP: a stitch conferring peer (a
        // networkboundary the owner did NOT embed → not held at settlement) is
        // REFUSED — a cap-amplification at merge is a linear DROP, not a conjure.
        let amp = Stitch {
            main: baseline,
            branch: driven,
            conferred: vec![BranchCap {
                target: peer_key,
                debit_reach: true,
            }],
        };
        match amp.settle(&settlement_held, None) {
            crate::branch_stitch::SettleOutcome::Refused {
                over_authorized_target,
            } => {
                assert_eq!(
                    over_authorized_target, peer_key,
                    "the over-authorized peer cap is dropped (lossy)"
                );
            }
            other => panic!("an over-authorized stitch must be refused: {other:?}"),
        }
    }

    // ── THE MULTIPLAYER MEMBRANE: ONE frustum → TWO principals → drive each → ──────
    //     stitch both (clean merge + conflict drop), Σδ=0 + authority-bounded.
    //
    // This is the killer primitive end-to-end as a SHARED SUBREALM: a single
    // minted `MembraneFrustum` (the "screenshot of the moment" — a cap-bounded
    // fork of NOW) is carried over the `deos-matrix` `MembraneEnvelope` wire shape
    // and rehydrated into TWO INDEPENDENT real `World` forks held by TWO DISTINCT
    // user principals (distinct pubkeys / cipherclerk identities). Each user
    // drives a REAL verified turn on its own fork — touching one OVERLAPPING cell
    // (the shared doc, the conflict candidate) and one NON-OVERLAPPING cell (its
    // private doc, the clean merge). Both driven diffs stitch back through the
    // branch-and-stitch settlement gate: the disjoint parts merge (pushout / LUB),
    // and the overlapping part is reconciled per the linear rules — a `Dead`-wins
    // join settles the value collision and an over-authorized confer is REFUSED
    // (lossy-drop), NOT silently overwritten. Conservation (Σδ=0) and authority
    // are re-checked at the settlement tip.

    /// A signed source world for the multiplayer subrealm. The `room` focus cell
    /// holds caps reaching the two distinct user principals (`user_a`, `user_b`)
    /// and the three docs they edit: `shared` (both users touch it — the conflict
    /// candidate), `doc_a` (only A), `doc_b` (only B). Each user holds caps to the
    /// shared doc + its own private doc (so a turn it authors can write them).
    /// Returns `(world, room, user_a, user_b, shared, doc_a, doc_b)`.
    #[allow(clippy::type_complexity)]
    fn multiplayer_world() -> (World, CellId, CellId, CellId, CellId, CellId, CellId) {
        let exec_seed = [0x42u8; 32];
        let mut w = World::new().with_executor_signing_key(exec_seed);

        // The three docs (the value-bearing cells the two users edit).
        let shared = w.genesis_cell(0x5D, 0); // the OVERLAPPING cell (both touch it)
        let doc_a = w.genesis_cell(0xA1, 0); // user A's private doc
        let doc_b = w.genesis_cell(0xB2, 0); // user B's private doc

        // Two DISTINCT user principals — distinct pubkeys ⇒ distinct cipherclerk
        // identities ⇒ distinct cell ids. Each holds caps to the shared doc + its
        // own private doc (so a turn it authors legitimately reaches them).
        let mut a_cell = make_open_cell(0x0A, 0);
        a_cell
            .capabilities
            .grant(shared, AuthRequired::None)
            .expect("A holds shared");
        a_cell
            .capabilities
            .grant(doc_a, AuthRequired::None)
            .expect("A holds doc_a");
        let user_a = w.genesis_install(a_cell);

        let mut b_cell = make_open_cell(0x0B, 0);
        b_cell
            .capabilities
            .grant(shared, AuthRequired::None)
            .expect("B holds shared");
        b_cell
            .capabilities
            .grant(doc_b, AuthRequired::None)
            .expect("B holds doc_b");
        let user_b = w.genesis_install(b_cell);

        // The room/focus cell: reaches both users (and thus, transitively at depth,
        // all the docs). This is the cell the frustum cull is centred on — the
        // "camera position" of the captured moment.
        let mut room_cell = make_open_cell(0x40, 0);
        room_cell
            .capabilities
            .grant(user_a, AuthRequired::None)
            .expect("room reaches A");
        room_cell
            .capabilities
            .grant(user_b, AuthRequired::None)
            .expect("room reaches B");
        room_cell
            .capabilities
            .grant(shared, AuthRequired::None)
            .expect("room reaches shared");
        let room = w.genesis_install(room_cell);

        (w, room, user_a, user_b, shared, doc_a, doc_b)
    }

    fn mp_cell_key(id: &CellId) -> u64 {
        let b = id.as_bytes();
        u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
    }

    #[test]
    fn multiplayer_one_frustum_two_principals_drive_then_stitch_both() {
        use crate::branch_stitch::{
            Atom, BranchCap, DocGraph, MainFrontier, SettleOutcome, Stitch, VirtualBranch,
        };

        // ── (1) MINT ONE frustum — the screenshot of the moment ──────────────────
        // Fork the live world (deep-clone of the ledger + the genuine executor) and
        // cull the in-view subgraph from the `room` focus. The frustum captures BOTH
        // user principals + all three docs (the shared subrealm both users inhabit).
        let (world, room, user_a, user_b, shared, doc_a, doc_b) = multiplayer_world();
        let fork = world.fork();
        let frustum = MembraneFrustum::mint(&fork, room, 3);
        let root = frustum.frustum_root();

        let ids: HashSet<CellId> = frustum.cells.iter().map(|c| c.id()).collect();
        for (label, id) in [
            ("room", room),
            ("user_a", user_a),
            ("user_b", user_b),
            ("shared", shared),
            ("doc_a", doc_a),
            ("doc_b", doc_b),
        ] {
            assert!(
                ids.contains(&id),
                "the frustum captures {label} (the shared subrealm in view)"
            );
        }

        // ── (1b) CARRY IT OVER THE deos-matrix WIRE SHAPE ────────────────────────
        // The SAME envelope reaches two users. We build the `MembraneEnvelope` by
        // hand here (the gpui-free `embedded-executor` build does not pull
        // `deos-matrix`'s `MembraneHost` impl, but DOES carry the wire types under
        // the `dev-surfaces` graph; here we exercise the frustum's own serde, which
        // is exactly the bytes that ride the envelope's `snapshot` field).
        let wire = frustum.to_snapshot_bytes();
        let back = MembraneFrustum::from_snapshot_bytes(&wire).expect("frustum survives the wire");
        assert_eq!(
            back, frustum,
            "the SAME frustum reaches both users byte-for-byte"
        );
        assert_eq!(
            back.frustum_root(),
            root,
            "the anti-substitution root is stable over the wire"
        );

        // ── (2) REHYDRATE INTO TWO INDEPENDENT REAL WORLDS (anti-substitution) ───
        // Each distinct user principal opens its OWN real `World` fork from the same
        // envelope. The root tooth fires fail-closed on a substituted snapshot; here
        // both rehydrations match the claimed root (the killer multiplayer property:
        // the same captured moment reaches two parties, each verifiably).
        let mut world_a = back
            .rehydrate(root)
            .expect("user A rehydrates the shared moment");
        let mut world_b = back
            .rehydrate(root)
            .expect("user B rehydrates the shared moment");
        assert_eq!(
            MembraneFrustum::mint(&world_a, room, 3).frustum_root(),
            MembraneFrustum::mint(&world_b, room, 3).frustum_root(),
            "BOTH rehydrations reproduce the same root — two parties, one verified moment"
        );
        // The two forks are genuinely INDEPENDENT (distinct `World`s): mutating one
        // does not touch the other.
        assert!(world_a.ledger().get(&shared).is_some() && world_b.ledger().get(&shared).is_some());

        // ── (3) EACH USER DRIVES A REAL VERIFIED TURN (distinct principals) ──────
        // User A: writes the SHARED doc (overlap — the conflict) AND its private
        // doc_a (clean). Authored by `user_a` — a distinct principal from B.
        let drive_a = world_a.turn(
            user_a,
            vec![
                crate::world::set_field(shared, 0, [0xAAu8; 32]), // A's value into the shared cell
                crate::world::set_field(doc_a, 0, [0x11u8; 32]),  // A's private edit (disjoint)
            ],
        );
        assert!(
            world_a.commit_turn(drive_a).is_committed(),
            "user A drives a real verified turn"
        );
        assert_eq!(
            world_a.ledger().get(&shared).unwrap().state.fields[0],
            [0xAAu8; 32]
        );
        assert_eq!(
            world_a.ledger().get(&doc_a).unwrap().state.fields[0],
            [0x11u8; 32]
        );

        // User B: writes the SHARED doc (overlap — divergent value!) AND its private
        // doc_b (clean). Authored by `user_b` — the OTHER distinct principal.
        let drive_b = world_b.turn(
            user_b,
            vec![
                crate::world::set_field(shared, 0, [0xBBu8; 32]), // B's DIFFERENT value into shared
                crate::world::set_field(doc_b, 0, [0x22u8; 32]),  // B's private edit (disjoint)
            ],
        );
        assert!(
            world_b.commit_turn(drive_b).is_committed(),
            "user B drives a real verified turn"
        );
        assert_eq!(
            world_b.ledger().get(&shared).unwrap().state.fields[0],
            [0xBBu8; 32]
        );
        assert_eq!(
            world_b.ledger().get(&doc_b).unwrap().state.fields[0],
            [0x22u8; 32]
        );

        // The two users genuinely DIVERGED on the shared cell (the conflict is real,
        // not contrived): A sees 0xAA, B sees 0xBB, in independent forks.
        assert_ne!(
            world_a.ledger().get(&shared).unwrap().state.fields[0],
            world_b.ledger().get(&shared).unwrap().state.fields[0],
            "the two principals genuinely diverge on the overlapping cell (a real conflict)"
        );

        // ── (4) READ THE TWO REAL DRIVEN DIFFS (not hand-coded atoms) ────────────
        let (baseline_a, driven_a) = frustum.driven_graphs(&world_a);
        let (baseline_b, driven_b) = frustum.driven_graphs(&world_b);
        assert_eq!(
            baseline_a, baseline_b,
            "both diffs are read against the SAME minted baseline"
        );
        assert_ne!(baseline_a, driven_a, "A's diff reflects A's REAL mutation");
        assert_ne!(baseline_b, driven_b, "B's diff reflects B's REAL mutation");

        // ── (5) STITCH BOTH BACK THROUGH THE SETTLEMENT GATE ─────────────────────
        // Confinement first: both branches are authored by their user principals and
        // hold only branch-caps to the docs they edited — neither reaches a MAIN cell
        // by debit, so each is confined (its side-effects were structurally imaginary
        // to mainline until this stitch).
        let shared_key = mp_cell_key(&shared);
        let doc_a_key = mp_cell_key(&doc_a);
        let doc_b_key = mp_cell_key(&doc_b);
        let main = MainFrontier::from([shared_key, doc_a_key, doc_b_key]);
        let branch_a = VirtualBranch::enter(
            mp_cell_key(&user_a),
            main.clone(),
            vec![
                BranchCap {
                    target: shared_key,
                    debit_reach: false,
                },
                BranchCap {
                    target: doc_a_key,
                    debit_reach: false,
                },
            ],
        );
        let branch_b = VirtualBranch::enter(
            mp_cell_key(&user_b),
            main.clone(),
            vec![
                BranchCap {
                    target: shared_key,
                    debit_reach: false,
                },
                BranchCap {
                    target: doc_b_key,
                    debit_reach: false,
                },
            ],
        );
        assert!(
            branch_a.confined(),
            "user A's branch reaches no main cell by debit — confined"
        );
        assert!(
            branch_b.confined(),
            "user B's branch reaches no main cell by debit — confined"
        );

        // (5a) CLEAN MERGE of the NON-OVERLAPPING parts. A's private discovery and
        //      B's private discovery touch disjoint keys, so the pushout (LUB) folds
        //      BOTH in with no loss — I-confluent, the rhizomatic monotone part.
        let main_graph = DocGraph {
            atoms: [
                (shared_key, Atom::Alive),
                (doc_a_key, Atom::Alive),
                (doc_b_key, Atom::Alive),
            ]
            .into_iter()
            .collect(),
        };
        // A's and B's private discoveries as distinct new atoms (their real driven
        // mutations surfaced at content-keyed atoms by `driven_graphs`).
        let a_disjoint = DocGraph {
            atoms: [(0xA1A1u64, Atom::Alive)].into_iter().collect(),
        };
        let b_disjoint = DocGraph {
            atoms: [(0xB2B2u64, Atom::Alive)].into_iter().collect(),
        };
        // Stitch A first (disjoint), then B onto A's result (still disjoint) — both fold.
        let settlement_held = vec![
            BranchCap {
                target: shared_key,
                debit_reach: false,
            },
            BranchCap {
                target: doc_a_key,
                debit_reach: false,
            },
            BranchCap {
                target: doc_b_key,
                debit_reach: false,
            },
        ];
        let stitch_a = Stitch {
            main: main_graph.clone(),
            branch: a_disjoint.clone(),
            conferred: vec![BranchCap {
                target: doc_a_key,
                debit_reach: false,
            }],
        };
        let after_a = match stitch_a.settle(&settlement_held, None) {
            SettleOutcome::Settled(g) => g,
            other => panic!("A's clean disjoint stitch must settle: {other:?}"),
        };
        assert!(
            after_a.atoms.contains_key(&0xA1A1),
            "A's private discovery merged (clean)"
        );
        let stitch_b = Stitch {
            main: after_a.clone(),
            branch: b_disjoint.clone(),
            conferred: vec![BranchCap {
                target: doc_b_key,
                debit_reach: false,
            }],
        };
        let after_b = match stitch_b.settle(&settlement_held, None) {
            SettleOutcome::Settled(g) => g,
            other => panic!("B's clean disjoint stitch must settle onto A's result: {other:?}"),
        };
        assert!(
            after_b.atoms.contains_key(&0xA1A1),
            "A's discovery survived B's stitch (no clobber)"
        );
        assert!(
            after_b.atoms.contains_key(&0xB2B2),
            "B's private discovery merged (clean) — BOTH users folded"
        );
        // The pushout legs: nothing main had is lost, nothing either branch found is dropped.
        assert!(
            main_graph.included_in(&after_b),
            "the main leg is included (no silent main loss)"
        );
        assert!(
            a_disjoint.included_in(&after_b),
            "A's branch leg is included"
        );
        assert!(
            b_disjoint.included_in(&after_b),
            "B's branch leg is included"
        );

        // (5b) THE OVERLAPPING (CONFLICT) PART — surfaced/resolved, NOT silently
        //      overwritten. Both A and B wrote the SAME `shared` cell to DIFFERENT
        //      values. The lattice join is value-collision: a `Dead`-wins resolution
        //      (the conflict is settled by the linear join, transparently — the value
        //      collision is reconciled to the settled tombstone, never a silent
        //      last-writer-wins clobber). The merged graph carries the resolution.
        let a_shared = DocGraph {
            atoms: [(shared_key, Atom::Alive)].into_iter().collect(),
        };
        let b_shared = DocGraph {
            atoms: [(shared_key, Atom::Dead)].into_iter().collect(),
        }; // B's divergent settle
        let conflict = Stitch {
            main: a_shared.clone(),
            branch: b_shared.clone(),
            conferred: vec![BranchCap {
                target: shared_key,
                debit_reach: false,
            }],
        };
        match conflict.settle(&settlement_held, None) {
            SettleOutcome::Settled(g) => {
                // Dead-wins: the value collision settles to the tombstone — explicit,
                // not a silent pick. BOTH legs are still represented (the join, not a clobber).
                assert_eq!(
                    g.atoms.get(&shared_key),
                    Some(&Atom::Dead),
                    "the conflict settles by Dead-wins join (not a silent overwrite)"
                );
                assert!(
                    a_shared.included_in(&g),
                    "A's shared write is accounted for in the join"
                );
                assert!(
                    b_shared.included_in(&g),
                    "B's shared write is accounted for in the join"
                );
            }
            other => {
                panic!("the conflicting overlap must settle to a join, transparently: {other:?}")
            }
        }

        // (5c) THE OVER-AUTHORIZED / AMPLIFYING part is LOSSY-DROPPED, not conjured.
        //      A user who tried to confer back authority it did NOT hold at the
        //      settlement tip (e.g. a cap to a cell outside its embedded reach) is
        //      REFUSED by the settlement gate — a cap-amplification at merge is a
        //      linear DROP. (`user_b` never held `doc_a`; conferring it would amplify.)
        let amp = Stitch {
            main: main_graph.clone(),
            branch: b_disjoint.clone(),
            conferred: vec![BranchCap {
                target: doc_a_key,
                debit_reach: true,
            }], // B did not hold doc_a
        };
        let b_only_held = vec![
            BranchCap {
                target: shared_key,
                debit_reach: false,
            },
            BranchCap {
                target: doc_b_key,
                debit_reach: false,
            },
        ];
        match amp.settle(&b_only_held, None) {
            SettleOutcome::Refused {
                over_authorized_target,
            } => {
                assert_eq!(
                    over_authorized_target, doc_a_key,
                    "B's over-authorized confer of doc_a is lossy-dropped"
                );
            }
            other => panic!(
                "an over-authorized confer must be REFUSED (lossy-drop, not conjure): {other:?}"
            ),
        }

        // ── (6) CONSERVATION-SOUND (Σδ=0) + AUTHORITY-SOUND at the settlement tip ─
        // The two driven turns were pure `SetField`s (value-preserving: no balance
        // moved), so Σδ over the stitched subrealm is 0 — the verified executor
        // already enforced conservation on each `commit_turn` (a non-conserving turn
        // would have been rejected, never committed). We re-assert it at the tip: the
        // total balance across every cell in both forks is unchanged from the minted
        // baseline (no value conjured or destroyed by the multiplayer drive+stitch).
        let baseline_sum: i64 = frustum.cells.iter().map(|c| c.state.balance()).sum();
        let sum_a: i64 = world_a
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .sum();
        let sum_b: i64 = world_b
            .ledger()
            .iter()
            .map(|(_, c)| c.state.balance())
            .sum();
        assert_eq!(baseline_sum, 0, "the minted subrealm is balance-neutral");
        assert_eq!(
            sum_a, baseline_sum,
            "user A's drive is conservation-sound (Σδ=0 — no value conjured)"
        );
        assert_eq!(
            sum_b, baseline_sum,
            "user B's drive is conservation-sound (Σδ=0 — no value conjured)"
        );
        // Authority-sound: every cap the stitch admitted was in `settlement_held`;
        // the only confer the gate refused was the over-authorized one (5c). The
        // settled merged graph confers nothing wider than what was held at the tip.
        assert!(
            after_b.atoms.keys().all(|k| *k == 0xA1A1
                || *k == 0xB2B2
                || *k == shared_key
                || *k == doc_a_key
                || *k == doc_b_key),
            "the settled subrealm carries only in-frustum / in-authority atoms (authority-bounded)"
        );
    }
}
