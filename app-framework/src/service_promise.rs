//! # Service-promise exchange — the spine of the agent service economy.
//!
//! The ring ([`crate::ring_trade::RingCoordinator`]) and the [`crate::payable`]
//! DSI exchange ASSETS atomically: a party offers an asset, wants an asset, the
//! verified [`RingSolver`] matches a conserving cycle and the legs settle
//! all-or-nothing. That is a *spot* market — value-for-value, both sides on the
//! table at once.
//!
//! A service economy needs more: a provider promises to PERFORM a service later,
//! and a consumer pays for it now. The danger is the half-open deal — the
//! consumer pays and the provider never performs, or the provider performs and
//! the consumer never pays. This module closes that gap with the SAME pieces the
//! ring already trusts, composed into a service-for-payment leg:
//!
//!  1. **Match** — a provider posts a [`ServicePromise`] ("I will perform service
//!     `S` for `price`"); a consumer posts a [`ServiceRequest`] ("I want `S`,
//!     offering `P`"). The match is found by the SAME [`RingSolver`] the asset
//!     ring uses: the service is encoded as a synthetic "promise-token" asset, so
//!     a provider↔consumer pair is exactly a 2-cycle (provider offers the
//!     promise-token + wants payment; consumer offers payment + wants the
//!     promise-token). [`ServicePromiseExchange::match_one`].
//!
//!  2. **Escrow** — the matched payment leg is not paid straight to the provider;
//!     it is HELD. The payment moves consumer → escrow through the verified
//!     executor ([`settle_ring_verified`], per-asset Σδ=0), exactly the
//!     conserving move the ring already proves. [`ServicePromiseExchange::fund`].
//!
//!  3. **Fulfill** — the promise is a guarded hole. The provider commits, at
//!     match time, to performing a specific verified turn (the service effect) — its
//!     hash AND the state-commitment transition (`expected_pre/post_commitment`) it
//!     moves through. The held payment is bound by a [`ProofCondition::TurnProven`]
//!     naming that hash + those endpoints — the exact promise-hole shape
//!     `turn/src/{eventual,conditional}.rs` defines (a one-shot continuation whose
//!     fill is a VERIFIED proof the service turn executed). When the provider performs
//!     the turn the commit pipeline produces a [`ProvenReceipt`] (the verified rotated
//!     EffectVM STARK); presenting its [`ConditionProof::EffectVmProof`] FILLS the hole
//!     ([`resolve_condition`] → `Resolved`) and the escrow RELEASES the payment escrow
//!     → provider, through the verified executor. [`ServicePromiseExchange::fulfill`].
//!
//!  4. **Refund** — if the promise lapses (the timeout passes with no conforming
//!     receipt) the held payment REFUNDS escrow → consumer.
//!     [`ServicePromiseExchange::refund`].
//!
//! Every value move is a single-leg [`settle_ring_verified`] fold, so each is
//! atomic and per-asset conserving on its own, and the whole lifecycle conserves
//! the payment asset end-to-end (consumer's `price` ends up wholly with the
//! provider on fulfillment, or wholly back with the consumer on refund — never
//! split). Release and refund are mutually-exclusive one-shot terminals, the same
//! consumed-once discipline `cell/src/escrow_sealed.rs` binds into a cell's
//! commitment; here the holder is the verified ledger rather than a heap leaf, but
//! the invariant is identical: a held leg is taken exactly once, by exactly one of
//! its two exits.
//!
//! ## What a "service" is, and how fulfillment is proven
//!
//! A [`ServiceId`] names a service as a `(target cell, method)` pair — a method/
//! effect the provider will exercise on a target. The provider's commitment to
//! perform it is the `service_turn_hash` it posts: the content-addressed
//! [`dregg_turn::Turn::hash`] of the exact verified turn that performs the
//! service. Fulfillment is proven the way the kernel proves "a turn ran" AFTER the
//! trusted-key retirement (assurance-perimeter #3): a VERIFIED rotated EffectVM STARK
//! ([`ConditionProof::EffectVmProof`]) whose bound turn hash matches the promise AND
//! whose wide state-commitment anchors equal the promised `expected_pre/post_commitment`
//! (the [`ProofCondition::TurnProven`] resolution path). No executor SIGNATURE is
//! consulted — the trust root is the PROOF. HONEST SCOPE: the proof attests the
//! state-commitment DELTA `pre -> post`, not the full state, and rests on the FRI floor
//! (`project-fri-soundness-reality`). This module does NOT decide what counts as the
//! service being "done well" — it binds payment to a PROVEN state transition. Richer
//! fulfillment (a STARK proof of an outcome predicate) is the
//! `ProofCondition::LocalProof` / `RemoteProof` path, pluggable through the same
//! [`ServiceEscrow::condition`] field.

use std::collections::HashSet;

use dregg_cell::Cell;
use dregg_cell::escrow_sealed::{decode_i64, encode_i64};
use dregg_intent::CommitmentId;
use dregg_intent::exchange::AssetId;
use dregg_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade};
use dregg_intent::verified_settle::{
    VerifiedSettleError, WideLedger, WideLeg, settle_ring_wide_verified,
};
use dregg_turn::conditional::{
    ConditionProof, ConditionalResult, ProofCondition, ProvenReceipt, resolve_condition,
};
use dregg_types::CellId;

/// Names a service `S`: a method/effect the provider exercises on a target cell.
///
/// The id is the domain-separated hash of `(target, method)`, so two providers
/// promising the same `(target, method)` post the SAME [`ServiceId`] and the ring
/// matcher recognises them as offering one service. Inside the ring graph the
/// service trades as a synthetic "promise-token" asset (its bytes ARE the asset
/// id) — that is what lets the asset ring matcher find a provider↔consumer cycle
/// without a bespoke service matcher.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ServiceId(pub [u8; 32]);

impl ServiceId {
    /// The service "exercise `method` on `target`".
    pub fn of(target: CellId, method: &str) -> Self {
        let mut h = blake3::Hasher::new_derive_key("dregg.service-promise.service-id.v1");
        h.update(target.as_bytes());
        h.update(method.as_bytes());
        ServiceId(*h.finalize().as_bytes())
    }

    /// A service id from raw bytes (e.g. an externally agreed service tag).
    pub fn from_bytes(bytes: [u8; 32]) -> Self {
        ServiceId(bytes)
    }

    /// The raw 32-byte id.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// The synthetic promise-token asset this service trades as inside the ring
    /// graph. (It never settles as real value — it is the marker the ring matcher
    /// pairs provider↔consumer on; the only value that moves is the payment.)
    fn as_asset(&self) -> AssetId {
        self.0
    }
}

/// A provider's posted promise: "I will perform `service` for `price` of
/// `payment_asset`, paid to me (`provider`)."
#[derive(Clone, Debug)]
pub struct ServicePromise {
    /// The provider's ring identity (its low byte is its verified-ledger cell).
    pub provider: CommitmentId,
    /// The service promised.
    pub service: ServiceId,
    /// The content-addressed [`dregg_turn::Turn::hash`] of the exact verified turn
    /// the provider will perform to fulfill — the fulfillment hole. A VERIFIED
    /// EffectVM STARK for THIS turn (a [`ProvenReceipt`], assurance-perimeter #3)
    /// fills it — NOT a trusted signature.
    pub service_turn_hash: [u8; 32],
    /// The pre-state circuit commitment the service turn is expected to move FROM
    /// (32-byte `commitment_8bb_to_bytes` form). The provider COMMITS to the exact
    /// state transition at promise time; a fulfilling proof's wide OLD anchor must
    /// equal this. This is the escrow's TRUSTED pre endpoint (never taken from the
    /// prover-controlled proof).
    pub expected_pre_commitment: [u8; 32],
    /// The post-state circuit commitment the service turn is expected to move TO. A
    /// fulfilling proof's wide NEW anchor must equal this — the escrow's TRUSTED post
    /// endpoint.
    pub expected_post_commitment: [u8; 32],
    /// The asset the provider wants to be paid in.
    pub payment_asset: AssetId,
    /// The price the provider asks.
    pub price: u64,
    /// The block height after which an unfulfilled promise's escrow may be
    /// refunded to the consumer (the promise window).
    pub timeout_height: u64,
}

/// A consumer's posted request: "I want `service`, offering up to `offer` of
/// `payment_asset` from me (`consumer`)."
#[derive(Clone, Debug)]
pub struct ServiceRequest {
    /// The consumer's ring identity (its low byte is its verified-ledger cell).
    pub consumer: CommitmentId,
    /// The service wanted.
    pub service: ServiceId,
    /// The asset the consumer pays in.
    pub payment_asset: AssetId,
    /// The most the consumer will pay.
    pub offer: u64,
}

/// A matched provider/consumer pair — the service-for-payment leg the ring found.
#[derive(Clone, Debug)]
pub struct ServiceMatch {
    /// The provider being paid on fulfillment.
    pub provider: CommitmentId,
    /// The consumer whose payment is escrowed.
    pub consumer: CommitmentId,
    /// The service being exchanged.
    pub service: ServiceId,
    /// The fulfillment hole (the promised service turn's hash).
    pub service_turn_hash: [u8; 32],
    /// The pre-state commitment the service turn is committed to move FROM (the
    /// escrow's TRUSTED pre endpoint, carried from the promise).
    pub expected_pre_commitment: [u8; 32],
    /// The post-state commitment the service turn is committed to move TO (the
    /// escrow's TRUSTED post endpoint, carried from the promise).
    pub expected_post_commitment: [u8; 32],
    /// The asset payment settles in.
    pub payment_asset: AssetId,
    /// The matched price (the verified ring leg's amount).
    pub price: u64,
    /// The promise window (refund becomes available after this height).
    pub timeout_height: u64,
    /// The ring the solver matched (audit: the cycle these two formed).
    pub ring: RingTrade,
}

impl ServiceMatch {
    /// A 32-byte canonical digest binding WHICH service-for-payment this escrow
    /// holds: the two parties, the service + its fulfillment hole, the payment
    /// asset, the held price, and the promise window. Domain-separated so it can
    /// never collide with any other heap value's preimage. Bound into the escrow
    /// cell's commitment (at [`KEY_SP_TERMS_DIGEST`]) so the held leg can never be
    /// reinterpreted under different terms — the same discipline
    /// [`dregg_cell::escrow_sealed::EscrowTerms::digest`] uses for the 2-of-2 swap.
    pub fn terms_digest(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg.service-promise.escrow-terms.v1");
        h.update(&self.provider.0);
        h.update(&self.consumer.0);
        h.update(self.service.as_bytes());
        h.update(&self.service_turn_hash);
        h.update(&self.expected_pre_commitment);
        h.update(&self.expected_post_commitment);
        h.update(&self.payment_asset);
        h.update(&self.price.to_le_bytes());
        h.update(&self.timeout_height.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

// ===========================================================================
// The COMMITTED escrow one-shot — release/refund mutual-exclusion bound into a
// CELL COMMITMENT, not the orchestrator's memory.
// ===========================================================================
//
// The held payment's terminal exit (release → provider XOR refund → consumer) is
// a one-shot: taken exactly once, by exactly one exit. Binding that into the
// escrow cell's committed heap — mirroring `dregg_cell::escrow_sealed`'s
// consumed-once discipline — means a RE-EXECUTING validator (not just the
// coordinator that ran the turn) witnesses the exclusion: once the cell records a
// terminal status, the committed state itself refuses the other exit. The
// in-memory [`EscrowStatus`] on [`ServiceEscrow`] is a convenience mirror; the
// committed cell is the AUTHORITY.

/// Reserved heap collection id for the service-promise escrow's committed
/// one-shot ledger. Lives inside the escrow cell's committed heap, so the held
/// amount and its consumed-once status are folded into the canonical state
/// commitment. Chosen high to avoid colliding with application heap collections,
/// distinct from [`dregg_cell::escrow_sealed::ESCROW_COLL`].
pub const SERVICE_ESCROW_COLL: u32 = 0x0053_5645; // "SVE" — service escrow

/// Heap key: the 32-byte [`ServiceMatch::terms_digest`] this escrow binds.
pub const KEY_SP_TERMS_DIGEST: u32 = 0;
/// Heap key: the held payment amount (canonical little-endian `i64`).
pub const KEY_SP_HELD_AMOUNT: u32 = 1;
/// Heap key: the lifecycle status felt — `1` Funded, `2` Released, `3` Refunded.
pub const KEY_SP_STATUS: u32 = 2;

const SP_STATUS_FUNDED: i64 = 1;
const SP_STATUS_RELEASED: i64 = 2;
const SP_STATUS_REFUNDED: i64 = 3;

/// The escrow's COMMITTED one-shot state, recovered from the escrow cell's heap —
/// the authority a re-executing validator consults (the held amount and the
/// consumed-once status are bound into the cell commitment, not held in
/// orchestrator memory).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommittedEscrow {
    /// The bound [`ServiceMatch::terms_digest`].
    pub terms_digest: [u8; 32],
    /// The held payment amount committed at fund time.
    pub held_amount: i64,
    /// The committed lifecycle status (the one-shot authority).
    pub status: EscrowStatus,
}

impl CommittedEscrow {
    /// Recover the committed escrow state from a cell, or `None` if the cell
    /// carries no service-escrow binding.
    pub fn read(cell: &Cell) -> Option<CommittedEscrow> {
        let terms_digest = cell
            .state
            .get_heap(SERVICE_ESCROW_COLL, KEY_SP_TERMS_DIGEST)?;
        let held_amount = cell
            .state
            .get_heap(SERVICE_ESCROW_COLL, KEY_SP_HELD_AMOUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let status = match cell
            .state
            .get_heap(SERVICE_ESCROW_COLL, KEY_SP_STATUS)
            .map(|f| decode_i64(&f))
            .unwrap_or(SP_STATUS_FUNDED)
        {
            SP_STATUS_RELEASED => EscrowStatus::Released,
            SP_STATUS_REFUNDED => EscrowStatus::Refunded,
            _ => EscrowStatus::Funded,
        };
        Some(CommittedEscrow {
            terms_digest,
            held_amount,
            status,
        })
    }
}

/// Open the committed escrow binding on `cell`: bind the terms digest, the held
/// amount, and a `Funded` status into the cell's commitment. After this the cell
/// commitment binds the held leg; a light client sees value is escrowed.
fn open_committed_escrow(cell: &mut Cell, matched: &ServiceMatch) {
    let st = &mut cell.state;
    st.set_heap(
        SERVICE_ESCROW_COLL,
        KEY_SP_TERMS_DIGEST,
        matched.terms_digest(),
    );
    st.set_heap(
        SERVICE_ESCROW_COLL,
        KEY_SP_HELD_AMOUNT,
        encode_i64(matched.price as i64),
    );
    st.set_heap(
        SERVICE_ESCROW_COLL,
        KEY_SP_STATUS,
        encode_i64(SP_STATUS_FUNDED),
    );
}

/// Flip the committed escrow status from `Funded` to a terminal exit, enforcing
/// the one-shot IN COMMITTED STATE: if the cell already records a terminal status
/// (or carries no/mismatched binding) the flip is REFUSED with
/// [`ServicePromiseError::AlreadySettled`] — a second release/refund is rejected
/// by the commitment, not an in-memory flag. This is the gate a re-executing
/// validator runs, so the exclusion is witnessed by anyone holding the cell.
fn commit_terminal(
    cell: &mut Cell,
    matched: &ServiceMatch,
    terminal: i64,
) -> Result<(), ServicePromiseError> {
    let view = CommittedEscrow::read(cell).ok_or(ServicePromiseError::AlreadySettled)?;
    if view.terms_digest != matched.terms_digest() || view.status != EscrowStatus::Funded {
        return Err(ServicePromiseError::AlreadySettled);
    }
    cell.state
        .set_heap(SERVICE_ESCROW_COLL, KEY_SP_STATUS, encode_i64(terminal));
    Ok(())
}

/// The lifecycle state of an escrowed promise. `Funded` is the only OPEN state;
/// `Released` and `Refunded` are one-shot terminals — a released escrow can never
/// refund and vice-versa (the held payment is taken exactly once).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EscrowStatus {
    /// Payment is held against the promise; awaiting fulfillment or lapse.
    Funded,
    /// Fulfillment was proven; payment was released to the provider.
    Released,
    /// The promise lapsed; payment was refunded to the consumer.
    Refunded,
}

/// A funded service escrow — the held payment plus the fulfillment condition that
/// gates its release.
#[derive(Clone, Debug)]
pub struct ServiceEscrow {
    /// The match this escrow was opened for.
    pub matched: ServiceMatch,
    /// The account holding the payment until release/refund.
    pub escrow: CommitmentId,
    /// The escrow CELL whose committed heap binds the held leg + its consumed-once
    /// status — the one-shot AUTHORITY a re-executing validator consults (see
    /// [`CommittedEscrow`]). The [`status`](Self::status) field is its in-memory
    /// mirror.
    pub escrow_cell: Cell,
    /// The fulfillment condition (the promise hole): a [`ProofCondition::TurnProven`]
    /// naming the promised service turn + its committed pre/post endpoints. Swap this
    /// for a `LocalProof`/`RemoteProof` to gate release on an outcome predicate instead
    /// of a proven execution.
    pub condition: ProofCondition,
    /// In-memory mirror of the committed lifecycle status. The committed cell
    /// ([`escrow_cell`](Self::escrow_cell)) is authoritative.
    pub status: EscrowStatus,
}

impl ServiceEscrow {
    /// Whether the escrow is still open (payment held, not yet released/refunded).
    pub fn is_open(&self) -> bool {
        matches!(self.status, EscrowStatus::Funded)
    }
}

/// Why a service-promise operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServicePromiseError {
    /// The promise and request name different services — nothing to match.
    ServiceMismatch,
    /// The promise and request settle in different payment assets.
    AssetMismatch,
    /// The consumer's offer does not cover the provider's price.
    Underfunded {
        /// What the consumer offered.
        offered: u64,
        /// What the provider asked.
        price: u64,
    },
    /// The ring matcher found no conserving cycle for the pair (e.g. a zero
    /// price, or the two share a verified-ledger cell index).
    NoMatch,
    /// A value move did not settle/conserve on the verified executor. Atomic: on
    /// this error no state changed.
    NotConserving(VerifiedSettleError),
    /// The escrow is already released or refunded — its one-shot exit was taken.
    AlreadySettled,
    /// Fulfillment was attempted but the presented proof did not resolve the
    /// promise (wrong/forged receipt, expired window, untrusted executor). No
    /// payment moved — the escrow stays funded.
    Unfulfilled(String),
    /// A refund was attempted before the promise window lapsed.
    NotYetRefundable {
        /// The height the refund was attempted at.
        current_height: u64,
        /// The height the promise window closes at.
        timeout_height: u64,
    },
}

impl std::fmt::Display for ServicePromiseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ServiceMismatch => write!(f, "promise and request name different services"),
            Self::AssetMismatch => write!(f, "promise and request use different payment assets"),
            Self::Underfunded { offered, price } => {
                write!(f, "consumer offers {offered} but provider asks {price}")
            }
            Self::NoMatch => write!(f, "no conserving service ring matched the pair"),
            Self::NotConserving(e) => write!(f, "value move did not conserve: {e}"),
            Self::AlreadySettled => write!(f, "escrow already released or refunded (one-shot)"),
            Self::Unfulfilled(d) => write!(f, "promise not fulfilled: {d}"),
            Self::NotYetRefundable {
                current_height,
                timeout_height,
            } => write!(
                f,
                "promise window still open: height {current_height} <= timeout {timeout_height}"
            ),
        }
    }
}

impl std::error::Error for ServicePromiseError {}

/// **The service-promise exchange.**
///
/// Holds the ring bound, the wall-clock `now` intents are judged against, and the
/// escrow holding account. It owns no value — value lives in the verified ledger; the
/// exchange MATCHES promises and drives the held-payment lifecycle through the
/// verified executor. Fulfillment is a VERIFIED EffectVM STARK (a [`ProvenReceipt`]),
/// not a trusted signature (assurance-perimeter #3).
#[derive(Clone, Debug)]
pub struct ServicePromiseExchange {
    /// Largest cycle the ring matcher searches (≥ 2; a service pair is a 2-cycle).
    pub max_ring_size: usize,
    /// The wall-clock time posted intents are judged fresh against.
    pub now: u64,
    /// The account that holds escrowed payments between fund and release/refund.
    pub escrow: CommitmentId,
    /// RETIRED as a trust root (assurance-perimeter #3): a trusted executor SIGNATURE
    /// no longer resolves the default fulfillment path (that path now requires a
    /// verified EffectVM STARK). Retained for API stability and the `RemoteProof`/
    /// `LocalProof` fulfillment variants; the default `TurnProven` path ignores it.
    pub trusted_executor_keys: Vec<[u8; 32]>,
    /// Maximum age (in blocks) a federation root may be for a `RemoteProof`
    /// fulfillment; unused by the default `TurnProven` path.
    pub max_root_age: u64,
}

impl ServicePromiseExchange {
    /// A new exchange holding escrowed payments in `escrow`, accepting fulfillment
    /// receipts signed by any of `trusted_executor_keys`.
    pub fn new(
        max_ring_size: usize,
        now: u64,
        escrow: CommitmentId,
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Self {
        Self {
            max_ring_size,
            now,
            escrow,
            trusted_executor_keys,
            max_root_age: u64::MAX,
        }
    }

    /// **Match** a posted promise with a posted request, through the SAME ring
    /// matcher the asset ring uses.
    ///
    /// Encodes the provider and consumer as ring intents — the service as a
    /// synthetic promise-token asset, the payment as the real asset — and asks the
    /// [`RingSolver`] for a cycle. A compatible pair is exactly a 2-cycle; the
    /// matched payment leg (consumer → provider, in the payment asset) carries the
    /// price the escrow will hold.
    pub fn match_one(
        &self,
        promise: &ServicePromise,
        request: &ServiceRequest,
    ) -> Result<ServiceMatch, ServicePromiseError> {
        if promise.service != request.service {
            return Err(ServicePromiseError::ServiceMismatch);
        }
        if promise.payment_asset != request.payment_asset {
            return Err(ServicePromiseError::AssetMismatch);
        }
        if request.offer < promise.price {
            return Err(ServicePromiseError::Underfunded {
                offered: request.offer,
                price: promise.price,
            });
        }

        let expiry = self.now.saturating_add(3600);
        let service_asset = promise.service.as_asset();

        // The provider offers the promise-token, wants payment.
        let provider_node = IntentNode {
            intent_id: intent_id(
                &promise.provider,
                b"provider",
                &service_asset,
                promise.price,
            ),
            exchange: ExchangeSpec {
                offer_asset: service_asset,
                offer_amount: 1,
                want_asset: promise.payment_asset,
                want_min_amount: promise.price,
                min_rate: None,
                max_rate: None,
            },
            creator: promise.provider,
            expiry,
        };
        // The consumer offers payment, wants the promise-token.
        let consumer_node = IntentNode {
            intent_id: intent_id(
                &request.consumer,
                b"consumer",
                &request.payment_asset,
                request.offer,
            ),
            exchange: ExchangeSpec {
                offer_asset: request.payment_asset,
                offer_amount: request.offer,
                want_asset: service_asset,
                want_min_amount: 1,
                min_rate: None,
                max_rate: None,
            },
            creator: request.consumer,
            expiry,
        };

        let solver = RingSolver::new(self.max_ring_size);
        let ring = solver
            .solve_best(&[provider_node, consumer_node], self.now)
            .ok_or(ServicePromiseError::NoMatch)?;

        // The payment leg is the matched settlement in the payment asset
        // (consumer → provider). Its amount is the verified matched price.
        let pay = ring
            .settlements
            .iter()
            .find(|s| s.asset == promise.payment_asset)
            .ok_or(ServicePromiseError::NoMatch)?;
        if pay.from != request.consumer || pay.to != promise.provider {
            return Err(ServicePromiseError::NoMatch);
        }

        Ok(ServiceMatch {
            provider: promise.provider,
            consumer: request.consumer,
            service: promise.service,
            service_turn_hash: promise.service_turn_hash,
            expected_pre_commitment: promise.expected_pre_commitment,
            expected_post_commitment: promise.expected_post_commitment,
            payment_asset: promise.payment_asset,
            price: pay.amount,
            timeout_height: promise.timeout_height,
            ring,
        })
    }

    /// **Fund** the escrow: move the matched payment from the consumer into the
    /// escrow account through the verified executor (per-asset Σδ=0), and open the
    /// escrow bound by the fulfillment condition. Returns the funded escrow and the
    /// post-ledger. Atomic: if the move does not conserve/settle, nothing changes.
    pub fn fund(
        &self,
        matched: &ServiceMatch,
        ledger: &WideLedger,
    ) -> Result<(ServiceEscrow, WideLedger), ServicePromiseError> {
        let leg = WideLeg {
            from: matched.consumer.0,
            to: self.escrow.0,
            asset: matched.payment_asset,
            amount: matched.price as i128,
        };
        let post = settle_ring_wide_verified(ledger, &[leg])
            .map_err(ServicePromiseError::NotConserving)?;
        // Bind the held leg + its one-shot status into the escrow cell's
        // commitment (the AUTHORITY); a light client sees value is escrowed.
        let mut escrow_cell = Cell::with_balance(self.escrow.0, matched.payment_asset, 0);
        open_committed_escrow(&mut escrow_cell, matched);
        let escrow = ServiceEscrow {
            matched: matched.clone(),
            escrow: self.escrow,
            escrow_cell,
            condition: ProofCondition::TurnProven {
                turn_hash: matched.service_turn_hash,
                expected_pre_commitment: matched.expected_pre_commitment,
                expected_post_commitment: matched.expected_post_commitment,
            },
            status: EscrowStatus::Funded,
        };
        Ok((escrow, post))
    }

    /// **Fulfill**: the provider presents the VERIFIED proof its promised service turn
    /// ran (a [`ConditionProof::EffectVmProof`] from its [`ProvenReceipt`], built via
    /// [`fulfillment_proof`]). The proof FILLS the promise hole via [`resolve_condition`]
    /// — a real EffectVM STARK bound to the promised turn hash + pre/post endpoints, no
    /// signature consulted; on `Resolved` the held payment RELEASES escrow → provider
    /// through the verified executor and the escrow becomes [`EscrowStatus::Released`].
    ///
    /// If the proof does not resolve (wrong/forged/tampered proof, a proof of a different
    /// transition, expired window) NOTHING moves and the escrow stays funded — there is no
    /// half-settle. A released or refunded escrow refuses
    /// ([`ServicePromiseError::AlreadySettled`]).
    pub fn fulfill(
        &self,
        escrow: &mut ServiceEscrow,
        ledger: &WideLedger,
        proof: &ConditionProof,
        current_height: u64,
    ) -> Result<WideLedger, ServicePromiseError> {
        if !escrow.is_open() {
            return Err(ServicePromiseError::AlreadySettled);
        }

        // Fill the hole: does the presented proof resolve the promise condition?
        let mut used_proof_hashes: HashSet<[u8; 32]> = HashSet::new();
        let result = resolve_condition(
            &escrow.condition,
            proof,
            current_height,
            escrow.matched.timeout_height,
            &[], // no federation roots needed for the TurnExecuted path
            self.max_root_age,
            &mut used_proof_hashes,
            &self.trusted_executor_keys,
        );
        if result != ConditionalResult::Resolved {
            return Err(ServicePromiseError::Unfulfilled(format!("{result:?}")));
        }

        // Take the one-shot terminal in COMMITTED state BEFORE any value moves:
        // this is the authority a re-executing validator runs, so a second
        // release/refund is refused by the commitment, not an in-memory flag.
        commit_terminal(&mut escrow.escrow_cell, &escrow.matched, SP_STATUS_RELEASED)?;

        // Promise fulfilled — release the held payment to the provider. Atomic.
        let leg = WideLeg {
            from: escrow.escrow.0,
            to: escrow.matched.provider.0,
            asset: escrow.matched.payment_asset,
            amount: escrow.matched.price as i128,
        };
        let post = settle_ring_wide_verified(ledger, &[leg])
            .map_err(ServicePromiseError::NotConserving)?;
        escrow.status = EscrowStatus::Released;
        Ok(post)
    }

    /// **Refund**: once the promise window has lapsed (`current_height >
    /// timeout_height`) with no fulfillment, return the held payment to the
    /// consumer through the verified executor and mark the escrow
    /// [`EscrowStatus::Refunded`]. A released or refunded escrow refuses; a refund
    /// before the window closes refuses ([`ServicePromiseError::NotYetRefundable`]).
    pub fn refund(
        &self,
        escrow: &mut ServiceEscrow,
        ledger: &WideLedger,
        current_height: u64,
    ) -> Result<WideLedger, ServicePromiseError> {
        if !escrow.is_open() {
            return Err(ServicePromiseError::AlreadySettled);
        }
        if current_height <= escrow.matched.timeout_height {
            return Err(ServicePromiseError::NotYetRefundable {
                current_height,
                timeout_height: escrow.matched.timeout_height,
            });
        }
        // Take the one-shot terminal in COMMITTED state BEFORE any value moves —
        // the same committed authority release runs, so the two exits exclude.
        commit_terminal(&mut escrow.escrow_cell, &escrow.matched, SP_STATUS_REFUNDED)?;
        let leg = WideLeg {
            from: escrow.escrow.0,
            to: escrow.matched.consumer.0,
            asset: escrow.matched.payment_asset,
            amount: escrow.matched.price as i128,
        };
        let post = settle_ring_wide_verified(ledger, &[leg])
            .map_err(ServicePromiseError::NotConserving)?;
        escrow.status = EscrowStatus::Refunded;
        Ok(post)
    }

    /// Seed a verified ledger with the three accounts a single service-for-payment
    /// touches (consumer, provider, escrow), funding the consumer with
    /// `consumer_balance` of the payment asset. The conserved reference the
    /// lifecycle settles against.
    pub fn seed_ledger(&self, matched: &ServiceMatch, consumer_balance: u64) -> WideLedger {
        let mut k = WideLedger::new();
        for cell in [matched.consumer.0, matched.provider.0, self.escrow.0] {
            k.add_account(cell);
        }
        k.set(
            matched.consumer.0,
            &matched.payment_asset,
            consumer_balance as i128,
        );
        k
    }
}

/// A content-addressed ring-intent id for one side of a service promise (binds the
/// party, its role, and its exchange terms). Distinct roles/parties get distinct
/// ids, in the same spirit as `ring_trade::intent_id_for`.
fn intent_id(creator: &CommitmentId, role: &[u8], asset: &AssetId, amount: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg.service-promise.intent-id.v1");
    h.update(&creator.0);
    h.update(role);
    h.update(asset);
    h.update(&amount.to_le_bytes());
    *h.finalize().as_bytes()
}

/// Build a fulfillment proof from the provider's [`ProvenReceipt`] — the
/// [`ConditionProof::EffectVmProof`] the provider presents to fill the promise hole
/// (assurance-perimeter #3). The provider performed the service turn through the
/// commit pipeline, which produced the VERIFIED rotated EffectVM STARK bundled in the
/// `ProvenReceipt`; that PROOF (not a trusted signature) is what resolves the escrow's
/// [`ProofCondition::TurnProven`] — the proof's turn hash must equal the promised
/// `service_turn_hash` and its wide anchors must equal the promised pre/post
/// endpoints. Exposed as a helper because "the provider performed the turn, here is
/// the proof" is the whole fulfillment gesture.
pub fn fulfillment_proof(proven: &ProvenReceipt) -> ConditionProof {
    proven.effect_vm_proof()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CommitmentId {
        CommitmentId([b; 32])
    }
    fn asset(b: u8) -> AssetId {
        let mut a = [0u8; 32];
        a[0] = b;
        a
    }

    fn sample() -> (
        ServicePromiseExchange,
        ServicePromise,
        ServiceRequest,
        [u8; 32],
    ) {
        let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
        let service_turn_hash = [0xAB; 32];
        let promise = ServicePromise {
            provider: cid(2),
            service,
            service_turn_hash,
            expected_pre_commitment: [0x11; 32],
            expected_post_commitment: [0x22; 32],
            payment_asset: asset(7),
            price: 100,
            timeout_height: 50,
        };
        let request = ServiceRequest {
            consumer: cid(1),
            service,
            payment_asset: asset(7),
            offer: 100,
        };
        let exchange = ServicePromiseExchange::new(4, 0, cid(9), vec![]);
        (exchange, promise, request, service_turn_hash)
    }

    #[test]
    fn match_pairs_provider_and_consumer_through_the_ring() {
        let (exchange, promise, request, _) = sample();
        let m = exchange
            .match_one(&promise, &request)
            .expect("pair must match");
        assert_eq!(m.provider, cid(2));
        assert_eq!(m.consumer, cid(1));
        assert_eq!(m.price, 100);
        assert_eq!(m.payment_asset, asset(7));
        // The match was found by the real ring solver (the cycle is recorded).
        assert_eq!(m.ring.participants.len(), 2);
    }

    #[test]
    fn mismatched_service_or_asset_or_underfunded_refuses() {
        let (exchange, promise, request, _) = sample();

        let mut wrong_service = request.clone();
        wrong_service.service = ServiceId::from_bytes([0xFF; 32]);
        assert!(matches!(
            exchange.match_one(&promise, &wrong_service),
            Err(ServicePromiseError::ServiceMismatch)
        ));

        let mut wrong_asset = request.clone();
        wrong_asset.payment_asset = asset(8);
        assert!(matches!(
            exchange.match_one(&promise, &wrong_asset),
            Err(ServicePromiseError::AssetMismatch)
        ));

        let mut poor = request.clone();
        poor.offer = 1;
        assert!(matches!(
            exchange.match_one(&promise, &poor),
            Err(ServicePromiseError::Underfunded {
                offered: 1,
                price: 100
            })
        ));
    }

    #[test]
    fn fund_escrows_the_payment_conserved() {
        let (exchange, promise, request, _) = sample();
        let m = exchange.match_one(&promise, &request).unwrap();
        let k0 = exchange.seed_ledger(&m, 100);
        assert_eq!(k0.get(m.consumer.0, &m.payment_asset), 100);

        let (escrow, k1) = exchange.fund(&m, &k0).expect("fund must settle");
        // Payment left the consumer and is held in escrow; provider untouched.
        assert_eq!(k1.get(m.consumer.0, &m.payment_asset), 0);
        assert_eq!(k1.get(exchange.escrow.0, &m.payment_asset), 100);
        assert_eq!(k1.get(m.provider.0, &m.payment_asset), 0);
        assert_eq!(escrow.status, EscrowStatus::Funded);
        // Conserved.
        assert_eq!(k1.total_asset(&m.payment_asset), 100);
        // The held leg + Funded status are bound into the escrow CELL's
        // commitment (the authority), not just the in-memory mirror.
        let committed = CommittedEscrow::read(&escrow.escrow_cell).expect("escrow binding");
        assert_eq!(committed.status, EscrowStatus::Funded);
        assert_eq!(committed.held_amount, 100);
        assert_eq!(committed.terms_digest, m.terms_digest());
    }

    // ── GAP 1: full 32-byte indexing — no low-byte collision ─────────────────

    /// A three party set whose commitments SHARE a low byte (0x07) but differ
    /// above it. Under the OLD low-byte projection consumer, provider, and escrow
    /// all aliased to verified-ledger cell 7 — the consumer→escrow payment would
    /// collapse into a `from == to` self-leg the gate rejects, and the parties'
    /// balances would merge. Full 32-byte indexing keeps them distinct, so the
    /// escrow funds and conserves correctly.
    #[test]
    fn full_indexing_avoids_low_byte_collision() {
        let mut c = [0u8; 32];
        c[0] = 0x07;
        c[1] = 0x01;
        let mut p = [0u8; 32];
        p[0] = 0x07;
        p[1] = 0x02;
        let mut e = [0u8; 32];
        e[0] = 0x07;
        e[1] = 0x03;
        let consumer = CommitmentId(c);
        let provider = CommitmentId(p);
        let escrow_id = CommitmentId(e);
        // They genuinely collide on the low byte the OLD path keyed by.
        assert_eq!(consumer.0[0], provider.0[0]);
        assert_eq!(consumer.0[0], escrow_id.0[0]);

        let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
        let promise = ServicePromise {
            provider,
            service,
            service_turn_hash: [0xAB; 32],
            expected_pre_commitment: [0x11; 32],
            expected_post_commitment: [0x22; 32],
            payment_asset: asset(7),
            price: 100,
            timeout_height: 50,
        };
        let request = ServiceRequest {
            consumer,
            service,
            payment_asset: asset(7),
            offer: 100,
        };
        let exchange = ServicePromiseExchange::new(4, 0, escrow_id, vec![]);

        let m = exchange
            .match_one(&promise, &request)
            .expect("pair matches");
        let k0 = exchange.seed_ledger(&m, 100);
        let (escrow, k1) = exchange
            .fund(&m, &k0)
            .expect("distinct full ids fund despite the shared low byte");

        // Three DISTINCT accounts — payment moved consumer → escrow, provider untouched.
        assert_eq!(k1.get(consumer.0, &asset(7)), 0);
        assert_eq!(k1.get(escrow_id.0, &asset(7)), 100);
        assert_eq!(k1.get(provider.0, &asset(7)), 0);
        assert_eq!(k1.total_asset(&asset(7)), 100, "conserved, no merge");
        assert_eq!(escrow.status, EscrowStatus::Funded);
    }

    // ── GAP 2: committed-state one-shot, witnessed by RE-EXECUTION ────────────

    /// Drive a full match → fund → fulfill, then take ONLY the escrow cell's
    /// committed state (what a re-executing validator has — no orchestrator
    /// in-memory flag) and show the committed status is `Released` AND that the
    /// committed state itself REFUSES a refund. The exclusion is bound into the
    /// commitment, not the coordinator's memory.
    ///
    /// The provider's committed transition is a GENUINE minted [`ProvenReceipt`]: its
    /// wide endpoints ARE what the provider promises (`expected_pre/post_commitment`),
    /// and its verified EffectVM STARK is what fulfills. Heavy: mints one real proof.
    fn fund_one() -> (
        ServicePromiseExchange,
        ServiceEscrow,
        WideLedger,
        ProvenReceipt,
    ) {
        let service = ServiceId::of(CellId::from_bytes([0x5e; 32]), "render-report");
        let service_turn_hash = [0xAB; 32];
        let proven = dregg_turn_prover::mint_transfer_proven_receipt(service_turn_hash, 7);
        let promise = ServicePromise {
            provider: cid(2),
            service,
            service_turn_hash,
            expected_pre_commitment: proven.pre_commitment,
            expected_post_commitment: proven.post_commitment,
            payment_asset: asset(7),
            price: 100,
            timeout_height: 50,
        };
        let request = ServiceRequest {
            consumer: cid(1),
            service,
            payment_asset: asset(7),
            offer: 100,
        };
        let exchange = ServicePromiseExchange::new(4, 0, cid(9), vec![]);
        let m = exchange.match_one(&promise, &request).unwrap();
        let k0 = exchange.seed_ledger(&m, 100);
        let (escrow, k1) = exchange.fund(&m, &k0).unwrap();
        (exchange, escrow, k1, proven)
    }

    #[test]
    fn committed_state_forbids_refund_after_release() {
        let (exchange, mut escrow, k1, proven) = fund_one();
        let proof = fulfillment_proof(&proven);
        exchange
            .fulfill(&mut escrow, &k1, &proof, 10)
            .expect("a verified proof releases");

        // The commitment moved (a light client sees the terminal state).
        let committed = CommittedEscrow::read(&escrow.escrow_cell).expect("binding");
        assert_eq!(committed.status, EscrowStatus::Released);

        // RE-EXECUTION view: a validator holding ONLY the committed cell (no
        // orchestrator memory) finds the committed state refuses the refund exit.
        let mut replay = escrow.escrow_cell.clone();
        assert_eq!(
            commit_terminal(&mut replay, &escrow.matched, SP_STATUS_REFUNDED),
            Err(ServicePromiseError::AlreadySettled),
            "committed Released forbids a refund flip, by re-execution"
        );
        // And it cannot release twice either.
        assert_eq!(
            commit_terminal(&mut replay, &escrow.matched, SP_STATUS_RELEASED),
            Err(ServicePromiseError::AlreadySettled)
        );
    }

    #[test]
    fn committed_state_forbids_release_after_refund() {
        let (exchange, mut escrow, k1, _) = fund_one();
        exchange
            .refund(&mut escrow, &k1, 51)
            .expect("lapsed promise refunds");

        let committed = CommittedEscrow::read(&escrow.escrow_cell).expect("binding");
        assert_eq!(committed.status, EscrowStatus::Refunded);

        // RE-EXECUTION view: committed Refunded refuses the release exit.
        let mut replay = escrow.escrow_cell.clone();
        assert_eq!(
            commit_terminal(&mut replay, &escrow.matched, SP_STATUS_RELEASED),
            Err(ServicePromiseError::AlreadySettled),
            "committed Refunded forbids a release flip, by re-execution"
        );
    }

    #[test]
    fn committed_terminal_moves_the_cell_commitment() {
        let (exchange, mut escrow, k1, proven) = fund_one();
        let before = escrow.escrow_cell.state_commitment();
        let proof = fulfillment_proof(&proven);
        exchange.fulfill(&mut escrow, &k1, &proof, 10).unwrap();
        let after = escrow.escrow_cell.state_commitment();
        assert_ne!(
            before, after,
            "taking the one-shot terminal re-seals the escrow cell's commitment"
        );
    }
}
