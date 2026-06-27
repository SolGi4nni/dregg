//! Cross-node handoff TRANSPORT: routing a [`HandoffPresentation`] over a live
//! [`Netlayer`](crate::netlayer::Netlayer) connection and resolving the
//! acceptance into a USABLE capability on the receiving node.
//!
//! # The missing leg
//!
//! [`crate::handoff`] already mints + validates a [`HandoffCertificate`]: a
//! signed third-party introduction with the proven non-amplification tooth
//! (`granted ⊆ held`, `granted.target = held.target`). [`crate::netlayer`]
//! already moves opaque frames between two parties (in-process or store-and-
//! forward over a relay). What was missing — the rung-7 federation-census gap —
//! is the WIRE between them: a node A holding a cap presents the introduction to
//! node B *over the transport*, B verifies it against its OWN swiss table +
//! `known_federations`, and resolves it into a live cap B can EXERCISE.
//!
//! This module is that wire. It is transport-agnostic: it speaks the
//! [`NetConnection`](crate::netlayer::NetConnection) frame trait, so the same
//! code drives the in-process fabric (the deterministic two-party test net) and
//! the relay netlayer (the real federation store-and-forward channel).
//!
//! # Flow (A = introducer/holder on node A, B = target on node B)
//!
//! 1. A registered a swiss entry at B recording what A holds for the cell
//!    (B's authoritative `held` record). A mints a [`HandoffCertificate`]
//!    naming the recipient and the (attenuated) granted authority.
//! 2. The recipient signs a [`HandoffPresentation`]. A (or the recipient,
//!    holding the connection) [`present_handoff`]s it as a frame over the
//!    transport to B.
//! 3. B [`accept_handoff`]s: it deserializes the frame, runs the PROVEN
//!    [`validate_handoff`] (introducer sig · recipient sig · known-federation ·
//!    expiry · swiss · TARGET-BIND · NON-AMPLIFICATION · replay), and on success
//!    [`resolve`](HandoffResolution::into_send_cap)s the acceptance into a
//!    [`SendCap`] bounded by the held authority. B replies with a
//!    [`HandoffReply`] frame.
//! 4. B EXERCISES the cap: a real [`Bus::enqueue`](crate::data_plane::Bus)
//!    leaving a signed custody receipt — the handed-off authority genuinely
//!    works, and an over-broad handoff was refused at step 3.
//!
//! Authority is NEVER amplified by the transport: B reads `held` from its own
//! swiss table (not the cert) and the resolved [`SendCap::grant`] is the
//! validated (attenuated) authority, which the Bus seam re-checks on every
//! enqueue.

use serde::{Deserialize, Serialize};

use dregg_cell::AuthRequired;
use dregg_types::{CellId, PublicKey};

use crate::FederationId;
use crate::data_plane::{ChannelName, SendCap};
use crate::handoff::{HandoffAcceptance, HandoffError, HandoffPresentation, validate_handoff};
use crate::netlayer::{NetConnection, NetlayerError};
use crate::sturdy::SwissTable;

// =============================================================================
// Wire frames
// =============================================================================

/// The frame a holder sends to present a handoff to a target node over a
/// [`NetConnection`]. Carries the introducer-signed presentation plus the
/// introducer's public key (so the target can verify the introducer signature
/// without an out-of-band directory lookup — the key is still cross-checked
/// against `known_federations` by id at the target).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PresentHandoffFrame {
    /// The serialized [`HandoffPresentation`] (certificate + recipient sig).
    pub presentation_bytes: Vec<u8>,
    /// The introducer's Ed25519 public key, for verifying the cert signature.
    pub introducer_pk: [u8; 32],
}

/// The target's reply after running [`validate_handoff`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HandoffReply {
    /// The handoff was accepted: the recipient now holds an attenuated cap.
    Accepted {
        /// A routing token for ongoing access (mirrors `HandoffAcceptance`).
        routing_token: [u8; 32],
        /// The cell the recipient now has access to.
        cell_id: [u8; 32],
        /// The granted (attenuated) permission tag.
        permissions_tag: u8,
    },
    /// The handoff was refused. `reason` is the [`HandoffError`] display string;
    /// `amplification` is set when the refusal was specifically an
    /// authority-amplification attempt (granted ⊄ held), the no-amplification
    /// bound this transport exists to enforce.
    Refused { reason: String, amplification: bool },
}

/// Errors carrying a presentation across the transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HandoffTransportError {
    /// The underlying netlayer connection failed.
    Net(NetlayerError),
    /// A frame could not be (de)serialized.
    Codec(String),
    /// The peer closed before a reply arrived.
    NoReply,
}

impl std::fmt::Display for HandoffTransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HandoffTransportError::Net(e) => write!(f, "handoff transport net error: {e}"),
            HandoffTransportError::Codec(e) => write!(f, "handoff transport codec error: {e}"),
            HandoffTransportError::NoReply => write!(f, "peer closed before handoff reply"),
        }
    }
}

impl std::error::Error for HandoffTransportError {}

impl From<NetlayerError> for HandoffTransportError {
    fn from(e: NetlayerError) -> Self {
        HandoffTransportError::Net(e)
    }
}

fn perm_tag(a: &AuthRequired) -> u8 {
    match a {
        AuthRequired::None => 0,
        AuthRequired::Signature => 1,
        AuthRequired::Proof => 2,
        AuthRequired::Either => 3,
        AuthRequired::Impossible => 4,
        AuthRequired::Custom { .. } => 5,
    }
}

// =============================================================================
// Introducer/holder side: present the handoff over the transport
// =============================================================================

/// Send a [`HandoffPresentation`] to the target node over `conn`.
///
/// This is the leg the federation census flagged missing: the
/// `PresentHandoffFrame` is now ROUTED over the node↔node connection (any
/// [`NetConnection`]: the in-process fabric or the relay store-and-forward
/// netlayer), not just constructed in memory. Await the verdict with
/// [`await_handoff_reply`].
pub async fn present_handoff<C: NetConnection>(
    conn: &C,
    presentation: &HandoffPresentation,
    introducer_pk: [u8; 32],
) -> Result<(), HandoffTransportError> {
    let frame = PresentHandoffFrame {
        presentation_bytes: postcard::to_stdvec(presentation)
            .map_err(|e| HandoffTransportError::Codec(e.to_string()))?,
        introducer_pk,
    };
    let bytes =
        postcard::to_stdvec(&frame).map_err(|e| HandoffTransportError::Codec(e.to_string()))?;
    conn.send(bytes).await?;
    Ok(())
}

/// Await the target's [`HandoffReply`] on `conn` after a [`present_handoff`].
///
/// `recv` is poll-shaped (`Ok(None)` = nothing pending yet); this spins,
/// yielding the thread, until a reply frame arrives or the peer closes. Split
/// from [`present_handoff`] so a single-threaded driver can interleave the
/// target's [`accept_handoff`] between the send and the reply-await (the
/// in-process fabric completes each frame synchronously).
pub async fn await_handoff_reply<C: NetConnection>(
    conn: &C,
) -> Result<HandoffReply, HandoffTransportError> {
    loop {
        match conn.recv().await {
            Ok(Some(reply_bytes)) => {
                let reply: HandoffReply = postcard::from_bytes(&reply_bytes)
                    .map_err(|e| HandoffTransportError::Codec(e.to_string()))?;
                return Ok(reply);
            }
            Ok(None) => std::thread::yield_now(),
            Err(NetlayerError::Closed) => return Err(HandoffTransportError::NoReply),
            Err(e) => return Err(HandoffTransportError::Net(e)),
        }
    }
}

// =============================================================================
// Target side: receive, verify, resolve into a usable cap
// =============================================================================

/// A successfully validated handoff at the target, ready to be turned into a
/// live capability the target can exercise.
#[derive(Clone, Debug)]
pub struct HandoffResolution {
    /// The full acceptance from the proven validator (held-bounded authority).
    pub acceptance: HandoffAcceptance,
}

impl HandoffResolution {
    /// The cell this resolution grants access to.
    pub fn cell_id(&self) -> CellId {
        self.acceptance.cell_id
    }

    /// The granted (attenuated) authority. By construction of
    /// [`validate_handoff`] this is `⊆` what the introducer held at the target.
    pub fn permissions(&self) -> &AuthRequired {
        &self.acceptance.permissions
    }

    /// Resolve the validated handoff into a live [`SendCap`] the target can
    /// exercise: the authority to enqueue, into `recipient`'s inbox under
    /// `channel`, at most as broad as the GRANTED (validated, held-bounded)
    /// permission. The data-plane [`Bus`](crate::data_plane::Bus) re-checks this
    /// grant on every enqueue, so the handed-off cap can never be amplified at
    /// use time either.
    pub fn into_send_cap(&self, recipient: FederationId, channel: ChannelName) -> SendCap {
        SendCap::grant(recipient, channel, self.acceptance.permissions.clone())
    }
}

/// Receive ONE pending [`PresentHandoffFrame`] from `conn`, validate it against
/// the target's swiss table + `known_federations` via the proven
/// [`validate_handoff`], reply with a [`HandoffReply`] over `conn`, and on
/// success return a [`HandoffResolution`].
///
/// Returns `Ok(None)` if no frame is pending yet (poll again).
///
/// The HELD authority is read from `swiss_table` (the target's authoritative
/// record), NOT from the certificate, so an introducer that forges/inflates the
/// cert's `permissions` cannot escalate beyond its registered rights: that path
/// is refused as [`HandoffError::Amplification`] and the reply is
/// `Refused { amplification: true }`.
pub async fn accept_handoff<C: NetConnection>(
    conn: &C,
    swiss_table: &mut SwissTable,
    known_federations: &[FederationId],
    current_height: u64,
) -> Result<Option<HandoffResolution>, HandoffTransportError> {
    let frame_bytes = match conn.recv().await {
        Ok(Some(b)) => b,
        Ok(None) => return Ok(None),
        Err(e) => return Err(HandoffTransportError::Net(e)),
    };

    let frame: PresentHandoffFrame = postcard::from_bytes(&frame_bytes)
        .map_err(|e| HandoffTransportError::Codec(e.to_string()))?;
    let presentation: HandoffPresentation = postcard::from_bytes(&frame.presentation_bytes)
        .map_err(|e| HandoffTransportError::Codec(e.to_string()))?;
    let introducer_pk = PublicKey(frame.introducer_pk);

    match validate_handoff(
        &presentation,
        &introducer_pk,
        swiss_table,
        known_federations,
        current_height,
    ) {
        Ok(acceptance) => {
            let reply = HandoffReply::Accepted {
                routing_token: acceptance.routing_token,
                cell_id: acceptance.cell_id.0,
                permissions_tag: perm_tag(&acceptance.permissions),
            };
            // Best-effort reply on the same conn. On a transport whose accept
            // side is inbound-only (e.g. the relay netlayer before the peer's
            // key is learned), this send fails closed; the resolution is still
            // authoritative and the caller re-routes the verdict on a dial-back.
            try_reply(conn, &reply).await;
            Ok(Some(HandoffResolution { acceptance }))
        }
        Err(e) => {
            let amplification = e == HandoffError::Amplification;
            let reply = HandoffReply::Refused {
                reason: e.to_string(),
                amplification,
            };
            try_reply(conn, &reply).await;
            Ok(None)
        }
    }
}

/// Best-effort: serialize and send a [`HandoffReply`] on `conn`, swallowing a
/// send failure (an inbound-only transport leg requires the caller to dial back
/// to deliver the verdict). Codec failure is unreachable for a `HandoffReply`.
async fn try_reply<C: NetConnection>(conn: &C, reply: &HandoffReply) {
    if let Ok(bytes) = postcard::to_stdvec(reply) {
        let _ = conn.send(bytes).await;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data_plane::Bus;
    use crate::handoff::HandoffCertificate;
    use crate::netlayer::{InProcessFabric, Netlayer};
    use dregg_cell::EffectMask;
    use dregg_types::{SigningKey, generate_keypair};

    /// A tiny no-op-waker executor (the in-process transport's futures never
    /// pend on external wakeups; they complete synchronously). Same shape as the
    /// `block_on` in `netlayer`'s test module — keeps `captp` tokio-free.
    fn block_on<F: std::future::Future>(fut: F) -> F::Output {
        use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
        fn raw() -> RawWaker {
            fn no_op(_: *const ()) {}
            fn clone(_: *const ()) -> RawWaker {
                raw()
            }
            RawWaker::new(
                std::ptr::null(),
                &RawWakerVTable::new(clone, no_op, no_op, no_op),
            )
        }
        let waker = unsafe { Waker::from_raw(raw()) };
        let mut cx = Context::from_waker(&waker);
        let mut fut = std::pin::pin!(fut);
        loop {
            match fut.as_mut().poll(&mut cx) {
                Poll::Ready(out) => return out,
                Poll::Pending => std::thread::yield_now(),
            }
        }
    }

    /// Drive one full handoff round over a freshly-dialed in-process session
    /// pair: A presents, B accepts (validates + replies), A reads the reply.
    /// Returns `(reply, Option<resolution>)`. Single-threaded, explicit order —
    /// the in-process fabric completes each frame synchronously, so the
    /// present → accept → await sequence needs no concurrency.
    fn drive_handoff(
        fabric: &InProcessFabric,
        presentation: &HandoffPresentation,
        introducer_pk: [u8; 32],
        swiss_table: &mut SwissTable,
        known: &[FederationId],
        height: u64,
    ) -> (HandoffReply, Option<HandoffResolution>) {
        block_on(async {
            let node_a = fabric.join([0xAA; 32]);
            let node_b = fabric.join([0xBB; 32]);
            let a_sess = node_a.dial(&[0xBB; 32]).await.unwrap();
            let b_sess = node_b
                .accept()
                .await
                .unwrap()
                .expect("B has a pending dial");

            // 1. A presents the handoff frame over the wire.
            present_handoff(&a_sess.conn, presentation, introducer_pk)
                .await
                .unwrap();
            // 2. B accepts: reads the frame, validates, sends its reply frame.
            let resolution = accept_handoff(&b_sess.conn, swiss_table, known, height)
                .await
                .unwrap();
            // 3. A reads B's reply.
            let reply = await_handoff_reply(&a_sess.conn).await.unwrap();
            (reply, resolution)
        })
    }

    /// Build a handoff scenario: an introducer/holder registers a swiss entry at
    /// the target recording `held` authority, then mints a cert granting
    /// `granted` authority to a fresh recipient. Returns the presentation, the
    /// introducer pk, the introducer federation id, and the target's swiss table.
    #[allow(clippy::type_complexity)]
    fn scenario(
        held: AuthRequired,
        held_effects: Option<EffectMask>,
        granted: AuthRequired,
        granted_effects: Option<EffectMask>,
    ) -> (
        HandoffPresentation,
        [u8; 32],
        FederationId,
        SwissTable,
        CellId,
    ) {
        let (intro_sk, intro_pk): (SigningKey, PublicKey) = generate_keypair();
        let intro_fed = FederationId(intro_pk.0);
        let (recip_sk, recip_pk) = generate_keypair();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        let swiss =
            swiss_table.export_with_options(target_cell, held, 100, None, held_effects, None);

        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            granted,
            granted_effects,
            None,
            None,
            swiss,
        );
        let presentation = HandoffPresentation::create(cert, &recip_sk);
        (
            presentation,
            intro_pk.0,
            intro_fed,
            swiss_table,
            target_cell,
        )
    }

    /// THE CROSS-NODE DEMONSTRATION (positive): node A presents an attenuating
    /// handoff to node B over a live two-party transport; B verifies + resolves
    /// it into a SendCap and EXERCISES it (a real Bus enqueue leaving a custody
    /// receipt). The handed-off authority genuinely works on B.
    #[test]
    fn cross_node_handoff_resolves_and_the_cap_works() {
        // Held = Either; granted = Signature (strict attenuation).
        let (presentation, intro_pk, intro_fed, mut swiss_table, target_cell) =
            scenario(AuthRequired::Either, None, AuthRequired::Signature, None);
        let known = vec![intro_fed];

        // Two nodes on one in-process fabric: A (the holder) and B (the target).
        let fabric = InProcessFabric::new();
        let (reply, resolution) = drive_handoff(
            &fabric,
            &presentation,
            intro_pk,
            &mut swiss_table,
            &known,
            150,
        );
        let resolution = resolution.expect("B resolved the handoff");

        // (a) The reply is Accepted with the GRANTED (attenuated) authority.
        match reply {
            HandoffReply::Accepted {
                cell_id,
                permissions_tag,
                ..
            } => {
                assert_eq!(cell_id, target_cell.0);
                assert_eq!(permissions_tag, 1, "granted authority is Signature");
            }
            other => panic!("expected Accepted, got {other:?}"),
        }

        // (b) Authority bound: the resolved grant is ⊆ what A held (Either).
        assert!(
            resolution
                .permissions()
                .is_narrower_or_equal(&AuthRequired::Either),
            "resolved grant must be bounded by the introducer's held authority"
        );
        assert_eq!(resolution.permissions(), &AuthRequired::Signature);

        // (c) THE CAP WORKS ON B: resolve into a SendCap and exercise it on a
        // real data-plane Bus — a genuine enqueue leaving a signed receipt.
        let (relay_sk, relay_pk) = generate_keypair();
        let relay_id = FederationId(relay_pk.0);
        let mut bus = Bus::new(relay_id, relay_sk, 64, 256);
        let recipient = FederationId(target_cell.0);
        let channel = ChannelName::new(b"handoff-demo".to_vec());
        let cap = resolution.into_send_cap(recipient, channel.clone());

        let delivery = bus
            .enqueue(
                &cap,
                recipient,
                &channel,
                AuthRequired::Signature, // offered ⊆ granted
                b"a real turn through the handed-off cap".to_vec(),
                1,
            )
            .expect("the handed-off cap must admit a within-grant enqueue");
        // A committed receipt: the cap genuinely works on B.
        assert_ne!(delivery.content_hash, [0u8; 32]);

        // And an OVER-broad use of the resolved cap is refused at the Bus seam:
        // offering None (broader) than the granted Signature is rejected.
        let over = bus.enqueue(
            &cap,
            recipient,
            &channel,
            AuthRequired::None, // broader than the grant: amplification at use
            b"over-broad use".to_vec(),
            2,
        );
        assert!(
            matches!(
                over,
                Err(crate::data_plane::DataPlaneError::Unauthorized { .. })
            ),
            "using the handed-off cap beyond its grant must be refused"
        );
    }

    /// THE NO-AMPLIFICATION PROOF (negative): node A tries to hand B MORE
    /// authority than A holds (held = Signature, granted = None). B's validator
    /// refuses it as amplification — over the wire, the reply is
    /// `Refused { amplification: true }` and B resolves NOTHING.
    #[test]
    fn over_broad_handoff_is_refused_over_the_wire() {
        // Held = Signature; granted = None (looser requirement = MORE authority).
        let (presentation, intro_pk, intro_fed, mut swiss_table, _cell) =
            scenario(AuthRequired::Signature, None, AuthRequired::None, None);
        let known = vec![intro_fed];

        let fabric = InProcessFabric::new();
        let (reply, resolution) = drive_handoff(
            &fabric,
            &presentation,
            intro_pk,
            &mut swiss_table,
            &known,
            150,
        );

        assert!(
            resolution.is_none(),
            "an amplifying handoff resolves NOTHING on B"
        );
        match reply {
            HandoffReply::Refused {
                amplification,
                reason,
            } => {
                assert!(
                    amplification,
                    "refusal must be flagged as amplification: {reason}"
                );
            }
            other => panic!("expected Refused(amplification), got {other:?}"),
        }
    }

    /// EFFECT-FACET amplification (granted effect bit the introducer lacks) is
    /// also refused over the wire.
    #[test]
    fn effect_amplifying_handoff_refused_over_the_wire() {
        use dregg_cell::{EFFECT_EMIT_EVENT, EFFECT_TRANSFER};
        // Held = {emit}; granted = {emit, transfer} (adds transfer).
        let (presentation, intro_pk, intro_fed, mut swiss_table, _cell) = scenario(
            AuthRequired::Signature,
            Some(EFFECT_EMIT_EVENT),
            AuthRequired::Signature,
            Some(EFFECT_EMIT_EVENT | EFFECT_TRANSFER),
        );
        let known = vec![intro_fed];

        let fabric = InProcessFabric::new();
        let (reply, resolution) = drive_handoff(
            &fabric,
            &presentation,
            intro_pk,
            &mut swiss_table,
            &known,
            150,
        );

        assert!(resolution.is_none());
        match reply {
            HandoffReply::Refused { amplification, .. } => assert!(amplification),
            other => panic!("expected Refused(amplification), got {other:?}"),
        }
    }

    /// THE SAME HANDOFF OVER THE RELAY (store-and-forward) NETLAYER — the real
    /// federation cross-party transport (sealed X25519 frames queued on a relay
    /// that sees only ciphertext). A (holder) seals the `PresentHandoff` frame to
    /// B over the relay; B drains it, validates via the proven validator, and
    /// resolves a usable cap. The reply rides back on a second relay leg (B dials
    /// A). Proves the wire is transport-agnostic: identical code, real federation
    /// channel.
    #[test]
    fn cross_node_handoff_over_the_relay_netlayer() {
        use crate::netlayer::{RelayAddr, RelayNetlayer};
        use crate::store_forward::{MessageRelay, generate_x25519_keypair};
        use std::sync::{Arc, Mutex};

        let (presentation, intro_pk, intro_fed, mut swiss_table, target_cell) =
            scenario(AuthRequired::Either, None, AuthRequired::Signature, None);
        let known = vec![intro_fed];

        // One shared relay (the hosted inbox); two parties sealing to each other.
        let relay = Arc::new(Mutex::new(MessageRelay::new(64, 256)));
        let (a_sk, a_pk) = generate_x25519_keypair();
        let (b_sk, b_pk) = generate_x25519_keypair();
        let a_id = FederationId([0xAA; 32]);
        let b_id = FederationId([0xBB; 32]);
        let node_a = RelayNetlayer::new(relay.clone(), a_id, a_sk, 100);
        let node_b = RelayNetlayer::new(relay, b_id, b_sk, 100);
        let to_b = RelayAddr {
            peer: b_id,
            dest_x25519_pk: b_pk,
        };
        let to_a = RelayAddr {
            peer: a_id,
            dest_x25519_pk: a_pk,
        };

        let (reply, resolution) = block_on(async {
            // A dials B (connectionless mint) and PRESENTS the handoff: the frame
            // is sealed end-to-end and queued on the relay.
            let a_sess = node_a.dial(&to_b).await.unwrap();
            present_handoff(&a_sess.conn, &presentation, intro_pk)
                .await
                .unwrap();

            // B accepts: drains the relay, surfacing A as an inbound session, then
            // validates + replies. The accepted session is inbound-only (no key),
            // so B dials A back with A's key to send the reply frame.
            let b_inbound = node_b.accept().await.unwrap().expect("inbound from A");
            let resolution = accept_handoff(&b_inbound.conn, &mut swiss_table, &known, 150)
                .await
                .unwrap();
            // `accept_handoff` already tried to reply on the inbound-only conn
            // (which fails closed); re-send the verdict on a real dial-back leg.
            let verdict = if let Some(r) = &resolution {
                HandoffReply::Accepted {
                    routing_token: r.acceptance.routing_token,
                    cell_id: r.acceptance.cell_id.0,
                    permissions_tag: perm_tag(&r.acceptance.permissions),
                }
            } else {
                HandoffReply::Refused {
                    reason: "refused".into(),
                    amplification: false,
                }
            };
            let b_dial = node_b.dial(&to_a).await.unwrap();
            b_dial
                .conn
                .send(postcard::to_stdvec(&verdict).unwrap())
                .await
                .unwrap();

            // A drains the reply leg.
            let a_inbound = node_a.accept().await.unwrap().expect("reply from B");
            let reply = await_handoff_reply(&a_inbound.conn).await.unwrap();
            (reply, resolution)
        });

        let resolution = resolution.expect("B resolved the relayed handoff");
        match reply {
            HandoffReply::Accepted { cell_id, .. } => assert_eq!(cell_id, target_cell.0),
            other => panic!("expected Accepted over the relay, got {other:?}"),
        }
        // The cap works on B: a real enqueue, bounded by the granted authority.
        assert_eq!(resolution.permissions(), &AuthRequired::Signature);
        let (relay_sk, relay_pk) = generate_keypair();
        let mut bus = Bus::new(FederationId(relay_pk.0), relay_sk, 64, 256);
        let recipient = FederationId(target_cell.0);
        let channel = ChannelName::new(b"relayed-handoff".to_vec());
        let cap = resolution.into_send_cap(recipient, channel.clone());
        let delivery = bus
            .enqueue(
                &cap,
                recipient,
                &channel,
                AuthRequired::Signature,
                b"a real turn through the relayed handed-off cap".to_vec(),
                1,
            )
            .expect("relayed handed-off cap must work");
        assert_ne!(delivery.content_hash, [0u8; 32]);
    }

    /// An UNTRUSTED introducer (not in B's `known_federations`) is refused over
    /// the wire — connectivity does not beget connectivity from a stranger.
    #[test]
    fn untrusted_introducer_refused_over_the_wire() {
        let (presentation, intro_pk, _intro_fed, mut swiss_table, _cell) =
            scenario(AuthRequired::Signature, None, AuthRequired::Signature, None);
        let known: Vec<FederationId> = vec![]; // B trusts no one

        let fabric = InProcessFabric::new();
        let (reply, resolution) = drive_handoff(
            &fabric,
            &presentation,
            intro_pk,
            &mut swiss_table,
            &known,
            150,
        );

        assert!(resolution.is_none());
        match reply {
            HandoffReply::Refused {
                amplification,
                reason,
            } => {
                assert!(!amplification);
                assert!(reason.contains("trusted") || reason.contains("introducer"));
            }
            other => panic!("expected Refused, got {other:?}"),
        }
    }
}
