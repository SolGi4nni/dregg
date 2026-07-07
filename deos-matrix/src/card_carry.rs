//! **The card-fork carry vehicle** — a co-driven card's fork-envelope riding a
//! real Matrix hop.
//!
//! Pillar 3 of the distributed-deos goal: two principals on two DIFFERENT running
//! cockpit processes co-drive ONE hyperdreggmedia card, and the fork-envelope that
//! carries one side's driven view CROSSES a live homeserver so the stitch lands on
//! both. Today the deos side already knows how to make a card portable — a
//! `starbridge_v2::distributed_card::CardForkEnvelope` (the three serializable
//! strings the `dregg_doc` stitch consumes + the authoring authority), sealed to
//! `postcard` bytes plus a domain-separated blake3 `fork_root` (the
//! anti-substitution tooth). What was missing is the WIRE: those bytes only ever
//! crossed an in-process test boundary.
//!
//! This module supplies the vehicle. It is deliberately **byte-only**: deos-matrix
//! is dependency-light (it does NOT pull the `deos-js`/`dregg-cell` executor graph),
//! so it never sees the `CardForkEnvelope` TYPE — only its opaque sealed bytes and
//! the claimed root. It reuses the EXISTING, homeserver-proven membrane wire path
//! ([`crate::membrane::MembraneEnvelope`] under
//! [`MEMBRANE_EVENT_KEY`](crate::membrane::MEMBRANE_EVENT_KEY), spliced into an
//! `m.room.message` by [`MatrixClient::send_membrane`]): a card-fork envelope rides
//! as a `MembraneEnvelope` whose `snapshot` is the sealed card bytes and whose
//! `frustum_root` is the card's claimed `fork_root`. A `dregg://card-fork/…`
//! sturdyref marks it as a card carry (vs a world-fork membrane).
//!
//! **The tooth is NOT here.** Re-deriving `fork_root` from the decoded
//! `CardForkEnvelope` (and thus REFUSING a substituted/forged envelope) is
//! `starbridge_v2::distributed_card::open_envelope` — it lives where the type lives.
//! This vehicle only carries the tooth's two inputs (the bytes and the claimed root)
//! ACROSS the wire, byte-intact, so the recipient's executor can fire the real tooth
//! (never trust the wire: acceptance is re-decided on the deos side). This is
//! symmetric to how a world-fork `MembraneEnvelope` rides here inertly and
//! `ForkMembraneHost` fires the `frustum_root` check on rehydrate.

use crate::membrane::{FrustumCut, MembraneEnvelope, WitnessCursor};
use crate::{MatrixClient, Result};

/// The `sturdyref` scheme that marks a [`MembraneEnvelope`] as a **card-fork carry**
/// (a portable `CardForkEnvelope`) rather than a world-fork membrane. The recipient
/// keys on this prefix to route the payload to the distributed-card open/rehydrate
/// path instead of the world rehydrate path.
pub const CARD_FORK_STURDYREF_PREFIX: &str = "dregg://card-fork/";

/// Wrap a sealed card-fork envelope (its `postcard` bytes + the claimed
/// `fork_root`, exactly what `starbridge_v2::distributed_card::seal_fork` returns)
/// into a [`MembraneEnvelope`] — the vehicle that rides the existing membrane wire
/// path over a real homeserver.
///
/// The mapping is faithful and load-bearing:
///   * `snapshot` ← the sealed card bytes (the tooth's payload input);
///   * `frustum_root` ← the card's claimed `fork_root` (the tooth's commitment input);
///   * `sturdyref` ← a [`CARD_FORK_STURDYREF_PREFIX`] tag so the recipient routes it
///     to the distributed-card path.
///
/// Both tooth inputs travel together and unchanged, so the recipient's
/// `open_envelope` re-derives the root from the carried bytes and refuses any
/// mismatch — the wire is never trusted.
pub fn card_fork_membrane(card_bytes: &[u8], fork_root: [u8; 32]) -> MembraneEnvelope {
    MembraneEnvelope {
        version: MembraneEnvelope::VERSION,
        frustum_root: fork_root,
        sturdyref: format!("{CARD_FORK_STURDYREF_PREFIX}{}", hex8(&fork_root)),
        // A card carry has no surface-capability meet: the authoring cap tooth is
        // INSIDE the sealed `CardForkEnvelope` (`edit_authority`), enforced by the
        // recipient's `rehydrate_fork` against its own `held`. So no lineage cap.
        lineage: Vec::new(),
        snapshot: card_bytes.to_vec(),
        cut: FrustumCut {
            focus_cell: fork_root,
            max_depth: 0,
            authority_bounded: true,
            cell_count: 1,
        },
        cursor: WitnessCursor {
            height: 0,
            commit_index: 0,
        },
    }
}

/// If `env` is a **card-fork carry** (its `sturdyref` bears
/// [`CARD_FORK_STURDYREF_PREFIX`] and its wire version is rehydratable), recover the
/// carried `(sealed_card_bytes, claimed_fork_root)` — the two inputs the recipient's
/// `starbridge_v2::distributed_card::open_envelope` tooth consumes. Returns `None`
/// for a world-fork membrane or an unsupported wire version (fail-closed: an
/// unrecognized carrier is never half-interpreted).
pub fn as_card_fork_carry(env: &MembraneEnvelope) -> Option<(Vec<u8>, [u8; 32])> {
    if !env.is_rehydratable() {
        return None;
    }
    if !env.sturdyref.starts_with(CARD_FORK_STURDYREF_PREFIX) {
        return None;
    }
    Some((env.snapshot.clone(), env.frustum_root))
}

/// Whether `env` is a card-fork carry (vs a world-fork membrane), without decoding
/// the payload.
pub fn is_card_fork_carry(env: &MembraneEnvelope) -> bool {
    env.sturdyref.starts_with(CARD_FORK_STURDYREF_PREFIX)
}

/// **Send a sealed card-fork envelope to a room over the live session.** A thin
/// convenience over [`MatrixClient::send_membrane`]: it wraps the sealed bytes +
/// root into a card-carry [`MembraneEnvelope`] and ships it under the proven
/// membrane wire key. A non-deos client sees the human `body` fallback; a deos
/// recipient extracts the membrane, routes it via [`as_card_fork_carry`], and fires
/// the real root tooth on the deos side. Returns the server-assigned event id.
///
/// `card_bytes` + `fork_root` are exactly what
/// `starbridge_v2::distributed_card::seal_fork` returns.
pub async fn send_card_fork(
    client: &MatrixClient,
    room_id: &str,
    body: &str,
    card_bytes: &[u8],
    fork_root: [u8; 32],
) -> Result<String> {
    let env = card_fork_membrane(card_bytes, fork_root);
    let body = if body.trim().is_empty() {
        format!("[deos card-fork · root {}]", hex8(&fork_root))
    } else {
        body.to_string()
    };
    client.send_membrane(room_id, &body, &env).await
}

fn hex8(b: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(8);
    for byte in &b[..4] {
        let _ = write!(s, "{byte:02x}");
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::membrane::MockMembraneHost;

    /// A stand-in for a sealed `CardForkEnvelope`'s bytes + root. deos-matrix cannot
    /// link the real type, so the vehicle is exercised over opaque bytes here; the
    /// REAL `CardForkEnvelope` round-trip + tooth refusal is proven on the executor
    /// side (`starbridge_v2::card_carry_bridge` tests).
    fn synthetic_seal() -> (Vec<u8>, [u8; 32]) {
        let bytes = b"a sealed card-fork envelope (postcard bytes, opaque here)".to_vec();
        // A synthetic "fork_root" — the vehicle treats it as an opaque commitment.
        let mut root = [0u8; 32];
        for (i, r) in root.iter_mut().enumerate() {
            *r = (i as u8).wrapping_mul(7).wrapping_add(3);
        }
        (bytes, root)
    }

    #[test]
    fn card_carry_vehicle_round_trips_bytes_and_root_through_the_membrane_wire() {
        let (bytes, root) = synthetic_seal();
        let env = card_fork_membrane(&bytes, root);

        // It is a well-formed card carry (tagged sturdyref, both tooth inputs present).
        assert!(is_card_fork_carry(&env));
        assert_eq!(env.frustum_root, root, "the claimed fork_root rides intact");
        assert_eq!(env.snapshot, bytes, "the sealed card bytes ride intact");

        // It survives the SAME JSON the `m.room.message` custom field carries on the
        // wire (the leg a real homeserver relays verbatim).
        let json = serde_json::to_string(&env).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(env, back, "the card carry survives the wire byte-intact");

        // And it unwraps to EXACTLY the sealed bytes + claimed root — the two inputs
        // the recipient's `open_envelope` tooth re-checks. Identity round-trip.
        let (got_bytes, got_root) =
            as_card_fork_carry(&back).expect("a card carry unwraps to its tooth inputs");
        assert_eq!(got_bytes, bytes, "the sealed bytes recovered identically");
        assert_eq!(got_root, root, "the claimed root recovered identically");
    }

    #[test]
    fn a_world_fork_membrane_is_not_mistaken_for_a_card_carry() {
        // A genuine world-fork membrane (mock host) must NOT be routed to the card
        // path — the sturdyref scheme distinguishes the two carriers.
        let world = MockMembraneHost::sample_envelope();
        assert!(!is_card_fork_carry(&world));
        assert!(as_card_fork_carry(&world).is_none());
    }

    #[test]
    fn a_tampered_card_carry_still_carries_the_tooth_inputs_for_downstream_refusal() {
        // The vehicle is byte-faithful: if an adversary substitutes the snapshot
        // bytes but leaves the claimed root, the wire preserves BOTH exactly — so the
        // recipient's real tooth (`open_envelope`, on the executor side) sees a root
        // that no longer matches the bytes and refuses. This test proves the vehicle
        // does not "heal" or drop either input (which would blind the tooth).
        let (bytes, root) = synthetic_seal();
        let mut env = card_fork_membrane(&bytes, root);
        env.snapshot.extend_from_slice(b"<<forged node>>"); // substitute payload, keep root

        let json = serde_json::to_string(&env).unwrap();
        let back: MembraneEnvelope = serde_json::from_str(&json).unwrap();
        let (got_bytes, got_root) = as_card_fork_carry(&back).expect("still a card carry");
        assert_ne!(got_bytes, bytes, "the substituted payload is carried as-is");
        assert_eq!(
            got_root, root,
            "the claimed root is UNCHANGED — the tooth will see bytes↔root disagree and refuse"
        );
    }
}
