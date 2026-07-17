//! The `/gallery` ↔ IPFS join (backlog #19) — **`pin:true` at publish + the CID shown**,
//! over the committed [`ugc_dregg::ipfs`] verify-don't-trust bridge (landed `05b8dadcb`).
//!
//! Two addresses, two jobs (the ugc-dregg module doc's mandate, kept intact here):
//! the **UniverseId** is the authorship commitment `/gallery` already shows; the **CID**
//! is the transport address a gateway routes/pins/serves by. The CID is a PURE function
//! of the canonical wire payload (`blake3` over the encoded bytes, CIDv1-wrapped), so
//! [`cid_of`] derives it **without any network** — through an in-process [`MockIpfs`]
//! store, which pins nothing anywhere and exists only to run the same refuse-before-pin
//! round-trip check ([`ugc_dregg::ipfs::publish_universe`] re-derives the universe's own
//! id from the payload before returning an address). Every published universe therefore
//! SHOWS its CID; `pin:true` additionally pushes the payload to the operator's Kubo node
//! (`DREGG_IPFS_API`, local daemon default) so it is durable across gateways.
//!
//! A stranger holding the CID re-verifies everything:
//! `ugc_dregg::ipfs::fetch_universe(client, cid, Some(expected_id))` re-witnesses every
//! block against the CID and re-derives the UniverseId through the REAL publish
//! validation — a lying gateway can serve neither tampered bytes nor a swapped universe.

use dregg_ipfs::client::{KuboClient, MockIpfs, StdHttpPost};
use ugc_dregg::Universe;
use ugc_dregg::ipfs::{PublishedUniverse, UgcIpfsError, publish_universe};

/// The default local Kubo RPC endpoint (`ipfs daemon`).
pub const DEFAULT_IPFS_API: &str = "http://127.0.0.1:5001";

/// The configured IPFS node: `DREGG_IPFS_API` or the local daemon default.
pub fn ipfs_api_base() -> String {
    std::env::var("DREGG_IPFS_API").unwrap_or_else(|_| DEFAULT_IPFS_API.to_string())
}

/// **Derive a universe's payload CID without a network** — the CID is content-derived
/// (blake3 of the canonical wire payload), so an in-process store yields the identical
/// address a real node pins under. Runs the full refuse-before-pin round-trip check.
pub fn cid_of(universe: &Universe) -> Result<String, UgcIpfsError> {
    publish_universe(&MockIpfs::new(), universe).map(|p| p.payload_cid.to_string_cid())
}

/// **PIN the universe's canonical payload to the configured Kubo node** — the durable
/// half of `pin:true`. Blocking IO (plain-HTTP RPC to the daemon); call off the async
/// loop (`spawn_blocking`).
pub fn pin_universe(universe: &Universe) -> Result<PublishedUniverse, UgcIpfsError> {
    let client = KuboClient::new(ipfs_api_base(), StdHttpPost::new());
    publish_universe(&client, universe)
}

/// The honest one-field IPFS note a `/gallery publish` embeds: the derived CID always,
/// plus the pin outcome — a real pin receipt, an explicit "not pinned" hint, or the
/// node's own refusal (never smoothed into success).
pub fn publish_note(universe: &Universe, pin: bool) -> String {
    let cid = match cid_of(universe) {
        Ok(cid) => cid,
        Err(e) => return format!("CID derivation refused: {e}"),
    };
    let pin_line = if pin {
        match pin_universe(universe) {
            Ok(p) => format!(
                "📌 pinned to `{}` ({} bytes) — durable across gateways.",
                ipfs_api_base(),
                p.payload_len
            ),
            Err(e) => format!(
                "⚠ pin to `{}` refused: {e}\nThe CID above is still the real address — \
                 any node that pins the payload serves it.",
                ipfs_api_base()
            ),
        }
    } else {
        "not pinned — pass `pin:true` to pin it to the configured IPFS node.".to_string()
    };
    format!(
        "CID `{cid}`\n{pin_line}\nFetching by CID re-verifies content AND authorship \
         (`fetch_universe` re-derives the universe id — a lying gateway is refused)."
    )
}

/// The one-line CID note `/gallery show` embeds (derivation only, never network).
pub fn show_note(universe: &Universe) -> String {
    match cid_of(universe) {
        Ok(cid) => format!(
            "payload CID `{cid}` — fetchable + re-verifiable off any gateway \
             (`pin:true` at publish makes it durable)."
        ),
        Err(e) => format!("CID derivation refused: {e}"),
    }
}

#[cfg(test)]
mod tests {
    //! The CID face is REAL: derivation is pure + stable, and it round-trips through the
    //! verified fetch path with the id tooth engaged.
    use dregg_ipfs::client::MockIpfs;
    use ugc_dregg::ipfs::fetch_universe;

    use super::*;

    fn a_universe() -> Universe {
        Universe::daily("gallery-ipfs-test", &[0x4D; 32]).expect("a daily universe publishes")
    }

    /// The derived CID equals the CID a real pin lands at (the same pure payload address),
    /// and the pinned payload FETCHES BACK as the identical universe with the expected-id
    /// tooth engaged.
    #[test]
    fn derived_cid_matches_the_pinned_address_and_round_trips() {
        let u = a_universe();
        let derived = cid_of(&u).expect("cid derives");

        let node = MockIpfs::new();
        let pinned = publish_universe(&node, &u).expect("pins");
        assert_eq!(
            derived,
            pinned.payload_cid.to_string_cid(),
            "the CID is a pure function of the payload — derivation == pin address"
        );

        let back = fetch_universe(&node, &pinned.payload_cid, Some(&u.id()))
            .expect("fetches + re-verifies");
        assert_eq!(back.id(), u.id(), "the re-derived identity matches");
    }

    /// The publish/show notes carry the CID (the user-visible tooth of #19).
    #[test]
    fn the_notes_carry_the_cid() {
        let u = a_universe();
        let cid = cid_of(&u).expect("cid derives");
        assert!(publish_note(&u, false).contains(&cid));
        assert!(show_note(&u).contains(&cid));
    }
}
